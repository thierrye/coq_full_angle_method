%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include <ctype.h>
  
#define MAX_STR_BUFF_SIZE 2000
#define MAX_PO_BUFF_SIZE 30
#define MAX_ID_LENGTH 6
#define POINT_TYPE_STR ": FA_Point,\n"
#define PO_DECL_STR "Lemma fa_l%d : forall "
#define PRED_NUMBER 13
#define FA_FUN  "fa_from_point"
  char *prol_id_buff[PRED_NUMBER] = {"coll",
				     "para",
				     "perp",
				     "cong",
				     "eqangle",
				     "midpoint",
				     "cyclic",
				     "foot",
				     "circumcenter",
				     "orthocenter",
				     "similar",
				     "incenter",
				     "pbisector"};
  char *coq_id_buff[PRED_NUMBER] = {"FA_P_col",
				    "FA_P_para",
				    "FA_P_perp",
				    "FA_P_cong",
				    "FA_P_eqangle",
				    "FA_P_midp",
				    "FA_P_cycl",
				    "FA_P_foot",
				    "FA_P_circum",
				    "FA_P_orthoc",
				    "FA_P_sim",
				    "FA_P_incenter",
				    "FA_P_pbisector"};
  enum { OUT_POS , PO_DECL_POS , HYP_POS , CONCL_POS} current_pos;
  enum str_type { PO_DECL , HYP_DECL , CONCL_DECL , ID_MATCH , PAIR_ID_MATCH , PONCT , DECL_SEP , PROP_ID , L_PAR , R_PAR , SQ_BR_L , SQ_BR_R , FA_VAL , PLUS_MATCH , MINUS_MATCH , EQUAL_MATCH} prev_tok_typ;
  bool sq_br_open;
  bool sq_prop;
  int fad_sbo_n_param;// should be always =<5
  
  char curr_str_buff[MAX_STR_BUFF_SIZE];
  //char *point_order_buff[MAX_PO_BUFF_SIZE];
  //  char prev_tok[MAX_STR_BUFF_SIZE];
  int curr_buff_pos;
  FILE* output_file;
  int line_number;
  int lemma_number;
  typedef struct ido_l{char id_str[MAX_ID_LENGTH]; struct ido_l* next;} ido_l;
  ido_l* point_order_l;

  void free_idl()
    {
      ido_l *curr_ido,*next_ido;
      curr_ido = point_order_l;
      while(curr_ido != 0)
	{
	  next_ido = curr_ido->next;
	  free(curr_ido);
	  curr_ido = next_ido;
	}
      point_order_l = 0;
    }
	  
  void curr_sbuff_zero(FILE *fd)
    {
      fprintf(fd,"buff state :");
      for(int i=0;i<20;i++)
	{
	  if(curr_str_buff[i] == '\0')
	    fprintf(fd," 0 ");
	  else
	    fprintf(fd," ELSE ");
	}
      fprintf(fd,"\n");
    }
  void print_current_pos(FILE *fd)
    {
      fprintf(fd,"current text posistion :");
      switch(current_pos)
	{
	case OUT_POS:
	  fprintf(fd,"outside of prol decl\n");break;
	case PO_DECL_POS:
	  fprintf(fd,"Point order declaration\n");break;
	case HYP_POS:
	  fprintf(fd,"Hypotheses parsing\n");break;
	case CONCL_POS:
	  fprintf(fd,"Printing concl\n");break;
	}
    }
  void print_prev_tok_typ(FILE *fd)
    {
      //fprintf(fd,"Previous token type :");
      switch(prev_tok_typ)
	{
	case ID_MATCH:
	  fprintf(fd,"Point ID\n");break;
	case DECL_SEP:
	  fprintf(fd,"A comma\n");break;
	case PO_DECL:
	  fprintf(fd,"decl a new section : point order\n");break;
	case HYP_DECL:
	  fprintf(fd,"decl a new section : hyp\n");break;
	case CONCL_DECL:
	  fprintf(fd,"decl a new section : concl\n");break;
	case PONCT:
	  fprintf(fd,"ponctuation\n");break;
	case PROP_ID:
	  fprintf(fd,"prop_id\n");break;
	case L_PAR:
	  fprintf(fd,"left par\n");break;
	case R_PAR:
	  fprintf(fd,"right par\n");break;
	}
    }
  void print_curr_str_buff(FILE* fd)
    {
      //curr_str_buff[curr_buff_pos]=0;
      fprintf(fd," buff_pos : %d curr_str_buff str : %s",curr_buff_pos,curr_str_buff);
    }
  void print_errs_to_fd(FILE* fd,char *msg)
    {
      fprintf(fd,"Error line : %d \n%s",line_number,msg);
      print_current_pos(fd);
      print_prev_tok_typ(fd);
      print_curr_str_buff(fd);
    }
  void print_error(char * msg)
    {
      //print_errs_to_fd(stderr,msg);
      print_errs_to_fd(stdout,msg);
      //exit(1);
    }
  void print_to_buffstr(char* tok_str_)
    {
      //curr_buff_pos = beginning;
      strcpy(curr_str_buff+curr_buff_pos,tok_str_);

      curr_buff_pos += strlen(tok_str_);
      if(curr_buff_pos > MAX_STR_BUFF_SIZE -2)
	{
	  fprintf(stderr,"to long str -> exiting\n");
	  exit(1);
	}
      //debug
      fprintf(stdout,"print_to_buffstr curr_buff_pos = %d line is : %d \n ",curr_buff_pos,line_number);
      print_prev_tok_typ(stdout);
      fprintf(stdout,"print_to_buffstrbis str is %s\n",tok_str_);
      //debug_end
    }
  void print_po_decl_format()
    {
      curr_buff_pos = 0;
      curr_buff_pos = sprintf(curr_str_buff,PO_DECL_STR,lemma_number);

      //debug
      fprintf(stdout,"print_po_decl_format : cur_sbuff :");
      fprintf(stdout,curr_str_buff);
      fprintf(stdout,"\nprint_po_decl_format  buff_pos = %d \n",curr_buff_pos);
      //debug_end
    }
  void print_buffstr_to_file(FILE *outfile)
    {
      fprintf(outfile,"%s",curr_str_buff);
      curr_buff_pos = 0;
      lemma_number++;
    }
  bool lookup_prop_id(char** coq_pred,char *prol_pred)
    {
      for(int i = 0;i < PRED_NUMBER;i++)
	{
	  if(strcmp(prol_pred,prol_id_buff[i]) == 0)
	    {
	      *coq_pred = coq_id_buff[i];
	      return true;
	    }
	}
      return false;
    }
  void add_id_to_idl(char* low_case_id)
    {
      ido_l* nid_lc = malloc(sizeof(*nid_lc));
      strcpy(nid_lc->id_str,low_case_id);
      nid_lc->next = NULL;
      
      if(point_order_l == NULL)
	{
	  point_order_l = nid_lc;
	  fprintf(stdout," add_id_to_idlerr : point_order_l->str = %s\n",
		  point_order_l->id_str);
	}
      else{
	ido_l* last = point_order_l;
	
	//last = malloc(sizeof(last));
	while(last->next != NULL)
	  last = last->next;
	last->next = nid_lc;
      }
    }
	   
  void printid_to_buffstr(char* low_case_id)
    {
      //add_id_to_idl(low_case_id);
      
      char up_case_id[MAX_ID_LENGTH];
      if(strlen(low_case_id)>MAX_ID_LENGTH -1)
	{
	  fprintf(stdout," printid_to_buffstr strlen = %d\n",strlen(low_case_id));
	  return;
	}	  
      for(int i=0;i<strlen(low_case_id);i++)
	{
	  up_case_id[i]=toupper(low_case_id[i]);
	}
      up_case_id[strlen(low_case_id)] = 0;
      print_to_buffstr(up_case_id);
    }

  	  
  int po_lookup(char* id,char* str_match)
    {
      if(point_order_l == NULL)
	return -1;
      ido_l* last = point_order_l;
      while(last != NULL)
	{
	  for(int i=1;i<5;i++)
	    {
	      if(memcmp(last->id_str,str_match,i) == 0)
		{
		  id = last->id_str;
		  return i;
		}
	    }
	  last = last->next;
	}
      return -1;
    }
  bool split_id(char* first_id,char* second_id,char* str_match)
    {
      
      /**/
      int f_str_size=po_lookup(first_id,str_match);
      if(f_str_size <0)
	{
	  fprintf(stdout,"split_id first no match str = %s\n",str_match);
	  //exit(1);
	  return false;
	}
      if(po_lookup(second_id,str_match+f_str_size) < 0)
	{
	  fprintf(stdout,"split_id second no match str = %s\n",str_match);
	  //exit(1);
	  return false;
	}
      return true;
    }

  void fa_print_sqbr_decl(enum str_type str_match_type,char *str_match)
    {
      //TODO prev_tok_typ handle maybe no need
      char* coq_pred;
      switch(str_match_type)
	{
	case SQ_BR_L:
	  fad_sbo_n_param = 0;
	  sq_br_open = true;
	  sq_prop = false;
	  prev_tok_typ = str_match_type;
	  return;break;
	case PROP_ID:
	  if(sq_prop == false && fad_sbo_n_param == 0)
	    {
	      sq_prop = true;
	      fad_sbo_n_param = 1;
	      sq_br_open = true;
	      lookup_prop_id(&coq_pred,str_match);
	      print_to_buffstr(coq_pred);
	      prev_tok_typ = str_match_type;
	      //print_to_buffstr(FA_FUN);
	    }else{
	    //error
	    fprintf(stdout,"fa_print_sqbr_declerr propid and sq_prop == true or paramn = %d\n",fad_sbo_n_param);
	  }
	  return;break;
	case ID_MATCH:
	  if(sq_prop)
	    {
	      printid_to_buffstr(str_match);
	    }else{
	    //first split id in two!!
	    char *first_id,*second_id;
	    if(split_id(first_id,second_id,str_match))
	      {
		printid_to_buffstr(first_id);
		print_to_buffstr(" ");
		printid_to_buffstr(second_id);
	      }else{
	      printid_to_buffstr(yytext);
	    }
	  }
	  fad_sbo_n_param++;
	  prev_tok_typ = str_match_type;
	  return;break;
	case PAIR_ID_MATCH:
	  if(sq_br_open)
	    {
	      char *first_id;
	      char* second_id;
	      if(split_id(first_id,second_id,str_match))
		{
		  printid_to_buffstr(first_id);
		  print_to_buffstr(" ");
		  printid_to_buffstr(second_id);
		}else{
		printid_to_buffstr(yytext);
	      }
	    }
	  else{
	    fprintf(stdout,"errorpair sq_br_open = false\n");
	    exit(1);
	  }
	  return;break;
	case DECL_SEP:
	  print_to_buffstr(" ");
	  prev_tok_typ = str_match_type;
	  return;break;
	case SQ_BR_R:
	  sq_br_open = false;
	  sq_prop = false;
	  prev_tok_typ = str_match_type;
	  return;break;
	case FA_VAL:
	  if(prev_tok_typ == CONCL_DECL)
	    {
	      print_to_buffstr(str_match);
	      print_to_buffstr(" * ");
	      prev_tok_typ == FA_VAL;
	    }
	  if(prev_tok_typ == EQUAL_MATCH || prev_tok_typ == PLUS_MATCH || prev_tok_typ == MINUS_MATCH)
	    {
	      print_to_buffstr(str_match);
	      prev_tok_typ == FA_VAL;
	    }
	  return; break;
	case PLUS_MATCH:
	case MINUS_MATCH:
	case EQUAL_MATCH:
	  print_to_buffstr(" ");
	  print_to_buffstr(str_match);
	  print_to_buffstr(" ");
	  prev_tok_typ = str_match_type;
	  return;break;

	}
    }
	  
	  
	  
  void po_decl_parse(char *str_match,enum str_type str_match_type)
    {
      switch(str_match_type)
	{
	case PO_DECL:
	  //print_to_buffstr(0,PO_DECL_STR);
	  print_po_decl_format();
	  current_pos = PO_DECL_POS;

	  fprintf(stdout,"podecl : free_idl\n");
	  free_idl();
	  prev_tok_typ = PO_DECL;return;
	  break;
	case HYP_DECL:
	  if(prev_tok_typ == PONCT){
	    current_pos = HYP_POS;
	    prev_tok_typ = HYP_DECL;
	    return;
	  }else{
	    //debug
	    fprintf(stdout,"error7 Hypdecl with wrong state currpos = PO_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    //debug_end
	  }
	case CONCL_DECL:
	  //debug
	  fprintf(stdout,"error01 Concldecl with wrong state currpos = PO_DECL but prevtok was : ");
	  print_prev_tok_typ(stdout);
	  //debug_end
	  current_pos = OUT_POS;
	  return;break;
	case ID_MATCH:
	  switch(prev_tok_typ)
	    {
	    case PO_DECL:
	      //print_to_buffstr(str_match);
	      printid_to_buffstr(str_match);
	      add_id_to_idl(str_match);
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    case DECL_SEP:
	      //print_to_buffstr(str_match);
	      //debug
	      if(point_order_l == NULL)
		{
		  fprintf(stdout,"errorPODECL_id point_order_l == NULL currstr : %s\n",
			  curr_str_buff);
		  exit(1);
		}
	      //debug_end
	      printid_to_buffstr(str_match);
	      add_id_to_idl(str_match);
	      prev_tok_typ = ID_MATCH;return;break;
	    default:
	      //debug
	      fprintf(stdout,"error02 id_match  currpos = PO_DECL but prevtok was : ");
	      print_prev_tok_typ(stdout);
	      //debug_end
	      return; break;
	    }
	case DECL_SEP://comma ok prev should be id_match
	  if(prev_tok_typ == ID_MATCH)
	    {
	      print_to_buffstr(" ");
	      prev_tok_typ = DECL_SEP;
	    }
	  else{
	    //debug
	    fprintf(stdout,"error03 comma currpos = PO_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    //debug_end
	  }
	  return ;break;
	case PONCT://end of PO_DECL entering hyp_decl
	  if(prev_tok_typ == ID_MATCH)
	    {
	      print_to_buffstr(POINT_TYPE_STR);
	      //print_buffstr_to_file(output_file);
	      prev_tok_typ = PONCT;
	      //current_pos = HYP_POS;
	      return; break;
	    }else{
	    //debug
	    fprintf(stdout,"error04 ponct  currpos = PO_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    //debug_end
	  }return; break;

	default :
	  current_pos = OUT_POS;
	  //debug
	  fprintf(stdout,"error666   currpos = PO_DECL but prevtok was : ");
	  print_prev_tok_typ(stdout);
	  fprintf(stdout,"error666bis str is %s\n",str_match);
	  //debug_end
	  return; break;
	}
    }
  void hyp_parse( char *str_match,enum str_type str_match_type)
    {
      char* coq_pred_id;
      switch(str_match_type)
	{	  
	case HYP_DECL:
	  //error
	  //debug
	  fprintf(stdout,"error05 hyp_decl  currpos = hyp_DECL but prevtok was : ");
	  print_prev_tok_typ(stdout);
	  fprintf(stdout,"error05bis str is %s\n",str_match);
	  current_pos = OUT_POS;
	  //debug_end
	  return;break;
	case CONCL_DECL:
	  if(prev_tok_typ == PONCT)
	    {
	      prev_tok_typ = CONCL_DECL;
	      current_pos = CONCL_POS;
	    }
	  else{
	    current_pos = OUT_POS;
	    //debug
	    fprintf(stdout,"error_06 concldecl  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error_06bis str is %s\n",str_match);
	    //debug_end
	  }
	  return;break;
	case ID_MATCH:
	  switch(prev_tok_typ)
	    {
	      //case HYP_DECL:
	    case L_PAR:
	      //print_to_buffstr(str_match);
	      printid_to_buffstr(str_match);
	      //print_to_buffstr(" ");
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    case DECL_SEP:
	      //print_to_buffstr(str_match);
	      printid_to_buffstr(str_match);
	      //print_to_buffstr(" ");
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    default:
	      //error
	      //debug
	      fprintf(stdout,"errorid_hyp id_match  currpos = hyp_DECL but prevtok was : ");
	      print_prev_tok_typ(stdout);
	      fprintf(stdout,"errorid_hypbis str is %s\n",str_match);
	      //debug_end
	      return;break;
	    }
	  break;
	case PROP_ID:
	  if(lookup_prop_id(&coq_pred_id,str_match)&&			\
	     (prev_tok_typ ==  HYP_DECL || prev_tok_typ == DECL_SEP) )
	    {
	      print_to_buffstr(coq_pred_id);
	      print_to_buffstr(" ");
	      prev_tok_typ = PROP_ID;
	    }else{
	    //ERROR : back to the outside
	    current_pos = OUT_POS;
	    
	    //debug
	    fprintf(stdout,"errorprop id_match  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"errorpropbis str is %s\n",str_match);
	    //debug_end
	  }
	  return;
	  break;
	case DECL_SEP:
	  switch(prev_tok_typ)
	    {
	    case ID_MATCH:
	      print_to_buffstr(" ");
	      prev_tok_typ = DECL_SEP;return;
	      break;
	    case R_PAR://next token should be PROP_ID
	      print_to_buffstr(" ->");
	      prev_tok_typ = DECL_SEP;return;
	      break;
	    default:
	      current_pos = OUT_POS;

	      //debug
	      fprintf(stdout,"error07 comma match  currpos = hyp_DECL but prevtok was : ");
	      print_prev_tok_typ(stdout);
	      fprintf(stdout,"error07bis str is %s\n",str_match);
	      //debug_end
	  
	      return;break;
	      
	    }return ;break;
	case PONCT:
	  if(prev_tok_typ == R_PAR)
	    {
	      print_to_buffstr(" ->\n");
	      //print_buffstr_to_file(output_file);
	      prev_tok_typ = PONCT;
	    }else{
	    current_pos = OUT_POS;


	    //debug
	    fprintf(stdout,"error08 ponct match  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error08bis str is %s\n",str_match);
	    //debug_end

	    
	  }
	  return;break;
	case L_PAR:
	  if(prev_tok_typ == PROP_ID)
	    {
	      print_to_buffstr(" ");
	      prev_tok_typ = L_PAR;
	      }
	  else{
	    //error
	    current_pos = OUT_POS;
	    
	    //debug
	    fprintf(stdout,"error09 lpar match  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error09bis str is %s\n",str_match);
	    //debug_end
	  }
	  return;break;
	case R_PAR:
	  if(prev_tok_typ = ID_MATCH)
	    {
	      prev_tok_typ = R_PAR;
	      return;break;
	      }
	  else{
	    //error
	    current_pos = OUT_POS;
	    
	    //debug
	    fprintf(stdout,"error10 rpar match  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error10bis str is %s\n",str_match);
	    //debug_end
	  }return;break;
	default:
	  current_pos = OUT_POS;

	  //debug
	  fprintf(stdout,"error10 rpar match  currpos = hyp_DECL but prevtok was : ");
	  print_prev_tok_typ(stdout);
	  fprintf(stdout,"error10bis str is %s\n",str_match);
	  //debug_end
	}
    }  
	      
  void concl_parse(char *str_match,enum str_type str_match_type)
    {
      char* coq_pred_id;

      switch(str_match_type)
	{
	case ID_MATCH:
	  switch(prev_tok_typ)
	    {
	    case L_PAR:
	      print_to_buffstr(str_match);
	      print_to_buffstr(" ");
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    case DECL_SEP:
	      print_to_buffstr(str_match);
	      print_to_buffstr(" ");
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    default:
	      //error
	      //debug
	      fprintf(stdout,"errorconcl  idmatch  but prevtok was : ");
	      print_prev_tok_typ(stdout);
	      fprintf(stdout,"error06bis str is %s\n",str_match);
	      //debug_end
	      return;break;
	    }
	  break;
	case PROP_ID:
	  if(lookup_prop_id(&coq_pred_id,str_match)&&	prev_tok_typ ==  CONCL_DECL)
	    {
	      print_to_buffstr(coq_pred_id);
	      print_to_buffstr(" ");
	      prev_tok_typ = PROP_ID;
	    }else{
	    //ERROR : back to the outside
	    current_pos = OUT_POS;
	    
	    //debug
	    fprintf(stdout,"error17 propmatch  currpos = concl_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error17bis str is %s\n",str_match);
	    //debug_end
	  }
	  break;
	case DECL_SEP:
	  if(prev_tok_typ == ID_MATCH)
	    {
	      print_to_buffstr(" ");
	      prev_tok_typ = DECL_SEP;return;
	    }
	  else{
	    //debug
	      fprintf(stdout,"error18 comma match  currpos = concl_DECL but prevtok was : ");
	      print_prev_tok_typ(stdout);
	      fprintf(stdout,"error18bis str is %s\n",str_match);
	      //debug_end
	  }return;break;
	case PONCT :
	  //end
	  if(prev_tok_typ == R_PAR)
	    {
	      print_to_buffstr(" .\n");
	      print_buffstr_to_file(output_file);
	      prev_tok_typ = PONCT;
	      current_pos = OUT_POS;
	      
	      //debug
	      fprintf(stdout,"noterror ponct match  currpos = concl_DECL but prevtok was : ");
	      print_prev_tok_typ(stdout);
	      fprintf(stdout,"noterror str is %s\n",str_match);
	      //debug_end
	      
	    }else{
	    
	    current_pos = OUT_POS;

	    //debug
	    fprintf(stdout,"error19 ponct match  currpos = concl_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error19bis str is %s\n",str_match);
	    //debug_end
	  }
	  return;break;
	case L_PAR:
	  if(prev_tok_typ == PROP_ID)
	    {
	      print_to_buffstr(" ");
	      prev_tok_typ = L_PAR;
	      sq_br_open = true;
	      }
	  else{
	    //error
	    current_pos = OUT_POS;
	    
	    //debug
	    fprintf(stdout,"error20 lpar match  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error20bis str is %s\n",str_match);
	    //debug_end
	  }
	  return;break;
	case R_PAR:
	  if(prev_tok_typ = ID_MATCH)
	    {
	      prev_tok_typ = R_PAR;
	      sq_br_open = false;
	      return;break;
	      }
	  else{
	    //error
	    current_pos = OUT_POS;
	    
	    //debug
	    fprintf(stdout,"error10 rpar match  currpos = hyp_DECL but prevtok was : ");
	    print_prev_tok_typ(stdout);
	    fprintf(stdout,"error10bis str is %s\n",str_match);
	    //debug_end
	  }
	default:
	  current_pos = OUT_POS;

	  //debug
	  fprintf(stdout,"error10 rpar match  currpos = hyp_DECL but prevtok was : ");
	  print_prev_tok_typ(stdout);
	  fprintf(stdout,"error10bis str is %s\n",str_match);
	  //debug_end

	  return;break;
	}
    }




	  
  void action_str_dep(char *str_match,enum str_type str_match_type)
    {
      char* coq_pred_id;
      if(str_match_type == PROP_ID && (current_pos == OUT_POS || current_pos == PO_DECL_POS))
	{
	  //do nothing
	  current_pos = OUT_POS;
	  return;
	}
      else{
	  switch(current_pos)
	    {
	    case OUT_POS:
	      if(str_match_type != PO_DECL)
		{
		  return;
		}
	      else{
		po_decl_parse(str_match,str_match_type);
		return;break;
	      }
	      break;
	    case PO_DECL_POS:
	      po_decl_parse(str_match,str_match_type);
	      return;
	      break;
	    case HYP_POS:
	    hyp_parse(str_match,str_match_type);return;
	    break;
	  case CONCL_POS:
	    concl_parse(str_match,str_match_type);return;
	    break;
	    }
	}
    }
  //////////////////////////////////////////////////////////////////////////////////////////////////
     
%}

PO_Decl      "Point"[ \t]+"order:"
Hyp_Decl     "Hypotheses:"
Concl_Decl   "Conclusion:"
P_ID         [a-zA-Z]{1,2}[0-9]*
Pred_id      [a-z][a-z]+

%%
[ \t]+  {      //save curr tok
  

      
}

{PO_Decl}       {
  
  action_str_dep(yytext,PO_DECL);
  
}
{Hyp_Decl}     {
  
  if(current_pos == PO_DECL_POS)
    action_str_dep(yytext,HYP_DECL);
    
  }
{Concl_Decl}   {
  if(current_pos == HYP_POS)
    action_str_dep(yytext,CONCL_DECL);

}
{Pred_id}    {
  if(current_pos != OUT_POS && current_pos != PO_DECL_POS)
    {
      if(sq_br_open)
	{
	  
	  if(current_pos == CONCL_POS)
	    fa_print_sqbr_decl(PROP_ID,yytext);
	  else
	    fprintf(stdout,"errorPREP while sq_br open\n");
	}
      else{
	 action_str_dep(yytext,PROP_ID);
      }
    }
}
{P_ID}  {
  if(current_pos != OUT_POS)
    {
      if(sq_br_open)
	{
	  if(current_pos == CONCL_POS)
	    fa_print_sqbr_decl(ID_MATCH,yytext);
	  else
	    fprintf(stdout,"errorp_id_match while sq_br open and not CONL\n");
	}
      else{
	action_str_dep(yytext,ID_MATCH);
      }
    }
}
{P_ID}{P_ID}   {
  if(current_pos != OUT_POS)
    {
      if(sq_br_open)
	{
	  if(current_pos != PROP_ID && current_pos != OUT_POS)
	    {
	      fa_print_sqbr_decl(PAIR_ID_MATCH,yytext);
	      fprintf(stdout,"P_IDP_ID : %s\n",yytext);
	    }else{
	    if(current_pos == PROP_ID)
	      {
		fprintf(stdout,"P_IDP_ID : %s and pos = PROP_ID\n",yytext);
		exit(1);
	      }
	  }
	}
      else{
	char *dontneed;
	if(lookup_prop_id(&dontneed,yytext))
	  {
	    if(current_pos == HYP_POS || current_pos == CONCL_POS)
	      {
		fa_print_sqbr_decl(PROP_ID,yytext);
		//debug
		fprintf(stdout,"OK : P_IDP_ID : %s and sq_br_open = false\n",yytext);
		//debug_end
	      }
	    else{
	      fprintf(stdout,"ERROR P_IDP_ID : %s and sq_br_open = false\n",yytext);
	      exit(1);
	    }
	  }
      }
    }
  //else ignore ie. current_pos == OUT_POS
  
}


      
[,]   {

  if(current_pos != OUT_POS)
   {
      if(sq_br_open)
	{
	  if(current_pos == CONCL_POS)
	    fa_print_sqbr_decl(DECL_SEP,yytext);
	  else
	    fprintf(stdout,"errorcomma while sq_br open\n");
	}
      else{
	 action_str_dep(yytext,DECL_SEP);
      }
   }
  
}
 
[.]   {
  if(current_pos != OUT_POS)
    action_str_dep(yytext,PONCT);
  
 }
 
[(]   {
    if(current_pos != OUT_POS && current_pos != PO_DECL_POS)
      {
	action_str_dep(yytext,L_PAR);
	//sq_br_open = true;
      }
    
  }
[)]   {
  if(current_pos != OUT_POS && current_pos != PO_DECL_POS)
    action_str_dep(yytext,R_PAR);
  //sq_br_open = false;  

  }

\[    {
  if(current_pos == HYP_DECL)
    fprintf(stdout,"fa decl square bracket within hypdecl\n");
  if(current_pos == CONCL_DECL)
    {
      if(sq_br_open == true)
	fprintf(stdout,"sq_br_open == true while got [\n");
      else{
	sq_br_open = true;
	fad_sbo_n_param = 0;
	//action_str_dep(yytext,SQ_BR_L);
	fa_print_sqbr_decl(SQ_BR_L,yytext);
      }
    }
}

\]   {
  if(current_pos == HYP_DECL)
    fprintf(stdout,"fa decl square bracket within hypdecl\n");
  if(current_pos == CONCL_DECL)
    {
      if(sq_br_open == false)
	fprintf(stdout,"sq_br_open == flase while got ]\n");
      else{
	//action_str_dep(yytext,SQ_BR_R);
	fa_print_sqbr_decl(SQ_BR_R,yytext);
	sq_br_open = false;
      }
    }
}
[0-9]+ {
  if(current_pos == CONCL_DECL)
    {
      fa_print_sqbr_decl(FA_VAL,yytext);
    }
}
\+   {
  if(current_pos == CONCL_DECL)
    {
      fa_print_sqbr_decl(PLUS_MATCH,yytext);
    }
}
\-   {
  if(current_pos == CONCL_DECL)
    {
      fa_print_sqbr_decl(MINUS_MATCH,yytext);
    }
}
\=   {
  if(current_pos == CONCL_DECL)
    {
      fa_print_sqbr_decl(EQUAL_MATCH,yytext);
    }
}
\n   {
  line_number ++;
  

}

.    {

  current_pos = OUT_POS;
  

}
%%

int main(int argc,char **argv)
  {
    output_file = NULL;
    if(argc != 3 && argc != 2)
      {
	fprintf(stderr,"usage : $%s input_filename output_filename\n",argv[0]);
	return 1;
      }
    yyin = fopen(argv[1], "r" );
    if(yyin == NULL)
      {
	perror("fopen in");
	fprintf(stderr,"%s",strerror(errno));
	return 2;
      }
    if(argc == 2)
      {
	output_file = stderr;
      }
    else{
      output_file = fopen(argv[2],"a");
      //fprintf(stderr,"argv2 is %s null is %d\n",argv[2],(int)NULL);
      //yyout = fopen(argv[2],"a");
      if(output_file == NULL);
      {
	perror("fopen out");
	fprintf(stderr,"%s\n",strerror(errno));
	return 3;
      }
    }
    //global var decl
    current_pos = OUT_POS;
    curr_buff_pos = 0;
    line_number = 0;
    lemma_number =0;
    sq_br_open = false;
    fad_sbo_n_param = 0;
    point_order_l = 0;
    
    //parse
    yylex();
    
    return 0;
  }
