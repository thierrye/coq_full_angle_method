%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
  
#define MAX_STR_BUFF_SIZE 500
  
#define POINT_TYPE_STR ": FA_Point,\n"
#define PO_DECL_STR "forall "
#define PRED_NUMBER 13
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
  enum str_type { PO_DECL , ID_MATCH , HYP_DECL , CONCL_DECL , PONCT , DECL_SEP , PROP_ID , L_PAR , R_PAR } prev_tok_typ;
  
  char curr_str_buff[MAX_STR_BUFF_SIZE];
  //  char prev_tok[MAX_STR_BUFF_SIZE];
  int curr_buff_pos;
  FILE* output_file;
  int line_number;

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
  void print_to_buffstr(int beginning,char* tok_str_)
    {
      curr_buff_pos = beginning;
      strcpy(curr_str_buff+curr_buff_pos,tok_str_);
      curr_buff_pos += strlen(tok_str_);
      if(curr_buff_pos > MAX_STR_BUFF_SIZE -2)
	{
	  fprintf(stderr,"to long str -> exiting\n");
	  exit(1);
	}
    }
  void print_buffstr_to_file(FILE *outfile)
    {
      fprintf(outfile,"%s",curr_str_buff);
      curr_buff_pos = 0;
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
  void po_decl_parse(char *str_match,enum str_type str_match_type)
    {
      switch(str_match_type)
	{
	case PO_DECL:
	  print_to_buffstr(0,PO_DECL_STR);
	  current_pos = PO_DECL_POS;
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
	      print_to_buffstr(curr_buff_pos,str_match);
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    case DECL_SEP:
	      print_to_buffstr(curr_buff_pos,str_match);
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
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos,POINT_TYPE_STR);
	      //print_to_buffstr(curr_buff_pos,",\n");
	      print_buffstr_to_file(output_file);
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
	      print_to_buffstr(curr_buff_pos,str_match);
	      print_to_buffstr(curr_buff_pos," ");
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    case DECL_SEP:
	      print_to_buffstr(curr_buff_pos,str_match);
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos,coq_pred_id);
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos," ");
	      prev_tok_typ = DECL_SEP;return;
	      break;
	    case R_PAR://next token should be PROP_ID
	      print_to_buffstr(curr_buff_pos," ->");
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
	      print_to_buffstr(curr_buff_pos," ->\n");
	      print_buffstr_to_file(output_file);
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
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos,str_match);
	      print_to_buffstr(curr_buff_pos," ");
	      prev_tok_typ = ID_MATCH;return;
	      break;
	    case DECL_SEP:
	      print_to_buffstr(curr_buff_pos,str_match);
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos,coq_pred_id);
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos," ");
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
	      print_to_buffstr(curr_buff_pos," .\n");
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
	      print_to_buffstr(curr_buff_pos," ");
	      prev_tok_typ = L_PAR;
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
		print_to_buffstr(0,PO_DECL_STR);
		current_pos = PO_DECL_POS;
		prev_tok_typ = PO_DECL;return;
		return;
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
  
  
  action_str_dep(yytext,HYP_DECL);
  

  
  }
{Concl_Decl}   {
  action_str_dep(yytext,CONCL_DECL);

  

}
{Pred_id}    {
  if(current_pos != OUT_POS || current_pos != PO_DECL_POS)
    {
      action_str_dep(yytext,PROP_ID);
    }
}
{P_ID}  {
    action_str_dep(yytext,ID_MATCH);
  
}
[,]   {

  
  action_str_dep(yytext,DECL_SEP);
  
  
}
 
[.]   {

  action_str_dep(yytext,PONCT);
  
 }
 
[(]   {
    action_str_dep(yytext,L_PAR);
    
  }
[)]   {
  action_str_dep(yytext,R_PAR);
  

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

    //parse
    yylex();
    
    return 0;
  }
