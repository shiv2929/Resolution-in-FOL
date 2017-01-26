import ply.lex as lex
import ply.yacc as yacc
import copy
from collections import OrderedDict

explored=[]
constants=[]
variables=[]
session_explored=[]
kb=[]
failure = "failure"
val=" "
hash_table=OrderedDict()
theta=[]
explored_rules=[]
frontier_queue=[]

#***********************************BEGIN PARSING*************************************************
tokens = ["ID","LPAREN","RPAREN","NOT","AND","OR","IMPLIES","COMMA"]

t_ignore = ' \t'
t_NOT = r"~"
t_LPAREN = r"\("
t_RPAREN = r"\)"
t_OR = r"\|"
t_AND = r"&"
t_IMPLIES = r"=>"
t_COMMA = r","

def t_ID(t):
    r'[a-zA-Z]\w*'
    return t

def t_error(t):
    t.lexer.skip(1)

lexer = lex.lex()


def p_formula_binary(p):
    """FORMULA : FORMULA IMPLIES FORMULA
                | FORMULA OR FORMULA
                | FORMULA AND FORMULA
                """
    p[0] = [p[1],p[2],p[3]]#check if this is valid

def p_formula_not(p):
    """FORMULA  : NOT FORMULA
                | NOT TERM"""
    p[0] = [p[1], p[2]]


def p_formula_group(p):
    "FORMULA : LPAREN FORMULA RPAREN"
    p[0] = p[2]

def p_formula_ID(p):
    "FORMULA : TERM"
    p[0] = p[1]

def p_term(p):
    """TERM : ID LPAREN TERMLIST RPAREN
            | ID"""
    p[0] = p[1] if len(p) == 2 else [p[1],p[3]]

def p_termlist(p):
    """TERMLIST : TERM COMMA TERMLIST
                | TERM"""
    if len(p) == 2:
        p[0] = p[1]

    else:
        p[0] = [p[1],p[3]]
    #p[0] = p[1] if len(p) == 2 else [p[1]] + [p[3]]

precedence = (
("right", "IMPLIES"),
("left", "OR"),
("left", "AND"),
("right", "NOT"))

def p_error(p):
    if p is None:
        raise ValueError("Unknown error")
    raise ValueError("Syntax error")

parser = yacc.yacc()
#*******************************************%%%%%%%%%%%END OF PARSING%%%%%%%%%%%%%%%%*****************************************


#***check impliaction exists**

def implication_exists(a):
    if len(a)==3:
        if "=>" in a:
            return True
        else:
            return False

def Or_Exists(a):
    if len(a)==3:
        if "|" in a:
            return True
        else:
            return False

def And_Exists(a):
    if len(a)== 3:
        if "&" in a:
            return True
        else:
            return False

def flatten(a, s):
    for l in a:
        if type(l) == list:
            flatten(l, s)
        else:
            s.append(l)
            #explored.append(l)
    return s


#**** remove implication**********
def implication_removal(logic):
    if len(logic)<=2 and logic[0] != "~":
        return logic
    elif len(logic)==2 and logic[0] == "~":
        if len(logic[1]) == 3:
            if Or_Exists(logic[1]):
                a = []
                #**** "~",(a(x) | b(x))
                first_term = ["~", logic[1][0]]
                middle_term = "&"
                last_term = ["~", logic[1][2]]
                a.append(first_term)
                a.append(middle_term)
                a.append(last_term)
                logic = a
            elif And_Exists(logic[1]):
                b=[]
                first_term = ["~", logic[1][0]]
                middle_term = "|"
                last_term = ["~", logic[1][2]]
                b.append(first_term)
                b.append(middle_term)
                b.append(last_term)
                logic = b
            elif implication_exists(logic[1]):
                c=[]
                first_term = logic[1][0]
                middle_term = "&"
                last_term = ["~", logic[1][2]]  #improve for ~b
                c.append(first_term)
                c.append(middle_term)
                c.append(last_term)
                logic = c
        elif len(logic[1])==2:
            if logic[1][0] == "~":
                logic = logic[1][1]

    if len(logic)== 2 and logic[0]=="~":
        if len(logic[1])==2 and logic[1][0]=="~":
            logic = implication_removal(logic)
        if len(logic[1]) == 3:
            if Or_Exists(logic[1]):
                a = []
                #**** "~",(a(x) | b(x))
                first_term = ["~", logic[1][0]]
                middle_term = "&"
                last_term = ["~", logic[1][2]]
                a.append(first_term)
                a.append(middle_term)
                a.append(last_term)
                logic = a
            elif And_Exists(logic[1]):
                b=[]
                first_term = ["~", logic[1][0]]
                middle_term = "|"
                last_term = ["~", logic[1][2]]
                b.append(first_term)
                b.append(middle_term)
                b.append(last_term)
                logic = b
            elif implication_exists(logic[1]):
                c=[]
                first_term = logic[1][0]
                middle_term = "&"
                last_term = ["~", logic[1][2]]  #improve for ~b
                c.append(first_term)
                c.append(middle_term)
                c.append(last_term)
                logic = c

    if len(logic)==3:
        if implication_exists(logic):
            d = []
            first_term = ["~",logic[0]]
            middle_term = "|"
            last_term = logic[2]
            d.append(first_term)
            d.append(middle_term)
            d.append(last_term)
            logic = d

    for j in range(len(logic)):

        if len(logic[j])>1:
            logic[j] = implication_removal(logic[j])
    return logic

def OrAnd_Check(a):
    if "|" in a:
        if ("&" in a[0]) or ("&" in a[2]):
            return True
        else:
            return False


def distribution_Or_And(logic):

    if len(logic)<3:
        pass
    elif len(logic) == 3:
        if OrAnd_Check(logic):
            if len(logic[0])!=3 and len(logic[2])==3:
                new_logic_1=[]
                f_term=[logic[0],"|",logic[2][0]]
                s_term="&"
                th_term=[logic[0],"|",logic[2][2]]
                new_logic_1.append(f_term)
                new_logic_1.append(s_term)
                new_logic_1.append(th_term)
                logic = new_logic_1

            elif len(logic[0])==3 and len(logic[2])!=3:
                new_logic_2 = []
                f_term = [logic[0][0], "|", logic[2]]
                s_term = "&"
                th_term = [logic[0][2], "|", logic[2]]
                new_logic_2.append(f_term)
                new_logic_2.append(s_term)
                new_logic_2.append(th_term)
                logic = new_logic_2

            elif len(logic[0])==3 and len(logic[2])==3:
                if ("&" in logic[0]) and ("&" in logic[2]):
                    new_logic_3=[]
                    f_term = [[logic[0][0],"|", logic[2][0]],"&",[logic[0][0],"|",logic[2][2]]]
                    s_term = "&"
                    th_term = [[logic[0][2],"|", logic[2][0]],"&",[logic[0][2],"|",logic[2][2]]]
                    new_logic_3.append(f_term)
                    new_logic_3.append(s_term)
                    new_logic_3.append(th_term)
                    logic = new_logic_3

                elif ("&" not in logic[0]) and ("&" in logic[2]):
                    new_logic_4=[]
                    f_term = [logic[0], "|", logic[2][0]]
                    s_term = "&"
                    th_term = [logic[0], "|", logic[2][2]]
                    new_logic_4.append(f_term)
                    new_logic_4.append(s_term)
                    new_logic_4.append(th_term)
                    logic = new_logic_4

                elif ("&" in logic[0]) and ("&" not in logic[2]):
                    new_logic_5=[]
                    f_term = [logic[0][0], "|", logic[2]]
                    s_term = "&"
                    th_term = [logic[0][2], "|", logic[2]]
                    new_logic_5.append(f_term)
                    new_logic_5.append(s_term)
                    new_logic_5.append(th_term)
                    logic = new_logic_5

    for j in range(len(logic)):
        if len(logic[j])>1:
            logic[j] = distribution_Or_And(logic[j])

    if OrAnd_Check(logic):
        logic = distribution_Or_And(logic)

    return logic

def flattening(logic):
    if len(logic)==2:
        if logic[0]== "~":
            s=[]
            if len(logic[1][1])>2:
                logic[1][1] = [logic[1][1]]

            elif len(logic[1][1])==2:

                if type(logic[1][1])==list:
                    m = flatten(logic[1][1], s)
                    logic[1][1] = m
                else:
                    logic[1][1]=[logic[1][1]]
            else:
                m = flatten(logic[1][1], s)
                logic[1][1] = m

        else:
            s=[]
            if len(logic[1])>2:
                logic[1] = [logic[1]]

            elif len(logic[1])==2:
                if type(logic[1])==list:
                    m = flatten(logic[1], s)
                    logic[1] = m
                else:
                    logic[1]=[logic[1]]

            else:
                m = flatten(logic[1], s)
                logic[1] = m

    if len(logic)==3:
        for p in range(len(logic)):
            if len(logic[p])>1:
                logic[p]= flattening(logic[p])
    return logic

def variable_generator(variables):
    s=[]
    length = len(explored)
    for var in variables:
        if var[0].isupper():
            constants.append(var)
            s.append(var)
        else:
            if var in explored:

                new_var = var + str(length)
                s.append(new_var)
                session_explored.append(new_var)
            else:
                new_var=var
                s.append(new_var)
                session_explored.append(new_var)
    return s


def standardiztion(logic):
    if len(logic)==2:
        if logic[0]== "~":
            n = variable_generator(logic[1][1])
            logic[1][1]=n

        else:
            n = variable_generator(logic[1])
            logic[1]=n

    if len(logic)==3:
        for u in range(len(logic)):
            if len(logic[u])>1:
                logic[u]= standardiztion(logic[u])
    return logic

##***********CLEAN UP**********
def cleanuplogiccandidate(a):
    if len(a)>3:
        for el in a:
            if len(a)>1:
                if len(el)==3:
                    sign_to_check = a[1]
                    if sign_to_check in el:
                        return True
                    else:
                        return False
    else:
        return False


def cleanUp(logic):
    if len(logic)==3:
        sign = logic[1]
        if len(logic[0])!=3 and len(logic[2])==3: #A&(B&C) or (A|(B|C)) or negations of them
            if sign in logic[2]:
                term_1 = [logic[0],logic[1],logic[2][0],logic[2][1],logic[2][2]]
                logic=term_1
        elif len(logic[0])==3 and len(logic[2])!=3:
            if sign in logic[0]:
                term_2 = [logic[0][0],logic[0][1],logic[0][2],logic[1],logic[2]]
                logic = term_2
        elif len(logic[0])==3 and len(logic[2])==3:
            if (sign in logic[0]) and (sign in logic[2]):
                term_3 = [logic[0][0],logic[0][1],logic[0][2],logic[1],logic[2][0],logic[2][1],logic[2][2]]
                logic = term_3
            elif (sign in logic[0]) and (sign not in logic[2]):
                term_4 = [logic[0][0],logic[0][1],logic[0][2],logic[1],logic[2]]
                logic = term_4
            elif (sign not in logic[0]) and (sign in logic[2]):
                term_5 = [logic[0],logic[1],logic[2][0],logic[2][1],logic[2][2]]
                logic=term_5

    for j in range(len(logic)):
        if len(logic[j])>1:
            logic[j] = cleanUp(logic[j])


    if cleanuplogiccandidate(logic):
        for element in logic:
            new_logic = []
            if len(element) == 3:
                position = logic.index(element)

                length = len(logic)
                for c in range(length):
                    if c == position:
                        new_term_1 = logic[position][0]
                        new_term_2 = logic[position][1]
                        new_term_3 = logic[position][2]
                        new_logic.append(new_term_1)
                        new_logic.append(new_term_2)
                        new_logic.append(new_term_3)
                    else:
                        new_logic.append(logic[c])

                logic = new_logic
    return logic

#*****************UNIFICATION*********************
def x_isVariable(x):
    if type(x) != list and x.islower():
        return True
    else:
        return False

def unify(x,y,theta):
    if theta == failure:
        return failure
    elif x == y:
        return theta
    elif x_isVariable(x):
        return unify_var(x,y,theta)
    elif x_isVariable(y):
        return unify_var(y,x,theta)
    elif type(x)==list and type(y)==list:
        x_cpy=copy.deepcopy(x)
        y_cpy=copy.deepcopy(y)
        first_x=x_cpy.pop(0)
        first_y=y_cpy.pop(0)
        return unify(x_cpy,y_cpy,unify(first_x,first_y,theta))
    else:
        return failure

def unify_var(var,x,theta):
    if [var,val] in theta:
        return unify(val,x,theta)
    elif [x,val] in theta:
        return unify(var,val,theta)
    else:
        return add_to_theta(var,x,theta)

def add_to_theta(var,val,theta):
    subs=[var,val]
    theta.append(subs)
    return theta

def substitution(clause,out_theta):
    if len(clause)==2:
        if clause[0]=="~":
            arguments = clause[1][1]
        else:
            arguments = clause[1]
        for j in range(len(arguments)):
            for l in out_theta:
                if arguments[j] == l[0]:
                    arguments[j] = l[1]
    else:
        for term in clause:
            if len(term) > 1:
                if term[0] == "~":
                    arguments = term[1][1]
                else:
                    arguments = term[1]

                for j in range(len(arguments)):
                    for l in out_theta:
                        if arguments[j] == l[0]:
                            arguments[j] = l[1]


    return clause


def resolution(clause_1,clause_2,pr_chk,quer_pred):
    if len(clause_2)<=2:        #single predicate
        clause_2=[]
    elif len(clause_2)>2:

        for el_11 in clause_2:
            if len(el_11)>1:
                if el_11[0]=="~":
                    if el_11[1][0]==pr_chk:
                        val_2 = "~" + pr_chk
                        if val_2 != quer_pred:
                            pos_2 = clause_2.index(el_11)
                            if pos_2 != len(clause_2) - 1:
                                clause_2.pop(pos_2)
                                clause_2.pop(pos_2)
                                break
                            elif pos_2 == len(clause_2)-1:
                                clause_2.pop(pos_2)
                                clause_2.pop(pos_2-1)
                                break

                elif el_11[0]==pr_chk:
                    val_2 = pr_chk
                    if val_2 != quer_pred:
                        pos_2 = clause_2.index(el_11)
                        if pos_2 != len(clause_2) - 1:
                            clause_2.pop(pos_2)
                            clause_2.pop(pos_2)
                            break
                        elif pos_2 == len(clause_2) - 1:
                            clause_2.pop(pos_2)
                            clause_2.pop(pos_2 - 1)
                            break



    if len(clause_1)<=2:
        clause_1=[]
    elif len(clause_1)>2:
        for el_21 in clause_1:
            if len(el_21)>1:
                if el_21[0]=="~":
                    if el_21[1][0]==pr_chk:
                        value_1 = "~"+pr_chk
                        if value_1 == quer_pred:
                            pos_5 = clause_1.index(el_21)
                            if pos_5 != len(clause_1)-1:
                                clause_1.pop(pos_5)
                                clause_1.pop(pos_5)
                                break
                            elif pos_5 == len(clause_1)-1:
                                clause_1.pop(pos_5)
                                clause_1.pop(pos_5-1)
                                break

                elif el_21[0]==pr_chk:
                    value_1 = pr_chk
                    if value_1 == quer_pred:
                        pos_5 = clause_1.index(el_21)
                        if pos_5 != len(clause_1)-1:
                            clause_1.pop(pos_5)
                            clause_1.pop(pos_5)
                            break
                        elif pos_5 ==len(clause_1)-1:
                            clause_1.pop(pos_5)
                            clause_1.pop(pos_5 - 1)
                            break
    if clause_1 ==[] or clause_2 == []:
        resolved_clause = clause_2+clause_1
    else:
        resolved_clause = clause_2+["|"]+clause_1
    return resolved_clause


def main_resolution(clause):
    x=0
    querry_predicate=0
    clause_2 = copy.deepcopy(clause)
    if len(clause)<=2:
        if clause[0]=="~":
            querry_predicate = clause[1][0]
            pred_check = querry_predicate
            x=clause[1][1]
        else:
            querry_predicate = "~"+clause[0]
            pred_check = clause[0]
            x=clause[1]
    else:
        each_term = clause[0]
        if each_term[0]=="~":
            querry_predicate = each_term[1][0]
            pred_check = querry_predicate
            x = each_term [1][1]
        else:
            querry_predicate = "~"+each_term[0]
            pred_check = each_term[0]
            x = each_term[1]

    if type(x) == list and len(x) == 1:
        x = x[0]
    y=0
    if (querry_predicate)in hash_table:
        frontier = hash_table[querry_predicate]
    else:
        frontier = []
    queue=[]
    new_queue=[]
    length = len(frontier)
    for clause_in_frontier in frontier: #runs as per initial length of frontier or possible unification statements and gives unified statements
        clause_1 = copy.deepcopy(clause_in_frontier)
        clause_2 = copy.deepcopy(clause)
        if len(clause_1)>2:
            for element in clause_1:
                if element[0]=="~":
                    if element[1][0] == pred_check:
                        y=element[1][1]
                else:
                    if element[0] == pred_check:
                        y= element[1]
        else:
            if clause_1[0]=="~":
                if clause_1[1][0]==pred_check:
                    y= clause_1[1][1]
            else:
                if clause_1[0]== pred_check:
                    y=clause_1[1]


        if type(y) == list and len(y) == 1:
            y = y[0]
        out = unify(x, y, theta=[])
        if out!= failure:
            resolved = resolution(clause_1,clause_2,pred_check,querry_predicate)
            if resolved == []:
                return  "TRUE"
            op = substitution(resolved,out)
            if op not in explored_rules:
                explored_rules.append(op)
                if len(op)>2:
                    queue.append(op)
                else:
                    queue=queue+op

    if [] in queue:
        return "TRUE"
    else:
        for new_items in queue:
            new_clause = new_items
            k = main_resolution(new_clause)
            if k == "TRUE":
                k="TRUE"
                return k

#********MAIN************
in_file = open("input.txt","r")
out_file = open("output.txt", "w")
no_queries = int(in_file.readline().split('\n')[0])
queries = []
rules = []

for i in range(no_queries):
    d=in_file.readline().split('\n')[0]
    question = parser.parse(str(d))
    question_after_flattening = flattening(question)
    question_after_standardization = standardiztion(question_after_flattening)
    queries.append(question_after_standardization)

no_rules = int(in_file.readline().split('\n')[0])

for j in range(no_rules):

    c=in_file.readline().split('\n')[0]
    res = parser.parse(str(c)) #((A=>B)|C) ((A(X) => B(X))|C(X))
    rules.append(res)
    res_after_implication_removal = implication_removal(res)
    res_after_flattening = flattening(res_after_implication_removal)
    res_after_standardization = standardiztion(res_after_flattening)
    explored = explored + session_explored
    session_explored=[]
    res_after_or_over_and = distribution_Or_And(res_after_standardization)
    res_after_clean_up = cleanUp(res_after_or_over_and)
    if "&" in res_after_clean_up:
        for each_element in res_after_clean_up:
            if each_element != "&":
                kb.append(each_element)
    else:
        kb.append(res_after_clean_up)

for individual_rule in kb:
    #out_file.write(str(individual_rule))
    #out_file.write('\n')
    if len(individual_rule)==2:
        if individual_rule[0]=="~":
            predicate_to_sort = "~"+individual_rule[1][0]
        else:
            predicate_to_sort = individual_rule[0]
        if predicate_to_sort not in hash_table.keys():
            hash_table[predicate_to_sort] = [individual_rule]
        else:
            hash_table[predicate_to_sort] = hash_table[predicate_to_sort] + [individual_rule]

    else:
        for expression in individual_rule:

                if len(expression)>1:
                    if expression[0]=="~":
                        predicate_to_sort = "~"+expression[1][0]
                    else:
                        predicate_to_sort = expression[0]

                    if predicate_to_sort not in hash_table.keys():
                        hash_table[predicate_to_sort]=[individual_rule]
                    else:
                        hash_table[predicate_to_sort]=hash_table[predicate_to_sort]+[individual_rule]

#********* TO CHECK unification*****

#***select query 1 and negate it, find the predicate for query**

for clause_2 in queries:
    if clause_2[0]=="~":
        clause_2=clause_2[1]

    else:
        h=[]
        F_term = "~"
        S_term = clause_2
        h.append(F_term)
        h.append(S_term)
        clause_2=h

    res_after_main_resolution = main_resolution(clause_2)
    if res_after_main_resolution != "TRUE":
        res_after_main_resolution = "FALSE"

    out_file.write(str(res_after_main_resolution)+'\n')

#*****CNF Conversion******

in_file.close()
out_file.close()