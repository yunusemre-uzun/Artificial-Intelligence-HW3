class Node:
    def __init__(self,data,node_type,parent):
        self.parent = parent
        self.type = node_type
        self.data = data
        self.children = []

    def add_child(self,node):
        self.children.append(node)
    
    def apply_mapping(self,mapping):
        stack = []
        stack.append(self)
        for child in self.children:
            child.apply_mapping(mapping)
        if(self.data in mapping):
            self.data = mapping[self.data]
            if(ord(self.data)>96 and ord(self.data)<123):
                self.type = "variable"
            else:
                self.type = "constant"
    
    def check_equal(self,clause):
        if(self.data == clause.data):
            if(len(self.children) != len(clause.children)):
                return False
            elif(len(self.children) == 0):
                return True
            else:
                flag = True
                for i in range(len(self.children)):
                    flag = flag and self.children[i].check_equal(clause.children[i])
                return flag
        else:
            return False


def theorem_prover(base_clauses, obtained_clauses):
    copied_base_clauses = base_clauses[0::]
    unification_mapping = unify_clauses(base_clauses)
    if(unification_mapping):
        (base_clauses,obtained_clauses) = change_clauses(base_clauses,obtained_clauses,unification_mapping)
        set_of_support = obtained_clauses
        (res,resolvents) = resolution(base_clauses,set_of_support)
        print_resolvents = []
        for resolvent in resolvents:
            if(resolvent[2]==""):
                print_resolvents.append(set_of_support[resolvent[1]]+"$"+copied_base_clauses[resolvent[0]]+"$empty")
            else:
                print_resolvents.append(set_of_support[resolvent[1]]+"$"+copied_base_clauses[resolvent[0]]+"$"+resolvent[2])
        if(res):
            return ("yes", print_resolvents)
        else:
            return ("no", [])

def change_clauses(base_clauses,obtained_clauses,unification_mapping):
    for key in unification_mapping:
        for i in range(len(base_clauses)):
            base_clauses[i] = base_clauses[i].replace(key,unification_mapping[key])
        for i in range(len(obtained_clauses)):
            obtained_clauses[i] =  obtained_clauses[i].replace(key,unification_mapping[key])
    return (base_clauses,obtained_clauses)

def resolution(base_clauses,set_of_support):
    new = []
    return_resolvents = []
    while(True):
        new = []
        for i in range(len(base_clauses)-1,-1,-1):
            for j in range(len(set_of_support)-1,-1,-1):
                resolvents = resolve(base_clauses[i],set_of_support[j])
                if(len(resolvents)>0):
                    set_of_support.append(resolvents[0])
                    return_resolvents.append((i,j,resolvents[0]))
                    if("" in resolvents):
                        return (True,return_resolvents)
                    else:
                        new = list(set(new) | set(resolvents))
        if(len(set(new).difference(set(base_clauses)))==0):
            return (False,None)
        else:
            base_clauses = list(set(new) | set(base_clauses))
    return None

def resolve(clause_1,clause_2):
    resolvents = []
    clause_1 = clause_1.split("+")
    clause_2 = clause_2.split("+")
    parsed_clause_1 = parse_function(clause_1)
    parsed_clause_2 = parse_function(clause_2)
    for i in parsed_clause_1:
        for j in parsed_clause_2:
            if(check_negated(i,j)):
                c = ""
                for k in clause_1:
                    if(parse_function([k])[0].check_equal(i)):
                        continue
                    else:
                        c += "+{}".format(k)
                for k in clause_2:
                    if(parse_function([k])[0].check_equal(j)):
                        continue
                    else:
                        c += "+{}".format(k)
                c = c[1::]
                resolvents = list(set(resolvents) | set([c]))
    return resolvents

def check_negated(clause_1,clause_2):
    if(clause_1.data=="~" and clause_2.data !="~") or (clause_1.data!="~" and clause_2.data=="~"):
        if(clause_1.data=="~"):
            clause_1 = clause_1.children[0]
        else:
            clause_2 = clause_2.children[0]
        return clause_1.check_equal(clause_2)
    else:
        return False

def extract_functions(base_clauses):
    clause_list = []
    for clause in base_clauses:
        splitted_clauses = clause.split('+')
        for new_clause in splitted_clauses:
            new_clause = new_clause.replace("~","")
            clause_list.append(new_clause)
    clause_list.sort()
    return clause_list

def parse_function(functions):
    parsed_functions = []
    for function in functions:
        root = None
        current_parent = None
        for i in range(len(function)):
            if(function[i] == "~"):
                if(root==None):
                    neg = Node("~","negation",None)
                    root = neg
                    current_parent = neg
                else:
                    neg = Node("~","negation",current_parent)
                    current_parent.add_child(neg)
                    current_parent = neg
                    
            elif(function[i] == "+"):
                if(current_parent.parent == None):
                    disjunct = Node("+","disjunction", None )
                    disjunct.add_child(current_parent)
                    current_parent.parent = disjunct
                    current_parent = disjunct
                    root = disjunct
                else:
                    disjunct = Node("+","disjunction", current_parent.parent )
                    current_parent.parent.add_child(disjunct)
                    disjunct.add_child(current_parent)
                    current_parent.parent = disjunct
                    current_parent = disjunct
            elif(ord(function[i])>96 and ord(function[i])<123): # if it is a lower-case character
                if(function[i+1]=="("): # it is a function
                    if(root == None): # if it is root
                        root = Node(function[i],"function",None)
                        current_parent = root
                    else:
                        child_function = Node(function[i],"function",current_parent)
                        current_parent.add_child(child_function)
                        current_parent = child_function
                elif(function[i+1]=="," or function[i+1]==")"): # it is function argument
                   child = Node(function[i],"variable",current_parent)
                   current_parent.add_child(child)
                elif(function[i+1]==")"): # if the paranthese close, change the parent to the upper level
                    current_parent = current_parent.parent
            elif(ord(function[i])>64 and ord(function[i])<91): # if it is a upper-case character
                child = Node(function[i],"constant",current_parent)
                current_parent.add_child(child)
        parsed_functions.append(root)
    return parsed_functions

def unify_functions(parsed_functions):
    variable_mapping = {}
    for i in range(len(parsed_functions)-1):
        function_1 = parsed_functions[i]
        function_2 = parsed_functions[i+1]
        if(function_1.data == function_2.data): # if they are the same functions
            new_mapping = unify_functions_helper(function_1,function_2)
            if(new_mapping):
                variable_mapping.update(new_mapping)
            else:
                return False
            apply_mapping(parsed_functions,variable_mapping)
    return variable_mapping

def unify_functions_helper(function_1,function_2):
    variable_mapping = {}
    if(function_1.type == "variable" and function_2.type == "constant"):
        variable_mapping[function_1.data] = function_2.data
    elif(function_1.type == "constant" and function_2.type == "variable"):
        variable_mapping[function_2.data] = function_1.data
    elif(function_1.type == "variable" and function_2.type == "variable"):
        variable_mapping[function_2.data] = function_1.data
    elif(function_1.type == "function" and function_2.type == "function" and function_1.data == function_2.data):
        for i in range(len(function_1.children)):
            result = unify_functions_helper(function_1.children[i],function_2.children[i])
            if(result):
                variable_mapping.update(unify_functions_helper(function_1.children[i],function_2.children[i]))
            else:
                 return False
    else:
        return False
    return variable_mapping

def apply_mapping(parsed_functions,variable_mapping):
    mapped_functions = []
    for function in parsed_functions:
        mapped_function = function.apply_mapping(variable_mapping)
        mapped_functions.append(mapped_function)
    return mapped_functions

def unify_clauses(base_clauses):
    functions = extract_functions(base_clauses)
    parsed_functions = parse_function(functions)
    unification_mapping = unify_functions(parsed_functions)
    return unification_mapping

if __name__ == "__main__":
    print theorem_prover(["p(A,f(t))" , "q(z)+~p(z,f(B))" , "~q(y)+r(y)"] , ["~r(A)"])
