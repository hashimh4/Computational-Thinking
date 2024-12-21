###############################################################################################################
##########################################QUESTION 3###########################################################
###############################################################################################################
# Load the text file, after putting the file location
import time

fileLocation = "C:/Users/hashi/Documents/Logic Coursework/8queens.txt"
file = open(fileLocation, 'r')

clauseSet = []
header = True

# Remove the spaces, the zero indicating a new line, and create a new list within the list for each clause set
for line in file:
    strip = line.strip()
    clause = strip.split()
    if header == False:
        clause = clause[:-1]
    clauseSet.append(clause)
    header = False
file.close()

# Save the number of variables and clause sets in this text file. (We could check whether these are actually correct)
header = clauseSet[0]
number_of_variables = int(header[2])
number_of_sets = int(header[3])

# Remove the header
clauseSet.pop(0)

# Convert all the items in the list into integers
clauseSet = [[int(float(clause)) for clause in clauses] for clauses in clauseSet]

###############################################################################################################
##########################################QUESTION 4###########################################################
###############################################################################################################
import itertools


# We pass the clause set through and a satisfying assignment is outputted
def simple_sat_solve(clause_set):
    # Use itertools to add all the possible truth assignments to a list
    combinations = []
    fin_evaluation1 = []
    fin_evaluation2 = []
    number_of_variables = 0
    for clause in clause_set:
        for literal in clause:
            if abs(literal) > number_of_variables:
                number_of_variables = abs(literal)
    for p in itertools.product([True, False], repeat=number_of_variables):
        combinations.append(p)

    # See what each combination of truth assignments evaluates to

    # Check if it's less than 0, mod it and find it in the list.
    # -1 is not truth_assignment[0]

    for combination in combinations:
        # Go through the formula
        fin_evaluation1 = []
        for clause in clause_set:
            evaluation = []
            for literal in clause:
                negate = False
                if literal < 0:
                    negate = True
                    literal = abs(literal)
                # Find the correct combination and then add it to a list, remembering to negate it where applicable
                if negate == True:
                    evaluation.append(not combination[literal - 1])
                if negate == False:
                    evaluation.append(combination[literal - 1])
            # Or all these together and add to another list, which we will and at the end to see what we get
            fin_evaluation1.append(any(evaluation))
        # And everything we have evaluated so far, for this particular combination (of T's and F's). If we get 'True' here, then the formula is satisfiable
        if all(fin_evaluation1) == True:
            fin_evaluation2.append(combination)

    # If there is a satifying truth assignment, just one is printed
    if fin_evaluation2 != []:
        for i in fin_evaluation2:
            return i
    #        return fin_evaluation2
    else:
        return "UNSAT"


###############################################################################################################
##########################################QUESTION 5###########################################################
###############################################################################################################
import copy
import sys

end = False
first_loop = True
new_array = []
real_partial = []


def branching_sat_solve(clause_set, partial_assignment):  # Partial assignement will be an array
    #    print("CLAUSE SET:", clause_set)
    #    print("PARTIAL ASSIGNMENT:", partial_assignment)

    global end
    global first_loop
    global new_array
    global real_partial

    # PART 1: If we get nothing at the end, after assigning all the variables, then the formula is SAT. Go back a step if we get False. If we have tried every route, then the formula is UNSAT
    # Find the number of variables (or we could use the information at the top of the DIMACS file)
    number_of_variables = 0
    for clause in clause_set:
        for literal in clause:
            if abs(literal) > number_of_variables:
                number_of_variables = abs(literal)

    partial_assignment_original = list(range(1, number_of_variables + 1))

    # If we find the inputted partial_assignment cannot hold, then print UNSAT
    for i in partial_assignment:
        if abs(i) > number_of_variables:
            end = True
            new_array = ["UNSAT"]
            return new_array

    if first_loop == True:
        real_partial = copy.deepcopy(partial_assignment)
        for index, i in enumerate(partial_assignment_original):
            for j in partial_assignment:
                if abs(j) == i:
                    del partial_assignment_original[index]
                    partial_assignment_original.insert(0, j)
        partial_assignment = partial_assignment_original
        first_loop = False

    clause_set_original = copy.deepcopy(clause_set)
    new_clause_set = copy.deepcopy(clause_set)
    partial_assignment_prev = copy.deepcopy(partial_assignment)
    n = 0
    case = False
    i = 0
    index = 0
    end_break = False

    # Simplyify the formula and check if we get True (then exit), otherwise try a different assignment
    # PART 2: If there is a partial assignment, sub the partial assignments into the clause set (e.g. x1 = True, x4 = False). Simplify where we see (something AND False = False) and (something OR True = True)
    # (We could do set(clause) for each clause)
    def simplifying(clauseSet, variable):
        #        print("ORIGINAL ORIGINAL:", clauseSet)
        newClauseSet = copy.deepcopy(clauseSet)
        for clause in list(newClauseSet):
            for index, literal in enumerate(clause):
                # Remove this clause, as this clause will evaluate to True, if there is a True in it. So if we are left with an empty set at the end, it is satisfiable
                if int(literal) == int(variable):
                    try:
                        newClauseSet.remove(clause)  # CHECK CONDITIONS OF SIMPLIFYING
                    except:
                        pass
                # Replace negative literal with False
                if int(-literal) == int(variable):  # and PARTIAL VARIABLES ARE SATISFIED, ELSE CONTINUE:
                    #                    print(clause)
                    clause[index] = False  # WORKS, bit above doesn't always work
        #        print("ORIGINAL:", clauseSet)
        #        print("NEW:", newClauseSet)
        return newClauseSet

    # PART 3: Now we want to check each clause can hold
    # We do not want any clauses to evaluate to false, as once we AND the entire formula, it will be unsatisfied
    # Go through each of the variables, starting from the first one. (We could remove the initial partially assigned ones from a list from 1 to n)
    # Checks the conditions for when we need to go back a step
    def falsity(clauseSet):
        for clause in clauseSet:
            # If we get a clause evaluating to False, go back a step, as the whole thing will be False
            if any(clause) == False:
                return True
            # If we get a contradiction between two clauses, go back a step
            for others in clauseSet:
                if len(clause) == 1 and len(others) == 1:
                    if clause[0] == -others[0]:
                        return True
        #        print(partial_assignment)
        if clauseSet == [] and all(elem in partial_assignment for elem in
                                   real_partial):  # and all(elem in clauseSet for elem in real_partial) == True
            partial_assignment_print = sorted(partial_assignment, key=abs)
            global new_array
            new_array = []
            for i in partial_assignment_print:
                if i > 0:
                    new_array.append(True)
                if i < 0:
                    new_array.append(False)
            #            print(new_array)
            global end
            end = True
            return False
        else:
            return False

    # PART 4: Piecing everything together and backtracking through recursion when necessary
    if end == False:
        for index, i in enumerate(partial_assignment):
            if end == True:
                break

            if type(i) == int and end == False:
                # Base case
                #        if i!=0 and all(z < 0 for z in partial_assignment[:(index )]) == True:
                #            print(partial_assignment[:(index)])
                #        return
                # Simplify for each assignment until we encounter an error
                #        print(partial_assignment)
                if not falsity(new_clause_set) == True and end == False:
                    #            print(i)
                    new_clause_set = simplifying(new_clause_set, int(i))
                #            print(new_clause_set)
                # If we don't encounter an error, then print the solution
                #        if abs(i) >= number_of_variables + 1:
                #            return partial_assignment

                # Make a change and try again by backtracking (CHECK CONDITIONS FOR WHEN TO ESCAPE AND JUST PRINT UNSAT)
                if falsity(new_clause_set) == True and end == False:
                    #            print("SCREAM")

                    if partial_assignment[index] > 0:
                        #                print("INDEX:", index - 1)
                        #                print(clause_set)
                        #                print(new_clause_set)
                        #                print(clause_set_original)
                        partial_assignment[index] = int(-i)
                        #                print(partial_assignment)
                        try:
                            branching_sat_solve(clause_set_original, partial_assignment)
                        except:
                            end = True
                            if len(new_array) == 0:
                                new_array = ["UNSAT"]
                                return "UNSAT"
                            break
                            # If you save the bit before, you can make it quicker maybe by changing what you sub in here

                    # CHECK THAT ALL THIS WORKS
                    if partial_assignment[index] < 0 and end == False:
                        #                print(partial_assignment)

                        while case == False and n <= index:  # Find the closest one before that isn't negative. Set it to negative. Set all the ones after it to positive. If they're all negative then UNSAT
                            #                    print("INDEX", index-n)
                            #                    print(partial_assignment[index - n])
                            #                    print(n)
                            if partial_assignment[index - n] < 0 and n <= index:
                                #                        print("YES")
                                n = n + 1
                                case = False
                            #                        print("HI", partial_assignment[index - n])
                            if partial_assignment[index - n] > 0 and n <= index:
                                #                        print("HI FINAL", partial_assignment[index - n])
                                #                        print("YES AGAIN")
                                partial_assignment[index - n] = -(partial_assignment[index - n])
                                #                        print(index - n + 1, len(partial_assignment) - 1)
                                for j in range(index - n + 1, len(partial_assignment)):
                                    #                            print("J", j, partial_assignment[j])
                                    partial_assignment[j] = abs(partial_assignment[j])
                                case = True

                        # If the previous test result is the same as this test result, then we have tested all options and it is UNSAT
                        if partial_assignment == partial_assignment_prev:
                            end = True
                            if len(new_array) == 0:
                                new_array = ["UNSAT"]
                                return "UNSAT"

                        try:
                            branching_sat_solve(clause_set_original, partial_assignment)
                        except:
                            end = True
                            if len(new_array) == 0:
                                new_array = ["UNSAT"]
                                return "UNSAT"
                            break
        if end == True:
            return new_array


###############################################################################################################
##########################################QUESTION 6###########################################################
###############################################################################################################
def unit_propagate(clause_set):
    literal_list = []
    removal = False

    # Find a single literal in a clause in clause_set
    for clause in clause_set:
        if len(clause) == 1:
            for i in clause:
                literal_list.append(i)
                clause_set.remove(clause)

    # Loop through and remove the negation from the clauses
    for i in literal_list:
        literal_removal = False
        for clause in clause_set:
            for literal in clause:
                if literal == -i:
                    clause.remove(literal)
                    removal = True
                    literal_removal = True
        if literal_removal == False:
            clause_set.insert(0, [i])

    # Repeat, unless we get the same answer as before
    for clause in clause_set:
        if removal == True:
            unit_propagate(clause_set)
            break

    return clause_set


###############################################################################################################
##########################################QUESTION 7###########################################################
###############################################################################################################
literal_list = []


def pure_literal_elimination(clause_set):
    negation = False

    # Find the literals in a clause, which have a negation in another clause
    for clause in clause_set:
        position = clause_set.index(clause)
        clause_set.remove(clause)
        for literal in clause:
            #            if literal not in literal_list == True:
            end = True
            negation = False
            for clause2 in clause_set:
                for literal2 in clause2:
                    if literal == -literal2:  # and negation == False:
                        #                        literal_list.append(literal)
                        negation = True

            if negation == False:
                clause_set.insert(position, clause)

                # Remove these pure literals, which can be set to anything
                for i in clause_set:
                    for j in i:
                        if literal == j:
                            i.remove(j)

                # Repeat if we end up removing
                pure_literal_elimination(clauseSet)

                # If we do not remove anything, check the literals, add back the temporarily removed clause and check the literals in the next clause
        clause_set.insert(position, clause)

    # If abs(literal) not in list 1 to 16 then check it
    # If it is and we remove then remove from list 1 to 16

    # Iterive, so look through until we find a case where the variable has no negation, remove it and repeat  etc.
    # n + 1 each time #
    array = []
    for x in clause_set:
        if x not in array:
            array.append(x)
    clause_set = array
    return clause_set


###############################################################################################################
##########################################QUESTION 8###########################################################
###############################################################################################################
# I have put together the previous three questions and applied pure literal elimination and unit propogation IN THE CORRECT ORDER
import time

end = False
first_loop = True
new_array = []
real_partial = []


def dpll_sat_solve(clause_set, partial_assignment):
    #    print("CLAUSE SET:", clause_set)
    #    print("PARTIAL ASSIGNMENT:", partial_assignment)

    global end
    global first_loop
    global new_array
    global real_partial

    # PART 1: If we get nothing at the end, after assigning all the variables, then the formula is SAT. Go back a step if we get False. If we have tried every route, then the formula is UNSAT
    # Find the number of variables (or we could use the information at the top of the DIMACS file)
    number_of_variables = 0
    for clause in clause_set:
        for literal in clause:
            if abs(literal) > number_of_variables:
                number_of_variables = abs(literal)

    partial_assignment_original = list(range(1, number_of_variables + 1))

    # If we find the inputted partial_assignment cannot hold, then print UNSAT
    for i in partial_assignment:
        if abs(i) > number_of_variables:
            end = True
            new_array = ["UNSAT"]
            return new_array

    if first_loop == True:
        real_partial = copy.deepcopy(partial_assignment)
        for index, i in enumerate(partial_assignment_original):
            for j in partial_assignment:
                if abs(j) == i:
                    del partial_assignment_original[index]
                    partial_assignment_original.insert(0, j)
        partial_assignment = partial_assignment_original
        first_loop = False

    clause_set_original = copy.deepcopy(clause_set)
    new_clause_set = copy.deepcopy(clause_set)
    partial_assignment_prev = copy.deepcopy(partial_assignment)
    n = 0
    case = False
    i = 0
    index = 0
    end_break = False

    # Simplyify the formula and check if we get True (then exit), otherwise try a different assignment
    # PART 2: If there is a partial assignment, sub the partial assignments into the clause set (e.g. x1 = True, x4 = False). Simplify where we see (something AND False = False) and (something OR True = True)
    # (We could do set(clause) for each clause)
    def simplifying(clauseSet, variable):
        #        print("ORIGINAL ORIGINAL:", clauseSet)
        newClauseSet = copy.deepcopy(clauseSet)

        for clause in list(newClauseSet):
            for index, literal in enumerate(clause):
                # Remove this clause, as this clause will evaluate to True, if there is a True in it. So if we are left with an empty set at the end, it is satisfiable
                if int(literal) == int(variable):
                    try:
                        newClauseSet.remove(clause)  # CHECK CONDITIONS OF SIMPLIFYING
                    except:
                        pass
                # Replace negative literal with False
                if int(-literal) == int(variable):  # and PARTIAL VARIABLES ARE SATISFIED, ELSE CONTINUE:
                    #                    print(clause)
                    clause[index] = False
                #        print("ORIGINAL:", clauseSet)
        #        print("NEW:", newClauseSet)

        newClauseSet = unit_propagate(newClauseSet)
        newClauseSet = pure_literal_elimination(newClauseSet)
        if newClauseSet == [[]]:
            newClauseSet = []

        return newClauseSet

    # PART 3: Now we want to check each clause
    # We do not want any clauses to evaluate to false, as once we AND the entire formula, it will be unsatisfied
    # Go through each of the variables, starting from the first one. (We could remove the initial partially assigned ones from a list from 1 to n)
    # Checks the conditions for when we need to go back a step
    def falsity(clauseSet):
        for clause in clauseSet:
            # If we get a clause evaluating to False, go back a step, as the whole thing will be False
            if any(clause) == False:
                return True
            # If we get a contradiction between two clauses, go back a step
            for others in clauseSet:
                if len(clause) == 1 and len(others) == 1:
                    if clause[0] == -others[0]:
                        return True
        #        print(partial_assignment)
        if clauseSet == [] and all(elem in partial_assignment for elem in
                                   real_partial):  # and all(elem in clauseSet for elem in real_partial) == True
            partial_assignment_print = sorted(partial_assignment, key=abs)
            global new_array
            new_array = []
            for i in partial_assignment_print:
                if i > 0:
                    new_array.append(True)
                if i < 0:
                    new_array.append(False)
            #            print(new_array)
            global end
            end = True
            return False
        else:
            return False

    # PART 4: Piecing everything together and backtracking through recursion when necessary
    if end == False:
        for index, i in enumerate(partial_assignment):
            if end == True:
                break

            #            unit_propagate(new_clause_set)
            #            pure_literal_elimination(new_clause_set) ########## ADDED IN "SIMPLIFY" FUNCTION

            if type(i) == int and end == False:
                # Base case
                #        if i!=0 and all(z < 0 for z in partial_assignment[:(index )]) == True:
                #            print(partial_assignment[:(index)])
                #        return
                # Simplify for each assignment until we encounter an error
                #        print(partial_assignment)
                if not falsity(new_clause_set) == True and end == False:
                    #            print(i)
                    new_clause_set = simplifying(new_clause_set, int(i))
                #            print(new_clause_set)

                # If we don't encounter an error, then print the solution
                #        if abs(i) >= number_of_variables + 1:
                #            return partial_assignment

                # Make a change and try again by backtracking (CHECK CONDITIONS FOR WHEN TO ESCAPE AND JUST PRINT UNSAT)
                if falsity(new_clause_set) == True and end == False:
                    #            print("SCREAM")

                    if partial_assignment[index] > 0:
                        #                print("INDEX:", index - 1)
                        #                print(clause_set)
                        #                print(new_clause_set)
                        #                print(clause_set_original)
                        partial_assignment[index] = int(-i)
                        #                print(partial_assignment)
                        try:
                            branching_sat_solve(clause_set_original, partial_assignment)
                        except:
                            end = True
                            if len(new_array) == 0:
                                new_array = ["UNSAT"]
                                return "UNSAT"
                            break
                            # If you save the bit before, you can make it quicker maybe by changing what you sub in here

                    # CHECK THAT ALL THIS WORKS
                    if partial_assignment[index] < 0 and end == False:
                        #                print(partial_assignment)

                        while case == False and n <= index:  # Find the closest one before that isn't negative. Set it to negative. Set all the ones after it to positive. If they're all negative then UNSAT
                            #                    print("INDEX", index-n)
                            #                    print(partial_assignment[index - n])
                            #                    print(n)
                            if partial_assignment[index - n] < 0 and n <= index:
                                #                        print("YES")
                                n = n + 1
                                case = False
                            #                        print("HI", partial_assignment[index - n])
                            if partial_assignment[index - n] > 0 and n <= index:
                                #                        print("HI FINAL", partial_assignment[index - n])
                                #                        print("YES AGAIN")
                                partial_assignment[index - n] = -(partial_assignment[index - n])
                                #                        print(index - n + 1, len(partial_assignment) - 1)
                                for j in range(index - n + 1, len(partial_assignment)):
                                    #                            print("J", j, partial_assignment[j])
                                    partial_assignment[j] = abs(partial_assignment[j])
                                case = True

                        # If the previous test result is the same as this test result, then we have tested all options and it is UNSAT
                        if partial_assignment == partial_assignment_prev:
                            end = True
                            if len(new_array) == 0:
                                new_array = ["UNSAT"]
                                return "UNSAT"

                        try:
                            branching_sat_solve(clause_set_original, partial_assignment)
                        except:
                            end = True
                            if len(new_array) == 0:
                                new_array = ["UNSAT"]
                                return "UNSAT"
                            break
        if end == True:
            return new_array

#print(number_of_variables)
#print(number_of_sets)
#print(clauseSet)

#simple_sat_solve(clauseSet)

#start=time.time()
#print(branching_sat_solve(clauseSet,[]))
#end=time.time()
#print(end-start)

#unit_propagate(clauseSet)
#pure_literal_elimination(clauseSet)

#start=time.time()
#print(dpll_sat_solve(clauseSet,[]))
#end=time.time()
#print(end-start)