import copy
import externalproperties

clauses = []
cnf = []
numguests = input[0]
maxtables = input[1]

# Assigns one table per guest
def onetableperguest():
    for guest in range(1, int(numguests) + 1):
        onetableclause = []
        for table in range(1, int(maxtables) + 1):
            literal = 'X' + str(guest) + '>' + str(table)
            onetableclause.append(literal)
        clauses.append(onetableclause)
    for guest in range(1, int(numguests) + 1):
        for table1 in range(1, int(maxtables) + 1):
            for table2 in range(table1 + 1, int(maxtables) + 1):
                if table1 < table2:
                    onetableclause = []
                    literal1 = '~X' + str(guest) + '>' + str(table1)
                    onetableclause.append(literal1)
                    literal2 = '~X' + str(guest) + '>' + str(table2)
                    onetableclause.append(literal2)
                    clauses.append(onetableclause)

# Implements friends seating constraints 
# Friends must be seated next to each other
def friendconstraints(rel):
    for table1 in range(1, int(maxtables) + 1):
        for table2 in range(1, int(maxtables) + 1):
            if table1 != table2:
                onetableclause = []
                literal1 = '~X' + rel[0] + '>' + str(table1)
                onetableclause.append(literal1)
                literal2 = '~X' + rel[1] + '>' + str(table2)
                onetableclause.append(literal2)
                clauses.append(onetableclause)

# Implements enemy constraints
# Enemies must be seated away from each other
def enemyconstraints(rel):
    for table in range(1, int(maxtables) + 1):
        onetableclause = []
        literal1 = '~X' + rel[0] + '>' + str(table)
        onetableclause.append(literal1)
        literal2 = '~X' + rel[1] + '>' + str(table)
        onetableclause.append(literal2)
        clauses.append(onetableclause)

def getsymbolsinsentencedpll(clauses):
    symbols = []
    for clause in clauses:
        for literal in clause:
            if literal not in symbols:
                symbols.append(literal)
    return symbols

def removefromsymbols(symbols, toberemovedsymbol):
    newsymlist = copy.copy(symbols)
    newsymlist.remove(toberemovedsymbol)
    if "~" in toberemovedsymbol:
        # for some pure clauses the symbols might not contain the negation, since the clauses might not contain them
        if toberemovedsymbol.strip('~') in newsymlist:
            newsymlist.remove(toberemovedsymbol.strip('~'))
    else:
        if "~" + toberemovedsymbol in newsymlist:
            newsymlist.remove("~" + toberemovedsymbol)
    return newsymlist

def dpll(clauses, symbols, model):
    if bool(model):
        if evaluateassignmentdpll(clauses, model):
            return model
        # returns only if some clause returns false(not if it returns None or true)
        for clause in clauses:
            value = findvaluesofclausedpll(clause, model)
            if (value != None) and (not value):
                return False
    symbolValue = findPureSymboldpll(clauses, symbols, model)
    if bool(symbolValue):
        symbolvaluepair = next(iter(symbolValue))
        return dpll(clauses, removefromsymbols(symbols, symbolvaluepair),
                    modelunion(model, symbolvaluepair, symbolValue[symbolvaluepair]))
        # make consistant by also assigning for corresponding negation of that
    symbolValue = findunitclause(clauses, model)
    if bool(symbolValue):
        symbolvaluepair = next(iter(symbolValue))
        return dpll(clauses, removefromsymbols(symbols, symbolvaluepair),
                    modelunion(model, symbolvaluepair, symbolValue[symbolvaluepair]))
    first = symbols[0]
    rest = symbols
    return dpll(clauses, removefromsymbols(rest, first), modelunion(model, first, True)) or dpll(clauses,removefromsymbols(rest, first), modelunion(model, first, False))

# returns false if even one completely assigned clause evaluates to false
# returns true otherwise
def evaluateassignmentdpll(clauses, model):
    for clause in clauses:
        cvalue = findvaluesofclausedpll(clause, model)
        # if (cvalue!=None) and (not cvalue):
        if not cvalue:
            return False
    return True

# returns None if a literal in the clause is unassigned
# returns true if clause evaluates to true
def findvaluesofclausedpll(clause, model):
    value = None
    unassigned = False
    # for positive literal
    for literal in [x for x in clause if not "~" in x]:
        if bool(model) & (literal in model):
            if model[literal]:
                value = True
                break
        else:
            unassigned = True
    # for negetive literals
    if value == None:
        for literal in filter(lambda x: '~' in x, clause):
            # if literal.strip('~') in model:
            if bool(model) & (literal in model):
                # if not model[literal.strip('~')]:
                if model[literal]:
                    value = True
                    break
            else:
                unassigned = True
        if value == None:
            if not unassigned:
                value = False
    return value

def modelunion(model, symbol, value):
    newmodel = copy.copy(model)
    if "~" in symbol:
        newmodel[symbol] = value
        newmodel[symbol.strip('~')] = not value
    else:
        newmodel[symbol] = value
        newmodel["~" + symbol] = not value
    return newmodel

def findPureSymboldpll(clauses, symbols, model):
    result = {}
    puresymbols = copy.copy(symbols)
    purepositivesymbols = []
    purenegativesymbols = []
    for clause in clauses:
        if findvaluesofclausedpll(clause, model):
            continue
        for pos in [x for x in clause if not "~" in x]:
            if (pos in puresymbols) and (pos not in purepositivesymbols):
                purepositivesymbols.append(pos)
        for neg in filter(lambda x: '~' in x, clause):
            if (neg in puresymbols) and (neg not in purenegativesymbols):
                purenegativesymbols.append(neg)
    for symbol in puresymbols:
        if "~" in symbol:
            if (symbol.strip('~') in purepositivesymbols) and (symbol in purenegativesymbols):
                purepositivesymbols.remove(symbol.strip('~'))
                purenegativesymbols.remove(symbol)
        else:
            if (symbol in purepositivesymbols) and ("~" + symbol in purenegativesymbols):
                purepositivesymbols.remove(symbol)
                purenegativesymbols.remove("~" + symbol)
    if len(purepositivesymbols) > 0:
        purepos = next(iter(purepositivesymbols))
        result[purepos] = True
    if len(purenegativesymbols) > 0:
        pureneg = next(iter(purenegativesymbols))
        result[pureneg] = True
    return result

def findunitclause(clauses, model):
    # returns unit clause symbol and value if one exists
    # else returns {}
    result = {}
    for clause in clauses:
        if findvaluesofclausedpll(clause, model) == None:
            unassigned = None
            if len(clause) == 1:
                unassigned = clause[0]
            else:
                for literal in clause:
                    if literal not in model:
                        # if value == None:
                        if unassigned == None:
                            unassigned = literal
                        else:
                            unassigned = None
                            break
            if unassigned != None:
                if "~" in unassigned:
                    result[unassigned] = True
                    break
                else:
                    result[unassigned] = True
                    break
    return result

def printclauses(clauses):
    for clause in clauses:
        print clause

def get_seat_arrangement(f, lines, numguests):
    lines.pop(0)
    onetableperguest()
    for line in lines:
        rel = line.split()
        if rel[2] == 'F':
            friendconstraints(rel)
        elif rel[2] == 'E':
            enemyconstraints(rel)
    result = dpll(clauses, getsymbolsinsentencedpll(clauses), {})
    if result:
        print >> f, "yes"
        assignment = {}
        for item in result:
            if result[item] & ("~" not in item):
                gt = item.strip('X').split('>')
                assignment[gt[0]] = gt[1]
        if len(assignment) < int(numguests):
            guest = 1
            while guest < int(numguests) + 1:
                if str(guest) not in assignment:
                    assignment[str(guest)] = "1"
                guest += 1
        for guest in sorted(assignment.keys(), key=int):
            print >> f, guest, assignment[guest]
    else:
        print >> f, "no"


def main():
    # Read input from INPUT_FILE_PATH
    rawinput = open(externalproperties.INPUT_FILE_PATH, 'r')
    lines = rawinput.read().splitlines()

    # Print output to OUTPUT_FILE_PATH
    f = open(externalproperties.OUTPUT_FILE_PATH, 'w')

    if int(numguests)<=0:
        print >> f, "yes"
    elif int(numguests)>0 and int(maxtables)<=0:
        print >> f, "no"
    else:
        get_seat_arrangement(f, lines, numguests)

if __name__ == "__main__":
    main()
