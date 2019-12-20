import sys
import copy
from collections import OrderedDict

#python main.py file.var confile.con {none or fc}
#print(sys.argv) #list of arguments
args = sys.argv[1:] #remove file name arg 'main.py'
varDomainLines = open(args[0], "r").readlines()
domains = {}
vars = []
tried = []
for line in varDomainLines:
    domains.setdefault(line[0], line[3:].split())
    vars.append(line[0])
originalDomains = copy.deepcopy(domains)
constraintLines = open(args[1], "r").readlines()
for x in range(len(constraintLines)-1):
    constraintLines[x] = constraintLines[x][:-1]
equals = {}
notEquals = {}
for var in vars:
    equals.setdefault(var, [])
    notEquals.setdefault(var, [])
greaterThan = []
for constraint in constraintLines:
    lineArgs = constraint.split()
    if lineArgs[1] == '>':
        if (lineArgs[2], lineArgs[0]) not in greaterThan:
            greaterThan.append((lineArgs[2], lineArgs[0]))
    elif lineArgs[1] == '=':
        equals.update({lineArgs[0]: equals[lineArgs[0]] + [lineArgs[2]]})
        equals.update({lineArgs[2]: equals[lineArgs[2]] + [lineArgs[0]]})
    elif lineArgs[1] == '!':
        notEquals.update({lineArgs[0]: notEquals[lineArgs[0]] + [lineArgs[2]]})
        notEquals.update({lineArgs[2]: notEquals[lineArgs[2]] + [lineArgs[0]]})
    else:
        if (lineArgs[0], lineArgs[2]) not in greaterThan:
            greaterThan.append((lineArgs[0], lineArgs[2]))
selected = OrderedDict()

if args[2] == 'none':
    #print("Not using forward checking")
    domainSize = {}
    for item in domains.items():
        key, value = item
        if len(value) in domainSize.keys():
            domainSize.update({len(value): domainSize[len(value)] + [key]})
        else:
            domainSize.setdefault(len(value), [key])
    #print(domainSize)
    domainSizes = sorted(domainSize.keys())
    allDomainSize = copy.deepcopy(domainSize)
    maxConstrainedVars = domainSize[domainSizes[0]]
    assigned = []
    if len(maxConstrainedVars) == 1:
        #print("Only one var")
        nextVar = maxConstrainedVars[0]
    else:
        curMax = (100,'Z')
        for var in maxConstrainedVars:
            numConstraints = 0
            for pair in greaterThan:
                #print(pair)
                if var in pair:
                    #print(var, "in pair'")
                    valid = True
                    for already in assigned:
                        if already in pair:
                            #print("But", already, "is already assigned")
                            valid = False
                    if valid:
                        numConstraints += 1
            for variable in equals[var]:
                if variable not in assigned:
                    #print("Equality with", variable)
                    numConstraints += 1
            for variable in notEquals[var]:
                if variable not in assigned:
                    #print("Inequality with", variable)
                    numConstraints += 1
            #print("Var ", var, "has N constraints: ", numConstraints)
            curMax = min(curMax, (-1*numConstraints, var))
        nextVar = curMax[1]
    #print("Heuristic chose",nextVar)
    varDomain = domains[nextVar]
    maxValidValues = (100,100)
    for num in varDomain:
        #print("Trying value",nextVar, num)
        validValues = 0
        for var in vars:
            if var != nextVar and var not in assigned:
                currentDomain = copy.deepcopy(domains[var]) #make sure this is an actual copy not a pointer
                toRemove = []
                #print(var, currentDomain)
                for value in currentDomain:
                    for comparison in greaterThan:
                        lesser, greater = comparison
                        if lesser == var and greater == nextVar:
                            if value >= num:
                                #print(var,value,"is not lesser than", nextVar,num)
                                for number in currentDomain:
                                    if number >= value:
                                        #print("removing", number)
                                        toRemove.append((number))
                            else:
                                pass
                                #print(var,value,"is lesser than", nextVar,num)
                        elif lesser == nextVar and greater == var:
                            if value <= num:
                                #print(nextVar,num,"is not lesser than", var,value)
                                for number in currentDomain:
                                    if number <= num:
                                        #print("removing", number)
                                        toRemove.append((number))
                            else:
                                pass
                                #print(nextVar,num,"is lesser than", var,value)
                    if var in notEquals[nextVar]:
                        if value == num and value not in toRemove:
                            toRemove.append(value)
                    if var in equals[nextVar]:
                        if value != num and value not in toRemove:
                            toRemove.append(value)
                    for aNumber in toRemove:
                        if aNumber in currentDomain:
                            currentDomain.remove(aNumber)


                #print(var, currentDomain)
                validValues += len(currentDomain)
        maxValidValues = min(maxValidValues, (-1*validValues, num))
    bestVal = maxValidValues[1]
    #print("Heuristic chose",nextVar,bestVal)
    selected.setdefault(nextVar, bestVal)
    tried.append(selected)
    assigned.append(nextVar)
    numFailures = 0
    place = 1
    backtracking = False
    while numFailures < 30:
        #print("new iteration")
        if not backtracking:
            count = copy.deepcopy(place)
            traversed = 0
            #print("Count:",count)
            while count >= 0:
                #print(traversed)
                #print(domainSize)
                maxConstrainedVars = allDomainSize[domainSizes[traversed]]
                #print(maxConstrainedVars)
                count -= len(maxConstrainedVars)
                #print("Count",count)
                traversed += 1
            maxConstrainedVars = copy.deepcopy(domainSize[domainSizes[traversed-1]])
            #print("already assigned vars:",assigned)
            goingToRemove = []
            for var in maxConstrainedVars:
                if var in assigned:
                    goingToRemove.append(var)
            for x in goingToRemove:
                maxConstrainedVars.remove(x)
            #print(maxConstrainedVars)
            if len(maxConstrainedVars) == 1:
                #print("Only one var")
                nextVar = maxConstrainedVars[0]
            else:
                curMax = (100, 'Z')
                for var in maxConstrainedVars:
                    numConstraints = 0
                    for pair in greaterThan:
                        if var in pair:
                            valid = True
                            for already in assigned:
                                if already in pair:
                                    valid = False
                            if valid:
                                numConstraints += 1
                    for variable in equals[var]:
                        if variable not in assigned:
                            numConstraints += 1
                    for variable in notEquals[var]:
                        if variable not in assigned:
                            numConstraints += 1
                    #print("Var", var, "constrains N vars:", numConstraints)
                    curMax = min(curMax, (-1*numConstraints, var))
                nextVar = curMax[1]
        else:
            nextVar = backtrackedVar
            backtracking = False
        #print("Heauristic chose",nextVar)
        varDomain = domains[nextVar]
        #print(varDomain)
        toRemoveDomain = []
        for alreadyTriedDict in tried:
            triedItems = alreadyTriedDict.items()
            selectedItems = selected.items()
            if len(triedItems) > len(selectedItems):
                ignore = False
                for key in selected.keys():
                    if selected[key] != alreadyTriedDict[key]:
                        ignore = True
                if not ignore:
                    toRemoveDomain.append(alreadyTriedDict[nextVar])
        for aValue in toRemoveDomain:
            if aValue in varDomain:
                #print("Already tried", aValue, "for", nextVar)
                varDomain.remove(aValue)
        maxValidValues = (100, 100)
        for num in varDomain:
            #print(nextVar, num)
            validValues = 0
            for var in vars:
                if var != nextVar and var not in assigned:
                    currentDomain = copy.deepcopy(domains[var])  # make sure this is an actual copy not a pointer
                    toRemove = []
                    #print(var, currentDomain)
                    for value in currentDomain:
                        for comparison in greaterThan:
                            lesser, greater = comparison
                            if lesser == var and greater == nextVar:
                                if value >= num:
                                    #print(var, value, "is not lesser than", nextVar, num)
                                    for number in currentDomain:
                                        if number >= value:
                                            #print("removing", number)
                                            toRemove.append((number))
                                else:
                                    pass
                                    #print(var, value, "is lesser than", nextVar, num)
                            elif lesser == nextVar and greater == var:
                                if value <= num:
                                    #print(nextVar, num, "is not lesser than", var, value)
                                    for number in currentDomain:
                                        if number <= num:
                                            # print("removing", number)
                                            toRemove.append((number))
                                else:
                                    pass
                                    #print(nextVar, num, "is lesser than", var, value)
                        if var in notEquals[nextVar]:
                            if value == num and value not in toRemove:
                                toRemove.append(value)
                        if var in equals[nextVar]:
                            if value != num and value not in toRemove:
                                toRemove.append(value)
                        for aNumber in toRemove:
                            if aNumber in currentDomain:
                                currentDomain.remove(aNumber)
                    #print(var, currentDomain)
                    validValues += len(currentDomain)
            maxValidValues = min(maxValidValues, (-1 * validValues, num))
        bestVal = maxValidValues[1]
        #print(bestVal)
        if nextVar in selected.keys():
            selected.update({nextVar: bestVal})
        else:
            selected.setdefault(nextVar, bestVal)
        if nextVar not in assigned:
            assigned.append(nextVar)
        failure = False
        #print(selected)
        for comparison in greaterThan:
            lesser, greater = comparison
            if lesser in selected.keys() and greater in selected.keys() and selected[lesser] >= selected[greater]:
                #print(lesser,"not less than", greater)
                failure = True
        for variable in selected.keys():
            for equalTo in equals[variable]:
                if equalTo in selected.keys() and selected[variable] != selected[equalTo]:
                    #print(variable,"not equal to", equalTo)
                    failure = True
        for variable in selected.keys():
            for notEqualTo in notEquals[variable]:
                if notEqualTo in selected.keys() and selected[variable] != selected[notEqualTo]:
                    #print(variable,"equal to", notEqualTo)
                    failure = True
        if failure:
            numFailures += 1
            toPrint = str(numFailures) + ". "
            for item in selected.items():
                variable, value = item
                toPrint += variable + "=" + str(value) + ", "
            toPrint = toPrint[:-2] + "  failure"
            print(toPrint)
            tried.append(copy.deepcopy(selected))
            del selected[nextVar]
            assigned.remove(nextVar)
            #print(varDomain)
            if(len(varDomain)) == 1:
                #print(nextVar)
                #print(domains)
                #print(originalDomains)
                domains.update({nextVar: copy.deepcopy(originalDomains[nextVar])})
                #print("Var domain has been exhausted. Backtracking...")
                #print(domains)
                place -= 1
                #print(place)
                #print(selected)
                backtracking = True
                backtrackedVar = next(reversed(selected))
        else:
            if len(selected.values()) == len(vars):
                numFailures += 1
                toPrint = str(numFailures) + ". "
                for item in selected.items():
                    variable, value = item
                    toPrint += variable + "=" + str(value) + ", "
                toPrint = toPrint[:-2] + "  solution"
                print(toPrint)
                break
            else:
                place += 1

else:
    # print("Using forward checking")
    domainSize = {}
    for item in domains.items():
        key, value = item
        if len(value) in domainSize.keys():
            domainSize.update({len(value): domainSize[len(value)] + [key]})
        else:
            domainSize.setdefault(len(value), [key])
    #print(domainSize)
    domainSizes = sorted(domainSize.keys())
    allDomainSize = copy.deepcopy(domainSize)
    maxConstrainedVars = domainSize[domainSizes[0]]
    assigned = []
    if len(maxConstrainedVars) == 1:
        #print("Only one var")
        nextVar = maxConstrainedVars[0]
    else:
        curMax = (100, 'Z')
        for var in maxConstrainedVars:
            numConstraints = 0
            for pair in greaterThan:
                # print(pair)
                if var in pair:
                    # print(var, "in pair'")
                    valid = True
                    for already in assigned:
                        if already in pair:
                            # print("But", already, "is already assigned")
                            valid = False
                    if valid:
                        numConstraints += 1
            for variable in equals[var]:
                if variable not in assigned:
                    # print("Equality with", variable)
                    numConstraints += 1
            for variable in notEquals[var]:
                if variable not in assigned:
                    # print("Inequality with", variable)
                    numConstraints += 1
            #print("Var ", var, "has N constraints: ", numConstraints)
            curMax = min(curMax, (-1 * numConstraints, var))
        nextVar = curMax[1]
    #print("Heuristic chose", nextVar)
    varDomain = domains[nextVar]
    maxValidValues = (100, 100)
    for num in varDomain:
        #print("Trying value", nextVar, num)
        validValues = 0
        for var in vars:
            if var != nextVar and var not in assigned:
                currentDomain = copy.deepcopy(domains[var])  # make sure this is an actual copy not a pointer
                toRemove = []
                #print(var, currentDomain)
                for value in currentDomain:
                    for comparison in greaterThan:
                        lesser, greater = comparison
                        if lesser == var and greater == nextVar:
                            if value >= num:
                                #print(var, value, "is not lesser than", nextVar, num)
                                for number in currentDomain:
                                    if number >= value:
                                        #print("removing", number)
                                        toRemove.append((number))
                            else:
                                pass
                                #print(var, value, "is lesser than", nextVar, num)
                        elif lesser == nextVar and greater == var:
                            if value <= num:
                                #print(nextVar, num, "is not lesser than", var, value)
                                for number in currentDomain:
                                    if number <= num:
                                        # print("removing", number)
                                        toRemove.append((number))
                            else:
                                pass
                                #print(nextVar, num, "is lesser than", var, value)
                    if var in notEquals[nextVar]:
                        if value == num and value not in toRemove:
                            toRemove.append(value)
                    if var in equals[nextVar]:
                        if value != num and value not in toRemove:
                            toRemove.append(value)
                    for aNumber in toRemove:
                        if aNumber in currentDomain:
                            currentDomain.remove(aNumber)

                #print(var, currentDomain)
                validValues += len(currentDomain)
        #print(nextVar,"=",num,"allows N valid values:", validValues)
        maxValidValues = min(maxValidValues, (-1 * validValues, num))
    bestVal = maxValidValues[1]
    #print("Heuristic chose", nextVar, bestVal)
    selected.setdefault(nextVar, bestVal)
    tried.append(selected)
    assigned.append(nextVar)
    numFailures = 0
    place = 1
    backtracking = False
    changed = True
    updatedDomains = copy.deepcopy(domains)
    updatedDomains.update({nextVar: [str(bestVal)]})

    for var in vars:
        toDelete = []
        if var != nextVar:
            for comparison in greaterThan:
                if var in comparison and nextVar in comparison:
                    if comparison[0] == var:
                        for member in updatedDomains[var]:
                            if member >= bestVal:
                                if member not in toDelete:
                                    toDelete.append(member)
                    else: #comparison[0] == nextVar:
                        for member in updatedDomains[var]:
                            if member <= bestVal:
                                if member not in toDelete:
                                    toDelete.append(member)

            for notEqualVar in notEquals[nextVar]:
                for member in updatedDomains[var]:
                    if member == bestVal:
                        if member not in toDelete:
                            toDelete.append(member)
            currentDomain = updatedDomains[var]
            for deletion in toDelete:
                currentDomain.remove(deletion)
            for equalVar in equals[nextVar]:
                updatedDomains.update({equalVar: [bestVal]})
    firstFailure = False
    for value in updatedDomains.values():
        if value == []:
            firstFailure = True
    if not firstFailure:
        domains = updatedDomains
        #print("Propogation complete")
        #print(domains)

    while numFailures < 30:
        if firstFailure:
            numFailures += 1
            toPrint = str(numFailures) + ". " + nextVar + "=" + str(bestVal) + "  failure"
            #print("first failure")
            print(toPrint)
            selected.setdefault(nextVar, bestVal)
            tried.append(selected)
            selected = OrderedDict()
            place -= 1
            assigned.remove(nextVar)
            firstFailure = False
            updatedDomains = domains
        #print("new iteration")
        if not backtracking:
            count = copy.deepcopy(place)
            traversed = 0
            #print("Count:", count)
            domainSize = {}
            #print(updatedDomains)
            for item in updatedDomains.items():
                key, value = item
                if len(value) in domainSize.keys():
                    domainSize.update({len(value): domainSize[len(value)] + [key]})
                else:
                    domainSize.setdefault(len(value), [key])
            domainSizes = sorted(domainSize.keys())

            while count >= 0:
                #print(traversed)
                #print(domainSize)
                maxConstrainedVars = domainSize[domainSizes[traversed]]
                #print(maxConstrainedVars)
                count -= len(maxConstrainedVars)
                #print("Count", count)
                traversed += 1
            maxConstrainedVars = copy.deepcopy(domainSize[domainSizes[traversed - 1]])
            #print("already assigned vars:", assigned)
            goingToRemove = []
            for var in maxConstrainedVars:
                if var in assigned:
                    goingToRemove.append(var)
            for x in goingToRemove:
                maxConstrainedVars.remove(x)
            #print(maxConstrainedVars)
            if len(maxConstrainedVars) == 1:
                #print("Only one var")
                nextVar = maxConstrainedVars[0]
            else:
                curMax = (100, 'Z')
                for var in maxConstrainedVars:
                    numConstraints = 0
                    for pair in greaterThan:
                        if var in pair:
                            valid = True
                            for already in assigned:
                                if already in pair:
                                    valid = False
                            if valid:
                                numConstraints += 1
                    for variable in equals[var]:
                        if variable not in assigned:
                            numConstraints += 1
                    for variable in notEquals[var]:
                        if variable not in assigned:
                            numConstraints += 1
                    #print("Var", var, "constrains N vars:", numConstraints)
                    curMax = min(curMax, (-1 * numConstraints, var))
                nextVar = curMax[1]
        else:
            nextVar = backtrackedVar
            backtracking = False
            domains = copy.deepcopy(originalDomains)
        #print("Heauristic chose", nextVar)
        varDomain = domains[nextVar]
        #print(varDomain)
        toRemoveDomain = []
        #print(tried)
        for alreadyTriedDict in tried:
            #print("tried",alreadyTriedDict)
            triedItems = alreadyTriedDict.items()
            #print("selected",selected)
            selectedItems = selected.items()
            if len(triedItems) >= len(selectedItems):
                #print("consider",triedItems,selectedItems)
                ignore = False
                for key in selected.keys():
                    try:
                        if selected[key] != alreadyTriedDict[key]:
                            ignore = True
                    except:
                        pass
                        #print("Key error")
                if not ignore:
                    try:
                        toRemoveDomain.append(alreadyTriedDict[nextVar])
                    except:
                        pass
                        #print("Key error. Ignore tried ")
        for aValue in toRemoveDomain:
            if aValue in varDomain:
                #print("Already tried", aValue, "for", nextVar)
                varDomain.remove(aValue)
        maxValidValues = (100, 100)
        for num in varDomain:
            #print(nextVar, num)
            validValues = 0
            for var in vars:
                if var != nextVar and var not in assigned:
                    currentDomain = copy.deepcopy(domains[var])  # make sure this is an actual copy not a pointer
                    toRemove = []
                    #print(var, currentDomain)
                    for value in currentDomain:
                        for comparison in greaterThan:
                            lesser, greater = comparison
                            if lesser == var and greater == nextVar:
                                if value >= num:
                                    #print(var, value, "is not lesser than", nextVar, num)
                                    for number in currentDomain:
                                        if number >= value:
                                            #print("removing", number)
                                            toRemove.append((number))
                                else:
                                    pass
                                    #print(var, value, "is lesser than", nextVar, num)
                            elif lesser == nextVar and greater == var:
                                if value <= num:
                                    #print(nextVar, num, "is not lesser than", var, value)
                                    for number in currentDomain:
                                        if number <= num:
                                            # print("removing", number)
                                            toRemove.append((number))
                                else:
                                    pass
                                    #print(nextVar, num, "is lesser than", var, value)
                        if var in notEquals[nextVar]:
                            if value == num and value not in toRemove:
                                toRemove.append(value)
                        if var in equals[nextVar]:
                            if value != num and value not in toRemove:
                                toRemove.append(value)
                        for aNumber in toRemove:
                            if aNumber in currentDomain:
                                currentDomain.remove(aNumber)
                    #print(var, currentDomain)
                    validValues += len(currentDomain)
            #print(nextVar, "=", num, "allows N valid values:", validValues)
            maxValidValues = min(maxValidValues, (-1 * validValues, num))
        bestVal = maxValidValues[1]
        #print(bestVal)
        if nextVar in selected.keys():
            selected.update({nextVar: bestVal})
        else:
            selected.setdefault(nextVar, bestVal)
        if nextVar not in assigned:
            assigned.append(nextVar)
        failure = False
        #print(selected)
        for comparison in greaterThan:
            lesser, greater = comparison
            if lesser in selected.keys() and greater in selected.keys() and selected[lesser] >= selected[greater]:
                #print(lesser, "not less than", greater)
                failure = True
        for variable in selected.keys():
            for equalTo in equals[variable]:
                if equalTo in selected.keys() and selected[variable] != selected[equalTo]:
                    #print(variable, "not equal to", equalTo)
                    failure = True
        for variable in selected.keys():
            for notEqualTo in notEquals[variable]:
                if notEqualTo in selected.keys() and selected[variable] != selected[notEqualTo]:
                    #print(variable, "equal to", notEqualTo)
                    failure = True
        changed = True
        updatedDomains = copy.deepcopy(domains)
        updatedDomains.update({nextVar: [str(bestVal)]})
        for var in vars:
            toDelete = []
            if var != nextVar:
                for comparison in greaterThan:
                    if var in comparison and nextVar in comparison:
                        if comparison[0] == var:
                            for member in updatedDomains[var]:
                                if int(member) >= int(bestVal):
                                    if member not in toDelete:
                                        toDelete.append(member)
                        else:  # comparison[0] == nextVar:
                            for member in updatedDomains[var]:
                                if int(member) <= int(bestVal):
                                    if member not in toDelete:
                                        toDelete.append(member)

                for notEqualVar in notEquals[nextVar]:
                    for member in updatedDomains[var]:
                        if member == bestVal:
                            if member not in toDelete:
                                toDelete.append(member)
                currentDomain = updatedDomains[var]
                for deletion in toDelete:
                    currentDomain.remove(deletion)
                for equalVar in equals[nextVar]:
                    updatedDomains.update({equalVar: [bestVal]})
        fcFailure = False
        for value in updatedDomains.values():
            if value == []:
                fcFailure = True
                failure = True
        if not fcFailure:
            domains = updatedDomains
            #print("Propogation complete")
            #print(domains)
        if failure:
            numFailures += 1
            toPrint = str(numFailures) + ". "
            for item in selected.items():
                variable, value = item
                toPrint += variable + "=" + str(value) + ", "
            toPrint = toPrint[:-2] + "  failure"
            print(toPrint)
            tried.append(copy.deepcopy(selected))
            del selected[nextVar]
            assigned.remove(nextVar)
            #print(varDomain)
            if (len(varDomain)) == 1:
                #print(nextVar)
                #print(domains)
                #print(originalDomains)
                domains.update({nextVar: copy.deepcopy(originalDomains[nextVar])})
                #print("Var domain has been exhausted. Backtracking...")
                #print(domains)
                place -= 1
                #print(place)
                #print(selected)
                backtracking = True
                backtrackedVar = next(reversed(selected))
                selected = OrderedDict()
        else:
            if len(selected.values()) == len(vars):
                numFailures += 1
                toPrint = str(numFailures) + ". "
                for item in selected.items():
                    variable, value = item
                    toPrint += variable + "=" + str(value) + ", "
                toPrint = toPrint[:-2] + "  solution"
                print(toPrint)
                break
            else:
                place += 1
