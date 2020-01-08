'''
File:       SMT_SA.py
Author:     Roozbeh Gholami (roozbeh[dot]gholami[at]iasbs[dot]ac[dot]ir, gholami[dot]roozbeh70[at]gmail[dot]com)
Date:       Summer-Autumn 2019
Summary of File:
    This file contains code which makes a timetable for
    univesity courses and minimizes number of classrooms.
'''

import random
import math
import re
from operator import itemgetter, attrgetter
import os
from os import system, name
import time
import timeit
import numpy as np
import copy
from time import gmtime, strftime, localtime

########################################
##### BGM  Neighborhood Relation #######
########################################

def neighbor(nei_timetable, nei_conflict_set, nei_availability,  nei_unavailability, nei_timeslot, ind):
    default = set()
    classrooms_space = [0] * number_of_classroom
    for r in range(number_of_classroom):
        for t in range(nei_timeslot):
            if (nei_timetable[r][t] == "-1"):
                classrooms_space[r] += 1
    if (ind % 2 == 0):
        room1 = classrooms_space.index(max(classrooms_space))
    else:
        room1 = random.randint(0, number_of_classroom -1)
    room2 = random.randint(0, number_of_classroom - 1)
    while (room1 == room2):
        room2 = random.randint(0, number_of_classroom - 1)
    room2_freespace = set()
    room1_lec = list()
    tmp_time = set()
    for t in range(nei_timeslot):
        tmp_time.add(t)
        if (nei_timetable[room2][t] == "-1"):
            room2_freespace.add(t)
        if (nei_timetable[room1][t] != "-1"):
            room1_lec.append((nei_timetable[room1][t], t))
    tmp_availability = {}
    counter = 0
    tmp_dict = {}
    for item in room1_lec:
        tmp_dict[str(counter)] = item
        tmp_set = set()
        for t in range(nei_timeslot):
            for r in range(number_of_classroom):
                if ((t != item[1]) & (r != room2) & ((item[0], nei_timetable[r][t]) in nei_conflict_set)):
                    tmp_set.add(t)
        tmp_availability[str(counter)] = tmp_time - (tmp_set|(nei_unavailability.get(item[0], default)))
        counter += 1
    matching = bipartiteMatch(tmp_availability)
    for item in matching[0]:
        if item in room2_freespace:
            nei_timetable[room2][item] = tmp_dict[matching[0][item]][0]
            nei_timetable[room1][tmp_dict[matching[0][item]][1]] = "-1"
    return nei_timetable

##########################################
#### Acceptance probability function #####
##########################################
def acceptance_probability(old_cost, new_cost, T):
    return math.exp((new_cost-old_cost)/T)


#########################################
#######     Cost function     ###########
#########################################

def cost (timetable):
    rooms_indicator = [0]* number_of_classroom
    for r in range(number_of_classroom):
        for t in range(timeslots):
            if (timetable[r][t] != "-1"):
                rooms_indicator[r] = 1
                break
    return (sum(rooms_indicator))

##########################################
###### Simulated annealing function ######
##########################################
def sim_anneal(sim_timetable, sim_conflict_set, sim_classroom_indicator, sim_availability, sim_unavailability, sim_timeslot):
    T = 1.0
    T_min = 0.1
    alpha = 0.9
    iteration_SA = 50
    counter_T = 1
    old_timetable = copy.copy(sim_timetable)
    old_cost = cost(sim_timetable)
    while T > T_min:
        i = 1
        while i <= iteration_SA:
            new_timetable = neighbor(old_timetable, sim_conflict_set, sim_availability,  sim_unavailability, sim_timeslot, i)
            new_cost = cost(new_timetable)
            ap = acceptance_probability(old_cost, new_cost, T)
            if ap > random.random():
                old_timetable = copy.copy(new_timetable)
                old_cost = copy.copy(new_cost)
            i += 1
        counter_T += 1
        T = T * alpha
    return old_timetable, old_cost

#######################################################################################
######  Hopcroft-Karp bipartite max-cardinality matching and max independent set ######
#####################   David Eppstein, UC Irvine, 27 Apr 2002   ######################
#######################################################################################

def bipartiteMatch(graph):
    '''Find maximum cardinality matching of a bipartite graph (U,V,E).
    The input format is a dictionary mapping members of U to a list
    of their neighbors in V.  The output is a triple (M,A,B) where M is a
    dictionary mapping members of V to their matches in U, A is the part
    of the maximum independent set in U, and B is the part of the MIS in V.
    The same object may occur in both U and V, and is treated as two
    distinct vertices if this happens.'''

    # initialize greedy matching (redundant, but faster than full search)
    matching = {}
    for u in graph:
        for v in graph[u]:
            if v not in matching:
                matching[v] = u
                break

    while 1:
        # structure residual graph into layers
        # pred[u] gives the neighbor in the previous layer for u in U
        # preds[v] gives a list of neighbors in the previous layer for v in V
        # unmatched gives a list of unmatched vertices in final layer of V,
        # and is also used as a flag value for pred[u] when u is in the first layer
        preds = {}
        unmatched = []
        pred = dict([(u, unmatched) for u in graph])
        for v in matching:
            del pred[matching[v]]
        layer = list(pred)

        # repeatedly extend layering structure by another pair of layers
        while layer and not unmatched:
            newLayer = {}
            for u in layer:
                for v in graph[u]:
                    if v not in preds:
                        newLayer.setdefault(v, []).append(u)
            layer = []
            for v in newLayer:
                preds[v] = newLayer[v]
                if v in matching:
                    layer.append(matching[v])
                    pred[matching[v]] = v
                else:
                    unmatched.append(v)

        # did we finish layering without finding any alternating paths?
        if not unmatched:
            unlayered = {}
            for u in graph:
                for v in graph[u]:
                    if v not in preds:
                        unlayered[v] = None
            return (matching, list(pred), list(unlayered))

        # recursively search backward through layers to find alternating paths
        # recursion returns true if found path, false otherwise
        def recurse(v):
            if v in preds:
                L = preds[v]
                del preds[v]
                for u in L:
                    if u in pred:
                        pu = pred[u]
                        del pred[u]
                        if pu is unmatched or recurse(pu):
                            matching[v] = u
                            return 1
            return 0

        for v in unmatched: recurse(v)

################################
###### Fitness function ########
################################
def fitness_function(pop, conflict_sets, unavailability_fit, generation_t):
    default = set()
    classroom_indicator = [0.0] * number_of_classroom
    beta = 1.0
    fit_Value = 0.0
    violation_existence = False
    rooms_freespace = [0]*number_of_classroom
    for c in range(number_of_classroom):
        for t in range(timeslots):
            lec1 = pop[c][t]
            if (lec1 != "-1"):
                classroom_indicator[c] = 1.0
                if (t in unavailability_fit.get(lec1, default)):
                    fit_Value += 1.0
                    violation_existence = True
                for cc in range(number_of_classroom):
                    if ((cc != c) & ((lec1,pop[cc][t]) in conflict_sets)):
                        fit_Value += 1.0
                        violation_existence = True
            else:
                rooms_freespace[c] += 1

    fitness_value = fit_Value
    classroom_value = sum(classroom_indicator) 
    return violation_existence, fitness_value, classroom_value


#######################
# number of iteration #
# number of runs      #
#######################


iteration = 100
number_of_runs = 20
file_index = 0
data = ["..\\Dataset\\EarlyDatasets\\", "..\\Dataset\\HiddenDatasets\\", "..\\Dataset\\LateDatasets\\"]
data_folder = ["EarlyDatasets", "HiddenDatasets", "LateDatasets"]
file_name = "comp0"
data_format = ".ctt"
z3_result = "competition\\competition_result"
z3_result_extention = "sol_z3_new_run"
z3_txt = ".txt"
results_path = data_folder[file_index] + "-Results-" + re.sub('.py', '',os.path.basename(__file__)) + "\\"
if not os.path.exists(results_path):
    os.makedirs(results_path)
showtime = strftime("%Y%m%d_%H%M%S", localtime())
myfile = results_path + showtime + ".txt"
g = open(myfile, 'w')
##########################################################################################
############################ Data strucure ###############################################
##########################################################################################
## attrib[0] = Name, attrib[1] = Courses, attrib[2] = number_of_rooms, attrib[3] = Days ##
## attrib[4] = Periods_per_day, attrib[5] =  Curricula, attrib[6] = Constraints         ##
##                                                                                      ##
##Courses: <CourseID> <Teacher> <# Lectures> <MinWorkingDays> <# Students>              ##
##Rooms: <RoomID> <Capacity>                                                            ##
##Curricula: <CurriculumID> <# Courses> <MemberID> ... <MemberID>                       ##
##Unavailability_Constraints: <CourseID> <Day> <Day_Period>                             ##
##########################################################################################
for file_num in range(7):
    total_time = 0.0
    print "File Name: " + file_name + str(file_num + 1)
    showtime = strftime("%Y%m%d_%H%M%S", localtime())
    myfile = results_path + showtime + ".txt"
    g = open(myfile, 'w')


    ##########################################
    ####### Reading data from file ###########
    ##########################################

    myfile = data[file_index] + file_name + str(file_num + 1) + data_format
    f = open(myfile, 'r')
    data_name = re.sub("Name: ", "", f.readline())
    number_of_course = int(re.sub("[^0-9]", "", f.readline()))
    number_of_classroom = int(re.sub("[^0-9]", "", f.readline()))
    number_of_days = int(re.sub("[^0-9]", "", f.readline()))
    number_of_period = int(re.sub("[^0-9]", "", f.readline()))
    number_of_curricula = int(re.sub("[^0-9]", "", f.readline()))
    number_of_constraints = int(re.sub("[^0-9]", "", f.readline()))
    timeslots = number_of_days * number_of_period
    number_of_lecures = 0
    courses = []
    courses_dict = {}
    index_to_course_dict = {}
    lecture_to_course = []
    classrooms = []
    classrooms_indicator = []
    conflict_in_classroom = []
    conflict_index = []
    curricula = []
    conflict_set = set()
    conflict_list = []
    unavailability = {}
    unavailability_update = {}
    availability = {}
    lecture_of_course = []
    number_of_each_course = {}
    f.readline()
    f.readline()
    for i in range(number_of_course):
        courses.append(f.readline().split())
        courses_dict[courses[i][0]] = i
        number_of_each_course[courses[i][0]] = int(courses[i][2])
        index_to_course_dict[i] = courses[i][0]
        number_of_lecures += int(courses[i][2])
        lecture_of_course.append(int(courses[i][2]))
        for lec in range(int(courses[i][2])):
            lecture_to_course.append(courses[i][0])
            tmp = set()
            conflict_list.append(tmp)
        temp = set()
        for t in range(timeslots):
            temp.add(t)
        availability[courses[i][0]] = temp
    for item in courses:
        for element in courses:
            if (item[1] == element[1]):
                conflict_set.add((item[0], element[0]))
                conflict_list[courses_dict[item[0]]].add(element[0])

    f.readline()
    f.readline()
    classrooms_list = list()
    for i in range(number_of_classroom):
        temp_seet = set()
        classrooms_list.append(i)
        classrooms.append(f.readline().split())
        classrooms_indicator.append(0)
        conflict_in_classroom.append(0)
        conflict_index.append(temp_seet)
    f.readline()
    f.readline()
    for i in range(number_of_curricula):
        curricula.append(f.readline().split())
    for item in curricula:
        for i in range(2, len(item)):
            for j in range(2, len(item)):
                conflict_set.add((item[i], item[j]))
                for l in range(lecture_of_course[courses_dict[item[i]]]):
                    conflict_list[courses_dict[item[i]]].add(item[j])
    f.readline()
    f.readline()
    temp1 = ""
    temp_set = set()
    for i in range(number_of_constraints):
        temp = f.readline().split()
        t = int(temp[1]) * number_of_period + int(temp[2])
        if ((temp[0] != temp1) & (temp1 != "")):
            unavailability[temp1] = temp_set
            availability[temp1] = availability[temp1] - unavailability[temp1]
            temp_set = set()
            temp_set.add(t)
        else:
            temp_set.add(t)
        temp1 = temp[0]

    default = set()
    max_violation = number_of_lecures * number_of_lecures
    time_room = timeslots * number_of_classroom
    print "Number of Timeslots = ", timeslots
    print "Number of Classrooms = ", number_of_classroom
    print "Number of Lectures = ", number_of_lecures
    for run in range(number_of_runs):
        z3_file = open(z3_result + str(file_num + 1) + z3_result_extention + str(run + 1) + z3_txt, 'r')
        z3_feasible_sol = ["-1"] * number_of_classroom
        for c in range(number_of_classroom):
            z3_feasible_sol[c] = ["-1"] * timeslots
        is_sat = z3_file.readline()
        print is_sat
        if (len(is_sat) == 4):
            counter = 1
            tmp_timeslot = list()
            tmp_room = list()
            for index in range(number_of_lecures):
                line = z3_file.readline()
                tmp_timeslot.append(int(filter(str.isdigit, line[5 + len(str(index + 1)):])))
            for index in range(number_of_lecures):
                line = z3_file.readline()
                tmp_room.append(int(filter(str.isdigit, line[5 + len(str(index + 1)):])))

            for index in range(number_of_lecures):
                z3_feasible_sol[tmp_room[index]][tmp_timeslot[index]] = lecture_to_course[index]
            lines = z3_file.readlines()
            z3_elapsed_time = float(re.findall(r"[-+]?\d*\.\d+|\d+", lines[len(lines) - 1])[0])
            # print z3_feasible_sol
            violation = False
            classrooms_frespace = []
            # print timetable
            for cc in range(number_of_classroom):
                tmp = 0
                for tt in range(timeslots):
                    if (z3_feasible_sol[cc][tt] == "-1"):
                        tmp += 1
                    else:
                        lecc = z3_feasible_sol[cc][tt]
                        classrooms_indicator[cc] = 1
                        if (tt not in availability[lecc]):
                            violation = True
                            break
                        for ccc in range(number_of_classroom):
                            if ((ccc != cc) & ((lecc, z3_feasible_sol[ccc][tt]) in conflict_set)):
                                violation = True
                                break
                    if (violation == True):
                        break
                if (violation == True):
                    print (" Conflict!!!!!!!!!!\n")
                    break
                classrooms_frespace.append(tmp)
        else:
            print "!!! NO SOLUTION !!!"
            violation = True
        if (violation == False):
            print "**** a feasible solution is found ****"
            print "#Run:  " + str(run)
        print "\n\n"
        if (violation == False):
            print "Simulated Annealing started...\n"
            start_time = timeit.default_timer()
            sim_timetable, sim_cost = sim_anneal(z3_feasible_sol, conflict_set, classrooms_indicator,
                                                 availability, unavailability, timeslots)
            print "Cost =", sim_cost
            elapsed = timeit.default_timer() - start_time
            g.write("File name: " + file_name + str(file_num + 1) + "\n")
            g.write("Z3 feasible solution \n")
            g.write(
                "Days = " + str(number_of_days) + "\n" + "Periods per day = " + str(
                    number_of_period) + "\n" + "Number of Courses = " + str(
                    number_of_lecures) + "\n")
            g.write("Number of rooms = " + str(number_of_classroom) + "\n")
            g.write("Number of iteration = " + str(iteration) + "\n")
            g.write("Elapsed time : " + str(elapsed) + " seconds" + "\n")
            g.write(str(fitness_function(sim_timetable, conflict_set, unavailability, counter)) + "\n")
            elapsed = timeit.default_timer() - start_time
            violation = False
            classrooms_frespace = []
            for cc in range(number_of_classroom):
                tmp = 0
                for tt in range(timeslots):
                    if (sim_timetable[cc][tt] == "-1"):
                        tmp += 1
                    else:
                        lecc = sim_timetable[cc][tt]
                        for ccc in range(number_of_classroom):
                            if ((ccc != cc) & ((lecc, sim_timetable[ccc][tt]) in conflict_set)):
                                print " Conflict!!!!!!!!!!"
                                violation = True
                                break
                    if (violation == True):
                        break
                classrooms_frespace.append(tmp)
                # g.write("Classrooms Freespace Individual #" + str(population.index(individual) + 1) +  "\n")
                # g.write(str(classrooms_frespace) + "\n")
        g.write("Elapsed time : " + str(elapsed + z3_elapsed_time) + " seconds" + "\n")
        total_time = total_time + (elapsed + z3_elapsed_time)
        g.write(
            "\n" + "--------------------------------------------------------------------------------------------------------------" + "\n")
        g.write(
            "##############################################################################################################" + "\n")
        g.write(
            "--------------------------------------------------------------------------------------------------------------" + "\n")
    g.write("total time:  " + str(total_time) + "\n")
g.close()
