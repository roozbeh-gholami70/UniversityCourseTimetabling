'''
File:       Hybrid_GCH_SA.py
Author:     Roozbeh Gholami (gholami.roozbeh70@gmail.com) 
Summary of File:
    This file contains a python code which makes a timetable for
    univesity courses and minimizes the number of classrooms.
    Classrooms have different capacity (number of seats).
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




####################################################
#####     Making an initial timetable     ##########
####  Least Saturation Degree first (SD)  ##########
#######       Largest degree first         #########
#######     Largest enrollment first      ##########
####################################################
def initial_population(availability, classrooms_list, classroom_cap, conflict_lists_index, number_of_lectures, number_of_student):
    number_of_availability_conflict = list()
    for i in range(number_of_lectures):
        tmp = list()
        tmp.append(i)
        tmp.append(len(availability[i]))
        tmp.append(1000-len(conflict_lists_index[i]))
        tmp.append(10000-number_of_student[i])
        number_of_availability_conflict.append(copy.copy(tmp))
    rand_num = random.randint(1,1000)
    if (rand_num % 2 == 0):
        sorted_list = sorted(number_of_availability_conflict, key=itemgetter(1,2,3))
    elif (rand_num % 3 == 0):
        sorted_list = sorted(number_of_availability_conflict, key=itemgetter(1,2,3,0))
    else:
        sorted_list = sorted(number_of_availability_conflict, key=itemgetter(2,1,3))
    sorted_room_list = sorted(classrooms_list, key=itemgetter(1))
    counter = 0
    time1 = time.time()
    while(True):
        initial_timetable = ["-1"] * number_of_classroom
        for c in  range(number_of_classroom):
            initial_timetable[c] = ["-1"] * timeslots
        counter += 1
        left_course = list()
        for lect in sorted_list:
            for room in sorted_room_list:
                if (room[1] >= number_of_student[lect[0]]):
                    available_time_list = list()
                    for tiime in range(timeslots):
                        violated = 0
                        if (initial_timetable[room[0]][tiime] != "-1"):
                            violated = 1
                        if (tiime not in availability[lect[0]]):
                            violated = 1
                        for ccc in range(number_of_classroom):
                                if ((ccc != room[0] ) & (initial_timetable[ccc][tiime]!="-1")):
                                    if(lect[0] in conflict_lists_index[initial_timetable[ccc][tiime]]):
                                        violated = 1
                        if (violated == 0):
                            available_time_list.append(tiime)
                    if (available_time_list != []):
                        initial_timetable[room[0]][random.choice(available_time_list)] = lect[0]
                        violated = 0
                        break
            if (violated == 1):
                left_course.append(lect[0])
        if ((left_course == []) | (time.time() - time1 > 500)):
            break
    solution = True
    if (len(left_course) > 0 ):
        solution = False
        initial_timetable = ["-1"] * 10
    return(initial_timetable,solution)

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



###########################################
##### Simple  Neighborhood Relation #######
###########################################

def neighbor_simple(nei_timetable, nei_conflict_set, nei_availability, nei_timeslot):
    classrooms_space = [0] * number_of_classroom
    for r in range(number_of_classroom):
        for t in range(nei_timeslot):
            if (nei_timetable[r][t] == "-1"):
                classrooms_space[r] += 1
    ind = random.randint(0,1000)
    if (ind % 2 == 0):
        room1 = classrooms_space.index(max(classrooms_space))
    else:
        room1 = random.randint(0, number_of_classroom -1)
    room2 = random.randint(0, number_of_classroom - 1)
    while ((room1 == room2) | (classrooms_capacity[room2] < classrooms_capacity[room1])):
        ind = random.randint(0,1000)
        if (ind % 2 == 0):
            room1 = classrooms_space.index(max(classrooms_space))
        else:
            room1 = random.randint(0, number_of_classroom -1)
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
    for lect in room1_lec:
        l = lect[0]
        tt = lect[1]
        tmp = set()
        tmp = copy.copy(room2_freespace)
        for t in tmp:
            violated = True
            if (t in nei_availability[l]):
                violated = False
                for c in range(number_of_classroom):
                    lect2 = nei_timetable[c][t]
                    if ((lect2 != "-1") & (t != tt)):
                        if (c != room2):
                            if (lect2 in nei_conflict_set[l]):
                                violated = True
                                break
            if (violated == False):
                nei_timetable[room2][t] = copy.copy(l)
                nei_timetable[room1][tt] = "-1"
                room2_freespace.discard(t)
                break
        if (violated == False):
            break
    return nei_timetable


########################################
##### BGM  Neighborhood Relation #######
########################################
def bgm_neighbor(nei_timetable, nei_conflict_set, nei_availability, nei_timeslot):
    classrooms_space = [0] * number_of_classroom
    for r in range(number_of_classroom):
        for t in range(nei_timeslot):
            if (nei_timetable[r][t] == "-1"):
                classrooms_space[r] += 1
    ind = random.randint(0,1000)
    if (ind % 2 == 0):
        room1 = classrooms_space.index(max(classrooms_space))
        room2 = random.randint(0, number_of_classroom -1)
    else:
        room1 = random.randint(0, number_of_classroom -1)
        room2 = classrooms_space.index(min(classrooms_space))
    while ((room1 == room2) | (classrooms_capacity[room2] < classrooms_capacity[room1])):
        ind = random.randint(0,1000)
        if (ind % 2 == 0):
            room1 = classrooms_space.index(max(classrooms_space))
            room2 = random.randint(0, number_of_classroom - 1)
        else:
            room1 = random.randint(0, number_of_classroom -1)
            room2 = classrooms_space.index(min(classrooms_space))
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
        lect_availability = set(copy.copy(nei_availability[item[0]]))
        for t in range(nei_timeslot):
            for r in range(number_of_classroom):
                if ((t != item[1]) & (r != room2) & (r != room1)):
                    if (nei_timetable[r][t] in nei_conflict_set[item[0]]):
                        tmp_set.add(t)
        tmp_availability[str(counter)] = lect_availability - tmp_set
        counter += 1
    matching = bipartiteMatch(tmp_availability)
    for item in matching[0]:
        if item in room2_freespace:
            nei_timetable[room2][item] = tmp_dict[matching[0][item]][0]
            nei_timetable[room1][tmp_dict[matching[0][item]][1]] = "-1"
    for t in range(nei_timeslot):
        lect = nei_timetable[room2][t]
        if (lect != "-1"):
            if ((nei_timetable[room1][t] in nei_conflict_set[lect])):
                for item in room1_lec:
                    if (item[0] == lect):
                        nei_timetable[room1][item[1]] = lect
                        nei_timetable[room2][t] = "-1"
                        break

    return nei_timetable

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


##########################################
###### Simulated annealing function ######
##########################################
def sim_anneal(sim_timetable, sim_conflict_list, sim_classroom_indicator, sim_availability, sim_timeslot, sim_conflict_set, sim_unavailability):
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
            new_timetable = bgm_neighbor(old_timetable, sim_conflict_list, sim_availability, sim_timeslot)
            # new_timetable = neighbor_simple(old_timetable, sim_conflict_list, sim_availability, sim_timeslot)
            new_cost = cost(new_timetable)
            ap = acceptance_probability(old_cost, new_cost, T)
            if ap > random.random():
                old_timetable = copy.copy(new_timetable)
                old_cost = copy.copy(new_cost)
            i += 1
        counter_T += 1
        T = T * alpha
    return old_timetable, old_cost

##########################################
#### Acceptance probability function #####
##########################################
def acceptance_probability(old_cost, new_cost, T):
    return math.exp((new_cost-old_cost)/T)



dataset_list = ["..\\Dataset\\EarlyDatasets\\", "..\\Dataset\\HiddenDatasets\\", "..\\Dataset\\LateDatasets\\"]
number_of_file = 7
number_of_runs = 20

population_size = 20
neighbor_structure = "_BGM"

file_name = "comp0"
file_format = ".ctt"
for dataset in dataset_list:
    for file_num in range(number_of_file):
        results_path = "Results-" + re.sub('.py', '',os.path.basename(__file__)) + "\\" + dataset[11:] 
        if not os.path.exists(results_path):
            os.makedirs(results_path)
        print("Dataset:  " + dataset[11:] + "\nFile Name: " + file_name + str(file_num + 1) + "\n\n")
        runtime_file = open(results_path +  file_name + str(file_num + 1) + "_runtime" + neighbor_structure + ".txt", 'w')
        runtime_file.write("File name: " + file_name + str(file_num + 1) + "\n")
        gg = open(results_path +  file_name + str(file_num + 1) + "_result" + neighbor_structure + ".txt", 'w')
        gg.write("File name: " + file_name + str(file_num + 1) + "\n" + "\nfitness   frequency_average   utilization_average\n") 
    ##########################################
    ####### Reading data from file ###########
    ##########################################

        myfile = dataset + file_name + str(file_num + 1) + file_format
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
        classrooms = []
        classrooms_capacity = []
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
        lectures_availability = []
        timeslot_lectures_availability = []
        lecture_attendence = []
        timeslot_max_range = []
        number_of_each_course = {}
        lectures = []
        lectures_index = {}
        lectures_conflict = []
        lectures_conflict_index = []
        f.readline()
        f.readline()
        cnt = 0
        for i in range(number_of_course):
            courses.append(f.readline().split())
            courses_dict[courses[i][0]] = i
            number_of_each_course[courses[i][0]] = int(courses[i][2])
            index_to_course_dict[i] = courses[i][0]
            number_of_lecures += int(courses[i][2])
            lecture_of_course.append(int(courses[i][2]))
            lec_cnt = set()
            for lec in range(int(courses[i][2])):
                lectures.append(courses[i][0])
                lec_cnt.add(cnt)
                cnt += 1
                tmp = set()
                tmp_lst = list()
                conflict_list.append(copy.copy(tmp))
                lectures_conflict.append(copy.copy(tmp_lst))
                lectures_conflict_index.append(copy.copy(tmp_lst))
                lectures_availability.append(copy.copy(tmp_lst))
                lecture_attendence.append(int(courses[i][4]))
            lectures_index[courses[i][0]] = lec_cnt
            temp = set()
            for t in range(timeslots):
                temp.add(t)
            availability[courses[i][0]] = temp

        for t in range(timeslots):
            timeslot_max_range.append(copy.copy(number_of_classroom))
            empty_list = list()
            timeslot_lectures_availability.append(copy.copy(empty_list))
        for item in courses:
            for element in courses:
                if (item[1] == element[1]):
                    conflict_set.add((item[0], element[0]))
                    conflict_list[courses_dict[item[0]]].add(element[0])
                    for i in lectures_index[item[0]]:
                        lectures_conflict[i].append(element[0])
                        for j in lectures_index[element[0]]:
                            if (i!=j):
                                lectures_conflict_index[i].append(j)

        f.readline()
        f.readline()
        classrooms_list = list()
        room_capacity_list = list()
        for i in range(number_of_classroom):
            temp_seet = set()
            tmp_room = list()
            classrooms_list.append(i)
            classrooms.append(f.readline().split())
            tmp_room.append(i)
            tmp_room.append((1.05)*int(classrooms[i][1]))
            room_capacity_list.append(copy.copy(tmp_room))
            classrooms_capacity.append(int(classrooms[i][1]))
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
                    for ii in lectures_index[item[i]]:
                        if (not(item[j] in lectures_conflict[ii])):
                            lectures_conflict[ii].append(item[j])
                            for jj in lectures_index[item[j]]:
                                lectures_conflict_index[ii].append(jj)
                    for l in range(lecture_of_course[courses_dict[item[i]]]):
                        conflict_list[courses_dict[item[i]]].add(item[j])
        f.readline()
        f.readline()
        temp1 = ""
        temp_set = set()
        tmp_time = [0]*timeslots
        timeslot_list = list(range(0, timeslots))
        for i in range(number_of_constraints):
            temp = f.readline().split()
            t = int(temp[1]) * number_of_period + int(temp[2])
            if ((temp[0] != temp1) & (temp1 != "")):
                unavailability[temp1] = temp_set
                availability[temp1] = availability[temp1] - unavailability[temp1]
                for ii in lectures_index[temp1]:
                    for tt in availability[temp1]:
                        lectures_availability[ii].append(tt)
                        timeslot_lectures_availability[tt].append(copy.copy(ii))
                temp_set = set()
                temp_set.add(t)
            else:
                temp_set.add(t)
            temp1 = temp[0]
        for ii in range(number_of_lecures):
            if (lectures_availability[ii] == []):
                for tt in range(timeslots):
                    lectures_availability[ii].append(tt)
                    timeslot_lectures_availability[tt].append(ii)
        for run in range(number_of_runs):
            allocated_room = [0.0] * number_of_classroom
            print("\nRun: " + str(run + 1))
            start_time = time.time()
            population = list()
            pre_tmp = list()
            feasiblity = False
            print("Initilizing population... ")
            for num_pop in range(population_size):
                tmp = initial_population(lectures_availability, room_capacity_list, classrooms_capacity, lectures_conflict_index, number_of_lecures, lecture_attendence)
                if (tmp[1] == True):
                    feasiblity = True
                    feasible_solution = copy.copy(tmp[0])
                    break
            print("Initilizing is finished... ")
            if (feasiblity == True):
                print("Simulated Annealing Started...")
                sim_timetable, sim_cost = sim_anneal(feasible_solution, lectures_conflict_index, classrooms_indicator,lectures_availability, timeslots,conflict_set, unavailability)
                print("Simulated Annealing Finshed...")
                elapsed_time = time.time() - start_time
                best_utilization = copy.copy(sim_timetable)
                for cc in range(number_of_classroom):
                    for dd in range(number_of_days):
                        if (best_utilization[cc][dd] != "-1"):
                            allocated_room[cc] = 1.0
                            break
                cnt = 0
            else:
                elapsed_time = time.time() - start_time
                print("No initial solution...")
            runtime_file.write(str(elapsed_time) + "\t" + str(sum(allocated_room)) + "\n")
        runtime_file.close()