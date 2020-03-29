'''
File:       Genetic Algorithm.py
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



###########################################
##### Simple  Neighborhood Relation #######
###########################################

def neighbor_simple(nei_timetable, nei_conflict_set, nei_availability,  nei_unavailability, nei_timeslot, ind):
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
    while (room1_lec != []):
        lect = room1_lec.pop()
        l = lect[0]
        tt = lect[1]
        tmp = set()
        tmp = copy.copy(room2_freespace)
        while (tmp):
            t = tmp.pop()
            violated = True
            if (t in nei_availability[l]):
                violated = False
                for c in range(number_of_classroom):
                    lect2 = nei_timetable[c][t]
                    if (lect2 != "-1"):
                        if ((t != tt) | (c != room1)):
                            if (c != room2):
                                if ((l, lect2) in nei_conflict_set):
                                    violated = True
                                    break
            if (violated == False):
                nei_timetable[room2][t] = l
                nei_timetable[room1][tt] = "-1"
                room2_freespace.discard(t)
                break
    return nei_timetable



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
            # new_timetable = neighbor(old_timetable, sim_conflict_set, sim_availability,  sim_unavailability, sim_timeslot, i)
            new_timetable = neighbor_simple(old_timetable, sim_conflict_set, sim_availability, sim_unavailability, sim_timeslot, i)
            new_cost = cost(new_timetable)
            ap = acceptance_probability(old_cost, new_cost, T)
            if ap > random.random():
                old_timetable = copy.copy(new_timetable)
                old_cost = copy.copy(new_cost)
            i += 1
        counter_T += 1
        T = T * alpha
    return old_timetable, old_cost

####################################################
##### Making an initial timetable first-fit ########
####################################################

def initial_timetable_firstfit(availability, lecture_of_course, courses_dict, index_to_course, classrooms_list):
    number_of_availability = list()
    lecture_of_course = copy.copy(lecture_of_course)
    for item in availability:
        for i in range(lecture_of_course[courses_dict[item]]):
            tmp = list()
            tmp.append(len(availability[item]))
            tmp.append(courses_dict[item])
            number_of_availability.append(tmp)
    sorted_by_availability = sorted(number_of_availability, key=itemgetter(0))
    left_course = list()
    room_freespace = [timeslots] * number_of_classroom
    first_fit_timetable = ["-1"] * number_of_classroom
    for c in  range(number_of_classroom):
        first_fit_timetable[c] = ["-1"] * timeslots
    class_indicator = [0] * number_of_classroom
    for corse in sorted_by_availability:
        random.shuffle(classrooms_list)
        for room in classrooms_list:
            for tiime in range(timeslots):
                violated = 0
                if (first_fit_timetable[room][tiime] != "-1"):
                    violated = 1
                if (tiime not in availability[index_to_course[corse[1]]]):
                    violated = 1
                if (violated == 0):
                    first_fit_timetable[room][tiime] = index_to_course[corse[1]]
                    class_indicator[room] = 1
                    room_freespace[room] -= 1
                    break
            if (violated == 0):
                break
        if (violated == 1):
            left_course.append(corse[1])
    counter = -1
    if (len(left_course) > 0 ):
        print "No solution"
        print "No left course: " + str(len(left_course))
    return first_fit_timetable

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


##########################
#######  mutation ########
##########################


def mutation(pop, conflict_sets, unavailability_mut):
    mutation_rate = random.randint(1,10)
    if (mutation_rate == 6):
        default = set()
        timeslot_fitness = []
        for c in range(number_of_classroom):
            for t in range(timeslots):
                lec1 = pop[c][t]
                tmp_sum = 0
                if (lec1 != "-1"):
                    if (t in unavailability_mut.get(lec1,default)):
                        tmp_sum += 1
                    for cc in range(number_of_classroom):
                        if ((cc != c) & ((lec1, pop[cc][t]) in conflict_sets)):
                            tmp_sum += 1
                timeslot_fitness.append(tmp_sum)
        max_conflicted_index = timeslot_fitness.index(max(timeslot_fitness))
        room_index = max_conflicted_index/timeslots
        time_index = max_conflicted_index%timeslots
        conflict_in_each_timeslot = []
        room_time_index = []
        lec1 = pop[room_index][time_index]
        for c in range(number_of_classroom):
            for t in range(timeslots):
                tmp_sum = 0
                if (pop[c][t] == "-1"):
                    if (t in unavailability_mut.get(lec1,default)):
                        tmp_sum += 1
                    for cc in range(number_of_classroom):
                        if ((cc != c) & ((lec1, pop[cc][t]) in conflict_sets)):
                            tmp_sum += 1
                    conflict_in_each_timeslot.append(tmp_sum)
                    room_time_index.append([c, t])
        new_room = room_time_index[conflict_in_each_timeslot.index(min(conflict_in_each_timeslot))][0]
        new_timeslot = room_time_index[conflict_in_each_timeslot.index(min(conflict_in_each_timeslot))][1]
        pop[new_room][new_timeslot] = pop[room_index][time_index]
        pop[room_index][time_index] = "-1"
    return pop
##########################
#######  Crossover #######
##########################

def crossover(par1, par2):
    offspring1 = []
    offspring2 = []
    crossover_point = (number_of_period/2) + 1
    for i in range(number_of_classroom):
        tmp_spring1 = []
        tmp_spring2 = []
        for t in range(timeslots):
            if (t % number_of_period < crossover_point):
                tmp_spring1.append(par1[i][t])
                tmp_spring2.append(par2[i][t])
            else:
                tmp_spring1.append(par2[i][t])
                tmp_spring2.append(par1[i][t])
        offspring1.append(tmp_spring1)
        offspring2.append(tmp_spring2)
    offspring1_course_counter = {}
    offspring2_course_counter = {}
    for ccc in courses:
        offspring1_course_counter[ccc[0]] = 0
        offspring2_course_counter[ccc[0]] = 0
    timeslot_fitness1 = []
    timeslot_fitness2 = []
    for c in range(number_of_classroom):
        for t in range(timeslots):
            lec1 = offspring1[c][t]
            lec2 = offspring2[c][t]
            tmp1_sum = 0
            tmp2_sum = 0
            if (lec1 != "-1"):
                for cc in range(number_of_classroom):
                    if ((cc != c) & ((lec1, offspring1[cc][t]) in conflict_set)):
                        tmp1_sum += 1
                offspring1_course_counter[offspring1[c][t]] += 1
            timeslot_fitness1.append(tmp1_sum)
            if (lec2 != "-1"):
                for cc in range(number_of_classroom):
                    if ((cc != c) & ((lec2, offspring2[cc][t]) in conflict_set)):
                        tmp1_sum += 1
                offspring2_course_counter[offspring2[c][t]] += 1
            timeslot_fitness2.append(tmp2_sum)
    offspring1_remainder = {key: number_of_each_course[key] - offspring1_course_counter.get(key, 0) for key in number_of_each_course.keys()}
    offspring2_remainder = {key: number_of_each_course[key] - offspring2_course_counter.get(key, 0) for key in number_of_each_course.keys()}
    for item in offspring1_remainder:
        deleted = 0
        events = list()
        if ((offspring1_remainder[item] < 0) & (item != "-1")):
            for c in range(number_of_classroom):
                for t in range(timeslots):
                    if (offspring1[c][t] == item):
                        events.append([c, t, timeslot_fitness1[c * timeslots + t]])
            sorted_events = sorted(events, key=itemgetter(2),reverse=True)
            while (deleted != -1 * offspring1_remainder[item]):
                pop_item = sorted_events.pop()
                offspring1[pop_item[0]][pop_item[1]] = "-1"
                deleted += 1
    for item in offspring2_remainder:
        deleted = 0
        events = list()
        if ((offspring2_remainder[item] < 0) & (item != "-1")):
            for c in range(number_of_classroom):
                for t in range(timeslots):
                    if (offspring2[c][t] == item):
                        events.append([c, t, timeslot_fitness2[c * timeslots + t]])
            sorted_events = sorted(events, key=itemgetter(2),reverse=True)
            while (deleted != -1 * offspring2_remainder[item]):
                pop_item = sorted_events.pop()
                offspring2[pop_item[0]][pop_item[1]] = "-1"
                deleted += 1
    for item in offspring1_remainder:
        if ((offspring1_remainder[item] > 0) & (item != "-1")):
            for c in  range(number_of_classroom):
                for t in range(timeslots):
                    violated = 0
                    if ((offspring1[c][t] == "-1") & (offspring1_remainder[item] > 0)):
                        for cc in range(number_of_classroom):
                            if ((cc != c) & ((item, offspring1[cc][t]) in conflict_set)):
                                violated = 1
                        if (violated == 0):
                            offspring1[c][t] = item
                            offspring1_remainder[item] -= 1
                            break
    for item in offspring2_remainder:
        if ((offspring2_remainder[item] > 0) & (item != "-1")):
            for c in  range(number_of_classroom):
                for t in range(timeslots):
                    violated = 0
                    if ((offspring2[c][t] == "-1") & (offspring2_remainder[item] > 0)):
                        for cc in range(number_of_classroom):
                            if ((cc != c) & ((item, offspring2[cc][t]) in conflict_set)):
                                violated = 1
                        if (violated == 0):
                            offspring2[c][t] = item
                            offspring2_remainder[item] -= 1
                            break
    for item in offspring1_remainder:
        added = 0
        events = list()
        if ((offspring1_remainder[item] > 0) & (item != "-1")):
            for c in range(number_of_classroom):
                for t in range(timeslots):
                    if (offspring1[c][t] == "-1"):
                        offspring1[c][t] = item
                        added += 1
                    if (added == offspring1_remainder[item]):
                        break
                if (added == offspring1_remainder[item]):
                    offspring1_remainder[item] = 0
                    offspring1_course_counter[item] += added
                    break
    for item in offspring2_remainder:
        added = 0
        if ((offspring2_remainder[item] > 0) & (item != "-1")):
            for c in range(number_of_classroom):
                for t in range(timeslots):
                    if (offspring2[c][t] == "-1"):
                        offspring2[c][t] = item
                        added += 1
                    if (added == offspring2_remainder[item]):
                        break
                if (added == offspring2_remainder[item]):
                    offspring2_remainder[item] = 0
                    offspring2_course_counter[item] += added
                    break
    return offspring1, offspring2

####################################
####### Tournament Selection #######
####################################
def tournament_selection(pop, k, N, pop_fitness):
    best = random.randint(0, N -1)
    for i in range(k-1):
        ind = random.randint(0, N -1)
        if ((pop_fitness[ind] < pop_fitness[best])):
            best = ind
    return pop[best]


#######################################
###### Roulette Wheel Selection #######
#######################################
def roulette_wheel_selection(pop, conflict_sets, generation):
    sum_pop = 0
    pop_fitness = []
    violation_existence = []
    for individual in pop:
        violation, fitness_value = fitness_function(individual,conflict_sets, generation)
        sum_pop = sum_pop + (fitness_value)
        pop_fitness.append(fitness_value)
        violation_existence.append(violation)
    indice = [-1]*2
    for i in range(2):
        fixed_point = random.random()
        tmp_sum = 0.0
        while (tmp_sum < fixed_point):
            indice[i] += 1
            tmp_sum += (float(pop_fitness[indice[i]]) / float(sum_pop))
    return pop[indice[0]], pop[indice[1]]



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
# number of population#
# number of iteration #
# number of runs      #
#######################

iteration = 100
number_of_population = 500
number_of_runs = 10
file_index = 0
data = ["..\\Dataset\\EarlyDatasets\\", "..\\Dataset\\HiddenDatasets\\", "..\\Dataset\\LateDatasets\\"]
data_folder = ["EarlyDatasets", "HiddenDatasets", "LateDatasets"]
file_name = "comp0"
data_format = ".ctt"
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
    print "File Name: " + file_name + str(file_num + 1)
    showtime = strftime("%Y%m%d_%H%M%S", localtime())
    myfile = results_path + showtime + ".txt"
    g = open(myfile, 'w')
    gg = open(results_path + "summary_result" + showtime[9:14] + ".txt", 'w')
    gg.write("File name: " + file_name + str(file_num + 1) + "\n")
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
    
    total_start_time = timeit.default_timer()

    print "Number of Timeslots = ", timeslots
    print "Number of Classrooms = ", number_of_classroom
    for run in range(number_of_runs):
        start_time = timeit.default_timer()
        population = []
        ##########################################
        ##### Making an initial timetable ########
        ##########################################
        for i in range(number_of_population):
            timetable = initial_timetable_firstfit(availability, lecture_of_course, courses_dict, index_to_course_dict,classrooms_list)
            population.append(timetable)
        print "Population Size = ", number_of_population
        counter = 0.0
        feas_sol_find = False
        best_population = []
        number_of_best_poppulation = 2
        while (counter < iteration):
            population_fitness = []
            tmp_fitness = []
            for individual in population:
                population_fitness.append(fitness_function(individual, conflict_set, unavailability, counter)+(population.index(individual),))
            population_fitness.extend(best_population)
            sorted_population_fitness = sorted(population_fitness, key=itemgetter(0,1,2))
            if (sorted_population_fitness[0][0] == False):
                feasible_sol = population[sorted_population_fitness[0][2]]
                ga_fitness = sorted_population_fitness[0]
                feas_sol_find = True
                print "Simulated Annealing Started..."
                break
            best_population = []
            best_population_index = []
            for i in range(number_of_best_poppulation):
                best_population.append(sorted_population_fitness[i])
                best_population_index.append(best_population[i][2])
            print int(counter), "of",  iteration, "iteration..."
            number_of_next_generation = copy.copy(number_of_population)
            number_of_parents = number_of_population/2 - number_of_best_poppulation/2
            next_generation = []
            selected_parents = []
            for i in range(number_of_parents):
                parent1 = tournament_selection(population, 2, number_of_population, population_fitness)
                parent2 = tournament_selection(population, 2, number_of_population, population_fitness)
                selected_parents.append(parent1)
                selected_parents.append(parent2)
                child1, child2 = crossover(parent1, parent2)
                next_generation.append(mutation(child1, conflict_set, unavailability))
                next_generation.append(mutation(child2, conflict_set, unavailability))
            for i in range(number_of_best_poppulation/2):
                parent1 = population[best_population_index[i]]
                parent2 = population[best_population_index[i + number_of_best_poppulation/2]]
                child1, child2 = crossover(parent1, parent2)
                next_generation.append(mutation(child1, conflict_set, unavailability))
                next_generation.append(mutation(child2, conflict_set, unavailability))
            selected_population_fitness = []
            population = list()
            number_of_population = copy.copy(len(next_generation))
            population = copy.copy(next_generation)
            counter += 1.0
            tmp_course_counter = {}
            for ccc in courses:
                tmp_course_counter[ccc[0]] = 0
            for ccc in range(number_of_classroom):
                for ttt in range(timeslots):
                    if (population[0][ccc][ttt] != "-1"):
                        tmp_course_counter[population[0][ccc][ttt]] += 1

        if (feas_sol_find == True):
            sim_timetable, sim_cost = sim_anneal(feasible_sol, conflict_set, classrooms_indicator,
                       availability, unavailability, timeslots)
            print "Cost =", sim_cost
            elapsed = timeit.default_timer() - start_time
            g.write("File name: " + file_name + str(file_num + 1) + "\n")
            g.write("firstfit initializing \n")
            g.write("GA fitness = " + str(ga_fitness) + "\n")
            # g.write("Best population append \n")
            g.write(
                "Days = " + str(number_of_days) + "\n" + "Periods per day = " + str(
                    number_of_period) + "\n" + "Number of Courses = " + str(
                    number_of_lecures) + "\n")
            g.write("Number of rooms = " + str(number_of_classroom) + "\n")
            g.write("Number of iteration = " + str(iteration) + "\n")
            g.write("Run " + str(run + 1) + " of " + str(number_of_runs) + "\n")
            g.write("Elapsed time : " + str(elapsed) + " seconds" + "\n")
            g.write("Break iteration : " + str(counter) + "\n")
            g.write("Population Size = " + str(number_of_population) + "\n")
            g.write("Population Fitness " + str(1) + " ... " + str(number_of_population) + "\n")
            g.write(str(fitness_function(sim_timetable, conflict_set,unavailability,counter)) + "\n")
            gg.write(str(number_of_runs) + "\t" + str(fitness_function(sim_timetable, conflict_set,unavailability,counter)[1]) + "\n")
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
        elapsed = timeit.default_timer() - start_time
        g.write("Elapsed time : " + str(elapsed) + " seconds" + "\n")
        g.write("\n" + "--------------------------------------------------------------------------------------------------------------" + "\n")
        g.write("##############################################################################################################" + "\n")
        g.write("--------------------------------------------------------------------------------------------------------------" + "\n")
    total_elapsed = timeit.default_timer() - total_start_time
    g.write("\n\nTotal runtime" + str(total_elapsed))
    g.close()
    gg.close()
