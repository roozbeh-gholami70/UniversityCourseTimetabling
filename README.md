# UniversityCourseTimetabling
Implementation of proposed methods for solving University Course Timetabling with Minimizing the Number of Allocated Classroom

These are proposed methods for solving a version of university course timetabling problem where the number of utilized classrooms is the objective.

Hybrid_GCH_SA_withoutCapacity.py is a hybrid heuristic approach when classrooms have equal capacity (number of seats). In this approach the Graph Coloring heuristics find a feasible solution and this solution is feed to SA to improve the number of classrooms.

Hybrid_GCH_SA_withCapacity.py is a hybrid heuristic approach when classrooms have different capacity (number of seats). In this approach the Graph Coloring heuristics find a feasible solution and this solution is feed to SA to improve the number of classrooms.


The 3rd track (Curriculum Based Course Timetabling) of the well-known dataset of International Timetabling Competition (ITC) 2007 http://www.cs.qub.ac.uk/itc2007/ used for testing the performance of methods.
