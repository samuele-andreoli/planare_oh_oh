load "lib/invariantTable.m";

SetLogFile("orbits.out": Overwrite:= true);
computeOrbitsTable();
UnsetLogFile();