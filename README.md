Execution
=========

To execute the search for fake quadrics, in the main directory, choose an integer N in [2..6], load magma and type

  ```
     load "Fields/DegreeNPared.txt";
     load "fake_quadric_search.m";
  ```

This will create an array FINALLIST containing fake quadrics in degree N and print verbose output to screen.

To output with more verbosity, change line 9 of fake_quadric_search.m.

(The file CFBoundMathematica.nb can be used to verify numerical computations in the paper.)