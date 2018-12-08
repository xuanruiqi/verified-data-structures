# Verified Data Structures/Functional Algorithms

Basically, trying to verify some data structures/functional algorithms 
in Coq/SSReflect, using dependent types, and using `Program` whenever it makes sense 
(unlike most Coq hackers). Currently, mostly formalizing tree structures. Those 
are the algorithms/data structures I have formalized/am formalizing:

* Sorted lists: [vds_sort.v](vds_sort.v)
* Quicksort: [quicksort.v](quicksort.v)
* Red-black trees (with ML types): [red_black.v](red_black.v)
* 2-3 trees (with dependent types); deletion is hard and still in progress: [twothree_dependent.v](twothree_dependent.v) 
  and [twothree_dependent_delete.v](twothree_dependent_delete.v)
  
## Author
Xuanrui (Ray) Qi. Email: [me@xuanruiqi.com](me@xuanruiqi.com).

## License
All of my code is released into the public domain.
