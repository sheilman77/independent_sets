The file `tree_independent_set_verifier.cpp` is C++ code that verifies that all integers up to some specified threshold
can be written as the number of independent sets of some tree (with 823 possible exceptions).

The file `tree_missing_list` contains 823 positive integers that cannot be written as the number of independent sets of any tree.
It is conjectured that these are the only 823 positive integers with this property.

For these 823 numbers, the file `verify_connected_planar_tree_missing.py` verifies that all of these integers can be written as 
the number of independent sets of a planar graph.  And the file `verify_unicyclic_or_forest.py` verifies that all of these integers except 71, 119, 191
and 203 can be written as the number of independent sets of a unicyclic graph or a forest (and these graphs $G=(V,E)$ satisfy $|E|/|V|\leq1$).  

For the remaining four numbers:
- $C_{4}\sqcup K_{1,4}$ has $7\cdot17=119$ independent sets, and $|E|/|V|=8/9<1$
- $C_{4}\sqcup C_{7}$ has $7\cdot 29=203$ independent sets, and $|E|/|V|=11/11=1$

Since 71 and 191 are prime, these two numbers cannot be realized as the number of indpenedent sets of disconnected graphs.  Since they also cannot be realized as the number of independent sets of a tree or unicyclic graph, this means a graph with that number of independent sets must have |E|/|V|>1.  Here are examples with smallest possible average degree.
- Define $G$ to be $K_{2,3}$ with two leaves attached to a degree 3 vertex and one leaf attached to another degree 3 vertex.  Then $G$ has 71 independent sets, and $|E|/|V|=9/8>1$.
- Define $G$ to have vertices $a,b,c,d,e,f,g,h,i,j,k$ with edges $ab,bc,ca,cd,ae,ef,bg,gh,gi,hi,hj,jk$.  Then $G$ has 191 independent sets and $|E|/|V|=12/11$.
