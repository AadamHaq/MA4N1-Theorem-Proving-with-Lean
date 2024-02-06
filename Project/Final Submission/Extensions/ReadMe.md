The proof of [The finite case](https://github.com/AadamHaq/MA4N1-Theorem-Proving-with-Lean/blob/main/Project/Final%20Submission/Extensions/Lusin_Finite_Case.lean) is very similar to that of [the countable case](https://github.com/AadamHaq/MA4N1-Theorem-Proving-with-Lean/blob/main/Project/Final%20Submission/Lusin_Theorem_Countable.lean).

The main differences include:
- New variables
- Adjusted variables, mainly changing the problem setup from $\mathbb{N}$ to 'Set.Icc 1 n'
- Theorems adjusted
- Proofs adjusted- many are similar with subtle differences, but some have major differences such as those involving 'ENN.Real'

Unfortunately, the whole proof could not be completed. 
The theorems named 'finite_collection_disjoint_subset_union', 'disjoint_K' and 'set_diff_union_n' share a common problem. The theorems utilise the evaluation of function A(n+1) which is not possible. A potential solution to this would have been to define the function of A with the input being 'Fin n', for $n \in \mathbb{N}$ instead of 'Set.Icc 1 n'. However this was found too late into the project and major changes would have to occur. Moreover, this alternative formulation may not directly support the desired line of argument.

The aim was to make the file run without any errors, there was one remaining at the time of deadline which we cannot fix.
