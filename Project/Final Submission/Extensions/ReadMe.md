The proof of [The finite case](https://github.com/AadamHaq/MA4N1-Theorem-Proving-with-Lean/blob/main/Project/Final%20Submission/Extensions/Lusin_Finite_Case.lean) is very similar to that of [the countable case](https://github.com/AadamHaq/MA4N1-Theorem-Proving-with-Lean/blob/main/Project/Final%20Submission/Lusin_Theorem_Countable.lean).

The main differences include:
- New variables
- Adjusted variables mainly changing work from $\mathcal{N}$ to Set.Icc 1 n
- Theorems adjusted
- Proofs adjusted (many are similar with subtle differences, but some have major differences such as those involving ENN.Real)

Unfortunately, the whole proof could not be completed. 
The theorems on lines 195, 210 and 221 have the same issue. The theorems utalise evaluating the function A(n+1) which is impossible. A potential solution to this would have been to define the function of A with the input being Fin n, for $n \in \mathcal{N}$ instead of Set.Icc 1 n, however this was found too late into the project and major changes would have to occur. This solution may also not be correct for what we need to do.
