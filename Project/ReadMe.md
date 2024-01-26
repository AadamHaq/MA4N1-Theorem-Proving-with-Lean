This GitHub repository is dedicated to proving Lusin's Theorem in Lean. An outline of the initial project is found within the [Lusin Theorem Project Plan pdf file](Lusins%20Theorem%20project%20outline.pdf). The file that proves [Egorov's Theorem](egorov.lean) was used as inspiration and so has been uploaded. The original proof was made by Kexing Ying. 

We restrict our attention to the measure space $(\mathbb{R}, \mathcal{B}(\mathbb{R}), \mu)$. In particular, we concern ourselves only with the Borel $\sigma$-algebra for simplicity. 

The theorem statement is as follows: Suppose that $f$ is a measurable function and $A \subset \mathbb{R}^d$ a Borel set with finite measure, i.e. $\mu(A) < \infty$. Then for all $\varepsilon > 0$, there exists a compact subset $K \subseteq A$ such that $\mu(A \backslash K) < \varepsilon$, such that the restriction of $f$ to the set $K$ is continuous.

The proof of the theorem involves proving the result for when $f$ takes either finitely many, countably many or uncountably many values. We have proven the result in the case where $f$ takes countably many values. This is our final project file, titled **'Lusin_Theorem_Countable.lean'**, which can be found in this folder. We also provide an (incomplete) proof for the finite case, which can be found in the `Extensions' folder.
