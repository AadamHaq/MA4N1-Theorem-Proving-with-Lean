# MA4N1-Theorem-Proving-with-Lean

This GitHub repository is dedicated to proving Lusin's Theorem in Lean. An outline of the initial project is found within the [Lusin Theorem Project Plan pdf file](Lusins%20Theorem%20project%20outline.pdf).

We restrict our attention to the measure space $(\mathbb{R}, \mathcal{B}(\mathbb{R}), \mu)$. In particular, we concern ourselves only with the Borel $\sigma$-algebra for simplicity. 

The theorem statement is as follows: Suppose that $f$ is a measurable function and $A \subset \mathbb{R}^d$ a Borel set with finite measure, i.e. $\mu(A) < \infty$. Then for all $\varepsilon > 0$, there exists a compact subset $K \subseteq A$ such that $\mu(A \backslash K) < \varepsilon$, such that the restriction of $f$ to the set $K$ is continuous.
