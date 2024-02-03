## Overview

This GitHub repository is dedicated to proving Lusin's Theorem in Lean. An outline of the initial project is found within the [Lusin Theorem Project Plan pdf file](Lusins%20Theorem%20project%20outline.pdf). The file that proves [Egorov's Theorem](egorov.lean) was used as inspiration and so has been added to this repo for reference. The original proof was made by Kexing Ying. 

We restrict our attention to the measure space $(\mathbb{R}, \mathcal{B}(\mathbb{R}), \mu)$. In particular, we concern ourselves only with the Borel $\sigma$-algebra $\mathcal{B}(\mathbb{R})$ for simplicity. Note that this is a slight simplification of the theorem statement given in Cohn's "Measure Theory" book, which states the theorem for any $\sigma$-algebra $\mathcal{A}$ which contains the Borel $\sigma$-algebra.

Our (slightly simplified) theorem statement is as follows: Suppose that $f$ is a measurable function and $A \subset \mathbb{R}^d$ a Borel set with finite measure, i.e. $\mu(A) < \infty$. Then for all $\varepsilon > 0$, there exists a compact subset $K \subseteq A$ such that $\mu(A \backslash K) < \varepsilon$, such that the restriction of $f$ to the set $K$ is continuous.

### Main submission file
Our final project file is titled **'Lusin_Theorem_Countable.lean'** and can be found directly in the 'Final Submission' folder of this repository.

## Limitations and extensions
The proof of the theorem involves proving the result for when $f$ takes either finitely many, countably many or uncountably many values. We have proven the result in the case where $f$ takes countably many values. This is our final project file, titled **'Lusin_Theorem_Countable.lean'**, which can be found in this folder. We also provide an (incomplete) proof for the finite case, which can be found in the `Extensions' folder. The goal would have been to then progress to the uncountable f case.

Concluding all three cases in full, the next step would be to prove the weaker statement given in Cohn's book, which proves the result for all $\mathcal{A}$ with $\mathcal{B}(\mathbb{R}) \subset \mathcal{A}$. Cohn's version of Lusin's Theorem has an additional statement, but we did not include this in our project because it was not discussed in Warwick's MA359 Measure Theory course.
