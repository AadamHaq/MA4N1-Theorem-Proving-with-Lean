import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- For regular measure
import Mathlib.MeasureTheory.Measure.Regular



open Nat Int Real Finset MeasureTheory
open scoped Topology

-- namespace MeasureTheory

/-
--- PRELIMINARY INFO---

For simplicity, we restrict our attention to the Borel σ-algebra: this differs slightly from Cohn's measure theory book, which accounts for any σ-algebra containing the Borel σ-algebra.
-/

variable {α β ι : Type*} {m : MeasurableSpace α} [n : MetricSpace β] {μ : Measure α}

-- aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- this is slightly more restrictive than the theorem in Cohn's book

class T2LocallyCompactSpace (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] : Prop
    where

instance (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] :
    T2LocallyCompactSpace α := {}

def T2LocallyCompactSpaceBorel (T2LocallyCompactSpace α) (m : MeasurableSpace α) :=
BorelSpace X

/-
We are using the following BorelSpace class definition, given below.
Namely, this tells us that the measurable sets are exactly the Borel-measurable sets.

class BorelSpace (α : Type*) [TopologicalSpace α] [MeasurableSpace α] : Prop where
    measurable_eq : ‹MeasurableSpace α› = borel α
-/



/-
Theorem 1: the pre-image of a singleton under f measurable is measurable
-/

-- write Theorem 1 here



/-
Theorem 2: the countable union of compact sets is compact.
-/

-- write Theorem 2 here



/-
Proposition 1.2.5 in Cohn's book [continuity of measure]: μ(⋃ A_k) = lim μ(A_k) for an increasing sequence of sets {A_k} with A = ⋃ A_k
-/

-- write Proposition 1.2.5 here



/-
Proposition 7.2.6 in Cohn's book [compactness-supremum characterisation of a set under a regular measure]: let X be a Hausdorff space endowed with the Borel σ-algebra B. Let μ be a regular measure on B.
If A ∈ B (and A is σ-finite under μ) then μ(A) = sup{μ(K) : K ⊆ A, K compact}.
-/

-- write Proposition 7.2.6 here



/-
Intermediate lemma: if f is a measurable function with K = ⋃K_i for K_i disjoint compact sets, then f is constant on each K_i. Hence, f|K (i.e. f restricted to the set K) continuous.
-/

-- write intermediate lemma here



/- Lusin's Theorem for measurable f which takes **countably many values**. Suppose that f takes countable many values {a_1,...,a_k}. Define A_k = f^-1(a_k) for each k, with A = ⋃ A_k.

Now apply Prop 1.2.5 to show that lim μ(⋃ A_k) = μ(A). Since μ is regular, μ(A) < ∞ and so the measure of A \ ⋃_k^n A_k is arbitrarily small.

We now apply the regularity of μ to apply a similar argument, only this time with compact K = ⋃ K_k for K_k compact.
-/

-- write countable f theorem here



/-
From proof in MA359 notes: the sequence of functions f_n := 2^-n * floor(2^n f) converges uniformly to f.
-/

-- write uniform convergence proof here



/- Lusin's Theorem for f taking **uncountably many values**:
-/

-- write uncountable f theorem here



-- Lusin's Theorem!
theorem lusin {X : T2LocallyCompactSpace α} [Measure.Regular μ]

#check Field

#synth T2Space ℝ
#synth LocallyCompactSpace ℝ
#synth TopologicalSpace ℝ
#synth T2LocallyCompactSpace ℝ
