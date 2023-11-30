import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Regular
-- for sequence indexing with ι
import Mathlib.Init.Order.Defs

open Nat Int Real Finset MeasureTheory ENNReal Set Filter TopologicalSpace
open scoped Topology

namespace MeasureTheory

class T2LocallyCompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- In a locally compact space,
    every neighbourhood of every point contains a compact neighbourhood of that same point.
    In a T2 space distinct points are contained within disjoint open sets--/
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s
  t2 : ∀ (x y : X), x ≠ y → ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v


variable  {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
variable [BorelSpace ℝ] (f: α → ℝ)
-- variable [Preorder ι] [Countable ι] (a : ι → ℝ)
variable (a : ℕ → ℝ)

-- definitions from Giovanni:
-- Union_A_i is the preimage of a countable union singletons under a measurable function
def Union_A_i := f ⁻¹'(⋃ i, {a i})
-- A_i is the preimage of a singleton under a measurable function. We select an i from our indexing set
def A_i (i : ℕ) := f ⁻¹'({a i})

-- NEED TO ALSO SAY SOMEWHERE THAT μ(Union_A_i) < ∞.


-- We have defined a : ι → ℝ  i.e. a_1, a_2,...
theorem countable_union_singleton_measurable : MeasurableSet (⋃ i, {a i}) := by
  refine MeasurableSet.iUnion ?_
  intro b
  refine IsClosed.measurableSet ?h.h
  exact T1Space.t1 (a b)
  done


theorem preimage_union_singleton_measurable (hf : Measurable f) : MeasurableSet (f ⁻¹'(⋃ i, {a i})) := by
  apply MeasurableSet.preimage  -- "undo" the preimage via a lemma that takes the measurability instances
  · exact countable_union_singleton_measurable a
  · exact hf
  done


-- Ameer's docstrings

-- pre-image of a measurable set under measurable f is measurable: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Basic.html#measurableSet_preimage


/-
Theorem: the pre-image of a **singleton** under f measurable is measurable
-/

-- result from Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Defs.html#MeasurableSingletonClass

-- e.g. "apply Mathlib.MeasureTheory.MeasurableSpace.Defs.measurableSet_singleton"


/-
Theorem: union of measurable sets is measurable.
-/

-- write mathlib reference here



/-
Theorem: the countable union of compact sets is compact.

-- For the proof, I think we will want to invoke: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#isCompact_iUnion

-- e.g. "apply Mathlib.Topology.Compactness.Compact.isCompact_iUnion"
-/


-- NEED TO WORK ON THIS NEXT!
theorem measure_notConvergentSeq_tendsto_zero  :
    Tendsto (fun N => μ (⋃ i, f ⁻¹'{a i}) \ f ⁻¹' (⋃ i ∈ Set.Icc 1 N, {a i})) atTop (𝓝 0) := by sorry

/-
Proposition 1.2.5 in Cohn's book [continuity of measure]: μ(⋃ A_k) = lim μ(A_k) for an increasing sequence of sets {A_k} with A = ⋃ A_k

-- result from Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/MeasureSpace.html#MeasureTheory.tendsto_measure_iUnion

-- e.g. "apply MeasureTheory.tendsto_measure_iUnion"
-/
-- Theorem 1 of 3 for μ(A \ K) < ε for countable f
-- theorem continuity_of_measure (hm : (μ (f ⁻¹'(⋃ i, {a i}))) ≠ ∞) (ε : ENNReal) : ∃ N : ℕ, μ ((⋃ i, f ⁻¹'{a i}) \ f ⁻¹' (⋃ i ∈ Set.Icc 1 N, {a i})) < ε/2 := by
--   simp only [ge_iff_le, not_le, lt_one_iff, gt_iff_lt, Set.mem_Icc, Set.preimage_iUnion]
--   -- Aadam is working on this proof!
--   sorry
theorem continuity_of_measure (hε : 0 < ε) : ∃ N : ℕ, μ ((⋃ i, f ⁻¹'{a i}) \ f ⁻¹' (⋃ i ∈ Set.Icc 1 N, {a i})) < ENNReal.ofReal (ε * 2⁻¹) := by sorry


/-
Next step: μ(A_n \ K_n) < ε/2n, where the A_k are defined as the pre-images of the {a_k} under f, and the K_k are compact subsets of the A_k.

The N : ℕ given as a hypothesis below should is provided as a result from the continuity_of_measure theorem above.
-/
-- Theorem 2 of 3 for μ(A \ K) for countable f
-- We break this theorem down into two smaller lemmas
lemma compact_subsets_from_regular_measure_condition_1 (n : ℕ) (K : ℕ → Set α) : ∃ i ∈ Set.Icc 1 n, K i ⊂ f ⁻¹'{a i} ∧ IsCompact (K i) := by sorry

lemma compact_subsets_from_regular_measure_condition_2 (n : ℕ) (K : ℕ → Set α) (h1 : ∃ i ∈ Set.Icc 1 n, K i ⊂ f ⁻¹'{a i}) (h2 : IsCompact (K i)) : μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n) := by sorry


/-
Final step involving A = ⋃ A_i, we now claim that the measure of A \ K is less than ε.
-/
-- Theorem 3 of 3 for μ(A \ K) < ε for countable f
-- NEED TO FIX ISSUE WITH INDEX i
theorem measure_of_As_minus_Ks (n : ℕ) (K : ℕ → Set α) (hck : ∀ i ∈ Set.Icc 1 n, IsCompact (K i)) (hc : ∀ i ∈ Set.Icc 1 n, K i ⊂ f ⁻¹'{a i}) (hε : μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n)) : μ (⋃ i, f ⁻¹'{a i} \ ⋃ i, K i) < ε := by sorry


-- The next step of the proof (for countable f) involves demonstrating that f is continuous when restricted to the K given by the above string of 3 proofs. We build up to this with some smaller lemma/theorem statements.

/-
Proposition 7.2.6 in Cohn's book [compactness-supremum characterisation of a set under a regular measure]: let X be a Hausdorff space endowed with the Borel σ-algebra B. Let μ be a regular measure on B.
If A ∈ B (and A is σ-finite under μ) then μ(A) = sup{μ(K) : K ⊆ A, K compact}.

-- class of regular functions in Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html#MeasureTheory.Measure.Regular

-- note that there are definitions of inner regular and outer regular incorporated with this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html
-/

/-
Theorem (kinda obvious but may need a bitesize outline here): If K is a compact subset of a set A and f is constant on A, i.e. A = f^-1({a}) for a singleton {a}, then f is constant on K, i.e. f(K) = {a}.
-/
theorem preimage_of_const_func_on_compact_subset_is_constant (K : Set α) (a : ℝ) (hk : IsCompact K) (hs : K ⊂ f ⁻¹' ({a} : Set ℝ)) : (∀ x ∈ K, f x = a) := by sorry


/-
Lemma: if f is a measurable function which is disjoint on the sets A and B, with f constant on A and f constant on B, then f is continuous on A ⋃ B.
-/
lemma meas_func_const_on_disjoint_pair_is_continuous (A B : Set α) (a b : ℝ) (hf : Measurable f) (ha : ∀ x : A, f x = a) (hb : ∀ x : B, f x = b) (hac : IsCompact A) (hbc : IsCompact B) (hd : A ∩ B = ∅) : ContinuousOn f (A∪B) := by sorry


/-
Theorem using the above: if f is a measurable function and K_1,...,K_n are disjoint sets with K = ⋃ K_i, then f is continuous on K.

Useful resources:
Restriction of a set to a function f: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Set.restrict
-/
theorem meas_func_const_on_disjoint_finite_union_is_continuous (n : ℕ) (K : ℕ → Set α) (hpd: ∀ i ∈ Set.Icc 1 n, Pairwise (Disjoint on K i)) : ContinuousOn f (⋃ i ∈ Set.Icc 1 n, K i) := by sorry





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
-- this may be related (but not the same!): https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.html#stronglyMeasurable_id



-- Lusin's Theorem!
theorem lusin (hf : μ )

-- theorem lusin {X : T2LocallyCompactSpace α} [Measure.Regular μ]
-- theorem LusinonT2LocallyCompactSpace [measure.regular μ]
--  ∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
--   Continuous Set.Restrict f t  := by sorry
