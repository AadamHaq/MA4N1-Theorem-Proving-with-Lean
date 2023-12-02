import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Init.Order.Defs
import Mathlib.Order.PartialSups

open Nat Int Real Finset MeasureTheory ENNReal
open scoped Topology

-- Aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- This is slightly more restrictive than the theorem in Cohn's book

namespace MeasureTheory

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α ][BorelSpace α]{μ : Measure α}
variable [BorelSpace ℝ] (f: α → ℝ) (a : ℕ → ℝ) (h: Measurable f)
variable (B : Set α)(hm : MeasurableSet B)(hf : μ B ≠ ∞)(hcount : f '' B = Set.range a)

--Checking this works, DELETE LATER
theorem check : Set.range a = ⋃ i, {a i} := by
exact Set.range_eq_iUnion a
done

--Might not be needed but kept in case
theorem pre_im_singleton_measurable (i : ℕ ) : MeasurableSet (f ⁻¹'({a i})) := by
  apply MeasurableSet.preimage
  exact MeasurableSet.singleton (a i)
  exact h
  done


-- We define the sequence of sets A_i as follows
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B
def Aa := ⋃ i, A f a B i

-- Since f maps to {a1, a2, ...} we have ⋃ i f ⁻¹({a i}) is the whole space, and thus ⋃ i A_i = B which is proven here

theorem B_eq_Union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[(Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i}))).symm]
  rw[(Set.preimage_iUnion).symm]
  rw[(Set.range_eq_iUnion a).symm]
  rw[hcount.symm]
  simp
  simp_rw[Set.subset_preimage_image f B]
  done



/-
We will be applying continuity of measure to show that the measure of the partial unions of these sets
converges up to the measure of Aa. Below we prove that the partial unions are an increasing sequence of
measurable sets, the hypothesis of continuity of measure.
-/
theorem measurable_A: (MeasurableSet (A f a B i)) := by
unfold A
apply MeasurableSet.inter
apply pre_im_singleton_measurable
apply h
exact hm
done

theorem measurable_Aa: (MeasurableSet (Aa f a B)) := by
apply MeasurableSet.iUnion
intro i
apply measurable_A
apply h
exact hm
done


-- Next we show that the partial union of sets up to k is measurable
theorem partial_union_A_measurable: MeasurableSet (⋃ i ∈ Set.Iic k , A f a B i )  := by
apply Set.Finite.measurableSet_biUnion
exact Set.finite_Iic k
intro b
exact fun x => measurable_A f a h B hm







--Next goal is to show that the sequence of partial unions is increasing
--The Monotone theorem works
--Just need to apply mwe to prove partial_union_increasing



theorem mwe (s: ℕ → Set α)(k i: ℕ)(hk: n ≤ k ): s n ⊆ ⋃ i ∈ Set.Iic k ,  s i := by
unfold Set.Iic
simp
exact Set.subset_biUnion_of_mem hk
done 



theorem partial_union_increasing(s: ℕ → Set α)(x y  : ℕ )(h: x ≤ y): ⋃ i ∈ Set.Iic x ,  A f a B i  ≤ ⋃ i ∈ Set.Iic y, A f a B i  := by
unfold Set.Iic
simp
---apply mwe (A f a B) k1 k2 h
intro j
apply mwe s j k2 h
sorry




theorem Monotone: Monotone (fun k => ⋃ i ∈ Set.Iic k , A f a B i) := by
unfold Monotone
intro x y
apply partial_union_increasing
aesop
done





--Attempt using partialSups 

theorem partial_union_increasing_sup (s: ℕ → Set α)(x y : ℕ )(h: x ≤ y):
partialSups s x  ≤  partialSups s y
 := by
simp
---apply partialSups_mono 


/-
theorem tendsto_measure_iUnions [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι]
    {s : ι → Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  rw [measure_iUnion_eq_iSup hm.directed_le]
  exact tendsto_atTop_iSup fun n m hnm => measure_mono <| hm hnm
#align measure_theory.tendsto_measure_Union MeasureTheory.tendsto_measure_iUnion
-/

theorem continuity_of_measure (ε : ENNReal) : ∃ N : ℕ, μ ((⋃ i, f ⁻¹'{a i}) \ f ⁻¹' (⋃ i ∈ Set.Icc 1 N, {a i})) < ε/2 := by
  simp only [ge_iff_le, not_le, lt_one_iff, gt_iff_lt, Set.mem_Icc, Set.preimage_iUnion]
  -- Aadam is working on this proof!
  sorry


-- Theorem 2 of 3 for μ(A \ K) for countable f
theorem compact_subsets_from_regular_measure (n : ℕ) (K : ℕ → Set α) : ∀ i ∈ Set.Icc 1 n, ∃ i, IsCompact (K i) ∧ K i ⊂ f ⁻¹'{a i} ∧ μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n) := by sorry


-- Theorem 3 of 3 for μ(A \ K) < ε for countable f
-- NEED TO FIX ISSUE WITH INDEX i
theorem lusin_for_countable_f (n : ℕ) (K : ℕ → Set α) (hck : ∀ i ∈ Set.Icc 1 n, IsCompact (K i)) (hc : ∀ i ∈ Set.Icc 1 n, K i ⊂ f ⁻¹'{a i}) (hε : μ (f ⁻¹'{a i} \ K i) ≤ ε/(2*n)) : μ (⋃ i, f ⁻¹'{a i} \ ⋃ i, K i) < ε := by sorry


-- class of regular functions in Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html#MeasureTheory.Measure.Regular note that there are definitions of inner regular and outer regular incorporated with this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html

/-
Theorem: the countable union of compact sets is compact.
-/

-- I think we want to invoke: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#isCompact_iUnion

-- e.g. "apply Mathlib.Topology.Compactness.Compact.isCompact_iUnion"



/-
Theorem (kinda obvious but may need a bitesize outline here): If K is a compact subset of a set A and f is constant on A, i.e. A = f^-1({a}) for a singleton {a}, then f is constant on K.
-/

theorem preimage_of_const_func_on_compact_subset_is_constant (K : Set α) (a : ℝ) (hk : IsCompact K) (hs : K ⊂ f ⁻¹' ({a} : Set ℝ)) : (∀ x ∈ K, f x = a) := by sorry


/-
Lemma: if f is a measurable function which is disjoint on the sets A and B, with f constant on A and f constant on B, then f is continuous on A ⋃ B.
-/

lemma meas_func_const_on_disjoint_pair_is_continuous (A B : Set α) (a b : ℝ) (hf : Measurable f) (ha : ∀ x : A, f x = a) (hb : ∀ x : B, f x = b) (hac : IsCompact A) (hbc : IsCompact B) (hd : A ∩ B = ∅) : ContinuousOn f (A∪B) := by sorry


/-
Intermediate lemma: if f is a measurable function with K = ⋃K_i for K_i disjoint compact sets, then f is constant on each K_i. Hence, f|K (i.e. f restricted to the set K) continuous.


Useful resources:
Restriction of a set to a function f: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Set.restrict
-/

theorem meas_func_const_on_disjoint_finite_union_is_continuous (n : ℕ) (K : ℕ → Set α) (hpd: ∀ i ∈ Set.Icc 1 n, Pairwise (Disjoint on K i)) : ContinuousOn f (⋃ i ∈ Set.Icc 1 n, K i) := by sorry

--theorem measurable_func_constant_on_sets_is_continuous_on__union [preorder τ] [countable τ] (hcs : compact K)

-- NOTE: in the below it may be better to use ℕ for sequence indexing rather than preorder/countable ι (that was just the convention that the Egorov proof followed)
-- theorem measurable_func_constant_on_sets_is_continuous_on_union {α : Type u_1} {β : Type u_2} {c : β} {m1: MeasurableSpace α} {m2: TopologicalSpace α} {m3 : MeasurableSpace β} {f : α → β } {K : ι → set α} [Preorder ι] [Countable ι] (hf : Measurable f) (hcs : ∀ (i : ι), IsCompact (K i)) (hck : f (K i) = c) (hpd: ∀ (i : ι), Pairwise (Disjoint on K)) : (1=2) := by sorry


-- write countable f theorem here



/-
From proof in MA359 notes: the sequence of functions f_n := 2^-n * floor(2^n f) converges uniformly to f.
-/

-- write uniform convergence proof here



/- Lusin's Theorem for f taking **uncountably many values**:
-/
theorem Lusin [measure.Regular μ] :
∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
  Continuous Set.Restrict f t  := by
sorry

 ∃ t, MeasurableSet t ∧ CompactSet t ∧ μ Set.diff a \ t ≤ ENNReal.ofReal ε ∧
  Continuous Set.Restrict f t  := by sorry
