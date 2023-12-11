import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Init.Order.Defs
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.Basic

set_option maxHeartbeats 0

open MeasureTheory ENNReal Filter
open scoped Topology

-- Aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- This is slightly more restrictive than the theorem in Cohn's book

namespace Lusin

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
variable [BorelSpace ℝ] (f: α → ℝ) (a: ℕ → ℝ) (h: Measurable f)
variable (B : Set α)(hm : MeasurableSet B)(hf : μ B ≠ ∞)(hf2 : μ B < T)(hcount : f '' B = Set.range a)
variable (ε : ENNReal)(hε: 0 < ε)(hj: ε < T)


-- We define the sequence of sets A_i as follows
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B

-- Since f maps to {a1, a2, ...} we have ⋃ i f ⁻¹({a i}) is the whole space, and thus ⋃ i A_i = B which is proven here

theorem B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hcount ]
  simp
  simp_rw[Set.subset_preimage_image f B]
  done

/-
Here we show some sets are measurable for later use
-/
theorem measurable_A : ∀ (i : ℕ), MeasurableSet (A f a B i) := by
  intro b
  apply MeasurableSet.inter
  apply MeasurableSet.preimage
  apply MeasurableSet.singleton (a b)
  apply h
  exact hm
  done

theorem measurable_Ai_Union : MeasurableSet (⋃ i, A f a B i) := by
  apply MeasurableSet.iUnion (measurable_A f a h B hm)
  done

--Next goal is to show that the sequence of partial unions is increasing
--The Monotone theorem works, but it requires "partial_union_increasing" which is sorried out.
--mwe is basically the same as partial_union_increasing I just simplified the statement as much as possible

theorem monotone_A : Monotone (fun k => ⋃ i, ⋃ (_ : i ≤ k) , A f a B i) := by
  unfold Monotone
  intro x y
  simp
  intro hxy j hjx
  have hjy := hjx.trans hxy
  apply Set.subset_biUnion_of_mem
  exact hjy
  done

theorem mwe_2 (s: ℕ → Set α) (j : ℕ): s j ⊆ ⋃ i, ⋃ (_ : i ≤ j) , s i  := by
  apply Set.subset_biUnion_of_mem
  apply Nat.le_refl
  done

/-We need a result which says that the union of partial unions is just the union.
This together with B_eq_Union_Ai will give us convergence up to μ(B) when we apply
continuity of measure. -/

theorem union_partial_eq_union (s: ℕ → Set α): ⋃ i, s i =
 ⋃ i, (⋃ j, ⋃ (_ : j ≤ i) , s j ) := by
  rw[superset_antisymm_iff]
  constructor
  simp
  exact fun i i_1 _ => Set.subset_iUnion s i_1
  simp
  intro t
  ---have hj := Set.subset_biUnion_of_mem (Nat.le_refl j)
  have hj := mwe_2 s t
  apply le_trans hj
  exact Set.subset_iUnion (fun x =>  ⋃ j, ⋃ (_ : j ≤ x), s j) t
  done

theorem union_partial_A_eq_B: ⋃ k,  ⋃ i, ⋃ (_ : i ≤ k), A f a B i = B := by
  rw[(union_partial_eq_union (A f a B)).symm]
  unfold A
  apply B_eq_union_Ai
  exact hcount
  done

---this theorem should follow directly from tendsto_measure_iUnion and union_partial_A_eq_B

theorem continuity_of_measure: Tendsto (fun k ↦ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_A_eq_B f a B hcount]
  apply tendsto_measure_iUnion
  apply monotone_A
  done

theorem union_partial_A_eq_B1: B \ ⋃ k,  ⋃ i, ⋃ (_ : i ≤ k) , A f a B i = ∅ := by
  rw[(union_partial_eq_union (A f a B)).symm]
  unfold A
  rw[Set.diff_eq_empty]
  apply subset_of_eq
  exact (B_eq_union_Ai f a B hcount).symm
  done

theorem epsilon1  : ∃ k : ℕ, μ (B) - ε  ≤  μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure μ f a B hcount) ε (by
      rw [gt_iff_lt]
      exact hε )
  exact ⟨N, (hN N le_rfl).1⟩
  done
--- Technical issue with moving the epsilon over to the other side

theorem mwe3 (a b e : ENNReal) (h : e < T ) (hk: b - e ≤ a ) : (b ≤ a + e) := by
exact tsub_le_iff_right.mp hk

theorem epsilon2  : ∃ k : ℕ, μ (B) ≤ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) + ε  := by
  have ⟨ N, hN ⟩ := epsilon1 μ f a B hf hcount ε hε
  have hy := mwe3 (μ (⋃ i, ⋃ (_ : i ≤ N), A f a B i)) (μ B) ε hj hN
  aesop

--- These three results will be required to turns this result into a set difference

theorem partial_union_A_measurable (N : ℕ): MeasurableSet (⋃ i ∈ Set.Iic N , A f a B i )  := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic N
  intro b
  exact fun a_1 => measurable_A f a h B hm b
  done

theorem subset (N : ℕ) : ⋃ i ∈ Set.Iic N , A f a B i ⊆ B := by
  unfold Set.Iic
  unfold A
  aesop
  done

theorem finite (N : ℕ ): μ (⋃ i ∈ Set.Iic N , A f a B i) ≠  T  :=
by
  have hk := subset f a B N
  have ht := (measure_mono hk).trans_lt hf2
  aesop
  done


theorem epsilon3 (k:ℕ ): ∃ k : ℕ, μ (B \ ⋃ i, ⋃ (_ : i ≤ k), A f a B i) ≤  ε := by
  have hs := epsilon2 μ f a B hf hcount ε hε hj
  let ⟨ M, h4 ⟩ := hs
  have h1 := subset f a B M
  have h2 := partial_union_A_measurable f a h B hm M
  have h3 := finite μ f a B hf2 M
  have hq := measure_diff h1 h2 h3
  --- hq should prove the theorem













-- class of regular functions in Mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html#MeasureTheory.Measure.Regular note that there are definitions of inner regular and outer regular incorporated with this: https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Regular.html

/-
Theorem: the countable union of compact sets is compact.
-/

-- I think we want to invoke: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#isCompact_iUnion

-- e.g. "apply Mathlib.Topology.Compactness.Compact.isCompact_iUnion"

theorem fio  (a b c: ENNReal)(f : c ≠ ∞) (h : a ≤  b + c ): a - c ≤ b := by
  exact tsub_le_iff_right.mpr h


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
