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

open MeasureTheory ENNReal Filter Finset BigOperators
open scoped Topology

-- The aim of this lean file is to prove Lusin's Theorem in the finite case. The previous file works for countable values however does not fully work for the finite case. This file attemps to adapt the proof and rewrite it in terms of finite many values i.e. the function goes from [1, n] -> R rather than what was shown previously; N -> R

namespace Lusin

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
-- Finite Case
variable [BorelSpace ℝ] (f: α → ℝ) (a: Set.Icc 1 n → ℝ) (hinja : Function.Injective a) (hmf: Measurable f)
variable (B : Set α)(hmb : MeasurableSet B)(hf : μ B ≠ ∞)(hfin : f '' B = Set.range a)

-- f takes finitely many values
def A (i : Set.Icc 1 n) := f ⁻¹'({a i}) ∩ B

-- All of the previous lemmas and theorems are similar to the countable case, but with finite variables. The proofs are similar but there are some subtle differences.
lemma B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hfin ]
  simp only [Set.inter_eq_right]
  simp_rw[Set.subset_preimage_image f B]
  done

lemma measurable_Ai : ∀ (i : Set.Icc 1 n), MeasurableSet (A f a B i) := by
  intro b
  apply MeasurableSet.inter ((MeasurableSet.preimage (MeasurableSet.singleton (a b)) hmf)) (hmb)
  done

theorem disjoint_Ai (i j : Set.Icc 1 n) (h : i ≠ j) :  A f a B i ∩ A f a B j = ∅ := by
  unfold A
  have hj : Disjoint (f ⁻¹' {a i}) (f ⁻¹' {a j}) := by
    have hj2 : Disjoint {a i} {a j} := by
      have neq : a i ≠ a j := by
        exact Function.Injective.ne hinja h
      rw[← Set.disjoint_singleton] at neq
      exact neq
    exact Disjoint.preimage f hj2
  rw [@Set.inter_inter_inter_comm]
  simp
  have ss := Set.inter_subset_left (f ⁻¹' {a i} ∩ f ⁻¹' {a j}) B
  rw [@Set.disjoint_iff_inter_eq_empty] at hj
  exact Set.subset_eq_empty ss hj

theorem monotone_Ai : Monotone (fun k => ⋃ i, ⋃ (_ : i ≤ k) , A f a B i) := by
  unfold Monotone
  intro a b
  simp only [ge_iff_le, not_le, Nat.lt_one_iff, gt_iff_lt, Set.mem_Icc,
    Set.le_eq_subset, Set.iUnion_subset_iff]
  intro hab i hia
  have hib := hia.trans hab
  apply Set.subset_biUnion_of_mem
  exact hib
  done

lemma element_subset_union_elements_fin (s: Set.Icc 1 n → Set α) (j : Set.Icc 1 n): s j ⊆ ⋃ i, ⋃ (_ : i ≤ j) , s i  := by
  apply Set.subset_biUnion_of_mem
  apply Nat.le_refl
  done

lemma union_partial_eq_union_fin (s: Set.Icc 1 n → Set α): ⋃ i, s i =
 ⋃ i, (⋃ j, ⋃ (_ : j ≤ i) , s j ) := by
  rw[superset_antisymm_iff]
  constructor
  simp only [Set.iUnion_subset_iff]
  exact fun i i_1 _ => Set.subset_iUnion s i_1
  simp only [Set.iUnion_subset_iff]
  intro t
  have hj := element_subset_union_elements_fin s t
  apply le_trans hj
  exact Set.subset_iUnion (fun x =>  ⋃ j, ⋃ (_ : j ≤ x), s j) t
  done

lemma union_partial_Ai_eq_B: ⋃ k,  ⋃ i, ⋃ (_ : i ≤ k), A f a B i = B := by
  rw[(union_partial_eq_union_fin (A f a B)).symm]
  unfold A
  apply B_eq_union_Ai
  exact hfin
  done

lemma continuity_of_measure_fin: Tendsto (fun k ↦ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_Ai_eq_B f a B hfin]
  apply tendsto_measure_iUnion
  apply monotone_Ai
  done

theorem partial_union_Ai_up_B_leq_epsilon : ∃ k : Set.Icc 1 n, μ (B)  ≤
μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) + ENNReal.ofReal (ε * (1/2))  := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure_fin μ f a B hfin) (ENNReal.ofReal (ε * (1/2))) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε one_half_pos)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl

  exact ⟨N, hy⟩
  sorry
-- Unfortunately, in the proof we stopped at this point due to issues in proving the above. The issue comes from ENNReal only thinking [1,n] can be empty. This is not the case as we want n to be an integer >_ 1. Despite adding hypotheses and trying to change the variables using this stipulation, further progress could not be achieved in proving this fact.
