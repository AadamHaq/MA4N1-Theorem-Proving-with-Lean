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
variable [BorelSpace ℝ] (g: α → ℝ) (x: Set.Icc 1 n → ℝ) (hinjx : Function.Injective x) (hmg: Measurable g)
variable (Y : Set α)(hmy : MeasurableSet Y)(hg : μ Y ≠ ∞)(hfin : g '' Y = Set.range x)

-- f takes finitely many values
def X (j : Set.Icc 1 n) := g ⁻¹'({x j}) ∩ Y

lemma Y_eq_union_Xj : ⋃ j, g ⁻¹'({x j}) ∩ Y = Y  := by
  rw[← Set.iUnion_inter Y (fun j ↦ g ⁻¹'({x j})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion x, ← hfin ]
  simp only [Set.inter_eq_right]
  simp_rw[Set.subset_preimage_image g Y]
  done

lemma measurable_Xj : ∀ (j : Set.Icc 1 n), MeasurableSet (X g x Y j) := by
  intro y
  apply MeasurableSet.inter ((MeasurableSet.preimage (MeasurableSet.singleton (x y)) hmg)) (hmy)
  done

theorem disjoint_Xj (i j : Set.Icc 1 n) (h : i ≠ j) :  X g x Y i ∩ X g x Y j= ∅ := by
  unfold X
  have hj : Disjoint (g ⁻¹' {x i}) (g ⁻¹' {x j}) := by
    have hj2 : Disjoint {x i} {x j} := by
      have neq : x i ≠ x j := by
        exact Function.Injective.ne hinjx h
      rw[← Set.disjoint_singleton] at neq
      exact neq
    exact Disjoint.preimage g hj2
  rw [@Set.inter_inter_inter_comm]
  simp
  have ss := Set.inter_subset_left (g ⁻¹' {x i} ∩ g ⁻¹' {x j}) Y
  rw [@Set.disjoint_iff_inter_eq_empty] at hj
  exact Set.subset_eq_empty ss hj

theorem monotone_Xj : Monotone (fun k => ⋃ j, ⋃ (_ : j ≤ k) , X g x Y j) := by
  unfold Monotone
  intro a b
  simp only [ge_iff_le, not_le, Nat.lt_one_iff, gt_iff_lt, Set.mem_Icc,
    Set.le_eq_subset, Set.iUnion_subset_iff]
  intro hab i hia
  have hib := hia.trans hab
  apply Set.subset_biUnion_of_mem
  exact hib
  done

lemma element_subset_union_elements_fin (s: Set.Icc 1 n → Set α) (i : Set.Icc 1 n): s i ⊆ ⋃ j, ⋃ (_ : j ≤ i) , s j  := by
  apply Set.subset_biUnion_of_mem
  apply Nat.le_refl
  done

lemma union_partial_eq_union_fin (s: Set.Icc 1 n → Set α): ⋃ j, s j =
 ⋃ j, (⋃ i, ⋃ (_ : i ≤ j) , s i ) := by
  rw[superset_antisymm_iff]
  constructor
  simp only [Set.iUnion_subset_iff]
  exact fun j j_1 _ => Set.subset_iUnion s j_1
  simp only [Set.iUnion_subset_iff]
  intro t
  have hi := element_subset_union_elements_fin s t
  apply le_trans hi
  exact Set.subset_iUnion (fun x =>  ⋃ i, ⋃ (_ : i ≤ x), s i) t
  done

lemma union_partial_Xj_eq_Y: ⋃ k,  ⋃ j, ⋃ (_ : j ≤ k), X g x Y j = Y := by
  rw[(union_partial_eq_union_fin (X g x Y)).symm]
  unfold X
  apply Y_eq_union_Xj
  exact hfin
  done

lemma continuity_of_measure_fin: Tendsto (fun k ↦ μ (⋃ j, ⋃ (_ : j ≤ k), X g x Y j))
  atTop (𝓝 (μ (Y))) := by
  nth_rw 2 [← union_partial_Xj_eq_Y g x Y hfin]
  apply tendsto_measure_iUnion
  apply monotone_Xj
  done

theorem partial_union_Xj_up_Y_leq_epsilon : ∃ k : Set.Icc 1 n, μ (Y)  ≤
μ (⋃ j, ⋃ (_ : j ≤ k), X g x Y j) + ENNReal.ofReal (ε * (1/2))  := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hg).1
    (continuity_of_measure_fin μ g x Y hfin) (ENNReal.ofReal (ε * (1/2))) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε one_half_pos)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl

  exact ⟨N, hy⟩
  sorry
