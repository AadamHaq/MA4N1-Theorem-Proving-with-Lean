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
variable (B : Set α)(hm : MeasurableSet B)(hf : μ B ≠ ∞)(hf2 : μ B < ∞)(hcount : f '' B = Set.range a)
variable (ε : ℝ)(hε: 0 < ε)

-- We define the sequence of sets A_i as follows
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B

-- Since f maps to {a1, a2, ...} we have ⋃ i f ⁻¹({a i}) is the whole space, and thus ⋃ i A_i = B which is proven here

theorem B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hcount ]
  simp
  simp_rw[Set.subset_preimage_image f B]
  done

--Here we show some sets are measurable for later use
theorem measurable_A : ∀ (i : ℕ), MeasurableSet (A f a B i) := by
  intro b
  apply MeasurableSet.inter
  apply MeasurableSet.preimage
  apply MeasurableSet.singleton (a b)
  apply h
  exact hm
  done

--We can just use 'MeasurableSet.iUnion (measurable_A f a h B hm)' later and then delete this
theorem measurable_Ai_Union : MeasurableSet (⋃ i, A f a B i) := by
  apply MeasurableSet.iUnion (measurable_A f a h B hm)
  done

--Next we show partial unions are monotone
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

theorem continuity_of_measure: Tendsto (fun k ↦ μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i))
  atTop (𝓝 (μ (B))) := by
  nth_rw 2 [← union_partial_A_eq_B f a B hcount]
  apply tendsto_measure_iUnion
  apply monotone_A
  done

theorem difference_epsilon (hs : (2⁻¹ : ℝ) > 0) (hε : (ε : ℝ ) > 0) : ∃ k : ℕ, μ (B)  ≤  μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) + ENNReal.ofReal (ε * 2⁻¹)  := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure μ f a B hcount) (ENNReal.ofReal (ε * 2⁻¹)) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε hs)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl
  exact ⟨N, hy⟩
  done

--- These three results will be required to turns this result into a set difference

theorem partial_union_A_measurable (N : ℕ): MeasurableSet (⋃ i, ⋃ (_ : i ≤ N) , A f a B i )  := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic N
  intro b
  exact fun _ => measurable_A f a h B hm b
  done

theorem subset (N : ℕ) : ⋃ i, ⋃ (_ : i ≤ N) , A f a B i ⊆ B := by
  unfold A
  aesop
  done

theorem finite (N : ℕ ): μ (⋃ i, ⋃ (_ : i ≤ N), A f a B i) ≠  ∞ := by
  have hk := subset f a B N
  have ht := (measure_mono hk).trans_lt hf2
  aesop
  done

theorem set_difference_epsilon (k: ℕ) (hs : (2⁻¹ : ℝ) > 0): ∃ k : ℕ, μ (B \ ⋃ i, ⋃ (_ : i ≤ k), A f a B i) ≤ ENNReal.ofReal (ε * 2⁻¹) := by
  have ht := difference_epsilon μ f a B hf hcount ε hs hε
  let ⟨ k, h4 ⟩ := ht
  have hq := measure_diff (subset f a B k) (partial_union_A_measurable f a h B hm k) (finite μ f a B hf2 k)
