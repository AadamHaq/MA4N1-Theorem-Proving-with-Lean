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

-- Aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- This is slightly more restrictive than the theorem in Cohn's book

namespace Lusin

-- Calling universal variables
variable  {α : Type*} [TopologicalSpace α][T2Space α][LocallyCompactSpace α][MeasurableSpace α][BorelSpace α](μ: Measure α) [Measure.Regular μ]
variable [BorelSpace ℝ] (f: α → ℝ) (a: ℕ → ℝ) (h: Measurable f)
variable (B : Set α)(hm : MeasurableSet B)(hf : μ B ≠ ∞)(hcount : f '' B = Set.range a)
variable (ε : ℝ)(hε: 0 < ε)

-- We define the sequence of sets A_i as follows
def A (i : ℕ) := f ⁻¹'({a i}) ∩ B

-- Since f maps to {a1, a2, ...} we have ⋃ i f ⁻¹({a i}) is the whole space, and thus
-- ⋃ i A_i = B which is proven here
theorem B_eq_union_Ai : ⋃ i, f ⁻¹'({a i}) ∩ B = B  := by
  rw[← Set.iUnion_inter B (fun i ↦ f ⁻¹'({a i})), ← Set.preimage_iUnion, ← Set.range_eq_iUnion a, ← hcount ]
  simp only [Set.inter_eq_right]
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

theorem difference_epsilon : ∃ k : ℕ, μ (B)  ≤
μ (⋃ i, ⋃ (_ : i ≤ k), A f a B i) + ENNReal.ofReal (ε * (1/2))  := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop hf).1
    (continuity_of_measure μ f a B hcount) (ENNReal.ofReal (ε * (1/2))) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε one_half_pos)
  have hl := (hN N le_rfl).1
  have hy := tsub_le_iff_right.mp hl
  exact ⟨N, hy⟩
  done

--- These results will be required to turns this result into a set difference
theorem partial_union_A_measurable (N : ℕ): MeasurableSet (⋃ i, ⋃ (_ : i ≤ N), A f a B i) := by
  apply Set.Finite.measurableSet_biUnion
  exact Set.finite_Iic N
  intro b
  exact fun _ => measurable_A f a h B hm b
  done

theorem subset (N : ℕ) : ⋃ i, ⋃ (_ : i ≤ N) , A f a B i ⊆ B := by
  unfold A
  aesop
  done

--The final result
theorem set_difference_epsilon : ∃ N : ℕ,
μ (B \ ⋃ i, ⋃ (_ : i ≤ N), A f a B i) ≤ ENNReal.ofReal (ε * (1/2)) := by
  have ht := difference_epsilon μ f a B hf hcount ε hε 
  let ⟨ k, h4 ⟩ := ht
  have hq := measure_diff (subset f a B k) (partial_union_A_measurable f a h B hm k)
    (ne_top_of_lt (LE.le.trans_lt (measure_mono (subset f a B k)) (Ne.lt_top hf)))
  have h5 := tsub_le_iff_left.mpr h4
  rw[← hq] at h5
  exact ⟨ k, h5 ⟩
  done

--Here we obtain the compact subsets K_i of A_i for each i, after two technical results
theorem finite_A (i : ℕ) : μ (A f a B i) ≠ ∞ := by
  have ss := Set.inter_subset_right (f ⁻¹' {a i}) B
  have hy := (measure_mono ss).trans_lt (Ne.lt_top hf)
  exact LT.lt.ne hy
  done




---We will take δ = ε/2N once N exists

theorem compact_subset(δ : ℝ)(hδ : 0 < δ  )(i : ℕ) : ∃ K : Set α,  K ⊆ (A f a B i) ∧  IsCompact K ∧ μ ((A f a B i)\K) ≤  ENNReal.ofReal δ    := by
  have hw := MeasurableSet.exists_isCompact_lt_add (measurable_A f a h B hm i) (finite_A μ f a B hf i) (zero_lt_iff.mp (ofReal_pos.mpr hδ))
  let ⟨ K, HK ⟩ := hw
  have ⟨ HK1, HK2, HK3 ⟩ := HK
  have hq := measure_diff (HK.1) (IsCompact.measurableSet HK2) (ne_top_of_lt (LE.le.trans_lt (measure_mono (Set.Subset.trans HK1 (Set.inter_subset_right (f ⁻¹' {a i}) B))) (Ne.lt_top hf)))
  have HK4 := tsub_le_iff_left.mpr (le_of_lt HK3)
  rw[← hq] at HK4
  exact ⟨ K, HK1, HK2, HK4 ⟩
  done

theorem compact_subset_N (δ : ℝ)(hδ : 0 < δ  )(N: ℕ) :  ∃ K : ℕ → Set α, ∀ i ≤ N, K i ⊆ (A f a B i) ∧ IsCompact (K i) ∧ μ ((A f a B i)\ (K i)) ≤  ENNReal.ofReal δ := by
  sorry




--These results will be needed to manipulate the sets

theorem set_diff (b c a : Set α )(h1 : b ⊆ c)(h2: c ⊆ a) : a\b = a\c ∪ c\b := by
  exact (Set.diff_union_diff_cancel h2 h1).symm
  done


--triv needed for set_diff_union_0
theorem triv(a b c : Set α) (h : c ⊆ b) (hc : a ∩ b = ∅ ) : (a ⊆ c.compl) := by

  sorry

--This is the easier case of what we want to prove
theorem set_diff_union_0(a1 a2 k1 k2 : Set α)(h1: k1 ⊆ a1) (h2: k2 ⊆ a2) (h3 : a1 ∩ a2 = ∅ ) :
(Set.diff a1 k1) ∪ (Set.diff a2 k2) = Set.diff (a1 ∪ a2) (k1 ∪ k2) := by
  unfold Set.diff
  simp

  have hh1 : {x | x ∈ a1 ∧ ¬(x ∈ k1 ∨ x ∈ k2)} = a1 ∩ k2.compl ∩ k1.compl := by
    sorry
    done

  have hh2 : {x | x ∈ a2 ∧ ¬(x ∈ k1 ∨ x ∈ k2)} = a2 ∩ k1.compl ∩ k2.compl := by
    sorry
    done

  rw[hh1, hh2]

  have hh3 : {a | a ∈ a1 ∧ ¬a ∈ k1} ∪ {a | a ∈ a2 ∧ ¬a ∈ k2} = (a1 ∩ k1.compl) ∪ (a2 ∩ k2.compl) := by
    aesop

  rw[hh3]

  have hh4 : a1 ∩ k2.compl = a1 := by
    exact Set.inter_eq_left.mpr (triv a1 a2 k2 h2 h3)

  have hh5 : a2 ∩ k1.compl = a2 := by
    rw[Set.inter_comm] at h3
    exact Set.inter_eq_left.mpr (triv a2 a1 k1 h1 h3)

  rw[hh4, hh5]


--This is the general version we need which should follow from set_diff_union_0 using induction

theorem set_diff_union (n : ℕ) (A : ℕ → Set α)(K : ℕ → Set α)(h1 : ∀ i,  K i  ⊆ A i) (h2 : ∀ i j, i ≠ j → A i  ∩ A j = ∅ ) :
⋃ (_ : i ≤ n), (Set.diff (A i) (K i)) = Set.diff (⋃ (_ : i ≤ n), A i) (⋃ (_ : i ≤ n), K i) := by
  ---induction' n with n ih
  sorry


--Will need isCompact_iUnion, and sub-additivity of measure


theorem lusin: ∃ K : Set α, IsCompact K ∧ μ (B \ K ) ≤ ENNReal.ofReal ε ∧ Continuous (Set.restrict K f) := by
  have H : ∃ K : Set α, IsCompact K ∧ μ (B \ K ) ≤ ENNReal.ofReal ε := by
    have HE := set_difference_epsilon μ f a h B hm hf hcount ε hε
    let ⟨ N, HSD ⟩ := HE
    have p : 0 < (ε/(2*N)) := by
      sorry
    have HK := compact_subset_N μ f a B (ε/(2*N)) p N
    rcases HK with ⟨K,P⟩

    --- want to split P up into three statements

    have KMP : IsCompact (⋃ i, ⋃ (_ : i ≤ N), K i) := by
      --exact isCompact_iUnion
      sorry



    use (⋃ i, ⋃ (_ : i ≤ N), K i)
    constructor
    apply KMP

    have h1 : (⋃ i, ⋃ (_ : i ≤ N), K i) ⊆ (⋃ i, ⋃ (_ : i ≤ N), A f a B i) := by
      sorry

    have h2 : (⋃ i, ⋃ (_ : i ≤ N), A f a B i) ⊆ B  := by
      sorry


    have S1 : μ (B\(⋃ i, ⋃ (_ : i ≤ N), K i)) ≤  μ (B\(⋃ i, ⋃ (_ : i ≤ N), A f a B i) )  + μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i)\(⋃ i, ⋃ (_ : i ≤ N), K i)) := by
      have SS := (Set.diff_union_diff_cancel h2 h1).symm

      ---have SS1 := measure_union_le (Set.diff B ((⋃ i, ⋃ (_ : i ≤ N), A f a B i))) (Set.diff (⋃ i, ⋃ (_ : i ≤ N), A f a B i) (⋃ i, ⋃ (_ : i ≤ N), K i))

      sorry
    have S2 : μ ((⋃ i, ⋃ (_ : i ≤ N), A f a B i)\(⋃ i, ⋃ (_ : i ≤ N), K i)) ≤ ∑ᶠ (i : Icc 0 N), μ ((A f a B i) \ (K i)) := by
      have SS2 := set_diff_union 

      sorry
    have S3 : ∑ᶠ (i : Icc 0 N), μ ((A f a B i) \ (K i)) ≤  ENNReal.ofReal (ε/2) := by
      sorry



---(μ((A f a B i)\(K i)))


    sorry
  let ⟨ K, H1, H2 ⟩ := H


  have HC : Continuous (Set.restrict K f) := by
    sorry

  exact ⟨ K, H1, H2, HC ⟩
  done


 
