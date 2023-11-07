import Mathlib.Tactic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Lusin's theorem

This file contains Lusin's theorem which put very simply and in the words of J. E. Littlewood,
"every measurable function is nearly continuous". More precisely the statement of Lusin's theorem
we will prove goes as follows: Let f be a  measureable function from a locally compact Hausdorff
space to the Reals, both equipped with the Borel sigma-algebra. For any set A in the first  
sigma-algebra with finite  measure, there exists a compact set K, such that f is continuous on
K and the measure of A \ K is arbitrarily small.

!-/


noncomputable section

--open MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α} [MetricSpace β] {μ : MeasureTheory.Measure α}


variable {f : α  → β }

--instance Real.measurableSpace : MeasurableSpace ℝ  := borel ℝ 


class T2LocComSpace  (X x : Type u) [TopologicalSpace X] : Prop where
  /-- Every two points  a Hausdorff space admit disjoint open neighbourhoods. -/
  t2 : ∀ x y, x ≠ y → ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
  local_compact_nhds : ∀ (x : X), ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s







