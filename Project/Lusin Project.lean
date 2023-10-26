import Mathlib.Tactic

/-!
# Lusin's theorem

This file contains Lusin's theorem which put very simply and in the words of J. E. Littlewood,
"every measurable function is nearly continuous". More precisely the statement of Lusin's theorem
we will prove goes as follows: Let f be a  measureable function from a Euclidean space equipped with
the Borel sigma-algebra to the Reals equipped with the Borel sigma-algebra. For any set A in the
first sigma-algebra with finite  measure, there exists a compact set K, such that f is continuous on
K and the measure of A \ K is arbitrarily small.

!-/

noncomputable section

open MeasureTheory

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [MetricSpace β] {μ : Measure α}

namespace Lusin
