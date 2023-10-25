import Mathlib.Tactic
/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
#align_import measure_theory.function.egorov from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `MeasureTheory.Egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/


noncomputable section

open Classical MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [MetricSpace β] {μ : Measure α}

namespace Egorov
