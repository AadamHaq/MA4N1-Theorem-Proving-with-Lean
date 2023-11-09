import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

-- For regular measure
import Mathlib.MeasureTheory.Measure.Regular



open Nat Int Real Finset MeasureTheory
open scoped Topology

-- namespace MeasureTheory

variable {α β ι : Type*} {m : MeasurableSpace α} [n : MetricSpace β] {μ : Measure α}


-- aim is to prove Lusin's Theorem for the Borel sigma algebra specifically
-- this is slightly more restrictive than the theorem in Cohn's book

class T2LocallyCompactSpace (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] : Prop
    where

instance (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] :
    T2LocallyCompactSpace α := {}

def T2LocallyCompactSpaceBorel (X : T2LocallyCompactSpace α) (m : MeasurableSpace α) :=
BorelSpace X

/-
We are using the following BorelSpace class definition, given below.
Namely, this tells us that the measurable sets are exactly the Borel-measurable sets.

class BorelSpace (α : Type*) [TopologicalSpace α] [MeasurableSpace α] : Prop where
    measurable_eq : ‹MeasurableSpace α› = borel α
-/

theorem lusin {X : T2LocallyCompactSpace α} [Measure.Regular μ]

#check Field

#synth T2Space ℝ
#synth LocallyCompactSpace ℝ
#synth TopologicalSpace ℝ
#synth T2LocallyCompactSpace ℝ
