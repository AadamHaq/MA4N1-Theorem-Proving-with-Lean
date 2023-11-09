import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Data.Real.Basic

open Nat Int Real Finset
open scoped Topology

class T2LocallyCompactSpace (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] : Prop
    where

instance (α : Type*) [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α] :
    T2LocallyCompactSpace α := {}

#check Field

#synth T2Space ℝ
#synth LocallyCompactSpace ℝ
#synth TopologicalSpace ℝ
#synth T2LocallyCompactSpace ℝ
