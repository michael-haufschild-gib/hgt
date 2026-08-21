import Mathlib
open Finset
example {α : Type*} [DecidableEq α] (s t : Finset α) (h : s ⊆ t) : (t \ s).card + s.card = t.card := by exact?
