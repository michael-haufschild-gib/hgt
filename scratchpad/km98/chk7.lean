import Mathlib.LinearAlgebra.Finsupp.LinearCombination
example (K : Type) [Field K] (m k : ℕ) (V : Fin m → (Fin k → K)) (x : Fin k → K)
    (hx : x ∈ Submodule.span K (Set.range V)) : ∃ c : Fin m → K, ∑ i, c i • V i = x := by
  exact?
