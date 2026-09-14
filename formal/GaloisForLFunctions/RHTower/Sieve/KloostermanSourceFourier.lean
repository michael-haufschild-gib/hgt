import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Lightweight Kloosterman source Fourier transform

This module isolates the source transform from the terminal-correlation implementation.  Source
estimates can now import the transform without elaborating the full Kloosterman completion chain.
-/

open scoped BigOperators
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Additive source transform at one inverse unit frequency. -/
def kloostermanSourceFourier
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) (x : (ZMod q)ˣ) : ℂ :=
  ∑ n ∈ B, b n * ZMod.stdAddChar
    ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

end

end RHTower.Sieve
