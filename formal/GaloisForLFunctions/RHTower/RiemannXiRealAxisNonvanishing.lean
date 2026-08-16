import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# The two corpus spellings of the completed Xi agree, and neither vanishes on the real axis

`RiemannTower.xi` and `RiemannXiZerosInfinite.riemannXi` are the same entire function written with
the division placed differently; the real-axis nonvanishing proved for the first therefore transfers
to the second, which is the form the zero-existence theorems use.
-/

open Complex

noncomputable section

namespace RHTower

theorem xi_eq_riemannXi (s : ℂ) : xi s = riemannXi s := by
  rw [xi, riemannXi]
  ring

/-- **`ξ` has no zero on the real axis.**  (Corpus form, in the real-argument spelling.) -/
theorem xi_ne_zero_of_ofReal (σ : ℝ) : xi ((σ : ℂ)) ≠ 0 := xi_ne_zero_of_real σ

/-- The second spelling inherits the real-axis nonvanishing. -/
theorem riemannXi_ne_zero_of_ofReal (σ : ℝ) : riemannXi ((σ : ℂ)) ≠ 0 := by
  rw [← xi_eq_riemannXi]
  exact xi_ne_zero_of_ofReal σ

end RHTower
