import GaloisForLFunctions.RHTower.WeldWeylMultiplicity

/-!
# The prime weld exponentiates to an exact dyadic Weyl relation

The infinitesimal identity `[∂,M_p]=-(log p)M_p` from `SeamWeldCommutator` has an exact global
form.  Spectral translation `T_t f(s)=f(s+t)` and Euler multiplication
`M_p f(s)=exp(-(log p)s)f(s)` obey

`T_t M_p = exp(-(log p)t) M_p T_t`.

At the dyadic prime-clock step `t_k=-2πi/(2^k log p)`, the multiplier is exactly the named
Böttcher/Prüfer phase `dyadicRoot k`.  Thus the prime--archimedean weld already supplies the global
source Weyl relation needed by `WeldWeylMultiplicity`.

The same theorem exposes the descent obstruction: every `t_k` is nonzero, so the translation has
no fixed spectral point.  It moves a pinned local divisor germ instead of acting internally on it.
The remaining RH core is therefore a nonlocal cutoff/incidence descent of this global action to the
undoubled finite SEM hole algebra.
-/

open Complex

namespace RHTower

noncomputable section

/-- Translation by a complex spectral displacement. -/
def spectralTranslate (t : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun s => f (s + t)

/-- Multiplication by the entire prime exponential `exp(-(log p)s)`. -/
def primeEulerExpMultiply (p : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun s => Complex.exp (-((Real.log p : ℝ) : ℂ) * s) * f s

/-- The depth-`k` dyadic fraction of the prime clock period. -/
def primeDyadicClockStep (p k : ℕ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I) /
    (((2 ^ k : ℕ) : ℂ) * ((Real.log p : ℝ) : ℂ))

/-- **Exponentiated weld law.**  Translation and prime Euler multiplication form a projective
commuting pair with multiplier `exp(-(log p)t)`. -/
theorem spectralTranslate_primeEulerExpMultiply (p : ℕ) (t s : ℂ) (f : ℂ → ℂ) :
    spectralTranslate t (primeEulerExpMultiply p f) s =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * t) *
        primeEulerExpMultiply p (spectralTranslate t f) s := by
  unfold spectralTranslate primeEulerExpMultiply
  have hexp : Complex.exp (-((Real.log p : ℝ) : ℂ) * (s + t)) =
      Complex.exp (-((Real.log p : ℝ) : ℂ) * t) *
        Complex.exp (-((Real.log p : ℝ) : ℂ) * s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- The prime-clock multiplier at depth `k` is exactly the coherent dyadic Prüfer phase. -/
theorem primeDyadicClockPhase_eq_dyadicRoot {p : ℕ} (hp : 1 < p) (k : ℕ) :
    Complex.exp (-((Real.log p : ℝ) : ℂ) * primeDyadicClockStep p k) =
      Bottcher.dyadicRoot k := by
  unfold primeDyadicClockStep Bottcher.dyadicRoot
  congr 1
  have hlogR : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hp))
  have hlogC : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hlogR
  have hpow : (((2 ^ k : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)
  field_simp

/-- **Prime dyadic Weyl relation.**  One prime multiplier and a dyadic fraction of its genuine
spectral clock give the primitive phase required by the level-`k` multiplicity gate. -/
theorem primeDyadicWeylRelation {p : ℕ} (hp : 1 < p) (k : ℕ) (s : ℂ) (f : ℂ → ℂ) :
    spectralTranslate (primeDyadicClockStep p k) (primeEulerExpMultiply p f) s =
      Bottcher.dyadicRoot k *
        primeEulerExpMultiply p (spectralTranslate (primeDyadicClockStep p k) f) s := by
  rw [spectralTranslate_primeEulerExpMultiply, primeDyadicClockPhase_eq_dyadicRoot hp]

/-- Every dyadic prime-clock step is nonzero. -/
theorem primeDyadicClockStep_ne_zero {p : ℕ} (hp : 1 < p) (k : ℕ) :
    primeDyadicClockStep p k ≠ 0 := by
  unfold primeDyadicClockStep
  apply div_ne_zero
  · exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
  · apply mul_ne_zero
    · exact_mod_cast pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0)
    · exact_mod_cast ne_of_gt (Real.log_pos (by exact_mod_cast hp))

/-- **Pinned-centre obstruction.**  The translation generator of the nontrivial Weyl phase fixes no
spectral point, so the global source relation does not automatically descend to any one local SEM
hole germ. -/
theorem primeDyadicClockStep_no_fixedPoint {p : ℕ} (hp : 1 < p) (k : ℕ) (s : ℂ) :
    s + primeDyadicClockStep p k ≠ s := by
  rw [add_ne_left]
  exact primeDyadicClockStep_ne_zero hp k

end

end RHTower
