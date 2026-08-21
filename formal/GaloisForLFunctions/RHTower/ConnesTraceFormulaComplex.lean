import GaloisForLFunctions.RHTower.ConnesWeilPrimeSide
import GaloisForLFunctions.RHTower.ConnesArchWeilTerm
import GaloisForLFunctions.RHTower.GradeMonodromyInversion
import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# Connes' trace formula on the resolvent test algebra, at every admissible abscissa

The identification of the finite part of Connes' geometric side with the von Mangoldt Dirichlet
series holds for every `s` with `Re s > 1`, not only for real abscissae: the local Weil term at
`p` is the geometric series over the valuation shells inside the unit ball, which is the local
Euler factor of `-ζ'/ζ`.  The prime-power regrouping and the term identity are corpus-owned
(`RHTower.support_vonMangoldtTerm_subset_primePow`, `RHTower.primeGradeSource_term_eq`).

Combined with the archimedean local term `(Γ_ℝ'/Γ_ℝ)(s)` and the two polar contributions
`1/s + 1/(s-1)` this gives Connes' geometric side at every `s` in the half-plane of absolute
convergence, and the spectral sum over the centred Xi divisor equals `-i` times that side.
-/

open ArithmeticFunction MeasureTheory Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **The finite part of Connes' geometric side is the von Mangoldt current.**  For `Re s > 1`,
`∑_p log p · (local Weil term at p) = L(Λ, s)`. -/
theorem connes_weil_primeSide_complex {s : ℂ} (hs : 1 < s.re) :
    (∑' p : Nat.Primes, (Real.log (((p : ℕ) : ℝ)) : ℂ) * connesLocalWeilTerm p s)
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hsum : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [LSeries, tsum_eq_tsum_primes_of_support_subset_prime_powers hsum
    (_root_.RHTower.support_vonMangoldtTerm_subset_primePow s)]
  refine tsum_congr fun p => ?_
  have hz : ‖(((p : ℕ) : ℂ)) ^ (-s)‖ < 1 := connes_padic_norm_cpow_neg_lt_one (p : ℕ) hspos
  have hloc : connesLocalWeilTerm p s
      = (((p : ℕ) : ℂ)) ^ (-s) * (1 - (((p : ℕ) : ℂ)) ^ (-s))⁻¹ :=
    connes_padic_weil_geometric (p : ℕ) hz
  have hgeom : (∑' k : ℕ, ((((p : ℕ) : ℂ)) ^ (-s)) ^ (k + 1))
      = (((p : ℕ) : ℂ)) ^ (-s) * (1 - (((p : ℕ) : ℂ)) ^ (-s))⁻¹ := by
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz]
  calc (Real.log (((p : ℕ) : ℝ)) : ℂ) * connesLocalWeilTerm p s
      = (Real.log (((p : ℕ) : ℝ)) : ℂ) * ∑' k : ℕ, ((((p : ℕ) : ℂ)) ^ (-s)) ^ (k + 1) := by
        rw [hloc, hgeom]
    _ = ∑' k : ℕ, (Real.log (((p : ℕ) : ℝ)) : ℂ) * ((((p : ℕ) : ℂ)) ^ (-s)) ^ (k + 1) :=
        tsum_mul_left.symm
    _ = ∑' k : ℕ,
          LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s ((p : ℕ) ^ (k + 1)) :=
        tsum_congr fun k => (_root_.RHTower.primeGradeSource_term_eq p k).symm

/-- **Connes' geometric side at an arbitrary abscissa.**  The sum over the finite places of the
local Weil terms, minus the polar contributions of the completed zeta, minus the archimedean
local term. -/
def connesGeometricSideC (s : ℂ) : ℂ :=
  (∑' p : Nat.Primes, (Real.log (((p : ℕ) : ℝ)) : ℂ) * connesLocalWeilTerm p s)
    - 1 / s - 1 / (s - 1)
    - ((∫ t in Ioi (0 : ℝ), connesArchWeilIntegrand (s / 2) t)
        - ((Real.log Real.pi : ℝ) : ℂ)) / 2

theorem connesGeometricSideC_eq {s : ℂ} (hs : 1 < s.re) :
    connesGeometricSideC s
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
        - logDeriv _root_.RHTower.archFactor s := by
  have hrepos : 0 < s.re := lt_trans zero_lt_one hs
  have hhalf : 0 < (s / 2).re := by
    rw [show s / 2 = (2 : ℝ)⁻¹ * s by push_cast; ring]
    simpa using hrepos
  have h0 : s ≠ 0 := by
    intro h
    rw [h] at hrepos
    simp at hrepos
  have h1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    rw [hm] at hhalf
    simp only [Complex.neg_re, Complex.natCast_re, neg_pos] at hhalf
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have harch : ((∫ t in Ioi (0 : ℝ), connesArchWeilIntegrand (s / 2) t)
      - ((Real.log Real.pi : ℝ) : ℂ)) / 2 = gammaRealLogConnection s := by
    rw [connes_archWeil_eq_logDeriv_Gammaℝ hrepos, logDeriv_Gammaℝ hrepos]
    ring
  rw [connesGeometricSideC, connes_weil_primeSide_complex hs, harch,
    _root_.RHTower.logDeriv_archFactor_closed_off_poles hpole h0 h1]
  ring

/-- **Connes' trace formula on the resolvent test algebra.**  For every centred base point whose
Xi coordinate lies in the half-plane of absolute convergence, the sum of the regularized Cauchy
kernel over the multiplicity-exact centred Xi divisor is `-i` times Connes' geometric side: the
sum over the places of `ℚ` of the local Weil terms. -/
theorem connes_traceFormula_resolvent_complex {z : ℂ}
    (hz : 1 < ((1 : ℂ) / 2 + z * Complex.I).re) :
    (∑' q : _root_.RHTower.XiZeroCopy,
        _root_.RHTower.xiCauchyRegularizedKernel z (_root_.RHTower.xiSpectralPoint q))
      = -Complex.I * connesGeometricSideC ((1 : ℂ) / 2 + z * Complex.I) := by
  rw [_root_.RHTower.xiGuinandWeilExplicitFormula_single
      (_root_.RHTower.XiExplicitAdmissible_of_one_lt_re hz),
    ← _root_.RHTower.primeArchSourceRelativeTrace_eq_continued hz,
    _root_.RHTower.primeArchSourceRelativeTrace, connesGeometricSideC_eq hz]

end

end GaloisForLFunctions.RHTower
