/-
# The Xi relative resolvent is the completed prime--archimedean flux

The centered Xi coordinate is the static affine change `s = 1/2 + z I`.  Its logarithmic
derivative therefore converts the regulator-independent relative resolvent trace into the
already constructed completed flux `-ξ'/ξ`.  Inside the critical strip this gives the exact
continued-prime plus archimedean/boundary decomposition.  No evolution, zero ordering, or
operator spectrum is introduced.
-/
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition

open Complex Function

namespace RHTower

noncomputable section

/-- Logarithmic derivative under the fixed centered affine coordinate. -/
theorem logDeriv_XiC_eq_mul_I_logDeriv_xi (z : ℂ) :
    logDeriv XiC z = Complex.I * logDeriv xi (1 / 2 + z * Complex.I) := by
  have haff : HasDerivAt (fun w : ℂ => 1 / 2 + w * Complex.I) Complex.I z := by
    convert (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
      ((hasDerivAt_id (𝕜 := ℂ) (x := z)).mul_const Complex.I) using 1
    all_goals ring
  have hderiv : deriv XiC z =
      deriv xi (1 / 2 + z * Complex.I) * Complex.I := by
    exact (xi_differentiable.differentiableAt.hasDerivAt.comp z haff).deriv
  rw [logDeriv_apply, logDeriv_apply, hderiv, XiC]
  ring

/-- The regulator-independent relative trace is exactly the centered completed flux. -/
theorem xiRelativeResolventTrace_eq_completedFlux {z : ℂ} (hz : XiC z ≠ 0) :
    xiRelativeResolventTrace z =
      -Complex.I * seamFluxCochain (1 / 2 + z * Complex.I) := by
  rw [← logDeriv_XiC_eq_relativeResolventTrace hz,
    logDeriv_XiC_eq_mul_I_logDeriv_xi, seamFluxCochain]
  ring

/-- In the open strip away from a zeta zero, the same relative trace is the exact continued
prime flux plus the archimedean/boundary correction. -/
theorem xiRelativeResolventTrace_eq_prime_add_archimedean
    {z : ℂ} (hz : XiC z ≠ 0)
    (hstrip : 0 < (1 / 2 + z * Complex.I).re ∧
      (1 / 2 + z * Complex.I).re < 1)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    xiRelativeResolventTrace z =
      -Complex.I * (infinitePrimeFlux (1 / 2 + z * Complex.I) -
        logDeriv archFactor (1 / 2 + z * Complex.I)) := by
  rw [xiRelativeResolventTrace_eq_completedFlux hz,
    seamFluxCochain_eq_infinitePrimeFlux_add_archimedean hstrip hzeta]

/-- On the absolute-convergence half-plane, the completed flux splits into its canonical
von-Mangoldt prime source and archimedean/boundary term without any cutoff or enumeration. -/
theorem seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    seamFluxCochain s = infinitePrimeFlux s - logDeriv archFactor s := by
  let U : Set ℂ := {z | 1 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hs
  have hev : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hsU] with z hz
    exact xi_eq_archFactor_mul_zeta
      (by intro h; subst z; change 1 < (0 : ℂ).re at hz; norm_num at hz)
      (by intro h; subst z; change 1 < (1 : ℂ).re at hz; norm_num at hz)
      (Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hz))
  have hlog : logDeriv xi s =
      logDeriv (fun z => archFactor z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have haf : archFactor s ≠ 0 := archFactor_ne_zero
    (by intro h; subst s; norm_num at hs)
    (by intro h; subst s; norm_num at hs)
    (Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs))
  rw [seamFluxCochain, infinitePrimeFlux, hlog,
    logDeriv_completed_split haf hzeta
      (hasDerivAt_archFactor_of_re_pos (lt_trans zero_lt_one hs)).differentiableAt
      (differentiableAt_riemannZeta (by intro h; subst s; norm_num at hs))]
  ring

/-- **Regulator-independent source relative trace.** On the half-plane where the Euler source is
absolutely convergent, this is the unordered von-Mangoldt `LSeries` plus the fixed
archimedean/boundary completion.  The definition contains no Xi zero data. -/
def primeArchSourceRelativeTrace (z : ℂ) : ℂ :=
  -Complex.I *
    (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (1 / 2 + z * Complex.I) -
      logDeriv archFactor (1 / 2 + z * Complex.I))

/-- **Source identity on the absolute-convergence domain.** The prime--archimedean source trace is
the centered Xi relative resolvent.  All convergence is intrinsic `tsum`/`LSeries` convergence;
no prime cutoff path or zero ordering occurs. -/
theorem primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    {z : ℂ} (hs : 1 < (1 / 2 + z * Complex.I).re) :
    primeArchSourceRelativeTrace z = xiRelativeResolventTrace z := by
  let s : ℂ := 1 / 2 + z * Complex.I
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.one_re] at hre
    linarith
  have hG := Gammaℝ_ne_zero_of_re_pos hspos
  have hXi : XiC z ≠ 0 := by
    change xi s ≠ 0
    rw [xi_eq_archFactor_mul_zeta hs0 hs1 hG]
    exact mul_ne_zero (archFactor_ne_zero hs0 hs1 hG) hzeta
  rw [primeArchSourceRelativeTrace]
  change -Complex.I *
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        logDeriv archFactor s) = _
  rw [← infinitePrimeFlux_eq_vonMangoldtLSeries hs,
    ← seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs,
    ← xiRelativeResolventTrace_eq_completedFlux hXi]

/-- The prime--archimedean decomposition is valid throughout the positive-real-part domain away
from the boundary point `1` and zeta zeros.  This is the source-side meromorphic continuation of
the absolutely convergent half-plane trace. -/
theorem seamFluxCochain_eq_continuedPrime_add_archimedean
    {s : ℂ} (hspos : 0 < s.re) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    seamFluxCochain s = infinitePrimeFlux s - logDeriv archFactor s := by
  let U : Set ℂ := {z | 0 < z.re} ∩ ({1} : Set ℂ)ᶜ
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hsU : s ∈ U := ⟨hspos, by simpa⟩
  have hev : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hsU] with z hz
    exact xi_eq_archFactor_mul_zeta
      (by intro h; subst z; have hpos := hz.1; norm_num at hpos)
      (by simpa using hz.2)
      (Gammaℝ_ne_zero_of_re_pos hz.1)
  have hlog : logDeriv xi s =
      logDeriv (fun z => archFactor z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hspos
  have haf : archFactor s ≠ 0 :=
    archFactor_ne_zero hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hspos)
  rw [seamFluxCochain, infinitePrimeFlux, hlog,
    logDeriv_completed_split haf hzeta
      (hasDerivAt_archFactor_of_re_pos hspos).differentiableAt
      (differentiableAt_riemannZeta hs1)]
  ring

/-- **Continued regulator-independent source trace.** This definition uses only the continued
prime carrier `-ζ'/ζ` and the fixed archimedean/boundary factor.  It contains neither Xi-zero
data nor a prime exhaustion. -/
def continuedPrimeArchSourceRelativeTrace (z : ℂ) : ℂ :=
  -Complex.I *
    (infinitePrimeFlux (1 / 2 + z * Complex.I) -
      logDeriv archFactor (1 / 2 + z * Complex.I))

/-- **Continued source identity.** On the positive-real-part domain away from its natural poles,
the source-built prime--archimedean relative trace is exactly the Xi relative resolvent. -/
theorem continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    {z : ℂ} (hspos : 0 < (1 / 2 + z * Complex.I).re)
    (hs1 : 1 / 2 + z * Complex.I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    continuedPrimeArchSourceRelativeTrace z = xiRelativeResolventTrace z := by
  let s : ℂ := 1 / 2 + z * Complex.I
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    linarith
  have hG := Gammaℝ_ne_zero_of_re_pos hspos
  have hXi : XiC z ≠ 0 := by
    change xi s ≠ 0
    rw [xi_eq_archFactor_mul_zeta hs0 hs1 hG]
    exact mul_ne_zero (archFactor_ne_zero hs0 hs1 hG) hzeta
  rw [continuedPrimeArchSourceRelativeTrace]
  change -Complex.I * (infinitePrimeFlux s - logDeriv archFactor s) = _
  rw [← seamFluxCochain_eq_continuedPrime_add_archimedean hspos hs1 hzeta,
    ← xiRelativeResolventTrace_eq_completedFlux hXi]

/-- The absolutely convergent Dirichlet-series source and its meromorphic continuation agree on
their common half-plane.  No limiting process is used to define the continuation. -/
theorem primeArchSourceRelativeTrace_eq_continued
    {z : ℂ} (hs : 1 < (1 / 2 + z * Complex.I).re) :
    primeArchSourceRelativeTrace z = continuedPrimeArchSourceRelativeTrace z := by
  rw [primeArchSourceRelativeTrace, continuedPrimeArchSourceRelativeTrace,
    infinitePrimeFlux_eq_vonMangoldtLSeries hs]

end

end RHTower
