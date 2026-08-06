import GaloisForLFunctions.RHTower.BVPrimeWindowDilationOrientation
import GaloisForLFunctions.HTGeometry.CoefficientDecimationSieve

/-!
# The prime-sieved BV source and its Laurent residue

Coefficient decimation by a positive integer acts on the complete prime--polar
coefficient of a compact BV window as argument dilation of the window: the finite
prime part is reindexed, and the archimedean counterterm rescales by the exact
Mellin character.  This is the source-side decimation law before any
continuation.

Applying the Möbius expansion of the off-multiple sieve therefore writes the
Dirichlet series of the sieved coefficient sequence as a finite alternating
combination of dilated continued sources, which is its canonical meromorphic
continuation.  At every zero of the pole-filled zeta the residue of that
combination collapses: the two characters `d^{-(rho+1/2)}` and `d^{rho-1/2}`
cancel to `d^{-1}`, and the Möbius divisor sum of the primorial is the Euler
product of the sieve.  The sieved source therefore carries exactly the sieve
density times the unsieved residue.
-/

open Complex Filter MeasureTheory Set Topology
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

open GaloisForLFunctions.HTGeometry

private theorem natCast_pos' {d : ℕ} (hd : 0 < d) : (0 : ℝ) < d :=
  Nat.cast_pos.mpr hd

/-- Argument dilation by a natural number, total in the index. -/
def natDilate (W : CompactBVPrimeWindow) (d : ℕ) : CompactBVPrimeWindow :=
  W.argumentDilation (max ((d : ℝ)) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))

theorem natDilate_eq (W : CompactBVPrimeWindow) {d : ℕ} (hd : 0 < d) :
    W.natDilate d = W.argumentDilation ((d : ℝ)) (natCast_pos' hd) := by
  have hmax : max ((d : ℝ)) 1 = (d : ℝ) := max_eq_left (by exact_mod_cast hd)
  rw [natDilate]
  congr 1

theorem mellinTransform_natDilate (W : CompactBVPrimeWindow) {d : ℕ} (hd : 0 < d)
    (s : ℂ) :
    (W.natDilate d).mellinTransform s = ((d : ℂ)) ^ (s - 1) * W.mellinTransform s := by
  rw [natDilate_eq W hd, mellinTransform_argumentDilation]
  push_cast
  ring

theorem continuedSourceResidueValue_natDilate (W : CompactBVPrimeWindow) {d : ℕ}
    (hd : 0 < d) (rho : ℂ) :
    (W.natDilate d).continuedSourceResidueValue rho
      = ((d : ℂ)) ^ (rho - 1 / 2) * W.continuedSourceResidueValue rho := by
  rw [natDilate_eq W hd, continuedSourceResidueValue_argumentDilation]
  push_cast
  ring

/-- Decimation reindexes the finite prime window as argument dilation. -/
theorem weightedPrimeWindow_decimate (W : CompactBVPrimeWindow) {q : ℕ} (hq : 0 < q)
    (n : ℕ) :
    W.weightedPrimeWindow (q * n) = (W.natDilate q).weightedPrimeWindow n := by
  rw [natDilate_eq W hq, weightedPrimeWindow, weightedPrimeWindow]
  refine tsum_congr fun k => ?_
  congr 1
  rw [argumentDilation_apply]
  congr 1
  push_cast
  rw [mul_div_assoc]

/-- **Source decimation law.**  Coefficient decimation by a positive integer acts
on the complete prime--polar coefficient as argument dilation of the window. -/
theorem polarCoefficient_decimate (W : CompactBVPrimeWindow) {q : ℕ} (hq : 0 < q)
    (n : ℕ) :
    W.polarCoefficient (q * n) = (W.natDilate q).polarCoefficient n := by
  have hsqrt : (Real.sqrt ((q * n : ℕ) : ℝ) : ℝ) = Real.sqrt q * Real.sqrt n := by
    push_cast
    exact Real.sqrt_mul (Nat.cast_nonneg q) _
  have hchar : ((q : ℂ)) ^ ((3 / 2 : ℂ) - 1) = ((Real.sqrt q : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg q)]
    norm_num
  rw [polarCoefficient, polarCoefficient, mellinTransform_natDilate W hq,
    weightedPrimeWindow_decimate W hq, hsqrt, hchar]
  push_cast
  ring

/-- The source decimation law in coefficient-operator form. -/
theorem decimate_polarCoefficient (W : CompactBVPrimeWindow) {q : ℕ} (hq : 0 < q) :
    decimate q W.polarCoefficient = (W.natDilate q).polarCoefficient := by
  funext n
  exact polarCoefficient_decimate W hq n

/-- The canonical continuation of the Dirichlet series of the sieved
prime--polar coefficient: a finite Möbius combination of dilated continued
sources. -/
def sievedContinuedSource (W : CompactBVPrimeWindow) (P : Finset Nat.Primes)
    (s : ℂ) : ℂ :=
  ∑ d ∈ (sievePrimorial P).divisors,
    ((μ d : ℤ) : ℂ) * (((d : ℂ)) ^ (-s) * (W.natDilate d).continuedSource s)

/-- **The sieved source is the continuation of the sieved coefficient
sequence.**  On the initial half-plane the ordinary Dirichlet series of the
off-multiple sieve of the prime--polar coefficient is the finite Möbius
combination of dilated continued sources. -/
theorem LSeries_sieveOffMultiple_polarCoefficient (W : CompactBVPrimeWindow)
    (P : Finset Nat.Primes) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries (sieveOffMultiple P W.polarCoefficient) s = W.sievedContinuedSource P s := by
  classical
  have hpol : LSeriesSummable W.polarCoefficient s := W.polarCoefficient_LSeriesSummable hs
  have hsummand : ∀ d ∈ (sievePrimorial P).divisors,
      LSeriesSummable
        ((((μ d : ℤ) : ℂ)) • multipleProjection d W.polarCoefficient) s := by
    intro d hd
    exact (LSeriesSummable_multipleProjection (Nat.pos_of_mem_divisors hd) hpol).smul _
  have hfun : sieveOffMultiple P W.polarCoefficient
      = ∑ d ∈ (sievePrimorial P).divisors,
          (((μ d : ℤ) : ℂ)) • multipleProjection d W.polarCoefficient := by
    funext M
    rw [Finset.sum_apply]
    exact sieveOffMultiple_eq_sum_divisors P _ M
  rw [hfun, LSeries_sum hsummand, sievedContinuedSource]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [LSeries_smul, LSeries_multipleProjection hd0, decimate_polarCoefficient W hd0,
    LSeries_polarCoefficient_eq_continuedSource _ hs]

/-- **The sieved Laurent residue law.**  At every zero of the pole-filled zeta the
prime-sieved BV source carries exactly the sieve density times the unsieved
residue: the decimation and inflation characters cancel to `d^{-1}` on every
divisor of the primorial, and the Möbius divisor sum of the primorial is the
Euler product of the sieve. -/
theorem tendsto_sievedContinuedSource_residue (W : CompactBVPrimeWindow)
    (P : Finset Nat.Primes) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0) :
    Tendsto (fun s : ℂ => (s - (rho + 1 / 2)) * W.sievedContinuedSource P s)
      (𝓝[≠] (rho + 1 / 2))
      (𝓝 (((sieveDensity P : ℝ) : ℂ) * W.continuedSourceResidueValue rho)) := by
  classical
  have hsum : ∀ d ∈ (sievePrimorial P).divisors,
      ((μ d : ℤ) : ℂ) * (((d : ℂ)) ^ (-(rho + 1 / 2))
          * (W.natDilate d).continuedSourceResidueValue rho)
        = (((μ d : ℤ) : ℂ) / (d : ℂ)) * W.continuedSourceResidueValue rho := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdC : ((d : ℂ)) ≠ 0 := by exact_mod_cast hd0.ne'
    have hchars : ((d : ℂ)) ^ (-(rho + 1 / 2)) * ((d : ℂ)) ^ (rho - 1 / 2)
        = ((d : ℂ))⁻¹ := by
      rw [← Complex.cpow_add _ _ hdC, show -(rho + 1 / 2) + (rho - 1 / 2) = -1 by ring,
        Complex.cpow_neg_one]
    rw [continuedSourceResidueValue_natDilate W hd0,
      show ((μ d : ℤ) : ℂ) * (((d : ℂ)) ^ (-(rho + 1 / 2))
            * (((d : ℂ)) ^ (rho - 1 / 2) * W.continuedSourceResidueValue rho))
        = (((d : ℂ)) ^ (-(rho + 1 / 2)) * ((d : ℂ)) ^ (rho - 1 / 2))
            * (((μ d : ℤ) : ℂ) * W.continuedSourceResidueValue rho) from by ring,
      hchars]
    field_simp
  have hval : ((sieveDensity P : ℝ) : ℂ) * W.continuedSourceResidueValue rho
      = ∑ d ∈ (sievePrimorial P).divisors,
          ((μ d : ℤ) : ℂ) * (((d : ℂ)) ^ (-(rho + 1 / 2))
            * (W.natDilate d).continuedSourceResidueValue rho) := by
    rw [Finset.sum_congr rfl hsum, ← Finset.sum_mul, sum_divisors_moebiusDiv_complex]
  rw [hval]
  have hterm : ∀ d ∈ (sievePrimorial P).divisors,
      Tendsto (fun s : ℂ => ((μ d : ℤ) : ℂ)
          * (((d : ℂ)) ^ (-s) * ((s - (rho + 1 / 2)) * (W.natDilate d).continuedSource s)))
        (𝓝[≠] (rho + 1 / 2))
        (𝓝 (((μ d : ℤ) : ℂ) * (((d : ℂ)) ^ (-(rho + 1 / 2))
          * (W.natDilate d).continuedSourceResidueValue rho))) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdC : ((d : ℂ)) ≠ 0 := by exact_mod_cast hd0.ne'
    have hres := (W.natDilate d).tendsto_continuedSource_residue_of_regularizedZeta_zero
      hrho hzero
    have hcpow : Tendsto (fun s : ℂ => ((d : ℂ)) ^ (-s)) (𝓝[≠] (rho + 1 / 2))
        (𝓝 (((d : ℂ)) ^ (-(rho + 1 / 2)))) := by
      have h1 : ContinuousAt (fun z : ℂ => ((d : ℂ)) ^ z) (-(rho + 1 / 2)) :=
        continuousAt_const_cpow hdC
      exact h1.tendsto.comp ((continuous_neg.tendsto _).mono_left nhdsWithin_le_nhds)
    exact (hcpow.mul hres).const_mul _
  refine Tendsto.congr ?_ (tendsto_finsetSum _ hterm)
  intro s
  rw [sievedContinuedSource, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **Source-normal blow-up of the sieved residue.**  The sieve density is
strictly positive for every finite prime set, so dividing it out recovers the
unsieved residue exactly: the principal-conormal direction survives the sieve at
every finite stage. -/
theorem tendsto_sievedContinuedSource_residue_normalized (W : CompactBVPrimeWindow)
    (P : Finset Nat.Primes) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0) :
    Tendsto (fun s : ℂ => ((sieveDensity P : ℝ) : ℂ)⁻¹
        * ((s - (rho + 1 / 2)) * W.sievedContinuedSource P s))
      (𝓝[≠] (rho + 1 / 2)) (𝓝 (W.continuedSourceResidueValue rho)) := by
  have hpos : ((sieveDensity P : ℝ) : ℂ) ≠ 0 := by
    simpa using (sieveDensity_pos P).ne'
  have h := (tendsto_sievedContinuedSource_residue W P hrho hzero).const_mul
    (((sieveDensity P : ℝ) : ℂ)⁻¹)
  rwa [← mul_assoc, inv_mul_cancel₀ hpos, one_mul] at h

/-- **Coarse cofinal collapse of the sieved residue.**  Along any enumeration of
the primes the sieved residue tends to zero: the sieve density is the whole
obstruction, and it vanishes cofinally. -/
theorem tendsto_sievedResidueValue_sievePrefix (W : CompactBVPrimeWindow)
    (e : ℕ ≃ Nat.Primes) (rho : ℂ) :
    Tendsto (fun m : ℕ => ((sieveDensity (sievePrefix e m) : ℝ) : ℂ)
        * W.continuedSourceResidueValue rho) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => ((sieveDensity (sievePrefix e m) : ℝ) : ℂ)) atTop
      (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_sieveDensity_sievePrefix e)
  rw [Complex.ofReal_zero] at h
  simpa using h.mul_const (W.continuedSourceResidueValue rho)

end CompactBVPrimeWindow
end RHTower
