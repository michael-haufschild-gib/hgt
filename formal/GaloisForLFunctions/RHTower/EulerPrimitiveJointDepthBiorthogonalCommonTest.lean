import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthHilbertSource
import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestSource

/-!
# Biorthogonal joint-depth primitive common-test source

Route R requires primitive promotion to remain attached to the complete
`(prime, valuation-depth)` carrier until the source pairing. The existing
positive common-test realization takes a geometric mean of the von Mangoldt
mass before pairing. Here the two legs remain different:

* source coefficient `log p / sqrt(p^(e+1))`;
* reciprocal-promotion co-source coefficient `1 / sqrt(p^(e+1))`.

Complex Hardy damping makes both legs Hilbert vectors for positive real
parameter. Their coordinate pairing is the exact von Mangoldt Dirichlet
term, and the full Hilbert pairing is the two-variable prime Laplace channel.
Tensoring with the common Hardy Cauchy factor therefore lands exactly in the
existing primitive common-test kernel, without early depth scalarization.
-/

open Complex Function Set Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

def xiGammaEulerPrimitiveCommonTestSourceCoeff (w : ℂ) (pe : Nat.Primes × ℕ) : ℂ :=
  (xiGammaEulerPrimitiveBoundaryAmplitude 0 pe : ℂ) *
    ((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹

def xiGammaEulerPrimitiveCommonTestCoSourceCoeff (w : ℂ) (pe : Nat.Primes × ℕ) : ℂ :=
  (xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) *
    ((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹

theorem xiGammaEulerPrimitiveDescentTestAmplitude_sq_eq_valuation (u : ℝ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveDescentTestAmplitude u pe ^ 2 =
      (xiGammaEulerValuationNat pe : ℝ)⁻¹ *
        Real.exp (-u * Real.log (xiGammaEulerValuationNat pe : ℝ)) := by
  have hlog : Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
  rw [xiGammaEulerPrimitiveDescentTestAmplitude_sq,
    xiGammaEulerBoundaryRealAmplitude_sq]
  field_simp [hlog]

theorem xiGammaEulerPrimitiveCommonTestSourceCoeff_norm_sq (w : ℂ) (pe : Nat.Primes × ℕ) :
    ‖xiGammaEulerPrimitiveCommonTestSourceCoeff w pe‖ ^ 2 =
      xiGammaEulerPrimitiveBoundaryAmplitude (2 * w.re) pe ^ 2 := by
  have hn : (0 : ℝ) < (xiGammaEulerValuationNat pe : ℝ) := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hcast : (xiGammaEulerValuationNat pe : ℂ) =
      ((xiGammaEulerValuationNat pe : ℝ) : ℂ) := by norm_num
  rw [xiGammaEulerPrimitiveCommonTestSourceCoeff, hcast, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hn,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 pe),
    mul_pow, xiGammaEulerPrimitiveBoundaryAmplitude_sq,
    xiGammaEulerPrimitiveBoundaryAmplitude_sq]
  rw [Real.rpow_def_of_pos hn]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  ring_nf

theorem xiGammaEulerPrimitiveCommonTestCoSourceCoeff_norm_sq (w : ℂ) (pe : Nat.Primes × ℕ) :
    ‖xiGammaEulerPrimitiveCommonTestCoSourceCoeff w pe‖ ^ 2 =
      xiGammaEulerPrimitiveDescentTestAmplitude (2 * w.re) pe ^ 2 := by
  have hn : (0 : ℝ) < (xiGammaEulerValuationNat pe : ℝ) := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hcast : (xiGammaEulerValuationNat pe : ℂ) =
      ((xiGammaEulerValuationNat pe : ℝ) : ℂ) := by norm_num
  rw [xiGammaEulerPrimitiveCommonTestCoSourceCoeff, hcast, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hn,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (xiGammaEulerPrimitiveDescentTestAmplitude_pos 0 pe),
    mul_pow, xiGammaEulerPrimitiveDescentTestAmplitude_sq_eq_valuation,
    xiGammaEulerPrimitiveDescentTestAmplitude_sq_eq_valuation]
  rw [Real.rpow_def_of_pos hn]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  rw [← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  ring_nf

def xiGammaEulerPrimitiveCommonTestSourceLp (w : ℂ) (hw : 0 < w.re) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ⟨xiGammaEulerPrimitiveCommonTestSourceCoeff w, HilbertSchmidt.memℓp_of_sq <| by
    simpa only [xiGammaEulerPrimitiveCommonTestSourceCoeff_norm_sq] using
      summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_of_pos
        (show 0 < 2 * w.re by linarith)⟩

def xiGammaEulerPrimitiveCommonTestCoSourceLp (w : ℂ) (hw : 0 < w.re) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ⟨xiGammaEulerPrimitiveCommonTestCoSourceCoeff w, HilbertSchmidt.memℓp_of_sq <| by
    simpa only [xiGammaEulerPrimitiveCommonTestCoSourceCoeff_norm_sq] using
      summable_sq_xiGammaEulerPrimitiveDescentTestAmplitude_of_pos
        (show 0 < 2 * w.re by linarith)⟩

@[simp] theorem xiGammaEulerPrimitiveCommonTestSourceLp_apply (w : ℂ) (hw : 0 < w.re)
    (pe : Nat.Primes × ℕ) : xiGammaEulerPrimitiveCommonTestSourceLp w hw pe = xiGammaEulerPrimitiveCommonTestSourceCoeff w pe := rfl

@[simp] theorem xiGammaEulerPrimitiveCommonTestCoSourceLp_apply (w : ℂ) (hw : 0 < w.re)
    (pe : Nat.Primes × ℕ) : xiGammaEulerPrimitiveCommonTestCoSourceLp w hw pe = xiGammaEulerPrimitiveCommonTestCoSourceCoeff w pe := rfl

theorem xiGammaEulerPrimitiveBoundary_mul_descent_zero_eq_depthOne_sq
    (pe : Nat.Primes × ℕ) :
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 pe : ℂ) *
        (xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) ^ 2 := by
  have hn : xiGammaEulerValuationNat pe ≠ 0 := by
    unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ pe.1.property.ne_zero
  calc
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 pe : ℂ) *
          (xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) =
        (eulerPrimeCurrentMass 1 (xiGammaEulerValuationNat pe) : ℂ) := by
      norm_cast
      simpa using xiGammaEulerPrimitiveBoundaryAmplitude_mul_descentTest 0 pe
    _ = finiteVonMangoldtWeight (xiGammaEulerValuationNat pe) := by
      rw [finiteVonMangoldtWeight, ofReal_eulerPrimeCurrentMass_eq]
      norm_num
    _ = finiteVonMangoldtDepthOneAmplitude
          (xiGammaEulerValuationNat pe) ^ 2 :=
      (finiteVonMangoldtDepthOneAmplitude_sq hn).symm

theorem xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term
    (w v : ℂ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCommonTestSourceCoeff w pe * star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff v pe) =
      LSeries.term
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (w + star v + 1) (xiGammaEulerValuationNat pe) := by
  have hn : xiGammaEulerValuationNat pe ≠ 0 := by
    unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ pe.1.property.ne_zero
  have hstarDescent :
      star ((xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ v)⁻¹) =
        (xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ star v)⁻¹ := by
    rw [show star (_ * _) = star (_ : ℂ) * star (_ : ℂ) by
      exact map_mul (starRingEnd ℂ) _ _]
    change (starRingEnd ℂ) (_ : ℂ) * star (_ : ℂ) = _
    rw [Complex.conj_ofReal, star_eulerPrimitivePrimeFeature v _ hn]
  have hstarDepthOne :
      star (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ v)⁻¹) =
        finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ star v)⁻¹ := by
    rw [show star (_ * _) = star (_ : ℂ) * star (_ : ℂ) by
      exact map_mul (starRingEnd ℂ) _ _,
      star_eulerPrimitivePrimeFeature v _ hn]
    simp [finiteVonMangoldtDepthOneAmplitude]
  rw [← eulerPrimitiveCommonTestLabelWeight_eq_term]
  rw [xiGammaEulerPrimitiveCommonTestSourceCoeff, xiGammaEulerPrimitiveCommonTestCoSourceCoeff, hstarDescent, hstarDepthOne]
  calc
    (xiGammaEulerPrimitiveBoundaryAmplitude 0 pe : ℂ) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹ *
        ((xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ star v)⁻¹) =
      ((xiGammaEulerPrimitiveBoundaryAmplitude 0 pe : ℂ) *
          (xiGammaEulerPrimitiveDescentTestAmplitude 0 pe : ℂ)) *
        (((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹ *
          ((xiGammaEulerValuationNat pe : ℂ) ^ star v)⁻¹) := by ring
    _ = finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) ^ 2 *
        (((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹ *
          ((xiGammaEulerValuationNat pe : ℂ) ^ star v)⁻¹) := by
      rw [xiGammaEulerPrimitiveBoundary_mul_descent_zero_eq_depthOne_sq]
    _ = finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ w)⁻¹ *
        (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
          ((xiGammaEulerValuationNat pe : ℂ) ^ star v)⁻¹) := by ring

theorem xiGammaEulerValuationNat_injective_commonTest : Function.Injective xiGammaEulerValuationNat := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have hpq : (p : ℕ) = (q : ℕ) :=
    eq_of_prime_pow_eq p.property.prime q.property.prime (by omega) h
  have hpq' : p = q := Subtype.ext hpq
  subst q
  have hef : e + 1 = f + 1 :=
    (Nat.pow_right_injective p.property.two_le) h
  congr
  omega

theorem inner_xiGammaEulerPrimitiveCommonTestCoSource_source_eq
    (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    inner ℂ (xiGammaEulerPrimitiveCommonTestCoSourceLp v hv) (xiGammaEulerPrimitiveCommonTestSourceLp w hw) =
      vonMangoldtPrimeLaplaceChannelComplex (w + star v) := by
  have hs : Summable (LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      (w + star v + 1)) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    change 1 < w.re + v.re + 1
    linarith
  have hsupport : Function.support (LSeries.term
      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      (w + star v + 1)) ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hpow
    apply hn
    simp [LSeries.term,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
  have hreindex :=
    tsum_eq_tsum_primes_of_support_subset_prime_powers hs hsupport
  rw [lp.inner_eq_tsum]
  calc
    (∑' pe : Nat.Primes × ℕ,
        inner ℂ (xiGammaEulerPrimitiveCommonTestCoSourceLp v hv pe) (xiGammaEulerPrimitiveCommonTestSourceLp w hw pe)) =
      ∑' pe : Nat.Primes × ℕ,
        LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (w + star v + 1) (xiGammaEulerValuationNat pe) := by
      apply tsum_congr
      intro pe
      rw [xiGammaEulerPrimitiveCommonTestCoSourceLp_apply, xiGammaEulerPrimitiveCommonTestSourceLp_apply, RCLike.inner_apply]
      change xiGammaEulerPrimitiveCommonTestSourceCoeff w pe * star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff v pe) = _
      exact xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term w v pe
    _ = ∑' p : Nat.Primes, ∑' e : ℕ,
        LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (w + star v + 1) (p ^ (e + 1)) := by
      have hpair : Summable (fun pe : Nat.Primes × ℕ =>
          LSeries.term
            (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            (w + star v + 1) (xiGammaEulerValuationNat pe)) :=
        hs.comp_injective xiGammaEulerValuationNat_injective_commonTest
      simpa only [xiGammaEulerValuationNat] using hpair.tsum_prod
    _ = ∑' n : ℕ,
        LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          (w + star v + 1) n := hreindex.symm
    _ = vonMangoldtPrimeLaplaceChannelComplex (w + star v) := rfl

def xiGammaEulerPrimitiveJointDepthCommonTestPairing
    (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) : ℂ :=
  inner ℂ (xiGammaEulerPrimitiveCommonTestCoSourceLp v hv) (xiGammaEulerPrimitiveCommonTestSourceLp w hw) *
    (1 / (w + star v))

theorem xiGammaEulerPrimitiveJointDepthCommonTestPairing_eq
    (w v : ℂ) (hw : 0 < w.re) (hv : 0 < v.re) :
    xiGammaEulerPrimitiveJointDepthCommonTestPairing w v hw hv =
      eulerPrimitiveCommonTestKernel w v := by
  rw [xiGammaEulerPrimitiveJointDepthCommonTestPairing,
    inner_xiGammaEulerPrimitiveCommonTestCoSource_source_eq, eulerPrimitiveCommonTestKernel]

end
end RHTower
