import GaloisForLFunctions.RHTower.VonMangoldtGammaConormalEulerBoundary
import GaloisForLFunctions.RHTower.VonMangoldtGammaInfinitePointedWard
import GaloisForLFunctions.RHTower.XiHurwitzAnchorPrimeTwoOrientationEnergy
import GaloisForLFunctions.RHTower.XiReciprocalFixedCauchyRealKrylovPrimeSeamWeld

/-!
# Dual prime-two Euler boundary calibration of Hurwitz monodromy and the first-prime seam

The Gamma-renormalized Euler boundary source already contains the periodic Hurwitz character at
one explicit prime-power cell.  At the prime-two ground cell, sample the boundary with damping and
phase

`u(s) = -4 * pi * Im(s) / log 2`, `t(s) = 4 * pi * Re(s) / log 2`.

The resulting source coordinate is exactly

`sqrt(log 2 / 2) * exp(-2 * pi * I * s)`.

There is a second, source-natural calibration: damping `2 * Re(s)` and height phase `2 * Im(s)`
give `sqrt(log 2 / 2) * 2^(-s)`.  Its FE/Schwarz difference is therefore the actual first-prime
von Mangoldt seam, up to one fixed nonzero normalization.  Unlike the monodromy calibration,
which compares phase at common damping, this radial calibration compares damping at common phase.

Therefore the functional-equation/Schwarz difference of two genuine Euler boundary samples has
the same zero fibre as the existing first-prime Hurwitz seam.  More strongly, its squared norm is
an explicit positive multiple of the Xi--Hurwitz orientation defect.  This closes the missing
prime--Gamma-to-Hurwitz-character interface; it does not prove that the calibrated source seam
vanishes.
-/

open Complex

namespace RHTower

noncomputable section

open HurwitzOrbit

/-- Damping which turns the prime-two Euler radial factor into Hurwitz monodromy magnitude. -/
def xiHurwitzPrimeTwoEulerDamping (s : ℂ) : ℝ :=
  -4 * Real.pi * s.im / Real.log 2

/-- Phase which turns the prime-two Euler height character into Hurwitz monodromy phase. -/
def xiHurwitzPrimeTwoEulerPhase (s : ℂ) : ℝ :=
  4 * Real.pi * s.re / Real.log 2

/-- Prime-two ground valuation cell. -/
def xiPrimeTwoEulerCell : Nat.Primes × ℕ :=
  (⟨2, Nat.prime_two⟩, 0)

/-- Gamma-renormalized Euler boundary sampled at the Hurwitz calibration parameters. -/
def xiHurwitzPrimeTwoEulerBoundarySample (s : ℂ) : ℂ :=
  xiGammaEulerHeightBoundaryFeature
    (xiHurwitzPrimeTwoEulerDamping s)
    (xiHurwitzPrimeTwoEulerPhase s)
    xiPrimeTwoEulerCell

/-- **Prime--Hurwitz calibration.**  One genuine Gamma-renormalized prime-two Euler coordinate is
exactly the periodic Hurwitz monodromy character, up to its fixed positive source amplitude. -/
theorem xiHurwitzPrimeTwoEulerBoundarySample_eq_monoScalar (s : ℂ) :
    xiHurwitzPrimeTwoEulerBoundarySample s =
      (Real.sqrt (Real.log 2 / 2) : ℂ) * monoScalar s := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≠ 0 := hlogpos.ne'
  have hu :
      -(xiHurwitzPrimeTwoEulerDamping s * Real.log 2) =
        4 * Real.pi * s.im := by
    unfold xiHurwitzPrimeTwoEulerDamping
    field_simp
  have ht :
      -(xiHurwitzPrimeTwoEulerPhase s * Real.log 2 / 2) =
        -2 * Real.pi * s.re := by
    unfold xiHurwitzPrimeTwoEulerPhase
    field_simp
    ring
  have hu' :
      -xiHurwitzPrimeTwoEulerDamping s * Real.log 2 =
        4 * Real.pi * s.im := by
    rw [← hu]
    ring
  have hphase :
      -(((xiHurwitzPrimeTwoEulerPhase s * Real.log 2 / 2 : ℝ) : ℂ) * Complex.I) =
        (((-2 * Real.pi * s.re : ℝ) : ℂ) * Complex.I) := by
    rw [← neg_mul]
    apply congrArg (fun z : ℂ => z * Complex.I)
    exact_mod_cast ht
  have hexpReal :
      Real.sqrt (Real.log 2 / 2 * Real.exp (4 * Real.pi * s.im)) =
        Real.sqrt (Real.log 2 / 2) * Real.exp (2 * Real.pi * s.im) := by
    rw [show Real.exp (4 * Real.pi * s.im) =
        Real.exp (2 * Real.pi * s.im) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ Real.log 2 / 2),
      Real.sqrt_sq (Real.exp_pos _).le]
  have hexponent :
      -(2 * (Real.pi : ℂ) * Complex.I * s) =
        (2 * Real.pi * s.im : ℝ) +
          ((-2 * Real.pi * s.re : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [xiHurwitzPrimeTwoEulerBoundarySample,
    xiGammaEulerHeightBoundaryFeature]
  simp only [xiPrimeTwoEulerCell, xiGammaEulerValuationNat, Nat.zero_add,
    pow_one, Nat.cast_ofNat]
  rw [hu', hphase, hexpReal, monoScalar, hexponent, Complex.exp_add,
    ← Complex.ofReal_exp]
  push_cast
  ring

/-- The two functional-equation/Schwarz endpoint samples use the same Euler damping. -/
theorem xiHurwitzPrimeTwoEulerDamping_conj_eq_one_sub (rho : ℂ) :
    xiHurwitzPrimeTwoEulerDamping ((starRingEnd ℂ) rho) =
      xiHurwitzPrimeTwoEulerDamping (1 - rho) := by
  simp [xiHurwitzPrimeTwoEulerDamping]

/-- Their common damping is positive on the upper half-plane. -/
theorem xiHurwitzPrimeTwoEulerDamping_conj_pos
    {rho : ℂ} (him : 0 < rho.im) :
    0 < xiHurwitzPrimeTwoEulerDamping ((starRingEnd ℂ) rho) := by
  rw [xiHurwitzPrimeTwoEulerDamping]
  rw [Complex.conj_im]
  rw [show -4 * Real.pi * -rho.im / Real.log 2 =
      4 * Real.pi * rho.im / Real.log 2 by ring]
  positivity

/-! ## Exact radial calibration of the first-prime source seam -/

/-- Source damping which realizes the reciprocal prime character `2^(-s)`. -/
def xiPrimeTwoEulerRadialDamping (s : ℂ) : ℝ :=
  2 * s.re

/-- Source height phase which realizes the reciprocal prime character `2^(-s)`. -/
def xiPrimeTwoEulerHeightPhase (s : ℂ) : ℝ :=
  2 * s.im

/-- **All-cell radial Euler calibration.**  At damping `2 * Re(s)` and phase `2 * Im(s)`, every
Gamma-renormalized prime-power boundary coordinate is exactly its square-root von Mangoldt
amplitude times the reciprocal prime-power character. -/
theorem xiGammaEulerHeightBoundaryFeature_radial_eq_cpow
    (s : ℂ) (pe : Nat.Primes × ℕ) :
    xiGammaEulerHeightBoundaryFeature
        (xiPrimeTwoEulerRadialDamping s) (xiPrimeTwoEulerHeightPhase s) pe =
      (Real.sqrt
          (Real.log (pe.1 : ℝ) /
            (xiGammaEulerValuationNat pe : ℝ)) : ℂ) *
        (xiGammaEulerValuationNat pe : ℂ) ^ (-s) := by
  let n := xiGammaEulerValuationNat pe
  have hnNat : 0 < n := pow_pos pe.1.property.pos (pe.2 + 1)
  have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hbase : 0 ≤ Real.log (pe.1 : ℝ) / (n : ℝ) := by positivity
  have hdensity :
      Real.sqrt
          (Real.log (pe.1 : ℝ) / (n : ℝ) *
            Real.exp (-xiPrimeTwoEulerRadialDamping s * Real.log n)) =
        Real.sqrt (Real.log (pe.1 : ℝ) / (n : ℝ)) *
          Real.exp (-(s.re * Real.log n)) := by
    rw [show -xiPrimeTwoEulerRadialDamping s * Real.log n =
        2 * (-(s.re * Real.log n)) by
      unfold xiPrimeTwoEulerRadialDamping
      ring]
    rw [show Real.exp (2 * (-(s.re * Real.log n))) =
        Real.exp (-(s.re * Real.log n)) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    rw [Real.sqrt_mul hbase, Real.sqrt_sq (Real.exp_pos _).le]
  have hphase :
      -(((xiPrimeTwoEulerHeightPhase s * Real.log n / 2 : ℝ) : ℂ) * Complex.I) =
        (((-(s.im * Real.log n) : ℝ) : ℂ) * Complex.I) := by
    rw [← neg_mul]
    apply congrArg (fun z : ℂ => z * Complex.I)
    unfold xiPrimeTwoEulerHeightPhase
    push_cast
    ring
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log hn.le]
  have hexponent :
      ((Real.log n : ℝ) : ℂ) * (-s) =
        (-(s.re * Real.log n) : ℝ) +
          (((-(s.im * Real.log n) : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp <;> ring
  rw [xiGammaEulerHeightBoundaryFeature]
  change
    (Real.sqrt
        (Real.log (pe.1 : ℝ) / (n : ℝ) *
          Real.exp (-xiPrimeTwoEulerRadialDamping s * Real.log n)) : ℂ) *
        Complex.exp
          (-(((xiPrimeTwoEulerHeightPhase s * Real.log n / 2 : ℝ) : ℂ) *
            Complex.I)) = _
  rw [hdensity, hphase,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hnNat.ne'), hlog,
    hexponent, Complex.exp_add, ← Complex.ofReal_exp]
  push_cast
  ring

private theorem xiGammaEulerValuationNat_injective :
    Function.Injective xiGammaEulerValuationNat := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have hpq : (p : ℕ) = (q : ℕ) :=
    eq_of_prime_pow_eq p.property.prime q.property.prime (by omega) h
  have hpq' : p = q := Subtype.ext hpq
  subst q
  have hef : e + 1 = f + 1 :=
    (Nat.pow_right_injective p.property.two_le) h
  congr
  omega

/-- Injection of the prime-power cells into the ordinary Euler enumeration `n + 2`. -/
private def xiGammaEulerValuationEncoding (pe : Nat.Primes × ℕ) : ℕ :=
  xiGammaEulerValuationNat pe - 2

private theorem xiGammaEulerValuationEncoding_injective :
    Function.Injective xiGammaEulerValuationEncoding := by
  intro i j hij
  apply xiGammaEulerValuationNat_injective
  have hi : 2 ≤ xiGammaEulerValuationNat i :=
    i.1.property.two_le.trans (Nat.le_pow (by omega))
  have hj : 2 ≤ xiGammaEulerValuationNat j :=
    j.1.property.two_le.trans (Nat.le_pow (by omega))
  have h := congrArg (fun n : ℕ => n + 2) hij
  simpa [xiGammaEulerValuationEncoding, Nat.sub_add_cancel hi,
    Nat.sub_add_cancel hj] using h

/-- The complete radial Gamma--Euler section is square-summable on the positive-real half-plane. -/
theorem summable_normSq_xiGammaEulerRadialSection
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun pe : Nat.Primes × ℕ =>
      Complex.normSq
        (xiGammaEulerHeightBoundaryFeature
          (xiPrimeTwoEulerRadialDamping s)
          (xiPrimeTwoEulerHeightPhase s) pe)) := by
  have hsum :=
    (summable_infiniteVonMangoldtGammaRawAtom
      (x := 2 * s.re) (by positivity) 0).comp_injective
        xiGammaEulerValuationEncoding_injective
  apply hsum.congr
  intro pe
  have hpe : 2 ≤ xiGammaEulerValuationNat pe :=
    pe.1.property.two_le.trans (Nat.le_pow (by omega))
  have hcast :
      (((xiGammaEulerValuationNat pe - 2 : ℕ) : ℝ) + 2) =
        (xiGammaEulerValuationNat pe : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hpe
  rw [normSq_xiGammaEulerHeightBoundaryFeature]
  change infiniteVonMangoldtGammaRawAtom (2 * s.re) 0
      (xiGammaEulerValuationEncoding pe) = _
  unfold infiniteVonMangoldtGammaRawAtom xiGammaEulerValuationEncoding
  rw [Nat.sub_add_cancel hpe]
  simp only [xiPrimeTwoEulerRadialDamping, pow_zero, mul_one]
  rw [hcast]
  change ArithmeticFunction.vonMangoldt (pe.1 ^ (pe.2 + 1)) /
      (xiGammaEulerValuationNat pe : ℝ) * _ = _
  rw [vonMangoldt_prime_pow_succ_eq_log pe]

/-- Positive-real radial sections are genuine complex `ell^2` vectors. -/
theorem memℓp_xiGammaEulerRadialSection
    {s : ℂ} (hs : 0 < s.re) :
    Memℓp (fun pe : Nat.Primes × ℕ =>
      xiGammaEulerHeightBoundaryFeature
        (xiPrimeTwoEulerRadialDamping s)
        (xiPrimeTwoEulerHeightPhase s) pe) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    Complex.normSq_eq_norm_sq] using
      summable_normSq_xiGammaEulerRadialSection hs

/-- Complete square-root von Mangoldt radial section as an actual Hilbert vector. -/
def xiGammaEulerRadialSectionLp
    (s : ℂ) (hs : 0 < s.re) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  ⟨fun pe => xiGammaEulerHeightBoundaryFeature
      (xiPrimeTwoEulerRadialDamping s)
      (xiPrimeTwoEulerHeightPhase s) pe,
    memℓp_xiGammaEulerRadialSection hs⟩

@[simp] theorem xiGammaEulerRadialSectionLp_apply
    (s : ℂ) (hs : 0 < s.re) (pe : Nat.Primes × ℕ) :
    xiGammaEulerRadialSectionLp s hs pe =
      xiGammaEulerHeightBoundaryFeature
        (xiPrimeTwoEulerRadialDamping s)
        (xiPrimeTwoEulerHeightPhase s) pe := rfl

/-- Full Hilbert-space difference of the FE/Schwarz radial source sections. -/
def xiGammaEulerRadialReflectionSeamLp (rho : XiDivisorSupport) :
    lp (fun _ : Nat.Primes × ℕ => ℂ) 2 :=
  xiGammaEulerRadialSectionLp ((starRingEnd ℂ) (rho : ℂ)) (by
      simpa using (xi_divisor_support_re_mem_open_unit rho).1) -
    xiGammaEulerRadialSectionLp (1 - (rho : ℂ)) (by
      have h := xi_divisor_support_re_mem_open_unit rho
      simp only [Complex.sub_re, Complex.one_re]
      linarith)

@[simp] theorem xiGammaEulerRadialReflectionSeamLp_apply
    (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    xiGammaEulerRadialReflectionSeamLp rho pe =
      (xiGammaEulerHeightBoundaryFeature
        (xiPrimeTwoEulerRadialDamping ((starRingEnd ℂ) (rho : ℂ)))
        (xiPrimeTwoEulerHeightPhase ((starRingEnd ℂ) (rho : ℂ))) pe -
      xiGammaEulerHeightBoundaryFeature
        (xiPrimeTwoEulerRadialDamping (1 - (rho : ℂ)))
        (xiPrimeTwoEulerHeightPhase (1 - (rho : ℂ))) pe) := rfl

/-- Prime-two Euler boundary sampled at the radial/height calibration. -/
def xiPrimeTwoEulerRadialSample (s : ℂ) : ℂ :=
  xiGammaEulerHeightBoundaryFeature
    (xiPrimeTwoEulerRadialDamping s)
    (xiPrimeTwoEulerHeightPhase s)
    xiPrimeTwoEulerCell

/-- **Exact reciprocal-prime calibration.**  The Gamma-renormalized prime-two boundary coordinate
is the first reciprocal-prime character, including its canonical square-root source amplitude. -/
theorem xiPrimeTwoEulerRadialSample_eq_cpow (s : ℂ) :
    xiPrimeTwoEulerRadialSample s =
      (Real.sqrt (Real.log 2 / 2) : ℂ) * (2 : ℂ) ^ (-s) := by
  simpa [xiPrimeTwoEulerRadialSample, xiPrimeTwoEulerCell,
    xiGammaEulerValuationNat] using
      xiGammaEulerHeightBoundaryFeature_radial_eq_cpow s xiPrimeTwoEulerCell

/-- FE/Schwarz radial seam at an arbitrary prime-power Euler cell. -/
def xiGammaEulerRadialCellSeam
    (rho : ℂ) (pe : Nat.Primes × ℕ) : ℂ :=
  xiGammaEulerHeightBoundaryFeature
      (xiPrimeTwoEulerRadialDamping ((starRingEnd ℂ) rho))
      (xiPrimeTwoEulerHeightPhase ((starRingEnd ℂ) rho)) pe -
    xiGammaEulerHeightBoundaryFeature
      (xiPrimeTwoEulerRadialDamping (1 - rho))
      (xiPrimeTwoEulerHeightPhase (1 - rho)) pe

/-- **All-cell source-seam law.**  Every prime-power radial Gamma boundary seam is an explicit
nonzero cell normalization of the canonical seam at that prime-power scale. -/
theorem log_valuation_mul_xiGammaEulerRadialCellSeam_eq
    (rho : ℂ) (pe : Nat.Primes × ℕ) :
    (Real.log (xiGammaEulerValuationNat pe) : ℂ) *
        xiGammaEulerRadialCellSeam rho pe =
      (Real.sqrt
          (Real.log (pe.1 : ℝ) /
            (xiGammaEulerValuationNat pe : ℝ)) : ℂ) *
        orbitwiseNatPrimeSeamCharge (xiGammaEulerValuationNat pe) rho := by
  rw [xiGammaEulerRadialCellSeam,
    xiGammaEulerHeightBoundaryFeature_radial_eq_cpow,
    xiGammaEulerHeightBoundaryFeature_radial_eq_cpow,
    orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge]
  push_cast
  ring

/-- The radial endpoint samples have the same height phase. -/
theorem xiPrimeTwoEulerHeightPhase_conj_eq_one_sub (rho : ℂ) :
    xiPrimeTwoEulerHeightPhase ((starRingEnd ℂ) rho) =
      xiPrimeTwoEulerHeightPhase (1 - rho) := by
  simp [xiPrimeTwoEulerHeightPhase]

/-- Both radial endpoint dampings are positive in the open critical strip. -/
theorem xiPrimeTwoEulerRadialDamping_endpoints_pos
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    0 < xiPrimeTwoEulerRadialDamping ((starRingEnd ℂ) rho) ∧
      0 < xiPrimeTwoEulerRadialDamping (1 - rho) := by
  simp only [xiPrimeTwoEulerRadialDamping, Complex.conj_re,
    Complex.sub_re, Complex.one_re]
  constructor <;> nlinarith

/-- Radial-source difference of the FE/Schwarz endpoint samples. -/
def xiPrimeTwoEulerRadialSeam (rho : ℂ) : ℂ :=
  xiGammaEulerRadialCellSeam rho xiPrimeTwoEulerCell

/-- **Exact first-prime source weld.**  After the fixed nonzero normalization, the radial Euler
boundary seam is literally the existing first-prime von Mangoldt seam charge. -/
theorem log_mul_xiPrimeTwoEulerRadialSeam_eq_sqrt_mul_firstPrimeSeamCharge
    (rho : ℂ) :
    (Real.log 2 : ℂ) * xiPrimeTwoEulerRadialSeam rho =
      (Real.sqrt (Real.log 2 / 2) : ℂ) *
        orbitwiseFirstPrimeSeamCharge rho := by
  rw [xiPrimeTwoEulerRadialSeam, xiGammaEulerRadialCellSeam,
    xiGammaEulerHeightBoundaryFeature_radial_eq_cpow,
    xiGammaEulerHeightBoundaryFeature_radial_eq_cpow,
    orbitwiseFirstPrimeSeamCharge]
  simp only [xiPrimeTwoEulerCell, xiGammaEulerValuationNat, Nat.zero_add,
    pow_one, Nat.cast_ofNat]
  ring

/-- The full square-root von Mangoldt radial source sections agree exactly on the critical line.
The reverse implication needs only their prime-two ground coordinate. -/
theorem xiGammaEulerRadialReflectionSeamLp_eq_zero_iff_re_eq_half
    (rho : XiDivisorSupport) :
    xiGammaEulerRadialReflectionSeamLp rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hcell := congrArg
      (fun v : lp (fun _ : Nat.Primes × ℕ => ℂ) 2 =>
        v xiPrimeTwoEulerCell) hzero
    have hseam : xiPrimeTwoEulerRadialSeam (rho : ℂ) = 0 := by
      simpa [xiPrimeTwoEulerRadialSeam, xiGammaEulerRadialCellSeam] using hcell
    have hscale :=
      log_mul_xiPrimeTwoEulerRadialSeam_eq_sqrt_mul_firstPrimeSeamCharge
        (rho : ℂ)
    rw [hseam, mul_zero] at hscale
    have hsqrt : (Real.sqrt (Real.log 2 / 2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2
        (div_pos (Real.log_pos (by norm_num)) (by norm_num))).ne'
    have hcharge : orbitwiseFirstPrimeSeamCharge (rho : ℂ) = 0 :=
      (mul_eq_zero.mp hscale.symm).resolve_left hsqrt
    exact (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (rho : ℂ)).mp hcharge
  · intro hre
    have horbit : (starRingEnd ℂ) (rho : ℂ) = 1 - (rho : ℂ) := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im]
        ring
    ext pe
    simp [xiGammaEulerRadialReflectionSeamLp, horbit]

/-- The radial Euler seam and the first-prime source seam have exactly the same zero fibre at
every complex point, with no strip or divisor hypothesis. -/
theorem xiPrimeTwoEulerRadialSeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero
    (rho : ℂ) :
    xiPrimeTwoEulerRadialSeam rho = 0 ↔
      orbitwiseFirstPrimeSeamCharge rho = 0 := by
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hsqrt : (Real.sqrt (Real.log 2 / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2
      (div_pos (Real.log_pos (by norm_num)) (by norm_num))).ne'
  constructor
  · intro hseam
    have h :=
      log_mul_xiPrimeTwoEulerRadialSeam_eq_sqrt_mul_firstPrimeSeamCharge rho
    rw [hseam, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hsqrt
  · intro hcharge
    have h :=
      log_mul_xiPrimeTwoEulerRadialSeam_eq_sqrt_mul_firstPrimeSeamCharge rho
    rw [hcharge, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hlog

/-- Every Xi-indexed full prime-power radial Gamma--Euler section is reflection-fixed. -/
def XiGammaEulerRadialReflectionSeamsVanish : Prop :=
  ∀ rho : XiDivisorSupport,
    xiGammaEulerRadialReflectionSeamLp rho = 0

/-- Every Xi-indexed radial prime-two Euler boundary seam vanishes. -/
def XiPrimeTwoEulerRadialSeamsVanish : Prop :=
  ∀ rho : XiDivisorSupport,
    xiPrimeTwoEulerRadialSeam (rho : ℂ) = 0

/-- Global radial Euler seam vanishing is exactly global first-prime seam vanishing. -/
theorem xiPrimeTwoEulerRadialSeamsVanish_iff_firstPrimeSeamChargesVanish :
    XiPrimeTwoEulerRadialSeamsVanish ↔ XiFirstPrimeSeamChargesVanish := by
  unfold XiPrimeTwoEulerRadialSeamsVanish XiFirstPrimeSeamChargesVanish
  exact forall_congr' fun rho ↦
    xiPrimeTwoEulerRadialSeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero (rho : ℂ)

/-- Full Hilbert-section reflection is equivalent to the single prime-two radial coordinate. -/
theorem xiGammaEulerRadialReflectionSeamsVanish_iff_primeTwoRadialSeamsVanish :
    XiGammaEulerRadialReflectionSeamsVanish ↔
      XiPrimeTwoEulerRadialSeamsVanish := by
  unfold XiGammaEulerRadialReflectionSeamsVanish
    XiPrimeTwoEulerRadialSeamsVanish
  apply forall_congr'
  intro rho
  exact (xiGammaEulerRadialReflectionSeamLp_eq_zero_iff_re_eq_half rho).trans
    ((xiPrimeTwoEulerRadialSeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero
        (rho : ℂ)).trans
      (orbitwiseFirstPrimeSeamCharge_eq_zero_iff (rho : ℂ))).symm

/-- The radial prime-two Euler boundary equality is itself an exact right-side RH endpoint. -/
theorem xiPrimeTwoEulerRadialSeamsVanish_iff_riemannHypothesis :
    XiPrimeTwoEulerRadialSeamsVanish ↔ RiemannHypothesis :=
  xiPrimeTwoEulerRadialSeamsVanish_iff_firstPrimeSeamChargesVanish.trans
    (xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero.trans
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.symm)

/-- The full all-prime/all-valuation radial source-section reflection law is exactly RH. -/
theorem xiGammaEulerRadialReflectionSeamsVanish_iff_riemannHypothesis :
    XiGammaEulerRadialReflectionSeamsVanish ↔ RiemannHypothesis :=
  xiGammaEulerRadialReflectionSeamsVanish_iff_primeTwoRadialSeamsVanish.trans
    xiPrimeTwoEulerRadialSeamsVanish_iff_riemannHypothesis

/-- Difference of the calibrated Euler samples at the FE/Schwarz endpoints. -/
def xiHurwitzPrimeTwoEulerBoundarySeam (rho : ℂ) : ℂ :=
  xiHurwitzPrimeTwoEulerBoundarySample ((starRingEnd ℂ) rho) -
    xiHurwitzPrimeTwoEulerBoundarySample (1 - rho)

/-- The Euler boundary seam is the anti-conjugation defect of Hurwitz monodromy. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeam_eq (rho : ℂ) :
    xiHurwitzPrimeTwoEulerBoundarySeam rho =
      (Real.sqrt (Real.log 2 / 2) : ℂ) *
        (monoScalar ((starRingEnd ℂ) rho) -
          (starRingEnd ℂ) (monoScalar ((starRingEnd ℂ) rho))) := by
  have hreflect :
      monoScalar (1 - rho) =
        (starRingEnd ℂ) (monoScalar ((starRingEnd ℂ) rho)) := by
    simpa using monoScalar_feReflection ((starRingEnd ℂ) rho)
  rw [xiHurwitzPrimeTwoEulerBoundarySeam,
    xiHurwitzPrimeTwoEulerBoundarySample_eq_monoScalar,
    xiHurwitzPrimeTwoEulerBoundarySample_eq_monoScalar, hreflect]
  ring

/-- In the open critical strip the calibrated Euler boundary seam vanishes exactly on the
critical line. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeam_eq_zero_iff
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    xiHurwitzPrimeTwoEulerBoundarySeam rho = 0 ↔ rho.re = 1 / 2 := by
  rw [xiHurwitzPrimeTwoEulerBoundarySeam_eq]
  have hc : (Real.sqrt (Real.log 2 / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2
      (div_pos (Real.log_pos (by norm_num)) (by norm_num))).ne'
  rw [mul_eq_zero]
  simp only [hc, false_or, sub_eq_zero]
  rw [eq_comm]
  have hstrip' :
      0 < ((starRingEnd ℂ) rho).re ∧ ((starRingEnd ℂ) rho).re < 1 := by
    simpa using hstrip
  simpa using openCriticalStrip_monoScalar_conj_fixed_iff hstrip'

/-- Pointwise the new Euler boundary seam and the existing first-prime seam have the same zero
fibre, without invoking RH. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero
    (rho : XiDivisorSupport) :
    xiHurwitzPrimeTwoEulerBoundarySeam (rho : ℂ) = 0 ↔
      orbitwiseFirstPrimeSeamCharge (rho : ℂ) = 0 := by
  rw [xiHurwitzPrimeTwoEulerBoundarySeam_eq_zero_iff
      (xi_divisor_support_re_mem_open_unit rho),
    orbitwiseFirstPrimeSeamCharge_eq_zero_iff]

private theorem normSq_sub_conj (z : ℂ) :
    Complex.normSq (z - (starRingEnd ℂ) z) = 4 * z.im ^ 2 := by
  rw [Complex.normSq_apply]
  simp
  ring

/-- **Exact Euler/Hurwitz seam-energy law.**  The actual prime-two Euler boundary seam energy is a
strictly positive scalar multiple of the existing Xi--Hurwitz orientation defect. -/
theorem normSq_xiHurwitzPrimeTwoEulerBoundarySeam (rho : XiDivisorSupport) :
    Complex.normSq (xiHurwitzPrimeTwoEulerBoundarySeam (rho : ℂ)) =
      2 * Real.log 2 * Real.exp (-4 * Real.pi * (rho : ℂ).im) *
        xiHurwitzOrientationDefect rho := by
  rw [xiHurwitzPrimeTwoEulerBoundarySeam_eq, Complex.normSq_mul,
    Complex.normSq_ofReal, normSq_sub_conj,
    xiHurwitzOrientationDefect_eq_sin_sq]
  have hsqrt :
      Real.sqrt (Real.log 2 / 2) * Real.sqrt (Real.log 2 / 2) =
        Real.log 2 / 2 := by
    exact Real.mul_self_sqrt (by positivity)
  rw [hsqrt]
  have hre :
      (-(2 * (Real.pi : ℂ) * Complex.I *
          ((starRingEnd ℂ) (rho : ℂ)))).re =
        -2 * Real.pi * (rho : ℂ).im := by
    simp
  have him :
      (-(2 * (Real.pi : ℂ) * Complex.I *
          ((starRingEnd ℂ) (rho : ℂ)))).im =
        -(2 * Real.pi * (rho : ℂ).re) := by
    simp
  rw [monoScalar, Complex.exp_im, hre, him, Real.sin_neg]
  have hexp :
      Real.exp (-2 * Real.pi * (rho : ℂ).im) ^ 2 =
        Real.exp (-4 * Real.pi * (rho : ℂ).im) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hexp]
  ring

/-- Every Xi-indexed calibrated prime-two Euler boundary seam vanishes. -/
def XiHurwitzPrimeTwoEulerBoundarySeamsVanish : Prop :=
  ∀ rho : XiDivisorSupport,
    xiHurwitzPrimeTwoEulerBoundarySeam (rho : ℂ) = 0

/-- Global calibrated Euler seam vanishing is exactly global first-prime seam vanishing. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_firstPrimeSeamChargesVanish :
    XiHurwitzPrimeTwoEulerBoundarySeamsVanish ↔ XiFirstPrimeSeamChargesVanish := by
  unfold XiHurwitzPrimeTwoEulerBoundarySeamsVanish XiFirstPrimeSeamChargesVanish
  exact forall_congr'
    xiHurwitzPrimeTwoEulerBoundarySeam_eq_zero_iff_firstPrimeSeamCharge_eq_zero

/-- Global calibrated Euler seam vanishing is exactly zero Hurwitz orientation energy. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_orientationEnergy_zero :
    XiHurwitzPrimeTwoEulerBoundarySeamsVanish ↔
      xiHurwitzOrientationEnergy = 0 :=
  xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_firstPrimeSeamChargesVanish.trans
    xiFirstPrimeSeamChargesVanish_iff_orientationEnergy_zero

/-- The newly exposed prime-two Euler boundary seam is a right-side RH endpoint.  The remaining
open source problem is to force these two calibrated samples to agree. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_riemannHypothesis :
    XiHurwitzPrimeTwoEulerBoundarySeamsVanish ↔ RiemannHypothesis :=
  xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_orientationEnergy_zero.trans
    riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.symm

/-- The radial Gamma--Euler source seam and the fixed reciprocal-Krylov adjoint seam are the same
global zero-fibre obstruction, without routing the proof through RH. -/
theorem xiPrimeTwoEulerRadialSeamsVanish_iff_reciprocalSquareFixedCauchyRealKrylovSeamSaturation :
    XiPrimeTwoEulerRadialSeamsVanish ↔
      XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation :=
  xiPrimeTwoEulerRadialSeamsVanish_iff_firstPrimeSeamChargesVanish.trans
    xiReciprocalSquareFixedCauchyRealKrylovSeamSaturation_iff_firstPrimeSeamChargesVanish.symm

/-- Full prime-power radial Gamma--Euler reflection is directly equivalent to fixed reciprocal
real-Krylov seam saturation. -/
theorem xiGammaEulerRadialReflectionSeamsVanish_iff_reciprocalSquareFixedCauchyRealKrylovSeamSaturation :
    XiGammaEulerRadialReflectionSeamsVanish ↔
      XiReciprocalSquareFixedCauchyRealKrylovSeamSaturation :=
  xiGammaEulerRadialReflectionSeamsVanish_iff_primeTwoRadialSeamsVanish.trans
    xiPrimeTwoEulerRadialSeamsVanish_iff_reciprocalSquareFixedCauchyRealKrylovSeamSaturation

/-- The common-damping monodromy seam and common-phase radial seam are dual exact Euler boundary
coordinates with the same global vanishing law. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_radialSeamsVanish :
    XiHurwitzPrimeTwoEulerBoundarySeamsVanish ↔
      XiPrimeTwoEulerRadialSeamsVanish :=
  xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_firstPrimeSeamChargesVanish.trans
    xiPrimeTwoEulerRadialSeamsVanish_iff_firstPrimeSeamChargesVanish.symm

/-- Common-damping Hurwitz monodromy reflection and the complete common-phase radial source
reflection are dual exact Gamma--Euler forms of the same global obstruction. -/
theorem xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_fullRadialReflectionSeamsVanish :
    XiHurwitzPrimeTwoEulerBoundarySeamsVanish ↔
      XiGammaEulerRadialReflectionSeamsVanish :=
  xiHurwitzPrimeTwoEulerBoundarySeamsVanish_iff_radialSeamsVanish.trans
    xiGammaEulerRadialReflectionSeamsVanish_iff_primeTwoRadialSeamsVanish.symm

end

end RHTower
