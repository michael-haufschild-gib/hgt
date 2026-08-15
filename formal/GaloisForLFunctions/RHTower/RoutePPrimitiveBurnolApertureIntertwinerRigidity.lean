import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolConstantChannelLandingNoGo

/-!
# Route P aperture-intertwiner spectral rigidity

The P-G187 weighted radial shift diagonalizes every primitive and Xi conormal
column.  This file tests the entire class of linear, possibly nonlocal landing
operators that commute with one positive aperture step.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Positive radial aperture ray. -/
abbrev RoutePBurnolPositiveRay := Set.Ioi (0 : ℝ)

/-- P-G187 weighted aperture shift as a linear endomorphism of all functions on
the positive ray. -/
def routePBurnolPositiveShift (c : ℝ) (hc : 0 ≤ c) :
    Module.End ℂ (RoutePBurnolPositiveRay → ℂ) where
  toFun f L :=
    (((L.1 / (L.1 + c) : ℝ) : ℂ)) *
      f ⟨L.1 + c, add_pos_of_pos_of_nonneg L.2 hc⟩
  map_add' f g := by
    funext L
    simp only [Pi.add_apply]
    ring
  map_smul' z f := by
    funext L
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- Primitive P-G186 column restricted to the positive ray. -/
def routePPrimitiveBurnolPositiveFeature
    (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    RoutePBurnolPositiveRay → ℂ :=
  fun L => routePPrimitiveBurnolWindowFeature pe kappa L.1

/-- Actual strict-right Xi conormal restricted to the positive ray. -/
def routePStrictRightBurnolPositiveFeature
    (q : XiRightZeroCopy) : RoutePBurnolPositiveRay → ℂ :=
  fun L => routePXiBaseConormalResidueFeature (q.1.1 : ℂ) L.1

/-- Primitive columns are eigenvectors of every positive weighted aperture
shift, with exact primitive complex log frequency. -/
theorem routePBurnolPositiveShift_primitiveFeature
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    routePBurnolPositiveShift c hc
        (routePPrimitiveBurnolPositiveFeature pe kappa) =
      Complex.exp (-((c : ℂ) *
        ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)))) •
        routePPrimitiveBurnolPositiveFeature pe kappa := by
  funext L
  simpa [routePBurnolPositiveShift,
    routePPrimitiveBurnolPositiveFeature, routePBurnolForwardDampingShift,
    smul_eq_mul] using
      routePBurnolForwardDampingShift_primitiveFeature hc L.2 pe kappa

/-- Strict-right Xi conormals are eigenvectors of the same shift, at their
centered Xi spectral rate. -/
theorem routePBurnolPositiveShift_strictRightFeature
    {c : ℝ} (hc : 0 ≤ c) (q : XiRightZeroCopy) :
    routePBurnolPositiveShift c hc
        (routePStrictRightBurnolPositiveFeature q) =
      Complex.exp (-(((q.1.1 : ℂ) - 1 / 2) * (c : ℂ))) •
        routePStrictRightBurnolPositiveFeature q := by
  funext L
  have h := routePBurnolForwardDampingShift_windowFeature
    hc L.2 (q.1.1 : ℂ)
  simp only [xiWardCubicBurnolWindowConormalFeature_eq] at h
  simpa [routePBurnolPositiveShift,
    routePStrictRightBurnolPositiveFeature, routePBurnolForwardDampingShift,
    smul_eq_mul] using h

/-- One nonzero positive aperture step already separates the primitive and
strict-right Xi eigencharacters. -/
theorem routePBurnol_primitiveEigenvalue_ne_strictRightEigenvalue
    {c : ℝ} (hc : 0 < c) (pe : Nat.Primes × ℕ) (kappa : ℝ)
    (q : XiRightZeroCopy) :
    Complex.exp (-((c : ℂ) *
        ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)))) ≠
      Complex.exp (-(((q.1.1 : ℂ) - 1 / 2) * (c : ℂ))) := by
  intro heq
  have hnorm := congrArg norm heq
  rw [Complex.norm_exp, Complex.norm_exp] at hnorm
  have harg := Real.exp_injective hnorm
  have hcenter :
      ((q.1.1 : ℂ) - 1 / 2).re = (xiRightCenteredZero q).re := by
    rw [← xiRightCenteredZero_eq_support_sub_half]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im,
    zero_mul, mul_zero, sub_zero] at harg
  rw [hcenter] at harg
  have hsourceRe :
      ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) +
        I * (kappa : ℂ)).re =
        xiGammaEulerPrimitiveLogFrequency pe := by simp
  rw [hsourceRe] at harg
  have hgap := xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency pe q
  nlinarith

/-- Every linear operator commuting with one positive P-G187 aperture step
preserves the conormal eigencharacter.  This requires no boundedness or
locality assumption. -/
theorem routePBurnolApertureIntertwiner_preserves_eigenvalue
    {c : ℝ} (hc : 0 < c)
    (A : Module.End ℂ (RoutePBurnolPositiveRay → ℂ))
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy)
    (hcomm : ∀ f,
      A (routePBurnolPositiveShift c hc.le f) =
        routePBurnolPositiveShift c hc.le (A f))
    (hmap : A (routePPrimitiveBurnolPositiveFeature pe kappa) =
      routePStrictRightBurnolPositiveFeature q) :
    Complex.exp (-((c : ℂ) *
        ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)))) =
      Complex.exp (-(((q.1.1 : ℂ) - 1 / 2) * (c : ℂ))) := by
  let source := routePPrimitiveBurnolPositiveFeature pe kappa
  let target := routePStrictRightBurnolPositiveFeature q
  let muSource := Complex.exp (-((c : ℂ) *
    ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ))))
  let muTarget := Complex.exp (-(((q.1.1 : ℂ) - 1 / 2) * (c : ℂ)))
  have hsource :
      routePBurnolPositiveShift c hc.le source = muSource • source := by
    simpa [source, muSource] using
      routePBurnolPositiveShift_primitiveFeature hc.le pe kappa
  have htarget :
      routePBurnolPositiveShift c hc.le target = muTarget • target := by
    simpa [target, muTarget] using
      routePBurnolPositiveShift_strictRightFeature hc.le q
  have heigen : muSource • target = muTarget • target := by
    calc
      muSource • target = muSource • A source := by rw [hmap]
      _ = A (muSource • source) := by rw [map_smul]
      _ = A (routePBurnolPositiveShift c hc.le source) := by rw [hsource]
      _ = routePBurnolPositiveShift c hc.le (A source) := hcomm source
      _ = routePBurnolPositiveShift c hc.le target := by rw [hmap]
      _ = muTarget • target := htarget
  let L : RoutePBurnolPositiveRay := ⟨1, by norm_num⟩
  have hpoint := congrFun heigen L
  have htargetNe : target L ≠ 0 := by
    dsimp [target, routePStrictRightBurnolPositiveFeature, L,
      routePXiBaseConormalResidueFeature]
    exact mul_ne_zero one_ne_zero (Complex.exp_ne_zero _)
  have hmu : muSource = muTarget := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (mul_right_cancel₀ htargetNe hpoint)
  simpa [muSource, muTarget] using hmu

/-- Exact anomaly law for every proposed landing: changing conormal spectral
rate forces a Burnol-shift commutator whose value on the source column is the
eigencharacter gap times the target column. -/
theorem routePBurnolLanding_commutator_eq_eigenvalueGap
    {c : ℝ} (hc : 0 < c)
    (A : Module.End ℂ (RoutePBurnolPositiveRay → ℂ))
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy)
    (hmap : A (routePPrimitiveBurnolPositiveFeature pe kappa) =
      routePStrictRightBurnolPositiveFeature q) :
    A (routePBurnolPositiveShift c hc.le
        (routePPrimitiveBurnolPositiveFeature pe kappa)) -
        routePBurnolPositiveShift c hc.le
          (A (routePPrimitiveBurnolPositiveFeature pe kappa)) =
      (Complex.exp (-((c : ℂ) *
          ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)))) -
        Complex.exp (-(((q.1.1 : ℂ) - 1 / 2) * (c : ℂ)))) •
          routePStrictRightBurnolPositiveFeature q := by
  rw [routePBurnolPositiveShift_primitiveFeature hc.le pe kappa,
    map_smul, hmap,
    routePBurnolPositiveShift_strictRightFeature hc.le q]
  ext L
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The forced landing anomaly is nonzero for every actual strict-right Xi
column.  Hence the missing polar--Gamma producer must carry a genuine source
commutator, not merely fail covariance abstractly. -/
theorem routePBurnolLanding_commutator_ne_zero
    {c : ℝ} (hc : 0 < c)
    (A : Module.End ℂ (RoutePBurnolPositiveRay → ℂ))
    (pe : Nat.Primes × ℕ) (kappa : ℝ) (q : XiRightZeroCopy)
    (hmap : A (routePPrimitiveBurnolPositiveFeature pe kappa) =
      routePStrictRightBurnolPositiveFeature q) :
    A (routePBurnolPositiveShift c hc.le
        (routePPrimitiveBurnolPositiveFeature pe kappa)) -
        routePBurnolPositiveShift c hc.le
          (A (routePPrimitiveBurnolPositiveFeature pe kappa)) ≠ 0 := by
  rw [routePBurnolLanding_commutator_eq_eigenvalueGap hc A pe kappa q hmap]
  intro hzero
  let L : RoutePBurnolPositiveRay := ⟨1, by norm_num⟩
  have hpoint := congrFun hzero L
  have hgap :
      Complex.exp (-((c : ℂ) *
          ((xiGammaEulerPrimitiveLogFrequency pe : ℂ) + I * (kappa : ℂ)))) -
        Complex.exp (-(((q.1.1 : ℂ) - 1 / 2) * (c : ℂ))) ≠ 0 :=
    sub_ne_zero.mpr
      (routePBurnol_primitiveEigenvalue_ne_strictRightEigenvalue
        hc pe kappa q)
  have htarget : routePStrictRightBurnolPositiveFeature q L ≠ 0 := by
    dsimp [routePStrictRightBurnolPositiveFeature, L,
      routePXiBaseConormalResidueFeature]
    exact mul_ne_zero one_ne_zero (Complex.exp_ne_zero _)
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hpoint
  exact mul_ne_zero hgap htarget hpoint

/-- No linear aperture-covariant operator, even unbounded and nonlocal, can
land a primitive P-G186 column on an actual strict-right Xi conormal. -/
theorem not_exists_routePBurnolApertureIntertwiner_eq_strictRightConormal
    {c : ℝ} (hc : 0 < c) (pe : Nat.Primes × ℕ) (kappa : ℝ)
    (q : XiRightZeroCopy) :
    ¬ ∃ A : Module.End ℂ (RoutePBurnolPositiveRay → ℂ),
      (∀ f,
        A (routePBurnolPositiveShift c hc.le f) =
          routePBurnolPositiveShift c hc.le (A f)) ∧
      A (routePPrimitiveBurnolPositiveFeature pe kappa) =
        routePStrictRightBurnolPositiveFeature q := by
  rintro ⟨A, hcomm, hmap⟩
  exact routePBurnol_primitiveEigenvalue_ne_strictRightEigenvalue
    hc pe kappa q
    (routePBurnolApertureIntertwiner_preserves_eigenvalue
      hc A pe kappa q hcomm hmap)

end

end RHTower
