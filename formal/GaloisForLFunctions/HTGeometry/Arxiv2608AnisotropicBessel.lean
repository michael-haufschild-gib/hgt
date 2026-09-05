import GaloisForLFunctions.RHTower.BesselJZeroODE
import GaloisForLFunctions.RHTower.BesselJOneRecurrence
import GaloisForLFunctions.RHTower.ImotoBesselActivationJets

/-!
# Anisotropic Bessel propagation from arXiv:2608.18478

This module formalizes the parameter identities and the isotropic `J₀` radial mode behind equations
(7)--(13) and (29)--(46) of Escobar--Linares--Plácido-Flores.  The physical interval `-1 < λ < 1`
is part of the parameter type, so every theorem is closed and carries no analytic side hypothesis.

The branch rule has a useful invariant form: the selected Bessel order is exactly `-σ`.  Hence the
radial prefactor and the small-argument Bessel power cancel for either sign of the anisotropy.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Physical anisotropy range used in arXiv:2608.18478. -/
abbrev EscobarAnisotropy := Set.Ioo (-1 : ℝ) 1

/-- Positive radial coordinate, used to absorb the regular-singular endpoint condition. -/
abbrev PositiveRadius := Set.Ioi (0 : ℝ)

/-- Equation (10): radial conjugation exponent. -/
def escobarSigma (lam : EscobarAnisotropy) : ℝ :=
  (lam : ℝ) / (2 * ((lam : ℝ) - 1))

/-- Equation (8): nonnegative effective Bessel order in the axisymmetric sector. -/
def escobarAxisymmetricOrder (lam : EscobarAnisotropy) : ℝ :=
  |(lam : ℝ)| / (2 * (1 - (lam : ℝ)))

/-- Equation (7): effective Bessel order of azimuthal Fourier mode `m`. -/
def escobarAzimuthalOrder (lam : EscobarAnisotropy) (m : ℤ) : ℝ :=
  Real.sqrt (4 * (m : ℝ) ^ 2 * (1 - (lam : ℝ)) + (lam : ℝ) ^ 2) /
    (2 * (1 - (lam : ℝ)))

/-- Equation (11): signed order of the branch compatible with a bright axis. -/
def escobarBranchOrder (lam : EscobarAnisotropy) : ℝ :=
  if 0 ≤ (lam : ℝ) then escobarAxisymmetricOrder lam else -escobarAxisymmetricOrder lam

/-- Equation (30), recorded as a squared dispersion law to avoid an artificial square-root choice. -/
def escobarBetaSq (lam : EscobarAnisotropy) (Ω η : ℝ) : ℝ :=
  Ω ^ 2 - (1 - (lam : ℝ)) * η ^ 2

/-- The physical anisotropy never changes the sign of the radial kinetic coefficient. -/
theorem escobar_one_sub_anisotropy_pos (lam : EscobarAnisotropy) :
    0 < 1 - (lam : ℝ) := by
  exact sub_pos.mpr lam.property.2

/-- Effective axisymmetric order is nonnegative. -/
theorem escobarAxisymmetricOrder_nonneg (lam : EscobarAnisotropy) :
    0 ≤ escobarAxisymmetricOrder lam := by
  exact div_nonneg (abs_nonneg _)
    (mul_nonneg (by norm_num) (escobar_one_sub_anisotropy_pos lam).le)

theorem escobarAzimuthalOrder_nonneg (lam : EscobarAnisotropy) (m : ℤ) :
    0 ≤ escobarAzimuthalOrder lam m := by
  exact div_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (escobar_one_sub_anisotropy_pos lam).le)

@[simp] theorem escobarAzimuthalOrder_neg (lam : EscobarAnisotropy) (m : ℤ) :
    escobarAzimuthalOrder lam (-m) = escobarAzimuthalOrder lam m := by
  simp [escobarAzimuthalOrder]

/-- The axisymmetric specialization of equation (7) is the paper's `nu_0`. -/
@[simp] theorem escobarAzimuthalOrder_zero (lam : EscobarAnisotropy) :
    escobarAzimuthalOrder lam 0 = escobarAxisymmetricOrder lam := by
  simp [escobarAzimuthalOrder, escobarAxisymmetricOrder]
  rw [Real.sqrt_sq_eq_abs]

/-- Exact square decomposition of every azimuthal order into radial anisotropy and angular parts. -/
theorem escobarAzimuthalOrder_sq_decomposition
    (lam : EscobarAnisotropy) (m : ℤ) :
    escobarAzimuthalOrder lam m ^ 2 =
      (m : ℝ) ^ 2 / (1 - (lam : ℝ)) + escobarAxisymmetricOrder lam ^ 2 := by
  have hL : 0 < 1 - (lam : ℝ) := escobar_one_sub_anisotropy_pos lam
  have hrad : 0 ≤ 4 * (m : ℝ) ^ 2 * (1 - (lam : ℝ)) + (lam : ℝ) ^ 2 := by
    positivity
  rw [escobarAzimuthalOrder, div_pow, Real.sq_sqrt hrad,
    escobarAxisymmetricOrder, div_pow, sq_abs]
  field_simp [ne_of_gt hL]
  ring

/-- Angular momentum can only increase the effective Bessel order. -/
theorem escobarAxisymmetricOrder_le_azimuthalOrder
    (lam : EscobarAnisotropy) (m : ℤ) :
    escobarAxisymmetricOrder lam ≤ escobarAzimuthalOrder lam m := by
  have hsq := escobarAzimuthalOrder_sq_decomposition lam m
  have hextra : 0 ≤ (m : ℝ) ^ 2 / (1 - (lam : ℝ)) :=
    div_nonneg (sq_nonneg _) (escobar_one_sub_anisotropy_pos lam).le
  have hleft := escobarAxisymmetricOrder_nonneg lam
  have hright := escobarAzimuthalOrder_nonneg lam m
  nlinarith

/-! ## Integer-order anisotropies -/

/-- Physical anisotropy `lambda_n = 2n/(2n+1)` whose axisymmetric order is exactly `n`. -/
def escobarIntegerAnisotropy (n : ℕ) : EscobarAnisotropy :=
  ⟨2 * (n : ℝ) / (2 * (n : ℝ) + 1), by
    have hden : 0 < 2 * (n : ℝ) + 1 := by positivity
    constructor
    · have hnonneg : 0 ≤ 2 * (n : ℝ) / (2 * (n : ℝ) + 1) := by positivity
      linarith
    · rw [div_lt_one hden]
      linarith⟩

@[simp] theorem escobarSigma_integerAnisotropy (n : ℕ) :
    escobarSigma (escobarIntegerAnisotropy n) = -(n : ℝ) := by
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  simp only [escobarSigma, escobarIntegerAnisotropy]
  field_simp [hden]
  ring

@[simp] theorem escobarAxisymmetricOrder_integerAnisotropy (n : ℕ) :
    escobarAxisymmetricOrder (escobarIntegerAnisotropy n) = (n : ℝ) := by
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hnonneg : 0 ≤ 2 * (n : ℝ) / (2 * (n : ℝ) + 1) := by positivity
  simp only [escobarAxisymmetricOrder, escobarIntegerAnisotropy, abs_of_nonneg hnonneg]
  field_simp [hden]
  ring

@[simp] theorem escobarBranchOrder_integerAnisotropy (n : ℕ) :
    escobarBranchOrder (escobarIntegerAnisotropy n) = (n : ℝ) := by
  have hnonneg : 0 ≤ (escobarIntegerAnisotropy n : ℝ) := by
    change 0 ≤ 2 * (n : ℝ) / (2 * (n : ℝ) + 1)
    positivity
  simp [escobarBranchOrder, hnonneg]

/-- The paper's sign-dependent branch is uniformly the order `-σ`. -/
theorem escobarBranchOrder_eq_neg_sigma (lam : EscobarAnisotropy) :
    escobarBranchOrder lam = -escobarSigma lam := by
  have hden : 1 - (lam : ℝ) ≠ 0 := ne_of_gt (escobar_one_sub_anisotropy_pos lam)
  have hden' : (lam : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt lam.property.2)
  rw [escobarBranchOrder]
  split_ifs with hnonneg
  · rw [escobarAxisymmetricOrder, abs_of_nonneg hnonneg, escobarSigma]
    field_simp [hden, hden']
    ring
  · have hneg : (lam : ℝ) < 0 := lt_of_not_ge hnonneg
    rw [escobarAxisymmetricOrder, abs_of_neg hneg, escobarSigma]
    field_simp [hden, hden']
    ring

/-- Equations (35)--(36): selected small-axis exponent vanishes for every physical `λ`. -/
theorem escobar_branch_exponent_eq_zero (lam : EscobarAnisotropy) :
    escobarSigma lam + escobarBranchOrder lam = 0 := by
  rw [escobarBranchOrder_eq_neg_sigma]
  ring

/-- Equation (45): the two presentations of the inverse-Hankel input weight agree. -/
theorem escobar_input_weight_exponent_eq (lam : EscobarAnisotropy) :
    1 - escobarSigma lam = escobarSigma lam + 1 / (1 - (lam : ℝ)) := by
  have hden : 1 - (lam : ℝ) ≠ 0 := ne_of_gt (escobar_one_sub_anisotropy_pos lam)
  have hden' : (lam : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt lam.property.2)
  rw [escobarSigma]
  field_simp [hden, hden']
  ring

/-- Equation (30): dispersion reconstruction after moving the radial term to the left. -/
theorem escobarBetaSq_add_radial (lam : EscobarAnisotropy) (Ω η : ℝ) :
    escobarBetaSq lam Ω η + (1 - (lam : ℝ)) * η ^ 2 = Ω ^ 2 := by
  simp [escobarBetaSq]

/-- Radial separated-equation residual from equation (29), with `β²` kept as one variable. -/
def escobarRadialResidual
    (lam : ℝ) (Ω betaSq r value first second : ℝ) : ℝ :=
  (1 - lam) * second + first / r + (Ω ^ 2 - betaSq) * value

/-- Squared order in the sign-independent form used by the transformed radial equation. -/
theorem escobarAxisymmetricOrder_sq (lam : EscobarAnisotropy) :
    escobarAxisymmetricOrder lam ^ 2 =
      (lam : ℝ) ^ 2 / (4 * (1 - (lam : ℝ)) ^ 2) := by
  rw [escobarAxisymmetricOrder, div_pow, sq_abs]
  ring

/-! ## Exact anisotropic radial conjugation -/

/-- Radial power multiplying the Bessel profile in equation (11). -/
def escobarConjugationScale (lam : EscobarAnisotropy) (r : ℝ) : ℝ :=
  r ^ escobarSigma lam

theorem hasDerivAt_escobarConjugationScale
    (lam : EscobarAnisotropy) (r : PositiveRadius) :
    HasDerivAt (escobarConjugationScale lam)
      (escobarSigma lam * (r : ℝ) ^ (escobarSigma lam - 1)) r := by
  exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt r.property))

/-- Value jet induced by `R = r^sigma u`. -/
def escobarConjugatedValue
    (lam : EscobarAnisotropy) (r u : ℝ) : ℝ :=
  escobarConjugationScale lam r * u

/-- First radial jet induced by `R = r^sigma u`. -/
def escobarConjugatedFirst
    (lam : EscobarAnisotropy) (r u u₁ : ℝ) : ℝ :=
  escobarConjugationScale lam r * (u₁ + escobarSigma lam * u / r)

/-- Second radial jet induced by `R = r^sigma u`. -/
def escobarConjugatedSecond
    (lam : EscobarAnisotropy) (r u u₁ u₂ : ℝ) : ℝ :=
  escobarConjugationScale lam r *
    (u₂ + 2 * escobarSigma lam * u₁ / r +
      escobarSigma lam * (escobarSigma lam - 1) * u / r ^ 2)

/-- Bessel-form radial residual reached after the paper's power conjugation. -/
def escobarBesselRadialResidual
    (lam : EscobarAnisotropy) (eta r u u₁ u₂ : ℝ) : ℝ :=
  u₂ + u₁ / r +
    (eta ^ 2 - escobarAxisymmetricOrder lam ^ 2 / r ^ 2) * u

/-- Equations (7)--(11) as one exact identity: the anisotropic radial operator is conjugate to the
Bessel operator of order `|lambda| / (2(1-lambda))`. -/
theorem escobar_radial_conjugation_identity
    (lam : EscobarAnisotropy) (Ω eta : ℝ) (r : PositiveRadius) (u u₁ u₂ : ℝ) :
    escobarRadialResidual (lam : ℝ) Ω (escobarBetaSq lam Ω eta) r
        (escobarConjugatedValue lam r u)
        (escobarConjugatedFirst lam r u u₁)
        (escobarConjugatedSecond lam r u u₁ u₂) =
      (1 - (lam : ℝ)) * escobarConjugationScale lam r *
        escobarBesselRadialResidual lam eta r u u₁ u₂ := by
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt r.property
  have hlam : 1 - (lam : ℝ) ≠ 0 := ne_of_gt (escobar_one_sub_anisotropy_pos lam)
  have hlam' : (lam : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt lam.property.2)
  simp only [escobarRadialResidual, escobarBetaSq, escobarConjugatedValue,
    escobarConjugatedFirst, escobarConjugatedSecond, escobarBesselRadialResidual,
    escobarSigma]
  rw [escobarAxisymmetricOrder_sq]
  field_simp [hr0, hlam, hlam']
  ring

/-! ## Order-one infrastructure and a nonzero-anisotropy exact mode -/

/-- The corpus all-order jet at order one is the existing first derivative of `J₀`. -/
theorem besselJ0HighJet_one_eq_deriv (u : ℝ) :
    GaloisForLFunctions.RHTower.besselJ0HighJet 1 u =
      GaloisForLFunctions.RHTower.besselJ0Deriv u := by
  have h := GaloisForLFunctions.RHTower.hasDerivAt_besselJ0HighJet 0 u
  have hfun : GaloisForLFunctions.RHTower.besselJ0HighJet 0 =
      GaloisForLFunctions.RHTower.besselJ0 :=
    funext GaloisForLFunctions.RHTower.besselJ0HighJet_zero
  rw [hfun] at h
  exact h.unique (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0 u)

/-- The order-two all-order jet is the existing second derivative of `J₀`. -/
theorem besselJ0HighJet_two_eq_second (u : ℝ) :
    GaloisForLFunctions.RHTower.besselJ0HighJet 2 u =
      GaloisForLFunctions.RHTower.besselJ0SecondDeriv u := by
  have h := GaloisForLFunctions.RHTower.hasDerivAt_besselJ0HighJet 1 u
  have hfun : GaloisForLFunctions.RHTower.besselJ0HighJet 1 =
      GaloisForLFunctions.RHTower.besselJ0Deriv :=
    funext besselJ0HighJet_one_eq_deriv
  rw [hfun] at h
  exact h.unique (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0Deriv u)

/-- Third derivative of `J₀`, supplied by the corpus's all-order integral jets. -/
def besselJ0ThirdDeriv (u : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ0HighJet 3 u

theorem hasDerivAt_besselJ0SecondDeriv (u : ℝ) :
    HasDerivAt GaloisForLFunctions.RHTower.besselJ0SecondDeriv
      (besselJ0ThirdDeriv u) u := by
  have h := GaloisForLFunctions.RHTower.hasDerivAt_besselJ0HighJet 2 u
  have hfun : GaloisForLFunctions.RHTower.besselJ0HighJet 2 =
      GaloisForLFunctions.RHTower.besselJ0SecondDeriv :=
    funext besselJ0HighJet_two_eq_second
  rw [hfun] at h
  exact h

/-- First derivative of the corpus order-one Bessel function. -/
def besselJ1Deriv (u : ℝ) : ℝ :=
  -GaloisForLFunctions.RHTower.besselJ0SecondDeriv u

/-- Second derivative of the corpus order-one Bessel function. -/
def besselJ1SecondDeriv (u : ℝ) : ℝ :=
  -besselJ0ThirdDeriv u

theorem hasDerivAt_besselJ1_certified (u : ℝ) :
    HasDerivAt GaloisForLFunctions.RHTower.besselJ1 (besselJ1Deriv u) u := by
  exact GaloisForLFunctions.RHTower.hasDerivAt_besselJ1 u

theorem hasDerivAt_besselJ1Deriv (u : ℝ) :
    HasDerivAt besselJ1Deriv (besselJ1SecondDeriv u) u := by
  exact (hasDerivAt_besselJ0SecondDeriv u).neg

/-- Missing analytic infrastructure exposed by the anisotropic paper: the corpus's `J₁ = -J₀'`
satisfies the order-one Bessel equation. -/
theorem besselJ1_ode (u : PositiveRadius) :
    besselJ1SecondDeriv u + besselJ1Deriv u / (u : ℝ) +
      (1 - 1 / (u : ℝ) ^ 2) * GaloisForLFunctions.RHTower.besselJ1 u = 0 := by
  let F : ℝ → ℝ := GaloisForLFunctions.RHTower.besselJ0SecondDeriv +
    GaloisForLFunctions.RHTower.besselJ0Deriv / id +
    GaloisForLFunctions.RHTower.besselJ0
  have hu0 : (u : ℝ) ≠ 0 := ne_of_gt u.property
  have hF : HasDerivAt F
      (besselJ0ThirdDeriv u +
        (GaloisForLFunctions.RHTower.besselJ0SecondDeriv u * (u : ℝ) -
          GaloisForLFunctions.RHTower.besselJ0Deriv u) / (u : ℝ) ^ 2 +
        GaloisForLFunctions.RHTower.besselJ0Deriv u) u := by
    dsimp only [F]
    simpa only [id_eq, mul_one] using ((hasDerivAt_besselJ0SecondDeriv u).add
      ((GaloisForLFunctions.RHTower.hasDerivAt_besselJ0Deriv u).div
        (hasDerivAt_id (u : ℝ)) hu0)).add
      (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0 u)
  have hFzero : HasDerivAt F 0 u := by
    apply (hasDerivAt_const (u : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds u.property] with x hx
    simpa only [F, Pi.add_apply, Pi.div_apply, id_eq] using
      GaloisForLFunctions.RHTower.besselJ0_ode (ne_of_gt hx)
  have hderiv := hF.unique hFzero
  simp only [besselJ1SecondDeriv, besselJ1Deriv,
    GaloisForLFunctions.RHTower.besselJ1] at ⊢
  field_simp [hu0] at hderiv ⊢
  linarith

/-- Physical anisotropy whose effective Bessel order is exactly one. -/
def escobarTwoThirdAnisotropy : EscobarAnisotropy := ⟨2 / 3, by norm_num⟩

@[simp] theorem escobarSigma_two_thirds :
    escobarSigma escobarTwoThirdAnisotropy = -1 := by
  norm_num [escobarSigma, escobarTwoThirdAnisotropy]

@[simp] theorem escobarAxisymmetricOrder_two_thirds :
    escobarAxisymmetricOrder escobarTwoThirdAnisotropy = 1 := by
  norm_num [escobarAxisymmetricOrder, escobarTwoThirdAnisotropy, abs_of_nonneg]

@[simp] theorem escobarBranchOrder_two_thirds :
    escobarBranchOrder escobarTwoThirdAnisotropy = 1 := by
  norm_num [escobarBranchOrder, escobarAxisymmetricOrder, escobarTwoThirdAnisotropy,
    abs_of_nonneg]

/-- Positive spectral frequency for the exact order-one anisotropic mode. -/
abbrev EscobarPositiveFrequency := Set.Ioi (0 : ℝ)

def escobarOrderOneMode (eta : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ1 ((eta : ℝ) * r)

def escobarOrderOneModeDeriv (eta : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  besselJ1Deriv ((eta : ℝ) * r) * (eta : ℝ)

def escobarOrderOneModeSecond (eta : EscobarPositiveFrequency) (r : ℝ) : ℝ :=
  (eta : ℝ) ^ 2 * besselJ1SecondDeriv ((eta : ℝ) * r)

theorem hasDerivAt_escobarOrderOneMode
    (eta : EscobarPositiveFrequency) (r : PositiveRadius) :
    HasDerivAt (escobarOrderOneMode eta) (escobarOrderOneModeDeriv eta r) r := by
  have hinner : HasDerivAt (fun x : ℝ => (eta : ℝ) * x) (eta : ℝ) r := by
    simpa using (hasDerivAt_id (r : ℝ)).const_mul (eta : ℝ)
  exact (hasDerivAt_besselJ1_certified ((eta : ℝ) * (r : ℝ))).comp (r : ℝ) hinner

theorem hasDerivAt_escobarOrderOneModeDeriv
    (eta : EscobarPositiveFrequency) (r : PositiveRadius) :
    HasDerivAt (escobarOrderOneModeDeriv eta) (escobarOrderOneModeSecond eta r) r := by
  have hinner : HasDerivAt (fun x : ℝ => (eta : ℝ) * x) (eta : ℝ) r := by
    simpa using (hasDerivAt_id (r : ℝ)).const_mul (eta : ℝ)
  have h := (hasDerivAt_besselJ1Deriv ((eta : ℝ) * (r : ℝ))).comp (r : ℝ) hinner
  have h' := h.mul_const (eta : ℝ)
  have hval : besselJ1SecondDeriv ((eta : ℝ) * (r : ℝ)) * (eta : ℝ) * (eta : ℝ) =
      escobarOrderOneModeSecond eta r := by
    rw [escobarOrderOneModeSecond]
    ring
  rw [hval] at h'
  exact h'

/-- Exact nonzero-anisotropy Bessel residual at `lambda = 2/3`. -/
theorem escobarOrderOneMode_bessel_residual_zero
    (eta : EscobarPositiveFrequency) (r : PositiveRadius) :
    escobarBesselRadialResidual escobarTwoThirdAnisotropy eta r
      (escobarOrderOneMode eta r) (escobarOrderOneModeDeriv eta r)
      (escobarOrderOneModeSecond eta r) = 0 := by
  have harg : 0 < (eta : ℝ) * (r : ℝ) := mul_pos eta.property r.property
  have hode := besselJ1_ode
    (⟨(eta : ℝ) * (r : ℝ), by exact harg⟩ : PositiveRadius)
  have heta : (eta : ℝ) ≠ 0 := ne_of_gt eta.property
  have hr : (r : ℝ) ≠ 0 := ne_of_gt r.property
  simp only [escobarBesselRadialResidual, escobarAxisymmetricOrder_two_thirds,
    escobarOrderOneMode, escobarOrderOneModeDeriv, escobarOrderOneModeSecond]
  calc
    (eta : ℝ) ^ 2 * besselJ1SecondDeriv ((eta : ℝ) * (r : ℝ)) +
        besselJ1Deriv ((eta : ℝ) * (r : ℝ)) * (eta : ℝ) / (r : ℝ) +
        ((eta : ℝ) ^ 2 - 1 ^ 2 / (r : ℝ) ^ 2) *
          GaloisForLFunctions.RHTower.besselJ1 ((eta : ℝ) * (r : ℝ)) =
      (eta : ℝ) ^ 2 *
        (besselJ1SecondDeriv ((eta : ℝ) * (r : ℝ)) +
          besselJ1Deriv ((eta : ℝ) * (r : ℝ)) / ((eta : ℝ) * (r : ℝ)) +
          (1 - 1 / ((eta : ℝ) * (r : ℝ)) ^ 2) *
            GaloisForLFunctions.RHTower.besselJ1 ((eta : ℝ) * (r : ℝ))) := by
        field_simp [heta, hr]
    _ = 0 := by rw [hode, mul_zero]

/-- Original anisotropic radial operator vanishes on the conjugated order-one mode at
`lambda = 2/3`. -/
theorem escobarTwoThirdOrderOne_residual_zero
    (Ω : ℝ) (eta : EscobarPositiveFrequency) (r : PositiveRadius) :
    escobarRadialResidual (escobarTwoThirdAnisotropy : ℝ) Ω
        (escobarBetaSq escobarTwoThirdAnisotropy Ω eta) r
        (escobarConjugatedValue escobarTwoThirdAnisotropy r (escobarOrderOneMode eta r))
        (escobarConjugatedFirst escobarTwoThirdAnisotropy r
          (escobarOrderOneMode eta r) (escobarOrderOneModeDeriv eta r))
        (escobarConjugatedSecond escobarTwoThirdAnisotropy r
          (escobarOrderOneMode eta r) (escobarOrderOneModeDeriv eta r)
          (escobarOrderOneModeSecond eta r)) = 0 := by
  rw [escobar_radial_conjugation_identity,
    escobarOrderOneMode_bessel_residual_zero]
  simp

/-- Isotropic point of the physical anisotropy interval. -/
def escobarZeroAnisotropy : EscobarAnisotropy := ⟨0, by norm_num⟩

@[simp] theorem escobarSigma_zero : escobarSigma escobarZeroAnisotropy = 0 := by
  norm_num [escobarSigma, escobarZeroAnisotropy]

@[simp] theorem escobarAxisymmetricOrder_zero :
    escobarAxisymmetricOrder escobarZeroAnisotropy = 0 := by
  norm_num [escobarAxisymmetricOrder, escobarZeroAnisotropy]

@[simp] theorem escobarBranchOrder_zero : escobarBranchOrder escobarZeroAnisotropy = 0 := by
  norm_num [escobarBranchOrder, escobarAxisymmetricOrder, escobarZeroAnisotropy]

@[simp] theorem escobarBetaSq_zero (Ω η : ℝ) :
    escobarBetaSq escobarZeroAnisotropy Ω η = Ω ^ 2 - η ^ 2 := by
  simp [escobarBetaSq, escobarZeroAnisotropy]

/-! ## Certified isotropic radial mode -/

/-- The paper's regular radial mode at `λ = 0`. -/
def escobarIsotropicRadialMode (η r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ0 (η * r)

/-- First radial derivative of the isotropic mode. -/
def escobarIsotropicRadialModeDeriv (η r : ℝ) : ℝ :=
  GaloisForLFunctions.RHTower.besselJ0Deriv (η * r) * η

/-- Second radial derivative of the isotropic mode. -/
def escobarIsotropicRadialModeSecond (η r : ℝ) : ℝ :=
  η ^ 2 * GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r)

theorem hasDerivAt_escobarIsotropicRadialMode (η r : ℝ) :
    HasDerivAt (escobarIsotropicRadialMode η)
      (escobarIsotropicRadialModeDeriv η r) r := by
  have hinner : HasDerivAt (fun x : ℝ => η * x) η r := by
    simpa using (hasDerivAt_id r).const_mul η
  have h := (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0 (η * r)).comp r hinner
  exact h

theorem hasDerivAt_escobarIsotropicRadialModeDeriv (η r : ℝ) :
    HasDerivAt (escobarIsotropicRadialModeDeriv η)
      (escobarIsotropicRadialModeSecond η r) r := by
  have hinner : HasDerivAt (fun x : ℝ => η * x) η r := by
    simpa using (hasDerivAt_id r).const_mul η
  have h := (GaloisForLFunctions.RHTower.hasDerivAt_besselJ0Deriv (η * r)).comp r
    hinner
  have h' := h.mul_const η
  have hval : GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r) * η * η =
      escobarIsotropicRadialModeSecond η r := by
    rw [escobarIsotropicRadialModeSecond]
    ring
  rw [hval] at h'
  exact h'

/-- At `λ = 0`, corpus `J₀` is an exact, certified separated radial mode for every frequency and
radial spectral parameter.  The zero-frequency case is included, not assumed away. -/
theorem escobarIsotropicRadialMode_residual_zero
    (Ω η : ℝ) (r : PositiveRadius) :
    escobarRadialResidual 0 Ω (escobarBetaSq escobarZeroAnisotropy Ω η) r
      (escobarIsotropicRadialMode η r)
      (escobarIsotropicRadialModeDeriv η r)
      (escobarIsotropicRadialModeSecond η r) = 0 := by
  rcases r with ⟨r, hr⟩
  by_cases hη : η = 0
  · subst η
    simp [escobarRadialResidual, escobarIsotropicRadialMode,
      escobarIsotropicRadialModeDeriv, escobarIsotropicRadialModeSecond]
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hx : η * r ≠ 0 := mul_ne_zero hη hr0
    have hode := GaloisForLFunctions.RHTower.besselJ0_ode hx
    simp only [escobarRadialResidual, escobarBetaSq_zero,
      escobarIsotropicRadialMode, escobarIsotropicRadialModeDeriv,
      escobarIsotropicRadialModeSecond]
    calc
      (1 - 0) * (η ^ 2 * GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r)) +
            GaloisForLFunctions.RHTower.besselJ0Deriv (η * r) * η / r +
            (Ω ^ 2 - (Ω ^ 2 - η ^ 2)) * GaloisForLFunctions.RHTower.besselJ0 (η * r) =
          η ^ 2 * (GaloisForLFunctions.RHTower.besselJ0SecondDeriv (η * r) +
            GaloisForLFunctions.RHTower.besselJ0Deriv (η * r) / (η * r) +
            GaloisForLFunctions.RHTower.besselJ0 (η * r)) := by
              field_simp [hη, hr0]
              ring
      _ = 0 := by rw [hode, mul_zero]

end GaloisForLFunctions.HTGeometry
