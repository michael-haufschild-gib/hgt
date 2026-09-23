import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Affine-Gamma parabolicity rigidity for moment-ratio flows

For an exponentially shifted moment ladder, adjacent normalized moment ratios obey a
one-sided Riccati chain.  This module classifies the normalizations for which the second
discrete curvature of that chain closes, on its zero boundary, as a nonnegative square plus
transport from the next curvature coordinate.

The classification is exact: this local parabolic closure exists at every index if and only if
the normalization weights are affine.  Their cumulative normalizers are therefore rising
Pochhammer products (scaled Gamma products when the step is positive).
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- The universal one-sided Riccati velocity of a normalized adjacent moment ratio. -/
def weightedMomentRatioVelocity (a q : ℕ → ℝ) (j : ℕ) : ℝ :=
  q j * (a (j + 1) * q (j + 1) - a j * q j)

/-- Second forward curvature of a sequence, with the sign convention used by the theta source. -/
def ratioSecondCurvature (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  q j - 2 * q (j + 1) + q (j + 2)

/-- Velocity induced on second curvature by the adjacent-ratio Riccati chain. -/
def ratioSecondCurvatureVelocity (a q : ℕ → ℝ) (j : ℕ) : ℝ :=
  weightedMomentRatioVelocity a q j -
    2 * weightedMomentRatioVelocity a q (j + 1) +
    weightedMomentRatioVelocity a q (j + 2)

/-- Four-state form of the curvature velocity at one index. -/
def localRatioSecondCurvatureVelocity
    (A B C D x y z w : ℝ) : ℝ :=
  x * (B * y - A * x) -
    2 * y * (C * z - B * y) +
    z * (D * w - C * z)

/-- A weight quadruple has local carré-parabolic closure when, on the zero-curvature boundary,
the curvature velocity is a square-production term plus transport from the next curvature. -/
def LocalCarreParabolicClosure (A B C D : ℝ) : Prop :=
  ∃ kappa tau : ℝ, ∀ x y z w : ℝ,
    x - 2 * y + z = 0 →
      localRatioSecondCurvatureVelocity A B C D x y z w =
        kappa * (x - y) ^ (2 : ℕ) + tau * z * (y - 2 * z + w)

/-- Any local carré-parabolic law forces both consecutive second differences of the weights to
vanish, and forces its production and transport coefficients. -/
theorem localCarreParabolicClosure_forces_affine_and_coefficients
    {A B C D kappa tau : ℝ}
    (hclosure : ∀ x y z w : ℝ,
      x - 2 * y + z = 0 →
        localRatioSecondCurvatureVelocity A B C D x y z w =
          kappa * (x - y) ^ (2 : ℕ) + tau * z * (y - 2 * z + w)) :
    A - 2 * B + C = 0 ∧
      B - 2 * C + D = 0 ∧
      kappa = 4 * (B - A) ∧
      tau = D := by
  have h100m10 := hclosure 1 0 (-1) 0 (by norm_num)
  have h0120 := hclosure 0 1 2 0 (by norm_num)
  have h1110 := hclosure 1 1 1 0 (by norm_num)
  have h1111 := hclosure 1 1 1 1 (by norm_num)
  simp only [localRatioSecondCurvatureVelocity] at h100m10 h0120 h1110 h1111
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- **Local affine-Gamma parabolicity classification.**  A four-step normalization admits a
source-independent local carré-parabolic boundary law exactly when its four weights lie in an
arithmetic progression. -/
theorem localCarreParabolicClosure_iff_affine
    (A B C D : ℝ) :
    LocalCarreParabolicClosure A B C D ↔
      A - 2 * B + C = 0 ∧ B - 2 * C + D = 0 := by
  constructor
  · rintro ⟨kappa, tau, hclosure⟩
    have h := localCarreParabolicClosure_forces_affine_and_coefficients hclosure
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hABC, hBCD⟩
    refine ⟨4 * (B - A), D, ?_⟩
    intro x y z w hcurvature
    have hC : C = 2 * B - A := by linarith
    have hD : D = 3 * B - 2 * A := by linarith
    have hz : z = 2 * y - x := by linarith
    rw [hC, hD, hz]
    simp only [localRatioSecondCurvatureVelocity]
    ring

/-- The production and transport constants of a local carré-parabolic closure are unique. -/
theorem localCarreParabolicClosure_coefficients_unique
    {A B C D kappa tau : ℝ}
    (hclosure : ∀ x y z w : ℝ,
      x - 2 * y + z = 0 →
        localRatioSecondCurvatureVelocity A B C D x y z w =
          kappa * (x - y) ^ (2 : ℕ) + tau * z * (y - 2 * z + w)) :
    kappa = 4 * (B - A) ∧ tau = D :=
  (localCarreParabolicClosure_forces_affine_and_coefficients hclosure).2.2

/-- **Full affine-Gamma curvature transport identity.**  Arithmetic normalization weights are
not merely sufficient on the boundary: off the boundary the remaining term is exactly a linear
reaction multiple of the current curvature. -/
theorem affineGamma_ratioSecondCurvatureVelocity_eq
    (A h x y z w : ℝ) :
    localRatioSecondCurvatureVelocity
        A (A + h) (A + 2 * h) (A + 3 * h) x y z w =
      4 * h * (x - y) ^ (2 : ℕ) +
        (A + 3 * h) * z * (y - 2 * z + w) +
        (x - 2 * y + z) *
          (-(A + 4 * h) * x + (h - A) * y + (A + 4 * h) * z) := by
  simp only [localRatioSecondCurvatureVelocity]
  ring

/-- Positive affine slope and positive forward transport orient the zero-curvature boundary
inward. -/
theorem affineGamma_ratioSecondCurvatureVelocity_nonneg_of_boundary
    {A h x y z w : ℝ}
    (hh : 0 ≤ h) (htransport : 0 ≤ A + 3 * h) (hz : 0 ≤ z)
    (hcurrent : x - 2 * y + z = 0)
    (hnext : 0 ≤ y - 2 * z + w) :
    0 ≤ localRatioSecondCurvatureVelocity
      A (A + h) (A + 2 * h) (A + 3 * h) x y z w := by
  rw [affineGamma_ratioSecondCurvatureVelocity_eq, hcurrent, zero_mul, add_zero]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by positivity) hh) (sq_nonneg _))
    (mul_nonneg (mul_nonneg htransport hz) hnext)

/-- With positive affine slope, a nonzero adjacent gap produces strictly inward curvature at the
boundary, even when the forward transport channel is only nonnegative. -/
theorem affineGamma_ratioSecondCurvatureVelocity_pos_of_boundary_of_gap
    {A h x y z w : ℝ}
    (hh : 0 < h) (htransport : 0 ≤ A + 3 * h) (hz : 0 ≤ z)
    (hcurrent : x - 2 * y + z = 0)
    (hnext : 0 ≤ y - 2 * z + w) (hgap : x ≠ y) :
    0 < localRatioSecondCurvatureVelocity
      A (A + h) (A + 2 * h) (A + 3 * h) x y z w := by
  rw [affineGamma_ratioSecondCurvatureVelocity_eq, hcurrent, zero_mul, add_zero]
  have hproduction : 0 < 4 * h * (x - y) ^ (2 : ℕ) := by
    exact mul_pos (mul_pos (by norm_num) hh) (sq_pos_of_ne_zero (sub_ne_zero.mpr hgap))
  exact add_pos_of_pos_of_nonneg hproduction
    (mul_nonneg (mul_nonneg htransport hz) hnext)

/-- A sequence is locally curvature-parabolic at one index when its consecutive weight
quadruple has the universal boundary closure. -/
def CurvatureParabolicAt (a : ℕ → ℝ) (j : ℕ) : Prop :=
  LocalCarreParabolicClosure (a j) (a (j + 1)) (a (j + 2)) (a (j + 3))

/-- Vanishing second differences force a real sequence to be affine in its natural index. -/
theorem eq_affine_of_secondDifference_zero
    {a : ℕ → ℝ}
    (hsecond : ∀ j : ℕ, a j - 2 * a (j + 1) + a (j + 2) = 0) :
    ∀ j : ℕ, a j = a 0 + (j : ℝ) * (a 1 - a 0) := by
  have hdiff : ∀ j : ℕ, a (j + 1) - a j = a 1 - a 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        have hj := hsecond j
        nlinarith
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      have hj := hdiff j
      push_cast
      nlinarith

/-- **Global affine-Gamma parabolicity rigidity law.**  Local carré-parabolic closure at every
index is equivalent to one global affine normalization sequence. -/
theorem curvatureParabolicAt_all_iff_affine (a : ℕ → ℝ) :
    (∀ j : ℕ, CurvatureParabolicAt a j) ↔
      ∃ alpha h : ℝ, ∀ j : ℕ, a j = alpha + (j : ℝ) * h := by
  constructor
  · intro hall
    have hsecond : ∀ j : ℕ, a j - 2 * a (j + 1) + a (j + 2) = 0 := by
      intro j
      have hj := (localCarreParabolicClosure_iff_affine
        (a j) (a (j + 1)) (a (j + 2)) (a (j + 3))).mp (hall j)
      exact hj.1
    exact ⟨a 0, a 1 - a 0, eq_affine_of_secondDifference_zero hsecond⟩
  · rintro ⟨alpha, h, ha⟩ j
    rw [CurvatureParabolicAt, localCarreParabolicClosure_iff_affine]
    constructor
    · rw [ha j, ha (j + 1), ha (j + 2)]
      push_cast
      ring
    · rw [ha (j + 1), ha (j + 2), ha (j + 3)]
      push_cast
      ring

/-- Cumulative normalizers with affine consecutive ratios are exactly rising Pochhammer
products. -/
theorem normalization_eq_affinePochhammerProduct
    {N : ℕ → ℝ} {alpha h : ℝ}
    (hrec : ∀ j : ℕ, N (j + 1) = (alpha + (j : ℝ) * h) * N j) :
    ∀ j : ℕ, N j = N 0 * ∏ k ∈ Finset.range j, (alpha + (k : ℝ) * h) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [hrec j, ih, Finset.prod_range_succ]
      ring

/-- Gamma/Pochhammer-normalized adjacent ratio of an abstract differentiable moment ladder. -/
def normalizedMomentRatio
    (M : ℝ → ℕ → ℝ) (a : ℕ → ℝ) (lambda : ℝ) (j : ℕ) : ℝ :=
  (M lambda (j + 1) / M lambda j) / a j

/-- Exact Riccati response of every normalized adjacent ratio under the universal moment shift
`M_j' = M_(j+1)`. -/
theorem hasDerivAt_normalizedMomentRatio
    {M : ℝ → ℕ → ℝ} {a : ℕ → ℝ} {lambda : ℝ} (j : ℕ)
    (hshift : ∀ k : ℕ,
      HasDerivAt (fun eta => M eta k) (M lambda (k + 1)) lambda)
    (hMne : ∀ k : ℕ, M lambda k ≠ 0)
    (hane : ∀ k : ℕ, a k ≠ 0) :
    HasDerivAt (fun eta => normalizedMomentRatio M a eta j)
      (weightedMomentRatioVelocity a
        (fun k => normalizedMomentRatio M a lambda k) j) lambda := by
  have hquot := (hshift (j + 1)).div (hshift j) (hMne j)
  have hscaled := hquot.div_const (a j)
  simpa only [normalizedMomentRatio, Pi.div_apply] using!
    hscaled.congr_deriv (by
      simp only [weightedMomentRatioVelocity]
      field_simp [hMne j, hMne (j + 1), hane j, hane (j + 1)])

/-- Second curvature of the normalized ratios of an abstract moment ladder. -/
def normalizedMomentRatioCurvature
    (M : ℝ → ℕ → ℝ) (a : ℕ → ℝ) (lambda : ℝ) (j : ℕ) : ℝ :=
  ratioSecondCurvature (fun k => normalizedMomentRatio M a lambda k) j

/-- The full affine-Gamma parabolic law is inherited by every differentiable moment ladder,
independently of its representing measure or source. -/
theorem hasDerivAt_normalizedMomentRatioCurvature_of_affineWeights
    {M : ℝ → ℕ → ℝ} {a : ℕ → ℝ} {lambda A h : ℝ} (j : ℕ)
    (hshift : ∀ k : ℕ,
      HasDerivAt (fun eta => M eta k) (M lambda (k + 1)) lambda)
    (hMne : ∀ k : ℕ, M lambda k ≠ 0)
    (hane : ∀ k : ℕ, a k ≠ 0)
    (ha0 : a j = A)
    (ha1 : a (j + 1) = A + h)
    (ha2 : a (j + 2) = A + 2 * h)
    (ha3 : a (j + 3) = A + 3 * h) :
    HasDerivAt (fun eta => normalizedMomentRatioCurvature M a eta j)
      (let q := fun k => normalizedMomentRatio M a lambda k
       4 * h * (q j - q (j + 1)) ^ (2 : ℕ) +
         (A + 3 * h) * q (j + 2) * ratioSecondCurvature q (j + 1) +
         ratioSecondCurvature q j *
           (-(A + 4 * h) * q j + (h - A) * q (j + 1) +
             (A + 4 * h) * q (j + 2))) lambda := by
  let q : ℕ → ℝ := fun k => normalizedMomentRatio M a lambda k
  have h0 := hasDerivAt_normalizedMomentRatio j hshift hMne hane
  have h1 := (hasDerivAt_normalizedMomentRatio (j + 1) hshift hMne hane).const_mul 2
  have h2 := hasDerivAt_normalizedMomentRatio (j + 2) hshift hMne hane
  have hsub :
      HasDerivAt (fun eta =>
        normalizedMomentRatio M a eta j -
          2 * normalizedMomentRatio M a eta (j + 1))
        (weightedMomentRatioVelocity a q j -
          2 * weightedMomentRatioVelocity a q (j + 1)) lambda := by
    exact HasDerivAt.sub h0 h1
  have hcurvature :
      HasDerivAt (fun eta => normalizedMomentRatioCurvature M a eta j)
        (ratioSecondCurvatureVelocity a q j) lambda := by
    simpa only [normalizedMomentRatioCurvature, ratioSecondCurvature,
      ratioSecondCurvatureVelocity, q, Pi.add_apply] using! HasDerivAt.add hsub h2
  have hid :
      ratioSecondCurvatureVelocity a q j =
        4 * h * (q j - q (j + 1)) ^ (2 : ℕ) +
          (A + 3 * h) * q (j + 2) * ratioSecondCurvature q (j + 1) +
          ratioSecondCurvature q j *
            (-(A + 4 * h) * q j + (h - A) * q (j + 1) +
              (A + 4 * h) * q (j + 2)) := by
    simp only [ratioSecondCurvatureVelocity, weightedMomentRatioVelocity,
      ratioSecondCurvature, q, Nat.add_assoc, Nat.reduceAdd]
    rw [ha0, ha1, ha2, ha3]
    ring
  dsimp only
  rw [← hid]
  exact hcurvature

end

end HTGeometry
