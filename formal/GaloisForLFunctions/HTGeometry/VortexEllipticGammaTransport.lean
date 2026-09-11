import GaloisForLFunctions.HTGeometry.EllipticGammaThetaBoundaryAnalytic

/-!
# Elliptic-Gamma transport for finite vortex products

The two source equations in Brunner–Cheng–Jockers, arXiv:2609.09298, equation (2.90),
define compatible theta multipliers. In the existing meromorphic field they give flatness,
finite products in both period directions, rectangular transport, and inverse-degree transport.
Periods are parametrized by unrestricted real coordinates; their positive imaginary parts
are proved, so no analytic regularity or nonvanishing premise is exposed by these statements.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
open GaloisForLFunctions Bottcher
noncomputable section

local instance vortexGammaAnalyticDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- A parametrization of upper-half-plane periods by unrestricted real coordinates. -/
def vortexUpperPeriod (x s : ℝ) : ℂ := (x : ℂ) + Complex.I * (Real.exp s : ℂ)

theorem vortexUpperPeriod_im_pos (x s : ℝ) : 0 < (vortexUpperPeriod x s).im := by
  simpa only [vortexUpperPeriod, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, one_mul, zero_add] using Real.exp_pos s

/-- Compatibility of the two elliptic-Gamma difference equations: their theta multipliers
have exactly zero multiplicative curvature in the meromorphic field. -/
theorem vortexEllipticGamma_theta_flatness (x s y t : ℝ) :
    let σ := vortexUpperPeriod x s
    let τ := vortexUpperPeriod y t
    let A := ellipticGammaThetaBoundaryMero τ (vortexUpperPeriod_im_pos y t)
    let B := ellipticGammaThetaBoundaryTauMero σ τ (vortexUpperPeriod_im_pos x s)
    addTranslationMeroEquiv τ A * B = addTranslationMeroEquiv σ B * A := by
  dsimp only
  let σ := vortexUpperPeriod x s
  let τ := vortexUpperPeriod y t
  let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  have hσ := ellipticGammaMero_add_sigma σ τ
    (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  have hτ := ellipticGammaMero_add_tau σ τ
    (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  apply mul_right_cancel₀ (ellipticGammaMero_ne_zero σ τ
    (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t))
  have hc : addTranslationMeroEquiv τ (addTranslationMeroEquiv σ Γ) =
      addTranslationMeroEquiv σ (addTranslationMeroEquiv τ Γ) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm τ σ]
  change addTranslationMeroEquiv τ (addTranslationMeroEquiv σ
      (ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t))) =
    addTranslationMeroEquiv σ (addTranslationMeroEquiv τ
      (ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t))) at hc
  simpa only [hσ, hτ, map_mul, mul_assoc] using hc

/-- Finite vortex-sector products telescope to an exact elliptic-Gamma translation in the
meromorphic field, where poles require no external regularity premise. -/
theorem vortexEllipticGamma_finite_shift (x s y t : ℝ) (n : ℕ) :
    let σ := vortexUpperPeriod x s
    let τ := vortexUpperPeriod y t
    let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
    let A := ellipticGammaThetaBoundaryMero τ (vortexUpperPeriod_im_pos y t)
    addTranslationMeroEquiv ((n : ℂ) * σ) Γ =
      (∏ k ∈ Finset.range n, addTranslationMeroEquiv ((k : ℂ) * σ) A) * Γ := by
  dsimp only
  let σ := vortexUpperPeriod x s
  let τ := vortexUpperPeriod y t
  let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  have hs := ellipticGammaMero_add_sigma σ τ
    (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.prod_empty, one_mul]
    have h := addTranslationMeroEquiv_add (0 : ℂ) 0 Γ
    rw [add_zero] at h
    exact (addTranslationMeroEquiv 0).injective h
  | succ n ih =>
    have hn : ((n + 1 : ℕ) : ℂ) * σ = (n : ℂ) * σ + σ := by push_cast; ring
    change addTranslationMeroEquiv (((n + 1 : ℕ) : ℂ) * σ) Γ = _
    rw [hn, ← addTranslationMeroEquiv_add, hs, map_mul, ih, Finset.prod_range_succ]
    ring

/-- Finite products in the second period direction telescope to an exact elliptic-Gamma translation in the
meromorphic field, where poles require no external regularity premise. -/
theorem vortexEllipticGamma_finite_tau_shift (x s y t : ℝ) (n : ℕ) :
    let σ := vortexUpperPeriod x s
    let τ := vortexUpperPeriod y t
    let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
    let A := ellipticGammaThetaBoundaryTauMero σ τ (vortexUpperPeriod_im_pos x s)
    addTranslationMeroEquiv ((n : ℂ) * τ) Γ =
      (∏ k ∈ Finset.range n, addTranslationMeroEquiv ((k : ℂ) * τ) A) * Γ := by
  dsimp only
  let σ := vortexUpperPeriod x s
  let τ := vortexUpperPeriod y t
  let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  have hs := ellipticGammaMero_add_tau σ τ
    (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, Finset.range_zero, Finset.prod_empty, one_mul]
    have h := addTranslationMeroEquiv_add (0 : ℂ) 0 Γ
    rw [add_zero] at h
    exact (addTranslationMeroEquiv 0).injective h
  | succ n ih =>
    have hn : ((n + 1 : ℕ) : ℂ) * τ = (n : ℂ) * τ + τ := by push_cast; ring
    change addTranslationMeroEquiv (((n + 1 : ℕ) : ℂ) * τ) Γ = _
    rw [hn, ← addTranslationMeroEquiv_add, hs, map_mul, ih, Finset.prod_range_succ]
    ring


/-- The two finite products compose to the exact rectangular lattice transport. -/
theorem vortexEllipticGamma_rectangular_shift (x s y t : ℝ) (m n : ℕ) :
    let σ := vortexUpperPeriod x s
    let τ := vortexUpperPeriod y t
    let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
    let A := ellipticGammaThetaBoundaryMero τ (vortexUpperPeriod_im_pos y t)
    let B := ellipticGammaThetaBoundaryTauMero σ τ (vortexUpperPeriod_im_pos x s)
    addTranslationMeroEquiv ((m : ℂ) * σ + (n : ℂ) * τ) Γ =
      addTranslationMeroEquiv ((n : ℂ) * τ)
        (∏ k ∈ Finset.range m, addTranslationMeroEquiv ((k : ℂ) * σ) A) *
      (∏ k ∈ Finset.range n, addTranslationMeroEquiv ((k : ℂ) * τ) B) * Γ := by
  dsimp only
  rw [add_comm ((m : ℂ) * vortexUpperPeriod x s), ← addTranslationMeroEquiv_add]
  rw [vortexEllipticGamma_finite_shift x s y t m, map_mul,
    vortexEllipticGamma_finite_tau_shift x s y t n, mul_assoc]

/-- Negative degree reverses the theta product. The denominator is a nonzero meromorphic
function, a consequence of the Gamma equation rather than an additional premise. -/
theorem vortexEllipticGamma_negative_shift (x s y t : ℝ) (n : ℕ) :
    let σ := vortexUpperPeriod x s
    let τ := vortexUpperPeriod y t
    let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
    let A := ellipticGammaThetaBoundaryMero τ (vortexUpperPeriod_im_pos y t)
    addTranslationMeroEquiv (-((n : ℂ) * σ)) Γ =
      Γ / addTranslationMeroEquiv (-((n : ℂ) * σ))
        (∏ k ∈ Finset.range n, addTranslationMeroEquiv ((k : ℂ) * σ) A) := by
  dsimp only
  let σ := vortexUpperPeriod x s
  let τ := vortexUpperPeriod y t
  let Γ := ellipticGammaMero σ τ (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t)
  let P := ∏ k ∈ Finset.range n, addTranslationMeroEquiv ((k : ℂ) * σ)
    (ellipticGammaThetaBoundaryMero τ (vortexUpperPeriod_im_pos y t))
  have hzero : addTranslationMeroEquiv 0 Γ = Γ := by
    have h := addTranslationMeroEquiv_add (0 : ℂ) 0 Γ
    rw [add_zero] at h
    exact (addTranslationMeroEquiv 0).injective h
  have ht := congrArg (addTranslationMeroEquiv (-((n : ℂ) * σ)))
    (vortexEllipticGamma_finite_shift x s y t n)
  change addTranslationMeroEquiv (-((n : ℂ) * σ))
      (addTranslationMeroEquiv ((n : ℂ) * σ) Γ) =
    addTranslationMeroEquiv (-((n : ℂ) * σ)) (P * Γ) at ht
  rw [addTranslationMeroEquiv_add, neg_add_cancel, hzero, map_mul] at ht
  have hp : addTranslationMeroEquiv (-((n : ℂ) * σ)) P ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at ht
    exact ellipticGammaMero_ne_zero σ τ
      (vortexUpperPeriod_im_pos x s) (vortexUpperPeriod_im_pos y t) ht
  apply (eq_div_iff hp).mpr
  simpa only [mul_comm] using ht.symm

end
end GaloisForLFunctions.HTGeometry
