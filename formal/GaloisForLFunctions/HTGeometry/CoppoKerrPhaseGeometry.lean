import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Kerr minima and collective-mode quartic geometry

The semiclassical Kerr energy of arXiv:2503.11928 and the effective quartic
potential of arXiv:2606.25061 share exact sum-of-squares certificates. These
statements concern the displayed polynomial models, not an approximation theorem
for the underlying quantum steady state.
-/

noncomputable section
namespace HTGeometry

/-- Two real Kerr amplitudes, with mass and cross-interaction parameters. -/
def coppoKerrEnergy (mass mu x y : ℝ) : ℝ :=
  x ^ (4 : ℕ) + y ^ (4 : ℕ) + 2 * mu * x ^ (2 : ℕ) * y ^ (2 : ℕ) - 2 * mass * (x ^ (2 : ℕ) + y ^ (2 : ℕ))

/-- Independent sign changes preserve the local Kerr energy. -/
theorem coppoKerrEnergy_signs (mass mu x y : ℝ) :
    coppoKerrEnergy mass mu (-x) y = coppoKerrEnergy mass mu x y ∧
    coppoKerrEnergy mass mu x (-y) = coppoKerrEnergy mass mu x y := by
  constructor <;> dsimp [coppoKerrEnergy] <;> ring

/-- Exchange of sites preserves the energy. -/
theorem coppoKerrEnergy_swap (mass mu x y : ℝ) :
    coppoKerrEnergy mass mu y x = coppoKerrEnergy mass mu x y := by
  dsimp [coppoKerrEnergy]; ring

/-- The density-wave chamber has radial and mixed-amplitude penalties. -/
theorem coppoKerrEnergy_density_square (g t x y : ℝ) :
    coppoKerrEnergy (g ^ (2 : ℕ)) (1 + t ^ (2 : ℕ)) x y + g ^ (4 : ℕ) =
      (x ^ (2 : ℕ) + y ^ (2 : ℕ) - g ^ (2 : ℕ)) ^ (2 : ℕ) + 2 * (t * x * y) ^ (2 : ℕ) := by
  dsimp [coppoKerrEnergy]; ring

/-- Constructed density-wave parameters always admit an axis minimum. -/
theorem coppoKerrEnergy_density_global_min (g t x y : ℝ) :
    coppoKerrEnergy (g ^ (2 : ℕ)) (1 + t ^ (2 : ℕ)) g 0 ≤
      coppoKerrEnergy (g ^ (2 : ℕ)) (1 + t ^ (2 : ℕ)) x y := by
  have h := coppoKerrEnergy_density_square g t x y
  have haxis : coppoKerrEnergy (g ^ (2 : ℕ)) (1 + t ^ (2 : ℕ)) g 0 = -g ^ (4 : ℕ) := by
    dsimp [coppoKerrEnergy]; ring
  rw [haxis]
  nlinarith [sq_nonneg (x ^ (2 : ℕ) + y ^ (2 : ℕ) - g ^ (2 : ℕ)), sq_nonneg (t * x * y)]

/-- Complete density-wave minimum classification, including the critical degeneracy. -/
theorem coppoKerrEnergy_density_min_iff (g t x y : ℝ) :
    coppoKerrEnergy (g ^ (2 : ℕ)) (1 + t ^ (2 : ℕ)) x y = -g ^ (4 : ℕ) ↔
      x ^ (2 : ℕ) + y ^ (2 : ℕ) = g ^ (2 : ℕ) ∧ t * x * y = 0 := by
  have h := coppoKerrEnergy_density_square g t x y
  constructor
  · intro he
    have hr : (x ^ (2 : ℕ) + y ^ (2 : ℕ) - g ^ (2 : ℕ)) ^ (2 : ℕ) = 0 := by nlinarith [sq_nonneg (t * x * y)]
    have ht : (t * x * y) ^ (2 : ℕ) = 0 := by nlinarith [sq_nonneg (x ^ (2 : ℕ) + y ^ (2 : ℕ) - g ^ (2 : ℕ))]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hr), sq_eq_zero_iff.mp ht⟩
  · rintro ⟨hr, ht⟩
    rw [hr, sub_self, ht] at h
    linarith

/-- At equal local and cross Kerr strengths the entire critical circle minimizes energy. -/
theorem coppoKerrEnergy_critical_circle (g x y : ℝ) :
    coppoKerrEnergy (g ^ (2 : ℕ)) 1 x y = -g ^ (4 : ℕ) ↔ x ^ (2 : ℕ) + y ^ (2 : ℕ) = g ^ (2 : ℕ) := by
  simpa using coppoKerrEnergy_density_min_iff g 0 x y

/-- In the strict density-wave chamber every minimizer lies on an axis. -/
theorem coppoKerrEnergy_strict_density_min_iff (g t x y : ℝ) :
    coppoKerrEnergy (g ^ (2 : ℕ)) (1 + (Real.exp t) ^ (2 : ℕ)) x y = -g ^ (4 : ℕ) ↔
      x ^ (2 : ℕ) + y ^ (2 : ℕ) = g ^ (2 : ℕ) ∧ (x = 0 ∨ y = 0) := by
  rw [coppoKerrEnergy_density_min_iff]
  simp [mul_eq_zero, Real.exp_ne_zero]

/-- Homogeneous Kerr energy separates radial and density-imbalance squares. -/
theorem coppoKerrEnergy_homogeneous_square (a mu x y : ℝ) :
    coppoKerrEnergy ((1 + mu) * a ^ (2 : ℕ)) mu x y + 2 * (1 + mu) * a ^ (4 : ℕ) =
      ((1 + mu) / 2) * (x ^ (2 : ℕ) + y ^ (2 : ℕ) - 2 * a ^ (2 : ℕ)) ^ (2 : ℕ) +
        ((1 - mu) / 2) * (x ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) := by
  dsimp [coppoKerrEnergy]; ring

/-- A rational parameterization covers the bounded homogeneous chamber without hypotheses. -/
theorem coppoKerrEnergy_homogeneous_rational_square (a t x y : ℝ) :
    coppoKerrEnergy ((2 / (1 + t ^ (2 : ℕ))) * a ^ (2 : ℕ))
        ((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) x y + 4 * a ^ (4 : ℕ) / (1 + t ^ (2 : ℕ)) =
      ((x ^ (2 : ℕ) + y ^ (2 : ℕ) - 2 * a ^ (2 : ℕ)) ^ (2 : ℕ) + t ^ (2 : ℕ) * (x ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ)) /
        (1 + t ^ (2 : ℕ)) := by
  have hd : (1 + t ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
  dsimp [coppoKerrEnergy]
  field_simp
  ring

/-- Homogeneous constructed amplitudes are global minima throughout that chamber. -/
theorem coppoKerrEnergy_homogeneous_global_min (a t x y : ℝ) :
    coppoKerrEnergy ((2 / (1 + t ^ (2 : ℕ))) * a ^ (2 : ℕ)) ((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) a a ≤
      coppoKerrEnergy ((2 / (1 + t ^ (2 : ℕ))) * a ^ (2 : ℕ)) ((1 - t ^ (2 : ℕ)) / (1 + t ^ (2 : ℕ))) x y := by
  have h := coppoKerrEnergy_homogeneous_rational_square a t x y
  have hmin := coppoKerrEnergy_homogeneous_rational_square a t a a
  have hp : 0 ≤ ((x ^ (2 : ℕ) + y ^ (2 : ℕ) - 2 * a ^ (2 : ℕ)) ^ (2 : ℕ) + t ^ (2 : ℕ) * (x ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ)) /
      (1 + t ^ (2 : ℕ)) := by positivity
  have hz : (a ^ (2 : ℕ) + a ^ (2 : ℕ) - 2 * a ^ (2 : ℕ)) ^ (2 : ℕ) + t ^ (2 : ℕ) * (a ^ (2 : ℕ) - a ^ (2 : ℕ)) ^ (2 : ℕ) = 0 := by ring
  rw [hz, zero_div] at hmin
  linarith

/-- The nonlocal paper's collective-coordinate potential. -/
def coppoCollectivePotential (alpha beta u v : ℝ) : ℝ :=
  -alpha / 2 * (u ^ (2 : ℕ) + v ^ (2 : ℕ)) + beta / 4 * (u ^ (4 : ℕ) + 6 * u ^ (2 : ℕ) * v ^ (2 : ℕ) + v ^ (4 : ℕ))

/-- The effective potential on the two original local coordinates. -/
def coppoNonlocalPotential (alpha beta xi x y : ℝ) : ℝ :=
  -alpha * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) + beta * (x ^ (4 : ℕ) + y ^ (4 : ℕ)) + xi * (x - y) ^ (2 : ℕ)

/-- The collective polynomial is the Kerr family at cross coefficient three. -/
theorem coppoCollectivePotential_eq_kerr (alpha u v : ℝ) :
    4 * coppoCollectivePotential alpha 1 u v = coppoKerrEnergy alpha 3 u v := by
  dsimp [coppoCollectivePotential, coppoKerrEnergy]; ring

/-- The orthogonal collective coordinates preserve quadratic energy. -/
theorem coppoCollective_quadratic (x y : ℝ) :
    ((x + y) / Real.sqrt 2) ^ (2 : ℕ) + ((x - y) / Real.sqrt 2) ^ (2 : ℕ) = x ^ (2 : ℕ) + y ^ (2 : ℕ) := by
  have hs : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by positivity)
  simp only [div_pow, hs]
  ring

/-- The apparently interacting collective quartic is a rotated sum of two local quartics. -/
theorem coppoCollective_quartic (x y : ℝ) :
    ((x + y) / Real.sqrt 2) ^ (4 : ℕ) +
        6 * ((x + y) / Real.sqrt 2) ^ (2 : ℕ) * ((x - y) / Real.sqrt 2) ^ (2 : ℕ) +
        ((x - y) / Real.sqrt 2) ^ (4 : ℕ) = 2 * (x ^ (4 : ℕ) + y ^ (4 : ℕ)) := by
  have hs : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by positivity)
  have hs4 : Real.sqrt 2 ^ (4 : ℕ) = (4 : ℝ) := by nlinarith [sq_nonneg (Real.sqrt 2 ^ (2 : ℕ) - 2)]
  simp only [div_pow, hs, hs4]
  ring

/-- Exact conversion of the collective potential to the paper's local-coordinate model. -/
theorem coppoCollectivePotential_rotation (alpha beta xi x y : ℝ) :
    2 * coppoCollectivePotential alpha beta ((x + y) / Real.sqrt 2) ((x - y) / Real.sqrt 2) +
      xi * (x - y) ^ (2 : ℕ) = coppoNonlocalPotential alpha beta xi x y := by
  rw [coppoCollectivePotential, coppoCollective_quadratic, coppoCollective_quartic]
  dsimp [coppoNonlocalPotential]; ring

/-- Exact synchronized-well certificate for the effective nonlocal potential. -/
theorem coppoNonlocalPotential_aligned_square (a beta xi x y : ℝ) :
    coppoNonlocalPotential (2 * beta * a ^ (2 : ℕ)) beta xi x y + 2 * beta * a ^ (4 : ℕ) =
      beta * ((x ^ (2 : ℕ) - a ^ (2 : ℕ)) ^ (2 : ℕ) + (y ^ (2 : ℕ) - a ^ (2 : ℕ)) ^ (2 : ℕ)) + xi * (x - y) ^ (2 : ℕ) := by
  dsimp [coppoNonlocalPotential]; ring

/-- A positive induced coupling selects synchronized global minima. -/
theorem coppoNonlocalPotential_aligned_global_min (a b c x y : ℝ) :
    coppoNonlocalPotential (2 * Real.exp b * a ^ (2 : ℕ)) (Real.exp b) (Real.exp c) a a ≤
      coppoNonlocalPotential (2 * Real.exp b * a ^ (2 : ℕ)) (Real.exp b) (Real.exp c) x y := by
  have h := coppoNonlocalPotential_aligned_square a (Real.exp b) (Real.exp c) x y
  have hmin : coppoNonlocalPotential (2 * Real.exp b * a ^ (2 : ℕ)) (Real.exp b) (Real.exp c) a a =
      -2 * Real.exp b * a ^ (4 : ℕ) := by dsimp [coppoNonlocalPotential]; ring
  rw [hmin]
  have hp : 0 ≤ Real.exp b * ((x ^ (2 : ℕ) - a ^ (2 : ℕ)) ^ (2 : ℕ) + (y ^ (2 : ℕ) - a ^ (2 : ℕ)) ^ (2 : ℕ)) +
      Real.exp c * (x - y) ^ (2 : ℕ) := by positivity
  linarith

/-- Opposite coupling is converted to positive coupling by a sign reversal and exact mass shift. -/
theorem coppoNonlocalPotential_antialigned_transport (alpha beta xi x y : ℝ) :
    coppoNonlocalPotential alpha beta (-xi) x y =
      coppoNonlocalPotential (alpha + 2 * xi) beta xi x (-y) := by
  dsimp [coppoNonlocalPotential]; ring

/-- Negative induced coupling selects antisynchronized wells at its shifted mass. -/
theorem coppoNonlocalPotential_antialigned_global_min (a b c x y : ℝ) :
    coppoNonlocalPotential (2 * Real.exp b * a ^ (2 : ℕ) - 2 * Real.exp c)
        (Real.exp b) (-Real.exp c) a (-a) ≤
      coppoNonlocalPotential (2 * Real.exp b * a ^ (2 : ℕ) - 2 * Real.exp c)
        (Real.exp b) (-Real.exp c) x y := by
  rw [coppoNonlocalPotential_antialigned_transport,
    coppoNonlocalPotential_antialigned_transport]
  simp only [sub_add_cancel, neg_neg]
  exact coppoNonlocalPotential_aligned_global_min a b c x (-y)

/-- Flipping one local amplitude exposes the signed synchronization energy exactly. -/
theorem coppoNonlocalPotential_single_flip (alpha beta xi x y : ℝ) :
    coppoNonlocalPotential alpha beta xi x (-y) - coppoNonlocalPotential alpha beta xi x y =
      4 * xi * x * y := by
  dsimp [coppoNonlocalPotential]; ring

end HTGeometry
