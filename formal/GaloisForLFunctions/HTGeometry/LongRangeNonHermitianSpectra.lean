import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra
import GaloisForLFunctions.HTGeometry.LaurentAnnulus
import GaloisForLFunctions.HTGeometry.FiniteLiouvillianHodgeGreenLaw
import GaloisForLFunctions.HTGeometry.ShiftedGeometricTails
import GaloisForLFunctions.HTGeometry.GeometricTailMass
import GaloisForLFunctions.HTGeometry.GeometricKallenLehmannResponse

/-!
# Long-range non-Hermitian spectral squeezing

Exact formal core extracted from Gu--Fu--Hu--Wang, arXiv:2608.28577.

The paper's asymptotic spectral claims are not asserted here.  This module isolates consequences
that are exact before any thermodynamic or infinitesimal limit is taken:

* projection of log-moduli to the convergence box `[-|α|, |α|]^d`;
* projection to the Euclidean convergence ball for two-norm hopping;
* exhaustive six-way ordering of two roots against the two tail radii;
* reciprocal forward/backward response rates;
* the rational closed form of the two-sided exponential hopping tail on the unit circle;
* factorization of finite two-dimensional one-norm tails;
* persistence of the corpus's exact Hatano--Nelson skin recurrence after squeezing;
* cancellation of affine covariance forcing after subtracting a reference state; and
* conjugate-paired quadratic-Liouvillian subset sums and their `4^N` pattern count.

All statements are unconditional: positivity and annulus bounds are manufactured by the
definitions rather than accepted as theorem premises.
-/

open scoped BigOperators Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Squeezed annulus and convergence domains -/

/-- Inner radius `e^{-|α|}` of the long-range convergence annulus. -/
def longRangeDecayRadius (α : ℝ) : ℝ := Real.exp (-|α|)

/-- Outer radius `e^{|α|}` of the long-range convergence annulus. -/
def longRangeGrowthRadius (α : ℝ) : ℝ := Real.exp |α|

/-- Inner long-range radius is always positive. -/
theorem longRangeDecayRadius_pos (α : ℝ) : 0 < longRangeDecayRadius α := by
  exact Real.exp_pos _

/-- Outer long-range radius is always positive. -/
theorem longRangeGrowthRadius_pos (α : ℝ) : 0 < longRangeGrowthRadius α := by
  exact Real.exp_pos _

/-- Paper's two annulus radii are exact reciprocals. -/
theorem longRangeDecayRadius_mul_growthRadius (α : ℝ) :
    longRangeDecayRadius α * longRangeGrowthRadius α = 1 := by
  rw [longRangeDecayRadius, longRangeGrowthRadius, Real.exp_neg]
  exact inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))

/-- Inner radius never exceeds outer radius, including the zero-width case. -/
theorem longRangeDecayRadius_le_growthRadius (α : ℝ) :
    longRangeDecayRadius α ≤ longRangeGrowthRadius α := by
  rw [longRangeDecayRadius, longRangeGrowthRadius, Real.exp_le_exp]
  linarith [abs_nonneg α]

/-- Squeezing in logarithmic radius: projection to `[-|α|, |α|]`. -/
def squeezedLogModulus (α μ : ℝ) : Set.Icc (-|α|) |α| :=
  Set.projIcc (-|α|) |α| (by linarith [abs_nonneg α]) μ

@[simp] theorem squeezedLogModulus_coe (α μ : ℝ) :
    (squeezedLogModulus α μ : ℝ) = max (-|α|) (min |α| μ) := rfl

/-- Squeezing is the nearest point of the allowed log-radius interval. -/
theorem squeezedLogModulus_minimizes_sq (α μ : ℝ)
    (x : Set.Icc (-|α|) |α|) :
    ((squeezedLogModulus α μ : ℝ) - μ) ^ 2 ≤ ((x : ℝ) - μ) ^ 2 := by
  by_cases hleft : μ ≤ -|α|
  · rw [squeezedLogModulus_coe, min_eq_right (hleft.trans (by linarith [abs_nonneg α])),
      max_eq_left hleft]
    nlinarith [x.property.1]
  · by_cases hright : |α| ≤ μ
    · rw [squeezedLogModulus_coe, min_eq_left hright,
        max_eq_right (by linarith [abs_nonneg α])]
      nlinarith [x.property.2]
    · have hlo : -|α| ≤ μ := le_of_not_ge hleft
      have hhi : μ ≤ |α| := le_of_not_ge hright
      rw [squeezedLogModulus_coe, min_eq_right hhi, max_eq_right hlo]
      simpa using sq_nonneg ((x : ℝ) - μ)

/-- Coordinate box used by the paper's one-norm hopping domain in arbitrary dimension. -/
def SqueezedLogBox (α : ℝ) (d : ℕ) := Fin d → Set.Icc (-|α|) |α|

/-- Coordinatewise projection to the squeezed log-radius box. -/
def squeezeLogBox (α : ℝ) {d : ℕ} (μ : Fin d → ℝ) : SqueezedLogBox α d :=
  fun i => squeezedLogModulus α (μ i)

/-- Squared displacement from an unrestricted log-radius vector. -/
def logBoxSquaredDisplacement (α : ℝ) {d : ℕ}
    (μ : Fin d → ℝ) (x : SqueezedLogBox α d) : ℝ :=
  ∑ i, ((x i : ℝ) - μ i) ^ 2

/-- Coordinatewise squeeze is the nearest point in every finite-dimensional box. -/
theorem squeezeLogBox_minimizes_squaredDisplacement (α : ℝ) {d : ℕ}
    (μ : Fin d → ℝ) (x : SqueezedLogBox α d) :
    logBoxSquaredDisplacement α μ (squeezeLogBox α μ) ≤
      logBoxSquaredDisplacement α μ x := by
  apply Finset.sum_le_sum
  intro i _
  exact squeezedLogModulus_minimizes_sq α (μ i) (x i)

/-- Radial projection to the ball of radius `|α|`, the convergence domain for two-norm hopping. -/
def squeezeToClosedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (v : E) : E :=
  if ‖v‖ ≤ |α| then v else (|α| / ‖v‖) • v

/-- Radial squeeze always lies in the required closed ball. -/
theorem norm_squeezeToClosedBall_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (v : E) : ‖squeezeToClosedBall α v‖ ≤ |α| := by
  by_cases h : ‖v‖ ≤ |α|
  · simp [squeezeToClosedBall, h]
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_lt (abs_nonneg α) (lt_of_not_ge h)
    rw [squeezeToClosedBall, if_neg h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (abs_nonneg α) hvpos.le), div_mul_cancel₀ _ (ne_of_gt hvpos)]

/-- Radial squeezing is idempotent. -/
theorem squeezeToClosedBall_idempotent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ) (v : E) :
    squeezeToClosedBall α (squeezeToClosedBall α v) = squeezeToClosedBall α v := by
  rw [squeezeToClosedBall, if_pos (norm_squeezeToClosedBall_le α v)]

/-- Root modulus projected to the paper's convergence annulus. -/
def squeezedRootModulus (α r : ℝ) :
    Set.Icc (longRangeDecayRadius α) (longRangeGrowthRadius α) :=
  Set.projIcc (longRangeDecayRadius α) (longRangeGrowthRadius α)
    (longRangeDecayRadius_le_growthRadius α) r

@[simp] theorem squeezedRootModulus_coe (α r : ℝ) :
    (squeezedRootModulus α r : ℝ) =
      max (longRangeDecayRadius α) (min (longRangeGrowthRadius α) r) := rfl

/-- Every squeezed root modulus remains strictly positive. -/
theorem squeezedRootModulus_pos (α r : ℝ) :
    0 < (squeezedRootModulus α r : ℝ) :=
  (longRangeDecayRadius_pos α).trans_le (squeezedRootModulus α r).property.1

/-! ## Table 1: root ordering and directional response -/

/-- Lower of the two middle-root moduli. -/
def lowerOrderedRoot (r s : ℝ) : ℝ := min r s

/-- Upper of the two middle-root moduli. -/
def upperOrderedRoot (r s : ℝ) : ℝ := max r s

/-- Forward Green-function exponential base after squeezing. -/
def forwardGreenRate (α r s : ℝ) : ℝ :=
  squeezedRootModulus α (lowerOrderedRoot r s)

/-- Backward Green-function exponential base before taking the reciprocal power. -/
def backwardGreenRate (α r s : ℝ) : ℝ :=
  squeezedRootModulus α (upperOrderedRoot r s)

/-- The six rows of the paper's Green-function table exhaust all possible relative orders. -/
theorem six_root_arrangements (α r s : ℝ) :
    let b₂ := lowerOrderedRoot r s
    let b₃ := upperOrderedRoot r s
    let lo := longRangeDecayRadius α
    let hi := longRangeGrowthRadius α
    (lo ≤ b₂ ∧ b₂ ≤ b₃ ∧ b₃ ≤ hi) ∨
    (b₂ ≤ lo ∧ lo ≤ hi ∧ hi ≤ b₃) ∨
    (b₂ ≤ lo ∧ lo ≤ b₃ ∧ b₃ ≤ hi) ∨
    (lo ≤ b₂ ∧ b₂ ≤ hi ∧ hi ≤ b₃) ∨
    (b₂ ≤ b₃ ∧ b₃ ≤ lo ∧ lo ≤ hi) ∨
    (lo ≤ hi ∧ hi ≤ b₂ ∧ b₂ ≤ b₃) := by
  dsimp [lowerOrderedRoot, upperOrderedRoot]
  have h23 : min r s ≤ max r s := min_le_max
  have hlh := longRangeDecayRadius_le_growthRadius α
  by_cases hE : max r s ≤ longRangeDecayRadius α
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h23, hE, hlh⟩))))
  · by_cases hF : longRangeGrowthRadius α ≤ min r s
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hlh, hF, h23⟩))))
    · by_cases h2 : min r s ≤ longRangeDecayRadius α
      · by_cases h3 : longRangeGrowthRadius α ≤ max r s
        · exact Or.inr (Or.inl ⟨h2, hlh, h3⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h2, le_of_not_ge hE, le_of_not_ge h3⟩))
      · by_cases h3 : longRangeGrowthRadius α ≤ max r s
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨le_of_not_ge h2, le_of_not_ge hF, h3⟩)))
        · exact Or.inl ⟨le_of_not_ge h2, h23, le_of_not_ge h3⟩

/-- Both directional response rates remain in the long-range annulus. -/
theorem greenRate_bounds (α r s : ℝ) :
    longRangeDecayRadius α ≤ forwardGreenRate α r s ∧
      forwardGreenRate α r s ≤ longRangeGrowthRadius α ∧
    longRangeDecayRadius α ≤ backwardGreenRate α r s ∧
      backwardGreenRate α r s ≤ longRangeGrowthRadius α := by
  exact ⟨(squeezedRootModulus α (lowerOrderedRoot r s)).property.1,
    (squeezedRootModulus α (lowerOrderedRoot r s)).property.2,
    (squeezedRootModulus α (upperOrderedRoot r s)).property.1,
    (squeezedRootModulus α (upperOrderedRoot r s)).property.2⟩

/-- Table 1 with the corresponding clipped Green-function rates in every order regime. -/
theorem six_green_rate_cases (α r s : ℝ) :
    let b₂ := lowerOrderedRoot r s
    let b₃ := upperOrderedRoot r s
    let lo := longRangeDecayRadius α
    let hi := longRangeGrowthRadius α
    (lo ≤ b₂ ∧ b₂ ≤ b₃ ∧ b₃ ≤ hi ∧
      forwardGreenRate α r s = b₂ ∧ backwardGreenRate α r s = b₃) ∨
    (b₂ ≤ lo ∧ lo ≤ hi ∧ hi ≤ b₃ ∧
      forwardGreenRate α r s = lo ∧ backwardGreenRate α r s = hi) ∨
    (b₂ ≤ lo ∧ lo ≤ b₃ ∧ b₃ ≤ hi ∧
      forwardGreenRate α r s = lo ∧ backwardGreenRate α r s = b₃) ∨
    (lo ≤ b₂ ∧ b₂ ≤ hi ∧ hi ≤ b₃ ∧
      forwardGreenRate α r s = b₂ ∧ backwardGreenRate α r s = hi) ∨
    (b₂ ≤ b₃ ∧ b₃ ≤ lo ∧ lo ≤ hi ∧
      forwardGreenRate α r s = lo ∧ backwardGreenRate α r s = lo) ∨
    (lo ≤ hi ∧ hi ≤ b₂ ∧ b₂ ≤ b₃ ∧
      forwardGreenRate α r s = hi ∧ backwardGreenRate α r s = hi) := by
  dsimp only
  rcases six_root_arrangements α r s with hA | hB | hC | hD | hE | hF
  · rcases hA with ⟨hlo2, h23, h3hi⟩
    have hf : forwardGreenRate α r s = lowerOrderedRoot r s := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (lowerOrderedRoot r s)) = lowerOrderedRoot r s
      rw [min_eq_right (h23.trans h3hi), max_eq_right hlo2]
    have hb : backwardGreenRate α r s = upperOrderedRoot r s := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (upperOrderedRoot r s)) = upperOrderedRoot r s
      rw [min_eq_right h3hi, max_eq_right (hlo2.trans h23)]
    exact Or.inl ⟨hlo2, h23, h3hi, hf, hb⟩
  · rcases hB with ⟨h2lo, hlohi, hhi3⟩
    have hf : forwardGreenRate α r s = longRangeDecayRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (lowerOrderedRoot r s)) = longRangeDecayRadius α
      rw [min_eq_right (h2lo.trans hlohi), max_eq_left h2lo]
    have hb : backwardGreenRate α r s = longRangeGrowthRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (upperOrderedRoot r s)) = longRangeGrowthRadius α
      rw [min_eq_left hhi3, max_eq_right hlohi]
    exact Or.inr (Or.inl ⟨h2lo, hlohi, hhi3, hf, hb⟩)
  · rcases hC with ⟨h2lo, hlo3, h3hi⟩
    have hf : forwardGreenRate α r s = longRangeDecayRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (lowerOrderedRoot r s)) = longRangeDecayRadius α
      rw [min_eq_right (h2lo.trans (longRangeDecayRadius_le_growthRadius α)),
        max_eq_left h2lo]
    have hb : backwardGreenRate α r s = upperOrderedRoot r s := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (upperOrderedRoot r s)) = upperOrderedRoot r s
      rw [min_eq_right h3hi, max_eq_right hlo3]
    exact Or.inr (Or.inr (Or.inl ⟨h2lo, hlo3, h3hi, hf, hb⟩))
  · rcases hD with ⟨hlo2, h2hi, hhi3⟩
    have hf : forwardGreenRate α r s = lowerOrderedRoot r s := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (lowerOrderedRoot r s)) = lowerOrderedRoot r s
      rw [min_eq_right h2hi, max_eq_right hlo2]
    have hb : backwardGreenRate α r s = longRangeGrowthRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (upperOrderedRoot r s)) = longRangeGrowthRadius α
      rw [min_eq_left hhi3, max_eq_right (longRangeDecayRadius_le_growthRadius α)]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hlo2, h2hi, hhi3, hf, hb⟩)))
  · rcases hE with ⟨h23, h3lo, hlohi⟩
    have hf : forwardGreenRate α r s = longRangeDecayRadius α := by
      have h2lo := h23.trans h3lo
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (lowerOrderedRoot r s)) = longRangeDecayRadius α
      rw [min_eq_right (h2lo.trans hlohi), max_eq_left h2lo]
    have hb : backwardGreenRate α r s = longRangeDecayRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (upperOrderedRoot r s)) = longRangeDecayRadius α
      rw [min_eq_right (h3lo.trans hlohi), max_eq_left h3lo]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h23, h3lo, hlohi, hf, hb⟩))))
  · rcases hF with ⟨hlohi, hhi2, h23⟩
    have hf : forwardGreenRate α r s = longRangeGrowthRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (lowerOrderedRoot r s)) = longRangeGrowthRadius α
      rw [min_eq_left hhi2, max_eq_right hlohi]
    have hb : backwardGreenRate α r s = longRangeGrowthRadius α := by
      change max (longRangeDecayRadius α)
        (min (longRangeGrowthRadius α) (upperOrderedRoot r s)) = longRangeGrowthRadius α
      rw [min_eq_left (hhi2.trans h23), max_eq_right hlohi]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hlohi, hhi2, h23, hf, hb⟩))))

/-- Opposite directional powers at one squeezed rate cancel exactly. -/
def pairedDirectionalGain (α r : ℝ) (L : ℕ) : ℝ :=
  (squeezedRootModulus α r : ℝ) ^ L *
    ((squeezedRootModulus α r : ℝ)⁻¹) ^ L

theorem pairedDirectionalGain_eq_one (α r : ℝ) (L : ℕ) :
    pairedDirectionalGain α r L = 1 := by
  rw [pairedDirectionalGain, ← mul_pow,
    mul_inv_cancel₀ (ne_of_gt (squeezedRootModulus_pos α r)), one_pow]

/-! ## Exact exponential tails -/

/-- Strict geometric ratio used for premise-free convergence statements. -/
def strictLongRangeRatio (α : ℝ) : ℝ := Real.exp (-(|α| + 1))

theorem strictLongRangeRatio_pos (α : ℝ) : 0 < strictLongRangeRatio α :=
  Real.exp_pos _

theorem strictLongRangeRatio_lt_one (α : ℝ) : strictLongRangeRatio α < 1 := by
  rw [strictLongRangeRatio, Real.exp_lt_one_iff]
  linarith [abs_nonneg α]

/-- Unit-modulus generalized Bloch factor on the periodic Brillouin zone. -/
def unitBlochFactor (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

@[simp] theorem norm_unitBlochFactor (θ : ℝ) : ‖unitBlochFactor θ‖ = 1 := by
  rw [unitBlochFactor, Complex.norm_exp]
  simp

/-- One term of the paper's symmetric exponentially decaying hopping tail. -/
def longRangeTailTerm (α θ : ℝ) (n : ℕ) : ℂ :=
  let q : ℂ := strictLongRangeRatio α
  let β := unitBlochFactor θ
  (q * β) ^ (n + 1) + (q * β⁻¹) ^ (n + 1)

/-- Two-pole rational form of the long-range tail. -/
def longRangeTailClosedForm (α θ : ℝ) : ℂ :=
  let q : ℂ := strictLongRangeRatio α
  let β := unitBlochFactor θ
  q * β * (1 - q * β)⁻¹ + q * β⁻¹ * (1 - q * β⁻¹)⁻¹

/-- Equation (3): the two-sided hopping tail sums to its exact two-pole rational form. -/
theorem hasSum_longRangeTailTerm (α θ : ℝ) :
    HasSum (longRangeTailTerm α θ) (longRangeTailClosedForm α θ) := by
  let q : ℂ := strictLongRangeRatio α
  let β := unitBlochFactor θ
  have hqnorm : ‖q * β‖ < 1 := by
    rw [norm_mul, show ‖q‖ = strictLongRangeRatio α by
      simp [q, abs_of_pos (strictLongRangeRatio_pos α)], norm_unitBlochFactor, mul_one]
    exact strictLongRangeRatio_lt_one α
  have hqinvnorm : ‖q * β⁻¹‖ < 1 := by
    rw [norm_mul, show ‖q‖ = strictLongRangeRatio α by
      simp [q, abs_of_pos (strictLongRangeRatio_pos α)], norm_inv,
      norm_unitBlochFactor, inv_one, mul_one]
    exact strictLongRangeRatio_lt_one α
  have hforward : HasSum (fun n : ℕ => (q * β) ^ (n + 1))
      (q * β * (1 - q * β)⁻¹) := by
    simpa [pow_succ'] using (hasSum_geometric_of_norm_lt_one hqnorm).mul_left (q * β)
  have hbackward : HasSum (fun n : ℕ => (q * β⁻¹) ^ (n + 1))
      (q * β⁻¹ * (1 - q * β⁻¹)⁻¹) := by
    simpa [pow_succ'] using (hasSum_geometric_of_norm_lt_one hqinvnorm).mul_left (q * β⁻¹)
  change HasSum (fun n : ℕ => (q * β) ^ (n + 1) + (q * β⁻¹) ^ (n + 1))
    (q * β * (1 - q * β)⁻¹ + q * β⁻¹ * (1 - q * β⁻¹)⁻¹)
  exact hforward.add hbackward

theorem tsum_longRangeTailTerm (α θ : ℝ) :
    ∑' n, longRangeTailTerm α θ n = longRangeTailClosedForm α θ :=
  (hasSum_longRangeTailTerm α θ).tsum_eq

/-- Existing Laurent-annulus tail theorem specialized to the strict long-range ratio. -/
theorem scalar_longRangeTail_eq (α : ℝ) (N : ℕ) :
    ∑' k : ℕ, strictLongRangeRatio α ^ (N + k) =
      strictLongRangeRatio α ^ N * (1 - strictLongRangeRatio α)⁻¹ := by
  simpa only [add_comm, div_eq_mul_inv] using tsum_geometric_tail
    (le_of_lt (strictLongRangeRatio_pos α)) (strictLongRangeRatio_lt_one α) N

/-- Shifted hopping tail, reusing the corpus's exact Wiman--Valiron geometric-tail identity. -/
theorem shiftedLongRangeTail_eq (α : ℝ) (N : ℕ) :
    ∑' j : ℕ, strictLongRangeRatio α ^ (N + 1 + j) =
      strictLongRangeRatio α ^ (N + 1) / (1 - strictLongRangeRatio α) :=
  tsum_shifted_geom (le_of_lt (strictLongRangeRatio_pos α))
    (strictLongRangeRatio_lt_one α) N

/-- Squared hopping-distance moment obeys the corpus's shifted geometric bound. -/
theorem shiftedLongRangeSecondMoment_le (α : ℝ) (N : ℕ) :
    ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ 2 * strictLongRangeRatio α ^ (N + 1 + j) ≤
      2 * ((N : ℝ) + 1) ^ 2 * strictLongRangeRatio α ^ (N + 1) /
        (1 - strictLongRangeRatio α) ^ 3 :=
  tsum_shifted_sq_weight_le (strictLongRangeRatio_pos α)
    (strictLongRangeRatio_lt_one α) N

/-- Success parameter whose failure probability is the strict long-range hopping ratio. -/
def longRangeSuccessProbability (α : ℝ) : unitInterval :=
  ⟨1 - strictLongRangeRatio α, by
    constructor
    · linarith [strictLongRangeRatio_lt_one α]
    · linarith [strictLongRangeRatio_pos α]⟩

theorem longRangeSuccessProbability_ne_zero (α : ℝ) :
    longRangeSuccessProbability α ≠ 0 := by
  intro h
  have hval := congrArg ((↑) : unitInterval → ℝ) h
  simp [longRangeSuccessProbability] at hval
  linarith [strictLongRangeRatio_lt_one α]

/-- Hopping beyond distance `m` has exact geometric probability mass `q^m`. -/
theorem geometricMeasure_longRangeTail (α : ℝ) (m : ℕ) :
    ProbabilityTheory.geometricMeasure (longRangeSuccessProbability α) {k : ℕ | m ≤ k} =
      ENNReal.ofReal (strictLongRangeRatio α ^ m) := by
  simpa [longRangeSuccessProbability] using
    geometricMeasure_Ici (longRangeSuccessProbability_ne_zero α) m

/-- Corpus geometric spectral moments specialized to the long-range hopping ratio. -/
theorem longRangeGeometricMoment_eq_tsum (α : ℝ) (n : ℕ) :
    _root_.HTGeometry.geometricKallenLehmannMoment
        (strictLongRangeRatio α) (strictLongRangeRatio α) n =
      ∑' k : ℕ, _root_.HTGeometry.geometricKallenLehmannWeight
          (strictLongRangeRatio α) k *
        _root_.HTGeometry.geometricKallenLehmannNode (strictLongRangeRatio α) k ^ n := by
  exact _root_.HTGeometry.geometricKallenLehmannMoment_eq_tsum
    (le_of_lt (strictLongRangeRatio_pos α)) (strictLongRangeRatio_lt_one α)
    (le_of_lt (strictLongRangeRatio_pos α)) (le_of_lt (strictLongRangeRatio_lt_one α)) n

/-- Long-range ratio turns the corpus mass-resolvent into an exact self-similar response. -/
theorem longRangeGeometricResponse_selfSimilarity (α : ℝ) :
    _root_.HTGeometry.geometricKallenLehmannResponse
        (strictLongRangeRatio α) (strictLongRangeRatio α) =
      (1 - strictLongRangeRatio α) • (PowerSeries.invOneSubPow ℝ 1).val +
        strictLongRangeRatio α • PowerSeries.rescale (strictLongRangeRatio α)
          (_root_.HTGeometry.geometricKallenLehmannResponse (strictLongRangeRatio α)
            (strictLongRangeRatio α)) := by
  exact _root_.HTGeometry.geometricKallenLehmannResponse_selfSimilarity
    (le_of_lt (strictLongRangeRatio_pos α)) (strictLongRangeRatio_lt_one α)
    (le_of_lt (strictLongRangeRatio_pos α)) (le_of_lt (strictLongRangeRatio_lt_one α))

/-- One coordinate of a finite one-norm hopping tail. -/
def l1AxisTailTerm (q : ℂ) (β : ℂˣ) (n : ℤ) : ℂ :=
  q ^ n.natAbs * ((β ^ n : ℂˣ) : ℂ)

/-- One term of the paper's two-dimensional Manhattan-distance hopping. -/
def l1LongRangeTerm (q : ℂ) (βx βy : ℂˣ) (n m : ℤ) : ℂ :=
  q ^ (n.natAbs + m.natAbs) * ((βx ^ n : ℂˣ) : ℂ) * ((βy ^ m : ℂˣ) : ℂ)

/-- Equation (7): every finite rectangular one-norm tail factors into its two axis tails. -/
theorem finite_l1LongRange_factorization (q : ℂ) (βx βy : ℂˣ)
    (I J : Finset ℤ) :
    ∑ n ∈ I, ∑ m ∈ J, l1LongRangeTerm q βx βy n m =
      (∑ n ∈ I, l1AxisTailTerm q βx n) *
        (∑ m ∈ J, l1AxisTailTerm q βy m) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [l1LongRangeTerm, l1AxisTailTerm, pow_add]
  ring

/-! ## Applications to corpus skin modes and Liouvillians -/

/-- Existing exact Hatano--Nelson sine mode evaluated at the squeezed radius. -/
def squeezedSkinSineMode (α r k : ℝ) (n : ℕ) : ℝ :=
  RabiHatanoNelson.skinSineMode (squeezedRootModulus α r) k n

/-- Squeezing preserves the corpus's exact asymmetric nearest-neighbour recurrence. -/
theorem squeezedSkinSineMode_recurrence (α s r k : ℝ) (n : ℕ) :
    (s * (squeezedRootModulus α r : ℝ) ^ 2) * squeezedSkinSineMode α r k n +
        s * squeezedSkinSineMode α r k (n + 2) =
      (2 * s * (squeezedRootModulus α r : ℝ) * Real.cos k) *
        squeezedSkinSineMode α r k (n + 1) := by
  exact RabiHatanoNelson.skinSineMode_recurrence s (squeezedRootModulus α r) k n

/-- Affine covariance drift from the paper's quadratic Lindblad equation. -/
def covarianceDrift {n : Type*} [Fintype n]
    (X M Δ : Matrix n n ℂ) : Matrix n n ℂ :=
  X * Δ + Δ * Xᴴ + (M + M)

/-- Homogeneous drift of a covariance deviation. -/
def covarianceDeviationDrift {n : Type*} [Fintype n]
    (X Δ : Matrix n n ℂ) : Matrix n n ℂ :=
  X * Δ + Δ * Xᴴ

/-- Equations (12)--(13): subtracting a reference covariance cancels affine forcing exactly. -/
theorem covarianceDrift_sub_eq_deviationDrift {n : Type*} [Fintype n]
    (X M Δ Δs : Matrix n n ℂ) :
    covarianceDrift X M Δ - covarianceDrift X M Δs =
      covarianceDeviationDrift X (Δ - Δs) := by
  unfold covarianceDrift covarianceDeviationDrift
  noncomm_ring

/-- Existing finite transition energies projected to the paper's squeeze interval. -/
def squeezedTransitionEnergy {ι : Type*} (α : ℝ) (energy : ι → ℝ) : ι → ℝ :=
  fun i => squeezedLogModulus α (energy i)

/-- Corpus Hodge--Green decomposition remains exact after spectral squeezing. -/
theorem squeezedTransitionGap_hodgeGreen_decomposition
    {ι : Type*} [Fintype ι] (α : ℝ) (energy : ι → ℝ)
    (x : EuclideanSpace ℂ (ι × ι)) :
    _root_.HTGeometry.transitionGapStationaryPart (squeezedTransitionEnergy α energy) x +
        _root_.HTGeometry.transitionGapLiouvillian (squeezedTransitionEnergy α energy)
          (_root_.HTGeometry.transitionGapGreenPrimitive
            (squeezedTransitionEnergy α energy) x) = x :=
  _root_.HTGeometry.transitionGap_hodgeGreen_decomposition
    (squeezedTransitionEnergy α energy) x

/-- Spectral squeezing preserves the exact self-adjoint finite transition Liouvillian. -/
theorem squeezedTransitionGapLiouvillian_isSelfAdjoint
    {ι : Type*} [Fintype ι] (α : ℝ) (energy : ι → ℝ) :
    IsSelfAdjoint
      (_root_.HTGeometry.transitionGapLiouvillian (squeezedTransitionEnergy α energy)) :=
  _root_.HTGeometry.transitionGapLiouvillian_isSelfAdjoint
    (squeezedTransitionEnergy α energy)

/-- Every energy difference after squeezing has magnitude at most twice the tail exponent. -/
theorem abs_squeezedTransitionEnergy_sub_le
    {ι : Type*} (α : ℝ) (energy : ι → ℝ) (i j : ι) :
    |squeezedTransitionEnergy α energy i - squeezedTransitionEnergy α energy j| ≤
      2 * |α| := by
  change |(squeezedLogModulus α (energy i) : ℝ) -
    (squeezedLogModulus α (energy j) : ℝ)| ≤ 2 * |α|
  rw [abs_le]
  constructor <;>
    linarith [(squeezedLogModulus α (energy i)).property.1,
      (squeezedLogModulus α (energy i)).property.2,
      (squeezedLogModulus α (energy j)).property.1,
      (squeezedLogModulus α (energy j)).property.2]

/-- Automatically nonnegative and symmetric finite transition intensity. -/
def symmetricSquaredTransitionIntensity {ι : Type*}
    (amplitude : ι → ι → ℝ) (i j : ι) : ℝ :=
  amplitude i j ^ 2 + amplitude j i ^ 2

/-- Corpus response-moment sum rule after long-range spectral squeezing. -/
theorem squeezedTransition_responseMoment_sumRule
    {ι : Type*} [Fintype ι]
    (α : ℝ) (energy : ι → ℝ) (amplitude : ι → ι → ℝ) (n : ℕ) :
    inner ℂ (_root_.HTGeometry.thermalTransitionVector
      (symmetricSquaredTransitionIntensity amplitude))
      (((_root_.HTGeometry.transitionGapLiouvillian
        (squeezedTransitionEnergy α energy)) ^ n)
          (_root_.HTGeometry.thermalTransitionVector
            (symmetricSquaredTransitionIntensity amplitude))) =
      (_root_.HTGeometry.thermalGapMoment
        (symmetricSquaredTransitionIntensity amplitude)
        (squeezedTransitionEnergy α energy) n : ℂ) := by
  apply _root_.HTGeometry.inner_transitionVector_pow_gapLiouvillian
  intro i j
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- Symmetric squared transition data annihilate every odd squeezed Liouvillian moment. -/
theorem squeezedTransition_oddResponseMoment_eq_zero
    {ι : Type*} [Fintype ι]
    (α : ℝ) (energy : ι → ℝ) (amplitude : ι → ι → ℝ) (n : ℕ) :
    inner ℂ (_root_.HTGeometry.thermalTransitionVector
      (symmetricSquaredTransitionIntensity amplitude))
      (((_root_.HTGeometry.transitionGapLiouvillian
        (squeezedTransitionEnergy α energy)) ^ (2 * n + 1))
          (_root_.HTGeometry.thermalTransitionVector
            (symmetricSquaredTransitionIntensity amplitude))) = 0 := by
  apply _root_.HTGeometry.inner_transitionVector_pow_gapLiouvillian_eq_zero_of_odd
  · intro i j
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro i j
    simp only [symmetricSquaredTransitionIntensity]
    ac_rfl
  · exact odd_two_mul_add_one n

/-! ## Quadratic-Liouvillian rapidity spectrum -/

/-- Particle/hole binary occupation pattern for `N` rapidities. -/
abbrev QuadraticOccupation (N : ℕ) :=
  (Fin N → Bool) × (Fin N → Bool)

/-- Equation (18): subset sum of rapidities and their conjugates. -/
def quadraticLiouvillianEigenvalue {N : ℕ} (x : Fin N → ℂ)
    (occupation : QuadraticOccupation N) : ℂ :=
  (∑ i, if occupation.1 i then x i else 0) +
    ∑ i, if occupation.2 i then conj (x i) else 0

/-- Particle/hole swap implementing conjugation on occupation patterns. -/
def conjugateOccupation {N : ℕ} (occupation : QuadraticOccupation N) :
    QuadraticOccupation N := (occupation.2, occupation.1)

/-- Empty occupation gives the paper's stationary eigenvalue `0`. -/
theorem quadraticLiouvillianEigenvalue_empty {N : ℕ} (x : Fin N → ℂ) :
    quadraticLiouvillianEigenvalue x ((fun _ => false), (fun _ => false)) = 0 := by
  simp [quadraticLiouvillianEigenvalue]

private theorem conj_sum_ite {ι : Type*} [Fintype ι]
    (p : ι → Bool) (f : ι → ℂ) :
    conj (∑ i, if p i then f i else 0) =
      ∑ i, if p i then conj (f i) else 0 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i <;> simp [h]

/-- The subset-sum spectrum is closed under complex conjugation. -/
theorem quadraticLiouvillianEigenvalue_conjugate {N : ℕ} (x : Fin N → ℂ)
    (occupation : QuadraticOccupation N) :
    quadraticLiouvillianEigenvalue x (conjugateOccupation occupation) =
      conj (quadraticLiouvillianEigenvalue x occupation) := by
  simp only [quadraticLiouvillianEigenvalue, conjugateOccupation, map_add,
    conj_sum_ite, Complex.conj_conj]
  ac_rfl

/-- Equation (18) has exactly `4^N` binary occupation patterns. -/
theorem card_quadraticOccupation (N : ℕ) :
    Fintype.card (QuadraticOccupation N) = 4 ^ N := by
  simp only [QuadraticOccupation, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [show 4 = 2 * 2 by norm_num, mul_pow]

end GaloisForLFunctions.HTGeometry
