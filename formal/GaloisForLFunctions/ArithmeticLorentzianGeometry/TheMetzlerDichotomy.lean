import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexTricklesDown

/-!
# The Metzler dichotomy

Let `Q` be a symmetric Metzler form (nonnegative off-diagonal entries, arbitrary diagonal) and
`π > 0` a positive weight. Conjugating by `diag π` turns the row sums into `π_i (Qπ)_i`, and the
graph Laplacian identity becomes

    Σ_i (Qπ)_i/π_i · v_i² − Q[v] = ½ Σ_{j,k} Q_jk π_j π_k (v_j/π_j − v_k/π_k)²
                                                              (`sum_weighted_sub_qf`).

The sign of `Qπ` splits the Metzler forms into two regimes.

* **Stability regime** (`qf_nonpos_of_mulVec_nonpos`): if `Qπ ≤ 0` for some `π > 0`, then `Q` is
  negative semidefinite. This is the shape of every unconditional positivity of Weil's form at
  atomic resolution: the self-energy on the diagonal pays the row sums of the off-diagonal kernel
  (the stability law of ArithmeticElectrostatics is the statement that the atom block of the
  intersection form has nonpositive weighted row sums below the atomic width).
* **Trickle-down regime** (`isHyperbolic_iff_weightedTrickleDown`): if `Qπ > 0` and the support is
  connected, then `Q` has one positive square iff

      Q[v] ≤ Σ_i π_i (Qv)_i² / (Qπ)_i                                     (TD_π).

  The weight `π` is free: any positive vector with positive image certifies the regime.

Hyperbolicity is invariant under the diagonal congruence (`isHyperbolic_diagConj_iff`), so the
weighted statements follow from the unweighted ones of `TheHodgeIndexTricklesDown`.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal congruence `diag(π) Q diag(π)`. -/
def diagConj (π : ι → ℝ) (Q : Matrix ι ι ℝ) : Matrix ι ι ℝ := diagonal π * Q * diagonal π

theorem diagConj_apply (π : ι → ℝ) (Q : Matrix ι ι ℝ) (j k : ι) :
    diagConj π Q j k = π j * Q j k * π k := by
  simp [diagConj, mul_apply, diagonal_apply, Finset.sum_ite_eq', mul_comm]

theorem diagConj_eq_pullback (π : ι → ℝ) (Q : Matrix ι ι ℝ) :
    diagConj π Q = (diagonal π)ᵀ * Q * diagonal π := by
  rw [diagConj, diagonal_transpose]

theorem diagConj_isSymm {π : ι → ℝ} {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) : (diagConj π Q).IsSymm :=
  Matrix.IsSymm.ext fun j k => by
    rw [diagConj_apply, diagConj_apply, hQ.apply j k]; ring

theorem diagConj_isMetzler {π : ι → ℝ} (hπ : ∀ i, 0 < π i) {Q : Matrix ι ι ℝ}
    (hM : IsMetzler Q) : IsMetzler (diagConj π Q) := fun j k hjk => by
  rw [diagConj_apply]; exact mul_nonneg (mul_nonneg (hπ j).le (hM j k hjk)) (hπ k).le

theorem diagConj_isConnectedSupport {π : ι → ℝ} (hπ : ∀ i, 0 < π i) {Q : Matrix ι ι ℝ}
    (hc : IsConnectedSupport Q) : IsConnectedSupport (diagConj π Q) := fun w hw =>
  hc w fun j k hjk => hw j k (by
    rw [diagConj_apply]; exact mul_ne_zero (mul_ne_zero (hπ j).ne' hjk) (hπ k).ne')

theorem rowSum_diagConj (π : ι → ℝ) (Q : Matrix ι ι ℝ) (i : ι) :
    rowSum (diagConj π Q) i = π i * (Q *ᵥ π) i := by
  simp only [rowSum, mulVec, dotProduct, Pi.one_apply, mul_one, diagConj_apply, mul_sum]
  exact sum_congr rfl fun k _ => by ring

theorem mulVec_diagConj (π : ι → ℝ) (Q : Matrix ι ι ℝ) (w : ι → ℝ) (i : ι) :
    (diagConj π Q *ᵥ w) i = π i * (Q *ᵥ (fun k => π k * w k)) i := by
  simp only [mulVec, dotProduct, diagConj_apply, mul_sum]
  exact sum_congr rfl fun k _ => by ring

theorem qf_diagConj (π : ι → ℝ) (Q : Matrix ι ι ℝ) (w : ι → ℝ) :
    qf (diagConj π Q) w = qf Q (fun k => π k * w k) := by
  rw [diagConj_eq_pullback, qf, bil_pullback, qf]
  congr 1 <;> ext k <;> simp [mulVec_diagonal]

/-- Hyperbolicity is invariant under the diagonal congruence by a nowhere-zero weight. -/
theorem isHyperbolic_diagConj_iff {π : ι → ℝ} (hπ : ∀ i, π i ≠ 0) {Q : Matrix ι ι ℝ} :
    IsHyperbolic (diagConj π Q) ↔ IsHyperbolic Q := by
  refine ⟨fun h => ?_, fun h => by rw [diagConj_eq_pullback]; exact h.pullback _⟩
  have := h.pullback (diagonal fun i => (π i)⁻¹)
  have e : (diagonal fun i => (π i)⁻¹)ᵀ * diagConj π Q * diagonal (fun i => (π i)⁻¹) = Q := by
    ext j k
    simp only [diagonal_transpose, mul_apply, diagonal_apply, diagConj_apply, ite_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true, mul_ite, mul_zero, sum_ite_eq']
    field_simp [hπ j, hπ k]
  rwa [e] at this

/-! ### The weighted Laplacian and the stability regime -/

/-- **The weighted Laplacian identity.** -/
theorem sum_weighted_sub_qf {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) {π : ι → ℝ} (hπ : ∀ i, π i ≠ 0)
    (v : ι → ℝ) :
    ∑ i, (Q *ᵥ π) i / π i * v i ^ 2 - qf Q v =
      (1 / 2) * ∑ j, ∑ k, π j * Q j k * π k * (v j / π j - v k / π k) ^ 2 := by
  have h := sum_rowSum_mul_sq_sub_qf (diagConj_isSymm (π := π) hQ) (fun i => v i / π i)
  have hv : (fun k => π k * (v k / π k)) = v := funext fun k => by field_simp [hπ k]
  rw [qf_diagConj, hv] at h
  simp only [rowSum_diagConj, diagConj_apply] at h
  rw [← h]
  congr 1
  exact sum_congr rfl fun i _ => by field_simp [hπ i]

/-- **The stability regime.** A Metzler form with `Qπ ≤ 0` for a positive weight `π` is negative
semidefinite: the diagonal pays the weighted row sums. -/
theorem qf_nonpos_of_mulVec_nonpos {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hM : IsMetzler Q)
    {π : ι → ℝ} (hπ : ∀ i, 0 < π i) (hneg : ∀ i, (Q *ᵥ π) i ≤ 0) (v : ι → ℝ) : qf Q v ≤ 0 := by
  have h := sum_weighted_sub_qf hQ (fun i => (hπ i).ne') v
  have h1 : ∑ i, (Q *ᵥ π) i / π i * v i ^ 2 ≤ 0 := sum_nonpos fun i _ =>
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (hneg i) (hπ i).le)
      (sq_nonneg _)
  have h2 : 0 ≤ ∑ j, ∑ k, π j * Q j k * π k * (v j / π j - v k / π k) ^ 2 :=
    sum_nonneg fun j _ => sum_nonneg fun k _ => by
      rcases eq_or_ne j k with rfl | hjk
      · simp
      · exact mul_nonneg (mul_nonneg (mul_nonneg (hπ j).le (hM j k hjk)) (hπ k).le)
          (sq_nonneg _)
  linarith

/-! ### The trickle-down regime -/

/-- **The weighted trickle-down inequality** `Q[v] ≤ Σ_i π_i (Qv)_i² / (Qπ)_i`. -/
def WeightedTrickleDown (π : ι → ℝ) (Q : Matrix ι ι ℝ) : Prop :=
  ∀ v, qf Q v ≤ ∑ i, π i * (Q *ᵥ v) i ^ 2 / (Q *ᵥ π) i

theorem trickleDownIneq_diagConj_iff {π : ι → ℝ} (hπ : ∀ i, 0 < π i) {Q : Matrix ι ι ℝ} :
    TrickleDownIneq (diagConj π Q) ↔ WeightedTrickleDown π Q := by
  have hrw : ∀ w : ι → ℝ, ∑ i, (diagConj π Q *ᵥ w) i ^ 2 / rowSum (diagConj π Q) i =
      ∑ i, π i * (Q *ᵥ fun k => π k * w k) i ^ 2 / (Q *ᵥ π) i := fun w =>
    sum_congr rfl fun i _ => by
      rw [mulVec_diagConj, rowSum_diagConj]
      have := (hπ i).ne'
      rcases eq_or_ne ((Q *ᵥ π) i) 0 with h0 | h0
      · simp [h0]
      · field_simp
  constructor
  · intro h v
    have := h (fun k => v k / π k)
    have hv : (fun k => π k * (v k / π k)) = v := funext fun k => by field_simp [(hπ k).ne']
    rwa [qf_diagConj, hrw, hv] at this
  · intro h w
    rw [qf_diagConj, hrw]
    exact h _

/-- **The weighted Metzler Hodge index theorem.** For a connected Metzler form and any positive
weight with positive image, one positive square ⇔ (TD_π). -/
theorem isHyperbolic_iff_weightedTrickleDown {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hM : IsMetzler Q) (hconn : IsConnectedSupport Q) {π : ι → ℝ} (hπ : ∀ i, 0 < π i)
    (hQπ : ∀ i, 0 < (Q *ᵥ π) i) : IsHyperbolic Q ↔ WeightedTrickleDown π Q := by
  have hD : ∀ i, 0 < rowSum (diagConj π Q) i := fun i => by
    rw [rowSum_diagConj]; exact mul_pos (hπ i) (hQπ i)
  rw [← isHyperbolic_diagConj_iff (fun i => (hπ i).ne'), ← trickleDownIneq_diagConj_iff hπ]
  exact isHyperbolic_iff_trickleDownIneq (diagConj_isSymm hQ) (diagConj_isMetzler hπ hM) hD
    (diagConj_isConnectedSupport hπ hconn)

end GaloisForLFunctions.ArithmeticLorentzianGeometry
