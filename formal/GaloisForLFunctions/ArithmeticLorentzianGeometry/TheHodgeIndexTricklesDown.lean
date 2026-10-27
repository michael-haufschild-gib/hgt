import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo

/-!
# The Hodge index trickles down

A **trickle-down datum** for a symmetric form `Q` with positive row sums `D = Q·1` is a family of
symmetric hyperbolic **links** `T_i` with `Σ_i T_i = Q` and `T_i·1 = Q e_i` (the link at `i` has the
`i`-th row of `Q` as its row sums). Reverse Cauchy–Schwarz in each link against `1` gives the
**trickle-down inequality**

    Q[v] ≤ Σ_i (Qv)_i² / D_i                                              (TD)

(`trickleDownIneq_of_links`). Global positivity is recovered from it for **Metzler** forms
(nonnegative off-diagonal entries) with connected support (`isHyperbolic_of_trickleDownIneq`): a
maximizer `v₀` of `Q` on the `D`-unit sphere of `{Σ D_i v_i = 0}` is a generalized eigenvector
`Qv₀ = m D v₀`; (TD) forces `m ≤ m²`, the graph Laplacian `Σ D_i v_i² − Q[v] = ½ Σ Q_jk (v_j − v_k)²`
forces `m ≤ 1` with equality only on constants, so `m ≤ 0`.

**The Metzler Hodge index theorem** (`isHyperbolic_iff_trickleDownIneq`,
`isHyperbolic_iff_hasHyperbolicLinks`): for a Metzler form with positive row sums and connected
support,

    one positive square  ⇔  (TD)  ⇔  hyperbolic links exist,

and the links can be taken rank one plus negative semidefinite. The point is the change of class:
hyperbolicity is not closed under sums, but (TD) says that `Q − Q D⁻¹ Q` is negative
semidefinite, and negative semidefinite forms *are* closed under sums. Local-to-global for the
Hodge index of a Metzler form is a sum of local semidefinite defects.

**Quantitative trickle-down** (`qf_le_of_approxTrickleDown`): (TD) up to `ε ‖v‖²_D` together with a
gap `Q ≤ (1 − g) D` on the constraint hyperplane gives `Q ≤ μ₋(ε) D` there, `μ₋ = (1 − √(1 − 4ε))/2`:
approximate links give an approximate Hodge index. The variational step is
`exists_max_generalizedEigen`.

Both side conditions are necessary: a disconnected form satisfies (TD) with two positive squares
(`trickleDown_disconnected`), and a form with a negative off-diagonal entry satisfies (TD) while
positive definite (`trickleDown_not_metzler`). The sign hypothesis of Lorentzian theory is used
exactly here.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι]

/-! ### Definitions -/

/-- The row sums `D = Q·1`. -/
def rowSum (Q : Matrix ι ι ℝ) : ι → ℝ := Q *ᵥ 1

/-- **Metzler**: nonnegative off-diagonal entries. The diagonal is unrestricted. -/
def IsMetzler (Q : Matrix ι ι ℝ) : Prop := ∀ j k, j ≠ k → 0 ≤ Q j k

/-- **Connected support**: a function constant along every nonzero entry is constant. -/
def IsConnectedSupport (Q : Matrix ι ι ℝ) : Prop :=
  ∀ w : ι → ℝ, (∀ j k, Q j k ≠ 0 → w j = w k) → ∀ j k, w j = w k

/-- **The trickle-down inequality** `Q[v] ≤ Σ_i (Qv)_i² / D_i`. -/
def TrickleDownIneq (Q : Matrix ι ι ℝ) : Prop :=
  ∀ v, qf Q v ≤ ∑ i, (Q *ᵥ v) i ^ 2 / rowSum Q i

/-! ### Bookkeeping -/

theorem qf_eq_sum (Q : Matrix ι ι ℝ) (v : ι → ℝ) : qf Q v = ∑ j, ∑ k, v j * Q j k * v k := by
  simp only [qf, bil, dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

theorem bil_one_left {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (v : ι → ℝ) :
    bil Q 1 v = ∑ i, rowSum Q i * v i := by
  rw [bil_comm hQ]
  simp only [bil, rowSum, dotProduct, mulVec, Pi.one_apply, mul_one, mul_sum, sum_mul]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem qf_one {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) : qf Q 1 = ∑ i, rowSum Q i := by
  rw [qf, bil_one_left hQ]; simp

theorem bil_sum_matrix (T : ι → Matrix ι ι ℝ) (x y : ι → ℝ) :
    bil (∑ i, T i) x y = ∑ i, bil (T i) x y := by
  simp only [bil, sum_mulVec, dotProduct_sum]

/-- **The graph Laplacian identity**: `Σ D_j v_j² − Q[v] = ½ Σ_{j,k} Q_jk (v_j − v_k)²`. -/
theorem sum_rowSum_mul_sq_sub_qf {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (v : ι → ℝ) :
    ∑ j, rowSum Q j * v j ^ 2 - qf Q v = (1 / 2) * ∑ j, ∑ k, Q j k * (v j - v k) ^ 2 := by
  have hsym : ∀ j k, Q j k = Q k j := fun j k => by
    exact hQ.apply k j
  have e1 : ∑ j, rowSum Q j * v j ^ 2 = ∑ j, ∑ k, Q j k * v j ^ 2 := by
    simp only [rowSum, mulVec, dotProduct, Pi.one_apply, mul_one, sum_mul]
  have e2 : ∑ j, ∑ k, Q j k * v k ^ 2 = ∑ j, ∑ k, Q j k * v j ^ 2 := by
    rw [sum_comm]; exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by rw [hsym]
  rw [qf_eq_sum, e1]
  have : ∑ j, ∑ k, Q j k * (v j - v k) ^ 2 =
      ∑ j, ∑ k, Q j k * v j ^ 2 + ∑ j, ∑ k, Q j k * v k ^ 2 -
        2 * ∑ j, ∑ k, v j * Q j k * v k := by
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rw [this, e2]; ring

/-- For a Metzler form, `Q[v] ≤ Σ D_j v_j²`. -/
theorem qf_le_sum_rowSum_mul_sq {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hM : IsMetzler Q)
    (v : ι → ℝ) : qf Q v ≤ ∑ j, rowSum Q j * v j ^ 2 := by
  have h := sum_rowSum_mul_sq_sub_qf hQ v
  have : 0 ≤ ∑ j, ∑ k, Q j k * (v j - v k) ^ 2 := sum_nonneg fun j _ => sum_nonneg fun k _ => by
    rcases eq_or_ne j k with rfl | hjk
    · simp
    · exact mul_nonneg (hM j k hjk) (sq_nonneg _)
  linarith

/-- **Equality in the Laplacian bound** forces `v` to be constant along the positive entries. -/
theorem eq_of_qf_eq_sum_rowSum {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hM : IsMetzler Q)
    {v : ι → ℝ} (h : qf Q v = ∑ j, rowSum Q j * v j ^ 2) : ∀ j k, 0 < Q j k → v j = v k := by
  have hl := sum_rowSum_mul_sq_sub_qf hQ v
  rw [h, sub_self] at hl
  have hz : ∑ j, ∑ k, Q j k * (v j - v k) ^ 2 = 0 := by linarith
  have hnn : ∀ j k, 0 ≤ Q j k * (v j - v k) ^ 2 := fun j k => by
    rcases eq_or_ne j k with rfl | hjk
    · simp
    · exact mul_nonneg (hM j k hjk) (sq_nonneg _)
  intro j k hjk
  have h1 := (sum_eq_zero_iff_of_nonneg fun j _ => sum_nonneg fun k _ => hnn j k).mp hz j
    (mem_univ j)
  have h2 := (sum_eq_zero_iff_of_nonneg fun k _ => hnn j k).mp h1 k (mem_univ k)
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hjk.ne'
  · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

/-! ### Hyperbolic forms satisfy (TD) -/

/-- **Hyperbolic ⇒ (TD).** Split `v = a·1 + z` with `z` orthogonal to `1`: `Q[z] ≤ 0`, and
`a² Q[1] = (Σ (Qv)_i)² / Σ D_i ≤ Σ (Qv)_i²/D_i` (Cauchy–Schwarz in Engel form). -/
theorem trickleDownIneq_of_isHyperbolic {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hD : ∀ i, 0 < rowSum Q i) (h : IsHyperbolic Q) : TrickleDownIneq Q := by
  intro v
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [qf, bil, dotProduct]
  have hS : 0 < ∑ i, rowSum Q i := sum_pos (fun i _ => hD i) univ_nonempty
  have h1 : 0 < qf Q 1 := by rw [qf_one hQ]; exact hS
  set a := bil Q 1 v / qf Q 1
  set z := v - a • (1 : ι → ℝ)
  have hz : bil Q 1 z = 0 := by
    have h1' : bil Q 1 1 ≠ 0 := h1.ne'
    rw [show z = v + (-a) • (1 : ι → ℝ) by simp [z, sub_eq_add_neg], bil_add_right,
      bil_smul_right]
    simp only [a, qf]
    rw [neg_mul, div_mul_cancel₀ _ h1', add_neg_cancel]
  have hzneg := h.nonpos_of_bil_eq_zero h1 hz
  have hv : v = a • (1 : ι → ℝ) + (1 : ℝ) • z := by simp [z]
  have hqv : qf Q v = a ^ 2 * qf Q 1 + qf Q z := by
    rw [hv, qf_add_smul hQ, hz]; ring
  have hQv : ∀ i, (Q *ᵥ v) i = (Q *ᵥ v) i := fun _ => rfl
  have hsumQv : ∑ i, (Q *ᵥ v) i = bil Q 1 v := by
    simp only [bil, dotProduct, Pi.one_apply, one_mul]
  have hengel : (∑ i, (Q *ᵥ v) i) ^ 2 / ∑ i, rowSum Q i ≤ ∑ i, (Q *ᵥ v) i ^ 2 / rowSum Q i :=
    sq_sum_div_le_sum_sq_div _ _ fun i _ => hD i
  have ha : a ^ 2 * qf Q 1 = (bil Q 1 v) ^ 2 / qf Q 1 := by
    simp only [a]; field_simp
  rw [hqv, ha, qf_one hQ, ← hsumQv]
  linarith

/-! ### The variational setup: the `D`-sphere of the constraint hyperplane -/

/-- If `a t + b t² ≤ 0` for every real `t`, then `a = 0`. -/
theorem eq_zero_of_forall_mul_add_mul_sq_nonpos {a b : ℝ} (h : ∀ t : ℝ, a * t + b * t ^ 2 ≤ 0) :
    a = 0 := by
  by_contra ha
  have hc : 0 < |b| + 1 := by positivity
  have := h (a / (2 * (|b| + 1)))
  have hb : b * (a / (2 * (|b| + 1))) ^ 2 ≥ -(|b| * (a / (2 * (|b| + 1))) ^ 2) := by
    nlinarith [neg_abs_le b, sq_nonneg (a / (2 * (|b| + 1)))]
  have ha2 : 0 < a ^ 2 := by positivity
  have key : a * (a / (2 * (|b| + 1))) - |b| * (a / (2 * (|b| + 1))) ^ 2 =
      a ^ 2 * (|b| + 2) / (4 * (|b| + 1) ^ 2) := by
    field_simp; ring
  have : 0 < a ^ 2 * (|b| + 2) / (4 * (|b| + 1) ^ 2) :=
    div_pos (mul_pos ha2 (by positivity)) (by positivity)
  linarith

/-- The `D`-weighted square `‖v‖²_D = Σ D_i v_i²`. -/
def dNormSq (Q : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := ∑ i, rowSum Q i * v i ^ 2

theorem dNormSq_pos {Q : Matrix ι ι ℝ} (hD : ∀ i, 0 < rowSum Q i) {v : ι → ℝ} (hv : v ≠ 0) :
    0 < dNormSq Q v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi0 : v i ≠ 0 := by simpa using hi
  have hi' : 0 < rowSum Q i * v i ^ 2 :=
    mul_pos (hD i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi0)))
  exact lt_of_lt_of_le hi' (single_le_sum (f := fun j => rowSum Q j * v j ^ 2)
    (fun j _ => mul_nonneg (hD j).le (sq_nonneg _)) (mem_univ i))

theorem dNormSq_smul (Q : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    dNormSq Q (c • v) = c ^ 2 * dNormSq Q v := by
  simp only [dNormSq, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun i _ => by ring

/-- The `D`-weighted pairing. -/
def dPair (Q : Matrix ι ι ℝ) (v z : ι → ℝ) : ℝ := ∑ i, rowSum Q i * v i * z i

theorem dNormSq_add_smul (Q : Matrix ι ι ℝ) (v z : ι → ℝ) (t : ℝ) :
    dNormSq Q (v + t • z) = dNormSq Q v + 2 * t * dPair Q v z + t ^ 2 * dNormSq Q z := by
  simp only [dNormSq, dPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum,
    ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- The constraint hyperplane `{Σ D_i v_i = 0}`. -/
def dHyperplane (Q : Matrix ι ι ℝ) : Set (ι → ℝ) := {v | ∑ i, rowSum Q i * v i = 0}

theorem isCompact_dSphere {Q : Matrix ι ι ℝ} (hD : ∀ i, 0 < rowSum Q i) :
    IsCompact (dHyperplane Q ∩ {v | dNormSq Q v = 1}) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ continuous_const)
    · exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
    · exact continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).pow 2)
  · -- on the sphere `v_i² ≤ 1/D_i ≤ R²`
    set R : ℝ := 1 + ∑ i, 1 / rowSum Q i
    have hs : 0 ≤ ∑ i, 1 / rowSum Q i := sum_nonneg fun j _ => (one_div_pos.mpr (hD j)).le
    have hR0 : 0 ≤ R := by linarith
    have hRi : ∀ i, 1 / rowSum Q i ≤ R ^ 2 := fun i => by
      have hi : 1 / rowSum Q i ≤ ∑ i, 1 / rowSum Q i :=
        single_le_sum (f := fun j => 1 / rowSum Q j)
          (fun j _ => (one_div_pos.mpr (hD j)).le) (mem_univ i)
      nlinarith
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨R, fun v hv => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg hR0).mpr fun i => ?_
    have h1 : dNormSq Q v = 1 := hv.2
    have hle : rowSum Q i * v i ^ 2 ≤ 1 := by
      rw [← h1]
      exact single_le_sum (f := fun j => rowSum Q j * v j ^ 2)
        (fun j _ => mul_nonneg (hD j).le (sq_nonneg _)) (mem_univ i)
    have hvi : v i ^ 2 ≤ R ^ 2 := by
      have : v i ^ 2 ≤ 1 / rowSum Q i := by
        rw [le_div_iff₀ (hD i)]; linarith
      linarith [hRi i]
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem continuous_qf (Q : Matrix ι ι ℝ) : Continuous (qf Q) := by
  have : qf Q = fun v => ∑ j, ∑ k, v j * Q j k * v k := funext (qf_eq_sum Q)
  rw [this]
  exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
    ((continuous_apply j).mul continuous_const).mul (continuous_apply k)

/-! ### Links -/

variable [DecidableEq ι]

/-- **Hyperbolic links**: symmetric hyperbolic `T_i` with `Σ T_i = Q` and `T_i·1 = Q e_i`. -/
def HasHyperbolicLinks (Q : Matrix ι ι ℝ) : Prop :=
  ∃ T : ι → Matrix ι ι ℝ, (∀ i, (T i).IsSymm ∧ IsHyperbolic (T i)) ∧ ∑ i, T i = Q ∧
    ∀ i, T i *ᵥ 1 = Q *ᵥ Pi.single i 1

/-- **Links ⇒ (TD).** Reverse Cauchy–Schwarz in the link `T_i` against `1`, whose square is `D_i`
and whose pairing with `v` is `(Qv)_i`. -/
theorem trickleDownIneq_of_links {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hD : ∀ i, 0 < rowSum Q i)
    (h : HasHyperbolicLinks Q) : TrickleDownIneq Q := by
  obtain ⟨T, hT, hsum, hrow⟩ := h
  intro v
  have hsym : ∀ j k, Q j k = Q k j := fun j k => by
    exact hQ.apply k j
  have e : qf Q v = ∑ i, qf (T i) v := by rw [← hsum]; exact bil_sum_matrix T v v
  rw [e]
  refine sum_le_sum fun i _ => ?_
  have h1 : qf (T i) 1 = rowSum Q i := by
    rw [qf, bil, hrow i]
    simp only [rowSum, dotProduct, mulVec, Pi.one_apply, one_mul, mul_one, Pi.single_apply,
      mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    exact sum_congr rfl fun j _ => hsym j i
  have h2 : bil (T i) 1 v = (Q *ᵥ v) i := by
    rw [bil_comm (hT i).1, bil, hrow i]
    simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq',
      mem_univ, if_true]
    exact sum_congr rfl fun j _ => by rw [hsym, mul_comm]
  have hcs := (hT i).2 1 v (by rw [h1]; exact hD i)
  rw [h1, h2] at hcs
  rw [le_div_iff₀ (hD i), mul_comm]
  exact hcs

/-! ### (TD) gives hyperbolicity for connected Metzler forms -/

theorem mulVec_single_dotProduct {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (i : ι) (v : ι → ℝ) :
    (Q *ᵥ Pi.single i 1) ⬝ᵥ v = (Q *ᵥ v) i := by
  have hsym : ∀ j k, Q j k = Q k j := fun j k => by
    exact hQ.apply k j
  simp only [dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_univ, if_true]
  exact sum_congr rfl fun j _ => by rw [hsym]

/-- **The variational principle on the constraint hyperplane.** If the hyperplane
`{Σ D_i v_i = 0}` contains a nonzero vector, `Q` attains its maximum `m` on the `D`-unit sphere of
the hyperplane at a generalized eigenvector `Q v₀ = m D v₀`, and `Q[v] ≤ m ‖v‖²_D` on the
hyperplane. -/
theorem exists_max_generalizedEigen {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hD : ∀ i, 0 < rowSum Q i) {z : ι → ℝ} (hzH : z ∈ dHyperplane Q) (hz0 : z ≠ 0) :
    ∃ v₀ ∈ dHyperplane Q, dNormSq Q v₀ = 1 ∧
      (∀ i, (Q *ᵥ v₀) i = qf Q v₀ * (rowSum Q i * v₀ i)) ∧
      ∀ v ∈ dHyperplane Q, qf Q v ≤ qf Q v₀ * dNormSq Q v := by
  have hι : Nonempty ι := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hz0; exact ⟨i⟩
  have hSD : 0 < ∑ i, rowSum Q i := sum_pos (fun i _ => hD i) univ_nonempty
  set K := dHyperplane Q ∩ {v | dNormSq Q v = 1}
  -- normalize a vector of the hyperplane onto the sphere
  have hnorm : ∀ v ∈ dHyperplane Q, v ≠ 0 →
      (1 / Real.sqrt (dNormSq Q v)) • v ∈ K := fun v hv hv0 => by
    have hN := dNormSq_pos hD hv0
    refine ⟨?_, ?_⟩
    · have hv' : ∑ i, rowSum Q i * v i = 0 := hv
      show ∑ i, rowSum Q i * ((1 / Real.sqrt (dNormSq Q v)) • v) i = 0
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show ∑ i, rowSum Q i * (1 / Real.sqrt (dNormSq Q v) * v i) =
        (1 / Real.sqrt (dNormSq Q v)) * ∑ i, rowSum Q i * v i by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring, hv', mul_zero]
    · show dNormSq Q ((1 / Real.sqrt (dNormSq Q v)) • v) = 1
      rw [dNormSq_smul, div_pow, Real.sq_sqrt hN.le]
      field_simp
  obtain ⟨v₀, hv₀K, hmax⟩ := (isCompact_dSphere hD).exists_isMaxOn
    ⟨_, hnorm z hzH hz0⟩ (continuous_qf Q).continuousOn
  set m := qf Q v₀
  -- homogeneity: `Q[v] ≤ m ‖v‖²_D` on the hyperplane
  have hhom : ∀ v ∈ dHyperplane Q, qf Q v ≤ m * dNormSq Q v := fun v hv => by
    rcases eq_or_ne v 0 with rfl | hv0
    · simp [qf, bil, dNormSq]
    · have hN := dNormSq_pos hD hv0
      have := hmax (hnorm v hv hv0)
      simp only [Set.mem_setOf_eq] at this
      have e : qf Q ((1 / Real.sqrt (dNormSq Q v)) • v) = qf Q v / dNormSq Q v := by
        have := qf_add_smul hQ (1 / Real.sqrt (dNormSq Q v)) 0 v v
        simp only [zero_smul, add_zero, zero_mul, mul_zero, zero_pow two_ne_zero] at this
        rw [this, div_pow, Real.sq_sqrt hN.le]; ring
      rw [e, div_le_iff₀ hN] at this
      exact this
  have hv₀H : v₀ ∈ dHyperplane Q := hv₀K.1
  have hv₀1 : dNormSq Q v₀ = 1 := hv₀K.2
  -- first variation: `v₀ᵀ Q z' = m ⟨v₀, z'⟩_D` on the hyperplane
  have hvar : ∀ z' ∈ dHyperplane Q, bil Q v₀ z' = m * dPair Q v₀ z' := fun z' hz' => by
    have key : ∀ t : ℝ, 2 * (bil Q v₀ z' - m * dPair Q v₀ z') * t +
        (qf Q z' - m * dNormSq Q z') * t ^ 2 ≤ 0 := fun t => by
      have hmem : (1 : ℝ) • v₀ + t • z' ∈ dHyperplane Q := by
        have h1 : ∑ i, rowSum Q i * v₀ i = 0 := hv₀H
        have h2 : ∑ i, rowSum Q i * z' i = 0 := hz'
        show ∑ i, rowSum Q i * ((1 : ℝ) • v₀ + t • z') i = 0
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, mul_add, sum_add_distrib]
        rw [h1, show ∑ i, rowSum Q i * (t * z' i) = t * ∑ i, rowSum Q i * z' i by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring, h2]
        ring
      have := hhom _ hmem
      rw [qf_add_smul hQ, one_smul, dNormSq_add_smul, hv₀1] at this
      nlinarith
    have := eq_zero_of_forall_mul_add_mul_sq_nonpos (a := 2 * (bil Q v₀ z' - m * dPair Q v₀ z'))
      (b := qf Q z' - m * dNormSq Q z') key
    linarith
  -- hence `Q v₀ = m D v₀`
  have heig : ∀ i, (Q *ᵥ v₀) i = m * (rowSum Q i * v₀ i) := fun i => by
    set y : ι → ℝ := Pi.single i 1
    set c := (∑ j, rowSum Q j * y j) / ∑ j, rowSum Q j
    have hyH : y - c • (1 : ι → ℝ) ∈ dHyperplane Q := by
      show ∑ j, rowSum Q j * (y - c • (1 : ι → ℝ)) j = 0
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, mul_sub,
        sum_sub_distrib]
      rw [← sum_mul]; simp only [c]; field_simp; ring
    have h1 := hvar _ hyH
    have hb1 : bil Q v₀ (1 : ι → ℝ) = 0 := by
      rw [bil_comm hQ, bil_one_left hQ]; exact hv₀H
    have hd1 : dPair Q v₀ (1 : ι → ℝ) = 0 := by
      simp only [dPair, Pi.one_apply, mul_one]; exact hv₀H
    rw [sub_eq_add_neg, ← neg_smul, bil_add_right, bil_smul_right, hb1] at h1
    have hdp : dPair Q v₀ (y + (-c) • (1 : ι → ℝ)) = dPair Q v₀ y := by
      simp only [dPair, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, mul_add,
        sum_add_distrib]
      have : ∑ x, rowSum Q x * v₀ x * -c = -c * ∑ x, rowSum Q x * v₀ x := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      rw [this, show ∑ x, rowSum Q x * v₀ x = 0 from hv₀H]; ring
    rw [hdp] at h1
    have hb : bil Q v₀ y = (Q *ᵥ v₀) i := by
      show bil Q v₀ (Pi.single i 1) = _
      rw [bil_comm hQ, bil, single_dotProduct, one_mul]
    have hd : dPair Q v₀ y = rowSum Q i * v₀ i := by
      simp only [dPair, y, Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
        if_true]
    rw [← hb, ← hd]; linarith
  exact ⟨v₀, hv₀H, hv₀1, heig, hhom⟩

/-- **(TD) ⇒ hyperbolic** for a connected Metzler form with positive row sums. -/
theorem isHyperbolic_of_trickleDownIneq {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hM : IsMetzler Q)
    (hD : ∀ i, 0 < rowSum Q i) (hconn : IsConnectedSupport Q) (h : TrickleDownIneq Q) :
    IsHyperbolic Q := by
  refine isHyperbolic_of_nonpos_on_ker hQ (dotLeft (rowSum Q)) fun z hz => ?_
  have hzH : z ∈ dHyperplane Q := by
    have : rowSum Q ⬝ᵥ z = 0 := hz
    simpa [dHyperplane, dotProduct] using this
  by_contra hpos
  push Not at hpos
  have hz0 : z ≠ 0 := by rintro rfl; simp [qf, bil] at hpos
  have hNz := dNormSq_pos hD hz0
  have hι : Nonempty ι := by
    obtain ⟨i, -⟩ := Function.ne_iff.mp hz0; exact ⟨i⟩
  have hSD : 0 < ∑ i, rowSum Q i := sum_pos (fun i _ => hD i) univ_nonempty
  obtain ⟨v₀, hv₀H, hv₀1, heig, hhom⟩ := exists_max_generalizedEigen hQ hD hzH hz0
  set m := qf Q v₀
  have hm0 : 0 < m := by
    have := hhom z hzH
    nlinarith
  -- (TD) at `v₀`: `m ≤ m²`
  have hTD := h v₀
  have hrhs : ∑ i, (Q *ᵥ v₀) i ^ 2 / rowSum Q i = m ^ 2 := by
    rw [← mul_one (m ^ 2), ← hv₀1, dNormSq, mul_sum]
    exact sum_congr rfl fun i _ => by rw [heig i]; field_simp [(hD i).ne']
  rw [hrhs] at hTD
  have hm1 : 1 ≤ m := by nlinarith
  -- Laplacian: `m ≤ 1`, with equality only on constants
  have hlap := qf_le_sum_rowSum_mul_sq hQ hM v₀
  rw [show ∑ j, rowSum Q j * v₀ j ^ 2 = dNormSq Q v₀ from rfl, hv₀1] at hlap
  have hm : m = 1 := le_antisymm hlap hm1
  have heq : qf Q v₀ = ∑ j, rowSum Q j * v₀ j ^ 2 := by
    rw [show ∑ j, rowSum Q j * v₀ j ^ 2 = dNormSq Q v₀ from rfl, hv₀1]; exact hm
  have hedge := eq_of_qf_eq_sum_rowSum hQ hM heq
  have hconst := hconn v₀ fun j k hjk => by
    rcases eq_or_ne j k with rfl | hne
    · rfl
    · exact hedge j k (lt_of_le_of_ne (hM j k hne) (Ne.symm hjk))
  obtain ⟨i₀⟩ := hι
  have hv₀c : v₀ = fun _ => v₀ i₀ := funext fun j => hconst j i₀
  have : v₀ i₀ * ∑ i, rowSum Q i = 0 := by
    have : ∑ i, rowSum Q i * v₀ i = 0 := hv₀H
    rw [hv₀c] at this
    rw [mul_sum]; rw [← this]; exact sum_congr rfl fun i _ => by ring
  have hc0 : v₀ i₀ = 0 := by
    rcases mul_eq_zero.mp this with h0 | h0
    · exact h0
    · exact absurd h0 hSD.ne'
  have : dNormSq Q v₀ = 0 := by
    rw [hv₀c, hc0]; simp [dNormSq]
  rw [hv₀1] at this
  exact one_ne_zero this

/-! ### Quantitative trickle-down -/

/-- **Quantitative trickle-down.** If the trickle-down inequality holds up to `ε ‖v‖²_D` and the form
has a gap `Q[v] ≤ (1 − g) ‖v‖²_D` on the constraint hyperplane that excludes the upper root
`μ₊ = (1 + √(1 − 4ε))/2`, then `Q[v] ≤ μ₋ ‖v‖²_D` on the hyperplane, `μ₋ = (1 − √(1 − 4ε))/2`.
Approximate links and a gap give an approximate Hodge index; no sign condition is used, the sign
enters through the gap (the graph Laplacian for Metzler forms). -/
theorem qf_le_of_approxTrickleDown {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hD : ∀ i, 0 < rowSum Q i)
    {ε g : ℝ} (h4 : 4 * ε ≤ 1)
    (hTD : ∀ v, qf Q v ≤ ∑ i, (Q *ᵥ v) i ^ 2 / rowSum Q i + ε * dNormSq Q v)
    (hgap : ∀ v ∈ dHyperplane Q, qf Q v ≤ (1 - g) * dNormSq Q v)
    (hg : 1 - g < (1 + Real.sqrt (1 - 4 * ε)) / 2) :
    ∀ v ∈ dHyperplane Q, qf Q v ≤ (1 - Real.sqrt (1 - 4 * ε)) / 2 * dNormSq Q v := by
  intro v hv
  rcases eq_or_ne v 0 with rfl | hv0
  · simp [qf, bil, dNormSq]
  obtain ⟨v₀, hv₀H, hv₀1, heig, hhom⟩ := exists_max_generalizedEigen hQ hD hv hv0
  set m := qf Q v₀
  set r := Real.sqrt (1 - 4 * ε)
  have hr : r ^ 2 = 1 - 4 * ε := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  -- (TD_ε) at `v₀`: `m ≤ m² + ε`
  have hTD0 := hTD v₀
  have hrhs : ∑ i, (Q *ᵥ v₀) i ^ 2 / rowSum Q i = m ^ 2 := by
    rw [← mul_one (m ^ 2), ← hv₀1, dNormSq, mul_sum]
    exact sum_congr rfl fun i _ => by rw [heig i]; field_simp [(hD i).ne']
  rw [hrhs, hv₀1, mul_one] at hTD0
  -- `(m − μ₋)(m − μ₊) ≥ 0` and the gap excludes `m ≥ μ₊`
  have hfac : 0 ≤ (m - (1 - r) / 2) * (m - (1 + r) / 2) := by nlinarith
  have hmgap : m < (1 + r) / 2 := by
    have := hgap v₀ hv₀H; rw [hv₀1, mul_one] at this; linarith
  have hm : m ≤ (1 - r) / 2 := by
    by_contra hlt; push Not at hlt
    have : 0 < (m - (1 - r) / 2) := by linarith
    have : (m - (1 + r) / 2) < 0 := by linarith
    nlinarith
  calc qf Q v ≤ m * dNormSq Q v := hhom v hv
    _ ≤ (1 - r) / 2 * dNormSq Q v :=
      mul_le_mul_of_nonneg_right hm (sum_nonneg fun i _ => mul_nonneg (hD i).le (sq_nonneg _))

/-! ### Links from (TD) -/

/-- **(TD) ⇒ links**: `T_i = c_i c_iᵀ + N/|ι|` with `c_i = D_i^{−1/2} Q e_i` and
`N = Q − Σ c_i c_iᵀ`, negative semidefinite by (TD). -/
theorem hasHyperbolicLinks_of_trickleDownIneq {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hD : ∀ i, 0 < rowSum Q i) (h : TrickleDownIneq Q) : HasHyperbolicLinks Q := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ => 0, fun i => isEmptyElim i, Subsingleton.elim _ _, fun i => isEmptyElim i⟩
  set c : ι → ι → ℝ := fun i => (1 / Real.sqrt (rowSum Q i)) • (Q *ᵥ Pi.single i 1)
  set R : Matrix ι ι ℝ := ∑ i, vecMulVec (c i) (c i)
  set N : Matrix ι ι ℝ := Q - R
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsq : ∀ i, (c i ⬝ᵥ (1 : ι → ℝ)) = Real.sqrt (rowSum Q i) := fun i => by
    simp only [c, smul_dotProduct, smul_eq_mul]
    rw [mulVec_single_dotProduct hQ, show (Q *ᵥ (1 : ι → ℝ)) i = rowSum Q i from rfl]
    have := Real.sq_sqrt (hD i).le
    have hs := Real.sqrt_pos.mpr (hD i)
    field_simp
    linarith
  have hcv : ∀ i v, (c i ⬝ᵥ v) ^ 2 = (Q *ᵥ v) i ^ 2 / rowSum Q i := fun i v => by
    simp only [c, smul_dotProduct, smul_eq_mul]
    rw [mulVec_single_dotProduct hQ, mul_pow, div_pow, Real.sq_sqrt (hD i).le]
    ring
  have hrank : ∀ (a : ι → ℝ) v, qf (vecMulVec a a) v = (a ⬝ᵥ v) ^ 2 := fun a v => by
    simp only [qf, bil, vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    rw [dotProduct_comm v a]; ring
  have hRsymm : R.IsSymm := by
    simp only [R]
    refine Matrix.IsSymm.ext fun j k => ?_
    simp only [Matrix.sum_apply, vecMulVec_apply, mul_comm]
  have hNsymm : N.IsSymm := hQ.sub hRsymm
  have hNneg : ∀ v, qf N v ≤ 0 := fun v => by
    have e : qf N v = qf Q v - ∑ i, (Q *ᵥ v) i ^ 2 / rowSum Q i := by
      simp only [N, R, qf, bil, sub_mulVec, dotProduct_sub, sum_mulVec, dotProduct_sum]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [← hcv]; exact hrank (c i) v
    rw [e]; linarith [h v]
  refine ⟨fun i => vecMulVec (c i) (c i) + (1 / (Fintype.card ι : ℝ)) • N, fun i => ⟨?_, ?_⟩,
    ?_, fun i => ?_⟩
  · refine (Matrix.IsSymm.ext fun j k => ?_).add (hNsymm.smul _)
    simp [vecMulVec_apply, mul_comm]
  · refine isHyperbolic_rankOne_add (hNsymm.smul _) (c i) fun v => ?_
    have : qf ((1 / (Fintype.card ι : ℝ)) • N) v = (1 / (Fintype.card ι : ℝ)) * qf N v := by
      simp only [qf, bil, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hNneg v)
  · rw [sum_add_distrib, ← Finset.sum_smul, sum_const, card_univ, nsmul_eq_mul, mul_one_div_cancel
      hcard.ne', one_smul]
    simp only [N, R]; abel
  · have hci : ∀ i, vecMulVec (c i) (c i) *ᵥ (1 : ι → ℝ) = Q *ᵥ Pi.single i 1 := fun i => by
      ext j
      have hc : (vecMulVec (c i) (c i) *ᵥ (1 : ι → ℝ)) j = c i j * (c i ⬝ᵥ (1 : ι → ℝ)) := by
        simp only [mulVec, dotProduct, vecMulVec_apply, Pi.one_apply, mul_one, mul_sum]
      rw [hc, hsq i]
      simp only [c, Pi.smul_apply, smul_eq_mul]
      have hs := Real.sqrt_pos.mpr (hD i)
      field_simp
    have hN1 : N *ᵥ (1 : ι → ℝ) = 0 := by
      ext j
      simp only [N, R, sub_mulVec, sum_mulVec, hci, Pi.sub_apply, Finset.sum_apply,
        Pi.zero_apply]
      simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.single_apply, mul_ite, mul_zero,
        sum_ite_eq', mem_univ, if_true, sub_self]
    rw [add_mulVec, hci, smul_mulVec, hN1, smul_zero, add_zero]

/-! ### The Metzler Hodge index theorem -/

/-- **The Metzler Hodge index theorem.** A connected Metzler form with positive row sums has one
positive square iff it satisfies the trickle-down inequality. -/
theorem isHyperbolic_iff_trickleDownIneq {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hM : IsMetzler Q)
    (hD : ∀ i, 0 < rowSum Q i) (hconn : IsConnectedSupport Q) :
    IsHyperbolic Q ↔ TrickleDownIneq Q :=
  ⟨trickleDownIneq_of_isHyperbolic hQ hD, isHyperbolic_of_trickleDownIneq hQ hM hD hconn⟩

/-- **(TD) ⇔ hyperbolic links.** No sign condition is needed here. -/
theorem trickleDownIneq_iff_hasHyperbolicLinks {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hD : ∀ i, 0 < rowSum Q i) : TrickleDownIneq Q ↔ HasHyperbolicLinks Q :=
  ⟨hasHyperbolicLinks_of_trickleDownIneq hQ hD, trickleDownIneq_of_links hQ hD⟩

/-- **The Hodge index trickles down.** A connected Metzler form with positive row sums has one
positive square iff it has hyperbolic links. -/
theorem isHyperbolic_iff_hasHyperbolicLinks {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hM : IsMetzler Q) (hD : ∀ i, 0 < rowSum Q i) (hconn : IsConnectedSupport Q) :
    IsHyperbolic Q ↔ HasHyperbolicLinks Q :=
  (isHyperbolic_iff_trickleDownIneq hQ hM hD hconn).trans
    (trickleDownIneq_iff_hasHyperbolicLinks hQ hD)

/-- **Lorentzian by trickle-down**: nonnegative entries, hyperbolic links, connected support. -/
theorem isLorentzian_of_hasHyperbolicLinks {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (hnn : ∀ i j, 0 ≤ Q i j) (hD : ∀ i, 0 < rowSum Q i) (hconn : IsConnectedSupport Q)
    (h : HasHyperbolicLinks Q) : IsLorentzian Q :=
  ⟨hQ, hnn, (isHyperbolic_iff_hasHyperbolicLinks hQ (fun j k _ => hnn j k) hD hconn).mpr h⟩

/-! ### Both side conditions are necessary -/

/-- **Connectivity is necessary.** The identity of `ℝ²` is Metzler with unit row sums and
hyperbolic links (`e₀e₀ᵀ`, `e₁e₁ᵀ`), but has two positive squares: each connected component
contributes one. -/
theorem trickleDown_disconnected :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm ∧ IsMetzler (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      (∀ i, 0 < rowSum (1 : Matrix (Fin 2) (Fin 2) ℝ) i) ∧
      HasHyperbolicLinks (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      ¬ IsHyperbolic (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hrow : ∀ i, rowSum (1 : Matrix (Fin 2) (Fin 2) ℝ) i = 1 := fun i => by
    simp [rowSum]
  have hD : ∀ i, 0 < rowSum (1 : Matrix (Fin 2) (Fin 2) ℝ) i := fun i => by
    rw [hrow]; exact one_pos
  refine ⟨Matrix.isSymm_one, fun j k hjk => by simp [Matrix.one_apply_ne hjk], hD,
    hasHyperbolicLinks_of_trickleDownIneq Matrix.isSymm_one hD fun v => ?_, fun h => ?_⟩
  · simp only [hrow, div_one, one_mulVec]
    simp [qf, bil, dotProduct, Fin.sum_univ_two, sq]
  · have := h (Pi.single 0 1) (Pi.single 1 1) (by simp [qf, bil])
    simp [qf, bil] at this
    linarith

/-- The positive definite form `2x² − 2xy + 2y²`: connected, unit row sums, one negative
off-diagonal entry. -/
def antiMetzlerForm : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 2]

/-- **The sign is necessary.** `antiMetzlerForm` is symmetric, connected, has unit row sums and
satisfies (TD), yet has two positive squares; it is not Metzler. -/
theorem trickleDown_not_metzler :
    antiMetzlerForm.IsSymm ∧ ¬ IsMetzler antiMetzlerForm ∧ (∀ i, 0 < rowSum antiMetzlerForm i) ∧
      IsConnectedSupport antiMetzlerForm ∧ TrickleDownIneq antiMetzlerForm ∧
      ¬ IsHyperbolic antiMetzlerForm := by
  have hrow : ∀ i, rowSum antiMetzlerForm i = 1 := fun i => by
    fin_cases i <;> simp [antiMetzlerForm, rowSum, mulVec, dotProduct, Fin.sum_univ_two] <;>
      norm_num
  refine ⟨?_, fun h => ?_, fun i => by rw [hrow]; exact one_pos, fun w hw j k => ?_,
    fun v => ?_, fun h => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [antiMetzlerForm]
  · have := h 0 1 (by decide)
    simp [antiMetzlerForm] at this
    linarith
  · have h01 : w 0 = w 1 := hw 0 1 (by simp [antiMetzlerForm])
    fin_cases j <;> fin_cases k <;> simp [h01]
  · simp only [hrow, div_one]
    simp [qf, bil, antiMetzlerForm, mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (v 0 - v 1)]
  · have := h (Pi.single 0 1) (Pi.single 1 1)
      (by simp [qf, bil, antiMetzlerForm, mulVec, dotProduct, Fin.sum_univ_two])
    simp [qf, bil, antiMetzlerForm, mulVec, dotProduct, Fin.sum_univ_two] at this
    norm_num at this

end GaloisForLFunctions.ArithmeticLorentzianGeometry
