import GaloisForLFunctions.RHTower.DeckMaassSelbergRegion
import GaloisForLFunctions.RHTower.DeckEisensteinStarDecay

/-!
# Continuation of the deck Maass–Selberg relation

On closed balls in the continuation domain `W \ {1}` the truncated deck Eisenstein series is bounded
on `𝒟` uniformly in the parameter: below height `Y` by continuity of the constant term and of the
scattering operator, above height `Y` by the uniform exponential decay of the non-constant part.
Hence the truncated pairing `P(u, u') = ∫_𝒟 ⟨Λ^Y Ẽ(u; v), Λ^Y Ẽ(u'; w)⟩_β` is holomorphic in each
parameter (Cauchy-dominated differentiation under the integral).  The cleared relation
`(u − u')(u + u' − 1) P(u, u') = R(u, u')` holds in the region of absolute convergence, hence on
`{Re > 1/2} \ {1}` in both variables by the identity theorem, and then at the points of the critical
line by continuity and a second application of the identity theorem on a neighbourhood of the line.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergEisensteinStarCriticalLine

noncomputable section

variable {N : ℕ}

/-- The continuation domain `W \ {1}` at level `N + 1`. -/
def contDom (N : ℕ) : Set ℂ := Wset (N + 1) \ {1}

theorem isOpen_contDom : IsOpen (contDom N) := (isOpen_Wset (N + 1)).sdiff isClosed_singleton

theorem mem_contDom_of_half_lt {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) : s ∈ contDom N :=
  ⟨mem_Wset_of_half_lt hs, hs1⟩

open Classical in
theorem norm_le_sum_coords (X : DeckSpace N) : ‖X‖ ≤ ∑ q : Deck N, ‖X q‖ := by
  have h := (EuclideanSpace.basisFun (Deck N) ℂ).sum_repr X
  conv_lhs => rw [← h]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_smul, (EuclideanSpace.basisFun (Deck N) ℂ).orthonormal.1 q, mul_one,
    EuclideanSpace.basisFun_repr]

/-! ## Continuity in the space variable -/

theorem continuous_eisStarVec {s : ℂ} (hs : s ∈ Wset (N + 1)) (v : DeckSpace N) :
    Continuous (eisStarVec s v) := by
  refine continuous_deck_of_coords fun q => ?_
  simp_rw [eisStarVec_apply]
  exact continuous_const.mul (continuous_finsetSum _ fun g _ =>
    continuous_const.mul (DeckPointPair.continuous_EstarExt (N + 1) _ hs))

theorem continuous_eisExt {s : ℂ} (hs : s ∈ Wset (N + 1)) (v : DeckSpace N) :
    Continuous (eisExt s v) := by
  have hc : Continuous fun z : ℍ => ((z.im : ℝ) : ℂ) := Complex.continuous_ofReal.comp continuous_im
  unfold eisExt
  refine (((Continuous.cpow hc continuous_const fun z => ?_).smul continuous_const).add
    ((Continuous.cpow hc continuous_const fun z => ?_).smul continuous_const)).add
      (continuous_eisStarVec hs v) <;>
  exact Or.inl (by simpa using z.im_pos)

theorem measurable_eisTrunc_of_mem {s : ℂ} (hs : s ∈ Wset (N + 1)) (Y : ℝ) (v : DeckSpace N) :
    Measurable (eisTrunc Y s v) := by
  have he : eisTrunc Y s v = fun z => eisExt s v z - if Y < z.im then eisCT s v z.im else 0 := by
    funext z; rw [eisTrunc_def]
  rw [he]
  exact (continuous_eisExt hs v).measurable.sub (Measurable.ite
    (measurableSet_lt measurable_const continuous_im.measurable) (measurable_eisCT_im s v)
    measurable_const)

/-! ## Holomorphy in the parameter -/

theorem differentiableAt_eisCT_apply (v : DeckSpace N) {y : ℝ} (hy : 0 < y) (q : Deck N) {s : ℂ}
    (hs : s ∈ contDom N) : DifferentiableAt ℂ (fun s => eisCT s v y q) s := by
  have hy' : ((y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [eisCT, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact ((differentiableAt_id.const_cpow (Or.inl hy')).mul_const _).add
    ((((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hy')).mul
      (differentiableAt_scatVec_apply v q hs.1 hs.2))

theorem differentiableAt_eisTrunc_apply (Y : ℝ) (v : DeckSpace N) (z : ℍ) (q : Deck N) {s : ℂ}
    (hs : s ∈ contDom N) : DifferentiableAt ℂ (fun s => eisTrunc Y s v z q) s := by
  simp only [eisTrunc_def, PiLp.sub_apply]
  refine (differentiableAt_eisExt_apply v z q hs.1 hs.2).sub ?_
  split_ifs
  · exact differentiableAt_eisCT_apply v z.im_pos q hs
  · simp

theorem differentiableAt_bil_eisTrunc {Y : ℝ} {v w : DeckSpace N} {u' : ℂ} (z : ℍ) {u : ℂ}
    (hu : u ∈ contDom N) :
    DifferentiableAt ℂ (fun u => bil (eisTrunc Y u v z) (eisTrunc Y u' w z)) u := by
  unfold bil
  exact DifferentiableAt.fun_sum fun q _ =>
    (differentiableAt_eisTrunc_apply Y v z q hu).mul_const _

/-! ## Uniform bounds on closed balls -/

theorem exists_norm_eisStarVec_le {s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hcb : closedBall s₀ r ⊆ Wset (N + 1))
    (v : DeckSpace N) :
    ∃ A, 0 ≤ A ∧ ∀ s ∈ closedBall s₀ r, ∀ z : ℍ, 1 / 2 ≤ z.im → ‖eisStarVec s v z‖ ≤ A := by
  have hL : (0 : ℝ) < (N + 1 : ℕ) := by exact_mod_cast Nat.succ_pos N
  have hY₀ : (0 : ℝ) < 1 / 2 / (N + 1 : ℕ) := by positivity
  choose A hA hbd using fun g : Deck N =>
    DeckPointPair.exists_norm_EstarExt_le (N + 1) (Quotient.out g : SL(2, ℤ)) hr hcb hY₀
  refine ⟨∑ q : Deck N, (∑ g : Deck N, ‖v‖ * A g), Finset.sum_nonneg fun q _ =>
    Finset.sum_nonneg fun g _ => mul_nonneg (norm_nonneg _) (hA g), fun s hs z hz => ?_⟩
  refine (norm_le_sum_coords _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [eisStarVec_apply, norm_mul]
  have hK : ‖(2 * (N + 1 : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    apply inv_le_one_of_one_le₀
    have : ‖(2 * (N + 1 : ℂ))‖ = 2 * (N + 1) := by
      rw [norm_mul]; norm_num; exact_mod_cast rfl
    rw [this]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  refine (mul_le_of_le_one_left (norm_nonneg _) hK).trans ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun g _ => ?_))
  rw [norm_mul]
  have hz' : 1 / 2 / (N + 1 : ℕ) ≤ z.im / (N + 1 : ℕ) := div_le_div_of_nonneg_right hz hL.le
  have h1 := hbd g s hs z hz'
  have h2 : Real.exp (-(Real.pi * (z.im / (N + 1 : ℕ)))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := z.im_pos; have := Real.pi_pos; nlinarith [div_pos z.im_pos hL]
  have h3 : ‖SelbergEisensteinStarCriticalLine.EstarExt (N + 1) (Quotient.out g) s z‖ ≤ A g :=
    h1.trans (mul_le_of_le_one_right (hA g) h2)
  exact mul_le_mul (PiLp.norm_apply_le v _) h3 (norm_nonneg _) (norm_nonneg _)

theorem exists_norm_scatVec_le {s₀ : ℂ} {r : ℝ} (hcb : closedBall s₀ r ⊆ contDom N) (v : DeckSpace N) :
    ∃ B, 0 ≤ B ∧ ∀ s ∈ closedBall s₀ r, ‖scatVec s v‖ ≤ B := by
  have hc : ContinuousOn (fun s => ∑ q : Deck N, ‖scatVec s v q‖) (closedBall s₀ r) :=
    continuousOn_finsetSum _ fun q _ => fun s hs =>
      ((differentiableAt_scatVec_apply v q (hcb hs).1 (hcb hs).2).continuousAt.norm).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  refine (norm_le_sum_coords _).trans (((le_abs_self _).trans ?_).trans (le_max_left _ _))
  have := hB s hs
  rwa [Real.norm_eq_abs] at this

theorem rpow_le_half_add {y Y : ℝ} (hy : 1 / 2 ≤ y) (hyY : y ≤ Y) (a : ℝ) :
    y ^ a ≤ (1 / 2 : ℝ) ^ a + Y ^ a := by
  have hy0 : 0 < y := by linarith
  have h1 : 0 ≤ (1 / 2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ Y ^ a := Real.rpow_nonneg (by linarith) _
  rcases le_or_gt 0 a with ha | ha
  · have := Real.rpow_le_rpow hy0.le hyY ha
    linarith
  · have := Real.rpow_le_rpow_of_nonpos (by norm_num) hy ha.le
    linarith

theorem rpow_le_of_mem_Icc_of_mem_Icc {y Y lo hi a : ℝ} (hy : 1 / 2 ≤ y) (hyY : y ≤ Y)
    (hlo : lo ≤ a) (hhi : a ≤ hi) :
    y ^ a ≤ (1 / 2 : ℝ) ^ lo + Y ^ lo + ((1 / 2 : ℝ) ^ hi + Y ^ hi) :=
  (SelbergPoincareContinuation.rpow_le_add (by linarith) hlo hhi).trans
    (add_le_add (rpow_le_half_add hy hyY lo) (rpow_le_half_add hy hyY hi))

theorem eisExt_sub_eisCT (s : ℂ) (v : DeckSpace N) (z : ℍ) :
    eisExt s v z - eisCT s v z.im = eisStarVec s v z := by
  unfold eisExt eisCT; abel

theorem re_mem_Icc_of_mem_closedBall {s₀ s : ℂ} {r : ℝ} (hs : s ∈ closedBall s₀ r) :
    s₀.re - r ≤ s.re ∧ s.re ≤ s₀.re + r := by
  have h := Complex.abs_re_le_norm (s - s₀)
  rw [mem_closedBall, dist_eq_norm] at hs
  simp only [Complex.sub_re] at h
  have := abs_le.1 (h.trans hs)
  constructor <;> linarith [this.1, this.2]

/-- **Uniform bound of the truncated series on `𝒟`** for parameters in a closed ball in `W \ {1}`. -/
theorem exists_norm_eisTrunc_le_ball {s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hcb : closedBall s₀ r ⊆ contDom N)
    {Y : ℝ} (hY : 1 ≤ Y) (v : DeckSpace N) :
    ∃ M, 0 ≤ M ∧ ∀ s ∈ closedBall s₀ r, ∀ z ∈ fd, ‖eisTrunc Y s v z‖ ≤ M := by
  obtain ⟨A, hA, hAb⟩ := exists_norm_eisStarVec_le hr (fun s hs => (hcb hs).1) v
  obtain ⟨B, hB, hBb⟩ := exists_norm_scatVec_le hcb v
  set lo := s₀.re - r
  set hi := s₀.re + r
  set P := (1 / 2 : ℝ) ^ lo + Y ^ lo + ((1 / 2 : ℝ) ^ hi + Y ^ hi)
  set P' := (1 / 2 : ℝ) ^ (1 - hi) + Y ^ (1 - hi) + ((1 / 2 : ℝ) ^ (1 - lo) + Y ^ (1 - lo))
  have hYp : 0 ≤ Y := by linarith
  have hP : 0 ≤ P := by positivity
  have hP' : 0 ≤ P' := by positivity
  refine ⟨P * ‖v‖ + P' * B + A, by positivity, fun s hs z hz => ?_⟩
  have hy : 1 / 2 ≤ z.im := (RHTower.half_lt_im_of_mem_fd' hz).le
  have hy0 : 0 < z.im := z.im_pos
  obtain ⟨h1, h2⟩ := re_mem_Icc_of_mem_closedBall hs
  rw [eisTrunc_def]
  by_cases hzY : Y < z.im
  · rw [if_pos hzY, eisExt_sub_eisCT]
    have := hAb s hs z hy
    have : 0 ≤ P * ‖v‖ + P' * B := by positivity
    linarith
  · rw [if_neg hzY, sub_zero]
    have hyY : z.im ≤ Y := not_lt.1 hzY
    unfold eisExt
    have e1 : ‖((z.im : ℂ) ^ s) • v‖ ≤ P * ‖v‖ := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      exact mul_le_mul_of_nonneg_right (rpow_le_of_mem_Icc_of_mem_Icc hy hyY h1 h2) (norm_nonneg _)
    have e2 : ‖((z.im : ℂ) ^ (1 - s)) • scatVec s v‖ ≤ P' * B := by
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_le_mul (rpow_le_of_mem_Icc_of_mem_Icc hy hyY (by linarith) (by linarith))
        (hBb s hs) (norm_nonneg _) hP'
    have e3 := hAb s hs z hy
    calc ‖((z.im : ℂ) ^ s) • v + ((z.im : ℂ) ^ (1 - s)) • scatVec s v + eisStarVec s v z‖
        ≤ ‖((z.im : ℂ) ^ s) • v‖ + ‖((z.im : ℂ) ^ (1 - s)) • scatVec s v‖ + ‖eisStarVec s v z‖ :=
          norm_add₃_le
      _ ≤ _ := by linarith

/-! ## Holomorphy of the truncated pairing -/

/-- The truncated pairing `P(u, u') = ∫_𝒟 ⟨Λ^Y Ẽ(·, u; v), Λ^Y Ẽ(·, u'; w)⟩_β`. -/
def truncPairing (Y : ℝ) (u : ℂ) (v : DeckSpace N) (u' : ℂ) (w : DeckSpace N) : ℂ :=
  ∫ z in fd, bil (eisTrunc Y u v z) (eisTrunc Y u' w z)

theorem truncPairing_comm (Y : ℝ) (u : ℂ) (v : DeckSpace N) (u' : ℂ) (w : DeckSpace N) :
    truncPairing Y u v u' w = truncPairing Y u' w u v := by
  unfold truncPairing; simp_rw [bil_comm]

theorem exists_closedBall_subset_contDom {u₀ : ℂ} (hu₀ : u₀ ∈ contDom N) :
    ∃ R, 0 < R ∧ closedBall u₀ (2 * R) ⊆ contDom N := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_contDom u₀ hu₀
  exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩

theorem differentiableAt_truncPairing_left {Y : ℝ} (hY : 1 ≤ Y) (v w : DeckSpace N) {u' : ℂ}
    (hu' : u' ∈ contDom N) {u₀ : ℂ} (hu₀ : u₀ ∈ contDom N) :
    DifferentiableAt ℂ (fun u => truncPairing Y u v u' w) u₀ := by
  obtain ⟨R, hR, hcb⟩ := exists_closedBall_subset_contDom hu₀
  obtain ⟨R', hR', hcb'⟩ := exists_closedBall_subset_contDom hu'
  obtain ⟨M, hM, hbd⟩ := exists_norm_eisTrunc_le_ball (by positivity) hcb hY v
  obtain ⟨M', hM', hbd'⟩ := exists_norm_eisTrunc_le_ball (by positivity) hcb' hY w
  have hu'mem : u' ∈ closedBall u' (2 * R') := mem_closedBall_self (by positivity)
  have hsub : ball u₀ R ⊆ closedBall u₀ (2 * R) := ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))
  have heq : (fun u => truncPairing Y u v u' w) = fun u =>
      ∫ z, fd.indicator (fun z => bil (eisTrunc Y u v z) (eisTrunc Y u' w z)) z :=
    funext fun u => (integral_indicator isClosed_fd.measurableSet).symm
  rw [heq]
  refine differentiableAt_integral_of_cauchy_dominated hR (bound := fd.indicator fun _ => M * M')
    (fun u hu => ?_) (fun z => ?_) (fun z u hu => ?_) ?_
  · exact ((measurable_bil (measurable_eisTrunc_of_mem (hcb (hsub hu)).1 Y v)
      (measurable_eisTrunc_of_mem hu'.1 Y w)).indicator isClosed_fd.measurableSet).aestronglyMeasurable
  · by_cases hz : z ∈ fd
    · simp only [Set.indicator_of_mem hz]
      exact fun u hu => (differentiableAt_bil_eisTrunc z (hcb (hsub hu))).differentiableWithinAt
    · simp only [Set.indicator_of_notMem hz]
      exact differentiableOn_const _
  · by_cases hz : z ∈ fd
    · simp only [Set.indicator_of_mem hz]
      exact (norm_bil_le _ _).trans (mul_le_mul (hbd u (hsub hu) z hz) (hbd' u' hu'mem z hz)
        (norm_nonneg _) hM)
    · simp [Set.indicator_of_notMem hz]
  · exact (integrable_indicator_iff isClosed_fd.measurableSet).2
      (integrableOn_const (by simp [volume_fd_ne_top]))

theorem differentiableAt_truncPairing_right {Y : ℝ} (hY : 1 ≤ Y) (v w : DeckSpace N) {u : ℂ}
    (hu : u ∈ contDom N) {u₀ : ℂ} (hu₀ : u₀ ∈ contDom N) :
    DifferentiableAt ℂ (fun u' => truncPairing Y u v u' w) u₀ := by
  simp_rw [truncPairing_comm Y u v]
  exact differentiableAt_truncPairing_left hY w v hu hu₀

/-! ## The cleared relation and its continuation -/

/-- The cleared right side `(u - u')(u + u' - 1) · msRHS`. -/
def msCleared (u u' : ℂ) (v w : DeckSpace N) (Y : ℝ) : ℂ :=
  (u - u') * (bil v w * (Y : ℂ) ^ (u + u' - 1) -
      bil (scatVec u v) (scatVec u' w) * (Y : ℂ) ^ (1 - u - u')) +
    (u + u' - 1) * (bil v (scatVec u' w) * (Y : ℂ) ^ (u - u') -
      bil (scatVec u v) w * (Y : ℂ) ^ (u' - u))

theorem msCleared_eq_mul {u u' : ℂ} (h1 : u - u' ≠ 0) (h2 : u + u' - 1 ≠ 0) (v w : DeckSpace N)
    (Y : ℝ) : msCleared u u' v w Y = (u - u') * (u + u' - 1) * msRHS u u' v w Y := by
  unfold msCleared msRHS
  field_simp
  ring

theorem differentiableAt_bil_scatVec_left (v X : DeckSpace N) {u : ℂ} (hu : u ∈ contDom N) :
    DifferentiableAt ℂ (fun u => bil (scatVec u v) X) u := by
  unfold bil
  exact DifferentiableAt.fun_sum fun q _ => (differentiableAt_scatVec_apply v q hu.1 hu.2).mul_const _

theorem differentiableAt_msCleared_left {Y : ℝ} (hY : 0 < Y) (v w : DeckSpace N) (u' : ℂ) {u : ℂ}
    (hu : u ∈ contDom N) : DifferentiableAt ℂ (fun u => msCleared u u' v w Y) u := by
  have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  unfold msCleared
  have hc : ∀ f : ℂ → ℂ, DifferentiableAt ℂ f u → DifferentiableAt ℂ (fun u => (Y : ℂ) ^ f u) u :=
    fun f hf => hf.const_cpow (Or.inl hY')
  refine ((differentiableAt_id.sub_const _).mul (((differentiableAt_const _).mul
    (hc _ ((differentiableAt_id.add_const _).sub_const _))).sub
      ((differentiableAt_bil_scatVec_left v _ hu).mul (hc _ ((differentiableAt_const _).sub
        differentiableAt_id |>.sub_const _))))).add
    (((differentiableAt_id.add_const _).sub_const _).mul (((differentiableAt_const _).mul
      (hc _ (differentiableAt_id.sub_const _))).sub
        ((differentiableAt_bil_scatVec_left v _ hu).mul (hc _ ((differentiableAt_const _).sub
          differentiableAt_id)))))

theorem msCleared_comm (u u' : ℂ) (v w : DeckSpace N) (Y : ℝ) :
    msCleared u u' v w Y = -msCleared u' u w v Y := by
  unfold msCleared
  rw [bil_comm v w, bil_comm (scatVec u v) (scatVec u' w), bil_comm v (scatVec u' w),
    bil_comm (scatVec u v) w]
  ring_nf

theorem differentiableAt_msCleared_right {Y : ℝ} (hY : 0 < Y) (v w : DeckSpace N) (u : ℂ) {u' : ℂ}
    (hu' : u' ∈ contDom N) : DifferentiableAt ℂ (fun u' => msCleared u u' v w Y) u' := by
  simp_rw [msCleared_comm u _ v w Y]
  exact (differentiableAt_msCleared_left hY w v u hu').neg

/-- The defect `(u - u')(u + u' - 1) P(u, u') - R(u, u')` of the cleared relation. -/
def msDefect (Y : ℝ) (u : ℂ) (v : DeckSpace N) (u' : ℂ) (w : DeckSpace N) : ℂ :=
  (u - u') * (u + u' - 1) * truncPairing Y u v u' w - msCleared u u' v w Y

theorem differentiableAt_msDefect_left {Y : ℝ} (hY : 1 ≤ Y) (v w : DeckSpace N) {u' : ℂ}
    (hu' : u' ∈ contDom N) {u : ℂ} (hu : u ∈ contDom N) :
    DifferentiableAt ℂ (fun u => msDefect Y u v u' w) u :=
  ((((differentiableAt_id.sub_const _).mul ((differentiableAt_id.add_const _).sub_const _)).mul
    (differentiableAt_truncPairing_left hY v w hu' hu))).sub
      (differentiableAt_msCleared_left (by linarith) v w u' hu)

theorem differentiableAt_msDefect_right {Y : ℝ} (hY : 1 ≤ Y) (v w : DeckSpace N) {u : ℂ}
    (hu : u ∈ contDom N) {u' : ℂ} (hu' : u' ∈ contDom N) :
    DifferentiableAt ℂ (fun u' => msDefect Y u v u' w) u' :=
  (((((differentiableAt_const _).sub differentiableAt_id).mul
    ((differentiableAt_const _).add differentiableAt_id |>.sub_const _)).mul
    (differentiableAt_truncPairing_right hY v w hu hu'))).sub
      (differentiableAt_msCleared_right (by linarith) v w u hu')

theorem msDefect_eq_zero_region (hN : 2 ≤ N) {u u' : ℂ} (hu' : 1 < u'.re) (huu : u'.re < u.re)
    {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) :
    msDefect Y u v u' w = 0 := by
  have h1 : u - u' ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : u + u' - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold msDefect truncPairing
  rw [deckMaassSelberg_region hN hu' huu hv hw hY, msCleared_eq_mul h1 h2, sub_self]

/-- The punctured half-plane `{Re > 1/2} \ {1}`. -/
abbrev halfPlaneDom : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1}

theorem halfPlaneDom_subset : halfPlaneDom ⊆ contDom N := fun _ hs => mem_contDom_of_half_lt hs.1 hs.2

theorem analyticOnNhd_of_differentiableAt {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ s ∈ U, DifferentiableAt ℂ f s) : AnalyticOnNhd ℂ f U :=
  DifferentiableOn.analyticOnNhd (fun s hs => (hf s hs).differentiableWithinAt) hU

/-- **The deck Maass–Selberg relation on `{Re > 1/2} \ {1}` in both parameters** (cleared form). -/
theorem msDefect_eq_zero (hN : 2 ≤ N) {u u' : ℂ} (hu : u ∈ halfPlaneDom) (hu' : u' ∈ halfPlaneDom)
    {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) :
    msDefect Y u v u' w = 0 := by
  have hopen := SelbergEisensteinCuspExpansion.isOpen_punctured
  have hconn := SelbergEisensteinCuspExpansion.isPreconnected_punctured
  -- first variable, for `Re u' > 1`
  have step1 : ∀ u' : ℂ, 1 < u'.re → ∀ u ∈ halfPlaneDom, msDefect Y u v u' w = 0 := by
    intro u' hu'1 u hu
    have hu'd : u' ∈ contDom N := mem_contDom_of_half_lt (by linarith) (by
      intro h; rw [h] at hu'1; norm_num at hu'1)
    have hf : AnalyticOnNhd ℂ (fun u => msDefect Y u v u' w) halfPlaneDom :=
      analyticOnNhd_of_differentiableAt hopen fun s hs =>
        differentiableAt_msDefect_left hY v w hu'd (halfPlaneDom_subset hs)
    have hmem : u' + 1 ∈ halfPlaneDom := ⟨by simp; linarith, by
      intro h; have := congrArg Complex.re h; simp at this; linarith⟩
    have hev : (fun u => msDefect Y u v u' w) =ᶠ[𝓝 (u' + 1)] 0 := by
      have : {s : ℂ | u'.re < s.re} ∈ 𝓝 (u' + 1) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with s hs
      exact msDefect_eq_zero_region hN hu'1 hs hv hw hY
    exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hmem hev hu
  -- second variable
  have hud : u ∈ contDom N := halfPlaneDom_subset hu
  have hf : AnalyticOnNhd ℂ (fun u' => msDefect Y u v u' w) halfPlaneDom :=
    analyticOnNhd_of_differentiableAt hopen fun s hs =>
      differentiableAt_msDefect_right hY v w hud (halfPlaneDom_subset hs)
  have hmem : (2 : ℂ) ∈ halfPlaneDom := ⟨by norm_num, by norm_num⟩
  have hev : (fun u' => msDefect Y u v u' w) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact step1 s hs u hu
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hmem hev hu'

/-! ## The critical line -/

theorem line_mem_contDom {t : ℝ} (ht : t ≠ 0) (σ₀ : ℝ) (hσ₀ : σ₀ = 1 / 2) :
    (σ₀ : ℂ) + t * Complex.I ∈ contDom N := by
  subst hσ₀
  refine ⟨mem_Wset_of_half_le (N + 1) (by simp) ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; simp at this; exact ht this
  · intro h; have := congrArg Complex.im h; simp at this; exact ht this

theorem msDefect_eq_zero_left_line (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {v w : DeckSpace N}
    (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) {u' : ℂ} (hu' : u' ∈ halfPlaneDom) :
    msDefect Y ((1 / 2 : ℝ) + t * Complex.I) v u' w = 0 := by
  set u₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
  have hu₀ : u₀ ∈ contDom N := line_mem_contDom ht _ rfl
  have hcont : ContinuousAt (fun u => msDefect Y u v u' w) u₀ :=
    (differentiableAt_msDefect_left hY v w (halfPlaneDom_subset hu') hu₀).continuousAt
  have hshift : Tendsto (fun ε : ℝ => u₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝 u₀) := by
    have : Tendsto (fun ε : ℝ => u₀ + (ε : ℂ)) (𝓝 0) (𝓝 (u₀ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hT := hcont.tendsto.comp hshift
  have h0 : (fun ε : ℝ => msDefect Y (u₀ + (ε : ℂ)) v u' w) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    refine msDefect_eq_zero hN ⟨?_, ?_⟩ hu' hv hw hY
    · simp only [u₀, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      simp only [mem_Ioi] at hε
      linarith
    · intro h; have := congrArg Complex.im h; simp [u₀] at this; exact ht this
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' h0.symm)

/-- **The cleared relation at the pair `(1/2 + it, 1/2 − it)`.** -/
theorem msDefect_eq_zero_line (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {v w : DeckSpace N}
    (hv : IsCuspVec v) (hw : IsCuspVec w) {Y : ℝ} (hY : 1 ≤ Y) :
    msDefect Y ((1 / 2 : ℝ) + t * Complex.I) v ((1 / 2 : ℝ) + (-t) * Complex.I) w = 0 := by
  set u₀ : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
  set u₁ : ℂ := ((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I
  have hu₀ : u₀ ∈ contDom N := line_mem_contDom ht _ rfl
  have hu₁ : u₁ ∈ contDom N := line_mem_contDom (neg_ne_zero.2 ht) _ rfl
  obtain ⟨R, hR, hcb⟩ := exists_closedBall_subset_contDom hu₁
  have hball : ball u₁ R ⊆ contDom N := ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith)) |>.trans hcb
  set U := halfPlaneDom ∪ ball u₁ R
  have hUo : IsOpen U := SelbergEisensteinCuspExpansion.isOpen_punctured.union isOpen_ball
  have hp : u₁ + ((R / 2 : ℝ) : ℂ) ∈ halfPlaneDom ∩ ball u₁ R := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [u₁, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im]
      linarith
    · intro h; have := congrArg Complex.im h; simp [u₁] at this; exact ht this
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
  have hUc : IsPreconnected U :=
    SelbergEisensteinCuspExpansion.isPreconnected_punctured.union _ hp.1 hp.2 (convex_ball _ _).isPreconnected
  have hUsub : U ⊆ contDom N := union_subset halfPlaneDom_subset hball
  have hf : AnalyticOnNhd ℂ (fun u' => msDefect Y u₀ v u' w) U :=
    analyticOnNhd_of_differentiableAt hUo fun s hs =>
      differentiableAt_msDefect_right hY v w hu₀ (hUsub hs)
  have hmem : (2 : ℂ) ∈ U := Or.inl ⟨by norm_num, by norm_num⟩
  have hev : (fun u' => msDefect Y u₀ v u' w) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    filter_upwards [SelbergEisensteinCuspExpansion.isOpen_punctured.mem_nhds
      (show (2 : ℂ) ∈ halfPlaneDom from ⟨by norm_num, by norm_num⟩)] with s hs
    exact msDefect_eq_zero_left_line hN ht hv hw hY hs
  have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hmem hev
    (Or.inr (mem_ball_self hR))
  simpa [u₁] using this

theorem bil_scatVec_of_msDefect {u u' : ℂ} {v w : DeckSpace N} (h : msDefect 1 u v u' w = 0)
    (h1 : u + u' - 1 = 0) (h2 : u - u' ≠ 0) : bil (scatVec u v) (scatVec u' w) = bil v w := by
  unfold msDefect msCleared at h
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  have key : (u - u') * (bil v w - bil (scatVec u v) (scatVec u' w)) = 0 := by
    linear_combination (-1 : ℂ) * h + ((u - u') * truncPairing 1 u v u' w -
      (bil v (scatVec u' w) - bil (scatVec u v) w)) * h1
  have := (mul_eq_zero.1 key).resolve_left h2
  linear_combination -this

/-- **The functional equation of the scattering operator on the critical line** (transposed form):
`⟨Φ̃(1/2 + it) v, Φ̃(1/2 − it) w⟩_β = ⟨v, w⟩_β` for `v, w ∈ V_∞`, `t ≠ 0`. -/
theorem bil_scatVec_line (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {v w : DeckSpace N} (hv : IsCuspVec v)
    (hw : IsCuspVec w) :
    bil (scatVec ((1 / 2 : ℝ) + t * Complex.I) v) (scatVec ((1 / 2 : ℝ) + (-t) * Complex.I) w) =
      bil v w := by
  refine bil_scatVec_of_msDefect (msDefect_eq_zero_line hN ht hv hw (le_refl 1)) (by push_cast; ring) ?_
  intro h
  have := congrArg Complex.im h
  simp at this
  exact ht (by linarith)

end

end GaloisForLFunctions.RHTower.DeckPointPair
