import GaloisForLFunctions.HTGeometry.PoincareHopf.IndexNeighborhood

/-!
# Invariance of the index under a change of chart

If `ψ` is injective and open near an isolated zero `p` of `v`, has invertible Jacobian at `p`, and
`w` is the pushforward of `v`, meaning `w ∘ ψ = Dψ · v`, then `w` has the same index at `ψ p` as `v`
has at `p`.

Two sign changes cancel.  Transporting the domain by `ψ` multiplies the degree by the sign of
`det Dψ`; replacing the varying matrix `Dψ x` by the constant `Dψ p`—legitimate because the affine
path between them stays bounded below near `p`—and pulling the constant matrix out multiplies by the
same sign again.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ}

/-- A crude operator bound for a matrix acting on the sup-normed space. -/
theorem norm_mulVec_le (M : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    ‖M *ᵥ z‖ ≤ (∑ a, ∑ b, |M a b|) * ‖z‖ := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  have h1 : ‖(M *ᵥ z) a‖ ≤ (∑ b, |M a b|) * ‖z‖ := by
    rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
    calc |∑ i, M a i * z i| ≤ ∑ i, |M a i * z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |M a i| * ‖z‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm z b) (abs_nonneg _)
      _ = (∑ b, |M a b|) * ‖z‖ := by rw [Finset.sum_mul]
  refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hz)
  exact Finset.single_le_sum (f := fun a' => ∑ b, |M a' b|)
    (fun a' _ => by positivity) (Finset.mem_univ a)

/-- A continuous function that is positive on a compact set is bounded below on it. -/
theorem exists_pos_two_lt_on_compact {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    {h : (Fin n → ℝ) → ℝ} (hc : Continuous h) (hpos : ∀ x ∈ S, 0 < h x) :
    ∃ ρ > 0, ∀ x ∈ S, ρ + ρ < h x := by
  rcases eq_empty_or_nonempty S with hemp | hne
  · exact ⟨1, one_pos, fun x hx => absurd hx (by rw [hemp]; exact notMem_empty x)⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hc.continuousOn
    refine ⟨h x₀ / 3, by linarith [hpos x₀ hx₀], fun x hx => ?_⟩
    have hle : h x₀ ≤ h x := hmin hx
    linarith [hpos x₀ hx₀]

section

variable {ψ : (Fin n → ℝ) → (Fin n → ℝ)} {p : Fin n → ℝ}

/-- The `ℓ¹` distance between the Jacobian at `x` and at `p`. -/
noncomputable def jacGap (ψ : (Fin n → ℝ) → (Fin n → ℝ)) (p x : Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, |jac ψ x a b - jac ψ p a b|

theorem continuous_jacGap (hψ : ContDiff ℝ 2 ψ) (p : Fin n → ℝ) :
    Continuous (jacGap ψ p) := by
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((contDiff_jacEntry hψ a b).continuous.sub continuous_const).abs

@[simp] theorem jacGap_self (ψ : (Fin n → ℝ) → (Fin n → ℝ)) (p : Fin n → ℝ) :
    jacGap ψ p p = 0 := by simp [jacGap]

/-- On the affine path between the two Jacobians the image of a vector stays bounded below. -/
theorem norm_path_mulVec_ge {c : ℝ} (hlow : ∀ z : Fin n → ℝ, c * ‖z‖ ≤ ‖matVec (jac ψ p) z‖)
    (x : Fin n → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : Fin n → ℝ) :
    (c - jacGap ψ p x) * ‖z‖
      ≤ ‖((1 - t) • jac ψ x + t • jac ψ p) *ᵥ z‖ := by
  have hsplit : ((1 - t) • jac ψ x + t • jac ψ p) *ᵥ z
      = (jac ψ p) *ᵥ z + (1 - t) • ((jac ψ x - jac ψ p) *ᵥ z) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hb : ‖(jac ψ x - jac ψ p) *ᵥ z‖ ≤ jacGap ψ p x * ‖z‖ := by
    have h := norm_mulVec_le (jac ψ x - jac ψ p) z
    simpa [jacGap, Matrix.sub_apply] using h
  have hs : ‖(1 - t) • ((jac ψ x - jac ψ p) *ᵥ z)‖ ≤ jacGap ψ p x * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith [norm_nonneg ((jac ψ x - jac ψ p) *ᵥ z)]
  have hlb : ‖(jac ψ p) *ᵥ z‖ - ‖(1 - t) • ((jac ψ x - jac ψ p) *ᵥ z)‖
      ≤ ‖(jac ψ p) *ᵥ z + (1 - t) • ((jac ψ x - jac ψ p) *ᵥ z)‖ := by
    have h := norm_sub_le ((jac ψ p) *ᵥ z + (1 - t) • ((jac ψ x - jac ψ p) *ᵥ z))
      ((1 - t) • ((jac ψ x - jac ψ p) *ᵥ z))
    simp only [add_sub_cancel_right] at h
    linarith
  have hc := hlow z
  rw [matVec_apply] at hc
  rw [hsplit]
  linarith

/-- Along the affine path between the two Jacobians the determinant never vanishes. -/
theorem path_det_ne_zero {c : ℝ}
    (hlow : ∀ z : Fin n → ℝ, c * ‖z‖ ≤ ‖matVec (jac ψ p) z‖)
    {x : Fin n → ℝ} (hgap : jacGap ψ p x < c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • jac ψ x + t • jac ψ p).det ≠ 0 := by
  set M := (1 - t) • jac ψ x + t • jac ψ p with hM
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    have h0 : M *ᵥ (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    have hb := norm_path_mulVec_ge hlow x ht0 ht1 (u - v)
    rw [← hM, h0, norm_zero] at hb
    have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
    have hzero : ‖u - v‖ = 0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hunit).ne_zero

/-- Near `p` the Jacobian determinant of `ψ` keeps the sign it has at `p`. -/
theorem det_jac_pos_iff {c : ℝ}
    (hlow : ∀ z : Fin n → ℝ, c * ‖z‖ ≤ ‖matVec (jac ψ p) z‖)
    {x : Fin n → ℝ} (hgap : jacGap ψ p x < c) :
    0 < (jac ψ x).det ↔ 0 < (jac ψ p).det := by
  set f : ℝ → ℝ := fun t => ((1 - t) • jac ψ x + t • jac ψ p).det with hf
  have hcont : Continuous f := by
    refine continuous_matrix_det (N := fun t : ℝ => (1 - t) • jac ψ x + t • jac ψ p) ?_
    intro a b
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ 0 := fun t ht => path_det_ne_zero hlow hgap ht.1 ht.2
  have hf0 : f 0 = (jac ψ x).det := by simp [hf]
  have hf1 : f 1 = (jac ψ p).det := by simp [hf]
  rw [← hf0, ← hf1]
  constructor
  · intro h0
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' (zero_le_one (α := ℝ)) hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨hcon, le_of_lt h0⟩)
    exact hne t ht hzero
  · intro h1
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (zero_le_one (α := ℝ)) hcont.continuousOn
      (show (0 : ℝ) ∈ Icc (f 0) (f 1) from ⟨hcon, le_of_lt h1⟩)
    exact hne t ht hzero

theorem det_jac_ne_zero_of_gap {c : ℝ}
    (hlow : ∀ z : Fin n → ℝ, c * ‖z‖ ≤ ‖matVec (jac ψ p) z‖)
    {x : Fin n → ℝ} (hgap : jacGap ψ p x < c) : (jac ψ x).det ≠ 0 := by
  have h := path_det_ne_zero hlow hgap (t := 0) le_rfl zero_le_one
  simpa using h

theorem mulVec_path (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (z : Fin n → ℝ) :
    A *ᵥ z + t • (B *ᵥ z - A *ᵥ z) = ((1 - t) • A + t • B) *ᵥ z := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.add_apply, Matrix.smul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The pushforward has an isolated zero at `ψ p`, with the same index. -/
theorem index_pushforward_aux {v w : (Fin n → ℝ) → (Fin n → ℝ)} {ε₀ : ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w) (hε₀ : 0 < ε₀)
    (hinj : Set.InjOn ψ (Metric.closedBall p ε₀))
    (hopenmap : ∀ S ⊆ Metric.ball p ε₀, IsOpen S → IsOpen (ψ '' S))
    (hdet : (jac ψ p).det ≠ 0)
    (hiso : ∀ x ∈ Metric.closedBall p ε₀, x ≠ p → v x ≠ 0)
    (htrans : ∀ x ∈ Metric.closedBall p ε₀, w (ψ x) = matVec (jac ψ x) (v x)) :
    (∃ ε > 0, IsolatingRadius w (ψ p) ε) ∧ index w (ψ p) = index v p := by
  classical
  obtain ⟨c, hcpos, hlow⟩ := exists_lower_bound_matVec hdet
  have hgapcont : Continuous (jacGap ψ p) := continuous_jacGap hψ p
  have hopenset : IsOpen {x : Fin n → ℝ | jacGap ψ p x < c} := isOpen_lt hgapcont continuous_const
  have hpmem : p ∈ {x : Fin n → ℝ | jacGap ψ p x < c} := by simpa using hcpos
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopenset p hpmem
  set ε := min ε₀ (δ / 2) with hεdef
  have hεpos : 0 < ε := lt_min hε₀ (by linarith)
  have hεle₀ : ε ≤ ε₀ := min_le_left _ _
  have hsubball : Metric.closedBall p ε ⊆ Metric.closedBall p ε₀ :=
    Metric.closedBall_subset_closedBall hεle₀
  have hgaplt : ∀ x ∈ Metric.closedBall p ε, jacGap ψ p x < c := by
    intro x hx
    refine hδ ?_
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    have hle : ε ≤ δ / 2 := min_le_right _ _
    linarith
  have hisoε : IsolatingRadius v p ε := ⟨hεpos, fun x hx hxp => hiso x (hsubball hx) hxp⟩
  have hsphere_ne : ∀ x ∈ frontier (Metric.ball p ε), x ≠ p ∧ x ∈ Metric.closedBall p ε := by
    intro x hx
    have hnx : ‖x - p‖ = ε := frontier_ball_norm hx
    refine ⟨fun h => by rw [h, sub_self, norm_zero] at hnx; linarith, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, hnx]
  have hvfront : ∀ x ∈ frontier (Metric.ball p ε), v x ≠ 0 := by
    intro x hx
    obtain ⟨hxp, hxb⟩ := hsphere_ne x hx
    exact hiso x (hsubball hxb) hxp
  have hdetball : ∀ x ∈ Metric.closedBall p ε, (jac ψ x).det ≠ 0 :=
    fun x hx => det_jac_ne_zero_of_gap hlow (hgaplt x hx)
  have hmatne : ∀ x ∈ Metric.closedBall p ε, v x ≠ 0 → matVec (jac ψ x) (v x) ≠ 0 := by
    intro x hx hvx hcon
    have hinjx : Function.Injective (jac ψ x).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (hdetball x hx)))
    exact hvx (hinjx (by simpa using hcon))
  -- the image ball
  have hKc : IsCompact (Metric.closedBall p ε) := isCompact_closedBall p ε
  have hUopen : IsOpen (ψ '' Metric.ball p ε) :=
    hopenmap _ (Metric.ball_subset_ball hεle₀) Metric.isOpen_ball
  have hUb : Bornology.IsBounded (ψ '' Metric.ball p ε) :=
    ((hKc.image hψ.continuous).isBounded).subset
      (Set.image_mono Metric.ball_subset_closedBall)
  have hclosureU : closure (ψ '' Metric.ball p ε) ⊆ ψ '' Metric.closedBall p ε :=
    closure_minimal (Set.image_mono Metric.ball_subset_closedBall)
      (hKc.image hψ.continuous).isClosed
  have hwzero : ∀ y ∈ closure (ψ '' Metric.ball p ε), y ≠ ψ p → w y ≠ 0 := by
    intro y hy hyne
    obtain ⟨x, hx, rfl⟩ := hclosureU hy
    have hxp : x ≠ p := fun h => hyne (by rw [h])
    have hvx : v x ≠ 0 := hiso x (hsubball hx) hxp
    rw [htrans x (hsubball hx)]
    exact hmatne x hx hvx
  have hstep1 : index w (ψ p) = degree w (ψ '' Metric.ball p ε) 0 :=
    index_eq_degree_of_isolating hw hUopen hUb ⟨p, Metric.mem_ball_self hεpos, rfl⟩ hwzero
  have hisow : ∃ ε' > 0, IsolatingRadius w (ψ p) ε' := by
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hUopen (ψ p)
      ⟨p, Metric.mem_ball_self hεpos, rfl⟩
    refine ⟨r / 2, by linarith, ⟨by linarith, fun y hy hyne => ?_⟩⟩
    refine hwzero y (subset_closure (hrsub ?_)) hyne
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith
  refine ⟨hisow, ?_⟩
  have hfrontw : ∀ x ∈ frontier (Metric.ball p ε), w (ψ x) ≠ 0 := by
    intro x hx
    obtain ⟨hxp, hxb⟩ := hsphere_ne x hx
    rw [htrans x (hsubball hxb)]
    exact hmatne x hxb (hvfront x hx)
  have hinjclos : Set.InjOn ψ (closure (Metric.ball p ε)) :=
    hinj.mono (subset_trans Metric.closure_ball_subset_closedBall hsubball)
  -- the homotopy to the constant linearization
  have hstep3 : degree (fun x => w (ψ x)) (Metric.ball p ε) 0
      = degree (fun x => matVec (jac ψ p) (v x)) (Metric.ball p ε) 0 := by
    have hsph : IsCompact (frontier (Metric.ball p ε)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_frontier
        (Metric.isBounded_ball.closure.subset frontier_subset_closure)
    have hhcont : Continuous fun x => (c - jacGap ψ p x) * ‖v x‖ :=
      (continuous_const.sub hgapcont).mul hv.continuous.norm
    have hhpos : ∀ x ∈ frontier (Metric.ball p ε), 0 < (c - jacGap ψ p x) * ‖v x‖ := by
      intro x hx
      obtain ⟨hxp, hxb⟩ := hsphere_ne x hx
      have h1 : jacGap ψ p x < c := hgaplt x hxb
      have h2 : 0 < ‖v x‖ := norm_pos_iff.mpr (hvfront x hx)
      have h3 : 0 < c - jacGap ψ p x := by linarith
      exact mul_pos h3 h2
    obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_two_lt_on_compact hsph hhcont hhpos
    refine degree_eq_of_linPath (hw.comp hψ) ((matVec (jac ψ p)).contDiff.comp hv)
      Metric.isOpen_ball Metric.isBounded_ball hρpos ?_
    intro t ht x hx
    obtain ⟨hxp, hxb⟩ := hsphere_ne x hx
    have hrepr : linPath (fun y => w (ψ y)) (fun y => matVec (jac ψ p) (v y)) t x
        = ((1 - t) • jac ψ x + t • jac ψ p) *ᵥ (v x) := by
      show w (ψ x) + t • (matVec (jac ψ p) (v x) - w (ψ x))
          = ((1 - t) • jac ψ x + t • jac ψ p) *ᵥ (v x)
      rw [htrans x (hsubball hxb)]
      exact mulVec_path (jac ψ x) (jac ψ p) t (v x)
    have hb := norm_path_mulVec_ge hlow x ht.1 ht.2 (v x)
    have hlt := hρ x hx
    rw [sub_zero, hrepr]
    linarith
  have hstep4 : degree (fun x => matVec (jac ψ p) (v x)) (Metric.ball p ε) 0
      = (if 0 < (jac ψ p).det then (1 : ℝ) else -1) * degree v (Metric.ball p ε) 0 :=
    degree_leftComp_matVec hdet hv Metric.isOpen_ball Metric.isBounded_ball hvfront
  have hstep5 : degree v (Metric.ball p ε) 0 = index v p := (index_eq_degree hv hisoε).symm
  by_cases hsign : 0 < (jac ψ p).det
  · have hposall : ∀ x ∈ Metric.ball p ε, 0 < (jac ψ x).det := fun x hx =>
      (det_jac_pos_iff hlow (hgaplt x (Metric.ball_subset_closedBall hx))).mpr hsign
    have hstep2 : degree w (ψ '' Metric.ball p ε) 0
        = degree (fun x => w (ψ x)) (Metric.ball p ε) 0 :=
      degree_domain_change hψ hw Metric.isOpen_ball Metric.isBounded_ball hUopen hinjclos
        hposall hfrontw
    rw [hstep1, hstep2, hstep3, hstep4, if_pos hsign, one_mul, hstep5]
  · have hnegall : ∀ x ∈ Metric.ball p ε, (jac ψ x).det < 0 := by
      intro x hx
      have hne : (jac ψ x).det ≠ 0 := hdetball x (Metric.ball_subset_closedBall hx)
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · exact absurd ((det_jac_pos_iff hlow (hgaplt x (Metric.ball_subset_closedBall hx))).mp h)
          hsign
    have hstep2 : degree w (ψ '' Metric.ball p ε) 0
        = -degree (fun x => w (ψ x)) (Metric.ball p ε) 0 :=
      degree_domain_change_neg hψ hw Metric.isOpen_ball Metric.isBounded_ball hUopen hinjclos
        hnegall hfrontw
    rw [hstep1, hstep2, hstep3, hstep4, if_neg hsign, hstep5]
    ring

/-- **Invariance of the index under a change of chart.** -/
theorem index_pushforward {v w : (Fin n → ℝ) → (Fin n → ℝ)} {ε₀ : ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w) (hε₀ : 0 < ε₀)
    (hinj : Set.InjOn ψ (Metric.closedBall p ε₀))
    (hopenmap : ∀ S ⊆ Metric.ball p ε₀, IsOpen S → IsOpen (ψ '' S))
    (hdet : (jac ψ p).det ≠ 0)
    (hiso : ∀ x ∈ Metric.closedBall p ε₀, x ≠ p → v x ≠ 0)
    (htrans : ∀ x ∈ Metric.closedBall p ε₀, w (ψ x) = matVec (jac ψ x) (v x)) :
    index w (ψ p) = index v p :=
  (index_pushforward_aux hψ hv hw hε₀ hinj hopenmap hdet hiso htrans).2

/-- The pushforward field has an isolated zero at the image point. -/
theorem exists_isolating_pushforward {v w : (Fin n → ℝ) → (Fin n → ℝ)} {ε₀ : ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hv : ContDiff ℝ 2 v) (hw : ContDiff ℝ 2 w) (hε₀ : 0 < ε₀)
    (hinj : Set.InjOn ψ (Metric.closedBall p ε₀))
    (hopenmap : ∀ S ⊆ Metric.ball p ε₀, IsOpen S → IsOpen (ψ '' S))
    (hdet : (jac ψ p).det ≠ 0)
    (hiso : ∀ x ∈ Metric.closedBall p ε₀, x ≠ p → v x ≠ 0)
    (htrans : ∀ x ∈ Metric.closedBall p ε₀, w (ψ x) = matVec (jac ψ x) (v x)) :
    ∃ ε > 0, IsolatingRadius w (ψ p) ε :=
  (index_pushforward_aux hψ hv hw hε₀ hinj hopenmap hdet hiso htrans).1

end

end GaloisForLFunctions.HTGeometry.PoincareHopf
