import GaloisForLFunctions.HTGeometry.LaplaceFormationSplitCycle

/-!
# The forced defect history of a Laplace formation

For a nontrivial half-line formation law with visible amplitudes `a_k` and hidden amplitudes
`d_k = √(1 - a_k²)`, the history map

`(W b)_{k,j} = d_k a_k^j b_k`,   `W : ℓ^∞ → ℓ^∞(ℓ²(ℕ₀))`,

is an isometry intertwining the visible formation with the backward history shift,
`S* W = W A`.  It is the unique diagonal isometry with nonnegative amplitudes doing so.  The state
decoder `(Q^∞ y)_k = ∑_j d_k a_k^j y_{k,j}` is a contraction with `Q^∞ W = I`, and at every finite
horizon `|b_k|² = a_k^{2N} |b_k|² + ∑_{j<N} d_k² a_k^{2j} |b_k|²`.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- History space `ℓ^∞(ℓ²(ℕ₀))`. -/
abbrev LaplaceHistorySpace := lp (fun _ : ℕ => lp (fun _ : ℕ => ℂ) 2) ⊤

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

/-- History amplitude `d_k a_k^j`. -/
def historyAmplitude (k j : ℕ) : ℝ := ν.hidden k * ν.visible k ^ j

theorem historyAmplitude_nonneg (k j : ℕ) : 0 ≤ ν.historyAmplitude k j :=
  mul_nonneg (ν.hidden_pos k).le (pow_nonneg (ν.visible_pos k).le j)

/-- `∑_j (d_k a_k^j)² = 1`. -/
theorem hasSum_historyAmplitude_sq (k : ℕ) :
    HasSum (fun j => ν.historyAmplitude k j ^ 2) 1 := by
  have ha2 : ν.visible k ^ 2 < 1 := by nlinarith [ν.visible_pos k, ν.visible_lt_one k]
  have hgeom := hasSum_geometric_of_lt_one (sq_nonneg (ν.visible k)) ha2
  have h := hgeom.mul_left (ν.hidden k ^ 2)
  have hd : ν.hidden k ^ 2 = 1 - ν.visible k ^ 2 := by
    have := ν.visible_sq_add_hidden_sq k; linarith
  rw [hd, mul_inv_cancel₀ (by linarith)] at h
  refine h.congr_fun fun j => ?_
  rw [historyAmplitude, mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hd]

theorem memℓp_historyRow (k : ℕ) (z : ℂ) :
    Memℓp (fun j : ℕ => ((ν.historyAmplitude k j : ℝ) : ℂ) * z) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (ν.historyAmplitude_nonneg k _), mul_pow]
  exact ((ν.hasSum_historyAmplitude_sq k).mul_right _).summable

/-- One history row `(d_k a_k^j z)_j ∈ ℓ²`. -/
def historyRow (k : ℕ) (z : ℂ) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun j => ((ν.historyAmplitude k j : ℝ) : ℂ) * z, ν.memℓp_historyRow k z⟩

theorem norm_historyRow (k : ℕ) (z : ℂ) : ‖ν.historyRow k z‖ = ‖z‖ := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (ν.historyRow k z)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have h2 : HasSum (fun j => ‖(ν.historyRow k z) j‖ ^ 2) (‖z‖ ^ 2) := by
    have := (ν.hasSum_historyAmplitude_sq k).mul_right (‖z‖ ^ 2)
    rw [one_mul] at this
    refine this.congr_fun fun j => ?_
    change ‖((ν.historyAmplitude k j : ℝ) : ℂ) * z‖ ^ 2 = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ν.historyAmplitude_nonneg k j), mul_pow]
  have := h.unique h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- The forced history `W_ν b = (d_k a_k^j b_k)`. -/
def history (b : LaplaceResponseSpace) : LaplaceHistorySpace :=
  ⟨fun k => ν.historyRow k (b k), memℓp_infty ⟨‖b‖, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    rw [ν.norm_historyRow]
    exact lp.norm_apply_le_norm (by simp) b k⟩⟩

theorem norm_history (b : LaplaceResponseSpace) : ‖ν.history b‖ = ‖b‖ := by
  rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
  congr 1
  funext k
  exact ν.norm_historyRow k (b k)

end HalfLineFormationLaw

/-- Backward shift of an `ℓ²` row: `(x_{j+1})_j`. -/
def rowBackwardShift (x : lp (fun _ : ℕ => ℂ) 2) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun j => x (j + 1), by
    refine memℓp_gen ?_
    have h := lp.hasSum_norm (p := 2) (by norm_num) x
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h ⊢
    exact (summable_nat_add_iff 1).2 h.summable⟩

theorem norm_rowBackwardShift_le (x : lp (fun _ : ℕ => ℂ) 2) : ‖rowBackwardShift x‖ ≤ ‖x‖ := by
  have hx := lp.hasSum_norm (p := 2) (by norm_num) x
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (rowBackwardShift x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hs
  have htail := hx.summable.sum_add_tsum_nat_add 1
  have hsq : ‖rowBackwardShift x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← hs.tsum_eq, ← hx.tsum_eq, ← htail]
    have : 0 ≤ ∑ i ∈ Finset.range 1, ‖x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    change ∑' j, ‖x (j + 1)‖ ^ 2 ≤ _
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Backward shift `S*` in the history coordinate. -/
def historyBackwardShift (y : LaplaceHistorySpace) : LaplaceHistorySpace :=
  ⟨fun k => rowBackwardShift (y k), memℓp_infty ⟨‖y‖, by
    rintro _ ⟨k, rfl⟩
    exact (norm_rowBackwardShift_le _).trans (lp.norm_apply_le_norm (by simp) y k)⟩⟩

namespace HalfLineFormationLaw

variable (ν : HalfLineFormationLaw)

/-- **Theorem 5.1 (LFD.19)** The history intertwines: `S* W_ν = W_ν A_ν`. -/
theorem historyBackwardShift_history (b : LaplaceResponseSpace) :
    historyBackwardShift (ν.history b) = ν.history (ν.visibleFormation b) := by
  apply lp.ext
  funext k
  apply lp.ext
  funext j
  change ((ν.historyAmplitude k (j + 1) : ℝ) : ℂ) * b k =
    ((ν.historyAmplitude k j : ℝ) : ℂ) * ((ν.visible k : ℂ) * b k)
  rw [historyAmplitude, historyAmplitude, pow_succ]
  push_cast
  ring

/-- **Theorem 5.1 (LFD.20)–(LFD.21), uniqueness.**  A diagonal map with nonnegative amplitudes
`(V b)_{k,j} = v_{k,j} b_k` that is isometric and intertwines `S* V = V A_ν` is the forced
history: `v_{k,j} = d_k a_k^j`. -/
theorem history_unique (v : ℕ → ℕ → ℝ) (hv : ∀ k j, 0 ≤ v k j)
    (V : LaplaceResponseSpace → LaplaceHistorySpace)
    (hV : ∀ b k j, (V b) k j = ((v k j : ℝ) : ℂ) * b k)
    (hiso : ∀ b, ‖V b‖ = ‖b‖)
    (hint : ∀ b, historyBackwardShift (V b) = V (ν.visibleFormation b)) :
    ∀ k j, v k j = ν.historyAmplitude k j := by
  intro k
  classical
  let e : LaplaceResponseSpace := lp.single ⊤ k 1
  have he : ∀ k', e k' = if k' = k then 1 else 0 := fun k' => by
    simp [e, lp.single_apply, Pi.single_apply]
  -- intertwining at coordinate `k`
  have hrec : ∀ j, v k (j + 1) = ν.visible k * v k j := by
    intro j
    have h := congrArg (fun y : LaplaceHistorySpace => (y k) j) (hint e)
    simp only at h
    change (V e) k (j + 1) = (V (ν.visibleFormation e)) k j at h
    rw [hV, hV, he, if_pos rfl] at h
    change ((v k (j + 1) : ℝ) : ℂ) * 1 = ((v k j : ℝ) : ℂ) * ((ν.visible k : ℂ) * e k) at h
    rw [he, if_pos rfl] at h
    have h' : ((v k (j + 1) : ℝ) : ℂ) = ((ν.visible k * v k j : ℝ) : ℂ) := by
      push_cast; linear_combination h
    exact_mod_cast h'
  have hgeom : ∀ j, v k j = ν.visible k ^ j * v k 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hrec, ih, pow_succ]; ring
  -- isometry at the coordinate vector `e`
  have hnorm_e : ‖e‖ = 1 := by
    simp [e, lp.norm_single]
  have hrow : ‖(V e) k‖ = 1 := by
    have hle : ‖(V e) k‖ ≤ ‖V e‖ := lp.norm_apply_le_norm (by simp) _ k
    have hge : ‖V e‖ ≤ ‖(V e) k‖ := by
      refine lp.norm_le_of_forall_le (norm_nonneg _) fun k' => ?_
      by_cases hk : k' = k
      · rw [hk]
      · have hz : (V e) k' = 0 := by
          apply lp.ext; funext j
          change (V e) k' j = 0
          rw [hV, he, if_neg hk, mul_zero]
        rw [hz, norm_zero]; exact norm_nonneg _
    rw [← hiso e, hnorm_e] at *
    linarith
  have hsum : HasSum (fun j => v k j ^ 2) 1 := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) ((V e) k)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, hrow, one_pow] at h
    refine h.congr_fun fun j => ?_
    rw [hV, he, if_pos rfl, mul_one, Complex.norm_real, Real.norm_of_nonneg (hv k j)]
  have ha2 : ν.visible k ^ 2 < 1 := by nlinarith [ν.visible_pos k, ν.visible_lt_one k]
  have hgeom_sum : HasSum (fun j => v k j ^ 2) (v k 0 ^ 2 / (1 - ν.visible k ^ 2)) := by
    have hg := (hasSum_geometric_of_lt_one (sq_nonneg (ν.visible k)) ha2).mul_left (v k 0 ^ 2)
    rw [← div_eq_mul_inv] at hg
    refine hg.congr_fun fun j => ?_
    rw [hgeom j, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    ring
  have hv0sq : v k 0 ^ 2 = ν.hidden k ^ 2 := by
    have := hsum.unique hgeom_sum
    have hd : ν.hidden k ^ 2 = 1 - ν.visible k ^ 2 := by
      have := ν.visible_sq_add_hidden_sq k; linarith
    rw [hd]
    have hne : 1 - ν.visible k ^ 2 ≠ 0 := by linarith
    rw [eq_div_iff hne, one_mul] at this
    linarith
  have hv0 : v k 0 = ν.hidden k :=
    (pow_left_inj₀ (hv k 0) (ν.hidden_pos k).le two_ne_zero).1 hv0sq
  intro j
  rw [hgeom j, hv0, historyAmplitude]
  ring

/-! ## State decoder and finite conservation -/

/-- **(LFD.22)** State decoder `(Q^∞ y)_k = ⟪(d_k a_k^j)_j, y_k⟫ = ∑_j d_k a_k^j y_{k,j}`. -/
def historyDecoder (y : LaplaceHistorySpace) : LaplaceResponseSpace :=
  ⟨fun k => inner ℂ (ν.historyRow k 1) (y k), memℓp_infty ⟨‖y‖, by
    rintro _ ⟨k, rfl⟩
    refine (norm_inner_le_norm _ _).trans ?_
    rw [ν.norm_historyRow, norm_one, one_mul]
    exact lp.norm_apply_le_norm (by simp) y k⟩⟩

theorem historyDecoder_apply (y : LaplaceHistorySpace) (k : ℕ) :
    ν.historyDecoder y k = ∑' j, ((ν.historyAmplitude k j : ℝ) : ℂ) * (y k) j := by
  change inner ℂ (ν.historyRow k 1) (y k) = _
  rw [lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  change inner ℂ (((ν.historyAmplitude k j : ℝ) : ℂ) * 1) ((y k) j) = _
  rw [mul_one, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

theorem norm_historyDecoder_le (y : LaplaceHistorySpace) : ‖ν.historyDecoder y‖ ≤ ‖y‖ :=
  lp.norm_le_of_forall_le (norm_nonneg _) fun k => by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [ν.norm_historyRow, norm_one, one_mul]
    exact lp.norm_apply_le_norm (by simp) y k

/-- **(LFD.23)** `Q^∞ W_ν = I`. -/
theorem historyDecoder_history (b : LaplaceResponseSpace) :
    ν.historyDecoder (ν.history b) = b := by
  apply lp.ext
  funext k
  change inner ℂ (ν.historyRow k 1) (ν.historyRow k (b k)) = b k
  have hrow : ν.historyRow k (b k) = b k • ν.historyRow k 1 := by
    apply lp.ext; funext j
    change ((ν.historyAmplitude k j : ℝ) : ℂ) * b k = b k * (((ν.historyAmplitude k j : ℝ) : ℂ) * 1)
    ring
  rw [hrow, inner_smul_right, inner_self_eq_norm_sq_to_K, ν.norm_historyRow, norm_one]
  simp

/-- The state decoder `Q^∞` as a bounded operator `ℓ^∞(ℓ²) → ℓ^∞`. -/
def historyDecoderCLM : LaplaceHistorySpace →L[ℂ] LaplaceResponseSpace :=
  LinearMap.mkContinuous
    { toFun := ν.historyDecoder
      map_add' := fun y z => by
        apply lp.ext; funext k
        change inner ℂ (ν.historyRow k 1) (y k + z k) =
          inner ℂ (ν.historyRow k 1) (y k) + inner ℂ (ν.historyRow k 1) (z k)
        exact inner_add_right _ _ _
      map_smul' := fun c y => by
        apply lp.ext; funext k
        change inner ℂ (ν.historyRow k 1) (c • y k) = c * inner ℂ (ν.historyRow k 1) (y k)
        exact inner_smul_right _ _ _ }
    1 (fun y => by rw [one_mul]; exact ν.norm_historyDecoder_le y)

theorem historyDecoderCLM_apply (y : LaplaceHistorySpace) :
    ν.historyDecoderCLM y = ν.historyDecoder y := rfl

/-- **(LFD.22)** `‖Q^∞‖ = 1`. -/
theorem norm_historyDecoderCLM : ‖ν.historyDecoderCLM‖ = 1 := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ zero_le_one _) ?_
  classical
  set b : LaplaceResponseSpace := lp.single ⊤ 0 (1 : ℂ)
  have hb : ‖b‖ = 1 := by rw [lp.norm_single (by simp), norm_one]
  have h := ν.historyDecoderCLM.le_opNorm (ν.history b)
  rw [historyDecoderCLM_apply, ν.historyDecoder_history, ν.norm_history, hb, mul_one] at h
  exact h

/-- **(LFD.24)** Finite-horizon conservation: terminal visible work plus ordered hidden-history
work equals initial work. -/
theorem finite_horizon_conservation (k N : ℕ) (z : ℂ) :
    ‖z‖ ^ 2 = ν.visible k ^ (2 * N) * ‖z‖ ^ 2 +
      ∑ j ∈ Finset.range N, ν.hidden k ^ 2 * ν.visible k ^ (2 * j) * ‖z‖ ^ 2 := by
  have hd : ν.hidden k ^ 2 = 1 - ν.visible k ^ 2 := by
    have := ν.visible_sq_add_hidden_sq k; linarith
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, hd]
    rw [hd] at ih
    have : ν.visible k ^ (2 * (N + 1)) = ν.visible k ^ (2 * N) * ν.visible k ^ 2 := by
      rw [mul_add, mul_one, pow_add]
    rw [this]
    linarith [ih]

end HalfLineFormationLaw

end GaloisForLFunctions.HTGeometry
