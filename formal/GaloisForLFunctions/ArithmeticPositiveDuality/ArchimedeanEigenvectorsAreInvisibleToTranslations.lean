import GaloisForLFunctions.ArithmeticPositiveDuality.AFiniteArchimedeanSpectrumBlindsTheSuccessor

/-!
# Archimedean dilation eigenvectors are invisible to translations

Let `π` be a unitary representation of `Aff(ℚ)` on a complex inner product space. A vector `v` is
an *archimedean eigenvector of frequency `γ`* if `π(x ↦ ux)v = u^{iγ}v` for every `u > 0`.

**Theorem.**
* (`IsArchEigen.inner_translation_eq`) If `v` has frequency `γ`, then `⟨v, π(x ↦ x + b)v⟩ = α`
  for every `b ≠ 0`, with `α` real: the translates of `v` form a *blind family*, with Gram
  matrix `α + (‖v‖² − α)δ_{xy}`.
* (`IsArchEigen.inner_translation_eq_zero`) If `v, w` have frequencies `γ ≠ γ'`, then
  `⟨w, π(x ↦ x + b)v⟩ = 0` for every `b`.
* (`IsArchEigen.inner_translation_eq_zero_of_continuous`) In a Hilbert space, if `ζ` is orthogonal
  to every eigenvector of frequency `γ` and its dilation orbit is continuous at `u = 1`, then
  `⟨ζ, π(x ↦ x + b)v⟩ = 0` for every `b`.

So in every unitary representation translations act on the archimedean point spectrum of the
dilations by one real constant per frequency and never mix frequencies, nor mix them with the
continuous part of the dilation spectrum. This is the representation-theoretic reason why atomic
archimedean dilation correlations, Weil's under RH among them, admit only blind successors.

Mechanism. Covariance `π(x ↦ x + ub)π(x ↦ ux) = π(x ↦ ux)π(x ↦ x + b)` makes `b ↦ ⟨v, π_b v⟩`
constant on each half-line. The Cauchy–Schwarz inequality for the blocks `X = Σ_{j<N} π_j v` and
`π_N X` gives `N²|c| ≤ N‖v‖² + N(N − 1)Re c`, so the constant is real. A blind family has
`‖Σ_j a_j t_{x_j}‖² = α|Σ a_j|² + (‖v‖² − α)Σ|a_j|²`, so its Cesàro means along any two
injective sequences approach each other; along `r_j b` with `r_j → 1` they converge (in a Hilbert
space) to an eigenvector of frequency `γ`, and pairing with `w` or `ζ` gives the vanishing.
-/

open Complex Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- `x ↦ x + ub` after `x ↦ ux` is `x ↦ ux` after `x ↦ x + b`. -/
theorem translation_mul_dilation (u : ℚˣ) (b : ℚ) :
    translation ((u : ℚ) * b) * dilation u = dilation u * translation b := by
  rw [← dilation_mul_translation_mul_inv, inv_mul_cancel_right]

theorem conj_archChar_mul (γ : ℝ) (u : ℚ) : conj (archChar γ u) * archChar γ u = 1 := by
  rw [mul_comm]; simpa [Complex.star_def] using archChar_mul_star γ u

theorem archChar_mul_conj (γ : ℝ) (u : ℚ) : archChar γ u * conj (archChar γ u) = 1 := by
  simpa [Complex.star_def] using archChar_mul_star γ u

/-! ### Rationals tending to `1` -/

/-- The rationals `r_j = (j + 2)/(j + 1)`, distinct and tending to `1`. -/
def nearOne (j : ℕ) : ℚ := ((j : ℚ) + 2) / ((j : ℚ) + 1)

theorem nearOne_pos (j : ℕ) : 0 < nearOne j := by unfold nearOne; positivity

theorem nearOne_injective : Function.Injective nearOne := by
  intro j k h
  unfold nearOne at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have : (j : ℚ) = k := by linear_combination -h
  exact_mod_cast this

theorem tendsto_nearOne : Tendsto (fun j => ((nearOne j : ℚ) : ℝ)) atTop (𝓝 1) := by
  have h : ∀ j : ℕ, ((nearOne j : ℚ) : ℝ) = 1 + 1 / ((j : ℝ) + 1) := by
    intro j
    unfold nearOne
    push_cast
    rw [one_add_div (by positivity)]
    congr 1
    ring
  simp_rw [h]
  have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  rwa [add_zero] at h2

theorem tendsto_archChar_nearOne (γ : ℝ) :
    Tendsto (fun j => archChar γ (nearOne j)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun j => Real.log ((nearOne j : ℚ) : ℝ)) atTop (𝓝 0) := by
    have h := ((Real.continuousAt_log one_ne_zero).tendsto).comp tendsto_nearOne
    rw [Real.log_one] at h
    exact h
  have h1 : Tendsto (fun j => cexp (I * (γ : ℂ) * ((Real.log ((nearOne j : ℚ) : ℝ) : ℝ) : ℂ)))
      atTop (𝓝 (cexp (I * (γ : ℂ) * ((0 : ℝ) : ℂ)))) :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).tendsto
      (0 : ℝ)).comp hlog
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h1
  exact h1

/-! ### Unitary representations of `Aff(ℚ)` -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (π : AffineGroupQ →* (E ≃ₗᵢ[ℂ] E))

/-- `v` is an archimedean dilation eigenvector of frequency `γ`: `π(x ↦ ux)v = u^{iγ}v`, `u > 0`. -/
def IsArchEigen (γ : ℝ) (v : E) : Prop :=
  ∀ u : ℚˣ, 0 < (u : ℚ) → π (dilation u) v = archChar γ u • v

theorem rep_mul_apply (g h : AffineGroupQ) (x : E) : π (g * h) x = π g (π h x) := by
  rw [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]

theorem rep_one_apply (x : E) : π 1 x = x := by
  rw [map_one, LinearIsometryEquiv.coe_one, id]

theorem rep_translation_zero (x : E) : π (translation 0) x = x := by
  rw [translation_zero, rep_one_apply]

theorem rep_translation_dilation (u : ℚˣ) (b : ℚ) (x : E) :
    π (translation ((u : ℚ) * b)) (π (dilation u) x) = π (dilation u) (π (translation b) x) := by
  rw [← rep_mul_apply, ← rep_mul_apply, translation_mul_dilation]

theorem inner_rep_translation (a b : ℚ) (x y : E) :
    ⟪π (translation a) x, π (translation b) y⟫_ℂ = ⟪x, π (translation (b - a)) y⟫_ℂ := by
  conv_lhs => rw [show b = a + (b - a) by ring, translation_add, rep_mul_apply]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem inner_rep_translation_neg (b : ℚ) (x y : E) :
    ⟪x, π (translation (-b)) y⟫_ℂ = ⟪π (translation b) x, y⟫_ℂ := by
  have h := inner_rep_translation π b 0 x y
  rw [rep_translation_zero, zero_sub] at h
  exact h.symm

/-- `⟪x, π_d y⟫ = ⟪π_{d⁻¹} x, y⟫` for a dilation `d`. -/
theorem inner_rep_dilation (u : ℚˣ) (x y : E) :
    ⟪x, π (dilation u) y⟫_ℂ = ⟪π (dilation u⁻¹) x, y⟫_ℂ := by
  conv_lhs => rw [← rep_one_apply π x, ← mul_inv_cancel (dilation u), ← map_inv, rep_mul_apply]
  exact LinearIsometryEquiv.inner_map_map _ _ _

variable {π}

/-! ### The diagonal: blindness -/

/-- Covariance on the diagonal: `⟨v, π_{ub} v⟩ = ⟨v, π_b v⟩` for `u > 0`. -/
theorem IsArchEigen.inner_translation_mul {γ : ℝ} {v : E} (hv : IsArchEigen π γ v) {u : ℚˣ}
    (hu : 0 < (u : ℚ)) (b : ℚ) :
    ⟪v, π (translation ((u : ℚ) * b)) v⟫_ℂ = ⟪v, π (translation b) v⟫_ℂ := by
  have h := LinearIsometryEquiv.inner_map_map (π (dilation u)) v (π (translation b) v)
  rw [← rep_translation_dilation, hv u hu, LinearIsometryEquiv.map_smul, inner_smul_left,
    inner_smul_right, ← mul_assoc, conj_archChar_mul, one_mul] at h
  exact h

/-- **Eigenvectors are blind.** For an archimedean eigenvector `v`, `⟨v, π(x ↦ x + b)v⟩` is one
real constant on `b ≠ 0`. -/
theorem IsArchEigen.inner_translation_eq {γ : ℝ} {v : E} (hv : IsArchEigen π γ v) :
    ∃ α : ℝ, ∀ b : ℚ, b ≠ 0 → ⟪v, π (translation b) v⟫_ℂ = α := by
  set c := ⟪v, π (translation 1) v⟫_ℂ with hc
  have hpos : ∀ b : ℚ, 0 < b → ⟪v, π (translation b) v⟫_ℂ = c := fun b hb => by
    simpa using hv.inner_translation_mul (u := Units.mk0 b hb.ne') hb 1
  have hneg : ∀ b : ℚ, b < 0 → ⟪v, π (translation b) v⟫_ℂ = conj c := fun b hb => by
    have h := hv.inner_translation_mul (u := Units.mk0 (-b) (by linarith))
      (by simp only [Units.val_mk0]; linarith) (-1)
    simp only [Units.val_mk0, mul_neg, mul_one, neg_neg] at h
    rw [h, inner_rep_translation_neg, hc, inner_conj_symm]
  -- the blocks `X_N = Σ_{j<N} π_j v`
  set s := ‖v‖ ^ 2
  set X : ℕ → E := fun N => ∑ j ∈ range N, π (translation (j : ℚ)) v
  have hcross : ∀ N : ℕ, ⟪X N, π (translation (N : ℚ)) v⟫_ℂ = N * c := by
    intro N
    simp only [X, sum_inner]
    rw [sum_congr rfl fun j hj => by
      rw [inner_rep_translation, hpos _ (by
        have := mem_range.mp hj; rw [sub_pos]; exact_mod_cast this)], sum_const, card_range,
      nsmul_eq_mul]
  have hnorm : ∀ N : ℕ, ‖X N‖ ^ 2 = N * s + N * (N - 1) * c.re := by
    intro N
    induction N with
    | zero => simp [X]
    | succ N ih =>
      rw [show X (N + 1) = X N + π (translation (N : ℚ)) v from sum_range_succ _ _,
        norm_add_sq (𝕜 := ℂ), ih, hcross, LinearIsometryEquiv.norm_map]
      simp only [RCLike.re_to_complex, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
      push_cast
      ring
  have hblock : ∀ N : ℕ, ⟪X N, π (translation (N : ℚ)) (X N)⟫_ℂ = (N : ℂ) ^ 2 * c := by
    intro N
    simp only [X, map_sum, sum_inner, inner_sum]
    rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => by
      rw [← rep_mul_apply, ← translation_add, inner_rep_translation, hpos _ (by
        have h1 : (j : ℚ) < N := by exact_mod_cast mem_range.mp hj
        have h2 : (k : ℚ) < N := by exact_mod_cast mem_range.mp hk
        have h3 : (0 : ℚ) ≤ j := Nat.cast_nonneg j
        have h4 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
        linarith)]]
    simp only [sum_const, card_range, nsmul_eq_mul]
    ring
  have hcs : ∀ N : ℕ, (N : ℝ) ^ 2 * ‖c‖ ≤ N * s + N * (N - 1) * c.re := by
    intro N
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (X N) (π (translation (N : ℚ)) (X N))
    rw [hblock, LinearIsometryEquiv.norm_map, norm_mul, norm_pow, Complex.norm_natCast, ← sq,
      hnorm] at h1
    exact h1
  have hre_le : c.re ≤ s := by
    have := norm_inner_le_norm (𝕜 := ℂ) v (π (translation 1) v)
    rw [LinearIsometryEquiv.norm_map, ← sq] at this
    exact (Complex.re_le_norm c).trans this
  have hreal : c.im = 0 := by
    by_contra hne
    have hlt : c.re < ‖c‖ := (le_abs_self _).trans_lt (Complex.abs_re_lt_norm.mpr hne)
    obtain ⟨N, hN⟩ := exists_nat_gt ((s - c.re) / (‖c‖ - c.re))
    have hd : 0 < ‖c‖ - c.re := by linarith
    have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by linarith) hd.le) hN
    have h1 := (div_lt_iff₀ hd).mp hN
    have h2 := mul_lt_mul_of_pos_left h1 hN0
    nlinarith [hcs N]
  have hcc : conj c = c := Complex.conj_eq_iff_im.mpr hreal
  have hcr : c = (c.re : ℂ) := (Complex.conj_eq_iff_re.mp hcc).symm
  refine ⟨c.re, fun b hb => ?_⟩
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hneg b h, hcc]; exact hcr
  · rw [hpos b h]; exact hcr

/-! ### Blind families -/

/-- A family `t : ℚ → E` with Gram matrix `α + (s − α)δ_{xy}`. -/
def IsBlindFamily (t : ℚ → E) (s α : ℝ) : Prop :=
  ∀ x y : ℚ, ⟪t x, t y⟫_ℂ = if x = y then (s : ℂ) else (α : ℂ)

/-- The translates of an archimedean eigenvector form a blind family. -/
theorem IsArchEigen.isBlindFamily {γ : ℝ} {v : E} (hv : IsArchEigen π γ v) :
    ∃ α : ℝ, α ≤ ‖v‖ ^ 2 ∧ IsBlindFamily (fun x => π (translation x) v) (‖v‖ ^ 2) α := by
  obtain ⟨α, hα⟩ := hv.inner_translation_eq
  refine ⟨α, ?_, fun x y => ?_⟩
  · have h1 := norm_inner_le_norm (𝕜 := ℂ) v (π (translation 1) v)
    rw [hα 1 one_ne_zero, LinearIsometryEquiv.norm_map, ← sq, Complex.norm_real,
      Real.norm_eq_abs] at h1
    exact (le_abs_self α).trans h1
  · rw [inner_rep_translation]
    split_ifs with h
    · rw [h, sub_self, rep_translation_zero, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · exact hα _ (sub_ne_zero.mpr (Ne.symm h))

/-- The squared norm of a combination of a blind family:
`‖Σ_j a_j t_{x_j}‖² = α|Σ a_j|² + (s − α)Σ|a_j|²`. -/
theorem IsBlindFamily.norm_sq_sum {t : ℚ → E} {s α : ℝ} (ht : IsBlindFamily t s α)
    {x : ℕ → ℚ} (hx : Function.Injective x) (S : Finset ℕ) (a : ℕ → ℂ) :
    ‖∑ j ∈ S, a j • t (x j)‖ ^ 2 = α * ‖∑ j ∈ S, a j‖ ^ 2 + (s - α) * ∑ j ∈ S, ‖a j‖ ^ 2 := by
  have hG : ∀ j ∈ S, ∀ k ∈ S, ⟪a j • t (x j), a k • t (x k)⟫_ℂ =
      conj (a j) * a k * α + (if j = k then conj (a j) * a k * (s - α) else 0) := by
    intro j _ k _
    rw [inner_smul_left, inner_smul_right, ht]
    by_cases h : j = k
    · subst h; simp only [if_true]; ring
    · simp only [hx.ne h, h, if_false, add_zero]; ring
  have hsum : ⟪∑ j ∈ S, a j • t (x j), ∑ j ∈ S, a j • t (x j)⟫_ℂ =
      (α : ℂ) * (conj (∑ j ∈ S, a j) * ∑ j ∈ S, a j) +
        ((s - α : ℝ) : ℂ) * ∑ j ∈ S, conj (a j) * a j := by
    rw [sum_inner]
    simp_rw [inner_sum]
    rw [sum_congr rfl fun j hj => sum_congr rfl fun k hk => hG j hj k hk]
    simp only [sum_add_distrib, sum_ite_eq]
    rw [show (∑ j ∈ S, if j ∈ S then conj (a j) * a j * ((s : ℂ) - α) else 0) =
      ∑ j ∈ S, conj (a j) * a j * ((s : ℂ) - α) from sum_congr rfl fun j hj => if_pos hj]
    have e1 : ∑ j ∈ S, ∑ k ∈ S, conj (a j) * a k * (α : ℂ) =
        (α : ℂ) * (conj (∑ j ∈ S, a j) * ∑ j ∈ S, a j) := by
      rw [map_sum, sum_mul_sum, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun k _ => by ring
    have e2 : ∑ j ∈ S, conj (a j) * a j * ((s : ℂ) - α) =
        ((s - α : ℝ) : ℂ) * ∑ j ∈ S, conj (a j) * a j := by
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [e1, e2]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hsum]
  simp only [RCLike.re_to_complex, Complex.add_re, Complex.re_ofReal_mul, Complex.conj_mul',
    Complex.re_sum]
  push_cast
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Two Cesàro sums of a blind family along injective sequences:
`‖Σ_{j<N} t_{x_j} − Σ_{j<N} t_{y_j}‖² ≤ 2N(s − α)`. -/
theorem IsBlindFamily.norm_sq_sub_le {t : ℚ → E} {s α : ℝ} (ht : IsBlindFamily t s α)
    (hαs : α ≤ s) {x y : ℕ → ℚ} (hx : Function.Injective x) (hy : Function.Injective y) (N : ℕ) :
    ‖∑ j ∈ range N, t (x j) - ∑ j ∈ range N, t (y j)‖ ^ 2 ≤ 2 * N * (s - α) := by
  have hone : ∀ z : ℕ → ℚ, Function.Injective z →
      ‖∑ j ∈ range N, t (z j)‖ ^ 2 = α * N ^ 2 + (s - α) * N := by
    intro z hz
    have h := ht.norm_sq_sum hz (range N) fun _ => 1
    simp only [one_smul, sum_const, card_range, nsmul_eq_mul, mul_one, norm_one, one_pow,
      Complex.norm_natCast] at h
    rw [h]
  have hre : (N : ℝ) ^ 2 * α ≤
      RCLike.re ⟪∑ j ∈ range N, t (x j), ∑ j ∈ range N, t (y j)⟫_ℂ := by
    simp only [sum_inner, inner_sum, map_sum]
    have : ∀ j ∈ range N, ∀ k ∈ range N, α ≤ RCLike.re ⟪t (x j), t (y k)⟫_ℂ := by
      intro j _ k _
      rw [ht]
      split_ifs <;> simpa using hαs
    calc (N : ℝ) ^ 2 * α = ∑ j ∈ range N, ∑ k ∈ range N, α := by
          simp only [sum_const, card_range, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun k hk => sum_le_sum fun j hj => this j hj k hk
  rw [norm_sub_sq (𝕜 := ℂ), hone x hx, hone y hy]
  linarith

/-- The Cesàro mean `N⁻¹ Σ_{j<N} t_{x_j}`. -/
def cesaroMean (t : ℚ → E) (x : ℕ → ℚ) (N : ℕ) : E := ((N : ℂ)⁻¹) • ∑ j ∈ range N, t (x j)

theorem inner_cesaroMean (w : E) (t : ℚ → E) (x : ℕ → ℚ) (N : ℕ) :
    ⟪w, cesaroMean t x N⟫_ℂ = (N : ℂ)⁻¹ * ∑ j ∈ range N, ⟪w, t (x j)⟫_ℂ := by
  rw [cesaroMean, inner_smul_right, inner_sum]

/-- Cesàro means of convergent complex sequences converge to the limit. -/
theorem tendsto_cesaro_complex {u : ℕ → ℂ} {l : ℂ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ range N, u j) atTop (𝓝 l) :=
  h.cesaro_smul.congr fun N => by rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- `‖C_N(x) − C_N(y)‖² ≤ 2(s − α)/N` for a blind family. -/
theorem IsBlindFamily.norm_sq_cesaroMean_sub_le {t : ℚ → E} {s α : ℝ} (ht : IsBlindFamily t s α)
    (hαs : α ≤ s) {x y : ℕ → ℚ} (hx : Function.Injective x) (hy : Function.Injective y) (N : ℕ) :
    ‖cesaroMean t x N - cesaroMean t y N‖ ^ 2 ≤ 2 * (s - α) * (N : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cesaroMean]
  have h := ht.norm_sq_sub_le hαs hx hy N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cesaroMean, cesaroMean, ← smul_sub, norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
  calc ((N : ℝ)⁻¹) ^ 2 * ‖∑ j ∈ range N, t (x j) - ∑ j ∈ range N, t (y j)‖ ^ 2
      ≤ ((N : ℝ)⁻¹) ^ 2 * (2 * N * (s - α)) := by gcongr
    _ = 2 * (s - α) * (N : ℝ)⁻¹ := by field_simp

/-- Cesàro means of a blind family along two injective sequences approach each other. -/
theorem IsBlindFamily.tendsto_cesaroMean_sub {t : ℚ → E} {s α : ℝ} (ht : IsBlindFamily t s α)
    (hαs : α ≤ s) {x y : ℕ → ℚ} (hx : Function.Injective x) (hy : Function.Injective y) :
    Tendsto (fun N => cesaroMean t x N - cesaroMean t y N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun N : ℕ => 2 * (s - α) * (N : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (s - α))
  have hsq := squeeze_zero (fun N => sq_nonneg _) (ht.norm_sq_cesaroMean_sub_le hαs hx hy) hg
  simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt

/-- Along `N = 2^k` the Cesàro means of a blind family are Cauchy. -/
theorem IsBlindFamily.cauchySeq_cesaroMean_pow {t : ℚ → E} {s α : ℝ} (ht : IsBlindFamily t s α)
    (hαs : α ≤ s) {x : ℕ → ℚ} (hx : Function.Injective x) :
    CauchySeq fun k => cesaroMean t x (2 ^ k) := by
  set r : ℝ := Real.sqrt (1 / 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine cauchySeq_of_le_geometric r (Real.sqrt (s - α)) hr1 fun k => ?_
  have hx' : Function.Injective fun j => x (2 ^ k + j) := fun j j' h => by simpa using hx h
  -- `C_{2N}(x) = (C_N(x) + C_N(x'))/2` with `x'_j = x_{N+j}`, `N = 2^k`
  have hsplit : cesaroMean t x (2 ^ (k + 1)) =
      (1 / 2 : ℂ) • (cesaroMean t x (2 ^ k) + cesaroMean t (fun j => x (2 ^ k + j)) (2 ^ k)) := by
    have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
    rw [cesaroMean, cesaroMean, cesaroMean, h2, sum_range_add, ← smul_add, smul_smul]
    congr 1
    push_cast
    rw [show (2 : ℂ) ^ k + 2 ^ k = 2 * 2 ^ k by ring, mul_inv]
    ring
  have hdist : dist (cesaroMean t x (2 ^ k)) (cesaroMean t x (2 ^ (k + 1))) =
      (1 / 2) * ‖cesaroMean t x (2 ^ k) - cesaroMean t (fun j => x (2 ^ k + j)) (2 ^ k)‖ := by
    rw [dist_eq_norm, hsplit, show cesaroMean t x (2 ^ k) - (1 / 2 : ℂ) • (cesaroMean t x (2 ^ k) +
      cesaroMean t (fun j => x (2 ^ k + j)) (2 ^ k)) = (1 / 2 : ℂ) • (cesaroMean t x (2 ^ k) -
      cesaroMean t (fun j => x (2 ^ k + j)) (2 ^ k)) by module, norm_smul]
    norm_num
  have hb := ht.norm_sq_cesaroMean_sub_le hαs hx hx' (2 ^ k)
  have hN : (((2 ^ k : ℕ) : ℝ))⁻¹ = (r ^ 2) ^ k := by
    rw [hr2]; push_cast; rw [one_div, inv_pow]
  rw [hdist]
  have hB : 0 ≤ Real.sqrt (s - α) * r ^ k := mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hr0 _)
  have hsq : ((1 / 2) * ‖cesaroMean t x (2 ^ k) - cesaroMean t (fun j => x (2 ^ k + j)) (2 ^ k)‖) ^ 2
      ≤ (Real.sqrt (s - α) * r ^ k) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), ← pow_mul, mul_comm k 2, pow_mul]
    rw [hN] at hb
    nlinarith [sq_nonneg (r ^ 2), pow_nonneg (sq_nonneg r) k]
  exact (sq_le_sq₀ (by positivity) hB).mp hsq

/-! ### Off the diagonal: frequencies do not mix -/

/-- Covariance between two eigenvectors: `⟨w, π_{ux} v⟩ = u^{iγ'}u^{−iγ}⟨w, π_x v⟩`. -/
theorem IsArchEigen.inner_translation_mul_of_two {γ γ' : ℝ} {v w : E} (hv : IsArchEigen π γ v)
    (hw : IsArchEigen π γ' w) {u : ℚˣ} (hu : 0 < (u : ℚ)) (x : ℚ) :
    ⟪w, π (translation ((u : ℚ) * x)) v⟫_ℂ =
      archChar γ' u * conj (archChar γ u) * ⟪w, π (translation x) v⟫_ℂ := by
  have h := LinearIsometryEquiv.inner_map_map (π (dilation u)) w (π (translation x) v)
  rw [← rep_translation_dilation, hv u hu, hw u hu, LinearIsometryEquiv.map_smul, inner_smul_left,
    inner_smul_right] at h
  rw [← h]
  linear_combination (-(conj (archChar γ u) * archChar γ u *
    ⟪w, π (translation ((u : ℚ) * x)) v⟫_ℂ)) * archChar_mul_conj γ' u +
    (-⟪w, π (translation ((u : ℚ) * x)) v⟫_ℂ) * conj_archChar_mul γ u

/-- A nonzero frequency is seen by `2` or `3`. -/
theorem exists_archChar_ne_one {δ : ℝ} (hδ : δ ≠ 0) :
    ∃ p : ℚˣ, 0 < (p : ℚ) ∧ archChar δ p ≠ 1 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have h2 := h (Units.mk0 2 two_ne_zero) (by norm_num)
  have h3 := h (Units.mk0 3 three_ne_zero) (by norm_num)
  exact hδ (eq_zero_of_archChar_eq_one Nat.prime_two Nat.prime_three (by norm_num)
    (by simpa using h2) (by simpa using h3))

/-- **Frequencies do not mix.** Eigenvectors of distinct frequencies have
`⟨w, π(x ↦ x + b)v⟩ = 0` for every `b`. -/
theorem IsArchEigen.inner_translation_eq_zero {γ γ' : ℝ} {v w : E} (hv : IsArchEigen π γ v)
    (hw : IsArchEigen π γ' w) (hne : γ ≠ γ') (b : ℚ) : ⟪w, π (translation b) v⟫_ℂ = 0 := by
  set χ : ℚ → ℂ := fun u => archChar γ' u * conj (archChar γ u) with hχ
  have hcov : ∀ u : ℚˣ, 0 < (u : ℚ) → ∀ x : ℚ,
      ⟪w, π (translation ((u : ℚ) * x)) v⟫_ℂ = χ u * ⟪w, π (translation x) v⟫_ℂ :=
    fun u hu x => hv.inner_translation_mul_of_two hw hu x
  obtain ⟨p, hp, hχp⟩ : ∃ p : ℚˣ, 0 < (p : ℚ) ∧ χ p ≠ 1 := by
    obtain ⟨p, hp, h⟩ := exists_archChar_ne_one (sub_ne_zero.mpr hne.symm)
    exact ⟨p, hp, by simpa [hχ, archChar_sub, Complex.star_def] using h⟩
  have hkill : ∀ z : ℂ, z = χ p * z → z = 0 := fun z hz => by
    have h1 : (1 - χ p) * z = 0 := by rw [sub_mul, one_mul, ← hz, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left fun h => hχp (sub_eq_zero.mp h).symm
  by_cases hb : b = 0
  · subst hb
    exact hkill _ (by simpa using hcov p hp 0)
  obtain ⟨α, hαs, ht⟩ := hv.isBlindFamily
  set t : ℚ → E := fun x => π (translation x) v
  set x : ℕ → ℚ := fun j => nearOne j * b
  set y : ℕ → ℚ := fun j => (p : ℚ) * (nearOne j * b)
  have hx : Function.Injective x := fun j k h => nearOne_injective (mul_right_cancel₀ hb h)
  have hy : Function.Injective y := fun j k h => hx (mul_left_cancel₀ (Units.ne_zero p) h)
  set m := ⟪w, π (translation b) v⟫_ℂ
  have hχlim : Tendsto (fun j => χ (nearOne j)) atTop (𝓝 1) := by
    have hc := (Complex.continuous_conj.tendsto 1).comp (tendsto_archChar_nearOne γ)
    rw [map_one] at hc
    have h := (tendsto_archChar_nearOne γ').mul hc
    rw [one_mul] at h
    exact h
  have hlim : Tendsto (fun N => ⟪w, cesaroMean t x N⟫_ℂ) atTop (𝓝 m) := by
    have hu : Tendsto (fun j => χ (nearOne j) * m) atTop (𝓝 m) := by
      simpa using hχlim.mul_const m
    refine (tendsto_cesaro_complex hu).congr fun N => ?_
    rw [inner_cesaroMean]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    exact (hcov (Units.mk0 (nearOne j) (nearOne_pos j).ne') (nearOne_pos j) b).symm
  have hyx : ∀ N, ⟪w, cesaroMean t y N⟫_ℂ = χ p * ⟪w, cesaroMean t x N⟫_ℂ := by
    intro N
    rw [inner_cesaroMean, inner_cesaroMean, sum_congr rfl fun j _ => hcov p hp (x j), ← mul_sum]
    ring
  have hdiff : Tendsto (fun N => (1 - χ p) * ⟪w, cesaroMean t x N⟫_ℂ) atTop (𝓝 0) := by
    have h := ((continuous_const.inner continuous_id : Continuous fun z : E => ⟪w, z⟫_ℂ).tendsto
      (0 : E)).comp (ht.tendsto_cesaroMean_sub hαs hx hy)
    simp only [inner_zero_right] at h
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, inner_sub_right, hyx]
    ring
  have h0 := tendsto_nhds_unique (hlim.const_mul (1 - χ p)) hdiff
  exact (mul_eq_zero.mp h0).resolve_left fun h => hχp (sub_eq_zero.mp h).symm

/-! ### The continuous part: no mixing either -/

/-- **The continuous dilation spectrum does not mix with eigenvectors.** In a Hilbert space, if
`ζ` is orthogonal to every eigenvector of frequency `γ` and `π(x ↦ x/r_j)ζ → ζ` along
`r_j = (j + 2)/(j + 1) → 1`, then `⟨ζ, π(x ↦ x + b)v⟩ = 0` for every eigenvector `v` of frequency
`γ` and every `b`. -/
theorem IsArchEigen.inner_translation_eq_zero_of_continuous [CompleteSpace E] {γ : ℝ} {v : E}
    (hv : IsArchEigen π γ v) {ζ : E} (hζ : ∀ w, IsArchEigen π γ w → ⟪ζ, w⟫_ℂ = 0)
    (hcont : Tendsto (fun j => π (dilation (Units.mk0 (nearOne j) (nearOne_pos j).ne')⁻¹) ζ)
      atTop (𝓝 ζ)) (b : ℚ) :
    ⟪ζ, π (translation b) v⟫_ℂ = 0 := by
  by_cases hb : b = 0
  · subst hb; rw [rep_translation_zero]; exact hζ v hv
  obtain ⟨α, hαs, ht⟩ := hv.isBlindFamily
  set t : ℚ → E := fun x => π (translation x) v
  set x : ℕ → ℚ := fun j => nearOne j * b
  have hx : Function.Injective x := fun j k h => nearOne_injective (mul_right_cancel₀ hb h)
  set D : ℕ → E := fun k => cesaroMean t x (2 ^ k)
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (ht.cauchySeq_cesaroMean_pow hαs hx)
  have hpow : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  -- the limit is an eigenvector of frequency `γ`
  have hceig : IsArchEigen π γ c := by
    intro u hu
    set ux : ℕ → ℚ := fun j => (u : ℚ) * x j
    have hux : Function.Injective ux := fun j k h => hx (mul_left_cancel₀ u.ne_zero h)
    have hmap : ∀ N, π (dilation u) (cesaroMean t x N) = archChar γ u • cesaroMean t ux N := by
      intro N
      simp only [cesaroMean, LinearIsometryEquiv.map_smul, map_sum, t, ux]
      rw [smul_comm, sum_congr rfl fun j _ => by rw [← rep_translation_dilation, hv u hu,
        LinearIsometryEquiv.map_smul], ← smul_sum]
    have h1 : Tendsto (fun k => π (dilation u) (D k)) atTop (𝓝 (π (dilation u) c)) :=
      ((π (dilation u)).continuous.tendsto c).comp hc
    have h2 : Tendsto (fun k => cesaroMean t ux (2 ^ k)) atTop (𝓝 c) := by
      have := ((ht.tendsto_cesaroMean_sub hαs hux hx).comp hpow).add hc
      simpa using this
    have h3 : Tendsto (fun k => π (dilation u) (D k)) atTop (𝓝 (archChar γ u • c)) :=
      (h2.const_smul (archChar γ u)).congr fun k => (hmap _).symm
    exact tendsto_nhds_unique h1 h3
  -- `⟨ζ, π_{r_j b} v⟩ → ⟨ζ, π_b v⟩`
  have hterm : Tendsto (fun j => ⟪ζ, t (x j)⟫_ℂ) atTop (𝓝 ⟪ζ, π (translation b) v⟫_ℂ) := by
    have hrel : ∀ j, ⟪ζ, t (x j)⟫_ℂ = conj (archChar γ (nearOne j)) *
        ⟪π (dilation (Units.mk0 (nearOne j) (nearOne_pos j).ne')⁻¹) ζ, π (translation b) v⟫_ℂ := by
      intro j
      have h := rep_translation_dilation π (Units.mk0 (nearOne j) (nearOne_pos j).ne') b v
      rw [hv _ (nearOne_pos j), LinearIsometryEquiv.map_smul, Units.val_mk0] at h
      rw [← inner_rep_dilation, ← h, inner_smul_right, ← mul_assoc, conj_archChar_mul, one_mul]
    have hconj : Tendsto (fun j => conj (archChar γ (nearOne j))) atTop (𝓝 1) := by
      have h := (Complex.continuous_conj.tendsto 1).comp (tendsto_archChar_nearOne γ)
      rw [map_one] at h
      exact h
    have hin := ((continuous_id.inner continuous_const : Continuous fun z : E =>
      ⟪z, π (translation b) v⟫_ℂ).tendsto ζ).comp hcont
    have h := hconj.mul hin
    rw [one_mul] at h
    exact h.congr fun j => (hrel j).symm
  have hlim1 : Tendsto (fun k => ⟪ζ, D k⟫_ℂ) atTop (𝓝 ⟪ζ, π (translation b) v⟫_ℂ) := by
    have := (tendsto_cesaro_complex hterm).comp hpow
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, D, inner_cesaroMean]
  have hlim2 : Tendsto (fun k => ⟪ζ, D k⟫_ℂ) atTop (𝓝 ⟪ζ, c⟫_ℂ) :=
    ((continuous_const.inner continuous_id : Continuous fun z : E => ⟪ζ, z⟫_ℂ).tendsto c).comp hc
  rw [tendsto_nhds_unique hlim1 hlim2, hζ c hceig]

end GaloisForLFunctions.ArithmeticPositiveDuality
