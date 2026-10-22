import GaloisForLFunctions.RHTower.CCM.CCMParityNearHalfTurn
import GaloisForLFunctions.HTGeometry.DanskinPerturbationBound

/-!
# The deep limit of the leading-order parity balance

Take distinct positive ordinates `t_j ≤ τ`, positive multiplicities `M_j` with maximum `M*`, and let
the offset `δ > 0` tend to zero. Write coefficient vectors as `x = √δ·y` with `Σ_j |y_j|² = 1`. The
Cauchy boundary vector is `(Gz)_j = ȳ_j/(2√δ) + √δ ρ_j(y)`, where the regular part `ρ_j` keeps the
sum Gram `1/(2δ − i(t_j+t_k))` and the off-diagonal difference Gram `1/(2δ − i(t_j−t_k))`. Both
stay bounded as `δ → 0`.

* **Exact expansion** (`quadForm_deepScale_eq`). On the sphere,
  `⟨T(θ)x, x⟩/‖x‖² = (q₀(y) + δ b_δ(y))/(4δ)`. Here `q₀(y) = Re Σ_j M_j e^{iθ_j} ȳ_j²` has
  symmetric extremes `±M*`, and `b_δ → b₀` uniformly on the sphere (`exists_abs_deepB_sub_le`).
* **Danskin** (`GaloisForLFunctions.HTGeometry.Danskin.exists_perturbed_max_le`). The half-turned
  maximum is at most `M* + δ(max over the bottom set of −b₀ + ε)`.
* **Bottom set along the aperture line** (`deep_bottom_structure`, `deepN1_zero_le_of_bottom`).
  The maximizers of `−q₀` satisfy `y_j = e^{−it_j a}(i v_j)` with `v` real and supported on the
  maximal multiplicities. There `−b₀ = M* n₁` with
  `n₁ = Σ_{j,k} v_j v_k (−2 sinc_a(t_j+t_k) + [j≠k] 2 sinc_a(t_j−t_k)) ≤ −2a + 4mτ²a³`, where
  `sinc_a(c) = sin(ca)/c`.
* **Top test vector** (`deepB_zero_topVec_ge`). The single-node vector `e^{−it_{j₀}a}e_{j₀}` gives
  `b₀ = M* sin(2t_{j₀}a)/t_{j₀} ≥ M*(2a − 2τ²a³)`.

**Theorem** (`exists_deep_balance_pos`). At the aperture `a₀ = 1/(τ(4m+2))`, the parity balance
`F(θ(a₀))` is positive for all sufficiently small `δ > 0`. In the limit the balance is
`M*[λ_max(Γ^c_{a₀}) − λ_max(Γ^s_{a₀})]`, where `Γ^c, Γ^s` are the `L²[0,a₀]` Grams of the cosines and
the sines `t_j s`. At small apertures the cosine Gram is close to `a₀𝟙𝟙ᵀ` and the sine Gram is
`O(a₀³)`.

**Corollary** (`exists_deep_ground_odd`). For fixed ordinates and multiplicities, every finite top
layer of sufficiently small depth has reflection-odd ground states at arbitrarily large apertures,
whatever integer relations the ordinates satisfy. By the scaling `(δ, t) ↦ (cδ, ct)`, the
configurations with `F ≤ 0` on the whole aperture line have depth bounded below relative to
their ordinate shape.
-/

open Matrix Complex Filter Topology Set
open RHTower.CCMParityCauchy

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-- The regular part `ρ_j(y)` of the Cauchy boundary vector. -/
def deepRho (δ : ℝ) (t : Fin m → ℝ) (y : Fin m → ℂ) (j : Fin m) : ℂ :=
  (∑ k, y k * (2 * (δ : ℂ) - I * ((t j : ℂ) + t k))⁻¹) +
    ∑ k, if k = j then 0 else (starRingEnd ℂ) (y k) * (2 * (δ : ℂ) - I * ((t j : ℂ) - t k))⁻¹

theorem cauchyGram_mulVec_realLift_inl (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (j : Fin m) :
    (cauchyGram (ccmNodes δ t) *ᵥ realLift x) (Sum.inl j) =
      (starRingEnd ℂ) (x j) * (2 * (δ : ℂ))⁻¹ + deepRho δ t x j := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, cauchyGram, Matrix.of_apply,
    ccmNodes, Sum.elim_inl, Sum.elim_inr, realLift, deepRho]
  have h1 : ∀ k, ((δ : ℂ) - I * t j + ((δ : ℂ) - I * t k))⁻¹ * x k =
      x k * (2 * (δ : ℂ) - I * ((t j : ℂ) + t k))⁻¹ := by
    intro k; rw [mul_comm]; congr 2; ring
  have h2 : ∀ k, ((δ : ℂ) - I * t j + ((δ : ℂ) + I * t k))⁻¹ * (starRingEnd ℂ) (x k) =
      (if k = j then (starRingEnd ℂ) (x j) * (2 * (δ : ℂ))⁻¹ else 0) +
        (if k = j then 0 else
          (starRingEnd ℂ) (x k) * (2 * (δ : ℂ) - I * ((t j : ℂ) - t k))⁻¹) := by
    intro k
    split_ifs with h
    · subst h; rw [mul_comm, add_zero]; congr 2; ring
    · rw [zero_add, mul_comm]; congr 2; ring
  simp_rw [h1, h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The boundary value `w_j = (G z)_j` at the `j`-th node. -/
theorem cauchyGram_mulVec_realLift_inr (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (j : Fin m) :
    (cauchyGram (ccmNodes δ t) *ᵥ realLift x) (Sum.inr j) =
      (starRingEnd ℂ) ((cauchyGram (ccmNodes δ t) *ᵥ realLift x) (Sum.inl j)) :=
  isRealVec_cauchyGram_mulVec δ t (isRealVec_realLift x) (Sum.inl j)

theorem normForm_eq_sum_inl (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    normForm δ t x =
      ∑ j, 2 * (x j * (cauchyGram (ccmNodes δ t) *ᵥ realLift x) (Sum.inl j)).re := by
  unfold normForm
  rw [dotProduct, Fintype.sum_sum_type]
  have hl : ∀ j, realLift x (Sum.inl j) = x j := fun j => rfl
  have hr : ∀ j, realLift x (Sum.inr j) = (starRingEnd ℂ) (x j) := fun j => rfl
  simp only [hl, hr, cauchyGram_mulVec_realLift_inr δ t x]
  rw [← Finset.sum_add_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_mul, Complex.add_re, Complex.conj_re]
  ring

theorem quadForm_eq_sum_inl (δ : ℝ) (t M θ : Fin m → ℝ) (x : Fin m → ℂ) :
    quadForm δ t M θ x = ∑ j, M j *
      (Complex.exp ((θ j : ℂ) * I) * ((cauchyGram (ccmNodes δ t) *ᵥ realLift x) (Sum.inl j)) ^ 2).re := by
  unfold quadForm
  rw [Fintype.sum_sum_type]
  simp only [phaseWeight, Sum.elim_inl, Sum.elim_inr]
  simp_rw [cauchyGram_mulVec_realLift_inr δ t x, ← Finset.sum_add_distrib, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set w := (cauchyGram (ccmNodes δ t) *ᵥ realLift x) (Sum.inl j)
  have hc : Complex.exp (-((θ j : ℂ) * I)) * (starRingEnd ℂ) w ^ 2 =
      (starRingEnd ℂ) (Complex.exp ((θ j : ℂ) * I) * w ^ 2) := by
    rw [map_mul, map_pow, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2; ring
  rw [mul_assoc, mul_assoc, hc, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    Complex.conj_re]
  ring

theorem deepRho_real_smul (δ : ℝ) (t : Fin m → ℝ) (r : ℝ) (y : Fin m → ℂ) (j : Fin m) :
    deepRho δ t (fun k => (r : ℂ) * y k) j = (r : ℂ) * deepRho δ t y j := by
  simp only [deepRho, map_mul, Complex.conj_ofReal, mul_add, Finset.mul_sum, mul_ite, mul_zero,
    mul_assoc]

/-! ## The rescaled forms -/

/-- `Σ_j |y_j|²`. -/
def deepSq (y : Fin m → ℂ) : ℝ := ∑ j, ‖y j‖ ^ 2

/-- The first-order norm correction `n₁ = 2 Re Σ_j y_j ρ_j`. -/
def deepN1 (δ : ℝ) (t : Fin m → ℝ) (y : Fin m → ℂ) : ℝ := ∑ j, 2 * (y j * deepRho δ t y j).re

/-- The leading parity form `q₀ = Re Σ_j M_j e^{iθ_j} ȳ_j²`. -/
def deepQ0 (M θ : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  ∑ j, M j * (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2).re

/-- The first-order parity correction `q₁ = Re Σ_j M_j e^{iθ_j}(4ȳ_jρ_j + 4δρ_j²)`. -/
def deepQ1 (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  ∑ j, M j * (Complex.exp ((θ j : ℂ) * I) *
    (4 * (starRingEnd ℂ) (y j) * deepRho δ t y j + 4 * δ * deepRho δ t y j ^ 2)).re

/-- The rescaled vector `√δ · y`. -/
def deepScale (δ : ℝ) (y : Fin m → ℂ) : Fin m → ℂ := fun j => ((Real.sqrt δ : ℝ) : ℂ) * y j

theorem mulVec_deepScale_inl {δ : ℝ} (t : Fin m → ℝ) (y : Fin m → ℂ) (j : Fin m) :
    (cauchyGram (ccmNodes δ t) *ᵥ realLift (deepScale δ y)) (Sum.inl j) =
      ((Real.sqrt δ : ℝ) : ℂ) * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + deepRho δ t y j) := by
  rw [cauchyGram_mulVec_realLift_inl]
  unfold deepScale
  rw [deepRho_real_smul, map_mul, Complex.conj_ofReal]
  ring

theorem normForm_deepScale {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (y : Fin m → ℂ) :
    normForm δ t (deepScale δ y) = deepSq y + δ * deepN1 δ t y := by
  rw [normForm_eq_sum_inl, deepSq, deepN1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_deepScale_inl]
  set s : ℂ := ((Real.sqrt δ : ℝ) : ℂ)
  set ρ := deepRho δ t y j
  have hss : s * s = (δ : ℂ) := by rw [← ofReal_mul, Real.mul_self_sqrt hδ.le]
  have hyy : y j * (starRingEnd ℂ) (y j) = ((‖y j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hδ0 : (δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hδ.ne'
  have key : deepScale δ y j * (s * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ)) =
      ((‖y j‖ ^ 2 / 2 : ℝ) : ℂ) + (δ : ℂ) * (y j * ρ) := by
    calc deepScale δ y j * (s * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ))
        = (s * s) * (y j * (starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + y j * ρ) := by
          simp only [deepScale, s]; ring
      _ = ((‖y j‖ ^ 2 / 2 : ℝ) : ℂ) + (δ : ℂ) * (y j * ρ) := by
          rw [hss, hyy]; push_cast; field_simp
  rw [key, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  ring

theorem quadForm_deepScale {δ : ℝ} (hδ : 0 < δ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) :
    4 * δ * quadForm δ t M θ (deepScale δ y) = deepQ0 M θ y + δ * deepQ1 δ t M θ y := by
  rw [quadForm_eq_sum_inl, deepQ0, deepQ1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_deepScale_inl]
  set s : ℂ := ((Real.sqrt δ : ℝ) : ℂ)
  set ρ := deepRho δ t y j
  set e := Complex.exp ((θ j : ℂ) * I)
  have hss : s * s = (δ : ℂ) := by rw [← ofReal_mul, Real.mul_self_sqrt hδ.le]
  have hδ0 : (δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hδ.ne'
  have key : ((4 * δ : ℝ) : ℂ) * (e * (s * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ)) ^ 2) =
      e * (starRingEnd ℂ) (y j) ^ 2 +
        (δ : ℂ) * (e * (4 * (starRingEnd ℂ) (y j) * ρ + 4 * δ * ρ ^ 2)) := by
    have : (s * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ)) ^ 2 =
        (s * s) * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ) ^ 2 := by ring
    rw [this, hss]; push_cast; field_simp; ring
  have h1 : 4 * δ * (M j * (e * (s * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ)) ^ 2).re) =
      M j * (((4 * δ : ℝ) : ℂ) *
        (e * (s * ((starRingEnd ℂ) (y j) * (2 * (δ : ℂ))⁻¹ + ρ)) ^ 2)).re := by
    rw [Complex.re_ofReal_mul]; ring
  rw [h1, key, Complex.add_re, Complex.re_ofReal_mul]
  ring

/-- The first-order coefficient `b = (q₁ − q₀n₁)/(1 + δn₁)` of the rescaled Rayleigh quotient. -/
def deepB (δ : ℝ) (t M θ : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  (deepQ1 δ t M θ y - deepQ0 M θ y * deepN1 δ t y) / (1 + δ * deepN1 δ t y)

theorem deepSq_real_smul (r : ℝ) (y : Fin m → ℂ) :
    deepSq (fun j => (r : ℂ) * y j) = r ^ 2 * deepSq y := by
  simp only [deepSq, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Finset.mul_sum]

theorem deepSq_pos {y : Fin m → ℂ} (hy : y ≠ 0) : 0 < deepSq y := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
  have hj' : 0 < ‖y j‖ ^ 2 := by positivity
  exact lt_of_lt_of_le hj' (Finset.single_le_sum (fun k _ => sq_nonneg ‖y k‖)
    (Finset.mem_univ j))

theorem deepScale_ne_zero {δ : ℝ} (hδ : 0 < δ) {y : Fin m → ℂ} (hy : deepSq y = 1) :
    deepScale δ y ≠ 0 := by
  intro h
  have : y = 0 := by
    funext j
    have hj := congr_fun h j
    simp only [deepScale, Pi.zero_apply, mul_eq_zero, ofReal_eq_zero] at hj
    rcases hj with hj | hj
    · exact absurd hj (Real.sqrt_pos.mpr hδ).ne'
    · exact hj
  rw [this] at hy
  simp [deepSq] at hy

/-- **The rescaled Rayleigh quotient.** On the sphere `Σ|y_j|² = 1`,
`⟨T(√δ y), √δ y⟩ = ((q₀ + δ b)/(4δ)) · ‖√δ y‖²`. -/
theorem quadForm_deepScale_eq {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (M θ : Fin m → ℝ) {y : Fin m → ℂ} (hy : deepSq y = 1) :
    quadForm δ t M θ (deepScale δ y) =
      (deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) * normForm δ t (deepScale δ y) := by
  have hN := normForm_pos hδ ht htpos (deepScale_ne_zero hδ hy)
  have hN' := normForm_deepScale hδ t y
  rw [hy] at hN'
  rw [hN'] at hN ⊢
  have hq := quadForm_deepScale hδ t M θ y
  have hQ : quadForm δ t M θ (deepScale δ y) =
      (deepQ0 M θ y + δ * deepQ1 δ t M θ y) / (4 * δ) := by
    rw [eq_div_iff (by positivity)]; linarith [hq]
  rw [hQ]
  unfold deepB
  field_simp
  ring

theorem le_ccmLambdaMax_deep {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) {y : Fin m → ℂ} (hy : deepSq y = 1) :
    (deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) ≤ ccmLambdaMax δ t M θ := by
  obtain ⟨-, -, -, hle⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  set x := deepScale δ y
  have hN := normForm_pos hδ ht htpos (deepScale_ne_zero hδ hy)
  set r : ℝ := (Real.sqrt (normForm δ t x))⁻¹ with hr
  have hx' : (fun j => (r : ℂ) * x j) ∈ unitLevel δ t := by
    rw [unitLevel, Set.mem_setOf_eq, normForm_smul, hr, inv_pow, Real.sq_sqrt hN.le,
      inv_mul_cancel₀ hN.ne']
  have h1 := hle _ hx'
  rw [quadForm_real_smul, hr, inv_pow, Real.sq_sqrt hN.le,
    quadForm_deepScale_eq hδ ht htpos M θ hy] at h1
  have e : (normForm δ t (deepScale δ y))⁻¹ * ((deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) *
      normForm δ t (deepScale δ y)) = (deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) := by
    field_simp
  rwa [e] at h1

theorem exists_ccmLambdaMax_halfTurn_deep {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) :
    ∃ y : Fin m → ℂ, deepSq y = 1 ∧
      ccmLambdaMax δ t M (halfTurn θ) = -((deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ)) := by
  obtain ⟨x, hx, hxl, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M (halfTurn θ)
  rw [unitLevel, Set.mem_setOf_eq] at hx
  have hx0 : x ≠ 0 := by
    intro h; rw [h, normForm_zero] at hx; exact zero_ne_one hx
  have hc := deepSq_pos hx0
  set c := deepSq x
  set y : Fin m → ℂ := fun j => (((Real.sqrt c)⁻¹ : ℝ) : ℂ) * x j with hy
  have hy1 : deepSq y = 1 := by
    rw [hy, deepSq_real_smul, inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  refine ⟨y, hy1, ?_⟩
  have hsc : deepScale δ y = fun j => ((Real.sqrt δ * (Real.sqrt c)⁻¹ : ℝ) : ℂ) * x j := by
    funext j; simp only [deepScale, hy]; push_cast; ring
  have hq := quadForm_deepScale_eq hδ ht htpos M θ hy1
  rw [hsc, quadForm_real_smul, normForm_smul, hx] at hq
  have hqx : quadForm δ t M θ x = -ccmLambdaMax δ t M (halfTurn θ) := by
    rw [← hxl, quadForm_halfTurn, neg_neg]
  rw [hqx] at hq
  have hpos : 0 < (Real.sqrt δ * (Real.sqrt c)⁻¹) ^ 2 := by
    have := Real.sqrt_pos.mpr hδ; have := Real.sqrt_pos.mpr hc; positivity
  have h2 := mul_left_cancel₀ hpos.ne' (hq.trans (by ring :
    (deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ) * ((Real.sqrt δ * (Real.sqrt c)⁻¹) ^ 2 * 1) =
      (Real.sqrt δ * (Real.sqrt c)⁻¹) ^ 2 * ((deepQ0 M θ y + δ * deepB δ t M θ y) / (4 * δ))))
  linarith

/-! ## Continuity at `δ = 0` -/

theorem two_mul_sub_I_mul_ne_zero (δ c : ℝ) (hc : c ≠ 0) : 2 * (δ : ℂ) - I * (c : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hc this

theorem continuous_deepRho {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (j : Fin m) : Continuous fun p : ℝ × (Fin m → ℂ) => deepRho p.1 t p.2 j := by
  have hδc : Continuous fun p : ℝ × (Fin m → ℂ) => 2 * ((p.1 : ℝ) : ℂ) :=
    continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)
  refine Continuous.add (continuous_finsetSum _ fun k _ => ?_)
    (continuous_finsetSum _ fun k _ => ?_)
  · refine ((continuous_apply k).comp continuous_snd).mul (Continuous.inv₀
      (hδc.sub continuous_const) fun p => ?_)
    have h := two_mul_sub_I_mul_ne_zero p.1 (t j + t k) (by linarith [htpos j, htpos k])
    push_cast at h
    exact h
  · by_cases hkj : k = j
    · simp only [hkj, if_true]; exact continuous_const
    · simp only [hkj, if_false]
      refine (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_snd)).mul
        (Continuous.inv₀ (hδc.sub continuous_const) fun p => ?_)
      have h := two_mul_sub_I_mul_ne_zero p.1 (t j - t k)
        (sub_ne_zero.mpr fun h => hkj (ht h).symm)
      push_cast at h
      exact h

theorem continuous_deepN1 {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) :
    Continuous fun p : ℝ × (Fin m → ℂ) => deepN1 p.1 t p.2 := by
  unfold deepN1
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (Complex.continuous_re.comp
    (((continuous_apply j).comp continuous_snd).mul (continuous_deepRho ht htpos j)))

theorem continuous_deepQ0 (M θ : Fin m → ℝ) : Continuous (deepQ0 M θ) := by
  unfold deepQ0
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (Complex.continuous_re.comp
    (continuous_const.mul ((Complex.continuous_conj.comp (continuous_apply j)).pow 2)))

theorem continuous_deepQ1 {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (M θ : Fin m → ℝ) : Continuous fun p : ℝ × (Fin m → ℂ) => deepQ1 p.1 t M θ p.2 := by
  unfold deepQ1
  have hρ := continuous_deepRho ht htpos
  refine continuous_finsetSum _ fun j _ => continuous_const.mul (Complex.continuous_re.comp
    (continuous_const.mul ?_))
  refine ((continuous_const.mul (Complex.continuous_conj.comp
    ((continuous_apply j).comp continuous_snd))).mul (hρ j)).add ?_
  exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul ((hρ j).pow 2)

theorem continuousAt_deepB {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (M θ : Fin m → ℝ) (y : Fin m → ℂ) :
    ContinuousAt (fun p : ℝ × (Fin m → ℂ) => deepB p.1 t M θ p.2) (0, y) := by
  unfold deepB
  refine ContinuousAt.div ?_ ?_ (by simp)
  · exact ((continuous_deepQ1 ht htpos M θ).sub (((continuous_deepQ0 M θ).comp continuous_snd).mul
      (continuous_deepN1 ht htpos))).continuousAt
  · exact (continuous_const.add (continuous_fst.mul (continuous_deepN1 ht htpos))).continuousAt

theorem continuous_deepB_zero {t : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j)
    (M θ : Fin m → ℝ) : Continuous (deepB 0 t M θ) := by
  have h : deepB 0 t M θ = fun y => deepQ1 0 t M θ y - deepQ0 M θ y * deepN1 0 t y := by
    funext y; simp [deepB]
  rw [h]
  have h1 := (continuous_deepQ1 ht htpos M θ).comp (Continuous.prodMk_right (0 : ℝ))
  have h2 := (continuous_deepN1 ht htpos).comp (Continuous.prodMk_right (0 : ℝ))
  exact h1.sub ((continuous_deepQ0 M θ).mul h2)

/-- The unit sphere `Σ_j |y_j|² = 1`. -/
def deepSphere (m : ℕ) : Set (Fin m → ℂ) := {y | deepSq y = 1}

theorem continuous_deepSq : Continuous (deepSq (m := m)) :=
  continuous_finsetSum _ fun j _ => (continuous_norm.comp (continuous_apply j)).pow 2

theorem isCompact_deepSphere : IsCompact (deepSphere m) := by
  refine (isCompact_closedBall (0 : Fin m → ℂ) 1).of_isClosed_subset
    (isClosed_eq continuous_deepSq continuous_const) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
  have h1 : ‖y j‖ ^ 2 ≤ 1 := by
    have := Finset.single_le_sum (fun k _ => sq_nonneg ‖y k‖) (Finset.mem_univ j)
    simp only [deepSphere, Set.mem_setOf_eq, deepSq] at hy
    linarith
  nlinarith [norm_nonneg (y j)]

/-- **Uniform convergence of the first-order coefficient on the sphere.** -/
theorem exists_abs_deepB_sub_le {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (M θ : Fin m → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, |δ| < κ → ∀ y ∈ deepSphere m,
      |deepB δ t M θ y - deepB 0 t M θ y| ≤ ε := by
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ y ∈ deepSphere m, |deepB δ t M θ y - deepB 0 t M θ y| ≤ ε := by
    refine isCompact_deepSphere.eventually_forall_of_forall_eventually fun y _ => ?_
    have hG := continuousAt_deepB ht htpos M θ y
    have hH : ContinuousAt (fun p : ℝ × (Fin m → ℂ) => deepB 0 t M θ p.2) (0, y) :=
      ((continuous_deepB_zero ht htpos M θ).comp continuous_snd).continuousAt
    have hlim : Tendsto (fun p : ℝ × (Fin m → ℂ) => deepB p.1 t M θ p.2 - deepB 0 t M θ p.2)
        (𝓝 ((0 : ℝ), y)) (𝓝 0) := by
      have h := (hG.sub hH).tendsto
      simp only [Pi.sub_apply, sub_self] at h
      exact h
    filter_upwards [Metric.tendsto_nhds.mp hlim ε hε] with z hz
    rw [Real.dist_eq, sub_zero] at hz
    exact hz.le
  obtain ⟨κ, hκ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨κ, hκ, fun δ hδ => hball (by rwa [Real.dist_eq, sub_zero])⟩

/-! ## Elementary bounds -/

/-- `|sin(ca)/c − a| ≤ c²a³/6`. -/
theorem abs_sin_mul_div_sub_le {a : ℝ} (ha : 0 < a) {c : ℝ} (hc : c ≠ 0) :
    |Real.sin (c * a) / c - a| ≤ c ^ 2 * a ^ 3 / 6 := by
  have key : Real.sin (c * a) / c = Real.sin (|c| * a) / |c| := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [abs_of_neg h, neg_mul, Real.sin_neg, neg_div_neg_eq]
    · rw [abs_of_pos h]
  rw [key, ← sq_abs c]
  have hc' : 0 < |c| := abs_pos.mpr hc
  have hu : 0 < |c| * a := mul_pos hc' ha
  have h1 := Real.sin_le hu.le
  have h2 := Real.sin_gt_sub_cube hu
  have hup : Real.sin (|c| * a) / |c| ≤ a := by
    rw [div_le_iff₀ hc']; linarith
  have hlo : a - |c| ^ 2 * a ^ 3 / 6 ≤ Real.sin (|c| * a) / |c| := by
    rw [le_div_iff₀ hc']
    have : (|c| * a) ^ 3 = |c| ^ 3 * a ^ 3 := by ring
    nlinarith
  have hnn : 0 ≤ |c| ^ 2 * a ^ 3 / 6 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- `Re(v e^{−iφ} (−ic)⁻¹) = v sin φ / c`. -/
theorem re_ofReal_mul_exp_mul_inv (v φ c : ℝ) :
    ((v : ℂ) * Complex.exp (-((φ : ℂ) * I)) * (-I * (c : ℂ))⁻¹).re = v * Real.sin φ / c := by
  have hinv : (-I * (c : ℂ))⁻¹ = I * ((c⁻¹ : ℝ) : ℂ) := by
    rw [mul_inv, inv_neg, Complex.inv_I, neg_neg]; push_cast; ring
  have he : Complex.exp (-((φ : ℂ) * I)) = Complex.exp (((-φ : ℝ) : ℂ) * I) := by
    push_cast; ring_nf
  rw [hinv, he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.I_re, Complex.I_im,
    Real.cos_neg, Real.sin_neg]
  rw [div_eq_mul_inv]
  ring

/-- `Σ_j Σ_k v_j v_k c_jk ≤ A Σ v_j² + E m Σ v_j²` when `c` is `E`-close to `A·δ_jk`. -/
theorem sum_sum_mul_le (v : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (A E : ℝ) (hE : 0 ≤ E)
    (hc : ∀ j k, |c j k - (if k = j then A else 0)| ≤ E) :
    ∑ j, ∑ k, v j * v k * c j k ≤ A * ∑ j, v j ^ 2 + E * m * ∑ j, v j ^ 2 := by
  have h2 : ∀ j k, v j * v k * (c j k - if k = j then A else 0) ≤ |v j| * |v k| * E := by
    intro j k
    calc v j * v k * (c j k - if k = j then A else 0)
        ≤ |v j * v k * (c j k - if k = j then A else 0)| := le_abs_self _
      _ = |v j| * |v k| * |c j k - if k = j then A else 0| := by rw [abs_mul, abs_mul]
      _ ≤ |v j| * |v k| * E := mul_le_mul_of_nonneg_left (hc j k) (by positivity)
  have h3 : ∑ j, ∑ k, v j * v k * (if k = j then A else 0) = A * ∑ j, v j ^ 2 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h4 : ∑ j, ∑ k, |v j| * |v k| * E = E * (∑ j, |v j|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have h5 : (∑ j, |v j|) ^ 2 ≤ m * ∑ j, v j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun j => |v j|)
    simpa [sq_abs] using this
  have hsplit : ∑ j, ∑ k, v j * v k * c j k = ∑ j, ∑ k, v j * v k * (if k = j then A else 0) +
      ∑ j, ∑ k, v j * v k * (c j k - if k = j then A else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have h6 : ∑ j, ∑ k, v j * v k * (c j k - if k = j then A else 0) ≤
      ∑ j, ∑ k, |v j| * |v k| * E :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h2 j k
  have h7 : E * (∑ j, |v j|) ^ 2 ≤ E * (m * ∑ j, v j ^ 2) := mul_le_mul_of_nonneg_left h5 hE
  rw [hsplit, h3]
  linarith

/-! ## The bottom maximum set -/

theorem norm_exp_mul_conj_sq (φ : ℝ) (z : ℂ) :
    ‖Complex.exp ((φ : ℂ) * I) * (starRingEnd ℂ) z ^ 2‖ = ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, norm_pow, Complex.norm_conj, one_mul]

/-- `−q₀ ≤ M* Σ|y_j|²`. -/
theorem neg_deepQ0_le {M θ : Fin m → ℝ} (hM : ∀ j, 0 ≤ M j) {Ms : ℝ} (hMs : ∀ j, M j ≤ Ms)
    (y : Fin m → ℂ) : -deepQ0 M θ y ≤ Ms * deepSq y := by
  rw [deepQ0, deepSq, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := neg_le_of_abs_le (Complex.abs_re_le_norm
    (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2))
  rw [norm_exp_mul_conj_sq] at h1
  have h2 : M j * -(Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2).re ≤
      M j * ‖y j‖ ^ 2 := mul_le_mul_of_nonneg_left (by linarith) (hM j)
  have h3 : M j * ‖y j‖ ^ 2 ≤ Ms * ‖y j‖ ^ 2 := mul_le_mul_of_nonneg_right (hMs j) (sq_nonneg _)
  linarith

/-- **Structure of the bottom maximizers.** On the sphere, `−q₀(y) = M*` forces `y` to live on the
maximal multiplicities and to satisfy `e^{iθ_j} ȳ_j = −y_j`. -/
theorem deep_bottom_structure {M θ : Fin m → ℝ} (hM : ∀ j, 0 < M j) {Ms : ℝ}
    (hMs : ∀ j, M j ≤ Ms) {y : Fin m → ℂ} (hy : deepSq y = 1) (hq : -deepQ0 M θ y = Ms) :
    (∀ j, (M j : ℂ) * y j = Ms * y j) ∧
      ∀ j, Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) = -y j := by
  set w : Fin m → ℂ := fun j => Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2 with hw
  have hwn : ∀ j, ‖w j‖ = ‖y j‖ ^ 2 := fun j => norm_exp_mul_conj_sq _ _
  have hre : ∀ j, 0 ≤ ‖y j‖ ^ 2 + (w j).re := by
    intro j; have := neg_le_of_abs_le (Complex.abs_re_le_norm (w j)); rw [hwn] at this; linarith
  have hterm : ∀ j, 0 ≤ (Ms - M j) * ‖y j‖ ^ 2 + M j * (‖y j‖ ^ 2 + (w j).re) := fun j =>
    add_nonneg (mul_nonneg (by linarith [hMs j]) (sq_nonneg _)) (mul_nonneg (hM j).le (hre j))
  have hsum : ∑ j, ((Ms - M j) * ‖y j‖ ^ 2 + M j * (‖y j‖ ^ 2 + (w j).re)) = 0 := by
    have e : ∀ j, (Ms - M j) * ‖y j‖ ^ 2 + M j * (‖y j‖ ^ 2 + (w j).re) =
        Ms * ‖y j‖ ^ 2 + M j * (w j).re := fun j => by ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ j, M j * (w j).re = deepQ0 M θ y := rfl
    rw [h1, ← deepSq, hy]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum
  have hparts : ∀ j, (Ms - M j) * ‖y j‖ ^ 2 = 0 ∧ M j * (‖y j‖ ^ 2 + (w j).re) = 0 := fun j =>
    (add_eq_zero_iff_of_nonneg (mul_nonneg (by linarith [hMs j]) (sq_nonneg _))
      (mul_nonneg (hM j).le (hre j))).mp (hzero j (Finset.mem_univ j))
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rcases mul_eq_zero.mp (hparts j).1 with h | h
    · rw [show M j = Ms by linarith]
    · have : y j = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; exact norm_eq_zero.mp this
      rw [this, mul_zero, mul_zero]
  · have h1 : (w j).re = -‖y j‖ ^ 2 := by
      rcases mul_eq_zero.mp (hparts j).2 with h | h
      · exact absurd h (hM j).ne'
      · linarith
    have him : (w j).im = 0 := by
      have h2 := Complex.sq_norm (w j)
      rw [Complex.normSq_apply, hwn, h1] at h2
      nlinarith [sq_nonneg (w j).im]
    have hwj : w j = -(y j * (starRingEnd ℂ) (y j)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      apply Complex.ext
      · simp only [Complex.neg_re, Complex.ofReal_re, h1]
      · simp only [Complex.neg_im, Complex.ofReal_im, him, neg_zero]
    have hfac : (starRingEnd ℂ) (y j) *
        (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) + y j) = 0 := by
      have : w j = Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) ^ 2 := rfl
      linear_combination this.symm.trans hwj
    rcases mul_eq_zero.mp hfac with h | h
    · have : y j = 0 := by simpa using h
      rw [this]; simp
    · linear_combination h

/-- On the bottom maximum set, `b₀ = −M* n₁`. -/
theorem deepB_zero_of_bottom {t M θ : Fin m → ℝ} {Ms : ℝ} {y : Fin m → ℂ}
    (hMy : ∀ j, (M j : ℂ) * y j = Ms * y j)
    (hph : ∀ j, Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) = -y j)
    (hq : deepQ0 M θ y = -Ms) :
    deepB 0 t M θ y = -Ms * deepN1 0 t y := by
  have h1 : deepQ1 0 t M θ y = -2 * Ms * deepN1 0 t y := by
    rw [deepQ1, deepN1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : Complex.exp ((θ j : ℂ) * I) * (4 * (starRingEnd ℂ) (y j) * deepRho 0 t y j +
        4 * ((0 : ℝ) : ℂ) * deepRho 0 t y j ^ 2) =
        4 * (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j)) * deepRho 0 t y j := by
      push_cast; ring
    rw [e, hph]
    have e2 : M j * (4 * -y j * deepRho 0 t y j).re =
        (-4 * ((M j : ℂ) * y j) * deepRho 0 t y j).re := by
      rw [show -4 * ((M j : ℂ) * y j) * deepRho 0 t y j =
        (M j : ℂ) * (4 * -y j * deepRho 0 t y j) by ring, Complex.re_ofReal_mul]
    rw [e2, hMy, show -4 * ((Ms : ℂ) * y j) * deepRho 0 t y j =
      ((-4 * Ms : ℝ) : ℂ) * (y j * deepRho 0 t y j) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  unfold deepB
  rw [h1, hq]
  simp
  ring

/-! ## The aperture line -/

/-- The unimodular factor `e^{−iφ}`. -/
def unimod (φ : ℝ) : ℂ := Complex.exp (-((φ : ℂ) * I))

theorem unimod_mul_conj (φ : ℝ) : unimod φ * (starRingEnd ℂ) (unimod φ) = 1 := by
  rw [unimod, ← Complex.exp_conj, ← Complex.exp_add]
  simp [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]

theorem unimod_add (x y : ℝ) : unimod (x + y) = unimod x * unimod y := by
  rw [unimod, unimod, unimod, ← Complex.exp_add]; congr 1; push_cast; ring

theorem unimod_sub (x y : ℝ) : unimod (x - y) = unimod x * (starRingEnd ℂ) (unimod y) := by
  rw [unimod, unimod, unimod, ← Complex.exp_conj, ← Complex.exp_add]; congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

theorem norm_unimod (φ : ℝ) : ‖unimod φ‖ = 1 := by
  rw [unimod, show -((φ : ℂ) * I) = ((-φ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem exp_aperturePhase (t : Fin m → ℝ) (a : ℝ) (j : Fin m) :
    Complex.exp ((aperturePhase t a j : ℂ) * I) = unimod (t j * a) * unimod (t j * a) := by
  rw [← unimod_add, unimod]; congr 1; simp only [aperturePhase]; push_cast; ring

/-- The real amplitude `v_j = Im(e^{it_j a} y_j)`. -/
def bottomV (t : Fin m → ℝ) (a : ℝ) (y : Fin m → ℂ) (j : Fin m) : ℝ :=
  ((starRingEnd ℂ) (unimod (t j * a)) * y j).im

/-- On the bottom set along the aperture line, `y_j = e^{−it_j a}(i v_j)` with `v_j` real. -/
theorem bottom_rep {t : Fin m → ℝ} {a : ℝ} {y : Fin m → ℂ}
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = -y j)
    (j : Fin m) :
    y j = unimod (t j * a) * (I * (bottomV t a y j : ℂ)) := by
  rw [bottomV]
  set E := unimod (t j * a)
  set F := (starRingEnd ℂ) E
  have hEF : E * F = 1 := unimod_mul_conj _
  set u := F * y j with hu_def
  have hu : (starRingEnd ℂ) u = -u := by
    have h := hph j
    rw [exp_aperturePhase] at h
    have hc : (starRingEnd ℂ) u = E * (starRingEnd ℂ) (y j) := by
      rw [hu_def, map_mul, Complex.conj_conj]
    rw [hc]
    calc E * (starRingEnd ℂ) (y j) = F * (E * E * (starRingEnd ℂ) (y j)) := by
          linear_combination (-(E * (starRingEnd ℂ) (y j))) * hEF
      _ = F * (-y j) := by rw [h]
      _ = -u := by rw [hu_def]; ring
  have hre : u.re = 0 := by
    have := congrArg Complex.re hu
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  have hu' : u = I * (u.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  calc y j = E * u := by rw [hu_def]; linear_combination (-(y j)) * hEF
    _ = E * (I * (u.im : ℂ)) := by rw [← hu']

theorem prod_bottom (x y v w : ℝ) :
    unimod x * (I * (v : ℂ)) * (unimod y * (I * (w : ℂ))) =
      ((-(v * w) : ℝ) : ℂ) * unimod (x + y) := by
  rw [unimod_add]; push_cast
  linear_combination (unimod x * unimod y * v * w) * Complex.I_sq

theorem prod_bottom_conj (x y v w : ℝ) :
    unimod x * (I * (v : ℂ)) * (starRingEnd ℂ) (unimod y * (I * (w : ℂ))) =
      ((v * w : ℝ) : ℂ) * unimod (x - y) := by
  rw [unimod_sub, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast
  linear_combination (-(unimod x * (starRingEnd ℂ) (unimod y) * v * w)) * Complex.I_sq

theorem re_unimod_mul_inv (v φ c : ℝ) :
    ((v : ℂ) * unimod φ * (-I * (c : ℂ))⁻¹).re = v * Real.sin φ / c :=
  re_ofReal_mul_exp_mul_inv v φ c

theorem deepRho_zero_eq (t : Fin m → ℝ) (y : Fin m → ℂ) (j : Fin m) :
    deepRho 0 t y j = (∑ k, y k * (-I * ((t j + t k : ℝ) : ℂ))⁻¹) +
      ∑ k, if k = j then 0 else (starRingEnd ℂ) (y k) * (-I * ((t j - t k : ℝ) : ℂ))⁻¹ := by
  simp only [deepRho]
  push_cast
  ring_nf

/-- The sinc-coefficient matrix of the bottom set. -/
def bottomCoeff (t : Fin m → ℝ) (a : ℝ) (j k : Fin m) : ℝ :=
  -2 * (Real.sin (t j * a + t k * a) / (t j + t k)) +
    if k = j then 0 else 2 * (Real.sin (t j * a - t k * a) / (t j - t k))

theorem deepN1_zero_bottom_eq {t : Fin m → ℝ} {a : ℝ} {y : Fin m → ℂ}
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = -y j) :
    deepN1 0 t y = ∑ j, ∑ k, bottomV t a y j * bottomV t a y k * bottomCoeff t a j k := by
  have hrep : ∀ j, y j = unimod (t j * a) * (I * (bottomV t a y j : ℂ)) :=
    fun j => bottom_rep hph j
  rw [deepN1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deepRho_zero_eq, mul_add, Finset.mul_sum, Finset.mul_sum, Complex.add_re, Complex.re_sum,
    Complex.re_sum, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : 2 * (y j * (y k * (-I * ((t j + t k : ℝ) : ℂ))⁻¹)).re =
      bottomV t a y j * bottomV t a y k * (-2 * (Real.sin (t j * a + t k * a) / (t j + t k))) := by
    rw [← mul_assoc, hrep j, hrep k, prod_bottom, re_unimod_mul_inv]; ring
  rw [h1, bottomCoeff, mul_add]
  congr 1
  split_ifs with hkj
  · simp
  · rw [← mul_assoc, hrep j, hrep k, prod_bottom_conj, re_unimod_mul_inv]; ring

theorem abs_bottomCoeff_sub_le {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) {τ : ℝ} (hτ : ∀ j, t j ≤ τ) {a : ℝ} (ha : 0 < a) (j k : Fin m) :
    |bottomCoeff t a j k - (if k = j then -2 * a else 0)| ≤ 4 * τ ^ 2 * a ^ 3 := by
  have hσ0 : t j + t k ≠ 0 := by linarith [htpos j, htpos k]
  have hσ := abs_sin_mul_div_sub_le ha hσ0
  rw [show (t j + t k) * a = t j * a + t k * a by ring] at hσ
  have hσsq : (t j + t k) ^ 2 ≤ 4 * τ ^ 2 := by
    nlinarith [htpos j, htpos k, hτ j, hτ k]
  have ha3 : 0 ≤ a ^ 3 := by positivity
  unfold bottomCoeff
  split_ifs with hkj
  · rw [add_zero, show -2 * (Real.sin (t j * a + t k * a) / (t j + t k)) - -2 * a =
      -2 * (Real.sin (t j * a + t k * a) / (t j + t k) - a) by ring, abs_mul]
    norm_num
    nlinarith
  · have hΔ0 : t j - t k ≠ 0 := sub_ne_zero.mpr fun h => hkj (ht h).symm
    have hΔ := abs_sin_mul_div_sub_le ha hΔ0
    rw [show (t j - t k) * a = t j * a - t k * a by ring] at hΔ
    have hΔsq : (t j - t k) ^ 2 ≤ τ ^ 2 := by
      nlinarith [htpos j, htpos k, hτ j, hτ k]
    have e : -2 * (Real.sin (t j * a + t k * a) / (t j + t k)) +
        2 * (Real.sin (t j * a - t k * a) / (t j - t k)) - 0 =
        2 * (Real.sin (t j * a - t k * a) / (t j - t k) - a) -
          2 * (Real.sin (t j * a + t k * a) / (t j + t k) - a) := by ring
    rw [e]
    calc |2 * (Real.sin (t j * a - t k * a) / (t j - t k) - a) -
          2 * (Real.sin (t j * a + t k * a) / (t j + t k) - a)|
        ≤ |2 * (Real.sin (t j * a - t k * a) / (t j - t k) - a)| +
          |2 * (Real.sin (t j * a + t k * a) / (t j + t k) - a)| := abs_sub _ _
      _ = 2 * |Real.sin (t j * a - t k * a) / (t j - t k) - a| +
          2 * |Real.sin (t j * a + t k * a) / (t j + t k) - a| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 4 * τ ^ 2 * a ^ 3 := by nlinarith

theorem norm_sq_eq_bottomV_sq {t : Fin m → ℝ} {a : ℝ} {y : Fin m → ℂ}
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = -y j)
    (j : Fin m) : ‖y j‖ ^ 2 = bottomV t a y j ^ 2 := by
  rw [bottom_rep hph j, norm_mul, norm_unimod, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul, one_mul, sq_abs]

/-- **The bottom set along the aperture line:** `n₁ ≤ −2a + 4mτ²a³`. -/
theorem deepN1_zero_le_of_bottom {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) {τ : ℝ} (hτ : ∀ j, t j ≤ τ) {a : ℝ} (ha : 0 < a) {y : Fin m → ℂ}
    (hy : deepSq y = 1)
    (hph : ∀ j, Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (y j) = -y j) :
    deepN1 0 t y ≤ -2 * a + 4 * m * τ ^ 2 * a ^ 3 := by
  rw [deepN1_zero_bottom_eq hph]
  have h := sum_sum_mul_le (bottomV t a y) (bottomCoeff t a) (-2 * a) (4 * τ ^ 2 * a ^ 3)
    (by positivity) (abs_bottomCoeff_sub_le ht htpos hτ ha)
  have hv : ∑ j, bottomV t a y j ^ 2 = 1 := by
    rw [← hy, deepSq]
    exact Finset.sum_congr rfl fun j _ => (norm_sq_eq_bottomV_sq hph j).symm
  rw [hv] at h
  linarith

/-! ## The top test vector -/

/-- The single-node top vector `e^{−it_{j₀} a} e_{j₀}`. -/
def topVec (t : Fin m → ℝ) (a : ℝ) (j₀ : Fin m) : Fin m → ℂ :=
  fun j => if j = j₀ then unimod (t j * a) else 0

theorem deepSq_topVec (t : Fin m → ℝ) (a : ℝ) (j₀ : Fin m) : deepSq (topVec t a j₀) = 1 := by
  simp only [deepSq, topVec, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, norm_unimod]
  simp

theorem topVec_phase (t : Fin m → ℝ) (a : ℝ) (j₀ j : Fin m) :
    Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (topVec t a j₀ j) =
      topVec t a j₀ j := by
  rw [exp_aperturePhase]
  unfold topVec
  split_ifs
  · linear_combination unimod (t j * a) * unimod_mul_conj (t j * a)
  · simp

theorem deepQ0_topVec (t M : Fin m → ℝ) (a : ℝ) (j₀ : Fin m) :
    deepQ0 M (aperturePhase t a) (topVec t a j₀) = M j₀ := by
  rw [deepQ0]
  have e : ∀ j, M j * (Complex.exp ((aperturePhase t a j : ℂ) * I) *
      (starRingEnd ℂ) (topVec t a j₀ j) ^ 2).re = if j = j₀ then M j₀ else 0 := by
    intro j
    rw [show Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (topVec t a j₀ j) ^ 2
      = (Complex.exp ((aperturePhase t a j : ℂ) * I) * (starRingEnd ℂ) (topVec t a j₀ j)) *
        (starRingEnd ℂ) (topVec t a j₀ j) by ring, topVec_phase]
    unfold topVec
    split_ifs with h
    · subst h; rw [unimod_mul_conj]; simp
    · simp
  simp_rw [e]
  simp

/-- On the top set, `b₀ = M* n₁`. -/
theorem deepB_zero_of_top {t M θ : Fin m → ℝ} {Ms : ℝ} {y : Fin m → ℂ}
    (hMy : ∀ j, (M j : ℂ) * y j = Ms * y j)
    (hph : ∀ j, Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j) = y j)
    (hq : deepQ0 M θ y = Ms) :
    deepB 0 t M θ y = Ms * deepN1 0 t y := by
  have h1 : deepQ1 0 t M θ y = 2 * Ms * deepN1 0 t y := by
    rw [deepQ1, deepN1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : Complex.exp ((θ j : ℂ) * I) * (4 * (starRingEnd ℂ) (y j) * deepRho 0 t y j +
        4 * ((0 : ℝ) : ℂ) * deepRho 0 t y j ^ 2) =
        4 * (Complex.exp ((θ j : ℂ) * I) * (starRingEnd ℂ) (y j)) * deepRho 0 t y j := by
      push_cast; ring
    rw [e, hph]
    have e2 : M j * (4 * y j * deepRho 0 t y j).re =
        (4 * ((M j : ℂ) * y j) * deepRho 0 t y j).re := by
      rw [show 4 * ((M j : ℂ) * y j) * deepRho 0 t y j =
        (M j : ℂ) * (4 * y j * deepRho 0 t y j) by ring, Complex.re_ofReal_mul]
    rw [e2, hMy, show 4 * ((Ms : ℂ) * y j) * deepRho 0 t y j =
      ((4 * Ms : ℝ) : ℂ) * (y j * deepRho 0 t y j) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  unfold deepB
  rw [h1, hq]
  simp
  ring

theorem deepN1_zero_topVec (t : Fin m → ℝ) (a : ℝ) (j₀ : Fin m) :
    deepN1 0 t (topVec t a j₀) = 2 * (Real.sin (t j₀ * a + t j₀ * a) / (t j₀ + t j₀)) := by
  rw [deepN1, Finset.sum_eq_single j₀]
  · rw [deepRho_zero_eq, Finset.sum_eq_single j₀, Finset.sum_eq_zero]
    · simp only [topVec, if_true, add_zero]
      rw [← mul_assoc, ← unimod_add, show unimod (t j₀ * a + t j₀ * a) =
        ((1 : ℝ) : ℂ) * unimod (t j₀ * a + t j₀ * a) by simp, re_unimod_mul_inv]
      ring
    · intro k _
      split_ifs with hk
      · rfl
      · simp [topVec, hk]
    · intro k _ hk; simp [topVec, hk]
    · simp
  · intro j _ hj; simp [topVec, hj]
  · simp

/-! ## The deep limit -/

/-- On the bottom maximum set along the aperture line, `−b₀ ≤ M*(−2a + 4mτ²a³)`. -/
theorem neg_deepB_zero_le_of_bottom {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) {Ms : ℝ} (hMs : ∀ j, M j ≤ Ms)
    (hMs0 : 0 < Ms) {τ : ℝ} (hτ : ∀ j, t j ≤ τ) {a : ℝ} (ha : 0 < a) {y : Fin m → ℂ}
    (hy : deepSq y = 1) (hq : -deepQ0 M (aperturePhase t a) y = Ms) :
    -deepB 0 t M (aperturePhase t a) y ≤ Ms * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) := by
  obtain ⟨hMy, hph⟩ := deep_bottom_structure hM hMs hy hq
  rw [deepB_zero_of_bottom (t := t) hMy hph (by linarith)]
  have hn := mul_le_mul_of_nonneg_left (deepN1_zero_le_of_bottom ht htpos hτ ha hy hph) hMs0.le
  linarith

/-- On the top vector, `b₀ ≥ M*(2a − 2τ²a³)`. -/
theorem deepB_zero_topVec_ge {t : Fin m → ℝ} (htpos : ∀ j, 0 < t j) {M : Fin m → ℝ}
    {j₀ : Fin m} (hMs0 : 0 < M j₀) {τ : ℝ} (hτ : ∀ j, t j ≤ τ) {a : ℝ}
    (ha : 0 < a) :
    M j₀ * (2 * a - 2 * τ ^ 2 * a ^ 3) ≤ deepB 0 t M (aperturePhase t a) (topVec t a j₀) := by
  have hb : deepB 0 t M (aperturePhase t a) (topVec t a j₀) =
      M j₀ * deepN1 0 t (topVec t a j₀) := by
    refine deepB_zero_of_top (fun j => ?_) (fun j => topVec_phase t a j₀ j) (deepQ0_topVec t M a j₀)
    unfold topVec; split_ifs with h
    · rw [h]
    · simp
  rw [hb, deepN1_zero_topVec]
  refine mul_le_mul_of_nonneg_left ?_ hMs0.le
  have h := abs_sin_mul_div_sub_le ha (show t j₀ + t j₀ ≠ 0 by linarith [htpos j₀])
  rw [show (t j₀ + t j₀) * a = t j₀ * a + t j₀ * a by ring] at h
  have h2 := (abs_le.mp h).1
  have h3 : (t j₀ + t j₀) ^ 2 ≤ 4 * τ ^ 2 := by nlinarith [htpos j₀, hτ j₀]
  have h4 : (t j₀ + t j₀) ^ 2 * a ^ 3 ≤ 4 * τ ^ 2 * a ^ 3 :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : 0 ≤ τ ^ 2 * a ^ 3 := by positivity
  linarith

/-- The arithmetic of the margin: `M*(2a − 2τ²a³) − ε/2 − (β + ε) ≥ M* a/2` for `ε = M* a`,
`β = M*(−2a + 4mτ²a³)` and `τ a (4m+2) = 1`. -/
theorem deep_margin {Ms a τ : ℝ} {m : ℕ} (hMs0 : 0 < Ms) (ha : 0 < a)
    (hua : τ * a * (4 * m + 2) = 1) :
    Ms * a / 2 ≤ Ms * (2 * a - 2 * τ ^ 2 * a ^ 3) - Ms * a / 2 -
      (Ms * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) + Ms * a) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu : τ * a ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ 4 * m + 2 := by linarith
    have hτa : 0 ≤ τ * a := by
      by_contra h
      push Not at h
      have : τ * a * (4 * m + 2) < 0 := mul_neg_of_neg_of_pos h (by linarith)
      linarith
    nlinarith
  have hcube : (2 + 4 * m) * τ ^ 2 * a ^ 3 = (τ * a) * a := by
    have : (2 + 4 * m) * τ ^ 2 * a ^ 3 = (τ * a * (4 * m + 2)) * (τ * a) * a := by ring
    rw [this, hua, one_mul]
  have h1 : Ms * ((τ * a) * a) ≤ Ms * (a / 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hMs0.le
  have e : Ms * (2 * a - 2 * τ ^ 2 * a ^ 3) - Ms * a / 2 -
      (Ms * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) + Ms * a) =
      5 / 2 * (Ms * a) - Ms * ((2 + 4 * m) * τ ^ 2 * a ^ 3) := by ring
  rw [e, hcube]
  have := mul_pos hMs0 ha
  linarith

/-- **The odd sector wins in the deep limit.** For distinct positive ordinates `t_j ≤ τ` and positive
multiplicities, the parity balance at the aperture `a₀ = 1/(τ(4m+2))` is positive for every
sufficiently small `δ > 0`. -/
theorem exists_deep_balance_pos {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) {τ : ℝ}
    (hτ : ∀ j, t j ≤ τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      0 < ccmParityBalance δ t M (aperturePhase t (1 / (τ * (4 * m + 2)))) := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (htpos ⟨0, hm⟩) (hτ ⟨0, hm⟩)
  set a : ℝ := 1 / (τ * (4 * m + 2)) with ha_def
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ha : 0 < a := by rw [ha_def]; positivity
  have hua : τ * a * (4 * m + 2) = 1 := by rw [ha_def]; field_simp
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ M ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hMs : ∀ j, M j ≤ M j₀ := fun j => hj₀ j (Finset.mem_univ j)
  have hMs0 : 0 < M j₀ := hM j₀
  have hε : 0 < M j₀ * a := mul_pos hMs0 ha
  obtain ⟨κ₁, hκ₁, hdan⟩ := GaloisForLFunctions.HTGeometry.Danskin.exists_perturbed_max_le
    (isCompact_deepSphere (m := m)) (q := fun y => -deepQ0 M (aperturePhase t a) y)
    (b₀ := fun y => -deepB 0 t M (aperturePhase t a) y)
    (continuous_deepQ0 M _).neg.continuousOn
    (continuous_deepB_zero ht htpos M _).neg.continuousOn (m₀ := M j₀)
    (β := M j₀ * (-2 * a + 4 * m * τ ^ 2 * a ^ 3)) hε
    (fun y hy => by
      have := neg_deepQ0_le (θ := aperturePhase t a) (fun j => (hM j).le) hMs y
      rwa [show deepSq y = 1 from hy, mul_one] at this)
    (fun y hy hq => neg_deepB_zero_le_of_bottom ht htpos hM hMs hMs0 hτ ha hy hq)
  obtain ⟨κ₂, hκ₂, hunif⟩ := exists_abs_deepB_sub_le ht htpos M (aperturePhase t a) (half_pos hε)
  refine ⟨min κ₁ κ₂, lt_min hκ₁ hκ₂, fun δ hδ hδκ => ?_⟩
  have hδ₁ : δ < κ₁ := lt_of_lt_of_le hδκ (min_le_left _ _)
  have hδ₂ : |δ| < κ₂ := by rw [abs_of_pos hδ]; exact lt_of_lt_of_le hδκ (min_le_right _ _)
  have h4δ : 0 < 4 * δ := by positivity
  -- the half-turned top eigenvalue
  obtain ⟨y, hy, hlam'⟩ := exists_ccmLambdaMax_halfTurn_deep hδ ht htpos hm M (aperturePhase t a)
  have hclose : ∀ x ∈ deepSphere m,
      |(fun y => -deepB δ t M (aperturePhase t a) y) x -
        (fun y => -deepB 0 t M (aperturePhase t a) y) x| ≤ M j₀ * a / 2 := by
    intro x hx
    rw [show (fun y => -deepB δ t M (aperturePhase t a) y) x -
        (fun y => -deepB 0 t M (aperturePhase t a) y) x =
        -(deepB δ t M (aperturePhase t a) x - deepB 0 t M (aperturePhase t a) x) from by ring,
      abs_neg]
    exact hunif δ hδ₂ x hx
  have hupper := hdan δ hδ hδ₁ _ hclose y hy
  have h2 : 4 * δ * ccmLambdaMax δ t M (halfTurn (aperturePhase t a)) ≤
      M j₀ + δ * (M j₀ * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) + M j₀ * a) := by
    rw [hlam', mul_neg, mul_div_cancel₀ _ h4δ.ne']
    linarith
  -- the top eigenvalue
  have hlow := le_ccmLambdaMax_deep hδ ht htpos hm M (aperturePhase t a) (deepSq_topVec t a j₀)
  rw [deepQ0_topVec, div_le_iff₀ h4δ] at hlow
  have hB := (abs_le.mp (hunif δ hδ₂ _ (deepSq_topVec t a j₀))).1
  have hB0 := deepB_zero_topVec_ge htpos hMs0 hτ ha
  have hmargin := deep_margin (m := m) hMs0 ha hua
  have hkey : δ * (M j₀ * a / 2) ≤ δ * (deepB δ t M (aperturePhase t a) (topVec t a j₀) -
      (M j₀ * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) + M j₀ * a)) :=
    mul_le_mul_of_nonneg_left (by linarith) hδ.le
  have hpos : 0 < δ * (M j₀ * a / 2) := by positivity
  have h3 : 0 < 4 * δ * (ccmLambdaMax δ t M (aperturePhase t a) -
      ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) := by
    have e : 4 * δ * (ccmLambdaMax δ t M (aperturePhase t a) -
        ccmLambdaMax δ t M (halfTurn (aperturePhase t a))) =
        ccmLambdaMax δ t M (aperturePhase t a) * (4 * δ) -
          4 * δ * ccmLambdaMax δ t M (halfTurn (aperturePhase t a)) := by ring
    rw [e]
    have e2 : δ * (deepB δ t M (aperturePhase t a) (topVec t a j₀) -
        (M j₀ * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) + M j₀ * a)) =
        δ * deepB δ t M (aperturePhase t a) (topVec t a j₀) -
          δ * (M j₀ * (-2 * a + 4 * m * τ ^ 2 * a ^ 3) + M j₀ * a) := by ring
    linarith
  unfold ccmParityBalance
  exact pos_of_mul_pos_right h3 h4δ.le

/-- **Odd ground states for deep finite top layers.** For fixed ordinates and multiplicities there is
`δ₀ > 0` such that every finite top layer of depth `δ < δ₀` with these data has reflection-odd
ground states at arbitrarily large apertures. -/
theorem exists_deep_ground_odd {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) {M : Fin m → ℝ} (hM : ∀ j, 0 < M j) {τ : ℝ}
    (hτ : ∀ j, t j ≤ τ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ < δ₀ → ∀ h : FiniteTopLayer δ t, h.mult = M → ∀ A : ℝ,
      ∃ a : SuzukiPositiveAperture, A < a.1 ∧
        ∀ u : CCMArchimedeanFormDomain a,
          ccmRestrictedWeilSourceQuadratic a u =
              ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
            ccmArchimedeanFormReflection a u = -u := by
  obtain ⟨δ₀, hδ₀, hF⟩ := exists_deep_balance_pos ht htpos hm hM hτ
  exact ⟨δ₀, hδ₀, fun δ hδ h hmult A =>
    exists_aperture_ground_odd h ⟨_, by rw [hmult]; exact hF δ h.pos hδ⟩ A⟩

end

end RHTower.CCMParityTopLayer