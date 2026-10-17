import GaloisForLFunctions.HTGeometry.SymbolicLevelSpaces

/-!
# Operator bounds for transfer operators on the Hölder space

Let `Ψ` bound the partition function `Φₙ(σ, x)` on the subshift and
`L = 2 + |s| D e^{|s| D}`, `D = C/(1 − θ)`.

* `norm_transferOp_pow_le`: `‖Lⁿ‖ ≤ Ψ (L + 1)`.
* `norm_transferOp_pow_comp_sub_cylAverage_le`: `‖Lⁿ(1 − E_n)‖ ≤ Ψ ϑⁿ (L + 2)` — the finite-rank
  approximation by cylinder averages is exponentially good (Lasota–Yorke).
* `norm_transferOp_sub_le`: for two `(R₀, C, θ)`-Hölder potentials with `|ψ − φ| ≤ C θ^m`,
  `‖L_ψ − L_φ‖ ≤ 3 k e^{|σ|R₀} |s| C e^{|s| C} (θ/ϑ)^m`.
* `partitionFun_levelPotential_le`, `partitionFun_le_periodicSum`: partition functions of the
  level potentials are controlled by those of the potential, and those by periodic-orbit sums.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop} {ϑ : ℝ}

theorem partitionFun_of_not_adm (φ : (ℕ → Fin k) → ℝ) (σ : ℝ) (n : ℕ) {x : ℕ → Fin k}
    (hx : ¬ IsAdmissible A x) : partitionFun A φ σ n x = 0 := by
  classical
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [if_neg]
  intro h
  exact hx (by simpa using h.shiftBy n)

/-- The Lasota–Yorke constant `2 + |s| D e^{|s| D}`, `D = C/(1 − θ)`. -/
def lyConst (C θ : ℝ) (s : ℂ) : ℝ := 2 + ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ)))

theorem lyConst_nonneg {C θ : ℝ} (hC : 0 ≤ C) (hθ1 : θ < 1) (s : ℂ) : 0 ≤ lyConst C θ s := by
  unfold lyConst
  have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
  positivity

section Bounds

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- **A Lasota–Yorke bound for a function**: if `g` vanishes off the subshift, `|g| ≤ a` and
`|g x − g y| ≤ b ϑ^j`, then `‖Lⁿ g‖ ≤ Ψ max(a, b ϑⁿ + a |s| D e^{|s| D}, 2a)`, written with the
common bound `Ψ (2a + b ϑⁿ + a |s| D e^{|s|D})`. -/
theorem norm_transferOp_pow_apply_bound (s : ℂ) (n : ℕ) {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ)
    (hΨ : ∀ x, IsAdmissible A x → partitionFun A φ s.re n x ≤ Ψ) (g : HolderSpace A ϑ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hsup : ∀ y, ‖g y‖ ≤ a)
    (hhol : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → ‖g x - g y‖ ≤ b * ϑ ^ j) :
    ‖(transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) g‖ ≤
      Ψ * (2 * a + b * ϑ ^ n + a * (‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))))) := by
  set T := transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s
  set D := C / (1 - θ) with hD
  have hD0 : 0 ≤ D := div_nonneg hC (by linarith)
  set E := ‖s‖ * D * Real.exp (‖s‖ * D)
  have hE : 0 ≤ E := by positivity
  have hsupp : ∀ y, ¬ IsAdmissible A y → g y = 0 := fun y hy => apply_of_not_adm g hy
  have hK : 0 ≤ Ψ * (2 * a + b * ϑ ^ n + a * E) := by
    have : 0 ≤ ϑ ^ n := pow_nonneg hϑ.le n
    positivity
  have hpt : ∀ y, IsAdmissible A y → ‖(T ^ n) g y‖ ≤ Ψ * a := by
    intro y hy
    rw [transferOp_pow_apply]
    exact (norm_transferFun_pow_apply_le φ s n hsupp hsup y).trans
      (mul_le_mul_of_nonneg_right (hΨ y hy) ha)
  refine norm_le_of_bounds hϑ _ hK (fun y => ?_) (fun x y j hx hy hxy => ?_)
  · by_cases hy : IsAdmissible A y
    · refine (hpt y hy).trans ?_
      have : 0 ≤ b * ϑ ^ n := mul_nonneg hb (pow_nonneg hϑ.le n)
      nlinarith
    · rw [apply_of_not_adm _ hy, norm_zero]; exact hK
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [pow_zero, mul_one]
      calc ‖(T ^ n) g x - (T ^ n) g y‖ ≤ ‖(T ^ n) g x‖ + ‖(T ^ n) g y‖ := norm_sub_le _ _
        _ ≤ Ψ * a + Ψ * a := add_le_add (hpt x hx) (hpt y hy)
        _ ≤ Ψ * (2 * a + b * ϑ ^ n + a * E) := by
            have : 0 ≤ Ψ * (b * ϑ ^ n + a * E) :=
              mul_nonneg hΨ0 (add_nonneg (mul_nonneg hb (pow_nonneg hϑ.le n)) (mul_nonneg ha hE))
            nlinarith
    · rw [transferOp_pow_apply, transferOp_pow_apply]
      have h := norm_transferFun_pow_apply_sub_le hφ hθ0 hθ1 (ϑ := ϑ) s n hsupp hsup hhol
        hx hy hj hxy
      refine h.trans ?_
      have hθj : θ ^ j ≤ ϑ ^ j := pow_le_pow_left₀ hθ0 hθϑ j
      have hϑj : 0 ≤ ϑ ^ j := pow_nonneg hϑ.le j
      have h1 : C * θ ^ j / (1 - θ) ≤ D * ϑ ^ j := by
        rw [hD, div_mul_eq_mul_div, mul_comm C (ϑ ^ j), mul_comm C (θ ^ j)]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθj hC) (by linarith)
      have h2 : b * ϑ ^ (n + j) + a * (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * D)) ≤
          (2 * a + b * ϑ ^ n + a * E) * ϑ ^ j := by
        rw [pow_add]
        have e1 : a * (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * D)) ≤ a * E * ϑ ^ j := by
          calc a * (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * D))
              ≤ a * (‖s‖ * (D * ϑ ^ j) * Real.exp (‖s‖ * D)) := by gcongr
            _ = a * E * ϑ ^ j := by ring
        have e2 : 0 ≤ 2 * a * ϑ ^ j := by positivity
        nlinarith
      calc partitionFun A φ s.re n x * (b * ϑ ^ (n + j) +
            a * (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ)))))
          ≤ Ψ * ((2 * a + b * ϑ ^ n + a * E) * ϑ ^ j) :=
            mul_le_mul (hΨ x hx) h2 (by positivity) hΨ0
        _ = Ψ * (2 * a + b * ϑ ^ n + a * E) * ϑ ^ j := by ring

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- **`‖Lⁿ‖ ≤ Ψ (L + 1)`.** -/
theorem norm_transferOp_pow_le (s : ℂ) (n : ℕ) {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ)
    (hΨ : ∀ x, IsAdmissible A x → partitionFun A φ s.re n x ≤ Ψ) :
    ‖transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n‖ ≤ Ψ * (lyConst C θ s + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hΨ0 (by linarith [lyConst_nonneg hC hθ1 s])) fun f => ?_
  have h := norm_transferOp_pow_apply_bound hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s n hΨ0 hΨ f
    (norm_nonneg f) (norm_nonneg f) (norm_apply_le f)
    (fun x y j hx hy hxy => norm_apply_sub_le hϑ f hx hy hxy)
  refine h.trans (le_of_eq_of_le rfl ?_)
  have hϑn : ϑ ^ n ≤ 1 := pow_le_one₀ hϑ.le hϑ1
  have hf := norm_nonneg f
  unfold lyConst
  have hE : 0 ≤ ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))) := by
    have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
    positivity
  have : ‖f‖ * ϑ ^ n ≤ ‖f‖ := mul_le_of_le_one_right hf hϑn
  nlinarith [mul_nonneg hΨ0 hf, mul_nonneg (mul_nonneg hΨ0 hf) hE]

include hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 in
/-- **`‖Lⁿ(1 − E_n)‖ ≤ Ψ ϑⁿ (L + 2)`**: the cylinder averages approximate exponentially well. -/
theorem norm_transferOp_pow_comp_sub_cylAverage_le (s : ℂ) (n : ℕ) {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ)
    (hΨ : ∀ x, IsAdmissible A x → partitionFun A φ s.re n x ≤ Ψ) :
    ‖transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n)‖ ≤
      Ψ * ϑ ^ n * (lyConst C θ s + 2) := by
  have hϑn : 0 ≤ ϑ ^ n := pow_nonneg hϑ.le n
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hΨ0 hϑn) (by linarith [lyConst_nonneg hC hθ1 s])) fun f => ?_
  set g := f - cylAverage hϑ n f
  have hg : ((transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n * (1 - cylAverage hϑ n) :
      HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ)) f =
      (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) g := rfl
  rw [hg]
  have hf := norm_nonneg f
  have hEf : ‖cylAverage hϑ n f‖ ≤ ‖f‖ :=
    ((cylAverage hϑ n).le_opNorm f).trans
      (by simpa using mul_le_mul_of_nonneg_right (norm_cylAverage_le (A := A) hϑ n) hf)
  have hgsup : ∀ y, ‖g y‖ ≤ ‖f‖ * ϑ ^ n := norm_sub_cylAverage_apply_le hϑ n f
  have hghol : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y →
      ‖g x - g y‖ ≤ (2 * ‖f‖) * ϑ ^ j := by
    intro x y j hx hy hxy
    calc ‖g x - g y‖ ≤ ‖g‖ * ϑ ^ j := norm_apply_sub_le hϑ g hx hy hxy
      _ ≤ (2 * ‖f‖) * ϑ ^ j := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hϑ.le j)
          calc ‖g‖ ≤ ‖f‖ + ‖cylAverage hϑ n f‖ := norm_sub_le _ _
            _ ≤ 2 * ‖f‖ := by linarith
  have h := norm_transferOp_pow_apply_bound hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s n hΨ0 hΨ g
    (mul_nonneg hf hϑn) (by positivity) hgsup hghol
  refine h.trans ?_
  unfold lyConst
  have hE : 0 ≤ ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))) := by
    have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
    positivity
  nlinarith [mul_nonneg (mul_nonneg hΨ0 hf) hϑn, mul_nonneg (mul_nonneg (mul_nonneg hΨ0 hf) hϑn) hE]

include hϑ hϑ1 hθ0 hθϑ in
/-- A quantity below both `θ^m` and `θ^j` is below `(θ/ϑ)^m ϑ^j`. -/
theorem le_div_pow_mul_pow {m j : ℕ} {c : ℝ} (hc : c ≤ θ ^ m) (hc' : c ≤ θ ^ j) :
    c ≤ (θ / ϑ) ^ m * ϑ ^ j := by
  have hq0 : 0 ≤ θ / ϑ := div_nonneg hθ0 hϑ.le
  have hq1 : θ / ϑ ≤ 1 := (div_le_one hϑ).mpr hθϑ
  have hθpow : ∀ i : ℕ, θ ^ i = (θ / ϑ) ^ i * ϑ ^ i := fun i => by
    rw [← mul_pow, div_mul_cancel₀ _ hϑ.ne']
  by_cases hjm : j ≤ m
  · refine hc.trans ?_
    rw [hθpow m]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hϑ.le hϑ1 hjm) (pow_nonneg hq0 m)
  · refine hc'.trans ?_
    rw [hθpow j]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 (by omega))
      (pow_nonneg hϑ.le j)

end Bounds

/-! ## Perturbation of the potential -/

section Perturbation

variable (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ ψ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hψ : IsHolderPotential A ψ R₀ C θ) (hC : 0 ≤ C)
  (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

/-- The perturbation constant `k e^{|σ| R₀} |s| C e^{|s| C}`. -/
def perturbConst (k : ℕ) (R₀ C : ℝ) (s : ℂ) : ℝ :=
  k * Real.exp (|s.re| * R₀) * (‖s‖ * C * Real.exp (‖s‖ * C))

/-- `|e^{−s a} − e^{−s b}| ≤ e^{|σ| R₀} |s| δ e^{|s| C}` for `|a| ≤ R₀`, `|a − b| ≤ δ ≤ C`. -/
theorem norm_cexp_sub_le_of_bounds (s : ℂ) {a b R₀ δ C : ℝ} (ha : |a| ≤ R₀) (hab : |a - b| ≤ δ)
    (hδC : δ ≤ C) :
    ‖Complex.exp (-(s * a)) - Complex.exp (-(s * b))‖ ≤
      Real.exp (|s.re| * R₀) * (‖s‖ * δ * Real.exp (‖s‖ * C)) := by
  refine (norm_cexp_neg_mul_sub_le s a b).trans ?_
  have h1 : Real.exp (-(s.re * a)) ≤ Real.exp (|s.re| * R₀) := by
    refine Real.exp_le_exp.mpr ?_
    have : -(s.re * a) ≤ |s.re| * |a| := by rw [← abs_mul]; exact neg_le_abs _
    exact this.trans (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
  have h2 : ‖s‖ * |a - b| * Real.exp (‖s‖ * |a - b|) ≤ ‖s‖ * δ * Real.exp (‖s‖ * C) := by
    have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hab
    gcongr
    exact hab.trans hδC
  exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le

include hφ hψ hθ0 hθ1 in
/-- **The transfer operator depends Lipschitz-continuously on the potential**:
`‖L_ψ − L_φ‖ ≤ 3 k e^{|σ| R₀} |s| C e^{|s| C} (θ/ϑ)^m` when `|ψ − φ| ≤ C θ^m`. -/
theorem norm_transferOp_sub_le {m : ℕ}
    (hclose : ∀ y, IsAdmissible A y → |ψ y - φ y| ≤ C * θ ^ m) (s : ℂ) :
    ‖transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s‖ ≤
      3 * perturbConst k R₀ C s * (θ / ϑ) ^ m := by
  set E₀ := Real.exp (|s.re| * R₀)
  set Q := ‖s‖ * C * Real.exp (‖s‖ * C)
  have hQ : 0 ≤ Q := by positivity
  have hE₀ : 0 ≤ E₀ := (Real.exp_pos _).le
  have hq0 : 0 ≤ θ / ϑ := div_nonneg hθ0 hϑ.le
  have hθm1 : θ ^ m ≤ 1 := pow_le_one₀ hθ0 hθ1.le
  have hθmq : θ ^ m ≤ (θ / ϑ) ^ m := by
    have := le_div_pow_mul_pow hϑ hϑ1 hθ0 hθϑ (m := m) (j := 0) (c := θ ^ m) le_rfl
      (pow_le_one₀ hθ0 hθ1.le |>.trans (by simp))
    simpa using this
  set h : (ℕ → Fin k) → ℂ := fun z => Complex.exp (-(s * ψ z)) - Complex.exp (-(s * φ z))
  have hsize : ∀ z, IsAdmissible A z → ‖h z‖ ≤ E₀ * Q * θ ^ m := by
    intro z hz
    rw [norm_sub_rev]
    have := norm_cexp_sub_le_of_bounds s (hφ.bound z hz)
      (by rw [abs_sub_comm]; exact hclose z hz)
      (mul_le_of_le_one_right hC hθm1)
    calc ‖Complex.exp (-(s * φ z)) - Complex.exp (-(s * ψ z))‖
        ≤ E₀ * (‖s‖ * (C * θ ^ m) * Real.exp (‖s‖ * C)) := this
      _ = E₀ * Q * θ ^ m := by ring
  have hholE : ∀ (χ : (ℕ → Fin k) → ℝ), IsHolderPotential A χ R₀ C θ → ∀ z z' j,
      IsAdmissible A z → IsAdmissible A z' → Agree j z z' →
      ‖Complex.exp (-(s * χ z)) - Complex.exp (-(s * χ z'))‖ ≤ E₀ * Q * θ ^ j := by
    intro χ hχ z z' j hz hz' hzz
    have := norm_cexp_sub_le_of_bounds s (hχ.bound z hz) (hχ.holder z z' j hz hz' hzz)
      (mul_le_of_le_one_right hC (pow_le_one₀ hθ0 hθ1.le))
    calc _ ≤ E₀ * (‖s‖ * (C * θ ^ j) * Real.exp (‖s‖ * C)) := this
      _ = E₀ * Q * θ ^ j := by ring
  have hhol : ∀ z z' j, IsAdmissible A z → IsAdmissible A z' → Agree j z z' →
      ‖h z - h z'‖ ≤ 2 * (E₀ * Q) * ((θ / ϑ) ^ m * ϑ ^ j) := by
    intro z z' j hz hz' hzz
    have e1 : ‖h z - h z'‖ ≤ 2 * (E₀ * Q * θ ^ m) := by
      calc ‖h z - h z'‖ ≤ ‖h z‖ + ‖h z'‖ := norm_sub_le _ _
        _ ≤ E₀ * Q * θ ^ m + E₀ * Q * θ ^ m := add_le_add (hsize z hz) (hsize z' hz')
        _ = 2 * (E₀ * Q * θ ^ m) := by ring
    have e2 : ‖h z - h z'‖ ≤ 2 * (E₀ * Q * θ ^ j) := by
      have hsplit : h z - h z' = (Complex.exp (-(s * ψ z)) - Complex.exp (-(s * ψ z'))) -
          (Complex.exp (-(s * φ z)) - Complex.exp (-(s * φ z'))) := by simp only [h]; ring
      rw [hsplit]
      calc _ ≤ ‖Complex.exp (-(s * ψ z)) - Complex.exp (-(s * ψ z'))‖ +
            ‖Complex.exp (-(s * φ z)) - Complex.exp (-(s * φ z'))‖ := norm_sub_le _ _
        _ ≤ E₀ * Q * θ ^ j + E₀ * Q * θ ^ j :=
            add_le_add (hholE ψ hψ z z' j hz hz' hzz) (hholE φ hφ z z' j hz hz' hzz)
        _ = 2 * (E₀ * Q * θ ^ j) := by ring
    have hc0 : 0 ≤ 2 * (E₀ * Q) := by positivity
    by_cases hEQ : 2 * (E₀ * Q) = 0
    · have : ‖h z - h z'‖ ≤ 0 := by
        calc ‖h z - h z'‖ ≤ 2 * (E₀ * Q * θ ^ m) := e1
          _ = 2 * (E₀ * Q) * θ ^ m := by ring
          _ = 0 := by rw [hEQ, zero_mul]
      rw [hEQ, zero_mul]; exact this
    · have hpos : 0 < 2 * (E₀ * Q) := lt_of_le_of_ne hc0 (Ne.symm hEQ)
      have hc := le_div_pow_mul_pow hϑ hϑ1 hθ0 hθϑ (m := m) (j := j)
        (c := ‖h z - h z'‖ / (2 * (E₀ * Q)))
        (by rw [div_le_iff₀ hpos]; linarith) (by rw [div_le_iff₀ hpos]; linarith)
      rwa [div_le_iff₀ hpos, mul_comm] at hc
  -- pointwise formula
  have happly : ∀ f : HolderSpace A ϑ, ∀ y,
      (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s) f y =
        ∑ a : Fin k, h (cons a y) * f (cons a y) := by
    intro f y
    rw [_root_.sub_apply, sub_apply, transferOp_apply, transferOp_apply,
      transferFun_apply, transferFun_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [h]; ring
  set K := 3 * perturbConst k R₀ C s * (θ / ϑ) ^ m
  have hK : 0 ≤ K := by unfold K perturbConst; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun f => ?_
  have hf := norm_nonneg f
  set g := (transferOp hϑ hϑ1 hψ hC hθ0 hθϑ hθ1 s - transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s) f
  have hsupg : ∀ y, ‖g y‖ ≤ k * (E₀ * Q * (θ / ϑ) ^ m) * ‖f‖ := by
    intro y
    rw [happly]
    calc ‖∑ a : Fin k, h (cons a y) * f (cons a y)‖
        ≤ ∑ a : Fin k, ‖h (cons a y) * f (cons a y)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Fin k, E₀ * Q * (θ / ϑ) ^ m * ‖f‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul]
          by_cases ha : IsAdmissible A (cons a y)
          · exact mul_le_mul ((hsize _ ha).trans
              (mul_le_mul_of_nonneg_left hθmq (by positivity))) (norm_apply_le f _)
              (norm_nonneg _) (by positivity)
          · rw [apply_of_not_adm f ha, norm_zero, mul_zero]; positivity
      _ = k * (E₀ * Q * (θ / ϑ) ^ m) * ‖f‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hKeq : K * ‖f‖ = 3 * (k * (E₀ * Q * (θ / ϑ) ^ m) * ‖f‖) := by
    simp only [K, perturbConst, E₀, Q]; ring
  have hk0 : 0 ≤ (k : ℝ) * (E₀ * Q * (θ / ϑ) ^ m) * ‖f‖ := by positivity
  refine norm_le_of_bounds hϑ g (mul_nonneg hK hf) (fun y => ?_) (fun x y j hx hy hxy => ?_)
  · rw [hKeq]; linarith [hsupg y]
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [pow_zero, mul_one, hKeq]
      calc ‖g x - g y‖ ≤ ‖g x‖ + ‖g y‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hsupg x, hsupg y]
    · rw [happly, happly, ← Finset.sum_sub_distrib]
      have h0 : x 0 = y 0 := hxy 0 hj
      calc ‖∑ a : Fin k, (h (cons a x) * f (cons a x) - h (cons a y) * f (cons a y))‖
          ≤ ∑ a : Fin k, ‖h (cons a x) * f (cons a x) - h (cons a y) * f (cons a y)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _a : Fin k, 3 * (E₀ * Q * (θ / ϑ) ^ m) * ‖f‖ * ϑ ^ j := by
            refine Finset.sum_le_sum fun a _ => ?_
            by_cases ha : A a (x 0)
            · have hax : IsAdmissible A (cons a x) := (isAdmissible_cons_iff a x).mpr ⟨ha, hx⟩
              have hay : IsAdmissible A (cons a y) :=
                (isAdmissible_cons_iff a y).mpr ⟨h0 ▸ ha, hy⟩
              have hag : Agree (j + 1) (cons a x) (cons a y) := (agree_cons_iff a x y).mpr hxy
              have hsp : h (cons a x) * f (cons a x) - h (cons a y) * f (cons a y) =
                  h (cons a x) * (f (cons a x) - f (cons a y)) +
                    f (cons a y) * (h (cons a x) - h (cons a y)) := by ring
              rw [hsp]
              have t1 : ‖h (cons a x) * (f (cons a x) - f (cons a y))‖ ≤
                  E₀ * Q * (θ / ϑ) ^ m * (‖f‖ * ϑ ^ j) := by
                rw [norm_mul]
                refine mul_le_mul ((hsize _ hax).trans
                  (mul_le_mul_of_nonneg_left hθmq (by positivity))) ?_ (norm_nonneg _)
                  (by positivity)
                refine (norm_apply_sub_le hϑ f hax hay hag).trans ?_
                exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hϑ.le hϑ1 (by omega)) hf
              have t2 : ‖f (cons a y) * (h (cons a x) - h (cons a y))‖ ≤
                  ‖f‖ * (2 * (E₀ * Q) * ((θ / ϑ) ^ m * ϑ ^ j)) := by
                rw [norm_mul]
                refine mul_le_mul (norm_apply_le f _) ?_ (norm_nonneg _) hf
                exact (hhol _ _ _ hax hay hag).trans (by
                  have : ϑ ^ (j + 1) ≤ ϑ ^ j := pow_le_pow_of_le_one hϑ.le hϑ1 (by omega)
                  have hc : 0 ≤ 2 * (E₀ * Q) * (θ / ϑ) ^ m := by positivity
                  nlinarith)
              calc _ ≤ ‖h (cons a x) * (f (cons a x) - f (cons a y))‖ +
                    ‖f (cons a y) * (h (cons a x) - h (cons a y))‖ := norm_add_le _ _
                _ ≤ E₀ * Q * (θ / ϑ) ^ m * (‖f‖ * ϑ ^ j) +
                    ‖f‖ * (2 * (E₀ * Q) * ((θ / ϑ) ^ m * ϑ ^ j)) := add_le_add t1 t2
                _ = 3 * (E₀ * Q * (θ / ϑ) ^ m) * ‖f‖ * ϑ ^ j := by ring
            · have hax : ¬ IsAdmissible A (cons a x) := fun h' =>
                ha ((isAdmissible_cons_iff a x).mp h').1
              have hay : ¬ IsAdmissible A (cons a y) := fun h' =>
                ha (h0 ▸ ((isAdmissible_cons_iff a y).mp h').1)
              rw [apply_of_not_adm f hax, apply_of_not_adm f hay, mul_zero, mul_zero, sub_zero,
                norm_zero]
              positivity
        _ = K * ‖f‖ * ϑ ^ j := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKeq]; ring

end Perturbation

/-! ## Partition functions -/

/-- Birkhoff sums of two potentials within `δ` of each other differ by at most `n δ`. -/
theorem abs_birkhoff_sub_birkhoff_le {φ ψ : (ℕ → Fin k) → ℝ} {δ : ℝ}
    (hclose : ∀ y, IsAdmissible A y → |ψ y - φ y| ≤ δ) (n : ℕ) {z : ℕ → Fin k}
    (hz : IsAdmissible A z) : |birkhoff ψ n z - birkhoff φ n z| ≤ n * δ := by
  rw [birkhoff, birkhoff, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range n, (ψ (shiftBy i z) - φ (shiftBy i z))|
      ≤ ∑ i ∈ Finset.range n, |ψ (shiftBy i z) - φ (shiftBy i z)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, δ := Finset.sum_le_sum fun i _ => hclose _ (hz.shiftBy i)
    _ = n * δ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Comparison of partition functions** of potentials within `δ`. -/
theorem partitionFun_le_of_close {φ ψ : (ℕ → Fin k) → ℝ} {δ : ℝ}
    (hclose : ∀ y, IsAdmissible A y → |ψ y - φ y| ≤ δ) (σ : ℝ) (n : ℕ) (x : ℕ → Fin k) :
    partitionFun A ψ σ n x ≤ Real.exp (|σ| * (n * δ)) * partitionFun A φ σ n x := by
  classical
  rw [partitionFun, partitionFun, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs with hv
  · rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hb := abs_birkhoff_sub_birkhoff_le hclose n hv
    have : -(σ * birkhoff ψ n (prepend v x)) + σ * birkhoff φ n (prepend v x) ≤
        |σ| * (n * δ) := by
      have h1 : -(σ * birkhoff ψ n (prepend v x)) + σ * birkhoff φ n (prepend v x) =
          -(σ * (birkhoff ψ n (prepend v x) - birkhoff φ n (prepend v x))) := by ring
      rw [h1]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg σ)
    linarith
  · rw [mul_zero]

/-- **Partition functions are bounded by periodic-orbit sums** (the closing lemma). -/
theorem partitionFun_le_periodicSum {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M)
    {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ} (hφ : IsHolderPotential A φ R₀ C θ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) [NeZero (n + (M - 1))] (x : ℕ → Fin k) :
    partitionFun A φ σ n x ≤ Real.exp (|σ| * (C / (1 - θ) + (M - 1) * R₀)) *
      ∑ p ∈ periodicPoints A (n + (M - 1)), Real.exp (-(σ * birkhoff φ (n + (M - 1)) p)) :=
  partitionSum_le_periodicSum hmix hM hθ0 hθ1 hφ.bound hφ.holder σ hn x

end

end GaloisForLFunctions.HTGeometry.Symbolic
