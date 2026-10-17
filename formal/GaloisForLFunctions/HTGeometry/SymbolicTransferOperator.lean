import GaloisForLFunctions.HTGeometry.SymbolicHolderSpace

/-!
# Transfer operators of Hölder potentials on a subshift

For a potential `φ` on sequences and `s ∈ ℂ` the transfer operator is

  `(L g)(x) = Σ_a e^{−s φ(a x)} g(a x)`.

Applied to functions vanishing off the subshift, only admissible preimages contribute, and its
`n`-th power is `(Lⁿ g)(x) = Σ_{|v| = n} e^{−s φⁿ(v x)} g(v x)` (`transferFun_pow_apply`).

* `norm_transferFun_pow_apply_le` and `norm_transferFun_pow_apply_sub_le` — the **Lasota–Yorke
  inequality**: with the partition function `Φₙ(x) = Σ_{v x admissible} e^{−σ φⁿ(v x)}`,
  `|Lⁿ g(x)| ≤ Φₙ(x) ‖g‖_∞`, and for admissible `x, y` agreeing on `j ≥ 1` symbols
  `|Lⁿ g(x) − Lⁿ g(y)| ≤ Φₙ(x) (b ϑ^{n+j} + ‖g‖_∞ |s| D θ^j e^{|s| D})` when `g` has Hölder
  constant `b` and `φ` has distortion constant `D = C/(1 − θ)`.
* `transferOp` — the bounded operator on `HolderSpace A ϑ`, with `transferOp_pow_apply`.
* `cylPoint`, `levelPotential` — the locally constant approximation `φ_m = φ ∘ π_m` of a Hölder
  potential, `π_m y` a chosen admissible sequence with the same first `m` symbols.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop}

/-! ## An exponential estimate -/

/-- `|e^{−s a} − e^{−s b}| ≤ e^{−σ a} |s| |a − b| e^{|s| |a − b|}`. -/
theorem norm_cexp_neg_mul_sub_le (s : ℂ) (a b : ℝ) :
    ‖Complex.exp (-(s * a)) - Complex.exp (-(s * b))‖ ≤
      Real.exp (-(s.re * a)) * (‖s‖ * |a - b| * Real.exp (‖s‖ * |a - b|)) := by
  have hfac : Complex.exp (-(s * a)) - Complex.exp (-(s * b)) =
      Complex.exp (-(s * a)) * -(Complex.exp (s * ((a : ℂ) - b)) - 1) := by
    have he : Complex.exp (-(s * a)) * Complex.exp (s * ((a : ℂ) - b)) = Complex.exp (-(s * b)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [mul_neg, mul_sub, he, mul_one]; ring
  rw [hfac, norm_mul, norm_neg, Complex.norm_exp]
  have hre : (-(s * (a : ℂ))).re = -(s.re * a) := by simp
  rw [hre]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (s * ((a : ℂ) - b)) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h
  have hn : ‖s * ((a : ℂ) - b)‖ = ‖s‖ * |a - b| := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rwa [hn] at h

/-! ## Hölder potentials -/

/-- A potential bounded by `R₀` and `(C, θ)`-Hölder on the subshift. -/
structure IsHolderPotential (A : Fin k → Fin k → Prop) (φ : (ℕ → Fin k) → ℝ) (R₀ C θ : ℝ) :
    Prop where
  bound : ∀ y, IsAdmissible A y → |φ y| ≤ R₀
  holder : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j

theorem IsHolderPotential.const_nonneg {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) {x : ℕ → Fin k} (hx : IsAdmissible A x) : 0 ≤ C := by
  have := hφ.holder x x 0 hx hx (Agree.refl 0 x)
  simpa using this

/-! ## The transfer operator on functions -/

/-- The transfer operator `(L g)(x) = Σ_a e^{−s φ(a x)} g(a x)` on functions of sequences. -/
def transferFun (φ : (ℕ → Fin k) → ℝ) (s : ℂ) :
    ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ where
  toFun g x := ∑ a : Fin k, Complex.exp (-(s * φ (cons a x))) * g (cons a x)
  map_add' g h := by
    funext x; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

theorem transferFun_apply (φ : (ℕ → Fin k) → ℝ) (s : ℂ) (g : (ℕ → Fin k) → ℂ) (x : ℕ → Fin k) :
    transferFun φ s g x = ∑ a : Fin k, Complex.exp (-(s * φ (cons a x))) * g (cons a x) := rfl

/-- **The `n`-th power of the transfer operator** is a sum over the words of length `n`. -/
theorem transferFun_pow_apply (φ : (ℕ → Fin k) → ℝ) (s : ℂ) (n : ℕ) (g : (ℕ → Fin k) → ℂ)
    (x : ℕ → Fin k) :
    (transferFun φ s ^ n) g x = ∑ v : Fin n → Fin k,
      Complex.exp (-(s * birkhoff φ n (prepend v x))) * g (prepend v x) := by
  induction n generalizing g with
  | zero =>
    rw [pow_zero, Module.End.one_apply, Fintype.sum_unique]
    simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    symm
    rw [← (Fin.consEquiv fun _ => Fin k).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [transferFun_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hc : (Fin.consEquiv fun _ => Fin k) (a, v) = (Fin.cons a v : Fin (n + 1) → Fin k) := by
      funext i; simp [Fin.consEquiv_apply]
    rw [hc, prepend_cons, birkhoff_succ_cons]
    push_cast
    rw [mul_add, neg_add, Complex.exp_add]
    ring

/-! ## The Lasota–Yorke inequality -/

variable (A) in
open Classical in
/-- The **partition function** `Φₙ(σ, x) = Σ_{v x admissible} e^{−σ φⁿ(v x)}`. -/
def partitionFun (φ : (ℕ → Fin k) → ℝ) (σ : ℝ) (n : ℕ) (x : ℕ → Fin k) : ℝ :=
  ∑ v : Fin n → Fin k, if IsAdmissible A (prepend v x) then
    Real.exp (-(σ * birkhoff φ n (prepend v x))) else 0

theorem partitionFun_nonneg (φ : (ℕ → Fin k) → ℝ) (σ : ℝ) (n : ℕ) (x : ℕ → Fin k) :
    0 ≤ partitionFun A φ σ n x := by
  classical
  refine Finset.sum_nonneg fun v _ => ?_
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem norm_cexp_neg_mul_ofReal (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-(s * t))‖ = Real.exp (-(s.re * t)) := by
  rw [Complex.norm_exp]; simp

/-- **Lasota–Yorke, supremum part**: `|Lⁿ g(x)| ≤ Φₙ(x) ‖g‖_∞`. -/
theorem norm_transferFun_pow_apply_le (φ : (ℕ → Fin k) → ℝ) (s : ℂ) (n : ℕ)
    {g : (ℕ → Fin k) → ℂ} {a : ℝ} (hsupp : ∀ y, ¬ IsAdmissible A y → g y = 0)
    (hsup : ∀ y, ‖g y‖ ≤ a) (x : ℕ → Fin k) :
    ‖(transferFun φ s ^ n) g x‖ ≤ partitionFun A φ s.re n x * a := by
  classical
  rw [transferFun_pow_apply, partitionFun, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  split_ifs with hv
  · rw [norm_mul, norm_cexp_neg_mul_ofReal]
    exact mul_le_mul_of_nonneg_left (hsup _) (Real.exp_pos _).le
  · rw [hsupp _ hv, mul_zero, norm_zero, zero_mul]

/-- **Lasota–Yorke, Hölder part.**  For admissible `x, y` agreeing on `j ≥ 1` symbols,
`|Lⁿ g(x) − Lⁿ g(y)| ≤ Φₙ(x) (b ϑ^{n+j} + a |s| (C θ^j/(1 − θ)) e^{|s| C/(1 − θ)})`. -/
theorem norm_transferFun_pow_apply_sub_le {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {ϑ : ℝ} (s : ℂ) (n : ℕ)
    {g : (ℕ → Fin k) → ℂ} {a b : ℝ} (hsupp : ∀ y, ¬ IsAdmissible A y → g y = 0)
    (hsup : ∀ y, ‖g y‖ ≤ a)
    (hhol : ∀ x y m, IsAdmissible A x → IsAdmissible A y → Agree m x y → ‖g x - g y‖ ≤ b * ϑ ^ m)
    {x y : ℕ → Fin k} (hx : IsAdmissible A x) (hy : IsAdmissible A y) {j : ℕ} (hj : 1 ≤ j)
    (hxy : Agree j x y) :
    ‖(transferFun φ s ^ n) g x - (transferFun φ s ^ n) g y‖ ≤
      partitionFun A φ s.re n x * (b * ϑ ^ (n + j) +
        a * (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))))) := by
  classical
  have h0 : x 0 = y 0 := hxy 0 (by omega)
  have hC : 0 ≤ C := hφ.const_nonneg hx
  have h1θ : 0 < 1 - θ := by linarith
  rw [transferFun_pow_apply, transferFun_pow_apply, ← Finset.sum_sub_distrib, partitionFun,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  have hiff := isAdmissible_prepend_congr (A := A) v hx hy h0
  split_ifs with hv
  · have hv' : IsAdmissible A (prepend v y) := hiff.mp hv
    set X := prepend v x
    set Y := prepend v y
    have hag : Agree (j + n) X Y := agree_prepend v hxy
    have hag' : Agree (n + j) X Y := by rwa [Nat.add_comm] at hag
    have hΔ := abs_birkhoff_sub_le hθ0 hθ1 hφ.holder n j hv hv' hag'
    have hΔ' : |birkhoff φ n X - birkhoff φ n Y| ≤ C / (1 - θ) := by
      refine hΔ.trans (div_le_div_of_nonneg_right ?_ h1θ.le)
      exact mul_le_of_le_one_right hC (pow_le_one₀ hθ0 hθ1.le)
    have hsplit : Complex.exp (-(s * birkhoff φ n X)) * g X - Complex.exp (-(s * birkhoff φ n Y)) * g Y
        = Complex.exp (-(s * birkhoff φ n X)) * (g X - g Y) +
          g Y * (Complex.exp (-(s * birkhoff φ n X)) - Complex.exp (-(s * birkhoff φ n Y))) := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_cexp_neg_mul_ofReal]
    have hgxy : ‖g X - g Y‖ ≤ b * ϑ ^ (n + j) := by
      have := hhol X Y (j + n) hv hv' hag
      rwa [Nat.add_comm j n] at this
    have hexp := norm_cexp_neg_mul_sub_le s (birkhoff φ n X) (birkhoff φ n Y)
    have hexp' : ‖Complex.exp (-(s * birkhoff φ n X)) - Complex.exp (-(s * birkhoff φ n Y))‖ ≤
        Real.exp (-(s.re * birkhoff φ n X)) *
          (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ)))) := by
      refine hexp.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      gcongr
    have hE := (Real.exp_pos (-(s.re * birkhoff φ n X))).le
    have ha : 0 ≤ a := (norm_nonneg _).trans (hsup X)
    calc Real.exp (-(s.re * birkhoff φ n X)) * ‖g X - g Y‖ +
          ‖g Y‖ * ‖Complex.exp (-(s * birkhoff φ n X)) - Complex.exp (-(s * birkhoff φ n Y))‖
        ≤ Real.exp (-(s.re * birkhoff φ n X)) * (b * ϑ ^ (n + j)) +
          a * (Real.exp (-(s.re * birkhoff φ n X)) *
            (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))))) := by
          gcongr
          exact hsup Y
      _ = Real.exp (-(s.re * birkhoff φ n X)) * (b * ϑ ^ (n + j) +
          a * (‖s‖ * (C * θ ^ j / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))))) := by ring
  · have hv' : ¬ IsAdmissible A (prepend v y) := fun h => hv (hiff.mpr h)
    rw [hsupp _ hv, hsupp _ hv', mul_zero, mul_zero, sub_zero, norm_zero, zero_mul]

/-- The one-step partition function is at most `k e^{|σ| R₀}`. -/
theorem partitionFun_one_le {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) (σ : ℝ) (x : ℕ → Fin k) :
    partitionFun A φ σ 1 x ≤ k * Real.exp (|σ| * R₀) := by
  classical
  rw [partitionFun]
  calc (∑ v : Fin 1 → Fin k, if IsAdmissible A (prepend v x) then
        Real.exp (-(σ * birkhoff φ 1 (prepend v x))) else 0)
      ≤ ∑ _v : Fin 1 → Fin k, Real.exp (|σ| * R₀) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs with hv
        · refine Real.exp_le_exp.mpr ?_
          have hb := hφ.bound _ hv
          have hb1 : birkhoff φ 1 (prepend v x) = φ (prepend v x) := by simp [birkhoff]
          rw [hb1]
          have := abs_le.mp hb
          have h2 : -(σ * φ (prepend v x)) ≤ |σ| * |φ (prepend v x)| := by
            rw [← abs_mul]; exact neg_le_abs _
          exact h2.trans (mul_le_mul_of_nonneg_left hb (abs_nonneg σ))
        · exact (Real.exp_pos _).le
    _ = k * Real.exp (|σ| * R₀) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, pow_one, nsmul_eq_mul]

/-! ## The transfer operator on the Hölder space -/

/-- The operator-norm constant of the one-step transfer operator. -/
def transferConst (k : ℕ) (R₀ C θ : ℝ) (s : ℂ) : ℝ :=
  k * Real.exp (|s.re| * R₀) * (2 + ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))))

theorem transferConst_nonneg {R₀ C θ : ℝ} (hC : 0 ≤ C) (hθ1 : θ < 1) (s : ℂ) :
    0 ≤ transferConst k R₀ C θ s := by
  unfold transferConst
  have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
  positivity

/-- **The transfer operator** on `F_ϑ` of a Hölder potential, for `θ ≤ ϑ ≤ 1`. -/
def transferOp {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)
    (s : ℂ) : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ :=
  ofLinear hϑ (transferFun φ s) (transferConst k R₀ C θ s) (transferConst_nonneg hC hθ1 s)
    (fun f y hy => by
      rw [transferFun_apply]
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ¬ IsAdmissible A (cons a y) := fun h => hy ((isAdmissible_cons_iff a y).mp h).2
      rw [apply_of_not_adm f this, mul_zero])
    (fun f y => by
      have h := norm_transferFun_pow_apply_le (A := A) φ s 1 (g := f)
        (fun y hy => apply_of_not_adm f hy) (norm_apply_le f) y
      rw [pow_one] at h
      refine h.trans ?_
      have hP := partitionFun_one_le hφ s.re y
      have hK : k * Real.exp (|s.re| * R₀) ≤ transferConst k R₀ C θ s := by
        unfold transferConst
        have : 0 ≤ C / (1 - θ) := div_nonneg hC (by linarith)
        have h1 : (1 : ℝ) ≤ 2 + ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))) := by
          have : 0 ≤ ‖s‖ * (C / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ))) := by positivity
          linarith
        exact le_mul_of_one_le_right (by positivity) h1
      exact mul_le_mul_of_nonneg_right (hP.trans hK) (norm_nonneg f))
    (fun f x y m hx hy hxy => by
      have hP : ∀ z, partitionFun A φ s.re 1 z ≤ k * Real.exp (|s.re| * R₀) :=
        partitionFun_one_le hφ s.re
      set K₀ := k * Real.exp (|s.re| * R₀) with hK₀
      set D := C / (1 - θ) with hDdef
      have hD : 0 ≤ D := div_nonneg hC (by linarith)
      have hK0 : 0 ≤ K₀ := by positivity
      have hf := norm_nonneg f
      have hE : 0 ≤ ‖s‖ * D * Real.exp (‖s‖ * D) := by positivity
      have hconst : transferConst k R₀ C θ s = K₀ * (2 + ‖s‖ * D * Real.exp (‖s‖ * D)) := rfl
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have h1 := norm_transferFun_pow_apply_le (A := A) φ s 1 (g := f)
          (fun y hy => apply_of_not_adm f hy) (norm_apply_le f) x
        have h2 := norm_transferFun_pow_apply_le (A := A) φ s 1 (g := f)
          (fun y hy => apply_of_not_adm f hy) (norm_apply_le f) y
        rw [pow_one] at h1 h2
        have h1' := h1.trans (mul_le_mul_of_nonneg_right (hP x) hf)
        have h2' := h2.trans (mul_le_mul_of_nonneg_right (hP y) hf)
        rw [pow_zero, mul_one, hconst]
        calc ‖transferFun φ s (toFn f) x - transferFun φ s (toFn f) y‖
            ≤ ‖transferFun φ s (toFn f) x‖ + ‖transferFun φ s (toFn f) y‖ := norm_sub_le _ _
          _ ≤ K₀ * ‖f‖ + K₀ * ‖f‖ := add_le_add h1' h2'
          _ ≤ K₀ * (2 + ‖s‖ * D * Real.exp (‖s‖ * D)) * ‖f‖ := by
              have := mul_nonneg (mul_nonneg hK0 hE) hf
              nlinarith
      · have h := norm_transferFun_pow_apply_sub_le hφ hθ0 hθ1 (ϑ := ϑ) s 1 (g := f)
          (a := ‖f‖) (b := ‖f‖) (fun y hy => apply_of_not_adm f hy) (norm_apply_le f)
          (fun x y m hx hy hxy => norm_apply_sub_le hϑ f hx hy hxy) hx hy hm hxy
        rw [pow_one] at h
        refine h.trans ?_
        have hθm : θ ^ m ≤ ϑ ^ m := pow_le_pow_left₀ hθ0 hθϑ m
        have hϑ1m : ϑ ^ (1 + m) ≤ ϑ ^ m := pow_le_pow_of_le_one hϑ.le hϑ1 (by omega)
        have hϑm : 0 ≤ ϑ ^ m := pow_nonneg hϑ.le m
        have hCθ : C * θ ^ m / (1 - θ) ≤ D * ϑ ^ m := by
          rw [hDdef, div_mul_eq_mul_div, mul_comm C (ϑ ^ m), mul_comm C (θ ^ m)]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hθm hC) (by linarith)
        have hin : ‖f‖ * ϑ ^ (1 + m) + ‖f‖ * (‖s‖ * (C * θ ^ m / (1 - θ)) *
            Real.exp (‖s‖ * (C / (1 - θ)))) ≤
            (2 + ‖s‖ * D * Real.exp (‖s‖ * D)) * ‖f‖ * ϑ ^ m := by
          have e1 : ‖f‖ * ϑ ^ (1 + m) ≤ ‖f‖ * ϑ ^ m := mul_le_mul_of_nonneg_left hϑ1m hf
          have e2 : ‖f‖ * (‖s‖ * (C * θ ^ m / (1 - θ)) * Real.exp (‖s‖ * (C / (1 - θ)))) ≤
              ‖f‖ * (‖s‖ * (D * ϑ ^ m) * Real.exp (‖s‖ * D)) := by
            gcongr
          nlinarith
        calc partitionFun A φ s.re 1 x * (‖f‖ * ϑ ^ (1 + m) + ‖f‖ * (‖s‖ * (C * θ ^ m / (1 - θ)) *
              Real.exp (‖s‖ * (C / (1 - θ)))))
            ≤ K₀ * ((2 + ‖s‖ * D * Real.exp (‖s‖ * D)) * ‖f‖ * ϑ ^ m) :=
              mul_le_mul (hP x) hin (by positivity) hK0
          _ = transferConst k R₀ C θ s * ‖f‖ * ϑ ^ m := by rw [hconst]; ring)

section TransferOpLemmas

variable {ϑ : ℝ} (hϑ : 0 < ϑ) (hϑ1 : ϑ ≤ 1) {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
  (hφ : IsHolderPotential A φ R₀ C θ) (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθϑ : θ ≤ ϑ) (hθ1 : θ < 1)

theorem transferOp_apply (s : ℂ) (f : HolderSpace A ϑ) (y : ℕ → Fin k) :
    transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s f y = transferFun φ s f y :=
  ofLinear_apply _ _ _ _ _ _ _ _ _

/-- The powers of the transfer operator act by the powers on functions. -/
theorem transferOp_pow_apply (s : ℂ) (n : ℕ) (f : HolderSpace A ϑ) (y : ℕ → Fin k) :
    (transferOp hϑ hϑ1 hφ hC hθ0 hθϑ hθ1 s ^ n) f y = (transferFun φ s ^ n) f y := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    have hmul : ∀ (S U : HolderSpace A ϑ →L[ℂ] HolderSpace A ϑ) (g : HolderSpace A ϑ),
        (S * U) g = S (U g) := fun _ _ _ => rfl
    rw [pow_succ, hmul, ih, pow_succ, Module.End.mul_apply]
    rfl

end TransferOpLemmas

/-! ## Locally constant approximations -/

variable (A) in
open Classical in
/-- A chosen admissible sequence with the same first `m` symbols as `y` (or `y` itself if there is
none). -/
def cylPoint (m : ℕ) (y : ℕ → Fin k) : ℕ → Fin k :=
  if h : ∃ z, IsAdmissible A z ∧ ∀ i : Fin m, z i = y i then Classical.choose h else y

theorem cylPoint_spec {m : ℕ} {y : ℕ → Fin k} (hy : IsAdmissible A y) :
    IsAdmissible A (cylPoint A m y) ∧ Agree m (cylPoint A m y) y := by
  have h : ∃ z, IsAdmissible A z ∧ ∀ i : Fin m, z i = y i := ⟨y, hy, fun _ => rfl⟩
  rw [cylPoint, dif_pos h]
  exact ⟨(Classical.choose_spec h).1, fun i hi => (Classical.choose_spec h).2 ⟨i, hi⟩⟩

theorem cylPoint_congr {m : ℕ} {y y' : ℕ → Fin k} (hy : IsAdmissible A y)
    (hy' : IsAdmissible A y') (h : Agree m y y') : cylPoint A m y = cylPoint A m y' := by
  have hw : (fun i : Fin m => y i) = fun i : Fin m => y' i := funext fun i => h i i.2
  have e1 : ∃ z, IsAdmissible A z ∧ ∀ i : Fin m, z i = y i := ⟨y, hy, fun _ => rfl⟩
  have e2 : ∃ z, IsAdmissible A z ∧ ∀ i : Fin m, z i = y' i := ⟨y', hy', fun _ => rfl⟩
  have hP : (fun z => IsAdmissible A z ∧ ∀ i : Fin m, z i = y i) =
      fun z => IsAdmissible A z ∧ ∀ i : Fin m, z i = y' i := by
    funext z; rw [show (∀ i : Fin m, z i = y i) ↔ ∀ i : Fin m, z i = y' i from
      ⟨fun hz i => (hz i).trans (h i i.2), fun hz i => (hz i).trans (h i i.2).symm⟩]
  rw [cylPoint, cylPoint, dif_pos e1, dif_pos e2]
  congr 1

variable (A) in
/-- The **level-`m` potential** `φ_m = φ ∘ π_m`, locally constant on cylinders of length `m`. -/
def levelPotential (φ : (ℕ → Fin k) → ℝ) (m : ℕ) : (ℕ → Fin k) → ℝ :=
  fun y => φ (cylPoint A m y)

theorem levelPotential_congr (φ : (ℕ → Fin k) → ℝ) {m : ℕ} {y y' : ℕ → Fin k}
    (hy : IsAdmissible A y) (hy' : IsAdmissible A y') (h : Agree m y y') :
    levelPotential A φ m y = levelPotential A φ m y' := by
  rw [levelPotential, levelPotential, cylPoint_congr hy hy' h]

/-- `|φ_m − φ| ≤ C θ^m` on the subshift. -/
theorem abs_levelPotential_sub_le {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) (m : ℕ) {y : ℕ → Fin k} (hy : IsAdmissible A y) :
    |levelPotential A φ m y - φ y| ≤ C * θ ^ m :=
  hφ.holder _ _ _ (cylPoint_spec hy).1 hy (cylPoint_spec hy).2

/-- The level-`m` potential is a Hölder potential with the same constants. -/
theorem isHolderPotential_levelPotential {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) (hθ0 : 0 ≤ θ) (m : ℕ) :
    IsHolderPotential A (levelPotential A φ m) R₀ C θ where
  bound y hy := hφ.bound _ (cylPoint_spec hy).1
  holder x y j hx hy hxy := by
    by_cases hjm : m ≤ j
    · rw [levelPotential_congr φ hx hy (hxy.mono hjm), sub_self, abs_zero]
      exact mul_nonneg (hφ.const_nonneg hx) (pow_nonneg hθ0 j)
    · have h1 : Agree j (cylPoint A m x) (cylPoint A m y) :=
        (((cylPoint_spec hx).2.mono (by omega)).trans hxy).trans
          ((cylPoint_spec hy).2.mono (by omega)).symm
      exact hφ.holder _ _ _ (cylPoint_spec hx).1 (cylPoint_spec hy).1 h1

end

end GaloisForLFunctions.HTGeometry.Symbolic
