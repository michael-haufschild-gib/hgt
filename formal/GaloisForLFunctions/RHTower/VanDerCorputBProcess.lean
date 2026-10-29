import GaloisForLFunctions.RHTower.StationaryPhaseWithCubicError
import GaloisForLFunctions.RHTower.TruncatedPoissonSummation

/-!
# The van der Corput `B`-process

Let `f` be real on `[A, B]` (`A ≤ B` integers) with `λ₂ ≤ f″ ≤ ρλ₂`, `|f‴| ≤ λ₃`, `α = f′(A) ≥ 0`,
`β = f′(B)`, and let `x_ν ∈ [A, B]` solve `f′(x_ν) = ν` for the integers `α < ν < β`.  For an
integer `K ≥ max(1, 2β)` and every `δ > 0` (`norm_sum_sub_bDualSum_le`),

  `‖Σ_{A<m≤B} e(f(m)) − Σ_{α<ν<β} e^{iπ/4} e(f(x_ν) − νx_ν)/√f″(x_ν)‖`
  `  ≤ 5 + K + 19/√λ₂ + (β − α + 1)(3λ₃δ⁴ + 3/(λ₂δ) + 2ρ)`.

**Proof.**  Truncated Poisson summation (`norm_sum_sub_truncatedPoisson_le`) replaces the sum by
the `2K + 1` integrals `∫ e(f(t) − νt)`, `|ν| ≤ K`, at cost `5`.  Each is then classified:
* `ν ≤ 0`, and `ν > 0` with `|f′ − ν| ≥ 1` throughout: first-derivative test, `≤ 1/2`;
* `ν` within distance `1` of `α` or of `β` (at most four integers, plus `ν = 0`): second-derivative
  test, or its crude stationary-phase companion, `≤ 4/√λ₂`;
* `α + 1 ≤ ν ≤ β − 1`: stationary phase with cubic error
  (`norm_integral_cexp_sub_stationary_le`); the stationary point is at distance `≥ 1/(ρλ₂)` from
  both ends, so the endpoint terms are `O(ρ)`.

The error `K` (one unit per dual frequency) is what this crude form pays for avoiding the
logarithmic Kusmin–Landau bookkeeping; it is below the trivial size `λ₂^{−1/2}` of a single dual
term.
-/

open Complex MeasureTheory Set intervalIntegral

namespace RHTower

noncomputable section

/-- The dual term of the `B`-process at frequency `ν`:
`e(f(x_ν) − νx_ν) f″(x_ν)^{−1/2} e^{iπ/4}`. -/
def bDualTerm (f f'' : ℝ → ℝ) (x : ℕ → ℝ) (ν : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (f (x ν) - ν * x ν) : ℝ) : ℂ) * I)
    * (((Real.sqrt (f'' (x ν)))⁻¹ : ℝ) : ℂ) * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)

theorem norm_bDualTerm_le {f f'' : ℝ → ℝ} {x : ℕ → ℝ} {ν : ℕ} {lam₂ : ℝ} (hlam₂ : 0 < lam₂)
    (h : lam₂ ≤ f'' (x ν)) : ‖bDualTerm f f'' x ν‖ ≤ (Real.sqrt lam₂)⁻¹ := by
  rw [bDualTerm, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
    one_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_anti₀ (Real.sqrt_pos.mpr hlam₂) (Real.sqrt_le_sqrt h)

/-- `√(2πλ) ≥ (9/4)√λ`. -/
theorem nine_fourths_mul_sqrt_le (y : ℝ) :
    9 / 4 * Real.sqrt y ≤ Real.sqrt (2 * Real.pi * y) := by
  rw [Real.sqrt_mul (by positivity) y]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [Real.pi_gt_three]

/-! ## The four regimes of a dual integral -/

/-- **Far from resonance.**  A convex phase with `|g′| ≥ 1` gives `‖∫ e(g)‖ ≤ 1/2`. -/
theorem norm_integral_cexp_twoPi_le_half {g g' g'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ∀ y ∈ Icc a b, HasDerivAt g (g' y) y) (hg' : ∀ y ∈ Icc a b, HasDerivAt g' (g'' y) y)
    (hg''c : ContinuousOn g'' (Icc a b)) (hpos : ∀ y ∈ Icc a b, 0 ≤ g'' y)
    (hlow : ∀ y ∈ Icc a b, 1 ≤ |g' y|) :
    ‖∫ t in a..b, Complex.exp (((2 * Real.pi * g t : ℝ) : ℂ) * I)‖ ≤ 1 / 2 := by
  have hpi := Real.pi_pos
  have h := norm_integral_cexp_side_le (F := fun t => 2 * Real.pi * g t)
    (F' := fun t => 2 * Real.pi * g' t) (F'' := fun t => 2 * Real.pi * g'' t)
    (m := 2 * Real.pi) hab (by positivity) (fun y hy => (hg y hy).const_mul _)
    (fun y hy => (hg' y hy).const_mul _) (continuousOn_const.mul hg''c)
    (fun y hy => mul_nonneg (by positivity) (hpos y hy))
    (fun y hy => by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [hlow y hy])
  refine h.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [Real.pi_gt_three]

/-- **Near resonance.**  `f″ ≥ λ₂` gives `‖∫ e(g)‖ ≤ 3/√λ₂`. -/
theorem norm_integral_cexp_twoPi_le_near {g g' g'' : ℝ → ℝ} {a b lam₂ : ℝ} (hab : a ≤ b)
    (hlam₂ : 0 < lam₂)
    (hg : ∀ y ∈ Icc a b, HasDerivAt g (g' y) y) (hg' : ∀ y ∈ Icc a b, HasDerivAt g' (g'' y) y)
    (hg''c : ContinuousOn g'' (Icc a b)) (hlo : ∀ y ∈ Icc a b, lam₂ ≤ g'' y) :
    ‖∫ t in a..b, Complex.exp (((2 * Real.pi * g t : ℝ) : ℂ) * I)‖ ≤ 3 / Real.sqrt lam₂ := by
  have hpi := Real.pi_pos
  have huI : uIcc a b = Icc a b := uIcc_of_le hab
  have h := norm_integral_cexp_secondDeriv (g := fun t => 2 * Real.pi * g t)
    (g' := fun t => 2 * Real.pi * g' t) (g'' := fun t => 2 * Real.pi * g'' t)
    hab (by positivity : 0 < 2 * Real.pi * lam₂)
    (fun y hy => (hg y (by rwa [huI] at hy)).const_mul _)
    (fun y hy => (hg' y (by rwa [huI] at hy)).const_mul _)
    (by rw [huI]; exact continuousOn_const.mul hg''c)
    (fun y hy => mul_le_mul_of_nonneg_left (hlo y (by rwa [huI] at hy)) (by positivity))
  refine h.trans ?_
  have hs := nine_fourths_mul_sqrt_le lam₂
  have hsq : 0 < Real.sqrt lam₂ := Real.sqrt_pos.mpr hlam₂
  rw [div_le_div_iff₀ (by positivity) hsq]
  nlinarith

/-- **Edge resonance.**  The crude stationary-phase bound: `‖∫ e(f − νt) − dual term‖ ≤ 4/√λ₂`. -/
theorem norm_integral_sub_bDualTerm_le_crude {f f' f'' : ℝ → ℝ} {A B lam₂ : ℝ} (hab : A ≤ B)
    (hlam₂ : 0 < lam₂)
    (hf : ∀ y ∈ Icc A B, HasDerivAt f (f' y) y) (hf' : ∀ y ∈ Icc A B, HasDerivAt f' (f'' y) y)
    (hf''c : ContinuousOn f'' (Icc A B)) (hlo : ∀ y ∈ Icc A B, lam₂ ≤ f'' y)
    {x : ℕ → ℝ} {ν : ℕ} (hxI : x ν ∈ Icc A B) :
    ‖(∫ t in A..B, Complex.exp (((2 * Real.pi * (f t - ν * t) : ℝ) : ℂ) * I))
        - bDualTerm f f'' x ν‖ ≤ 4 / Real.sqrt lam₂ := by
  have hpi := Real.pi_pos
  have huI : uIcc A B = Icc A B := uIcc_of_le hab
  have hμ : 0 < f'' (x ν) := lt_of_lt_of_le hlam₂ (hlo _ hxI)
  have h := norm_integral_cexp_sub_main_le_crude (F := fun t => 2 * Real.pi * (f t - ν * t))
    (F' := fun t => 2 * Real.pi * (f' t - ν)) (F'' := fun t => 2 * Real.pi * f'' t)
    (c := x ν) (lam₂ := 2 * Real.pi * lam₂)
    (θ := 2 * Real.pi * (f (x ν) - ν * x ν)) hab
    (fun y hy => (((hf y (by rwa [huI] at hy)).sub ((hasDerivAt_id' y).const_mul (ν : ℝ))).const_mul
      (2 * Real.pi)).congr_deriv (by ring))
    (fun y hy => ((hf' y (by rwa [huI] at hy)).sub_const (ν : ℝ)).const_mul (2 * Real.pi))
    (by rw [huI]; exact continuousOn_const.mul hf''c) (by positivity)
    (fun y hy => mul_le_mul_of_nonneg_left (hlo y (by rwa [huI] at hy)) (by positivity))
    (mul_le_mul_of_nonneg_left (hlo _ hxI) (by positivity))
  have hmain : Complex.exp (((2 * Real.pi * (f (x ν) - ν * x ν) : ℝ) : ℂ) * I)
      * (Complex.ofReal (Real.sqrt (2 * Real.pi / (2 * Real.pi * f'' (x ν))))
        * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)) = bDualTerm f f'' x ν := by
    have hsq : Real.sqrt (2 * Real.pi / (2 * Real.pi * f'' (x ν))) = (Real.sqrt (f'' (x ν)))⁻¹ := by
      rw [show 2 * Real.pi / (2 * Real.pi * f'' (x ν)) = (f'' (x ν))⁻¹ by field_simp,
        Real.sqrt_inv]
    rw [hsq, bDualTerm]
    ring
  rw [hmain] at h
  refine h.trans ?_
  have hs := nine_fourths_mul_sqrt_le lam₂
  have hsq : 0 < Real.sqrt lam₂ := Real.sqrt_pos.mpr hlam₂
  rw [div_le_div_iff₀ (by positivity) hsq]
  nlinarith

/-- **Deep resonance.**  For `α + 1 ≤ ν ≤ β − 1` the stationary point is `≥ 1/(ρλ₂)` from both ends,
and stationary phase leaves `3λ₃δ⁴ + 3/(λ₂δ) + 2ρ`. -/
theorem norm_integral_sub_bDualTerm_le_deep {f f' f'' f''' : ℝ → ℝ} {A B lam₂ lam₃ ρ δ : ℝ}
    (hf : ∀ y ∈ Icc A B, HasDerivAt f (f' y) y) (hf' : ∀ y ∈ Icc A B, HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Icc A B, HasDerivAt f'' (f''' y) y)
    (hlam₂ : 0 < lam₂) (hlo : ∀ y ∈ Icc A B, lam₂ ≤ f'' y)
    (hhi : ∀ y ∈ Icc A B, f'' y ≤ ρ * lam₂)
    (h3 : ∀ y ∈ Icc A B, |f''' y| ≤ lam₃) (hδ : 0 < δ)
    {x : ℕ → ℝ} {ν : ℕ} (hxI : x ν ∈ Icc A B) (hxν : f' (x ν) = ν)
    (hνa : f' A + 1 ≤ ν) (hνb : (ν : ℝ) + 1 ≤ f' B) :
    ‖(∫ t in A..B, Complex.exp (((2 * Real.pi * (f t - ν * t) : ℝ) : ℂ) * I))
        - bDualTerm f f'' x ν‖ ≤ 3 * lam₃ * δ ^ 4 + 3 / (lam₂ * δ) + 2 * ρ := by
  have hpi := Real.pi_pos
  have hAI : A ∈ Icc A B := ⟨le_rfl, hxI.1.trans hxI.2⟩
  have hBI : B ∈ Icc A B := ⟨hxI.1.trans hxI.2, le_rfl⟩
  have hlam₃ : 0 ≤ lam₃ := (abs_nonneg _).trans (h3 A hAI)
  have hρ : 0 < ρ * lam₂ := lt_of_lt_of_le hlam₂ ((hlo A hAI).trans (hhi A hAI))
  have hρ0 : 0 < ρ := pos_of_mul_pos_left hρ hlam₂.le
  -- the derivative grows at most at rate `ρλ₂`
  have hup : ∀ y ∈ Icc A B, ∀ z ∈ Icc A B, y ≤ z → f' z - f' y ≤ ρ * lam₂ * (z - y) := by
    refine (convex_Icc A B).image_sub_le_mul_sub_of_deriv_le
      (fun y hy => (hf' y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hf' y (interior_subset hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_)
    rw [(hf' y (interior_subset hy)).deriv]
    exact hhi y (interior_subset hy)
  have hgapA : 1 ≤ ρ * lam₂ * (x ν - A) := by
    have := hup A hAI (x ν) hxI hxI.1
    rw [hxν] at this; linarith
  have hgapB : 1 ≤ ρ * lam₂ * (B - x ν) := by
    have := hup (x ν) hxI B hBI hxI.2
    rw [hxν] at this; linarith
  have hxA : A < x ν := by
    by_contra h
    have : x ν - A ≤ 0 := by linarith
    nlinarith
  have hxB : x ν < B := by
    by_contra h
    have : B - x ν ≤ 0 := by linarith
    nlinarith
  have h := norm_integral_cexp_sub_stationary_le (F := fun t => 2 * Real.pi * (f t - ν * t))
    (F' := fun t => 2 * Real.pi * (f' t - ν)) (F'' := fun t => 2 * Real.pi * f'' t)
    (F''' := fun t => 2 * Real.pi * f''' t) (c := x ν) (lam₂ := 2 * Real.pi * lam₂)
    (lam₃ := 2 * Real.pi * lam₃) (δ := δ)
    (fun y hy => (((hf y hy).sub ((hasDerivAt_id' y).const_mul (ν : ℝ))).const_mul
      (2 * Real.pi)).congr_deriv (by ring))
    (fun y hy => ((hf' y hy).sub_const (ν : ℝ)).const_mul (2 * Real.pi))
    (fun y hy => (hf'' y hy).const_mul (2 * Real.pi)) (by positivity)
    (fun y hy => mul_le_mul_of_nonneg_left (hlo y hy) (by positivity))
    (fun y hy => by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      exact mul_le_mul_of_nonneg_left (h3 y hy) (by positivity))
    hδ hxA hxB (by simp [hxν])
  have hmain : Complex.exp (((2 * Real.pi * (f (x ν) - ν * x ν) : ℝ) : ℂ) * I)
      * (Complex.ofReal (Real.sqrt (2 * Real.pi / (2 * Real.pi * f'' (x ν))))
        * Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I)) = bDualTerm f f'' x ν := by
    have hμ : 0 < f'' (x ν) := lt_of_lt_of_le hlam₂ (hlo _ hxI)
    have hsq : Real.sqrt (2 * Real.pi / (2 * Real.pi * f'' (x ν))) = (Real.sqrt (f'' (x ν)))⁻¹ := by
      rw [show 2 * Real.pi / (2 * Real.pi * f'' (x ν)) = (f'' (x ν))⁻¹ by field_simp,
        Real.sqrt_inv]
    rw [hsq, bDualTerm]
    ring
  rw [hmain] at h
  refine h.trans ?_
  have e1 : 2 * Real.pi * lam₃ * δ ^ 4 / 3 ≤ 3 * lam₃ * δ ^ 4 := by
    have : 0 ≤ lam₃ * δ ^ 4 := by positivity
    nlinarith [Real.pi_lt_d2]
  have e2 : 14 / (2 * Real.pi * lam₂ * δ) ≤ 3 / (lam₂ * δ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < lam₂ * δ := mul_pos hlam₂ hδ
    nlinarith [Real.pi_gt_three]
  have e3 : ∀ g : ℝ, 1 ≤ ρ * lam₂ * g → 4 / (2 * Real.pi * lam₂ * g) ≤ ρ := by
    intro g hg
    have hg0 : 0 < g := by
      rcases le_or_gt g 0 with h0 | h0
      · nlinarith
      · exact h0
    rw [div_le_iff₀ (by positivity)]
    have : 4 ≤ 2 * Real.pi * (ρ * lam₂ * g) := by nlinarith [Real.pi_gt_three]
    nlinarith
  have e4 := e3 _ hgapA
  have e5 := e3 _ hgapB
  linarith

/-! ## Counting the exceptional frequencies -/

theorem sum_range_ite_le_card {K : ℕ} {p : ℕ → Prop} [DecidablePred p] {a : ℝ} (ha : 0 ≤ a)
    (s : Finset ℕ) (hs : ∀ n, p (n + 1) → n + 1 ∈ s) :
    ∑ n ∈ Finset.range K, (if p (n + 1) then a else 0) ≤ a * s.card := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ ha
  exact_mod_cast Finset.card_le_card_of_injOn (fun n => n + 1)
    (fun n hn => hs n (Finset.mem_filter.mp hn).2) (fun _ _ _ _ h => Nat.succ_injective h)

theorem card_bad_le (u v : ℕ) : (({u, u + 1, v, v + 1} : Finset ℕ).card : ℝ) ≤ 4 := by
  have : ({u, u + 1, v, v + 1} : Finset ℕ).card ≤ 4 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
  exact_mod_cast this

theorem card_Icc_floor_le {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    ((Finset.Icc (⌊α⌋₊ + 1) ⌊β⌋₊).card : ℝ) ≤ β - α + 1 := by
  rw [Nat.card_Icc]
  have h1 := Nat.floor_le (hα.trans hαβ)
  have h2 := Nat.lt_floor_add_one α
  rcases le_total (⌊α⌋₊ + 1) (⌊β⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]
    push_cast
    linarith
  · rw [Nat.sub_eq_zero_of_le h]
    push_cast
    linarith

/-! ## The `B`-process -/

/-- **The van der Corput `B`-process.**  See the module docstring. -/
theorem norm_sum_sub_bDualSum_le {f f' f'' f''' : ℝ → ℝ} {A B : ℤ} (hAB : A ≤ B)
    {lam₂ lam₃ ρ δ : ℝ} {K : ℕ}
    (hf : ∀ y ∈ Icc (A : ℝ) B, HasDerivAt f (f' y) y)
    (hf' : ∀ y ∈ Icc (A : ℝ) B, HasDerivAt f' (f'' y) y)
    (hf'' : ∀ y ∈ Icc (A : ℝ) B, HasDerivAt f'' (f''' y) y)
    (hlam₂ : 0 < lam₂) (hlo : ∀ y ∈ Icc (A : ℝ) B, lam₂ ≤ f'' y)
    (hhi : ∀ y ∈ Icc (A : ℝ) B, f'' y ≤ ρ * lam₂)
    (h3 : ∀ y ∈ Icc (A : ℝ) B, |f''' y| ≤ lam₃) (hδ : 0 < δ)
    (hα : 0 ≤ f' A) (hK : 2 * f' B ≤ K) (hK1 : 1 ≤ K)
    (x : ℕ → ℝ)
    (hx : ∀ ν : ℕ, f' A < ν → (ν : ℝ) < f' B → x ν ∈ Icc (A : ℝ) B ∧ f' (x ν) = ν) :
    ‖(∑ m ∈ Finset.Ioc A B, Complex.exp (((2 * Real.pi * f m : ℝ) : ℂ) * I))
        - ∑ ν ∈ Finset.Ioo ⌊f' A⌋₊ ⌈f' B⌉₊, bDualTerm f f'' x ν‖
      ≤ 5 + K + 19 / Real.sqrt lam₂
        + (f' B - f' A + 1) * (3 * lam₃ * δ ^ 4 + 3 / (lam₂ * δ) + 2 * ρ) := by
  classical
  have hab : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hAI : (A : ℝ) ∈ Icc (A : ℝ) B := ⟨le_rfl, hab⟩
  have hBI : (B : ℝ) ∈ Icc (A : ℝ) B := ⟨hab, le_rfl⟩
  set α := f' A with hαdef
  set β := f' B with hβdef
  have hf''c : ContinuousOn f'' (Icc (A : ℝ) B) := fun y hy =>
    (hf'' y hy).continuousAt.continuousWithinAt
  have hpos : ∀ y ∈ Icc (A : ℝ) B, 0 ≤ f'' y := fun y hy => hlam₂.le.trans (hlo y hy)
  have hgrow : ∀ y ∈ Icc (A : ℝ) B, ∀ z ∈ Icc (A : ℝ) B, y ≤ z → 0 * (z - y) ≤ f' z - f' y := by
    refine (convex_Icc (A : ℝ) B).mul_sub_le_image_sub_of_le_deriv
      (fun y hy => (hf' y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hf' y (interior_subset hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => ?_)
    rw [(hf' y (interior_subset hy)).deriv]
    exact hpos y (interior_subset hy)
  have hrange : ∀ y ∈ Icc (A : ℝ) B, α ≤ f' y ∧ f' y ≤ β := fun y hy =>
    ⟨by linarith [hgrow _ hAI y hy hy.1], by linarith [hgrow y hy _ hBI hy.2]⟩
  have hαβ : α ≤ β := (hrange _ hBI).1
  have hK' : ∀ y ∈ Icc (A : ℝ) B, |f' y| ≤ β := fun y hy => by
    rw [abs_of_nonneg (hα.trans (hrange y hy).1)]; exact (hrange y hy).2
  have hP := norm_sum_sub_truncatedPoisson_le hAB hf hf' hf''c hpos hK' hK hK1
  -- the phase derivatives of `f ± νt`
  have hsub : ∀ ν : ℝ, ∀ y ∈ Icc (A : ℝ) B, HasDerivAt (fun t => f t - ν * t) (f' y - ν) y :=
    fun ν y hy => ((hf y hy).sub ((hasDerivAt_id' y).const_mul ν)).congr_deriv (by ring)
  have hsub' : ∀ ν : ℝ, ∀ y ∈ Icc (A : ℝ) B, HasDerivAt (fun t => f' t - ν) (f'' y) y :=
    fun ν y hy => (hf' y hy).sub_const ν
  have hadd : ∀ ν : ℝ, ∀ y ∈ Icc (A : ℝ) B, HasDerivAt (fun t => f t + ν * t) (f' y + ν) y :=
    fun ν y hy => ((hf y hy).add ((hasDerivAt_id' y).const_mul ν)).congr_deriv (by ring)
  have hadd' : ∀ ν : ℝ, ∀ y ∈ Icc (A : ℝ) B, HasDerivAt (fun t => f' t + ν) (f'' y) y :=
    fun ν y hy => (hf' y hy).add_const ν
  -- the integrals of the Poisson formula
  set I₀ := ∫ t in (A : ℝ)..B, Complex.exp (((2 * Real.pi * f t : ℝ) : ℂ) * I) with hI₀
  set Ip : ℕ → ℂ := fun n => ∫ t in (A : ℝ)..B,
    Complex.exp (((2 * Real.pi * (f t + ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I) with hIp
  set Im : ℕ → ℂ := fun n => ∫ t in (A : ℝ)..B,
    Complex.exp (((2 * Real.pi * (f t - ((n : ℝ) + 1) * t) : ℝ) : ℂ) * I) with hIm
  have hI₀ : ‖I₀‖ ≤ 3 / Real.sqrt lam₂ :=
    norm_integral_cexp_twoPi_le_near hab hlam₂ hf hf' hf''c hlo
  have hIp_le : ∀ n : ℕ, ‖Ip n‖ ≤ 1 / 2 := fun n =>
    norm_integral_cexp_twoPi_le_half hab (hadd _) (hadd' _) hf''c hpos (fun y hy => by
      have h1 := (hrange y hy).1
      have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [abs_of_nonneg (by linarith)]
      linarith)
  -- the resonant frequencies and the main term
  set res : ℕ → Prop := fun ν => α < ν ∧ (ν : ℝ) < β with hres
  set R : ℕ → ℂ := fun n => if res (n + 1) then bDualTerm f f'' x (n + 1) else 0 with hR
  have hmain : ∑ ν ∈ Finset.Ioo ⌊α⌋₊ ⌈β⌉₊, bDualTerm f f'' x ν = ∑ n ∈ Finset.range K, R n := by
    have h1 : ∑ n ∈ Finset.range K, R n
        = ∑ ν ∈ Finset.Ico 1 (K + 1), (if res ν then bDualTerm f f'' x ν else 0) := by
      rw [Finset.sum_Ico_eq_sum_range, show K + 1 - 1 = K by omega]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hR, add_comm 1 n]
    rw [h1, ← Finset.sum_filter]
    congr 1
    ext ν
    simp only [Finset.mem_Ioo, Finset.mem_filter, Finset.mem_Ico, hres]
    rw [Nat.floor_lt hα, Nat.lt_ceil]
    constructor
    · rintro ⟨h1, h2⟩
      have hν0 : (0 : ℝ) < ν := lt_of_le_of_lt hα h1
      have hν1 : 1 ≤ ν := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
        rintro rfl; simp at hν0)
      have hνK : (ν : ℝ) < K + 1 := by linarith
      exact ⟨⟨hν1, by exact_mod_cast hνK⟩, h1, h2⟩
    · rintro ⟨_, h1, h2⟩
      exact ⟨h1, h2⟩
  -- the per-frequency error
  set S := 3 * lam₃ * δ ^ 4 + 3 / (lam₂ * δ) + 2 * ρ with hS
  set Bad : Finset ℕ := {⌊α⌋₊, ⌊α⌋₊ + 1, ⌊β⌋₊, ⌊β⌋₊ + 1} with hBad
  set deep : ℕ → Prop := fun ν => α + 1 ≤ ν ∧ (ν : ℝ) + 1 ≤ β with hdeep
  have hlam₃ : 0 ≤ lam₃ := (abs_nonneg _).trans (h3 _ hAI)
  have hρ : 0 ≤ ρ := by
    have h := (hlo _ hAI).trans (hhi _ hAI)
    rcases lt_or_ge ρ 0 with hneg | hneg
    · nlinarith
    · exact hneg
  have hS0 : 0 ≤ S := by positivity
  have hsq0 : 0 ≤ 4 / Real.sqrt lam₂ := by positivity
  have hαfl := Nat.floor_le hα
  have hαfl' := Nat.lt_floor_add_one α
  have hβfl := Nat.floor_le (hα.trans hαβ)
  have hβfl' := Nat.lt_floor_add_one β
  have herr : ∀ n ∈ Finset.range K, ‖Im n - R n‖
      ≤ (if n + 1 ∈ Bad then 4 / Real.sqrt lam₂ else 0) + (if deep (n + 1) then S else 0)
        + 1 / 2 := by
    intro n _
    set ν : ℕ := n + 1 with hν
    have hνcast : ((ν : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hν]; push_cast; ring
    have hImν : Im n = ∫ t in (A : ℝ)..B,
        Complex.exp (((2 * Real.pi * (f t - ν * t) : ℝ) : ℂ) * I) := by
      simp only [hIm, hνcast]
    have hite1 : 0 ≤ (if ν ∈ Bad then 4 / Real.sqrt lam₂ else 0) := by
      split_ifs <;> simp [hsq0]
    have hite2 : 0 ≤ (if deep ν then S else 0) := by split_ifs <;> simp [hS0]
    by_cases hB : ν ∈ Bad
    · rw [if_pos hB]
      by_cases hr : res ν
      · have hRn : R n = bDualTerm f f'' x ν := by simp only [hR]; rw [if_pos hr]
        rw [hRn, hImν]
        have := norm_integral_sub_bDualTerm_le_crude hab hlam₂ hf hf' hf''c hlo
          (hx ν hr.1 hr.2).1
        linarith
      · have hRn : R n = 0 := by simp only [hR]; rw [if_neg hr]
        rw [hRn, sub_zero, hImν]
        have := norm_integral_cexp_twoPi_le_near hab hlam₂ (hsub (ν : ℝ)) (hsub' (ν : ℝ)) hf''c hlo
        have h34 : 3 / Real.sqrt lam₂ ≤ 4 / Real.sqrt lam₂ :=
          div_le_div_of_nonneg_right (by norm_num) (Real.sqrt_nonneg _)
        linarith
    · rw [if_neg hB]
      simp only [hBad, Finset.mem_insert, Finset.mem_singleton, not_or] at hB
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hB
      by_cases hr : res ν
      · -- a resonant frequency away from the edges is deep
        have hdν : deep ν := by
          obtain ⟨hr1, hr2⟩ := hr
          have hfa : ⌊α⌋₊ < ν := (Nat.floor_lt hα).mpr hr1
          have hfb : ν ≤ ⌊β⌋₊ := Nat.le_floor hr2.le
          have h1 : ⌊α⌋₊ + 2 ≤ ν := by omega
          have h2 : ν + 1 ≤ ⌊β⌋₊ := by omega
          have h1' : ((⌊α⌋₊ : ℕ) : ℝ) + 2 ≤ ν := by exact_mod_cast h1
          have h2' : (ν : ℝ) + 1 ≤ ((⌊β⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
          exact ⟨by linarith, by linarith⟩
        rw [if_pos hdν]
        have hRn : R n = bDualTerm f f'' x ν := by simp only [hR]; rw [if_pos hr]
        rw [hRn, hImν]
        have := norm_integral_sub_bDualTerm_le_deep hf hf' hf'' hlam₂ hlo hhi h3 hδ
          (hx ν hr.1 hr.2).1 (hx ν hr.1 hr.2).2 hdν.1 hdν.2
        linarith
      · -- a non-resonant frequency away from the edges is far
        have hdν : ¬ deep ν := fun hd => hr ⟨by linarith [hd.1], by linarith [hd.2]⟩
        rw [if_neg hdν]
        have hRn : R n = 0 := by simp only [hR]; rw [if_neg hr]
        rw [hRn, sub_zero, hImν]
        have hfar : ∀ y ∈ Icc (A : ℝ) B, 1 ≤ |f' y - ν| := by
          intro y hy
          obtain ⟨hy1, hy2⟩ := hrange y hy
          simp only [hres, not_and_or, not_lt] at hr
          rcases hr with hr | hr
          · have hfa : ν ≤ ⌊α⌋₊ := Nat.le_floor hr
            have h1 : ν + 1 ≤ ⌊α⌋₊ := by omega
            have h1' : (ν : ℝ) + 1 ≤ ((⌊α⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
            rw [abs_of_nonneg (by linarith)]
            linarith
          · have hfb : ⌊β⌋₊ ≤ ν := Nat.floor_le_of_le hr
            have h2 : ⌊β⌋₊ + 2 ≤ ν := by omega
            have h2' : ((⌊β⌋₊ : ℕ) : ℝ) + 2 ≤ ν := by exact_mod_cast h2
            rw [abs_of_neg (by linarith)]
            linarith
        have := norm_integral_cexp_twoPi_le_half hab (hsub (ν : ℝ)) (hsub' (ν : ℝ)) hf''c hpos hfar
        linarith
  -- summing the per-frequency errors
  have hcount1 : ∑ n ∈ Finset.range K, (if n + 1 ∈ Bad then 4 / Real.sqrt lam₂ else 0)
      ≤ 4 / Real.sqrt lam₂ * Bad.card :=
    sum_range_ite_le_card (p := fun ν => ν ∈ Bad) hsq0 Bad (fun n h => h)
  have hcount2 := sum_range_ite_le_card (K := K) (p := deep) hS0
    (Finset.Icc (⌊α⌋₊ + 1) ⌊β⌋₊) (fun n hd => by
      rw [Finset.mem_Icc]
      have hd1 : α < ((n + 1 : ℕ) : ℝ) := by linarith [hd.1]
      have hd2 : ((n + 1 : ℕ) : ℝ) ≤ β := by linarith [hd.2]
      exact ⟨by have := (Nat.floor_lt hα).mpr hd1; omega, Nat.le_floor hd2⟩)
  have hcard1 : (Bad.card : ℝ) ≤ 4 := card_bad_le _ _
  have hcard2 := card_Icc_floor_le hα hαβ
  have hsumerr : ∑ n ∈ Finset.range K, ‖Im n - R n‖
      ≤ 16 / Real.sqrt lam₂ + (β - α + 1) * S + K / 2 := by
    refine (Finset.sum_le_sum herr).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have h1 : 4 / Real.sqrt lam₂ * (Bad.card : ℝ) ≤ 16 / Real.sqrt lam₂ :=
      calc _ ≤ 4 / Real.sqrt lam₂ * 4 := mul_le_mul_of_nonneg_left hcard1 hsq0
        _ = 16 / Real.sqrt lam₂ := by ring
    have h2 : S * ((Finset.Icc (⌊α⌋₊ + 1) ⌊β⌋₊).card : ℝ) ≤ (β - α + 1) * S :=
      calc _ ≤ S * (β - α + 1) := mul_le_mul_of_nonneg_left hcard2 hS0
        _ = (β - α + 1) * S := by ring
    linarith
  have hsumIp : ‖∑ n ∈ Finset.range K, Ip n‖ ≤ K / 2 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n _ => hIp_le n).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    linarith
  -- assemble
  rw [hmain]
  set Ssum := ∑ m ∈ Finset.Ioc A B, Complex.exp (((2 * Real.pi * f m : ℝ) : ℂ) * I) with hSsum
  have e : Ssum - ∑ n ∈ Finset.range K, R n
      = (Ssum - (I₀ + ∑ n ∈ Finset.range K, (Ip n + Im n))) + I₀
        + ∑ n ∈ Finset.range K, Ip n + ∑ n ∈ Finset.range K, (Im n - R n) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [e]
  have hIm_sum : ‖∑ n ∈ Finset.range K, (Im n - R n)‖ ≤ 16 / Real.sqrt lam₂ + (β - α + 1) * S
      + K / 2 := (norm_sum_le _ _).trans hsumerr
  have hsplit : ‖(Ssum - (I₀ + ∑ n ∈ Finset.range K, (Ip n + Im n))) + I₀
        + ∑ n ∈ Finset.range K, Ip n + ∑ n ∈ Finset.range K, (Im n - R n)‖
      ≤ ‖Ssum - (I₀ + ∑ n ∈ Finset.range K, (Ip n + Im n))‖ + ‖I₀‖
        + ‖∑ n ∈ Finset.range K, Ip n‖ + ‖∑ n ∈ Finset.range K, (Im n - R n)‖ := by
    refine (norm_add_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_add_le _ _
  have h19 : 3 / Real.sqrt lam₂ + 16 / Real.sqrt lam₂ = 19 / Real.sqrt lam₂ := by ring
  linarith

end

end RHTower
