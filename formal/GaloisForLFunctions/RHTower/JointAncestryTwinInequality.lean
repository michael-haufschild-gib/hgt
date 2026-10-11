import GaloisForLFunctions.RHTower.JointAncestryClusterIdentity

/-!
# Twins cannot rescue a phase-designed Euler product

Let `G(y) = Π_{p∈s} (1 − b_p e^{i y_p})⁻¹` with `0 ≤ b_p ≤ 1/10`.  In route JAS, `G` is the b-side
of a near-`1` zero's twisted Euler density on a prime shell, and the phase design `τ` (the same on
every prime) makes `G(τ)` negative real.  Averaging over a pair of members whose prime-phase
patterns differ by `x`, the extra terms are `G(τ + x)` and `G(τ − x)`.

**Theorem** (`jasTwin_sum_le`).  If `cos τ ≥ 9/10`, `sin τ ≥ 0` and `(Σ b_p) sin² τ ≤ 1/100`, then

`|G(τ + x)| + |G(τ − x)| ≤ 2 |G(τ)| · exp(−(1/16) Σ_p b_p (1 − cos x_p))`.

Consequently (`jasTwin_re_le`), when `G(τ)` is negative real, the pair-averaged value
`(u₁² + u₂²) Re G(τ) + u₁u₂ (Re G(τ+x) + Re G(τ−x))` is at most
`−|G(τ)| ((u₁ − u₂)² + 2u₁u₂ (1 − exp(−E/16)))` with `E = Σ b_p (1 − cos x_p)`.  So it is strictly
negative unless the two patterns agree modulo `2π`.

**Proof.**  With `q(y) = |1 − b e^{iy}|² = 1 + b² − 2b cos y`, the even part
`log(q(τ+x)q(τ−x)/q(τ)²)` is at least `b(1 − cos x)/2`, by the exact identity
`q(τ+x)q(τ−x) − q(τ)² = 4b(1 − cos x)((1+b²) cos τ − b(1 + cos x))`.  The odd part
`|log(q(τ+x)/q(τ−x))|` is at most `10 b sin τ |sin x|`.  Then `e^{−u/2} + e^{−v/2} =
2e^{−(u+v)/4} cosh((u−v)/4)`, `cosh y ≤ e^{y²/2}`, and Cauchy–Schwarz with `sin² ≤ 2(1 − cos)`
show that the odd part is dominated once `S sin² τ ≤ 1/100`.
-/

open Real

namespace RHTower

noncomputable section

/-- `q(b, y) = |1 − b e^{iy}|²`. -/
def jasTwinQ (b y : ℝ) : ℝ := 1 + b ^ 2 - 2 * b * Real.cos y

theorem jasTwinQ_ge {b : ℝ} (hb0 : 0 ≤ b) (y : ℝ) : (1 - b) ^ 2 ≤ jasTwinQ b y := by
  unfold jasTwinQ; nlinarith [Real.cos_le_one y]

theorem jasTwinQ_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (y : ℝ) : 0 < jasTwinQ b y :=
  lt_of_lt_of_le (by nlinarith) (jasTwinQ_ge hb0 y)

theorem normSq_one_sub_mul_exp_eq_jasTwinQ (b y : ℝ) :
    Complex.normSq (1 - (b : ℂ) * Complex.exp ((y : ℂ) * Complex.I)) = jasTwinQ b y := by
  rw [Complex.normSq_apply, jasTwinQ]
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq y]

theorem jasTwinQ_mul_sub (b τ x : ℝ) :
    jasTwinQ b (τ + x) * jasTwinQ b (τ - x) - jasTwinQ b τ ^ 2 =
      4 * b * (1 - Real.cos x) * ((1 + b ^ 2) * Real.cos τ - b * (1 + Real.cos x)) := by
  unfold jasTwinQ
  rw [Real.cos_add, Real.cos_sub]
  linear_combination (-4 * b ^ 2 * Real.sin x ^ 2) * Real.sin_sq_add_cos_sq τ +
    (-4 * b ^ 2 * (1 - Real.cos τ ^ 2)) * Real.sin_sq_add_cos_sq x

theorem jasTwinQ_add_sub_sub (b τ x : ℝ) :
    jasTwinQ b (τ + x) - jasTwinQ b (τ - x) = 4 * b * Real.sin τ * Real.sin x := by
  unfold jasTwinQ
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- The even part of the log-modulus. -/
theorem log_jasTwinQ_even_ge {b τ x : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 10)
    (hτ : 9 / 10 ≤ Real.cos τ) :
    b * (1 - Real.cos x) / 2 ≤
      Real.log (jasTwinQ b (τ + x) * jasTwinQ b (τ - x) / jasTwinQ b τ ^ 2) := by
  have hq0 : 0 < jasTwinQ b τ := jasTwinQ_pos hb0 (by linarith) τ
  have hq1 : jasTwinQ b τ ≤ 101 / 100 := by
    unfold jasTwinQ; nlinarith [mul_nonneg hb0 (show (0:ℝ) ≤ Real.cos τ by linarith)]
  have hcx1 := Real.cos_le_one x
  have hcxm := Real.neg_one_le_cos x
  obtain ⟨y, hy⟩ : ∃ y, y = b * (1 - Real.cos x) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; nlinarith
  have hy1 : y ≤ 1 := by rw [hy]; nlinarith
  have hbr : 7 / 10 ≤ (1 + b ^ 2) * Real.cos τ - b * (1 + Real.cos x) := by
    nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) (show (0:ℝ) ≤ Real.cos τ by linarith)]
  have hid := jasTwinQ_mul_sub b τ x
  have hnum : jasTwinQ b τ ^ 2 * (1 + y) ≤ jasTwinQ b (τ + x) * jasTwinQ b (τ - x) := by
    have h1 : jasTwinQ b τ ^ 2 * y ≤ 4 * b * (1 - Real.cos x) *
        ((1 + b ^ 2) * Real.cos τ - b * (1 + Real.cos x)) := by
      rw [hy]
      have hq2 : jasTwinQ b τ ^ 2 ≤ 4 * ((1 + b ^ 2) * Real.cos τ - b * (1 + Real.cos x)) := by
        nlinarith
      have hb1x : 0 ≤ b * (1 - Real.cos x) := by nlinarith
      nlinarith
    nlinarith
  have hratio : 1 + y ≤ jasTwinQ b (τ + x) * jasTwinQ b (τ - x) / jasTwinQ b τ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hlog : Real.log (1 + y) ≤
      Real.log (jasTwinQ b (τ + x) * jasTwinQ b (τ - x) / jasTwinQ b τ ^ 2) :=
    Real.log_le_log (by linarith) hratio
  have hlow : y / 2 ≤ Real.log (1 + y) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 1 + y by linarith)
    have : y / 2 ≤ 1 - (1 + y)⁻¹ := by
      rw [show 1 - (1 + y)⁻¹ = y / (1 + y) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  rw [← hy]
  linarith

/-- The odd part of the log-modulus. -/
theorem abs_log_jasTwinQ_odd_le {b τ x : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 10)
    (hs : 0 ≤ Real.sin τ) :
    |Real.log (jasTwinQ b (τ + x) / jasTwinQ b (τ - x))| ≤
      10 * b * Real.sin τ * |Real.sin x| := by
  have hqm : (81 / 100 : ℝ) ≤ jasTwinQ b (τ - x) := by
    have := jasTwinQ_ge hb0 (τ - x); nlinarith
  have hqm0 : 0 < jasTwinQ b (τ - x) := by linarith
  obtain ⟨z, hz⟩ : ∃ z, z = 4 * b * Real.sin τ * Real.sin x / jasTwinQ b (τ - x) := ⟨_, rfl⟩
  have hratio : jasTwinQ b (τ + x) / jasTwinQ b (τ - x) = 1 + z := by
    rw [hz]
    field_simp
    linarith [jasTwinQ_add_sub_sub b τ x]
  have hst1 := Real.sin_le_one τ
  have hsx : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hzabs : |z| ≤ 400 / 81 * b * Real.sin τ * |Real.sin x| := by
    rw [hz, abs_div, abs_of_pos hqm0, div_le_iff₀ hqm0, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num), abs_of_nonneg hb0, abs_of_nonneg hs]
    have : 0 ≤ b * Real.sin τ * |Real.sin x| := by positivity
    nlinarith
  have hzh : |z| ≤ 1 / 2 := by
    have : b * Real.sin τ * |Real.sin x| ≤ 1 / 10 := by
      have h1 : Real.sin τ * |Real.sin x| ≤ 1 := by
        calc Real.sin τ * |Real.sin x| ≤ 1 * 1 :=
              mul_le_mul hst1 hsx (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      nlinarith [mul_nonneg hs (abs_nonneg (Real.sin x))]
    nlinarith
  rw [hratio]
  have hz1 : 0 < 1 + z := by linarith [neg_abs_le z]
  have hup : Real.log (1 + z) ≤ |z| := by
    have := Real.log_le_sub_one_of_pos hz1; linarith [le_abs_self z]
  have hdown : -(2 * |z|) ≤ Real.log (1 + z) := by
    have h := Real.one_sub_inv_le_log_of_pos hz1
    have : -(2 * |z|) ≤ 1 - (1 + z)⁻¹ := by
      rw [show 1 - (1 + z)⁻¹ = z / (1 + z) by field_simp; ring, le_div_iff₀ hz1]
      nlinarith [neg_abs_le z, le_abs_self z, abs_nonneg z]
    linarith
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg z]

/-- Cauchy–Schwarz with `|sin| ` and the deficit. -/
theorem sq_sum_mul_abs_sin_le {α : Type*} (s : Finset α) {b x : α → ℝ} (hb : ∀ a ∈ s, 0 ≤ b a) :
    (∑ a ∈ s, b a * |Real.sin (x a)|) ^ 2 ≤
      2 * (∑ a ∈ s, b a) * ∑ a ∈ s, b a * (1 - Real.cos (x a)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => Real.sqrt (b a))
    (fun a => Real.sqrt (b a) * |Real.sin (x a)|)
  have h1 : ∀ a ∈ s, Real.sqrt (b a) * (Real.sqrt (b a) * |Real.sin (x a)|) =
      b a * |Real.sin (x a)| := fun a ha => by rw [← mul_assoc, Real.mul_self_sqrt (hb a ha)]
  have h2 : ∀ a ∈ s, Real.sqrt (b a) ^ 2 = b a := fun a ha => Real.sq_sqrt (hb a ha)
  have h3 : ∀ a ∈ s, (Real.sqrt (b a) * |Real.sin (x a)|) ^ 2 ≤
      2 * (b a * (1 - Real.cos (x a))) := fun a ha => by
    rw [mul_pow, h2 a ha, sq_abs]
    have hsc := Real.sin_sq_add_cos_sq (x a)
    have hs : Real.sin (x a) ^ 2 ≤ 2 * (1 - Real.cos (x a)) := by
      nlinarith [sq_nonneg (1 - Real.cos (x a))]
    calc b a * Real.sin (x a) ^ 2 ≤ b a * (2 * (1 - Real.cos (x a))) :=
          mul_le_mul_of_nonneg_left hs (hb a ha)
      _ = 2 * (b a * (1 - Real.cos (x a))) := by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at hcs
  calc (∑ a ∈ s, b a * |Real.sin (x a)|) ^ 2
      ≤ (∑ a ∈ s, b a) * ∑ a ∈ s, (Real.sqrt (b a) * |Real.sin (x a)|) ^ 2 := hcs
    _ ≤ (∑ a ∈ s, b a) * ∑ a ∈ s, 2 * (b a * (1 - Real.cos (x a))) := by
        gcongr with a ha
        · exact Finset.sum_nonneg hb
        · exact h3 a ha
    _ = 2 * (∑ a ∈ s, b a) * ∑ a ∈ s, b a * (1 - Real.cos (x a)) := by
        rw [← Finset.mul_sum]; ring

theorem inv_sqrt_eq_exp {q : ℝ} (hq : 0 < q) : (Real.sqrt q)⁻¹ = Real.exp (-(Real.log q / 2)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq, Real.exp_neg]
  congr 2; ring

/-- **Twin inequality.** -/
theorem jasTwin_sum_le {α : Type*} (s : Finset α) {b x : α → ℝ} (hb0 : ∀ p ∈ s, 0 ≤ b p)
    (hb : ∀ p ∈ s, b p ≤ 1 / 10) {τ : ℝ} (hc : 9 / 10 ≤ Real.cos τ) (hs : 0 ≤ Real.sin τ)
    (hS : (∑ p ∈ s, b p) * Real.sin τ ^ 2 ≤ 1 / 100) :
    ∏ p ∈ s, (Real.sqrt (jasTwinQ (b p) (τ + x p)))⁻¹ +
        ∏ p ∈ s, (Real.sqrt (jasTwinQ (b p) (τ - x p)))⁻¹ ≤
      2 * (∏ p ∈ s, (Real.sqrt (jasTwinQ (b p) τ))⁻¹) *
        Real.exp (-((∑ p ∈ s, b p * (1 - Real.cos (x p))) / 16)) := by
  have hpos : ∀ p ∈ s, ∀ y, 0 < jasTwinQ (b p) y := fun p hp y =>
    jasTwinQ_pos (hb0 p hp) (by linarith [hb p hp]) y
  have hprod : ∀ f : α → ℝ, (∀ p ∈ s, 0 < jasTwinQ (b p) (f p)) →
      ∏ p ∈ s, (Real.sqrt (jasTwinQ (b p) (f p)))⁻¹ =
        Real.exp (-((∑ p ∈ s, Real.log (jasTwinQ (b p) (f p))) / 2)) := by
    intro f hf
    rw [Finset.prod_congr rfl fun p hp => inv_sqrt_eq_exp (hf p hp), ← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib, Finset.sum_div]
  have e1 := hprod (fun p => τ + x p) fun p hp => hpos p hp _
  have e2 := hprod (fun p => τ - x p) fun p hp => hpos p hp _
  have e3 := hprod (fun _ => τ) fun p hp => hpos p hp _
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3]
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ p ∈ s, Real.log (jasTwinQ (b p) τ) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = ∑ p ∈ s, Real.log (jasTwinQ (b p) (τ + x p)) - A := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = ∑ p ∈ s, Real.log (jasTwinQ (b p) (τ - x p)) - A := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ p ∈ s, b p * (1 - Real.cos (x p)) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ p ∈ s, b p := ⟨_, rfl⟩
  rw [← hA, ← hE]
  rw [← hSdef] at hS
  have hE0 : 0 ≤ E := by
    rw [hE]; exact Finset.sum_nonneg fun p hp => mul_nonneg (hb0 p hp)
      (by linarith [Real.cos_le_one (x p)])
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg hb0
  -- the even part
  have huv : E / 2 ≤ u + v := by
    have : u + v = ∑ p ∈ s, Real.log (jasTwinQ (b p) (τ + x p) * jasTwinQ (b p) (τ - x p) /
        jasTwinQ (b p) τ ^ 2) := by
      rw [hu, hv, hA]
      rw [show (∑ p ∈ s, Real.log (jasTwinQ (b p) (τ + x p)) - ∑ p ∈ s, Real.log (jasTwinQ (b p) τ)) +
          (∑ p ∈ s, Real.log (jasTwinQ (b p) (τ - x p)) - ∑ p ∈ s, Real.log (jasTwinQ (b p) τ)) =
          ∑ p ∈ s, (Real.log (jasTwinQ (b p) (τ + x p)) + Real.log (jasTwinQ (b p) (τ - x p)) -
            2 * Real.log (jasTwinQ (b p) τ)) by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]; ring]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Real.log_div (by have := hpos p hp (τ + x p); have := hpos p hp (τ - x p); positivity)
        (by have := hpos p hp τ; positivity), Real.log_mul (hpos p hp _).ne' (hpos p hp _).ne',
        Real.log_pow]
      push_cast; ring
    rw [this, hE, Finset.sum_div]
    exact Finset.sum_le_sum fun p hp => log_jasTwinQ_even_ge (hb0 p hp) (hb p hp) hc
  -- the odd part
  have hmuv : |u - v| ≤ 10 * Real.sin τ * ∑ p ∈ s, b p * |Real.sin (x p)| := by
    have : u - v = ∑ p ∈ s, Real.log (jasTwinQ (b p) (τ + x p) / jasTwinQ (b p) (τ - x p)) := by
      rw [hu, hv, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Real.log_div (hpos p hp _).ne' (hpos p hp _).ne']
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have := abs_log_jasTwinQ_odd_le (x := x p) (hb0 p hp) (hb p hp) hs
    linarith
  have hcs := sq_sum_mul_abs_sin_le s (x := x) hb0
  rw [← hSdef, ← hE] at hcs
  have hsq : (u - v) ^ 2 ≤ 200 * (S * Real.sin τ ^ 2) * E := by
    have h1 : (u - v) ^ 2 ≤ (10 * Real.sin τ * ∑ p ∈ s, b p * |Real.sin (x p)|) ^ 2 := by
      rw [← sq_abs (u - v)]
      exact pow_le_pow_left₀ (abs_nonneg _) hmuv 2
    have h2 : (10 * Real.sin τ * ∑ p ∈ s, b p * |Real.sin (x p)|) ^ 2 =
        100 * Real.sin τ ^ 2 * (∑ p ∈ s, b p * |Real.sin (x p)|) ^ 2 := by ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 100 * Real.sin τ ^ 2 by positivity)
    nlinarith
  -- combine
  have hexp : Real.exp (-((A + u) / 2)) + Real.exp (-((A + v) / 2)) =
      Real.exp (-(A / 2)) * (2 * Real.exp (-((u + v) / 4)) * Real.cosh ((u - v) / 4)) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-((A + v) / 2)) =
        Real.exp (-(A / 2)) * Real.exp (-((u + v) / 4)) * Real.exp ((u - v) / 4) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-((A + u) / 2)) =
        Real.exp (-(A / 2)) * Real.exp (-((u + v) / 4)) * Real.exp (-((u - v) / 4)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [h1, h2]
    ring
  have hA1 : ∑ p ∈ s, Real.log (jasTwinQ (b p) (τ + x p)) = A + u := by rw [hu]; ring
  have hA2 : ∑ p ∈ s, Real.log (jasTwinQ (b p) (τ - x p)) = A + v := by rw [hv]; ring
  rw [hA1, hA2, hexp]
  have hcosh : Real.cosh ((u - v) / 4) ≤ Real.exp (((u - v) / 4) ^ 2 / 2) :=
    Real.cosh_le_exp_half_sq _
  have hfin : Real.exp (-((u + v) / 4)) * Real.cosh ((u - v) / 4) ≤ Real.exp (-(E / 16)) := by
    calc Real.exp (-((u + v) / 4)) * Real.cosh ((u - v) / 4)
        ≤ Real.exp (-((u + v) / 4)) * Real.exp (((u - v) / 4) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
      _ = Real.exp (-((u + v) / 4) + ((u - v) / 4) ^ 2 / 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(E / 16)) := by
          apply Real.exp_le_exp.mpr
          have : (u - v) ^ 2 ≤ 2 * E := by nlinarith
          nlinarith
  have hpA := Real.exp_pos (-(A / 2))
  nlinarith

/-- The phase-designed Euler product `G(y) = Π_{p∈s} (1 − b_p e^{i y_p})⁻¹`. -/
def jasTwinG {α : Type*} (s : Finset α) (b y : α → ℝ) : ℂ :=
  ∏ p ∈ s, (1 - (b p : ℂ) * Complex.exp ((y p : ℂ) * Complex.I))⁻¹

theorem norm_jasTwinG {α : Type*} (s : Finset α) (b y : α → ℝ) :
    ‖jasTwinG s b y‖ = ∏ p ∈ s, (Real.sqrt (jasTwinQ (b p) (y p)))⁻¹ := by
  unfold jasTwinG
  rw [norm_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [norm_inv, ← normSq_one_sub_mul_exp_eq_jasTwinQ, ← Complex.sq_norm, Real.sqrt_sq (norm_nonneg _)]

/-- **Twins cannot rescue.**  If the design makes `G(τ)` negative real, the pair-averaged value of
two members with pattern difference `x` is at most
`−|G(τ)| ((u₁ − u₂)² + 2u₁u₂ (1 − exp(−E/16)))`. -/
theorem jasTwin_re_le {α : Type*} (s : Finset α) {b x : α → ℝ} (hb0 : ∀ p ∈ s, 0 ≤ b p)
    (hb : ∀ p ∈ s, b p ≤ 1 / 10) {τ : ℝ} (hc : 9 / 10 ≤ Real.cos τ) (hs : 0 ≤ Real.sin τ)
    (hS : (∑ p ∈ s, b p) * Real.sin τ ^ 2 ≤ 1 / 100) {u₁ u₂ : ℝ} (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂)
    (hneg : (jasTwinG s b fun _ => τ).re = -‖jasTwinG s b fun _ => τ‖) :
    (u₁ ^ 2 + u₂ ^ 2) * (jasTwinG s b fun _ => τ).re +
        u₁ * u₂ * ((jasTwinG s b fun p => τ + x p).re + (jasTwinG s b fun p => τ - x p).re) ≤
      -‖jasTwinG s b fun _ => τ‖ * ((u₁ - u₂) ^ 2 +
        2 * u₁ * u₂ * (1 - Real.exp (-((∑ p ∈ s, b p * (1 - Real.cos (x p))) / 16)))) := by
  have hsum := jasTwin_sum_le s (x := x) hb0 hb hc hs hS
  rw [← norm_jasTwinG s b (fun p => τ + x p), ← norm_jasTwinG s b (fun p => τ - x p),
    ← norm_jasTwinG s b (fun _ => τ)] at hsum
  have h1 := Complex.re_le_norm (jasTwinG s b fun p => τ + x p)
  have h2 := Complex.re_le_norm (jasTwinG s b fun p => τ - x p)
  have hu := mul_nonneg hu₁ hu₂
  have h3 : u₁ * u₂ * ((jasTwinG s b fun p => τ + x p).re + (jasTwinG s b fun p => τ - x p).re) ≤
      u₁ * u₂ * (2 * ‖jasTwinG s b fun _ => τ‖ *
        Real.exp (-((∑ p ∈ s, b p * (1 - Real.cos (x p))) / 16))) :=
    mul_le_mul_of_nonneg_left (by linarith) hu
  rw [hneg]
  nlinarith

end

end RHTower
