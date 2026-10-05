import GaloisForLFunctions.RHTower.WeilIntegerMassAtomicRigidity
import GaloisForLFunctions.RHTower.MaassZetaSquaredConverse
import GaloisForLFunctions.HTGeometry.GammaReciprocalExpBound

/-!
# A completed Dirichlet series of finite order has order one

Let `E` be entire of finite order, `‖E(s)‖ ≤ C exp(‖s‖^ρ)`, with `E(1 − s) = ε E(s)`, `|ε| = 1`,
and `E(s) = (s(s − 1)Γ_ℝ(s))^k Σ g(n) n^{−s}` on `Re s ≥ 2`, the series converging absolutely at
`s = 2`.  Then `E` has the order-one envelope

`‖E(s)‖ ≤ exp(C' (1 + ‖s‖) log(2 + ‖s‖))`  (`orderOneEnvelope_of_finiteOrder`).

**Proof.**
* On `Re s = 2`, `s(s − 1)Γ_ℝ(s)` is bounded (vertical decay of `Γ`), and so is the Dirichlet
  series; by the functional equation `E` is bounded on `Re s = −1` too.  Finite order is far
  below the Phragmén–Lindelöf threshold, so `E` is bounded on `−1 ≤ Re s ≤ 2`.
* On `Re s ≥ 2`, `‖Γ(s/2)‖ ≤ Γ(Re s/2) ≤ (Re s/2)^{Re s/2}` (`Γ ≤ 1` on `[1, 2]` by convexity,
  then `Γ(x) = (x − 1)Γ(x − 1)`); the functional equation covers `Re s ≤ −1`.
-/

open Complex Filter Topology Set Asymptotics

noncomputable section

namespace RHTower.CompletionGrowth

/-! ## The real Gamma function -/

/-- `Γ ≤ 1` on `[1, 2]`, by convexity and `Γ(1) = Γ(2) = 1`. -/
theorem real_Gamma_le_one {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have hc := Real.convexOn_Gamma.2 (by norm_num : (1 : ℝ) ∈ Ioi 0)
    (by norm_num : (2 : ℝ) ∈ Ioi 0) (show (0 : ℝ) ≤ 2 - x by linarith)
    (show (0 : ℝ) ≤ x - 1 by linarith) (by ring)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at hc
  rw [show (2 - x) * 1 + (x - 1) * 2 = x by ring] at hc
  linarith

theorem real_Gamma_le_rpow_self_aux :
    ∀ n : ℕ, ∀ x : ℝ, 1 ≤ x → x ≤ n + 2 → Real.Gamma x ≤ x ^ x
  | 0, x, h1, h2 =>
    (real_Gamma_le_one h1 (by simpa using h2)).trans (Real.one_le_rpow h1 (by linarith))
  | n + 1, x, h1, h2 => by
    by_cases hx : x ≤ 2
    · exact (real_Gamma_le_one h1 hx).trans (Real.one_le_rpow h1 (by linarith))
    · rw [not_le] at hx
      have ih := real_Gamma_le_rpow_self_aux n (x - 1) (by linarith) (by push_cast at h2; linarith)
      have hx1 : x - 1 ≠ 0 := by linarith
      have hG : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
        have := Real.Gamma_add_one hx1
        rwa [sub_add_cancel] at this
      calc Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := hG
        _ ≤ (x - 1) * (x - 1) ^ (x - 1) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (x - 1) ^ x := by
            rw [mul_comm, ← Real.rpow_add_one hx1, sub_add_cancel]
        _ ≤ x ^ x := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)

/-- `Γ(x) ≤ x^x` for `x ≥ 1`. -/
theorem real_Gamma_le_rpow_self {x : ℝ} (hx : 1 ≤ x) : Real.Gamma x ≤ x ^ x :=
  real_Gamma_le_rpow_self_aux ⌈x⌉₊ x hx (by linarith [Nat.le_ceil x])

/-- `‖Γ_ℝ(s)‖ ≤ exp(‖s‖ log(2 + ‖s‖))` on `Re s ≥ 2`. -/
theorem norm_Gammaℝ_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.exp (‖s‖ * Real.log (2 + ‖s‖)) := by
  have hσ : 1 ≤ s.re / 2 := by linarith
  have hre : (s / 2).re = s.re / 2 := by simp
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hpi : Real.pi ^ (-s / 2).re ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    simp; linarith
  have hG : ‖Complex.Gamma (s / 2)‖ ≤ (s.re / 2) ^ (s.re / 2) := by
    refine (GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re (by rw [hre]; linarith)).trans ?_
    rw [hre]
    exact real_Gamma_le_rpow_self hσ
  have hpow : (s.re / 2) ^ (s.re / 2) ≤ Real.exp (‖s‖ * Real.log (2 + ‖s‖)) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp, mul_comm]
    have hsn : s.re / 2 ≤ ‖s‖ := by
      have := Complex.re_le_norm s
      linarith
    have hl0 : 0 ≤ Real.log (s.re / 2) := Real.log_nonneg hσ
    have hl : Real.log (s.re / 2) ≤ Real.log (2 + ‖s‖) :=
      Real.log_le_log (by linarith) (by linarith [norm_nonneg s])
    exact mul_le_mul hsn hl hl0 (norm_nonneg s)
  calc Real.pi ^ (-s / 2).re * ‖Complex.Gamma (s / 2)‖
      ≤ 1 * (s.re / 2) ^ (s.re / 2) :=
        mul_le_mul hpi hG (norm_nonneg _) zero_le_one
    _ ≤ Real.exp (‖s‖ * Real.log (2 + ‖s‖)) := by rw [one_mul]; exact hpow

/-- `s(s − 1)Γ_ℝ(s)` is bounded on `Re s = 2`. -/
theorem exists_bound_completionFactor_two :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ,
      ‖(2 + τ * I) * (2 + τ * I - 1) * Complex.Gammaℝ (2 + τ * I)‖ ≤ B := by
  obtain ⟨Cγ, Nγ, hCγ, hγ⟩ := IntegerMassRigidity.exists_bound_Gammaℝ_two
  set F : ℝ := (4 / Real.pi) ^ (Nγ + 2) * (Nγ + 2).factorial * Real.exp Real.pi with hF
  refine ⟨Cγ * F, by positivity, fun τ => ?_⟩
  have hτ := abs_nonneg τ
  have h1 : ‖(2 + (τ : ℂ) * I)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I)‖ ≤ ‖(2 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have h2 : ‖(2 + (τ : ℂ) * I - 1)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I - 1)‖ = ‖(1 : ℂ) + (τ : ℂ) * I‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have hpe : (|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4)) ≤ F := by
    have h := MaassZetaSquaredConverse.pow_mul_exp_le (by positivity : (0 : ℝ) ≤ |τ| + 4) (Nγ + 2)
    have he : Real.exp (-(Real.pi * |τ| / 4)) =
        Real.exp (-(Real.pi * (|τ| + 4) / 4)) * Real.exp Real.pi := by
      rw [← Real.exp_add]; ring_nf
    rw [he, hF, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  rw [norm_mul, norm_mul]
  calc ‖(2 + (τ : ℂ) * I)‖ * ‖(2 + (τ : ℂ) * I - 1)‖ * ‖Complex.Gammaℝ (2 + τ * I)‖
      ≤ (|τ| + 4) * (|τ| + 4) * (Cγ * ((|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)))) := by
        gcongr
        exact hγ τ
    _ = Cγ * ((|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4))) := by ring
    _ ≤ Cγ * F := mul_le_mul_of_nonneg_left hpe hCγ

/-! ## Absorbing constants into the order-one envelope -/

theorem le_exp_envelope {A M : ℝ} (hM : 0 ≤ M) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      A * (1 + r) ^ N * Real.exp (M * r * Real.log (2 + r)) ≤
        Real.exp (C * (1 + r) * Real.log (2 + r)) := by
  set A' : ℝ := max A 1 with hA'
  have hA1 : 1 ≤ A' := le_max_right _ _
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a : ℝ := Real.log A' / Real.log 2 with ha
  have ha0 : 0 ≤ a := div_nonneg (Real.log_nonneg hA1) hl2.le
  refine ⟨a + N + M, by positivity, fun r hr => ?_⟩
  have hL : Real.log 2 ≤ Real.log (2 + r) := Real.log_le_log two_pos (by linarith)
  have hL0 : 0 ≤ Real.log (2 + r) := hl2.le.trans hL
  have hX : Real.log 2 ≤ (1 + r) * Real.log (2 + r) := by nlinarith
  have hA : A ≤ Real.exp (a * (1 + r) * Real.log (2 + r)) := by
    refine (le_max_left A 1).trans ?_
    rw [← hA', ← Real.exp_log (by linarith : (0 : ℝ) < A'), Real.exp_le_exp]
    have : Real.log A' = a * Real.log 2 := by rw [ha]; field_simp
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left hX ha0
  have hP : (1 + r) ^ N ≤ Real.exp (N * (1 + r) * Real.log (2 + r)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (1 + r) ^ N), Real.exp_le_exp, Real.log_pow,
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
    have h1 : Real.log (1 + r) ≤ Real.log (2 + r) := Real.log_le_log (by linarith) (by linarith)
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + r by linarith)]
  have hE : Real.exp (M * r * Real.log (2 + r)) ≤ Real.exp (M * (1 + r) * Real.log (2 + r)) := by
    rw [Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left (show r ≤ 1 + r by linarith) hM
    exact mul_le_mul_of_nonneg_right this hL0
  have hA0 : 0 ≤ Real.exp (a * (1 + r) * Real.log (2 + r)) := (Real.exp_pos _).le
  calc A * (1 + r) ^ N * Real.exp (M * r * Real.log (2 + r))
      ≤ Real.exp (a * (1 + r) * Real.log (2 + r)) * Real.exp (N * (1 + r) * Real.log (2 + r)) *
          Real.exp (M * (1 + r) * Real.log (2 + r)) := by
        rcases le_or_gt 0 A with hA0' | hAneg
        · gcongr
        · have : A * (1 + r) ^ N * Real.exp (M * r * Real.log (2 + r)) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hAneg.le (by positivity))
              (Real.exp_pos _).le
          exact this.trans (by positivity)
    _ = Real.exp ((a + N + M) * (1 + r) * Real.log (2 + r)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf

/-! ## Phragmén–Lindelöf on `−1 ≤ Re s ≤ 2` -/

/-- Finite order is far below the strip Phragmén–Lindelöf threshold. -/
theorem isBigO_strip_of_finiteOrder {E : ℂ → ℂ} {ρ C₀ : ℝ}
    (hfin : ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ)) :
    ∃ c < Real.pi / (2 - (-1)), ∃ B,
      E =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1) 2)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  set c : ℝ := Real.pi / 6 with hc
  have hc0 : 0 < c := by positivity
  set n : ℕ := ⌈ρ⌉₊ with hn
  set B : ℝ := (2 / c) ^ n * n.factorial * Real.exp c with hB
  refine ⟨c, by rw [hc]; linarith [Real.pi_pos], B, ?_⟩
  refine IsBigO.of_bound C₀ ?_
  have him : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1) 2),
      1 ≤ |z.im| := by
    refine Eventually.filter_mono inf_le_left ?_
    exact (eventually_ge_atTop (1 : ℝ)).comap _
  have hre : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (-1) 2),
      z.re ∈ Ioo (-1 : ℝ) 2 :=
    Eventually.filter_mono inf_le_right (eventually_principal.mpr fun z hz => hz)
  filter_upwards [him, hre] with z hz hzre
  set t := |z.im| with ht
  have hz1 : 1 ≤ ‖z‖ := hz.trans (Complex.abs_im_le_norm z)
  have hz2 : ‖z‖ ≤ 2 + t := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 + t := by
          have : |z.re| ≤ 2 := abs_le.mpr ⟨by linarith [hzre.1], hzre.2.le⟩
          linarith
  have hpow : ‖z‖ ^ ρ ≤ ‖z‖ ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (Nat.le_ceil ρ)
  have hpow2 : ‖z‖ ^ n ≤ B * Real.exp (c * t) := by
    have h := Real.pow_div_factorial_le_exp (c / 2 * (2 + t)) (by positivity) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hf] at h
    have e1 : (2 + t) ^ n = (2 / c) ^ n * (c / 2 * (2 + t)) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 : Real.exp (c / 2 * (2 + t)) ≤ Real.exp c * Real.exp (c * t) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith [abs_nonneg z.im]
    calc ‖z‖ ^ n ≤ (2 + t) ^ n := pow_le_pow_left₀ (norm_nonneg _) hz2 n
      _ = (2 / c) ^ n * (c / 2 * (2 + t)) ^ n := e1
      _ ≤ (2 / c) ^ n * (Real.exp (c / 2 * (2 + t)) * n.factorial) := by gcongr
      _ ≤ (2 / c) ^ n * ((Real.exp c * Real.exp (c * t)) * n.factorial) := by gcongr
      _ = B * Real.exp (c * t) := by rw [hB]; ring
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hfin z).trans ?_
  have hC0 : 0 ≤ C₀ := by
    have := (norm_nonneg (E z)).trans (hfin z)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  gcongr
  exact hpow.trans hpow2

/-! ## The envelope -/

theorem norm_LSeries_le_of_two_le {g : ℕ → ℂ} (hg : LSeriesSummable g 2) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖LSeries g s‖ ≤ ∑' n, ‖LSeries.term g 2 n‖ := by
  have hs' : LSeriesSummable g s := hg.of_re_le_re (by simpa using hs)
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hs'.norm).trans ?_
  refine hs'.norm.tsum_le_tsum (fun n => ?_) hg.norm
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn,
      show ((2 : ℂ)).re = 2 by norm_num]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs)

/-- **A completed Dirichlet series bounded on `−1 ≤ Re s ≤ 2` has the order-one envelope.** -/
theorem orderOneEnvelope_of_strip_bound {E : ℂ → ℂ} {ε : ℂ} (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s) {k : ℕ} {g : ℕ → ℂ} (hg : LSeriesSummable g 2)
    (hcomp : ∀ s : ℂ, 2 ≤ s.re → E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s)
    {B : ℝ} (hstrip : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖E z‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  set S : ℝ := ∑' n, ‖LSeries.term g 2 n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have hLb : ∀ s : ℂ, 2 ≤ s.re → ‖LSeries g s‖ ≤ S := fun s hs => norm_LSeries_le_of_two_le hg hs
  have hflip : ∀ s, ‖E s‖ = ‖E (1 - s)‖ := by
    intro s
    have := hsym (1 - s)
    rw [sub_sub_cancel] at this
    rw [this, norm_mul, hε, one_mul]
  -- the right half-plane
  obtain ⟨C₁, hC₁0, hC₁⟩ := le_exp_envelope (A := S) (M := k) (Nat.cast_nonneg k) (2 * k)
  have hright : ∀ s : ℂ, 2 ≤ s.re →
      ‖E s‖ ≤ Real.exp (C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro s hs
    refine le_trans ?_ (hC₁ ‖s‖ (norm_nonneg s))
    rw [hcomp s hs, norm_mul, norm_pow, norm_mul, norm_mul]
    have h1 : ‖s‖ ≤ 1 + ‖s‖ := by linarith
    have h2 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by simp; ring
    have hG := norm_Gammaℝ_le hs
    calc (‖s‖ * ‖s - 1‖ * ‖Complex.Gammaℝ s‖) ^ k * ‖LSeries g s‖
        ≤ ((1 + ‖s‖) * (1 + ‖s‖) * Real.exp (‖s‖ * Real.log (2 + ‖s‖))) ^ k * S := by
          gcongr
          exact hLb s hs
      _ = S * (1 + ‖s‖) ^ (2 * k) * Real.exp (k * ‖s‖ * Real.log (2 + ‖s‖)) := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul, two_mul, pow_add]
          ring_nf
  -- the strip bound in envelope form
  obtain ⟨C₂, hC₂0, hC₂⟩ := le_exp_envelope (A := B) (M := 0) le_rfl 0
  refine ⟨4 * C₁ + C₂, by positivity, fun s => ?_⟩
  have hmono : ∀ C' : ℝ, C' ≤ 4 * C₁ + C₂ → 0 ≤ C' →
      Real.exp (C' * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
        Real.exp ((4 * C₁ + C₂) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro C' hC' _
    rw [Real.exp_le_exp]
    have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
    have : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := mul_nonneg (by positivity) hL0
    nlinarith
  rcases le_or_gt 2 s.re with h2 | h2
  · exact (hright s h2).trans (hmono C₁ (by linarith) hC₁0)
  rcases le_or_gt (-1) s.re with h1 | h1
  · have := hC₂ ‖s‖ (norm_nonneg s)
    simp only [pow_zero, mul_one, zero_mul, Real.exp_zero] at this
    exact ((hstrip s h1 h2.le).trans this).trans (hmono C₂ (by linarith) hC₂0)
  · rw [hflip]
    have hre : 2 ≤ (1 - s).re := by simp; linarith
    refine (hright (1 - s) hre).trans ?_
    have hn : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by simp
    refine le_trans ?_ (hmono (4 * C₁) (by linarith) (by positivity))
    rw [Real.exp_le_exp]
    have hx := norm_nonneg s
    have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
    have hl : Real.log (2 + ‖1 - s‖) ≤ 2 * Real.log (2 + ‖s‖) := by
      rw [← Real.log_rpow (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      norm_num
      nlinarith
    have hl0 : 0 ≤ Real.log (2 + ‖1 - s‖) := Real.log_nonneg (by linarith [norm_nonneg (1 - s)])
    calc C₁ * (1 + ‖1 - s‖) * Real.log (2 + ‖1 - s‖)
        ≤ C₁ * (2 * (1 + ‖s‖)) * (2 * Real.log (2 + ‖s‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₁0) hl hl0 (by positivity)
      _ = 4 * C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖) := by ring


/-- **A completed Dirichlet series of finite order has the order-one envelope.** -/
theorem orderOneEnvelope_of_finiteOrder {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hfin : ∃ ρ C₀ : ℝ, ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ)) {ε : ℂ} (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s) {k : ℕ} {g : ℕ → ℂ} (hg : LSeriesSummable g 2)
    (hcomp : ∀ s : ℂ, 2 ≤ s.re → E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨ρ, C₀, hfin⟩ := hfin
  have hflip : ∀ s, ‖E s‖ = ‖E (1 - s)‖ := by
    intro s
    have := hsym (1 - s)
    rw [sub_sub_cancel] at this
    rw [this, norm_mul, hε, one_mul]
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_bound_completionFactor_two
  set B : ℝ := B₁ ^ k * ∑' n, ‖LSeries.term g 2 n‖ with hB
  have hline : ∀ z : ℂ, z.re = 2 → ‖E z‖ ≤ B := by
    intro z hz
    have hz' : z = 2 + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hz]
    rw [hcomp z hz.ge, norm_mul, norm_pow]
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
      (norm_LSeries_le_of_two_le hg hz.ge) (norm_nonneg _) (by positivity)
    rw [hz']
    exact hB₁ z.im
  refine orderOneEnvelope_of_strip_bound hε hsym hg hcomp (B := B) fun z h1 h2 => ?_
  refine PhragmenLindelof.vertical_strip hE.diffContOnCl (isBigO_strip_of_finiteOrder hfin)
    (fun w hw => ?_) hline h1 h2
  rw [hflip]
  exact hline (1 - w) (by simp [hw]; norm_num)

/-- The order-one envelope is a finite-order bound. -/
theorem finiteOrder_of_orderOne {E : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hE : ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) :
    ∃ ρ C₀ : ℝ, ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ) := by
  refine ⟨3, Real.exp (4 * C + 8 * C ^ 3), fun s => (hE s).trans ?_⟩
  rw [← Real.exp_add, Real.exp_le_exp]
  set r := ‖s‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg s
  have hlog : Real.log (2 + r) ≤ 1 + r := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + r by positivity)
    linarith
  have hr3 : r ^ (3 : ℝ) = r ^ 3 := by exact_mod_cast Real.rpow_natCast r 3
  rw [hr3]
  have h1 : C * (1 + r) * Real.log (2 + r) ≤ C * (1 + r) * (1 + r) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : 2 * C * r ^ 2 ≤ r ^ 3 + 8 * C ^ 3 := by
    rcases le_or_gt (2 * C) r with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg r), pow_nonneg hC 3]
    · have hsq : r ^ 2 ≤ (2 * C) ^ 2 := pow_le_pow_left₀ hr0 h.le 2
      nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * C),
        pow_nonneg hr0 3]
  nlinarith [sq_nonneg (1 - r)]

end RHTower.CompletionGrowth
