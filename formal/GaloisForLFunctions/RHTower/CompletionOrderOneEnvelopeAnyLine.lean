import GaloisForLFunctions.RHTower.CompletionOrderOneEnvelope

/-!
# The order-one envelope for any abscissa of absolute convergence

`CompletionGrowth.orderOneEnvelope_of_finiteOrder` assumes that the Dirichlet series converges
absolutely at `s = 2`.  Here only absolute convergence on `Re s > σ₀` is assumed
(`orderOneEnvelope_of_finiteOrder_abscissa`): the argument runs on the line `Re s = 2m` with
`2m > σ₀` and on the strip `1 − 2m ≤ Re s ≤ 2m`.

* `exists_bound_Gammaℝ_even`: `|Γ_ℝ(2m + iτ)| ≤ C (|τ| + 4)^N e^{−π|τ|/4}`, by
  `Γ_ℝ(s + 2) = Γ_ℝ(s) s/(2π)` from the line `Re s = 2`.
* `isBigO_strip_of_finiteOrder_even`: finite order is below the Phragmén–Lindelöf threshold of the
  strip of width `4m − 1`.
-/

open Complex Filter Topology Set Asymptotics

noncomputable section

namespace RHTower.CompletionGrowth

/-- Vertical decay of `Γ_ℝ` on the line `Re s = 2m`. -/
theorem exists_bound_Gammaℝ_even {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ τ : ℝ,
      ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ ≤
        C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
  induction m, hm using Nat.le_induction with
  | base =>
    obtain ⟨C, N, hC, h⟩ := IntegerMassRigidity.exists_bound_Gammaℝ_two
    exact ⟨C, N, hC, fun τ => by simpa using h τ⟩
  | succ m hm ih =>
    obtain ⟨C, N, hC, h⟩ := ih
    refine ⟨C * (2 * m) / (2 * Real.pi), N + 1, by positivity, fun τ => ?_⟩
    have hs0 : ((2 * m : ℕ) : ℂ) + τ * I ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      omega
    have e : ((2 * (m + 1) : ℕ) : ℂ) + τ * I = (((2 * m : ℕ) : ℂ) + τ * I) + 2 := by
      push_cast; ring
    rw [e, Complex.Gammaℝ_add_two hs0, norm_div, norm_div, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn : ‖((2 * m : ℕ) : ℂ) + τ * I‖ ≤ (2 * m) * (|τ| + 4) := by
      calc ‖((2 * m : ℕ) : ℂ) + τ * I‖ ≤ ‖((2 * m : ℕ) : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
        _ = 2 * m + |τ| := by simp
        _ ≤ (2 * m) * (|τ| + 4) := by nlinarith [abs_nonneg τ]
    have hpi : 0 < 2 * Real.pi := by positivity
    calc ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ * ‖((2 * m : ℕ) : ℂ) + τ * I‖ / 2 / Real.pi
        = ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ * ‖((2 * m : ℕ) : ℂ) + τ * I‖ /
            (2 * Real.pi) := by ring
      _ ≤ (C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4)))) * ((2 * m) * (|τ| + 4)) /
            (2 * Real.pi) := by gcongr; exact h τ
      _ = C * (2 * m) / (2 * Real.pi) *
            ((|τ| + 4) ^ (N + 1) * Real.exp (-(Real.pi * |τ| / 4))) := by ring

/-- `s(s − 1)Γ_ℝ(s)` is bounded on the line `Re s = 2m`. -/
theorem exists_bound_completionFactor_even {m : ℕ} (hm : 1 ≤ m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ,
      ‖(((2 * m : ℕ) : ℂ) + τ * I) * (((2 * m : ℕ) : ℂ) + τ * I - 1) *
        Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ ≤ B := by
  obtain ⟨Cγ, Nγ, hCγ, hγ⟩ := exists_bound_Gammaℝ_even hm
  set F : ℝ := (4 / Real.pi) ^ (Nγ + 2) * (Nγ + 2).factorial * Real.exp Real.pi with hF
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨(2 * m) * (2 * m) * Cγ * F, by positivity, fun τ => ?_⟩
  have hτ := abs_nonneg τ
  have h1 : ‖((2 * m : ℕ) : ℂ) + τ * I‖ ≤ (2 * m) * (|τ| + 4) := by
    calc ‖((2 * m : ℕ) : ℂ) + τ * I‖ ≤ ‖((2 * m : ℕ) : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 * m + |τ| := by simp
      _ ≤ (2 * m) * (|τ| + 4) := by nlinarith
  have h2 : ‖((2 * m : ℕ) : ℂ) + τ * I - 1‖ ≤ (2 * m) * (|τ| + 4) := by
    have e : ((2 * m : ℕ) : ℂ) + τ * I - 1 = ((2 * m - 1 : ℝ) : ℂ) + τ * I := by push_cast; ring
    rw [e]
    calc ‖((2 * m - 1 : ℝ) : ℂ) + τ * I‖ ≤ ‖((2 * m - 1 : ℝ) : ℂ)‖ + ‖(τ : ℂ) * I‖ :=
          norm_add_le _ _
      _ = (2 * m - 1) + |τ| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; simp
      _ ≤ (2 * m) * (|τ| + 4) := by nlinarith
  have hpe : (|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4)) ≤ F := by
    have h := MaassZetaSquaredConverse.pow_mul_exp_le (by positivity : (0 : ℝ) ≤ |τ| + 4) (Nγ + 2)
    have he : Real.exp (-(Real.pi * |τ| / 4)) =
        Real.exp (-(Real.pi * (|τ| + 4) / 4)) * Real.exp Real.pi := by
      rw [← Real.exp_add]; ring_nf
    rw [he, hF, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  rw [norm_mul, norm_mul]
  calc ‖((2 * m : ℕ) : ℂ) + τ * I‖ * ‖((2 * m : ℕ) : ℂ) + τ * I - 1‖ *
        ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖
      ≤ ((2 * m) * (|τ| + 4)) * ((2 * m) * (|τ| + 4)) *
          (Cγ * ((|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)))) := by
        gcongr
        exact hγ τ
    _ = (2 * m) * (2 * m) * Cγ * ((|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4))) := by
        ring
    _ ≤ (2 * m) * (2 * m) * Cγ * F := mul_le_mul_of_nonneg_left hpe (by positivity)

/-- Finite order is below the Phragmén–Lindelöf threshold of the strip `1 − N < Re s < N`. -/
theorem isBigO_strip_of_finiteOrder_at {E : ℂ → ℂ} {ρ C₀ : ℝ}
    (hfin : ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ)) {N : ℝ} (hN : 1 ≤ N) :
    ∃ c < Real.pi / (N - (1 - N)), ∃ B,
      E =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
  have hw : 0 < N - (1 - N) := by linarith
  set c : ℝ := Real.pi / (2 * (N - (1 - N))) with hc
  have hc0 : 0 < c := by positivity
  set n : ℕ := ⌈ρ⌉₊ with hn
  set B : ℝ := (2 * N / c) ^ n * n.factorial * Real.exp (N * c) with hB
  refine ⟨c, ?_, B, ?_⟩
  · rw [hc, div_lt_div_iff₀ (by positivity) hw]
    nlinarith [Real.pi_pos]
  refine IsBigO.of_bound C₀ ?_
  have him : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N),
      1 ≤ |z.im| := by
    refine Eventually.filter_mono inf_le_left ?_
    exact (eventually_ge_atTop (1 : ℝ)).comap _
  have hre : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (1 - N) N),
      z.re ∈ Ioo (1 - N) N :=
    Eventually.filter_mono inf_le_right (eventually_principal.mpr fun z hz => hz)
  filter_upwards [him, hre] with z hz hzre
  set t := |z.im| with ht
  have hz1 : 1 ≤ ‖z‖ := hz.trans (Complex.abs_im_le_norm z)
  have hz2 : ‖z‖ ≤ N + t := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ N + t := by
          have : |z.re| ≤ N := abs_le.mpr ⟨by linarith [hzre.1], hzre.2.le⟩
          linarith
  have hpow : ‖z‖ ^ ρ ≤ ‖z‖ ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (Nat.le_ceil ρ)
  have hpow2 : ‖z‖ ^ n ≤ B * Real.exp (c * t) := by
    have h := Real.pow_div_factorial_le_exp (c / (2 * N) * (N + t)) (by positivity) n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_le_iff₀ hf] at h
    have e1 : (N + t) ^ n = (2 * N / c) ^ n * (c / (2 * N) * (N + t)) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 : Real.exp (c / (2 * N) * (N + t)) ≤ Real.exp (N * c) * Real.exp (c * t) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hN0 : 0 < N := by linarith
      have e : c / (2 * N) * (N + t) = c / 2 + c * t / (2 * N) := by field_simp
      have ht0 : 0 ≤ t := abs_nonneg _
      have h1 : c / 2 ≤ N * c := by nlinarith
      have h2 : c * t / (2 * N) ≤ c * t := div_le_self (by positivity) (by linarith)
      linarith
    calc ‖z‖ ^ n ≤ (N + t) ^ n := pow_le_pow_left₀ (norm_nonneg _) hz2 n
      _ = (2 * N / c) ^ n * (c / (2 * N) * (N + t)) ^ n := e1
      _ ≤ (2 * N / c) ^ n * (Real.exp (c / (2 * N) * (N + t)) * n.factorial) := by gcongr
      _ ≤ (2 * N / c) ^ n * ((Real.exp (N * c) * Real.exp (c * t)) * n.factorial) := by gcongr
      _ = B * Real.exp (c * t) := by rw [hB]; ring
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hfin z).trans ?_
  have hC0 : 0 ≤ C₀ := by
    have := (norm_nonneg (E z)).trans (hfin z)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  gcongr
  exact hpow.trans hpow2

theorem norm_LSeries_le_of_le {g : ℕ → ℂ} {N : ℝ} (hg : LSeriesSummable g N) {s : ℂ}
    (hs : N ≤ s.re) : ‖LSeries g s‖ ≤ ∑' n, ‖LSeries.term g N n‖ := by
  have hs' : LSeriesSummable g s := hg.of_re_le_re (by simpa using hs)
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hs'.norm).trans ?_
  refine hs'.norm.tsum_le_tsum (fun n => ?_) hg.norm
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, Complex.ofReal_re]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hs)

/-- **A completed Dirichlet series bounded on the strip `1 − N ≤ Re s ≤ N` has the order-one
envelope.** -/
theorem orderOneEnvelope_of_strip_bound_at {E : ℂ → ℂ} {ε : ℂ} (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s) {k : ℕ} {g : ℕ → ℂ} {N : ℝ} (hN : 2 ≤ N)
    (hg : LSeriesSummable g N)
    (hcomp : ∀ s : ℂ, N ≤ s.re → E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s)
    {B : ℝ} (hstrip : ∀ z : ℂ, 1 - N ≤ z.re → z.re ≤ N → ‖E z‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  set S : ℝ := ∑' n, ‖LSeries.term g N n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have hLb : ∀ s : ℂ, N ≤ s.re → ‖LSeries g s‖ ≤ S := fun s hs => norm_LSeries_le_of_le hg hs
  have hflip : ∀ s, ‖E s‖ = ‖E (1 - s)‖ := by
    intro s
    have := hsym (1 - s)
    rw [sub_sub_cancel] at this
    rw [this, norm_mul, hε, one_mul]
  obtain ⟨C₁, hC₁0, hC₁⟩ := le_exp_envelope (A := S) (M := k) (Nat.cast_nonneg k) (2 * k)
  have hright : ∀ s : ℂ, N ≤ s.re →
      ‖E s‖ ≤ Real.exp (C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro s hs
    refine le_trans ?_ (hC₁ ‖s‖ (norm_nonneg s))
    rw [hcomp s hs, norm_mul, norm_pow, norm_mul, norm_mul]
    have h1 : ‖s‖ ≤ 1 + ‖s‖ := by linarith
    have h2 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by simp; ring
    have hG := norm_Gammaℝ_le (s := s) (by linarith)
    calc (‖s‖ * ‖s - 1‖ * ‖Complex.Gammaℝ s‖) ^ k * ‖LSeries g s‖
        ≤ ((1 + ‖s‖) * (1 + ‖s‖) * Real.exp (‖s‖ * Real.log (2 + ‖s‖))) ^ k * S := by
          gcongr
          exact hLb s hs
      _ = S * (1 + ‖s‖) ^ (2 * k) * Real.exp (k * ‖s‖ * Real.log (2 + ‖s‖)) := by
          rw [mul_pow, mul_pow, ← Real.exp_nat_mul, two_mul, pow_add]
          ring_nf
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
  rcases le_or_gt N s.re with h2 | h2
  · exact (hright s h2).trans (hmono C₁ (by linarith) hC₁0)
  rcases le_or_gt (1 - N) s.re with h1 | h1
  · have := hC₂ ‖s‖ (norm_nonneg s)
    simp only [pow_zero, mul_one, zero_mul, Real.exp_zero] at this
    exact ((hstrip s h1 h2.le).trans this).trans (hmono C₂ (by linarith) hC₂0)
  · rw [hflip]
    have hre : N ≤ (1 - s).re := by simp; linarith
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

/-- **A completed Dirichlet series of finite order, absolutely convergent on `Re s > σ₀`, has the
order-one envelope.** -/
theorem orderOneEnvelope_of_finiteOrder_abscissa {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hfin : ∃ ρ C₀ : ℝ, ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ)) {ε : ℂ} (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s) {k : ℕ} {g : ℕ → ℂ} {σ₀ : ℝ}
    (hg : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable g s)
    (hcomp : ∀ s : ℂ, σ₀ < s.re → E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨ρ, C₀, hfin⟩ := hfin
  set m : ℕ := ⌈max σ₀ 0⌉₊ + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hmσ : σ₀ < ((2 * m : ℕ) : ℝ) := by
    have h1 : max σ₀ 0 ≤ ⌈max σ₀ 0⌉₊ := Nat.le_ceil _
    have h2 : σ₀ ≤ max σ₀ 0 := le_max_left _ _
    have h3 : (0 : ℝ) ≤ max σ₀ 0 := le_max_right _ _
    push_cast [hmdef]
    linarith
  have hN2 : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast; linarith
  set N : ℝ := ((2 * m : ℕ) : ℝ) with hN
  have hflip : ∀ s, ‖E s‖ = ‖E (1 - s)‖ := by
    intro s
    have := hsym (1 - s)
    rw [sub_sub_cancel] at this
    rw [this, norm_mul, hε, one_mul]
  have hgN : LSeriesSummable g N := hg N (by simpa using hmσ)
  have hcompN : ∀ s : ℂ, N ≤ s.re → E s = (s * (s - 1) * Complex.Gammaℝ s) ^ k * LSeries g s :=
    fun s hs => hcomp s (by linarith)
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_bound_completionFactor_even hm
  set B : ℝ := B₁ ^ k * ∑' n, ‖LSeries.term g N n‖ with hB
  have hline : ∀ z : ℂ, z.re = N → ‖E z‖ ≤ B := by
    intro z hz
    have hz' : z = ((2 * m : ℕ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hz, hN]
    rw [hcompN z hz.ge, norm_mul, norm_pow]
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ?_ k)
      (norm_LSeries_le_of_le hgN hz.ge) (norm_nonneg _) (by positivity)
    rw [hz']
    exact hB₁ z.im
  refine orderOneEnvelope_of_strip_bound_at hε hsym hN2 hgN hcompN (B := B) fun z h1 h2 => ?_
  refine PhragmenLindelof.vertical_strip hE.diffContOnCl
    (isBigO_strip_of_finiteOrder_at hfin (by linarith)) (fun w hw => ?_) hline h1 h2
  rw [hflip]
  exact hline (1 - w) (by simp [hw])

end RHTower.CompletionGrowth

end
