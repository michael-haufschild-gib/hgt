import GaloisForLFunctions.RHTower.ExactNullCertificateLogRoomGrowth

/-!
# Exact-null tests of every order: the divisor transfer and the growth law

Order `k` generalizes `ExactNullCertificateDivisorTransfer` (`k = 2`). For `R` holomorphic on
`½ ≤ Re s ≤ k+1` with `ξ^k R` and `G^k R` decaying (`G(s) = s(s−1)Γ_ℝ(s)/2`), the test
`ĝ(t) = Ξ(t)^k R(½+it)` satisfies `g(log n) ∝ √n Σ_m d_k(m) Ψ(mn)` with `Ψ = 𝓜^{−1}[G^k R]`
(`integral_xi_pow_mul_cpow_eq_tsum`), because `ζ^k = Σ d_k(m) m^{−s}`. The Dirichlet inverse of
`d_k = ζ^{⋆k}` is `μ^{⋆k}` with `|μ^{⋆k}| ≤ d_k ≤ n^{k−1}`, so:

* blindness at every `log n`, `n ≥ 2`, is equivalent to `Ψ` vanishing on `ℕ_{≥2}`
  (`logNode_blind_iff_certKernelPow_vanishes`), and then `∫ Ξ^k R = 2π Ψ(1)`;
* under the critical logarithmic room for `G^k R` on the line, blindness forces `∫ Ξ^k R = 0`
  (`integral_xi_pow_eq_zero_of_logNode_blind_of_logRoom`).

Since `|G(½+it)|^k ≍ |t|^{7k/4} e^{−kπ|t|/4}` against the Carlson rate `π/2`:
order 1 is subcritical (blind tests exist with growing `R`), order 2 is critical (room
`e^{(π/2)|t|/log|t|}`), and for order `k ≥ 3` every `R` with `|R| ≤ e^{(k−2)π|t|/4 − ε|t|}`
gives a zero test. Exact-null certificates for uniqueness therefore live at order 2.
-/

open Complex MeasureTheory ArithmeticFunction LSeries
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius LSeries.notation

noncomputable section

namespace RHTower.ExactNullDivisorTransfer

/-- `d_k = ζ^{⋆k}` as a complex sequence. -/
def divisorPow (k : ℕ) (n : ℕ) : ℂ := ((((ζ : ArithmeticFunction ℤ) ^ k) n : ℤ) : ℂ)

/-- `μ^{⋆k}` as a complex sequence. -/
def moebiusPow (k : ℕ) (n : ℕ) : ℂ := ((((μ : ArithmeticFunction ℤ) ^ k) n : ℤ) : ℂ)

theorem divisorPow_zero_right (k : ℕ) : divisorPow k 0 = 0 := by simp [divisorPow]

theorem moebiusPow_zero_right (k : ℕ) : moebiusPow k 0 = 0 := by simp [moebiusPow]

/-- `μ^{⋆k} ⋆ ζ^{⋆k} = δ₁`. -/
theorem moebiusPow_convolution_divisorPow (k : ℕ) :
    moebiusPow k ⍟ divisorPow k = fun n => if n = 1 then 1 else 0 := by
  have key : (μ : ArithmeticFunction ℤ) ^ k * (ζ : ArithmeticFunction ℤ) ^ k = 1 := by
    rw [← mul_pow, moebius_mul_coe_zeta, one_pow]
  funext n
  rw [LSeries.convolution_def]
  dsimp only
  have h := congrArg (fun F : ArithmeticFunction ℤ => ((F n : ℤ) : ℂ)) key
  simp only [moebiusPow, divisorPow]
  simp only [ArithmeticFunction.mul_apply, Int.cast_sum, Int.cast_mul,
    ArithmeticFunction.one_apply] at h ⊢
  rw [h]
  split_ifs <;> simp

/-- `0 ≤ d_k(n) ≤ n^{k−1}` for `k, n ≥ 1`, and `|μ^{⋆k}(n)| ≤ d_k(n)`. -/
theorem divisorPow_bounds (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (((ζ : ArithmeticFunction ℤ) ^ k) n : ℤ) ∧
      ((((ζ : ArithmeticFunction ℤ) ^ k) n : ℤ) : ℝ) ≤ (n : ℝ) ^ (k - 1) ∧
      |((((μ : ArithmeticFunction ℤ) ^ k) n : ℤ) : ℝ)| ≤ ((((ζ : ArithmeticFunction ℤ) ^ k) n : ℤ) : ℝ) := by
  induction k, hk using Nat.le_induction generalizing n with
  | base =>
    simp only [pow_one, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
      Nat.sub_self, pow_zero]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, if_false]
    refine ⟨by norm_num, by norm_num, ?_⟩
    push_cast
    exact_mod_cast abs_moebius_le_one
  | succ k hk ih =>
    rw [pow_succ, pow_succ, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
    have hz : ∀ x ∈ n.divisorsAntidiagonal,
        ((ζ : ArithmeticFunction ℤ) ^ k) x.1 * (ζ : ArithmeticFunction ℤ) x.2 =
          ((ζ : ArithmeticFunction ℤ) ^ k) x.1 := by
      intro x hx
      have := Nat.mem_divisorsAntidiagonal.mp hx
      have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at this; exact this.2 this.1.symm
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, h2]
    rw [Finset.sum_congr rfl hz]
    have hpos : ∀ x ∈ n.divisorsAntidiagonal, 1 ≤ x.1 ∧ x.1 ≤ n := by
      intro x hx
      have := Nat.mem_divisorsAntidiagonal.mp hx
      have h1 : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at this; exact this.2 this.1.symm
      exact ⟨Nat.one_le_iff_ne_zero.mpr h1, Nat.le_of_dvd (by omega) ⟨x.2, this.1.symm⟩⟩
    refine ⟨Finset.sum_nonneg fun x hx => (ih x.1 (hpos x hx).1).1, ?_, ?_⟩
    · push_cast
      calc ∑ x ∈ n.divisorsAntidiagonal, ((((ζ : ArithmeticFunction ℤ) ^ k) x.1 : ℤ) : ℝ)
          ≤ ∑ _x ∈ n.divisorsAntidiagonal, (n : ℝ) ^ (k - 1) := by
            refine Finset.sum_le_sum fun x hx => (ih x.1 (hpos x hx).1).2.1.trans ?_
            exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (hpos x hx).2) _
        _ = (n.divisorsAntidiagonal.card : ℝ) * (n : ℝ) ^ (k - 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [← Nat.map_div_right_divisors, Finset.card_map]
            exact_mod_cast Nat.card_divisors_le_self n
        _ = (n : ℝ) ^ (k + 1 - 1) := by
            rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    · push_cast
      calc |∑ x ∈ n.divisorsAntidiagonal, ((((μ : ArithmeticFunction ℤ) ^ k) x.1 : ℤ) : ℝ) *
            ((μ x.2 : ℤ) : ℝ)|
          ≤ ∑ x ∈ n.divisorsAntidiagonal, |((((μ : ArithmeticFunction ℤ) ^ k) x.1 : ℤ) : ℝ) *
            ((μ x.2 : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x ∈ n.divisorsAntidiagonal, ((((ζ : ArithmeticFunction ℤ) ^ k) x.1 : ℤ) : ℝ) := by
            refine Finset.sum_le_sum fun x hx => ?_
            rw [abs_mul]
            have h1 := (ih x.1 (hpos x hx).1).2.2
            have h2 : |((μ x.2 : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
            calc |((((μ : ArithmeticFunction ℤ) ^ k) x.1 : ℤ) : ℝ)| * |((μ x.2 : ℤ) : ℝ)|
                ≤ |((((μ : ArithmeticFunction ℤ) ^ k) x.1 : ℤ) : ℝ)| * 1 :=
                  mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
              _ ≤ _ := by rw [mul_one]; exact h1

theorem norm_divisorPow_le {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ‖divisorPow k n‖ ≤ (n : ℝ) ^ (k - 1) := by
  obtain ⟨h0, h1, -⟩ := divisorPow_bounds k hk n hn
  rw [divisorPow, Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast h0)]
  exact h1

theorem norm_moebiusPow_le {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ‖moebiusPow k n‖ ≤ (n : ℝ) ^ (k - 1) := by
  obtain ⟨-, h1, h2⟩ := divisorPow_bounds k hk n hn
  rw [moebiusPow, Complex.norm_intCast]
  exact h2.trans h1

/-- **Dilation inversion for `d_k`.** If `Ψ(N) = O(N^{−(k+1)})` and `Σ_m d_k(m) Ψ(mj) = 0` for
every `j ≥ 2`, then `Ψ` vanishes on `ℕ_{≥2}`. -/
theorem eq_zero_of_divisorPowDilation_eq_zero {k : ℕ} (hk : 1 ≤ k) {Ψ : ℕ → ℂ} {C : ℝ}
    (hΨ : ∀ N : ℕ, 1 ≤ N → ‖Ψ N‖ ≤ C / (N : ℝ) ^ (k + 1))
    (hblind : ∀ j : ℕ, 2 ≤ j → ∑' m, divisorPow k m * Ψ (m * j) = 0) :
    ∀ n : ℕ, 2 ≤ n → Ψ n = 0 := by
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsq : Summable fun a : ℕ => ((a : ℝ) ^ 2)⁻¹ := by
    simp [Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)]
  have hprod : Summable fun p : ℕ × ℕ => ‖((p.1 : ℝ) ^ 2)⁻¹‖ * ‖((p.2 : ℝ) ^ 2)⁻¹‖ := by
    have := summable_mul_of_summable_norm (f := fun a : ℕ => ((a : ℝ) ^ 2)⁻¹)
      (g := fun a : ℕ => ((a : ℝ) ^ 2)⁻¹) (by simp [hsq]) (by simp [hsq])
    refine (this.norm).congr fun p => ?_
    simp [norm_mul]
  have hsum : Summable fun p : ℕ × ℕ =>
      moebiusPow k p.1 * divisorPow k p.2 * Ψ (p.1 * p.2 * n) := by
    refine Summable.of_norm_bounded ((hprod.mul_left (C / (n : ℝ) ^ (k + 1)))) fun p => ?_
    obtain ⟨a, b⟩ := p
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [moebiusPow_zero_right]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [divisorPow_zero_right]
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hN : 1 ≤ a * b * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h1 := norm_moebiusPow_le hk ha
    have h2 := norm_divisorPow_le hk hb
    have h3 := hΨ _ hN
    rw [norm_mul, norm_mul]
    simp only [norm_inv, norm_pow, Real.norm_natCast]
    push_cast at h3
    have hC : 0 ≤ C := by
      have := hΨ 1 le_rfl
      simp at this
      linarith [norm_nonneg (Ψ 1)]
    calc ‖moebiusPow k a‖ * ‖divisorPow k b‖ * ‖Ψ (a * b * n)‖
        ≤ (a : ℝ) ^ (k - 1) * (b : ℝ) ^ (k - 1) * (C / ((a : ℝ) * b * n) ^ (k + 1)) := by
          gcongr
      _ = C / (n : ℝ) ^ (k + 1) * (((a : ℝ) ^ 2)⁻¹ * ((b : ℝ) ^ 2)⁻¹) := by
          have hka : (a : ℝ) ^ (k + 1) = (a : ℝ) ^ (k - 1) * (a : ℝ) ^ 2 := by
            rw [← pow_add]; congr 1; omega
          have hkb : (b : ℝ) ^ (k + 1) = (b : ℝ) ^ (k - 1) * (b : ℝ) ^ 2 := by
            rw [← pow_add]; congr 1; omega
          rw [mul_pow, mul_pow, hka, hkb]
          have : (0 : ℝ) < (a : ℝ) ^ (k - 1) := by positivity
          have : (0 : ℝ) < (b : ℝ) ^ (k - 1) := by positivity
          field_simp
  have hinv := tsum_tsum_mul_comp_mul (f := fun N => Ψ (N * n)) (moebiusPow_zero_right k)
    (divisorPow_zero_right k) hsum
  rw [moebiusPow_convolution_divisorPow] at hinv
  have hrhs : (∑' N, (if N = 1 then (1 : ℂ) else 0) * Ψ (N * n)) = Ψ n := by
    rw [tsum_eq_single 1 (fun N hN => by simp [hN])]
    simp
  have hlhs : (∑' a, ∑' b, moebiusPow k a * divisorPow k b * Ψ (a * b * n)) = 0 := by
    refine (tsum_congr fun a => ?_).trans tsum_zero
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [moebiusPow_zero_right]
    have han : 2 ≤ a * n := le_trans hn (Nat.le_mul_of_pos_left n ha)
    have : (∑' b, moebiusPow k a * divisorPow k b * Ψ (a * b * n)) =
        moebiusPow k a * ∑' b, divisorPow k b * Ψ (b * (a * n)) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun b => ?_
      rw [show a * b * n = b * (a * n) by ring]; ring
    rw [this, hblind _ han, mul_zero]
  rw [← hrhs, ← hinv]
  exact hlhs

/-- `ζ(s)^k = Σ d_k(m) m^{−s}` on `Re s > 1`, with absolute convergence (`k ≥ 1`). -/
theorem riemannZeta_pow_eq_tsum {s : ℂ} (hs : 1 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    LSeriesSummable (divisorPow k) s ∧ LSeries (divisorPow k) s = riemannZeta s ^ k := by
  have h1 : LSeriesSummable (fun _ => 1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hz : LSeries (fun _ => 1 : ℕ → ℂ) s = riemannZeta s := LSeries_one_eq_riemannZeta hs
  have hzeta : ∀ {n : ℕ}, n ≠ 0 → ((((ζ : ArithmeticFunction ℤ)) n : ℤ) : ℂ) = 1 := by
    intro n hn; simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]
  induction k, hk using Nat.le_induction with
  | base =>
    have hd : ∀ {n : ℕ}, n ≠ 0 → divisorPow 1 n = (fun _ => 1 : ℕ → ℂ) n := by
      intro n hn; simp only [divisorPow, pow_one]; exact hzeta hn
    refine ⟨(LSeriesSummable_congr s hd).mpr h1, ?_⟩
    rw [LSeries_congr hd s, hz, pow_one]
  | succ k hk ih =>
    have hconv : divisorPow (k + 1) = divisorPow k ⍟ fun _ => 1 := by
      funext n
      rw [LSeries.convolution_def]
      simp only [divisorPow, pow_succ, ArithmeticFunction.mul_apply, Int.cast_sum, Int.cast_mul,
        mul_one]
      refine Finset.sum_congr rfl fun x hx => ?_
      have := Nat.mem_divisorsAntidiagonal.mp hx
      have h2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at this; exact this.2 this.1.symm
      rw [hzeta h2, mul_one]
    refine ⟨?_, ?_⟩
    · rw [hconv]; exact ih.1.convolution h1
    · rw [hconv, LSeries_convolution' ih.1 h1, ih.2, hz, pow_succ]

/-- `ζ(s)^k = Σ d_k(m) m^{−s}` as a `tsum` with `m^{−s}`. -/
theorem riemannZeta_pow_eq_tsum' {s : ℂ} (hs : 1 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    riemannZeta s ^ k = ∑' m : ℕ, divisorPow k m * (m : ℂ) ^ (-s) := by
  rw [← (riemannZeta_pow_eq_tsum hs hk).2, LSeries]
  refine tsum_congr fun m => ?_
  rw [term_def]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [divisorPow_zero_right]
  · rw [if_neg hm, div_eq_mul_inv, Complex.cpow_neg]

/-- **Divisor transfer at order `k`.** For `R` holomorphic on `½ ≤ Re s ≤ k+1` with `ξ^k R` and
`G^k R` (on `Re s = k+1`) decaying like `1/(1+t²)`, the line integral of `ξ(s)^k R(s) n^{−s}` over
`Re s = ½` equals `2π Σ_m d_k(m) Ψ(mn)`, `Ψ = 𝓜^{−1}_{k+1}[G^k R]`. -/
theorem integral_xi_pow_mul_cpow_eq_tsum {k : ℕ} (hk : 1 ≤ k) (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → ‖xi s ^ k * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + t * I) ^ k *
      R (((k : ℝ) + 1 : ℝ) + t * I)‖ ≤ C' / (1 + t ^ 2))
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I)) =
      2 * Real.pi * ∑' m : ℕ, divisorPow k m *
        mellinInv ((k : ℝ) + 1) (fun s => archXi s ^ k * R s) ((m * n : ℕ) : ℝ) := by
  set c : ℝ := (k : ℝ) + 1 with hcdef
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc1 : (1 : ℝ) < c := by rw [hcdef]; linarith
  set Φ : ℂ → ℂ := fun s => xi s ^ k * R s * (n : ℂ) ^ (-s) with hΦ
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hstrip : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) c → 1 / 2 ≤ s.re ∧ s.re ≤ k + 1 := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith)] at hs
    exact ⟨hs.1, hs.2⟩
  have hd : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) c → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hx : DifferentiableAt ℂ xi s := xi_differentiable s
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hn0)
    exact ((hx.pow k).mul (hR s h1 h2)).mul hcp
  have hb : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) c → ‖Φ s‖ ≤ C / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hcpw := norm_natCast_cpow_neg_re_le_one hn (s := s) (by linarith)
    rw [hΦ, norm_mul]
    calc ‖xi s ^ k * R s‖ * ‖(n : ℂ) ^ (-s)‖ ≤ (C / (1 + s.im ^ 2)) * 1 :=
          mul_le_mul (hC s h1 h2) hcpw (norm_nonneg _) (le_trans (norm_nonneg _) (hC s h1 h2))
      _ = C / (1 + s.im ^ 2) := mul_one _
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay hd hb
  have hL : (∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I))) =
      ∫ t : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hΦ]; push_cast; ring_nf
  rw [hL, hshift]
  set K : ℝ → ℂ := fun t => archXi ((c : ℂ) + t * I) ^ k * R ((c : ℂ) + t * I) with hK
  set F : ℕ → ℝ → ℂ := fun m t =>
    divisorPow k m * (((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) * K t) with hF
  have hser : ∀ t : ℝ, Φ ((c : ℂ) + t * I) = ∑' m, F m t := by
    intro t
    have hre : 1 < ((c : ℂ) + t * I).re := by simp; exact hc1
    simp only [hΦ, hF, hK]
    rw [xi_eq_archXi_mul_zeta hre, mul_pow, riemannZeta_pow_eq_tsum' hre hk]
    rw [show archXi ((c : ℂ) + t * I) ^ k * (∑' m : ℕ, divisorPow k m * (m : ℂ) ^ (-((c : ℂ) + t * I))) *
        R ((c : ℂ) + t * I) * (n : ℂ) ^ (-((c : ℂ) + t * I)) =
        (∑' m : ℕ, divisorPow k m * (m : ℂ) ^ (-((c : ℂ) + t * I))) *
          ((n : ℂ) ^ (-((c : ℂ) + t * I)) * (archXi ((c : ℂ) + t * I) ^ k * R ((c : ℂ) + t * I)))
        by ring, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hKcont : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : (0 : ℝ) < ((c : ℂ) + t * I).re := by simp; linarith
    have h3 : DifferentiableAt ℂ (fun s => archXi s ^ k * R s) ((c : ℂ) + t * I) :=
      ((differentiableAt_archXi hre).pow k).mul (hR _ (by simp; linarith) (by simp [hcdef]))
    exact ContinuousAt.comp (g := fun s => archXi s ^ k * R s) h3.continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => (c : ℂ) + t * I) t)
  have hKint : Integrable K := by
    refine (integrable_inv_one_add_sq.const_mul C').mono' hKcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have := hC' t
    simp only [hK, hcdef, div_eq_mul_inv] at this ⊢
    push_cast at this ⊢
    exact this
  have hnorm_cpow : ∀ m : ℕ, ∀ t : ℝ, 1 ≤ m →
      ‖((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I))‖ = ((m * n : ℕ) : ℝ) ^ (-c) := by
    intro m t hm
    have hpos : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    rw [show (((m * n : ℕ) : ℂ)) = ((((m * n : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorPow_zero_right]
    have hcc : Continuous fun t : ℝ => ((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) := by
      have hb0 : ((m * n : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mp (Nat.one_le_iff_ne_zero.mpr (by positivity)))
      exact Continuous.const_cpow (by fun_prop) (Or.inl hb0)
    have hbound : ∀ t, ‖F m t‖ ≤ ‖divisorPow k m‖ * ((m * n : ℕ) : ℝ) ^ (-c) * ‖K t‖ := by
      intro t
      simp only [hF, norm_mul, hnorm_cpow m t hm]
      ring_nf; rfl
    refine ((hKint.norm.const_mul (‖divisorPow k m‖ * ((m * n : ℕ) : ℝ) ^ (-c)))).mono'
      ((continuous_const.mul (hcc.mul hKcont)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  have hFnorm : ∀ m : ℕ, ∫ t, ‖F m t‖ =
      ‖divisorPow k m‖ * ((m * n : ℕ) : ℝ) ^ (-c) * ∫ t, ‖K t‖ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorPow_zero_right]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, norm_mul, hnorm_cpow m t hm]
    ring
  have hFsum : Summable fun m => ∫ t, ‖F m t‖ := by
    simp_rw [hFnorm]
    refine Summable.mul_right _ ?_
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)))
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [divisorPow_zero_right]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hd := norm_divisorPow_le hk hm
    have hmn : ((m * n : ℕ) : ℝ) ^ (-c) ≤ (m : ℝ) ^ (-c) := by
      push_cast
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
    have hmc : (m : ℝ) ^ (-c) = ((m : ℝ) ^ (k + 1))⁻¹ := by
      rw [Real.rpow_neg (by positivity), hcdef, show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    calc ‖divisorPow k m‖ * ((m * n : ℕ) : ℝ) ^ (-c) ≤ (m : ℝ) ^ (k - 1) * (m : ℝ) ^ (-c) :=
          mul_le_mul hd hmn (by positivity) (by positivity)
      _ = ((m : ℝ) ^ 2)⁻¹ := by
          rw [hmc]
          have : (m : ℝ) ^ (k + 1) = (m : ℝ) ^ (k - 1) * (m : ℝ) ^ 2 := by
            rw [← pow_add]; congr 1; omega
          rw [this]
          have : (0 : ℝ) < (m : ℝ) ^ (k - 1) := by positivity
          field_simp
  rw [show (∫ t : ℝ, Φ ((c : ℂ) + t * I)) = ∫ t : ℝ, ∑' m, F m t from
    integral_congr_ae (Filter.Eventually.of_forall hser),
    ← integral_tsum_of_summable_integral_norm hFint hFsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hI : (∫ y : ℝ, (((m * n : ℕ) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) •
      (archXi ((c : ℂ) + y * I) ^ k * R ((c : ℂ) + y * I))) =
      ∫ t : ℝ, ((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) * K t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hK, smul_eq_mul]
    push_cast
    ring_nf
  simp only [hF]
  rw [integral_const_mul, mellinInv, hI, Complex.real_smul]
  push_cast
  field_simp
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_comm I]

/-- The ζ-free kernel of an order-`k` exact-null test: `Ψ = 𝓜^{−1}_{k+1}[G^k R]`. -/
def certKernelPow (k : ℕ) (R : ℂ → ℂ) (x : ℝ) : ℂ :=
  mellinInv ((k : ℝ) + 1) (fun s => archXi s ^ k * R s) x

theorem norm_certKernelPow_le (k : ℕ) (R : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    ‖certKernelPow k R x‖ ≤
      (∫ t : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + t * I) ^ k * R (((k : ℝ) + 1 : ℝ) + t * I)‖) /
        (2 * Real.pi) * x ^ (-((k : ℝ) + 1)) := by
  rw [certKernelPow, mellinInv, norm_smul]
  have h1 : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h1]
  have h2 : ‖∫ y : ℝ, (x : ℂ) ^ (-(((k : ℝ) + 1 : ℝ) + y * I : ℂ)) •
      (archXi (((k : ℝ) + 1 : ℝ) + y * I) ^ k * R (((k : ℝ) + 1 : ℝ) + y * I))‖ ≤
      ∫ y : ℝ, x ^ (-((k : ℝ) + 1)) *
        ‖archXi (((k : ℝ) + 1 : ℝ) + y * I) ^ k * R (((k : ℝ) + 1 : ℝ) + y * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_smul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  rw [integral_const_mul] at h2
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, (x : ℂ) ^ (-(((k : ℝ) + 1 : ℝ) + y * I : ℂ)) •
        (archXi (((k : ℝ) + 1 : ℝ) + y * I) ^ k * R (((k : ℝ) + 1 : ℝ) + y * I))‖
      ≤ 1 / (2 * Real.pi) * (x ^ (-((k : ℝ) + 1)) *
          ∫ y : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + y * I) ^ k * R (((k : ℝ) + 1 : ℝ) + y * I)‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem integral_xi_pow_logNode (k : ℕ) (R : ℂ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) =
      (n : ℂ) ^ (1 / 2 : ℂ) *
        ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have : (n : ℂ) ^ (-((t : ℂ) * I)) = (n : ℂ) ^ (1 / 2 : ℂ) * (n : ℂ) ^ (-(1 / 2 + t * I)) := by
    rw [← Complex.cpow_add _ _ hn0]; ring_nf
  simp only [this]; ring

/-- **Order-`k` exact-null blindness is ζ-free.** `ĝ(t) = Ξ(t)^k R(½+it)` vanishes at every
`log n`, `n ≥ 2`, iff `Ψ = 𝓜^{−1}[G^k R]` vanishes on `ℕ_{≥2}` (inverse of `d_k` is `μ^{⋆k}`). -/
theorem logNode_blind_iff_certKernelPow_vanishes {k : ℕ} (hk : 1 ≤ k) (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → ‖xi s ^ k * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + t * I) ^ k *
      R (((k : ℝ) + 1 : ℝ) + t * I)‖ ≤ C' / (1 + t ^ 2)) :
    (∀ n : ℕ, 2 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) = 0) ↔
    (∀ n : ℕ, 2 ≤ n → certKernelPow k R n = 0) := by
  have hval : ∀ n : ℕ, 1 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) =
        (n : ℂ) ^ (1 / 2 : ℂ) * (2 * Real.pi *
          ∑' m : ℕ, divisorPow k m * certKernelPow k R ((m * n : ℕ) : ℝ)) := by
    intro n hn
    rw [integral_xi_pow_logNode k R hn, integral_xi_pow_mul_cpow_eq_tsum hk R hR hC hC' hn]
    rfl
  constructor
  · intro hblind
    set K := ∫ t : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + t * I) ^ k * R (((k : ℝ) + 1 : ℝ) + t * I)‖
    refine eq_zero_of_divisorPowDilation_eq_zero hk (Ψ := fun N : ℕ => certKernelPow k R N)
      (C := K / (2 * Real.pi)) (fun N hN => ?_) (fun j hj => ?_)
    · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have := norm_certKernelPow_le k R hN0
      rw [Real.rpow_neg hN0.le, show ((N : ℝ) ^ ((k : ℝ) + 1)) = (N : ℝ) ^ (k + 1) by
        rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast],
        ← div_eq_mul_inv] at this
      exact this
    · have h := hval j (by omega)
      rw [hblind j hj] at h
      have hj0 : (j : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; push Not
        intro h0; exact absurd h0 (by exact_mod_cast (by omega : j ≠ 0))
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      have := (mul_eq_zero.mp h.symm).resolve_left hj0
      have := (mul_eq_zero.mp this).resolve_left hpi
      simpa [Nat.cast_mul] using this
  · intro hvan n hn
    rw [hval n (by omega)]
    have : (∑' m : ℕ, divisorPow k m * certKernelPow k R ((m * n : ℕ) : ℝ)) = 0 := by
      refine (tsum_congr fun m => ?_).trans tsum_zero
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [divisorPow_zero_right]
      · have hmn : 2 ≤ m * n := le_trans hn (Nat.le_mul_of_pos_left n hm)
        rw [hvan _ hmn, mul_zero]
    rw [this, mul_zero, mul_zero]

theorem divisorPow_one (k : ℕ) : divisorPow k 1 = 1 := by
  induction k with
  | zero => simp [divisorPow]
  | succ k ih =>
    have : (((ζ : ArithmeticFunction ℤ) ^ (k + 1)) 1 : ℤ) =
        (((ζ : ArithmeticFunction ℤ) ^ k) 1 : ℤ) * ((ζ : ArithmeticFunction ℤ) 1) := by
      rw [pow_succ, ArithmeticFunction.mul_apply]
      simp
    rw [divisorPow, this]
    push_cast
    rw [show ((((ζ : ArithmeticFunction ℤ) ^ k) 1 : ℤ) : ℂ) = divisorPow k 1 from rfl, ih]
    simp [ArithmeticFunction.natCoe_apply]

/-- Under blindness the central value is `2π Ψ(1)`. -/
theorem integral_xi_pow_eq_certKernelPow_one {k : ℕ} (hk : 1 ≤ k) (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → ‖xi s ^ k * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + t * I) ^ k *
      R (((k : ℝ) + 1 : ℝ) + t * I)‖ ≤ C' / (1 + t ^ 2))
    (hvan : ∀ n : ℕ, 2 ≤ n → certKernelPow k R n = 0) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) = 2 * Real.pi * certKernelPow k R 1 := by
  have h := integral_xi_pow_logNode k R (n := 1) le_rfl
  rw [integral_xi_pow_mul_cpow_eq_tsum hk R hR hC hC' le_rfl] at h
  simp only [Nat.cast_one, Complex.one_cpow, mul_one, one_mul] at h
  rw [h, tsum_eq_single 1 (fun m hm => ?_)]
  · simp [divisorPow_one, certKernelPow]
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [divisorPow_zero_right]
    · have : 2 ≤ m := by omega
      have h2 := hvan m this
      rw [certKernelPow] at h2
      rw [h2, mul_zero]

theorem certKernelPow_eq_mellinInv_half {k : ℕ} (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 →
      ‖archXi s ^ k * R s‖ ≤ C / (1 + s.im ^ 2))
    {x : ℝ} (hx : 0 < x) :
    certKernelPow k R x = mellinInv (1 / 2) (fun s => archXi s ^ k * R s) x := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hstrip : ∀ s : ℂ, s.re ∈ Set.uIcc ((k : ℝ) + 1) (1 / 2) → 1 / 2 ≤ s.re ∧ s.re ≤ k + 1 := by
    intro s hs
    rw [Set.uIcc_of_ge (by linarith)] at hs
    exact hs
  have hcp : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 →
      ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (-((k : ℝ) + 1)) := by
    intro s h1 h2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    rcases le_or_gt x 1 with hx1 | hx1
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -s.re ≥ -((k : ℝ) + 1) by linarith)
      have : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show -s.re ≤ -(1 / 2) by linarith)
      have : 0 ≤ x ^ (-((k : ℝ) + 1)) := Real.rpow_nonneg hx.le _
      linarith
  unfold certKernelPow mellinInv
  congr 1
  have key := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay
    (Φ := fun s : ℂ => (x : ℂ) ^ (-s) * (archXi s ^ k * R s)) (c₁ := (k : ℝ) + 1) (c₂ := 1 / 2)
    (C := (x ^ (-(1 / 2 : ℝ)) + x ^ (-((k : ℝ) + 1))) * C)
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hstrip s hs
      have hre : 0 < s.re := by linarith
      exact (((differentiableAt_id.neg).const_cpow (Or.inl hx0))).mul
        (((differentiableAt_archXi hre).pow k).mul (hR s h1 h2)))
    (fun s hs => by
      obtain ⟨h1, h2⟩ := hstrip s hs
      rw [norm_mul, mul_div_assoc]
      exact mul_le_mul (hcp s h1 h2) (hC s h1 h2) (norm_nonneg _) (by positivity))
  simpa [smul_eq_mul] using key

/-- **Order-`k` growth law.** If `Ξ^k R` is blind at every `log n`, `n ≥ 2`, and
`G(½+it)^k R(½+it)` is integrable against the critical room
`e^{(π/2)(|t| − |t|/log(|t|+3))}`, then `∫ Ξ^k R = 0`. Since `|G(½+it)|^k ≍ e^{−kπ|t|/4}`, for
`k ≥ 3` this covers every `R` growing slower than `e^{(k−2)π|t|/4}` up to sub-exponential
factors; `k = 2` is the critical order. -/
theorem integral_xi_pow_eq_zero_of_logNode_blind_of_logRoom {k : ℕ} (hk : 1 ≤ k) (R : ℂ → ℂ)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 → ‖xi s ^ k * R s‖ ≤ C / (1 + s.im ^ 2))
    {C'' : ℝ} (hC'' : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ k + 1 →
      ‖archXi s ^ k * R s‖ ≤ C'' / (1 + s.im ^ 2))
    (hroom : Integrable fun t : ℝ =>
      ‖archXi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I)‖ *
        RHTower.PrimeBlindCarlson.logRoomWeight (Real.pi / 2) t)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) = 0) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) = 0 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hC' : ∀ t : ℝ, ‖archXi (((k : ℝ) + 1 : ℝ) + t * I) ^ k *
      R (((k : ℝ) + 1 : ℝ) + t * I)‖ ≤ C'' / (1 + t ^ 2) := by
    intro t
    have := hC'' (((k : ℝ) + 1 : ℝ) + t * I) (by simp; linarith) (by simp)
    simpa using this
  have hvan := (logNode_blind_iff_certKernelPow_vanishes hk R hR hC hC').mp hblind
  set w : ℝ → ℂ := fun t => archXi (1 / 2 + t * I) ^ k * R (1 / 2 + t * I) with hw
  have hwcont : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre : (0 : ℝ) < ((1 / 2 : ℂ) + t * I).re := by simp
    have h3 : DifferentiableAt ℂ (fun s => archXi s ^ k * R s) ((1 / 2 : ℂ) + t * I) :=
      ((differentiableAt_archXi hre).pow k).mul (hR _ (by simp) (by simp; linarith))
    exact ContinuousAt.comp (g := fun s => archXi s ^ k * R s) h3.continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t)
  have hmoment : ∀ x : ℝ, 0 < x → certKernelPow k R x =
      (1 / (2 * Real.pi) : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∫ t, w t * cexp (-(I * t) * Real.log x) := by
    intro x hx
    rw [certKernelPow_eq_mellinInv_half R hR hC'' hx, mellinInv, Complex.real_smul,
      ← integral_const_mul, ← integral_const_mul]
    push_cast
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hcp : (x : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * cexp (-(I * t) * Real.log x) := by
      rw [show -((1 / 2 : ℂ) + t * I) = -(1 / 2 : ℂ) + (-(t * I)) by ring,
        Complex.cpow_add _ _ hx0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
      ring_nf
    simp only [smul_eq_mul, hw]
    rw [hcp]; ring
  have hmom : ∀ n ∈ {n : ℕ | 2 ≤ n}, ∫ t, w t * cexp (-(I * t) * Real.log n) = 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by simp at hn; omega : 0 < n)
    have h := hmoment n hn0
    rw [hvan n hn] at h
    have hc : (1 / (2 * Real.pi) : ℂ) * ((n : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
      refine mul_ne_zero (one_div_ne_zero (by
        exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0))) ?_
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0; exact absurd h0 (by exact_mod_cast hn0.ne')
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  have hzero := RHTower.PrimeBlindCarlson.fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical
    (fun n hn => hn) RHTower.PrimeBlindCarlson.not_summable_one_div_mul_log
    hwcont.aestronglyMeasurable hroom hmom 0
  have hk1 : certKernelPow k R 1 = 0 := by
    rw [hmoment 1 one_pos]
    simp only [Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hzero ⊢
    rw [hzero, mul_zero]
  rw [integral_xi_pow_eq_certKernelPow_one hk R hR hC hC' hvan, hk1, mul_zero]

end RHTower.ExactNullDivisorTransfer
