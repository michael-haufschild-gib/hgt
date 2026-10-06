import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability

/-!
# Twisted Selberg log-monomials

For coprime squarefree `a, b` and `i, j ≥ 1`,

`Q_{a,b}(i, j, N) = Σ_{m, n ≤ N} μ(m)μ(n)(ma, nb)/(mn) · log^i(N/m) log^j(N/n)`.

**Dilated inner sums.** For a coefficient `G` and a model `Φ(d, e, N)`,
`W_x(N) = Σ_{y ≤ N/x} G(y) Φ(x₁y₁, x₂y₂, N)`. Weighted sums of `(F ⋆ G) ⋆ P` collapse to
`Σ_x F(x) W_x(N)` when the weighted sums of `P` are `Φ` (`sum_Icc_convolution_convolution_mul`).
If `Φ/log^k N → κ` with a uniform envelope and `G` is absolutely summable,
`W_x(N)/log^k N → κ Σ G` by dominated convergence (`tendsto_dilatedInner`), and for finitely
supported `F` the full sum tends to `κ (Σ F)(Σ G)` (`tendsto_sum_mul_dilatedInner`).

* **Decomposition** (`twistedLogMonomial_eq`): with `c_{a,b} = (F ⋆ G) ⋆ P`,
  `Q_{a,b} = Σ_x F(x) W_x(N)` with `Φ` the dilated principal Selberg model.
* **Cancellation** (`tendsto_twistedLogMonomial_div`): if `ab > 1` then `Q_{a,b}/log^{i+j−1} N → 0`,
  because `F` has total mass zero.
* **Uniform envelope** (`exists_abs_twistedLogMonomial_le`):
  `|Q_{a,b}| ≤ M d(ab) d(a) d(b) 2^{ω(a)+ω(b)} log^{i+j−1} N` for all such `a, b`.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-! ## Dilated inner sums -/

/-- The dilated inner sum `W_x(N) = Σ_{y ≤ N/x} G(y) Φ(x₁y₁, x₂y₂, N)`. -/
def dilatedInner (G : ℕ → ℕ → ℝ) (Φ : ℕ → ℕ → ℕ → ℝ) (x₁ x₂ N : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (N / x₁), ∑ s ∈ Finset.Icc 1 (N / x₂), G r s * Φ (x₁ * r) (x₂ * s) N

/-- **Weighted sums of a double convolution.** If the `w_N`-weighted sums of `P` over the dilated
boxes are `Φ`, then `Σ_{m,n ≤ N} ((F ⋆ G) ⋆ P)(m,n) w_N(m,n) = Σ_x F(x) W_x(N)`. -/
theorem sum_Icc_convolution_convolution_mul (F G P : ℕ → ℕ → ℝ) (w Φ : ℕ → ℕ → ℕ → ℝ) (N : ℕ)
    (hΦ : ∀ d ∈ Finset.Icc 1 N, ∀ e ∈ Finset.Icc 1 N,
      ∑ r ∈ Finset.Icc 1 (N / d), ∑ s ∈ Finset.Icc 1 (N / e), P r s * w N (d * r) (e * s) =
        Φ d e N) :
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        bivariateDirichletConvolution (bivariateDirichletConvolution F G) P m n * w N m n =
      ∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, F x₁ x₂ * dilatedInner G Φ x₁ x₂ N := by
  rw [sum_Icc_bivariateDirichletConvolution_mul,
    Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => by rw [hΦ d hd e he],
    sum_Icc_bivariateDirichletConvolution_mul]
  rfl

/-- The inner sum as a series over all pairs, cut off at `N/x`. -/
theorem dilatedInner_eq_tsum (G : ℕ → ℕ → ℝ) (Φ : ℕ → ℕ → ℕ → ℝ) (x₁ x₂ N : ℕ) :
    dilatedInner G Φ x₁ x₂ N = ∑' y : ℕ × ℕ,
      (if 1 ≤ y.1 ∧ y.1 ≤ N / x₁ ∧ 1 ≤ y.2 ∧ y.2 ≤ N / x₂ then
        G y.1 y.2 * Φ (x₁ * y.1) (x₂ * y.2) N else 0) := by
  unfold dilatedInner
  rw [tsum_eq_sum (s := Finset.Icc 1 (N / x₁) ×ˢ Finset.Icc 1 (N / x₂)), Finset.sum_product]
  · refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun t ht => ?_
    rw [if_pos ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2, (Finset.mem_Icc.mp ht).1,
      (Finset.mem_Icc.mp ht).2⟩]
  · intro y hy
    rw [if_neg]
    intro h
    exact hy (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩,
      Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩⟩)

/-- **The inner limit.** `W_x(N)/log^k N → κ Σ G` by dominated convergence. -/
theorem tendsto_dilatedInner {G : ℕ → ℕ → ℝ} (hG : Summable fun y : ℕ × ℕ => |G y.1 y.2|)
    (hG0 : ∀ n, G 0 n = 0) (hG0' : ∀ m, G m 0 = 0) {Φ : ℕ → ℕ → ℕ → ℝ} {k : ℕ} {κ M : ℝ}
    (hΦ : ∀ {d e : ℕ}, 0 < d → 0 < e →
      Tendsto (fun N : ℕ => Φ d e N / Real.log N ^ k) atTop (𝓝 κ)) (hM0 : 0 ≤ M)
    (hM : ∀ᶠ N : ℕ in atTop, ∀ d e : ℕ, 0 < d → 0 < e → |Φ d e N| ≤ M * Real.log N ^ k)
    {x₁ x₂ : ℕ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    Tendsto (fun N : ℕ => dilatedInner G Φ x₁ x₂ N / Real.log N ^ k) atTop
      (𝓝 ((∑' y : ℕ × ℕ, G y.1 y.2) * κ)) := by
  have hlim : Tendsto (fun N : ℕ => ∑' y : ℕ × ℕ,
      (if 1 ≤ y.1 ∧ y.1 ≤ N / x₁ ∧ 1 ≤ y.2 ∧ y.2 ≤ N / x₂ then
        G y.1 y.2 * Φ (x₁ * y.1) (x₂ * y.2) N else 0) / Real.log N ^ k)
      atTop (𝓝 (∑' y : ℕ × ℕ, G y.1 y.2 * κ)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun y => M * |G y.1 y.2|)
      (hG.mul_left M) (fun y => ?_) ?_
    · rcases Nat.eq_zero_or_pos y.1 with h1 | h1
      · rw [h1, hG0, zero_mul]
        refine tendsto_const_nhds.congr fun N => ?_
        rw [if_neg (by omega), zero_div]
      rcases Nat.eq_zero_or_pos y.2 with h2 | h2
      · rw [h2, hG0', zero_mul]
        refine tendsto_const_nhds.congr fun N => ?_
        rw [if_neg (by omega), zero_div]
      refine ((hΦ (Nat.mul_pos hx₁ h1) (Nat.mul_pos hx₂ h2)).const_mul (G y.1 y.2)).congr' ?_
      filter_upwards [eventually_ge_atTop (x₁ * y.1), eventually_ge_atTop (x₂ * y.2)]
        with N hN1 hN2
      rw [if_pos ⟨h1, (Nat.le_div_iff_mul_le hx₁).mpr (by linarith [Nat.mul_comm x₁ y.1]), h2,
        (Nat.le_div_iff_mul_le hx₂).mpr (by linarith [Nat.mul_comm x₂ y.2])⟩]
      ring
    · filter_upwards [hM, eventually_ge_atTop 2] with N hN hN2 y
      have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
      split_ifs with h
      · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (pow_pos hL _),
          div_le_iff₀ (pow_pos hL _)]
        calc |G y.1 y.2| * |Φ (x₁ * y.1) (x₂ * y.2) N|
            ≤ |G y.1 y.2| * (M * Real.log N ^ k) :=
              mul_le_mul_of_nonneg_left (hN _ _ (Nat.mul_pos hx₁ h.1) (Nat.mul_pos hx₂ h.2.2.1))
                (abs_nonneg _)
          _ = M * |G y.1 y.2| * Real.log N ^ k := by ring
      · simp only [zero_div, norm_zero]
        exact mul_nonneg hM0 (abs_nonneg _)
  rw [tsum_mul_right] at hlim
  refine hlim.congr fun N => ?_
  rw [dilatedInner_eq_tsum, ← tsum_div_const]

/-- **Finitely supported outer factor.** If `F` vanishes outside `[1, X₀]²`, then
`Σ_x F(x) W_x(N)/log^k N → (Σ_{x ≤ X₀} F(x)) κ Σ G`. -/
theorem tendsto_sum_mul_dilatedInner {F G : ℕ → ℕ → ℝ} (X₀ : ℕ)
    (hF : ∀ x₁ x₂, X₀ < x₁ ∨ X₀ < x₂ → F x₁ x₂ = 0)
    (hG : Summable fun y : ℕ × ℕ => |G y.1 y.2|) (hG0 : ∀ n, G 0 n = 0) (hG0' : ∀ m, G m 0 = 0)
    {Φ : ℕ → ℕ → ℕ → ℝ} {k : ℕ} {κ M : ℝ}
    (hΦ : ∀ {d e : ℕ}, 0 < d → 0 < e →
      Tendsto (fun N : ℕ => Φ d e N / Real.log N ^ k) atTop (𝓝 κ)) (hM0 : 0 ≤ M)
    (hM : ∀ᶠ N : ℕ in atTop, ∀ d e : ℕ, 0 < d → 0 < e → |Φ d e N| ≤ M * Real.log N ^ k) :
    Tendsto (fun N : ℕ => (∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N,
        F x₁ x₂ * dilatedInner G Φ x₁ x₂ N) / Real.log N ^ k) atTop
      (𝓝 ((∑ x₁ ∈ Finset.Icc 1 X₀, ∑ x₂ ∈ Finset.Icc 1 X₀, F x₁ x₂) *
        ((∑' y : ℕ × ℕ, G y.1 y.2) * κ))) := by
  have hlim : Tendsto (fun N : ℕ => ∑ x ∈ Finset.Icc 1 X₀ ×ˢ Finset.Icc 1 X₀, F x.1 x.2 *
      (dilatedInner G Φ x.1 x.2 N / Real.log N ^ k)) atTop
      (𝓝 (∑ x ∈ Finset.Icc 1 X₀ ×ˢ Finset.Icc 1 X₀,
        F x.1 x.2 * ((∑' y : ℕ × ℕ, G y.1 y.2) * κ))) := by
    refine tendsto_finsetSum _ fun x hx => ?_
    have hx' := Finset.mem_product.mp hx
    exact (tendsto_dilatedInner hG hG0 hG0' hΦ hM0 hM (Finset.mem_Icc.mp hx'.1).1
      (Finset.mem_Icc.mp hx'.2).1).const_mul _
  rw [← Finset.sum_mul, Finset.sum_product] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop X₀] with N hN
  have hR : (∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, F x₁ x₂ * dilatedInner G Φ x₁ x₂ N) /
      Real.log N ^ k = ∑ x ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N,
        F x.1 x.2 * (dilatedInner G Φ x.1 x.2 N / Real.log N ^ k) := by
    rw [Finset.sum_product, Finset.sum_div]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x₂ _ => ?_
    ring
  rw [hR]
  refine Finset.sum_subset (s₁ := Finset.Icc 1 X₀ ×ˢ Finset.Icc 1 X₀)
    (s₂ := Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ?_ ?_
  · intro x hx
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨hx.1.1, hx.1.2.trans hN⟩, ⟨hx.2.1, hx.2.2.trans hN⟩⟩
  · intro x hx hxS
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx hxS
    have hout : X₀ < x.1 ∨ X₀ < x.2 := by
      by_contra h; push Not at h; exact hxS ⟨⟨hx.1.1, h.1⟩, ⟨hx.2.1, h.2⟩⟩
    rw [hF _ _ hout, zero_mul]

/-- **Envelope of `Σ_x F(x) W_x(N)`** from the masses of `F`, `G` and a bound on `Φ`. -/
theorem abs_sum_mul_dilatedInner_le {F G : ℕ → ℕ → ℝ} {Φ : ℕ → ℕ → ℕ → ℝ} {N : ℕ} {A B C : ℝ}
    (hF : ∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, |F x₁ x₂| ≤ A)
    (hG : ∀ X Y : ℕ, ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |G r s| ≤ B)
    (hΦ : ∀ d e : ℕ, 0 < d → 0 < e → |Φ d e N| ≤ C) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    |∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, F x₁ x₂ * dilatedInner G Φ x₁ x₂ N| ≤
      A * (B * C) := by
  have hinner : ∀ x₁ ∈ Finset.Icc 1 N, ∀ x₂ ∈ Finset.Icc 1 N,
      |dilatedInner G Φ x₁ x₂ N| ≤ B * C := by
    intro x₁ hx₁ x₂ hx₂
    unfold dilatedInner
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun r' _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r' ∈ Finset.Icc 1 (N / x₁), ∑ s ∈ Finset.Icc 1 (N / x₂),
          |G r' s * Φ (x₁ * r') (x₂ * s) N|
        ≤ ∑ r' ∈ Finset.Icc 1 (N / x₁), ∑ s ∈ Finset.Icc 1 (N / x₂), |G r' s| * C := by
          refine Finset.sum_le_sum fun r' hr' => Finset.sum_le_sum fun s hs => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hΦ _ _ (Nat.mul_pos (Finset.mem_Icc.mp hx₁).1
            (Finset.mem_Icc.mp hr').1) (Nat.mul_pos (Finset.mem_Icc.mp hx₂).1
            (Finset.mem_Icc.mp hs).1)) (abs_nonneg _)
      _ = (∑ r' ∈ Finset.Icc 1 (N / x₁), ∑ s ∈ Finset.Icc 1 (N / x₂), |G r' s|) * C := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => ?_; rw [Finset.sum_mul]
      _ ≤ B * C := mul_le_mul_of_nonneg_right (hG _ _) hC
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun x₁ _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, |F x₁ x₂ * dilatedInner G Φ x₁ x₂ N|
      ≤ ∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, |F x₁ x₂| * (B * C) := by
        refine Finset.sum_le_sum fun x₁ hx₁ => Finset.sum_le_sum fun x₂ hx₂ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hinner x₁ hx₁ x₂ hx₂) (abs_nonneg _)
    _ = (∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, |F x₁ x₂|) * (B * C) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => ?_; rw [Finset.sum_mul]
    _ ≤ A * (B * C) := mul_le_mul_of_nonneg_right hF (by positivity)

/-! ## The twisted log-monomials -/

/-- The twisted log-monomial `Q_{a,b}(i, j, N)`. -/
def twistedLogMonomial (a b i j N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, twistedOriginalCoeff a b m n *
    (Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j)

/-- **The decomposition `Q_{a,b} = Σ_x F(x) W_x(N)`.** -/
theorem twistedLogMonomial_eq {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) (i j N : ℕ) :
    twistedLogMonomial a b i j N =
      ∑ x₁ ∈ Finset.Icc 1 N, ∑ x₂ ∈ Finset.Icc 1 N, twistFinite a b x₁ x₂ *
        dilatedInner (twistSummable a b) (selbergPrincipalScaledLogPowerModel i j) x₁ x₂ N := by
  unfold twistedLogMonomial
  rw [← sum_Icc_convolution_convolution_mul _ _ selbergPrincipalCoeff
    (fun N m n => Real.log ((N : ℝ) / (m : ℝ)) ^ i * Real.log ((N : ℝ) / (n : ℝ)) ^ j) _ N
    fun d hd e he => selbergPrincipalCoeff_weighted_logPower_eq_scaledModel i j d e N
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  rw [twistedOriginalCoeff_eq_convolution hab ha hb (Finset.mem_Icc.mp hm).1
    (Finset.mem_Icc.mp hn).1]

/-- **Cancellation.** If `ab > 1`, `Q_{a,b}(q+1, r+1, N)/log^{q+r+1} N → 0`. -/
theorem tendsto_twistedLogMonomial_div {a b : ℕ} (hab : Nat.Coprime a b) (ha : Squarefree a)
    (hb : Squarefree b) (hab1 : a ≠ 1 ∨ b ≠ 1) (q r : ℕ) :
    Tendsto (fun N : ℕ => twistedLogMonomial a b (q + 1) (r + 1) N / Real.log N ^ (q + r + 1))
      atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  have h := tendsto_sum_mul_dilatedInner (a * b * (a * b))
    (fun _ _ hx => twistFinite_eq_zero_of_lt ha.ne_zero hb.ne_zero hx)
    (summable_abs_twistSummable a b) (twistSummable_zero_left a b) (twistSummable_zero_right a b)
    (fun hd he => tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow q r hd he) hM0 hM
  rw [sum_twistFinite_eq_zero ha.ne_zero hb.ne_zero hab1 le_rfl, zero_mul] at h
  refine h.congr fun N => ?_
  rw [twistedLogMonomial_eq hab ha hb]

/-- **Uniform envelope** of the twisted log-monomials. -/
theorem exists_abs_twistedLogMonomial_le (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, Nat.Coprime a b → Squarefree a → Squarefree b →
      |twistedLogMonomial a b (q + 1) (r + 1) N| ≤
        M * (((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card) *
          ((2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card)) * Real.log N ^ (q + r + 1) := by
  obtain ⟨M, hM, hMb⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  set E₁ : ℝ := ∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|
  have hE₁ : 0 ≤ E₁ := tsum_nonneg fun _ => abs_nonneg _
  refine ⟨M * E₁, by positivity, ?_⟩
  filter_upwards [hMb, eventually_ge_atTop 2] with N hN hN2 a b hab ha hb
  have hL : 0 ≤ Real.log N ^ (q + r + 1) := pow_nonneg (Real.log_nonneg (by exact_mod_cast
    (by omega : 1 ≤ N))) _
  rw [twistedLogMonomial_eq hab ha hb]
  refine (abs_sum_mul_dilatedInner_le (sum_Icc_abs_twistFinite_le ha.ne_zero hb.ne_zero N N)
    (sum_Icc_abs_twistSummable_le a b) hN (by positivity) (by positivity)).trans (le_of_eq ?_)
  ring

end

end RHTower.Sieve
