import GaloisForLFunctions.RHTower.XiSliceBoundedDetectionOrder
import GaloisForLFunctions.RHTower.XiSliceLowestCoeffPositive

/-!
# Bounded detection order at an ordinate carrying a critical zero

`exists_re_xiSliceCoeff_neg_of_offLine_mass` detects an off-line zero `ρ` of `ξ` at bounded slice
order at its ordinate `γ = Im ρ`, under the hypothesis `Ξ(γ) ≠ 0`.  This file removes that
hypothesis.  Let `Ξ` vanish to order `k ≥ 0` at `γ`, so a critical zero of multiplicity `k` sits at
the same height as the off-line pair `γ ± iδ`, `δ = |Re ρ − ½|` (the mixed class).

The Hadamard product splits off the `k` copies at `γ`:
`Ξ(z) = (z − γ)^k h(z)` with `h(z) = Ξ(0) (−e^{z/γ}/γ)^k P(z)`, where `P` is the canonical product
over the zero copies away from `γ` (`xiCanonicalProduct_factorization_at_support`).  Hence

  `g_γ(x) = x^{2k} h(γ − ix) h(γ + ix)`,   `h(γ − ix) h(γ + ix) = h(γ)² Π_{z ≠ γ} (1 + x²/(z − γ)²)`,

the product running over the other zero copies.  The lowest coefficient is `c_{2k}(γ) = h(γ)² > 0`
(`xiSliceCoeff_lowest_of_factor`).  On `|x| = 2δ` the product is at most `5^m e^{4δ²S}` exactly as in
the case `k = 0`, and the Cauchy tail estimate shifted by `2k`
(`exists_re_xiSliceCoeff_neg_of_shifted_tail_lt`) gives:

**Theorem** (`exists_re_xiSliceCoeff_neg_of_offLine_mass_of_order`).  Let `ρ` be an off-line zero,
`k` the order of `Ξ` at `γ`, at most `m` copies at `γ ± iδ`, and `Σ 1/|z − γ|² ≤ S` over the copies
at neither `γ ± iδ` nor `γ`.  If `2 · 5^m · e^{4δ²S} < 2^N`, some `c_n(γ)` with `n < 2k + N` has
negative real part.

So a critical zero at the ordinate of an off-line pair delays detection by exactly its own
vanishing order `2k`, and no more: the mixed class is detected at bounded order above the lowest
nonvanishing coefficient, uniformly in the height.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- **Detection order, shifted.**  Let `ρ` be a zero of `ξ` with `δ = |Re ρ − ½| > 0`, `R > δ`,
and `|g_γ| ≤ M` on `|x| = R`, `γ = Im ρ`.  If `M R^{−k} (δ/R)^N/(1 − δ/R) < Re c_k(γ)`, then some
slice coefficient `c_n(γ)` with `n < k + N` has negative real part. -/
theorem exists_re_xiSliceCoeff_neg_of_shifted_tail_lt {ρ : ℂ} (hρ : xi ρ = 0)
    (hδ : 0 < |ρ.re - 1 / 2|) {R M : ℝ} (hR : |ρ.re - 1 / 2| < R)
    (hM : ∀ x ∈ sphere (0 : ℂ) R, ‖xiSliceProduct ρ.im x‖ ≤ M) (k : ℕ) {N : ℕ}
    (hN : M / R ^ k * (|ρ.re - 1 / 2| / R) ^ N / (1 - |ρ.re - 1 / 2| / R) <
      (xiSliceCoeff ρ.im k).re) :
    ∃ n < k + N, (xiSliceCoeff ρ.im n).re < 0 := by
  by_contra hall
  push Not at hall
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hR0 : 0 < R := hδ.trans hR
  set r : ℝ := δ / R with hr
  have hr0 : 0 ≤ r := div_nonneg hδ.le hR0.le
  have hr1 : r < 1 := (div_lt_one hR0).mpr hR
  have hcoef := norm_xiSliceCoeff_le hR0 hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hcoef 0 |>.trans (by simp))
  have hRk : 0 < R ^ k := pow_pos hR0 k
  have hck : (xiSliceCoeff ρ.im k).re ≤ M / R ^ k :=
    (Complex.re_le_norm _).trans (hcoef k)
  -- the trivial order `N = 0`
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [pow_zero, mul_one] at hN
    have : M / R ^ k ≤ M / R ^ k / (1 - r) :=
      le_div_self (div_nonneg hM0 hRk.le) (by linarith) (by linarith)
    linarith
  -- the Taylor series at the real point `δ`, split at `k + N`
  have hsum := hasSum_xiSliceCoeff ρ.im (δ : ℂ)
  rw [xiSliceProduct_abs_eq_zero hρ] at hsum
  have htail := (hasSum_nat_add_iff' (k + N)).mpr hsum
  have hg : HasSum (fun n : ℕ => M * r ^ (k + N) * r ^ n) (M * r ^ (k + N) / (1 - r)) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M * r ^ (k + N))
    simpa [div_eq_mul_inv] using this
  have hbound : ∀ n : ℕ, ‖xiSliceCoeff ρ.im (n + (k + N)) * (δ : ℂ) ^ (n + (k + N))‖ ≤
      M * r ^ (k + N) * r ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ.le]
    calc ‖xiSliceCoeff ρ.im (n + (k + N))‖ * δ ^ (n + (k + N))
        ≤ M / R ^ (n + (k + N)) * δ ^ (n + (k + N)) :=
          mul_le_mul_of_nonneg_right (hcoef _) (pow_nonneg hδ.le _)
      _ = M * r ^ (k + N) * r ^ n := by
          rw [hr, div_pow, div_pow, pow_add, pow_add]
          field_simp
          ring
  have htailnorm := htail.norm_le_of_bounded hg hbound
  -- the head is at least `c_k δ^k`
  have hhead : (xiSliceCoeff ρ.im k).re * δ ^ k ≤
      (∑ i ∈ Finset.range (k + N), xiSliceCoeff ρ.im i * (δ : ℂ) ^ i).re := by
    rw [Complex.re_sum]
    have hterm : ∀ i ∈ Finset.range (k + N), 0 ≤ (xiSliceCoeff ρ.im i * (δ : ℂ) ^ i).re := by
      intro i hi
      rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
      exact mul_nonneg (hall i (Finset.mem_range.mp hi)) (pow_nonneg hδ.le _)
    have h0 := Finset.single_le_sum hterm (Finset.mem_range.mpr (by omega : k < k + N))
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal] at h0
    exact h0
  have hre : (∑ i ∈ Finset.range (k + N), xiSliceCoeff ρ.im i * (δ : ℂ) ^ i).re ≤
      M * r ^ (k + N) / (1 - r) := by
    have e : (∑ i ∈ Finset.range (k + N), xiSliceCoeff ρ.im i * (δ : ℂ) ^ i) =
        -(0 - ∑ i ∈ Finset.range (k + N), xiSliceCoeff ρ.im i * (δ : ℂ) ^ i) := by ring
    rw [e, Complex.neg_re]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans htailnorm)
  -- compare
  have hδk : 0 < δ ^ k := pow_pos hδ k
  have hscale : M * r ^ (k + N) / (1 - r) = (M / R ^ k * r ^ N / (1 - r)) * δ ^ k := by
    rw [hr, pow_add, div_pow]
    field_simp
  have := mul_lt_mul_of_pos_right hN hδk
  linarith

/-- **The reduced Xi function at a real zero.**  For a divisor point `ρ₀` with spectral point `a`,
`Ξ(z) = (z − a)^{m₀} h(z)` with `h(z) = Ξ(0) (−e^{z/a}/a)^{m₀} P(z)`, where `m₀` is the multiplicity
and `P` the canonical product over the copies away from `ρ₀`. -/
def xiReducedAt (ρ₀ : XiDivisorSupport) (z : ℂ) : ℂ :=
  XiC 0 * (-(1 / xiSpectralPointSupport ρ₀) * Complex.exp (z / xiSpectralPointSupport ρ₀)) ^
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ)) *
    xiCanonicalProductAway ρ₀ z

private theorem xiSpectralPointSupport_ne_zero (ρ₀ : XiDivisorSupport) :
    xiSpectralPointSupport ρ₀ ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr (xi_divisor_support_ne_half ρ₀)) (neg_ne_zero.mpr I_ne_zero)

/-- `Ξ(z) = (z − a)^{m₀} h(z)` globally. -/
theorem XiC_eq_pow_mul_xiReducedAt (ρ₀ : XiDivisorSupport) (z : ℂ) :
    XiC z = (z - xiSpectralPointSupport ρ₀) ^
        Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ)) * xiReducedAt ρ₀ z := by
  set a := xiSpectralPointSupport ρ₀ with ha
  have ha0 : a ≠ 0 := xiSpectralPointSupport_ne_zero ρ₀
  have hX : XiC z = XiC 0 * xiCanonicalProduct z := by
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct z
  have hE : weierstrassE1 (z / a) = (z - a) * (-(1 / a) * Complex.exp (z / a)) := by
    unfold weierstrassE1
    field_simp
    ring
  rw [hX, xiCanonicalProduct_factorization_at_support ρ₀ z, ← ha, hE, mul_pow, xiReducedAt, ← ha]
  ring

theorem xiReducedAt_analytic (ρ₀ : XiDivisorSupport) (z : ℂ) :
    AnalyticAt ℂ (xiReducedAt ρ₀) z := by
  have hP := xiCanonicalProductAway_analytic ρ₀ z (Set.mem_univ _)
  unfold xiReducedAt
  exact (analyticAt_const.mul ((analyticAt_const.mul (by fun_prop)).pow _)).mul hP

theorem xiReducedAt_ne_zero_at (ρ₀ : XiDivisorSupport) :
    xiReducedAt ρ₀ (xiSpectralPointSupport ρ₀) ≠ 0 := by
  have ha0 := xiSpectralPointSupport_ne_zero ρ₀
  unfold xiReducedAt
  refine mul_ne_zero (mul_ne_zero XiC_zero_ne (pow_ne_zero _ ?_))
    (xiCanonicalProductAway_ne_zero_at ρ₀)
  exact mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero ha0)) (Complex.exp_ne_zero _)

theorem xiSpectralPoint_ne_support_of_away {ρ₀ : XiDivisorSupport} (q : XiZeroCopyAway ρ₀) :
    xiSpectralPoint q.1 ≠ xiSpectralPointSupport ρ₀ := by
  intro h
  exact q.2 (xiSpectralPointSupport_injective (by simpa only [xiSpectralPoint_eq_support] using h))

/-- **The away product along a horizontal slice.**  For `a = xiSpectralPointSupport ρ₀`,
`P(a − ix) P(a + ix)/P(a)² = lim Π_{q away} (1 + x²/(z_q − a)²)`. -/
theorem tendsto_prod_away_one_add_sq_div (ρ₀ : XiDivisorSupport) (x : ℂ) :
    Tendsto (fun F : Finset (XiZeroCopyAway ρ₀) => ∏ q ∈ F,
        (1 + x ^ 2 / (xiSpectralPoint q.1 - xiSpectralPointSupport ρ₀) ^ 2)) atTop
      (𝓝 (xiCanonicalProductAway ρ₀ (xiSpectralPointSupport ρ₀ - I * x) *
          xiCanonicalProductAway ρ₀ (xiSpectralPointSupport ρ₀ + I * x) /
            xiCanonicalProductAway ρ₀ (xiSpectralPointSupport ρ₀) ^ 2)) := by
  set a := xiSpectralPointSupport ρ₀ with ha
  have hP : TendstoLocallyUniformlyOn
      (fun (F : Finset (XiZeroCopyAway ρ₀)) w => ∏ q ∈ F, weierstrassE1 (w / xiSpectralPoint q.1))
      (xiCanonicalProductAway ρ₀)
      atTop Set.univ :=
    canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      (fun q : XiZeroCopyAway ρ₀ => xiSpectralPoint q.1) (fun q => xiSpectralPoint_ne_zero q.1)
      (xiCanonicalProductAway_inv_sq_summable ρ₀)
  have hpt : ∀ w : ℂ, Tendsto (fun F : Finset (XiZeroCopyAway ρ₀) =>
      ∏ q ∈ F, weierstrassE1 (w / xiSpectralPoint q.1)) atTop
        (𝓝 (xiCanonicalProductAway ρ₀ w)) :=
    fun w => hP.tendsto_at (Set.mem_univ w)
  have hne : ∀ q : XiZeroCopyAway ρ₀, xiSpectralPoint q.1 ≠ a :=
    fun q => xiSpectralPoint_ne_support_of_away q
  have hE : ∀ q : XiZeroCopyAway ρ₀, weierstrassE1 (a / xiSpectralPoint q.1) ≠ 0 := by
    intro q
    unfold weierstrassE1
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    rw [sub_ne_zero, ne_comm, Ne, div_eq_one_iff_eq (xiSpectralPoint_ne_zero q.1)]
    exact fun h => hne q h.symm
  have hlim := ((hpt (a - I * x)).mul (hpt (a + I * x))).div ((hpt a).pow 2)
    (pow_ne_zero 2 (xiCanonicalProductAway_ne_zero_at ρ₀))
  refine hlim.congr fun F => ?_
  have hden : (∏ q ∈ F, weierstrassE1 (a / xiSpectralPoint q.1)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr fun q _ => hE q)
  simp only [Pi.div_apply]
  rw [div_eq_iff hden, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hpair := weierstrassE1_pair_eq a (-(I * x)) (xiSpectralPoint q.1)
    (xiSpectralPoint_ne_zero q.1) (hne q)
  rw [← sub_eq_add_neg, sub_neg_eq_add] at hpair
  rw [hpair]
  have hsq : (-(I * x)) ^ 2 = -x ^ 2 := by ring_nf; rw [I_sq]; ring
  rw [hsq]
  ring

/-- The finite-product bound on `|x| = 2δ`: at most `m` factors at `t ± iδ`, each at most `5`, and
the others at most `e^{4δ² S}` in total, `S` bounding the inverse-square mass of the copies with
property `p` away from `t ± iδ`. -/
theorem norm_prod_one_add_sq_div_le_of_mass {t δ : ℝ} (hδ : 0 < δ) {m : ℕ} {S : ℝ}
    {p : XiZeroCopy → Prop}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (t : ℂ) + (δ : ℂ) * I ∨ xiSpectralPoint q = (t : ℂ) - (δ : ℂ) * I) →
      F.card ≤ m)
    (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (t : ℂ) + (δ : ℂ) * I ∨
          xiSpectralPoint q = (t : ℂ) - (δ : ℂ) * I) ∧ p q) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ S)
    {x : ℂ} (hx : ‖x‖ = 2 * δ) (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, p q) :
    ‖∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2)‖ ≤ 5 ^ m * Real.exp (4 * δ ^ 2 * S) := by
  classical
  set own : XiZeroCopy → Prop := fun q =>
    xiSpectralPoint q = (t : ℂ) + (δ : ℂ) * I ∨ xiSpectralPoint q = (t : ℂ) - (δ : ℂ) * I
  rw [← Finset.prod_filter_mul_prod_filter_not F own, norm_mul, norm_prod, norm_prod]
  have hx2 : ‖x ^ 2‖ = 4 * δ ^ 2 := by rw [norm_pow, hx]; ring
  have h1 : ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤ 5 ^ m := by
    calc ∏ q ∈ F with own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
        ≤ ∏ q ∈ F with own q, (5 : ℝ) := by
          refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => ?_
          have hsq : (xiSpectralPoint q - t) ^ 2 = -((δ : ℂ) ^ 2) := by
            rcases (Finset.mem_filter.mp hq).2 with h | h <;> rw [h] <;> ring_nf <;>
              rw [I_sq] <;> ring
          rw [hsq]
          calc ‖1 + x ^ 2 / -((δ : ℂ) ^ 2)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / -((δ : ℂ) ^ 2)‖ :=
                norm_add_le _ _
            _ = 5 := by
                rw [norm_one, norm_div, norm_neg, hx2, norm_pow, Complex.norm_real,
                  Real.norm_eq_abs, abs_of_pos hδ]
                field_simp
                norm_num
      _ = 5 ^ (F.filter own).card := by rw [Finset.prod_const]
      _ ≤ 5 ^ m := pow_le_pow_right₀ (by norm_num)
          (hown _ fun q hq => (Finset.mem_filter.mp hq).2)
  have h2 : ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤
      Real.exp (4 * δ ^ 2 * S) := by
    calc ∏ q ∈ F with ¬ own q, ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
        ≤ ∏ q ∈ F with ¬ own q, Real.exp (4 * δ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) := by
          refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q _ => ?_
          calc ‖1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2‖
              ≤ ‖(1 : ℂ)‖ + ‖x ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := norm_add_le _ _
            _ = 4 * δ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) + 1 := by
                rw [norm_one, norm_div, hx2, norm_pow]; ring
            _ ≤ Real.exp (4 * δ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) :=
                Real.add_one_le_exp _
      _ = Real.exp (4 * δ ^ 2 * ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
          rw [Finset.mul_sum, Real.exp_sum]
      _ ≤ Real.exp (4 * δ ^ 2 * S) := by
          apply Real.exp_le_exp.mpr
          have hsum := hS (F.filter fun q => ¬ own q) fun q hq =>
            ⟨(Finset.mem_filter.mp hq).2, hF q (Finset.mem_filter.mp hq).1⟩
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun q _ => norm_nonneg _) (by positivity)

/-- **Bounded detection order at an ordinate carrying a critical zero.**  Let `ρ` be a zero of `ξ`
off the critical line, `γ = Im ρ`, `δ = |Re ρ − ½|`, and let `Ξ` vanish to order `k` at `γ`.
Suppose at most `m` zero copies sit at `γ ± iδ`, and the copies at neither `γ ± iδ` nor `γ` have
`Σ 1/|z − γ|² ≤ S`.  If `2 · 5^m · e^{4δ²S} < 2^N`, some slice coefficient `c_n(γ)` with
`n < 2k + N` has negative real part. -/
theorem exists_re_xiSliceCoeff_neg_of_offLine_mass_of_order {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) {k : ℕ} (hk : analyticOrderAt XiC (ρ.im : ℂ) = k) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) ∧
            xiSpectralPoint q ≠ (ρ.im : ℂ)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ} (hN : 2 * 5 ^ m * Real.exp (4 * |ρ.re - 1 / 2| ^ 2 * S) < 2 ^ N) :
    ∃ n < 2 * k + N, (xiSliceCoeff ρ.im n).re < 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  by_cases hΞ : XiC t = 0
  swap
  · -- no critical zero at the ordinate: the known bound
    obtain ⟨n, hn, hneg⟩ := exists_re_xiSliceCoeff_neg_of_offLine_mass hρ hne hΞ hown
      (fun F hF => hS F fun q hq => ⟨hF q hq, xiSpectralPoint_ne_ofReal hΞ q⟩) hN
    exact ⟨n, by omega, hneg⟩
  -- the divisor point at the ordinate
  obtain ⟨q₀, hq₀⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp hΞ
  set ρ₀ : XiDivisorSupport := q₀.1 with hρ₀
  have ha : xiSpectralPointSupport ρ₀ = (t : ℂ) := by rw [← hq₀, xiSpectralPoint_eq_support]
  have hkm : k = Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ)) := by
    have h1 := XiC_analyticOrderAt_support ρ₀
    rw [ha, hk] at h1
    exact_mod_cast h1
  -- the reduced function `h = Ξ(0) E^k P`
  set P : ℂ → ℂ := xiCanonicalProductAway ρ₀ with hP
  set E : ℂ → ℂ := fun w => -(1 / (t : ℂ)) * Complex.exp (w / t) with hE
  set h : ℂ → ℂ := fun w => XiC 0 * E w ^ k * P w with hh
  have ht0 : (t : ℂ) ≠ 0 := by rw [← ha]; exact xiSpectralPointSupport_ne_zero ρ₀
  have hfac : ∀ z, XiC z = (z - t) ^ k * h z := fun z => by
    rw [XiC_eq_pow_mul_xiReducedAt ρ₀ z, xiReducedAt, ha, ← hkm]
  have hhan : AnalyticAt ℂ h t := by
    have hPa : AnalyticAt ℂ P t := xiCanonicalProductAway_analytic ρ₀ _ (Set.mem_univ _)
    have hEa : AnalyticAt ℂ E t := by simp only [hE]; fun_prop
    exact (analyticAt_const.mul (hEa.pow k)).mul hPa
  have hP0 : P t ≠ 0 := by rw [hP, ← ha]; exact xiCanonicalProductAway_ne_zero_at ρ₀
  have hE0 : ∀ w, E w ≠ 0 := fun w =>
    mul_ne_zero (neg_ne_zero.mpr (one_div_ne_zero ht0)) (Complex.exp_ne_zero _)
  have hh0 : h t ≠ 0 := mul_ne_zero (mul_ne_zero XiC_zero_ne (pow_ne_zero _ (hE0 _))) hP0
  obtain ⟨-, hc, hcpos⟩ :=
    xiSliceCoeff_lowest_of_factor hhan hh0 (Eventually.of_forall hfac)
  set c : ℂ := xiSliceCoeff t (2 * k) with hcdef
  have hcre : 0 < c.re := (Complex.lt_def.mp hcpos).1
  have hcnorm : ‖h t * h t‖ = c.re := by
    rw [← hc]
    have hcim : c.im = 0 := ((Complex.lt_def.mp hcpos).2).symm
    have hreal : c = (c.re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hcim)
    conv_lhs => rw [hreal]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcre]
  -- the slice through the away product
  set Q : ℂ → ℂ := fun x => P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x) / P t ^ 2 with hQ
  have hslice : ∀ x : ℂ, xiSliceProduct t x = x ^ (2 * k) * (h t * h t * Q x) := by
    intro x
    rw [xiSliceProduct_eq_XiC_mul, hfac, hfac, neg_I_mul_pow_mul_I_mul_pow_sub]
    congr 1
    have hEE : E ((t : ℂ) - I * x) * E ((t : ℂ) + I * x) = E t * E t := by
      simp only [hE]
      have hexp : Complex.exp (((t : ℂ) - I * x) / t) * Complex.exp (((t : ℂ) + I * x) / t) =
          Complex.exp ((t : ℂ) / t) * Complex.exp ((t : ℂ) / t) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        ring
      calc -(1 / (t : ℂ)) * Complex.exp (((t : ℂ) - I * x) / t) *
            (-(1 / (t : ℂ)) * Complex.exp (((t : ℂ) + I * x) / t))
          = (1 / (t : ℂ)) ^ 2 * (Complex.exp (((t : ℂ) - I * x) / t) *
              Complex.exp (((t : ℂ) + I * x) / t)) := by ring
        _ = _ := by rw [hexp]; ring
    have hP2 : P t ^ 2 ≠ 0 := pow_ne_zero 2 hP0
    calc h ((t : ℂ) - I * x) * h ((t : ℂ) + I * x)
        = XiC 0 ^ 2 * (E ((t : ℂ) - I * x) * E ((t : ℂ) + I * x)) ^ k *
            (P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x)) := by
          simp only [hh]
          rw [mul_pow (E ((t : ℂ) - I * x)) (E ((t : ℂ) + I * x)) k]
          ring
      _ = XiC 0 ^ 2 * (E t * E t) ^ k * (P ((t : ℂ) - I * x) * P ((t : ℂ) + I * x)) := by
          rw [hEE]
      _ = h t * h t * Q x := by
          simp only [hh, hQ]
          rw [mul_pow (E t) (E t) k]
          field_simp
  -- the bound on the circle `|x| = 2δ`
  set B : ℝ := 5 ^ m * Real.exp (4 * δ ^ 2 * S) with hB
  have hQB : ∀ x : ℂ, ‖x‖ = 2 * δ → ‖Q x‖ ≤ B := by
    intro x hx
    have hlim := (tendsto_prod_away_one_add_sq_div ρ₀ x).norm
    rw [ha] at hlim
    refine le_of_tendsto hlim (Eventually.of_forall fun F => ?_)
    have hmap : ∏ q ∈ F, (1 + x ^ 2 / (xiSpectralPoint q.1 - t) ^ 2) =
        ∏ q ∈ F.map (Function.Embedding.subtype _),
          (1 + x ^ 2 / (xiSpectralPoint q - t) ^ 2) := by
      rw [Finset.prod_map]; rfl
    rw [hmap]
    refine norm_prod_one_add_sq_div_le_of_mass hδ hown hS hx _ fun q hq => ?_
    obtain ⟨q', -, rfl⟩ := Finset.mem_map.mp hq
    rw [← ha]
    exact xiSpectralPoint_ne_support_of_away q'
  have hM : ∀ x ∈ sphere (0 : ℂ) (2 * δ), ‖xiSliceProduct t x‖ ≤ (2 * δ) ^ (2 * k) * c.re * B := by
    intro x hx
    have hx' : ‖x‖ = 2 * δ := mem_sphere_zero_iff_norm.mp hx
    rw [hslice, norm_mul, norm_mul, norm_pow, hx', hcnorm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hQB x hx') hcre.le)
      (by positivity)
  -- the shifted detection bound at `R = 2δ`
  obtain ⟨n, hn, hneg⟩ := exists_re_xiSliceCoeff_neg_of_shifted_tail_lt hρ hδ (R := 2 * δ)
    (by linarith) hM (2 * k) (N := N) (by
      rw [← hδdef]
      have hhalf : δ / (2 * δ) = 1 / 2 := by field_simp
      rw [hhalf]
      have h2N : (0 : ℝ) < 2 ^ N := by positivity
      have h2δ : (0 : ℝ) < (2 * δ) ^ (2 * k) := by positivity
      have e : (2 * δ) ^ (2 * k) * c.re * B / (2 * δ) ^ (2 * k) * (1 / 2) ^ N / (1 - 1 / 2) =
          (2 * B / 2 ^ N) * c.re := by
        rw [one_div_pow]; field_simp; ring
      rw [e]
      have hB2 : 2 * B / 2 ^ N < 1 := by
        rw [div_lt_one h2N, hB]
        simpa [mul_assoc] using hN
      nlinarith)
  exact ⟨n, hn, hneg⟩

end

end RHTower
