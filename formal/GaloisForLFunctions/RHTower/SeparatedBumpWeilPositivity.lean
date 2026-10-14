import GaloisForLFunctions.RHTower.SeparatedBumpPrimeBlindPositivity

/-!
# Weil positivity for separated narrow bumps below the pole scale

Fix a real `C²` bump `φ` supported in `[−δ/2, δ/2]`, real amplitudes `a_j` and `s`-separated
centres `x_j` (`j < N`), and put `f(u) = Σ_j a_j φ(u − x_j)` (`bumpSum`).  No condition relates the
centres to the logarithms of the integers.

**Theorem** (`exists_weilPositive_bumpSum`).  For every separation `s > 0` and every `0 < κ < 2`
there is `δ₀ > 0` such that, for all `0 < δ < δ₀`, every such configuration of span
`max |x_i − x_j| ≤ κ log(1/δ)` satisfies Weil's inequality with the von Mangoldt weights:

`Re W_Λ(f ⋆ f̃) = W_∞(f ⋆ f̃) − Σ_{n ≥ 2} Λ(n) n^{−½} ((f ⋆ f̃)(log n) + (f ⋆ f̃)(−log n)) ≥ 0`.

The support length of `f` is unbounded as `δ → 0`, and the amplitudes have arbitrary signs.

Proof.
* *Lévy gain.*  `W_∞(f ⋆ f̃) ≥ (A(0) + e^{−s/2} log((s−δ)/δ))‖f‖² − |2P|`
  (`levy_sub_abs_pole_le_weilArchRe`).
* *Pole.*  `|2P| ≤ 2e^{δ/2} e^{D/2} δ N ‖f‖²` for span `D` (`abs_pole_le_of_exp_le`).  At
  `D = κ log(1/δ)` this is `O(δ^{1−κ/2} log(1/δ))‖f‖²`.
* *Primes.*  `(f ⋆ f̃)(y) = Σ_{i,j} a_i a_j ∫ φ(u − x_i) φ(u − y − x_j)`, and the `(i,j)` term
  vanishes unless `|y − (x_i − x_j)| ≤ δ`.  So the prime sum is at most
  `‖φ‖² Σ_{i,j} |a_i a_j| K_{ij}` with `K_{ij} = ν(x_i − x_j) + ν(x_j − x_i)`, where the node weight
  `ν(d) = Σ_{e^{d−δ} ≤ n ≤ e^{d+δ}} Λ(n)/√n` (`nodeWeight`) is at most
  `6δ(d+1)e^{d/2} + 8e^{−d/4}` (`nodeWeight_le`).  A Schur test (`sum_abs_mul_le_of_rowSum`) and
  packing (`card_le_one_add_div_of_separated`) bound the row sums of `K` by
  `N · 6δ(D+1)e^{D/2} + 8(2 + 2M/s) + 8N e^{−M/4}` (`sum_pairKernel_le`).  With `M` a small
  multiple of `log(1/δ)` this is a quarter of the Lévy gain plus `o(1)`.

**Theorem** (`exists_nonneg_of_blind_bumpSum`).  If the bump is nonnegative and positive on
`(−δ/2, δ/2)` and the amplitudes are nonzero, prime-blindness of `f ⋆ f̃` alone (however it
arises) forces span `< log(2/δ)` (`abs_sub_lt_log_of_blind`): at the extreme difference only the
extreme pair contributes, so cancellation cannot hide it, and beyond `log(2/δ)` the nodes `log n`
are `δ`-dense.  Hence the pole and archimedean energy of every such blind test is nonnegative.

Reading: the Lévy gain `Θ(log 1/δ)` beats every trivial bound on primes and pole exactly up to the
span `2 log(1/δ)`, where the pole term `e^{D/2}δ` reaches size one.  Beyond it the prime sum must
cancel against the pole, which is the prime number theorem in intervals of relative length `δ` at
height `e^D` with error `o(e^{D/2})`.
-/

open Complex MeasureTheory Set Filter Topology Finsupp
open Zeta23

noncomputable section

namespace RHTower.SeparatedBump

variable {N : ℕ}

/-! ## Products of translates -/

theorem integrable_translate_mul_translate {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (c c' : ℝ) :
    Integrable fun u => φ (u - c) * φ (u - c') := by
  have h1 : Continuous fun u => φ (u - c) * φ (u - c') := by
    have := hφ.continuous; fun_prop
  refine h1.integrable_of_hasCompactSupport
    (hasCompactSupport_of_abs_gt (R := |c| + δ / 2) fun u hu => ?_)
  show φ (u - c) * φ (u - c') = 0
  rw [translate_eq_zero hφs c hu, zero_mul]

theorem abs_integral_translate_mul_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (c c' : ℝ) :
    |∫ u, φ (u - c) * φ (u - c')| ≤ ∫ u, φ u ^ 2 := by
  have hsq : ∀ c : ℝ, Integrable fun u => φ (u - c) ^ 2 := fun c => by
    simpa [sq] using integrable_translate_mul_translate hφ hφs c c
  have htr : ∀ c : ℝ, ∫ u, φ (u - c) ^ 2 = ∫ u, φ u ^ 2 := fun c =>
    integral_sub_right_eq_self (fun u => φ u ^ 2) c
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ u, |φ (u - c) * φ (u - c')| ≤ ∫ u, (φ (u - c) ^ 2 / 2 + φ (u - c') ^ 2 / 2) :=
        integral_mono (integrable_translate_mul_translate hφ hφs c c').abs
          (((hsq c).div_const 2).add ((hsq c').div_const 2)) fun u => by
            rw [abs_mul]
            nlinarith [sq_nonneg (|φ (u - c)| - |φ (u - c')|), sq_abs (φ (u - c)),
              sq_abs (φ (u - c'))]
    _ = ∫ u, φ u ^ 2 := by
        rw [integral_add ((hsq c).div_const 2) ((hsq c').div_const 2), integral_div,
          integral_div, htr, htr]
        ring

/-! ## The autocorrelation of a configuration -/

theorem integral_bumpSum_mul_bumpSum_sub {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) (y : ℝ) :
    ∫ u, bumpSum φ a x u * bumpSum φ a x (u - y) =
      ∑ i, ∑ j, a i * a j * ∫ u, φ (u - x i) * φ (u - (y + x j)) := by
  have e : ∀ u, bumpSum φ a x u * bumpSum φ a x (u - y) =
      ∑ i, ∑ j, a i * a j * (φ (u - x i) * φ (u - (y + x j))) := fun u => by
    unfold bumpSum
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show u - y - x j = u - (y + x j) by ring]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_translate_mul_translate hφ hφs _ _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (integrable_translate_mul_translate hφ hφs _ _).const_mul _]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- **Only aligned pairs contribute.**  The autocorrelation at lag `y` is at most `‖φ‖²` times the
sum of `|a_i a_j|` over the pairs with `|y − (x_i − x_j)| ≤ δ`. -/
theorem abs_integral_bumpSum_mul_bumpSum_sub_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) (y : ℝ) :
    |∫ u, bumpSum φ a x u * bumpSum φ a x (u - y)| ≤
      (∫ u, φ u ^ 2) * ∑ i, ∑ j, |a i| * |a j| *
        (if |y - (x i - x j)| ≤ δ then 1 else 0) := by
  rw [integral_bumpSum_mul_bumpSum_sub hφ hφs, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul]
  split_ifs with h
  · have := abs_integral_translate_mul_le hφ hφs (x i) (y + x j)
    rw [mul_one]
    calc |a i| * |a j| * |∫ u, φ (u - x i) * φ (u - (y + x j))|
        ≤ |a i| * |a j| * ∫ u, φ u ^ 2 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = (∫ u, φ u ^ 2) * (|a i| * |a j|) := by ring
  · have hfar : δ < |x i - (y + x j)| := by
      rw [show x i - (y + x j) = -(y - (x i - x j)) by ring, abs_neg]
      exact lt_of_not_ge h
    have hz : (fun u => φ (u - x i) * φ (u - (y + x j))) = fun _ => 0 :=
      funext fun u => mul_translate_eq_zero hφs hfar u
    simp [hz]

theorem logValue_bumpSum (φ : ℝ → ℝ) (a x : Fin N → ℝ) (n : ℕ) :
    WeilOneSided.logValue (fun u => (bumpSum φ a x u : ℂ)) n =
      ((∫ u, bumpSum φ a x u * bumpSum φ a x (u - Real.log n)) +
        ∫ u, bumpSum φ a x u * bumpSum φ a x (u - -Real.log n)) / Real.sqrt n := by
  unfold WeilOneSided.logValue
  rw [weilTest_ofReal_apply, weilTest_ofReal_apply, integral_complex_ofReal,
    integral_complex_ofReal]
  simp

/-! ## Blindness confines the span -/

/-- Two overlapping translates of a positive bump have positive correlation. -/
theorem integral_translate_mul_pos {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφpos : ∀ u, |u| < δ / 2 → 0 < φ u) {c c' : ℝ} (hcc : |c' - c| < δ) :
    0 < ∫ u, φ (u - c) * φ (u - c') := by
  set α := max c c' - δ / 2 with hα
  set β := min c c' + δ / 2 with hβ
  have hαβ : α < β := by
    rcases le_total c c' with h | h
    · rw [hα, hβ, max_eq_right h, min_eq_left h]
      rw [abs_of_nonneg (by linarith)] at hcc
      linarith
    · rw [hα, hβ, max_eq_left h, min_eq_right h]
      rw [abs_of_nonpos (by linarith)] at hcc
      linarith
  have hint := integrable_translate_mul_translate hφ hφs c c'
  have hpos : ∀ u ∈ Set.Ioo α β, 0 < φ (u - c) * φ (u - c') := by
    intro u hu
    have h1 := le_max_left c c'
    have h2 := le_max_right c c'
    have h3 := min_le_left c c'
    have h4 := min_le_right c c'
    obtain ⟨hu1, hu2⟩ := hu
    refine mul_pos (hφpos _ ?_) (hφpos _ ?_) <;> rw [abs_lt] <;> constructor <;> linarith
  have h1 : 0 < ∫ u in α..β, φ (u - c) * φ (u - c') :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint.intervalIntegrable hpos hαβ
  rw [intervalIntegral.integral_of_le hαβ.le] at h1
  exact h1.trans_le (setIntegral_le_integral hint
    (Eventually.of_forall fun u => mul_nonneg (hφ0 _) (hφ0 _)))

/-- **Blindness confines the span.**  Let `φ ≥ 0` be positive on `(−δ/2, δ/2)`, every amplitude
nonzero and the centres `s`-separated with `s > 2δ`.  If `f ⋆ f̃` vanishes at every `log n`,
`n ≥ 2`, then every difference of centres is below `log(2/δ)`: at the extreme difference only the
extreme pair contributes, so no cancellation can hide it, and beyond `log(2/δ)` the nodes `log n`
are `δ`-dense. -/
theorem abs_sub_lt_log_of_blind {φ : ℝ → ℝ} {δ s : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφpos : ∀ u, |u| < δ / 2 → 0 < φ u) (hδ : 0 < δ) (hδ1 : δ < 1) (hδs : 2 * δ < s)
    {a x : Fin N → ℝ} (ha : ∀ j, a j ≠ 0) (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ u, bumpSum φ a x u * bumpSum φ a x (u - Real.log n) = 0)
    (i j : Fin N) : |x i - x j| < Real.log (2 / δ) := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ x hne
  obtain ⟨q, -, hq⟩ := Finset.exists_min_image Finset.univ x hne
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hD : x p - x q < Real.log (2 / δ) := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨n, hn, hclose⟩ := exists_log_near hδ hδ1 hcon
    have hz := hblind n hn
    rw [integral_bumpSum_mul_bumpSum_sub hφ hφs] at hz
    have hlow : x p - x q - δ < Real.log n := by
      have := (abs_lt.mp hclose).2
      linarith
    have hother : ∀ k l : Fin N, (k, l) ≠ (p, q) →
        ∫ u, φ (u - x k) * φ (u - (Real.log n + x l)) = 0 := by
      intro k l hkl
      have hdiff : x k - x l ≤ x p - x q - s := by
        by_cases hk : k = p
        · subst hk
          have hl : l ≠ q := fun h => hkl (by rw [h])
          have h1 := hsep l q hl
          have hql := hq l (Finset.mem_univ _)
          rw [abs_of_nonneg (by linarith)] at h1
          linarith
        · have h1 := hsep k p hk
          have hkp := hp k (Finset.mem_univ _)
          rw [abs_of_nonpos (by linarith)] at h1
          have hql := hq l (Finset.mem_univ _)
          linarith
      have hfar : δ < |x k - (Real.log n + x l)| := by
        rw [show x k - (Real.log n + x l) = -(Real.log n - (x k - x l)) by ring, abs_neg,
          abs_of_pos (by linarith)]
        linarith
      have hz' : (fun u => φ (u - x k) * φ (u - (Real.log n + x l))) = fun _ => 0 :=
        funext fun u => mul_translate_eq_zero hφs hfar u
      rw [hz', integral_zero]
    rw [Finset.sum_eq_single p (fun k _ hk => Finset.sum_eq_zero fun l _ => by
        rw [hother k l (fun h => hk (Prod.mk.inj h).1), mul_zero]) (by simp),
      Finset.sum_eq_single q (fun l _ hl => by
        rw [hother p l (fun h => hl (Prod.mk.inj h).2), mul_zero]) (by simp)] at hz
    have hpos : 0 < ∫ u, φ (u - x p) * φ (u - (Real.log n + x q)) :=
      integral_translate_mul_pos hφ hφs hφ0 hφpos (by
        rw [show Real.log n + x q - x p = -(x p - x q - Real.log n) by ring, abs_neg]
        exact hclose)
    exact mul_ne_zero (mul_ne_zero (ha p) (ha q)) hpos.ne' hz
  have hi1 := hp i (Finset.mem_univ _)
  have hi2 := hq i (Finset.mem_univ _)
  have hj1 := hp j (Finset.mem_univ _)
  have hj2 := hq j (Finset.mem_univ _)
  rw [abs_lt]
  constructor <;> linarith

/-- **Prime-blind positivity for separated positive narrow bumps.**  For every separation
`s > 0` there is `δ₀ > 0` such that for `0 < δ < δ₀` every configuration of bumps of width `δ`
with a bump `φ ≥ 0` positive on `(−δ/2, δ/2)`, nonzero amplitudes and `s`-separated centres,
whose autocorrelation vanishes at every `log n`, `n ≥ 2`, has nonnegative pole and archimedean
energy.  No condition on how the blindness arises is assumed. -/
theorem exists_nonneg_of_blind_bumpSum {s : ℝ} (hs : 0 < s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (N : ℕ) (φ : ℝ → ℝ) (a x : Fin N → ℝ),
      ContDiff ℝ 2 φ → (∀ u, δ / 2 < |u| → φ u = 0) → (∀ u, 0 ≤ φ u) →
      (∀ u, |u| < δ / 2 → 0 < φ u) → (∀ j, a j ≠ 0) →
      (∀ i j, i ≠ j → s ≤ |x i - x j|) →
      (∀ n : ℕ, 2 ≤ n →
        EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ))
          (Real.log n) = 0) →
      0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (bumpSum φ a x u : ℂ))
        (fun u => (bumpSum φ a x u : ℂ))) := by
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_le_weilArchRe_bumpSum hs
  refine ⟨min δ₀ (min (1 / 2) (s / 4)), lt_min hδ₀ (lt_min (by norm_num) (by positivity)),
    fun δ hδ hδlt N φ a x hφ hφs hφ0 hφpos ha hsep hblind => ?_⟩
  have hd0 : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hd1 : δ < 1 / 2 := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : δ < s / 4 := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_right _ _))
  have hblind' : ∀ n : ℕ, 2 ≤ n →
      ∫ u, bumpSum φ a x u * bumpSum φ a x (u - Real.log n) = 0 := fun n hn => by
    have h := hblind n hn
    rw [weilTest_ofReal_apply, integral_complex_ofReal] at h
    exact_mod_cast h
  exact hpos δ hδ hd0 N φ a x hφ hφs hsep
    (abs_sub_lt_log_of_blind hφ hφs hφ0 hφpos hδ (by linarith) (by linarith) ha hsep hblind')

/-! ## Node weights -/

/-- The node weight `Σ Λ(n)/√n` over `e^{d−δ} ≤ n ≤ e^{d+δ}`. -/
def nodeWeight (δ d : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc ⌈Real.exp (d - δ)⌉₊ ⌊Real.exp (d + δ)⌋₊,
    ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem nodeWeight_nonneg (δ d : ℝ) : 0 ≤ nodeWeight δ d :=
  Finset.sum_nonneg fun _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem nodeWeight_eq_zero {δ d : ℝ} (h : Real.exp (d + δ) < 2) : nodeWeight δ d = 0 := by
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hfl : ⌊Real.exp (d + δ)⌋₊ < 2 :=
    (Nat.floor_lt (Real.exp_pos _).le).mpr (by exact_mod_cast h)
  have h1 : n ≤ 1 := by omega
  interval_cases n <;> simp

/-- **Indicator sums are dominated by the node weight.** -/
theorem sum_indicator_le_nodeWeight (T : Finset ℕ) (δ d : ℝ) :
    ∑ n ∈ T, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      (if |Real.log n - d| ≤ δ then 1 else 0) ≤ nodeWeight δ d := by
  set F : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (if |Real.log n - d| ≤ δ then 1 else 0) with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (by split_ifs <;> norm_num)
  have hFle : ∀ n, F n ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := fun n => by
    have h0 := div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg n)
    simp only [hF]
    split_ifs <;> linarith
  have hsub : T.filter (fun n => F n ≠ 0) ⊆
      Finset.Icc ⌈Real.exp (d - δ)⌉₊ ⌊Real.exp (d + δ)⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hne := hn.2
    simp only [hF, ne_eq, mul_eq_zero, not_or, div_eq_zero_iff] at hne
    obtain ⟨⟨hΛ, -⟩, hind⟩ := hne
    have hcl : |Real.log n - d| ≤ δ := by
      by_contra hc
      exact hind (if_neg hc)
    have hn0 : n ≠ 0 := fun h => hΛ (by rw [h]; simp)
    have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [abs_le] at hcl
    rw [Finset.mem_Icc]
    constructor
    · refine Nat.ceil_le.mpr ?_
      calc Real.exp (d - δ) ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr (by linarith)
        _ = n := Real.exp_log hpos
    · refine Nat.le_floor ?_
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (d + δ) := Real.exp_le_exp.mpr (by linarith)
  calc ∑ n ∈ T, F n = ∑ n ∈ T.filter (fun n => F n ≠ 0), F n := (Finset.sum_filter_ne_zero T).symm
    _ ≤ ∑ n ∈ Finset.Icc ⌈Real.exp (d - δ)⌉₊ ⌊Real.exp (d + δ)⌋₊, F n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hF0 n
    _ ≤ nodeWeight δ d := Finset.sum_le_sum fun n _ => hFle n

/-- **The node weight above `δ`.**  `ν(d) ≤ (e^{d+δ} − e^{d−δ} + 1)(d + δ)e^{−(d−δ)/2}`. -/
theorem nodeWeight_le_card_mul {δ d : ℝ} (hδ : 0 ≤ δ) (hd : δ ≤ d) :
    nodeWeight δ d ≤ (Real.exp (d + δ) - Real.exp (d - δ) + 1) *
      ((d + δ) * Real.exp (-(d - δ) / 2)) := by
  set A := Real.exp (d - δ) with hA
  set B := Real.exp (d + δ) with hB
  have hA1 : 1 ≤ A := Real.one_le_exp (by linarith)
  have hAB : A ≤ B := Real.exp_le_exp.mpr (by linarith)
  have hterm : ∀ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤
      (d + δ) * Real.exp (-(d - δ) / 2) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnA : A ≤ n := Nat.ceil_le.mp hn.1
    have hnB : (n : ℝ) ≤ B := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (by positivity))
    have hpos : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ d + δ := by
      rw [← Real.log_exp (d + δ)]
      exact Real.log_le_log hpos hnB
    have hsq : Real.exp ((d - δ) / 2) ≤ Real.sqrt n := by
      rw [Real.exp_half]
      exact Real.sqrt_le_sqrt hnA
    have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hpos
    rw [div_le_iff₀ hsqpos]
    have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have he : Real.exp (-(d - δ) / 2) * Real.exp ((d - δ) / 2) = 1 := by
      rw [← Real.exp_add, show -(d - δ) / 2 + (d - δ) / 2 = 0 by ring, Real.exp_zero]
    have hdδ : 0 ≤ d + δ := by linarith
    have h1 : d + δ ≤ (d + δ) * Real.exp (-(d - δ) / 2) * Real.sqrt n := by
      calc d + δ = (d + δ) * (Real.exp (-(d - δ) / 2) * Real.exp ((d - δ) / 2)) := by
            rw [he, mul_one]
        _ ≤ (d + δ) * (Real.exp (-(d - δ) / 2) * Real.sqrt n) := by gcongr
        _ = (d + δ) * Real.exp (-(d - δ) / 2) * Real.sqrt n := by ring
    linarith
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  have hcard : ((Finset.Icc ⌈A⌉₊ ⌊B⌋₊).card : ℝ) ≤ B - A + 1 := by
    rw [Nat.card_Icc]
    by_cases hle : ⌈A⌉₊ ≤ ⌊B⌋₊ + 1
    · rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
      have h1 : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by positivity)
      have h2 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
      linarith
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
      linarith
  have hb0 : 0 ≤ (d + δ) * Real.exp (-(d - δ) / 2) :=
    mul_nonneg (by linarith) (Real.exp_pos _).le
  calc nodeWeight δ d ≤ ((Finset.Icc ⌈A⌉₊ ⌊B⌋₊).card : ℝ) *
        ((d + δ) * Real.exp (-(d - δ) / 2)) := hsum
    _ ≤ (B - A + 1) * ((d + δ) * Real.exp (-(d - δ) / 2)) :=
        mul_le_mul_of_nonneg_right hcard hb0

/-- **The node weight bound.**  For `0 ≤ δ ≤ ½` and `d ≥ δ`,
`ν(d) ≤ 6δ(d + 1)e^{d/2} + 8e^{−d/4}`. -/
theorem nodeWeight_le {δ d : ℝ} (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hd : δ ≤ d) :
    nodeWeight δ d ≤ 6 * δ * (d + 1) * Real.exp (d / 2) + 8 * Real.exp (-(d / 4)) := by
  refine (nodeWeight_le_card_mul hδ hd).trans ?_
  -- the length of the window
  have hwin : Real.exp (d + δ) - Real.exp (d - δ) ≤ 2 * δ * Real.exp (d + δ) := by
    have h := Real.add_one_le_exp (-(2 * δ))
    have e : Real.exp (d - δ) = Real.exp (d + δ) * Real.exp (-(2 * δ)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos (d + δ)]
  have hexp1 : Real.exp (d + δ) * Real.exp (-(d - δ) / 2) =
      Real.exp (d / 2) * Real.exp (3 * δ / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hexp2 : Real.exp (-(d - δ) / 2) = Real.exp (-(d / 2)) * Real.exp (δ / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h34 : Real.exp (3 * δ / 2) ≤ 3 := by
    have := Real.exp_one_lt_d9
    have : Real.exp (3 * δ / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h14 : Real.exp (δ / 2) ≤ 2 := by
    have := Real.log_two_gt_d9
    calc Real.exp (δ / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hquart : (d + 1) * Real.exp (-(d / 2)) ≤ 4 * Real.exp (-(d / 4)) := by
    have h := Real.add_one_le_exp (d / 4)
    have e : Real.exp (-(d / 4)) = Real.exp (d / 4) * Real.exp (-(d / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith [Real.exp_pos (-(d / 2))]
  have hd0 : 0 ≤ d := le_trans hδ hd
  have hE := Real.exp_pos (-(d - δ) / 2)
  have hEd := Real.exp_pos (d / 2)
  have hEm := Real.exp_pos (-(d / 2))
  calc (Real.exp (d + δ) - Real.exp (d - δ) + 1) * ((d + δ) * Real.exp (-(d - δ) / 2))
      ≤ (2 * δ * Real.exp (d + δ) + 1) * ((d + 1) * Real.exp (-(d - δ) / 2)) := by
        gcongr
        nlinarith
    _ = 2 * δ * (d + 1) * (Real.exp (d + δ) * Real.exp (-(d - δ) / 2)) +
          (d + 1) * Real.exp (-(d - δ) / 2) := by ring
    _ = 2 * δ * (d + 1) * (Real.exp (d / 2) * Real.exp (3 * δ / 2)) +
          (d + 1) * Real.exp (-(d / 2)) * Real.exp (δ / 2) := by
        rw [hexp1, hexp2]; ring
    _ ≤ 2 * δ * (d + 1) * (Real.exp (d / 2) * 3) + 4 * Real.exp (-(d / 4)) * 2 := by
        gcongr
    _ = 6 * δ * (d + 1) * Real.exp (d / 2) + 8 * Real.exp (-(d / 4)) := by ring

/-! ## A Schur test -/

/-- **Schur test.**  For a symmetric nonnegative kernel with row sums at most `R`,
`Σ_{i,j} |a_i| |a_j| K_{ij} ≤ R Σ a_i²`. -/
theorem sum_abs_mul_le_of_rowSum {K : Fin N → Fin N → ℝ} (hK0 : ∀ i j, 0 ≤ K i j)
    (hKs : ∀ i j, K i j = K j i) {R : ℝ} (hR : ∀ i, ∑ j, K i j ≤ R) (a : Fin N → ℝ) :
    ∑ i, ∑ j, |a i| * |a j| * K i j ≤ R * ∑ i, a i ^ 2 := by
  have h1 : ∀ i j, |a i| * |a j| * K i j ≤ (a i ^ 2 / 2) * K i j + (a j ^ 2 / 2) * K j i :=
    fun i j => by
      have := two_mul_le_add_sq |a i| |a j|
      rw [sq_abs, sq_abs] at this
      rw [← hKs i j]
      nlinarith [hK0 i j]
  have h2 : ∑ i, ∑ j, (a j ^ 2 / 2) * K j i = ∑ i, ∑ j, (a i ^ 2 / 2) * K i j :=
    Finset.sum_comm
  calc ∑ i, ∑ j, |a i| * |a j| * K i j
      ≤ ∑ i, ∑ j, ((a i ^ 2 / 2) * K i j + (a j ^ 2 / 2) * K j i) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ i, a i ^ 2 * ∑ j, K i j := by
        simp_rw [Finset.sum_add_distrib]
        rw [h2, ← two_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, a i ^ 2 * R :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hR i) (sq_nonneg _)
    _ = R * ∑ i, a i ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-! ## The prime sum -/

/-- The pair kernel `K_{ij} = ν(x_i − x_j) + ν(x_j − x_i)`. -/
def pairKernel (δ : ℝ) (x : Fin N → ℝ) (i j : Fin N) : ℝ :=
  nodeWeight δ (x i - x j) + nodeWeight δ (x j - x i)

theorem pairKernel_nonneg (δ : ℝ) (x : Fin N → ℝ) (i j : Fin N) : 0 ≤ pairKernel δ x i j :=
  add_nonneg (nodeWeight_nonneg _ _) (nodeWeight_nonneg _ _)

theorem pairKernel_symm (δ : ℝ) (x : Fin N → ℝ) (i j : Fin N) :
    pairKernel δ x i j = pairKernel δ x j i := add_comm _ _

/-- The prime majorant at a single integer. -/
def primeMajorant (δ : ℝ) (φ : ℝ → ℝ) (a x : Fin N → ℝ) (n : ℕ) : ℝ :=
  (∫ u, φ u ^ 2) * ∑ i, ∑ k, |a i| * |a k| *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (if |Real.log n - (x i - x k)| ≤ δ then 1 else 0) +
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (if |Real.log n - (x k - x i)| ≤ δ then 1 else 0))

theorem vonMangoldt_mul_abs_logValue_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n *
        |WeilOneSided.logValue (fun u => (bumpSum φ a x u : ℂ)) n| ≤
      primeMajorant δ φ a x n := by
  rw [logValue_bumpSum]
  have h1 := abs_integral_bumpSum_mul_bumpSum_sub_le hφ hφs a x (Real.log n)
  have h2 := abs_integral_bumpSum_mul_bumpSum_sub_le hφ hφs a x (-Real.log n)
  have e2 : ∀ i k : Fin N, |-Real.log n - (x i - x k)| = |Real.log n - (x k - x i)| := fun i k => by
    rw [show -Real.log n - (x i - x k) = -(Real.log n - (x k - x i)) by ring, abs_neg]
  simp_rw [e2] at h2
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hsq := Real.sqrt_nonneg n
  rw [abs_div, abs_of_nonneg hsq]
  have htri := abs_add_le (∫ u, bumpSum φ a x u * bumpSum φ a x (u - Real.log n))
    (∫ u, bumpSum φ a x u * bumpSum φ a x (u - -Real.log n))
  have hexp : primeMajorant δ φ a x n = ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      ((∫ u, φ u ^ 2) * ∑ i, ∑ k, |a i| * |a k| *
          (if |Real.log n - (x i - x k)| ≤ δ then 1 else 0) +
        (∫ u, φ u ^ 2) * ∑ i, ∑ k, |a i| * |a k| *
          (if |Real.log n - (x k - x i)| ≤ δ then 1 else 0)) := by
    unfold primeMajorant
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hexp, mul_div_assoc', mul_comm (ArithmeticFunction.vonMangoldt n), mul_div_assoc,
    mul_comm _ (ArithmeticFunction.vonMangoldt n / Real.sqrt n)]
  exact mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 h2)) (div_nonneg hΛ hsq)

theorem sum_primeMajorant_le (δ : ℝ) (φ : ℝ → ℝ) (a x : Fin N → ℝ) (T : Finset ℕ) :
    ∑ n ∈ T, primeMajorant δ φ a x n ≤
      (∫ u, φ u ^ 2) * ∑ i, ∑ k, |a i| * |a k| * pairKernel δ x i k := by
  have hφ0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  unfold primeMajorant
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hφ0
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
  · exact sum_indicator_le_nodeWeight T δ (x i - x k)
  · exact sum_indicator_le_nodeWeight T δ (x k - x i)

/-- **The prime sum of a configuration** is at most `‖φ‖² Σ_{i,j} |a_i a_j| K_{ij}`. -/
theorem abs_linearCombination_vonMangoldt_le {φ : ℝ → ℝ} {δ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (a x : Fin N → ℝ) (F : WeilOneSided.WeilTestFn)
    (hF : F.1 = fun u => (bumpSum φ a x u : ℂ)) :
    |linearCombination ℝ (fun j : WeilOneSided.LogIndex => ArithmeticFunction.vonMangoldt j)
        (WeilOneSided.logVector F)| ≤
      (∫ u, φ u ^ 2) * ∑ i, ∑ k, |a i| * |a k| * pairKernel δ x i k := by
  set T := (WeilOneSided.logVector F).support
  rw [linearCombination_apply]
  unfold Finsupp.sum
  simp_rw [WeilOneSided.logVector_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hj : ∀ j ∈ T, |WeilOneSided.logValue F.1 j * ArithmeticFunction.vonMangoldt j| ≤
      primeMajorant δ φ a x j := fun j _ => by
    rw [abs_mul, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := j)), mul_comm, hF]
    exact vonMangoldt_mul_abs_logValue_le hφ hφs a x j
  refine (Finset.sum_le_sum hj).trans ?_
  have hmap : ∑ j ∈ T, primeMajorant δ φ a x j =
      ∑ n ∈ T.map (Function.Embedding.subtype _), primeMajorant δ φ a x n :=
    (Finset.sum_map T (Function.Embedding.subtype _) (primeMajorant δ φ a x)).symm
  rw [hmap]
  exact sum_primeMajorant_le δ φ a x _

/-! ## Row sums -/

theorem nodeWeight_neg_eq_zero {δ d s : ℝ} (hδs : δ < s) (hd : d ≤ -s) : nodeWeight δ d = 0 := by
  refine nodeWeight_eq_zero ?_
  have : Real.exp (d + δ) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- **Row sums of the pair kernel.**  For an `s`-separated configuration of span `≤ D` and any
`M ≥ 0`, every row sum of `K` is at most
`N · 6δ(D + 1)e^{D/2} + 8(2 + 2M/s) + 8N e^{−M/4}`. -/
theorem sum_pairKernel_le {δ s D M : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδs : δ < s)
    (hM : 0 ≤ M) {x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hspan : ∀ i j, |x i - x j| ≤ D) (i : Fin N) :
    ∑ j, pairKernel δ x i j ≤ N * (6 * δ * (D + 1) * Real.exp (D / 2)) +
      8 * (2 + 2 * M / s) + 8 * N * Real.exp (-(M / 4)) := by
  have hs : 0 < s := hδ.trans hδs
  have hD : 0 ≤ D := (abs_nonneg _).trans (hspan i i)
  set c : ℝ := 6 * δ * (D + 1) * Real.exp (D / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hexpδ : Real.exp (0 + δ) < 2 := by
    rw [zero_add]
    have := Real.log_two_gt_d9
    calc Real.exp δ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  -- one entry
  have hentry : ∀ j, pairKernel δ x i j ≤
      c + 8 * ((if |x i - x j| ≤ M then 1 else 0) + Real.exp (-(M / 4))) := by
    intro j
    have hEM := Real.exp_pos (-(M / 4))
    have hind : (0 : ℝ) ≤ if |x i - x j| ≤ M then 1 else 0 := by split_ifs <;> norm_num
    by_cases hij : i = j
    · subst hij
      have h0 : pairKernel δ x i i = 0 := by
        unfold pairKernel
        rw [sub_self, nodeWeight_eq_zero hexpδ, add_zero]
      rw [h0]
      linarith
    · have ht := hsep i j hij
      -- the bound at the positive distance
      have hnw : ∀ t : ℝ, t = |x i - x j| → nodeWeight δ t ≤
          c + 8 * ((if |x i - x j| ≤ M then 1 else 0) + Real.exp (-(M / 4))) := by
        intro t ht'
        have hts : s ≤ t := ht' ▸ ht
        have htD : t ≤ D := ht' ▸ hspan i j
        refine (nodeWeight_le hδ.le hδ2 (by linarith)).trans ?_
        have h1 : 6 * δ * (t + 1) * Real.exp (t / 2) ≤ c := by
          rw [hc]
          gcongr
        have h2 : Real.exp (-(t / 4)) ≤ (if |x i - x j| ≤ M then 1 else 0) +
            Real.exp (-(M / 4)) := by
          split_ifs with hM'
          · have : Real.exp (-(t / 4)) ≤ 1 := by
              rw [← Real.exp_zero]
              exact Real.exp_le_exp.mpr (by linarith)
            linarith
          · rw [zero_add]
            refine Real.exp_le_exp.mpr ?_
            rw [← ht'] at hM'
            linarith [not_le.mp hM']
        linarith
      unfold pairKernel
      rcases le_total 0 (x i - x j) with hpos | hneg
      · rw [nodeWeight_neg_eq_zero (d := x j - x i) hδs (by
            rw [abs_of_nonneg hpos] at ht
            linarith), add_zero]
        exact hnw _ (abs_of_nonneg hpos).symm
      · rw [nodeWeight_neg_eq_zero (d := x i - x j) hδs (by
            rw [abs_of_nonpos hneg] at ht
            linarith), zero_add]
        refine hnw _ ?_
        rw [abs_of_nonpos hneg]
        ring
  -- packing near `x i`
  have hcard : ((Finset.univ.filter fun j => |x i - x j| ≤ M).card : ℝ) ≤ 2 + 2 * M / s := by
    have h := card_le_one_add_div_of_separated (Finset.univ.filter fun j => |x i - x j| ≤ M) x
      hs (by positivity : (0 : ℝ) ≤ 2 * M + s) (fun j _ k _ hjk => hsep j k hjk)
      fun j hj k hk _ => by
        rw [Finset.mem_filter] at hj hk
        have := abs_sub_le (x j) (x i) (x k)
        rw [abs_sub_comm (x j) (x i)] at this
        linarith [hj.2, hk.2]
    calc ((Finset.univ.filter fun j => |x i - x j| ≤ M).card : ℝ) ≤ 1 + (2 * M + s) / s := h
      _ = 2 + 2 * M / s := by field_simp; ring
  calc ∑ j, pairKernel δ x i j
      ≤ ∑ j, (c + 8 * ((if |x i - x j| ≤ M then 1 else 0) + Real.exp (-(M / 4)))) :=
        Finset.sum_le_sum fun j _ => hentry j
    _ = N * c + 8 * ((Finset.univ.filter fun j => |x i - x j| ≤ M).card +
          N * Real.exp (-(M / 4))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_boole,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ N * c + 8 * ((2 + 2 * M / s) + N * Real.exp (-(M / 4))) := by gcongr
    _ = N * (6 * δ * (D + 1) * Real.exp (D / 2)) + 8 * (2 + 2 * M / s) +
          8 * N * Real.exp (-(M / 4)) := by rw [hc]; ring

/-! ## The asymptotic margin -/

theorem tendsto_lin_mul_exp_neg {α β γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun L => (α + β * L) * Real.exp (-(γ * L))) atTop (𝓝 0) := by
  have hlin : Tendsto (fun L => γ * L) atTop atTop := tendsto_id.const_mul_atTop hγ
  have h0 : Tendsto (fun L => Real.exp (-(γ * L))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have h1' : Tendsto (fun L => (γ * L) ^ 1 * Real.exp (-(γ * L))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  have h1 : Tendsto (fun L => L * Real.exp (-(γ * L))) atTop (𝓝 0) := by
    have := h1'.const_mul γ⁻¹
    rw [mul_zero] at this
    refine this.congr fun L => ?_
    rw [pow_one, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]
  have := (h0.const_mul α).add (h1.const_mul β)
  rw [mul_zero, mul_zero, add_zero] at this
  exact this.congr fun L => by ring

/-- **The margin.**  The losses `(2 + κL/s)((6(κL + 1) + 4)e^{−(1−κ/2)L} + 8e^{−θL/4})` plus any
constant stay below `(3/4)cL` for large `L`. -/
theorem exists_margin {s κ θ c C : ℝ} (hκ2 : κ < 2) (hθ : 0 < θ) (hc : 0 < c) :
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → 0 < L ∧
      (2 + κ * L / s) * ((6 * (κ * L + 1) + 4) * Real.exp (-((1 - κ / 2) * L)) +
        8 * Real.exp (-(θ * L / 4))) + C ≤ 3 / 4 * c * L := by
  have hη : 0 < (1 - κ / 2) / 2 := by linarith
  have hu := tendsto_lin_mul_exp_neg (α := 2) (β := κ / s) hη
  have hv := tendsto_lin_mul_exp_neg (α := 10) (β := 6 * κ) hη
  have hw := tendsto_lin_mul_exp_neg (α := 2) (β := κ / s) (by positivity : 0 < θ / 4)
  have hE := (hu.mul hv).add (hw.const_mul 8)
  rw [mul_zero, mul_zero, add_zero] at hE
  have hE' : Tendsto (fun L => (2 + κ * L / s) * ((6 * (κ * L + 1) + 4) *
      Real.exp (-((1 - κ / 2) * L)) + 8 * Real.exp (-(θ * L / 4)))) atTop (𝓝 0) := by
    refine hE.congr fun L => ?_
    have e1 : Real.exp (-((1 - κ / 2) * L)) =
        Real.exp (-((1 - κ / 2) / 2 * L)) * Real.exp (-((1 - κ / 2) / 2 * L)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(θ * L / 4)) = Real.exp (-(θ / 4 * L)) := by ring_nf
    rw [e1, e2]
    ring
  have hev1 := (tendsto_order.1 hE').2 1 one_pos
  have hev2 := (tendsto_id.const_mul_atTop (by positivity : 0 < 3 / 4 * c)).eventually_ge_atTop
    (C + 1)
  have hev3 := eventually_gt_atTop (0 : ℝ)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp ((hev1.and hev2).and hev3)
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hL₀ L hL
  exact ⟨h3, by simp only [id] at h2; linarith⟩

/-! ## Weil positivity -/

/-- **Quantitative Weil inequality for a separated configuration of span `≤ D`.**  For any
`M ≥ 0`, `Re W_Λ(f ⋆ f̃) ≥ (G − 2e^{δ/2} e^{D/2} δ N − R) ‖f‖²` with the Lévy gain
`G = A(0) + e^{−s/2} log((s − δ)/δ)` and the prime loss
`R = N · 6δ(D + 1)e^{D/2} + 8(2 + 2M/s) + 8N e^{−M/4}`. -/
theorem le_re_weilFullFunctional_bumpSum {φ : ℝ → ℝ} {δ s D M : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφs : ∀ u, δ / 2 < |u| → φ u = 0) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδs : 2 * δ < s)
    (hM : 0 ≤ M) {a x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hspan : ∀ i j, |x i - x j| ≤ D) :
    (EF.gammaBracket 0 + Real.exp (-s / 2) * Real.log ((s - δ) / δ) -
        2 * Real.exp (δ / 2) * (Real.exp (D / 2) * δ) * N -
        (N * (6 * δ * (D + 1) * Real.exp (D / 2)) + 8 * (2 + 2 * M / s) +
          8 * N * Real.exp (-(M / 4)))) * ∫ u, bumpSum φ a x u ^ 2 ≤
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ)))).re := by
  have hfd := contDiff_bumpSum hφ a x
  have hfc := hasCompactSupport_bumpSum hφs a x
  let F : WeilOneSided.WeilTestFn := ⟨fun u => (bumpSum φ a x u : ℂ),
    Complex.ofRealCLM.contDiff.comp hfd, hfc.comp_left Complex.ofReal_zero⟩
  have hW := WeilOneSided.re_weilFullFunctional_eq
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) F
  rw [hW]
  have hlevy := levy_sub_abs_pole_le_weilArchRe (a := a) hφ hφs hδ hδs hsep
  have hexp : ∀ i j : Fin N, Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j) ≤
      Real.exp (D / 2) := fun i j => by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := (le_abs_self (x i - x j)).trans (hspan i j)
    linarith
  have hpole := abs_pole_le_of_exp_le (a := a) hφ hφs hδ (by linarith) hsep
    (Real.exp_pos _).le hexp
  have hprime := abs_linearCombination_vonMangoldt_le (δ := δ) hφ hφs a x F rfl
  have hrow := sum_pairKernel_le (D := D) (M := M) hδ hδ2 (by linarith) hM hsep hspan
  have hschur := sum_abs_mul_le_of_rowSum (pairKernel_nonneg δ x) (pairKernel_symm δ x) hrow a
  have hφ0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hEφ : ∫ u, bumpSum φ a x u ^ 2 = (∑ j, a j ^ 2) * ∫ u, φ u ^ 2 :=
    integral_bumpSum_sq hφ hφs (by linarith) hsep
  have hprime' := hprime.trans (mul_le_mul_of_nonneg_left hschur hφ0)
  have hl := le_abs_self (linearCombination ℝ
      (fun j : WeilOneSided.LogIndex => ArithmeticFunction.vonMangoldt j)
      (WeilOneSided.logVector F))
  rw [hEφ] at hlevy hpole ⊢
  linarith

/-- **The coefficient is nonnegative** once `L = log(1/δ)` is past the margin. -/
theorem coefficient_nonneg {s κ δ L N γ : ℝ} (hs : 0 < s) (hκ0 : 0 < κ)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδs : δ ≤ s / 2) (hδL : δ = Real.exp (-L)) (hL : 0 < L)
    (hN0 : 0 ≤ N) (hN : N ≤ 2 + κ * L / s)
    (hmargin : (2 + κ * L / s) * ((6 * (κ * L + 1) + 4) * Real.exp (-((1 - κ / 2) * L)) +
        8 * Real.exp (-(s * Real.exp (-s / 2) / 64 * L / 4))) +
        (17 + |γ| + Real.exp (-s / 2) * |Real.log (s / 2)|) ≤ 3 / 4 * Real.exp (-s / 2) * L) :
    0 ≤ γ + Real.exp (-s / 2) * Real.log ((s - δ) / δ) -
      2 * Real.exp (δ / 2) * (Real.exp (κ * L / 2) * δ) * N -
      (N * (6 * δ * (κ * L + 1) * Real.exp (κ * L / 2)) +
        8 * (2 + 2 * (s * Real.exp (-s / 2) / 64 * L) / s) +
        8 * N * Real.exp (-(s * Real.exp (-s / 2) / 64 * L / 4))) := by
  set c : ℝ := Real.exp (-s / 2) with hc
  have hc0 : 0 < c := Real.exp_pos _
  set ε₁ : ℝ := Real.exp (-((1 - κ / 2) * L)) with hε₁
  set ε₂ : ℝ := Real.exp (-(s * c / 64 * L / 4)) with hε₂
  have hε₁0 : 0 ≤ ε₁ := (Real.exp_pos _).le
  have hε₂0 : 0 ≤ ε₂ := (Real.exp_pos _).le
  have hgain : Real.log (s / 2) + L ≤ Real.log ((s - δ) / δ) := by
    have hLδ : L = Real.log (1 / δ) := by
      rw [hδL, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    have h1 : s / 2 * (1 / δ) ≤ (s - δ) / δ := by
      rw [div_eq_mul_one_div (s - δ)]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) (by positivity), ← hLδ] at h2
  have he1 : Real.exp (κ * L / 2) * δ = ε₁ := by
    rw [hδL, ← Real.exp_add, hε₁]
    congr 1
    ring
  have he2 : 6 * δ * (κ * L + 1) * Real.exp (κ * L / 2) = 6 * (κ * L + 1) * ε₁ := by
    rw [← he1]; ring
  have hexpδ : Real.exp (δ / 2) ≤ 2 := by
    have := Real.log_two_gt_d9
    calc Real.exp (δ / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hθs : 8 * (2 * (s * c / 64 * L) / s) = c / 4 * L := by field_simp; ring
  rw [he1, he2]
  have hpole' : 2 * Real.exp (δ / 2) * ε₁ * N ≤ 4 * ε₁ * N := by
    have := mul_le_mul_of_nonneg_right hexpδ (mul_nonneg hε₁0 hN0)
    linarith
  have hloss : N * ((6 * (κ * L + 1) + 4) * ε₁ + 8 * ε₂) ≤
      (2 + κ * L / s) * ((6 * (κ * L + 1) + 4) * ε₁ + 8 * ε₂) :=
    mul_le_mul_of_nonneg_right hN (by positivity)
  have hg := neg_abs_le γ
  have hcl : c * -|Real.log (s / 2)| ≤ c * Real.log (s / 2) :=
    mul_le_mul_of_nonneg_left (neg_abs_le _) hc0.le
  have hgain' : c * (Real.log (s / 2) + L) ≤ c * Real.log ((s - δ) / δ) :=
    mul_le_mul_of_nonneg_left hgain hc0.le
  linarith

/-- **Weil positivity for separated narrow bumps below the pole scale.**  For every separation
`s > 0` and every `0 < κ < 2` there is `δ₀ > 0` such that for `0 < δ < δ₀` every configuration of
bumps of width `δ`, `s`-separated and of span at most `κ log(1/δ)`, satisfies
`Re W_Λ(f ⋆ f̃) ≥ 0`.  The amplitudes are arbitrary and no condition ties the centres to the
logarithms of the integers. -/
theorem exists_weilPositive_bumpSum {s κ : ℝ} (hs : 0 < s) (hκ0 : 0 < κ) (hκ2 : κ < 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ (N : ℕ) (φ : ℝ → ℝ) (a x : Fin N → ℝ),
      ContDiff ℝ 2 φ → (∀ u, δ / 2 < |u| → φ u = 0) →
      (∀ i j, i ≠ j → s ≤ |x i - x j|) →
      (∀ i j, |x i - x j| ≤ κ * Real.log (1 / δ)) →
      0 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (bumpSum φ a x u : ℂ)) (fun u => (bumpSum φ a x u : ℂ)))).re := by
  have hc0 : 0 < Real.exp (-s / 2) := Real.exp_pos _
  obtain ⟨L₀, hL₀⟩ := exists_margin (s := s) (κ := κ) (θ := s * Real.exp (-s / 2) / 64)
    (c := Real.exp (-s / 2))
    (C := 17 + |EF.gammaBracket 0| + Real.exp (-s / 2) * |Real.log (s / 2)|) hκ2
    (by positivity) hc0
  refine ⟨min (min (1 / 2) (s / 4)) (Real.exp (-L₀)), by positivity,
    fun δ hδ hδlt N φ a x hφ hφs hsep hspan => ?_⟩
  have hd1 : δ < 1 / 2 := lt_of_lt_of_le hδlt ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : δ < s / 4 := lt_of_lt_of_le hδlt ((min_le_left _ _).trans (min_le_right _ _))
  have hd3 : δ < Real.exp (-L₀) := lt_of_lt_of_le hδlt (min_le_right _ _)
  have hLL₀ : L₀ ≤ Real.log (1 / δ) := by
    have : Real.exp L₀ < 1 / δ := by
      rw [lt_div_iff₀ hδ, mul_comm, ← lt_div_iff₀ (Real.exp_pos _), div_eq_mul_inv,
        one_mul, ← Real.exp_neg]
      exact hd3
    exact ((Real.lt_log_iff_exp_lt (by positivity)).mpr this).le
  obtain ⟨hLpos, hmargin⟩ := hL₀ _ hLL₀
  have hδL : δ = Real.exp (-Real.log (1 / δ)) := by
    rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hN : (N : ℝ) ≤ 2 + κ * Real.log (1 / δ) / s := by
    have := natCast_le_one_add_div_of_separated hs
      (by positivity : (0 : ℝ) ≤ κ * Real.log (1 / δ) + s) hsep
      fun i j _ => lt_of_le_of_lt (hspan i j) (by linarith)
    calc (N : ℝ) ≤ 1 + (κ * Real.log (1 / δ) + s) / s := this
      _ = 2 + κ * Real.log (1 / δ) / s := by field_simp; ring
  have key := le_re_weilFullFunctional_bumpSum (a := a) (M := s * Real.exp (-s / 2) / 64 *
    Real.log (1 / δ)) hφ hφs hδ hd1.le (by linarith) (by positivity) hsep hspan
  have hcoef := coefficient_nonneg (γ := EF.gammaBracket 0) hs hκ0 hδ hd1.le (by linarith) hδL
    hLpos (Nat.cast_nonneg N) hN hmargin
  have hE0 : 0 ≤ ∫ u, bumpSum φ a x u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg hcoef hE0) key

end RHTower.SeparatedBump

end
