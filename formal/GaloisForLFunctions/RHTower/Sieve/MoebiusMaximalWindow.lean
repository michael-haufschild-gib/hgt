import GaloisForLFunctions.RHTower.Sieve.CoprimeMaximalWindow
import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpLittleO

/-!
# The Möbius input: the mean square is carried by the first moment

The last hypothesis of the card is a *second* moment of the maximal short Möbius sum.  For a weight
bounded by one it is carried by the *first* moment, because a window of length at most `H + 1`
carries a sum of modulus at most `H + 1`:

    max_{m ≤ H} (∑_{y ≤ n ≤ y+m} f(n))²  ≤  (H+1) · max_{m ≤ H} |∑_{y ≤ n ≤ y+m} f(n)|.

So any `L¹` short-interval estimate suffices; no `L²` estimate is needed.  This is the same device
that made the two squarefree inputs elementary, and it applies verbatim here.

Also recorded is the Mertens function in real form together with `M(N) = o(N)`, the corpus's
unconditional prime number theorem, which is what bounds the first moment in the long-window regime.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- The largest modulus of a window sum of length at most `H` starting at `y`. -/
noncomputable def maxWindowAbs (f : ℕ → ℝ) (H y : ℕ) : ℝ :=
  (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one
    (fun m => |∑ b ∈ Finset.Icc y (y + m), f b|)

theorem maxWindowAbs_nonneg (f : ℕ → ℝ) (H y : ℕ) : 0 ≤ maxWindowAbs f H y := by
  refine le_trans (abs_nonneg (∑ b ∈ Finset.Icc y (y + 0), f b)) ?_
  exact Finset.le_sup' (fun m => |∑ b ∈ Finset.Icc y (y + m), f b|)
    (Finset.mem_range.2 (by omega))

theorem abs_le_maxWindowAbs {f : ℕ → ℝ} {H y m : ℕ} (hm : m ≤ H) :
    |∑ b ∈ Finset.Icc y (y + m), f b| ≤ maxWindowAbs f H y :=
  Finset.le_sup' (fun m => |∑ b ∈ Finset.Icc y (y + m), f b|)
    (Finset.mem_range.2 (by omega))

/-- **The maximal square is carried by the maximal modulus.** -/
theorem maxWindowSq_le_mul_maxWindowAbs {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) (H y : ℕ) :
    maxWindowSq f H y ≤ ((H : ℝ) + 1) * maxWindowAbs f H y := by
  refine Finset.sup'_le _ _ ?_
  intro m hm
  rw [Finset.mem_range] at hm
  have hmH : m ≤ H := by omega
  have hlen : |∑ b ∈ Finset.Icc y (y + m), f b| ≤ (H : ℝ) + 1 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun b _ => hf b)) ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have hcard : ((y + m + 1 - y : ℕ) : ℝ) = (m : ℝ) + 1 := by
      have : y + m + 1 - y = m + 1 := by omega
      rw [this]
      push_cast
      ring
    rw [hcard]
    have : (m : ℝ) ≤ (H : ℝ) := by exact_mod_cast hmH
    linarith
  have hmax := abs_le_maxWindowAbs (f := f) (H := H) (y := y) hmH
  have habs : |∑ b ∈ Finset.Icc y (y + m), f b| ^ 2 = (∑ b ∈ Finset.Icc y (y + m), f b) ^ 2 :=
    sq_abs _
  nlinarith [abs_nonneg (∑ b ∈ Finset.Icc y (y + m), f b)]

/-- **The first moment of the maximal short sum over all starting points.** -/
def MaximalWindowFirstMoment (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowAbs f ⌈hh x⌉₊ y) / (hh x * Real.sqrt x)) atTop (𝓝 0)

/-- **The mean square follows from the first moment.**  No `L²` short-interval estimate is needed. -/
theorem maximalWindowMeanSquare_of_firstMoment {f : ℕ → ℝ} {hh : ℝ → ℝ}
    (hf : ∀ n, |f n| ≤ 1) (hgrow : Tendsto hh atTop atTop)
    (hfm : MaximalWindowFirstMoment f hh) : MaximalWindowMeanSquare f hh := by
  have h2 : Tendsto (fun x => 2 * ((∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowAbs f ⌈hh x⌉₊ y) / (hh x * Real.sqrt x))) atTop (𝓝 0) := by
    have := hfm.const_mul (2 : ℝ)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop 2] with x hx hhx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hh0 : (0 : ℝ) < hh x := by linarith
  have hden : (0 : ℝ) < hh x ^ 2 * Real.sqrt x := by positivity
  have hHup : ((⌈hh x⌉₊ : ℕ) : ℝ) + 1 ≤ 2 * hh x := by
    have := (Nat.ceil_lt_add_one hh0.le).le
    linarith
  have hsum : ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowSq f ⌈hh x⌉₊ y
      ≤ (2 * hh x) * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
          maxWindowAbs f ⌈hh x⌉₊ y := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro y _
    refine le_trans (maxWindowSq_le_mul_maxWindowAbs hf _ y) ?_
    exact mul_le_mul_of_nonneg_right hHup (maxWindowAbs_nonneg f _ y)
  have habs0 : (0 : ℝ) ≤ ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowSq f ⌈hh x⌉₊ y :=
    Finset.sum_nonneg (fun y _ => maxWindowSq_nonneg f _ y)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine le_trans (div_le_div_of_nonneg_right hsum hden.le) (le_of_eq ?_)
  field_simp

/-- The Mertens function, in real form. -/
noncomputable def mertensM (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ)

/-- **The prime number theorem, in Mertens form.**  `M(N) = o(N)`. -/
theorem tendsto_abs_mertensM_div : Tendsto (fun N : ℕ => |mertensM N| / (N : ℝ))
    atTop (𝓝 0) := by
  have hbase := tendsto_norm_sum_moebius_div.comp tendsto_natCast_atTop_atTop
  refine hbase.congr fun N => ?_
  simp only [Function.comp_apply, Nat.floor_natCast]
  congr 1
  rw [mertensM]
  have hcast : (∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℂ))
      = ((∑ n ∈ Finset.range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

/-- The largest modulus of the Mertens function below `Z`. -/
noncomputable def mertensSup (Z : ℕ) : ℝ :=
  (Finset.range (Z + 1)).sup' Finset.nonempty_range_add_one (fun z => |mertensM z|)

theorem abs_mertensM_le_mertensSup {z Z : ℕ} (h : z ≤ Z) : |mertensM z| ≤ mertensSup Z :=
  Finset.le_sup' (fun z => |mertensM z|) (Finset.mem_range.2 (by omega))

theorem mertensSup_nonneg (Z : ℕ) : 0 ≤ mertensSup Z :=
  le_trans (abs_nonneg _) (abs_mertensM_le_mertensSup (Nat.zero_le Z))

/-- **The supremum of the Mertens function is `o(Z)` too.** -/
theorem tendsto_mertensSup_div : Tendsto (fun Z : ℕ => mertensSup Z / (Z : ℝ)) atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((NormedAddGroup.tendsto_nhds_zero.1 tendsto_abs_mertensM_div) (ε / 2) hhalf)
  set C : ℝ := mertensSup N₀ with hC
  have hC0 : 0 ≤ C := mertensSup_nonneg N₀
  refine Filter.eventually_atTop.2 ⟨⌈2 * C / ε⌉₊ + N₀ + 1, ?_⟩
  intro Z hZ
  have hZ0 : (0 : ℝ) < (Z : ℝ) := by
    have : 0 < Z := by omega
    exact_mod_cast this
  have hCZ : C ≤ ε / 2 * (Z : ℝ) := by
    have hceil : (2 * C / ε) ≤ ((⌈2 * C / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hle : ((⌈2 * C / ε⌉₊ : ℕ) : ℝ) ≤ (Z : ℝ) := by
      have : ⌈2 * C / ε⌉₊ ≤ Z := by omega
      exact_mod_cast this
    have : 2 * C / ε ≤ (Z : ℝ) := le_trans hceil hle
    rw [div_le_iff₀ hε] at this
    linarith
  have hbound : mertensSup Z ≤ ε / 2 * (Z : ℝ) := by
    refine Finset.sup'_le _ _ ?_
    intro z hz
    rw [Finset.mem_range] at hz
    rcases Nat.lt_or_ge N₀ z with hzgt | hzle
    · have hz0 : (0 : ℝ) < (z : ℝ) := by
        have : 0 < z := by omega
        exact_mod_cast this
      have hzZ : (z : ℝ) ≤ (Z : ℝ) := by
        have : z ≤ Z := by omega
        exact_mod_cast this
      have := hN₀ z (le_of_lt hzgt)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      rw [div_lt_iff₀ hz0] at this
      nlinarith [this, hz0, hzZ, hhalf]
    · exact le_trans (abs_mertensM_le_mertensSup hzle) hCZ
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mertensSup_nonneg Z) hZ0.le),
    div_lt_iff₀ hZ0]
  nlinarith [hbound, hε, hZ0]

/-- A window sum of the Möbius function is a difference of Mertens values. -/
theorem sum_window_moebius_eq {y m : ℕ} (hy : 1 ≤ y) :
    ∑ b ∈ Finset.Icc y (y + m), ((ArithmeticFunction.moebius b : ℤ) : ℝ)
      = mertensM (y + m) - mertensM (y - 1) := by
  have hIcc : Finset.Icc y (y + m) = Finset.Ico y (y + m + 1) := rfl
  have hpred : y - 1 + 1 = y := by omega
  rw [hIcc, Finset.sum_Ico_eq_sub _ (by omega : y ≤ y + m + 1), mertensM, mertensM, hpred]

/-- **The maximal Möbius window sum is controlled by the Mertens supremum.** -/
theorem maxWindowAbs_moebius_le {H y Z : ℕ} (hy : 1 ≤ y) (hZ : y + H ≤ Z) :
    maxWindowAbs (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) H y
      ≤ 2 * mertensSup Z := by
  refine Finset.sup'_le _ _ ?_
  intro m hm
  rw [Finset.mem_range] at hm
  have hmH : m ≤ H := by omega
  rw [sum_window_moebius_eq hy]
  refine le_trans (abs_sub _ _) ?_
  have h1 : |mertensM (y + m)| ≤ mertensSup Z := abs_mertensM_le_mertensSup (by omega)
  have h2 : |mertensM (y - 1)| ≤ mertensSup Z := abs_mertensM_le_mertensSup (by omega)
  linarith

/-- **The Möbius first moment, at the exact rate the method allows.**  The admissible window laws
are precisely those that dominate the Mertens supremum at the scale `3√x`. -/
theorem maximalWindowFirstMoment_moebius_of_rate {hh : ℝ → ℝ}
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x) (hposv : ∀ᶠ x in atTop, 0 < hh x)
    (hrate : Tendsto (fun x : ℝ => mertensSup ⌈3 * Real.sqrt x⌉₊ / hh x) atTop (𝓝 0)) :
    MaximalWindowFirstMoment (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  classical
  have hmaj : Tendsto (fun x : ℝ => 2 * (mertensSup ⌈3 * Real.sqrt x⌉₊ / hh x))
      atTop (𝓝 0) := by
    have := hrate.const_mul (2 : ℝ)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (16 : ℝ), hsmall, hposv] with x hx hsx hh0
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
    have : Real.sqrt 16 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [show Real.sqrt 16 = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  set A : ℕ := ⌈Real.sqrt x / 2⌉₊ with hA
  set B : ℕ := ⌈Real.sqrt x⌉₊ with hB
  set H : ℕ := ⌈hh x⌉₊ with hH
  set Z : ℕ := ⌈3 * Real.sqrt x⌉₊ with hZ
  have hA1 : 1 ≤ A := Nat.one_le_ceil_iff.2 (by linarith)
  have hBup : (B : ℝ) ≤ Real.sqrt x + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hHup : (H : ℝ) ≤ Real.sqrt x + 1 := by
    have := (Nat.ceil_lt_add_one hh0.le).le
    linarith
  have hAlow : Real.sqrt x / 2 ≤ (A : ℝ) := Nat.le_ceil _
  have hZlow : 3 * Real.sqrt x ≤ (Z : ℝ) := Nat.le_ceil _
  have hterm : ∀ y ∈ Finset.Icc A B,
      maxWindowAbs (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) H y
        ≤ 2 * mertensSup Z := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hy1 : 1 ≤ y := le_trans hA1 hy.1
    have hyZ : y + H ≤ Z := by
      have hyB : (y : ℝ) ≤ (B : ℝ) := by exact_mod_cast hy.2
      have : ((y + H : ℕ) : ℝ) ≤ ((Z : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact maxWindowAbs_moebius_le hy1 hyZ
  have hcard : (((Finset.Icc A B).card : ℕ) : ℝ) ≤ Real.sqrt x := by
    rw [Nat.card_Icc]
    have hABle : A ≤ B := Nat.ceil_le_ceil (by linarith)
    have hcast : ((B + 1 - A : ℕ) : ℝ) = (B : ℝ) + 1 - (A : ℝ) := by
      push_cast [Nat.cast_sub (by omega : A ≤ B + 1)]
      ring
    rw [hcast]
    linarith
  have hsum : ∑ y ∈ Finset.Icc A B,
      maxWindowAbs (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) H y
      ≤ Real.sqrt x * (2 * mertensSup Z) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by linarith [mertensSup_nonneg Z])
  have hden : (0 : ℝ) < hh x * Real.sqrt x := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (Finset.sum_nonneg fun y _ => maxWindowAbs_nonneg _ _ y) hden.le)]
  refine le_trans (div_le_div_of_nonneg_right hsum hden.le) (le_of_eq ?_)
  field_simp

/-- The Mertens supremum at the square-root scale is `o(√x)`. -/
theorem tendsto_mertensSup_sqrt_div :
    Tendsto (fun x : ℝ => mertensSup ⌈3 * Real.sqrt x⌉₊ / Real.sqrt x) atTop (𝓝 0) := by
  have hZtop : Tendsto (fun x : ℝ => ⌈3 * Real.sqrt x⌉₊) atTop atTop := by
    refine tendsto_nat_ceil_atTop.comp ?_
    exact Real.tendsto_sqrt_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
  have hmaj : Tendsto (fun x : ℝ => 4
      * (mertensSup ⌈3 * Real.sqrt x⌉₊ / ((⌈3 * Real.sqrt x⌉₊ : ℕ) : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_mertensSup_div.comp hZtop).const_mul (4 : ℝ)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hs1 : (1 : ℝ) ≤ Real.sqrt x := by
    have : Real.sqrt 1 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_one] at this
  set Z : ℕ := ⌈3 * Real.sqrt x⌉₊ with hZ
  have hZup : (Z : ℝ) ≤ 4 * Real.sqrt x := by
    have := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt x)).le
    linarith
  have hZ0 : (0 : ℝ) < (Z : ℝ) := by
    have : 3 * Real.sqrt x ≤ (Z : ℝ) := Nat.le_ceil _
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mertensSup_nonneg Z) hs0.le),
    div_le_iff₀ hs0]
  have hval : 4 * (mertensSup Z / (Z : ℝ)) * Real.sqrt x
      = mertensSup Z * (4 * Real.sqrt x) / (Z : ℝ) := by
    field_simp
  rw [hval, le_div_iff₀ hZ0]
  nlinarith [mertensSup_nonneg Z, hZup]

/-- **The Möbius first moment in the long-window regime.**  When the window length is within a
constant factor of `√x`, the prime number theorem alone bounds the first moment. -/
theorem maximalWindowFirstMoment_moebius_long {K : ℝ} (hK : 0 < K) {hh : ℝ → ℝ}
    (hlow : ∀ᶠ x in atTop, Real.sqrt x / K ≤ hh x)
    (hsmall : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x) :
    MaximalWindowFirstMoment (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  have hposv : ∀ᶠ x in atTop, 0 < hh x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hlow] with x hx hlx
    have : (0 : ℝ) < Real.sqrt x / K := by
      have : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
      positivity
    linarith
  refine maximalWindowFirstMoment_moebius_of_rate hsmall hposv ?_
  have hmaj : Tendsto (fun x : ℝ => K
      * (mertensSup ⌈3 * Real.sqrt x⌉₊ / Real.sqrt x)) atTop (𝓝 0) := by
    have := tendsto_mertensSup_sqrt_div.const_mul K
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlow, hposv] with x hx hlx hh0
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
  set Z : ℕ := ⌈3 * Real.sqrt x⌉₊ with hZ
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mertensSup_nonneg Z) hh0.le)]
  rw [div_le_iff₀ hh0]
  have hval : K * (mertensSup Z / Real.sqrt x) * hh x
      = mertensSup Z * (K * hh x) / Real.sqrt x := by
    field_simp
  rw [hval, le_div_iff₀ hs0]
  have hKh : Real.sqrt x ≤ K * hh x := by
    rw [div_le_iff₀ hK] at hlx
    linarith
  nlinarith [mertensSup_nonneg Z, hKh]

end RHTower.Sieve
