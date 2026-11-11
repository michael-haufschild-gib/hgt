import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheZeroSumVanishes
import GaloisForLFunctions.RHTower.PrimeShortIntervalsHuxleyAsymptotic

/-!
# Character sums of the von Mangoldt function in short windows

For every nonprincipal character `χ` modulo `q` and `θ = 1 − u₁/16` (`u₁ = 1/(14·10⁷ + 12)`),

`(ψ(x + x^θ, χ) − ψ(x, χ)) / x^θ → 0`        (`tendsto_window_character`).

For primitive `χ` this is the window bound of `CharacterSumsInShortWindows` at `h = x^θ`,
`h' = x^{θ'}`, `θ' = 1 − u₁/8`: the zero sum is taken at `8x²/(hh') = 8 x^{2u}`, `u = 3u₁/32`, and
vanishes (`tendsto_tsum_zeroShortWeight`); the two windows of length `h'` are `O(h')` by Huxley's
theorem.  An imprimitive `χ` agrees with its primitive character on integers prime to `q`; a window
`(x, x + h]` with `h ≤ x` contains at most one power of each prime, so the two window sums differ
by at most `Σ_{p ∣ q} log p` (`norm_window_sub_primitive_le`).
-/

open Complex Filter Topology Finset ArithmeticFunction

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-- The window exponent `θ = 1 − u₁/16`. -/
def windowExponent : ℝ := 1 - nearExponent / 16

theorem windowExponent_lt_one : windowExponent < 1 := by
  unfold windowExponent; linarith [nearExponent_pos]

theorem seven_twelfths_lt_windowExponent : 7 / 12 < windowExponent := by
  unfold windowExponent nearExponent; norm_num

/-- The window of `ψ(·, χ)`. -/
theorem psiChi_sub_eq_sum {N : ℕ} (χ : DirichletCharacter ℂ N) {a b : ℝ} (hab : a ≤ b) :
    psiChi χ b - psiChi χ a = ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, twistedVM χ n := by
  unfold psiChi
  have hfl : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hsplit : Icc 1 ⌊b⌋₊ = Icc 1 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b⌋₊) := by
    rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]
  ring

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Primitive characters.**  `‖ψ(x + x^θ, χ) − ψ(x, χ)‖ / x^θ → 0`. -/
theorem tendsto_window_primitive (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    Tendsto (fun x : ℝ => ‖psiChi χ (x + x ^ windowExponent) - psiChi χ x‖ / x ^ windowExponent)
      atTop (𝓝 0) := by
  set u₁ := nearExponent with hu₁def
  have hu₁ : 0 < u₁ := nearExponent_pos
  have hu₁small : u₁ < 1 / 24 := by rw [hu₁def, nearExponent]; norm_num
  set θ := windowExponent with hθ
  set θ' : ℝ := 1 - u₁ / 8 with hθ'
  have hθθ' : θ' - θ = -(u₁ / 16) := by rw [hθ, hθ', windowExponent]; ring
  have hθ0 : 0 < θ := by rw [hθ, windowExponent]; linarith
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  obtain ⟨C, hC, hwin⟩ := norm_psiChi_window_le hχ hprim
  -- Huxley's windows
  have hH := RHTower.tendsto_psi_short_window_div_seven_twelfths (α := θ')
    (by rw [hθ']; linarith) (by rw [hθ']; linarith)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (hH.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num)))
  have hS := tendsto_tsum_zeroShortWeight hχ hprim (u := 3 * u₁ / 32) (c := 8) (by positivity)
    (by linarith) (by norm_num)
  set S : ℝ → ℝ := fun x => ∑' r : LZero χ,
    RHTower.zeroShortWeight x (8 * x ^ (2 * (3 * u₁ / 32))) r.point with hSdef
  set U : ℝ → ℝ := fun x => 10 * x ^ (θ' - θ) + 2 * S x +
    C * (1 + Real.log 2 + Real.log x) * x ^ (-θ) + C * x ^ (-(θ + θ')) with hU
  have hUlim : Tendsto U atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (θ' - θ)) atTop (𝓝 0) := by
      rw [hθθ']; exact tendsto_rpow_neg_atTop (by positivity)
    have h2 : Tendsto (fun x : ℝ => x ^ (-θ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hθ0
    have h3 : Tendsto (fun x : ℝ => Real.log x * x ^ (-θ)) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hθ0).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.rpow_neg hx.le, div_eq_mul_inv]
    have h4 : Tendsto (fun x : ℝ => x ^ (-(θ + θ'))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have := (((h1.const_mul 10).add (hS.const_mul 2)).add
      (((h2.const_mul (C * (1 + Real.log 2))).add (h3.const_mul C)))).add (h4.const_mul C)
    refine this.congr' (Eventually.of_forall fun x => ?_) |>.trans (by simp)
    simp only [hU]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUlim
    (by filter_upwards [eventually_ge_atTop 0] with x hx; positivity) ?_
  have hbig : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (u₁ / 16) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop 2
  filter_upwards [hbig, eventually_ge_atTop (max Y₀ 2)] with x hx2θ hxY
  have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hxY
  have hxY₀ : Y₀ ≤ x := le_trans (le_max_left _ _) hxY
  have hx0 : 0 < x := by linarith
  set h := x ^ θ with hh
  set h' := x ^ θ' with hh'
  have hh0 : 0 < h := by positivity
  have hh'0 : 0 < h' := by positivity
  have hh'h : 2 * h' ≤ h := by
    have hθeq : θ = θ' + u₁ / 16 := by linarith [hθθ']
    have e : h = h' * x ^ (u₁ / 16) := by rw [hh, hh', hθeq, Real.rpow_add hx0]
    rw [e, mul_comm h']
    exact mul_le_mul_of_nonneg_right hx2θ hh'0.le
  have hhx : h ≤ x := by
    calc h = x ^ θ := rfl
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hw := hwin x h h' hx2 hh'0 hh'h hhx
  -- the two windows
  have hW₁ : Chebyshev.psi (x + h') - Chebyshev.psi x ≤ 2 * h' := by
    have := hY₀ x hxY₀
    rw [div_lt_iff₀ hh'0] at this
    linarith
  have hW₂ : Chebyshev.psi (x + h) - Chebyshev.psi (x + h - h') ≤ 4 * h' := by
    set y := x + h - h' with hy
    have hyx : x ≤ y := by rw [hy]; linarith
    have hy0 : 0 < y := by linarith
    have h1 := hY₀ y (hxY₀.trans hyx)
    rw [div_lt_iff₀ (by positivity)] at h1
    have h2 : h' ≤ y ^ θ' := Real.rpow_le_rpow hx0.le hyx hθ'0.le
    have h3 : Chebyshev.psi (y + h') ≤ Chebyshev.psi (y + y ^ θ') :=
      Chebyshev.psi_mono (by linarith)
    have h4 : y ^ θ' ≤ 2 * h' := by
      have hy2 : y ≤ 2 * x := by rw [hy]; linarith
      calc y ^ θ' ≤ (2 * x) ^ θ' := Real.rpow_le_rpow hy0.le hy2 hθ'0.le
        _ = 2 ^ θ' * h' := by rw [Real.mul_rpow (by norm_num) hx0.le]
        _ ≤ 2 * h' := by
            refine mul_le_mul_of_nonneg_right ?_ hh'0.le
            calc (2 : ℝ) ^ θ' ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := Real.rpow_one 2
    have h5 : x + h = y + h' := by rw [hy]; ring
    rw [h5]
    linarith
  -- the zero sum argument
  have hY : 8 * x ^ 2 / (h * h') = 8 * x ^ (2 * (3 * u₁ / 32)) := by
    rw [hh, hh', ← Real.rpow_add hx0, mul_div_assoc]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_sub hx0]
    congr 1
    rw [hθ, hθ', windowExponent]; push_cast; ring
  rw [hY] at hw
  have hlog2 : Real.log (2 * x) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
  rw [div_le_iff₀ hh0]
  have hS0 : 0 ≤ S x := tsum_nonneg fun r =>
    RHTower.zeroShortWeight_nonneg hx0.le (by positivity) _
  have e1 : 10 * x ^ (θ' - θ) * h = 10 * h' := by
    rw [hh, hh', mul_assoc, ← Real.rpow_add hx0]; congr 2; ring
  have e2 : x ^ (-θ) * h = 1 := by rw [hh, ← Real.rpow_add hx0, neg_add_cancel, Real.rpow_zero]
  have e3 : x ^ (-(θ + θ')) * h = 1 / h' := by
    rw [hh, hh', ← Real.rpow_add hx0, show -(θ + θ') + θ = -θ' by ring, Real.rpow_neg hx0.le,
      one_div]
  simp only [hU]
  have : (10 * x ^ (θ' - θ) + 2 * S x + C * (1 + Real.log 2 + Real.log x) * x ^ (-θ) +
      C * x ^ (-(θ + θ'))) * h = 10 * h' + 2 * h * S x + C * (1 + Real.log 2 + Real.log x) +
        C / h' := by
    have := e1; have := e2; have := e3
    calc _ = 10 * x ^ (θ' - θ) * h + 2 * h * S x +
          C * (1 + Real.log 2 + Real.log x) * (x ^ (-θ) * h) + C * (x ^ (-(θ + θ')) * h) := by ring
      _ = _ := by rw [e1, e2, e3]; ring
  rw [this]
  rw [hlog2] at hw
  have hSx : ∑' r : LZero χ, RHTower.zeroShortWeight x (8 * x ^ (2 * (3 * u₁ / 32))) r.point
      = S x := rfl
  rw [hSx] at hw
  linarith

/-! ### Characters sharing values on integers prime to `q` -/

omit [NeZero q] in
/-- **Prime powers in a window.**  A window `(x, x + h]` with `h ≤ x` contains at most one power
of each prime, so its integers not prime to `q` carry von Mangoldt mass at most `Σ_{p ∣ q} log p`. -/
theorem sum_window_not_coprime_le {x h : ℝ} (hx : 0 < x) (hhx : h ≤ x) (hq : q ≠ 0) :
    ∑ n ∈ (Ioc ⌊x⌋₊ ⌊x + h⌋₊).filter (fun n => ¬ n.Coprime q), vonMangoldt n ≤
      ∑ p ∈ q.primeFactors, Real.log p := by
  classical
  set W := (Ioc ⌊x⌋₊ ⌊x + h⌋₊).filter (fun n => ¬ n.Coprime q) with hW
  have hwin : ∀ n ∈ W, x < n ∧ (n : ℝ) ≤ x + h := by
    intro n hn
    rw [hW, mem_filter, mem_Ioc] at hn
    have hxh : 0 ≤ x + h ∨ x + h < 0 := le_or_gt 0 (x + h)
    refine ⟨Nat.lt_of_floor_lt hn.1.1, ?_⟩
    rcases hxh with h0 | h0
    · exact (Nat.cast_le.mpr hn.1.2).trans (Nat.floor_le h0)
    · rw [Nat.floor_of_nonpos h0.le] at hn; omega
  rw [← Finset.sum_filter_of_ne (p := fun n => IsPrimePow n)
    (fun n _ hn => vonMangoldt_ne_zero_iff.mp hn)]
  set W' := W.filter (fun n => IsPrimePow n) with hW'
  have hlog : ∀ n ∈ W', vonMangoldt n = Real.log (n.minFac) := by
    intro n hn
    rw [vonMangoldt_apply, if_pos (mem_filter.mp hn).2]
  rw [Finset.sum_congr rfl hlog]
  have hinj : Set.InjOn Nat.minFac W' := by
    intro n hn m hm hnm
    have hn' := mem_filter.mp hn
    have hm' := mem_filter.mp hm
    obtain ⟨hnx, hnh⟩ := hwin n hn'.1
    obtain ⟨hmx, hmh⟩ := hwin m hm'.1
    have en := hn'.2.minFac_pow_factorization_eq
    have em := hm'.2.minFac_pow_factorization_eq
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn'.2.ne_one
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [← hnm] at em
    set a := n.factorization p
    set b := m.factorization p
    have key : ∀ i j : ℕ, i < j → x < ((p ^ i : ℕ) : ℝ) → ((p ^ j : ℕ) : ℝ) ≤ x + h → False := by
      intro i j hij hi hj
      have h1 : ((p ^ (i + 1) : ℕ) : ℝ) ≤ ((p ^ j : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right hp.pos hij
      have h2 : ((p ^ (i + 1) : ℕ) : ℝ) = (p : ℝ) * ((p ^ i : ℕ) : ℝ) := by push_cast; ring
      nlinarith
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (key a b hab (by rw [en]; exact hnx) (by rw [em]; exact hmh)).elim
    · rw [← en, ← em, hab]
    · exact (key b a hab (by rw [em]; exact hmx) (by rw [en]; exact hnh)).elim
  rw [← Finset.sum_image (f := fun p : ℕ => Real.log (p : ℝ)) (g := Nat.minFac) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
  intro p hp
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hp
  have hn' := mem_filter.mp hn
  have hcop := (mem_filter.mp hn'.1).2
  have hprime : n.minFac.Prime := Nat.minFac_prime hn'.2.ne_one
  obtain ⟨r, hr, hrn, hrq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have en := hn'.2.minFac_pow_factorization_eq
  have hrp : r = n.minFac := by
    rw [← en] at hrn
    exact (Nat.prime_dvd_prime_iff_eq hr hprime).mp (hr.dvd_of_dvd_pow hrn)
  rw [Nat.mem_primeFactors]
  exact ⟨hprime, hrp ▸ hrq, hq⟩

/-- **Comparison of windows.**  If `χ(n) = g(n)` for `n` prime to `q` and `|g| ≤ 1`, the windows of
`Σ χ(n)Λ(n)` and `Σ g(n)Λ(n)` differ by at most `Σ_{p ∣ q} log p`. -/
theorem norm_window_sub_le (χ : DirichletCharacter ℂ q) (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hcop : ∀ n : ℕ, n.Coprime q → χ n = g n) {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (hhx : h ≤ x) :
    ‖(psiChi χ (x + h) - psiChi χ x) -
        ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + h⌋₊, g n * ((vonMangoldt n : ℝ) : ℂ)‖ ≤
      ∑ p ∈ q.primeFactors, Real.log p := by
  classical
  rw [psiChi_sub_eq_sum χ (by linarith), ← Finset.sum_sub_distrib]
  unfold twistedVM
  have hsplit := Finset.sum_filter_add_sum_filter_not (Ioc ⌊x⌋₊ ⌊x + h⌋₊)
    (fun n => n.Coprime q)
    (fun n => χ n * ((vonMangoldt n : ℝ) : ℂ) - g n * ((vonMangoldt n : ℝ) : ℂ))
  have hzero : ∑ n ∈ (Ioc ⌊x⌋₊ ⌊x + h⌋₊).filter (fun n => n.Coprime q),
      (χ n * ((vonMangoldt n : ℝ) : ℂ) - g n * ((vonMangoldt n : ℝ) : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [hcop n (mem_filter.mp hn).2, sub_self]
  rw [← hsplit, hzero, zero_add]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
    (sum_window_not_coprime_le hx hhx (NeZero.ne q)))
  have hnc := (mem_filter.mp hn).2
  have hχn : χ n = 0 := MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime])
  rw [hχn, zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]
  calc ‖g n‖ * vonMangoldt n ≤ 1 * vonMangoldt n :=
        mul_le_mul_of_nonneg_right (hg n) vonMangoldt_nonneg
    _ = vonMangoldt n := one_mul _

/-- **Nonprincipal characters.**  `‖ψ(x + x^θ, χ) − ψ(x, χ)‖ / x^θ → 0` for every `χ ≠ 1`. -/
theorem tendsto_window_character (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => ‖psiChi χ (x + x ^ windowExponent) - psiChi χ x‖ / x ^ windowExponent)
      atTop (𝓝 0) := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χs := χ.primitiveCharacter with hχs
  have hχs1 : χs ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, ← hχs, h, map_one]
  have hprim : χs.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hP := tendsto_window_primitive hχs1 hprim
  have hcop : ∀ n : ℕ, n.Coprime q → χ n = χs n := by
    intro n hn
    have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hn)
    rw [hχs]
    exact_mod_cast h.symm
  set E := ∑ p ∈ q.primeFactors, Real.log p with hE
  have hθ0 : 0 < windowExponent := by linarith [seven_twelfths_lt_windowExponent]
  have hE0 : Tendsto (fun x : ℝ => E / x ^ windowExponent) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hθ0).const_mul E
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  have hsum := hP.add hE0
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (by filter_upwards [eventually_ge_atTop 0] with x hx; positivity) ?_
  have hθ1 := windowExponent_lt_one
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < x ^ windowExponent := by positivity
  have hhx : x ^ windowExponent ≤ x := by
    calc x ^ windowExponent ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1.le
      _ = x := Real.rpow_one x
  have hcmp := norm_window_sub_le χ (fun n => χs n) (fun n => DirichletCharacter.norm_le_one χs n)
    hcop hx0 hh0.le hhx
  have hwin : psiChi χs (x + x ^ windowExponent) - psiChi χs x =
      ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + x ^ windowExponent⌋₊, χs n * ((vonMangoldt n : ℝ) : ℂ) := by
    rw [psiChi_sub_eq_sum χs (by linarith)]
    rfl
  rw [← hwin] at hcmp
  rw [← add_div, div_le_div_iff_of_pos_right hh0]
  have := norm_le_norm_sub_add (psiChi χ (x + x ^ windowExponent) - psiChi χ x)
    (psiChi χs (x + x ^ windowExponent) - psiChi χs x)
  linarith

/-- **The principal character.**  `(ψ(x + x^θ, χ₀) − ψ(x, χ₀)) / x^θ → 1`. -/
theorem tendsto_window_principal :
    Tendsto (fun x : ℝ => (psiChi (1 : DirichletCharacter ℂ q) (x + x ^ windowExponent) -
        psiChi (1 : DirichletCharacter ℂ q) x) / (x ^ windowExponent : ℝ)) atTop (𝓝 1) := by
  have hθ0 : 0 < windowExponent := by linarith [seven_twelfths_lt_windowExponent]
  have hθ1 := windowExponent_lt_one
  have hH := RHTower.tendsto_psi_short_window_div_seven_twelfths
    seven_twelfths_lt_windowExponent hθ1
  have hHC : Tendsto (fun x : ℝ => (((Chebyshev.psi (x + x ^ windowExponent) - Chebyshev.psi x) /
      x ^ windowExponent : ℝ) : ℂ)) atTop (𝓝 1) := by
    have := (Complex.continuous_ofReal.tendsto 1).comp hH
    refine this.congr fun x => ?_
    simp only [Function.comp]
    push_cast
  set E := ∑ p ∈ q.primeFactors, Real.log p with hE
  have hE0 : Tendsto (fun x : ℝ => E / x ^ windowExponent) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hθ0).const_mul E
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.rpow_neg hx.le, div_eq_mul_inv]
  rw [tendsto_iff_norm_sub_tendsto_zero] at hHC ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hHC.add hE0 |>.trans
    (by rw [zero_add])) (Eventually.of_forall fun x => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < x ^ windowExponent := by positivity
  have hhx : x ^ windowExponent ≤ x := by
    calc x ^ windowExponent ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hθ1.le
      _ = x := Real.rpow_one x
  have hcop : ∀ n : ℕ, n.Coprime q → (1 : DirichletCharacter ℂ q) n = (fun _ => (1 : ℂ)) n := by
    intro n hn
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn)
  have hcmp := norm_window_sub_le (1 : DirichletCharacter ℂ q) (fun _ => (1 : ℂ))
    (fun _ => by simp) hcop hx0 hh0.le hhx
  have hpsi : ∑ n ∈ Ioc ⌊x⌋₊ ⌊x + x ^ windowExponent⌋₊, (fun _ => (1 : ℂ)) n *
      ((vonMangoldt n : ℝ) : ℂ)
      = ((Chebyshev.psi (x + x ^ windowExponent) - Chebyshev.psi x : ℝ) : ℂ) := by
    rw [← psi_mono_window (by linarith) hx0.le]
    push_cast
    simp
  rw [hpsi] at hcmp
  set A := psiChi (1 : DirichletCharacter ℂ q) (x + x ^ windowExponent) -
    psiChi (1 : DirichletCharacter ℂ q) x
  set B := Chebyshev.psi (x + x ^ windowExponent) - Chebyshev.psi x
  have hhC : ((x ^ windowExponent : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh0.ne'
  have : A / ((x ^ windowExponent : ℝ) : ℂ) - 1
      = ((B / x ^ windowExponent : ℝ) : ℂ) - 1 + (A - (B : ℂ)) / ((x ^ windowExponent : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
  exact div_le_div_of_nonneg_right hcmp hh0.le

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
