import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionAbs

/-!
# Growth of `Re (ξ'/ξ)` on the line `Re s = 1`

Twice the real part of `ξ'/ξ(s)` is the series of reflection-paired resolvent terms
`(Re s − β)/|s − ρ|² + (Re s − (1 − β))/|s − (1 − ρ)|²` over the divisor copies, every term being
positive for `Re s ≥ 1`.  At `s = 1 + 2it` the copies with ordinate in `(t, 3t]` already give a
lower bound: each such term is at least `(1 − β)/(1 + t²)`, the Littlewood zero-free region gives
`1 − β ≥ c·log log t / log(3t)`, and the Riemann–von Mangoldt asymptotic gives at least
`t·log t/(2π)` copies in the window.  Hence

`Re (ξ'/ξ)(1 + 2it) ≥ c₁ · log log t / t` for all large `t`,

so `t · Re (ξ'/ξ)(1 + 2it)` exceeds every constant eventually.  For the two-rate horizon clock at
a critical-line point `ρ = 1/2 + it` this is the statement that the constant-mode weight
`c₀(ρ) = 4|ξ(1+2it)|²·Re (ξ'/ξ)(1+2it)` exceeds `A·|ξ(1+2it)|²/t` for every `A`, which is the
lower bound the on-line sign comparison against the bulk spectral weight requires.
-/

open Complex

namespace RHTower

noncomputable section

/-- The paired resolvent term as a function of the support point. -/
def xiPairedSupportTerm (s : ℂ) (ρ : XiDivisorSupport) : ℝ :=
  (s.re - (ρ : ℂ).re) / normSq (s - (ρ : ℂ)) +
    (s.re - (1 - (ρ : ℂ).re)) / normSq (s - (1 - (ρ : ℂ)))

theorem xiPairedResolventTerm_eq_support (s : ℂ) (q : XiZeroCopy) :
    xiPairedResolventTerm s q = xiPairedSupportTerm s q.1 := rfl

/-- All divisor copies over a finite set of supports. -/
def xiCopiesOf (W : Finset XiDivisorSupport) : Finset XiZeroCopy :=
  W.sigma (fun _ => Finset.univ)

/-- Summing a support function over the copies weights it by the multiplicity. -/
theorem sum_xiCopiesOf (s : ℂ) (W : Finset XiDivisorSupport) :
    ∑ q ∈ xiCopiesOf W, xiPairedResolventTerm s q =
      ∑ ρ ∈ W, (xiSupportMultiplicity ρ : ℝ) * xiPairedSupportTerm s ρ := by
  unfold xiCopiesOf
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  have hconst : ∀ i ∈ (Finset.univ : Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ)
      (ρ : ℂ))))), xiPairedResolventTerm s ⟨ρ, i⟩ = xiPairedSupportTerm s ρ := fun _ _ => rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rfl

theorem xiSupportsPos_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : xiSupportsPos T₁ ⊆ xiSupportsPos T₂ := by
  intro ρ hρ
  rw [mem_xiSupportsPos] at hρ ⊢
  exact ⟨hρ.1.trans h, hρ.2⟩

/-- Supports with ordinate in `(T₁, T₂]`. -/
def xiSupportsWindow (T₁ T₂ : ℝ) : Finset XiDivisorSupport :=
  xiSupportsPos T₂ \ xiSupportsPos T₁

theorem mem_xiSupportsWindow {T₁ T₂ : ℝ} (h0 : 0 ≤ T₁) {ρ : XiDivisorSupport} :
    ρ ∈ xiSupportsWindow T₁ T₂ ↔ T₁ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T₂ := by
  unfold xiSupportsWindow
  rw [Finset.mem_sdiff, mem_xiSupportsPos, mem_xiSupportsPos]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hnot : ¬ |(ρ : ℂ).im| ≤ T₁ := fun h' => h3 ⟨h', h2⟩
    rw [abs_of_pos h2] at h1 hnot
    exact ⟨lt_of_not_ge hnot, h1⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < (ρ : ℂ).im := by linarith
    refine ⟨⟨by rw [abs_of_pos hpos]; exact h2, hpos⟩, fun h' => ?_⟩
    rw [abs_of_pos hpos] at h'
    linarith [h'.1]

/-- The multiplicity-weighted size of a window is the difference of the counting function. -/
theorem sum_mult_xiSupportsWindow {T₁ T₂ : ℝ} (h0 : 0 ≤ T₁) (h : T₁ ≤ T₂) :
    ∑ ρ ∈ xiSupportsWindow T₁ T₂, (xiSupportMultiplicity ρ : ℝ) =
      (xiZeroCount T₂ : ℝ) - (xiZeroCount T₁ : ℝ) := by
  classical
  have hsub := xiSupportsPos_mono h
  have hsd := Finset.sum_sdiff (f := fun ρ => (xiSupportMultiplicity ρ : ℝ)) hsub
  have e1 : (xiZeroCount T₁ : ℝ) = ∑ ρ ∈ xiSupportsPos T₁, (xiSupportMultiplicity ρ : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (xiZeroCount_eq_pos_sum h0)
    push_cast at this
    exact this
  have e2 : (xiZeroCount T₂ : ℝ) = ∑ ρ ∈ xiSupportsPos T₂, (xiSupportMultiplicity ρ : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) (xiZeroCount_eq_pos_sum (h0.trans h))
    push_cast at this
    exact this
  unfold xiSupportsWindow
  linarith [hsd, e1, e2]

/-- On `Re s = 1` the paired support term is at least `(1 − β)/|s − ρ|²`. -/
theorem xiPairedSupportTerm_ge {s : ℂ} (hs : s.re = 1) (ρ : XiDivisorSupport) :
    (1 - (ρ : ℂ).re) / normSq (s - (ρ : ℂ)) ≤ xiPairedSupportTerm s ρ := by
  unfold xiPairedSupportTerm
  rw [hs]
  obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit ρ
  have hne : s - (1 - (ρ : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re, hs] at this
    linarith
  have h2 : 0 ≤ (1 - (1 - (ρ : ℂ).re)) / normSq (s - (1 - (ρ : ℂ))) :=
    div_nonneg (by linarith) (Complex.normSq_pos.mpr hne).le
  linarith

/-- The Littlewood zero-free region bounds `1 − β` from below at every support of large ordinate. -/
theorem one_sub_re_ge_of_littlewood {c T : ℝ}
    (hzf : ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 →
      1 - c * Real.log (Real.log |γ|) / Real.log |γ| < β →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0)
    (ρ : XiDivisorSupport) (hT : T ≤ |(ρ : ℂ).im|) :
    c * Real.log (Real.log |(ρ : ℂ).im|) / Real.log |(ρ : ℂ).im| ≤ 1 - (ρ : ℂ).re := by
  obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit ρ
  have hzero : xi (ρ : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support ρ
  have hne1 : (ρ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.one_re] at this
    linarith
  have hzeta : riemannZeta (ρ : ℂ) = 0 := (xi_eq_zero_iff hβ0 hne1).mp hzero
  by_contra hlt
  push Not at hlt
  have hform : ((((ρ : ℂ).re : ℝ) : ℂ) + (((ρ : ℂ).im : ℝ) : ℂ) * Complex.I) = (ρ : ℂ) :=
    Complex.re_add_im (ρ : ℂ)
  have := hzf (ρ : ℂ).re (ρ : ℂ).im hT hβ1.le (by linarith)
  rw [hform] at this
  exact this hzeta

/-- **Growth of `Re (ξ'/ξ)` on `Re s = 1`.**  There are `c₁ > 0` and `t₀` with
`c₁ · log log t / t ≤ Re (ξ'/ξ)(1 + 2it)` for all `t ≥ t₀`. -/
theorem exists_re_logDeriv_xi_lineOne_loglog_lower :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ t₀ : ℝ, 16 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      c₁ * Real.log (Real.log t) / t ≤ (logDeriv xi (1 + 2 * t * I)).re := by
  classical
  obtain ⟨c, TL, hc, hTL, hzf⟩ := Sieve.exists_littlewood_zero_free_region_abs
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨T₀, hT₀, hN⟩ := exists_xiZeroCount_close (1 / (16 * Real.pi)) (by positivity)
  refine ⟨c / (16 * Real.pi), by positivity, max (max T₀ TL) 16, le_max_right _ _, ?_⟩
  intro t ht
  have ht16 : (16 : ℝ) ≤ t := (le_max_right _ _).trans ht
  have htT₀ : T₀ ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
  have htTL : TL ≤ t := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) < t := by linarith
  -- logarithms
  have hlogt : (1 : ℝ) ≤ Real.log t := by
    have h : Real.log (Real.exp 1) ≤ Real.log t :=
      Real.log_le_log (Real.exp_pos 1) ((Real.exp_one_lt_d9.le.trans (by norm_num)).trans ht16)
    rwa [Real.log_exp] at h
  have hloglog : (0 : ℝ) ≤ Real.log (Real.log t) := Real.log_nonneg hlogt
  have hlog3t : Real.log (3 * t) ≤ 2 * Real.log t := by
    rw [Real.log_mul (by norm_num) ht0.ne']
    have : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlog3t_pos : 0 < Real.log (3 * t) := Real.log_pos (by linarith)
  -- the window and the lower bound of each term
  set s : ℂ := 1 + 2 * t * I with hsdef
  have hs1 : s.re = 1 := by simp [hsdef]
  have hsne : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hs1])
  set m : ℝ := c * Real.log (Real.log t) / Real.log (3 * t) / (1 + t ^ (2 : ℕ)) with hmdef
  have hm0 : 0 ≤ m := by positivity
  have hterm : ∀ ρ ∈ xiSupportsWindow t (3 * t), m ≤ xiPairedSupportTerm s ρ := by
    intro ρ hρ
    rw [mem_xiSupportsWindow ht0.le] at hρ
    obtain ⟨hγ1, hγ2⟩ := hρ
    have hγpos : 0 < (ρ : ℂ).im := by linarith
    have habs : |(ρ : ℂ).im| = (ρ : ℂ).im := abs_of_pos hγpos
    obtain ⟨hβ0, hβ1⟩ := xi_divisor_support_re_mem_open_unit ρ
    -- zero-free region
    have hzf' := one_sub_re_ge_of_littlewood hzf ρ (by rw [habs]; linarith)
    rw [habs] at hzf'
    -- monotonicity of the zero-free width in the ordinate
    have hlogγ : Real.log t ≤ Real.log (ρ : ℂ).im := Real.log_le_log ht0 hγ1.le
    have hlogγ3 : Real.log (ρ : ℂ).im ≤ Real.log (3 * t) := Real.log_le_log hγpos hγ2
    have hloglogγ : Real.log (Real.log t) ≤ Real.log (Real.log (ρ : ℂ).im) :=
      Real.log_le_log (by linarith) hlogγ
    have hwidth : c * Real.log (Real.log t) / Real.log (3 * t) ≤
        c * Real.log (Real.log (ρ : ℂ).im) / Real.log (ρ : ℂ).im := by
      have hnum : c * Real.log (Real.log t) ≤ c * Real.log (Real.log (ρ : ℂ).im) :=
        mul_le_mul_of_nonneg_left hloglogγ hc.le
      have hlogγpos : 0 < Real.log (ρ : ℂ).im := by linarith
      calc c * Real.log (Real.log t) / Real.log (3 * t)
          ≤ c * Real.log (Real.log (ρ : ℂ).im) / Real.log (3 * t) :=
            div_le_div_of_nonneg_right hnum hlog3t_pos.le
        _ ≤ c * Real.log (Real.log (ρ : ℂ).im) / Real.log (ρ : ℂ).im :=
            div_le_div_of_nonneg_left
              (mul_nonneg hc.le (Real.log_nonneg (by linarith))) hlogγpos hlogγ3
    have h1β : c * Real.log (Real.log t) / Real.log (3 * t) ≤ 1 - (ρ : ℂ).re :=
      hwidth.trans hzf'
    -- the modulus bound
    have hnormSq : normSq (s - (ρ : ℂ)) ≤ 1 + t ^ (2 : ℕ) := by
      rw [Complex.normSq_apply]
      have hre : (s - (ρ : ℂ)).re = 1 - (ρ : ℂ).re := by simp [hsdef]
      have him : (s - (ρ : ℂ)).im = 2 * t - (ρ : ℂ).im := by simp [hsdef]
      rw [hre, him]
      nlinarith
    have hnormSq_pos : 0 < normSq (s - (ρ : ℂ)) := by
      apply Complex.normSq_pos.mpr
      intro h
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.zero_re, hs1] at this
      linarith
    calc m = c * Real.log (Real.log t) / Real.log (3 * t) / (1 + t ^ (2 : ℕ)) := rfl
      _ ≤ (1 - (ρ : ℂ).re) / (1 + t ^ (2 : ℕ)) := div_le_div_of_nonneg_right h1β (by positivity)
      _ ≤ (1 - (ρ : ℂ).re) / normSq (s - (ρ : ℂ)) :=
          div_le_div_of_nonneg_left (by linarith) hnormSq_pos hnormSq
      _ ≤ xiPairedSupportTerm s ρ := xiPairedSupportTerm_ge hs1 ρ
  -- the window count from Riemann–von Mangoldt
  have hcount : t * Real.log t / (2 * Real.pi) ≤
      (xiZeroCount (3 * t) : ℝ) - (xiZeroCount t : ℝ) := by
    have hA := hN t htT₀
    have hB := hN (3 * t) (by linarith)
    rw [abs_le] at hA hB
    have h3log : Real.log (3 * t) * (3 * t) ≥ 3 * t * Real.log t := by
      have : Real.log t ≤ Real.log (3 * t) := Real.log_le_log ht0 (by linarith)
      nlinarith
    have hup : 3 * t * Real.log (3 * t) ≤ 6 * t * Real.log t := by nlinarith
    have hpos_tl : 0 ≤ t * Real.log t := by positivity
    have key1 : (1 / (2 * Real.pi)) * (3 * t * Real.log (3 * t)) -
        (1 / (16 * Real.pi)) * (3 * t * Real.log (3 * t)) ≤ (xiZeroCount (3 * t) : ℝ) := by
      linarith [hB.1]
    have key2 : (xiZeroCount t : ℝ) ≤ (1 / (2 * Real.pi)) * (t * Real.log t) +
        (1 / (16 * Real.pi)) * (t * Real.log t) := by linarith [hA.2]
    have hinv : 0 < 1 / (16 * Real.pi) := by positivity
    -- (3/(2π) − 3/(16π))·(t log t) − (1/(2π) + 1/(16π))·(t log t) = (3/2 − 3/16 − 1/2 − 1/16)/π = 3/4 /π ≥ 1/(2π)
    have hmain : (1 / (2 * Real.pi)) * (3 * t * Real.log (3 * t)) -
        (1 / (16 * Real.pi)) * (3 * t * Real.log (3 * t)) -
        ((1 / (2 * Real.pi)) * (t * Real.log t) + (1 / (16 * Real.pi)) * (t * Real.log t)) ≥
        t * Real.log t / (2 * Real.pi) := by
      have hπ2 : 0 < 1 / (2 * Real.pi) := by positivity
      have e : (1 / (2 * Real.pi)) * (3 * t * Real.log (3 * t)) -
          (1 / (16 * Real.pi)) * (3 * t * Real.log (3 * t)) =
          (7 / (16 * Real.pi)) * (3 * t * Real.log (3 * t)) := by field_simp; ring
      rw [e]
      have hge : (7 / (16 * Real.pi)) * (3 * t * Real.log (3 * t)) ≥
          (7 / (16 * Real.pi)) * (3 * t * Real.log t) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have e2 : (7 / (16 * Real.pi)) * (3 * t * Real.log t) -
          ((1 / (2 * Real.pi)) * (t * Real.log t) + (1 / (16 * Real.pi)) * (t * Real.log t)) =
          (12 / (16 * Real.pi)) * (t * Real.log t) := by field_simp; ring
      have e3 : t * Real.log t / (2 * Real.pi) = (8 / (16 * Real.pi)) * (t * Real.log t) := by
        field_simp; ring
      rw [e3]
      have : (8 / (16 * Real.pi)) * (t * Real.log t) ≤ (12 / (16 * Real.pi)) * (t * Real.log t) :=
        mul_le_mul_of_nonneg_right (by
          apply div_le_div_of_nonneg_right (by norm_num) (by positivity)) hpos_tl
      linarith
    linarith
  -- assemble
  have hsum := summable_xiPairedResolventTerm hsne
  have hwin : ∑ q ∈ xiCopiesOf (xiSupportsWindow t (3 * t)), xiPairedResolventTerm s q ≤
      ∑' q : XiZeroCopy, xiPairedResolventTerm s q :=
    hsum.sum_le_tsum _ (fun q _ => (xiPairedResolventTerm_pos (by rw [hs1]) q).le)
  rw [sum_xiCopiesOf] at hwin
  have hlow : ∑ ρ ∈ xiSupportsWindow t (3 * t), (xiSupportMultiplicity ρ : ℝ) * m ≤
      ∑ ρ ∈ xiSupportsWindow t (3 * t),
        (xiSupportMultiplicity ρ : ℝ) * xiPairedSupportTerm s ρ :=
    Finset.sum_le_sum (fun ρ hρ => mul_le_mul_of_nonneg_left (hterm ρ hρ) (by positivity))
  rw [← Finset.sum_mul, sum_mult_xiSupportsWindow ht0.le (by linarith)] at hlow
  have htwice := two_mul_re_logDeriv_xi_eq_tsum_paired hsne
  -- 2 Re ≥ (N(3t) − N(t)) m ≥ (t log t/(2π)) m
  have hprod : t * Real.log t / (2 * Real.pi) * m ≤
      ((xiZeroCount (3 * t) : ℝ) - (xiZeroCount t : ℝ)) * m :=
    mul_le_mul_of_nonneg_right hcount hm0
  have h2re : t * Real.log t / (2 * Real.pi) * m ≤ 2 * (logDeriv xi s).re := by
    linarith
  -- finish: m ≥ c log log t /(2 log t · 2 t²)
  have hm_ge : c * Real.log (Real.log t) / (4 * Real.log t * t ^ (2 : ℕ)) ≤ m := by
    rw [hmdef]
    have hden1 : 1 + t ^ (2 : ℕ) ≤ 2 * t ^ (2 : ℕ) := by nlinarith
    have hlogt_pos : 0 < Real.log t := by linarith
    calc c * Real.log (Real.log t) / (4 * Real.log t * t ^ (2 : ℕ))
        = c * Real.log (Real.log t) / (2 * Real.log t) / (2 * t ^ (2 : ℕ)) := by
          field_simp
          ring
      _ ≤ c * Real.log (Real.log t) / Real.log (3 * t) / (2 * t ^ (2 : ℕ)) :=
          div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_left (by positivity) hlog3t_pos hlog3t) (by positivity)
      _ ≤ c * Real.log (Real.log t) / Real.log (3 * t) / (1 + t ^ (2 : ℕ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden1
  have hfinal : c / (16 * Real.pi) * Real.log (Real.log t) / t ≤
      t * Real.log t / (2 * Real.pi) * (c * Real.log (Real.log t) / (4 * Real.log t * t ^ (2 : ℕ))) / 2 := by
    have hlogt_pos : 0 < Real.log t := by linarith
    have e : t * Real.log t / (2 * Real.pi) * (c * Real.log (Real.log t) / (4 * Real.log t * t ^ (2 : ℕ))) / 2
        = c / (16 * Real.pi) * Real.log (Real.log t) / t := by
      field_simp
      ring
    rw [e]
  have hchain : t * Real.log t / (2 * Real.pi) * (c * Real.log (Real.log t) / (4 * Real.log t * t ^ (2 : ℕ))) ≤
      t * Real.log t / (2 * Real.pi) * m :=
    mul_le_mul_of_nonneg_left hm_ge (by positivity)
  linarith

/-- **Corollary.**  `t · Re (ξ'/ξ)(1+2it)` eventually exceeds every constant. -/
theorem exists_re_logDeriv_xi_lineOne_ge_div (A : ℝ) :
    ∃ t₀ : ℝ, 16 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → A / t ≤ (logDeriv xi (1 + 2 * t * I)).re := by
  obtain ⟨c₁, hc₁, t₀, ht₀, h⟩ := exists_re_logDeriv_xi_lineOne_loglog_lower
  -- choose t₁ with log log t₁ ≥ A / c₁
  refine ⟨max t₀ (Real.exp (Real.exp (max (A / c₁) 1))), ?_, ?_⟩
  · exact ht₀.trans (le_max_left _ _)
  · intro t ht
    have ht₀' : t₀ ≤ t := (le_max_left _ _).trans ht
    have hexp : Real.exp (Real.exp (max (A / c₁) 1)) ≤ t := (le_max_right _ _).trans ht
    have ht0 : (0 : ℝ) < t := by
      have := ht₀.trans ht₀'
      linarith
    have hll : max (A / c₁) 1 ≤ Real.log (Real.log t) := by
      have h1 : Real.exp (max (A / c₁) 1) ≤ Real.log t := by
        have := Real.log_le_log (Real.exp_pos _) hexp
        rwa [Real.log_exp] at this
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have hA : A / c₁ ≤ Real.log (Real.log t) := (le_max_left _ _).trans hll
    have hmain := h t ht₀'
    have hAle : A / t ≤ c₁ * Real.log (Real.log t) / t := by
      apply div_le_div_of_nonneg_right _ ht0.le
      have := mul_le_mul_of_nonneg_left hA hc₁.le
      rwa [mul_div_cancel₀ _ hc₁.ne'] at this
    exact hAle.trans hmain

end

end RHTower
