import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistGradedBound
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistCollapsedBound
import GaloisForLFunctions.RHTower.Sieve.ChebyshevDecayAtChoice
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSeriesBound
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# The twisted Route-T bound at balanced contour parameters

Two of the three free parameters are fixed against the twist and the cutoff,

```text
d = 1 + 1/log N,        T = |τ|/2,
```

and the smoothing width is left free.  The truncation height is half the twist — the largest value
the no-pole regime allows — which makes the contour parameter `K = 3|τ|/2` a function of the twist
alone; the Perron abscissa is the usual one, so the Dirichlet series at it costs `(log N)²`.

What survives is a single inequality in `N`, `H` and `τ`:

```text
‖2π ∑ₙ Λ(n) n^{-iτ} w(n)‖
  ≤ C·N·(N/H)²·[ (log N)²/|τ| + (1/|τ| + log K/w(K+1))·((3N)^{-W(K)} + |τ|^{-2}) ].
```

The width enters only through `(N/H)²`, the square of the cutoff-to-window ratio, which is the exact
cost of the cutoff's order-two Mellin decay.  Against it stands the arithmetic saving
`(3N)^{-W(K)} = exp(-W(K)·log 3N)` bought by the Route-T zero-free width, and the contour is
worthwhile precisely when `W(K)·log N` beats `2 log(N/H)` — which is also the condition under which
removing the smoothing afterwards costs less than the contour saves.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The graded Mellin constant of a smoothed cutoff. -/
noncomputable def twistMellinConst (Cj N H σ' : ℝ) : ℝ :=
  Cj / H ^ (1 + 1) * (N + H + 1) ^ (1 + 1 : ℕ) * (N + H + 1) ^ σ'

/-- **The graded Mellin constant at a free width.**  The width enters only through the square of
the cutoff-to-window ratio; the abscissa contributes one power of the support. -/
theorem twistMellinConst_le {N H Cj σ' : ℝ} (hN : 1 ≤ N) (hH0 : 0 < H) (hHN : H + 1 ≤ 2 * N)
    (hCj : 0 ≤ Cj) (hσ0 : 0 ≤ σ') :
    twistMellinConst Cj N H σ' ≤ 9 * Cj * (N / H) ^ 2 * (3 * N) ^ σ' := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hY3 : N + H + 1 ≤ 3 * N := by linarith
  have hY0 : (0 : ℝ) ≤ N + H + 1 := by positivity
  have hrp : (N + H + 1) ^ σ' ≤ (3 * N) ^ σ' := Real.rpow_le_rpow hY0 hY3 hσ0
  have hrp0 : (0 : ℝ) ≤ (N + H + 1) ^ σ' := Real.rpow_nonneg hY0 _
  have hpow : (N + H + 1) ^ (1 + 1 : ℕ) ≤ (3 * N) ^ (1 + 1 : ℕ) :=
    pow_le_pow_left₀ hY0 hY3 _
  have hCH : (0 : ℝ) ≤ Cj / H ^ (1 + 1) := by positivity
  have hid : Cj / H ^ (1 + 1) * (3 * N) ^ (1 + 1 : ℕ) = 9 * Cj * (N / H) ^ 2 := by
    field_simp
    ring
  have hcoef : Cj / H ^ (1 + 1) * (N + H + 1) ^ (1 + 1 : ℕ) ≤ 9 * Cj * (N / H) ^ 2 := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hpow hCH
  have hE0 : (0 : ℝ) ≤ 9 * Cj * (N / H) ^ 2 := by positivity
  unfold twistMellinConst
  calc Cj / H ^ (1 + 1) * (N + H + 1) ^ (1 + 1 : ℕ) * (N + H + 1) ^ σ'
      ≤ (9 * Cj * (N / H) ^ 2) * (N + H + 1) ^ σ' := mul_le_mul_of_nonneg_right hcoef hrp0
    _ ≤ (9 * Cj * (N / H) ^ 2) * (3 * N) ^ σ' := mul_le_mul_of_nonneg_left hrp hE0

/-- `e² ≤ 8`. -/
theorem exp_two_le_eight : Real.exp 2 ≤ 8 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- **The support power at the Perron abscissa.**  With `d = 1 + 1/log N` the support factor is at
most a constant times the cutoff. -/
theorem rpow_three_mul_perron_le {N : ℝ} (hN : 1 ≤ N) (hL : 9 ≤ Real.log N) :
    (3 * N) ^ (1 + 1 / Real.log N) ≤ 24 * N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have h3N : (0 : ℝ) < 3 * N := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith
  have hlog3N : Real.log (3 * N) = Real.log 3 + Real.log N := by
    rw [Real.log_mul (by norm_num) hN0.ne']
  have hsplit : (3 * N) ^ (1 + 1 / Real.log N)
      = (3 * N) * (3 * N) ^ (1 / Real.log N) := by
    rw [Real.rpow_add h3N, Real.rpow_one]
  have hfrac : (3 * N) ^ (1 / Real.log N) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos h3N, hlog3N]
    refine Real.exp_le_exp.2 ?_
    rw [mul_one_div, div_le_iff₀ hL0]
    linarith
  have hexp8 := exp_two_le_eight
  rw [hsplit]
  nlinarith [Real.rpow_nonneg h3N.le (1 / Real.log N)]

/-- **The support power at the contour abscissa** splits off the saving. -/
theorem rpow_three_mul_contour {N A delta K : ℝ} (hN : 1 ≤ N) :
    (3 * N) ^ routeTTwistAbscissa A delta K
      = 3 * N * (3 * N) ^ (-(routeTUniformRegWidth A delta K)) := by
  have h3N : (0 : ℝ) < 3 * N := by linarith
  rw [routeTTwistAbscissa_eq, show (1 : ℝ) - routeTUniformRegWidth A delta K
      = 1 + -(routeTUniformRegWidth A delta K) by ring,
    Real.rpow_add h3N, Real.rpow_one]

set_option maxHeartbeats 2000000 in
/-- **The twisted Route-T bound at balanced parameters.**  One explicit inequality in the cutoff and
the twist alone: the truncation tail decays like `1/|τ|`, the horizontal edges like `1/|τ|²`, and the
left edge carries the arithmetic saving `(3N)^{-W}` bought by the Route-T zero-free width. -/
theorem exists_norm_tsum_vonMangoldtTwist_routeT_balanced :
    ∃ A Creg delta Ctot τ₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ N H τ : ℝ, Real.exp 9 ≤ N → 0 < H → H ≤ N → τ₀ ≤ |τ| →
        ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, vonMangoldtTwist τ n
            * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
          ≤ Ctot * N * (N / H) ^ 2
              * ((Real.log N) ^ 2 / |τ|
                  + (1 / |τ| + Real.log (3 * |τ| / 2)
                      / routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
                    * ((3 * N) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                        + 1 / |τ| ^ 2)) := by
  obtain ⟨A, Creg, delta, K₀, hCreg, hdelta, hK₀, hgraded⟩ :=
    exists_norm_tsum_vonMangoldtTwist_routeT_graded
  obtain ⟨Cj, hCj, hmell⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  set c₁ : ℝ := max 2 Creg with hc₁def
  set c₂ : ℝ := 486 * Cj + 12 with hc₂def
  have hc₁0 : (0 : ℝ) < c₁ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc₂0 : (0 : ℝ) < c₂ := by rw [hc₂def]; positivity
  refine ⟨A, Creg, delta, max (6912 * Cj) (c₁ * c₂) + 1, max 2 K₀, hCreg, hdelta, ?_,
    le_max_left _ _, ?_⟩
  · have h0 : (0 : ℝ) ≤ max (6912 * Cj) (c₁ * c₂) :=
      le_trans (by positivity) (le_max_left _ _)
    linarith
  intro N H τ hN hH0 hHN hτ
  set Ctot : ℝ := max (6912 * Cj) (c₁ * c₂) + 1 with hCtotdef
  have hCtot1 : 6912 * Cj ≤ Ctot := by
    rw [hCtotdef]; linarith [le_max_left (6912 * Cj) (c₁ * c₂)]
  have hCtot2 : c₁ * c₂ ≤ Ctot := by
    rw [hCtotdef]; linarith [le_max_right (6912 * Cj) (c₁ * c₂)]
  -- the cutoff
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hN
  have hL : (9 : ℝ) ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 hN
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by
    have h := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 9)
    linarith
  set L : ℝ := Real.log N with hLdef
  set E : ℝ := (N / H) ^ 2 with hEdef
  have hE1 : (1 : ℝ) ≤ E := by
    rw [hEdef]
    have hratio : (1 : ℝ) ≤ N / H := (one_le_div hH0).2 hHN
    nlinarith
  have hE0 : (0 : ℝ) < E := by linarith
  -- the twist
  have hτ2 : (2 : ℝ) ≤ |τ| := le_trans (le_max_left _ _) hτ
  have hτK : K₀ ≤ |τ| := le_trans (le_max_right _ _) hτ
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  set d : ℝ := 1 + 1 / L with hddef
  have hd : (1 : ℝ) < d := by
    rw [hddef]
    have hpos : (0 : ℝ) < 1 / L := by positivity
    linarith
  have hd98 : d ≤ 9 / 8 := by
    rw [hddef]
    have : 1 / L ≤ 1 / 9 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
    linarith
  have hd2 : d ≤ 2 := by linarith
  set T : ℝ := |τ| / 2 with hTdef
  have hT1 : (1 : ℝ) ≤ T := by rw [hTdef]; linarith
  have hTτ : T < |τ| := by rw [hTdef]; linarith
  have hKeq : |τ| + T = 3 * |τ| / 2 := by rw [hTdef]; ring
  have hKK : K₀ ≤ |τ| + T := by rw [hKeq]; linarith
  -- the graded estimate at these parameters
  set Cfun : ℝ → ℝ := twistMellinConst Cj N H with hCfundef
  have hbd : ∀ σ' : ℝ, σ' ≤ d → ∀ s : ℂ, 0 < s.re → s.re ≤ σ' →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cfun σ' := by
    intro σ' _ s hs1 hs2
    exact hmell N H hN0 hH0 σ' s hs1 hs2
  have hg := hgraded N H d T τ Cfun hN0 hH0 hd hd98 hT1 hTτ hKK hbd
  rw [hKeq] at hg
  set σ : ℝ := routeTTwistAbscissa A delta (3 * |τ| / 2) with hσdef
  set W : ℝ := routeTUniformRegWidth A delta (3 * |τ| / 2) with hWdef
  set Lk : ℝ := Real.log (3 * |τ| / 2) with hLkdef
  set w : ℝ := routeTZeroFreeWidth A (3 * |τ| / 2 + 1) with hwdef
  set S : ℝ := (3 * N) ^ (-W) with hSdef
  have hw0 : (0 : ℝ) < w := by rw [hwdef]; exact routeTZeroFreeWidth_pos A _
  have hLk0 : (0 : ℝ) ≤ Lk := by rw [hLkdef]; exact Real.log_nonneg (by linarith)
  have hS0 : (0 : ℝ) < S := by rw [hSdef]; exact Real.rpow_pos_of_pos (by linarith) _
  have hσ0 : (0 : ℝ) < σ := by rw [hσdef]; exact routeTTwistAbscissa_pos A delta _
  have hσ1 : σ < 1 := by rw [hσdef]; exact routeTTwistAbscissa_lt_one hdelta
  have hσhalf : 1 / 2 ≤ σ := by rw [hσdef]; exact routeTTwistAbscissa_ge_half A delta _
  have hσlow : 1 - 1 / 320 ≤ σ := by rw [hσdef]; exact routeTTwistAbscissa_ge_one_sub A delta _
  have hinv : (|τ| - T)⁻¹ = 2 / |τ| := by
    rw [hTdef, show |τ| - |τ| / 2 = |τ| / 2 by ring, inv_div]
  rw [hinv] at hg
  -- the two Mellin constants
  have hCd : Cfun d ≤ 216 * Cj * N * E := by
    have h1 := twistMellinConst_le (N := N) (H := H) (Cj := Cj) (σ' := d) hN1 hH0
      (by linarith) hCj (by linarith)
    have h2 : (3 * N) ^ d ≤ 24 * N := by
      rw [hddef]; exact rpow_three_mul_perron_le hN1 hL
    have h3 : (0 : ℝ) ≤ 9 * Cj * E := by positivity
    have h4 : 9 * Cj * E * (3 * N) ^ d ≤ 9 * Cj * E * (24 * N) :=
      mul_le_mul_of_nonneg_left h2 h3
    rw [hCfundef]
    calc twistMellinConst Cj N H d ≤ 9 * Cj * E * (3 * N) ^ d := h1
      _ ≤ 9 * Cj * E * (24 * N) := h4
      _ = 216 * Cj * N * E := by ring
  have hCσ : Cfun σ ≤ 27 * Cj * N * E * S := by
    have h1 := twistMellinConst_le (N := N) (H := H) (Cj := Cj) (σ' := σ) hN1 hH0
      (by linarith) hCj (by linarith)
    have h2 : (3 * N) ^ σ = 3 * N * S := by
      rw [hσdef, hSdef, hWdef]
      exact rpow_three_mul_contour hN1
    rw [hCfundef]
    calc twistMellinConst Cj N H σ ≤ 9 * Cj * E * (3 * N) ^ σ := h1
      _ = 9 * Cj * E * (3 * N * S) := by rw [h2]
      _ = 27 * Cj * N * E * S := by ring
  have hCd0 : (0 : ℝ) ≤ Cfun d := by
    rw [hCfundef]
    unfold twistMellinConst
    have h : (0 : ℝ) ≤ (N + H + 1) ^ d := Real.rpow_nonneg (by positivity) _
    positivity
  have hCσ0 : (0 : ℝ) ≤ Cfun σ := by
    rw [hCfundef]
    unfold twistMellinConst
    have h : (0 : ℝ) ≤ (N + H + 1) ^ σ := Real.rpow_nonneg (by positivity) _
    positivity
  -- the left-edge power
  have hNH3 : N + H ≤ 3 * N := by linarith
  have hV : 2 * ((N + H) ^ σ / σ) ≤ 12 * N * S := by
    have hp1 : (N + H) ^ σ ≤ (3 * N) ^ σ :=
      Real.rpow_le_rpow (by positivity) hNH3 (by linarith)
    have hp2 : (3 * N) ^ σ = 3 * N * S := by
      rw [hσdef, hSdef, hWdef]; exact rpow_three_mul_contour hN1
    have hp0 : (0 : ℝ) ≤ (N + H) ^ σ := Real.rpow_nonneg (by positivity) _
    have hdiv : (N + H) ^ σ / σ ≤ 2 * (N + H) ^ σ := by
      rw [div_le_iff₀ hσ0]
      nlinarith [hp0, hσhalf]
    calc 2 * ((N + H) ^ σ / σ) ≤ 2 * (2 * (N + H) ^ σ) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 4 * (N + H) ^ σ := by ring
      _ ≤ 4 * (3 * N) ^ σ := mul_le_mul_of_nonneg_left hp1 (by norm_num)
      _ = 4 * (3 * N * S) := by rw [hp2]
      _ = 12 * N * S := by ring
  -- the Dirichlet series
  have hSer : (∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) ≤ 8 * L ^ 2 := by
    have h := tsum_vonMangoldt_rpow_neg_le hd hd2
    have he : (d - 1) ^ 2 = (1 / L) ^ 2 := by rw [hddef]; ring
    rw [he] at h
    have : (8 : ℝ) / (1 / L) ^ 2 = 8 * L ^ 2 := by field_simp
    linarith [h, this.le, this.ge]
  have hSer0 : (0 : ℝ) ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d) :=
    tsum_vonMangoldt_rpow_nonneg
  -- the gap between the abscissae
  have hgap : (0 : ℝ) ≤ d - σ := by linarith
  have hgap4 : d - σ ≤ 1 / 4 := by
    have : 1 / L ≤ 1 / 9 := by rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
    rw [hddef]; linarith
  have hT2 : T ^ 2 = |τ| ^ 2 / 4 := by rw [hTdef]; ring
  -- assemble
  have hMreg0 : (0 : ℝ) ≤ Creg * Lk / w := by positivity
  have hMp0 : (0 : ℝ) ≤ 2 / |τ| := by positivity
  have htail : 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * Cfun d) / T
      ≤ 6912 * Cj * N * E * (L ^ 2 / |τ|) := by
    rw [hTdef]
    have hprod : (∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * Cfun d
        ≤ (8 * L ^ 2) * (216 * Cj * N * E) :=
      mul_le_mul hSer hCd hCd0 (by positivity)
    rw [div_le_iff₀ (by positivity)]
    have hfin : (6912 * Cj * N * E * (L ^ 2 / |τ|)) * (|τ| / 2)
        = 3456 * Cj * N * E * L ^ 2 := by field_simp; ring
    rw [hfin]
    nlinarith [hprod]
  have hbracket : 2 * (Cfun d / T ^ 2 * (d - σ)) + (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ)
      ≤ c₂ * (N * E) * (S + 1 / |τ| ^ 2) := by
    have hT20 : (0 : ℝ) < T ^ 2 := by positivity
    have hX0 : (0 : ℝ) ≤ N * E * S := by positivity
    have hY0 : (0 : ℝ) ≤ N * E * (1 / |τ| ^ 2) := by positivity
    have hq : (216 * Cj * N * E) / T ^ 2 * (1 / 4) = 216 * Cj * (N * E * (1 / |τ| ^ 2)) := by
      rw [hT2]
      field_simp
    have hstep2 : Cfun d / T ^ 2 ≤ (216 * Cj * N * E) / T ^ 2 :=
      div_le_div_of_nonneg_right hCd hT20.le
    have hA : 2 * (Cfun d / T ^ 2 * (d - σ)) ≤ 432 * Cj * (N * E * (1 / |τ| ^ 2)) := by
      have hle : Cfun d / T ^ 2 * (d - σ) ≤ 216 * Cj * (N * E * (1 / |τ| ^ 2)) := by
        calc Cfun d / T ^ 2 * (d - σ) ≤ Cfun d / T ^ 2 * (1 / 4) :=
              mul_le_mul_of_nonneg_left hgap4 (div_nonneg hCd0 hT20.le)
          _ ≤ (216 * Cj * N * E) / T ^ 2 * (1 / 4) :=
              mul_le_mul_of_nonneg_right hstep2 (by norm_num)
          _ = 216 * Cj * (N * E * (1 / |τ| ^ 2)) := hq
      linarith
    have hB : 2 * ((N + H) ^ σ / σ) ≤ 12 * (N * E * S) := by
      have hprod : (0 : ℝ) ≤ N * S * (E - 1) :=
        mul_nonneg (mul_nonneg hN0.le hS0.le) (by linarith)
      nlinarith [hV, hprod]
    have hC : 2 * Cfun σ ≤ 54 * Cj * (N * E * S) := by nlinarith [hCσ]
    have hfinal : 432 * Cj * (N * E * (1 / |τ| ^ 2)) + 12 * (N * E * S) + 54 * Cj * (N * E * S)
        ≤ c₂ * (N * E) * (S + 1 / |τ| ^ 2) := by
      have e : c₂ * (N * E) * (S + 1 / |τ| ^ 2)
          = c₂ * (N * E * S) + c₂ * (N * E * (1 / |τ| ^ 2)) := by ring
      rw [e, hc₂def]
      nlinarith [mul_nonneg hCj hX0, mul_nonneg hCj hY0, hX0, hY0]
    linarith
  have hfac : 2 / |τ| + Creg * Lk / w ≤ c₁ * (1 / |τ| + Lk / w) := by
    have h1 : (2 : ℝ) ≤ c₁ := le_max_left _ _
    have h2 : Creg ≤ c₁ := le_max_right _ _
    have e1 : c₁ * (1 / |τ| + Lk / w) = c₁ * (1 / |τ|) + c₁ * (Lk / w) := by ring
    have e2 : Creg * Lk / w = Creg * (Lk / w) := by ring
    rw [e1, e2]
    have hb1 : (2 : ℝ) / |τ| ≤ c₁ * (1 / |τ|) := by
      rw [show (2:ℝ) / |τ| = 2 * (1 / |τ|) by ring]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hb2 : Creg * (Lk / w) ≤ c₁ * (Lk / w) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have hbr0 : (0 : ℝ) ≤ 2 * (Cfun d / T ^ 2 * (d - σ)) + (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ) := by
    have h1 : (0 : ℝ) ≤ (N + H) ^ σ := Real.rpow_nonneg (by positivity) _
    have h2 : (0 : ℝ) ≤ Cfun d / T ^ 2 * (d - σ) := by positivity
    have h3 : (0 : ℝ) ≤ (N + H) ^ σ / σ := by positivity
    linarith
  have hfac0 : (0 : ℝ) ≤ c₁ * (1 / |τ| + Lk / w) := by positivity
  have hmain : (2 / |τ| + Creg * Lk / w)
        * (2 * (Cfun d / T ^ 2 * (d - σ)) + (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ))
      ≤ Ctot * N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2)) := by
    have hstep : (2 / |τ| + Creg * Lk / w)
        * (2 * (Cfun d / T ^ 2 * (d - σ)) + (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ))
        ≤ (c₁ * (1 / |τ| + Lk / w)) * (c₂ * (N * E) * (S + 1 / |τ| ^ 2)) :=
      mul_le_mul hfac hbracket hbr0 hfac0
    have hrw : (c₁ * (1 / |τ| + Lk / w)) * (c₂ * (N * E) * (S + 1 / |τ| ^ 2))
        = (c₁ * c₂) * (N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2))) := by ring
    rw [hrw] at hstep
    have hrest : (0 : ℝ) ≤ N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2)) := by positivity
    have hfin : (c₁ * c₂) * (N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2)))
        ≤ Ctot * (N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2))) :=
      mul_le_mul_of_nonneg_right hCtot2 hrest
    calc (2 / |τ| + Creg * Lk / w)
          * (2 * (Cfun d / T ^ 2 * (d - σ)) + (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ))
        ≤ (c₁ * c₂) * (N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2))) := hstep
      _ ≤ Ctot * (N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2))) := hfin
      _ = Ctot * N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2)) := by ring
  have hregroup : 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * Cfun d) / T
      + ((2 / |τ| * Cfun d / T ^ 2 * (d - σ) + 2 / |τ| * Cfun d / T ^ 2 * (d - σ)
          + 2 / |τ| * (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ))
        + (Creg * Lk / w * Cfun d / T ^ 2 * (d - σ)
          + Creg * Lk / w * Cfun d / T ^ 2 * (d - σ)
          + Creg * Lk / w * (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ)))
      = 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * Cfun d) / T
        + (2 / |τ| + Creg * Lk / w)
          * (2 * (Cfun d / T ^ 2 * (d - σ)) + (2 * ((N + H) ^ σ / σ) + 2 * Cfun σ)) := by
    ring
  rw [hregroup] at hg
  have htailC : 6912 * Cj * N * E * (L ^ 2 / |τ|) ≤ Ctot * N * E * (L ^ 2 / |τ|) := by
    have hrest : (0 : ℝ) ≤ N * E * (L ^ 2 / |τ|) := by positivity
    have e1 : 6912 * Cj * N * E * (L ^ 2 / |τ|) = (6912 * Cj) * (N * E * (L ^ 2 / |τ|)) := by ring
    have e2 : Ctot * N * E * (L ^ 2 / |τ|) = Ctot * (N * E * (L ^ 2 / |τ|)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hCtot1 hrest
  have hsplit : Ctot * N * E * (L ^ 2 / |τ|
        + (1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2))
      = Ctot * N * E * (L ^ 2 / |τ|)
        + Ctot * N * E * ((1 / |τ| + Lk / w) * (S + 1 / |τ| ^ 2)) := by ring
  rw [hsplit]
  linarith [hg, htail, htailC, hmain]

end RHTower.Sieve
