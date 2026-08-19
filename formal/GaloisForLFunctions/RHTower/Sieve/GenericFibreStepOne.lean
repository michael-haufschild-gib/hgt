import GaloisForLFunctions.RHTower.Sieve.FibreStepOnePositive

/-!
# Step 1 of the reciprocal-marker Hall law at an arbitrary window

`Sieve/FibreStepOne{,Closed,Positive}` fix the window at `exp((log x)^{99/100})`, but every step of
their proofs is generic in the window: what is used is that the Möbius fibre mean square vanishes at
that window, that the window grows, that it is small against `√x`, and that it beats the cube of the
logarithm.  This module restates the three conclusions with those four properties as hypotheses, so
that a shrunk window `c·exp((log x)^β)` inherits them.
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

/-- **Step 1 at the fibre data, at an arbitrary window.** -/
theorem eventually_fibre_step_one_gen {hh : ℝ → ℝ}
    (hms : AveragedMeanSquare (fun n => ((moebius n : ℤ) : ℝ)) hh)
    (hgrow : Tendsto hh atTop atTop) {D : ℝ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ∀ Bad₂ : Finset ℕ,
        (∀ a ∈ outerBlock x (hh x), a ∉ Bad₂ →
          (1 / 2) * D * (fibreLen x (hh x) a : ℝ)
            ≤ ∑ b ∈ innerFibre x (hh x) a, ((moebius b : ℤ) : ℝ) ^ 2) →
        ((outerBlock x (hh x)).card : ℝ)
          ≤ (((outerBlock x (hh x)).filter (fun a =>
              (3 / 16) * D * (fibreLen x (hh x) a : ℝ)
                  ≤ (((Finset.Ioc (fibreStartIdx x a)
                      (fibreStartIdx x a + fibreLen x (hh x) a)).filter
                      (fun n => moebius n = 1)).card : ℝ)
                ∧ (3 / 16) * D * (fibreLen x (hh x) a : ℝ)
                  ≤ (((Finset.Ioc (fibreStartIdx x a)
                      (fibreStartIdx x a + fibreLen x (hh x) a)).filter
                      (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
            + 1024 * ε * Real.sqrt x / D ^ 2 + (Bad₂.card : ℝ) := by
  have hqt : ∀ᶠ x : ℝ in atTop,
      (∑ a ∈ outerBlock x (hh x),
        (∑ b ∈ innerFibre x (hh x) a, ((moebius b : ℤ) : ℝ)) ^ 2)
        / (hh x ^ 2 * Real.sqrt x) < ε :=
    hms.eventually (gt_mem_nhds hε)
  have hlen : ∀ᶠ x : ℝ in atTop, 4 ≤ hh x := hgrow.eventually_ge_atTop 4
  filter_upwards [hqt, hlen, eventually_ge_atTop (4 : ℝ)] with x hq hh4 hx4
  intro Bad₂ h2
  set h : ℝ := hh x with hhdef
  clear_value h
  clear hhdef
  have hh0 : (0 : ℝ) < h := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ) < h ^ 2 * Real.sqrt x := by positivity
  set V : ℝ := ε * (h ^ 2 * Real.sqrt x) with hVdef
  have hmsx : ∑ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2 ≤ V := by
    rw [hVdef]
    rw [div_lt_iff₀ hden] at hq
    linarith
  set δ : ℝ := (1 / 32) * D * h with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδL : ∀ a ∈ outerBlock x h, δ ≤ (1 / 8) * D * (fibreLen x h a : ℝ) := by
    intro a ha
    have hge := fibreLen_ge hx4 hh4 ha
    rw [hδdef]
    nlinarith [hge, hD, hh0]
  have hbase := card_le_good_add_fibreMeanSquare (x := x) (h := h) hx4 hh0.le
    (Bad₂ := Bad₂) (D := D) (V := V) (δ := δ) hδ0 hδL hmsx h2
  refine le_trans hbase (le_of_le_of_eq (le_refl _) ?_)
  have hval : V / δ ^ 2 = 1024 * ε * Real.sqrt x / D ^ 2 := by
    rw [hVdef, hδdef]
    field_simp
    ring
  rw [hval]

set_option maxHeartbeats 800000 in
/-- **Step 1 with a growing truncation level, at an arbitrary window.** -/
theorem eventually_fibre_step_one_growing_gen {hh : ℝ → ℝ}
    (hms : AveragedMeanSquare (fun n => ((moebius n : ℤ) : ℝ)) hh)
    (hgrow : Tendsto hh atTop atTop)
    (hratio : Tendsto (fun x : ℝ => hh x / Real.sqrt x) atTop (𝓝 0))
    (hpoly : Tendsto (fun x : ℝ => (Real.log x) ^ (3 : ℝ) / hh x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((outerBlock x (hh x)).card : ℝ)
        ≤ (((outerBlock x (hh x)).filter (fun a =>
            (3 / 16) * squarefreeDensity * (fibreLen x (hh x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (hh x) a)).filter
                    (fun n => moebius n = 1)).card : ℝ)
              ∧ (3 / 16) * squarefreeDensity * (fibreLen x (hh x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (hh x) a)).filter
                    (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
          + 1024 * ε * Real.sqrt x / squarefreeDensity ^ 2
          + Real.sqrt x / (Real.log x) ^ 2 := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hDge : (3 : ℝ) / 8 ≤ squarefreeDensity := squarefreeDensity_ge
  have hstep := eventually_fibre_step_one_gen hms hgrow (D := squarefreeDensity) hD hε
  have hbig := hgrow.eventually_ge_atTop (300000 : ℝ)
  have hR3 : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (3 : ℝ) / hh x ≤ 1 / 2000 :=
    hpoly.eventually_le_const (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, hh x / Real.sqrt x ≤ 1 / 100 :=
    hratio.eventually_le_const (by norm_num)
  have hlogbig : ∀ᶠ x : ℝ in atTop, (1000 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1000 : ℝ)
  have hsqbig : ∀ᶠ x : ℝ in atTop, (300 : ℝ) ≤ Real.sqrt x := by
    have := Real.tendsto_sqrt_atTop.eventually_ge_atTop (300 : ℝ)
    simpa using this
  filter_upwards [hstep, hbig, hR3, hsmall, hlogbig, hsqbig, eventually_ge_atTop (4 : ℝ)]
    with x hx1 hbg hRlog hratio' hlx hsx hx4
  set h : ℝ := hh x with hhdef
  clear_value h
  clear hhdef
  have hh0 : (0 : ℝ) < h := by linarith
  have hh4 : (4 : ℝ) ≤ h := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hhs : h ≤ 1 / 100 * Real.sqrt x := by
    rw [div_le_iff₀ hs0] at hratio'
    linarith
  set P : ℝ := (Real.log x) ^ 2 with hPdef
  have hP0 : (0 : ℝ) < P := by rw [hPdef]; positivity
  have hrpow : (Real.log x) ^ (3 : ℝ) = P * Real.log x := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hPdef]
    ring
  set L3 : ℝ := (Real.log x) ^ (3 : ℝ) with hL3def
  have hL3pos : (0 : ℝ) < L3 := by rw [hL3def]; exact Real.rpow_pos_of_pos (by linarith) 3
  have hL3h : L3 ≤ 1 / 2000 * h := by
    rw [div_le_iff₀ hh0] at hRlog
    linarith
  set R : ℕ := ⌈L3⌉₊ + 100 with hRdef
  have hR1 : 1 ≤ R := by omega
  have hRge : L3 ≤ (R : ℝ) := by
    have := Nat.le_ceil L3
    rw [hRdef]
    push_cast
    linarith
  have hRle : (R : ℝ) ≤ L3 + 101 := by
    have := Nat.ceil_lt_add_one hL3pos.le
    rw [hRdef]
    push_cast
    linarith
  have hR100 : (100 : ℝ) ≤ (R : ℝ) := by
    have : (100 : ℕ) ≤ R := by omega
    exact_mod_cast this
  have hRh : (R : ℝ) ≤ h / 1000 := by
    have : (R : ℝ) ≤ 1 / 2000 * h + 101 := by linarith
    linarith
  have hRP : 1000 * P ≤ (R : ℝ) := by
    have hPL : 1000 * P ≤ L3 := by
      rw [hrpow]
      nlinarith [hP0, hlx]
    linarith
  have hR0 : (0 : ℝ) < (R : ℝ) := by linarith
  set T : ℝ := x + h * Real.sqrt x with hTdef
  have hT4 : (4 : ℝ) ≤ T := by
    have hprod : (0 : ℝ) ≤ h * Real.sqrt x := (mul_pos hh0 hs0).le
    rw [hTdef]
    linarith
  set M' : ℕ := ⌈Real.sqrt T⌉₊ with hM'
  set θ : ℝ := h / 100 with hθdef
  have hθ0 : (0 : ℝ) < θ := by rw [hθdef]; linarith
  set Bad : Finset ℕ := (outerBlock x h).filter (fun a =>
      θ ≤ windowTail (fibreStartIdx x a) (fibreLen x h a) R M') with hBad
  have hgap : ∀ a ∈ outerBlock x h,
      (R : ℝ) + (fibreLen x h a : ℝ) / (R : ℝ) + θ
        ≤ (1 / 2) * squarefreeDensity * (fibreLen x h a : ℝ) := by
    intro a ha
    have hL := fibreLen_ge hx4 hh4 ha
    have hL0 : (0 : ℝ) ≤ (fibreLen x h a : ℝ) := Nat.cast_nonneg _
    have hquot : (fibreLen x h a : ℝ) / (R : ℝ) ≤ (fibreLen x h a : ℝ) / 100 :=
      div_le_div_of_nonneg_left hL0 (by norm_num) hR100
    have hprod : (3 / 8 : ℝ) * (fibreLen x h a : ℝ)
        ≤ squarefreeDensity * (fibreLen x h a : ℝ) :=
      mul_le_mul_of_nonneg_right hDge hL0
    rw [hθdef]
    linarith [hL, hprod, hquot, hRh]
  have h2 : ∀ a ∈ outerBlock x h, a ∉ Bad →
      (1 / 2) * squarefreeDensity * (fibreLen x h a : ℝ)
        ≤ ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) ^ 2 := by
    intro a ha hnot
    have htail : windowTail (fibreStartIdx x a) (fibreLen x h a) R M' ≤ θ := by
      by_contra hcon
      exact hnot (by rw [hBad, Finset.mem_filter]; exact ⟨ha, (not_le.mp hcon).le⟩)
    exact fibre_squarefree_mass hx4 hh0.le hR1
      (fun b hb => fibre_top_le_floor hx4 hh0.le hb)
      (fibre_step_one_ceil_le hT4)
      (fun b hb => fibre_top_lt_sq hx4 hh0.le hb) hgap a ha htail
  have hcard : ((Bad.card : ℕ) : ℝ) ≤ fibreTailBudgetSharp x h R / θ := by
    rw [hBad]
    exact card_fibre_bad_le_sharp hx4 hh0.le hR1 hθ0
  have htail : fibreTailBudgetSharp x h R / θ ≤ Real.sqrt x / P := by
    set u : ℝ := ((⌈h⌉₊ + 1 : ℕ) : ℝ) with hu
    set s : ℝ := ((⌈Real.sqrt x⌉₊ : ℕ) : ℝ) with hs
    have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
    have hs0' : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have hule : u ≤ h + 2 := by
      have := Nat.ceil_lt_add_one hh0.le
      rw [hu]
      push_cast
      linarith
    have hsle : s ≤ Real.sqrt x + 1 := by
      have := Nat.ceil_lt_add_one hs0.le
      rw [hs]
      linarith
    have hsu : s + u ≤ Real.sqrt x + h + 3 := by linarith
    have hkey : u * (s + u) ≤ (h + 2) * (Real.sqrt x + h + 3) :=
      mul_le_mul hule hsu (by linarith) (by linarith)
    have hexp : (h + 2) * (Real.sqrt x + h + 3)
        = h * Real.sqrt x + h ^ 2 + 5 * h + 2 * Real.sqrt x + 6 := by ring
    have hh2 : h ^ 2 ≤ h * Real.sqrt x / 100 := by
      have := mul_le_mul_of_nonneg_left hhs hh0.le
      linarith
    have h5h : 5 * h ≤ h * Real.sqrt x / 60 := by
      have := mul_le_mul_of_nonneg_left hsx hh0.le
      linarith
    have h2s : 2 * Real.sqrt x ≤ h * Real.sqrt x / 150000 := by
      have := mul_le_mul_of_nonneg_right hbg hs0.le
      linarith
    have h6 : (6 : ℝ) ≤ h * Real.sqrt x / 150000 := by
      have := mul_le_mul hbg hsx (by norm_num : (0:ℝ) ≤ 300) (by linarith : (0:ℝ) ≤ h)
      linarith
    have hfin : u * (s + u) ≤ 5 / 2 * (Real.sqrt x * h) := by
      rw [hexp] at hkey
      nlinarith [hkey, hh2, h5h, h2s, h6]
    rw [fibreTailBudgetSharp, ← hu, ← hs, hθdef]
    have hPne : P ≠ 0 := ne_of_gt hP0
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < h / 100) hP0]
    have hstep1 : (s + u) / (R : ℝ) ≤ (s + u) / (1000 * P) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hRP
    have hmul : 4 * u * ((s + u) / (R : ℝ)) * P ≤ 4 * u * ((s + u) / (1000 * P)) * P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hstep1 (by linarith)) hP0.le
    have hval : 4 * u * ((s + u) / (1000 * P)) * P = 4 * (u * (s + u)) / 1000 := by
      field_simp
    rw [hval] at hmul
    have hgoal : 4 * (u * (s + u)) / 1000 ≤ Real.sqrt x * (h / 100) := by
      linarith [hfin]
    linarith
  have hmain := hx1 Bad h2
  have hPval : Real.sqrt x / (Real.log x) ^ 2 = Real.sqrt x / P := by rw [hPdef]
  rw [hPval]
  linarith [hmain, hcard, htail]

/-- **A positive proportion of the fibres is good, at an arbitrary window.** -/
theorem eventually_fibre_step_one_positive_gen {hh : ℝ → ℝ}
    (hms : AveragedMeanSquare (fun n => ((moebius n : ℤ) : ℝ)) hh)
    (hgrow : Tendsto hh atTop atTop)
    (hratio : Tendsto (fun x : ℝ => hh x / Real.sqrt x) atTop (𝓝 0))
    (hpoly : Tendsto (fun x : ℝ => (Real.log x) ^ (3 : ℝ) / hh x) atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop,
      (3 / 4) * Real.sqrt x
        ≤ (((outerBlock x (hh x)).filter (fun a =>
            (3 / 16) * squarefreeDensity * (fibreLen x (hh x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (hh x) a)).filter
                    (fun n => moebius n = 1)).card : ℝ)
              ∧ (3 / 16) * squarefreeDensity * (fibreLen x (hh x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (hh x) a)).filter
                    (fun n => moebius n = -1)).card : ℝ))).card : ℝ) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hDge : (3 : ℝ) / 8 ≤ squarefreeDensity := squarefreeDensity_ge
  have hstep := eventually_fibre_step_one_growing_gen hms hgrow hratio hpoly
    (ε := 1 / 100000) (by norm_num)
  have hlogbig : ∀ᶠ x : ℝ in atTop, (100 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (100 : ℝ)
  have hsqbig : ∀ᶠ x : ℝ in atTop, (100 : ℝ) ≤ Real.sqrt x := by
    have := Real.tendsto_sqrt_atTop.eventually_ge_atTop (100 : ℝ)
    simpa using this
  filter_upwards [hstep, hlogbig, hsqbig, hgrow.eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (4 : ℝ)] with x hx1 hlx hsx hhpos hx4
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  have houter := card_outerBlock_ge (x := x) (h := hh x) hx4 hhpos.le
  have hAbound : 1024 * (1 / 100000 : ℝ) * Real.sqrt x / squarefreeDensity ^ 2
      ≤ 3 / 40 * Real.sqrt x := by
    have hsqge : (9 : ℝ) / 64 ≤ squarefreeDensity ^ 2 := by nlinarith [hDge, hD]
    have hnum : (0 : ℝ) ≤ 1024 * (1 / 100000 : ℝ) * Real.sqrt x := by positivity
    have hcmp := div_le_div_of_nonneg_left hnum (by norm_num : (0:ℝ) < 9 / 64) hsqge
    calc 1024 * (1 / 100000 : ℝ) * Real.sqrt x / squarefreeDensity ^ 2
        ≤ 1024 * (1 / 100000 : ℝ) * Real.sqrt x / (9 / 64) := hcmp
      _ ≤ 3 / 40 * Real.sqrt x := by linarith
  have hBbound : Real.sqrt x / (Real.log x) ^ 2 ≤ 1 / 10 * Real.sqrt x := by
    have hlog2 : (10000 : ℝ) ≤ (Real.log x) ^ 2 := by nlinarith [hlx]
    have hlog0 : (0 : ℝ) < (Real.log x) ^ 2 := by linarith
    rw [div_le_iff₀ hlog0]
    nlinarith [hlog2, hs0]
  linarith [hx1, houter, hAbound, hBbound]

end RHTower.Sieve
