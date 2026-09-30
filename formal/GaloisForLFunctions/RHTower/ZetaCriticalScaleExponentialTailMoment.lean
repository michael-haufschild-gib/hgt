import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMoment

/-!
# Exponential decay of the off-line first moment beyond the critical scale

With the admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` of the exponential
near-line density (`exists_windowZeros_count_le`), for every `c ≥ 4`

`Σ_{Re ρ − ½ ≥ c/L} m_ρ (Re ρ − ½) ≤ (A/2π)(1 + 4800/c) e^{−c/4800} U + (2K/π) L²`,   `L = log U`

(`exists_offLineTailMoment_window_exponential_le`): on the dyadic shell
`2^j c/(2L) ≤ Re ρ − ½ < 2^{j+1} c/(2L)` the weight is at most `2^{j+1}c/(2L)` and the count is at
most `((U/4)A e^{−2^j c/4800} + KL)/(π 2^j c/(2L))`, and `Σ_j e^{−2^j x} ≤ (1 + 1/x)e^{−x}`.

The shadow argument of `ZetaCriticalScaleTailMoment` then gives exponentially small failure sets for
the Hadamard sign on the line `σ = ½ + c/L` and for vertical monotonicity of `|Ξ|` above `c/L`
(`exists_volume_hadamardFail_criticalScale_exponential_le`,
`exists_volume_monotoneFail_criticalScale_exponential_le`): both hold on all of `[T₁ + 1, T₂ − 1]`
outside measure `(A/π)(1 + 4800/c) e^{−c/4800} U + (4K/π) L²`.
-/

noncomputable section

open Complex Set MeasureTheory Filter Metric

namespace RHTower

open Sieve

/-- One dyadic shell with the linear weight. -/
theorem shell_term_linear_le {U A K L v N : ℝ} (hv : 0 < v)
    (hN : N ≤ ((U / 4) * A * Real.exp (-(v * L / 2400)) + K * L) / (Real.pi * v)) :
    2 * v * N ≤ 2 / Real.pi * ((U / 4) * A * Real.exp (-(v * L / 2400)) + K * L) := by
  have hπ := Real.pi_pos
  have := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2 * v by positivity)
  calc 2 * v * N ≤ 2 * v * (((U / 4) * A * Real.exp (-(v * L / 2400)) + K * L) / (Real.pi * v)) :=
        this
    _ = 2 / Real.pi * ((U / 4) * A * Real.exp (-(v * L / 2400)) + K * L) := by
        field_simp

/-- **Exponential tail moment on the admissible window.** -/
theorem exists_offLineTailMoment_window_exponential_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          ∀ c : ℝ, 4 ≤ c →
          ∑ w ∈ Z.filter (fun w => 1 / 2 + c / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ≤
            A / (2 * Real.pi) * (1 + 4800 / c) * Real.exp (-(c / 4800)) * U +
              2 * K / Real.pi * Real.log U ^ 2 := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_windowZeros_count_le
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 4), eventually_ge_atTop 8] with U hU hUe hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, hcount⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ c hc => ?_⟩
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos 4) hUe
  set L := Real.log U with hLdef
  have hL : 4 ≤ L := by
    have := Real.log_le_log (Real.exp_pos 4) hUe; rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  -- identify `Z` with the window zeros and the multiplicities
  have hZw : Z = windowZeros T₁ T₂ := by
    ext z; rw [hZ, mem_windowZeros_iff hT₁pos hT12]
  have hmult : ∀ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) = zeroMult w := by
    intro w hw
    have hmem := ((hZ w).mp hw).1
    have hw1 : w ≠ 1 := by
      intro h
      have := (Complex.mem_reProdIm.mp hmem).2
      rw [h, uIcc_of_le hT12] at this
      simp at this
      linarith [this.1]
    exact (zeroMult_eq_zeta_order hw1).symm
  set v₀ : ℝ := c / (2 * L) with hv₀
  have hv₀0 : 0 < v₀ := by positivity
  have hv₀2 : 2 / L ≤ v₀ := by
    rw [hv₀, div_le_div_iff₀ hL0 (by positivity)]; nlinarith
  set f : ℝ → ℝ := fun u => max u 0 with hf
  have hf0 : ∀ u, 0 ≤ f u := fun u => le_max_right _ _
  have hfm : Monotone f := fun a b hab => max_le_max hab le_rfl
  set J : ℕ := ⌊L⌋₊ with hJ
  have hJL : (J : ℝ) ≤ L := Nat.floor_le hL0.le
  have hJpow : L < 2 ^ J := by
    have h1 := Nat.lt_floor_add_one L
    have h2 : ((J + 1 : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt Nat.lt_two_pow_self
    push_cast at h2
    rw [← hJ] at h1
    linarith
  have hre1 : ∀ w ∈ windowZeros T₁ T₂, w.re < 1 := fun w hw => windowZeros_re_lt_one hT₁pos hT12 hw
  have hcover : ∀ w ∈ windowZeros T₁ T₂, w.re - 1 / 2 ≤ 2 ^ J * v₀ := by
    intro w hw
    have h1 := hre1 w hw
    have h2 : 2 ≤ 2 ^ J * v₀ := by
      have := (div_le_iff₀ hL0).mp hv₀2
      nlinarith
    linarith
  have hsh := sum_mult_weight_le_shells (windowZeros T₁ T₂) hf0 hfm hv₀0 J hcover
  -- the tail moment is dominated by the shell sum over `Re w − ½ > v₀`
  have hle : ∑ w ∈ Z.filter (fun w => 1 / 2 + c / L ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) ≤
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re), zeroMult w * f (w.re - 1 / 2) := by
    rw [hZw] at hmult ⊢
    refine (Finset.sum_le_sum fun w hw => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun w _ _ => mul_nonneg (zeroMult_nonneg w) (hf0 _))
    · rw [hmult w (Finset.mem_filter.mp hw).1]
      have hwre := (Finset.mem_filter.mp hw).2
      have : w.re - 1 / 2 ≤ f (w.re - 1 / 2) := le_max_left _ _
      exact mul_le_mul_of_nonneg_left this (zeroMult_nonneg w)
    · intro w hw
      rw [Finset.mem_filter] at hw ⊢
      refine ⟨hw.1, ?_⟩
      have : v₀ < c / L := by
        rw [hv₀, div_lt_div_iff₀ (by positivity) hL0]; nlinarith
      linarith [hw.2]
  refine hle.trans (hsh.trans ?_)
  have hterm : ∀ j ∈ Finset.range J, f (2 ^ (j + 1) * v₀) *
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re), zeroMult w ≤
      2 / Real.pi * ((U / 4) * A * Real.exp (-(2 ^ j * (c / 4800))) + K * L) := by
    intro j _
    have hrhs0 : 0 ≤ 2 / Real.pi * ((U / 4) * A * Real.exp (-(2 ^ j * (c / 4800))) + K * L) := by
      positivity
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hvj : 0 < 2 ^ j * v₀ := by positivity
    have hfv : f (2 ^ (j + 1) * v₀) = 2 * (2 ^ j * v₀) := by
      rw [hf]; simp only; rw [max_eq_left (by positivity), pow_succ]; ring
    rw [hfv]
    have hexp : -(2 ^ j * (c / 4800)) = -(2 ^ j * v₀ * L / 2400) := by
      rw [hv₀]; field_simp; ring
    by_cases hjv : 2 ^ j * v₀ ≤ 1 / 2
    · have hvle : 2 ^ j * v₀ ≤ 1 - 2 / L := by
        have : 2 / L ≤ 1 / 2 := by rw [div_le_iff₀ hL0]; linarith
        linarith
      have hvge : 2 / L ≤ 2 ^ j * v₀ := by nlinarith
      have hN := hcount (2 ^ j * v₀) hvge hvle
      rw [hexp]
      exact shell_term_linear_le hvj hN
    · push Not at hjv
      have hempty : (windowZeros T₁ T₂).filter (fun w => 1 / 2 + 2 ^ j * v₀ ≤ w.re) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun w hw hle' => ?_
        have := hre1 w hw
        linarith
      rw [hempty, Finset.sum_empty, mul_zero]
      exact hrhs0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeo := sum_exp_neg_two_pow_le (show 0 < c / 4800 by positivity) J
  have h1c : 1 + 1 / (c / 4800) = 1 + 4800 / c := by field_simp
  rw [h1c] at hgeo
  have hsum1 : ∑ j ∈ Finset.range J, (U / 4) * A * Real.exp (-(2 ^ j * (c / 4800))) ≤
      (U / 4) * A * ((1 + 4800 / c) * Real.exp (-(c / 4800))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeo (by positivity)
  have hsum2 : (J : ℝ) * (K * L) ≤ L * (K * L) :=
    mul_le_mul_of_nonneg_right hJL (by positivity)
  have hπ := Real.pi_pos
  have e1 : 2 / Real.pi * ((U / 4) * A * ((1 + 4800 / c) * Real.exp (-(c / 4800)))) =
      A / (2 * Real.pi) * (1 + 4800 / c) * Real.exp (-(c / 4800)) * U := by
    field_simp; ring
  have e2 : 2 / Real.pi * (L * (K * L)) = 2 * K / Real.pi * L ^ 2 := by
    field_simp
  calc 2 / Real.pi * (∑ j ∈ Finset.range J, (U / 4) * A * Real.exp (-(2 ^ j * (c / 4800))) +
        (J : ℝ) * (K * L))
      ≤ 2 / Real.pi * ((U / 4) * A * ((1 + 4800 / c) * Real.exp (-(c / 4800))) + L * (K * L)) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (by positivity)
    _ = _ := by rw [mul_add, e1, e2]

/-- **The Hadamard sign at the critical scale, exponential form.** For all large `U` there is one
window on which, for every `c ≥ 4`, the heights `t ∈ [T₁ + 1, T₂ − 1]` where `ξ(σ + it) = 0` or
`Re (ξ'/ξ)(σ + it) < 0` on the line `σ = ½ + c/log U` have measure at most
`(D/π)(1 + 4800/c)e^{−c/4800}U + (4K/π) log² U`. -/
theorem exists_volume_hadamardFail_criticalScale_exponential_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 4 ≤ c →
        volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
          ¬ (xi (((1 / 2 + c / Real.log U : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 ∧
            0 ≤ (logDeriv xi (((1 / 2 + c / Real.log U : ℝ) : ℂ) + (t : ℂ) * I)).re)}
          ≤ ENNReal.ofReal (2 * (D / (2 * Real.pi) * (1 + 4800 / c) * Real.exp (-(c / 4800)) * U +
            2 * K / Real.pi * Real.log U ^ 2)) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_exponential_le
  refine ⟨D, K, hD.le, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (100 : ℝ)] with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc4 => ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  set σ := 1 / 2 + c / Real.log U with hσdef
  have hσ : 1 / 2 < σ := by
    have : 0 < c / Real.log U := div_pos (by linarith) hL0
    linarith
  set Zc := Z.filter (fun w => σ ≤ w.re)
  have hsub : {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ¬ (xi ((σ : ℂ) + (t : ℂ) * I) ≠ 0 ∧ 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re)} ⊆
      ⋃ w ∈ Zc, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    intro t ⟨ht, hfail⟩
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    obtain ⟨ρ, hρ, hρs⟩ := DeBruijn.exists_boxZero_of_hadamard_fail (V := t)
      (by rw [hsre]; exact hσ) (by rw [hsim]; exact ht0) (by rw [hsim]) hfail
    rw [mem_boxFinsetLe] at hρ
    obtain ⟨hρ1, hρ2, -, -, hρ0⟩ := hρ
    simp only [DeBruijn.hadamardRect, mem_preimage, Complex.measurableEquivRealProd_apply,
      mem_prod, mem_Ioc, mem_Icc] at hρs
    rw [hsre, hsim] at hρs
    obtain ⟨⟨-, hσρ⟩, hlo, hhi⟩ := hρs
    have hζ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, hζ⟩
    exact mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hσρ⟩, ⟨by linarith, by linarith⟩⟩
  refine (volume_le_of_subset_shadows (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ))
    hsub fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact ⟨by linarith, by exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0⟩
  · have := hc Z hZ c hc4
    linarith

/-- **Vertical monotonicity at the critical scale, exponential form.** For all large `U` there is
one window on which, for every `c ≥ 4`, the abscissae `x ∈ [T₁ + 1, T₂ − 1]` at which
`y ↦ |Ξ(x + iy)|` fails to be nondecreasing on `y ≥ c/log U` have measure at most
`(D/π)(1 + 4800/c)e^{−c/4800}U + (4K/π) log² U`. -/
theorem exists_volume_monotoneFail_criticalScale_exponential_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 4 ≤ c →
        volume {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
          ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖)
            (Ici (c / Real.log U))}
          ≤ ENNReal.ofReal (2 * (D / (2 * Real.pi) * (1 + 4800 / c) * Real.exp (-(c / 4800)) * U +
            2 * K / Real.pi * Real.log U ^ 2)) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_exponential_le
  refine ⟨D, K, hD.le, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (100 : ℝ)] with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc4 => ?_⟩
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  set y₀ := c / Real.log U with hy₀def
  have hy₀ : 0 < y₀ := div_pos (by linarith) hL0
  set Zc := Z.filter (fun w => 1 / 2 + y₀ ≤ w.re)
  have hsub : {x : ℝ | x ∈ Icc (T₁ + 1) (T₂ - 1) ∧
      ¬ MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici y₀)} ⊆
      ⋃ w ∈ Zc, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    intro x ⟨hx, hfail⟩
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have hbad : ∃ ζ, DeBruijn.riemannHeat 0 ζ = 0 ∧ y₀ ^ 2 < ζ.im ^ 2 ∧
        (ζ.re - x) ^ 2 < ζ.im ^ 2 := by
      by_contra hno
      apply hfail
      refine DeBruijn.monotoneOn_norm_xi_vertical_Ici hy₀.le fun ζ hζ => ?_
      by_contra hc'
      rw [not_or, not_le, not_le] at hc'
      exact hno ⟨ζ, hζ, hc'.1, hc'.2⟩
    obtain ⟨ζ, hζ, hy, hlt⟩ := hbad
    obtain ⟨ρ, hρ0, hρ1, hρ2, hρx⟩ := DeBruijn.exists_xiZero_of_obstruct hx0 hζ hy hlt hy₀.le
    have hζρ : riemannZeta ρ = 0 := by
      have hne : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
      exact (xi_eq_zero_iff (by linarith) hne).mp hρ0
    have hρx' := abs_lt.mp hρx
    have hZρ : ρ ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩, hζρ⟩
    exact mem_iUnion₂.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hZρ, hρ1.le⟩, ⟨by linarith, by linarith⟩⟩
  refine (volume_le_of_subset_shadows (m := fun w => ((analyticOrderAt riemannZeta w).toNat : ℝ))
    hsub fun w hw => ?_).trans (ENNReal.ofReal_le_ofReal ?_)
  · obtain ⟨hwZ, hwσ⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact ⟨by linarith, by exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0⟩
  · have := hc Z hZ c hc4
    linarith

end RHTower
