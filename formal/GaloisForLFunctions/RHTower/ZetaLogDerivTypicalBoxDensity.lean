import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBox

/-!
# Exceptional heights for the typical `ζ'/ζ` box bound

Let `C₀` bound the multiplicity of the fixed rectangle, `Σ m_w ≤ C₀ (4T + 4) log(4T + 5)`
(`exists_sum_mult_selbergMidZeros_le`). For `t ∈ [T, 2T]`:

* the Lorentzian sum at width `R/4` exceeds `M` on a set of measure
  `≤ (4π/R) C₀ (4T + 4) log(4T + 5)/M` (`volume_selbergLorentzSum_ge_le`);
* the far-right majorant exceeds `M` on a set of measure
  `≤ (4π/(3Rℓ)) e^{−Rℓ/2} C₀ (4T + 4) log(4T + 5)/M` (`volume_selbergRightFar_ge_le`);
* `|D_x| > M` somewhere on the box `½ + 3R/4 ≤ Re ≤ ½ + 6R`, `|Im − t| ≤ 6R`, on a set of measure
  `≤ 1380 Q/(π M²)`, `Q = 20 (T + 17R + 8N(1 + log N))/R²`, `N = ⌈x²⌉`
  (`volume_largeNearBox_selbergVonMangoldtPoly_le`).
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

open Sieve

/-- **Lorentzian exceptional set.** -/
theorem volume_selbergLorentzSum_ge_le {C₀ T R M : ℝ} (hT : 16 ≤ T) (hR : 0 < R) (hM : 0 < M)
    (hC₀ : ∑ w ∈ selbergMidZeros T, zeroMult w ≤ C₀ * (4 * T + 4) * Real.log (4 * T + 5)) :
    volume {t | t ∈ Icc T (2 * T) ∧ M ≤ selbergLorentzSum (selbergMidZeros T) (R / 4) t} ≤
      ENNReal.ofReal (4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / M) := by
  have hu : 0 < R / 4 := by positivity
  refine volume_Icc_setOf_le_le_of_integral (by linarith) hM
    (fun t => selbergLorentzSum_nonneg _ _ t) (continuous_selbergLorentzSum _ hu) ?_
  refine (integral_selbergLorentzSum_le _ hu (by linarith)).trans ?_
  have e : Real.pi / (R / 4) = 4 * Real.pi / R := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hC₀ (by positivity)

/-- **Far-right exceptional set.** -/
theorem volume_selbergRightFar_ge_le {C₀ T x R M : ℝ} (hT : 16 ≤ T) (hx : 1 < x) (hR : 0 < R)
    (hM : 0 < M)
    (hC₀ : ∑ w ∈ selbergMidZeros T, zeroMult w ≤ C₀ * (4 * T + 4) * Real.log (4 * T + 5)) :
    volume {t | t ∈ Icc T (2 * T) ∧ M ≤ selbergRightFar (selbergMidZeros T) x R t} ≤
      ENNReal.ofReal (4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
        (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / M) := by
  have hl := Real.log_pos hx
  refine volume_Icc_setOf_le_le_of_integral (by linarith) hM
    (selbergRightFar_nonneg _ hx hR) (continuous_selbergRightFar _ hR) ?_
  refine (integral_selbergRightFar_le _ hx hR (by linarith)).trans ?_
  set c : ℝ := 4 * Real.pi / (3 * R * Real.log x) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
        zeroMult w * c * Real.exp (-((w.re - 1 / 2) * Real.log x))
      ≤ ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
          c * Real.exp (-(R / 2 * Real.log x)) * zeroMult w := by
        refine Finset.sum_le_sum fun w hw => ?_
        have hwre := (Finset.mem_filter.mp hw).2
        have he : Real.exp (-((w.re - 1 / 2) * Real.log x)) ≤ Real.exp (-(R / 2 * Real.log x)) := by
          apply Real.exp_le_exp.mpr
          have : R / 2 * Real.log x ≤ (w.re - 1 / 2) * Real.log x :=
            mul_le_mul_of_nonneg_right (by linarith) hl.le
          linarith
        have := mul_le_mul_of_nonneg_left he (mul_nonneg (zeroMult_nonneg w) hc0)
        linarith
    _ = c * Real.exp (-(R / 2 * Real.log x)) *
          ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re), zeroMult w := by
        rw [Finset.mul_sum]
    _ ≤ c * Real.exp (-(R / 2 * Real.log x)) * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hC₀) (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun w _ _ => zeroMult_nonneg w

/-- **Large values of `D_x` on the box.** -/
theorem volume_largeNearBox_selbergVonMangoldtPoly_le {T x R M : ℝ} (hT : 0 < T) (hx : 1 < x)
    (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hM : 0 < M) :
    volume (largeNearBox (selbergVonMangoldtPoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R M) ≤
      ENNReal.ofReal (1380 * (20 * (T + 17 * R + 8 * selbergPolyLength x *
        (1 + Real.log (selbergPolyLength x))) / R ^ 2) / (Real.pi * M ^ 2)) := by
  set N := selbergPolyLength x with hN
  set Q : ℝ := 20 * (T + 17 * R + 8 * N * (1 + Real.log N)) / R ^ 2 with hQ
  have hlogN : 0 ≤ 8 * (N : ℝ) * (1 + Real.log N) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hpos)
      positivity
  have hcol : ∀ c ∈ Icc (1 / 2 + 3 * R / 4 - R / 4) (1 / 2 + 6 * R + R / 4),
      ∫ y in (T - (7 : ℕ) * R)..(T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R),
        ‖selbergVonMangoldtPoly x ((c : ℂ) + (y : ℂ) * I)‖ ^ 2 ≤ Q := by
    intro c hc
    set δ := c - 1 / 2 with hδ
    have hδ0 : R / 2 ≤ δ := by rw [hδ]; linarith [hc.1]
    have hδ1 : δ ≤ 1 := by rw [hδ]; linarith [hc.2]
    have hδpos : 0 < δ := by linarith
    have hceq : c = 1 / 2 + δ := by rw [hδ]; ring
    have hceil : (⌈T / R⌉₊ : ℝ) ≤ T / R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hlen : T - (7 : ℕ) * R ≤ T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R := by
      push_cast
      have : (0 : ℝ) ≤ ⌈T / R⌉₊ := Nat.cast_nonneg _
      nlinarith
    have h := integral_normSq_selbergVonMangoldtPoly_le hx hδpos hδ1 hlen
    rw [hceq]
    refine h.trans ?_
    have hlen2 : T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) ≤ T + 17 * R := by
      push_cast
      have : (⌈T / R⌉₊ : ℝ) * R ≤ (T / R + 1) * R := mul_le_mul_of_nonneg_right hceil hR.le
      have e : (T / R + 1) * R = T + R := by field_simp
      nlinarith
    have hδ2 : 5 / δ ^ 2 ≤ 20 / R ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hA : 0 ≤ T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) +
        8 * N * (1 + Real.log N) := by linarith
    calc (T + (((⌈T / R⌉₊ + 1 : ℕ) : ℝ) + (8 : ℕ)) * R - (T - (7 : ℕ) * R) +
          8 * N * (1 + Real.log N)) * (5 / δ ^ 2)
        ≤ (T + 17 * R + 8 * N * (1 + Real.log N)) * (20 / R ^ 2) :=
          mul_le_mul (by linarith) hδ2 (by positivity) (by linarith)
      _ = Q := by rw [hQ]; ring
  have hbox := volume_largeNearBox_le (differentiable_selbergVonMangoldtPoly hx)
    (T := T) (a := 1 / 2 + 3 * R / 4) (b := 1 / 2 + 6 * R) (R := R) (r := R / 4) (M := M) (Q := Q)
    (by positivity) (by linarith) hM (by linarith) hcol
  refine hbox.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  field_simp
  ring

theorem ZetaLogDerivScaleData.mono {t R B B' : ℝ} (h : ZetaLogDerivScaleData t R B)
    (hB : B ≤ B') : ZetaLogDerivScaleData t R B' :=
  ⟨h.zeroFree, fun s h1 h2 h3 => (h.logDeriv s h1 h2 h3).trans hB⟩

/-- `C (log T + 3)ⁿ ≤ T^a` for all large `T`. -/
theorem eventually_mul_log_add_pow_le_exp (n : ℕ) (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T in atTop, C * (Real.log T + 3) ^ n ≤ Real.exp (a * Real.log T) := by
  set c : ℝ := 1 / (|C| * 2 ^ n + 1) with hc
  have hc0 : 0 < c := by positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop n ha).bound hc0
  have h2 : ∀ᶠ u in atTop, C * (u + 3) ^ n ≤ Real.exp (a * u) := by
    filter_upwards [h, eventually_ge_atTop 3] with u hu hu3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_pos (Real.exp_pos _)] at hu
    have h1 : (u + 3) ^ n ≤ 2 ^ n * u ^ n := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) n
    have h3 : |C| * 2 ^ n * c ≤ 1 := by
      rw [hc, mul_one_div, div_le_one (by positivity)]; linarith
    calc C * (u + 3) ^ n ≤ |C| * (u + 3) ^ n :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (2 ^ n * u ^ n) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ ≤ |C| * (2 ^ n * (c * Real.exp (a * u))) := by gcongr
      _ = (|C| * 2 ^ n * c) * Real.exp (a * u) := by ring
      _ ≤ 1 * Real.exp (a * u) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp (a * u) := one_mul _
  exact Real.tendsto_log_atTop.eventually h2

/-- **The exceptional heights at one scale**, bounded by three exceptional measures and the measure
of the large values of `D_x` near the box. -/
theorem volume_not_zetaLogDerivScaleData_le_of_largeNearBox {T x R B C₀ M_D M_L M_F : ℝ}
    (hT : 64 ≤ T) (hx : 1 < x) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hRx : 1 ≤ 36 * R * Real.log x)
    (hEF : ∀ t ∈ Icc T (2 * T), ∃ T₁ T₂ : ℝ, t / 2 - 1 < T₁ ∧ T₂ < 3 * t / 2 + 1 ∧ T₁ ≤ T₂ ∧
      ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 → riemannZeta s₀ ≠ 0 →
        ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
          ∑ w ∈ selbergHeightZeros t T₁ T₂,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 1)
    (hC₀ : ∑ w ∈ selbergMidZeros T, zeroMult w ≤ C₀ * (4 * T + 4) * Real.log (4 * T + 5))
    (hML : 0 < M_L) (hMF : 0 < M_F)
    (hB : 1 + M_D + 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 * M_L + M_F ≤ B) :
    volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R B} ≤
      ENNReal.ofReal (∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
          2 * selbergRightWindow x R w) +
        ENNReal.ofReal (4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / M_L) +
        ENNReal.ofReal (4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
          (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / M_F) +
        volume (largeNearBox (selbergVonMangoldtPoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R
          M_D) := by
  have hl := Real.log_pos hx
  set Z := selbergMidZeros T with hZ
  set cL : ℝ := 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 with hcL
  have hcL0 : 0 ≤ cL := by rw [hcL]; positivity
  set Sa := {t | t ∈ Icc T (2 * T) ∧ ∃ w ∈ Z, 1 / 2 + R / 2 < w.re ∧
    |w.im - t| ≤ selbergRightWindow x R w} with hSa
  set Sb := {t | t ∈ Icc T (2 * T) ∧ M_L ≤ selbergLorentzSum Z (R / 4) t} with hSb
  set Sc := {t | t ∈ Icc T (2 * T) ∧ M_F ≤ selbergRightFar Z x R t} with hSc
  set Sd := largeNearBox (selbergVonMangoldtPoly x) T (1 / 2 + 3 * R / 4) (1 / 2 + 6 * R) R M_D
    with hSd
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R B} ⊆ ((Sa ∪ Sb) ∪ Sc) ∪ Sd := by
    rintro t ⟨ht, hnot⟩
    by_contra hout
    simp only [mem_union, not_or] at hout
    obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := hout
    apply hnot
    have hgood : ∀ w ∈ Z, 1 / 2 + R / 2 < w.re → selbergRightWindow x R w < |w.im - t| := by
      intro w hw hre
      by_contra hle
      exact ha ⟨ht, w, hw, hre, not_lt.mp hle⟩
    have hLor : selbergLorentzSum Z (R / 4) t < M_L := by
      by_contra hle; exact hb ⟨ht, not_lt.mp hle⟩
    have hFar : selbergRightFar Z x R t < M_F := by
      by_contra hle; exact hc ⟨ht, not_lt.mp hle⟩
    have hD : ∀ z : ℂ, 1 / 2 + 3 * R / 4 ≤ z.re → z.re ≤ 1 / 2 + 6 * R → |z.im - t| ≤ 6 * R →
        ‖selbergVonMangoldtPoly x z‖ ≤ M_D := by
      intro z h1 h2 h3
      by_contra hlt
      exact hd ⟨ht, z, h1, h2, h3, not_le.mp hlt⟩
    obtain ⟨T₁, T₂, h1, h2, h12, hbound⟩ := hEF t ht
    refine (zetaLogDerivScaleData_of_good hT ht hx hR hR16 hRx h1 h2 h12 hbound hgood hD).mono ?_
    have := mul_le_mul_of_nonneg_left hLor.le hcL0
    rw [← hcL]
    linarith
  have hva : volume Sa ≤ ENNReal.ofReal (∑ w ∈ Z.filter (fun w => 1 / 2 + R / 2 < w.re),
      2 * selbergRightWindow x R w) := volume_selbergRightExceptional_le Z hR
  have hvb := volume_selbergLorentzSum_ge_le (by linarith) hR hML hC₀
  have hvc := volume_selbergRightFar_ge_le (by linarith) hx hR hMF hC₀
  calc volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R B}
      ≤ volume (((Sa ∪ Sb) ∪ Sc) ∪ Sd) := measure_mono hsub
    _ ≤ volume ((Sa ∪ Sb) ∪ Sc) + volume Sd := measure_union_le _ _
    _ ≤ (volume (Sa ∪ Sb) + volume Sc) + volume Sd := by gcongr; exact measure_union_le _ _
    _ ≤ ((volume Sa + volume Sb) + volume Sc) + volume Sd := by
        gcongr; exact measure_union_le _ _
    _ ≤ _ := by gcongr

/-- **The exceptional heights at one scale**, as a sum of the four exceptional measures. -/
theorem volume_not_zetaLogDerivScaleData_le_of {T x R B C₀ M_D M_L M_F : ℝ} (hT : 64 ≤ T)
    (hx : 1 < x) (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hRx : 1 ≤ 36 * R * Real.log x)
    (hEF : ∀ t ∈ Icc T (2 * T), ∃ T₁ T₂ : ℝ, t / 2 - 1 < T₁ ∧ T₂ < 3 * t / 2 + 1 ∧ T₁ ≤ T₂ ∧
      ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 → riemannZeta s₀ ≠ 0 →
        ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
          ∑ w ∈ selbergHeightZeros t T₁ T₂,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 1)
    (hC₀ : ∑ w ∈ selbergMidZeros T, zeroMult w ≤ C₀ * (4 * T + 4) * Real.log (4 * T + 5))
    (hMD : 0 < M_D) (hML : 0 < M_L) (hMF : 0 < M_F)
    (hB : 1 + M_D + 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 * M_L + M_F ≤ B) :
    volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R B} ≤
      ENNReal.ofReal (∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
          2 * selbergRightWindow x R w) +
        ENNReal.ofReal (4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / M_L) +
        ENNReal.ofReal (4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
          (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / M_F) +
        ENNReal.ofReal (1380 * (20 * (T + 17 * R + 8 * selbergPolyLength x *
          (1 + Real.log (selbergPolyLength x))) / R ^ 2) / (Real.pi * M_D ^ 2)) := by
  refine (volume_not_zetaLogDerivScaleData_le_of_largeNearBox hT hx hR hR16 hRx hEF hC₀ hML hMF
    hB).trans ?_
  gcongr
  exact volume_largeNearBox_selbergVonMangoldtPoly_le (by linarith : 0 < T) hx hR hR16 hMD

/-- The length term: `8N(1 + log N) ≤ T` for `x = T^{1/30000}` and `N = ⌈x²⌉`. -/
theorem polyLength_term_le {T : ℝ} (hT : 1 < T)
    (h : 16 * (Real.log T + 3) ^ 1 ≤ Real.exp ((1 - 1 / 15000) * Real.log T)) :
    8 * (selbergPolyLength (Real.exp (Real.log T / 30000)) : ℝ) *
      (1 + Real.log (selbergPolyLength (Real.exp (Real.log T / 30000)))) ≤ T := by
  set L := Real.log T with hL
  have hL0 : 0 < L := Real.log_pos hT
  set x := Real.exp (L / 30000) with hx
  set N := selbergPolyLength x with hN
  have hx2 : x ^ 2 = Real.exp (L / 15000) := by
    rw [hx, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx21 : 1 ≤ x ^ 2 := by rw [hx2]; exact Real.one_le_exp (by positivity)
  have hNle : (N : ℝ) ≤ 2 * x ^ 2 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x ^ 2 by positivity)
    rw [hN, selbergPolyLength]
    linarith
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hN, selbergPolyLength]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [Nat.ceil_eq_zero] at h0
      linarith)
  have hlogN : Real.log N ≤ 1 + L / 15000 := by
    have h1 : Real.log N ≤ Real.log (2 * x ^ 2) := Real.log_le_log (by linarith) hNle
    rw [Real.log_mul (by norm_num) (by positivity), hx2, Real.log_exp] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hT' : T = Real.exp ((1 - 1 / 15000) * L) * Real.exp (L / 15000) := by
    rw [← Real.exp_add, hL, show (1 - 1 / 15000) * Real.log T + Real.log T / 15000 = Real.log T by
      ring, Real.exp_log (by linarith)]
  calc 8 * (N : ℝ) * (1 + Real.log N) ≤ 8 * (2 * x ^ 2) * (2 + L / 15000) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
    _ ≤ 16 * (L + 3) * Real.exp (L / 15000) := by
        rw [hx2]
        have : 0 < Real.exp (L / 15000) := Real.exp_pos _
        nlinarith
    _ ≤ Real.exp ((1 - 1 / 15000) * L) * Real.exp (L / 15000) := by
        rw [pow_one] at h
        exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = T := hT'.symm

/-- The Lorentzian term at level `M_L = (εL/4)/c_L`. -/
theorem lorentz_term_le {T L R ε C₀ x : ℝ} (hT : 0 < T) (hL0 : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hC₀ : 0 < C₀) (hκ1 : 1 ≤ R * L) (hlx : Real.log x = L / 30000)
    (hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L) :
    4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
      (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153)) ≤
      4 * Real.pi * 2306 * 1200000 * C₀ * T * (Real.exp (-(R * L / 120000)) / ε) := by
  rw [hlx]
  set E := Real.exp (-(R * L / 120000)) with hE
  have hE' : Real.exp (-(R / 4) * (L / 30000)) = E := by rw [hE]; congr 1; ring
  rw [hE']
  have hE0 : 0 < E := Real.exp_pos _
  set Φ := C₀ * (4 * T + 4) * Real.log (4 * T + 5) with hΦdef
  have key : 4 * Real.pi / R * Φ / (ε * L / 4 / (2 * E / (L / 30000) * 1153)) =
      4 * Real.pi * 2306 * 120000 * E / (ε * R * L ^ 2) * Φ := by
    field_simp; ring
  rw [key]
  calc 4 * Real.pi * 2306 * 120000 * E / (ε * R * L ^ 2) * Φ
      ≤ 4 * Real.pi * 2306 * 120000 * E / (ε * R * L ^ 2) * (10 * C₀ * T * L) :=
        mul_le_mul_of_nonneg_left hΦ (by positivity)
    _ = 4 * Real.pi * 2306 * 1200000 * C₀ * T * (E / ε) / (R * L) := by
        field_simp; ring
    _ ≤ 4 * Real.pi * 2306 * 1200000 * C₀ * T * (E / ε) := div_le_self (by positivity) hκ1

/-- The far-majorant term at level `εL/4`. -/
theorem far_term_le {T L R ε C₀ x : ℝ} (hT : 0 < T) (hL0 : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hC₀ : 0 < C₀) (hκ1 : 1 ≤ R * L) (hlx : Real.log x = L / 30000)
    (hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L)
    (hΦ0 : 0 ≤ Real.log (4 * T + 5)) :
    4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
      (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4) ≤
      1600000 * Real.pi * C₀ * T * (Real.exp (-(R * L / 120000)) / ε) := by
  rw [hlx]
  set E := Real.exp (-(R * L / 120000)) with hE
  have hexp : Real.exp (-(R / 2 * (L / 30000))) ≤ E := by
    rw [hE]; apply Real.exp_le_exp.mpr
    have : 0 ≤ R * L := by positivity
    nlinarith
  set Φ := C₀ * (4 * T + 4) * Real.log (4 * T + 5) with hΦdef
  have hΦ0' : 0 ≤ Φ := by positivity
  have key : 4 * Real.pi / (3 * R * (L / 30000)) * Real.exp (-(R / 2 * (L / 30000))) * Φ /
      (ε * L / 4) = 4 * Real.pi * 120000 / (3 * ε * R * L ^ 2) *
        (Real.exp (-(R / 2 * (L / 30000))) * Φ) := by
    field_simp; ring
  rw [key]
  calc 4 * Real.pi * 120000 / (3 * ε * R * L ^ 2) * (Real.exp (-(R / 2 * (L / 30000))) * Φ)
      ≤ 4 * Real.pi * 120000 / (3 * ε * R * L ^ 2) * (E * (10 * C₀ * T * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hexp hΦ hΦ0' (Real.exp_pos _).le
    _ = 1600000 * Real.pi * C₀ * T * (E / ε) / (R * L) := by
        field_simp; ring
    _ ≤ 1600000 * Real.pi * C₀ * T * (E / ε) :=
        div_le_self (by have := Real.exp_pos (-(R * L / 120000)); positivity) hκ1

/-- The Dirichlet-polynomial term at level `εL/4`. -/
theorem poly_term_le {T L R ε N : ℝ} (hT : 64 ≤ T) (hL0 : 0 < L) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (hε : 0 < ε) (hN : N ≤ T) :
    1380 * (20 * (T + 17 * R + N) / R ^ 2) / (Real.pi * (ε * L / 4) ^ 2) ≤
      1324800 / Real.pi * T * (1 / (ε ^ 2 * (R * L) ^ 2)) := by
  have hsum : T + 17 * R + N ≤ 3 * T := by linarith
  have e : 1380 * (20 * (T + 17 * R + N) / R ^ 2) / (Real.pi * (ε * L / 4) ^ 2) =
      441600 / (Real.pi * ε ^ 2 * (R * L) ^ 2) * (T + 17 * R + N) := by
    field_simp; ring
  have e2 : 1324800 / Real.pi * T * (1 / (ε ^ 2 * (R * L) ^ 2)) =
      441600 / (Real.pi * ε ^ 2 * (R * L) ^ 2) * (3 * T) := by
    field_simp; ring
  rw [e, e2]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The window term. -/
theorem window_term_le {T L R ε A Kw x S : ℝ} (hT : 0 < T) (hL : Real.log T = L)
    (hκ : 30000 ≤ R * L) (hε : 0 < ε) (hε1 : ε ≤ 1) (hA : 0 < A)
    (hlx : Real.log x = L / 30000)
    (hE5 : 144 * Kw / Real.pi * (L + 3) ^ 2 ≤ Real.exp ((1 / 2 - 1 / 10000) * L))
    (hS : S ≤ 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) +
      144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi) :
    S ≤ 336 * A / Real.pi * T * (Real.exp (-(R * L / 120000)) / ε) + T ^ ((1 : ℝ) / 2) := by
  set κ := R * L with hκdef
  set E := Real.exp (-(κ / 120000)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEε : E ≤ E / ε := le_div_self hE0.le hε hε1
  have ha1 : 168 * T * A / Real.pi * (1 + 9600 / κ) * Real.exp (-(κ / 9600)) ≤
      336 * A / Real.pi * T * (E / ε) := by
    have h1 : 1 + 9600 / κ ≤ 2 := by
      have : 9600 / κ ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have h2 : Real.exp (-(κ / 9600)) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have : 0 ≤ κ := by linarith
      linarith
    have hc : 0 ≤ 168 * T * A / Real.pi := by positivity
    calc 168 * T * A / Real.pi * (1 + 9600 / κ) * Real.exp (-(κ / 9600))
        ≤ 168 * T * A / Real.pi * 2 * E :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (Real.exp_pos _).le (by positivity)
      _ = 336 * A / Real.pi * T * E := by ring
      _ ≤ 336 * A / Real.pi * T * (E / ε) :=
          mul_le_mul_of_nonneg_left hEε (by positivity)
  have ha2 : 144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi ≤ T ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hT, hL, hlx]
    have e : 144 * (L + 3) ^ 2 * Kw * Real.exp (3 * (L / 30000)) / Real.pi =
        144 * Kw / Real.pi * (L + 3) ^ 2 * Real.exp (L / 10000) := by
      rw [show 3 * (L / 30000) = L / 10000 by ring]; ring
    rw [e]
    have e2 : Real.exp (L * (1 / 2)) = Real.exp ((1 / 2 - 1 / 10000) * L) * Real.exp (L / 10000) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right hE5 (Real.exp_pos _).le
  linarith

/-- Selberg's explicit formula with remainder `≤ 1` at every height of `[T, 2T]`, for `x` with
`(log T + 3)⁴⁰ ≤ x` and `log x ≤ (log T)/8`. -/
theorem selberg_explicit_formula_block {KE t₀ T x : ℝ}
    (hEFall : ∀ t : ℝ, 64 ≤ t → ∃ T₁ T₂ : ℝ,
      t / 2 - 1 < T₁ ∧ T₁ < t / 2 + 1 ∧ 3 * t / 2 - 1 < T₂ ∧ T₂ < 3 * t / 2 + 1 ∧
      ∀ x : ℝ, 1 < x → ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 →
        riemannZeta s₀ ≠ 0 →
        ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
          ∑ w ∈ selbergHeightZeros t T₁ T₂,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤
          selbergHeightError KE x t)
    (ht₀ : ∀ t ≥ t₀, ∀ x : ℝ, Real.log t ^ (40 : ℕ) ≤ x → x ≤ t ^ ((1 : ℝ) / 8) →
      selbergHeightError KE x t ≤ 1)
    (hT64 : 64 ≤ T) (hTt₀ : t₀ ≤ T) (hx : 1 < x) (hx40 : (Real.log T + 3) ^ 40 ≤ x)
    (hx8 : Real.log x ≤ Real.log T / 8) :
    ∀ t ∈ Icc T (2 * T), ∃ T₁ T₂ : ℝ, t / 2 - 1 < T₁ ∧ T₂ < 3 * t / 2 + 1 ∧ T₁ ≤ T₂ ∧
      ∀ s₀ : ℂ, |s₀.im - t| ≤ t / 8 → 1 / 2 ≤ s₀.re → s₀.re ≤ 1 → riemannZeta s₀ ≠ 0 →
        ‖logDeriv riemannZeta s₀ + selbergVonMangoldtPoly x s₀ +
          ∑ w ∈ selbergHeightZeros t T₁ T₂,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * selbergKernel x (w - s₀)‖ ≤ 1 := by
  intro t ht
  have hT0 : 0 < T := by linarith
  have ht64 : 64 ≤ t := le_trans hT64 ht.1
  have ht0 : 0 < t := by linarith
  obtain ⟨T₁, T₂, a1, a2, a3, a4, hb⟩ := hEFall t ht64
  refine ⟨T₁, T₂, a1, a4, by linarith, fun s₀ h1 h2 h3 h4 => (hb x hx s₀ h1 h2 h3 h4).trans ?_⟩
  have hlogt : Real.log t ≤ Real.log T + 3 := by
    have h1 : Real.log t ≤ Real.log (2 * T) := Real.log_le_log ht0 ht.2
    rw [Real.log_mul (by norm_num) hT0.ne'] at h1
    have := Real.log_two_lt_d9
    linarith
  have hlogT : Real.log T ≤ Real.log t := Real.log_le_log hT0 ht.1
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  refine ht₀ t (le_trans hTt₀ ht.1) x ?_ ?_
  · exact (pow_le_pow_left₀ hlogt0 hlogt 40).trans hx40
  · rw [Real.rpow_def_of_pos ht0]
    have hx0 : 0 < x := by linarith
    rw [← Real.exp_log hx0]
    apply Real.exp_le_exp.mpr
    linarith

/-- Combination of the four terms. -/
theorem four_terms_combine {a b c d A Cb Cc T E ε κ s : ℝ} (hA : 0 ≤ A) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (hT : 0 ≤ T) (hE : 0 ≤ E) (hε : 0 < ε) (hs : 0 ≤ s)
    (ha : a ≤ 336 * A / Real.pi * T * (E / ε) + s) (hb : b ≤ Cb * T * (E / ε))
    (hc : c ≤ Cc * T * (E / ε)) (hd : d ≤ 1324800 / Real.pi * T * (1 / (ε ^ 2 * κ ^ 2))) :
    a + b + c + d ≤ (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * T *
      (E / ε + 1 / (ε ^ 2 * κ ^ 2)) + (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * s := by
  have hp : 0 ≤ 336 * A / Real.pi := by positivity
  have hq : 0 ≤ 1324800 / Real.pi := by positivity
  have hTE : 0 ≤ T * (E / ε) := by positivity
  have hTk : 0 ≤ T * (1 / (ε ^ 2 * κ ^ 2)) := by positivity
  have k1 : (336 * A / Real.pi + Cb + Cc) * (T * (E / ε)) ≤
      (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * (T * (E / ε)) :=
    mul_le_mul_of_nonneg_right (by linarith) hTE
  have k2 : 1324800 / Real.pi * (T * (1 / (ε ^ 2 * κ ^ 2))) ≤
      (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * (T * (1 / (ε ^ 2 * κ ^ 2))) :=
    mul_le_mul_of_nonneg_right (by linarith) hTk
  have k3 : 1 * s ≤ (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * s :=
    mul_le_mul_of_nonneg_right (by linarith) hs
  have e1 : 336 * A / Real.pi * T * (E / ε) + Cb * T * (E / ε) + Cc * T * (E / ε) =
      (336 * A / Real.pi + Cb + Cc) * (T * (E / ε)) := by ring
  have e2 : 1324800 / Real.pi * T * (1 / (ε ^ 2 * κ ^ 2)) =
      1324800 / Real.pi * (T * (1 / (ε ^ 2 * κ ^ 2))) := by ring
  have e3 : (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * T *
      (E / ε + 1 / (ε ^ 2 * κ ^ 2)) =
      (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * (T * (E / ε)) +
      (336 * A / Real.pi + Cb + Cc + 1324800 / Real.pi + 1) * (T * (1 / (ε ^ 2 * κ ^ 2))) := by
    ring
  rw [e3]
  linarith

/-- The four exceptional measures at one scale, bounded in closed form. -/
theorem scale_terms_le {T L R ε A Kw C₀ x S : ℝ} (hT64 : 64 ≤ T) (hL : Real.log T = L)
    (hR : 0 < R) (hR16 : R ≤ 1 / 16) (hκ : 30000 ≤ R * L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : 0 < A) (hC₀ : 0 < C₀) (hx : x = Real.exp (L / 30000))
    (hE5 : 144 * Kw / Real.pi * (L + 3) ^ 2 ≤ Real.exp ((1 / 2 - 1 / 10000) * L))
    (hE6 : 16 * (Real.log T + 3) ^ 1 ≤ Real.exp ((1 - 1 / 15000) * Real.log T))
    (hS0 : 0 ≤ S)
    (hS : S ≤ 168 * T * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) +
      144 * (L + 3) ^ 2 * Kw * Real.exp (3 * Real.log x) / Real.pi) :
    ENNReal.ofReal S +
        ENNReal.ofReal (4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
          (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153))) +
        ENNReal.ofReal (4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
          (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4)) +
        ENNReal.ofReal (1380 * (20 * (T + 17 * R + 8 * selbergPolyLength x *
          (1 + Real.log (selbergPolyLength x))) / R ^ 2) / (Real.pi * (ε * L / 4) ^ 2)) ≤
      ENNReal.ofReal ((336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ +
          1600000 * Real.pi * C₀ + 1324800 / Real.pi + 1) * T *
          (Real.exp (-(R * L / 120000)) / ε + 1 / (ε ^ 2 * (R * L) ^ 2)) +
        (336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ + 1600000 * Real.pi * C₀ +
          1324800 / Real.pi + 1) * T ^ ((1 : ℝ) / 2)) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by rw [← hL]; exact Real.log_pos (by linarith)
  have hlx : Real.log x = L / 30000 := by rw [hx, Real.log_exp]
  have hx1 : 1 < x := by rw [hx]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hlx0 := Real.log_pos hx1
  have hκ1 : 1 ≤ R * L := by linarith
  have hΦ0 : 0 ≤ Real.log (4 * T + 5) := Real.log_nonneg (by linarith)
  have hΦ : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ 10 * C₀ * T * L := by
    have h1 : Real.log (4 * T + 5) ≤ 2 * L := by
      have : Real.log (4 * T + 5) ≤ Real.log (T ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow, hL] at this
      push_cast at this
      linarith
    have h3 : C₀ * (4 * T + 4) * Real.log (4 * T + 5) ≤ C₀ * (5 * T) * (2 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₀.le) h1 hΦ0 (by positivity)
    linarith
  have ha := window_term_le hT0 hL hκ hε hε1 hA hlx hE5 hS
  have hb := lorentz_term_le (x := x) hT0 hL0 hR hε hC₀ hκ1 hlx hΦ
  have hc := far_term_le (x := x) hT0 hL0 hR hε hC₀ hκ1 hlx hΦ hΦ0
  have hN := polyLength_term_le (by linarith) hE6
  rw [hL, ← hx] at hN
  have hd := poly_term_le hT64 hL0 hR hR16 hε hN
  have hN0 : 0 ≤ (selbergPolyLength x : ℝ) * (1 + Real.log (selbergPolyLength x)) := by
    rcases Nat.eq_zero_or_pos (selbergPolyLength x) with h0 | hpos
    · rw [h0]; simp
    · have := Real.log_nonneg (show (1 : ℝ) ≤ selbergPolyLength x by exact_mod_cast hpos)
      positivity
  have hnb : 0 ≤ 4 * Real.pi / R * (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) /
      (ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153)) := by positivity
  have hnc : 0 ≤ 4 * Real.pi / (3 * R * Real.log x) * Real.exp (-(R / 2 * Real.log x)) *
      (C₀ * (4 * T + 4) * Real.log (4 * T + 5)) / (ε * L / 4) := by positivity
  have hnd0 : 0 ≤ T + 17 * R + 8 * (selbergPolyLength x : ℝ) *
      (1 + Real.log (selbergPolyLength x)) := by
    have : 0 ≤ 8 * ((selbergPolyLength x : ℝ) * (1 + Real.log (selbergPolyLength x))) :=
      by positivity
    rw [← mul_assoc] at this
    linarith
  have hnd : 0 ≤ 1380 * (20 * (T + 17 * R + 8 * selbergPolyLength x *
      (1 + Real.log (selbergPolyLength x))) / R ^ 2) / (Real.pi * (ε * L / 4) ^ 2) := by
    positivity
  rw [← ENNReal.ofReal_add hS0 hnb, ← ENNReal.ofReal_add (by positivity) hnc,
    ← ENNReal.ofReal_add (by positivity) hnd]
  exact ENNReal.ofReal_le_ofReal (four_terms_combine hA.le (by positivity) (by positivity) hT0.le
    (Real.exp_pos _).le hε (by positivity) ha hb hc hd)

/-- **Typical `ζ'/ζ` box bound at one scale.** For `0 < ε ≤ 1` there is `C` such that for all
large `T` and every scale `0 < R ≤ 1/16` with `κ = R log T ≥ 30000`, the heights `t ∈ [T, 2T]`
without log-derivative scale data at level `ε log T` have measure
`≤ C T (e^{−κ/120000}/ε + 1/(ε²κ²)) + C T^{1/2}`. -/
theorem exists_volume_not_zetaLogDerivScaleData_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → R ≤ 1 / 16 → 30000 ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (ε * Real.log T)} ≤
        ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / ε +
          1 / (ε ^ 2 * (R * Real.log T) ^ 2)) + C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨KE, hKE, hEFall⟩ := exists_selberg_explicit_formula_at_height
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (eventually_selbergHeightError_le_one hKE)
  obtain ⟨A, Kw, hA, hKw, hwin⟩ := exists_sum_selbergRightWindow_le
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_sum_mult_selbergMidZeros_le
  refine ⟨336 * A / Real.pi + 4 * Real.pi * 2306 * 1200000 * C₀ + 1600000 * Real.pi * C₀ +
    1324800 / Real.pi + 1, by positivity, ?_⟩
  have hE2 := eventually_mul_log_add_pow_le_exp 40 1 (show (0 : ℝ) < 1 / 30000 by norm_num)
  have hE3 := Real.tendsto_log_atTop.eventually_ge_atTop (4 / ε)
  have hE5 := eventually_mul_log_add_pow_le_exp 2 (144 * Kw / Real.pi)
    (show (0 : ℝ) < 1 / 2 - 1 / 10000 by norm_num)
  have hE6 := eventually_mul_log_add_pow_le_exp 1 16 (show (0 : ℝ) < 1 - 1 / 15000 by norm_num)
  filter_upwards [hwin, eventually_ge_atTop (max t₀ 64), hE2, hE3, hE5, hE6] with T hTwin hTt
    hE2 hE3 hE5 hE6
  intro R hR hR16 hκ
  have hT64 : 64 ≤ T := le_of_max_le_right hTt
  set L := Real.log T with hLdef
  have hL4 : 4 ≤ L := le_trans (by rw [le_div_iff₀ hε]; linarith) hE3
  have hL0 : 0 < L := by linarith
  set x := Real.exp (L / 30000) with hxdef
  have hlx : Real.log x = L / 30000 := Real.log_exp _
  have hx : 1 < x := Real.one_lt_exp_iff.mpr (by positivity)
  have hRx : 1 ≤ 36 * R * Real.log x := by
    rw [hlx]
    have : 36 * R * (L / 30000) = 36 * (R * L) / 30000 := by ring
    rw [this, le_div_iff₀ (by norm_num)]
    linarith
  have hEF := selberg_explicit_formula_block hEFall ht₀ hT64 (le_of_max_le_left hTt) hx
    (by rw [hxdef, show L / 30000 = 1 / 30000 * L by ring]; linarith)
    (by rw [hlx]; linarith)
  have hcL0 : 0 < 2 * Real.exp (-(R / 4) * Real.log x) / Real.log x * 1153 := by
    have := Real.log_pos hx; positivity
  have hεL : 0 < ε * L / 4 := by positivity
  have hε4 : 4 ≤ ε * L := by
    have := (div_le_iff₀ hε).mp hE3
    linarith
  refine (volume_not_zetaLogDerivScaleData_le_of (B := ε * L) (C₀ := C₀)
    (M_D := ε * L / 4) (M_L := ε * L / 4 / (2 * Real.exp (-(R / 4) * Real.log x) /
      Real.log x * 1153)) (M_F := ε * L / 4) hT64 hx hR hR16 hRx hEF (hC₀ T (by linarith))
    hεL (div_pos hεL hcL0) hεL (by rw [mul_div_cancel₀ _ hcL0.ne']; linarith)).trans ?_
  exact scale_terms_le hT64 hLdef.symm hR hR16 hκ hε hε1 hA hC₀pos hxdef hE5 hE6
    (Finset.sum_nonneg fun w _ => by have := selbergRightWindow_pos (x := x) hR w; positivity)
    (hTwin x R hx hR (by linarith) (by linarith) (by
      rw [hlx, show 6 * (L / 30000) / L = 1 / 5000 by field_simp; ring]; norm_num))

end RHTower
