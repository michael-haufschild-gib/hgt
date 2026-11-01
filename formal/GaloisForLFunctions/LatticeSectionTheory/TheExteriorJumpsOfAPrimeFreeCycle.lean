import GaloisForLFunctions.LatticeSectionTheory.ThePrimitiveH1OfPrimeFreeCyclesIsAJumpCount

/-!
# The exterior jumps of a prime-free cycle

On a test `f` supported in `[−a, a]` the jump count `J(f) = ∫_0^∞ (A_f(0) − A_f(x)) w(x) dx`,
`w(x) = e^{x/2}/sinh x`, counts every jump of `f` with the Lévy weight of the Gamma factor. Two
families of jumps are seen by every such test, whatever its shape:

* **Gaps beyond `2a`.** `A_f(x) = 0`, so the whole mass `‖f‖²` jumps (`ThePrimitiveH1OfPrime…`).
* **Gaps between `a` and `2a`** (`autocorr_le_half_of_le`). The translate by `x ≥ a` overlaps `f`
  only where `f` sits left of `0` and the translate right of `0`, so
  `A_f(x) ≤ ½(∫_{u ≤ 0} f² + ∫_{u ≥ 0} f²) = ½‖f‖²`: half the mass jumps.

With the Lévy tail `w(x) ≥ 2 e^{−x/2}` on `(1, ∞)` (`archLevySinhWeight_ge_exp`) this gives
(`jumpCount_ge_exterior`)

    J(f) ≥ ‖f‖² (½(log 2 − a/2) + log(1/2a) − (1 − 2a)/2 + 4 e^{−1/2}),

and the count alone forces prime-free positivity on the larger window `a ≤ 1/64`
(`exteriorJumps_derivation_of_primeFree_positivity`): `W(f, f) ≥ ‖f‖²/20`, and the primitive `h¹`
of these cycles is at least `‖f‖²/40` (`primitiveH1_ge_of_exteriorJumps`).
-/

noncomputable section

open Real MeasureTheory Set

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri BiScaleUncertainty RHTower.ArchimedeanAnomaly Zeta23

/-- **Half the mass jumps across gaps between `a` and `2a`.** For a test supported in `[−a, a]` and
`x ≥ a`: `A_f(x) ≤ ½ ‖f‖²`. -/
theorem autocorr_le_half_of_le {f : ℝ → ℝ} (hf : f ∈ realTests) {a x : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (hax : a ≤ x) : autocorr f x ≤ (∫ u, f u ^ 2) / 2 := by
  have hcont : Continuous f := hf.1.continuous
  have hsq : Integrable fun u => f u ^ 2 :=
    (hcont.pow 2).integrable_of_hasCompactSupport (hf.2.pow (by norm_num))
  set g₁ : ℝ → ℝ := (Iic (0 : ℝ)).indicator fun u => f u ^ 2
  set g₂ : ℝ → ℝ := (Ici (0 : ℝ)).indicator fun u => f u ^ 2
  have hg₁ : Integrable g₁ := hsq.indicator measurableSet_Iic
  have hg₂ : Integrable g₂ := hsq.indicator measurableSet_Ici
  -- pointwise: the product lives where `f` is left of `0` and its translate right of `0`
  have hpt : ∀ u, f u * f (u + x) ≤ (g₁ u + g₂ (u + x)) / 2 := by
    intro u
    have h1 : 0 ≤ g₁ u := Set.indicator_nonneg (fun _ _ => sq_nonneg _) u
    have h2 : 0 ≤ g₂ (u + x) := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
    by_cases hu : f u = 0
    · rw [hu, zero_mul]; linarith
    by_cases hux : f (u + x) = 0
    · rw [hux, mul_zero]; linarith
    have hu' := hs (subset_tsupport f hu)
    have hux' := hs (subset_tsupport f hux)
    have hl : u ∈ Iic (0 : ℝ) := by simp only [mem_Iic]; linarith [hu'.1, hux'.2]
    have hr : u + x ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith [hu'.1, hux'.1]
    simp only [g₁, g₂, Set.indicator_of_mem hl, Set.indicator_of_mem hr]
    nlinarith [sq_nonneg (f u - f (u + x))]
  have hprod : Integrable fun u => f u * f (u + x) :=
    (hcont.mul (hcont.comp (continuous_add_right x))).integrable_of_hasCompactSupport
      (hf.2.mul_right)
  have hrhs : Integrable fun u => (g₁ u + g₂ (u + x)) / 2 :=
    (hg₁.add (hg₂.comp_add_right x)).div_const 2
  have hmono := integral_mono hprod hrhs hpt
  have hsplit : ∫ u, (g₁ u + g₂ (u + x)) / 2 = (∫ u, f u ^ 2) / 2 := by
    rw [integral_div, integral_add hg₁ (hg₂.comp_add_right x),
      MeasureTheory.integral_add_right_eq_self g₂ x]
    simp only [g₁, g₂]
    rw [integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ici,
      integral_Ici_eq_integral_Ioi, intervalIntegral.integral_Iic_add_Ioi hsq.integrableOn
        hsq.integrableOn]
  unfold autocorr
  linarith

/-- The Lévy weight dominates its tail: `e^{x/2}/sinh x ≥ 2 e^{−x/2}`. -/
theorem archLevySinhWeight_ge_exp {x : ℝ} (hx : 0 < x) :
    2 * Real.exp (-(1 / 2) * x) ≤ archLevySinhWeight x := by
  unfold archLevySinhWeight
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hsinh : Real.sinh x ≤ Real.exp x / 2 := by
    rw [Real.sinh_eq]; linarith [Real.exp_pos (-x)]
  rw [le_div_iff₀ hs]
  have : 2 * Real.exp (-(1 / 2) * x) * (Real.exp x / 2) = Real.exp (x / 2) := by
    rw [mul_div_assoc', mul_comm 2, mul_div_assoc, div_self two_ne_zero.symm.symm, mul_one,
      ← Real.exp_add]
    · congr 1; ring
  have h := mul_le_mul_of_nonneg_left hsinh (show 0 ≤ 2 * Real.exp (-(1 / 2) * x) by positivity)
  linarith

/-- **Exterior jumps.** A test supported in `[−a, a]`, `0 < 2a ≤ 1`, has
`J(f) ≥ ‖f‖²(½(log 2 − a/2) + log(1/2a) − (1 − 2a)/2 + 4 e^{−1/2})`. -/
theorem jumpCount_ge_exterior {f : ℝ → ℝ} (hf : f ∈ realTests) {a : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (ha0 : 0 < a) (ha1 : 2 * a ≤ 1) :
    (∫ u, f u ^ 2) * ((Real.log 2 - a / 2) / 2 + (Real.log (1 / (2 * a)) - (1 - 2 * a) / 2) +
      4 * Real.exp (-(1 / 2))) ≤ jumpCount f := by
  set M := ∫ u, f u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hA0 : autocorr f 0 = M := autocorr_zero_eq f
  set F := fun x : ℝ => (autocorr f 0 - autocorr f x) * archLevySinhWeight x
  have hint : IntegrableOn F (Ioi 0) := integrableOn_biScaleLevyIntegrand hf.1 hf.2
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ F x := by
    intro x hx
    have h1 := abs_autocorr_le_zero hf.2 hf.1.continuous x
    have h2 := le_abs_self (autocorr f x)
    exact mul_nonneg (by linarith) (archLevySinhWeight_pos hx).le
  -- the three windows `(a, 2a]`, `(2a, 1]`, `(1, ∞)`
  set S₁ := Ioc a (2 * a)
  set S₂ := Ioc (2 * a) 1
  set S₃ := Ioi (1 : ℝ)
  have hd12 : Disjoint S₁ S₂ := Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
  have hd3 : Disjoint (S₁ ∪ S₂) S₃ := Set.disjoint_left.mpr fun x h h3 => by
    rcases h with h | h
    · have : (1 : ℝ) < x := h3; linarith [h.2]
    · have : (1 : ℝ) < x := h3; linarith [h.2]
  have hsub : S₁ ∪ S₂ ∪ S₃ ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rcases hx with (h | h) | h
    · exact Set.mem_Ioi.mpr (by linarith [h.1])
    · exact Set.mem_Ioi.mpr (by linarith [h.1])
    · exact Set.mem_Ioi.mpr (lt_trans one_pos h)
  have hJ : ∫ x in S₁ ∪ S₂ ∪ S₃, F x ≤ jumpCount f :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall hnn)) (Filter.Eventually.of_forall hsub)
  have hi : ∀ S ⊆ Ioi (0 : ℝ), IntegrableOn F S := fun S hS => hint.mono_set hS
  rw [setIntegral_union hd3 measurableSet_Ioi (hi _ fun x hx => hsub (Or.inl hx))
      (hi _ fun x hx => hsub (Or.inr hx)),
    setIntegral_union hd12 measurableSet_Ioc (hi _ fun x hx => hsub (Or.inl (Or.inl hx)))
      (hi _ fun x hx => hsub (Or.inl (Or.inr hx)))] at hJ
  -- window `(a, 2a]`: half the mass jumps
  have hinvI : ∀ b c : ℝ, 0 < b → b ≤ c → IntervalIntegrable (fun x : ℝ => x⁻¹) volume b c :=
    fun b c hb _ => intervalIntegral.intervalIntegrable_inv (fun x hx => (show (0 : ℝ) < x by
      rcases Set.mem_uIcc.mp hx with h | h <;> linarith [h.1, h.2]).ne') continuousOn_id
  have hcontS : ∀ b c : ℝ, 0 < b → ContinuousOn (fun x : ℝ => 1 / x - 1 / 2) (Icc b c) :=
    fun b c hb => (continuousOn_const.div continuousOn_id fun x hx =>
      (show (0 : ℝ) < x by linarith [hx.1]).ne').sub continuousOn_const
  have hintI : ∀ b c : ℝ, 0 < b → b ≤ c →
      ∫ x in Ioc b c, (1 / x - 1 / 2) = Real.log (c / b) - (c - b) / 2 := by
    intro b c hb hbc
    rw [← intervalIntegral.integral_of_le hbc]
    simp only [one_div]
    rw [intervalIntegral.integral_sub (hinvI b c hb hbc) intervalIntegrable_const,
      integral_inv_of_pos hb (by linarith), intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h1 : M / 2 * (Real.log 2 - a / 2) ≤ ∫ x in S₁, F x := by
    have hlow : ∫ x in S₁, M / 2 * (1 / x - 1 / 2) ≤ ∫ x in S₁, F x := by
      refine setIntegral_mono_on (((hcontS a (2 * a) ha0).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self).const_mul _) (hi _ fun x hx => hsub (Or.inl (Or.inl hx)))
        measurableSet_Ioc fun x hx => ?_
      have hx0 : 0 < x := by linarith [hx.1]
      have hhalf := autocorr_le_half_of_le hf hs hx.1.le
      have hw := archLevySinhWeight_ge hx0
      have hwpos := (archLevySinhWeight_pos hx0).le
      show M / 2 * (1 / x - 1 / 2) ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x
      rw [hA0]
      calc M / 2 * (1 / x - 1 / 2) ≤ M / 2 * archLevySinhWeight x :=
            mul_le_mul_of_nonneg_left hw (by linarith)
        _ ≤ (M - autocorr f x) * archLevySinhWeight x :=
            mul_le_mul_of_nonneg_right (by linarith) hwpos
    rw [integral_const_mul, hintI a (2 * a) ha0 (by linarith),
      show 2 * a / a = 2 by field_simp, show (2 * a - a) / 2 = a / 2 by ring] at hlow
    exact hlow
  -- window `(2a, 1]`: the whole mass jumps
  have h2 : M * (Real.log (1 / (2 * a)) - (1 - 2 * a) / 2) ≤ ∫ x in S₂, F x := by
    have hlow : ∫ x in S₂, M * (1 / x - 1 / 2) ≤ ∫ x in S₂, F x := by
      refine setIntegral_mono_on (((hcontS (2 * a) 1 (by linarith)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self).const_mul _) (hi _ fun x hx => hsub (Or.inl (Or.inr hx)))
        measurableSet_Ioc fun x hx => ?_
      show M * (1 / x - 1 / 2) ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x
      rw [hA0, autocorr_eq_zero_of_support hs hx.1, sub_zero]
      exact mul_le_mul_of_nonneg_left (archLevySinhWeight_ge (by linarith [hx.1])) hM
    rw [integral_const_mul, hintI (2 * a) 1 (by linarith) ha1] at hlow
    exact hlow
  -- the tail `(1, ∞)`
  have h3 : M * (4 * Real.exp (-(1 / 2))) ≤ ∫ x in S₃, F x := by
    have hlow : ∫ x in S₃, M * (2 * Real.exp (-(1 / 2) * x)) ≤ ∫ x in S₃, F x := by
      refine setIntegral_mono_on (((integrableOn_exp_mul_Ioi (by norm_num) 1).const_mul 2).const_mul
        M) (hi _ fun x hx => hsub (Or.inr hx)) measurableSet_Ioi fun x hx => ?_
      have hx1 : (1 : ℝ) < x := hx
      show M * (2 * Real.exp (-(1 / 2) * x)) ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x
      rw [hA0, autocorr_eq_zero_of_support hs (by linarith), sub_zero]
      exact mul_le_mul_of_nonneg_left (archLevySinhWeight_ge_exp (by linarith)) hM
    rw [integral_const_mul, integral_const_mul, integral_exp_mul_Ioi (by norm_num) 1] at hlow
    have : 2 * (-Real.exp (-(1 / 2) * 1) / -(1 / 2)) = 4 * Real.exp (-(1 / 2)) := by
      rw [mul_one]; field_simp; ring
    rw [this] at hlow
    exact hlow
  nlinarith

/-- **Prime-free positivity from the exterior jumps.** For a test supported in `[−a, a]`,
`0 < a ≤ 1/64`: `W(f, f) ≥ ‖f‖²/20`. -/
theorem exteriorJumps_derivation_of_primeFree_positivity {f : ℝ → ℝ} (hf : f ∈ realTests)
    {a : ℝ} (hs : tsupport f ⊆ Icc (-a) a) (ha0 : 0 < a) (ha : a ≤ 1 / 64) :
    (∫ u, f u ^ 2) / 20 ≤ weilPair f f := by
  have hlog2 : 2 * a < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hid := weilPair_eq_jumpCount_of_primeFree hf hs hlog2
  have hJ := jumpCount_ge_exterior hf hs ha0 (by linarith)
  have hP := abs_poleCross_le hf hs ha0.le hlog2 (toRealWeilTestFn hf).supportScale
  have hΩ := RHTower.WeilLevyOsculatingFloor.neg_gammaBracket_zero_lt_5373_over_1000
  set M := ∫ u, f u ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hl2 := Real.log_two_gt_d9
  -- `log(1/2a) ≥ log 32 = 5 log 2`
  have hlog : 5 * Real.log 2 ≤ Real.log (1 / (2 * a)) := by
    have h1 : (32 : ℝ) ≤ 1 / (2 * a) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h2 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
    rw [← h2]; exact Real.log_le_log (by norm_num) h1
  -- `4 e^{−1/2} ≥ 12/5`, from `e < 25/9`
  have hexp : 12 / 5 ≤ 4 * Real.exp (-(1 / 2)) := by
    have he := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have hlt : Real.exp (1 / 2) ≤ 5 / 3 := by
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    nlinarith
  have hcosh : Real.cosh a ≤ 2 := by
    have := Real.cosh_le_cosh.mpr (show |a| ≤ |1| by
      rw [abs_of_pos ha0, abs_one]; linarith)
    have hc1 : Real.cosh 1 ≤ 2 := by
      rw [Real.cosh_eq]
      have := Real.exp_one_lt_d9
      have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      linarith
    linarith
  have hpole : -(16 * a * M) ≤ 2 * poleCross (toRealWeilTestFn hf).supportScale f := by
    have h := (abs_le.mp hP).1
    have : 2 * Real.cosh a * M * (2 * a) ≤ 8 * a * M := by
      have := mul_le_mul_of_nonneg_right hcosh (show 0 ≤ M * a by positivity)
      nlinarith
    linarith
  have hbrack : 5 * Real.log 2 + (Real.log 2 - 1 / 128) / 2 - 1 / 2 + 12 / 5 ≤
      (Real.log 2 - a / 2) / 2 + (Real.log (1 / (2 * a)) - (1 - 2 * a) / 2) +
        4 * Real.exp (-(1 / 2)) := by
    nlinarith
  have hJ' : M * (5 * Real.log 2 + (Real.log 2 - 1 / 128) / 2 - 1 / 2 + 12 / 5) ≤ jumpCount f :=
    (mul_le_mul_of_nonneg_left hbrack hM).trans hJ
  have h16a : 16 * a * M ≤ M / 4 := by nlinarith
  rw [hid]
  nlinarith

/-- **The primitive `h¹` of the cycles of aperture `≤ 1/64` is controlled by their exterior jumps**:
`h¹_prim(x) ≥ ‖f‖²/40`. -/
theorem primitiveH1_ge_of_exteriorJumps {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 64)
    (x : ℝ × ℝ × realTestsAt a) :
    (∫ u, (x.2.2.1.1 u) ^ 2) / 40 ≤ primitiveH1 (scalingSubsurface (realTestsAt a)) x := by
  rw [primitiveH1_eq, scalingSubsurface_defect_self]
  have h := exteriorJumps_derivation_of_primeFree_positivity x.2.2.1.2 x.2.2.2 ha0 ha
  linarith

end GaloisForLFunctions.LatticeSectionTheory
