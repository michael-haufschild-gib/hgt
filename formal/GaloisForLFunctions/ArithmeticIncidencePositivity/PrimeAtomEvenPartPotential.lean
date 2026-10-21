import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpFoldOddWindowPastSevenTwentieths

/-!
# The first prime atom pays potential: its even part about `log 2 / 2`

For odd `F` supported in `[−r, r]`, `L/2 < r`, split `F` on the strip `S = [L − r, r]` into its parts
even and odd about `L/2`: `F(a) = e(a) + α(a)` and `F(L − a) = e(a) − α(a)`. The atom sees
`F(a)F(L − a) = e² − α²`, while `e² + α² = (F(a)² + F(L − a)²)/2`. Hence
(`integral_mul_shift_eq_two_reflectedOdd_sub`)

    ∫ F(x) F(x + L) dx = 2 ∫_S α² − ∫_S F².

The atom costs only through the odd part `α`. Its even part, the direction of the ground state,
makes it a gain: the prime term `−2Λ(2)/√2 ∫ F F(· + log 2)` of the Weil form equals
`2Λ(2)/√2 ∫_S F² − 4Λ(2)/√2 ∫_S α²`. Interpolating with `∫ F F(· + L) ≤ ∫_S α²`
(`integral_mul_shift_le_reflectedOdd`) gives, for `t ≤ 1`,
`∫ F F(· + L) ≤ (1 + t) ∫_S α² − t ∫_S F²` (`integral_mul_shift_le_interp`).

The sharp micro-fold pays `(1 + t)` times the odd part with the fraction
`θ = (1 + t) 2Λ(2)/√2 / λ` of the strip surplus. The strip then carries the positive prime potential
`(Λ(2)/√2) t ≥ (49/100) t` (`fourKilling_add_potentialMixPrime_le_archJump_sub_prime`). With `t = 1/2`
this is `0.245`, against a strip loss of order `θ L |S| / (2h)`: the inner-edge wall of the first
prime window disappears.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The atom on an odd test, exactly -/

/-- **The first prime atom on an odd test, exactly.** For odd `F` supported in `[−r, r]` with
`L − r ≤ r`: `∫ F(x) F(x + L) dx = 2 ∫_{L−r}^{r} α² − ∫_{L−r}^{r} F²`, `α` the odd part about `L/2`. -/
theorem integral_mul_shift_eq_two_reflectedOdd_sub {F : ℝ → ℝ} (hF : Continuous F)
    (hodd : ∀ x, F (-x) = -F x) {r L : ℝ} (hr0 : 0 ≤ r) (hLr : L - r ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    (∫ x, F x * F (x + L)) =
      2 * (∫ a in (L - r)..r, reflectedOddPart F L a ^ 2) - ∫ a in (L - r)..r, F a ^ 2 := by
  have e : (∫ x, F x * F (x + L)) = ∫ a, -(F a * F (L - a)) := by
    rw [← integral_neg_eq_self (fun x => F x * F (x + L)) volume]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [hodd, show -a + L = L - a by ring]
    ring
  set S := Icc (L - r) r
  have hpt : ∀ a, -(F a * F (L - a)) = S.indicator
      (fun a => 2 * reflectedOddPart F L a ^ 2 - (F a ^ 2 + F (L - a) ^ 2) / 2) a := by
    intro a
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha]; unfold reflectedOddPart; ring
    · rw [Set.indicator_of_notMem ha]
      have : F a * F (L - a) = 0 := by
        simp only [S, mem_Icc, not_and_or, not_le] at ha
        rcases ha with h | h
        · rw [hsupp (L - a) (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
        · rw [hsupp a (by rw [abs_of_pos (by linarith)]; linarith), zero_mul]
      rw [this, neg_zero]
  rw [e, integral_congr_ae (Eventually.of_forall hpt), MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hLr]
  -- `∫_S F(L − a)² = ∫_S F²` by the reflection `a ↦ L − a`
  have hrefl : (∫ a in (L - r)..r, F (L - a) ^ 2) = ∫ a in (L - r)..r, F a ^ 2 := by
    have := intervalIntegral.integral_comp_sub_left (fun a => F a ^ 2) L (a := L - r) (b := r)
    rw [sub_sub_cancel] at this
    exact this
  have hα : IntervalIntegrable (fun a => reflectedOddPart F L a ^ 2) volume (L - r) r := by
    apply Continuous.intervalIntegrable; unfold reflectedOddPart; fun_prop
  have h1 : IntervalIntegrable (fun a => F a ^ 2) volume (L - r) r :=
    (hF.pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun a => F (L - a) ^ 2) volume (L - r) r :=
    ((hF.comp (continuous_const.sub continuous_id)).pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hα.const_mul 2) ((h1.add h2).div_const 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_add h1 h2, hrefl]
  ring

/-- **The atom bounded by its odd part, interpolated.** For odd `F` supported in `[−r, r]`,
`L − r ≤ r`, and `t ≤ 1`: `∫ F(x) F(x + L) dx ≤ (1 + t) ∫_{L−r}^{r} α² − t ∫_{L−r}^{r} F²`. -/
theorem integral_mul_shift_le_interp {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) {r L : ℝ} (hr0 : 0 ≤ r) (hLr : L - r ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) {t : ℝ} (ht : t ≤ 1) :
    (∫ x, F x * F (x + L)) ≤
      (1 + t) * (∫ a in (L - r)..r, reflectedOddPart F L a ^ 2) - t * ∫ a in (L - r)..r, F a ^ 2 := by
  have h1 := integral_mul_shift_eq_two_reflectedOdd_sub hF hodd hr0 hLr hsupp
  have h2 := integral_mul_shift_le_reflectedOdd hF hFc hodd hr0 hLr hsupp
  nlinarith [mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 ht)]

/-- `Λ(2)/√2 = log 2/√2 ≥ 0.49`. -/
theorem vonMangoldtAtom_two_ge : 49 / 100 ≤ vonMangoldtAtom 2 := by
  unfold vonMangoldtAtom
  rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs0 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hl0 := Real.log_two_gt_d9
  push_cast at hs hs0 ⊢
  rw [le_div_iff₀ hs0]
  nlinarith

/-! ### The prime window with the even part kept -/

section MixPrime

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The first prime window with the strip shared and the atom's even part kept.** If the fraction
`θ` of the strip surplus pays `(1 + t)` times the odd part of the atom through the sharp micro-fold,
`(1 + t) 2Λ(2)/√2 ≤ θ λ`, `0 ≤ t ≤ 1`, the archimedean jump energy minus the prime term dominates the
killing, the mixed ground-state potential `(1 − θ) U_h + θ U_h^{off}`, and the prime potential
`(49/100) t` on the strip `[log 2 − r, r]`. -/
theorem fourKilling_add_potentialMixPrime_le_archJump_sub_prime {h : ℝ → ℝ} {r a₀ L θ t : ℝ}
    (hFcs : HasCompactSupport F) (hr : Real.log 2 / 2 < r) (hr' : r ≤ Real.log 2 / 2 + 1 / 12)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hθ : (1 + t) * (2 * (4902 / 10000)) ≤ θ * (19 / 10 - (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) -
      3 * ((r - (Real.log 2 - r)) / 2) ^ 2))
    (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hPcs : HasCompactSupport P) (hh : Continuous h) (ha₀ : 0 < a₀)
    (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
        θ * surplusPotentialOff h (Real.log 2 - r) r x)) (Ioi 0) ∧
      4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
          2 * ((∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
            θ * surplusPotentialOff h (Real.log 2 - r) r x)) +
          49 / 100 * t * ∫ x in (Real.log 2 - r)..r, F x ^ 2) ≤
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
          2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have hr0 : 0 < r := by linarith
  obtain ⟨hIA, hA⟩ := surplusEnergy_ge_potential hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 hrB hPr hFr
    hh ha₀ hhpos hhL
  obtain ⟨hIB, hBs⟩ := surplusEnergy_ge_potentialOff_add_strip hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1
    (p := Real.log 2 - r) (by linarith) (by linarith) hrB hPr hFr hh ha₀ hhpos hhL
  have hfold := fourKilling_add_surplusEnergy_le_archJump hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0
    hB1 hr0 hrB hPr hFr hPcs
  have hsupp : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  -- the sharp micro-fold pays the atom with the fraction `θ` of the strip
  set p := Real.log 2 - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hL : p + r = Real.log 2 := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr6 : r - p ≤ 1 / 6 := by rw [hpdef]; linarith
  have hms := sharpMicroFold_strip_ge hFc hFL hp0 hpr hL hr3 hr6
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hFc hFL hp0 hpr.le (by linarith)
  have hshift := integral_mul_shift_le_interp hFc hFcs hFo (r := r) (L := Real.log 2)
    (by linarith) (by rw [← hpdef]; exact hpr.le) hsupp ht1
  rw [← hpdef] at hshift
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F (Real.log 2) x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hΛ2 := vonMangoldtAtom_two_ge
  have hS0 : 0 ≤ ∫ x in p..r, F x ^ 2 := intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hdom : 2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) ≤
      θ * (2 * stripSurplus F p r) - 49 / 50 * t * ∫ x in p..r, F x ^ 2 := by
    set A := ∫ x in p..r, reflectedOddPart F (Real.log 2) x ^ 2 with hA
    set B := ∫ x in p..r, F x ^ 2 with hB
    have k1 := mul_le_mul_of_nonneg_left hshift hΛ0
    have k2 := mul_le_mul_of_nonneg_right hθ hα0
    have k3 := mul_le_mul_of_nonneg_right hΛ1 (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) hα0)
    have k4 := mul_le_mul_of_nonneg_left hms hθ0
    have k5 := mul_le_mul_of_nonneg_right hΛ2 (mul_nonneg ht0 hS0)
    rw [hT] at k4
    nlinarith
  -- the mixed potential
  have h1 : IntegrableOn (fun x => (1 - θ) * (F x ^ 2 * surplusPotential h r x)) (Ioi 0) :=
    hIA.const_mul (1 - θ)
  have h2 : IntegrableOn (fun x => θ * (F x ^ 2 * surplusPotentialOff h p r x)) (Ioi 0) :=
    hIB.const_mul θ
  have h3 : IntegrableOn (fun x => (1 - θ) * (F x ^ 2 * surplusPotential h r x) +
      θ * (F x ^ 2 * surplusPotentialOff h p r x)) (Ioi 0) := h1.add h2
  have hmix : IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
      θ * surplusPotentialOff h p r x)) (Ioi 0) :=
    h3.congr_fun (fun x _ => by ring) measurableSet_Ioi
  refine ⟨hmix, ?_⟩
  have hsplit : (∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
      θ * surplusPotentialOff h p r x)) =
      (1 - θ) * (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotential h r x) +
        θ * ∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h p r x := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
  rw [hsplit]
  have hθ1' : 0 ≤ 1 - θ := by linarith
  have k5 := mul_le_mul_of_nonneg_left hA hθ1'
  have k6 := mul_le_mul_of_nonneg_left hBs hθ0
  nlinarith

end MixPrime

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
