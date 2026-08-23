import GaloisForLFunctions.RHTower.ZetaDivPowRepresentative
import GaloisForLFunctions.RHTower.HeadTailMellinAnalytic
import GaloisForLFunctions.RHTower.ZetaMellinHeadHardy
import GaloisForLFunctions.RHTower.MellinReflectionEquation

/-!
# Head/tail descriptions of `ζ(s)/(s-ρ)^l` and of its reflection

Burnol's Proposition 4.2 (`isMellinHeadHardy_zetaQuotient`) says `ζ(s)/(s-ρ)^l` lies in the head
Hardy class `L̂₁`; combined with Proposition 4.1 that produces a head constant and a tail datum.
The reflection `χ(s)·(ζ/(·-ρ)^l)(1-s)` is `(-1)^l ζ(s)/(s-(1-ρ))^l`, of the very same shape at the
mirror zero `1-ρ`, whose order equals that of `ρ` (`analyticOrderAt_riemannZeta_one_sub`).  So the
*two-sided* hypothesis of `SoninFromHardyData` is available for these functions.

## Main results

* `exists_headTail_zetaDivPowNF`
* `exists_headTail_zetaDivPowNF_reflect`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem ne_intCast_of_mem_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (m : ℤ) : s ≠ (m : ℂ) := by
  intro hm
  have hre : s.re = (m : ℝ) := by rw [hm]; simp
  rw [hre] at h0 h1
  have hm0 : (0 : ℤ) < m := by exact_mod_cast h0
  have hm1 : m < (1 : ℤ) := by exact_mod_cast h1
  omega

theorem chi_sign_cancel (A Z1 P e : ℂ) (he : e * e = 1) (he0 : e ≠ 0) (hP : P ≠ 0) :
    A * (Z1 / (e * P)) = e * ((A * Z1) / P) := by
  have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have h1 : (e * P)⁻¹ = e * P⁻¹ := by rw [mul_inv, hinv]
  rw [div_eq_mul_inv, div_eq_mul_inv, h1]
  ring

theorem isOpen_openStrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem isOpen_rightStrip : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- **A head/tail description of the analytic representative of `ζ(s)/(s-ρ)^l`.** -/
theorem exists_headTail_zetaDivPowNF {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {l : ℕ} (hl : 1 ≤ l)
    (hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ (c : ℂ) (g : ℝ → ℂ), MemLp g 2 (volume.restrict (Ioi (1 : ℝ))) ∧
      ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 → zetaDivPowNF ρ l z = headTailMellin 1 c g z := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  obtain ⟨G, hGH, hGeq⟩ := isMellinHeadHardy_zetaQuotient hρ1 hρ0 hl hord
  obtain ⟨c, g, hg, hheq⟩ := (isMellinHeadHardy_iff one_pos G).1 hGH
  refine ⟨c, g, hg, ?_⟩
  have hoff : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 → z ≠ ρ →
      zetaDivPowNF ρ l z = headTailMellin 1 c g z := by
    intro z hz1 hz2 hzρ
    have hz1' : z ≠ 1 := by
      intro h; rw [h] at hz2; simp at hz2
    rw [zetaDivPowNF_eq hz1' hzρ, ← hGeq z hz1 hz1' hzρ, hheq z hz1 hz1']
  intro z hz1 hz2
  by_cases hzρ : z = ρ
  · subst hzρ
    have hz1' : z ≠ 1 := by
      intro h; rw [h] at hz2; simp at hz2
    refine eq_of_eventuallyEq_punctured ?_ ?_ ?_
    · exact ((analyticAt_zetaDivPowNF hρ1 hord hz1').continuousAt)
    · exact (differentiableAt_headTailMellin one_pos c hg hz1 hz1').continuousAt
    · have hnbhd : ∀ᶠ w : ℂ in 𝓝 z, 1 / 2 < w.re ∧ w.re < 1 :=
        isOpen_rightStrip.mem_nhds ⟨hz1, hz2⟩
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnbhd]
        with w hw hw'
      exact hoff w hw'.1 hw'.2 hw
  · exact hoff z hz1 hz2 hzρ

/-- **A head/tail description of the reflected representative.** -/
theorem exists_headTail_zetaDivPowNF_reflect {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {l : ℕ}
    (hl : 1 ≤ l) (hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ (c : ℂ) (g : ℝ → ℂ), MemLp g 2 (volume.restrict (Ioi (1 : ℝ))) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        burnolChiFactor s * zetaDivPowNF ρ l (1 - s) = headTailMellin 1 c g s := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hmre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by rw [Complex.sub_re]; simp
  have hm0 : 0 < ((1 : ℂ) - ρ).re := by rw [hmre]; linarith
  have hm1 : ((1 : ℂ) - ρ).re < 1 := by rw [hmre]; linarith
  have hordm : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ((1 : ℂ) - ρ) := by
    rw [analyticOrderAt_riemannZeta_one_sub h0 h1]
    exact hord
  obtain ⟨c₀, g₀, hg₀, heq₀⟩ := exists_headTail_zetaDivPowNF hm0 hm1 hl hordm
  refine ⟨(-1 : ℂ) ^ l * c₀, fun t : ℝ => (-1 : ℂ) ^ l * g₀ t, ?_, ?_⟩
  · exact hg₀.const_mul _
  -- the scaled head/tail transform
  have hscale : ∀ s : ℂ, headTailMellin 1 ((-1 : ℂ) ^ l * c₀) (fun t : ℝ => (-1 : ℂ) ^ l * g₀ t) s
      = (-1 : ℂ) ^ l * headTailMellin 1 c₀ g₀ s := by
    intro s
    rw [headTailMellin, headTailMellin, mul_add]
    congr 1
    · ring
    · rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      ring
  have hoff : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → s ≠ (1 : ℂ) - ρ →
      burnolChiFactor s * zetaDivPowNF ρ l (1 - s)
        = headTailMellin 1 ((-1 : ℂ) ^ l * c₀) (fun t : ℝ => (-1 : ℂ) ^ l * g₀ t) s := by
    intro s hs1 hs2 hsm
    have hs0 : 0 < s.re := by linarith
    have hint : ∀ m : ℤ, s ≠ (m : ℂ) := ne_intCast_of_mem_strip hs0 hs2
    have hzeta : riemannZeta s = burnolChiFactor s * riemannZeta (1 - s) :=
      riemannZeta_eq_burnolChiFactor_mul_one_sub hint
    have hsne1 : s ≠ 1 := by simpa using hint 1
    have hone : (1 : ℂ) - s ≠ 1 := by
      intro h
      have : s = 0 := by linear_combination -h
      exact (hint 0) (by simpa using this)
    have hrho : (1 : ℂ) - s ≠ ρ := by
      intro h
      exact hsm (by linear_combination -h)
    have hpowne : ((s : ℂ) - ((1 : ℂ) - ρ)) ^ l ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.2 hsm)
    have hsign : (((1 : ℂ) - s) - ρ) ^ l = (-1 : ℂ) ^ l * (s - ((1 : ℂ) - ρ)) ^ l := by
      rw [← mul_pow]
      congr 1
      ring
    have hsgn : ((-1 : ℂ) ^ l) ≠ 0 := pow_ne_zero _ (by norm_num)
    have he2 : ((-1 : ℂ) ^ l) * ((-1 : ℂ) ^ l) = 1 := by
      rw [← pow_add, show l + l = 2 * l from by ring, pow_mul]
      norm_num
    rw [zetaDivPowNF_eq hone hrho, hsign, hscale s, ← heq₀ s hs1 hs2,
      zetaDivPowNF_eq hsne1 hsm, hzeta]
    exact chi_sign_cancel _ _ _ _ he2 hsgn hpowne
  intro s hs1 hs2
  by_cases hsm : s = (1 : ℂ) - ρ
  · subst hsm
    have hsne1 : ((1 : ℂ) - ρ) ≠ 1 := by
      intro h; rw [h] at hs2; simp at hs2
    refine eq_of_eventuallyEq_punctured (ρ := (1 : ℂ) - ρ)
      (F := fun w : ℂ => burnolChiFactor w * zetaDivPowNF ρ l (1 - w))
      (H := fun w : ℂ => headTailMellin 1 ((-1 : ℂ) ^ l * c₀)
        (fun t : ℝ => (-1 : ℂ) ^ l * g₀ t) w) ?_ ?_ ?_
    · have hchi : ContinuousAt burnolChiFactor ((1 : ℂ) - ρ) :=
        (differentiableAt_burnolChiFactor hs2).continuousAt
      have hz : ContinuousAt (fun s : ℂ => zetaDivPowNF ρ l (1 - s)) ((1 : ℂ) - ρ) := by
        have hone : ((1 : ℂ) - ((1 : ℂ) - ρ)) ≠ 1 := by
          have : (1 : ℂ) - ((1 : ℂ) - ρ) = ρ := by ring
          rw [this]
          exact hρ1
        have ha := (analyticAt_zetaDivPowNF hρ1 hord hone).continuousAt
        have hsub : ContinuousAt (fun s : ℂ => (1 : ℂ) - s) ((1 : ℂ) - ρ) := by fun_prop
        exact ha.comp hsub
      exact hchi.mul hz
    · exact (differentiableAt_headTailMellin one_pos _ (hg₀.const_mul _) hs1 hsne1).continuousAt
    · have hnbhd : ∀ᶠ w : ℂ in 𝓝 ((1 : ℂ) - ρ), 1 / 2 < w.re ∧ w.re < 1 :=
        isOpen_rightStrip.mem_nhds ⟨hs1, hs2⟩
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnbhd]
        with w hw hw'
      exact hoff w hw'.1 hw'.2 hw
  · exact hoff s hs1 hs2 hsm

end

end RHTower
