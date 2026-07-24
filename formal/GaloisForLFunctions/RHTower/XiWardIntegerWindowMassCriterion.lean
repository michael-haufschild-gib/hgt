import GaloisForLFunctions.RHTower.XiWardEdgeMassQuantization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integer-window mass criterion for the anti-causal Ward response

Localizing the edge mass quantization: any strict-right pair deposits mass at
least `4·arctan(1/2)` in the unit-radius window centered at the integer nearest
to its reflected height, because the reflected Lorentzian has half-width less
than one and mass `4·arctan(1/(2·width))` in its own half-unit window.

Consequently RH is equivalent to the vanishing of the countable family of
integer-window edge masses: a fully explicit criterion indexed by `ℤ`, with no
cutoff, grid, or choice in its statement.
-/

open Complex Filter MeasureTheory Real

namespace RHTower

noncomputable section

/-- Windowed Lorentzian mass: the half-unit window of a centered Lorentzian of
half-width `x` carries mass `4·arctan(1/(2x))`. -/
theorem windowed_lorentzian_integral {x : ℝ} (hx : 0 < x) :
    ∫ u in (-(1 / 2) : ℝ)..(1 / 2), 2 * x / (x ^ 2 + u ^ 2) =
      4 * Real.arctan (1 / (2 * x)) := by
  have hfun : ∀ u : ℝ, 2 * x / (x ^ 2 + u ^ 2) =
      (2 / x) * (1 + (u / x) ^ 2)⁻¹ := by
    intro u
    have hden : (0 : ℝ) < x ^ 2 + u ^ 2 := by positivity
    field_simp
  simp only [hfun]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun v : ℝ => (1 + v ^ 2)⁻¹) hx.ne',
    integral_inv_one_add_sq,
    show ((1 / 2 : ℝ)) / x = 1 / (2 * x) by ring,
    show ((-(1 / 2) : ℝ)) / x = -(1 / (2 * x)) by ring,
    Real.arctan_neg, smul_eq_mul]
  field_simp
  ring

/-- The unit-radius integer window mass of the continued Ward response. -/
def xiWardIntegerWindowMass (k : ℤ) : ENNReal :=
  ∫⁻ t in Set.Ioc ((k : ℝ) - 1) ((k : ℝ) + 1),
    ENNReal.ofReal
      ((continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))).re)

/-- **Localized counting**: every strict-right pair deposits mass at least
`4·arctan(1/2)` in the integer window nearest to its reflected height. -/
theorem le_xiWardIntegerWindowMass_round (q : XiRightUpperZeroCopy) :
    ENNReal.ofReal (4 * Real.arctan (1 / 2)) ≤
      xiWardIntegerWindowMass (round (-(xiRightCenteredZero q.1).im)) := by
  set lam := xiRightCenteredZero q.1
  set x : ℝ := lam.re + 1 / 2 with hxdef
  have ha : 0 < lam.re := xiRightCenteredZero_re_pos q.1
  have hahalf : lam.re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx0 : 0 < x := by rw [hxdef]; linarith
  have hx1 : x < 1 := by rw [hxdef]; linarith
  set k : ℤ := round (-lam.im) with hkdef
  have hround : |(-lam.im) - (k : ℝ)| ≤ 1 / 2 := by
    rw [hkdef]
    exact abs_sub_round _
  have habs := abs_le.mp hround
  -- the half-unit window around the reflected height sits inside the window
  have hsub : Set.Ioc (-lam.im - 1 / 2) (-lam.im + 1 / 2) ⊆
      Set.Ioc ((k : ℝ) - 1) ((k : ℝ) + 1) := by
    apply Set.Ioc_subset_Ioc
    · linarith [habs.1, habs.2]
    · linarith [habs.1, habs.2]
  -- pointwise Lorentzian minorant of the full response
  have hpt : ∀ t : ℝ,
      ENNReal.ofReal (2 * x / (x ^ 2 + (t + lam.im) ^ 2)) ≤
        ENNReal.ofReal
          ((continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))).re) := by
    intro t
    apply ENNReal.ofReal_le_ofReal
    have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
      norm_num [Complex.add_re, Complex.mul_re]
    have hle := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
    have heq := re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq q t
    rw [heq] at hle
    have hL2 := lorentzian_nonneg hx0 (t + -lam.im)
    linarith
  -- integral of the minorant over the half-unit window
  have hIoc : ∫ t in Set.Ioc (-lam.im - 1 / 2) (-lam.im + 1 / 2),
      2 * x / (x ^ 2 + (t + lam.im) ^ 2) = 4 * Real.arctan (1 / (2 * x)) := by
    rw [← intervalIntegral.integral_of_le (by linarith : -lam.im - 1 / 2 ≤ -lam.im + 1 / 2)]
    rw [intervalIntegral.integral_comp_add_right
      (fun u : ℝ => 2 * x / (x ^ 2 + u ^ 2)) lam.im,
      show (-lam.im - 1 / 2 + lam.im : ℝ) = -(1 / 2) by ring,
      show (-lam.im + 1 / 2 + lam.im : ℝ) = (1 / 2 : ℝ) by ring]
    exact windowed_lorentzian_integral hx0
  have hlift : ∫⁻ t in Set.Ioc (-lam.im - 1 / 2) (-lam.im + 1 / 2),
      ENNReal.ofReal (2 * x / (x ^ 2 + (t + lam.im) ^ 2)) =
      ENNReal.ofReal (4 * Real.arctan (1 / (2 * x))) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((lorentzian_continuous hx0 lam.im).integrableOn_Ioc)
      (Filter.Eventually.of_forall (fun t => lorentzian_nonneg hx0 (t + lam.im))),
      hIoc]
  -- monotonicity of the arctan charge in the half-width
  have harctan : Real.arctan (1 / 2) ≤ Real.arctan (1 / (2 * x)) := by
    apply Real.arctan_mono
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  calc ENNReal.ofReal (4 * Real.arctan (1 / 2))
      ≤ ENNReal.ofReal (4 * Real.arctan (1 / (2 * x))) := by
        apply ENNReal.ofReal_le_ofReal
        linarith
    _ = ∫⁻ t in Set.Ioc (-lam.im - 1 / 2) (-lam.im + 1 / 2),
        ENNReal.ofReal (2 * x / (x ^ 2 + (t + lam.im) ^ 2)) := hlift.symm
    _ ≤ ∫⁻ t in Set.Ioc ((k : ℝ) - 1) ((k : ℝ) + 1),
        ENNReal.ofReal (2 * x / (x ^ 2 + (t + lam.im) ^ 2)) :=
        MeasureTheory.lintegral_mono'
          (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
    _ ≤ xiWardIntegerWindowMass k :=
        MeasureTheory.lintegral_mono (fun t => hpt t)

/-- **Integer-window mass criterion.**  RH is equivalent to the vanishing of
the countable family of unit-radius integer-window edge masses. -/
theorem riemannHypothesis_iff_forall_xiWardIntegerWindowMass_eq_zero :
    RiemannHypothesis ↔ ∀ k : ℤ, xiWardIntegerWindowMass k = 0 := by
  constructor
  · intro hRH k
    have hpt : ∀ t : ℝ,
        ENNReal.ofReal
          ((continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))).re) = 0 := by
      intro t
      have hw : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
        norm_num [Complex.add_re, Complex.mul_re]
      rw [continuedXiAntiCausalWardResponse_eq_zero_of_riemannHypothesis
        hRH hw]
      simp
    unfold xiWardIntegerWindowMass
    rw [lintegral_congr hpt]
    simp
  · intro h0
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
    have hlow := le_xiWardIntegerWindowMass_round q
    rw [h0 (round (-(xiRightCenteredZero q.1).im)), le_zero_iff,
      ENNReal.ofReal_eq_zero] at hlow
    have harctan : 0 < Real.arctan (1 / 2) := Real.arctan_pos.mpr (by norm_num)
    nlinarith

end

end RHTower
