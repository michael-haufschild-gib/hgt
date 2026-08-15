import GaloisForLFunctions.RHTower.StripPropagatorLineDecay
import GaloisForLFunctions.HTGeometry.PowerTailIntegral

/-!
# The propagated datum on a ray, with the decay in the radius

The squared line mass of `H(·+iσ)c` is a fixed constant times `‖c‖²`, but on a terminal ray it is far
smaller: the weight `(1+|x|)^{-2p}` has ray mass `O(Y^{1-2p}) = O(Y^{-2σ})`, so

`‖H(·+iσ)c‖_{L²(|x|>Y)} ≤ C Y^{-σ}‖c‖`.

That decay is not a refinement for its own sake.  In the one-block estimate the datum accumulated
below the frequency threshold grows like `X_m^{p+1/2}`, and only the ray decay `X_m^{1/2-p}` of the
propagator brings the product back to a *single* power of the threshold — which is what makes the
block weight `e^{max(0,−m)}` rather than `e^{(1+σ)max(0,−m)}`, and hence what makes the block series
converge at all.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The tail mass of the weight on a ray**, with the explicit decay in the radius. -/
theorem lintegral_oneAddAbsWeight_Ioi_le {s Y : ℝ} (hs : 1 < s) (hY : 0 < Y) :
    (∫⁻ x in Ioi Y, oneAddAbsWeight s x) ≤ ENNReal.ofReal (Y ^ (1 - s) / (s - 1)) := by
  have hmaj : ∀ x ∈ Ioi Y, oneAddAbsWeight s x ≤ ENNReal.ofReal (|x| ^ (-s)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hY hx
    rw [oneAddAbsWeight]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_of_pos hx0]
    refine Real.rpow_le_rpow_of_nonpos hx0 ?_ (by linarith)
    linarith
  have hint : IntegrableOn (fun ξ : ℝ => |ξ| ^ (-s)) (Ioi Y) volume :=
    integrableOn_powerTail_Ioi hY hs
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi Y)] fun ξ : ℝ => |ξ| ^ (-s) := by
    filter_upwards with ξ
    positivity
  calc (∫⁻ x in Ioi Y, oneAddAbsWeight s x)
      ≤ ∫⁻ x in Ioi Y, ENNReal.ofReal (|x| ^ (-s)) :=
        setLIntegral_mono' measurableSet_Ioi hmaj
    _ = ENNReal.ofReal (∫ ξ in Ioi Y, |ξ| ^ (-s)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (Y ^ (1 - s) / (s - 1)) := by rw [integral_powerTail_Ioi hY hs]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **The propagated datum decays on the terminal ray.**  Its squared ray mass carries the factor
`Y^{1-2p} = Y^{-2σ}`, which is what cancels the growth of the datum accumulated below the threshold —
the reason the one-block constant sees only one power of the threshold. -/
theorem exists_bound_lintegral_sq_ray_stripPropagator (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ c : X,
      (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
        ≤ ENNReal.ofReal (C * ‖c‖ ^ 2 * Y ^ (-(2 * σ))) := by
  obtain ⟨K, hK, hbound⟩ := exists_bound_stripPropagator_line hT hE hσ0 hσ1
  refine ⟨K ^ 2 / (2 * σ), by positivity, fun Y hY c => ?_⟩
  set p : ℝ := 1 / 2 + σ with hpdef
  have hmaj : ∀ x ∈ Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2
      ≤ ENNReal.ofReal ((K * ‖c‖) ^ 2) * oneAddAbsWeight (2 * p) x := by
    intro x _
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hpt : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
        ≤ (K * ‖c‖) * (1 + |x|) ^ (-p) := by
      calc ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖
          ≤ ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖c‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K * (1 + |x|) ^ (-p)) * ‖c‖ :=
            mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
        _ = (K * ‖c‖) * (1 + |x|) ^ (-p) := by ring
    have hsq : ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ ^ 2
        ≤ (K * ‖c‖) ^ 2 * (1 + |x|) ^ (-(2 * p)) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hpt 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((1 + |x|) ^ (-p)) 2, ← Real.rpow_mul hx0.le]
      congr 2
      push_cast
      ring
    calc ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2
        = ENNReal.ofReal (‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal ((K * ‖c‖) ^ 2 * (1 + |x|) ^ (-(2 * p))) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal ((K * ‖c‖) ^ 2) * oneAddAbsWeight (2 * p) x := by
          rw [oneAddAbsWeight, ← ENNReal.ofReal_mul (by positivity)]
  have hmass := lintegral_oneAddAbsWeight_Ioi_le (s := 2 * p) (by rw [hpdef]; linarith) hY
  have hexp : (1 : ℝ) - 2 * p = -(2 * σ) := by rw [hpdef]; ring
  have hden : 2 * p - 1 = 2 * σ := by rw [hpdef]; ring
  calc (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
      ≤ ∫⁻ x in Ioi Y, ENNReal.ofReal ((K * ‖c‖) ^ 2) * oneAddAbsWeight (2 * p) x :=
        setLIntegral_mono' measurableSet_Ioi hmaj
    _ = ENNReal.ofReal ((K * ‖c‖) ^ 2) * ∫⁻ x in Ioi Y, oneAddAbsWeight (2 * p) x :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((K * ‖c‖) ^ 2) * ENNReal.ofReal (Y ^ (1 - 2 * p) / (2 * p - 1)) :=
        mul_le_mul' le_rfl hmass
    _ = ENNReal.ofReal (K ^ 2 / (2 * σ) * ‖c‖ ^ 2 * Y ^ (-(2 * σ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), hexp, hden]
        congr 1
        field_simp

end GaloisForLFunctions.RHTower
