import GaloisForLFunctions.RHTower.ThetaCuspLogFourthNegative
import GaloisForLFunctions.RHTower.ThetaTiltLogDensity

/-! Two simultaneous source-port zeros have strictly negative free derivatives.
The actual theta slope and its coordinate-weighted version lie strictly above
every extrapolated secant on the nonnegative ray. -/

noncomputable section
open Set

namespace RHTower.ThetaPort

private theorem logThird_neg {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 3 thetaCuspLogSource x < 0 := by
  have hanti : StrictAnti (iteratedDeriv 3 thetaCuspLogSource) := by
    apply strictAnti_of_deriv_neg
    intro y
    rw [(hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 y).deriv]
    exact iteratedDeriv_four_thetaCuspLogSource_neg_all y
  have hz := iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 3) ⟨1, rfl⟩
  simpa only [hz] using hanti hx

private theorem slope_hasDerivAt (x : ℝ) :
    HasDerivAt thetaCuspLogDecaySlope (-iteratedDeriv 2 thetaCuspLogSource x) x :=
  (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).neg

/-- Strict convexity of the literal logarithmic decay slope on the positive ray. -/
theorem strictConvexOn_slope : StrictConvexOn ℝ (Ici 0) thetaCuspLogDecaySlope := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    (fun x _ => (slope_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd : deriv thetaCuspLogDecaySlope = fun x => -iteratedDeriv 2 thetaCuspLogSource x :=
    funext fun x => (slope_hasDerivAt x).deriv
  have hdd : HasDerivAt (fun z => -iteratedDeriv 2 thetaCuspLogSource z)
      (-iteratedDeriv 3 thetaCuspLogSource x) x :=
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x).neg
  change 0 < deriv (deriv thetaCuspLogDecaySlope) x
  rw [hd, hdd.deriv]
  exact neg_pos.mpr (logThird_neg hx')

/-- The coordinate-weighted decay slope. -/
def weightedSlope (x : ℝ) : ℝ := x * thetaCuspLogDecaySlope x

private theorem weightedSlope_hasDerivAt (x : ℝ) :
    HasDerivAt weightedSlope
      (-iteratedDeriv 1 thetaCuspLogSource x - x * iteratedDeriv 2 thetaCuspLogSource x) x := by
  convert! (hasDerivAt_id x).mul (slope_hasDerivAt x) using 1
  simp only [id_eq, thetaCuspLogDecaySlope]
  ring

/-- Strict convexity also holds for the coordinate-weighted literal slope. -/
theorem strictConvexOn_weightedSlope : StrictConvexOn ℝ (Ici 0) weightedSlope := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    (fun x _ => (weightedSlope_hasDerivAt x).continuousAt.continuousWithinAt)
  intro x hx
  have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd : deriv weightedSlope = fun x =>
      -iteratedDeriv 1 thetaCuspLogSource x - x * iteratedDeriv 2 thetaCuspLogSource x :=
    funext fun x => (weightedSlope_hasDerivAt x).deriv
  have hdd : HasDerivAt (fun z => -iteratedDeriv 1 thetaCuspLogSource z -
      z * iteratedDeriv 2 thetaCuspLogSource z)
      (-2 * iteratedDeriv 2 thetaCuspLogSource x - x * iteratedDeriv 3 thetaCuspLogSource x) x := by
    convert! ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).neg).sub
      ((hasDerivAt_id x).mul (hasDerivAt_iteratedDeriv_thetaCuspLogSource 2 x)) using 1
    dsimp
    ring
  change 0 < deriv (deriv weightedSlope) x
  rw [hd, hdd.deriv]
  have h2 := iteratedDeriv_two_thetaCuspLogSource_neg x
  have h3 := mul_neg_of_pos_of_neg hx' (logThird_neg hx')
  linarith

private theorem extrapolation_defect_neg {f : ℝ → ℝ} (hf : StrictConvexOn ℝ (Ici 0) f)
    {x₁ x₂ y : ℝ} (hx : 0 ≤ x₁) (h12 : x₁ < x₂) (h2y : x₂ < y) :
    ((x₂-y)/(x₂-x₁))*f x₁ + ((y-x₁)/(x₂-x₁))*f x₂ - f y < 0 := by
  have hs := hf.slope_strict_mono_adjacent hx
    (show y ∈ Ici 0 from (hx.trans h12.le).trans h2y.le) h12 h2y
  have hc := (div_lt_div_iff₀ (sub_pos.mpr h12) (sub_pos.mpr h2y)).mp hs
  have he : ((x₂-y)/(x₂-x₁))*f x₁ + ((y-x₁)/(x₂-x₁))*f x₂ - f y =
      ((x₂-y)*f x₁+(y-x₁)*f x₂-(x₂-x₁)*f y)/(x₂-x₁) := by
    field_simp [sub_ne_zero.mpr h12.ne']
  rw [he]
  exact div_neg_of_neg_of_pos (by nlinarith only [hc]) (sub_pos.mpr h12)

/-- Both literal source slopes have strictly negative two-node extrapolation defects. -/
theorem two_node_extrapolation_defects_neg {x₁ x₂ y : ℝ}
    (hx : 0 ≤ x₁) (h12 : x₁ < x₂) (h2y : x₂ < y) :
    (((x₂-y)/(x₂-x₁))*thetaCuspLogDecaySlope x₁ +
      ((y-x₁)/(x₂-x₁))*thetaCuspLogDecaySlope x₂ - thetaCuspLogDecaySlope y < 0) ∧
    (((x₂-y)/(x₂-x₁))*weightedSlope x₁ +
      ((y-x₁)/(x₂-x₁))*weightedSlope x₂ - weightedSlope y < 0) :=
  ⟨extrapolation_defect_neg strictConvexOn_slope hx h12 h2y,
    extrapolation_defect_neg strictConvexOn_weightedSlope hx h12 h2y⟩

private theorem source_deriv_eq (z : ℝ) :
    deriv thetaCuspFullSource z = -thetaCuspLogDecaySlope z * thetaCuspFullSource z := by
  have h : iteratedDeriv 1 thetaCuspLogSource z =
      deriv thetaCuspFullSource z / thetaCuspFullSource z := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource z).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all z).ne']

/-- At a simultaneous zero of the two source ports, both free source derivatives
are negative. The coefficients need not satisfy additional sign assumptions. -/
theorem simultaneous_port_free_derivatives_neg {x₁ x₂ y c₁ c₂ : ℝ}
    (hx : 0 ≤ x₁) (h12 : x₁ < x₂) (h2y : x₂ < y)
    (hA : thetaCuspFullSource y - c₁*thetaCuspFullSource x₁ - c₂*thetaCuspFullSource x₂ = 0)
    (hB : y*thetaCuspFullSource y - c₁*x₁*thetaCuspFullSource x₁ -
      c₂*x₂*thetaCuspFullSource x₂ = 0) :
    (deriv thetaCuspFullSource y - c₁*deriv thetaCuspFullSource x₁ -
      c₂*deriv thetaCuspFullSource x₂ < 0) ∧
    (y*deriv thetaCuspFullSource y - c₁*x₁*deriv thetaCuspFullSource x₁ -
      c₂*x₂*deriv thetaCuspFullSource x₂ < 0) := by
  let a := (x₂-y)/(x₂-x₁)
  let b := (y-x₁)/(x₂-x₁)
  have ha : c₁*thetaCuspFullSource x₁ = a*thetaCuspFullSource y := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (sub_ne_zero.mpr h12.ne')).mpr
    linear_combination hB - x₂*hA
  have hb : c₂*thetaCuspFullSource x₂ = b*thetaCuspFullSource y := by
    dsimp [b]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (sub_ne_zero.mpr h12.ne')).mpr
    linear_combination x₁*hA - hB
  obtain ⟨hp, hq⟩ := two_node_extrapolation_defects_neg hx h12 h2y
  have hp' := mul_neg_of_pos_of_neg (thetaCuspFullSource_pos_all y) hp
  have hq' := mul_neg_of_pos_of_neg (thetaCuspFullSource_pos_all y) hq
  simp only [source_deriv_eq]
  constructor
  · have he : -thetaCuspLogDecaySlope y*thetaCuspFullSource y -
        c₁*(-thetaCuspLogDecaySlope x₁*thetaCuspFullSource x₁) -
        c₂*(-thetaCuspLogDecaySlope x₂*thetaCuspFullSource x₂) =
        thetaCuspFullSource y*(a*thetaCuspLogDecaySlope x₁ +
          b*thetaCuspLogDecaySlope x₂-thetaCuspLogDecaySlope y) := by
      linear_combination thetaCuspLogDecaySlope x₁*ha + thetaCuspLogDecaySlope x₂*hb
    rw [he]
    exact hp'
  · have he : y*(-thetaCuspLogDecaySlope y*thetaCuspFullSource y) -
        c₁*x₁*(-thetaCuspLogDecaySlope x₁*thetaCuspFullSource x₁) -
        c₂*x₂*(-thetaCuspLogDecaySlope x₂*thetaCuspFullSource x₂) =
        thetaCuspFullSource y*(a*weightedSlope x₁+b*weightedSlope x₂-weightedSlope y) := by
      dsimp only [weightedSlope]
      linear_combination (x₁*thetaCuspLogDecaySlope x₁)*ha + (x₂*thetaCuspLogDecaySlope x₂)*hb
    rw [he]
    exact hq'

end RHTower.ThetaPort
