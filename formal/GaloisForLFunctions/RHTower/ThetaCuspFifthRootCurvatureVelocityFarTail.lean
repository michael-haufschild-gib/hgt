import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5SeamFarTail
import GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodBregmanCone

/-!
# Literal modular-center C5 velocity at both open ends

The exact first-atom likelihood factorization gives normalized reflected log jets
`q₁/S → 4`, `q₂/S → 8`, and `q₃/S → 16` on the physical far tail.  The reflected action radius
diverges.  Dividing the literal fifth-root-curvature action velocity by `r * t² * S³` therefore
kills every term except `5 * (q₁/S)³`, whose limit is `320`.  Thus literal center velocity is
strictly positive on a cofinal tail.

At the modular seam, the exact eighth C5 jet is positive.  Descending its derivative tower proves
literal velocity is also positive on a punctured right neighborhood.  Together these statements
reduce global center-velocity positivity exactly to one compact annulus, with qualitative and
uncomputed endpoints.

RH chain: compact center-velocity premise -> modular-center C5 -> fixed-action and higher-packet
transport -> no escape -> CLG/TTF or Weil polarization positivity -> RH.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

private theorem thetaCuspC5VelocityFarTail_reflectionScale_ne_zero (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
  unfold thetaCuspSingleAtomReflectionScale
  positivity

private theorem thetaCuspC5VelocityFarTail_natCast_le_coe_enatTop (n : ℕ) :
    (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.mpr (by exact_mod_cast le_top)

theorem thetaCuspC5VelocityFarTail_superpotential_div_scale_tendsto_one :
    Tendsto (fun x : ℝ =>
      thetaCuspBornWittenSuperpotential 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 1) := by
  have hs := thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hc : Tendsto (fun x : ℝ =>
      (thetaCuspLikelihoodCoordinate x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp thetaCuspC5FarTail_coordinate_tendsto_atTop
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h := (hone.sub (hs.const_mul (5 / 4 : ℝ))).sub hc
  have h' : Tendsto (fun x : ℝ =>
      1 - (5 / 4 : ℝ) *
          (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ -
        (thetaCuspLikelihoodCoordinate x)⁻¹) atTop (nhds 1) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hs0 := thetaCuspC5VelocityFarTail_reflectionScale_ne_zero x
  have hcpos := thetaCuspLikelihoodCoordinate_pos hx
  have hc0 := hcpos.ne'
  have hsc : thetaCuspLikelihoodCoordinate x + 3 / 2 ≠ 0 := by
    positivity
  symm
  unfold thetaCuspBornWittenSuperpotential thetaCuspMorseSuperpotential
  rw [thetaCuspBornWittenWeight_eq,
    thetaCuspC5FarTail_morseScale_one_eq_reflectionScale,
    thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hs0, hc0, hsc]
  ring

theorem tendsto_thetaCuspReflectedLogJetOne_zero_div_scale_four :
    Tendsto (fun x : ℝ =>
      thetaCuspReflectedLogJetOne 0 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 4) := by
  have hW :=
    thetaCuspC5VelocityFarTail_superpotential_div_scale_tendsto_one.const_mul 4
  have hm0 := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 0
  have hm : Tendsto (fun x : ℝ =>
      thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 0) := by
    simpa using hm0
  have h := hW.add (hm.const_mul 4)
  have h' : Tendsto (fun x : ℝ =>
      4 * (thetaCuspBornWittenSuperpotential 1 x /
        thetaCuspSingleAtomReflectionScale 1 x) +
      4 * thetaCuspLikelihoodMean (thetaCuspLikelihoodCoordinate x))
      atTop (nhds 4) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hs0 := thetaCuspC5VelocityFarTail_reflectionScale_ne_zero x
  symm
  rw [thetaCuspReflectedLogJetOne_zero_eq_likelihood hx0]
  unfold thetaCuspFirstAtomLogJetOne
    thetaCuspLikelihoodSourceLogPartitionJetOne
  field_simp [hs0]
  ring

theorem tendsto_thetaCuspReflectedLogJetTwo_zero_div_scale_eight :
    Tendsto (fun x : ℝ =>
      thetaCuspReflectedLogJetTwo 0 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 8) := by
  have h := thetaCuspC5FarTail_neg_logJetTwo_div_scale_tendsto_four.const_mul 2
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [show thetaCuspReflectedLogJetTwo 0 x =
      -2 * iteratedDeriv 2 thetaCuspLogSource x by
    unfold thetaCuspReflectedLogJetTwo thetaCuspLogCurvature
    rw [zero_add, zero_sub, iteratedDeriv_thetaCuspLogSource_neg]
    norm_num
    ring]
  ring

theorem tendsto_thetaCuspReflectedLogJetThree_zero_div_scale_sixteen :
    Tendsto (fun x : ℝ =>
      thetaCuspReflectedLogJetThree 0 x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 16) := by
  have h := thetaCuspC5FarTail_neg_logJetThree_div_scale_tendsto_eight.const_mul 2
  norm_num at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [show thetaCuspReflectedLogJetThree 0 x =
      -2 * iteratedDeriv 3 thetaCuspLogSource x by
    unfold thetaCuspReflectedLogJetThree thetaCuspLogCurvatureJet
    rw [zero_add, zero_sub, iteratedDeriv_thetaCuspLogSource_neg]
    norm_num
    ring]
  ring

theorem tendsto_thetaCuspCenterFifthRootVelocityActionRadius_atTop :
    Tendsto (fun x : ℝ =>
      Real.exp (thetaCuspReflectedLogAction 0 x) - 1) atTop atTop := by
  have haction : Tendsto (thetaCuspReflectedLogAction 0) atTop atTop := by
    have hbound : (fun x : ℝ => x) ≤ᶠ[atTop]
        thetaCuspReflectedLogAction 0 := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have h := nineteen_mul_sq_sub_self_lt_thetaCuspReflectedLogAction_zero
        (by linarith : 0 < x)
      have hpoly : x ≤ 19 * x ^ 2 - x := by nlinarith
      exact hpoly.trans h.le
    exact tendsto_atTop_mono' atTop hbound tendsto_id
  have hexp := Real.tendsto_exp_atTop.comp haction
  simpa [sub_eq_add_neg] using
    tendsto_atTop_add_const_right atTop (-1 : ℝ) hexp

theorem tendsto_thetaCuspCenterFifthRootVelocityActionRadius_inv_zero :
    Tendsto (fun x : ℝ =>
      (Real.exp (thetaCuspReflectedLogAction 0 x) - 1)⁻¹)
      atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    tendsto_thetaCuspCenterFifthRootVelocityActionRadius_atTop

theorem tendsto_thetaCuspCenterFifthRootVelocityActionCore_normalized :
    Tendsto (fun x : ℝ =>
      thetaCuspReflectedActionFifthRootVelocityCore
          (Real.exp (thetaCuspReflectedLogAction 0 x) - 1) x
          (thetaCuspReflectedLogJetOne 0 x)
          (thetaCuspReflectedLogJetTwo 0 x)
          (thetaCuspReflectedLogJetThree 0 x) /
        ((Real.exp (thetaCuspReflectedLogAction 0 x) - 1) * x ^ 2 *
          thetaCuspSingleAtomReflectionScale 1 x ^ 3))
      atTop (nhds 320) := by
  let A : ℝ → ℝ := fun x =>
    thetaCuspReflectedLogJetOne 0 x /
      thetaCuspSingleAtomReflectionScale 1 x
  let B : ℝ → ℝ := fun x =>
    thetaCuspReflectedLogJetTwo 0 x /
      thetaCuspSingleAtomReflectionScale 1 x
  let C : ℝ → ℝ := fun x =>
    thetaCuspReflectedLogJetThree 0 x /
      thetaCuspSingleAtomReflectionScale 1 x
  let X : ℝ → ℝ := fun x => x⁻¹
  let S : ℝ → ℝ := fun x =>
    (thetaCuspSingleAtomReflectionScale 1 x)⁻¹
  let R : ℝ → ℝ := fun x =>
    (Real.exp (thetaCuspReflectedLogAction 0 x) - 1)⁻¹
  have hA : Tendsto A atTop (nhds 4) := by
    simpa only [A] using tendsto_thetaCuspReflectedLogJetOne_zero_div_scale_four
  have hB : Tendsto B atTop (nhds 8) := by
    simpa only [B] using tendsto_thetaCuspReflectedLogJetTwo_zero_div_scale_eight
  have hC : Tendsto C atTop (nhds 16) := by
    simpa only [C] using tendsto_thetaCuspReflectedLogJetThree_zero_div_scale_sixteen
  have hX : Tendsto X atTop (nhds 0) := by
    simpa only [X] using (tendsto_inv_atTop_zero :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  have hS : Tendsto S atTop (nhds 0) := by
    simpa only [S] using thetaCuspC5FarTail_reflectionScale_inv_tendsto_zero
  have hR : Tendsto R atTop (nhds 0) := by
    simpa only [R] using
      tendsto_thetaCuspCenterFifthRootVelocityActionRadius_inv_zero
  have h1 := (((hA.const_mul 39).mul (hX.pow 2)).mul (hS.pow 2))
  have h2 := (hB.mul hX).mul (hS.pow 2)
  have h3 := (((hA.pow 2).mul hX).mul hS).const_mul (-1)
  have h4 := (hC.mul (hS.pow 2)).const_mul 5
  have h5 := ((hA.mul hB).mul hS).const_mul (-15)
  have h6 := (hA.pow 3).const_mul 5
  have h7 := ((((hR.mul hX).mul (hA.pow 2)).mul hS).const_mul (-17))
  have h8 := ((hR.mul ((hA.mul hB).mul hS)).const_mul (-3))
  have h9 := (hR.mul (hA.pow 3)).const_mul 3
  have hsum := ((((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9)
  have hnorm : Tendsto (fun x =>
      39 * A x * X x ^ 2 * S x ^ 2 +
      B x * X x * S x ^ 2 - A x ^ 2 * X x * S x +
      5 * C x * S x ^ 2 - 15 * A x * B x * S x + 5 * A x ^ 3 -
      17 * R x * X x * A x ^ 2 * S x -
      3 * R x * A x * B x * S x + 3 * R x * A x ^ 3)
      atTop (nhds 320) := by
    convert hsum using 1
    · funext x
      ring
    · norm_num
  refine hnorm.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hspos : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hrpos : 0 < Real.exp (thetaCuspReflectedLogAction 0 x) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos hx0)
  simp only [A, B, C, X, S, R]
  field_simp [hxne, hspos.ne', hrpos.ne']
  unfold thetaCuspReflectedActionFifthRootVelocityCore
  ring

theorem eventually_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos :
    ∀ᶠ x : ℝ in atTop,
      0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 x := by
  have hnormalized : ∀ᶠ x : ℝ in atTop,
      0 < thetaCuspReflectedActionFifthRootVelocityCore
          (Real.exp (thetaCuspReflectedLogAction 0 x) - 1) x
          (thetaCuspReflectedLogJetOne 0 x)
          (thetaCuspReflectedLogJetTwo 0 x)
          (thetaCuspReflectedLogJetThree 0 x) /
        ((Real.exp (thetaCuspReflectedLogAction 0 x) - 1) * x ^ 2 *
          thetaCuspSingleAtomReflectionScale 1 x ^ 3) :=
    (tendsto_order.1
      tendsto_thetaCuspCenterFifthRootVelocityActionCore_normalized).1 0 (by norm_num)
  filter_upwards [hnormalized, eventually_ge_atTop (1 : ℝ)] with x hnorm hx
  have hx0 : 0 < x := by linarith
  have hrpos : 0 < Real.exp (thetaCuspReflectedLogAction 0 x) - 1 := by
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (thetaCuspReflectedLogAction_pos hx0)
  have hspos : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have hden : 0 < (Real.exp (thetaCuspReflectedLogAction 0 x) - 1) * x ^ 2 *
      thetaCuspSingleAtomReflectionScale 1 x ^ 3 := by positivity
  have hcore := mul_pos hnorm hden
  rw [div_mul_cancel₀ _ hden.ne'] at hcore
  rw [thetaCuspReflectedSourceFifthRootCurvatureVelocity_pos_iff_actionCore]
  exact hcore

theorem exists_forall_ge_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 x := by
  exact eventually_atTop.1
    eventually_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos

theorem exists_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_right :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : ℝ, 0 < x → x < delta →
      0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 x := by
  let f : ℝ → ℝ := thetaCuspReflectedSourceProduct 0
  let W : ℝ → ℝ := HilbertMetric.fifthRootDividedDropCurvatureNumerator f
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f :=
    contDiff_thetaCuspReflectedSourceProduct 0
  have heven : Function.Even f := thetaCuspReflectedSourceProduct_even 0
  have hF1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv 1 f) :=
    HTGeometry.contDiff_top_iteratedDeriv_real f hf 1
  have hF2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv 2 f) :=
    HTGeometry.contDiff_top_iteratedDeriv_real f hf 2
  have hWtop : ContDiff ℝ (↑(⊤ : ℕ∞)) W := by
    dsimp only [W]
    unfold HilbertMetric.fifthRootDividedDropCurvatureNumerator
    fun_prop
  have hW : ContDiff ℝ 8 W :=
    hWtop.of_le (thetaCuspC5VelocityFarTail_natCast_le_coe_enatTop 8)
  have hchain : ∀ n : ℕ, n < 8 → ∀ x : ℝ,
      HasDerivAt (iteratedDeriv n W) (iteratedDeriv (n + 1) W x) x := by
    intro n hn x
    have hd := hW.differentiable_iteratedDeriv n (by exact_mod_cast hn)
    simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt
  have hzero : ∀ n : ℕ, n < 8 → iteratedDeriv n W 0 = 0 := by
    intro n hn
    exact HilbertMetric.iteratedDeriv_fifthRootDividedDropCurvatureNumerator_zero_of_lt_eight
      hf heven hn
  have hHankel : 0 <
      iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
        iteratedDeriv 4 f 0 ^ 2 := by
    dsimp only [f]
    rw [thetaCuspReflectedSourceProduct_secondSixthHankel_zero]
    exact thetaCuspFullSourceReflectionSecondSixthCurvature_pos 0
  have height : 0 < iteratedDeriv 8 W 0 := by
    dsimp only [W]
    rw [HilbertMetric.iteratedDeriv_eight_fifthRootDividedDropCurvatureNumerator_zero
      hf heven]
    positivity
  have hW8cont : Continuous (iteratedDeriv 8 W) :=
    hW.continuous_iteratedDeriv 8 (by norm_num)
  have hopen : IsOpen {x : ℝ | 0 < iteratedDeriv 8 W x} :=
    isOpen_lt continuous_const hW8cont
  have hn : {x : ℝ | 0 < iteratedDeriv 8 W x} ∈ nhds 0 :=
    hopen.mem_nhds height
  rcases Metric.mem_nhds_iff.mp hn with ⟨d, hd, hball⟩
  let delta := d / 2
  have hdelta : 0 < delta := div_pos hd (by norm_num)
  have h8pos : ∀ x ∈ interior (Icc (0 : ℝ) delta),
      0 < iteratedDeriv 8 W x := by
    intro x hx
    have hxIoo : x ∈ Ioo (0 : ℝ) delta := by
      simpa [interior_Icc, hdelta.ne'] using hx
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg hxIoo.1.le]
    exact lt_trans hxIoo.2 (by dsimp only [delta]; linarith)
  have hW7cont : Continuous (iteratedDeriv 7 W) :=
    hW.continuous_iteratedDeriv 7 (by norm_num)
  have hW7strict : StrictMonoOn (iteratedDeriv 7 W) (Icc (0 : ℝ) delta) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 delta)
      hW7cont.continuousOn
      (fun x _ => (hchain 7 (by norm_num) x).hasDerivWithinAt) h8pos
  have h7pos : ∀ x : ℝ, 0 < x → x < delta →
      0 < iteratedDeriv 7 W x := by
    intro x hx hxdelta
    have hlt := hW7strict ⟨le_rfl, hdelta.le⟩
      ⟨hx.le, hxdelta.le⟩ hx
    simpa [hzero 7 (by norm_num)] using hlt
  have h5pos : ∀ x : ℝ, 0 < x → x < delta →
      0 < iteratedDeriv 5 W x := by
    intro x hx hxdelta
    apply HilbertMetric.pos_right_of_secondJet_posOn
      (hchain 5 (by norm_num)) (hchain 6 (by norm_num))
      (hzero 5 (by norm_num)) (hzero 6 (by norm_num)) hdelta
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) delta := by
        simpa [interior_Icc, hdelta.ne'] using hs
      exact h7pos s hs'.1 hs'.2
    · exact hx
    · exact hxdelta
  have h3pos : ∀ x : ℝ, 0 < x → x < delta →
      0 < iteratedDeriv 3 W x := by
    intro x hx hxdelta
    apply HilbertMetric.pos_right_of_secondJet_posOn
      (hchain 3 (by norm_num)) (hchain 4 (by norm_num))
      (hzero 3 (by norm_num)) (hzero 4 (by norm_num)) hdelta
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) delta := by
        simpa [interior_Icc, hdelta.ne'] using hs
      exact h5pos s hs'.1 hs'.2
    · exact hx
    · exact hxdelta
  have h1pos : ∀ x : ℝ, 0 < x → x < delta →
      0 < iteratedDeriv 1 W x := by
    intro x hx hxdelta
    apply HilbertMetric.pos_right_of_secondJet_posOn
      (hchain 1 (by norm_num)) (hchain 2 (by norm_num))
      (hzero 1 (by norm_num)) (hzero 2 (by norm_num)) hdelta
    · intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) delta := by
        simpa [interior_Icc, hdelta.ne'] using hs
      exact h3pos s hs'.1 hs'.2
    · exact hx
    · exact hxdelta
  refine ⟨delta, hdelta, fun x hx hxdelta => ?_⟩
  have hNW : thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 = W := by
    funext t
    exact thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_generic 0 t
  have hderiv :=
    (hasDerivAt_thetaCuspReflectedSourceFifthRootCurvatureNumerator 0 x).deriv
  rw [hNW] at hderiv
  rw [← hderiv]
  simpa only [iteratedDeriv_one] using h1pos x hx hxdelta

/-- Exact compact-annulus reduction of the global literal center-velocity premise. -/
theorem exists_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_compactCore :
    ∃ delta T : ℝ, 0 < delta ∧ delta ≤ T ∧
      ((∀ x : ℝ, 0 < x →
          0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 x) ↔
        ∀ x : ℝ, x ∈ Icc delta T →
          0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 x) := by
  rcases exists_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_right with
    ⟨delta0, hdelta0, hseam⟩
  rcases exists_forall_ge_thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos with
    ⟨T0, htail0⟩
  let T := max 1 T0
  have htail : ∀ x : ℝ, T ≤ x →
      0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 x := by
    intro x hx
    exact htail0 x ((le_max_right 1 T0).trans hx)
  let delta := min delta0 T
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left 1 T0)
  have hdelta : 0 < delta := lt_min hdelta0 hTpos
  refine ⟨delta, T, hdelta, min_le_right _ _, ?_⟩
  constructor
  · intro h x hxI
    exact h x (lt_of_lt_of_le hdelta hxI.1)
  · intro h x hx
    by_cases hxdelta : x < delta
    · exact hseam x hx (lt_of_lt_of_le hxdelta (min_le_left _ _))
    · by_cases hTx : T ≤ x
      · exact htail x hTx
      · exact h x ⟨le_of_not_gt hxdelta, le_of_not_ge hTx⟩

end

end RHTower
