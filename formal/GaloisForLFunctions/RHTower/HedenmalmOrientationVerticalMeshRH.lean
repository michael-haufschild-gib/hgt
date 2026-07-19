import GaloisForLFunctions.RHTower.HedenmalmOrientationUpperSingularityCeilingRH

/-!
# A reciprocal vertical value mesh forces the Hedenmalm singularity ceiling

At a forced boundary singularity `b_rho`, the exact canonical orientation residue implies

`epsilon_n * Re Q_a (b_rho + i epsilon_n) -> -m_rho`,

where `epsilon_n = 1/(n+1)` and `m_rho` is the positive Xi multiplicity.  Consequently, an
eventual finite lower bound for the unscaled real values on every such upper vertical mesh rules
out all forced singularities above `Im b = a`.  The positive translation-boundary criterion then
proves RH.

This is a sampled-value bridge.  No lower bound is proved here from the prime--Gamma source.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- The canonical reciprocal mesh approaching a point from above in frequency space. -/
def orientationVerticalMeshEpsilon (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)⁻¹)

theorem orientationVerticalMeshEpsilon_pos (n : ℕ) :
    0 < orientationVerticalMeshEpsilon n := by
  unfold orientationVerticalMeshEpsilon
  positivity

theorem orientationVerticalMeshEpsilon_tendsto_zero :
    Tendsto orientationVerticalMeshEpsilon atTop (nhds 0) := by
  unfold orientationVerticalMeshEpsilon
  exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
    (Filter.tendsto_add_atTop_nat 1)

/-- The exact residue at a forced boundary singularity becomes a negative scaled real-value limit
along the reciprocal vertical mesh. -/
theorem tendsto_orientationVerticalMeshEpsilon_mul_re_canonicalOrientation_of_leftBoundary
    {a : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary (2 * a)) :
    Tendsto
      (fun n : ℕ => orientationVerticalMeshEpsilon n *
        (xiCanonicalHorizontalOrientationMultiplier a
          (xiOrientationFrequencyOfPoint a ρ +
            (orientationVerticalMeshEpsilon n : ℂ) * I)).re)
      atTop
      (nhds (-((analyticOrderAt xi ρ).toNat : ℝ))) := by
  let x : ℕ → ℂ := fun n => (-(orientationVerticalMeshEpsilon n) : ℝ)
  have hx : Tendsto x atTop (nhds 0) := by
    have hneg : Tendsto (fun n : ℕ => -orientationVerticalMeshEpsilon n)
        atTop (nhds 0) := by
      simpa using orientationVerticalMeshEpsilon_tendsto_zero.neg
    exact (Complex.continuous_ofReal.tendsto 0).comp hneg
  have hxWithin : Tendsto x atTop (nhdsWithin 0 ({0}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hx, Eventually.of_forall (fun n => ?_)⟩
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ofReal_ne_zero.mpr
      (neg_ne_zero.mpr (orientationVerticalMeshEpsilon_pos n).ne')
  have hlimit : Tendsto
      (fun n => xiCanonicalOrientationBoundaryResidueGerm a ρ (x n))
      atTop
      (nhds (xiCanonicalOrientationBoundaryResidueGerm a ρ 0)) :=
    (analyticAt_xiCanonicalOrientationBoundaryResidueGerm hρ).continuousAt.tendsto.comp hx
  have heq :=
    (xiCanonicalOrientationBoundaryResidueGerm_eventuallyEq a ρ).comp_tendsto hxWithin
  have hproduct : Tendsto
      (fun n =>
        (xiOrientationFrequencyOfPoint a (ρ + x n) -
          xiOrientationFrequencyOfPoint a ρ) *
            xiCanonicalHorizontalOrientationMultiplier a
              (xiOrientationFrequencyOfPoint a (ρ + x n)))
      atTop
      (nhds (xiCanonicalOrientationBoundaryResidueGerm a ρ 0)) :=
    hlimit.congr' heq
  have him := Complex.continuous_im.continuousAt.tendsto.comp hproduct
  have him' : Tendsto
      (fun n => ((xiOrientationFrequencyOfPoint a (ρ + x n) -
          xiOrientationFrequencyOfPoint a ρ) *
            xiCanonicalHorizontalOrientationMultiplier a
              (xiOrientationFrequencyOfPoint a (ρ + x n))).im)
      atTop (nhds (-((analyticOrderAt xi ρ).toNat : ℝ))) := by
    simpa [Function.comp_apply,
      xiCanonicalOrientationBoundaryResidueGerm_zero] using him
  have hfun :
      (fun n : ℕ => orientationVerticalMeshEpsilon n *
        (xiCanonicalHorizontalOrientationMultiplier a
          (xiOrientationFrequencyOfPoint a ρ +
            (orientationVerticalMeshEpsilon n : ℂ) * I)).re) =
      (fun n => ((xiOrientationFrequencyOfPoint a (ρ + x n) -
          xiOrientationFrequencyOfPoint a ρ) *
            xiCanonicalHorizontalOrientationMultiplier a
              (xiOrientationFrequencyOfPoint a (ρ + x n))).im) := by
    funext n
    have hpoint : xiOrientationFrequencyOfPoint a (ρ + x n) =
        xiOrientationFrequencyOfPoint a ρ +
          (orientationVerticalMeshEpsilon n : ℂ) * I := by
      dsimp only [x]
      unfold xiOrientationFrequencyOfPoint
      push_cast
      ring
    have hdiff : xiOrientationFrequencyOfPoint a (ρ + x n) -
        xiOrientationFrequencyOfPoint a ρ =
          (orientationVerticalMeshEpsilon n : ℂ) * I := by
      rw [hpoint]
      ring
    rw [hdiff, hpoint]
    simp [Complex.mul_im]
  rw [hfun]
  exact him'

/-- At every center above `Im b = a`, the real orientation values on the canonical reciprocal
vertical mesh are eventually bounded below by some center-dependent finite constant. -/
def XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow (a : ℝ) : Prop :=
  ∀ b : ℂ, a < b.im → ∃ L : ℝ, ∀ᶠ n : ℕ in atTop,
    L ≤ (xiCanonicalHorizontalOrientationMultiplier a
      (b + (orientationVerticalMeshEpsilon n : ℂ) * I)).re

/-- The vertical-mesh lower bound excludes a forced boundary singularity above `Im b = a`, so
every left `2a`-boundary zero lies on or right of the critical line. -/
theorem xiLeftShiftBoundary_re_ge_half_of_orientationUpperVerticalMeshLocallyBoundedBelow
    {a : ℝ} (hmesh : XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow a)
    {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary (2 * a)) :
    (1 / 2 : ℝ) ≤ ρ.re := by
  by_contra hre
  have hrelt : ρ.re < (1 / 2 : ℝ) := lt_of_not_ge hre
  let b : ℂ := xiOrientationFrequencyOfPoint a ρ
  have hbUpper : a < b.im := by
    dsimp only [b]
    rw [xiOrientationFrequencyOfPoint_im]
    linarith
  obtain ⟨L, hL⟩ := hmesh b hbUpper
  let m : ℕ := (analyticOrderAt xi ρ).toNat
  have hmPos : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hρ.1)
  have hmRealPos : 0 < (m : ℝ) := by exact_mod_cast hmPos
  have hscaled :=
    tendsto_orientationVerticalMeshEpsilon_mul_re_canonicalOrientation_of_leftBoundary hρ
  have hevUpper : ∀ᶠ n : ℕ in atTop,
      orientationVerticalMeshEpsilon n *
          (xiCanonicalHorizontalOrientationMultiplier a
            (b + (orientationVerticalMeshEpsilon n : ℂ) * I)).re <
        -(m : ℝ) / 2 := by
    have htarget : -(m : ℝ) < -(m : ℝ) / 2 := by linarith
    simpa [b, m] using hscaled.eventually (eventually_lt_nhds htarget)
  have hscaledL : Tendsto
      (fun n : ℕ => orientationVerticalMeshEpsilon n * L)
      atTop (nhds 0) := by
    simpa using orientationVerticalMeshEpsilon_tendsto_zero.mul_const L
  have hevLower : ∀ᶠ n : ℕ in atTop,
      -(m : ℝ) / 2 < orientationVerticalMeshEpsilon n * L :=
    hscaledL.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨n, hnBound, hnUpper, hnLower⟩ :=
    (hL.and (hevUpper.and hevLower)).exists
  have hmul := mul_le_mul_of_nonneg_left hnBound
    (le_of_lt (orientationVerticalMeshEpsilon_pos n))
  linarith

/-- **Vertical sampled-value criterion for RH.**  Eventual lower boundedness on all canonical
upper reciprocal meshes at one positive aperture forces RH. -/
theorem riemannHypothesis_of_orientationUpperVerticalMeshLocallyBoundedBelow
    {a : ℝ} (ha : 0 < a)
    (hmesh : XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow a) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiLeftShiftBoundary_re_ge_half (h := 2 * a)
    (by linarith)
  intro ρ hρ
  exact xiLeftShiftBoundary_re_ge_half_of_orientationUpperVerticalMeshLocallyBoundedBelow
    hmesh hρ

/-- Under RH, the canonical orientation multiplier is analytic at every mesh center strictly above
the aperture line.  Its values on the reciprocal vertical mesh therefore converge and are
eventually bounded below. -/
theorem orientationUpperVerticalMeshLocallyBoundedBelow_of_riemannHypothesis
    {a : ℝ} (ha : 0 < a) (hRH : RiemannHypothesis) :
    XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow a := by
  intro b hb
  have hanalytic : AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a) b :=
    canonicalOrientation_analyticAt_of_riemannHypothesis ha hRH hb
  have hepsilonCast : Tendsto
      (fun n : ℕ => (orientationVerticalMeshEpsilon n : ℂ)) atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      orientationVerticalMeshEpsilon_tendsto_zero
  have hmesh : Tendsto
      (fun n : ℕ => b + (orientationVerticalMeshEpsilon n : ℂ) * I)
      atTop (nhds b) := by
    simpa using tendsto_const_nhds.add (hepsilonCast.mul_const I)
  have hvalues : Tendsto
      (fun n : ℕ => xiCanonicalHorizontalOrientationMultiplier a
        (b + (orientationVerticalMeshEpsilon n : ℂ) * I))
      atTop (nhds (xiCanonicalHorizontalOrientationMultiplier a b)) :=
    hanalytic.continuousAt.tendsto.comp hmesh
  have hre : Tendsto
      (fun n : ℕ => (xiCanonicalHorizontalOrientationMultiplier a
        (b + (orientationVerticalMeshEpsilon n : ℂ) * I)).re)
      atTop (nhds (xiCanonicalHorizontalOrientationMultiplier a b).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hvalues
  refine ⟨(xiCanonicalHorizontalOrientationMultiplier a b).re - 1, ?_⟩
  have hlt : (xiCanonicalHorizontalOrientationMultiplier a b).re - 1 <
      (xiCanonicalHorizontalOrientationMultiplier a b).re := by linarith
  filter_upwards [hre.eventually (eventually_gt_nhds hlt)] with n hn
  exact hn.le

/-- **Exact reciprocal-vertical-mesh criterion for RH.** -/
theorem orientationUpperVerticalMeshLocallyBoundedBelow_iff_riemannHypothesis
    {a : ℝ} (ha : 0 < a) :
    XiCanonicalOrientationUpperVerticalMeshLocallyBoundedBelow a ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_orientationUpperVerticalMeshLocallyBoundedBelow ha,
    orientationUpperVerticalMeshLocallyBoundedBelow_of_riemannHypothesis ha⟩

end

end RHTower
