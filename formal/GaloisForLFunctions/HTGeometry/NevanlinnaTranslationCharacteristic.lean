import GaloisForLFunctions.HTGeometry.NevanlinnaTranslationBoundary
import GaloisForLFunctions.HTGeometry.ShiftedGreenKernelHarnack
import GaloisForLFunctions.HTGeometry.SmallGrowthFractionTranslation

/-!
# Nevanlinna characteristic under translation

Quantitative divisor and boundary estimates used to prove that precomposition by a fixed complex
translation preserves meromorphic functions of characteristic `o(r)`.
-/

open Complex Metric Real Set Topology Filter ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

open PoissonJensen MeromorphicOn

noncomputable section

/-- Pole mass in a disc is controlled by the pole-counting function at twice the radius. -/
theorem log_two_mul_poleMultiplicityMass_le_logCounting
    {f : ℂ → ℂ} (hf : Meromorphic f) {R : ℝ} (hR : 1 ≤ R) :
    Real.log 2 * poleMultiplicityMass f R ≤ logCounting f ⊤ (2 * R) := by
  classical
  let D : Function.locallyFinsupp ℂ ℤ := (divisor f Set.univ)⁻
  let DR := divisor f (closedBall (0 : ℂ) |R|)
  let P := (Function.locallyFinsuppWithin.toClosedBall (2 * R)) D
  have h2R : 0 < 2 * R := by positivity
  have hRabs : |R| = R := abs_of_nonneg (le_trans zero_le_one hR)
  have h2Rabs : |2 * R| = 2 * R := abs_of_pos h2R
  have hDRfin : DR.support.Finite :=
    DR.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hmassFin : (Function.support fun u : ℂ ↦ (DR u : ℝ)⁻).Finite :=
    hDRfin.subset (by
      intro u hu
      have hu' := Function.mem_support.mp hu
      exact Function.mem_support.mpr fun hzero ↦ hu' (by simp [hzero]))
  let S := hmassFin.toFinset
  have hmass : poleMultiplicityMass f R = ∑ u ∈ S, (DR u : ℝ)⁻ := by
    rw [poleMultiplicityMass]
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu
    rw [hDu] at hu
    simp at hu
  have hPfin : P.support.Finite :=
    P.finiteSupport (isCompact_closedBall (0 : ℂ) |2 * R|)
  let T := hPfin.toFinset
  have hcount : logCounting f ⊤ (2 * R) =
      ∑ u ∈ T, (P u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹) +
        (D 0 : ℝ) * Real.log (2 * R) := by
    rw [logCounting_top]
    change Function.locallyFinsuppWithin.logCounting D (2 * R) = _
    change (∑ᶠ u : ℂ, (P u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹)) +
        (D 0 : ℝ) * Real.log (2 * R) = _
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
    intro hPu
    exact hu (by simp [hPu])
  have hlocalGlobalInt : ∀ u ∈ closedBall (0 : ℂ) R, (DR u)⁻ = D u := by
    intro u hu
    have huabs : u ∈ closedBall (0 : ℂ) |R| := by
      rw [hRabs]
      exact hu
    have hlocal := divisor_apply (fun z _ => hf z) huabs
    have hglobal := divisor_apply (fun z _ => hf z) (Set.mem_univ u)
    dsimp [DR, D]
    rw [hlocal, hglobal]
  have hlocalGlobal : ∀ u ∈ closedBall (0 : ℂ) R, (DR u : ℝ)⁻ = (D u : ℝ) := by
    intro u hu
    rw [← hlocalGlobalInt u hu]
    change max (-(DR u : ℝ)) 0 = ((max (-DR u) 0 : ℤ) : ℝ)
    norm_cast
  have hSball : ∀ u ∈ S, u ∈ closedBall (0 : ℂ) R := by
    intro u hu
    have huMass : (DR u : ℝ)⁻ ≠ 0 := by simpa [S] using hu
    have huSupp : u ∈ DR.support := by
      apply Function.mem_support.mpr
      intro hzero
      rw [hzero] at huMass
      simp at huMass
    have huDomain := DR.supportWithinDomain huSupp
    rw [hRabs] at huDomain
    exact huDomain
  have hST : ∀ u ∈ S, u ≠ 0 → u ∈ T := by
    intro u huS hu0
    have huBall := hSball u huS
    have hu2Ball : u ∈ closedBall (0 : ℂ) |2 * R| := by
      rw [h2Rabs, mem_closedBall_zero_iff]
      have := mem_closedBall_zero_iff.mp huBall
      linarith
    have hDu : D u ≠ 0 := by
      have huMass : (DR u : ℝ)⁻ ≠ 0 := by simpa [S] using huS
      have hlocal := hlocalGlobal u huBall
      intro hzero
      rw [hzero] at hlocal
      exact huMass (by simpa using hlocal)
    have hPu : P u ≠ 0 := by
      change (if u ∈ closedBall (0 : ℂ) |2 * R| then D u else 0) ≠ 0
      rw [if_pos hu2Ball]
      exact hDu
    simpa [T] using hPu
  have hweight : ∀ u ∈ S, u ≠ 0 →
      Real.log 2 * (DR u : ℝ)⁻ ≤
        (P u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹) := by
    intro u huS hu0
    have huBall := hSball u huS
    have huNorm : ‖u‖ ≤ R := by simpa [mem_closedBall_zero_iff] using huBall
    have huNormPos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hu2Ball : u ∈ closedBall (0 : ℂ) |2 * R| := by
      rw [h2Rabs, mem_closedBall_zero_iff]
      linarith
    have hPD : P u = D u := by
      change (if u ∈ closedBall (0 : ℂ) |2 * R| then D u else 0) = D u
      rw [if_pos hu2Ball]
    have hcoeff : (P u : ℝ) = (DR u : ℝ)⁻ := by
      rw [hPD, ← hlocalGlobal u huBall]
    rw [hcoeff]
    have hlog : Real.log 2 ≤ Real.log ((2 * R) * ‖u‖⁻¹) := by
      apply Real.log_le_log (by norm_num)
      rw [inv_eq_one_div, mul_div]
      exact (le_div_iff₀ huNormPos).2 (by nlinarith)
    calc
      Real.log 2 * (DR u : ℝ)⁻ = (DR u : ℝ)⁻ * Real.log 2 := mul_comm _ _
      _ ≤ (DR u : ℝ)⁻ * Real.log ((2 * R) * ‖u‖⁻¹) :=
        mul_le_mul_of_nonneg_left hlog (negPart_nonneg _)
  have hsumNonzero : Real.log 2 * ∑ u ∈ S.erase 0, (DR u : ℝ)⁻ ≤
      ∑ u ∈ T, (P u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹) := by
    rw [Finset.mul_sum]
    calc
      ∑ u ∈ S.erase 0, Real.log 2 * (DR u : ℝ)⁻ ≤
          ∑ u ∈ S.erase 0, (P u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hweight u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
      _ ≤ ∑ u ∈ T, (P u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          exact hST u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
        · intro u huT _
          have huSupp : u ∈ P.support := by simpa [T] using huT
          have huBall := P.supportWithinDomain huSupp
          have huNorm : ‖u‖ ≤ 2 * R := by
            simpa [h2Rabs, mem_closedBall_zero_iff] using huBall
          have hPD : P u = D u := by
            change (if u ∈ closedBall (0 : ℂ) |2 * R| then D u else 0) = D u
            rw [if_pos huBall]
          have hcoeff : 0 ≤ (P u : ℝ) := by
            rw [hPD]
            norm_cast
            dsimp [D]
            exact negPart_nonneg _
          have hlog : 0 ≤ Real.log ((2 * R) * ‖u‖⁻¹) := by
            by_cases hu0 : u = 0
            · simp [hu0]
            · apply Real.log_nonneg
              rw [inv_eq_one_div, mul_div]
              exact (one_le_div (norm_pos_iff.mpr hu0)).2 (by simpa using huNorm)
          positivity
  have hzeroCoeff : (DR 0 : ℝ)⁻ = (D 0 : ℝ) := by
    exact hlocalGlobal 0 (by simp [le_trans zero_le_one hR])
  have hzero : Real.log 2 * (DR 0 : ℝ)⁻ ≤ (D 0 : ℝ) * Real.log (2 * R) := by
    rw [hzeroCoeff]
    have hlog : Real.log 2 ≤ Real.log (2 * R) := by
      apply Real.log_le_log (by norm_num)
      linarith
    calc
      Real.log 2 * (D 0 : ℝ) = (D 0 : ℝ) * Real.log 2 := mul_comm _ _
      _ ≤ (D 0 : ℝ) * Real.log (2 * R) := by
        apply mul_le_mul_of_nonneg_left hlog
        norm_cast
        dsimp [D]
        exact negPart_nonneg _
  rw [hmass, hcount]
  by_cases h0S : 0 ∈ S
  · rw [← Finset.sum_erase_add S (fun u ↦ (DR u : ℝ)⁻) h0S, mul_add]
    linarith
  · rw [Finset.erase_eq_self.mpr h0S] at hsumNonzero
    have hmass0 : (DR 0 : ℝ)⁻ = 0 := by
      have hnot : 0 ∉ Function.support (fun u : ℂ ↦ (DR u : ℝ)⁻) := by
        simpa [S] using h0S
      simpa [Function.mem_support] using hnot
    rw [hmass0] at hzeroCoeff
    rw [← hzeroCoeff]
    simp
    exact hsumNonzero

/-- Proximity after a fixed translation is controlled by two unshifted characteristics and a
fixed origin-germ constant. -/
theorem proximity_translate_le_characteristic
    {x : EntireField ℂ} (p : EntireFractionPresentation x) (hx : x ≠ 0)
    (c : ℂ) {r : ℝ} (hr : 1 ≤ r) (hc : ‖c‖ ≤ r) :
    proximity (fun z ↦ p.function (z + c)) ⊤ r ≤
      4 * characteristic p.function ⊤ (8 * r) +
        2 * max |Real.log ‖p.function 0‖|
          |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖| +
        (Real.log 9 / Real.log 2) * logCounting p.function ⊤ (16 * r) := by
  classical
  let R : ℝ := 8 * r
  let D := divisor p.function (closedBall (0 : ℂ) |R|)
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hR : 0 < R := by dsimp [R]; positivity
  have hRabs : |R| = R := abs_of_pos hR
  have hinner : ‖c‖ + r < R := by dsimp [R]; nlinarith
  have hDfin : D.support.Finite := D.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  let S := hDfin.toFinset
  let G : ℂ → ℝ := fun w ↦
    ∑ u ∈ S, (D u : ℝ)⁻ * outerDiscGreenKernel u R w
  let A : ℝ := Real.circleAverage (fun z ↦ |Real.log ‖p.function z‖|) 0 R
  let B : ℝ := 2 * A
  let Q : ℂ → ℝ := fun w ↦ B + G w
  have hmero := p.meromorphic
  have horder : ∀ u, meromorphicOrderAt p.function u ≠ ⊤ :=
    p.meromorphicOrderAt_ne_top hx
  have hSball : ∀ u ∈ S, u ∈ closedBall (0 : ℂ) R := by
    intro u hu
    have huSupp : u ∈ D.support := by simpa [S] using hu
    have huDomain := D.supportWithinDomain huSupp
    rw [hRabs] at huDomain
    exact huDomain
  have hGint : CircleIntegrable G c r := by
    dsimp [G]
    have hfun : (fun w ↦ ∑ u ∈ S, (D u : ℝ)⁻ * outerDiscGreenKernel u R w) =
        ∑ u ∈ S, fun w ↦ (D u : ℝ)⁻ * outerDiscGreenKernel u R w := by
      funext w
      simp
    rw [hfun]
    induction S using Finset.induction with
    | empty =>
        change CircleIntegrable (fun _ : ℂ ↦ (0 : ℝ)) c r
        exact circleIntegrable_const 0 c r
    | @insert u T hu ih =>
        rw [Finset.sum_insert hu]
        apply CircleIntegrable.add
        · change CircleIntegrable ((D u : ℝ)⁻ • outerDiscGreenKernel u R) c r
          show IntervalIntegrable
            (fun θ ↦ (D u : ℝ)⁻ • outerDiscGreenKernel u R (circleMap c r θ))
            MeasureTheory.volume 0 (2 * Real.pi)
          exact (circleIntegrable_outerDiscGreenKernel u c hR).const_smul
        · exact ih
  have hQint : CircleIntegrable Q c r := by
    dsimp [Q]
    change CircleIntegrable ((fun _ : ℂ ↦ B) + G) c r
    exact (circleIntegrable_const B c r).add hGint
  have hpint : CircleIntegrable (fun w ↦ Real.posLog ‖p.function w‖) c r :=
    (show MeromorphicOn p.function (sphere c |r|) from fun w _ ↦ hmero w).circleIntegrable_posLog_norm
  have hgood : ∀ᶠ w in Filter.codiscrete ℂ,
      (p.numerator : ℂ → ℂ) w ≠ 0 ∧ (p.denominator : ℂ → ℂ) w ≠ 0 := by
    have hnum := (p.inv hx).denominator_eventually_ne_zero
    have hden := p.denominator_eventually_ne_zero
    filter_upwards [hnum, hden] with w hn hd
    exact ⟨hn, hd⟩
  have hgoodWithin : ∀ᶠ w in Filter.codiscreteWithin (sphere c |r|),
      (p.numerator : ℂ → ℂ) w ≠ 0 ∧ (p.denominator : ℂ → ℂ) w ≠ 0 :=
    hgood.filter_mono (Filter.codiscreteWithin_mono (subset_univ _))
  have havg0 : 0 ≤ A := by
    have hEq := circleAverage_abs_log_norm_eq
      (f := p.function) (r := R) (fun z _ ↦ hmero z)
    dsimp [A]
    rw [hEq]
    exact add_nonneg
      ((ValueDistribution.proximity_nonneg (f := p.function) (a := (⊤ : WithTop ℂ))) R)
      ((ValueDistribution.proximity_nonneg (f := p.function) (a := (0 : WithTop ℂ))) R)
  have hpoint : ∀ w ∈ sphere c |r|,
      Real.posLog ‖p.function w‖ ≤ |Q w| := by
    intro w hwSphere
    by_cases hfw : p.function w = 0
    · simp [hfw]
    have hden : (p.denominator : ℂ → ℂ) w ≠ 0 := by
      intro hd
      apply hfw
      simp [EntireFractionPresentation.function, hd]
    have hwf : AnalyticAt ℂ p.function w := by
      apply AnalyticAt.div
      · exact p.numerator.2 w (Set.mem_univ w)
      · exact p.denominator.2 w (Set.mem_univ w)
      · exact hden
    have hwr : ‖w‖ ≤ 2 * r := by
      have hwc : ‖w - c‖ = r := by
        simpa [abs_of_pos hr0, mem_sphere_iff_norm] using hwSphere
      calc
        ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          have := norm_add_le (w - c) c
          simpa using this
        _ ≤ 2 * r := by nlinarith
    have hwBall : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      dsimp [R]
      nlinarith
    have hraw := posLog_norm_le_poissonBoundary_add_poleGreen
      hR hmero horder hwBall hwf hfw hwr (by dsimp [R]; nlinarith)
    have hsum :
        (∑ᶠ u : ℂ, (D u : ℝ)⁻ * outerDiscGreenKernel u R w) = G w := by
      dsimp [G]
      apply finsum_eq_sum_of_support_subset
      intro u hu
      simp only [Function.mem_support] at hu
      simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
      intro hDu
      exact hu (by simp [hDu])
    change Real.posLog ‖p.function w‖ ≤
      (R + 2 * r) / (R - 2 * r) * A +
        (∑ᶠ u : ℂ, (D u : ℝ)⁻ * outerDiscGreenKernel u R w) at hraw
    rw [hsum] at hraw
    have hfactor : (R + 2 * r) / (R - 2 * r) ≤ 2 := by
      dsimp [R]
      rw [div_le_iff₀ (by nlinarith : 0 < 8 * r - 2 * r)]
      nlinarith
    have hBQ : (R + 2 * r) / (R - 2 * r) * A + G w ≤ Q w := by
      dsimp [Q, B]
      nlinarith
    exact hraw.trans hBQ |>.trans (le_abs_self _)
  have hQnonneg : ∀ᶠ w in Filter.codiscreteWithin (sphere c |r|), 0 ≤ Q w := by
    filter_upwards [hgoodWithin, Filter.self_mem_codiscreteWithin (sphere c |r|)]
      with w hwgood hwSphere
    have hfw : p.function w ≠ 0 := by
      exact div_ne_zero hwgood.1 hwgood.2
    have hwf : AnalyticAt ℂ p.function w := by
      apply AnalyticAt.div
      · exact p.numerator.2 w (Set.mem_univ w)
      · exact p.denominator.2 w (Set.mem_univ w)
      · exact hwgood.2
    have hwClosedOuter : w ∈ closedBall (0 : ℂ) R := by
      have hwc : ‖w - c‖ = r := by
        simpa [abs_of_pos hr0, mem_sphere_iff_norm] using hwSphere
      rw [mem_closedBall_zero_iff]
      calc
        ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          have := norm_add_le (w - c) c
          simpa using this
        _ ≤ 2 * r := by nlinarith
        _ ≤ R := by dsimp [R]; nlinarith
    have hGw : 0 ≤ G w := by
      dsimp [G]
      apply Finset.sum_nonneg
      intro u huS
      have huBall := hSball u huS
      have hwu : w ≠ u := by
        intro hwu
        subst u
        have hwD : D w = 0 := by
          rw [divisor_apply (fun z _ ↦ hmero z) (by simpa [hRabs] using hwClosedOuter),
            hwf.meromorphicOrderAt_eq, hwf.analyticOrderAt_eq_zero.mpr hfw]
          simp
        have hwSupp : w ∈ D.support := by simpa [S] using huS
        exact Function.mem_support.mp hwSupp hwD
      exact mul_nonneg (negPart_nonneg _)
        (outerDiscGreenKernel_nonneg hR huBall hwClosedOuter hwu)
    dsimp [Q, B]
    positivity
  have hcircleQabs : Real.circleAverage (fun w ↦ |Q w|) c r =
      Real.circleAverage Q c r := by
    apply Real.circleAverage_congr_codiscreteWithin _ hr0.ne'
    filter_upwards [hQnonneg] with w hw
    exact abs_of_nonneg hw
  have hmeanPoint : Real.circleAverage (fun w ↦ Real.posLog ‖p.function w‖) c r ≤
      Real.circleAverage Q c r := by
    have hmono := Real.circleAverage_mono hpint hQint.abs hpoint
    change Real.circleAverage (fun w ↦ Real.posLog ‖p.function w‖) c r ≤
      Real.circleAverage (fun w ↦ |Q w|) c r at hmono
    exact hmono.trans_eq hcircleQabs
  have hGmean : Real.circleAverage G c r ≤ Real.log 9 * poleMultiplicityMass p.function R := by
    have hmeans : ∀ u ∈ S,
        Real.circleAverage (outerDiscGreenKernel u R) c r ≤ Real.log 9 := by
      intro u huS
      have huBall := hSball u huS
      have hu := circleAverage_innerLogKernel_sub_log_norm_le hR hr0 huBall hinner
      have hratio : (R + ‖c‖) / r ≤ 9 := by
        rw [div_le_iff₀ hr0]
        dsimp [R]
        nlinarith
      exact hu.trans (Real.log_le_log (by positivity) hratio)
    have hmeanEq : Real.circleAverage G c r =
        ∑ u ∈ S, (D u : ℝ)⁻ *
          Real.circleAverage (outerDiscGreenKernel u R) c r := by
      dsimp [G]
      have hfun : (fun w ↦ ∑ u ∈ S, (D u : ℝ)⁻ * outerDiscGreenKernel u R w) =
          ∑ u ∈ S, fun w ↦ (D u : ℝ)⁻ * outerDiscGreenKernel u R w := by
        funext w
        simp
      rw [hfun]
      rw [Real.circleAverage_sum]
      · apply Finset.sum_congr rfl
        intro u hu
        change Real.circleAverage ((D u : ℝ)⁻ • outerDiscGreenKernel u R) c r = _
        rw [Real.circleAverage_smul]
        rfl
      · intro u hu
        change CircleIntegrable ((D u : ℝ)⁻ • outerDiscGreenKernel u R) c r
        show IntervalIntegrable
          (fun θ ↦ (D u : ℝ)⁻ • outerDiscGreenKernel u R (circleMap c r θ))
          MeasureTheory.volume 0 (2 * Real.pi)
        exact (circleIntegrable_outerDiscGreenKernel u c hR).const_smul
    have hsum :
        (∑ u ∈ S, (D u : ℝ)⁻ *
            Real.circleAverage (outerDiscGreenKernel u R) c r) ≤
          ∑ u ∈ S, (D u : ℝ)⁻ * Real.log 9 := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hmeans u hu) (negPart_nonneg (D u : ℝ))
    rw [hmeanEq]
    calc
      ∑ u ∈ S, (D u : ℝ)⁻ * Real.circleAverage (outerDiscGreenKernel u R) c r ≤
          ∑ u ∈ S, (D u : ℝ)⁻ * Real.log 9 := hsum
      _ = Real.log 9 * poleMultiplicityMass p.function R := by
        rw [poleMultiplicityMass]
        have hmass : (∑ᶠ u : ℂ, (D u : ℝ)⁻) = ∑ u ∈ S, (D u : ℝ)⁻ := by
          apply finsum_eq_sum_of_support_subset
          intro u hu
          simp only [Function.mem_support] at hu
          simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
          intro hDu
          exact hu (by simp [hDu])
        rw [hmass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        exact mul_comm _ _
  have hmass := log_two_mul_poleMultiplicityMass_le_logCounting hmero
    (show 1 ≤ R by dsimp [R]; nlinarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hgreenBound : Real.circleAverage G c r ≤
      (Real.log 9 / Real.log 2) * logCounting p.function ⊤ (16 * r) := by
    have hmass' : poleMultiplicityMass p.function R ≤
        logCounting p.function ⊤ (2 * R) / Real.log 2 :=
      (le_div_iff₀ hlog2).2 (by simpa [mul_comm] using hmass)
    calc
      Real.circleAverage G c r ≤ Real.log 9 * poleMultiplicityMass p.function R := hGmean
      _ ≤ Real.log 9 * (logCounting p.function ⊤ (2 * R) / Real.log 2) :=
        mul_le_mul_of_nonneg_left hmass' hlog9
      _ = (Real.log 9 / Real.log 2) * logCounting p.function ⊤ (16 * r) := by
        dsimp [R]
        ring_nf
  have hA := circleAverage_abs_log_norm_le_characteristic
    (f := p.function) (r := R) (show 1 ≤ R by dsimp [R]; nlinarith) hmero
  rw [proximity_comp_add_top]
  calc
    Real.circleAverage (fun z ↦ Real.posLog ‖p.function z‖) c r ≤
        Real.circleAverage Q c r := hmeanPoint
    _ = B + Real.circleAverage G c r := by
      dsimp [Q]
      change Real.circleAverage ((fun _ : ℂ ↦ B) + G) c r = _
      rw [Real.circleAverage_add (circleIntegrable_const B c r) hGint,
        Real.circleAverage_const]
    _ ≤ 2 * (2 * characteristic p.function ⊤ R +
          max |Real.log ‖p.function 0‖|
            |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖|) +
        (Real.log 9 / Real.log 2) * logCounting p.function ⊤ (16 * r) := by
      dsimp [B]
      nlinarith
    _ = 4 * characteristic p.function ⊤ (8 * r) +
        2 * max |Real.log ‖p.function 0‖|
          |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖| +
        (Real.log 9 / Real.log 2) * logCounting p.function ⊤ (16 * r) := by
      dsimp [R]
      ring

/-- Little-o growth is stable under evaluation at a fixed positive radial dilation. -/
theorem isLittleO_comp_pos_mul {u : ℝ → ℝ} (hu : u =o[atTop] id)
    {a : ℝ} (ha : 0 < a) :
    (fun r ↦ u (a * r)) =o[atTop] id := by
  have hcomp := hu.comp_tendsto
    ((Filter.tendsto_const_mul_atTop_of_pos (f := id) ha).2 tendsto_id)
  have hscale := hcomp.const_mul_right (c := a⁻¹) (inv_ne_zero ha.ne')
  apply hscale.congr' (Filter.Eventually.of_forall fun _ ↦ rfl)
    (Filter.Eventually.of_forall fun r ↦ ?_)
  simp [id_eq, ha.ne']

/-- The translated proximity of a nonzero small-growth fraction is still `o(r)`. -/
theorem proximity_translate_isLittleO
    {x : EntireField ℂ} (p : EntireFractionPresentation x) (hx : x ≠ 0)
    (hp : characteristic p.function ⊤ =o[atTop] id) (c : ℂ) :
    proximity (fun z ↦ p.function (z + c)) ⊤ =o[atTop] id := by
  let C : ℝ := max |Real.log ‖p.function 0‖|
    |Real.log ‖meromorphicTrailingCoeffAt p.function 0‖|
  let K : ℝ := Real.log 9 / Real.log 2
  let v : ℝ → ℝ := fun r ↦
    4 * characteristic p.function ⊤ (8 * r) + 2 * C +
      K * characteristic p.function ⊤ (16 * r)
  have h8 : (fun r ↦ characteristic p.function ⊤ (8 * r)) =o[atTop] id :=
    isLittleO_comp_pos_mul hp (by norm_num)
  have h16 : (fun r ↦ characteristic p.function ⊤ (16 * r)) =o[atTop] id :=
    isLittleO_comp_pos_mul hp (by norm_num)
  have hv : v =o[atTop] id := by
    exact ((h8.const_mul_left 4).add
      (Asymptotics.isLittleO_const_id_atTop (2 * C))).add (h16.const_mul_left K)
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards with r
    exact ValueDistribution.proximity_nonneg r
  · filter_upwards [eventually_ge_atTop (max 1 ‖c‖)] with r hr
    have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
    have hcr : ‖c‖ ≤ r := le_trans (le_max_right _ _) hr
    have hprox := proximity_translate_le_characteristic p hx c hr1 hcr
    have hN : logCounting p.function ⊤ (16 * r) ≤
        characteristic p.function ⊤ (16 * r) := by
      change logCounting p.function ⊤ (16 * r) ≤
        proximity p.function ⊤ (16 * r) + logCounting p.function ⊤ (16 * r)
      have hprox0 : 0 ≤ proximity p.function ⊤ (16 * r) :=
        (ValueDistribution.proximity_nonneg
          (f := p.function) (a := (⊤ : WithTop ℂ))) (16 * r)
      linarith
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    dsimp [v, C, K]
    exact hprox.trans (by gcongr)

/-- Pole-counting under translation is bounded by a dilated unshifted count plus a fixed local
`O(log r)` contribution. -/
theorem eventually_logCounting_translate_le
    {x : EntireField ℂ} (p : EntireFractionPresentation x) (c : ℂ) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧
      ∀ᶠ r in atTop,
        logCounting (fun z ↦ p.function (z + c)) ⊤ r ≤
          logCounting p.function ⊤ (2 * (1 + ‖c‖) * r) + M * Real.log r + C := by
  classical
  let g : ℂ → ℂ := fun z ↦ p.function (z + c)
  let Dg : Function.locallyFinsupp ℂ ℤ := (divisor g Set.univ)⁻
  let Df : Function.locallyFinsupp ℂ ℤ := (divisor p.function Set.univ)⁻
  let L : ℝ := max 1 ‖c‖
  let PL := (Function.locallyFinsuppWithin.toClosedBall L) Dg
  have hg : Meromorphic g := by
    intro z
    exact meromorphicAt_comp_add.mpr (p.meromorphic (z + c))
  have hPLfin : PL.support.Finite :=
    PL.finiteSupport (isCompact_closedBall (0 : ℂ) |L|)
  let U := hPLfin.toFinset
  let M : ℝ := (∑ z ∈ U, (Dg z : ℝ)) + (Dg 0 : ℝ)
  let C : ℝ := ∑ z ∈ U, (Dg z : ℝ) * |Real.log ‖z‖|
  have hDg0 : ∀ z, 0 ≤ (Dg z : ℝ) := by
    intro z
    norm_cast
    dsimp [Dg]
    exact negPart_nonneg _
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (Finset.sum_nonneg fun z _ ↦ hDg0 z) (hDg0 0)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hDg0 z) (abs_nonneg _)
  refine ⟨M, C, hM, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 ‖c‖)] with r hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
  have hcr : ‖c‖ ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  let a : ℝ := 2 * (1 + ‖c‖)
  have ha : 0 < a := by dsimp [a]; positivity
  let Pg := (Function.locallyFinsuppWithin.toClosedBall r) Dg
  let Pf := (Function.locallyFinsuppWithin.toClosedBall (a * r)) Df
  have hPgfin : Pg.support.Finite :=
    Pg.finiteSupport (isCompact_closedBall (0 : ℂ) |r|)
  have hPffin : Pf.support.Finite :=
    Pf.finiteSupport (isCompact_closedBall (0 : ℂ) |a * r|)
  let S := hPgfin.toFinset
  let T := hPffin.toFinset
  let isLocal (z : ℂ) : Prop := ‖z‖ < 1 ∨ z + c = 0
  let Sloc := S.filter isLocal
  let Sfar := S.filter (fun z ↦ ¬ isLocal z)
  have hcountG : logCounting g ⊤ r =
      ∑ z ∈ S, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) +
        (Dg 0 : ℝ) * Real.log r := by
    rw [logCounting_top]
    change Function.locallyFinsuppWithin.logCounting Dg r = _
    change (∑ᶠ z : ℂ, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹)) +
      (Dg 0 : ℝ) * Real.log r = _
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro z hz
    simp only [Function.mem_support] at hz
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
    intro hzero
    exact hz (by simp [hzero])
  have hcountF : logCounting p.function ⊤ (a * r) =
      ∑ u ∈ T, (Pf u : ℝ) * Real.log ((a * r) * ‖u‖⁻¹) +
        (Df 0 : ℝ) * Real.log (a * r) := by
    rw [logCounting_top]
    change Function.locallyFinsuppWithin.logCounting Df (a * r) = _
    change (∑ᶠ u : ℂ, (Pf u : ℝ) * Real.log ((a * r) * ‖u‖⁻¹)) +
      (Df 0 : ℝ) * Real.log (a * r) = _
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
    intro hzero
    exact hu (by simp [hzero])
  have hdiv : ∀ z : ℂ, Dg z = Df (z + c) := by
    intro z
    dsimp [Dg, Df, g]
    congr 1
    rw [divisor_apply (fun w _ ↦ hg w) (Set.mem_univ z),
      divisor_apply (fun w _ ↦ p.meromorphic w) (Set.mem_univ (z + c)),
      meromorphicOrderAt_comp_add]
  have hSball : ∀ z ∈ S, z ∈ closedBall (0 : ℂ) |r| := by
    intro z hz
    have hzSupp : z ∈ Pg.support := by simpa [S] using hz
    exact Pg.supportWithinDomain hzSupp
  have hSPg : ∀ z ∈ S, Pg z = Dg z := by
    intro z hz
    have hzBall := hSball z hz
    change (if z ∈ closedBall (0 : ℂ) |r| then Dg z else 0) = Dg z
    rw [if_pos hzBall]
  have hlocalU : Sloc ⊆ U := by
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    have hzLocal := (Finset.mem_filter.mp hz).2
    have hzPg : Pg z ≠ 0 := by simpa [S] using hzS
    have hzDg : Dg z ≠ 0 := by simpa [hSPg z hzS] using hzPg
    have hzNorm : ‖z‖ ≤ L := by
      rcases hzLocal with hzsmall | hzc
      · exact hzsmall.le.trans (le_max_left 1 ‖c‖)
      · have hz : z = -c := by linear_combination hzc
        rw [hz, norm_neg]
        exact le_max_right _ _
    have hzBall : z ∈ closedBall (0 : ℂ) |L| := by
      rw [mem_closedBall_zero_iff]
      have hL0 : 0 ≤ L := le_trans zero_le_one (le_max_left _ _)
      simpa [abs_of_nonneg hL0] using hzNorm
    have hzPL : PL z ≠ 0 := by
      change (if z ∈ closedBall (0 : ℂ) |L| then Dg z else 0) ≠ 0
      rw [if_pos hzBall]
      exact hzDg
    simpa [U] using hzPL
  have hlocalTerm : ∀ z ∈ Sloc,
      (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤
        (Dg z : ℝ) * (Real.log r + |Real.log ‖z‖|) := by
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    rw [hSPg z hzS]
    apply mul_le_mul_of_nonneg_left _ (hDg0 z)
    by_cases hz0 : z = 0
    · subst z
      simp
      exact Real.log_nonneg hr1
    · rw [Real.log_mul hr0.ne' (inv_ne_zero (norm_ne_zero_iff.mpr hz0)), Real.log_inv]
      linarith [neg_le_abs (Real.log ‖z‖)]
  have hlocalSum :
      ∑ z ∈ Sloc, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤
        (∑ z ∈ U, (Dg z : ℝ)) * Real.log r + C := by
    calc
      ∑ z ∈ Sloc, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤
          ∑ z ∈ Sloc, (Dg z : ℝ) * (Real.log r + |Real.log ‖z‖|) := by
        exact Finset.sum_le_sum hlocalTerm
      _ ≤ ∑ z ∈ U, (Dg z : ℝ) * (Real.log r + |Real.log ‖z‖|) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hlocalU
        intro z hzU _
        exact mul_nonneg (hDg0 z) (add_nonneg (Real.log_nonneg hr1) (abs_nonneg _))
      _ = (∑ z ∈ U, (Dg z : ℝ)) * Real.log r + C := by
        dsimp [C]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_mul]
  have hfarTerm : ∀ z ∈ Sfar,
      (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤
        (Df (z + c) : ℝ) * Real.log ((a * r) * ‖z + c‖⁻¹) := by
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    have hzFar := (Finset.mem_filter.mp hz).2
    have hzNorm : 1 ≤ ‖z‖ := le_of_not_gt (fun h ↦ hzFar (Or.inl h))
    have hzu : z + c ≠ 0 := fun h ↦ hzFar (Or.inr h)
    rw [hSPg z hzS, hdiv z]
    apply mul_le_mul_of_nonneg_left _
    · rw [← hdiv z]
      exact hDg0 z
    · apply Real.log_le_log
      · have : 0 < r * ‖z‖⁻¹ := mul_pos hr0 (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hzNorm))
        exact this
      · rw [inv_eq_one_div, inv_eq_one_div, mul_div, mul_div]
        apply (div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one hzNorm)
          (norm_pos_iff.mpr hzu)).2
        have hnorm : ‖z + c‖ ≤ (1 + ‖c‖) * ‖z‖ := by
          calc
            ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le _ _
            _ ≤ ‖z‖ + ‖c‖ * ‖z‖ := by
              linarith [le_mul_of_one_le_right (norm_nonneg c) hzNorm]
            _ = (1 + ‖c‖) * ‖z‖ := by ring
        have hscaled := mul_le_mul_of_nonneg_left hnorm hr0.le
        dsimp [a]
        nlinarith [mul_nonneg hr0.le (mul_nonneg (by positivity : 0 ≤ 1 + ‖c‖) (norm_nonneg z))]
  let V := Sfar.image (fun z ↦ z + c)
  have hVT : V ⊆ T := by
    intro u huV
    obtain ⟨z, hzFar, rfl⟩ := Finset.mem_image.mp huV
    have hzS := (Finset.mem_filter.mp hzFar).1
    have hzFarProp := (Finset.mem_filter.mp hzFar).2
    have hzu : z + c ≠ 0 := fun h ↦ hzFarProp (Or.inr h)
    have hzPg : Pg z ≠ 0 := by simpa [S] using hzS
    have hzDg : Dg z ≠ 0 := by simpa [hSPg z hzS] using hzPg
    have huDf : Df (z + c) ≠ 0 := by simpa [hdiv z] using hzDg
    have hzNorm : ‖z‖ ≤ r := by
      have := hSball z hzS
      simpa [abs_of_pos hr0, mem_closedBall_zero_iff] using this
    have huNorm : ‖z + c‖ ≤ a * r := by
      calc
        ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le _ _
        _ ≤ 2 * r := by nlinarith
        _ ≤ a * r := by dsimp [a]; nlinarith [norm_nonneg c]
    have huBall : z + c ∈ closedBall (0 : ℂ) |a * r| := by
      rw [mem_closedBall_zero_iff, abs_of_pos (mul_pos ha hr0)]
      exact huNorm
    have huPf : Pf (z + c) ≠ 0 := by
      change (if z + c ∈ closedBall (0 : ℂ) |a * r| then Df (z + c) else 0) ≠ 0
      rw [if_pos huBall]
      exact huDf
    simpa [T] using huPf
  have hfarSum :
      ∑ z ∈ Sfar, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤
        ∑ u ∈ T, (Pf u : ℝ) * Real.log ((a * r) * ‖u‖⁻¹) := by
    calc
      ∑ z ∈ Sfar, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) ≤
          ∑ z ∈ Sfar, (Df (z + c) : ℝ) *
            Real.log ((a * r) * ‖z + c‖⁻¹) := Finset.sum_le_sum hfarTerm
      _ = ∑ u ∈ V, (Df u : ℝ) * Real.log ((a * r) * ‖u‖⁻¹) := by
        symm
        apply Finset.sum_image
        intro z hz y hy hEq
        exact add_right_cancel hEq
      _ = ∑ u ∈ V, (Pf u : ℝ) * Real.log ((a * r) * ‖u‖⁻¹) := by
        apply Finset.sum_congr rfl
        intro u huV
        have huT := hVT huV
        have huSupp : u ∈ Pf.support := by simpa [T] using huT
        have huBall := Pf.supportWithinDomain huSupp
        have hPf : Pf u = Df u := by
          change (if u ∈ closedBall (0 : ℂ) |a * r| then Df u else 0) = Df u
          rw [if_pos huBall]
        rw [hPf]
      _ ≤ ∑ u ∈ T, (Pf u : ℝ) * Real.log ((a * r) * ‖u‖⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hVT
        intro u huT _
        have huSupp : u ∈ Pf.support := by simpa [T] using huT
        have huBall := Pf.supportWithinDomain huSupp
        have huNorm : ‖u‖ ≤ a * r := by
          simpa [abs_of_pos (mul_pos ha hr0), mem_closedBall_zero_iff] using huBall
        have hcoeff : 0 ≤ (Pf u : ℝ) := by
          have hPf : Pf u = Df u := by
            change (if u ∈ closedBall (0 : ℂ) |a * r| then Df u else 0) = Df u
            rw [if_pos huBall]
          rw [hPf]
          norm_cast
          dsimp [Df]
          exact negPart_nonneg _
        have hlog : 0 ≤ Real.log ((a * r) * ‖u‖⁻¹) := by
          by_cases hu0 : u = 0
          · simp [hu0]
          · apply Real.log_nonneg
            rw [inv_eq_one_div, mul_div]
            exact (one_le_div (norm_pos_iff.mpr hu0)).2 (by simpa using huNorm)
        positivity
  rw [hcountG, hcountF]
  have hsplit := Finset.sum_filter_add_sum_filter_not S isLocal
    (fun z ↦ (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹))
  have hsplit' :
      (∑ z ∈ Sloc, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹)) +
        ∑ z ∈ Sfar, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) =
          ∑ z ∈ S, (Pg z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
    simpa [Sloc, Sfar] using hsplit
  rw [← hsplit']
  have hDfZero : 0 ≤ (Df 0 : ℝ) := by
    norm_cast
    dsimp [Df]
    exact negPart_nonneg _
  have hlogar : 0 ≤ Real.log (a * r) := Real.log_nonneg (by
    have : 1 ≤ a * r := by dsimp [a]; nlinarith [norm_nonneg c]
    exact this)
  dsimp [M]
  have hOuterZero : 0 ≤ (Df 0 : ℝ) * Real.log (a * r) := mul_nonneg hDfZero hlogar
  linarith

/-- The translated pole-counting function of a small-growth fraction is still `o(r)`. -/
theorem logCounting_translate_isLittleO
    {x : EntireField ℂ} (p : EntireFractionPresentation x)
    (hp : characteristic p.function ⊤ =o[atTop] id) (c : ℂ) :
    logCounting (fun z ↦ p.function (z + c)) ⊤ =o[atTop] id := by
  obtain ⟨M, C, hM, hC, hbound⟩ := eventually_logCounting_translate_le p c
  let a : ℝ := 2 * (1 + ‖c‖)
  let v : ℝ → ℝ := fun r ↦
    characteristic p.function ⊤ (a * r) + M * Real.log r + C
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscaled : (fun r ↦ characteristic p.function ⊤ (a * r)) =o[atTop] id :=
    isLittleO_comp_pos_mul hp ha
  have hv : v =o[atTop] id := by
    exact (hscaled.add (Real.isLittleO_log_id_atTop.const_mul_left M)).add
      (Asymptotics.isLittleO_const_id_atTop C)
  apply isLittleO_of_eventually_nonneg_le hv
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact ValueDistribution.logCounting_nonneg hr
  · filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with r hrBound hr
    have hN : logCounting p.function ⊤ (a * r) ≤
        characteristic p.function ⊤ (a * r) := by
      change logCounting p.function ⊤ (a * r) ≤
        proximity p.function ⊤ (a * r) + logCounting p.function ⊤ (a * r)
      have hprox : 0 ≤ proximity p.function ⊤ (a * r) :=
        ValueDistribution.proximity_nonneg (a * r)
      linarith
    change logCounting (fun z ↦ p.function (z + c)) ⊤ r ≤ v r
    dsimp [v, a]
    exact hrBound.trans (by linarith)

/-- Fixed translation preserves sublinear Nevanlinna characteristic for a nonzero fraction. -/
theorem characteristic_translate_isLittleO
    {x : EntireField ℂ} (p : EntireFractionPresentation x) (hx : x ≠ 0)
    (hp : characteristic p.function ⊤ =o[atTop] id) (c : ℂ) :
    characteristic (fun z ↦ p.function (z + c)) ⊤ =o[atTop] id := by
  change (fun r ↦ proximity (fun z ↦ p.function (z + c)) ⊤ r +
    logCounting (fun z ↦ p.function (z + c)) ⊤ r) =o[atTop] id
  exact (proximity_translate_isLittleO p hx hp c).add
    (logCounting_translate_isLittleO p hp c)

/-- Fixed complex translation preserves Nagoshi's small-growth condition. -/
theorem HasSmallGrowth.translate {x : EntireField ℂ} (hx : HasSmallGrowth x) (c : ℂ) :
    HasSmallGrowth (fieldTranslateEquiv c x) := by
  by_cases hx0 : x = 0
  · simpa [hx0] using hasSmallGrowth_zero
  · obtain ⟨p, hp⟩ := hx
    refine ⟨p.translate c, ?_⟩
    rw [p.function_translate]
    exact characteristic_translate_isLittleO p hx0 hp c

/-- Translation restricted to Nagoshi's exact small-growth field. -/
noncomputable def smallGrowthTranslateEquiv (c : ℂ) :
    SmallGrowthMeromorphicField ≃+* SmallGrowthMeromorphicField where
  toFun x := ⟨fieldTranslateEquiv c x.1, x.2.translate c⟩
  invFun x := ⟨(fieldTranslateEquiv c).symm x.1, by
    change HasSmallGrowth (fieldTranslateEquiv (-c) x.1)
    exact x.2.translate (-c)⟩
  left_inv x := Subtype.ext ((fieldTranslateEquiv c).left_inv x.1)
  right_inv x := Subtype.ext ((fieldTranslateEquiv c).right_inv x.1)
  map_add' x y := Subtype.ext (map_add (fieldTranslateEquiv c) x.1 y.1)
  map_mul' x y := Subtype.ext (map_mul (fieldTranslateEquiv c) x.1 y.1)

@[simp]
theorem smallGrowthTranslateEquiv_coe (c : ℂ) (x : SmallGrowthMeromorphicField) :
    ((smallGrowthTranslateEquiv c x : SmallGrowthMeromorphicField) : EntireField ℂ) =
      fieldTranslateEquiv c x :=
  rfl

/-- Restriction of global meromorphic fractions to the upper end commutes with translation. -/
theorem entireFieldToUpperEndMero_fieldTranslateEquiv (c : ℂ) (x : EntireField ℂ) :
    entireFieldToUpperEndMero (fieldTranslateEquiv c x) =
      upperEndTranslationMeroEquiv c (entireFieldToUpperEndMero x) := by
  letI := isDomain_upperEndAnalyticSubring
  have hbase : ∀ a : entireSubring ℂ,
      entireFieldToUpperEndMero
          (fieldTranslateEquiv c
            (algebraMap (entireSubring ℂ) (EntireField ℂ) a)) =
        upperEndTranslationMeroEquiv c
          (entireFieldToUpperEndMero
            (algebraMap (entireSubring ℂ) (EntireField ℂ) a)) := by
    intro a
    rw [fieldTranslateEquiv_algebraMap, entireFieldToUpperEndMero_algebraMap,
      entireFieldToUpperEndMero_algebraMap, upperEndTranslationMeroEquiv_algebraMap]
    congr 1
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (entireSubring ℂ) x
  rw [map_div₀, map_div₀, map_div₀, hbase a, hbase b]
  rw [← map_div₀]

/-- The exact `F_s` realization in the upper-end field is translation-equivariant. -/
@[simp]
theorem smallGrowthTranslateEquiv_algebraMap (c : ℂ)
    (x : SmallGrowthMeromorphicField) :
    algebraMap SmallGrowthMeromorphicField upperEndMeroField
        (smallGrowthTranslateEquiv c x) =
      upperEndTranslationMeroEquiv c
        (algebraMap SmallGrowthMeromorphicField upperEndMeroField x) := by
  change entireFieldToUpperEndMero (fieldTranslateEquiv c x.1) =
    upperEndTranslationMeroEquiv c (entireFieldToUpperEndMero x.1)
  exact entireFieldToUpperEndMero_fieldTranslateEquiv c x.1

end

end GaloisForLFunctions.HTGeometry
