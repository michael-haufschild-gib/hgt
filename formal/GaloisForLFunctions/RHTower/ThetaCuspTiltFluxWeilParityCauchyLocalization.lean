import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityWeld
import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion

/-!
# Off-line Cauchy fibers localize entirely in the reflection-odd Weil channel

The finite sign vector of a non-real Xi divisor fiber is not merely Weil-negative: it is exactly
reflection-odd.  Its even energy is zero and its odd energy is the full multiplicity of the fiber
and its critical-line reflection.

Normalized regular two-pole Cauchy packets converge to this boundary vector.  Continuity of the
Hilbert parity projections therefore gives a sharp channelwise limit: even energy tends to zero,
while odd energy tends to the exact conjugate-fiber multiplicity.  Thus any off-line fiber forces
an eventual strict odd-energy escape already in a two-pole holomorphic packet.

This separates two notions of rank exposed by the corpus.  Two positive-real Euler nodes are
unconditionally safe, but two moving complex Cauchy poles are complete RH detectors because they
localize a reflection-antisymmetric divisor fiber.  The obstruction is reflected-fiber geometry,
not raw packet size.
-/

open Complex Filter Function
open scoped Topology

namespace RHTower

noncomputable section

/-- A non-real conjugate-fiber sign vector is pointwise anti-invariant under critical-line
reflection. -/
theorem xiOffRealSignTest_parityFlip
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilParityFlip (xiOffRealSignTest alpha) =
      fun z => -xiOffRealSignTest alpha z := by
  funext z
  by_cases hza : z = alpha
  · subst z
    simp [xiWeilParityFlip, xiOffRealSignTest, h]
  · by_cases hzb : z = (starRingEnd ℂ) alpha
    · subst z
      simp [xiWeilParityFlip, xiOffRealSignTest, h]
    · have hca : (starRingEnd ℂ) z ≠ alpha := by
        intro hz
        apply hzb
        have := congrArg (starRingEnd ℂ) hz
        simpa using this
      have hcb : (starRingEnd ℂ) z ≠ (starRingEnd ℂ) alpha := by
        intro hz
        apply hza
        exact Complex.conjCLE.injective hz
      simp [xiWeilParityFlip, xiOffRealSignTest, hza, hzb, hca, hcb]

theorem xiWeilEvenPart_offRealSignTest_eq_zero
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilEvenPart (xiOffRealSignTest alpha) = 0 := by
  funext z
  have hp := congrFun (xiOffRealSignTest_parityFlip h) z
  rw [xiWeilParityFlip] at hp
  change (xiOffRealSignTest alpha z +
    xiOffRealSignTest alpha ((starRingEnd ℂ) z)) / 2 = (0 : ℂ)
  rw [hp]
  ring

theorem xiWeilOddPart_offRealSignTest_eq
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilOddPart (xiOffRealSignTest alpha) = xiOffRealSignTest alpha := by
  funext z
  have hp := congrFun (xiOffRealSignTest_parityFlip h) z
  rw [xiWeilParityFlip] at hp
  rw [xiWeilOddPart, hp]
  ring

/-- The off-real sign vector has no reflection-even divisor energy. -/
theorem xiWeilEvenEnergy_offRealSignTest_eq_zero
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilEvenEnergy (xiOffRealSignTest alpha) = 0 := by
  simp [xiWeilEvenEnergy, xiWeilEvenPart_offRealSignTest_eq_zero h]

/-- Its reflection-odd energy is exactly the multiplicity of both reflected fibers. -/
theorem xiWeilOddEnergy_offRealSignTest_eq_card
    {alpha : ℂ} (h : (starRingEnd ℂ) alpha ≠ alpha) :
    xiWeilOddEnergy (xiOffRealSignTest alpha) =
      (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset).card : ℝ) := by
  have hp := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiOffRealSignTest_squareSummable alpha)
  rw [xiWeilPolarization_offRealSignTest alpha h,
    xiWeilEvenEnergy_offRealSignTest_eq_zero h] at hp
  have hre := congrArg Complex.re hp
  norm_num at hre ⊢
  linarith

/-- Even spectral projection on the multiplicity-exact Xi `ell²` carrier. -/
def xiWeilEvenProjectionLp
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  (2 : ℂ)⁻¹ • (v + xiWeilLineConjLp v)

/-- Odd spectral projection on the multiplicity-exact Xi `ell²` carrier. -/
def xiWeilOddProjectionLp
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  (2 : ℂ)⁻¹ • (v - xiWeilLineConjLp v)

theorem xiWeilEvaluationLp_evenPart
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    xiWeilEvaluationLp (xiWeilEvenPart F)
        (xiWeilEvenPart_squareSummable hF) =
      xiWeilEvenProjectionLp (xiWeilEvaluationLp F hF) := by
  apply Subtype.ext
  funext q
  change (F (xiSpectralPoint q) +
      F ((starRingEnd ℂ) (xiSpectralPoint q))) / 2 =
    (2 : ℂ)⁻¹ * (F (xiSpectralPoint q) +
      F (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))
  rw [xiSpectralPoint_lineConj]
  ring

theorem xiWeilEvaluationLp_oddPart
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    xiWeilEvaluationLp (xiWeilOddPart F)
        (xiWeilOddPart_squareSummable hF) =
      xiWeilOddProjectionLp (xiWeilEvaluationLp F hF) := by
  apply Subtype.ext
  funext q
  change (F (xiSpectralPoint q) -
      F ((starRingEnd ℂ) (xiSpectralPoint q))) / 2 =
    (2 : ℂ)⁻¹ * (F (xiSpectralPoint q) -
      F (xiSpectralPoint (xiZeroCopyLineConjEquiv q)))
  rw [xiSpectralPoint_lineConj]
  ring

theorem xiWeilEvenEnergy_eq_norm_projection_sq
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    xiWeilEvenEnergy F =
      ‖xiWeilEvenProjectionLp (xiWeilEvaluationLp F hF)‖ ^ 2 := by
  rw [← xiWeilEvaluationLp_evenPart hF,
    HilbertSchmidt.lp_norm_sq_eq]
  rfl

theorem xiWeilOddEnergy_eq_norm_projection_sq
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    xiWeilOddEnergy F =
      ‖xiWeilOddProjectionLp (xiWeilEvaluationLp F hF)‖ ^ 2 := by
  rw [← xiWeilEvaluationLp_oddPart hF,
    HilbertSchmidt.lp_norm_sq_eq]
  rfl

theorem tendsto_xiWeilEvenProjectionLp
    {v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2}
    {x : lp (fun _ : XiZeroCopy => ℂ) 2}
    (h : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => xiWeilEvenProjectionLp (v n)) atTop
      (𝓝 (xiWeilEvenProjectionLp x)) := by
  exact (h.add (tendsto_xiWeilLineConjLp h)).const_smul (2 : ℂ)⁻¹

theorem tendsto_xiWeilOddProjectionLp
    {v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2}
    {x : lp (fun _ : XiZeroCopy => ℂ) 2}
    (h : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => xiWeilOddProjectionLp (v n)) atTop
      (𝓝 (xiWeilOddProjectionLp x)) := by
  exact (h.sub (tendsto_xiWeilLineConjLp h)).const_smul (2 : ℂ)⁻¹

/-- Norm convergence of divisor evaluations forces separate convergence of both parity energies. -/
theorem tendsto_xiWeilParityEnergies
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, XiWeilSquareSummable (F n))
    {G : ℂ → ℂ} (hG : XiWeilSquareSummable G)
    (h : Tendsto (fun n => xiWeilEvaluationLp (F n) (hF n)) atTop
      (𝓝 (xiWeilEvaluationLp G hG))) :
    Tendsto (fun n => xiWeilEvenEnergy (F n)) atTop
        (𝓝 (xiWeilEvenEnergy G)) ∧
      Tendsto (fun n => xiWeilOddEnergy (F n)) atTop
        (𝓝 (xiWeilOddEnergy G)) := by
  constructor
  · have hseq : (fun n => xiWeilEvenEnergy (F n)) = fun n =>
        ‖xiWeilEvenProjectionLp
          (xiWeilEvaluationLp (F n) (hF n))‖ ^ 2 := by
        funext n
        exact xiWeilEvenEnergy_eq_norm_projection_sq (hF n)
    rw [hseq, xiWeilEvenEnergy_eq_norm_projection_sq hG]
    exact (tendsto_xiWeilEvenProjectionLp h).norm.pow 2
  · have hseq : (fun n => xiWeilOddEnergy (F n)) = fun n =>
        ‖xiWeilOddProjectionLp
          (xiWeilEvaluationLp (F n) (hF n))‖ ^ 2 := by
        funext n
        exact xiWeilOddEnergy_eq_norm_projection_sq (hF n)
    rw [hseq, xiWeilOddEnergy_eq_norm_projection_sq hG]
    exact (tendsto_xiWeilOddProjectionLp h).norm.pow 2

/-- Every off-line Xi fiber is localized by regular two-pole Cauchy packets whose even energy
tends to zero and whose odd energy tends to exact reflected-fiber multiplicity. -/
theorem exists_twoCauchyPacket_parity_localization
    (q : XiZeroCopy)
    (h : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q) :
    ∃ z w : ℕ → XiCRegularPoint,
      let alpha := xiSpectralPoint q
      let F : ℕ → ℂ → ℂ := fun n =>
        xiWeilTwoCauchyPacket (z n) (w n)
          (alpha - (z n : ℂ))
          (-((starRingEnd ℂ) alpha - (w n : ℂ)))
      Tendsto (fun n => xiWeilEvenEnergy (F n)) atTop (𝓝 0) ∧
        Tendsto (fun n => xiWeilOddEnergy (F n)) atTop
          (𝓝 (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
            (finite_xiSpectralPoint_fiber
              ((starRingEnd ℂ) alpha)).toFinset).card : ℝ)) := by
  let alpha : ℂ := xiSpectralPoint q
  obtain ⟨z, hz⟩ := exists_normalizedCauchyLp_tendsto_fiberIndicator alpha
  obtain ⟨w, hw⟩ :=
    exists_normalizedCauchyLp_tendsto_fiberIndicator ((starRingEnd ℂ) alpha)
  let F : ℕ → ℂ → ℂ := fun n =>
    xiWeilTwoCauchyPacket (z n) (w n)
      (alpha - (z n : ℂ))
      (-((starRingEnd ℂ) alpha - (w n : ℂ)))
  have hFsum : ∀ n, XiWeilSquareSummable (F n) := by
    intro n
    exact xiWeilTwoCauchyPacket_squareSummable _ _ _ _
  let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n =>
    xiWeilEvaluationLp (F n) (hFsum n)
  let Vlim : lp (fun _ : XiZeroCopy => ℂ) 2 :=
    xiWeilEvaluationLp (xiOffRealSignTest alpha)
      (xiOffRealSignTest_squareSummable alpha)
  have hV : Tendsto V atTop (𝓝 Vlim) := by
    have hsub := hz.sub hw
    have heq : V = fun n =>
        (alpha - (z n : ℂ)) • xiWeilCauchyLp (z n) -
          ((starRingEnd ℂ) alpha - (w n : ℂ)) • xiWeilCauchyLp (w n) := by
      funext n
      apply Subtype.ext
      funext q'
      change F n (xiSpectralPoint q') =
        (alpha - (z n : ℂ)) * xiWeilCauchyTest (z n) (xiSpectralPoint q') -
          ((starRingEnd ℂ) alpha - (w n : ℂ)) *
            xiWeilCauchyTest (w n) (xiSpectralPoint q')
      simp only [F, xiWeilTwoCauchyPacket]
      ring
    have helim : Vlim = xiWeilFiberIndicatorLp alpha -
        xiWeilFiberIndicatorLp ((starRingEnd ℂ) alpha) := by
      exact xiWeilEvaluationLp_offRealSignTest h
    rw [heq, helim]
    exact hsub
  have henergy := tendsto_xiWeilParityEnergies hFsum
    (xiOffRealSignTest_squareSummable alpha) hV
  refine ⟨z, w, ?_, ?_⟩
  · have he := henergy.1
    rw [xiWeilEvenEnergy_offRealSignTest_eq_zero h] at he
    simpa only [F, alpha] using he
  · have ho := henergy.2
    rw [xiWeilOddEnergy_offRealSignTest_eq_card h] at ho
    simpa only [F, alpha] using ho

/-- The localized two-pole packets eventually escape the parity contraction cone. -/
theorem exists_twoCauchyPacket_eventually_oddEnergy_gt_evenEnergy
    (q : XiZeroCopy)
    (h : (starRingEnd ℂ) (xiSpectralPoint q) ≠ xiSpectralPoint q) :
    ∃ z w : ℕ → XiCRegularPoint,
      let alpha := xiSpectralPoint q
      let F : ℕ → ℂ → ℂ := fun n =>
        xiWeilTwoCauchyPacket (z n) (w n)
          (alpha - (z n : ℂ))
          (-((starRingEnd ℂ) alpha - (w n : ℂ)))
      ∀ᶠ n in atTop, xiWeilEvenEnergy (F n) < xiWeilOddEnergy (F n) := by
  obtain ⟨z, w, heven, hodd⟩ :=
    exists_twoCauchyPacket_parity_localization q h
  refine ⟨z, w, ?_⟩
  let alpha : ℂ := xiSpectralPoint q
  let F : ℕ → ℂ → ℂ := fun n =>
    xiWeilTwoCauchyPacket (z n) (w n)
      (alpha - (z n : ℂ))
      (-((starRingEnd ℂ) alpha - (w n : ℂ)))
  let N : ℝ := (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
    (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset).card : ℝ)
  have hN : 0 < N := by
    have hmem : q ∈ (finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset := by
      apply Finset.mem_union_left
      simp [alpha]
    have hNat : 0 < ((finite_xiSpectralPoint_fiber alpha).toFinset ∪
        (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset).card :=
      Finset.card_pos.mpr ⟨q, hmem⟩
    change 0 < (((finite_xiSpectralPoint_fiber alpha).toFinset ∪
      (finite_xiSpectralPoint_fiber ((starRingEnd ℂ) alpha)).toFinset).card : ℝ)
    exact_mod_cast hNat
  have hdiff : Tendsto
      (fun n => xiWeilOddEnergy (F n) - xiWeilEvenEnergy (F n))
      atTop (𝓝 (N - 0)) := hodd.sub heven
  filter_upwards [hdiff.eventually_const_lt (by simpa using hN)] with n hn
  linarith

/-- Reflection-odd energy is contractive on every regular two-pole Cauchy packet. -/
def XiWeilRegularTwoCauchyParityDomination : Prop :=
  ∀ (z w : XiCRegularPoint) (a b : ℂ),
    xiWeilOddEnergy (xiWeilTwoCauchyPacket z w a b) ≤
      xiWeilEvenEnergy (xiWeilTwoCauchyPacket z w a b)

/-- RH is exactly parity contraction on the regular two-pole Cauchy family. -/
theorem riemannHypothesis_iff_regularTwoCauchyParityDomination :
    RiemannHypothesis ↔ XiWeilRegularTwoCauchyParityDomination := by
  constructor
  · intro hRH z w a b
    have hnonneg := (riemannHypothesis_iff_regularTwoCauchy_nonneg.mp hRH) z w a b
    have heq := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
      (xiWeilTwoCauchyPacket_squareSummable z w a b)
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith
  · intro hdom
    apply riemannHypothesis_iff_regularTwoCauchy_nonneg.mpr
    intro z w a b
    have hle := hdom z w a b
    have heq := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
      (xiWeilTwoCauchyPacket_squareSummable z w a b)
    have hre := congrArg Complex.re heq
    norm_num at hre
    linarith

end
end RHTower
