import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZSchwarzschildResponseJetInterpolationNoGo
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.RHTower.DeBrangesExplicitGammaGauge
import GaloisForLFunctions.HTGeometry.MinimalTypeProjectiveSeparation

/-!
# FZZ--Schwarzschild completed response symmetry no-go

The full Schwarzschild/FZZ response jet still does not determine a completed complex-order source
after imposing the Riemann-Xi functional equation, Schwarz reality, and the natural global
order-one growth class.

In response coordinate `z = s - 2`, put

`X(z) = xi(z+2)`,

`K(z) = Gamma(-z)⁻¹ Gamma(z+3)⁻¹`.

The physical jet determines every sample `X(m)`, including its Archimedean completion weight.
The null generator `K` is entire, order one, Schwarz-real, fixed by `z ↦ -3-z`, and invisible at
every natural response order.  More sharply, analytic division gives the exact classification

`F = X + H K`,

where `H` is an arbitrary entire function carrying the same reflection and real structure.

The explicit real constant quotient obtained by cancelling `X` at `z=-5/4` produces an entire,
order-one, FE-symmetric, Schwarz-real continuation with all physical samples and with paired zeros
at `s=3/4` and `s=1/4`.  These lie strictly inside the critical strip and off the critical line.

Thus the strengthened source-only chain

`all Schwarzschild/FZZ response orders + completion + FE + Schwarz + order one`

`-> Xi zero control -> Ward equivariance -> RH`

is false.  Any surviving producer must add off-lattice or genuinely nonlocal source information
that excludes this symmetric reciprocal-Gamma ideal.

**[FALSIFIED] [ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]** The completed physical response samples,
FE, Schwarz reality, and order-one growth select the Xi continuation or force critical-line zeros.

**[NOVELTY AUDIT]** Reciprocal-Gamma divisors and entire interpolation are classical.  The corpus
already contained the one-ladder response classification and generic FE/Schwarz countermodels.
A targeted literature audit through 2026-08-30 found no theorem preserving Solon's exact completed
Schwarzschild response samples together with this symmetry package, no two-ladder principal-ideal
classification, and no resulting FZZ/RH route kill.  Novelty is the exact cross-model theorem and
its source-selection consequence.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- The completed Xi continuation of the physical response clock in response coordinate
`z = s - 2`. -/
def completedBlackHoleJetInterpolation (z : ℂ) : ℂ := xi (z + 2)

/-- The reciprocal-Gamma divisor invisible on the natural response ladder and its
functional-equation reflection. -/
def symmetricJetNullGenerator (z : ℂ) : ℂ :=
  reciprocalGammaEntire (-z) * reciprocalGammaEntire (z + 3)

theorem differentiable_completedBlackHoleJetInterpolation :
    Differentiable ℂ completedBlackHoleJetInterpolation := by
  exact xi_differentiable.comp (by fun_prop)

theorem completedBlackHoleJetInterpolation_reflection (z : ℂ) :
    completedBlackHoleJetInterpolation (-3 - z) =
      completedBlackHoleJetInterpolation z := by
  rw [completedBlackHoleJetInterpolation, completedBlackHoleJetInterpolation]
  have h := xi_one_sub (z + 2)
  ring_nf at h ⊢
  exact h

theorem completedBlackHoleJetInterpolation_conj (z : ℂ) :
    completedBlackHoleJetInterpolation ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedBlackHoleJetInterpolation z) := by
  rw [completedBlackHoleJetInterpolation, completedBlackHoleJetInterpolation]
  have h := xi_conj (z + 2)
  simpa only [map_add, map_ofNat] using h

theorem orderOneEnvelope_completedBlackHoleJetInterpolation :
    OrderOneEnvelope completedBlackHoleJetInterpolation := by
  exact (orderOneEnvelope_riemannXi.comp_affine 1 2).congr fun z => by
    rw [completedBlackHoleJetInterpolation, ← xi_eq_riemannXi]
    ring_nf

/-- The completed physical sample: the normalized Solon jet multiplied by the elementary and
Archimedean Xi completion factors. -/
def completedBlackHoleJetSample (scaleLog : ℂ) (m : ℕ) : ℂ :=
  (((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) / 2) *
    Complex.Gammaℝ ((m + 2 : ℕ) : ℂ) *
      (_root_.HTGeometry.normalizedBlackHoleFarZoneJet scaleLog m : ℂ)

/-- The canonical completed continuation reproduces the completed physical response sample at
every natural order, independently of the far-zone scale convention. -/
theorem completedBlackHoleJetInterpolation_nat (scaleLog : ℂ) (m : ℕ) :
    completedBlackHoleJetInterpolation (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  have hs : (m : ℂ) + 2 = ((m + 2 : ℕ) : ℂ) := by
    push_cast
    ring_nf
  rw [completedBlackHoleJetInterpolation, hs]
  have hs0 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by
    have hn : m + 2 ≠ 0 := by omega
    exact_mod_cast hn
  have hs1 : ((m + 2 : ℕ) : ℂ) ≠ 1 := by
    intro h
    have hn : m + 2 = 1 := by exact_mod_cast h
    omega
  rw [xi_eq_half_mul hs0 hs1]
  have hG : Complex.Gammaℝ ((m + 2 : ℕ) : ℂ) ≠ 0 := by
    exact Gammaℝ_ofReal_ne_zero (t := (m + 2 : ℕ)) (by positivity)
  have hz := riemannZeta_def_of_ne_zero hs0
  have hcompleted : completedRiemannZeta ((m + 2 : ℕ) : ℂ) =
      riemannZeta ((m + 2 : ℕ) : ℂ) * Complex.Gammaℝ ((m + 2 : ℕ) : ℂ) := by
    rw [hz, div_mul_cancel₀ _ hG]
  rw [hcompleted,
    ← _root_.HTGeometry.normalizedBlackHoleFarZoneJet_ofReal_eq_riemannZeta
      scaleLog m]
  simp only [completedBlackHoleJetSample]
  have hsucc : ((m + 2 : ℕ) : ℂ) - 1 = ((m + 1 : ℕ) : ℂ) := by
    push_cast
    ring_nf
  rw [hsucc]
  ring_nf

theorem differentiable_symmetricJetNullGenerator :
    Differentiable ℂ symmetricJetNullGenerator := by
  exact (contDiff_reciprocalGammaEntire.differentiable (by simp)).comp (by fun_prop) |>.mul
    ((contDiff_reciprocalGammaEntire.differentiable (by simp)).comp (by fun_prop))

theorem symmetricJetNullGenerator_reflection (z : ℂ) :
    symmetricJetNullGenerator (-3 - z) = symmetricJetNullGenerator z := by
  rw [symmetricJetNullGenerator, symmetricJetNullGenerator]
  ring_nf

theorem symmetricJetNullGenerator_conj (z : ℂ) :
    symmetricJetNullGenerator ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (symmetricJetNullGenerator z) := by
  rw [symmetricJetNullGenerator, symmetricJetNullGenerator, map_mul]
  rw [← GaloisForLFunctions.RHTower.reciprocalGammaEntire_conj,
    ← GaloisForLFunctions.RHTower.reciprocalGammaEntire_conj]
  have hthree : (starRingEnd ℂ) (3 : ℂ) = 3 :=
    map_ofNat (starRingEnd ℂ) 3
  rw [show -((starRingEnd ℂ) z) = (starRingEnd ℂ) (-z) by simp,
    show (starRingEnd ℂ) z + 3 = (starRingEnd ℂ) (z + 3) by
      rw [map_add, hthree]]

theorem orderOneEnvelope_symmetricJetNullGenerator :
    OrderOneEnvelope symmetricJetNullGenerator := by
  refine ((orderOneEnvelope_reciprocalGammaEntire.comp_affine (-1) 0).mul
    (orderOneEnvelope_reciprocalGammaEntire.comp_affine 1 3)).congr ?_
  intro z
  simp only [symmetricJetNullGenerator]
  congr 1 <;> ring_nf

theorem symmetricJetNullGenerator_nat (m : ℕ) :
    symmetricJetNullGenerator (m : ℂ) = 0 := by
  simp [symmetricJetNullGenerator, reciprocalGammaEntire,
    Complex.Gamma_neg_nat_eq_zero]

/-- Interior response coordinate used to force a nontrivial off-critical zero.  It corresponds to
the completed variable `s=3/4`. -/
def interiorResponsePoint : ℂ := ((-(5 / 4) : ℝ) : ℂ)

theorem symmetricJetNullGenerator_interiorResponsePoint_ne_zero :
    symmetricJetNullGenerator interiorResponsePoint ≠ 0 := by
  rw [symmetricJetNullGenerator]
  apply mul_ne_zero
  · unfold reciprocalGammaEntire
    apply inv_ne_zero
    intro hzero
    rw [Complex.Gamma_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    have hre := congrArg Complex.re hn
    norm_num [interiorResponsePoint] at hre
    have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · unfold reciprocalGammaEntire
    apply inv_ne_zero
    intro hzero
    rw [Complex.Gamma_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    have hre := congrArg Complex.re hn
    norm_num [interiorResponsePoint] at hre
    have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The unique constant coefficient that forces cancellation at `s=3/4`. -/
def interiorResponseCoefficient : ℂ :=
  -completedBlackHoleJetInterpolation interiorResponsePoint /
    symmetricJetNullGenerator interiorResponsePoint

theorem completedBlackHoleJetInterpolation_interiorResponsePoint_ne_zero :
    completedBlackHoleJetInterpolation interiorResponsePoint ≠ 0 := by
  rw [completedBlackHoleJetInterpolation]
  convert xi_ne_zero_of_ofReal (3 / 4) using 1
  norm_num [interiorResponsePoint]

theorem interiorResponseCoefficient_ne_zero : interiorResponseCoefficient ≠ 0 := by
  rw [interiorResponseCoefficient]
  exact div_ne_zero
    (neg_ne_zero.mpr completedBlackHoleJetInterpolation_interiorResponsePoint_ne_zero)
    symmetricJetNullGenerator_interiorResponsePoint_ne_zero

theorem interiorResponseCoefficient_conj :
    (starRingEnd ℂ) interiorResponseCoefficient = interiorResponseCoefficient := by
  have ha : (starRingEnd ℂ) interiorResponsePoint = interiorResponsePoint := by
    simpa only [interiorResponsePoint] using
      (Complex.conj_ofReal (-(5 / 4) : ℝ))
  have hX := completedBlackHoleJetInterpolation_conj interiorResponsePoint
  have hK := symmetricJetNullGenerator_conj interiorResponsePoint
  rw [ha] at hX hK
  rw [interiorResponseCoefficient, map_div₀, map_neg, ← hX, ← hK]

/-- Explicit completed-source countermodel with all physical samples and a paired off-critical
interior zero. -/
def interiorStripSymmetricResponseCountermodel (z : ℂ) : ℂ :=
  completedBlackHoleJetInterpolation z +
    interiorResponseCoefficient * symmetricJetNullGenerator z

theorem interiorStripSymmetricResponseCountermodel_zero :
    interiorStripSymmetricResponseCountermodel interiorResponsePoint = 0 := by
  rw [interiorStripSymmetricResponseCountermodel, interiorResponseCoefficient]
  rw [div_mul_cancel₀ _
    symmetricJetNullGenerator_interiorResponsePoint_ne_zero]
  ring_nf

theorem differentiable_interiorStripSymmetricResponseCountermodel :
    Differentiable ℂ interiorStripSymmetricResponseCountermodel := by
  exact differentiable_completedBlackHoleJetInterpolation.add
    (differentiable_const interiorResponseCoefficient |>.mul
      differentiable_symmetricJetNullGenerator)

theorem interiorStripSymmetricResponseCountermodel_nat (scaleLog : ℂ) (m : ℕ) :
    interiorStripSymmetricResponseCountermodel (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  rw [interiorStripSymmetricResponseCountermodel,
    symmetricJetNullGenerator_nat, mul_zero, add_zero,
    completedBlackHoleJetInterpolation_nat]

theorem interiorStripSymmetricResponseCountermodel_reflection (z : ℂ) :
    interiorStripSymmetricResponseCountermodel (-3 - z) =
      interiorStripSymmetricResponseCountermodel z := by
  rw [interiorStripSymmetricResponseCountermodel,
    interiorStripSymmetricResponseCountermodel,
    completedBlackHoleJetInterpolation_reflection,
    symmetricJetNullGenerator_reflection]

theorem interiorStripSymmetricResponseCountermodel_conj (z : ℂ) :
    interiorStripSymmetricResponseCountermodel ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (interiorStripSymmetricResponseCountermodel z) := by
  rw [interiorStripSymmetricResponseCountermodel,
    interiorStripSymmetricResponseCountermodel, map_add, map_mul,
    completedBlackHoleJetInterpolation_conj,
    symmetricJetNullGenerator_conj, interiorResponseCoefficient_conj]

theorem orderOneEnvelope_interiorStripSymmetricResponseCountermodel :
    OrderOneEnvelope interiorStripSymmetricResponseCountermodel := by
  exact (orderOneEnvelope_completedBlackHoleJetInterpolation.add
    (orderOneEnvelope_symmetricJetNullGenerator.const_mul interiorResponseCoefficient)).congr
      fun z => by rfl

/-- Full natural analytic package proposed as a repair of response-order interpolation:
entireness, all completed physical samples, functional-equation reflection, Schwarz reality, and
the global order-one envelope. -/
def IsCompletedBlackHoleJetAnalyticPackage (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    (∀ m : ℕ, F (m : ℂ) = completedBlackHoleJetSample scaleLog m) ∧
    (∀ z : ℂ, F (-3 - z) = F z) ∧
    (∀ z : ℂ, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z)) ∧
    OrderOneEnvelope F

theorem interiorStripSymmetricResponseCountermodel_package (scaleLog : ℂ) :
    IsCompletedBlackHoleJetAnalyticPackage scaleLog
      interiorStripSymmetricResponseCountermodel := by
  exact ⟨differentiable_interiorStripSymmetricResponseCountermodel,
    interiorStripSymmetricResponseCountermodel_nat scaleLog,
    interiorStripSymmetricResponseCountermodel_reflection,
    interiorStripSymmetricResponseCountermodel_conj,
    orderOneEnvelope_interiorStripSymmetricResponseCountermodel⟩

theorem interiorStripSymmetricResponseCountermodel_ne_canonical :
    interiorStripSymmetricResponseCountermodel ≠ completedBlackHoleJetInterpolation := by
  intro h
  have hv := congrFun h interiorResponsePoint
  rw [interiorStripSymmetricResponseCountermodel_zero] at hv
  exact completedBlackHoleJetInterpolation_interiorResponsePoint_ne_zero hv.symm

/-- **Strengthened completed-response route kill.** There is an entire, order-one, FE-symmetric,
Schwarz-real continuation carrying every completed physical Schwarzschild/FZZ sample, but having a
zero strictly inside the critical strip and off the critical line.  It is not the Xi continuation. -/
theorem completed_response_FE_Schwarz_orderOne_route_noGo (scaleLog : ℂ) :
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      IsCompletedBlackHoleJetAnalyticPackage scaleLog F ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ F z = 0 ∧
      F ≠ completedBlackHoleJetInterpolation := by
  refine ⟨interiorStripSymmetricResponseCountermodel, interiorResponsePoint,
    interiorStripSymmetricResponseCountermodel_package scaleLog, ?_, ?_, ?_,
    interiorStripSymmetricResponseCountermodel_zero,
    interiorStripSymmetricResponseCountermodel_ne_canonical⟩
  all_goals norm_num [interiorResponsePoint]

/-! ## Exact symmetric principal-ideal classification -/

/-- The reflected natural-ladder null generator. -/
def reflectedNaturalJetNullGenerator (z : ℂ) : ℂ :=
  naturalJetNullGenerator (-3 - z)

theorem differentiable_reflectedNaturalJetNullGenerator :
    Differentiable ℂ reflectedNaturalJetNullGenerator := by
  exact differentiable_naturalJetNullGenerator.comp (by fun_prop)

theorem reflectedNaturalJetNullGenerator_eq_zero_iff (z : ℂ) :
    reflectedNaturalJetNullGenerator z = 0 ↔
      ∃ m : ℕ, z = -3 - (m : ℂ) := by
  rw [reflectedNaturalJetNullGenerator, naturalJetNullGenerator_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    linear_combination -hm
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring_nf⟩

theorem analyticOrderAt_reflectedNaturalJetNullGenerator (m : ℕ) :
    analyticOrderAt reflectedNaturalJetNullGenerator (-3 - (m : ℂ)) = 1 := by
  let phi : ℂ → ℂ := fun z => -3 - z
  have hphi : AnalyticAt ℂ phi (-3 - (m : ℂ)) := by fun_prop
  have hderiv : deriv phi (-3 - (m : ℂ)) ≠ 0 := by
    simp [phi]
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := naturalJetNullGenerator) hphi hderiv
  have hpoint : phi (-3 - (m : ℂ)) = (m : ℂ) := by
    simp only [phi]
    ring_nf
  rw [show reflectedNaturalJetNullGenerator = naturalJetNullGenerator ∘ phi by rfl,
    hcomp, hpoint, analyticOrderAt_naturalJetNullGenerator_nat]

theorem symmetricJetNullGenerator_eq_product (z : ℂ) :
    symmetricJetNullGenerator z =
      naturalJetNullGenerator z * reflectedNaturalJetNullGenerator z := by
  rw [symmetricJetNullGenerator, naturalJetNullGenerator,
    reflectedNaturalJetNullGenerator, naturalJetNullGenerator]
  unfold reciprocalGammaEntire
  congr 1
  ring_nf

theorem naturalJetNullGenerator_reflected_nat_ne_zero (m : ℕ) :
    naturalJetNullGenerator (-3 - (m : ℂ)) ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := (naturalJetNullGenerator_eq_zero_iff _).mp hzero
  have hre := congrArg Complex.re hn
  norm_num at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Entire completed response interpolants carrying both reflection symmetries; growth is omitted
here because the exact quotient need not preserve an order-one envelope. -/
def IsEntireCompletedBlackHoleSymmetricInterpolant
    (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧
    (∀ m : ℕ, F (m : ℂ) = completedBlackHoleJetSample scaleLog m) ∧
    (∀ z : ℂ, F (-3 - z) = F z) ∧
    (∀ z : ℂ, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))

/-- **Exact two-ladder principal-ideal classification.** Every entire completed response
interpolant with the Xi functional equation and Schwarz reality, and only such an interpolant, is
the canonical shifted Xi plus the symmetric reciprocal-Gamma generator times an entire quotient
carrying the same two symmetries. -/
theorem isEntireCompletedBlackHoleSymmetricInterpolant_iff_twoLadderGammaNull
    (scaleLog : ℂ) (F : ℂ → ℂ) :
    IsEntireCompletedBlackHoleSymmetricInterpolant scaleLog F ↔
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        (∀ z : ℂ, H (-3 - z) = H z) ∧
        GaloisForLFunctions.RHTower.SchwarzRealGauge H ∧
        ∀ z : ℂ, F z = completedBlackHoleJetInterpolation z +
          H z * symmetricJetNullGenerator z := by
  constructor
  · rintro ⟨hF, hsamples, hreflect, hconj⟩
    let D : ℂ → ℂ := fun z => F z - completedBlackHoleJetInterpolation z
    have hD : Differentiable ℂ D :=
      hF.sub differentiable_completedBlackHoleJetInterpolation
    have hDnat : ∀ m : ℕ, D (m : ℂ) = 0 := by
      intro m
      dsimp only [D]
      rw [hsamples m, completedBlackHoleJetInterpolation_nat scaleLog m]
      ring_nf
    have horderNatural : ∀ z : ℂ,
        analyticOrderAt naturalJetNullGenerator z ≤ analyticOrderAt D z := by
      intro z
      by_cases hz : naturalJetNullGenerator z = 0
      · obtain ⟨m, rfl⟩ := (naturalJetNullGenerator_eq_zero_iff z).mp hz
        rw [analyticOrderAt_naturalJetNullGenerator_nat]
        have hDA : AnalyticAt ℂ D (m : ℂ) :=
          hD.differentiableOn.analyticAt (s := Set.univ) Filter.univ_mem
        exact Order.one_le_iff_ne_zero.mpr (fun hzero => by
          rw [hDA.analyticOrderAt_eq_zero] at hzero
          exact hzero (hDnat m))
      · have hzero : analyticOrderAt naturalJetNullGenerator z = 0 :=
          (differentiable_naturalJetNullGenerator.differentiableOn.analyticAt
            (s := Set.univ) Filter.univ_mem).analyticOrderAt_eq_zero.mpr hz
        rw [hzero]
        exact bot_le
    obtain ⟨Q, hQ, hDQ⟩ := exists_entire_quotient hD
      differentiable_naturalJetNullGenerator
      ⟨-1, by simp [naturalJetNullGenerator_neg_one]⟩ horderNatural
    have horderReflected : ∀ z : ℂ,
        analyticOrderAt reflectedNaturalJetNullGenerator z ≤ analyticOrderAt Q z := by
      intro z
      by_cases hz : reflectedNaturalJetNullGenerator z = 0
      · obtain ⟨m, rfl⟩ := (reflectedNaturalJetNullGenerator_eq_zero_iff z).mp hz
        rw [analyticOrderAt_reflectedNaturalJetNullGenerator]
        have hDzero : D (-3 - (m : ℂ)) = 0 := by
          dsimp only [D]
          rw [hreflect (m : ℂ), completedBlackHoleJetInterpolation_reflection]
          exact hDnat m
        have hQzero : Q (-3 - (m : ℂ)) = 0 := by
          have hfactor := hDQ (-3 - (m : ℂ))
          rw [hDzero] at hfactor
          exact (mul_eq_zero.mp hfactor.symm).resolve_right
            (naturalJetNullGenerator_reflected_nat_ne_zero m)
        have hQA : AnalyticAt ℂ Q (-3 - (m : ℂ)) :=
          hQ.differentiableOn.analyticAt (s := Set.univ) Filter.univ_mem
        exact Order.one_le_iff_ne_zero.mpr (fun hzero => by
          rw [hQA.analyticOrderAt_eq_zero] at hzero
          exact hzero hQzero)
      · have hzero : analyticOrderAt reflectedNaturalJetNullGenerator z = 0 :=
          (differentiable_reflectedNaturalJetNullGenerator.differentiableOn.analyticAt
            (s := Set.univ) Filter.univ_mem).analyticOrderAt_eq_zero.mpr hz
        rw [hzero]
        exact bot_le
    have hreflectedNonzero :
        reflectedNaturalJetNullGenerator interiorResponsePoint ≠ 0 := by
      intro hzero
      apply symmetricJetNullGenerator_interiorResponsePoint_ne_zero
      rw [symmetricJetNullGenerator_eq_product, hzero, mul_zero]
    obtain ⟨H, hH, hQH⟩ := exists_entire_quotient hQ
      differentiable_reflectedNaturalJetNullGenerator
      ⟨interiorResponsePoint, hreflectedNonzero⟩ horderReflected
    have hDK : ∀ z : ℂ, D z = H z * symmetricJetNullGenerator z := by
      intro z
      rw [hDQ z, hQH z, symmetricJetNullGenerator_eq_product]
      ring_nf
    have hKfun : symmetricJetNullGenerator ≠ 0 := by
      intro hzero
      exact symmetricJetNullGenerator_interiorResponsePoint_ne_zero
        (congrFun hzero interiorResponsePoint)
    have hDreflect : ∀ z : ℂ, D (-3 - z) = D z := by
      intro z
      dsimp only [D]
      rw [hreflect, completedBlackHoleJetInterpolation_reflection]
    let R : ℂ → ℂ := fun z => H (-3 - z) - H z
    have hR : Differentiable ℂ R := (hH.comp (by fun_prop)).sub hH
    have hRprod : (fun z => R z * symmetricJetNullGenerator z) = 0 := by
      funext z
      have hz := hDreflect z
      rw [hDK, hDK, symmetricJetNullGenerator_reflection] at hz
      dsimp only [R]
      rw [sub_mul, hz, sub_self]
      simp only [Pi.zero_apply]
    have hRzero : R = 0 := by
      by_contra hRne
      exact (differentiable_mul_ne_zero hR
        differentiable_symmetricJetNullGenerator hRne hKfun) hRprod
    have hHref : ∀ z : ℂ, H (-3 - z) = H z := by
      intro z
      exact sub_eq_zero.mp (congrFun hRzero z)
    have hDconj : ∀ z : ℂ,
        D ((starRingEnd ℂ) z) = (starRingEnd ℂ) (D z) := by
      intro z
      dsimp only [D]
      rw [hconj, completedBlackHoleJetInterpolation_conj, map_sub]
    let S : ℂ → ℂ := fun z =>
      (starRingEnd ℂ) (H ((starRingEnd ℂ) z)) - H z
    have hS : Differentiable ℂ S := (differentiable_conj_reflect hH).sub hH
    have hSprod : (fun z => S z * symmetricJetNullGenerator z) = 0 := by
      funext z
      have hz := congrArg (starRingEnd ℂ) (hDK ((starRingEnd ℂ) z))
      rw [map_mul, hDconj, Complex.conj_conj,
        symmetricJetNullGenerator_conj, Complex.conj_conj] at hz
      rw [hDK] at hz
      dsimp only [S]
      rw [sub_mul, hz, sub_self]
      simp only [Pi.zero_apply]
    have hSzero : S = 0 := by
      by_contra hSne
      exact (differentiable_mul_ne_zero hS
        differentiable_symmetricJetNullGenerator hSne hKfun) hSprod
    have hHschwarz : GaloisForLFunctions.RHTower.SchwarzRealGauge H := by
      intro z
      exact sub_eq_zero.mp (congrFun hSzero z)
    refine ⟨H, hH, hHref, hHschwarz, fun z => ?_⟩
    have hz := hDK z
    dsimp only [D] at hz
    rw [← hz]
    ring_nf
  · rintro ⟨H, hH, hreflect, hschwarz, hfactor⟩
    have hHconj : ∀ z : ℂ,
        H ((starRingEnd ℂ) z) = (starRingEnd ℂ) (H z) := by
      intro z
      have hz := hschwarz ((starRingEnd ℂ) z)
      rw [GaloisForLFunctions.RHTower.suzukiEntireSharp] at hz
      simpa only [Complex.conj_conj] using hz.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show F = fun z => completedBlackHoleJetInterpolation z +
          H z * symmetricJetNullGenerator z from funext hfactor]
      exact differentiable_completedBlackHoleJetInterpolation.add
        (hH.mul differentiable_symmetricJetNullGenerator)
    · intro m
      rw [hfactor, symmetricJetNullGenerator_nat, mul_zero, add_zero,
        completedBlackHoleJetInterpolation_nat]
    · intro z
      rw [hfactor, hfactor, completedBlackHoleJetInterpolation_reflection,
        hreflect, symmetricJetNullGenerator_reflection]
    · intro z
      rw [hfactor, hfactor, map_add, map_mul,
        completedBlackHoleJetInterpolation_conj, hHconj,
        symmetricJetNullGenerator_conj]

end RHTower
