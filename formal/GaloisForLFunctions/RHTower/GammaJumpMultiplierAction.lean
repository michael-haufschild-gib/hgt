import GaloisForLFunctions.RHTower.GammaJumpBinetFormula

/-!
# The jump operator acts by its multiplier

On a character `e^{iLa}` the second difference of the jump operator is `(2 − 2cos(as))` times the
character, so the Binet formula makes the operator act by multiplication by `r(a)`.  On a
superposition of characters it therefore inserts `r` under the integral sign.

The interchange is Fubini in the order *frequency first, scale second*: in the other order the
`s`-integral of the crude bound diverges at the origin, since the Laplace weight is `~1/s` there.
Taking the frequency outside makes the inner integral the exact multiplier `r(a)`, and the outer one
converges precisely when `r·ν` is integrable — which is the hypothesis.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The physical Gamma jump operator `(26)`. -/
def gammaJumpOperator (F : ℝ → X) (L : ℝ) : X :=
  ∫ s in Ioi (0 : ℝ), _root_.RHTower.gammaJumpWeight s •
    ((2 : ℝ) • F L - F (L + s) - F (L - s))

/-- The character of frequency `a`, as a function of position. -/
def freqChar (a L : ℝ) : ℂ := Complex.exp (Complex.I * (L : ℂ) * (a : ℂ))

theorem norm_freqChar (a L : ℝ) : ‖freqChar a L‖ = 1 := by
  rw [freqChar, Complex.norm_exp]
  have h : (Complex.I * (L : ℂ) * (a : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

omit [CompleteSpace X] in
/-- The second difference of a character is its `(2 − 2cos)` multiple. -/
theorem freqChar_secondDifference (a L s : ℝ) (v : X) :
    (2 : ℝ) • (freqChar a L • v) - freqChar a (L + s) • v - freqChar a (L - s) • v
      = (2 - 2 * Real.cos (a * s)) • (freqChar a L • v) := by
  have hadd : freqChar a (L + s) = freqChar a L * Complex.exp (Complex.I * (s : ℂ) * (a : ℂ)) := by
    rw [freqChar, freqChar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsub : freqChar a (L - s) = freqChar a L * Complex.exp (-(Complex.I * (s : ℂ) * (a : ℂ))) := by
    rw [freqChar, freqChar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcos : Complex.exp (Complex.I * (s : ℂ) * (a : ℂ))
      + Complex.exp (-(Complex.I * (s : ℂ) * (a : ℂ))) = 2 * (Real.cos (a * s) : ℂ) := by
    have h : (Complex.I * (s : ℂ) * (a : ℂ)) = ((a * s : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h]
    have hc : ((Real.cos (a * s) : ℝ) : ℂ) = Complex.cos ((a * s : ℝ) : ℂ) :=
      Complex.ofReal_cos (a * s)
    rw [hc, Complex.cos, show (-((a * s : ℝ) : ℂ)) * Complex.I
      = -(((a * s : ℝ) : ℂ) * Complex.I) by ring]
    ring
  have hR : ∀ (r : ℝ) (w : X), r • w = (r : ℂ) • w := fun r w => (Complex.coe_smul r w).symm
  rw [hadd, hsub, hR 2, hR (2 - 2 * Real.cos (a * s))]
  simp only [smul_smul, ← sub_smul]
  congr 1
  push_cast
  rw [Complex.cos, show ((a : ℂ) * (s : ℂ)) * Complex.I = Complex.I * (s : ℂ) * (a : ℂ) by ring,
    show (-((a : ℂ) * (s : ℂ))) * Complex.I = -(Complex.I * (s : ℂ) * (a : ℂ)) by ring]
  ring

/-- **The jump operator acts on a character by its multiplier.** -/
theorem gammaJumpOperator_freqChar (a L : ℝ) (v : X) :
    gammaJumpOperator (fun M => freqChar a M • v) L
      = gammaJumpMultiplier a • (freqChar a L • v) := by
  rw [gammaJumpOperator]
  have hpt : ∀ s ∈ Ioi (0 : ℝ), _root_.RHTower.gammaJumpWeight s •
      ((2 : ℝ) • (freqChar a L • v) - freqChar a (L + s) • v - freqChar a (L - s) • v)
      = (_root_.RHTower.gammaJumpWeight s * (2 - 2 * Real.cos (a * s))) • (freqChar a L • v) := by
    intro s _
    rw [freqChar_secondDifference, smul_smul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_smul_const]
  congr 1
  rw [← integral_jumpBinet a]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

/-- The character superposition of a frequency density. -/
def freqSuperposition (ν : ℝ → X) (L : ℝ) : X := ∫ a : ℝ, freqChar a L • ν a

omit [CompleteSpace X] in
theorem integrable_freqChar_smul {ν : ℝ → X} (hν : Integrable ν) (M : ℝ) :
    Integrable fun a : ℝ => freqChar a M • ν a := by
  have hmeas : AEStronglyMeasurable (fun a : ℝ => freqChar a M • ν a) volume := by
    have hc : Continuous fun a : ℝ => freqChar a M := by
      unfold freqChar
      fun_prop
    exact hc.aestronglyMeasurable.smul hν.aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  have heq : ∀ a : ℝ, ‖freqChar a M • ν a‖ₑ = ‖ν a‖ₑ := by
    intro a
    rw [← ofReal_norm, ← ofReal_norm, norm_smul, norm_freqChar, one_mul]
  rw [hasFiniteIntegral_iff_enorm, lintegral_congr heq, ← hasFiniteIntegral_iff_enorm]
  exact hν.hasFiniteIntegral

/-- **The jump operator acts on a superposition by inserting its multiplier.** -/
theorem gammaJumpOperator_freqSuperposition {ν : ℝ → X} (hν : Integrable ν)
    (hrν : Integrable fun a : ℝ => gammaJumpMultiplier a • ν a) (L : ℝ) :
    gammaJumpOperator (freqSuperposition ν) L
      = ∫ a : ℝ, gammaJumpMultiplier a • (freqChar a L • ν a) := by
  set f : ℝ → ℝ → X := fun a s =>
    ((2 - 2 * Real.cos (a * s)) * _root_.RHTower.gammaJumpWeight s) • (freqChar a L • ν a)
    with hfdef
  -- the pointwise norm
  have hnormf : ∀ a s : ℝ, s ∈ Ioi (0 : ℝ) →
      ‖f a s‖ = ((2 - 2 * Real.cos (a * s)) * _root_.RHTower.gammaJumpWeight s) * ‖ν a‖ := by
    intro a s hs
    have hw : 0 < _root_.RHTower.gammaJumpWeight s := _root_.RHTower.gammaJumpWeight_pos hs
    have hc : Real.cos (a * s) ≤ 1 := Real.cos_le_one _
    rw [hfdef, norm_smul, norm_smul, norm_freqChar, one_mul, Real.norm_of_nonneg (by nlinarith)]
  -- the inner integral in s
  have hinner : ∀ a : ℝ, (∫ s in Ioi (0 : ℝ), f a s)
      = gammaJumpMultiplier a • (freqChar a L • ν a) := by
    intro a
    rw [hfdef, integral_smul_const, integral_jumpBinet a]
  -- integrability of the uncurried integrand
  have hmeasf : AEStronglyMeasurable (Function.uncurry f)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hs : Measurable fun p : ℝ × ℝ =>
        (2 - 2 * Real.cos (p.1 * p.2)) * _root_.RHTower.gammaJumpWeight p.2 := by
      have h1 : Measurable fun p : ℝ × ℝ => 2 - 2 * Real.cos (p.1 * p.2) := by fun_prop
      have h2 : Measurable fun p : ℝ × ℝ => _root_.RHTower.gammaJumpWeight p.2 := by
        unfold _root_.RHTower.gammaJumpWeight
        fun_prop
      exact h1.mul h2
    have hv : AEStronglyMeasurable (fun p : ℝ × ℝ => freqChar p.1 L • ν p.1)
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (integrable_freqChar_smul hν L).aestronglyMeasurable.comp_fst
    exact hs.aestronglyMeasurable.smul hv
  have hnormint : ∀ a : ℝ, (∫ s in Ioi (0 : ℝ), ‖f a s‖) = gammaJumpMultiplier a * ‖ν a‖ := by
    intro a
    rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => hnormf a s hs),
      integral_mul_const, integral_jumpBinet a]
  have hprod : Integrable (Function.uncurry f)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [MeasureTheory.integrable_prod_iff hmeasf]
    refine ⟨Filter.Eventually.of_forall fun a => ?_, ?_⟩
    · exact (integrableOn_jumpBinetIntegrand a).smul_const (freqChar a L • ν a)
    · refine (hrν.norm).congr (Filter.Eventually.of_forall fun a => ?_)
      show ‖gammaJumpMultiplier a • ν a‖ = ∫ s in Ioi (0 : ℝ), ‖f a s‖
      rw [norm_smul, Real.norm_of_nonneg (gammaJumpMultiplier_nonneg a), ← hnormint a]
  have hswap := MeasureTheory.integral_integral_swap hprod
  -- the second difference of the superposition
  have hstep : ∀ s ∈ Ioi (0 : ℝ),
      _root_.RHTower.gammaJumpWeight s • ((2 : ℝ) • freqSuperposition ν L
        - freqSuperposition ν (L + s) - freqSuperposition ν (L - s)) = ∫ a : ℝ, f a s := by
    intro s _
    have hI0 : Integrable (fun a : ℝ => freqChar a L • ν a) volume :=
      integrable_freqChar_smul hν L
    have hIp : Integrable (fun a : ℝ => freqChar a (L + s) • ν a) volume :=
      integrable_freqChar_smul hν (L + s)
    have hIm : Integrable (fun a : ℝ => freqChar a (L - s) • ν a) volume :=
      integrable_freqChar_smul hν (L - s)
    have hIA : Integrable (fun a : ℝ => (2 : ℝ) • (freqChar a L • ν a)) volume :=
      Integrable.smul (2 : ℝ) hI0
    have hIB : Integrable
        (fun a : ℝ => (2 : ℝ) • (freqChar a L • ν a) - freqChar a (L + s) • ν a) volume :=
      hIA.sub hIp
    have h1 : (∫ a : ℝ, ((2 : ℝ) • (freqChar a L • ν a) - freqChar a (L + s) • ν a
            - freqChar a (L - s) • ν a))
        = (2 : ℝ) • freqSuperposition ν L - freqSuperposition ν (L + s)
          - freqSuperposition ν (L - s) := by
      rw [integral_sub hIB hIm, integral_sub hIA hIp, integral_smul]
      rfl
    rw [← h1, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    show _root_.RHTower.gammaJumpWeight s • ((2 : ℝ) • (freqChar a L • ν a)
        - freqChar a (L + s) • ν a - freqChar a (L - s) • ν a)
      = ((2 - 2 * Real.cos (a * s)) * _root_.RHTower.gammaJumpWeight s) • (freqChar a L • ν a)
    rw [freqChar_secondDifference, smul_smul]
    congr 1
    ring
  rw [gammaJumpOperator, setIntegral_congr_fun measurableSet_Ioi hstep, ← hswap]
  exact integral_congr_ae (Filter.Eventually.of_forall hinner)

end GaloisForLFunctions.RHTower
