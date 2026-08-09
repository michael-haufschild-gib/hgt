import GaloisForLFunctions.HTGeometry.MeroExponentialGauge
import GaloisForLFunctions.HTGeometry.FiniteNomeSectionSchemeGauge
import GaloisForLFunctions.HTGeometry.BankOddExponentDichotomy
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaValues

/-!
# The genus gauge does not move the differential phase of a finite section

A finite section of the canonical product is entire, and raising its genus multiplies it by the
exponential of a polynomial in the exponential coordinate whose coefficients are the finite Euler
products of the nome set.  That exponent is differentially algebraic over the rational coordinate
field, so its exponential is a nowhere-zero differentially algebraic gauge.

Consequently the finite section at any genus and the finite section at genus zero lie in the same
differential phase, both as functions and through their logarithmic derivatives: whichever of them
is differentially algebraic, both are, and whichever is hypertranscendental, both are.
-/

open Set Complex Filter
open scoped Differential BigOperators

noncomputable section

namespace HTGeometry

/-- A finite section is entire. -/
theorem analyticOnNhd_finiteNomeSection {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) :
    AnalyticOnNhd ℂ (finiteNomeSection g p S) (Set.univ : Set ℂ) := by
  have h : finiteNomeSection g p S
      = infiniteMultipleEllipticGamma g (fun a : S => p a) := by
    funext t
    exact finiteNomeSection_eq_restricted g p S t
  rw [h]
  exact infiniteMultipleEllipticGamma_analytic g (fun a : S => p a)
    (fun a => hp_ne a) (fun a => hp_lt a) Summable.of_finite

/-- The coefficient of the genus gauge at order `k + 1`. -/
def gaugeCoefficient {ι : Type*} (p : ι → ℂ) (S : Finset ι) (k : ℕ) : ℂ :=
  (∏ a ∈ S, (1 - p a ^ (k + 1))⁻¹) / ((k + 1 : ℕ) : ℂ)

theorem finiteSectionGauge_eq_sum {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (t : ℂ) :
    finiteSectionGauge g p S t = ∑ k ∈ Finset.range g, gaugeCoefficient p S k * t ^ (k + 1) := by
  rw [finiteSectionGauge]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gaugeCoefficient]
  ring

@[simp] theorem finiteNomeSection_at_zero {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) :
    finiteNomeSection g p S 0 = 1 := by
  rw [finiteNomeSection_eq_restricted, infiniteMultipleEllipticGamma_at_zero]

/-- A finite section is nonzero somewhere off the origin: it equals one at the origin. -/
theorem exists_finiteNomeSection_ne_zero {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) :
    ∃ t : ℂ, t ≠ 0 ∧ finiteNomeSection g p S t ≠ 0 := by
  have hcont : ContinuousAt (finiteNomeSection g p S) 0 :=
    ((analyticOnNhd_finiteNomeSection g p hp_ne hp_lt S) 0 (Set.mem_univ 0)).continuousAt
  have hev : ∀ᶠ t in nhds (0 : ℂ), finiteNomeSection g p S t ≠ 0 :=
    hcont.eventually_ne (by rw [finiteNomeSection_at_zero]; exact one_ne_zero)
  have h2 : ∀ᶠ t in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ,
      finiteNomeSection g p S t ≠ 0 ∧ t ≠ 0 := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ha hb
    exact ⟨ha, hb⟩
  obtain ⟨t, ht⟩ := h2.exists
  exact ⟨t, ht.2, ht.1⟩

end HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

variable {ι : Type*}

/-- The gauge exponent, read in an exponential coordinate with a scale. -/
def gaugeExponent (g : ℕ) (p : ι → ℂ) (S : Finset ι) (b c : ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range g,
    (_root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1)) * Complex.exp (c * z) ^ (k + 1)

theorem analyticOnNhd_gaugeExponentTerm (p : ι → ℂ) (S : Finset ι) (b c : ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        (_root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1)) * Complex.exp (c * z) ^ (k + 1))
      (Set.univ : Set ℂ) :=
  analyticOnNhd_const.mul ((analyticOnNhd_expLinear c).pow _)

theorem analyticOnNhd_gaugeExponent (g : ℕ) (p : ι → ℂ) (S : Finset ι) (b c : ℂ) :
    AnalyticOnNhd ℂ (gaugeExponent g p S b c) (Set.univ : Set ℂ) := by
  classical
  have hpi : gaugeExponent g p S b c
      = ∑ k ∈ Finset.range g,
          fun z : ℂ =>
            (_root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1)) *
              Complex.exp (c * z) ^ (k + 1) := by
    funext z
    rw [gaugeExponent, Finset.sum_apply]
  rw [hpi]
  exact Finset.sum_induction _ (fun h => AnalyticOnNhd ℂ h (Set.univ : Set ℂ))
    (fun a b ha hb => ha.add hb) analyticOnNhd_const
    (fun k _ => analyticOnNhd_gaugeExponentTerm p S b c k)

/-- **The gauge exponent is differentially algebraic over the rational coordinate field.** -/
theorem differentialAlgebraicOver_gaugeExponent (g : ℕ) (p : ι → ℂ) (S : Finset ι) (b c : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (gaugeExponent g p S b c) (analyticOnNhd_gaugeExponent g p S b c)) := by
  classical
  have hsplit :
      analyticMeroElement (gaugeExponent g p S b c) (analyticOnNhd_gaugeExponent g p S b c)
      = ∑ k ∈ Finset.range g,
          analyticMeroElement
            (fun z : ℂ =>
              (_root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1)) *
                Complex.exp (c * z) ^ (k + 1))
            (analyticOnNhd_gaugeExponentTerm p S b c k) :=
    analyticMeroElement_finsetSum (Finset.range g) _
      (fun k => analyticOnNhd_gaugeExponentTerm p S b c k) (analyticOnNhd_gaugeExponent g p S b c)
  rw [hsplit]
  refine _root_.HTGeometry.differentialAlgebraicOver_finset_sum _ _ fun k _ => ?_
  have hterm : analyticMeroElement
      (fun z : ℂ =>
        (_root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1)) * Complex.exp (c * z) ^ (k + 1))
      (analyticOnNhd_gaugeExponentTerm p S b c k)
      = analyticMeroElement
          (fun _ : ℂ => _root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1))
          analyticOnNhd_const *
        analyticMeroElement (fun z : ℂ => Complex.exp (c * z)) (analyticOnNhd_expLinear c) ^
          (k + 1) := by
    have e1 : analyticMeroElement
        (fun z : ℂ =>
          (_root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1)) * Complex.exp (c * z) ^ (k + 1))
        (analyticOnNhd_gaugeExponentTerm p S b c k)
        = analyticMeroElement
            (fun _ : ℂ => _root_.HTGeometry.gaugeCoefficient p S k * b ^ (k + 1))
            analyticOnNhd_const *
          analyticMeroElement (fun z : ℂ => Complex.exp (c * z) ^ (k + 1))
            ((analyticOnNhd_expLinear c).pow (k + 1)) :=
      analyticMeroElement_mul analyticOnNhd_const ((analyticOnNhd_expLinear c).pow (k + 1))
    rw [e1, analyticMeroElement_pow (analyticOnNhd_expLinear c) (k + 1)]
  rw [hterm]
  refine differentialAlgebraicOver_mul ?_
    (differentialAlgebraicOver_pow
      (differentialAlgebraicOver_analyticMeroElement_expLinear c) (k + 1))
  rw [← algebraMap_ratFunc_C_eq]
  exact differentialAlgebraicOver_algebraMap _

theorem analyticOnNhd_finiteNomeSection_expLinear (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0)
    (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b c : ℂ) :
    AnalyticOnNhd ℂ
      (fun z : ℂ => _root_.HTGeometry.finiteNomeSection g p S (b * Complex.exp (c * z)))
      (Set.univ : Set ℂ) :=
  (_root_.HTGeometry.analyticOnNhd_finiteNomeSection g p hp_ne hp_lt S).comp
    (analyticOnNhd_const.mul (analyticOnNhd_expLinear c)) (Set.mapsTo_univ _ _)

/-- A finite section read in an exponential coordinate with a scale, as an element of the
meromorphic field.  The scale carries both branches of the parity assembly: the direct coordinate
is the scale one, and the reciprocal branch is the nome product with the opposite rate. -/
def finiteSectionMero (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (S : Finset ι) (b c : ℂ) : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement
    (fun z : ℂ => _root_.HTGeometry.finiteNomeSection g p S (b * Complex.exp (c * z)))
    (analyticOnNhd_finiteNomeSection_expLinear g p hp_ne hp_lt S b c)

/-- **The finite section is its genus-zero form times an exponential gauge.** -/
theorem finiteSectionMero_eq (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (S : Finset ι) (b c : ℂ) :
    finiteSectionMero g p hp_ne hp_lt S b c
      = finiteSectionMero 0 p hp_ne hp_lt S b c *
        analyticMeroElement (fun z : ℂ => Complex.exp (gaugeExponent g p S b c z))
          (analyticOnNhd_gaugeExponent g p S b c).cexp := by
  rw [finiteSectionMero, finiteSectionMero,
    ← analyticMeroElement_mul
      (analyticOnNhd_finiteNomeSection_expLinear 0 p hp_ne hp_lt S b c)
      (analyticOnNhd_gaugeExponent g p S b c).cexp]
  refine analyticMeroElement_congr _ _ ?_
  funext z
  rw [_root_.HTGeometry.finiteNomeSection_eq_zero_genus_mul_gauge g p hp_ne hp_lt S,
    gaugeExponent, _root_.HTGeometry.finiteSectionGauge_eq_sum]
  refine congrArg _ (congrArg Complex.exp (Finset.sum_congr rfl fun k _ => ?_))
  rw [mul_pow]
  ring

/-- **The genus gauge preserves the differentially algebraic phase of a finite section.** -/
theorem differentialAlgebraicOver_finiteSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b c : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (finiteSectionMero g p hp_ne hp_lt S b c)
      ↔ DifferentialAlgebraicOver (RatFunc ℂ) (finiteSectionMero 0 p hp_ne hp_lt S b c) := by
  rw [finiteSectionMero_eq g p hp_ne hp_lt S b c]
  exact differentialAlgebraicOver_mul_analyticMeroElement_exp_iff _ _
    (analyticOnNhd_gaugeExponent g p S b c) (differentialAlgebraicOver_gaugeExponent g p S b c)

/-- **The genus gauge preserves the hypertranscendental phase of a finite section.** -/
theorem hypertranscendentalOver_finiteSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b c : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (finiteSectionMero g p hp_ne hp_lt S b c)
      ↔ HypertranscendentalOver (RatFunc ℂ) (finiteSectionMero 0 p hp_ne hp_lt S b c) := by
  rw [finiteSectionMero_eq g p hp_ne hp_lt S b c]
  exact hypertranscendentalOver_mul_analyticMeroElement_exp_iff _ _
    (analyticOnNhd_gaugeExponent g p S b c) (differentialAlgebraicOver_gaugeExponent g p S b c)

/-- A finite section read in a nondegenerate exponential coordinate is a nonzero field element. -/
theorem finiteSectionMero_ne_zero (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0)
    (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) {b c : ℂ} (hb : b ≠ 0) (hc : c ≠ 0) :
    finiteSectionMero g p hp_ne hp_lt S b c ≠ 0 := by
  rw [finiteSectionMero, Ne, analyticMeroElement_eq_zero_iff]
  intro h
  obtain ⟨t, ht0, htne⟩ :=
    _root_.HTGeometry.exists_finiteNomeSection_ne_zero g p hp_ne hp_lt S
  have hz : b * Complex.exp (c * (Complex.log (t / b) / c)) = t := by
    rw [show c * (Complex.log (t / b) / c) = Complex.log (t / b) by field_simp,
      Complex.exp_log (div_ne_zero ht0 hb)]
    field_simp
  refine htne ?_
  rw [← hz]
  exact h _ (Set.mem_univ _)

/-- **The genus gauge preserves the differentially algebraic phase of the logarithmic derivative of
a finite section.** -/
theorem differentialAlgebraicOver_logDeriv_finiteSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) {b c : ℂ} (hb : b ≠ 0)
    (hc : c ≠ 0) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        ((finiteSectionMero g p hp_ne hp_lt S b c)′ / finiteSectionMero g p hp_ne hp_lt S b c)
      ↔ DifferentialAlgebraicOver (RatFunc ℂ)
        ((finiteSectionMero 0 p hp_ne hp_lt S b c)′ / finiteSectionMero 0 p hp_ne hp_lt S b c) := by
  rw [finiteSectionMero_eq g p hp_ne hp_lt S b c]
  exact differentialAlgebraicOver_logDeriv_mul_iff_of_expGauge
    (differentialAlgebraicOver_gaugeExponent g p S b c)
    (deriv_analyticMeroElement_exp _ (analyticOnNhd_gaugeExponent g p S b c))
    (finiteSectionMero_ne_zero 0 p hp_ne hp_lt S hb hc)
    (analyticMeroElement_exp_ne_zero _ (analyticOnNhd_gaugeExponent g p S b c))

/-- **The genus gauge preserves the hypertranscendental phase of the logarithmic derivative of a
finite section.** -/
theorem hypertranscendentalOver_logDeriv_finiteSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) {b c : ℂ} (hb : b ≠ 0)
    (hc : c ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
        ((finiteSectionMero g p hp_ne hp_lt S b c)′ / finiteSectionMero g p hp_ne hp_lt S b c)
      ↔ HypertranscendentalOver (RatFunc ℂ)
        ((finiteSectionMero 0 p hp_ne hp_lt S b c)′ / finiteSectionMero 0 p hp_ne hp_lt S b c) := by
  rw [finiteSectionMero_eq g p hp_ne hp_lt S b c]
  exact hypertranscendentalOver_logDeriv_mul_iff_of_expGauge
    (differentialAlgebraicOver_gaugeExponent g p S b c)
    (deriv_analyticMeroElement_exp _ (analyticOnNhd_gaugeExponent g p S b c))
    (finiteSectionMero_ne_zero 0 p hp_ne hp_lt S hb hc)
    (analyticMeroElement_exp_ne_zero _ (analyticOnNhd_gaugeExponent g p S b c))

/-! ## The parity assembly -/

/-- **The two-branch assembly differs from its genus-zero form by one exponential gauge.** -/
theorem assembledSectionMero_eq (g : ℕ) (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0)
    (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b₁ c₁ b₂ c₂ : ℂ) :
    finiteSectionMero g p hp_ne hp_lt S b₁ c₁ * finiteSectionMero g p hp_ne hp_lt S b₂ c₂
      = (finiteSectionMero 0 p hp_ne hp_lt S b₁ c₁ * finiteSectionMero 0 p hp_ne hp_lt S b₂ c₂) *
        analyticMeroElement
          (fun z : ℂ => Complex.exp (gaugeExponent g p S b₁ c₁ z + gaugeExponent g p S b₂ c₂ z))
          ((analyticOnNhd_gaugeExponent g p S b₁ c₁).add
            (analyticOnNhd_gaugeExponent g p S b₂ c₂)).cexp := by
  rw [finiteSectionMero_eq g p hp_ne hp_lt S b₁ c₁, finiteSectionMero_eq g p hp_ne hp_lt S b₂ c₂,
    ← analyticMeroElement_exp_add _ _ (analyticOnNhd_gaugeExponent g p S b₁ c₁)
      (analyticOnNhd_gaugeExponent g p S b₂ c₂)]
  ring

/-- **The genus gauge preserves the differentially algebraic phase of the two-branch assembly.**
The parity power is then irrelevant, since inversion preserves both phases. -/
theorem differentialAlgebraicOver_assembledSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b₁ c₁ b₂ c₂ : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (finiteSectionMero g p hp_ne hp_lt S b₁ c₁ * finiteSectionMero g p hp_ne hp_lt S b₂ c₂)
      ↔ DifferentialAlgebraicOver (RatFunc ℂ)
        (finiteSectionMero 0 p hp_ne hp_lt S b₁ c₁ *
          finiteSectionMero 0 p hp_ne hp_lt S b₂ c₂) := by
  rw [assembledSectionMero_eq g p hp_ne hp_lt S b₁ c₁ b₂ c₂]
  exact differentialAlgebraicOver_mul_analyticMeroElement_exp_iff _ _
    ((analyticOnNhd_gaugeExponent g p S b₁ c₁).add (analyticOnNhd_gaugeExponent g p S b₂ c₂))
    (by
      have h := differentialAlgebraicOver_add
        (differentialAlgebraicOver_gaugeExponent g p S b₁ c₁)
        (differentialAlgebraicOver_gaugeExponent g p S b₂ c₂)
      rwa [← analyticMeroElement_add (analyticOnNhd_gaugeExponent g p S b₁ c₁)
        (analyticOnNhd_gaugeExponent g p S b₂ c₂)] at h)

/-- **The genus gauge preserves the hypertranscendental phase of the two-branch assembly.** -/
theorem hypertranscendentalOver_assembledSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b₁ c₁ b₂ c₂ : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (finiteSectionMero g p hp_ne hp_lt S b₁ c₁ * finiteSectionMero g p hp_ne hp_lt S b₂ c₂)
      ↔ HypertranscendentalOver (RatFunc ℂ)
        (finiteSectionMero 0 p hp_ne hp_lt S b₁ c₁ *
          finiteSectionMero 0 p hp_ne hp_lt S b₂ c₂) := by
  rw [assembledSectionMero_eq g p hp_ne hp_lt S b₁ c₁ b₂ c₂]
  exact hypertranscendentalOver_mul_analyticMeroElement_exp_iff _ _
    ((analyticOnNhd_gaugeExponent g p S b₁ c₁).add (analyticOnNhd_gaugeExponent g p S b₂ c₂))
    (by
      have h := differentialAlgebraicOver_add
        (differentialAlgebraicOver_gaugeExponent g p S b₁ c₁)
        (differentialAlgebraicOver_gaugeExponent g p S b₂ c₂)
      rwa [← analyticMeroElement_add (analyticOnNhd_gaugeExponent g p S b₁ c₁)
        (analyticOnNhd_gaugeExponent g p S b₂ c₂)] at h)

/-- **The parity power is irrelevant.**  Inversion preserves the hypertranscendental phase, so the
parity-normalized assembly transfers exactly as the assembly does. -/
theorem hypertranscendentalOver_inv_assembledSectionMero_iff (g : ℕ) (p : ι → ℂ)
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) (b₁ c₁ b₂ c₂ : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (finiteSectionMero g p hp_ne hp_lt S b₁ c₁ * finiteSectionMero g p hp_ne hp_lt S b₂ c₂)⁻¹
      ↔ HypertranscendentalOver (RatFunc ℂ)
        (finiteSectionMero 0 p hp_ne hp_lt S b₁ c₁ *
          finiteSectionMero 0 p hp_ne hp_lt S b₂ c₂)⁻¹ := by
  rw [hypertranscendentalOver_inv_iff, hypertranscendentalOver_inv_iff]
  exact hypertranscendentalOver_assembledSectionMero_iff g p hp_ne hp_lt S b₁ c₁ b₂ c₂

end GaloisForLFunctions.HTGeometry

end
