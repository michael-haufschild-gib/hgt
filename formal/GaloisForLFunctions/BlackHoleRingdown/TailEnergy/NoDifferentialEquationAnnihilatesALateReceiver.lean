import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.RegularityAndReceiverEquivalence
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Roots

/-!
# No constant-coefficient differential equation annihilates a late receiver

Every nonzero differential polynomial in the reflected field has strictly
positive energy on each late half-line. The operator acts on the input
by the same polynomial in time differentiation. On the Fourier line its
multiplier has only finitely many zeros, and strict tail positivity then
applies to the transformed compact input.
-/

noncomputable section
open MeasureTheory Set Filter Complex Polynomial Finset
open scoped Polynomial
namespace GaloisForLFunctions.BlackHoleRingdown

/-- All receiver derivatives are reflected derivatives of the compact input. -/
theorem receiver_iterated_deriv (h : CompactPulse) (n : ℕ) :
    iteratedDeriv n (pulseReflected h) = pulseReflected (CompactPulse.iterD n h) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,CompactPulse.iterD_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun t => (hasDerivAt_pulseReflected _ t).deriv

/-- Applying a polynomial in the time derivative to a receiver. -/
def receiverDifferentialReading (P : ℂ[X]) (h : CompactPulse) (t : ℝ) : ℂ :=
  ∑ j ∈ P.support, P.coeff j*iteratedDeriv j (pulseReflected h) t

/-- Evaluation of a constant-coefficient differential operator is linear in
the polynomial, including at receiver zeros. -/
def receiverJetFunctional (h : CompactPulse) (t : ℝ) : ℂ[X] →ₗ[ℂ] ℂ :=
  Polynomial.lsum fun j => LinearMap.toSpanSingleton ℂ ℂ (iteratedDeriv j (pulseReflected h) t)

theorem receiverJetFunctional_apply (h : CompactPulse) (t : ℝ) (P : ℂ[X]) :
    receiverJetFunctional h t P=receiverDifferentialReading P h t := rfl

theorem receiverJetFunctional_monomial (h : CompactPulse) (t : ℝ) (j : ℕ) (c : ℂ) :
    receiverJetFunctional h t (monomial j c)=c*iteratedDeriv j (pulseReflected h) t := by
  simp [receiverJetFunctional,Polynomial.lsum_apply,Polynomial.sum_monomial_index,smul_eq_mul]

private theorem realize_jets (h : CompactPulse) (c : ℕ → ℂ) (S : Finset ℕ) :
    ∃ g : CompactPulse, (∀ w : ℂ, pulseAmplitude g w=
      (∑ j ∈ S, c j*(I*w)^j)*pulseAmplitude h w) ∧
      ∀ t : ℝ, pulseReflected g t=∑ j ∈ S, c j*iteratedDeriv j (pulseReflected h) t := by
  induction S using Finset.induction_on with
  | empty => exact ⟨CompactPulse.zero,fun w => by simp [pulseAmplitude_zero],
      fun t => by simp [pulseReflected_zero]⟩
  | @insert i S hi ih =>
    obtain ⟨g,ha,hr⟩ := ih
    refine ⟨(CompactPulse.smul (c i) (CompactPulse.iterD i h)).add g,?_,?_⟩
    · intro w
      rw [pulseAmplitude_add,pulseAmplitude_smul,CompactPulse.amplitude_iterD,ha,sum_insert hi]
      ring
    · intro t
      rw [pulseReflected_add,pulseReflected_smul,hr,sum_insert hi,receiver_iterated_deriv]

private theorem finite_exceptional_frequencies {P : ℂ[X]} (hp : P ≠ 0) :
    {ξ : ℝ | P.eval (I*(ξ:ℂ))=0}.Finite := by
  have hi : Function.Injective (fun ξ : ℝ => I*(ξ:ℂ)) :=
    fun _ _ he => Complex.ofReal_injective (mul_left_cancel₀ I_ne_zero he)
  exact (Polynomial.finite_setOf_isRoot hp).preimage hi.injOn

/-- A nonzero polynomial in the receiver derivatives has a strictly positive
Gram quadratic form on every half-line, even after an arbitrary cutoff. -/
theorem receiver_differential_tail_positive (P : ℂ[X]) (hp : P≠0) (h : CompactPulse)
    (hh : ∃ x : ℝ, h x ≠ 0) (T : ℝ) :
    0 < ∫ t in Ioi T, ‖receiverDifferentialReading P h t‖^2 := by
  obtain ⟨g,ha,hr⟩ := realize_jets h P.coeff P.support
  have hmult (w : ℂ) : pulseAmplitude g w=P.eval (I*w)*pulseAmplitude h w := by
    rw [Polynomial.eval_eq_sum]
    exact ha w
  have hg : ∃ x : ℝ, g x≠0 := by
    by_contra! hz
    have gz : (g : ℝ → ℂ)=CompactPulse.zero := funext fun x => hz x
    have hzero : ∀ᵐ ξ : ℝ, pulseAmplitude h (ξ:ℂ)=0 := by
      have hgood : ∀ᵐ ξ : ℝ, P.eval (I*(ξ:ℂ))≠0 :=
        ae_iff.mpr (by simpa only [not_not] using (finite_exceptional_frequencies hp).measure_zero volume)
      filter_upwards [hgood] with ξ hξ
      have he := hmult (ξ:ℂ)
      rw [gz,pulseAmplitude_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hξ
    have hdead (t : ℝ) : pulseReflected h t=0 := by
      unfold pulseReflected
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with ξ hξ
      simp only [hξ,zero_mul,Pi.zero_apply]
    have hpos := tailEnergy_pos h hh T
    simp only [tailEnergy,hdead,norm_zero,zero_pow (by decide : 2 ≠ 0),integral_zero,lt_self_iff_false] at hpos
  have hpos := tailEnergy_pos g hg T
  simpa only [tailEnergy,hr,receiverDifferentialReading] using hpos

/-- No nonzero constant-coefficient differential operator can annihilate the
observed field from any time onward, even almost everywhere. -/
theorem receiver_late_annihilator_iff (P : ℂ[X]) (h : CompactPulse)
    (hh : ∃ x : ℝ, h x ≠ 0) (T : ℝ) :
    (∀ᵐ t ∂volume.restrict (Ioi T), receiverDifferentialReading P h t=0) ↔ P=0 := by
  constructor
  · intro he
    by_contra hp
    have hz : (∫ t in Ioi T, ‖receiverDifferentialReading P h t‖^2)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [he] with t ht
      simp [ht]
    exact (receiver_differential_tail_positive P hp h hh T).ne' hz
  · rintro rfl
    simp [receiverDifferentialReading]

/-- All derivative orders remain linearly independent on every late half-line. -/
theorem receiver_late_derivatives_independent (h : CompactPulse)
    (hh : ∃ x : ℝ, h x ≠ 0) (T : ℝ) :
    LinearIndependent ℂ (fun j : ℕ => fun t : Ioi T => iteratedDeriv j (pulseReflected h) t) := by
  let L : ℂ[X] →ₗ[ℂ] (Ioi T → ℂ) := LinearMap.pi fun t => receiverJetFunctional h t
  have hk : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro P hp
    apply (receiver_late_annihilator_iff P h hh T).mp
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    exact congrFun hp ⟨t,ht⟩
  have he : L ∘ (Polynomial.basisMonomials ℂ : ℕ → ℂ[X]) =
      fun j => fun t : Ioi T => iteratedDeriv j (pulseReflected h) t := by
    funext j t
    simp only [L,Function.comp_apply,Polynomial.coe_basisMonomials,LinearMap.pi_apply,
      receiverJetFunctional_monomial,one_mul]
  rw [← he]
  exact (Polynomial.basisMonomials ℂ).linearIndependent.map' L hk

/-- Any finite selection of derivative orders can be distinguished exactly
by the same number of distinct samples taken after an arbitrary cutoff.
The dual weights recover every coefficient of the differential reading. -/
theorem receiver_late_sampling_recovery {J : Type*} [Fintype J] [DecidableEq J]
    (h : CompactPulse) (hh : ∃ x : ℝ, h x≠0) (orders : J ↪ ℕ) (T : ℝ) :
    ∃ (t : J → Ioi T) (dual : J → J → ℂ), Function.Injective t ∧
      ∀ (a : J → ℂ) q, ∑ i, dual q i *
        (∑ j, a j*iteratedDeriv (orders j) (pulseReflected h) (t i)) = a q := by
  have hi := (receiver_late_derivatives_independent h hh T).comp orders orders.injective
  obtain ⟨t,dual,ht,_,hrec⟩ :=
    HTGeometry.exists_injective_evaluation_dualReconstruction_of_linearIndependent _ hi
  exact ⟨t,dual,ht,hrec⟩

#print axioms receiver_differential_tail_positive
#print axioms receiver_late_annihilator_iff
#print axioms receiver_late_sampling_recovery

end GaloisForLFunctions.BlackHoleRingdown
