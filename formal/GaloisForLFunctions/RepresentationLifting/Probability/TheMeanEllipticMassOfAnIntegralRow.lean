import GaloisForLFunctions.RepresentationLifting.Probability.QuadraticIrreducibilityOnThinCoefficientBoxes
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging the elliptic mass over an integral row

For independent Haar b,y,z the polynomial X²+bX+s y z has an
irreducibility probability depending on the scale s. Split the y
integral into units and multiples of p. Two successive splittings,
combined with the two-digit shrink of the coefficient box, determine
the first two averages: 1/2 for s=1 and 1/(p+1) for s=p.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory RHTower
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "𝒪" => ℤ_[p]
local notation "μₚ" => fieldOnePadicIntNormalizedHaar p
private instance coordProbability : IsProbabilityMeasure μₚ :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

/-- The restriction to pZ_p is 1/p times the pushforward of probability
by multiplication by p. This also gives a change of variables for integrals. -/
theorem haar_restrict_prime_multiples :
    let d := fun x : 𝒪 => (p:𝒪)*x
    (μₚ).restrict (Set.range d)=(p:ENNReal)⁻¹ • (μₚ).map d := by
  let d := fun x : 𝒪 => (p:𝒪)*x
  have hd : Measurable d := (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.restrict_apply hS,Measure.smul_apply,Measure.map_apply hd hS,
    ←Set.image_preimage_eq_inter_range]
  exact padic_integral_haar_prime_image p (d ⁻¹' S)

/-- If a real observable is constant on the units, its Haar integral
obeys the residue decomposition into the unit contribution and a rescaled copy. -/
theorem integral_constant_on_padic_units (f : 𝒪 → ℝ) (c : ℝ) (hf : Measurable f)
    (hfi : Integrable f μₚ) (hunit : ∀ u : 𝒪ˣ, f u=c) :
    (∫ y, f y ∂μₚ)=(1-(p:ℝ)⁻¹)*c+(p:ℝ)⁻¹*(∫ y : 𝒪, f ((p:𝒪)*y) ∂μₚ) := by
  let d := fun y : 𝒪 => (p:𝒪)*y
  let D := Set.range d
  have hd : Continuous d := continuous_const.mul continuous_id
  have hD : MeasurableSet D := (isCompact_range hd).isClosed.measurableSet
  have hmass : (μₚ).real D=(p:ℝ)⁻¹ := by
    have hh := padic_integral_haar_prime_image p (Set.univ : Set 𝒪)
    rw [Set.image_univ,measure_univ,mul_one] at hh
    exact (congrArg ENNReal.toReal hh).trans (by rw [ENNReal.toReal_inv,ENNReal.toReal_natCast])
  have hvalue : Set.EqOn f (fun _ => c) Dᶜ := by
    intro y hy
    have hu : IsUnit y := by
      by_contra hn
      obtain ⟨z,hz⟩ := (PadicInt.norm_lt_one_iff_dvd y).mp (PadicInt.not_isUnit_iff.mp hn)
      exact hy ⟨z,hz.symm⟩
    simpa only [hu.unit_spec] using hunit hu.unit
  have outside : (∫ y in Dᶜ, f y ∂μₚ)=(1-(p:ℝ)⁻¹)*c := by
    rw [setIntegral_congr_fun hD.compl hvalue,setIntegral_const,smul_eq_mul,measureReal_compl hD,
      probReal_univ,hmass]
  have inside : (∫ y in D, f y ∂μₚ)=(p:ℝ)⁻¹*(∫ y, f (d y) ∂μₚ) := by
    rw [show (μₚ).restrict D=(p:ENNReal)⁻¹ • (μₚ).map d from haar_restrict_prime_multiples p,
      integral_smul_measure,integral_map hd.measurable.aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [←integral_add_compl hD hfi,inside,outside,add_comm]

/-- A unit factor in the scale is absorbed into the uniform constant coefficient. -/
theorem scaledIrreducibleMass_mul_unit (s : 𝒪) (u : 𝒪ˣ) :
    scaledIrreducibleMass p (s*u)=scaledIrreducibleMass p s := by
  let f : 𝒪×𝒪 →+ 𝒪×𝒪 := {
    toFun := fun z => (z.1,(u:𝒪)*z.2)
    map_zero' := by simp
    map_add' := by rintro ⟨a,b⟩ ⟨v,w⟩; simp [mul_add] }
  have hc : Continuous f := continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hsur : Function.Surjective f := by
    rintro ⟨b,c⟩
    exact ⟨(b,(↑u⁻¹:𝒪)*c),Prod.ext rfl (by change (u:𝒪)*((↑u⁻¹:𝒪)*c)=c; rw [←mul_assoc,Units.mul_inv,one_mul])⟩
  have hmp : MeasurePreserving f ((μₚ).prod μₚ) ((μₚ).prod μₚ) := AddMonoidHom.measurePreserving hc hsur rfl
  have he : scaledQuadraticIrreducible p (s*u)=f ⁻¹' scaledQuadraticIrreducible p s := by
    ext z
    change z∈scaledQuadraticIrreducible p (s*u) ↔ (z.1,(u:𝒪)*z.2)∈scaledQuadraticIrreducible p s
    simp only [mem_scaledQuadraticIrreducible,mul_assoc]
  unfold scaledIrreducibleMass
  rw [he]
  exact congrArg ENNReal.toReal (hmp.measure_preimage (measurableSet_scaledQuadraticIrreducible p s).nullMeasurableSet)

theorem measurable_scaledIrreducibleMass : Measurable (scaledIrreducibleMass p) :=
  (measurable_measure_prodMk_left (ν:=(μₚ).prod μₚ)
    (measurableSet_scaledQuadraticIrreducible_family p)).ennreal_toReal

/-- Average irreducibility when the constant coefficient is the product
of two independent uniform factors and a fixed scale. -/
def meanEllipticMass (s : 𝒪) : ℝ := ∫ y : 𝒪, scaledIrreducibleMass p (s*y) ∂μₚ

/-- Integrating the two-digit law keeps its exact scale factor. -/
theorem meanEllipticMass_two_digits (s : 𝒪) :
    meanEllipticMass p ((p:𝒪)^2*s)=meanEllipticMass p s/(p:ℝ) := by
  unfold meanEllipticMass
  simp_rw [mul_assoc,scaledIrreducibleMass_two_digits]
  rw [integral_div]

private theorem mean_residue_decomposition (s : 𝒪) :
    meanEllipticMass p s = (1-(p:ℝ)⁻¹)*scaledIrreducibleMass p s+
      (p:ℝ)⁻¹*meanEllipticMass p ((p:𝒪)*s) := by
  let f (y : 𝒪) := scaledIrreducibleMass p (s*y)
  have hf : Measurable f := (measurable_scaledIrreducibleMass p).comp (continuous_const.mul continuous_id).measurable
  have hfi : Integrable f μₚ := (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      change ‖((μₚ).prod μₚ).real (scaledQuadraticIrreducible p (s*y))‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)
  have hh := integral_constant_on_padic_units p f (scaledIrreducibleMass p s) hf hfi
    (fun u => scaledIrreducibleMass_mul_unit p s u)
  simpa only [f,meanEllipticMass,mul_assoc,mul_left_comm s (p:𝒪)] using hh

/-- The hyperspecial and integral Iwahori coefficient averages. No
conjugacy-class stratification or restriction on the residue prime is needed. -/
theorem meanEllipticMass_first_two :
    meanEllipticMass p 1=1/2 ∧ meanEllipticMass p p=1/((p:ℝ)+1) := by
  let A := meanEllipticMass p 1
  let B := meanEllipticMass p p
  let q := (p:ℝ)
  have hq : 1<q := by
    dsimp only [q]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp := zero_lt_one.trans hq
  have hc := (add_pos hp zero_lt_one).ne'
  have e₀ := mean_residue_decomposition p 1
  rw [scaledIrreducibleMass_one,mul_one] at e₀
  have e₁ := mean_residue_decomposition p p
  rw [scaledIrreducibleMass_prime,show (p:𝒪)*p=(p:𝒪)^2*1 by rw [mul_one,sq],
    meanEllipticMass_two_digits] at e₁
  change A=(1-q⁻¹)*((q+2)/(2*(q+1)))+q⁻¹*B at e₀
  change B=(1-q⁻¹)*((2*q+1)/(2*(q+1)*q))+q⁻¹*(A/q) at e₁
  have ea : 2*q*(q+1)*A-(q-1)*(q+2)-2*(q+1)*B=0 := by
    rw [e₀]
    field_simp [hp.ne',hc]
    ring
  have eb : 2*q^2*(q+1)*B-(q-1)*(2*q+1)-2*(q+1)*A=0 := by
    rw [e₁]
    field_simp [hp.ne',hc]
    ring
  have zero : (q+1)*(q^3-1)*(2*A-1)=0 := by linear_combination q^2*ea+eb
  have h₃ : 0<q^3-1 := sub_pos.mpr (one_lt_pow₀ hq (by decide : (3:ℕ)≠0))
  have hA : A=1/2 := by
    have := (mul_eq_zero.mp zero).resolve_left (mul_ne_zero hc h₃.ne')
    linarith only [this]
  refine ⟨hA,?_⟩
  rw [hA] at ea
  change B=1/(q+1)
  apply (eq_div_iff hc).mpr
  linear_combination -ea/2

/-- Irreducibility on every integral off-diagonal lattice, with the
quotient of successive two-digit probabilities equal to 1/p. -/
theorem meanEllipticMass_all_prime_powers (k : ℕ) :
    meanEllipticMass p ((p:𝒪)^(2*k))=1/(2*(p:ℝ)^k) ∧
    meanEllipticMass p ((p:𝒪)^(2*k+1))=1/(((p:ℝ)+1)*(p:ℝ)^k) := by
  induction k with
  | zero => simpa only [mul_zero,zero_add,pow_zero,pow_one,mul_one] using meanEllipticMass_first_two p
  | succ k ih =>
    obtain ⟨he,ho⟩ := ih
    constructor
    · rw [show 2*(k+1)=2+2*k by omega,pow_add,meanEllipticMass_two_digits,he,div_div,pow_succ,mul_assoc]
    · rw [show 2*(k+1)+1=2+(2*k+1) by omega,pow_add (p:𝒪) 2 (2*k+1),meanEllipticMass_two_digits,
        ho,div_div,pow_succ,mul_assoc]

#print axioms integral_constant_on_padic_units
#print axioms scaledIrreducibleMass_mul_unit
#print axioms meanEllipticMass_first_two
#print axioms meanEllipticMass_all_prime_powers
end
end GaloisForLFunctions.RepresentationLifting
