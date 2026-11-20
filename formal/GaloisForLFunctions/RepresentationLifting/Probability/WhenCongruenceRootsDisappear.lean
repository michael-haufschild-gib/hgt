import GaloisForLFunctions.RepresentationLifting.Probability.TheSplitProbabilityOfAPadicQuadratic

/-!
# When finite-precision roots disappear

A quadratic can have a root modulo p^h and be irreducible over Q_p.
The Haar mass of this event loses exactly a factor p² every two
additional digits. Its two initial values distinguish odd and even
precision, including for dyadic coefficients.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset MeasureTheory RHTower Polynomial
noncomputable section
open scoped Classical
variable (p : ℕ) [Fact p.Prime]
local notation "𝒪" => ℤ_[p]
private instance coordProbability : IsProbabilityMeasure (fieldOnePadicIntNormalizedHaar p) :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

/-- Probability of passing the modular root test for a quadratic that
is irreducible over the field. Coefficients are uniform in the whole box. -/
def spuriousRootMass (h : ℕ) : ℝ :=
  let μ := fieldOnePadicIntNormalizedHaar p
  (μ.prod μ).real (quadraticSplitTube p h ∩ {z : 𝒪×𝒪 | Irreducible
    (X^2+C (z.1:ℚ_[p])*X+C (z.2:ℚ_[p]))})

private theorem spuriousRootMass_series (h : ℕ) :
    spuriousRootMass p h = (1-(p:ℝ)⁻¹)/2*(∑ j ∈ range ((h+1)/2), ((p:ℝ)⁻¹^2)^j)+
      1/(p:ℝ)^h-(p:ℝ)/(2*((p:ℝ)+1)) := by
  let μ := fieldOnePadicIntNormalizedHaar p
  let S := {z : 𝒪×𝒪 | ∃ x : 𝒪, x*(z.1-x)=z.2}
  have hsub : S⊆quadraticSplitTube p h := fun z hz =>
    (padic_quadratic_root_iff_all_precisions p z.1 z.2).mp hz h
  have hs : {z : 𝒪×𝒪 | Irreducible (X^2+C (z.1:ℚ_[p])*X+C (z.2:ℚ_[p]))}=Sᶜ := by
    ext z
    exact (irreducible_quadratic_iff _ _).trans (not_congr (quadratic_root_integral p _ _))
  unfold spuriousRootMass
  rw [hs]
  change (μ.prod μ).real (quadraticSplitTube p h \ S)=_
  rw [measureReal_sdiff hsub (show MeasurableSet S from measurableSet_padic_quadratic_split p),
    show (μ.prod μ).real S=(p:ℝ)/(2*((p:ℝ)+1)) from padic_quadratic_split_probability p,
    quadraticSplitTube_mass,show (p:ℝ)^(2*h)=((p:ℝ)^h)^2 by rw [←pow_mul,Nat.mul_comm]]
  rw [finite_quadratic_split_probability]

/-- Two further digits eliminate a constant fraction of the surviving
irreducible quadratics, independently of the initial precision. -/
theorem spuriousRootMass_two_digits (h : ℕ) :
    spuriousRootMass p (h+2) = spuriousRootMass p h/(p:ℝ)^2 := by
  let r := ((p:ℝ)⁻¹)^2
  let m := (h+1)/2
  have hsum : ∑ j ∈ range (m+1), r^j= r*(∑ j ∈ range m, r^j)+1 := by
    rw [sum_range_succ']
    simp only [pow_zero,pow_succ',←mul_sum]
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have he : (h+2+1)/2=m+1 := by dsimp only [m]; omega
  rw [spuriousRootMass_series,spuriousRootMass_series,he,pow_add]
  change (1-(p:ℝ)⁻¹)/2*(∑ j ∈ range (m+1), r^j)+_ - _ = _
  rw [hsum]
  change (1-(p:ℝ)⁻¹)/2*(r*(∑ j ∈ range m, r^j)+1)+1/((p:ℝ)^h*(p:ℝ)^2)-
    (p:ℝ)/(2*((p:ℝ)+1)) = ((1-(p:ℝ)⁻¹)/2*(∑ j ∈ range m, r^j)+1/(p:ℝ)^h-
      (p:ℝ)/(2*((p:ℝ)+1)))/(p:ℝ)^2
  generalize (∑ j ∈ range m, r^j)=s
  dsimp only [r]
  field_simp [hp.ne',(add_pos hp zero_lt_one).ne']
  ring

/-- The precise survival law at every even and odd precision. The first
coordinate tests an even number of digits and the second tests the next digit. -/
theorem spuriousRootMass_even_odd (k : ℕ) :
    spuriousRootMass p (2*k)=((p:ℝ)+2)/(2*((p:ℝ)+1)*(p:ℝ)^(2*k)) ∧
    spuriousRootMass p (2*k+1)=(2*(p:ℝ)+1)/(2*((p:ℝ)+1)*(p:ℝ)^(2*k+1)) := by
  have hp : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hc := (add_pos hp zero_lt_one).ne'
  induction k with
  | zero =>
    constructor <;> rw [spuriousRootMass_series] <;>
      norm_num [sum_range_succ] <;> field_simp [hp.ne',hc] <;> ring
  | succ k ih =>
    obtain ⟨he,ho⟩ := ih
    constructor
    · rw [show 2*(k+1)=2*k+2 by omega,spuriousRootMass_two_digits,he,
        pow_add (p:ℝ) (2*k) 2,div_div,mul_assoc]
    · rw [show 2*(k+1)+1=(2*k+1)+2 by omega,spuriousRootMass_two_digits,ho,
        pow_add (p:ℝ) (2*k+1) 2,div_div,mul_assoc]

#print axioms spuriousRootMass_two_digits
#print axioms spuriousRootMass_even_odd
end
end GaloisForLFunctions.RepresentationLifting
