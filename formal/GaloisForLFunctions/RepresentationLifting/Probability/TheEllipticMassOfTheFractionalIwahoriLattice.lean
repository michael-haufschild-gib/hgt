import GaloisForLFunctions.RepresentationLifting.Probability.EllipticMatricesOnEveryIntegralOffDiagonalLattice

/-!
# The elliptic mass of the fractional Iwahori lattice

Multiplication of the spectral variable by p makes a single fractional
off-diagonal digit integral. A unit linear coefficient would force a
Hensel root, so the transformed irreducible locus is already contained
in the first-coordinate p-ball. Conditioning on that ball multiplies
its mass by p. For a unit numerator this gives p/(p+1), the other
Iwahori density in Lapid and Shusterman's Proposition C.3.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory RHTower Polynomial Matrix
open scoped Matrix
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "𝒪" => ℤ_[p]
local notation "Mat" => Matrix (Fin 2) (Fin 2) 𝒪
local notation "μₚ" => fieldOnePadicIntNormalizedHaar p

/-- Shrinking the linear coefficient gives an exact conditioning factor
when the constant coefficient is already divisible by p. -/
theorem scaledIrreducibleMass_condition_linear (u : 𝒪) :
    ((μₚ).prod μₚ).real ((fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2)) ⁻¹'
      scaledQuadraticIrreducible p ((p:𝒪)*u)) = (p:ℝ)*scaledIrreducibleMass p ((p:𝒪)*u) := by
  let d (z : 𝒪×𝒪) := ((p:𝒪)*z.1,z.2)
  let E := scaledQuadraticIrreducible p ((p:𝒪)*u)
  have hd : Continuous d := (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hs : E⊆Set.range d := by
    rintro ⟨b,c⟩ h
    obtain ⟨t,ht⟩ : (p:𝒪)∣b := by
      by_contra hn
      apply (mem_scaledQuadraticIrreducible p _ _).mp h
      simpa only [mul_assoc] using padic_quadratic_root_of_unit_linear p b (u*c) hn
    exact ⟨(t,c),Prod.ext ht.symm rfl⟩
  have hh := product_haar_prime_first_image p (d ⁻¹' E)
    ((measurableSet_scaledQuadraticIrreducible p _).preimage hd.measurable)
  change ((μₚ).prod μₚ).real (d '' (d ⁻¹' E))=((μₚ).prod μₚ).real (d ⁻¹' E)/(p:ℝ) at hh
  rw [Set.image_preimage_eq_of_subset hs] at hh
  exact ((eq_div_iff (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mp hh).symm.trans (mul_comm _ _)

/-- Uniform coordinates in the lattice whose upper-right entry lies
in (s/p)Z_p, with the other three entries integral. -/
def fractionalIwahoriMatrix (s : 𝒪) (A : Mat) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![(A 0 0:ℚ_[p]),((s:ℚ_[p])/(p:ℚ_[p]))*(A 0 1:ℚ_[p]);(A 1 0:ℚ_[p]),(A 1 1:ℚ_[p])]

private theorem scaled_root_equivalence {K : Type*} [Field K] (a b c d s m : K) (hm : m≠0) :
    (∃ x : K, x*(-(a+d)-x)=a*d-(s/m*b)*c) ↔
    ∃ z : K, z*(m*(a-d)-z)=((m*s)*b)*(-c) := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨m*(x+a),?_⟩
    field_simp [hm] at hx
    linear_combination m*hx
  · rintro ⟨z,hz⟩
    refine ⟨z/m-a,?_⟩
    field_simp [hm]
    linear_combination hz

private theorem fractional_test (s : 𝒪) (A : Mat) :
    Irreducible (fractionalIwahoriMatrix p s A).charpoly ↔
      ((p:𝒪)*(A 0 0-A 1 1),-A 1 0)∈scaledQuadraticIrreducible p (((p:𝒪)*s)*A 0 1) := by
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  have hp : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpoly (u v w z : ℚ_[p]) : (!![u,v;w,z]).charpoly=X^2+C (-(u+z))*X+C (u*z-v*w) := by
    rw [charpoly_fin_two,trace_fin_two_of,det_fin_two_of,map_neg,neg_mul,sub_eq_add_neg]
  change Irreducible (!![(a:ℚ_[p]),((s:ℚ_[p])/(p:ℚ_[p]))*b;(c:ℚ_[p]),(d:ℚ_[p])]).charpoly ↔
    Irreducible (X^2+C (((p:𝒪)*(a-d):𝒪):ℚ_[p])*X+C (((p*s*b)*(-c):𝒪):ℚ_[p]))
  rw [hpoly,irreducible_quadratic_iff,irreducible_quadratic_iff]
  push_cast
  exact not_congr (scaled_root_equivalence (a:ℚ_[p]) b c d s (p:ℚ_[p]) hp)

private def fractionalFamily (s : 𝒪) : Set (𝒪×(𝒪×𝒪)) :=
  {q | ((p:𝒪)*q.2.1,q.2.2)∈scaledQuadraticIrreducible p (((p:𝒪)*s)*q.1)}

private theorem fractionalFamily_measurable (s : 𝒪) : MeasurableSet (fractionalFamily p s) := by
  let f (q : 𝒪×(𝒪×𝒪)) := (((p:𝒪)*s)*q.1,(p:𝒪)*q.2.1,q.2.2)
  have hc : Continuous f := (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd))
  exact hc.measurable (measurableSet_scaledQuadraticIrreducible_family p)

private theorem fractional_event_eq_preimage (s : 𝒪) :
    {A : Mat | Irreducible (fractionalIwahoriMatrix p s A).charpoly} =
      (matrixEllipticCoordinates p) ⁻¹' fractionalFamily p s := by
  ext A
  exact fractional_test p s A

private theorem fractionalFamily_section (s y : 𝒪) :
    ((μₚ).prod μₚ).real (Prod.mk y ⁻¹' fractionalFamily p s) =
      (p:ℝ)*scaledIrreducibleMass p (((p:𝒪)*s)*y) := by
  change ((μₚ).prod μₚ).real ((fun z : 𝒪×𝒪 => ((p:𝒪)*z.1,z.2)) ⁻¹'
      scaledQuadraticIrreducible p (((p:𝒪)*s)*y))=_
  rw [mul_assoc,scaledIrreducibleMass_condition_linear]

private theorem fractionalFamily_probability (s : 𝒪) :
    (padicMatrixHaar p 2).real ((matrixEllipticCoordinates p) ⁻¹' fractionalFamily p s) =
      (p:ℝ)*meanEllipticMass p ((p:𝒪)*s) := by
  have h := matrixEllipticCoordinates_event p (fractionalFamily p s) (fractionalFamily_measurable p s)
  refine h.trans ((integral_congr_ae (Filter.Eventually.of_forall (fractionalFamily_section p s))).trans ?_)
  exact integral_const_mul (p:ℝ) (fun y : 𝒪 => scaledIrreducibleMass p (((p:𝒪)*s)*y))

/-- Elliptic probability for any integral numerator of the fractional
upper-right scale. A factor p comes from eliminating its denominator. -/
theorem fractionalIwahoriMatrix_probability (s : 𝒪) :
    (padicMatrixHaar p 2).real {A | Irreducible (fractionalIwahoriMatrix p s A).charpoly} =
      (p:ℝ)*meanEllipticMass p ((p:𝒪)*s) :=
  (congrArg (padicMatrixHaar p 2).real (fractional_event_eq_preimage p s)).trans (fractionalFamily_probability p s)

/-- Over every p-adic field, the irreducible fraction for an upper-right
entry uniform in p⁻¹ Z_p is p/(p+1), including 2/3 over Q₂. -/
theorem fractionalIwahori_elliptic_density :
    (padicMatrixHaar p 2).real {A | Irreducible (fractionalIwahoriMatrix p 1 A).charpoly} =
      (p:ℝ)/((p:ℝ)+1) := by
  rw [fractionalIwahoriMatrix_probability,mul_one,(meanEllipticMass_first_two p).2,mul_one_div]

#print axioms scaledIrreducibleMass_condition_linear
#print axioms fractionalIwahoriMatrix_probability
#print axioms fractionalIwahori_elliptic_density
end
end GaloisForLFunctions.RepresentationLifting
