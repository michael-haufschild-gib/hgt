import GaloisForLFunctions.RepresentationLifting.Probability.PadicMatrixHaar
import GaloisForLFunctions.RepresentationLifting.Probability.TheMeanEllipticMassOfAnIntegralRow

/-!
# Elliptic matrices on integral off-diagonal lattices

Under additive Haar probability, the upper-right entry, the diagonal
difference and the negative lower-left entry are independent. Translation
of the spectral variable reduces the characteristic polynomial to a
quadratic with a product constant coefficient. This yields the elliptic
mass for every lower-left valuation bound, including the hyperspecial and
Iwahori lattices in Propositions C.2 and C.3 of Lapid and Shusterman.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory RHTower Matrix Polynomial
open scoped Matrix
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "𝒪" => ℤ_[p]
local notation "μₚ" => fieldOnePadicIntNormalizedHaar p
local notation "Mat" => Matrix (Fin 2) (Fin 2) 𝒪
private instance coordProbability : IsProbabilityMeasure μₚ :=
  ⟨fieldOnePadicIntNormalizedHaar_univ p⟩

/-- The three coordinates needed for the translation-invariant quadratic test. -/
def matrixEllipticCoordinates : Mat →+ 𝒪×(𝒪×𝒪) where
  toFun A := (A 0 1,A 0 0-A 1 1,-A 1 0)
  map_zero' := by simp
  map_add' A B := by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · change A 0 0+B 0 0-(A 1 1+B 1 1)=(A 0 0-A 1 1)+(B 0 0-B 1 1)
      abel
    · exact neg_add (A 1 0) (B 1 0)

/-- Averaging matrix Haar measure induces independent Haar coordinates. -/
theorem measurePreserving_matrixEllipticCoordinates :
    MeasurePreserving (matrixEllipticCoordinates p) (padicMatrixHaar p 2) ((μₚ).prod ((μₚ).prod μₚ)) := by
  have entry (i j : Fin 2) : Continuous (fun A : Mat => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hc : Continuous (matrixEllipticCoordinates p) :=
    (entry 0 1).prodMk (((entry 0 0).sub (entry 1 1)).prodMk (entry 1 0).neg)
  have hs : Function.Surjective (matrixEllipticCoordinates p) := by
    rintro ⟨y,b,c⟩
    refine ⟨!![b,y;-c,0],?_⟩
    change (y,b-0,- -c)=(y,b,c)
    rw [sub_zero,neg_neg]
  letI : ((μₚ).prod μₚ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  letI : ((μₚ).prod ((μₚ).prod μₚ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact AddMonoidHom.measurePreserving (μ:=padicMatrixHaar p 2) (ν:=(μₚ).prod ((μₚ).prod μₚ))
    hc hs (by rw [measure_univ,measure_univ])

/-- Disintegrate any measurable event in the three coordinates over
the upper-right entry, leaving a product Haar section on the other two. -/
theorem matrixEllipticCoordinates_event (E : Set (𝒪×(𝒪×𝒪))) (hE : MeasurableSet E) :
    (padicMatrixHaar p 2).real ((matrixEllipticCoordinates p) ⁻¹' E) =
      ∫ y, ((μₚ).prod μₚ).real (Prod.mk y ⁻¹' E) ∂μₚ := by
  have hm := measurable_measure_prodMk_left (ν:=(μₚ).prod μₚ) hE
  rw [Measure.real,(measurePreserving_matrixEllipticCoordinates p).measure_preimage hE.nullMeasurableSet,
    Measure.prod_apply hE]
  exact (integral_toReal hm.aemeasurable (Filter.Eventually.of_forall fun _ => measure_lt_top _ _)).symm

/-- The field-valued matrix in which the lower-left coordinate is scaled. -/
def offDiagonalLatticeMatrix (s : 𝒪) (A : Mat) : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  (!![A 0 0,A 0 1;s*A 1 0,A 1 1]).map (PadicInt.Coe.ringHom (p:=p))

private theorem translate_quadratic_test (a b c d s : 𝒪) :
    (∃ x : 𝒪, x*(-(a+d)-x)=a*d-b*(s*c)) ↔
    ∃ x : 𝒪, x*((a-d)-x)=(s*b)*(-c) := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x+a,by linear_combination hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x-a,by linear_combination hx⟩

theorem offDiagonalLatticeMatrix_irreducible_iff (s : 𝒪) (A : Mat) :
    Irreducible (offDiagonalLatticeMatrix p s A).charpoly ↔
      (matrixEllipticCoordinates p A).2∈scaledQuadraticIrreducible p (s*A 0 1) := by
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  change Irreducible (!![(a:ℚ_[p]),(b:ℚ_[p]);((s*c:𝒪):ℚ_[p]),(d:ℚ_[p])]).charpoly ↔
    (a-d,-c)∈scaledQuadraticIrreducible p (s*b)
  have hpoly (u v w z : ℚ_[p]) : (!![u,v;w,z]).charpoly =
      X^2+C (-(u+z))*X+C (u*z-v*w) := by
    rw [charpoly_fin_two,trace_fin_two_of,det_fin_two_of,map_neg,neg_mul,sub_eq_add_neg]
  rw [hpoly]
  have ht : -((a:ℚ_[p])+d) = ((-(a+d):𝒪):ℚ_[p]) := by push_cast; rfl
  have hd : (a:ℚ_[p])*d-b*((s*c:𝒪):ℚ_[p])=((a*d-b*(s*c):𝒪):ℚ_[p]) := by push_cast; rfl
  rw [ht,hd,irreducible_quadratic_iff,quadratic_root_integral,mem_scaledQuadraticIrreducible]
  exact not_congr (translate_quadratic_test p a b c d s)

private def ellipticFamily (s : 𝒪) : Set (𝒪×(𝒪×𝒪)) :=
  {q | q.2∈scaledQuadraticIrreducible p (s*q.1)}

private theorem ellipticFamily_measurable (s : 𝒪) : MeasurableSet (ellipticFamily p s) := by
  let f (q : 𝒪×(𝒪×𝒪)) := (s*q.1,q.2)
  have hc : Continuous f := (continuous_const.mul continuous_fst).prodMk continuous_snd
  exact hc.measurable (measurableSet_scaledQuadraticIrreducible_family p)

private theorem offDiagonal_event_eq_preimage (s : 𝒪) :
    {A : Mat | Irreducible (offDiagonalLatticeMatrix p s A).charpoly} =
      (matrixEllipticCoordinates p) ⁻¹' ellipticFamily p s := by
  ext A
  exact offDiagonalLatticeMatrix_irreducible_iff p s A

private theorem ellipticFamily_probability (s : 𝒪) :
    (padicMatrixHaar p 2).real ((matrixEllipticCoordinates p) ⁻¹' ellipticFamily p s) =
      meanEllipticMass p s := by
  have h := matrixEllipticCoordinates_event p (ellipticFamily p s) (ellipticFamily_measurable p s)
  exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun _ => rfl))

/-- The elliptic mass of the lattice is the integral of its conditional
quadratic masses over the upper-right coordinate. -/
theorem offDiagonalLatticeMatrix_probability (s : 𝒪) :
    (padicMatrixHaar p 2).real {A | Irreducible (offDiagonalLatticeMatrix p s A).charpoly} =
      meanEllipticMass p s :=
  (congrArg (padicMatrixHaar p 2).real (offDiagonal_event_eq_preimage p s)).trans (ellipticFamily_probability p s)

/-- For a lower-left entry uniform in p^h Z_p, the elliptic probabilities
at h=2k and h=2k+1, respectively. -/
theorem elliptic_probability_at_every_integral_depth (k : ℕ) :
    (padicMatrixHaar p 2).real {A | Irreducible (offDiagonalLatticeMatrix p ((p:𝒪)^(2*k)) A).charpoly} =
      1/(2*(p:ℝ)^k) ∧
    (padicMatrixHaar p 2).real {A | Irreducible (offDiagonalLatticeMatrix p ((p:𝒪)^(2*k+1)) A).charpoly} =
      1/(((p:ℝ)+1)*(p:ℝ)^k) := by
  rw [offDiagonalLatticeMatrix_probability,offDiagonalLatticeMatrix_probability]
  exact meanEllipticMass_all_prime_powers p k

/-- One half of all integral two-by-two matrices have irreducible
characteristic polynomial over the fraction field, also at p=2. -/
theorem padicMatrixHaar_irreducible_charpoly :
    (padicMatrixHaar p 2).real {A : Mat | Irreducible (A.map (PadicInt.Coe.ringHom (p:=p))).charpoly} = 1/2 := by
  have he (A : Mat) : offDiagonalLatticeMatrix p 1 A=A.map (PadicInt.Coe.ringHom (p:=p)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [offDiagonalLatticeMatrix]
  simpa only [he] using (offDiagonalLatticeMatrix_probability p 1).trans (meanEllipticMass_first_two p).1

#print axioms measurePreserving_matrixEllipticCoordinates
#print axioms offDiagonalLatticeMatrix_probability
#print axioms elliptic_probability_at_every_integral_depth
#print axioms padicMatrixHaar_irreducible_charpoly

end
end GaloisForLFunctions.RepresentationLifting
