import GaloisForLFunctions.RepresentationLifting.Probability.TheSplitProbabilityOfAPadicQuadratic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Haar law of a unit off-diagonal row

With a fixed unit in the upper-right entry, the two characteristic
coefficients are an affine change of the lower row with invertible
linear part. It transports every uniform residue box to its coefficient
box. The maximal-ideal box gives the last assertion of Lapid and
Shusterman's Lemma C.1 over the p-adic fields.
-/

namespace GaloisForLFunctions.RepresentationLifting
open MeasureTheory Matrix Polynomial
open scoped Matrix
noncomputable section

private def rowLinear {R : Type*} [CommRing R] (x : R) (y : Rˣ) : R×R →+ R×R where
  toFun q := (-q.2,x*q.2-y*q.1)
  map_zero' := by simp
  map_add' := by rintro ⟨z,w⟩ ⟨a,b⟩; ext <;> simp [mul_add] <;> ring

/-- A unit off-diagonal entry makes the linear part of the coefficient
chart a Haar-preserving automorphism, over any compact topological ring. -/
theorem measurePreserving_row_coefficients {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R] (μ : Measure R) [μ.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (x t : R) (y : Rˣ) :
    MeasurePreserving (fun q : R×R => (-(t+q.2),x*q.2-y*q.1))
      (μ.prod μ) (μ.prod μ) := by
  have hc : Continuous (rowLinear x y) :=
    continuous_snd.neg.prodMk ((continuous_const.mul continuous_snd).sub (continuous_const.mul continuous_fst))
  have hsur : Function.Surjective (rowLinear x y) := by
    rintro ⟨b,d⟩
    refine ⟨(↑y⁻¹*(x*(-b)-d),-b),?_⟩
    change (- -b,x*(-b)-y*(↑y⁻¹*(x*(-b)-d)))=(b,d)
    rw [neg_neg,←mul_assoc,Units.mul_inv,one_mul,sub_sub_cancel]
  have hl : MeasurePreserving (rowLinear x y) (μ.prod μ) (μ.prod μ) :=
    AddMonoidHom.measurePreserving hc hsur rfl
  have he : (fun q : R×R => (-(t+q.2),x*q.2-y*q.1)) =
      (fun z : R×R => z+(-t,0)) ∘ rowLinear x y := by
    funext q
    change (-(t+q.2),x*q.2-y*q.1)=(-q.2 + -t,x*q.2-y*q.1+0)
    rw [neg_add_rev,add_zero]
  rw [he]
  exact (measurePreserving_add_right (μ.prod μ) (-t,0)).comp hl

variable (p : ℕ) [Fact p.Prime]
local notation "𝒪" => ℤ_[p]
private instance coordProbability : IsProbabilityMeasure (RHTower.fieldOnePadicIntNormalizedHaar p) :=
  ⟨RHTower.fieldOnePadicIntNormalizedHaar_univ p⟩

/-- The joint law of the negative trace and determinant on every lower-row
coset is the independent translated coefficient law at the same scale. -/
theorem coefficient_distribution_on_lower_row_box (x z₀ w₀ a : 𝒪) (y : 𝒪ˣ) :
    let μ := RHTower.fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).map (fun q : 𝒪×𝒪 =>
      (-(x+(w₀+a*q.2)),x*(w₀+a*q.2)-y*(z₀+a*q.1))) =
    (μ.prod μ).map (fun b : 𝒪×𝒪 => (-(x+w₀)+a*b.1,x*w₀-y*z₀+a*b.2)) := by
  let μ := RHTower.fieldOnePadicIntNormalizedHaar p
  let shift (b : 𝒪×𝒪) := (-(x+w₀)+a*b.1,x*w₀-y*z₀+a*b.2)
  have hh := measurePreserving_row_coefficients μ x 0 y
  have hs : Measurable shift := ((continuous_const.add (continuous_const.mul continuous_fst)).prodMk
    (continuous_const.add (continuous_const.mul continuous_snd))).measurable
  have hmap := Measure.map_map (μ:=μ.prod μ) hs hh.measurable
  rw [hh.map_eq] at hmap
  refine Eq.trans ?_ hmap.symm
  apply congrArg (fun f => (μ.prod μ).map f)
  funext q
  apply Prod.ext
  · change -(x+(w₀+a*q.2))= -(x+w₀)+a*(-(0+q.2))
    ring
  · change x*(w₀+a*q.2)-y*(z₀+a*q.1)=x*w₀-y*z₀+a*(x*q.2-y*q.1)
    ring

private theorem charpoly_lower_row (x y z w : ℚ_[p]) :
    (!![x,y;z,w]).charpoly=X^2+C (-(x+w))*X+C (x*w-y*z) := by
  rw [charpoly_fin_two,trace_fin_two_of,det_fin_two_of,map_neg,neg_mul,sub_eq_add_neg]

/-- Irreducibility of the field-valued characteristic polynomial for
each fixed top row (pu,y), with y a unit, and random lower row in pZ_p². -/
theorem ramified_lower_row_irreducibility (u : 𝒪) (y : 𝒪ˣ) :
    let μ := RHTower.fieldOnePadicIntNormalizedHaar p
    (μ.prod μ).real {q : 𝒪×𝒪 | Irreducible (!![
      ((p:𝒪)*u:𝒪),(y:𝒪); (p:𝒪)*q.1,(p:𝒪)*q.2].map (PadicInt.Coe.ringHom (p:=p))).charpoly} =
      (2*(p:ℝ)+1)/(2*((p:ℝ)+1)) := by
  let μ := RHTower.fieldOnePadicIntNormalizedHaar p
  let S := {b : 𝒪×𝒪 | Irreducible
    (X^2+C (((p:𝒪)*b.1:𝒪):ℚ_[p])*X+C (((p:𝒪)*b.2:𝒪):ℚ_[p]))}
  let f (q : 𝒪×𝒪) := (-(u+q.2),(p*u)*q.2-y*q.1)
  have hmp : MeasurePreserving f (μ.prod μ) (μ.prod μ) := measurePreserving_row_coefficients μ (p*u) u y
  have hS : MeasurableSet S := by
    have hc : Continuous (fun b : 𝒪×𝒪 => ((p:𝒪)*b.1,(p:𝒪)*b.2)) :=
      (continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd)
    have he : S=(fun b : 𝒪×𝒪 => ((p:𝒪)*b.1,(p:𝒪)*b.2)) ⁻¹'
        {z : 𝒪×𝒪 | ∃ x : 𝒪, x*(z.1-x)=z.2}ᶜ := by
      ext b
      exact (irreducible_quadratic_iff _ _).trans (not_congr (quadratic_root_integral p _ _))
    rw [he]
    exact hc.measurable (measurableSet_padic_quadratic_split p).compl
  have he : {q : 𝒪×𝒪 | Irreducible (!![
      ((p:𝒪)*u:𝒪),(y:𝒪); (p:𝒪)*q.1,(p:𝒪)*q.2].map (PadicInt.Coe.ringHom (p:=p))).charpoly} = f ⁻¹' S := by
    ext q
    change Irreducible ((!![(((p:𝒪)*u:𝒪):ℚ_[p]),((y:𝒪):ℚ_[p]);
      (((p:𝒪)*q.1:𝒪):ℚ_[p]),(((p:𝒪)*q.2:𝒪):ℚ_[p])]).charpoly) ↔ _
    rw [charpoly_lower_row]
    change Irreducible _ ↔ Irreducible (X^2+C (((p:𝒪)*(-(u+q.2)):𝒪):ℚ_[p])*X+
      C (((p:𝒪)*((p*u)*q.2-y*q.1):𝒪):ℚ_[p]))
    push_cast
    ring_nf
  rw [he]
  have hmass := hmp.measure_preimage hS.nullMeasurableSet
  exact (congrArg ENNReal.toReal hmass).trans (padic_ramified_quadratic_irreducible_probability p)

#print axioms measurePreserving_row_coefficients
#print axioms coefficient_distribution_on_lower_row_box
#print axioms ramified_lower_row_irreducibility
end
end GaloisForLFunctions.RepresentationLifting
