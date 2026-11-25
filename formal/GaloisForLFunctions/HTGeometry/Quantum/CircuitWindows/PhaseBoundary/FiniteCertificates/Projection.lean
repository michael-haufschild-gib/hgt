import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FiniteFactors
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Projection

/-! # Projection preserves a finite family of local polynomial certificates -/

open Polynomial Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section
variable {A X : Type*} [CommRing A] [TopologicalSpace X]

/-- Every member admits a local defining equation drawn from one finite family. -/
def FinitelyCertified (ρ : X → A →+* ℝ) (S : Set X) : Prop :=
  ∃ T : Finset A, ∀ x∈S, ∃ p∈T, ρ x p=0 ∧ ∀ᶠ z in 𝓝 x, ρ z p=0 → z∈S

private theorem factor_root (p : A[X]) (c : FactorChoice A) (ψ : A →+* ℝ) (z : ℝ)
    (hg : ψ (coefficientSquares (c.remainder p))=0) (hd : ψ c.den≠0) (hz : c.factor.eval₂ ψ z=0) :
    p.eval₂ ψ z=0 := by
  have he := congrArg (Polynomial.eval z) ((coefficientSquares_zero_iff ..).mp hg)
  rw [eval_map,eval_zero] at he
  simp only [FactorChoice.remainder,eval₂_sub,eval₂_mul,eval₂_C,hz,zero_mul,sub_zero] at he
  exact (mul_eq_zero.mp he).resolve_left hd

/-- For each old equation, keep its coefficient norm and the coefficient
norms of the remainders of its finite family of simple factorizations. -/
theorem FinitelyCertified.fst_image {ρ : X → A →+* ℝ} (hc : ∀ a, Continuous fun x => ρ x a)
    {S : Set (X × ℝ)} (hs : FinitelyCertified (appendEval ρ) S) : FinitelyCertified ρ (Prod.fst '' S) := by
  classical
  obtain ⟨T,hT⟩ := hs
  choose F hF using fun p : A[X] => finite_factors p
  let R (p : A[X]) (c : FactorChoice A) := coefficientSquares (c.remainder p)
  let B (p : A[X]) := insert (coefficientSquares p) ((F p).image (R p))
  refine ⟨T.biUnion B,?_⟩
  rintro _ ⟨⟨x,y⟩,hxy,rfl⟩
  obtain ⟨p,hp,hzero,hw⟩ := hT (x,y) hxy
  have of_mem {g : A} (hg : g∈B p) : g∈T.biUnion B := Finset.mem_biUnion.mpr ⟨p,hp,hg⟩
  by_cases hz : p.map (ρ x)=0
  · exact ⟨_,of_mem (Finset.mem_insert_self ..),(coefficientSquares_zero_iff ..).mpr hz,
      project_zero_specialization p hw⟩
  · obtain ⟨c,hcF,hd,hR,hP,hder⟩ := hF p (ρ x) y hzero hz
    exact ⟨R p c,of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hcF)),
      (coefficientSquares_zero_iff ..).mpr hR,project_simple_factor hc hw hd hP hder (factor_root p c)⟩

#print axioms FinitelyCertified.fst_image
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
