import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.DomainWalls
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.TransverseField
import GaloisForLFunctions.HTGeometry.PolynomialMatrixSimpleSpectrumTransport

/-! # Splitting all complementary Ising pairs by one transverse local field -/
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- All but finitely many values on a polynomial matrix line have simple
spectrum when one specialization does. The exceptional set is the root
set of the characteristic resultant in the line parameter. -/
theorem finite_singular_parameters {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ[X]) (a : ℂ) (ha : (M.map (evalRingHom a)).charpoly.Separable) :
    ∃ F : Finset ℂ, ∀ z : ℂ, z ∉ F → (M.map (evalRingHom z)).charpoly.Separable := by
  classical
  let m := Fintype.card I
  let p := Polynomial.resultant M.charpoly M.charpoly.derivative m (m-1)
  have he (z : ℂ) :
      p.eval z = Polynomial.resultant (M.map (evalRingHom z)).charpoly
        (M.map (evalRingHom z)).charpoly.derivative := by
    let φ := evalRingHom z
    change φ (Polynomial.resultant _ _ _ _) = _
    rw [←Polynomial.resultant_map_map,←Polynomial.derivative_map,←Matrix.charpoly_map]
    simp only [Matrix.charpoly_natDegree_eq_dim,Polynomial.natDegree_derivative,m,φ]
  have hp : p ≠ 0 := by
    intro h
    have hz : p.eval a = 0 := by rw [h,eval_zero]
    exact (Polynomial.resultant_eq_zero_iff.mp ((he a).symm.trans hz)).2
      ((Polynomial.separable_def _).mp ha)
  refine ⟨p.roots.toFinset,?_⟩
  intro z hz
  apply (Polynomial.separable_def _).mpr
  by_contra hn
  have hr := Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl (M.map (evalRingHom z)).charpoly_monic.ne_zero,hn⟩
  exact hz (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ((he z).trans hr)))

/-- A line inside the physical path family. Its endpoint at zero has
the isolated complementary doublets and its endpoint at one is simple. -/
def splitShell (n : ℕ) (v : ℝ) : PathShell n := (1-v) • isingShell n + v • transverseShell n

theorem split_simple_off_finite (n : ℕ) :
    ∃ F : Finset ℂ, ∀ v : ℝ, (v:ℂ) ∉ F → (pathHamiltonian (splitShell n v)).charpoly.Separable := by
  let A := pathHamiltonian (isingShell n)
  let B := pathHamiltonian (transverseShell n)
  let M : Matrix _ _ ℂ[X] := Matrix.of fun i j => (1-X)*C (A i j)+X*C (B i j)
  have he (v : ℝ) : M.map (evalRingHom (v:ℂ)) = pathHamiltonian (splitShell n v) := by
    change _ = pathHamiltonianLM n ((1-v) • isingShell n+v • transverseShell n)
    rw [map_add,map_smul,map_smul]
    ext i j
    simp only [M,Matrix.map_apply,Matrix.of_apply,Polynomial.coe_evalRingHom,eval_add,eval_mul,eval_sub,
      eval_one,eval_X,eval_C,Matrix.add_apply,Matrix.smul_apply]
    change (1-(v:ℂ))*A i j+(v:ℂ)*B i j=_
    simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
    rfl
  have he1 : M.map (evalRingHom 1) = B := by
    simpa only [Complex.ofReal_one,splitShell,sub_self,zero_smul,one_smul,zero_add] using he 1
  have h₁ : (M.map (evalRingHom 1)).charpoly.Separable := he1.symm ▸ transverse_simple n
  obtain ⟨F,hF⟩ := finite_singular_parameters M 1 h₁
  refine ⟨F,fun v hv => ?_⟩
  rw [←he]
  exact hF v hv

#print axioms split_simple_off_finite
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
