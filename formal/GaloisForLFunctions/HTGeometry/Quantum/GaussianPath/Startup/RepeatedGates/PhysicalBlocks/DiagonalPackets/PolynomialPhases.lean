import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralArcs.PacketApproach
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.SpectralAlgebra

/-! # Polynomial phase targets varying continuously with a local generator -/
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.DiagonalPackets
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

private abbrev Mat (J : Type) := Matrix J J ℂ

private theorem polynomial_diagonal (p : ℝ[X]) (d : I → ℝ) :
    aeval (diagonal (fun i => (d i:ℂ))) p = diagonal (fun i => (p.eval (d i):ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add,hp,hq]
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [hij]
  | monomial k a =>
    simp only [aeval_def,eval₂_monomial]
    rw [Matrix.algebraMap_eq_diagonal,Matrix.diagonal_pow,Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j; simp
    · simp [hij]

private theorem continuous_eval (p : ℝ[X]) : Continuous (fun H : Mat I => aeval H p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial k a =>
    simp only [aeval_def,eval₂_monomial]
    exact continuous_const.mul (continuous_id.pow k)

/-- Apply the real polynomial to the generator and evolve for one time unit. -/
def polynomialPhase (p : ℝ[X]) (H : Mat I) : Mat I := unitaryEvolution (aeval H p) 1

theorem continuous_polynomialPhase (p : ℝ[X]) : Continuous (polynomialPhase (I:=I) p) := by
  unfold polynomialPhase unitaryEvolution
  have he := continuous_eval (I:=I) p
  fun_prop

theorem polynomialPhase_diagonal (p : ℝ[X]) (d : I → ℝ) :
    polynomialPhase p (diagonal (fun i => (d i:ℂ))) =
      diagonal (fun i => Complex.exp (-(Complex.I*(p.eval (d i):ℂ)))) := by
  rw [polynomialPhase,polynomial_diagonal,unitaryEvolution_diagonal]
  simp only [Complex.ofReal_one,one_mul]

private theorem polynomialPhase_spectral {H : Mat I} (hH : H.IsHermitian) (p : ℝ[X]) :
    polynomialPhase p H = hH.eigenvectorUnitary.val *
      diagonal (fun j => Complex.exp (-(Complex.I*(p.eval (hH.eigenvalues j):ℂ)))) *
      star hH.eigenvectorUnitary.val := by
  let V := hH.eigenvectorUnitary
  let L := Unitary.conjStarAlgAut ℝ (Mat I) V
  let d := fun j => (hH.eigenvalues j:ℂ)
  have he : H=L (diagonal d) := isHermitian_eq_conj_diagonal hH
  have heval : aeval H p=L (diagonal (fun j => (p.eval (hH.eigenvalues j):ℂ))) := calc
    _ = aeval (L (diagonal d)) p := congrArg (fun M : Mat I => aeval M p) he
    _ = _ := by rw [aeval_algHom_apply,polynomial_diagonal]
  rw [polynomialPhase,heval]
  change unitaryEvolution (V.val * diagonal _ * star V.val) 1=_
  rw [unitaryEvolution_conj_diagonal _ V.property]
  simp only [Complex.ofReal_one,one_mul]

/-- At full projective rank every polynomial phase target is approached
by the original one-parameter evolution, up to global phase. -/
theorem approaches_polynomialPhase {N D : ℕ} (e : (Fin N→Bool) ≃ Fin (D+1))
    {H : Register N} (hH : H.IsHermitian) (hmax : MaximallyProjectiveEnergy hH.eigenvalues)
    (p : ℝ[X]) {ε : ℝ} (hε : 0<ε) :
    ∃ t>0, ∃ z : ℂ, ‖z‖=1 ∧ ‖unitaryEvolution H t-z • polynomialPhase p H‖<ε := by
  let f (i : Fin (D+1)) := Complex.exp (-(Complex.I*(p.eval (hH.eigenvalues (e.symm i)):ℂ)))
  have hf (i : Fin (D+1)) : ‖f i‖=1 := by simp [f,Complex.norm_exp]
  have hm := hmax.comp_equiv_relabel e.symm
  obtain ⟨G,_,hg⟩ := SpectralArcs.syndetic_packet_approach e hH hm f hf hε
  obtain ⟨t,ht,z,hz,he⟩ := hg 1
  refine ⟨t,zero_lt_one.trans_le ht.1,z,hz,?_⟩
  have hd : f ∘ e=(fun j => Complex.exp (-(Complex.I*(p.eval (hH.eigenvalues j):ℂ)))) := by
    funext j; simp only [Function.comp_apply,f,e.symm_apply_apply]
  rw [polynomialPhase_spectral hH p,←hd]
  exact he

#print axioms approaches_polynomialPhase
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.DiagonalPackets
