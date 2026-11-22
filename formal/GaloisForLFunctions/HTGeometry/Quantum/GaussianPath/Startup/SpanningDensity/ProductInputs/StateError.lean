import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.ArbitraryBases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.ProjectorTransport

/-! # The empty circuit reproduces each individual product input up to its own phase -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
noncomputable section

private theorem phase_on_column {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (x : d) (E : d→ℝ) (t : ℝ) :
    basisProjector x*unitaryEvolution (diagonal fun i => (E i:ℂ)) t=
      Complex.exp ((-(t*E x):ℝ)*Complex.I) • basisProjector x := by
  rw [unitaryEvolution_diagonal_phase]
  ext i j
  by_cases hi : i=x <;> by_cases hj : j=x <;> by_cases hij : i=j <;>
    simp_all [basisProjector]

/-- In every product basis and for each input column the empty circuit
has projective state error at most √21 |t|‖u‖. This is a Euclidean
state-vector estimate, uniform in all single-site choices. -/
theorem product_input_empty_error {n : ℕ} (u : PathShell n) (t : ℝ)
    (B : Fin (n+2)→Matrix.unitaryGroup Bool ℂ) (x : Bits (n+2)) :
    let V := (basisUnitary B).val
    ∃ z : ℂ, ‖z‖=1 ∧ (∑ y, ‖(unitaryEvolution (pathHamiltonian u) t*V) y x-z*V y x‖^2)
      ≤ 21*t^2*‖u‖^2 := by
  intro V
  let H := pathHamiltonian u
  let F := star V*H*V
  have hV : V∈unitary (Reg (n+2)) := (basisUnitary B).2
  have hV' := Unitary.star_mem hV
  have hF : IsSelfAdjoint F := by
    simp only [IsSelfAdjoint,F,star_mul,star_star,(isSelfAdjoint_pathHamiltonian u).star_eq,mul_assoc,H]
  let E (i : Bits (n+2)) := (F i i).re
  have hx : F x x=E x := by
    have hh := congrArg (fun M : Reg (n+2) => M x x) hF.isHermitian.eq
    exact (Complex.conj_eq_iff_re.mp hh).symm
  let z := Complex.exp ((-(t*E x):ℝ)*Complex.I)
  refine ⟨z,Complex.norm_exp_ofReal_mul_I _,?_⟩
  have hinv := (inv_eq_star_of_mem_unitary hV').trans (star_star V)
  have he : unitaryEvolution F t=star V*unitaryEvolution H t*V := by
    have his : IsUnit (star V) := ⟨⟨star V,V,(Unitary.mem_iff.mp hV).1,(Unitary.mem_iff.mp hV).2⟩,rfl⟩
    simpa only [hinv,F] using unitaryEvolution_conj (star V) H his t
  let P := basisProjector x
  let R := (unitaryEvolution H t*V-z • V)*P
  have hR : star V*R=unitaryEvolution F t*P-z • P := by
    dsimp only [R]
    rw [←mul_assoc,mul_sub,←mul_assoc,←he,Matrix.mul_smul,(Unitary.mem_iff.mp hV).1,sub_mul,Matrix.smul_mul,one_mul]
  have herr := projector_residual F hF E x hx t
  rw [phase_on_column] at herr
  have hn : ‖R‖ ≤ |t| * Real.sqrt (∑ y∈Finset.univ.erase x, ‖F y x‖^2) := by
    rw [←CStarRing.norm_mem_unitary_mul R hV',hR]
    exact herr
  have hcol : ∀ y, R y x=(unitaryEvolution H t*V) y x-z*V y x := by
    intro y
    simp [R,P,basisProjector,mul_diagonal]
  have hw := sum_normSq_column_le_opNorm_sq R x
  simp only [hcol] at hw
  apply hw.trans
  have hsq := pow_le_pow_left₀ (norm_nonneg R) hn 2
  rw [mul_pow,sq_abs,Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hsq
  exact hsq.trans ((mul_le_mul_of_nonneg_left (product_basis_variance u B x) (sq_nonneg t)).trans_eq (by ring))

#print axioms product_input_empty_error
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
