import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.OrbitDegree

/-! # The degree of the actual Gaussian orbit in one dephased local observable -/
open Matrix Polynomial MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section

/-- Interpolation in the dephased boundary Z represents the whole physical
orbit. Except at finitely many times on any compact interval, its degree
attains 2ᴺ−1. -/
theorem gaussian_firstZ_orbit_degree : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
    let H := pathHamiltonian (pathPauliDisorderShell ω n)
    let hH := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian
    let V := hH.eigenvectorUnitary
    let z := firstZProfile (pathPauliDisorderShell ω n)
    let p := orbitInterpolant z hH.eigenvalues
    (∀ t : ℝ, (p t).degree < (2^(n+2):ℕ) ∧
      aeval (spectralFunction V z) (p t)=unitaryEvolution H t) ∧
    ∀ a b : ℝ, {t ∈ Icc a b | (p t).coeff (2^(n+2)-1)=0}.Finite := by
  filter_upwards [gaussian_simple_firstZ_distinguishes] with ω hω n
  intro H hH V z p
  have hiz : Function.Injective z := fun i j hij => (hω n).2 (congrArg Complex.re hij)
  have hn : Set.InjOn z (↑(Finset.univ : Finset (Fin (n+2) → Bool))) := hiz.injOn
  refine ⟨?_,fun a b => by simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,p] using
    finite_exceptional_degree z hH.eigenvalues hiz (hω n).1 a b⟩
  intro t
  let f (j : Fin (n+2)→Bool) := Complex.exp (Complex.I*((t * -hH.eigenvalues j : ℝ):ℂ))
  have heval (j) : (p t).eval (z j)=f j := Lagrange.eval_interpolate_at_node f hn (Finset.mem_univ j)
  have hdeg := Lagrange.degree_interpolate_lt f hn
  rw [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hdeg
  refine ⟨hdeg,?_⟩
  have hp : (fun j => (p t).eval (z j)) =
      (fun j => Complex.exp (-(Complex.I*((t:ℂ)*(hH.eigenvalues j:ℂ))))) := by
    funext j
    rw [heval]
    apply congrArg Complex.exp
    push_cast
    ring
  rw [spectral_aeval,hp,spectralFunction,Unitary.conjStarAlgAut_apply,unitaryEvolution_spectral hH]

#print axioms gaussian_firstZ_orbit_degree
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
