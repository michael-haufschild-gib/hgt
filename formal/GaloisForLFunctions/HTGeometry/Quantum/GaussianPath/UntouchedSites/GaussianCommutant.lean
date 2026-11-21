import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.GenericRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.PathWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.Coercivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # A single site distinguishes the commutant of a Gaussian Pauli path -/
open Matrix MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section
variable {n : ℕ}

private def silent (v : Fin (n+2)) (r : Fin (n+2) → Bool) : Submodule ℂ (SpinMatrix (Fin (n+2))) :=
  (Matrix.entryLinearMap ℂ ℂ r r).ker ⊓ ⨅ a : Fin 3, (bracket (spin v a)).ker

private theorem mem_silent (v : Fin (n+2)) (r : Fin (n+2) → Bool) (X : SpinMatrix (Fin (n+2))) :
    X ∈ silent v r ↔ X r r = 0 ∧ ∀ a, spin v a*X = X*spin v a := by
  simp only [silent,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker]
  change (X r r=0 ∧ ∀ a, spin v a*X-X*spin v a=0) ↔ _
  simp only [sub_eq_zero]

private abbrev Count (n : ℕ) := Fintype.card (ChainLabel (n+2))
private def response (v : Fin (n+2)) (r : Fin (n+2) → Bool) (i : Fin (Count n)) :
    silent v r →ₗ[ℂ] SpinMatrix (Fin (n+2)) :=
  (bracket (finitePauliMatrix (pathWord (pathCoeffEquiv n i)))).comp (silent v r).subtype

private theorem response_eq (v : Fin (n+2)) (r : Fin (n+2) → Bool) (u : PathShell n)
    (X : silent v r) :
    pencil (response v r) (fun i => u (pathCoeffEquiv n i)) X =
      pathHamiltonian u*X.val-X.val*pathHamiltonian u := by
  have hH : pathHamiltonian u = ∑ i, (u (pathCoeffEquiv n i):ℂ) •
      finitePauliMatrix (pathWord (pathCoeffEquiv n i)) := by
    rw [pathHamiltonian_eq_sum]
    exact ((pathCoeffEquiv n).sum_comp (fun l => (u l:ℂ) • finitePauliMatrix (pathWord l))).symm
  rw [hH,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  simp only [pencil,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.smul_mul,Matrix.mul_smul,←smul_sub]
  rfl

private theorem one_site_ae (n : ℕ) (v : Fin (n+2)) (r : Fin (n+2) → Bool) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ X : SpinMatrix (Fin (n+2)),
      pathHamiltonian (pathPauliDisorderShell ω n)*X = X*pathHamiltonian (pathPauliDisorderShell ω n) →
      (∀ a, spin v a*X = X*spin v a) → X = X r r • (1 : SpinMatrix (Fin (n+2))) := by
  let w (i : Fin (Count n)) := detectingShell n (pathCoeffEquiv n i)
  have hw : Function.Injective (pencil (response v r) w) := by
    rw [←LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro X hx
    have hm := (mem_silent v r X.val).mp X.property
    have eqH := (response_eq v r (detectingShell n) X).symm.trans hx
    have hu := witness_scalar v r X.val (sub_eq_zero.mp eqH).symm (fun a => (hm.2 a).symm)
    apply Subtype.ext
    exact hu.trans (by rw [hm.1,zero_smul]; rfl)
  have hac : centredProductGaussian (Fin (Count n)) 1 ≪ volume := by
    simpa [centredProductGaussian] using productGaussian_absolutelyContinuous (Count n) one_ne_zero (fun _ => 0)
  have h := (gaussian_pauli_prefix_coordinates_law n).quasiMeasurePreserving.ae
    (hac.ae_le (pencil_ae_injective (response v r) w hw))
  filter_upwards [h] with ω hω X hH hP
  let Y := X-X r r • (1 : SpinMatrix (Fin (n+2)))
  have he (M : SpinMatrix (Fin (n+2))) (hm : M*X=X*M) : M*Y=Y*M := by
    dsimp only [Y]
    rw [mul_sub,sub_mul,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,hm]
  have hm : Y ∈ silent v r := (mem_silent v r Y).mpr ⟨by simp [Y],fun a => he _ (hP a)⟩
  let Z : silent v r := ⟨Y,hm⟩
  have hz := (response_eq v r (pathPauliDisorderShell ω n) Z).trans (sub_eq_zero.mpr (he _ hH))
  have hz' : Z = 0 := hω (hz.trans (map_zero _).symm)
  exact sub_eq_zero.mp (congrArg Subtype.val hz')

/-- Almost surely, on every finite path, H and the three axes at any
single site have only scalars in their joint commutant. -/
theorem gaussian_one_site_scalar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n, ∀ v : Fin (n+2),
      let r : Fin (n+2) → Bool := fun _ => false
      ∀ X : SpinMatrix (Fin (n+2)),
        pathHamiltonian (pathPauliDisorderShell ω n)*X = X*pathHamiltonian (pathPauliDisorderShell ω n) →
        (∀ a, spin v a*X=X*spin v a) → X=X r r • (1 : SpinMatrix (Fin (n+2))) :=
  ae_all_iff.mpr fun n => ae_all_iff.mpr fun v => one_site_ae n v _

#print axioms gaussian_one_site_scalar
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
