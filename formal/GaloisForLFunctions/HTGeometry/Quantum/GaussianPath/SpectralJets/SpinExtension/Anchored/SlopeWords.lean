import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.Anchored.JointSlope
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectionalWords

/-! # Lifting old spectral response words through a transverse bond -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev M := Matrix I I ℂ

private theorem product_line (W V A B : M) (l : ℂ) :
    (W+l • A)*(V+l • B)=W*V+l • (A*V+W*B)+l^2 • (A*B) := by
  rw [add_mul,mul_add,mul_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,smul_add,pow_two]
  abel

/-- At inverse splitting zero, the bond derivative of the sector velocity
removes the common transverse background. The identity is local in the old
matrix, so it persists after every ordered old response word. -/
theorem transverse_word (H W V A B : M) (b : ℂ) (f : M → ℂ) (e : Blocks I × ℂ → ℂ)
    (hslope : ∀ᶠ p : Blocks I in 𝓝 (H,W,V), deriv (fun u : ℂ => e (p,u)) 0 =
      fderiv ℂ f p.1 (b⁻¹ • (p.2.1*p.2.2))) (w : List M) :
    response w (fun K => deriv (fun l : ℂ =>
      deriv (fun u : ℂ => e ((K,W+l • A,V+l • B),u)) 0) 0) H =
    response w (fun K => fderiv ℂ f K (b⁻¹ • (A*V+W*B))) H := by
  apply (response_germ w _).eq_of_nhds
  have hK : Tendsto (fun K : M => (K,W,V)) (𝓝 H) (𝓝 (H,W,V)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  filter_upwards [hK.eventually hslope.eventually_nhds] with K hk
  let L := fderiv ℂ f K
  let p (l : ℂ) : Blocks I := (K,W+l • A,V+l • B)
  have hp : Tendsto p (𝓝 0) (𝓝 (K,W,V)) := by
    have hh : Continuous p := by dsimp only [p]; fun_prop
    simpa only [p,zero_smul,add_zero] using hh.continuousAt (x:=0) |>.tendsto
  let c := L (b⁻¹ • (W*V))
  let d := L (b⁻¹ • (A*V+W*B))
  let v := L (b⁻¹ • (A*B))
  have hpoly : (fun l : ℂ => deriv (fun u : ℂ => e (p l,u)) 0) =ᶠ[𝓝 0]
      (fun l => c+l*d+l^2*v) := by
    filter_upwards [hp.eventually hk] with l hl
    rw [hl]
    change L (b⁻¹ • ((W+l • A)*(V+l • B)))=_
    rw [product_line]
    simp only [smul_add,map_add,map_smul,smul_eq_mul,c,d,v]
    ring
  have hd := (((hasDerivAt_id (0:ℂ)).mul_const d).const_add c).add
    (((hasDerivAt_id (0:ℂ)).pow 2).mul_const v)
  exact hpoly.deriv_eq.trans (by simpa using hd.deriv)

#print axioms transverse_word
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
