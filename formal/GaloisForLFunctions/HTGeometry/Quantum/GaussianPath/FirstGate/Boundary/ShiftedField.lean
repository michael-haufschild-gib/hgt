import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.SectorHamiltonian
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Physical boundary slopes from the inverse-splitting chart -/
open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

def sectorZ (I : Type*) [Fintype I] [DecidableEq I] : Mat (I ⊕ I) :=
  fromBlocks (1 : Mat I) 0 0 (-1 : Mat I)

theorem shift_sector (H W : Mat I) (d s : ℂ) :
    sectorMatrix H W W d+s • sectorZ I = sectorMatrix H W W (d+s) := by
  simp only [sectorMatrix,sectorZ,fromBlocks_smul,fromBlocks_add,add_smul,smul_zero,add_zero,smul_neg,sub_eq_add_neg]
  congr 1 <;> abel

def shifted (e : ℂ→ℂ) (d s : ℂ) := d+s+e ((d+s)⁻¹)

theorem shifted_response (e : ℂ→ℂ) (d : ℂ) (hd : d≠0) (he : AnalyticAt ℂ e d⁻¹) :
    AnalyticAt ℂ (shifted e d) 0 ∧ shifted e d 0=d+e d⁻¹ ∧
    deriv (shifted e d) 0=1-(d⁻¹)^2*deriv e d⁻¹ := by
  have hn : d+(0:ℂ) ≠ 0 := by simpa using hd
  have ha : AnalyticAt ℂ (fun s : ℂ => d+s) 0 := analyticAt_const.add analyticAt_id
  have hr : HasDerivAt (fun s : ℂ => d+s) 1 0 := (hasDerivAt_id (0:ℂ)).const_add d
  have hrat := ha.inv hn
  have hE : AnalyticAt ℂ e ((d+0)⁻¹) := by simpa using he
  refine ⟨ha.add (hE.comp (f := fun s : ℂ => (d+s)⁻¹) (x := 0) hrat),by simp [shifted],?_⟩
  have h := (hr.add (hE.differentiableAt.hasDerivAt.comp 0 (hr.inv hn))).deriv
  simpa only [shifted,add_zero,one_div,neg_one_mul,div_eq_mul_inv,inv_pow,neg_mul,mul_neg,←sub_eq_add_neg,
    mul_comm (deriv e d⁻¹),one_mul,Pi.add_def,Pi.inv_def,Function.comp_def] using! h

theorem shifted_root (H W : Mat I) (e : ℂ→ℂ) (d : ℂ) (hd : d≠0)
    (hr : ∀ᶠ u in 𝓝 d⁻¹, splitDet (scalar I (e u)-H) W W 2 u=0) :
    ∀ᶠ s in 𝓝 (0:ℂ), matrixCharpolyRelation (sectorMatrix H W W (d+s),shifted e d s)=0 := by
  have hn : d+(0:ℂ)≠0 := by simpa using hd
  have hcont : ContinuousAt (fun s : ℂ => d+s) 0 := continuousAt_const.add continuousAt_id
  have ht : Tendsto (fun s : ℂ => (d+s)⁻¹) (𝓝 0) (𝓝 d⁻¹) := by simpa using! (hcont.inv₀ hn).tendsto
  filter_upwards [ht.eventually hr,hcont.eventually_ne hn] with s hs hds
  have h := splitDet_physical H W W (d+s) (d+s)⁻¹ (e (d+s)⁻¹)
  rw [show (d+s)⁻¹*(2*(d+s))=2 by field_simp [hds],hs] at h
  have hroot := (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (inv_ne_zero hds))
  simpa only [shifted,add_comm (e (d+s)⁻¹) (d+s)] using hroot

end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
