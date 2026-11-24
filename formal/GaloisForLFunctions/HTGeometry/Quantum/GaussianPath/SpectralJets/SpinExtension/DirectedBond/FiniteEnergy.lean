import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ProjectedBranch
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.EnergySeparation

/-! # Restoring finite physical energies on both tilted sectors -/
open Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local notation "P" => (E × ℂ) × ℂ

/-- Physical energy in a normalized transverse-field coordinate. -/
def energy (b : Bool) (e : P × ℂ → ℂ) (n : ℕ) (p : P) :=
  (sign b*splitting p.2)*height n+e (p,inverseHeight n)

theorem sector_square (b : Bool) (t : ℂ) :
    (sign b*splitting t)^2=(3/5:ℂ)^2+(4/5+t)^2 := by
  cases b <;> simp [sign,splitting_square,base_square]

/-- Each regular branch gives an analytic physical root on a neighborhood
of zero controls for every sufficiently large integer splitting. -/
theorem finite_energy (b : Bool) (H : E→M) (A : M) (e : P × ℂ → ℂ)
    (he : AnalyticAt ℂ e 0)
    (hr : ∀ᶠ q : P × ℂ in 𝓝 0,
      (reduced (scalar I (e q)-H q.1.1.1) (q.1.1.2 • A) (3/5) (sign b*splitting q.1.2) q.2).det=0) :
    ∀ᶠ n : ℕ in atTop, AnalyticAt ℂ (energy b e n) 0 ∧ ∀ᶠ p : P in 𝓝 0,
      matrixCharpolyRelation (physical (H p.1.1) (p.1.2 • A) ((3/5)*height n)
        ((4/5+p.2)*height n),energy b e n p)=0 := by
  have ht : Tendsto (fun n => ((0:P),inverseHeight n)) atTop (𝓝 0) :=
    tendsto_const_nhds.prodMk_nhds inverseHeight_tendsto
  have hg : AnalyticAt ℂ (fun p : P => splitting p.2) 0 :=
    (profile_analytic (1/2)).comp (f:=fun p : P => p.2) (x:=0) analyticAt_snd
  have hd : ∀ᶠ p : P in 𝓝 0, (4/5:ℂ)+p.2≠0 :=
    (continuousAt_const.add continuousAt_snd).eventually_ne (by change (4/5:ℂ)+0≠0; norm_num)
  filter_upwards [ht.eventually he.eventually_analyticAt,ht.eventually hr.eventually_nhds] with n han hroot
  have hs : AnalyticAt ℂ (fun p : P => (p,inverseHeight n)) 0 := analyticAt_id.prod analyticAt_const
  have he' : AnalyticAt ℂ (fun p : P => e (p,inverseHeight n)) 0 :=
    han.comp (f:=fun p : P => (p,inverseHeight n)) (x:=0) hs
  refine ⟨((analyticAt_const.mul hg).mul analyticAt_const).add he',?_⟩
  filter_upwards [hs.continuousAt.tendsto.eventually hroot,hd] with p hp hne
  exact reduced_root_physical _ _ _ (sector_square b p.2) (height_mul_inverse n)
    (mul_ne_zero hne (height_ne_zero n)) hp

#print axioms finite_energy
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
