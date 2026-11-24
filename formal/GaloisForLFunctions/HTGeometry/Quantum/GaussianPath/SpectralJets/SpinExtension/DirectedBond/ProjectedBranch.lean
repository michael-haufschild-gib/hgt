import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.RegularBranch
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.TiltResponses

/-! # Physical energy branches on the two tilted spin sectors -/
open Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local notation "P" => (E × ℂ) × ℂ

def sign : Bool→ℂ | false => 1 | true => -1

private theorem projected_scalar (b : Bool) (t : ℂ) :
    (3/5:ℂ)/(sign b*splitting t)=sign b*alignment t := by
  cases b <;> simp [sign,alignment_eq_div,div_eq_mul_inv]

/-- The projected old field in sector b, as a function of the old controls,
the bond and the new tilt. -/
def projectField (b : Bool) (p : P) : E × ℂ :=
  (p.1.1, (sign b*alignment p.2)*p.1.2)

omit [NormedSpace ℂ E] [CompleteSpace E] in
@[simp] theorem projectField_zero (b : Bool) : projectField (E:=E) b 0=0 := by
  change ((0:E),(sign b*alignment 0)*0)=0
  rw [mul_zero]
  rfl

omit [CompleteSpace E] in
private theorem analytic_projectField (b : Bool) : AnalyticAt ℂ (projectField (E:=E) b) 0 := by
  have ha : AnalyticAt ℂ alignment 0 := analyticAt_const.mul (profile_analytic _)
  have hx : AnalyticAt ℂ (fun q : P => q.1.1) 0 := analyticAt_fst.comp analyticAt_fst
  have hz : AnalyticAt ℂ (fun q : P => alignment q.2) 0 :=
    ha.comp (f:=fun q : P => q.2) (x:=0) analyticAt_snd
  exact hx.prod ((analyticAt_const.mul hz).mul (analyticAt_snd.comp analyticAt_fst))

/-- A simple eigenvalue of the old spin chain extends jointly in all controls
and inverse splitting. The limiting surface is the old branch with its
terminal field multiplied by the signed longitudinal alignment. -/
theorem tilted_branch (b : Bool) (H : E→M) (A : M) (f : E × ℂ → ℂ)
    (hH : AnalyticAt ℂ H 0) (hf : AnalyticAt ℂ f 0)
    (hr : ∀ᶠ p in 𝓝 (0 : E × ℂ), matrixCharpolyRelation (H p.1+p.2 • A,f p)=0)
    (hs : (H 0).charpoly.derivative.eval (f 0)≠0) :
    ∃ e : P × ℂ → ℂ, AnalyticAt ℂ e 0 ∧ e 0=f 0 ∧
      (∀ᶠ p : P in 𝓝 0, e (p,0)=f (projectField b p)) ∧
      ∀ᶠ q : P × ℂ in 𝓝 0,
        (reduced (scalar I (e q)-H q.1.1.1) (q.1.1.2 • A)
          (3/5) (sign b*splitting q.1.2) q.2).det=0 := by
  let Z (p : P) := sign b*splitting p.2
  let V (p : P) := p.1.2 • A
  let K (p : P) := H p.1.1
  let F := f ∘ projectField b
  have hx : AnalyticAt ℂ (fun q : P => q.1.1) 0 := analyticAt_fst.comp analyticAt_fst
  have hK : AnalyticAt ℂ K 0 := hH.comp (f:=fun q : P => q.1.1) (x:=0) hx
  have hV : AnalyticAt ℂ V 0 := (analyticAt_snd.comp analyticAt_fst).smul analyticAt_const
  have hg : AnalyticAt ℂ (fun q : P => splitting q.2) 0 :=
    (profile_analytic (1/2)).comp (f:=fun q : P => q.2) (x:=0) analyticAt_snd
  have hZ : AnalyticAt ℂ Z 0 := analyticAt_const.mul hg
  have hn : Z 0≠0 := by cases b <;> simp [Z,sign,splitting]
  have hπ := analytic_projectField (E:=E) b
  have heq (p : P) : K p+((3/5:ℂ)/Z p) • V p = H (projectField b p).1+(projectField b p).2 • A := by
    simp only [K,Z,V,projectField,projected_scalar,smul_smul]
  have ht : Tendsto (projectField (E:=E) b) (𝓝 0) (𝓝 0) := by simpa using hπ.continuousAt.tendsto
  have hF : AnalyticAt ℂ F 0 := (show AnalyticAt ℂ f (projectField b 0) by simpa using hf).comp hπ
  have hroot : ∀ᶠ p in 𝓝 0, matrixCharpolyRelation (K p+((3/5:ℂ)/Z p) • V p,F p)=0 :=
    (ht.eventually hr).mono fun p hp => by simpa only [heq,F,Function.comp_apply] using hp
  have hsimple : (K 0+((3/5:ℂ)/Z 0) • V 0).charpoly.derivative.eval (F 0)≠0 := by
    simpa only [heq,projectField_zero,Prod.fst_zero,Prod.snd_zero,zero_smul,add_zero,F,Function.comp_apply] using hs
  obtain ⟨e,ha,h0,he,hr'⟩ := regular_branch (3/5) hK hV hZ hF hn hroot hsimple
  refine ⟨e,ha,?_,he,hr'⟩
  change e ((0:P),(0:ℂ))=f 0
  exact h0.trans (congrArg f (projectField_zero b))

#print axioms tilted_branch
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
