import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheFullParabolicRayJetOfTheHeatFamily
import GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision
import GaloisForLFunctions.RHTower.XiSliceMixedClassDetection
import GaloisForLFunctions.Bottcher.ArgumentPrinciple

/-!
# A rigid second-order translation of the colliding heat sheets

At an order-m collision, every sheet has expansion
z + ρs + d s² + O(s³), where
d = 2 H⁽ᵐ⁺¹⁾(z)/((m+1) H⁽ᵐ⁾(z)). The drift d is common to all
Hermite roots. Every pair, including nonopposite sheets, consequently
has a squared gap (ρ−η)² s² with an analytic remainder divisible by s⁴.
-/

noncomputable section
open Complex Filter Topology RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

open private fderiv_collisionBlowup_ne_zero from GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision

/-- Every radial derivative of the analytic blow-up is determined by
a single spatial derivative and the corresponding parabolic Hermite polynomial. -/
theorem IsCollision.blowup_ray_jet {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) (y : ℂ) (j : ℕ) :
    (((m+j).choose m*m.factorial:ℕ):ℂ)*iteratedDeriv j (fun s : ℂ => collisionBlowup τ z m (s,y)) 0 =
      parabolicRayPolynomial (m+j) y*iteratedDeriv (m+j) (complexHeat τ) z := by
  have hd : Differentiable ℂ (fun s : ℂ => collisionBlowup τ z m (s,y)) := fun s =>
    ((analyticAt_collisionBlowup τ z m (s,y)).comp (analyticAt_id.prod analyticAt_const)).differentiableAt
  have h := heat_parabolic_ray_derivative τ z y (m+j) 0
  simp only [iteratedDeriv_zero,Nat.zero_add] at h
  rw [show (fun s : ℂ => complexHeat (τ+s^2) (z+s*y))=(fun s => s^m*collisionBlowup τ z m (s,y)) from
    funext fun s => complexHeat_blowup hc.vanish s y,iteratedDeriv_pow_mul_zero hd,
    if_pos (Nat.le_add_right m j),Nat.add_sub_cancel_left] at h
  exact h

/-- Common translation coefficient for all roots in the physical time τ+s². -/
def collisionDrift (τ z : ℂ) (m : ℕ) : ℂ :=
  2*iteratedDeriv (m+1) (complexHeat τ) z / (((m:ℂ)+1)*iteratedDeriv m (complexHeat τ) z)

theorem IsCollision.all_branches_have_one_drift {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hr : heatModelFwd m ρ=0) : deriv (collisionBranch τ z m ρ) 0=collisionDrift τ z m := by
  let G := collisionBlowup τ z m
  let Y := collisionBranch τ z m ρ
  let D := fderiv ℂ G (0,ρ)
  let A := iteratedDeriv m (complexHeat τ) z
  let B := iteratedDeriv (m+1) (complexHeat τ) z
  let F : ℂ := m.factorial
  let q := parabolicRayPolynomial m
  have hF : F≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hA : A≠0 := hc.top_ne_zero
  have hM : (m:ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero m
  have hval (u : ℂ) : F*G (0,u)=q u*A := by
    simpa only [Nat.add_zero,Nat.choose_self,one_mul,iteratedDeriv_zero] using hc.blowup_ray_jet u 0
  have hzero : G (0,ρ)=0 := by rw [show G (0,ρ)=_ from collisionBlowup_zero hc.vanish ρ,hr,mul_zero]
  have hq : q ρ=0 := (mul_eq_zero.mp ((hval ρ).symm.trans (by rw [hzero,mul_zero]))).resolve_right hA
  have hd := (analyticAt_collisionBlowup τ z m (0,ρ)).differentiableAt.hasFDerivAt
  have hx : deriv (fun s : ℂ => G (s,ρ)) 0=D (1,0) :=
    (hd.comp_hasDerivAt 0 ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 ρ))).deriv
  have hz := hd.comp_hasDerivAt ρ ((hasDerivAt_const ρ (0:ℂ)).prodMk (hasDerivAt_id ρ))
  have hp : HasDerivAt q (deriv q ρ) ρ := ((heatShiftPoly (1/4) m).hasDerivAt_aeval ρ).differentiableAt.hasDerivAt
  have hspace : F*D (0,1)=deriv q ρ*A :=
    (hz.const_mul F).unique ((hp.mul_const A).congr_of_eventuallyEq (Eventually.of_forall hval))
  have hcnt : (m+1).choose m=m+1 := by
    rw [←Nat.choose_symm (Nat.le_succ m),show m+1-m=1 by omega,Nat.choose_one_right]
  have htime := hc.blowup_ray_jet ρ 1
  rw [hcnt,Nat.cast_mul,Nat.cast_succ,iteratedDeriv_one,hx,parabolic_ray_raise,hq,mul_zero,zero_sub] at htime
  change (((m:ℂ)+1)*F)*D (1,0)= -(2*deriv q ρ)*B at htime
  obtain ⟨hY,hY0,hYZ,_⟩ := collisionBranch_spec hc hr
  have hD' : HasFDerivAt G D (0,Y 0) := by rw [show Y 0=ρ from hY0]; exact hd
  have hzero' := (hD'.comp_hasDerivAt 0 ((hasDerivAt_id 0).prodMk hY.differentiableAt.hasDerivAt)).unique
    ((hasDerivAt_const (0:ℂ) (0:ℂ)).congr_of_eventuallyEq hYZ)
  change D (1,deriv Y 0)=0 at hzero'
  rw [show ((1:ℂ),deriv Y 0) = ((1,0):ℂ × ℂ) + deriv Y 0 • ((0,1):ℂ × ℂ) by ext <;> simp,
    map_add,map_smul,smul_eq_mul] at hzero'
  have hq' : deriv q ρ≠0 := fun he => (mul_ne_zero hF (fderiv_collisionBlowup_ne_zero hc hr))
    (hspace.trans (by rw [he,zero_mul]))
  change deriv Y 0=2*B/(((m:ℂ)+1)*A)
  apply (eq_div_iff (mul_ne_zero hM hA)).mpr
  apply mul_left_cancel₀ hq'
  linear_combination (((m:ℂ)+1)*F)*hzero' - htime - (((m:ℂ)+1)*deriv Y 0)*hspace

/-- The leading motion distinguishes the root; the first physical-time
correction is shared. The remaining factor is analytic on the square-root cover. -/
theorem IsCollision.sheet_after_common_translation {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hr : heatModelFwd m ρ=0) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ ∀ᶠ s in 𝓝 0,
      collisionZero τ z m ρ s=z+ρ*s+collisionDrift τ z m*s^2+s^3*V s := by
  let Y := collisionBranch τ z m ρ
  obtain ⟨hY,hY0,_,_⟩ := collisionBranch_spec hc hr
  obtain ⟨u,hu,h₁,hu0⟩ := Bottcher.analyticAt_simple_factor (hY.sub (analyticAt_const (v:=ρ)))
    (by change Y 0-ρ=0; rw [hY0,sub_self])
  have hder : deriv (fun s => Y s-ρ) 0=collisionDrift τ z m :=
    (hY.differentiableAt.hasDerivAt.sub_const ρ).deriv.trans (hc.all_branches_have_one_drift hr)
  have hu₀ : u 0=collisionDrift τ z m := hu0.trans hder
  obtain ⟨v,hv,h₂,_⟩ := Bottcher.analyticAt_simple_factor
    (hu.sub (analyticAt_const (v:=collisionDrift τ z m))) (by simp only [Pi.sub_apply,hu₀,sub_self])
  refine ⟨v,hv,Eventually.of_forall fun s => ?_⟩
  have ha : Y s-ρ=s*u s := by simpa only [sub_zero] using h₁ s
  have hb : u s-collisionDrift τ z m=s*v s := by simpa only [sub_zero] using h₂ s
  change z+s*Y s=z+ρ*s+collisionDrift τ z m*s^2+s^3*v s
  linear_combination s*ha+s^2*hb

/-- Even without a reflected pairing, the squared gap has no cubic
term on the cover. In physical time its error is of quadratic order. -/
theorem IsCollision.arbitrary_pair_squared_gap {τ z ρ η : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hρ : heatModelFwd m ρ=0) (hη : heatModelFwd m η=0) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ ∀ᶠ s in 𝓝 0,
      (collisionZero τ z m ρ s-collisionZero τ z m η s)^2=(ρ-η)^2*s^2+s^4*V s := by
  obtain ⟨u,hu,h₁⟩ := hc.sheet_after_common_translation hρ
  obtain ⟨v,hv,h₂⟩ := hc.sheet_after_common_translation hη
  let d (s : ℂ) := u s-v s
  have hd : AnalyticAt ℂ d 0 := hu.sub hv
  refine ⟨fun s => (2*(ρ-η)+s^2*d s)*d s,(analyticAt_const.add ((analyticAt_id.pow 2).mul hd)).mul hd,?_⟩
  filter_upwards [h₁,h₂] with s ha hb
  rw [ha,hb]
  dsimp only [d]
  ring

#print axioms IsCollision.blowup_ray_jet
#print axioms IsCollision.all_branches_have_one_drift
#print axioms IsCollision.sheet_after_common_translation
#print axioms IsCollision.arbitrary_pair_squared_gap
end GaloisForLFunctions.GaloisTheoryOfZeros
