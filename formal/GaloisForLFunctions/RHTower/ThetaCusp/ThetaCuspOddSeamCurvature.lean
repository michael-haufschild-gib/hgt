import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamCurvatureModel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamCurvatureMoments
/-!
# Positive actual-source quadratic curvature at the modular seam

The complete signed moments identify the exact second jets of all relevant
cofactors. Quotient differentiation cancels the actual source mass. At the
fixed load C4=10^13, the resulting normalized curvature is strictly positive
for every real correction direction. Propagation to nonzero centers across
the compact region remains open.
-/
namespace RHTower.ThetaOddSeamCurvature
noncomputable section
open scoped ContDiff

/-- Exact even two-jet used only to identify the actual cofactor curvature. -/
structure SeamJet (f : ℝ → ℝ) (a b : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  value : f 0=a
  first : deriv f 0=0
  second : deriv (deriv f) 0=b

namespace SeamJet
variable {f g : ℝ → ℝ} {a b c d : ℝ}

private theorem second_eq_iterated (f : ℝ → ℝ) :
    deriv (deriv f) 0=iteratedDeriv 2 f 0 := by
  rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]

theorem const (a : ℝ) : SeamJet (fun _ => a) a 0 := by
  constructor
  · fun_prop
  · rfl
  · simp
  · simp

theorem add (hf : SeamJet f a b) (hg : SeamJet g c d) :
    SeamJet (fun x => f x+g x) (a+c) (b+d) := by
  refine ⟨hf.smooth.add hg.smooth,by rw [hf.value,hg.value],?_,?_⟩
  · rw [deriv_fun_add (hf.smooth.differentiable (by simp) 0)
      (hg.smooth.differentiable (by simp) 0),hf.first,hg.first,add_zero]
  · rw [second_eq_iterated,iteratedDeriv_fun_add
      (hf.smooth.of_le (by change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).contDiffAt (hg.smooth.of_le (by change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).contDiffAt,
      ← second_eq_iterated,← second_eq_iterated,hf.second,hg.second]

theorem sub (hf : SeamJet f a b) (hg : SeamJet g c d) :
    SeamJet (fun x => f x-g x) (a-c) (b-d) := by
  refine ⟨hf.smooth.sub hg.smooth,by rw [hf.value,hg.value],?_,?_⟩
  · rw [deriv_fun_sub (hf.smooth.differentiable (by simp) 0)
      (hg.smooth.differentiable (by simp) 0),hf.first,hg.first,sub_self]
  · rw [second_eq_iterated,iteratedDeriv_fun_sub
      (hf.smooth.of_le (by change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).contDiffAt (hg.smooth.of_le (by change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).contDiffAt,
      ← second_eq_iterated,← second_eq_iterated,hf.second,hg.second]

theorem mul (hf : SeamJet f a b) (hg : SeamJet g c d) :
    SeamJet (fun x => f x*g x) (a*c) (b*c+a*d) := by
  refine ⟨hf.smooth.mul hg.smooth,by rw [hf.value,hg.value],?_,?_⟩
  · rw [deriv_fun_mul (hf.smooth.differentiable (by simp) 0)
      (hg.smooth.differentiable (by simp) 0),hf.first,hg.first]
    ring
  · rw [second_eq_iterated,iteratedDeriv_fun_mul
      (hf.smooth.of_le (by change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).contDiffAt (hg.smooth.of_le (by change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).contDiffAt]
    norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_succ,iteratedDeriv_zero,
      hf.value,hg.value,hf.first,hg.first,hf.second,hg.second]
    ring

theorem neg (hf : SeamJet f a b) : SeamJet (fun x => -f x) (-a) (-b) := by
  convert (const (-1)).mul hf using 1 <;> simp

theorem inv (hf : SeamJet f a b) (hn : ∀ x, f x≠0) :
    SeamJet (fun x => (f x)⁻¹) a⁻¹ (-b/a^2) := by
  have hs := hf.smooth.inv hn
  have hval : (f 0)⁻¹=a⁻¹ := by rw [hf.value]
  have hfirst : deriv (fun x => (f x)⁻¹) 0=0 := by
    have hd := (hf.smooth.differentiable (by simp) 0).hasDerivAt.inv (hn 0)
    change HasDerivAt (fun x => (f x)⁻¹) _ 0 at hd
    rw [hd.deriv,hf.first]
    simp
  have ht : SeamJet (fun x => (f x)⁻¹) a⁻¹ (deriv (deriv (fun x => (f x)⁻¹)) 0) :=
    ⟨hs,hval,hfirst,rfl⟩
  have h := (hf.mul ht).second
  have he : (fun x => f x*(f x)⁻¹)=(fun _ : ℝ => (1:ℝ)) := by
    funext x
    exact mul_inv_cancel₀ (hn x)
  rw [he] at h
  try simp at h
  have ha : a≠0 := by rw [← hf.value]; exact hn 0
  refine ⟨hs,hval,hfirst,?_⟩
  apply (eq_div_iff (pow_ne_zero 2 ha)).mpr
  field_simp at h
  simp only [one_div,zero_mul] at h
  nlinarith only [h]

end SeamJet
end
end RHTower.ThetaOddSeamCurvature

namespace RHTower.ThetaOddSeamCurvature
noncomputable section
open scoped ContDiff
open ThetaCuspOddDirectionTransport
open HTGeometry.ThetaSeamOddCurvature
local notation "Phi" => thetaCuspFullSource
local notation "mass" => thetaCuspSelfDualThetaMass
local notation "scale" => thetaCuspSelfDualModularScale^2
local notation "G" => thetaCuspCenterCompensationSource
local notation "Hactual" => thetaCuspNativeOddHeadDet
local notation "Dactual" => thetaCuspNativeOddHankelThreeDet

private theorem source_smooth (n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n Phi) := by
  rw [iteratedDeriv_eq_iterate]
  exact contDiff_thetaCuspFullSource.iterate_deriv n

private theorem source_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n Phi) (iteratedDeriv (n+1) Phi x) x := by
  simp_rw [iteratedDeriv_thetaCuspFullSource]
  exact hasDerivAt_thetaCuspFullDerivative n x

private theorem moment_smooth (k : Fin 7) : ContDiff ℝ ∞ (moment k) := by
  have hs := source_smooth
  unfold moment
  simp_rw [thetaCuspNativeReflectionJet_eq]
  fun_prop

private theorem moment_jet (k : Fin 7) : SeamJet (moment k)
    (mass^2*mH (k.val+1) scale 1) (mass^2*vH (k.val+1) scale 1) := by
  refine ⟨moment_smooth k,?_,moment_first_zero k,?_⟩
  · rw [mH_one]
    exact native_value k
  · rw [vH_one]
    exact moment_second_zero k

private theorem head_jet : SeamJet Hactual (mass^4*HTGeometry.ThetaSeamOddCurvature.H scale 1) (mass^4*H2 scale 1) := by
  have h := ((moment_jet 0).mul (moment_jet 2)).sub ((moment_jet 1).mul (moment_jet 1))
  convert h using 1
  · funext x
    norm_num [thetaCuspNativeOddHeadDet,moment]
    ring
  · norm_num [HTGeometry.ThetaSeamOddCurvature.H]
    ring
  · norm_num [H2]
    ring

private theorem A_jet : SeamJet cofactorA (mass^6*A scale 1) (mass^6*A2 scale 1) := by
  let j := moment_jet
  have h := (((((j 0).mul (j 2)).mul (j 6)).sub ((j 0).mul ((j 4).mul (j 4)))).sub
    (((j 1).mul (j 1)).mul (j 6))).add ((((SeamJet.const 2).mul (j 1)).mul (j 3)).mul (j 4))
  have h := h.sub ((j 2).mul ((j 3).mul (j 3)))
  convert h using 1
  · funext x
    unfold cofactorA
    ring
  · norm_num [A]
    ring
  · norm_num [A2]
    ring

private theorem B_jet : SeamJet cofactorB (mass^6*B scale 1) (mass^6*B2 scale 1) := by
  let j := moment_jet
  have h := ((((((j 0).mul (j 2)).mul (j 5)).sub (((j 0).mul (j 3)).mul (j 4))).sub
    (((j 1).mul (j 1)).mul (j 5))).add (((j 1).mul (j 2)).mul (j 4))).add
    ((j 1).mul ((j 3).mul (j 3)))
  have h := (h.sub (((j 2).mul (j 2)).mul (j 3))).neg
  convert h using 1
  · funext x
    unfold cofactorB
    ring
  · norm_num [B]
    ring
  · norm_num [B2]
    ring

private theorem D_jet : SeamJet Dactual (mass^6*D scale 1) (mass^6*D2 scale 1) := by
  let j := moment_jet
  have h := (((((j 0).mul (j 2)).mul (j 4)).sub ((j 0).mul ((j 3).mul (j 3)))).sub
    (((j 1).mul (j 1)).mul (j 4))).add ((((SeamJet.const 2).mul (j 1)).mul (j 2)).mul (j 3))
  have h := h.sub (((j 2).mul (j 2)).mul (j 2))
  convert h using 1
  · funext x
    norm_num [thetaCuspNativeOddHankelThreeDet,HilbertMetric.signedEvenHankelThreeDet,moment]
    ring
  · norm_num [D]
    ring
  · norm_num [D2]
    ring

private theorem Phi_jet : SeamJet Phi (mass*pH 0 scale 1) (mass*pH 1 scale 1) := by
  refine ⟨contDiff_thetaCuspFullSource,?_,?_,?_⟩
  · rw [pH_one]
    change Phi 0=mass*P 0 scale
    simpa only [Fin.val_zero,mul_zero,iteratedDeriv_zero] using source_even (0:Fin 9)
  · simpa only [iteratedDeriv_one] using
      iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=1) (by norm_num : Odd 1)
  · rw [pH_one]
    change deriv (deriv Phi) 0=mass*P 1 scale
    simpa only [Fin.val_one,show 2*1=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
      source_even (1:Fin 9)

private theorem Phi_six_jet : SeamJet (fun x => Phi x^6)
    ((mass*pH 0 scale 1)^6) (6*(mass*pH 0 scale 1)^5*(mass*pH 1 scale 1)) := by
  have h2 := Phi_jet.mul Phi_jet
  have h := h2.mul (h2.mul h2)
  convert h using 1
  · funext x
    ring
  · ring
  · ring

private def gFirst (x : ℝ) : ℝ :=
  8*Phi x*iteratedDeriv 1 Phi x+2*x*((iteratedDeriv 1 Phi x)^2+Phi x*iteratedDeriv 2 Phi x)

private theorem g_deriv (x : ℝ) : HasDerivAt G (gFirst x) x := by
  have h := (((source_deriv 0 x).pow 2).const_mul 3).add
    ((((hasDerivAt_id x).const_mul 2).mul (source_deriv 0 x)).mul (source_deriv 1 x))
  convert h using 1 <;> first
    | rfl
    | { funext y
        simp only [thetaCuspCenterCompensationSource,iteratedDeriv_zero,iteratedDeriv_one,
          Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq] }
    | { simp only [gFirst,Nat.reduceAdd,iteratedDeriv_succ,iteratedDeriv_zero,Pi.mul_apply,id_eq]
        ring }

private theorem G_jet : SeamJet G (3*(mass*pH 0 scale 1)^2)
    (10*(mass*pH 0 scale 1)*(mass*pH 1 scale 1)) := by
  have h0 := Phi_jet.value
  have h1 := Phi_jet.first
  have h2 := Phi_jet.second
  have hg : deriv G=gFirst := funext (fun x => (g_deriv x).deriv)
  refine ⟨?_,?_,?_,?_⟩
  · have hp := contDiff_thetaCuspFullSource
    have hs := source_smooth 1
    simp only [iteratedDeriv_one] at hs
    unfold thetaCuspCenterCompensationSource
    fun_prop
  · simp [thetaCuspCenterCompensationSource,h0]
  · rw [hg]
    simp [gFirst,iteratedDeriv_one,h1]
  · have hd := ((((source_deriv 0 0).mul (source_deriv 1 0)).const_mul 8).add
      (((hasDerivAt_id 0).const_mul 2).mul
        (((source_deriv 1 0).pow 2).add ((source_deriv 0 0).mul (source_deriv 2 0)))))
    have he : (fun y => 8*(iteratedDeriv 0 Phi y*iteratedDeriv 1 Phi y)+
        2*id y*((iteratedDeriv 1 Phi y)^2+iteratedDeriv 0 Phi y*iteratedDeriv 2 Phi y))=gFirst := by
      funext y
      simp only [iteratedDeriv_zero,id_eq,gFirst]
      ring
    change HasDerivAt (fun y => 8*(iteratedDeriv 0 Phi y*iteratedDeriv 1 Phi y)+
      2*id y*((iteratedDeriv 1 Phi y)^2+iteratedDeriv 0 Phi y*iteratedDeriv 2 Phi y)) _ 0 at hd
    rw [he] at hd
    rw [hg,hd.deriv]
    simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,iteratedDeriv_succ,iteratedDeriv_zero,id_eq,h0,h1,h2]
    ring

private theorem mass_and_source_ne : mass≠0 ∧ pH 0 scale 1≠0 := by
  have hn : mass*pH 0 scale 1≠0 := by
    rw [← Phi_jet.value]
    exact (thetaCuspFullSource_pos_all 0).ne'
  constructor
  · intro h
    exact hn (by rw [h,zero_mul])
  · intro h
    exact hn (by rw [h,mul_zero])

private theorem inverse_six_jet : SeamJet (fun x => (Phi x^6)⁻¹)
    (((mass*pH 0 scale 1)^6)⁻¹)
    (-(6*(mass*pH 0 scale 1)^5*(mass*pH 1 scale 1))/((mass*pH 0 scale 1)^6)^2) :=
  Phi_six_jet.inv (fun x => pow_ne_zero 6 (thetaCuspFullSource_pos_all x).ne')

theorem normalizedBase_second_zero :
    deriv (deriv (normalizedBase 10000000000000)) 0=Na scale 1/(pH 0 scale 1)^7 := by
  have h := (A_jet.add ((SeamJet.const 10000000000000).mul (G_jet.mul head_jet))).mul inverse_six_jet
  have he : (fun x => (cofactorA x+10000000000000*(G x*Hactual x))*(Phi x^6)⁻¹)=
      normalizedBase 10000000000000 := by
    funext x
    unfold normalizedBase
    rw [div_eq_mul_inv]
    ring
  rw [he] at h
  rw [h.second]
  unfold Na
  simp only [one_pow,mul_one]
  field_simp [mass_and_source_ne.1,mass_and_source_ne.2]
  ring

theorem normalizedB_second_zero :
    deriv (deriv normalizedB) 0=Nb scale 1/(pH 0 scale 1)^7 := by
  have h := B_jet.mul inverse_six_jet
  have he : (fun x => cofactorB x*(Phi x^6)⁻¹)=normalizedB := by
    funext x
    simp only [normalizedB,div_eq_mul_inv]
  rw [he] at h
  rw [h.second]
  unfold Nb
  field_simp [mass_and_source_ne.1,mass_and_source_ne.2]
  ring

theorem normalizedD_second_zero :
    deriv (deriv normalizedD) 0=Nd scale 1/(pH 0 scale 1)^7 := by
  have h := D_jet.mul inverse_six_jet
  have he : (fun x => Dactual x*(Phi x^6)⁻¹)=normalizedD := by
    funext x
    simp only [normalizedD,div_eq_mul_inv]
  rw [he] at h
  rw [h.second]
  unfold Nd
  field_simp [mass_and_source_ne.1,mass_and_source_ne.2]
  ring

private theorem actual_model_signs : 0<Na scale 1 ∧ 0<quadraticDet scale 1 := by
  let u := 192-10*scale
  let v := 10*scale-191
  have hu : 0≤u := by
    dsimp [u]
    linarith [thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths]
  have hv : 0≤v := by
    dsimp [v]
    linarith [thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one]
  have huv : u+v=1 := by dsimp [u,v]; ring
  have hav : (191*u+192*v)/10=scale := by dsimp [u,v]; ring
  have ha := Na_pos hu hv (by rw [huv]; norm_num)
  have hd := quadraticDet_pos hu hv (by rw [huv]; norm_num)
  rw [hav,huv] at ha hd
  exact ⟨ha,hd⟩

/-- Actual complete-source curvature is strictly positive in every correction direction. -/
theorem actual_curvature_positive (t : ℝ) :
    0<deriv (deriv (normalizedBase 10000000000000)) 0+
      2*deriv (deriv normalizedB) 0*t+deriv (deriv normalizedD) 0*t^2 := by
  have ha := actual_model_signs.1
  have hd := actual_model_signs.2
  have hraw : 0<Na scale 1+2*Nb scale 1*t+Nd scale 1*t^2 := by
    by_cases ht : t=0
    · simpa [ht] using ha
    · have hgain := mul_pos hd (sq_pos_of_ne_zero ht)
      have hs := sq_nonneg (Na scale 1+Nb scale 1*t)
      by_contra hn
      have hn' := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
      unfold quadraticDet at hgain
      nlinarith only [hgain,hs,hn']
  have hp : 0<pH 0 scale 1 := by
    rw [pH_one]
    norm_num [sourceJet,HTGeometry.modularThetaEvenSeamSourcePolynomial]
    linarith [thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one]
  rw [normalizedBase_second_zero,normalizedB_second_zero,normalizedD_second_zero]
  calc
    0 < (Na scale 1+2*Nb scale 1*t+Nd scale 1*t^2)/(pH 0 scale 1)^7 := div_pos hraw (pow_pos hp 7)
    _ = Na scale 1/(pH 0 scale 1)^7+2*(Nb scale 1/(pH 0 scale 1)^7)*t+
        Nd scale 1/(pH 0 scale 1)^7*t^2 := by ring

end
end RHTower.ThetaOddSeamCurvature
