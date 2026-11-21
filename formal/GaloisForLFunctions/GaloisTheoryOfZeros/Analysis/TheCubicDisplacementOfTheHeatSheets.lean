import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheCommonDriftOfAllSheetsAtAHeatCollision
import GaloisForLFunctions.GaloisTheoryOfZeros.TheLocalDiscriminantOfAHeatCollision
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Cubic displacement of colliding heat sheets

The common quadratic translation cancels in each sheet difference. The
next coefficient is proportional to the Hermite root, with the same
scale factor for every branch.
-/

noncomputable section
open Complex Filter Topology RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

open private fderiv_collisionBlowup_ne_zero from GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision

/-- Taylor coefficient of the spatial heat profile at a marked place. -/
def heatSpatialCoefficient (τ z : ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k (complexHeat τ) z / k.factorial

private theorem normalized_ray {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) (y : ℂ) (j : ℕ) :
    iteratedDeriv j (fun s : ℂ => collisionBlowup τ z m (s,y)) 0 =
      (j.factorial : ℂ) * heatSpatialCoefficient τ z (m+j) * parabolicRayPolynomial (m+j) y := by
  have hj := hc.blowup_ray_jet y j
  let n := (m+j).choose m * m.factorial
  have hfac : n * j.factorial = (m+j).factorial := by
    simpa only [n,add_comm j m,mul_right_comm] using Nat.add_choose_mul_factorial_mul_factorial j m
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast (fun h => Nat.factorial_ne_zero (m+j) (by rw [←hfac,h,zero_mul]) : n ≠ 0)
  apply mul_left_cancel₀ hn
  change (n:ℂ) * _ = _
  rw [show (n:ℂ) * iteratedDeriv j (fun s : ℂ => collisionBlowup τ z m (s,y)) 0 =
    parabolicRayPolynomial (m+j) y * iteratedDeriv (m+j) (complexHeat τ) z from hj,heatSpatialCoefficient]
  have hF : ((m+j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (m+j)
  field_simp [hF]
  have id : (n:ℂ) * j.factorial = (m+j).factorial := by exact_mod_cast hfac
  linear_combination -(parabolicRayPolynomial (m+j) y * iteratedDeriv (m+j) (complexHeat τ) z) * id

private theorem acceleration (G : ℂ × ℂ → ℂ) (hG : ∀ p, AnalyticAt ℂ G p)
    (P V : ℂ → ℂ × ℂ) (x : ℂ) (W : ℂ × ℂ)
    (hv : ∀ᶠ t in 𝓝 x, HasDerivAt P (V t) t) (hw : HasDerivAt V W x) :
    deriv (deriv (fun t => G (P t))) x =
      fderiv ℂ (fderiv ℂ G) (P x) (V x) (V x) + fderiv ℂ G (P x) W := by
  have he : deriv (fun t => G (P t)) =ᶠ[𝓝 x] fun t => fderiv ℂ G (P t) (V t) := by
    filter_upwards [hv] with t ht
    exact ((hG _).differentiableAt.hasFDerivAt.comp_hasDerivAt t ht).deriv
  rw [he.deriv_eq]
  have h1 := (hG _).fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt x hv.self_of_nhds
  exact (h1.clm_apply hw).deriv

private theorem ray_second {G : ℂ × ℂ → ℂ} (hG : ∀ p, AnalyticAt ℂ G p)
    (P : ℂ → ℂ × ℂ) (x : ℂ) (v : ℂ × ℂ) (hp : ∀ t, HasDerivAt P v t) :
    deriv (deriv (fun t => G (P t))) x = fderiv ℂ (fderiv ℂ G) (P x) v v := by
  simpa only [map_zero,add_zero] using
    acceleration G hG P (fun _ => v) x 0 (Eventually.of_forall hp) (hasDerivAt_const x v)

private theorem hermite_second_at_root (m : ℕ) (ρ : ℂ) (h : parabolicRayPolynomial m ρ = 0) :
    2 * deriv (deriv (parabolicRayPolynomial m)) ρ = ρ * deriv (parabolicRayPolynomial m) ρ := by
  let q := parabolicRayPolynomial m
  have hq := ((heatShiftPoly (1/4) m).hasDerivAt_aeval ρ).differentiableAt.hasDerivAt
  have he : deriv q = fun y => Polynomial.aeval y (heatShiftPoly (1/4) m).derivative :=
    funext fun y => ((heatShiftPoly (1/4) m).hasDerivAt_aeval y).deriv
  have hd : DifferentiableAt ℂ (deriv q) ρ := by
    rw [he]; exact ((heatShiftPoly (1/4) m).derivative.hasDerivAt_aeval ρ).differentiableAt
  have hq' : HasDerivAt q (deriv q ρ) ρ := hq
  have raised := (((hasDerivAt_id ρ).mul hq').sub (hd.hasDerivAt.const_mul 2)).deriv
  have eq := congrArg (fun f : ℂ → ℂ => deriv f ρ) (funext (parabolic_ray_raise m))
  rw [parabolic_ray_lower,h,mul_zero] at eq
  change 0 = deriv (fun y => y*q y - 2*deriv q y) ρ at eq
  have raised' : deriv (fun y => y*q y - 2*deriv q y) ρ = 1 * q ρ + id ρ * deriv q ρ - 2 * deriv (deriv q) ρ :=
    raised
  rw [raised',show q ρ = 0 from h] at eq
  change 2*deriv (deriv q) ρ = ρ*deriv q ρ
  simp only [id_eq] at eq
  linear_combination eq

/-- The common relative cubic coefficient of all sheet differences. -/
def collisionCubicScale (τ z : ℂ) (m : ℕ) : ℂ :=
  2 * (heatSpatialCoefficient τ z (m+2) / heatSpatialCoefficient τ z m) -
    (heatSpatialCoefficient τ z (m+1) / heatSpatialCoefficient τ z m)^2

/-- Normalizing a branch by its Hermite root leaves the same second
derivative on every sheet. This also covers the central root. -/
theorem IsCollision.branch_second_displacement {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hr : heatModelFwd m ρ = 0) :
    deriv (deriv (collisionBranch τ z m ρ)) 0 = 2 * ρ * collisionCubicScale τ z m := by
  let G := collisionBlowup τ z m
  let Y := collisionBranch τ z m ρ
  let c := heatSpatialCoefficient τ z
  let q := parabolicRayPolynomial m
  let p : ℂ × ℂ := (0,ρ)
  let x : ℂ × ℂ := (1,0)
  let y : ℂ × ℂ := (0,1)
  let D := fderiv ℂ G p
  let H := fderiv ℂ (fderiv ℂ G) p
  let A := c (m+1) / c m
  let B := c (m+2) / c m
  have cm : c m ≠ 0 := div_ne_zero hc.top_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
  have an := analyticAt_collisionBlowup τ z m
  have ht (u t : ℂ) : HasDerivAt (fun s : ℂ => (s,u)) x t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t u)
  have hy (t : ℂ) : HasDerivAt (fun u : ℂ => ((0:ℂ),u)) y t :=
    (hasDerivAt_const t (0:ℂ)).prodMk (hasDerivAt_id t)
  have hval : (fun u : ℂ => G (0,u)) = fun u => c m*q u := by
    funext u
    simpa only [Nat.add_zero,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,one_mul]
      using normalized_ray hc u 0
  have hq : q ρ = 0 := by
    have eq := congrFun hval ρ
    change collisionBlowup τ z m (0,ρ) = c m * q ρ at eq
    rw [collisionBlowup_zero hc.vanish,hr,mul_zero] at eq
    exact (mul_eq_zero.mp eq.symm).resolve_left cm
  have qt (n : ℕ) (u : ℂ) : HasDerivAt (parabolicRayPolynomial n)
      (deriv (parabolicRayPolynomial n) u) u :=
    ((heatShiftPoly (1/4) n).hasDerivAt_aeval u).differentiableAt.hasDerivAt
  have space : D y = c m * deriv q ρ :=
    ((an p).differentiableAt.hasFDerivAt.comp_hasDerivAt ρ (hy ρ)).unique
      (((qt m ρ).const_mul (c m)).congr_of_eventuallyEq (Eventually.of_forall (congrFun hval)))
  have space2 : 2 * H y y = ρ * D y := by
    have sec := ray_second an (fun u : ℂ => ((0:ℂ),u)) ρ y hy
    rw [hval] at sec
    have hom : deriv (fun u => c m*q u) = fun u => c m*deriv q u :=
      funext fun u => ((qt m u).const_mul (c m)).deriv
    rw [hom,deriv_const_mul_field] at sec
    change c m * deriv (deriv q) ρ = H y y at sec
    rw [←sec,space]
    linear_combination c m * hermite_second_at_root m ρ hq
  have mixed : H y x = 0 := by
    have hv (u : ℂ) : fderiv ℂ G (0,u) x = c (m+1)*parabolicRayPolynomial (m+1) u := by
      have eq := normalized_ray hc u 1
      rw [iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,one_mul] at eq
      exact (((an _).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 (ht u 0)).deriv.symm).trans eq
    have hd := (((an p).fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt ρ (hy ρ)).clm_apply
      (hasDerivAt_const ρ x))
    have eq := hd.unique (((qt (m+1) ρ).const_mul (c (m+1))).congr_of_eventuallyEq
      (Eventually.of_forall hv))
    simpa only [map_zero,add_zero,parabolic_ray_lower,show parabolicRayPolynomial m ρ = 0 from hq,mul_zero]
      using eq
  have mixed' : H x y = 0 := ((an p).contDiffAt.isSymmSndFDerivAt_of_omega x y).trans mixed
  have time2 : H x x = -4 * ρ * B * D y := by
    have sec := ray_second an (fun t : ℂ => (t,ρ)) 0 x (ht ρ)
    have eq := normalized_ray hc ρ 2
    rw [show iteratedDeriv 2 (fun t : ℂ => G (t,ρ)) 0 =
      deriv (deriv (fun t : ℂ => G (t,ρ))) 0 by rw [iteratedDeriv_succ,iteratedDeriv_one],
      sec,show m+2=(m+1)+1 by omega,parabolic_ray_raise,parabolic_ray_lower,
      parabolic_ray_raise,show parabolicRayPolynomial m ρ = 0 from hq,mul_zero,zero_sub] at eq
    have can : B*c m = c (m+2) := div_mul_cancel₀ _ cm
    rw [space]
    change H x x = _ at eq
    rw [eq]
    norm_num [Nat.factorial]
    have hinv : c m * (c m)⁻¹ = 1 := mul_inv_cancel₀ cm
    linear_combination 4*ρ*deriv q ρ*can -
      8*heatSpatialCoefficient τ z (m+1+1)*ρ*deriv (parabolicRayPolynomial m) ρ*hinv
  have drift : deriv Y 0 = 2*A := by
    rw [hc.all_branches_have_one_drift hr]
    dsimp only [A,c,heatSpatialCoefficient,collisionDrift]
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    field_simp [hc.top_ne_zero,Nat.factorial_ne_zero]
    <;> ring
  obtain ⟨hY,hY0,hzero,_⟩ := collisionBranch_spec hc hr
  let P (t : ℂ) : ℂ × ℂ := (t,Y t)
  let V (t : ℂ) : ℂ × ℂ := (1,deriv Y t)
  have vel : ∀ᶠ t in 𝓝 0, HasDerivAt P (V t) t :=
    hY.eventually_analyticAt.mono fun t a => (hasDerivAt_id t).prodMk a.differentiableAt.hasDerivAt
  have hdY : AnalyticAt ℂ (deriv Y) 0 := hY.deriv
  have acc := acceleration G an P V 0 (0,deriv (deriv Y) 0) vel
    ((hasDerivAt_const (0:ℂ) (1:ℂ)).prodMk hdY.differentiableAt.hasDerivAt)
  have hconst : deriv (deriv (fun t => G (P t))) 0 = 0 :=
    have hz' : (fun s => G (P s)) =ᶠ[𝓝 0] fun _ => (0:ℂ) := hzero
    hz'.deriv.deriv_eq.trans (by simp)
  have p0 : P 0 = p := Prod.ext rfl hY0
  have v0 : V 0 = x + (2*A) • y := by ext <;> simp [V,x,y,drift]
  rw [hconst,p0,v0] at acc
  change 0 = H _ _ + D (0,deriv (deriv Y) 0) at acc
  rw [show ((0,deriv (deriv Y) 0) : ℂ × ℂ) = deriv (deriv Y) 0 • y by ext <;> simp [y]] at acc
  simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,mixed,mixed',mul_zero,add_zero,zero_add,time2] at acc
  apply mul_right_cancel₀ (show D y ≠ 0 from fderiv_collisionBlowup_ne_zero hc hr)
  change deriv (deriv Y) 0 * D y = 2 * ρ * (2*B-A^2) * D y
  linear_combination -acc - 2*A^2*space2

private theorem branch_expansion {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hr : heatModelFwd m ρ = 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ s, collisionBranch τ z m ρ s =
      ρ + collisionDrift τ z m*s + ρ*collisionCubicScale τ z m*s^2 + s^3*R s := by
  obtain ⟨han,h0,_,_⟩ := collisionBranch_spec hc hr
  obtain ⟨R,hR,eq⟩ := han.exists_eq_sum_add_pow_mul 3
  refine ⟨R,hR,fun s => ?_⟩
  have h := eq s
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.factorial_zero,
    Nat.factorial_succ,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,one_mul,mul_one,pow_zero,pow_one,
    div_one,smul_eq_mul,iteratedDeriv_zero,h0] at h
  rw [show iteratedDeriv 2 (collisionBranch τ z m ρ) 0 = deriv (deriv (collisionBranch τ z m ρ)) 0 by
    rw [iteratedDeriv_succ,iteratedDeriv_one],iteratedDeriv_one,
    hc.branch_second_displacement hr,hc.all_branches_have_one_drift hr] at h
  rw [h]; ring

/-- In physical space the first branch-dependent correction to the Hermite
motion is cubic in the square root of time. -/
theorem IsCollision.cubic_sheet_displacement {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hr : heatModelFwd m ρ = 0) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ s, collisionZero τ z m ρ s =
      z + ρ*s + collisionDrift τ z m*s^2 + ρ*collisionCubicScale τ z m*s^3 + s^4*R s := by
  obtain ⟨R,han,h⟩ := branch_expansion hc hr
  refine ⟨R,han,fun s => ?_⟩
  rw [collisionZero,h]; ring

/-- For factors with zero linear term, their relative quadratic
coefficients add under multiplication. -/
private theorem product_expansion {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (a : ι → ℂ)
    (c : ℂ) (h : ∀ i ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧
      ∀ s, f i s = a i*(1+c*s^2) + s^3*R s) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ s, (∏ i ∈ S, f i s) =
      (∏ i ∈ S, a i)*(1+(S.card:ℂ)*c*s^2) + s^3*R s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0,analyticAt_const,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨R,hR,eR⟩ := h i (Finset.mem_insert_self ..)
    obtain ⟨T,hT,eT⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    let A := ∏ j ∈ S, a j
    let b := (S.card:ℂ)*c
    let v (s : ℂ) := a i*A*c*b*s + a i*(1+c*s^2)*T s + A*(1+b*s^2)*R s + s^3*R s*T s
    have hv : AnalyticAt ℂ v 0 := by dsimp only [v]; fun_prop
    refine ⟨v,hv,fun s => ?_⟩
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_succ,eR,eT]
    dsimp only [v,A,b]
    ring

open private rootDifferences disc_factor disc_unit from GaloisForLFunctions.GaloisTheoryOfZeros.TheLocalDiscriminantOfAHeatCollision

/-- Removing the collision power leaves a time-analytic discriminant
whose logarithmic derivative counts ordered pairs of distinct sheets. -/
theorem IsCollision.regularized_discriminant_log_derivative {τ z : ℂ} {m : ℕ}
    (hc : IsCollision τ z m) :
    ∃ V : ℂ → ℂ, AnalyticAt ℂ V 0 ∧ V 0 ≠ 0 ∧
      (∀ᶠ s in 𝓝 0, collisionSheetDiscriminant τ z m s = (s^2)^(m.choose 2)*V (s^2)) ∧
      deriv V 0 / V 0 = (m*(m-1):ℕ) * collisionCubicScale τ z m := by
  classical
  obtain ⟨V,hV,h0,disc⟩ := disc_unit hc
  refine ⟨V,hV,h0,disc,?_⟩
  let S := (profileRoots m).offDiag
  let a (p : ℝ × ℝ) := (p.1:ℂ)-p.2
  let f (p : ℝ × ℝ) (s : ℂ) := collisionBranch τ z m p.1 s-collisionBranch τ z m p.2 s
  let c := collisionCubicScale τ z m
  let A := ∏ i ∈ S, a i
  let b := (S.card:ℂ)*c
  obtain ⟨R,hR,prod⟩ := product_expansion S f a c (by
    intro p hp
    obtain ⟨ha,hb,_⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨U,hU,eU⟩ := branch_expansion hc (heatModelFwd_profileRoot ha)
    obtain ⟨T,hT,eT⟩ := branch_expansion hc (heatModelFwd_profileRoot hb)
    refine ⟨fun s => U s-T s,hU.sub hT,fun s => ?_⟩
    dsimp only [f,a,c]
    rw [eU,eT]; ring)
  have he : ∀ᶠ s in 𝓝[≠] (0:ℂ), V (s^2) = A*(1+b*s^2) + s^3*R s := by
    filter_upwards [disc.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hd hs
    rw [disc_factor] at hd
    exact (mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero 2 hs)) hd).symm.trans (prod s)
  have left : ContinuousAt (fun s : ℂ => V (s^2)) 0 := by
    have h2 : ContinuousAt (fun s : ℂ => s^2) 0 := continuousAt_id.pow 2
    have hV0 : ContinuousAt V ((fun s : ℂ => s^2) 0) := by simpa using hV.continuousAt
    exact ContinuousAt.comp (f := fun s : ℂ => s^2) (x := 0) hV0 h2
  have right : ContinuousAt (fun s : ℂ => A*(1+b*s^2)+s^3*R s) 0 := by
    have := hR.continuousAt
    fun_prop
  have val : V 0 = A := by
    simpa using tendsto_nhds_unique_of_eventuallyEq
      (left.tendsto.mono_left nhdsWithin_le_nhds) (right.tendsto.mono_left nhdsWithin_le_nhds) he
  obtain ⟨T,hT,tay⟩ := hV.exists_eq_sum_add_pow_mul 2
  have ht (w : ℂ) : V w = V 0 + deriv V 0*w + w^2*T w := by
    simpa [Finset.sum_range_succ,smul_eq_mul,mul_comm w] using tay w
  have slope : ∀ᶠ s in 𝓝[≠] (0:ℂ), deriv V 0 - A*b = s*R s-s^2*T (s^2) := by
    filter_upwards [he,self_mem_nhdsWithin] with s eq hs
    rw [ht,val] at eq
    apply mul_left_cancel₀ (pow_ne_zero 2 hs)
    linear_combination eq
  have cont : ContinuousAt (fun s : ℂ => s*R s-s^2*T (s^2)) 0 := by
    have ht0 : ContinuousAt T ((0:ℂ)^2) := by simpa using hT.continuousAt
    have hr := hR.continuousAt
    fun_prop
  have eq : deriv V 0 - A*b = 0 := by
    simpa using tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds
      (cont.tendsto.mono_left nhdsWithin_le_nhds) slope
  have card : S.card = m*(m-1) := by
    rw [show S.card = _ from Finset.offDiag_card (profileRoots m),card_profileRoots,Nat.mul_sub,Nat.mul_one]
  apply (div_eq_iff h0).mpr
  rw [val,←card]
  change deriv V 0 = b*A
  linear_combination eq

end GaloisForLFunctions.GaloisTheoryOfZeros
