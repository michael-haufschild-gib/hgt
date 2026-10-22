import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegularizedClockRatio
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5RegularizedSourceJets
/-! Actual intrinsic inverse-source/denominator-clock germ.
Exact regularized source jets identify the first three quotient jets as zero
and the fourth as a strictly positive complete-source orientation at every
nonnegative center. Successive strict derivative comparison gives genuine
local increase of the original quotient. Global finite-displacement order
and arbitrary-degree positivity remain open. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology
open scoped BigOperators ContDiff
noncomputable section
private theorem smooth_at_nat {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) : ContDiffAt ℝ n f 0 :=
  hf.contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
private theorem smooth_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) := by
  simpa only [iteratedDeriv_one] using HTGeometry.contDiff_top_iteratedDeriv_real f hf 1

private structure EvenFourJet (f : ℝ → ℝ) (a b c : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  value : f 0=a
  first : iteratedDeriv 1 f 0=0
  second : iteratedDeriv 2 f 0=b
  third : iteratedDeriv 3 f 0=0
  fourth : iteratedDeriv 4 f 0=c

private theorem mul_jet (f g : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedDeriv n (fun t => f t*g t) 0=
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i f 0*iteratedDeriv (n-i) g 0 :=
  by simpa only [Pi.mul_def] using iteratedDeriv_mul (smooth_at_nat hf n) (smooth_at_nat hg n)

namespace EvenFourJet
variable {f g : ℝ → ℝ} {a b c d e h : ℝ}
private theorem const (a : ℝ) : EvenFourJet (fun _ => a) a 0 0 := by
  exact ⟨contDiff_const,rfl,by simp [iteratedDeriv_const],by simp [iteratedDeriv_const],by simp [iteratedDeriv_const],by simp [iteratedDeriv_const]⟩
private theorem add (hf : EvenFourJet f a b c) (hg : EvenFourJet g d e h) :
    EvenFourJet (fun t => f t+g t) (a+d) (b+e) (c+h) := by
  refine ⟨hf.smooth.add hg.smooth,by rw [hf.value,hg.value],?_,?_,?_,?_⟩
  all_goals
    change iteratedDeriv _ (f+g) 0 = _
    rw [iteratedDeriv_add (smooth_at_nat hf.smooth _) (smooth_at_nat hg.smooth _)]
    simp only [hf.first,hg.first,hf.second,hg.second,hf.third,hg.third,hf.fourth,hg.fourth,zero_add]
private theorem sub (hf : EvenFourJet f a b c) (hg : EvenFourJet g d e h) :
    EvenFourJet (fun t => f t-g t) (a-d) (b-e) (c-h) := by
  refine ⟨hf.smooth.sub hg.smooth,by rw [hf.value,hg.value],?_,?_,?_,?_⟩
  all_goals
    change iteratedDeriv _ (f-g) 0 = _
    rw [iteratedDeriv_sub (smooth_at_nat hf.smooth _) (smooth_at_nat hg.smooth _)]
    simp only [hf.first,hg.first,hf.second,hg.second,hf.third,hg.third,hf.fourth,hg.fourth,sub_self]
private theorem mul (hf : EvenFourJet f a b c) (hg : EvenFourJet g d e h) :
    EvenFourJet (fun t => f t*g t) (a*d) (b*d+a*e) (c*d+6*b*e+a*h) := by
  refine ⟨hf.smooth.mul hg.smooth,by rw [hf.value,hg.value],?_,?_,?_,?_⟩ <;>
    rw [mul_jet f g hf.smooth hg.smooth] <;>
    norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,
      hf.value,hg.value,hf.first,hg.first,hf.second,hg.second,hf.third,hg.third,hf.fourth,hg.fourth] <;> ring
private theorem scale (hf : EvenFourJet f a b c) (r : ℝ) :
    EvenFourJet (fun t => r*f t) (r*a) (r*b) (r*c) := by
  convert (const r).mul hf using 1 <;> ring

private theorem rpow (hf : EvenFourJet f a b c) (hp : ∀ t, 0 < f t) (p : ℝ) :
    EvenFourJet (fun t => (f t)^p) (a^p) (p*a^p*b/a)
      (p*a^p*c/a+3*p*(p-1)*a^p*b^2/a^2) := by
  let g : ℝ → ℝ := fun t => (f t)^p
  have hg : ContDiff ℝ ∞ g := hf.smooth.rpow_const_of_ne (fun t => (hp t).ne')
  have ha : a≠0 := by rw [←hf.value]; exact (hp 0).ne'
  have hg0 : g 0=a^p := by simp only [g,hf.value]
  have he : (fun t => f t*deriv g t)=fun t => p*(g t*deriv f t) := by
    funext t
    have hh := ((hf.smooth.differentiable (by simp) t).hasDerivAt).rpow_const (Or.inl (hp t).ne') (p:=p)
    rw [show deriv g t=deriv (fun t => (f t)^p) t by rfl,hh.deriv,Real.rpow_sub_one (hp t).ne']
    dsimp only [g]
    field_simp [(hp t).ne']
  have heq (n : ℕ) := congrArg (fun F : ℝ → ℝ => iteratedDeriv n F 0) he
  have heq' (n : ℕ) :
      (∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i f 0*iteratedDeriv (n-i+1) g 0)=
      p*(∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i g 0*iteratedDeriv (n-i+1) f 0) := by
    have hh := heq n
    rw [mul_jet f (deriv g) hf.smooth (smooth_deriv hg),iteratedDeriv_const_mul_field,
      mul_jet g (deriv f) hg (smooth_deriv hf.smooth)] at hh
    simpa only [←iteratedDeriv_succ'] using hh
  have h1 := heq' 0
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hf.value,hg0,hf.first] at h1
  have hg1 : iteratedDeriv 1 g 0=0 := by simpa only [iteratedDeriv_one] using h1.resolve_left ha
  have h2 := heq' 1
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hf.value,hg0,hf.first,hg1,hf.second] at h2
  have hg2 : iteratedDeriv 2 g 0=p*a^p*b/a := by
    apply (eq_div_iff ha).mpr
    nlinarith only [h2]
  have h3 := heq' 2
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hf.value,hg0,hf.first,hg1,hf.second,hf.third] at h3
  have hg3 : iteratedDeriv 3 g 0=0 := h3.resolve_left ha
  have h4 := heq' 3
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hf.value,hg0,hf.first,hg1,
    hf.second,hg2,hf.third,hg3,hf.fourth] at h4
  refine ⟨hg,hg0,hg1,hg2,hg3,?_⟩
  field_simp [ha] at h4 ⊢
  nlinarith only [h4]

private theorem inv (hf : EvenFourJet f a b c) (hp : ∀ t, 0 < f t) :
    EvenFourJet (fun t => (f t)⁻¹) a⁻¹ (-b/a^2) (6*b^2/a^3-c/a^2) := by
  have hh := hf.rpow hp (-1)
  have ha : a≠0 := by rw [←hf.value]; exact (hp 0).ne'
  norm_num only [Real.rpow_neg_one] at hh
  convert hh using 1 <;> field_simp [ha] <;> ring
private theorem div (hf : EvenFourJet f a b c) (hg : EvenFourJet g d e h) (hp : ∀ t, 0 < g t) :
    EvenFourJet (fun t => f t/g t) (a/d) (b/d-a*e/d^2)
      (c/d-6*b*e/d^2+6*a*e^2/d^3-a*h/d^2) := by
  have hd : d≠0 := by rw [←hg.value]; exact (hp 0).ne'
  convert hf.mul (hg.inv hp) using 1 <;> simp only [div_eq_mul_inv] <;> ring

private theorem exp (hf : EvenFourJet f a b c) :
    EvenFourJet (fun t => Real.exp (f t)) (Real.exp a) (Real.exp a*b)
      (Real.exp a*(c+3*b^2)) := by
  let g : ℝ → ℝ := fun t => Real.exp (f t)
  have hg : ContDiff ℝ ∞ g := hf.smooth.exp
  have hg0 : g 0=Real.exp a := by simp only [g,hf.value]
  have hd : deriv g=fun t => g t*deriv f t := by
    funext t
    exact ((hf.smooth.differentiable (by simp) t).hasDerivAt.exp).deriv
  have hj (n : ℕ) : iteratedDeriv (n+1) g 0=
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i g 0*iteratedDeriv (n-i+1) f 0 := by
    rw [iteratedDeriv_succ',hd,mul_jet g (deriv f) hg (smooth_deriv hf.smooth)]
    simp only [←iteratedDeriv_succ']
  have h1 := hj 0
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hg0,hf.first] at h1
  have h2 := hj 1
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hg0,h1,hf.first,hf.second] at h2
  have h3 := hj 2
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hg0,h1,hf.first,hf.second,hf.third] at h3
  have h4 := hj 3
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,hg0,h1,h2,h3,hf.first,hf.second,hf.third,hf.fourth] at h4
  refine ⟨hg,hg0,by simpa only [iteratedDeriv_one] using h1,h2,h3,?_⟩
  nlinarith only [h4]

private theorem euler (hf : EvenFourJet f a b c) :
    EvenFourJet (fun t => t*deriv f t) 0 (2*b) (4*c) := by
  have hc : ContDiff ℝ ∞ (fun t => t*deriv f t) := contDiff_id.mul (smooth_deriv hf.smooth)
  have hj (n : ℕ) : iteratedDeriv (n+1) (fun t => t*deriv f t) 0=
      (n+1:ℕ)*iteratedDeriv (n+1) f 0 := by
    rw [iteratedDeriv_coordinate_mul_zero (smooth_deriv hf.smooth),←iteratedDeriv_succ']
  refine ⟨hc,by simp,?_,?_,?_,?_⟩
  · simpa only [Nat.zero_add,Nat.cast_one,one_mul,hf.first] using hj 0
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,hf.second] using hj 1
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,hf.third,mul_zero] using hj 2
  · simpa only [Nat.reduceAdd,Nat.cast_ofNat,hf.fourth] using hj 3


private theorem euler_two (hf : EvenFourJet f a b c) :
    EvenFourJet (fun t => t^2*deriv (deriv f) t) 0 (2*b) (12*c) := by
  have hh := hf.euler.euler.sub hf.euler
  have hd : deriv (fun t => t*deriv f t)=fun t => deriv f t+t*deriv (deriv f) t := by
    funext t
    have hs := (hasDerivAt_id t).mul (((smooth_deriv hf.smooth).differentiable (by simp) t).hasDerivAt)
    simpa only [Pi.mul_def,id_eq,one_mul] using hs.deriv
  convert! hh using 1
  · funext t
    rw [hd]
    ring
  all_goals ring

private theorem cosh_coordinate (hf : EvenFourJet f a b c) (r : ℝ) :
    EvenFourJet (fun t => Real.cosh (r*(t*f t))) 1 (r^2*a^2)
      (r^4*a^4+12*r^2*a*b) := by
  let H : ℝ → ℝ := fun t => r*(t*f t)
  let V : ℝ → ℝ := fun t => r*(f t+t*deriv f t)
  let G : ℝ → ℝ := fun t => Real.cosh (H t)
  let S : ℝ → ℝ := fun t => Real.sinh (H t)
  have jV : EvenFourJet V (r*a) (3*r*b) (5*r*c) := by
    convert (hf.add hf.euler).scale r using 1 <;> ring
  have hH : ContDiff ℝ ∞ H := contDiff_const.mul (contDiff_id.mul hf.smooth)
  have hG : ContDiff ℝ ∞ G := by dsimp [G]; fun_prop
  have hS : ContDiff ℝ ∞ S := by dsimp [S]; fun_prop
  have hdH (t : ℝ) : HasDerivAt H (V t) t := by
    convert! ((hasDerivAt_id t).mul ((hf.smooth.differentiable (by simp) t).hasDerivAt)).const_mul r using 1
    dsimp only [V,id_eq]
    ring
  have hdG : deriv G=fun t => S t*V t := by
    funext t
    exact (hdH t).cosh.deriv
  have hdS : deriv S=fun t => G t*V t := by
    funext t
    exact (hdH t).sinh.deriv
  have g0 : G 0=1 := by simp [G,H]
  have s0 : S 0=0 := by simp [S,H]
  have hjG (n : ℕ) : iteratedDeriv (n+1) G 0=
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i S 0*iteratedDeriv (n-i) V 0 := by
    rw [iteratedDeriv_succ',hdG,mul_jet S V hS jV.smooth]
  have hjS (n : ℕ) : iteratedDeriv (n+1) S 0=
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*iteratedDeriv i G 0*iteratedDeriv (n-i) V 0 := by
    rw [iteratedDeriv_succ',hdS,mul_jet G V hG jV.smooth]
  have g1 := hjG 0
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,s0] at g1
  have s1 := hjS 0
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,g0,jV.value] at s1
  have g2 := hjG 1
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,s0,s1,jV.value,jV.first] at g2
  have s2 := hjS 1
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,g0,g1,jV.first] at s2
  have g3 := hjG 2
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,s0,s1,s2,jV.first] at g3
  have s3 := hjS 2
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,g0,g1,g2,jV.value,jV.first,jV.second] at s3
  have g4 := hjG 3
  norm_num [Finset.sum_range_succ,Nat.choose,iteratedDeriv_zero,s0,s1,s2,s3,jV.value,jV.first,jV.second] at g4
  refine ⟨hG,g0,by simpa only [iteratedDeriv_one] using g1,?_,g3,?_⟩
  · nlinarith only [g2]
  · nlinarith only [g4]

end EvenFourJet

local notation "c" => thetaCuspLogCurvature
local notation "e" => completedCurvatureEven
local notation "Eb" => curvaturePrimitiveFactor
local notation "Qb" => curvatureActionFactor
local notation "k" => denominatorClockRate

private theorem curvature_even_jet (u : ℝ) :
    EvenFourJet (e u) (c u) (iteratedDeriv 2 c u) (iteratedDeriv 4 c u) := by
  refine ⟨completedCurvatureEven_smooth u,?_,?_,?_,?_,?_⟩
  · simp [completedCurvatureEven]
  all_goals rw [completedCurvatureEven_jet_zero]; norm_num

private theorem primitive_factor_jet (u : ℝ) :
    EvenFourJet (Eb u) (c u) (iteratedDeriv 2 c u/3) (iteratedDeriv 4 c u/5) := by
  have he := curvature_even_jet u
  refine ⟨curvaturePrimitiveFactor_smooth u,curvaturePrimitiveFactor_zero u,?_,?_,?_,?_⟩ <;>
    rw [curvaturePrimitiveFactor_jet] <;>
    norm_num [he.first,he.second,he.third,he.fourth]

private theorem action_factor_jet (u : ℝ) :
    EvenFourJet (Qb u) (c u) (iteratedDeriv 2 c u/6) (iteratedDeriv 4 c u/15) := by
  have he := curvature_even_jet u
  refine ⟨curvatureActionFactor_smooth u,curvatureActionFactor_zero u,?_,?_,?_,?_⟩ <;>
    rw [curvatureActionFactor_jet] <;>
    norm_num [he.first,he.second,he.third,he.fourth] <;> ring

private theorem square_jet : EvenFourJet (fun t : ℝ => t^2) 0 2 0 := by
  refine ⟨contDiff_id.pow 2,by norm_num,?_,?_,?_,?_⟩ <;>
    norm_num [iteratedDeriv_fun_pow_zero]

private theorem slope_eq_deriv (u : ℝ) : shapeCurvatureSlope u=deriv (e u) :=
  funext fun t => (hasDerivAt_completedCurvatureEven u t).deriv.symm

private theorem second_eq_deriv (u : ℝ) : shapeCurvatureSecond u=deriv (deriv (e u)) := by
  rw [←slope_eq_deriv u]
  funext t
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u+t)).comp t ((hasDerivAt_id t).const_add u)
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u-t)).comp t ((hasDerivAt_id t).const_sub u)
  have hh : HasDerivAt (shapeCurvatureSlope u) (shapeCurvatureSecond u t) t := by
    convert! (hp.sub hm).div_const 2 using 1
    unfold shapeCurvatureSecond
    ring
  exact hh.deriv.symm

private theorem regular_reserve_jet (u : ℝ) :
    let b := iteratedDeriv 2 c u/c u
    let v := iteratedDeriv 4 c u/c u
    EvenFourJet (regularActionInverseReserve u) 24
      (432*c u/5+48*b/5)
      (24*(288*(c u)^2/25+904*c u*b/25-377*v/225+542*b^2/225)) := by
  dsimp only
  let b := iteratedDeriv 2 c u/c u
  let v := iteratedDeriv 4 c u/c u
  have hc := (thetaCuspLogCurvature_pos u).ne'
  have je := curvature_even_jet u
  have jE := primitive_factor_jet u
  have jQ := action_factor_jet u
  have jZ : EvenFourJet (fun t => t^2*Eb u t) 0 (2*c u) (4*iteratedDeriv 2 c u) := by
    convert square_jet.mul jE using 1 <;> ring
  have ja : EvenFourJet (fun t => e u t/Eb u t) 1 (2*b/3) (4*v/5-4*b^2/3) := by
    convert je.div jE (curvaturePrimitiveFactor_pos u) using 1 <;>
      (try dsimp only [b,v]) <;> field_simp [hc] <;> ring
  have jg : EvenFourJet (fun t => Eb u t/Qb u t) 1 (b/6) (2*v/15-b^2/6) := by
    convert jE.div jQ (curvatureActionFactor_pos u) using 1 <;>
      (try dsimp only [b,v]) <;> field_simp [hc] <;> ring
  have jb : EvenFourJet (fun t => t*shapeCurvatureSlope u t/Eb u t) 0 (2*b) (4*v-4*b^2) := by
    rw [slope_eq_deriv u]
    convert je.euler.div jE (curvaturePrimitiveFactor_pos u) using 1 <;>
      (try dsimp only [b,v]) <;> field_simp [hc] <;> ring
  have jd : EvenFourJet (fun t => t^2*shapeCurvatureSecond u t/Eb u t) 0 (2*b) (12*v-4*b^2) := by
    rw [second_eq_deriv u]
    convert je.euler_two.div jE (curvaturePrimitiveFactor_pos u) using 1 <;>
      (try dsimp only [b,v]) <;> field_simp [hc] <;> ring
  have jP := ((((((((jZ.mul jZ).scale 144).add ((jZ.mul jg).scale 384)).add
    ((jg.mul jg).scale 96)).add (jZ.scale 156)).add (jg.scale 208)).sub
    (EvenFourJet.const 9)).add (ja.scale 5)).add (jb.scale 25)
  have jA := ((EvenFourJet.const 9).add (jZ.scale 12)).add (jg.scale 16)
  have hh := ((((ja.scale 2).add jb).mul jP).scale (1/25)).sub
    ((((jb.scale 3).add jd).mul jA).scale (1/5))
  convert! hh using 1
  · funext t
    dsimp [regularActionInverseReserve]
    ring
  · ring
  · dsimp [b,v]
    field_simp [hc]
    ring
  · dsimp [b,v]
    field_simp [hc]
    ring

private theorem profile_factor_jet (u : ℝ) :
    let b := iteratedDeriv 2 c u/c u
    let v := iteratedDeriv 4 c u/c u
    let f0 := (c u)^((8:ℝ)/5)
    EvenFourJet (intrinsicActionSmoothFactor u) f0
      (f0*(12*c u/5+4*b/15))
      (f0*(432*(c u)^2/25+156*c u*b/25+2*b^2/25+8*v/75)) := by
  dsimp only
  have hc := (thetaCuspLogCurvature_pos u).ne'
  have jQ := action_factor_jet u
  have jpow := jQ.rpow (curvatureActionFactor_pos u) ((8:ℝ)/5)
  have jexp := ((square_jet.mul jQ).scale (6/5)).exp
  have hh := jpow.mul jexp
  convert! hh using 1
  · funext t
    unfold intrinsicActionSmoothFactor
    rw [thetaCuspReflectedLogAction_factor u t]
    congr 2
    ring
  · simp
  · simp only [zero_mul,mul_zero,Real.exp_zero,mul_one]
    field_simp [hc]
    ring
  · simp only [zero_mul,mul_zero,Real.exp_zero,mul_one]
    field_simp [hc]
    ring

private theorem inverse_factor_jet (u : ℝ) :
    let b := iteratedDeriv 2 c u/c u
    let v := iteratedDeriv 4 c u/c u
    let j0 := 6*(c u)^((8:ℝ)/5)
    EvenFourJet (intrinsicInverseSmoothFactor u) j0
      (j0*(6*c u+2*b/3))
      (j0*(2016*(c u)^2/25+1348*c u*b/25+704*b^2/225-353*v/225)) := by
  dsimp only
  have hh := ((profile_factor_jet u).mul (regular_reserve_jet u)).scale (1/4)
  convert! hh using 1
  · funext t
    unfold intrinsicInverseSmoothFactor
    ring
  all_goals ring

private theorem clock_factor_jet (u : ℝ) :
    let b := iteratedDeriv 2 c u/c u
    let v := iteratedDeriv 4 c u/c u
    let C0 := 2*k u*c u
    EvenFourJet (denominatorClockSmoothFactor u) C0
      (C0*(6*c u+2*b/3))
      (C0*(324*(c u)^2/5+72*c u*b+3*v/5)) := by
  dsimp only
  have hc := (thetaCuspLogCurvature_pos u).ne'
  have hk2 : (k u)^2=9/(2*c u) :=
    (eq_div_iff (mul_ne_zero (by norm_num) hc)).mpr (denominatorClockRate_sq u)
  have je := curvature_even_jet u
  have jE := primitive_factor_jet u
  have jcosh := (jE.add je).cosh_coordinate (k u)
  have jd := ((je.scale 2).add je.euler).scale (k u)
  have jp := jd.mul jcosh
  have hf : denominatorClockProfileJet u=
      fun t => (k u*(2*e u t+t*deriv (e u) t))*
        Real.cosh (k u*(t*(Eb u t+e u t))) := by
    funext t
    unfold denominatorClockProfileJet completedLocalDenominator completedFirstDenominator
    rw [completedDecayEvenPrimitive_factor u t,←slope_eq_deriv u]
    unfold shapeCurvatureSlope
    congr 2
    ring
  have jprime : EvenFourJet (denominatorClockProfileJet u) (2*k u*c u)
      (4*k u*iteratedDeriv 2 c u+8*(k u)^3*(c u)^3)
      (6*k u*iteratedDeriv 4 c u+160*(k u)^3*(c u)^2*iteratedDeriv 2 c u+
        32*(k u)^5*(c u)^5) := by
    rw [hf]
    convert! jp using 1 <;> ring
  have hj (n : ℕ) : iteratedDeriv n (denominatorClockSmoothFactor u) 0=
      iteratedDeriv n (denominatorClockProfileJet u) 0/(n+1:ℕ) := by
    have hh := iteratedDeriv_coordinate_mul_zero (denominatorClockSmoothFactor_smooth u) n
    rw [←show denominatorClockProfile u=(fun t => t*denominatorClockSmoothFactor u t) from
      funext (denominatorClockProfile_factor u),iteratedDeriv_succ',
      show deriv (denominatorClockProfile u)=denominatorClockProfileJet u from
        funext fun t => (hasDerivAt_denominatorClockProfile u t).deriv] at hh
    apply (eq_div_iff (by positivity : ((n+1:ℕ):ℝ) ≠ 0)).mpr
    simpa only [mul_comm] using hh.symm
  refine ⟨denominatorClockSmoothFactor_smooth u,denominatorClockSmoothFactor_zero u,?_,?_,?_,?_⟩
  · rw [hj,jprime.first]; simp
  · rw [hj,jprime.second]
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat]
    rw [show (k u)^3=k u*(k u)^2 by ring,hk2]
    field_simp [hc]
    ring
  · rw [hj,jprime.third]; simp
  · rw [hj,jprime.fourth]
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat]
    rw [show (k u)^3=k u*(k u)^2 by ring,show (k u)^5=k u*((k u)^2)^2 by ring,hk2]
    field_simp [hc]
    ring

private theorem actual_ratio_jet (u : ℝ) :
    let b := iteratedDeriv 2 c u/c u
    let v := iteratedDeriv 4 c u/c u
    let R0 := 3*(c u)^((8:ℝ)/5)/(k u*c u)
    EvenFourJet (intrinsicClockRegularRatio u) R0 0
      ((4:ℝ)/225*R0*(891*(c u)^2-1017*c u*b-122*v+176*b^2)) := by
  dsimp only
  have hc := (thetaCuspLogCurvature_pos u).ne'
  have hk := (denominatorClockRate_pos u).ne'
  have hh := (inverse_factor_jet u).div (clock_factor_jet u) (denominatorClockSmoothFactor_pos u)
  convert! hh using 1
  all_goals field_simp [hc,hk]; ring

/-- Exact analytic classification of the actual inverse-source/clock quotient.
The first three jets vanish; the first surviving candidate is the literal
source orientation with coefficient 891, not the clock-model coefficient 1311. -/
theorem intrinsicClockRegularRatio_jet_classification (u : ℝ) :
    iteratedDeriv 1 (intrinsicClockRegularRatio u) 0=0 ∧
    iteratedDeriv 2 (intrinsicClockRegularRatio u) 0=0 ∧
    iteratedDeriv 3 (intrinsicClockRegularRatio u) 0=0 ∧
    iteratedDeriv 4 (intrinsicClockRegularRatio u) 0=
      ((4:ℝ)/225)*(3*(c u)^((8:ℝ)/5)/(k u*c u))*
        (891*(c u)^2-1017*iteratedDeriv 2 c u-
          122*(iteratedDeriv 4 c u/c u)+176*(iteratedDeriv 2 c u/c u)^2) := by
  have hj := actual_ratio_jet u
  refine ⟨hj.first,hj.second,hj.third,?_⟩
  rw [hj.fourth]
  have hc := (thetaCuspLogCurvature_pos u).ne'
  field_simp [hc]

private theorem curvature_second (u : ℝ) : iteratedDeriv 2 c u=thetaCuspLogCurvatureJetTwo u := by
  unfold thetaCuspLogCurvature thetaCuspLogCurvatureJetTwo
  rw [iteratedDeriv_fun_neg,HTGeometry.iteratedDeriv_iteratedDeriv_real]
private theorem curvature_fourth (u : ℝ) : iteratedDeriv 4 c u=-iteratedDeriv 6 thetaCuspLogSource u := by
  unfold thetaCuspLogCurvature
  rw [iteratedDeriv_fun_neg,HTGeometry.iteratedDeriv_iteratedDeriv_real]

/-- Strict source orientation of the actual inverse-source/clock germ. -/
theorem intrinsicClockRegularRatio_fourth_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < iteratedDeriv 4 (intrinsicClockRegularRatio u) 0 := by
  rw [(intrinsicClockRegularRatio_jet_classification u).2.2.2]
  have hc0 := thetaCuspLogCurvature_pos u
  have hc := sourceCurvature_gt_eighteen hu
  have hb := source_projective_upper hu
  have hv := source_fourth_curvature_upper hu
  rw [←curvature_second u] at hb
  rw [←curvature_fourth u] at hv
  let b := iteratedDeriv 2 c u/c u
  let v := iteratedDeriv 4 c u/c u
  have hb' : 0 ≤ 9-b := by
    have h := (div_lt_iff₀ hc0).mpr hb
    dsimp only [b]
    linarith
  have hv' : 0 ≤ 846-v := by
    have h := (div_lt_iff₀ hc0).mpr hv
    dsimp only [v]
    linarith
  have hct : 0 ≤ c u-18 := by linarith
  have hp : 0 < 891*(c u)^2-1017*c u*b-122*v+176*b^2 := by
    have he : 891*(c u)^2-1017*c u*b-122*v+176*b^2=
        891*(c u-18)^2+22923*(c u-18)+20718+
        1017*c u*(9-b)+122*(846-v)+176*b^2 := by ring
    rw [he]
    positivity
  have hp' : 0 < 891*(c u)^2-1017*iteratedDeriv 2 c u-122*v+176*b^2 := by
    convert hp using 1
    dsimp only [b]
    field_simp [hc0.ne']
  have hk := denominatorClockRate_pos u
  have hpow := Real.rpow_pos_of_pos hc0 ((8:ℝ)/5)
  exact mul_pos (by positivity) hp'


/-- The actual inverse-source/clock ratio strictly increases near its removable
endpoint. This is the local source comparison itself, without a sign premise. -/
theorem intrinsicClockRegularRatio_deriv_pos_near_zero {u : ℝ} (hu : 0 ≤ u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < deriv (intrinsicClockRegularRatio u) t := by
  let f := intrinsicClockRegularRatio u
  have hf : ContDiff ℝ ∞ f := intrinsicClockRegularRatio_smooth u
  have h4c : ContinuousAt (iteratedDeriv 4 f) 0 :=
    (HTGeometry.contDiff_top_iteratedDeriv_real f hf 4).continuous.continuousAt
  have h4pos : 0 < iteratedDeriv 4 f 0 := intrinsicClockRegularRatio_fourth_pos hu
  have hevent : {t : ℝ | 0 < iteratedDeriv 4 f t} ∈ nhds 0 := h4c.eventually (Ioi_mem_nhds h4pos)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hp4 (t : ℝ) (ht : 0 < t) (htδ : t < δ) : 0 < iteratedDeriv 4 f t := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht]
    exact htδ
  have step (n : ℕ) (hzero : iteratedDeriv n f 0=0)
      (hpos : ∀ t : ℝ, 0 < t → t < δ → 0 < iteratedDeriv (n+1) f t) :
      ∀ t : ℝ, 0 < t → t < δ → 0 < iteratedDeriv n f t := by
    intro t ht htδ
    have hc := (HTGeometry.contDiff_top_iteratedDeriv_real f hf n).continuous
    have hm : StrictMonoOn (iteratedDeriv n f) (Icc 0 t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 t) hc.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      rw [←iteratedDeriv_succ]
      exact hpos x hx.1 (hx.2.trans htδ)
    have hh := hm (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht.le⟩)
      (show t ∈ Icc 0 t from ⟨ht.le,le_rfl⟩) ht
    simpa only [hzero] using hh
  have hj := intrinsicClockRegularRatio_jet_classification u
  have hp3 := step 3 hj.2.2.1 hp4
  have hp2 := step 2 hj.2.1 hp3
  have hp1 := step 1 hj.1 hp2
  refine ⟨δ,hδ,?_⟩
  intro t ht htδ
  simpa only [iteratedDeriv_one] using hp1 t ht htδ

/-- Local strict order holds for the original positive inverse source divided
by the original denominator clock, not merely its smooth extension. -/
theorem intrinsicActionInverseSource_clock_strictMono_near_zero {u : ℝ} (hu : 0 ≤ u) :
    ∃ δ : ℝ, 0 < δ ∧ StrictMonoOn
      (fun t => intrinsicActionInverseSource u t/denominatorClockProfile u t) (Ioo 0 δ) := by
  obtain ⟨δ,hδ,hp⟩ := intrinsicClockRegularRatio_deriv_pos_near_zero hu
  have hm : StrictMonoOn (intrinsicClockRegularRatio u) (Ioo 0 δ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 δ)
      (intrinsicClockRegularRatio_smooth u).continuous.continuousOn
    intro t ht
    rw [interior_Ioo] at ht
    exact hp t ht.1 ht.2
  refine ⟨δ,hδ,?_⟩
  intro a ha b hb hab
  dsimp only
  rw [intrinsicClockRegularRatio_eq ha.1,intrinsicClockRegularRatio_eq hb.1]
  exact hm ha hb hab

end
end RHTower.ThetaCuspDefect
