import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import GaloisForLFunctions.HTGeometry.IteratedDerivVanishing

/-! Exact vanishing jets of the four original optical radial caps. -/
open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMOpticalBoundaryCaps
open GaloisForLFunctions.HTGeometry
noncomputable section

private def primitiveBasis (i : Fin 7) (x : ℝ) : ℝ :=
  ![(-1/5)*(x^5)⁻¹,(-1/4)*(x^4)⁻¹,(-1/3)*(x^3)⁻¹,
    (-1/2)*(x^2)⁻¹,-x⁻¹,Real.log x,x] i

private theorem primitiveBasis_derivative (i : Fin 7) (x : Ioi (0:ℝ)) :
    HasDerivAt (primitiveBasis i) (x.val^i.val/x.val^6) x.val := by
  have hx : x.val ≠ 0 := ne_of_gt x.property
  fin_cases i
  · convert (((hasDerivAt_id x.val).pow 5).inv (pow_ne_zero 5 hx)).const_mul (-1/5) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 4).inv (pow_ne_zero 4 hx)).const_mul (-1/4) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 3).inv (pow_ne_zero 3 hx)).const_mul (-1/3) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · convert (((hasDerivAt_id x.val).pow 2).inv (pow_ne_zero 2 hx)).const_mul (-1/2) using 1 <;>
      first | rfl | (try dsimp only [id_eq,Pi.pow_apply]; field_simp [hx]; ring)
  · change HasDerivAt (fun y : ℝ => -y⁻¹) (x.val^4/x.val^6) x.val
    convert ((hasDerivAt_id x.val).inv hx).neg using 1 <;>
      first | rfl | (norm_num only [id_eq]; field_simp [hx])
  · change HasDerivAt Real.log (x.val^5/x.val^6) x.val
    convert Real.hasDerivAt_log hx using 1
    field_simp [hx]
  · change HasDerivAt (fun y : ℝ => y) (x.val^6/x.val^6) x.val
    convert hasDerivAt_id x.val using 1 <;>
      first | rfl | exact div_self (pow_ne_zero 6 hx)

private def coefficient (n i : Fin 7) (L : ℝ) : ℝ :=
  if i.val ≤ n.val then (n.val.choose i.val:ℝ)*(-L)^(n.val-i.val) else 0

@[fun_prop] private theorem coefficient_smooth (n i : Fin 7) (k : ℕ) (x : ℝ) :
    ContDiffAt ℝ k (coefficient n i) x := by
  unfold coefficient
  split_ifs <;> fun_prop

private def moment (n : Fin 7) (L x : ℝ) : ℝ :=
  (∑ i : Fin 7, coefficient n i L*primitiveBasis i (L+x))-
    ∑ i : Fin 7, coefficient n i L*primitiveBasis i L

private theorem moment_derivative (n : Fin 7) (L x : ℝ) (hx : 0 < L+x) :
    HasDerivAt (moment n L) (x^n.val/(L+x)^6) x := by
  have hb (i : Fin 7) : HasDerivAt
      (fun y : ℝ => coefficient n i L*primitiveBasis i (L+y))
      (coefficient n i L*((L+x)^i.val/(L+x)^6)) x := by
    convert ((primitiveBasis_derivative i ⟨L+x,hx⟩).comp x
      ((hasDerivAt_id x).const_add L)).const_mul (coefficient n i L) using 1 <;>
      first | rfl | simp
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hb i)).sub_const
    (∑ i : Fin 7, coefficient n i L*primitiveBasis i L)
  apply hd.congr_deriv
  fin_cases n <;>
    norm_num [coefficient,Fin.sum_univ_succ,Fin.sum_univ_zero,Nat.choose] <;> ring

private theorem moment_smooth (n : Fin 7) (L : Ioi (2:ℝ)) (k : ℕ) :
    ContDiffAt ℝ k (moment n L.val) 0 := by
  have hL : L.val ≠ 0 := ne_of_gt (lt_trans (by norm_num) L.property)
  unfold moment
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,primitiveBasis,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  fun_prop (disch := simpa using hL)

private theorem moment_flat (n : Fin 7) (L : Ioi (2:ℝ)) (j : ℕ) (hj : j ≤ n.val) :
    iteratedDeriv j (moment n L.val) 0 = 0 := by
  by_cases hj0 : j=0
  · subst j
    simp [moment]
  have hderiv : deriv (moment n L.val) =ᶠ[𝓝 0]
      fun x : ℝ => x^n.val*((L.val+x)^6)⁻¹ := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with x hx
    have hLgt : (2:ℝ) < L.val := L.property
    have hxgt : (-1:ℝ) < x := hx.1
    simpa only [div_eq_mul_inv] using (moment_derivative n L.val x (by linarith only [hLgt,hxgt])).deriv
  have hL : L.val ≠ 0 := ne_of_gt (lt_trans (by norm_num) L.property)
  apply iteratedDeriv_eq_zero_of_velocity_flat (d := n.val)
    (D := fun x : ℝ => x^n.val) (G := fun x : ℝ => ((L.val+x)^6)⁻¹)
    (fun k => by fun_prop) (fun k => by fun_prop (disch := simpa using pow_ne_zero 6 hL)) hderiv
    (fun i hi => ?_) (by omega) hj
  have hn : n.val-i ≠ 0 := by omega
  simp [iteratedDeriv_pow,zero_pow hn]

/-- Original source-radius powers in the four radial coefficients. -/
def sourcePower (row : Fin 4) : ℕ := match row.val with | 0 => 1 | 1 => 1 | _ => 3
/-- Original target-radius powers in the same order. -/
def targetPower (row : Fin 4) : ℕ := match row.val with | 0 => 1 | 2 => 1 | _ => 3

/-- The four literal radial caps at a target endpoint `c`. At `c=1` this is
the source edge; `cap L (-1) row (-epsilon)` is the internal interface difference. -/
def cap (L c : ℝ) (row : Fin 4) : ℝ → ℝ :=
  match row.val with
  | 0 => fun x => moment 2 L x+(c-x)*moment 1 L x
  | 1 => fun x => moment 4 L x+3*(c-x)*moment 3 L x+3*(c-x)^2*moment 2 L x+(c-x)^3*moment 1 L x
  | 2 => fun x => moment 4 L x+(c-x)*moment 3 L x
  | _ => fun x => moment 6 L x+3*(c-x)*moment 5 L x+3*(c-x)^2*moment 4 L x+(c-x)^3*moment 3 L x

/-- Exact number of vanishing jets needed by the original source-polynomial current. -/
def capOrder (row : Fin 4) : ℕ := sourcePower row+1

private theorem cap_smooth (L : Ioi (2:ℝ)) (c : ℝ) (row : Fin 4) (k : ℕ) :
    ContDiffAt ℝ k (cap L.val c row) 0 := by
  have h1 := moment_smooth 1 L k
  have h2 := moment_smooth 2 L k
  have h3 := moment_smooth 3 L k
  have h4 := moment_smooth 4 L k
  have h5 := moment_smooth 5 L k
  have h6 := moment_smooth 6 L k
  fin_cases row <;> dsimp only [cap]
  all_goals fun_prop

private theorem cap_flat_nat (L : Ioi (2:ℝ)) (c : ℝ) (row : Fin 4) (j : ℕ)
    (hj : j < capOrder row) : iteratedDeriv j (cap L.val c row) 0 = 0 := by
  have h1 := moment_smooth 1 L j
  have h2 := moment_smooth 2 L j
  have h3 := moment_smooth 3 L j
  have h4 := moment_smooth 4 L j
  have h5 := moment_smooth 5 L j
  have h6 := moment_smooth 6 L j
  have hp (n : Fin 7) (hn : j ≤ n.val) (g : ℝ → ℝ)
      (hg : ∀ k : ℕ, ContDiffAt ℝ k g 0) :
      iteratedDeriv j (fun x => g x*moment n L.val x) 0=0 := by
    have h := iteratedDeriv_mul_eq_zero_of_vanishing j
      (fun k => moment_smooth n L k) hg (fun i hi => moment_flat n L i (le_trans hi hn))
    simpa only [mul_comm] using h
  have hsum {f g : ℝ → ℝ} (hf : ContDiffAt ℝ j f 0) (hg : ContDiffAt ℝ j g 0)
      (hf0 : iteratedDeriv j f 0=0) (hg0 : iteratedDeriv j g 0=0) :
      iteratedDeriv j (fun x => f x+g x) 0=0 := by
    rw [iteratedDeriv_fun_add hf hg,hf0,hg0,add_zero]
  fin_cases row <;> norm_num [capOrder,sourcePower] at hj
  all_goals dsimp only [cap]
  all_goals
    repeat' first
      | apply hsum (by fun_prop) (by fun_prop)
      | exact moment_flat _ L j (by omega)
      | exact hp _ (by omega) _ (fun k => by fun_prop)

/-- The actual optical cap has every jet below its source-determined order equal to zero. -/
theorem cap_flat_jet (L : Ioi (2:ℝ)) (c : ℝ) (row : Fin 4) (j : Fin (capOrder row)) :
    iteratedDeriv j.val (cap L.val c row) 0 = 0 :=
  cap_flat_nat L c row j.val j.isLt

private theorem moment_integral (n : Fin 7) (L : Ioi (2:ℝ)) (x : Ioo (-1:ℝ) 1) :
    (∫ y in (0:ℝ)..x.val, y^n.val/(L.val+y)^6)=moment n L.val x.val := by
  have hpos (y : ℝ) (hy : y ∈ uIcc (0:ℝ) x.val) : 0 < L.val+y := by
    have hmin : (-1:ℝ) < min 0 x.val := lt_min (by norm_num) x.property.1
    have hy1 : -1<y := hmin.trans_le hy.1
    have hLgt : (2:ℝ) < L.val := L.property
    linarith only [hy1,hLgt]
  have hi : IntervalIntegrable (fun y : ℝ => y^n.val/(L.val+y)^6) volume 0 x.val := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact ((continuousAt_id.pow n.val).div
      ((continuousAt_const.add continuousAt_id).pow 6)
      (pow_ne_zero 6 (hpos y hy).ne')).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => moment_derivative n L.val y (hpos y hy)) hi
  simpa [moment] using h

/-- The cap is the actual radial integral, with its moving target factor retained.
Both signs of the small cap length are included. -/
theorem cap_integral (L : Ioi (2:ℝ)) (c : ℝ) (row : Fin 4) (x : Ioo (-1:ℝ) 1) :
    (∫ y in (0:ℝ)..x.val,
      y^(sourcePower row)*(y+c-x.val)^(targetPower row)/(L.val+y)^6)=
        cap L.val c row x.val := by
  have hi (n : Fin 7) : IntervalIntegrable
      (fun y : ℝ => y^n.val/(L.val+y)^6) volume 0 x.val := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    have hmin : (-1:ℝ) < min 0 x.val := lt_min (by norm_num) x.property.1
    have hLgt : (2:ℝ) < L.val := L.property
    have hpos : 0 < L.val+y := by linarith only [hmin.trans_le hy.1,hLgt]
    exact ((continuousAt_id.pow n.val).div
      ((continuousAt_const.add continuousAt_id).pow 6)
      (pow_ne_zero 6 hpos.ne')).continuousWithinAt
  have hfour (a b c d : ℝ) (i j k l : Fin 7) :
      (∫ y in (0:ℝ)..x.val,
        a*(y^i.val/(L.val+y)^6)+b*(y^j.val/(L.val+y)^6)+
          c*(y^k.val/(L.val+y)^6)+d*(y^l.val/(L.val+y)^6))=
        a*moment i L.val x.val+b*moment j L.val x.val+
          c*moment k L.val x.val+d*moment l L.val x.val := by
    rw [intervalIntegral.integral_add (((hi i).const_mul a).add ((hi j).const_mul b) |>.add
      ((hi k).const_mul c)) ((hi l).const_mul d),
      intervalIntegral.integral_add (((hi i).const_mul a).add ((hi j).const_mul b)) ((hi k).const_mul c),
      intervalIntegral.integral_add ((hi i).const_mul a) ((hi j).const_mul b)]
    simp only [intervalIntegral.integral_const_mul,moment_integral _ L x]
  fin_cases row
  · convert hfour 1 (c-x.val) 0 0 2 1 0 0 using 1
    · apply intervalIntegral.integral_congr
      intro y hy
      simp only [sourcePower,targetPower]
      norm_num
      ring
    · simp [cap]
  · convert hfour 1 (3*(c-x.val)) (3*(c-x.val)^2) ((c-x.val)^3) 4 3 2 1 using 1
    · apply intervalIntegral.integral_congr
      intro y hy
      simp only [sourcePower,targetPower]
      norm_num
      ring
    · simp [cap]
  · convert hfour 1 (c-x.val) 0 0 4 3 0 0 using 1
    · apply intervalIntegral.integral_congr
      intro y hy
      simp only [sourcePower,targetPower]
      norm_num
      ring
    · simp [cap]
  · convert hfour 1 (3*(c-x.val)) (3*(c-x.val)^2) ((c-x.val)^3) 6 5 4 3 using 1
    · apply intervalIntegral.integral_congr
      intro y hy
      simp only [sourcePower,targetPower]
      norm_num
      ring
    · simp [cap]

/-- The image-side interface uses the same cap at the negative cap length;
all of its required jets also vanish. -/
theorem interface_cap_flat_jet (L : Ioi (2:ℝ)) (row : Fin 4) (j : Fin (capOrder row)) :
    iteratedDeriv j.val (fun x : ℝ => cap L.val (-1) row (-x)) 0=0 := by
  rw [iteratedDeriv_comp_neg]
  simp only [neg_zero,cap_flat_jet,smul_zero]

private theorem moment_joint_smooth (n : Fin 7) (L : Ioi (2:ℝ)) (k : ℕ) :
    ContDiffAt ℝ k (fun p : ℝ × ℝ => moment n p.1 p.2) (L.val,0) := by
  have hL : L.val ≠ 0 := ne_of_gt (lt_trans (by norm_num) L.property)
  simp only [moment,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,primitiveBasis,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  fun_prop (disch := simpa using hL)

/-- Joint smoothness in optical time and cap length supplies the mixed derivatives
needed for the actual source-current traces. -/
theorem cap_joint_smooth (L : Ioi (2:ℝ)) (c : ℝ) (row : Fin 4) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => cap p.1 c row p.2) (L.val,0) := by
  apply contDiffAt_infty.mpr
  intro k
  have h1 := moment_joint_smooth 1 L k
  have h2 := moment_joint_smooth 2 L k
  have h3 := moment_joint_smooth 3 L k
  have h4 := moment_joint_smooth 4 L k
  have h5 := moment_joint_smooth 5 L k
  have h6 := moment_joint_smooth 6 L k
  fin_cases row <;> dsimp only [cap]
  all_goals fun_prop

end
end RHTower.D4BMOpticalBoundaryCaps
