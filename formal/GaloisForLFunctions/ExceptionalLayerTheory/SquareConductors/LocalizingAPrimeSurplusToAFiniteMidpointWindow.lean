import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SharpPowerRecoveryFromOrdinaryPrimeMidpoints
import GaloisForLFunctions.RHTower.ChebyshevThetaLittlewoodOmega

/-!
# Localizing a prime surplus to one finite window of integer midpoints

A nonpositive midpoint defect bounds a price between its two outer
dilation strips. The square-root weight contracts strictly, so the
comparison holds for bounded discontinuous prices. Applied to Chebyshev's
function, the corpus zero-free strip pays for both boundaries of a finite
observation window at a cost strictly below the square-root scale.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A submean inequality needs to be tested only on [L,U]. Bounds on
the two adjoining dilation strips then propagate throughout the interval.
Boundedness in the square-root unit replaces any continuity condition. -/
theorem midpoint_comparison_on_two_strips {F : ℝ → ℝ} {L U : ℝ} (hL : 0<L)
    {C : ℝ} (hC : 0≤C)
    (hbase : ∀ y ∈ Icc (2/3*L) (4/3*U), F y≤C*y^(1/2:ℝ))
    (hout : ∀ y ∈ Icc (2/3*L) (4/3*U), y∉Icc L U → F y≤0)
    (hin : ∀ y ∈ Icc L U, 2*F y≤F ((2/3)*y)+F ((4/3)*y)) :
    ∀ y ∈ Icc (2/3*L) (4/3*U), F y≤0 := by
  let r := ternaryPowerGain (1/2)
  have hr : 0<r := ternary_gain_pos _
  have hr' : r<1 := (ternary_gain_phase _).1.mpr ⟨by norm_num,by norm_num⟩
  have iter (n : ℕ) (y : ℝ) (hy : y∈Icc (2/3*L) (4/3*U)) : F y≤C*y^(1/2:ℝ)*r^n := by
    induction n generalizing y with
    | zero => simpa only [pow_zero,mul_one] using hbase y hy
    | succ n ih =>
      have hy' : 0<y := (mul_pos (by norm_num) hL).trans_le hy.1
      by_cases h : y∈Icc L U
      · have hleft := ih ((2/3)*y) ⟨by linarith only [h.1],by linarith only [h.2,hy']⟩
        have hright := ih ((4/3)*y) ⟨by linarith only [h.1,hy'],by linarith only [h.2]⟩
        rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2/3) hy'.le] at hleft
        rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4/3) hy'.le] at hright
        have he := congrArg (fun q : ℝ => C*y^(1/2:ℝ)*r^n*q)
          (show r=((2/3:ℝ)^(1/2:ℝ)+(4/3:ℝ)^(1/2:ℝ))/2 from rfl)
        change C*y^(1/2:ℝ)*r^n*r=C*y^(1/2:ℝ)*r^n*(((2/3:ℝ)^(1/2:ℝ)+(4/3:ℝ)^(1/2:ℝ))/2) at he
        rw [pow_succ]
        linarith only [hin y h,hleft,hright,he]
      · exact (hout y hy h).trans (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hy'.le _)) (pow_nonneg hr.le _))
  intro y hy
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr').const_mul (C*y^(1/2:ℝ))
  exact (le_of_tendsto_of_tendsto' tendsto_const_nhds hz fun n => iter n y hy).trans_eq (mul_zero _)

/-- Rounding any one of the four integer dilations can add fewer than
four sites. The same power majorant works for both signs of the defect. -/
private theorem rounded_midpoint_both_signs {d y : ℝ} (hd : 0<d) (hy : 0<y) :
    |realMidpointObservation Chebyshev.theta y-primeMidpointPrice ⌊y⌋₊|≤
      (16*(4:ℝ)^d/d)*y^d := by
  let n := ⌊y⌋₊
  have hn : (n:ℝ)≤y := Nat.floor_le hy.le
  have hstep : y<(n:ℝ)+1 := Nat.lt_floor_add_one _
  let B := 4*(4:ℝ)^d/d*y^d
  have part (k : ℕ) (hk : k≤4) :
      0≤Chebyshev.theta ((k:ℝ)*y)-Chebyshev.theta (k*n:ℕ) ∧
      Chebyshev.theta ((k:ℝ)*y)-Chebyshev.theta (k*n:ℕ)≤B := by
    let z := ⌊(k:ℝ)*y⌋₊
    have hz : (z:ℝ)≤(k:ℝ)*y := Nat.floor_le (by positivity)
    have hkn : k*n≤z := Nat.le_floor (by push_cast; exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))
    have h4 : (k:ℝ)≤4 := by exact_mod_cast hk
    have width : (z:ℝ)-(k*n:ℕ)≤4 := by
      push_cast
      linarith only [hz,mul_le_mul_of_nonneg_left hstep.le (Nat.cast_nonneg (α:=ℝ) k),h4]
    have hlog := (Real.log_le_rpow_div (Nat.cast_nonneg (α:=ℝ) z) hd).trans
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (hz.trans (mul_le_mul_of_nonneg_right h4 hy.le)) hd.le) hd.le)
    rw [Chebyshev.theta_eq_theta_coe_floor ((k:ℝ)*y)]
    refine ⟨sub_nonneg.mpr (Chebyshev.theta_mono (Nat.cast_le.mpr hkn)),?_⟩
    have hh := (theta_integer_interval_bound hkn).trans (mul_le_mul width hlog (Real.log_natCast_nonneg z)
      (by norm_num : (0:ℝ)≤4))
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hy.le] at hh
    change _≤4*(4:ℝ)^d/d*y^d
    exact hh.trans_eq (by ring)
  have h₂ := part 2 (by decide)
  have h₃ := part 3 (by decide)
  have h₄ := part 4 le_rfl
  norm_num only [Nat.cast_ofNat] at h₂ h₃ h₄
  change |realMidpointObservation Chebyshev.theta y-primeMidpointPrice n|≤_
  rw [realMidpointObservation,prime_midpoint_price_eq,abs_le]
  simp only [B,div_eq_mul_inv] at h₂ h₃ h₄ ⊢
  constructor <;> linarith only [h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]

private def boundaryExponent : ℝ := 41999/48000
private def windowErrorExponent : ℝ := 5999/12000

/-- Above the zero abscissa, the same power majorizes the ordinary-prime
error once it covers the square-root contribution of proper powers. -/
theorem theta_power_envelope_of_zero_sup {a : ℝ} (ha : _root_.RHTower.zeroReSup < a) (hh : 1/2 ≤ a) :
    ∃ M : ℝ, 0≤M ∧ ∀ y : ℝ, 1≤y → |Chebyshev.theta y-y|≤M*y^a := by
  obtain ⟨C,hC,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow ha
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C+|D|,add_nonneg hC (abs_nonneg _),fun y hy => ?_⟩
  have ht := Chebyshev.theta_le_psi y
  have hpow := Real.rpow_le_rpow_of_exponent_le hy hh
  have hproper := (hD y).trans (mul_le_mul (le_abs_self D) (by simpa only [Real.sqrt_eq_rpow] using hpow) (Real.sqrt_nonneg _) (abs_nonneg _))
  have hθ := abs_le.mp (hψ y hy)
  have hab := mul_nonneg (abs_nonneg D) (Real.rpow_nonneg (zero_le_one.trans hy) a)
  rw [abs_le]
  constructor <;> linarith only [ht,hproper,hθ.1,hθ.2,hab]

private theorem theta_boundary_envelope :
    ∃ M : ℝ, 0≤M ∧ ∀ y : ℝ, 1≤y → |Chebyshev.theta y-y|≤M*y^boundaryExponent :=
  theta_power_envelope_of_zero_sup
    (GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt (by norm_num [boundaryExponent]))
    (by norm_num [boundaryExponent])

/-- The finite annulus uses the same reciprocal gap as the full Green
inverse. Its two external boundaries contribute a fixed power strictly
below one half, for either sign of the ordinary-prime price. -/
theorem prime_error_from_square_root_to_fourth_power :
    ∃ K : ℝ, 0≤K ∧ ∀ x : ℝ, 36≤x → ∀ σ : ℝ, (σ=1 ∨ σ= -1) → ∀ A : ℝ, 0≤A →
      (∀ n : ℕ, x^(1/2:ℝ)≤n → (n:ℝ)≤x^4 → σ*primeMidpointPrice n≤A*(n:ℝ)^(1/2:ℝ)) →
      σ*(Chebyshev.theta x-x)≤A/midpointPowerGap (1/2)*x^(1/2:ℝ)+K*x^(5999/12000:ℝ) := by
  obtain ⟨M,hM,hME⟩ := theta_boundary_envelope
  let d : ℝ := 1/4
  let s : ℝ := 1/2
  let J := 16*(4:ℝ)^d/d
  let B := J/midpointPowerGap d
  have hJ : 0≤J := by dsimp only [J,d]; positivity
  have hB : 0≤B := div_nonneg hJ (midpointPowerGap_pos ⟨by norm_num [d],by norm_num [d]⟩).le
  have ha : 0≤boundaryExponent := by norm_num [boundaryExponent]
  refine ⟨M*(6:ℝ)^boundaryExponent+M+B,by positivity,?_⟩
  intro x hx σ hσ A hA hread
  have hx1 : 1≤x := by linarith only [hx]
  have hx0 : 0<x := zero_lt_one.trans_le hx1
  let L := 6*x^s
  let U := x^4
  let H := A/midpointPowerGap s
  have hH : 0≤H := div_nonneg hA (midpointPowerGap_pos ⟨by norm_num [s],by norm_num [s]⟩).le
  have hL : 6≤L := by
    have h := Real.one_le_rpow hx1 (by norm_num [s] : 0 ≤ s)
    dsimp only [L]
    linarith only [h]
  have hxL : L≤x := by
    have hs : 6≤Real.sqrt x := Real.le_sqrt_of_sq_le (by simpa only [show (6:ℝ)^2=36 by norm_num] using hx)
    have h := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
    simpa only [L,s,←Real.sqrt_eq_rpow,←sq,Real.sq_sqrt hx0.le] using h
  have hxU : x≤U := by
    change x≤x^4
    calc x = x^1 := (pow_one _).symm
         _ ≤ x^4 := pow_le_pow_right₀ hx1 (by decide)
  let low := M*L^boundaryExponent
  let slope := M*U^(boundaryExponent-1)
  let V := fun y : ℝ => σ*(Chebyshev.theta y-y)-
    (H*y^s+B*y^d+low+slope*y)
  have hnon (y : ℝ) (hy : 0≤y) : 0≤H*y^s+B*y^d+low+slope*y := by
    dsimp only [low,slope,U,L]
    positivity
  have one (y : ℝ) (hy : y∈Icc (2/3*L) (4/3*U)) : 1≤y := by linarith only [hy.1,hL]
  have hmajor (y : ℝ) (hy : 1≤y) : σ*(Chebyshev.theta y-y)≤M*y^boundaryExponent := by
    apply le_trans _ (hME y hy)
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using le_abs_self (Chebyshev.theta y-y)
    · simpa only [neg_one_mul] using neg_le_abs (Chebyshev.theta y-y)
  let C := M*((4/3)*U)^boundaryExponent
  have hC : 0≤C := by dsimp only [C,U]; positivity
  have outside (y : ℝ) (hy : y∈Icc (2/3*L) (4/3*U)) (ho : y∉Icc L U) : V y≤0 := by
    have h1 := one y hy
    have h0 := zero_lt_one.trans_le h1
    have p₁ := mul_nonneg hH (Real.rpow_nonneg h0.le s)
    have p₂ := mul_nonneg hB (Real.rpow_nonneg h0.le d)
    have hl : 0≤low := by dsimp only [low,L]; positivity
    have hr : 0 ≤ slope*y := by dsimp only [slope,U]; positivity
    simp only [mem_Icc,not_and_or,not_le] at ho
    dsimp only [V]
    rcases ho with hlo | hhi
    · have h := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0.le hlo.le ha) hM
      change M*y^boundaryExponent≤low at h
      linarith only [hmajor y h1,h,p₁,p₂,hr]
    · have hneg : boundaryExponent-1≤0 := by norm_num [boundaryExponent]
      have h := Real.rpow_le_rpow_of_nonpos (show 0<U by dsimp only [U]; positivity) hhi.le hneg
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hM) h0.le
      have he := Real.rpow_add_one h0.ne' (boundaryExponent-1)
      rw [sub_add_cancel] at he
      rw [mul_assoc M,←he] at hh
      change M*y^boundaryExponent ≤ slope*y at hh
      linarith only [hmajor y h1,hh,p₁,p₂,hl]
  have inside (y : ℝ) (hy : y∈Icc L U) : 2*V y≤V ((2/3)*y)+V ((4/3)*y) := by
    let z := y/3
    let n := ⌊z⌋₊
    have hz : 0<z := by dsimp only [z]; linarith only [hL,hy.1]
    have hn : (n:ℝ)≤z := Nat.floor_le hz.le
    have hnlow : x^s≤n := by
      have h := Nat.lt_floor_add_one z
      have h1 := Real.one_le_rpow hx1 (by norm_num [s] : 0 ≤ s)
      change z<(n:ℝ)+1 at h
      dsimp only [z] at h
      have hLx : 6*x^s≤y := hy.1
      linarith only [hLx,h,h1]
    have hzy : z≤y := div_le_self (by linarith only [hy.1,hL]) (by norm_num)
    have hnhi : (n:ℝ)≤x^4 := hn.trans (hzy.trans hy.2)
    have hm := (hread n hnlow hnhi).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by norm_num [s] : 0 ≤ s)) hA)
    have hround := abs_le.mp (rounded_midpoint_both_signs (by norm_num [d] : 0<d) hz)
    have hprice : σ*realMidpointObservation Chebyshev.theta z≤A*z^s+J*z^d := by
      change -(J*z^d)≤realMidpointObservation Chebyshev.theta z-primeMidpointPrice n ∧
        realMidpointObservation Chebyshev.theta z-primeMidpointPrice n≤J*z^d at hround
      rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul] at hm ⊢ <;>
        linarith only [hround.1,hround.2,hm]
    have eigen (r C : ℝ) (hgap : 0 < midpointPowerGap r) :
        2*(C/midpointPowerGap r)*(3*z)^r-(C/midpointPowerGap r)*(2*z)^r-
          (C/midpointPowerGap r)*(4*z)^r=C*z^r := by
      have h := congrArg (fun v : ℝ => C/midpointPowerGap r*v) (real_midpoint_of_power r hz.le)
      dsimp only [realMidpointObservation] at h
      rw [←mul_assoc,div_mul_cancel₀ C hgap.ne'] at h
      linarith only [h]
    have e₁ := eigen s A (midpointPowerGap_pos ⟨by norm_num [s],by norm_num [s]⟩)
    have e₂ := eigen d J (midpointPowerGap_pos ⟨by norm_num [d],by norm_num [d]⟩)
    change 2*H*(3*z)^s-H*(2*z)^s-H*(4*z)^s=_ at e₁
    change 2*B*(3*z)^d-B*(2*z)^d-B*(4*z)^d=_ at e₂
    have hy₃ : 3*z=y := by dsimp only [z]; ring
    have hy₂ : 2*z=2/3*y := by dsimp only [z]; ring
    have hy₄ : 4*z=4/3*y := by dsimp only [z]; ring
    simp only [realMidpointObservation,hy₃,hy₂,hy₄] at hprice e₁ e₂
    dsimp only [V]
    linarith only [hprice,e₁,e₂]
  have hlocal := midpoint_comparison_on_two_strips (F:=V) (by linarith only [hL] : 0<L) hC
    (fun y hy => by
      have h1 := one y hy
      have h0 := zero_le_one.trans h1
      have h := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hy.2 ha) hM
      have hCy := le_mul_of_one_le_right hC (Real.one_le_rpow h1 (by norm_num : (0:ℝ)≤1/2))
      dsimp only [V]
      exact (sub_le_self _ (hnon y h0)).trans ((hmajor y h1).trans (h.trans hCy)))
    outside inside x ⟨by linarith only [hxL,hL],by linarith only [hxU,hx0]⟩
  have hlo : low≤M*(6:ℝ)^boundaryExponent*x^windowErrorExponent := by
    dsimp only [low,L]
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _),←Real.rpow_mul hx0.le,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num [s,boundaryExponent,windowErrorExponent])) (by positivity)
  have hhi : slope*x=M*x^windowErrorExponent := by
    change M*(x^4)^(boundaryExponent-1)*x=_
    rw [←Real.rpow_natCast x 4,←Real.rpow_mul hx0.le,mul_assoc,←Real.rpow_add_one hx0.ne']
    norm_num [boundaryExponent,windowErrorExponent]
  have hsmall := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1
    (show d≤windowErrorExponent by norm_num [d,windowErrorExponent])) hB
  change σ*(Chebyshev.theta x-x)-(H*x^s+B*x^d+low+slope*x)≤0 at hlocal
  change _≤H*x^s+(M*(6:ℝ)^boundaryExponent+M+B)*x^windowErrorExponent
  linarith only [hlocal,hlo,hhi,hsmall]

/-- Largest nonnegative normalized reading on the finite integer window.
Inserting zero also defines the maximum for empty windows. -/
def finiteMidpointPeak (σ x : ℝ) : ℝ :=
  let W := Finset.Icc ⌈x^(1/2:ℝ)⌉₊ ⌊x^4⌋₊
  let V := W.image fun n : ℕ => σ*primeMidpointPrice n/(n:ℝ)^(1/2:ℝ)
  (insert 0 V).max' (Finset.insert_nonempty 0 V)

/-- At every sufficiently large real x, a finite maximum of actual prime
midpoints controls each sign of the prime error with a power saving
over the square-root scale. -/
theorem prime_error_bounded_by_finite_midpoint_peak :
    ∃ K : ℝ, 0≤K ∧ ∀ x : ℝ, 36≤x → ∀ σ : ℝ, (σ=1 ∨ σ= -1) →
      σ*(Chebyshev.theta x-x)≤finiteMidpointPeak σ x/midpointPowerGap (1/2)*Real.sqrt x+
        K*x^(5999/12000:ℝ) := by
  obtain ⟨K,hK,h⟩ := prime_error_from_square_root_to_fourth_power
  refine ⟨K,hK,fun x hx σ hσ => ?_⟩
  let W := Finset.Icc ⌈x^(1/2:ℝ)⌉₊ ⌊x^4⌋₊
  let price := fun n : ℕ => σ*primeMidpointPrice n/(n:ℝ)^(1/2:ℝ)
  let V := insert 0 (W.image price)
  have hpeak {r : ℝ} (hr : r∈V) : r≤finiteMidpointPeak σ x := Finset.le_max' V r hr
  rw [Real.sqrt_eq_rpow]
  apply h x hx σ hσ _ (hpeak (Finset.mem_insert_self _ _))
  intro n hl hu
  have hn : n∈W := Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hl,Nat.le_floor hu⟩
  have hpos : 0<(n:ℝ) := (Real.rpow_pos_of_pos (by linarith only [hx] : 0<x) _).trans_le hl
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hpos _)).mp
    (hpeak (Finset.mem_insert_of_mem (Finset.mem_image_of_mem price hn)))

private def tripleLog (x : ℝ) := Real.log (Real.log (Real.log x))

/-- Triple logarithms at the two ends of the power window differ by a
bounded additive amount once the smaller argument is large. -/
private theorem triple_log_on_power_window :
    ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x^(1/2:ℝ)≤y → y≤x^4 → tripleLog y≤tripleLog x+Real.log 2 := by
  have hlog := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hs := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2))
  filter_upwards [eventually_gt_atTop (1:ℝ),hlog.eventually_ge_atTop (Real.log 4),
    hs.eventually_gt_atTop (Real.exp 1)] with x hx hxlog hmin
  change Real.log 4≤Real.log (Real.log x) at hxlog
  intro y hlo hup
  have hy : Real.exp 1<y := hmin.trans_le hlo
  have hly : 1<Real.log y := (Real.lt_log_iff_exp_lt ((Real.exp_pos 1).trans hy)).mpr hy
  have hu : Real.log y≤4*Real.log x := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log ((Real.exp_pos _).trans hy) hup
  have hll := Real.log_le_log (zero_lt_one.trans hly) hu
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (Real.log_pos hx).ne'] at hll
  have hll' : Real.log (Real.log y)≤2*Real.log (Real.log x) := by linarith only [hll,hxlog]
  have hxll : 0<Real.log (Real.log x) := (Real.log_pos (by norm_num : (1:ℝ)<4)).trans_le hxlog
  have h₃ := Real.log_le_log (Real.log_pos hly) hll'
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hxll.ne'] at h₃
  exact h₃.trans_eq (add_comm _ _)

/-- Every constant strictly below the product of the Mellin gap and
Littlewood's ordinary-prime constant occurs for both signs of the
integer midpoint, with the full triple logarithm. -/
theorem littlewood_excursions_of_integer_prime_midpoints {c : ℝ} (hc : 0<c)
    (hc' : c < midpointPowerGap (1/2)*(_root_.RHTower.littlewoodConst/28)) :
    ∀ σ : ℝ, (σ=1 ∨ σ= -1) →
      ∃ᶠ n : ℕ in atTop, c*Real.sqrt n*Real.log (Real.log (Real.log n))<σ*primeMidpointPrice n := by
  obtain ⟨K,hK,hwindow⟩ := prime_error_from_square_root_to_fourth_power
  intro σ hσ
  let g := midpointPowerGap (1/2)
  let C := _root_.RHTower.littlewoodConst/28
  have hg : 0<g := midpointPowerGap_pos ⟨by norm_num,by norm_num⟩
  have hgap : 0<C-c/g := sub_pos.mpr ((div_lt_iff₀ hg).mpr (by
    change c<g*C at hc'
    rwa [mul_comm C g]))
  have exc : ∃ᶠ x : ℝ in atTop, C*Real.sqrt x*tripleLog x<σ*(Chebyshev.theta x-x) := by
    obtain ⟨hneg,hpos⟩ := _root_.RHTower.chebyshevTheta_sub_omega_pm_littlewood
    rcases hσ with rfl | rfl
    · simpa only [C,tripleLog,one_mul] using hpos
    · exact hneg.mono fun x hx => by
        dsimp only [C,tripleLog]
        rw [neg_one_mul]
        linarith only [hx]
  by_contra! hn
  obtain ⟨N,hN⟩ := eventually_atTop.mp hn
  have hL : Tendsto tripleLog atTop atTop := _root_.RHTower.tendsto_logLogLog_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).eventually_ge_atTop (N:ℝ)
  have large := hL.eventually_gt_atTop (((c/g)*Real.log 2+K)/(C-c/g))
  obtain ⟨x,hx,h36,hNx,hlogs,h0,hpaid⟩ := (exc.and_eventually
    ((eventually_ge_atTop (36:ℝ)).and (hpow.and (triple_log_on_power_window.and
      ((hL.eventually_ge_atTop 0).and large))))).exists
  let A := c*(tripleLog x+Real.log 2)
  have hA : 0≤A := mul_nonneg hc.le (add_nonneg h0 (Real.log_nonneg (by norm_num)))
  have hread (n : ℕ) (hl : x^(1/2:ℝ)≤n) (hu : (n:ℝ)≤x^4) :
      σ*primeMidpointPrice n≤A*(n:ℝ)^(1/2:ℝ) := by
    have hh := hN n (Nat.cast_le.mp (hNx.trans hl))
    have h := mul_le_mul_of_nonneg_left (hlogs n hl hu) (mul_nonneg hc.le (Real.sqrt_nonneg n))
    change σ*primeMidpointPrice n≤c*Real.sqrt n*tripleLog n at hh
    rw [←Real.sqrt_eq_rpow]
    dsimp only [A]
    linarith only [hh,h]
  have hupper := hwindow x h36 σ hσ A hA hread
  have hx1 : 1≤x := by linarith only [h36]
  have hpow' := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5999/12000:ℝ)≤1/2)
  have hku := mul_le_mul_of_nonneg_left hpow' hK
  rw [←Real.sqrt_eq_rpow x] at hupper hku
  have hlt := (div_lt_iff₀ hgap).mp hpaid
  have hfinal : (A/g+K)*Real.sqrt x < C*Real.sqrt x*tripleLog x := by
    dsimp only [A]
    rw [show c*(tripleLog x+Real.log 2)/g=c/g*(tripleLog x+Real.log 2) by ring]
    have h := mul_lt_mul_of_pos_right hlt (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx1))
    linarith only [h]
  change σ*(Chebyshev.theta x-x)≤A/g*Real.sqrt x+K*x^(5999/12000:ℝ) at hupper
  linarith only [hupper,hx,hfinal,hku]

#print axioms prime_error_bounded_by_finite_midpoint_peak
#print axioms littlewood_excursions_of_integer_prime_midpoints

#print axioms midpoint_comparison_on_two_strips
#print axioms prime_error_from_square_root_to_fourth_power

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
