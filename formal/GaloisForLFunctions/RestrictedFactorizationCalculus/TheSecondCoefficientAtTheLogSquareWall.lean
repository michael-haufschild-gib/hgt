import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTwoSignsOfTheCriticalSmoothSector
import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsBelowTheRoughCofactorCutoff
import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeAndProperPowerMassAtTheCriticalWall

/-!
# The second coefficient at the log-square sieve wall

The rounded wall has square root asymptotic to the log of the endpoint.
An additional prime in a dyadic interval multiplies the signed smooth
supply, with logarithmic loss negligible at the second scale.
-/
noncomputable section
open Filter Finset RHTower RHTower.Sieve
open scoped Classical Topology ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev L (n : ℕ) := Real.log (n:ℝ)
private abbrev W := logSquareCutoff
private abbrev M (n : ℕ) := Real.log (L n)
private abbrev R (n : ℕ) := Real.sqrt (W n)
private abbrev l (n : ℕ) := Real.log (W n)
private abbrev second (n : ℕ) (main x : ℝ) := (x-main)*M n/L n
private abbrev ln_infty : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem log_wall_ratio :
    Tendsto (fun n => l n/M n) atTop (𝓝 2) := by
  have tube := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp log_square_wall_root_ratio
  rw [Real.log_one] at tube
  have negligible := tube.div_atTop (Real.tendsto_log_atTop.comp ln_infty)
  have h := negligible.const_mul 2
  rw [mul_zero] at h
  have g := h.const_add 2
  rw [add_zero] at g
  apply g.congr'
  filter_upwards [logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,ln_infty.eventually_gt_atTop 1] with n yn large
  have root : 0<R n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr yn)
  have pos := zero_lt_one.trans large
  have lp : 0<M n := Real.log_pos large
  change 2+2*(Real.log (R n/L n)/M n)=l n/M n
  rw [Real.log_div root.ne' pos.ne',Real.log_sqrt (Nat.cast_nonneg _)]
  change 2+2*((l n/2-M n)/M n)=l n/M n
  field_simp; ring

private theorem second_wall_scale :
    Tendsto (fun n => (R n/L n)*(M n/l n)) atTop (𝓝 (1/2)) := by
  have h := log_square_wall_root_ratio.mul (log_wall_ratio.inv₀ (by norm_num))
  simpa only [inv_div,one_mul,one_div] using h

private theorem normalized_log_losses :
    Tendsto (fun n => M n/L n) atTop (𝓝 0) ∧
    Tendsto (fun n => M n*M n/L n) atTop (𝓝 0) := by
  have lp : (0:ℝ)<1/2 := by norm_num
  have t := (isLittleO_log_rpow_atTop lp).tendsto_div_nhds_zero.comp ln_infty
  refine ⟨?_,?_⟩
  · simpa only [Real.rpow_one,Function.comp_apply] using
      (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero.comp ln_infty
  · have h := t.mul t
    rw [zero_mul] at h
    apply h.congr'
    filter_upwards [ln_infty.eventually_gt_atTop 0] with n pn
    change (M n/(L n)^(1/2:ℝ))*(M n/(L n)^(1/2:ℝ))=_
    rw [div_mul_div_comm,←Real.rpow_add pn,show (1/2:ℝ)+1/2=1 by norm_num,Real.rpow_one]

private theorem change_wall_units {f h : ℕ → ℝ} {A : ℝ}
    (bound : Tendsto (fun n => (f n-h n)*l n/R n) atTop (𝓝 A)) :
    Tendsto (fun n => second n (h n) (f n)) atTop (𝓝 (A/2)) := by
  have result := bound.mul second_wall_scale
  rw [show A*(1/2)=A/2 by ring] at result
  apply result.congr'
  filter_upwards [logSquareCutoff_tendsto_atTop.eventually_ge_atTop 2] with n yn
  have root : 0<R n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have logn : 0<l n := Real.log_pos (Nat.one_lt_cast.mpr yn)
  change (f n-h n)*l n/R n*(R n/L n*(M n/l n))=_
  dsimp only [second]; field_simp [root.ne',logn.ne']

private theorem scaled_height (a : ℝ) : Tendsto (fun n => a*L n/R n) atTop (𝓝 a) := by
  have ratio := log_square_wall_root_ratio.inv₀ (by norm_num)
  simp only [inv_div,inv_one] at ratio
  simpa only [mul_one,mul_div_assoc] using ratio.const_mul a

/-- The two squarefree sign populations and the count with repetitions
share the coefficient a(1+log(2/a))/2 at height X^a. -/
theorem second_coefficient_of_the_smooth_sign_populations {a : ℝ} (ap : 0<a) :
    let C := (a/2)*(1+Real.log (2/a))
    (∀ b,Tendsto (fun X => second X (a*L X/2) (Real.log (signedSmoothSector b (W X) (a*L X)).card)) atTop (𝓝 C)) ∧
    Tendsto (fun X => second X (a*L X/2)
      (Real.log (smoothUpTo (Nat.primesLE (W X)) ⌊Real.exp (a*L X)⌋₊).card)) atTop (𝓝 C) := by
  obtain ⟨signs,all⟩ := critical_smooth_counts_of_both_signs logSquareCutoff_tendsto_atTop ap (scaled_height a)
  have coefficient : a*(1+Real.log (2/a))/2=(a/2)*(1+Real.log (2/a)) := by ring
  exact ⟨fun b => coefficient ▸ change_wall_units (signs b),coefficient ▸ change_wall_units all⟩

private theorem smooth_sign_as_squarefree (b : Bool) (y : ℕ) (H : ℝ) :
    signedSmoothSector b y H=(squarefreeSmoothUpTo y ⌊Real.exp H⌋₊).filter
      (fun n => μ n=if b then (1:ℤ) else -1) := by
  ext n
  simp only [signedSmoothSector,squarefreeSmoothUpTo,mem_filter]
  constructor
  · rintro ⟨h,sign⟩
    have nz : μ n ≠ 0 := by rw [sign]; cases b <;> decide
    exact ⟨⟨h,ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp nz⟩,sign⟩
  · rintro ⟨⟨h,_⟩,sign⟩; exact ⟨h,sign⟩

private theorem growth_of_the_prime_octave {γ : ℝ} (gp : 0<γ) (g1 : γ ≤ 1) :
    ∀ᶠ X in atTop,let V := (X:ℝ)^γ
      let P := (windowPrimes (V/2) (2*(V/2))).card
      0<P ∧ γ*L X-M X-Real.log 4 ≤ Real.log P := by
  have grows : Tendsto (fun X : ℕ => (X:ℝ)^γ/2) atTop atTop :=
    tendsto_atTop.mpr (fun k => (((tendsto_rpow_atTop gp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2*k)).mono
      (fun n h => by
        change 2*k ≤ (n:ℝ)^γ at h
        change k ≤ (n:ℝ)^γ/2
        linarith only [h]))
  filter_upwards [grows eventually_dyadic_prime_lower,ln_infty.eventually_gt_atTop 0,
    eventually_ge_atTop (2:ℕ)] with X supply lp xp
  let V := (X:ℝ)^γ
  let P := (windowPrimes (V/2) (2*(V/2))).card
  have x0 : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have v0 : 0<V := Real.rpow_pos_of_pos x0 _
  have eq : 2*(V/2)=V := by ring
  have gl : Real.log V=γ*L X := Real.log_rpow x0 _
  have norm : (99/100)*(V/2)/Real.log (2*(V/2)) ≤ P := supply
  rw [eq,gl] at norm
  have compare : V/(4*L X) ≤ P := by
    apply le_trans _ norm
    apply (div_le_div_iff₀ (by positivity) (mul_pos gp lp)).mpr
    nlinarith only [mul_le_of_le_one_right (mul_nonneg v0.le lp.le) g1]
  have small := div_pos v0 (mul_pos (by norm_num : (0:ℝ)<4) lp)
  have h := Real.log_le_log small compare
  rw [Real.log_div v0.ne' (by positivity),Real.log_mul (by norm_num) lp.ne',gl] at h
  exact ⟨Nat.cast_pos.mp (small.trans_le compare),by change γ*L X-M X-Real.log 4 ≤ Real.log P; linarith only [h]⟩

/-- The exact second coefficient for the smooth term in the centered
quotient identity, including its integer floor and its sieve prefactor. -/
theorem second_coefficient_of_the_smooth_quotient_center :
    Tendsto (fun X => second X (L X/2) (Real.log (smoothQuotientCenter (W X) X))) atTop
      (𝓝 ((1+Real.log 2)/2)) := by
  let H := fun X => L X-l X
  have grow := logSquareCutoff_tendsto_atTop
  have logs : Tendsto (fun X => l X/R X) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.comp grow)
    simpa only [Function.comp_apply,Real.sqrt_eq_rpow] using h
  have ratio := scaled_height 1
  simp only [one_mul] at ratio
  have h : Tendsto (fun X => H X/R X) atTop (𝓝 1) := by
    simpa only [H,sub_div,sub_zero] using ratio.sub logs
  have content := (critical_smooth_counts_of_both_signs grow zero_lt_one h).2
  have main := change_wall_units content
  simp only [one_mul,div_one] at main
  have err := (log_wall_ratio.mul normalized_log_losses.2).div_const 2
  rw [mul_zero,zero_div] at err
  have total := main.add err
  rw [add_zero] at total
  apply total.congr'
  filter_upwards [grow.eventually_ge_atTop 2,ln_infty.eventually_gt_atTop 1,
    h.eventually_const_lt (by norm_num : (0:ℝ)<1),eventually_ge_atTop (1:ℕ)] with X yp large high xp
  have x0 : (0:ℝ)<X := Nat.cast_pos.mpr xp
  have y0 : (0:ℝ)<W X := Nat.cast_pos.mpr (by omega)
  have mh : M X ≠ 0 := (Real.log_pos large).ne'
  have pos : 0<H X := (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr y0)).mp high
  have floor : ⌊Real.exp (H X)⌋₊=X/W X := by
    rw [show H X=Real.log X-Real.log (W X) from rfl,Real.exp_sub,Real.exp_log x0,Real.exp_log y0,
      Nat.floor_div_natCast,Nat.floor_natCast]
  let A := smoothUpTo (Nat.primesLE (W X)) (X/W X)
  have one : 1∈A := mem_smoothUpTo.mpr ⟨⟨le_rfl,floor ▸ Nat.le_floor
    (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr pos.le)⟩,by simp⟩
  have nonzero := (Nat.cast_pos.mpr (card_pos.mpr ⟨_,one⟩) : (0:ℝ)<A.card).ne'
  change second X (H X/2) (Real.log (smoothUpTo _ ⌊Real.exp (H X)⌋₊).card)+
    (l X/M X*(M X*M X/L X))/2=_
  rw [floor]
  change second X (H X/2) (Real.log A.card)+(l X/M X*(M X*M X/L X))/2=
    second X (L X/2) (Real.log ((W X:ℝ)*(A.card:ℝ)))
  rw [Real.log_mul y0.ne' nonzero]
  dsimp only [H,second,l]
  field_simp [mh]; ring

/-- Number of squarefree integers of the selected sign with rough part
at most the specified power of X at the log-square sieve wall. -/
def polynomialRoughSignCount (γ : ℝ) (b : Bool) (X : ℕ) :=
  ((smallRoughCofactors (W X) X ⌊(X:ℝ)^γ⌋₊).filter (fun n => μ n=if b then (1:ℤ) else -1)).card

private theorem signed_rough_sandwich {γ : ℝ} (gp : 0<γ) (g1 : γ<1) (b : Bool)
    {s : ℕ → ℝ} (st : Tendsto s atTop (𝓝 (1/2))) :
    ∀ᶠ X in atTop,let a := 1-γ
      let H := a*L X
      let E := deletionPrice (s X) (W X)
      let C := Real.log (polynomialRoughSignCount γ b X)
      Real.log (signedSmoothSector (!b) (W X) H).card+γ*L X-M X-Real.log 4 ≤ C ∧
      C ≤ γ*L X+s X*H+Real.log E+Real.log 4 := by
  let a := 1-γ
  have ap : 0<a := sub_pos.mpr g1
  filter_upwards [growth_of_the_prime_octave gp g1.le,cutoff_below_power gp,
    st.eventually_const_lt (by norm_num : (0:ℝ)<1/2),st.eventually_lt_const (by norm_num : (1/2:ℝ)<3/4),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 2,ln_infty.eventually_ge_atTop (Real.log 2/a),
    eventually_ge_atTop (2:ℕ)] with X supply room sp up yp high xp
  let y := W X
  let H := a*L X
  let T := (X:ℝ)^γ
  let P := (windowPrimes (T/2) (2*(T/2))).card
  let A := (signedSmoothSector (!b) y H).card
  let N := polynomialRoughSignCount γ b X
  let E := deletionPrice (s X) y
  let σ : ℤ := if b then 1 else -1
  have sign : (if !b then (1:ℤ) else -1)= -σ := by cases b <;> decide
  have x0 : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have t0 : 0<T := Real.rpow_pos_of_pos x0 _
  have h2 : Real.log 2 ≤ H := ((div_le_iff₀ ap).mp high).trans_eq (mul_comm ..)
  have apos : 0<A := card_pos.mpr (signed_sector_nonempty yp h2 (!b))
  have product : Real.exp H*T=X := by
    dsimp only [H,T,a,L]
    rw [mul_comm _ (Real.log _),Real.exp_mul,Real.exp_log x0,←Real.rpow_add x0,sub_add_cancel,Real.rpow_one]
  have tap : 2*(T/2)=T := by ring
  have wall : (⌊Real.exp H⌋₊:ℝ)*(2*(T/2)) ≤ X := by
    rw [tap,←product]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (Real.exp_pos _).le) t0.le
  have lim : (y:ℝ) ≤ T/2 := by linarith only [room]
  have inc : A*P ≤ N := by
    dsimp only [A]; rw [smooth_sign_as_squarefree,sign]
    exact products_supply_one_rough_sign y _ X _ (T/2) (half_pos t0) lim wall
      (by rw [tap]) σ
  have pp : 0<P := supply.1
  have np := (Nat.mul_pos apos pp).trans_le inc
  have count := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos apos pp) : (0:ℝ)<((A*P:ℕ):ℝ)) (Nat.cast_le.mpr inc)
  rw [Nat.cast_mul,Real.log_mul (Nat.cast_pos.mpr apos).ne' (Nat.cast_pos.mpr pp).ne'] at count
  refine ⟨by change Real.log A+γ*L X-M X-Real.log 4 ≤ Real.log N; linarith only [count,supply.2],?_⟩
  have small : s X<1 := up.trans (by norm_num)
  have den := sub_pos.mpr small
  have e0 : 0<E := zero_lt_one.trans_le (deletionPrice_one_le sp y)
  have price := small_rough_cofactor_card_bound sp small y X ⌊T⌋₊
  have sub : N ≤ (smallRoughCofactors y X ⌊T⌋₊).card := card_le_card (filter_subset ..)
  have top := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le t0.le) den.le
  have coeff : 1/(1-s X) ≤ 4 := (div_le_iff₀ den).mpr (by linarith only [up])
  have rat := mul_le_mul top coeff (one_div_nonneg.mpr den.le) (Real.rpow_nonneg t0.le (1-s X))
  simp only [mul_one_div] at rat
  have paid := (Nat.cast_le.mpr sub : (N:ℝ) ≤ _).trans
    (price.trans (mul_le_mul_of_nonneg_left rat (mul_nonneg e0.le (Real.rpow_nonneg x0.le _))))
  have upper := Real.log_le_log (Nat.cast_pos.mpr np) paid
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul e0.ne' (Real.rpow_pos_of_pos x0 _).ne',
    Real.log_mul (Real.rpow_pos_of_pos t0 _).ne' (by norm_num),Real.log_rpow x0,Real.log_rpow t0,
    Real.log_rpow x0] at upper
  change Real.log N ≤ γ*L X+s X*H+Real.log E+Real.log 4
  dsimp only [H,a,L]
  linarith only [upper]

/-- With rough part at most X^γ, each squarefree sign has leading log-height
(1+γ)log X/2 and second coefficient (1−γ)(1+log(2/(1−γ)))/2. -/
theorem second_coefficient_with_a_polynomial_rough_cutoff {γ : ℝ} (gp : 0<γ) (g1 : γ<1) (b : Bool) :
    Tendsto (fun X => second X ((1+γ)*L X/2) (Real.log (polynomialRoughSignCount γ b X))) atTop
      (𝓝 (((1-γ)/2)*(1+Real.log (2/(1-γ))))) := by
  let a := 1-γ
  let c := Real.log (2/a)
  let s := fun X => criticalWallTilt c (W X)
  have ap : 0<a := sub_pos.mpr g1
  have ll := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp logSquareCutoff_tendsto_atTop)
  have top : Tendsto s atTop (𝓝 (1/2)) := by
    simpa only [s,criticalWallTilt,add_zero] using (ll.const_div_atTop c).const_add (1/2:ℝ)
  let A := fun X => Real.log (signedSmoothSector (!b) (W X) (a*L X)).card
  let E := fun X => Real.log (deletionPrice (s X) (W X))
  let N := fun X => Real.log (polynomialRoughSignCount γ b X)
  have density := (second_coefficient_of_the_smooth_sign_populations ap).1 (!b)
  obtain ⟨first,square⟩ := normalized_log_losses
  have cost := square.add (first.const_mul (Real.log 4))
  rw [mul_zero,add_zero] at cost
  have lower := density.sub cost
  rw [sub_zero] at lower
  have eu := (critical_euler_partition_and_mean_limits logSquareCutoff_tendsto_atTop
    (tendsto_const_nhds (x := c))).2.1
  have h : 2*Real.exp (-c)=a := by rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) ap)]; field_simp
  rw [h] at eu
  have e : Tendsto (fun n => E n*M n/L n) atTop (𝓝 (a/2)) := by
    have f := change_wall_units (h := fun _ => 0) (f := E) (by simpa only [sub_zero] using eu)
    simpa only [second,sub_zero] using f
  have r := log_wall_ratio.inv₀ (by norm_num)
  simp only [inv_div] at r
  have upper := ((r.const_mul (c*a)).add e).add (first.const_mul (Real.log 4))
  rw [mul_zero,add_zero,show c*a*(2:ℝ)⁻¹+a/2=(a/2)*(1+Real.log (2/a)) by dsimp only [c]; ring] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  all_goals
    filter_upwards [signed_rough_sandwich gp g1 b top,ln_infty.eventually_gt_atTop 1,
      logSquareCutoff_tendsto_atTop.eventually_ge_atTop 2] with X bracket large yp
    have lp := zero_lt_one.trans large
    have llp : 0<l X := Real.log_pos (Nat.one_lt_cast.mpr yp)
    have mp : 0 ≤ M X := (Real.log_pos large).le
    have mono (k : ℝ) : Monotone (second X k) := fun u v uv =>
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (sub_le_sub_right uv _) mp) lp.le
    have eq : (1+γ)*L X/2=γ*L X+a*L X/2 := by dsimp [a]; ring
    change A X+γ*L X-M X-Real.log 4 ≤ N X ∧ N X ≤ γ*L X+s X*(a*L X)+E X+Real.log 4 at bracket
  · apply le_trans _ (mono _ bracket.1)
    change second X (a*L X/2) (A X)-(M X*M X/L X+Real.log 4*(M X/L X)) ≤ _
    rw [eq]; dsimp only [second]; exact le_of_eq (by ring)
  · apply (mono _ bracket.2).trans
    change _ ≤ c*a*(M X/l X)+E X*M X/L X+Real.log 4*(M X/L X)
    rw [eq]; dsimp only [second,s,criticalWallTilt]
    change _ ≤ c*a*(M X/l X)+E X*M X/L X+Real.log 4*(M X/L X)
    apply le_of_eq
    field_simp [llp.ne',lp.ne']; ring

end GaloisForLFunctions.RestrictedFactorizationCalculus
