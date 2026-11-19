import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalEulerPriceOfTheLogSquareCutoff

/-!
# The prime moments of the moving critical Euler tilt

Under reciprocal square-root weights the normalized logarithmic
coordinate of a prime concentrates at the top of the sieve. The defect
is exactly the difference of the first two prime number theorem limits.
It controls the moving exponential factor at every bounded tilt.
-/
noncomputable section
open Finset Filter RHTower RHTower.Sieve
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The power at a fixed logarithmic distance from one half. -/
def criticalWallTilt (c : ℝ) (y : ℕ) := 1/2+c/Real.log y

private abbrev rootMass (p : ℕ) := 1/Real.sqrt p
private def primeDefect (y : ℕ) := ∑ p ∈ Nat.primesLE y,(Real.log y-Real.log p)/Real.sqrt p

private theorem disappearing_prime_defect :
    Tendsto (fun y : ℕ => primeDefect y/Real.sqrt y) atTop (𝓝 0) := by
  have h := limit_reciprocal_roots_of_primes.sub limit_log_weighted_roots_of_primes
  rw [sub_self] at h
  apply h.congr
  intro y
  change (∑ p ∈ Nat.primesLE y,rootMass p)*Real.log y/Real.sqrt y-
    (∑ p ∈ Nat.primesLE y,Real.log p/Real.sqrt p)/Real.sqrt y=_
  rw [←sub_div,primeDefect,sum_mul,←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro p _; dsimp only [rootMass]; ring

private theorem exp_gap {s t C : ℝ} (sc : s ≤ C) (tc : t ≤ C) :
    |Real.exp s-Real.exp t| ≤ Real.exp C*|s-t| := by
  have forward {x y : ℝ} (xy : x ≤ y) (yc : y ≤ C) :
      Real.exp y-Real.exp x ≤ Real.exp C*(y-x) := by
    have tangent := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
    rw [←Real.exp_add,sub_add_cancel] at tangent
    exact (show Real.exp y-Real.exp x ≤ Real.exp y*(y-x) by linarith only [tangent]).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr yc) (sub_nonneg.mpr xy))
  rcases le_total s t with st | ts
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr st)),abs_of_nonpos (sub_nonpos.mpr st),neg_sub,neg_sub]
    exact forward st tc
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr ts)),abs_of_nonneg (sub_nonneg.mpr ts)]
    exact forward ts sc

private theorem tilt_at_a_prime (c : ℝ) {p y : ℕ} (pp : 0<(p:ℝ)) :
    (p:ℝ)^(-criticalWallTilt c y) =
      Real.exp (-c*(Real.log p/Real.log y))*rootMass p := by
  rw [criticalWallTilt,show -(1/2+c/Real.log y)=(-c/Real.log y)+ -(1/2) by ring,
    Real.rpow_add pp,Real.rpow_neg pp.le,←Real.sqrt_eq_rpow,Real.rpow_def_of_pos pp]
  dsimp only [rootMass]
  rw [one_div]; congr 2; ring

private theorem tilted_prime_atom {c C : ℝ} (bounded : |c| ≤ C) {p y : ℕ} (hp : p ∈ Nat.primesLE y) :
    |(p:ℝ)^(-criticalWallTilt c y)-Real.exp (-c)*rootMass p| *Real.log y ≤
      Real.exp C*C*((Real.log y-Real.log p)/Real.sqrt p) := by
  obtain ⟨py,prime⟩ := Nat.mem_primesLE.mp hp
  have pp : 0<(p:ℝ) := Nat.cast_pos.mpr prime.pos
  have lp := Real.log_pos (Nat.one_lt_cast.mpr prime.one_lt)
  have order := Real.log_le_log pp (Nat.cast_le.mpr py)
  have ly := lp.trans_le order
  let t := Real.log p/Real.log y
  have t0 : 0 ≤ t := div_nonneg lp.le ly.le
  have t1 : t ≤ 1 := (div_le_one ly).mpr order
  have c0 := (abs_nonneg c).trans bounded
  have neg : -c ≤ C := (neg_le_abs _).trans bounded
  have mx : -c*t ≤ C := (mul_le_mul_of_nonneg_right neg t0).trans
    (mul_le_of_le_one_right c0 t1)
  have cost := exp_gap mx neg
  rw [show -c*t- -c=c*(1-t) by ring,abs_mul,abs_of_nonneg (sub_nonneg.mpr t1)] at cost
  have gap := cost.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right bounded (sub_nonneg.mpr t1)) (Real.exp_pos _).le)
  have tilt := tilt_at_a_prime c (y := y) pp
  rw [tilt,←sub_mul,abs_mul,abs_of_nonneg (by dsimp [rootMass]; positivity : 0 ≤ rootMass p)]
  have scaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right gap
    (by dsimp [rootMass]; positivity : 0 ≤ rootMass p)) ly.le
  have eval : t*Real.log y=Real.log p := div_mul_cancel₀ _ ly.ne'
  apply scaled.trans_eq
  dsimp only [rootMass]
  calc _ = Real.exp C*C*((Real.log y-t*Real.log y)/Real.sqrt p) := by ring
       _ = _ := by rw [eval]

private theorem tilted_prime_sum_errors {C c : ℝ} (bounded : |c| ≤ C) {y : ℕ} (yp : 2 ≤ y) :
    let a := fun p : ℕ => (p:ℝ)^(-criticalWallTilt c y)
    |(∑ p ∈ Nat.primesLE y,a p)*Real.log y-Real.exp (-c)*((∑ p ∈ Nat.primesLE y,rootMass p)*Real.log y)| ≤
      Real.exp C*C*primeDefect y ∧
    |(∑ p ∈ Nat.primesLE y,a p*Real.log p)-Real.exp (-c)*(∑ p ∈ Nat.primesLE y,Real.log p/Real.sqrt p)| ≤
      Real.exp C*C*primeDefect y := by
  let P := Nat.primesLE y
  let a := fun p : ℕ => (p:ℝ)^(-criticalWallTilt c y)
  have ly := Real.log_nonneg (Nat.one_le_cast.mpr (by omega : 1 ≤ y))
  have estimate (f : ℕ → ℝ) (nn : ∀ p ∈ P,0 ≤ f p) (le : ∀ p ∈ P,f p ≤ Real.log y) :
      |(∑ p ∈ P,(a p-Real.exp (-c)*rootMass p)*f p)| ≤ Real.exp C*C*primeDefect y := by
    apply (abs_sum_le_sum_abs ..).trans
    rw [primeDefect,mul_sum]
    apply sum_le_sum
    intro p hp
    rw [abs_mul,abs_of_nonneg (nn p hp)]
    exact (mul_le_mul_of_nonneg_left (le p hp) (abs_nonneg _)).trans (tilted_prime_atom bounded hp)
  have one := estimate (fun _ => Real.log y) (fun _ _ => ly) (fun _ _ => le_rfl)
  have two := estimate (fun p => Real.log p) (fun p _ => Real.log_natCast_nonneg p)
    (fun p hp => Real.log_le_log (Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos) (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1))
  have identity (p : ℕ) : (a p-Real.exp (-c)*rootMass p)*Real.log p =
      a p*Real.log p-Real.exp (-c)*(Real.log p/Real.sqrt p) := by dsimp only [rootMass]; ring
  rw [sum_congr rfl (fun p _ => identity p),sum_sub_distrib,←mul_sum] at two
  rw [←sum_mul,sum_sub_distrib,←mul_sum,sub_mul,mul_assoc] at one
  exact ⟨one,two⟩

/-- Both normalized prime moments acquire the same multiplier at a
moving tilt converging in the logarithmic coordinate. -/
theorem limits_of_the_two_tilted_prime_moments {Y : ℕ → ℕ} (wall : Tendsto Y atTop atTop)
    {b : ℕ → ℝ} {c : ℝ} (converges : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE (Y n),(p:ℝ)^(-criticalWallTilt (b n) (Y n)))*Real.log (Y n)/Real.sqrt (Y n)) atTop (𝓝 (Real.exp (-c)*2)) ∧
    Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE (Y n),(p:ℝ)^(-criticalWallTilt (b n) (Y n))*Real.log p)/Real.sqrt (Y n)) atTop (𝓝 (Real.exp (-c)*2)) := by
  let C := |c|+1
  have bounded := converges.abs.eventually_lt_const (show |c|<C by dsimp only [C]; linarith)
  let E := fun y : ℕ => Real.exp (-(b y))
  have e : Tendsto E atTop (𝓝 (Real.exp (-c))) := Real.continuous_exp.continuousAt.tendsto.comp converges.neg
  have zero := (disappearing_prime_defect.comp wall).const_mul (Real.exp C*C)
  rw [mul_zero] at zero
  have limits {A B : ℕ → ℝ} (main : Tendsto B atTop (𝓝 (Real.exp (-c)*2)))
      (err : ∀ᶠ y : ℕ in atTop,|A y-B y| ≤ Real.exp C*C*(primeDefect (Y y)/Real.sqrt (Y y))) :
      Tendsto A atTop (𝓝 (Real.exp (-c)*2)) := by
    have van : Tendsto (fun y => A y-B y) atTop (𝓝 0) :=
      squeeze_zero_norm' (by simpa only [Real.norm_eq_abs,Function.comp_apply] using err) zero
    have result := van.add main
    rw [zero_add] at result
    exact result.congr (fun y => sub_add_cancel ..)
  have normalize {x z k r P : ℝ} (positive : 0 ≤ r) (paid : |x-k*z| ≤ P) :
      |x/r-k*(z/r)| ≤ P/r := by
    rw [show x/r-k*(z/r)=(x-k*z)/r by ring,abs_div,abs_of_nonneg positive]
    exact div_le_div_of_nonneg_right paid positive
  have bounds := (bounded.and (wall.eventually_ge_atTop 2)).mono (fun y h => tilted_prime_sum_errors h.1.le h.2)
  constructor
  · apply limits ((e.mul (limit_reciprocal_roots_of_primes.comp wall)))
    filter_upwards [bounds] with y h
    exact (normalize (Real.sqrt_nonneg _) h.1).trans_eq (mul_div_assoc ..)
  · apply limits ((e.mul (limit_log_weighted_roots_of_primes.comp wall)))
    filter_upwards [bounds] with y h
    exact (normalize (Real.sqrt_nonneg _) h.2).trans_eq (mul_div_assoc ..)

/-- Logarithm of the squarefree Euler product and the expected log-product
under its independent prime occupations. -/
def squarefreeEulerLog (s : ℝ) (y : ℕ) :=
  ∑ p ∈ Nat.primesLE y,Real.log (1+(p:ℝ)^(-s))

def squarefreeEulerMean (s : ℝ) (y : ℕ) :=
  ∑ p ∈ Nat.primesLE y,Real.log p*((p:ℝ)^(-s)/(1+(p:ℝ)^(-s)))

private theorem local_euler_errors {u d : ℝ} (u0 : 0 ≤ u) (d0 : 0<d) (room : d ≤ 1-u) :
    |Real.log (1+u)-u| ≤ u^2 ∧
    |u/(1+u)-u| ≤ u^2 ∧
    |Real.log ((1-u)⁻¹)-u| ≤ u^2/d := by
  have add : 0<1+u := by linarith only [u0]
  have sub := d0.trans_le room
  have below := Real.log_le_sub_one_of_pos add
  have above := Real.log_le_sub_one_of_pos (inv_pos.mpr add)
  rw [Real.log_inv] at above
  have frac : u-u/(1+u)=u^2/(1+u) := by field_simp; ring
  have lower : u/(1+u) ≤ Real.log (1+u) := by
    have eq : 1-(1+u)⁻¹=u/(1+u) := by field_simp; ring
    linarith only [above,eq]
  have loss := (le_of_eq frac).trans (div_le_self (sq_nonneg u) (by linarith only [u0]))
  have posloss : u/(1+u) ≤ u := div_le_self u0 (by linarith only [u0])
  have ga := Real.log_le_sub_one_of_pos sub
  have gb := Real.log_le_sub_one_of_pos (inv_pos.mpr sub)
  have ge : (1-u)⁻¹-1-u=u^2/(1-u) := by field_simp; ring
  refine ⟨?_,?_,?_⟩
  · rw [abs_of_nonpos (by linarith only [below])]
    linarith only [loss,lower]
  · rw [abs_of_nonpos (sub_nonpos.mpr posloss)]
    linarith only [loss]
  · rw [Real.log_inv,abs_of_nonneg (by linarith only [ga])]
    rw [Real.log_inv] at gb
    linarith only [gb,ge,div_le_div_of_nonneg_left (sq_nonneg u) d0 room]

private theorem error_of_the_tilted_euler_factors {C : ℝ} (C0 : 0 ≤ C) :
    ∃ K : ℝ,0<K ∧ ∀ {y : ℕ} {c : ℝ},|c| ≤ C → 1/4 ≤ criticalWallTilt c y →
    let s := criticalWallTilt c y
    let A := ∑ p ∈ Nat.primesLE y,(p:ℝ)^(-s)
    let B := ∑ p ∈ Nat.primesLE y,(p:ℝ)^(-s)*Real.log p
    |squarefreeEulerLog s y-A| ≤ K*(1+Real.log y) ∧
    |Real.log (deletionPrice s y)-A| ≤ K*(1+Real.log y) ∧
    |squarefreeEulerMean s y-B| ≤ K*(1+Real.log y)*Real.log y := by
  let d := 1-((2:ℝ)^(1/4:ℝ))⁻¹
  have two := Real.one_lt_rpow (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<1/4)
  have d0 : 0<d := sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans two)).mpr two)
  have d1 : d ≤ 1 := sub_le_self _ (inv_nonneg.mpr (zero_lt_one.trans two).le)
  let K := (Real.exp C)^2/d
  have positive : 0<K := div_pos (sq_pos_of_pos (Real.exp_pos C)) d0
  refine ⟨K,positive,?_⟩
  intro y c bc quarter
  let s := criticalWallTilt c y
  let u := fun p : ℕ => (p:ℝ)^(-s)
  let P := Nat.primesLE y
  let h := fun p : ℕ => K*(1/(p:ℝ))
  have atoms (p : ℕ) (hp : p∈P) :
      |Real.log (1+u p)-u p| ≤ h p ∧ |Real.log ((1-u p)⁻¹)-u p| ≤ h p ∧
      |u p/(1+u p)-u p| ≤ h p ∧ 0<1-u p := by
    obtain ⟨py,prime⟩ := Nat.mem_primesLE.mp hp
    have pp : 0<(p:ℝ) := Nat.cast_pos.mpr prime.pos
    have p2 : (2:ℝ) ≤ p := by exact_mod_cast prime.two_le
    have p1 : (1:ℝ) ≤ p := le_trans (by norm_num) p2
    have lp := Real.log_pos (Nat.one_lt_cast.mpr prime.one_lt)
    have ly := Real.log_le_log pp (Nat.cast_le.mpr py)
    let t := Real.log p/Real.log y
    have t0 : 0 ≤ t := div_nonneg lp.le (lp.trans_le ly).le
    have t1 : t ≤ 1 := (div_le_one (lp.trans_le ly)).mpr ly
    have arg := (mul_le_mul_of_nonneg_right ((neg_le_abs c).trans bc) t0).trans
      (mul_le_of_le_one_right C0 t1)
    have u0 := (Real.rpow_pos_of_pos pp (-s)).le
    have lower := (Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 2) p2 (by norm_num : (0:ℝ) ≤ 1/4)).trans
      (Real.rpow_le_rpow_of_exponent_le p1 quarter)
    have bound : u p ≤ ((2:ℝ)^(1/4:ℝ))⁻¹ := by
      dsimp only [u]; rw [Real.rpow_neg pp.le]
      exact inv_anti₀ (zero_lt_one.trans two) lower
    have room : d ≤ 1-u p := sub_le_sub_left bound 1
    have small : u p ≤ Real.exp C*rootMass p := by
      dsimp only [u,s]; rw [tilt_at_a_prime c pp]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr arg) (by dsimp [rootMass]; positivity)
    have sq := pow_le_pow_left₀ u0 small 2
    rw [mul_pow,show (rootMass p)^2=1/(p:ℝ) by
      dsimp only [rootMass]; rw [div_pow,one_pow,Real.sq_sqrt pp.le]] at sq
    have scaled : (u p)^2/d ≤ h p := (div_le_div_of_nonneg_right sq d0.le).trans_eq (by dsimp only [h,K]; ring)
    have unscaled := (le_div_self (sq_nonneg (u p)) d0 d1).trans scaled
    obtain ⟨a,b,g⟩ := local_euler_errors u0 d0 room
    exact ⟨a.trans unscaled,g.trans scaled,b.trans unscaled,d0.trans_le room⟩
  have total : (∑ p ∈ P,h p) ≤ K*(1+Real.log y) := by
    simp only [h,←mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_finset_bounded_le_one_add_log P y
      (fun _ h => (Nat.prime_of_mem_primesLE h).pos) (fun _ h => (Nat.mem_primesLE.mp h).1)) positive.le
  have logprice : Real.log (deletionPrice s y)=∑ p ∈ P,Real.log ((1-u p)⁻¹) := by
    have eq (p : ℕ) : (1/(p:ℝ))^s=u p := by
      dsimp only [u]; rw [one_div,Real.inv_rpow (Nat.cast_nonneg _),Real.rpow_neg (Nat.cast_nonneg _)]
    simp only [deletionPrice,eq]
    exact Real.log_prod (fun p hp => (inv_pos.mpr (atoms p hp).2.2.2).ne')
  have priced (f : ℕ → ℝ) (cost : ∀ p ∈ P,|f p-u p| ≤ h p) :
      |(∑ p ∈ P,f p)-(∑ p ∈ P,u p)| ≤ K*(1+Real.log y) := by
    rw [←sum_sub_distrib]
    exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum cost).trans total)
  refine ⟨priced _ (fun p hp => (atoms p hp).1),?_,?_⟩
  · change |Real.log (deletionPrice s y)-_| ≤ _
    rw [logprice]; exact priced _ (fun p hp => (atoms p hp).2.1)
  · change |(∑ p ∈ P,Real.log p*(u p/(1+u p)))-(∑ p ∈ P,u p*Real.log p)| ≤ _
    rw [←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    apply le_trans _ (mul_le_mul_of_nonneg_right total (Real.log_natCast_nonneg y))
    rw [sum_mul]
    apply sum_le_sum
    intro p hp
    rw [mul_comm (Real.log _),←sub_mul,abs_mul,abs_of_nonneg (Real.log_natCast_nonneg _)]
    exact mul_le_mul (atoms p hp).2.2.1
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos) (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1))
      (Real.log_natCast_nonneg _) (by dsimp [h]; positivity)

private theorem normalized_quadratic_error (K : ℝ) :
    Tendsto (fun y : ℕ => K*(1+Real.log y)*Real.log y/Real.sqrt y) atTop (𝓝 0) := by
  let q := (1/4:ℝ)
  have qp : 0<q := by norm_num [q]
  have vanish : Tendsto (fun y : ℕ => Real.log y/(y:ℝ)^q) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop qp).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have inv : Tendsto (fun y : ℕ => ((y:ℝ)^q)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop qp).comp tendsto_natCast_atTop_atTop)
  have h := ((inv.add vanish).mul vanish).const_mul K
  simp only [add_zero,mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with y yp
  have pos : (0:ℝ)<y := Nat.cast_pos.mpr yp
  have eq : Real.sqrt (y:ℝ)=(y:ℝ)^q*(y:ℝ)^q := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add pos]; congr 1; norm_num [q]
  change K*((((y:ℝ)^q)⁻¹+Real.log y/(y:ℝ)^q)*(Real.log y/(y:ℝ)^q))=_
  rw [eq]; ring

/-- The geometric and squarefree log-partitions have the same critical
asymptotic. The first moment is the mean log-product of the finite tilt. -/
theorem critical_euler_partition_and_mean_limits {Y : ℕ → ℕ} (wall : Tendsto Y atTop atTop)
    {b : ℕ → ℝ} {c : ℝ} (converges : Tendsto b atTop (𝓝 c)) :
    let s := fun n => criticalWallTilt (b n) (Y n)
    let L := 2*Real.exp (-c)
    Tendsto (fun n => squarefreeEulerLog (s n) (Y n)*Real.log (Y n)/Real.sqrt (Y n)) atTop (𝓝 L) ∧
    Tendsto (fun n => Real.log (deletionPrice (s n) (Y n))*Real.log (Y n)/Real.sqrt (Y n)) atTop (𝓝 L) ∧
    Tendsto (fun n => squarefreeEulerMean (s n) (Y n)/Real.sqrt (Y n)) atTop (𝓝 L) := by
  let s := fun n => criticalWallTilt (b n) (Y n)
  let C := |c|+1
  have C0 : 0 ≤ C := by dsimp only [C]; positivity
  have bounded := converges.abs.eventually_lt_const (show |c|<C by dsimp only [C]; linarith)
  have ly := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp wall)
  have st : Tendsto s atTop (𝓝 (1/2)) := by
    simpa only [s,criticalWallTilt,add_zero,Function.comp_apply] using
      (converges.div_atTop ly).const_add (1/2:ℝ)
  obtain ⟨K,_,cost⟩ := error_of_the_tilted_euler_factors C0
  have prices := (bounded.and (st.eventually_const_lt (by norm_num : (1/4:ℝ)<1/2))).mono
    (fun n h => cost h.1.le h.2.le)
  obtain ⟨mass,logs⟩ := limits_of_the_two_tilted_prime_moments wall converges
  rw [mul_comm (Real.exp (-c)) 2] at mass logs
  have van := (normalized_quadratic_error K).comp wall
  have transfer {F G : ℕ → ℝ} (main : Tendsto G atTop (𝓝 (2*Real.exp (-c))))
      (small : ∀ᶠ n in atTop, |F n-G n| ≤ K*(1+Real.log (Y n))*Real.log (Y n)/Real.sqrt (Y n)) :
      Tendsto F atTop (𝓝 (2*Real.exp (-c))) := by
    have gap : Tendsto (fun n => F n-G n) atTop (𝓝 0) :=
      squeeze_zero_norm' (by simpa only [Real.norm_eq_abs,Function.comp_apply] using small) van
    have h := gap.add main
    rw [zero_add] at h
    exact h.congr (fun _ => sub_add_cancel ..)
  have scale {a b r t k : ℝ} (r0 : 0 ≤ r) (t0 : 0 ≤ t) (h : |a-b| ≤ k) :
      |a*t/r-b*t/r| ≤ k*t/r := by
    rw [←sub_div,←sub_mul,abs_div,abs_mul,abs_of_nonneg t0,abs_of_nonneg r0]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h t0) r0
  refine ⟨transfer mass ?_,transfer mass ?_,transfer logs ?_⟩
  · filter_upwards [prices] with n h
    exact scale (Real.sqrt_nonneg _) (Real.log_natCast_nonneg _) h.1
  · filter_upwards [prices] with n h
    exact scale (Real.sqrt_nonneg _) (Real.log_natCast_nonneg _) h.2.1
  · filter_upwards [prices] with n h
    rw [←sub_div,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right h.2.2 (Real.sqrt_nonneg _)

private theorem mean_is_continuous (y : ℕ) :
    Continuous (fun c => squarefreeEulerMean (criticalWallTilt c y) y) := by
  unfold squarefreeEulerMean
  apply continuous_finsetSum
  intro p hp
  have pp : 0<(p:ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos
  have wt : Continuous (fun c => (p:ℝ)^(-criticalWallTilt c y)) := by
    simp only [Real.rpow_def_of_pos pp,criticalWallTilt]
    fun_prop
  exact continuous_const.mul (wt.div (continuous_const.add wt) (by
    intro c
    exact (add_pos zero_lt_one (Real.rpow_pos_of_pos pp _)).ne'))

private theorem mean_is_decreasing (y : ℕ) :
    Antitone (fun c => squarefreeEulerMean (criticalWallTilt c y) y) := by
  intro c d cd
  have st : criticalWallTilt c y ≤ criticalWallTilt d y :=
    add_le_add le_rfl (div_le_div_of_nonneg_right cd (Real.log_natCast_nonneg y))
  apply sum_le_sum
  intro p hp
  have pp : 0<(p:ℝ) := Nat.cast_pos.mpr (Nat.prime_of_mem_primesLE hp).pos
  let u := (p:ℝ)^(-criticalWallTilt d y)
  let v := (p:ℝ)^(-criticalWallTilt c y)
  have u0 : 0<u := Real.rpow_pos_of_pos pp _
  have v0 : 0<v := Real.rpow_pos_of_pos pp _
  have uv : u ≤ v := Real.rpow_le_rpow_of_exponent_le
    (Nat.one_le_cast.mpr (Nat.prime_of_mem_primesLE hp).pos) (neg_le_neg st)
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  exact (div_le_div_iff₀ (add_pos zero_lt_one u0) (add_pos zero_lt_one v0)).mpr (by linarith only [uv])

/-- Any target asymptotic to a positive multiple of the square root of
the prime wall has an exact saddle at every sufficiently large index.
Its logarithmic tilt converges to log(2/a). -/
theorem calibrate_the_finite_prime_mean {Y : ℕ → ℕ} (wall : Tendsto Y atTop atTop)
    {H : ℕ → ℝ} {a : ℝ} (ap : 0<a)
    (size : Tendsto (fun n => H n/Real.sqrt (Y n)) atTop (𝓝 a)) :
    ∃ b : ℕ → ℝ,Tendsto b atTop (𝓝 (Real.log (2/a))) ∧
      ∀ᶠ n in atTop,squarefreeEulerMean (criticalWallTilt (b n) (Y n)) (Y n)=H n := by
  let c := Real.log (2/a)
  let M := fun n u => squarefreeEulerMean (criticalWallTilt u (Y n)) (Y n)
  have mass (u : ℝ) : Tendsto (fun n => M n u/Real.sqrt (Y n)) atTop (𝓝 (2*Real.exp (-u))) :=
    (critical_euler_partition_and_mean_limits wall (tendsto_const_nhds (x := u))).2.2
  have centre : 2*Real.exp (-c)=a := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) ap)]; field_simp
  have order {u v : ℝ} (hv : u<v) : 2*Real.exp (-v)<2*Real.exp (-u) :=
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (neg_lt_neg hv)) (by norm_num)
  have bracket {u v : ℝ} (l : u<c) (r : c<v) :
      ∀ᶠ n in atTop,M n v<H n ∧ H n<M n u := by
    have hi := (mass v).eventually_lt size ((order r).trans_eq centre)
    have lo := size.eventually_lt (mass u) (centre.symm.trans_lt (order l))
    filter_upwards [hi,lo,wall.eventually_ge_atTop 1] with n x z yn
    have pos := Real.sqrt_pos.mpr (Nat.cast_pos.mpr yn : (0:ℝ)<Y n)
    exact ⟨(div_lt_div_iff_of_pos_right pos).mp x,(div_lt_div_iff_of_pos_right pos).mp z⟩
  have exist : ∀ᶠ n in atTop,∃ t,M n t=H n := by
    filter_upwards [bracket (by linarith : c-1<c) (by linarith : c<c+1)] with n h
    obtain ⟨t,_,eq⟩ := intermediate_value_Icc' (show c-1 ≤ c+1 by linarith)
      (mean_is_continuous (Y n)).continuousOn ⟨h.1.le,h.2.le⟩
    exact ⟨t,eq⟩
  let b := fun n => if h : ∃ t,M n t=H n then h.choose else c
  have hit : ∀ᶠ n in atTop,M n (b n)=H n := exist.mono (fun n h => by
    dsimp only [b]; rw [dif_pos h]; exact h.choose_spec)
  refine ⟨b,tendsto_order.mpr ⟨?_,?_⟩,hit⟩
  · intro u low
    filter_upwards [bracket low (by linarith : c<c+1),hit] with n h eq
    exact lt_of_not_ge (fun le => h.2.not_ge ((mean_is_decreasing (Y n) le).trans_eq eq))
  · intro v high
    filter_upwards [bracket (by linarith : c-1<c) high,hit] with n h eq
    exact lt_of_not_ge (fun le => h.1.not_ge (eq.symm.le.trans (mean_is_decreasing (Y n) le)))

#print axioms calibrate_the_finite_prime_mean
#print axioms critical_euler_partition_and_mean_limits
#print axioms limits_of_the_two_tilted_prime_moments
end GaloisForLFunctions.RestrictedFactorizationCalculus
