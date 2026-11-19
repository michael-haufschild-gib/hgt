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

private theorem tilted_prime_atom {c C : ℝ} (bounded : |c| ≤ C) {p y : ℕ} (hp : p ∈ Nat.primesLE y) :
    |(p:ℝ)^(-criticalWallTilt c y)-Real.exp (-c)*rootMass p|*Real.log y ≤
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
  have mx : -c*t ≤ C := (mul_le_mul_of_nonneg_right (neg_le_of_abs_le bounded) t0).trans
    (mul_le_of_le_one_right c0 t1)
  have cost := exp_gap mx (neg_le_of_abs_le bounded)
  rw [show -c*t- -c=c*(1-t) by ring,abs_mul,abs_of_nonneg (sub_nonneg.mpr t1)] at cost
  have gap := cost.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right bounded (sub_nonneg.mpr t1)) (Real.exp_pos _).le)
  have tilt : (p:ℝ)^(-criticalWallTilt c y)=Real.exp (-c*t)*rootMass p := by
    rw [criticalWallTilt,show -(1/2+c/Real.log y)=(-c/Real.log y)+ -(1/2) by ring,
      Real.rpow_add pp,Real.rpow_neg pp.le,←Real.sqrt_eq_rpow,Real.rpow_def_of_pos pp]
    dsimp only [t,rootMass]
    rw [one_div]; congr 2; ring
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
theorem limits_of_the_two_tilted_prime_moments {b : ℕ → ℝ} {c : ℝ} (converges : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun y : ℕ => (∑ p ∈ Nat.primesLE y,(p:ℝ)^(-criticalWallTilt (b y) y))*Real.log y/Real.sqrt y) atTop (𝓝 (Real.exp (-c)*2)) ∧
    Tendsto (fun y : ℕ => (∑ p ∈ Nat.primesLE y,(p:ℝ)^(-criticalWallTilt (b y) y)*Real.log p)/Real.sqrt y) atTop (𝓝 (Real.exp (-c)*2)) := by
  let C := |c|+1
  have bounded := converges.abs.eventually_lt_const (show |c|<C by dsimp only [C]; linarith)
  let E := fun y : ℕ => Real.exp (-(b y))
  have e : Tendsto E atTop (𝓝 (Real.exp (-c))) := Real.continuous_exp.continuousAt.tendsto.comp converges.neg
  have zero := disappearing_prime_defect.const_mul (Real.exp C*C)
  rw [mul_zero] at zero
  have limits {A B : ℕ → ℝ} (main : Tendsto B atTop (𝓝 (Real.exp (-c)*2)))
      (err : ∀ᶠ y : ℕ in atTop,|A y-B y| ≤ Real.exp C*C*(primeDefect y/Real.sqrt y)) :
      Tendsto A atTop (𝓝 (Real.exp (-c)*2)) := by
    have van : Tendsto (fun y => A y-B y) atTop (𝓝 0) :=
      squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using err) zero
    have result := van.add main
    rw [zero_add] at result
    exact result.congr (fun y => sub_add_cancel ..)
  have bounds := (bounded.and (eventually_ge_atTop (2:ℕ))).mono (fun y h => tilted_prime_sum_errors h.1.le h.2)
  constructor
  · apply limits ((e.mul limit_reciprocal_roots_of_primes))
    filter_upwards [bounds] with y h
    have paid := div_le_div_of_nonneg_right h.1 (Real.sqrt_nonneg y)
    rw [←abs_of_nonneg (Real.sqrt_nonneg y),←abs_div] at paid
    apply le_trans (le_of_eq ?_) (paid.trans_eq ?_) <;> unfold Function.comp <;> dsimp only [E] <;> ring_nf
  · apply limits ((e.mul limit_log_weighted_roots_of_primes))
    filter_upwards [bounds] with y h
    have paid := div_le_div_of_nonneg_right h.2 (Real.sqrt_nonneg y)
    rw [←abs_of_nonneg (Real.sqrt_nonneg y),←abs_div] at paid
    apply le_trans (le_of_eq ?_) (paid.trans_eq ?_) <;> dsimp only [E] <;> ring_nf

#print axioms limits_of_the_two_tilted_prime_moments
end GaloisForLFunctions.RestrictedFactorizationCalculus
