import GaloisForLFunctions.RestrictedFactorizationCalculus.SplittingEverySmoothWindowAtItsLargestPrime
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothPopulationAtAnInteriorQuotientCut

/-!
# A positive smooth proportion on every polynomial range

Each largest-prime extraction advances r/(r+1) of a power of the smooth
cutoff. The reciprocal mass of the prime band pays at least the inverse
of 4r(k+1) at step k+1, giving a factorial price for the whole range.
-/
noncomputable section
open Finset Filter
open scoped Topology Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev smooth (y Z : ℕ) := RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z
private abbrev primes (z y : ℕ) := RHTower.Sieve.bigPrimeSet z y

private theorem small_count {y Z : ℕ} (hy : Z ≤ y) : (smooth y Z).card = Z := by
  have eq : smooth y Z = Icc 1 Z := by
    ext n
    rw [RHTower.mem_smoothUpTo_iff,mem_Icc]
    refine ⟨And.left,fun h => ⟨h,?_⟩⟩
    intro p hp
    exact (Nat.le_of_dvd h.1 (Nat.dvd_of_mem_primeFactors hp)).trans (h.2.trans hy)
  rw [eq,Nat.card_Icc,Nat.add_sub_cancel]

private abbrev wall (a : ℝ) (y : ℕ) := ⌊(y:ℝ)^a⌋₊

private theorem wall_grows {a : ℝ} (ha : 0 < a) :
    Tendsto (wall a) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

private theorem prime_mass {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ y : ℕ in atTop, Real.log (1/a)/2 ≤ ∑ p∈primes (wall a y) y,1/(p:ℝ) := by
  have hl : 0 < Real.log (1/a) := Real.log_pos ((one_lt_div ha).mpr ha1)
  filter_upwards [wall_grows ha (reciprocal_mass_above_the_prime_wall (half_pos hl)),
    (wall_grows ha).eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)] with y h hz hy
  let z := wall a y
  have y1 : (1:ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have yp : 0 < (y:ℝ) := zero_lt_one.trans_le y1
  have zp : (1:ℝ) < z := by exact_mod_cast (show 1 < z from hz)
  have z0 := zero_lt_one.trans zp
  have lo := Nat.floor_le (Real.rpow_nonneg yp.le a)
  have cap : z ≤ y := Nat.cast_le.mp (lo.trans (show (y:ℝ)^a ≤ (y:ℝ) by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le y1 ha1.le))
  have log_bound := Real.log_le_log z0 lo
  rw [Real.log_rpow yp] at log_bound
  have ratio : 1/a ≤ Real.log y/Real.log z :=
    (div_le_div_iff₀ ha (Real.log_pos zp)).mpr (by linarith only [log_bound])
  have obs := (abs_le.mp (h y cap)).1
  change -(Real.log (1/a)/2) ≤ (∑ p∈primes z y,1/(p:ℝ))-Real.log (Real.log y/Real.log z) at obs
  change Real.log (1/a)/2 ≤ ∑ p∈primes z y,1/(p:ℝ)
  exact (by linarith only [obs, Real.log_le_log (by positivity : 0 < 1/a) ratio])

private def stepExponent (r k : ℕ) : ℝ :=
  (((k+1)*r : ℕ) : ℝ)/((k*r+(r+1) : ℕ) : ℝ)

private theorem drop_step (r k y Z p : ℕ) (hp : 0 < p)
    (past : wall (stepExponent r k) y < p) (room : Z^(r+1) ≤ y^((k+1)*r)) :
    (Z/p)^(r+1) ≤ p^(k*r) := by
  have bound : (y:ℝ)^(stepExponent r k) < p :=
    (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mp past
  have degree : stepExponent r k*((k*r+(r+1):ℕ):ℝ)=(((k+1)*r:ℕ):ℝ) :=
    div_mul_cancel₀ _ (by positivity)
  have powBound := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg y) (stepExponent r k)) bound.le (k*r+(r+1))
  have iden : ((y:ℝ)^(stepExponent r k))^(k*r+(r+1))=(y:ℝ)^((k+1)*r) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg y),degree,Real.rpow_natCast]
  rw [iden] at powBound
  have cover : y^((k+1)*r) ≤ p^(k*r+(r+1)) := by exact_mod_cast powBound
  apply (mul_le_mul_iff_left₀ (pow_pos hp (r+1))).mp
  calc
    (Z/p)^(r+1)*p^(r+1) = ((Z/p)*p)^(r+1) := (mul_pow ..).symm
    _ ≤ Z^(r+1) := Nat.pow_le_pow_left (Nat.div_mul_le_self Z p) _
    _ ≤ p^(k*r+(r+1)) := room.trans cover
    _ = p^(k*r)*p^(r+1) := pow_add ..

private theorem floor_half_price {Z p : ℕ} (hp : 0 < p) (lo : p ≤ Z) :
    (Z:ℝ)/(2*p) ≤ (Z/p:ℕ) := by
  have fac := Nat.div_pos lo hp
  have rem := Nat.mod_lt Z hp
  have eq := Nat.mod_add_div Z p
  have mul : p ≤ p*(Z/p) := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left p fac
  have size : Z ≤ 2*p*(Z/p) := by
    rw [show 2*p*(Z/p)=p*(Z/p)+p*(Z/p) by ring]
    omega
  apply (div_le_iff₀ (by positivity : 0 < 2*(p:ℝ))).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm (Z/p)] using size : Z ≤ (Z/p)*(2*p))

private theorem partial_count (Z y z : ℕ) :
    (∑ p∈primes z y,((smooth p (Z/p)).card:ℝ)) ≤ (smooth y Z).card := by
  have sub : primes z y ⊆ Nat.primesLE y := fun p hp => Nat.mem_primesLE.mpr
    ⟨(mem_Icc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have b := sum_le_sum_of_subset_of_nonneg (f:=fun p : ℕ => ((smooth p (Z/p)).card:ℝ))
    sub (fun _ _ _ => Nat.cast_nonneg _)
  apply b.trans
  exact_mod_cast (show (∑ p∈Nat.primesLE y,(smooth p (Z/p)).card) ≤ (smooth y Z).card by
    rw [count_smooth_by_largest_prime y Z]; exact Nat.le_add_left ..)

private def populationCost (r k : ℕ) : ℝ := (8*(r:ℝ))^k*(k.factorial:ℝ)

private theorem cost_step (r k : ℕ) :
    populationCost r (k+1)=populationCost r k*(8*(((k+1)*r:ℕ):ℝ)) := by
  simp only [populationCost,pow_succ,Nat.factorial_succ,Nat.cast_mul];ring

private theorem reciprocal_gain {d : ℝ} (h : 1 ≤ d) :
    1/(4*d) ≤ Real.log ((d+1)/d)/2 := by
  have dp : 0 < d := zero_lt_one.trans_le h
  have xp : 0 < (d+1)/d := by positivity
  have bound := Real.one_sub_inv_le_log_of_pos xp
  have frac : 1/(d+1)=1-((d+1)/d)⁻¹ := by
    rw [inv_div];field_simp [dp.ne',(by positivity : 0 < d+1).ne'];ring
  have lower : 1/(2*d) ≤ 1/(d+1) :=
    div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith only [h])
  have half := div_le_div_of_nonneg_right (lower.trans (frac.trans_le bound)) (by norm_num : (0:ℝ) ≤ 2)
  calc
    1/(4*d) = (1/(2*d))/2 := by rw [div_div,show 2*d*2=4*d by ring]
    _ ≤ _ := half

/-- Explicit factorial price for smooth numbers. One may choose the
step parameter r separately for every target degree. Larger r advances
farther at each prime extraction, at the cost of a narrower prime window. -/
theorem smooth_population_at_factorial_price (r k : ℕ) (hr : 0 < r) :
    ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,Z^(r+1) ≤ y^(k*r) →
      (1/((8*(r:ℝ))^k*(k.factorial:ℝ)))*(Z:ℝ) ≤
        (RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card := by
  change ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,Z^(r+1) ≤ y^(k*r) →
    1/populationCost r k*(Z:ℝ) ≤ (smooth y Z).card
  induction k with
  | zero =>
    filter_upwards [eventually_ge_atTop (1:ℕ)] with y hy
    intro Z hz
    simp only [Nat.zero_mul,pow_zero] at hz
    have le := (Nat.le_self_pow (Nat.succ_ne_zero r) Z).trans hz
    simp [populationCost,small_count (le.trans hy)]
  | succ k ih =>
    obtain ⟨N,hN⟩ := eventually_atTop.mp ih
    let d : ℝ := (((k+1)*r:ℕ):ℝ)
    have d1 : 1 ≤ d := Nat.one_le_cast.mpr (Nat.mul_pos (Nat.succ_pos k) hr)
    have dp : 0 < d := zero_lt_one.trans_le d1
    let a := stepExponent r k
    have repr : a=d/(d+1) := by
      change d/((k*r+(r+1):ℕ):ℝ)=d/(d+1)
      apply congrArg (fun x : ℝ => d/x)
      dsimp only [d]; push_cast; ring
    have ap : 0 < a := repr.symm ▸ div_pos dp (by positivity)
    have a1 : a < 1 := by rw [repr];exact (div_lt_one (by positivity)).mpr (by linarith)
    have shift : 1/a=(d+1)/d := by rw [repr,one_div,inv_div]
    let c := 1/populationCost r k
    have costPos : 0 < populationCost r k := by
      unfold populationCost;have := Nat.factorial_pos k;positivity
    have cp : 0 < c := one_div_pos.mpr costPos
    have stepCost : 1/populationCost r (k+1)=c*(1/(4*d))/2 := by
      rw [cost_step];change 1/(populationCost r k*(8*d))=1/populationCost r k*(1/(4*d))/2
      field_simp [costPos.ne',dp.ne'] <;> ring
    filter_upwards [prime_mass ap a1,(wall_grows ap).eventually_ge_atTop N] with y mass cutoff
    intro Z room
    by_cases small : Z ≤ y
    · rw [small_count small]
      have r1 : (1:ℝ) ≤ r := Nat.one_le_cast.mpr hr
      have q1 : (1:ℝ) ≤ (8*(r:ℝ))^(k+1) := one_le_pow₀ (by linarith only [r1])
      have fac : (1:ℝ) ≤ ((k+1).factorial:ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos (k+1))
      have denom : 1 ≤ populationCost r (k+1) := one_le_mul_of_one_le_of_one_le q1 fac
      simpa using mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le zero_lt_one denom) (Nat.cast_nonneg (α:=ℝ) Z)
    have step (p : ℕ) (member : p∈primes (wall a y) y) :
        c*(Z:ℝ)/2*(1/(p:ℝ)) ≤ (smooth p (Z/p)).card := by
      have prime := RHTower.Sieve.prime_of_mem_bigPrimeSet member
      have above := RHTower.Sieve.lt_of_mem_bigPrimeSet member
      have top := (mem_Icc.mp (mem_filter.mp member).1).2
      have floor := floor_half_price prime.pos (top.trans (le_of_not_ge small))
      have ind := hN p (cutoff.trans above.le) (Z/p) (drop_step r k y Z p prime.pos above room)
      calc
        _ = c*((Z:ℝ)/(2*p)) := by
          field_simp [(Nat.cast_pos.mpr prime.pos : 0 < (p:ℝ)).ne']
        _ ≤ _ := (mul_le_mul_of_nonneg_left floor cp.le).trans ind
    have mass' := (reciprocal_gain d1).trans (shift ▸ mass)
    calc
      1/populationCost r (k+1)*(Z:ℝ) = c*(Z:ℝ)/2*(1/(4*d)) := by rw [stepCost];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left mass' (by positivity : 0 ≤ c*(Z:ℝ)/2)
      _ ≤ _ := by rw [mul_sum];exact sum_le_sum step
      _ ≤ _ := partial_count ..

end GaloisForLFunctions.RestrictedFactorizationCalculus
