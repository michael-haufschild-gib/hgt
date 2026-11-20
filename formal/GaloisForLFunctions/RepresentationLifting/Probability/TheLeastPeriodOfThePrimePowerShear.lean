import GaloisForLFunctions.RepresentationLifting.Probability.PrimePowerRootCountsOfTheShear
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.GCD

/-!
# The least additive period of the quadratic root count

The number of solutions of r(r+g)=0 modulo a prime power depends on
a truncated gcd of g. The outermost jump vanishes precisely at the
even powers of two. At modulus 2^(2k+2) the whole function is twice
gcd(g,2^k), so exactly one further binary digit disappears.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Function
noncomputable section
variable (p : ℕ) [Fact p.Prime]
private abbrev shear (h : ℕ) := _root_.RHTower.quadraticCongruenceRootCountTotal (p^h)

private theorem int_power_dvd_iff_valuation {g : ℤ} (hg : g≠0) (k : ℕ) :
    (p:ℤ)^k∣g ↔ k≤(g:ℤ_[p]).valuation := by
  have h := OperatorKernels.padicProjection_eq_zero_iff_norm_le p (g:ℤ_[p]) k
  have hp : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [map_intCast,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_pow,
    PadicInt.norm_eq_zpow_neg_valuation (Int.cast_ne_zero.mpr hg),zpow_le_zpow_iff_right₀ hp] at h
  exact h.trans (by omega)

private theorem gcd_of_bounded_valuation {g : ℤ} (hg : g≠0) {k : ℕ} (hk : (g:ℤ_[p]).valuation≤k) :
    g.gcd ((p:ℤ)^k)=p^(g:ℤ_[p]).valuation := by
  let d := g.gcd ((p:ℤ)^k)
  have hgd : d∣p^k := by exact_mod_cast Int.gcd_dvd_right g ((p:ℤ)^k)
  obtain ⟨e,_,he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hgd
  apply Nat.dvd_antisymm
  · have hd : (p:ℤ)^e∣g := by
      have hh : (d:ℤ)∣g := Int.gcd_dvd_left _ _
      rw [he,Nat.cast_pow] at hh
      exact hh
    rw [show g.gcd ((p:ℤ)^k)=p^e from he]
    exact pow_dvd_pow p ((int_power_dvd_iff_valuation p hg e).mp hd)
  · have hd := Int.dvd_coe_gcd ((int_power_dvd_iff_valuation p hg _).mpr le_rfl) (pow_dvd_pow (p:ℤ) hk)
    exact_mod_cast hd

/-- Arithmetic gcd formula one digit below the terminal root ball.
The only correction is on the zero class at the next precision. -/
theorem arithmetic_shear_gcd_formula (h k : ℕ) (hk : (h+1)/2=k+1) (g : ℤ) :
    _root_.RHTower.quadraticCongruenceRootCountTotal (p^h) g = if (p:ℤ)^(k+1)∣g then p^(h/2) else 2*g.gcd ((p:ℤ)^k) := by
  rw [arithmetic_shear_root_count,hk]
  by_cases hd : (p:ℤ)^(k+1)∣g
  · simp only [hd,if_true]
  · have hg : g≠0 := fun h => hd (h ▸ dvd_zero _)
    have hv : (g:ℤ_[p]).valuation≤k := by
      have := mt (int_power_dvd_iff_valuation p hg (k+1)).mpr hd
      omega
    rw [if_neg hd,if_neg hd,gcd_of_bounded_valuation p hg hv]

private theorem power_not_dvd_prev (k : ℕ) : ¬(p:ℤ)^(k+1)∣(p:ℤ)^k := by
  intro h
  have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he := (int_power_dvd_iff_valuation p (pow_ne_zero k hp) (k+1)).mp h
  simp only [Int.cast_pow,Int.cast_natCast,PadicInt.valuation_pow,PadicInt.valuation_p,mul_one] at he
  omega

private theorem at_zero (h : ℕ) : shear p h 0=p^(h/2) := by
  rw [shear,arithmetic_shear_root_count,if_pos (dvd_zero _)]

private theorem at_last_power (h k : ℕ) (hk : (h+1)/2=k+1) :
    shear p h ((p:ℤ)^k)=2*p^k := by
  rw [shear,arithmetic_shear_root_count,hk,if_neg (power_not_dvd_prev p k)]
  simp only [Int.cast_pow,Int.cast_natCast,PadicInt.valuation_pow,PadicInt.valuation_p,mul_one]

private theorem integer_period_of_dvd {α : Type*} {f : ℤ → α} {l t : ℤ}
    (hf : Periodic f l) (hd : l∣t) : Periodic f t := by
  obtain ⟨v,rfl⟩ := hd
  simpa only [Int.cast_id,mul_comm v l] using hf.int_mul v

private theorem prime_power_period_iff {α : Type*} (f : ℤ → α) (k : ℕ)
    (full : Periodic f ((p:ℤ)^(k+1))) (jump : f ((p:ℤ)^k)≠f 0) (t : ℤ) :
    Periodic f t ↔ (p:ℤ)^(k+1)∣t := by
  refine ⟨fun ht => ?_,integer_period_of_dvd full⟩
  let N : ℤ := (p:ℤ)^(k+1)
  let d := t.gcd N
  have hdiv : d∣p^(k+1) := by exact_mod_cast Int.gcd_dvd_right t ((p:ℤ)^(k+1))
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdiv
  by_cases heq : i=k+1
  · have hd : (d:ℤ)∣t := Int.gcd_dvd_left _ _
    rwa [he,heq,Nat.cast_pow] at hd
  · have hd : d∣p^k := he ▸ pow_dvd_pow p (by omega : i≤k)
    obtain ⟨a,b,hab⟩ := Int.gcd_dvd_iff.mp hd
    have hh : Periodic f (a*t+b*N) := (ht.int_mul a).add_period (full.int_mul b)
    have eq : a*t+b*N=(p:ℤ)^k := by rw [mul_comm a,mul_comm b,←hab,Nat.cast_pow]
    rw [eq] at hh
    exact (jump (by simpa only [zero_add] using hh 0)).elim

private theorem half_period (h : ℕ) : Periodic (shear p h) ((p:ℤ)^((h+1)/2)) := fun g => by
  simpa only [mul_one] using arithmetic_shear_half_period p h g 1

/-- At every odd precision, exactly the multiples of p^(k+1) preserve
all shear counts modulo p^(2k+1). -/
theorem odd_precision_shear_periods (k : ℕ) (t : ℤ) :
    Periodic (_root_.RHTower.quadraticCongruenceRootCountTotal (p^(2*k+1))) t ↔ (p:ℤ)^(k+1)∣t := by
  have hk : (2*k+1+1)/2=k+1 := by omega
  have hfull := half_period p (2*k+1)
  rw [hk] at hfull
  apply prime_power_period_iff p (shear p (2*k+1)) k hfull _ t
  rw [at_last_power p _ _ hk,at_zero,show (2*k+1)/2=k by omega]
  have hp := pow_pos (Fact.out : p.Prime).pos k
  omega

/-- At even precision the half-precision period is sharp for every odd prime. -/
theorem even_precision_odd_prime_shear_periods (hp : p≠2) (k : ℕ) (t : ℤ) :
    Periodic (_root_.RHTower.quadraticCongruenceRootCountTotal (p^(2*(k+1)))) t ↔ (p:ℤ)^(k+1)∣t := by
  have hk : (2*(k+1)+1)/2=k+1 := by omega
  have hfull := half_period p (2*(k+1))
  rw [hk] at hfull
  apply prime_power_period_iff p (shear p (2*(k+1))) k hfull _ t
  rw [at_last_power p _ _ hk,at_zero,show 2*(k+1)/2=k+1 by omega,pow_succ,mul_comm (p^k)]
  exact fun he => hp ((Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos k) he).symm)

/-- The even dyadic shear is exactly a gcd signal, including the zero gap. -/
theorem even_dyadic_shear_eq_gcd (k : ℕ) (g : ℤ) :
    _root_.RHTower.quadraticCongruenceRootCountTotal (2^(2*(k+1))) g = 2*g.gcd ((2:ℤ)^k) := by
  rw [arithmetic_shear_gcd_formula 2 _ k (by omega)]
  split
  · rename_i hd
    rw [Int.gcd_eq_natAbs_right_iff_dvd.mpr ((pow_dvd_pow (2:ℤ) (Nat.le_succ k)).trans hd)]
    simp only [show 2*(k+1)/2=k+1 by omega,pow_succ',Int.natAbs_pow]
    rfl
  · rfl

/-- The complete period group at even dyadic precision. Modulo 4 every
gap gives two roots, and each further pair of digits doubles the least period. -/
theorem even_dyadic_shear_periods (k : ℕ) (t : ℤ) :
    Periodic (_root_.RHTower.quadraticCongruenceRootCountTotal (2^(2*(k+1)))) t ↔ (2:ℤ)^k∣t := by
  constructor
  · intro ht
    have he := ht 0
    rw [zero_add,even_dyadic_shear_eq_gcd,even_dyadic_shear_eq_gcd,Int.gcd_zero_left] at he
    exact Int.gcd_eq_natAbs_right_iff_dvd.mp (by omega)
  · intro hd g
    rw [even_dyadic_shear_eq_gcd,even_dyadic_shear_eq_gcd,Int.gcd_add_right_left_of_dvd _ hd]

end
end GaloisForLFunctions.RepresentationLifting
