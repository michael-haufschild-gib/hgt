import GaloisForLFunctions.ArithmeticElectrostatics.PowerMapsAreSimilitudesOfTheAbelEnergy

/-!
# Primitive torsion energy as a finite arithmetic divisor sum

Full groups of roots split into primitive orbits. Double Möbius inversion
therefore transfers the full-root energy formula to the original primitive
pairing. At an exponential radius, the divergence and intersection terms
separate exactly, leaving a finite divisor transform of the scalar defect
`log u - log(1 - exp(-u))`.
-/

noncomputable section
open Finset Complex Polynomial
open scoped ComplexConjugate ArithmeticFunction.Moebius
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticElectrostatics

/-- Full-root energy splits into primitive-orbit energies by exact order. -/
theorem fullTorsionEnergy_eq_sum_torsionEnergy (r : ℝ) (m n : ℕ) :
    fullTorsionEnergy r m n = ∑ d ∈ m.divisors, ∑ e ∈ n.divisors,
      torsionEnergy r d e := by
  simp only [fullTorsionEnergy, torsionEnergy, sum_nthRoots_eq_sum_divisors_real]
  exact sum_congr rfl fun d _ => sum_comm

/-- Double Möbius inversion recovers the original primitive energy at every radius. -/
theorem torsionEnergy_eq_doubleMoebius (r : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    torsionEnergy r m n = doubleMoebius m n (fullTorsionEnergy r) :=
  (sum_divisors_moebius_eq_of (f := fun n' => torsionEnergy r m n')
    (g := fun b => ∑ a ∈ m.divisors, (μ (m/a):ℝ)*fullTorsionEnergy r a b)
    (fun b _ => (sum_divisors_moebius_eq_of
      (f := fun m' => ∑ e ∈ b.divisors, torsionEnergy r m' e)
      (g := fun a => fullTorsionEnergy r a b)
      (fun a _ => (fullTorsionEnergy_eq_sum_torsionEnergy r a b).symm) hm).symm) hn).symm

/-- A finite logarithmic divisor formula for the actual primitive-orbit energy. -/
theorem torsionEnergy_divisor_formula (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    torsionEnergy r m n = ∑ d ∈ m.divisors, ∑ e ∈ n.divisors,
      (μ (m/d):ℝ)*(μ (n/e):ℝ)*
        (Nat.gcd d e:ℝ)*(-Real.log (1-r^(Nat.lcm d e))) := by
  rw [torsionEnergy_eq_doubleMoebius r m n hm hn, doubleMoebius_swap]
  simp only [mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  rw [fullTorsionEnergy_eq hr0 hr1 (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)]
  ring

/-- The logarithmic divergence counts common primitive roots. -/
private theorem doubleMoebius_gcd_diagonal (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    doubleMoebius m n (fun a b => (Nat.gcd a b:ℝ)) =
      if m=n then (Nat.totient n:ℝ) else 0 := by
  rw [doubleMoebius_swap]
  simp only [sum_moebius_mul_gcd _ hn, sum_moebius_ite_dvd hm]
  by_cases hnm : n∣m
  · rw [if_pos hnm, ← sum_mul]
    obtain ⟨k, rfl⟩ := hnm
    have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
    rw [Nat.mul_div_cancel_left k hn, sum_divisors_moebius hk]
    by_cases hk1 : k=1
    · subst hk1; simp
    · have hne : n*k≠n := fun h => hk1 (Nat.eq_of_mul_eq_mul_left hn (h.trans (mul_one n).symm))
      rw [if_neg hk1, if_neg hne, zero_mul]
  · rw [if_neg hnm, if_neg fun h : m=n => hnm (h ▸ dvd_rfl)]

private theorem doubleMoebius_mul_const (m n : ℕ) (X : ℕ → ℕ → ℝ) (c : ℝ) :
    doubleMoebius m n (fun a b => X a b*c) = doubleMoebius m n X*c := by
  simp only [doubleMoebius, sum_mul, mul_sum, mul_assoc]

/-- The defect between the logarithmic radius and the exact radial logarithm. -/
def logarithmicSpacingDefect (u : ℝ) : ℝ := Real.log u-Real.log (1-Real.exp (-u))

/-- A finite arithmetic divisor formula for the residual exponential-radius energy. -/
def torsionExponentialDefect (t : ℝ) (m n : ℕ) : ℝ :=
  doubleMoebius m n (fun d e => (Nat.gcd d e:ℝ)*
    logarithmicSpacingDefect (t*(Nat.lcm d e:ℝ)))

private theorem fullTorsionEnergy_exponential (t : ℝ) (ht : 0 < t)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    fullTorsionEnergy (Real.exp (-t)) d e =
      (Nat.gcd d e:ℝ)*logarithmicSpacingDefect (t*(Nat.lcm d e:ℝ)) +
      (Nat.gcd d e:ℝ)*(-Real.log t) -
      (Nat.gcd d e:ℝ)*Real.log (Nat.lcm d e) := by
  have hL : (0:ℝ)<Nat.lcm d e := by exact_mod_cast Nat.lcm_pos hd he
  have hp : Real.exp (-t)^(Nat.lcm d e) = Real.exp (-(t*(Nat.lcm d e:ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [fullTorsionEnergy_eq (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)) hd he, hp,
    logarithmicSpacingDefect, Real.log_mul ht.ne' hL.ne']
  ring

/-- The original exponential-radius energy has an exact finite arithmetic remainder. -/
theorem torsionEnergy_exponential_decomposition (t : ℝ) (ht : 0 < t)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    torsionEnergy (Real.exp (-t)) m n +
      (if m=n then (Nat.totient n:ℝ) else 0)*Real.log t + orbitIntersection m n =
        torsionExponentialDefect t m n := by
  have hk := doubleMoebius_congr (m := m) (n := n)
    (fun d hd e he => fullTorsionEnergy_exponential t ht d e
      (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he))
  have hI : doubleMoebius m n (fun d e => (Nat.gcd d e:ℝ)*Real.log (Nat.lcm d e)) =
      orbitIntersection m n := by
    rw [orbitIntersection_eq_doubleMoebius hm hn]
    exact doubleMoebius_congr fun d hd e he =>
      (logEnergy_eq (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)).symm
  rw [torsionEnergy_eq_doubleMoebius _ m n hm hn, hk, doubleMoebius_add_sub,
    doubleMoebius_mul_const, doubleMoebius_gcd_diagonal m n hm hn, hI]
  unfold torsionExponentialDefect
  ring


#print axioms torsionEnergy_eq_doubleMoebius
#print axioms torsionEnergy_divisor_formula
#print axioms torsionEnergy_exponential_decomposition

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
