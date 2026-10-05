import GaloisForLFunctions.RHTower.ChiRamanujanFinitePrimeCompensation
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier

/-!
# Literal finite divisor-torsion atoms of the Ramanujan source

All rational atoms are retained. Their Fourier multiplier is the divisor
coefficient at the gcd with the finite prime radical, including frequency zero.
Compensation is performed before either limit.
-/

noncomputable section
open Filter Set ArithmeticFunction
open scoped BigOperators Topology
namespace RHTower.BAGTrace

def ramanujanPrimeRadical (P : Finset ℕ) : ℕ := ∏ p ∈ P.filter Nat.Prime, p

private theorem radical_ne_zero (P : Finset ℕ) : ramanujanPrimeRadical P ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (Finset.mem_filter.mp hp).2.ne_zero

private theorem radical_primeFactors (P : Finset ℕ) :
    (ramanujanPrimeRadical P).primeFactors = P.filter Nat.Prime :=
  Nat.primeFactors_prod (fun _ hp => (Finset.mem_filter.mp hp).2)

private theorem gcd_radical_primeFactors (P : Finset ℕ) (n : ℕ) :
    ((ramanujanPrimeRadical P).gcd n).primeFactors = ramanujanFiniteIncidence P n := by
  have hQ := radical_ne_zero P
  have hg := (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hQ)).ne'
  ext p
  have hQmem := Nat.mem_primeFactors_of_ne_zero (n := ramanujanPrimeRadical P) (p := p) hQ
  rw [radical_primeFactors] at hQmem
  simp only [Finset.mem_filter] at hQmem
  simp only [Nat.mem_primeFactors_of_ne_zero hg, Nat.dvd_gcd_iff,
    ramanujanFiniteIncidence, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hpQ, hpn⟩
    exact ⟨(hQmem.mpr ⟨hp,hpQ⟩).1, hp, hpn⟩
  · rintro ⟨hpP, hp, hpn⟩
    exact ⟨hp, (hQmem.mp ⟨hpP,hp⟩).2, hpn⟩

/-- The zero coordinate is included: its gcd is the full finite prime radical. -/
theorem ramanujanFiniteMultiplier_eq_gcd (P : Finset ℕ) (ε : ℝ) (n : ℕ) :
    ramanujanFiniteMultiplier P ε n =
      pmPowerDampedDivisorCoeff ε ((ramanujanPrimeRadical P).gcd n) := by
  have hg := (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero (radical_ne_zero P))).ne'
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hg, gcd_radical_primeFactors,
    ramanujanFiniteMultiplier, woldSieveNormalFactor]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.pos
  rw [Real.rpow_def_of_pos hp0]
  congr 2
  ring

local instance divisor_neZero (Q : ℕ) (d : Q.divisors) : NeZero (d : ℕ) :=
  ⟨ne_zero_of_dvd_ne_zero (Nat.ne_zero_of_mem_divisors d.property)
    (Nat.dvd_of_mem_divisors d.property)⟩

/-- Every divisor torsion point is retained, including repetitions at the same rational point. -/
abbrev RamanujanAtomIndex (P : Finset ℕ) :=
  (d : (ramanujanPrimeRadical P).divisors) × ZMod (d : ℕ)

noncomputable instance ramanujanAtomIndexFintype (P : Finset ℕ) : Fintype (RamanujanAtomIndex P) :=
  inferInstance

def ramanujanAtomNode {P : Finset ℕ} (a : RamanujanAtomIndex P) : ℝ :=
  (a.2.val : ℝ) / (a.1.val : ℝ)

def ramanujanAtomWeight (P : Finset ℕ) (ε : ℝ) (a : RamanujanAtomIndex P) : ℝ :=
  (moebius a.1.val : ℝ) * (a.1.val : ℝ)^(-ε) / (a.1.val : ℝ)

def ramanujanCompensatedAtomWeight (P : Finset ℕ) (ε : ℝ) (a : RamanujanAtomIndex P) : ℝ :=
  (ramanujanAtomWeight P ε a - ramanujanAtomWeight P 0 a) / ε

def ramanujanFourierPhase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x * (n : ℝ) : ℝ) * Complex.I)

private theorem fourierPhase_eq_stdAddChar {d : ℕ} [NeZero d] (a : ZMod d) (n : ℤ) :
    ramanujanFourierPhase n ((a.val : ℝ) / (d : ℝ)) =
      ZMod.stdAddChar (a * (n : ZMod d)) := by
  have he := ZMod.stdAddChar_coe (N := d) ((a.val : ℤ) * n)
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at he
  rw [he, ramanujanFourierPhase]
  congr 1
  push_cast
  ring

private theorem sum_fourierPhase {d : ℕ} [NeZero d] (n : ℤ) :
    (∑ a : ZMod d, ramanujanFourierPhase n ((a.val : ℝ) / d)) =
      if d ∣ n.natAbs then (d : ℂ) else 0 := by
  simp_rw [fourierPhase_eq_stdAddChar, RHTower.Sieve.sum_stdAddChar_mul,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  split_ifs <;> simp

/-- Finite torsion orthogonality, exposed for further literal atom constructions. -/
theorem sum_ramanujanFourierPhase_torsion {d : ℕ} (hd : d ≠ 0) (n : ℤ) :
    (∑ a : Fin d, ramanujanFourierPhase n ((a.val : ℝ) / d)) =
      if d ∣ n.natAbs then (d : ℂ) else 0 := by
  letI : NeZero d := ⟨hd⟩
  cases d with
  | zero => exact (hd rfl).elim
  | succ d => exact sum_fourierPhase (d := d+1) n

/-- Literal finite signed rational atoms have the required Fourier multiplier. -/
theorem sum_ramanujanAtomWeight_fourier (P : Finset ℕ) (ε : ℝ) (n : ℤ) :
    (∑ a : RamanujanAtomIndex P,
      (ramanujanAtomWeight P ε a : ℂ) * ramanujanFourierPhase n (ramanujanAtomNode a)) =
      (ramanujanFiniteMultiplier P ε n.natAbs : ℂ) := by
  classical
  rw [ramanujanFiniteMultiplier_eq_gcd, pmPowerDampedDivisorCoeff, Complex.ofReal_sum,
    Fintype.sum_sigma]
  have hsum : (∑ d : (ramanujanPrimeRadical P).divisors,
      ∑ a : ZMod (d : ℕ), (ramanujanAtomWeight P ε ⟨d,a⟩ : ℂ) *
        ramanujanFourierPhase n (ramanujanAtomNode ⟨d,a⟩)) =
      ∑ d ∈ (ramanujanPrimeRadical P).divisors,
        if d ∣ n.natAbs then (((moebius d : ℝ) * (d : ℝ)^(-ε) : ℝ) : ℂ) else 0 := by
    conv_rhs => rw [← Finset.sum_attach]
    simp only [Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [ramanujanAtomWeight, ramanujanAtomNode]
    rw [← Finset.mul_sum, sum_fourierPhase]
    by_cases hn : (d : ℕ) ∣ n.natAbs
    · rw [if_pos hn, if_pos hn, Complex.ofReal_div, Complex.ofReal_natCast,
        div_mul_cancel₀ _ (by exact_mod_cast (NeZero.ne (d : ℕ)) : (d : ℂ) ≠ 0)]
    · simp [hn]
  rw [hsum, ← Finset.sum_filter]
  have hfilter : ((ramanujanPrimeRadical P).divisors.filter (fun d => d ∣ n.natAbs)) =
      ((ramanujanPrimeRadical P).gcd n.natAbs).divisors := by
    ext d
    have hg := (Nat.gcd_pos_of_pos_left n.natAbs (Nat.pos_of_ne_zero (radical_ne_zero P))).ne'
    simp [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, radical_ne_zero P, hg]
  rw [hfilter]

/-- Compensation acts on the same literal rational atoms before either limit is taken. -/
theorem sum_ramanujanCompensatedAtomWeight_fourier (P : Finset ℕ) (ε : ℝ) (n : ℤ) :
    (∑ a : RamanujanAtomIndex P,
      (ramanujanCompensatedAtomWeight P ε a : ℂ) * ramanujanFourierPhase n (ramanujanAtomNode a)) =
      (ramanujanCompensatedMultiplier P ε n.natAbs : ℂ) := by
  simp only [ramanujanCompensatedAtomWeight, Complex.ofReal_div, Complex.ofReal_sub,
    div_mul_eq_mul_div, sub_mul, ramanujanCompensatedMultiplier]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_ramanujanAtomWeight_fourier,
    sum_ramanujanAtomWeight_fourier]

/-- On every finite physical band above one, the actual divisor source is recovered
exactly once the finite prime range covers the band; no term is dropped. -/
theorem ramanujanCompensatedMultiplier_range (ε : ℝ) (M : ℕ)
    {n : ℕ} (hn : 1 < n) (hM : n ≤ M) :
    ramanujanCompensatedMultiplier (Finset.range (M+1)) ε n =
      pmPowerDampedDivisorCoeff ε n / ε := by
  have hn0 : n ≠ 0 := by omega
  have hP : n.primeFactors ⊆ Finset.range (M+1) := by
    intro p hp
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hM)
  have hzero : pmPowerDampedDivisorCoeff 0 n = 0 := by
    rw [pmPowerDampedDivisorCoeff_eq_prod 0 hn0]
    obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hn
    exact Finset.prod_eq_zero hp (by simp)
  rw [ramanujanCompensatedMultiplier,
    ramanujanFiniteMultiplier_eq_divisorCoeff hn0 hP ε,
    ramanujanFiniteMultiplier_eq_divisorCoeff hn0 hP 0, hzero, sub_zero]

end RHTower.BAGTrace
