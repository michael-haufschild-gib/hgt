import GaloisForLFunctions.PrimeExponentialSums.RamifiedGeometricEulerFactors
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernelMass
import Mathlib.Analysis.PSeries

/-!
# Absolute convergence after cancellation of initial Euler coefficients

The half-plane in Gou's Lemma 3.1 comes from the vanishing linear
coefficient of every correction factor. Vanishing through degree m−1
gives the corresponding half-plane mσ>1 for bounded local coefficients.
The majorant is uniform in the protected prime set.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler

/-- A local series supported in degrees zero and at least m has a geometric
tail whose cost starts with the m-th power of the local ratio. -/
theorem delayed_local_mass (m : ℕ+) (u : ℕ → ℝ) (C q : ℝ)
    (hu : ∀ j, 0 ≤ u j) (h₀ : u 0=1) (hz : ∀ j : ℕ, 0<j → j<(m : ℕ) → u j=0)
    (hb : ∀ j : ℕ, (m : ℕ) ≤ j → u j ≤ C) (hq₀ : 0 ≤ q) (hq : q<1) :
    Summable (fun j : ℕ => u j*q^j) ∧
      (∑' j : ℕ, u j*q^j) ≤ 1+C*q^(m : ℕ)/(1-q) := by
  have geom := summable_geometric_of_lt_one hq₀ hq
  have htail : ∀ j : ℕ, u (j+(m : ℕ))*q^(j+(m : ℕ)) ≤
      (C*q^(m : ℕ))*q^j := by
    intro j
    exact (mul_le_mul_of_nonneg_right (hb (j+(m : ℕ)) (Nat.le_add_left _ _))
      (pow_nonneg hq₀ _)).trans_eq (by rw [pow_add]; ac_rfl)
  have hs : Summable (fun j : ℕ => u j*q^j) := by
    rw [← summable_nat_add_iff (m : ℕ)]
    exact Summable.of_nonneg_of_le (fun j => mul_nonneg (hu _) (pow_nonneg hq₀ _))
      htail (geom.mul_left _)
  refine ⟨hs,?_⟩
  rw [← hs.sum_add_tsum_nat_add (m : ℕ)]
  have hhead : (∑ j ∈ range (m : ℕ), u j*q^j)=1 := by
    rw [sum_eq_single 0]
    · simp [h₀]
    · intro j hj hne
      rw [hz j (Nat.pos_of_ne_zero hne) (mem_range.mp hj),zero_mul]
    · exact fun h => (h (mem_range.mpr m.pos)).elim
  rw [hhead]
  apply add_le_add_right
  have hh := ((summable_nat_add_iff _).2 hs).tsum_le_tsum htail (geom.mul_left _)
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq₀ hq] at hh
  simpa only [div_eq_mul_inv] using hh

/-- Absolute Dirichlet mass as a real multiplicative arithmetic function. -/
def weightedNorm (f : ArithmeticFunction ℂ) (σ : ℝ) : ArithmeticFunction ℝ where
  toFun n := ‖f n‖*(n : ℝ)^(-σ)
  map_zero' := by simp

private theorem weighted_mul (f : ArithmeticFunction ℂ) (σ : ℝ) (hf : f.IsMultiplicative) :
    (weightedNorm f σ).IsMultiplicative := by
  refine ⟨by simp [weightedNorm,hf.map_one],fun {a b} hab => ?_⟩
  change ‖f (a*b)‖*((a*b : ℕ) : ℝ)^(-σ) = _
  rw [hf.map_mul_of_coprime hab,norm_mul,Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  change _ = (‖f a‖*(a : ℝ)^(-σ))*(‖f b‖*(b : ℝ)^(-σ))
  ring

private theorem weighted_prime (f : ArithmeticFunction ℂ) (σ : ℝ) (p j : ℕ) :
    weightedNorm f σ (p^j)=‖f (p^j)‖*((p : ℝ)^(-σ))^j := by
  change ‖f (p^j)‖*((p^j : ℕ) : ℝ)^(-σ) = _
  rw [Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg _),mul_comm (j : ℝ),
    Real.rpow_mul_natCast (Nat.cast_nonneg _)]

/-- Uniformly bounded local rows with a gap of length m−1 give absolute
convergence throughout the half-plane mσ>1. -/
theorem delayed_absolute_convergence (m : ℕ+) (C : NNReal) (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hz : ∀ (p : Nat.Primes) (j : ℕ), 0 < j → j < (m : ℕ) → f ((p : ℕ)^j)=0)
    (hb : ∀ (p : Nat.Primes) (j : ℕ), (m : ℕ) ≤ j → ‖f ((p : ℕ)^j)‖ ≤ (C : ℝ))
    (σ : ℝ) (hσ : 1 < (m : ℝ)*σ) : Summable fun n : ℕ => weightedNorm f σ n := by
  have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hpos : 0 < σ := pos_of_mul_pos_right (zero_lt_one.trans hσ) hm.le
  let ρ : ℝ := (2 : ℝ)^(-σ)
  have hρ : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr hpos)
  let rate (n : ℕ) : ℝ := (n : ℝ)^(-σ)
  have rate_nonneg (n : ℕ) : 0 ≤ rate n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrate (p : Nat.Primes) : rate p ≤ ρ :=
    Real.rpow_le_rpow_of_nonpos zero_lt_two (by exact_mod_cast p.property.two_le) (neg_nonpos.mpr hpos.le)
  have localMass (p : Nat.Primes) := delayed_local_mass m (fun j => ‖f ((p : ℕ)^j)‖) C (rate p)
    (fun _ => norm_nonneg _) (by simp [hf.map_one])
    (fun j hj hlt => by rw [hz p j hj hlt,norm_zero]) (hb p) (rate_nonneg p) ((hrate p).trans_lt hρ)
  let K := (C : ℝ)/(1-ρ)
  have hK : 0 ≤ K := div_nonneg C.property (sub_nonneg.mpr hρ.le)
  let b (n : ℕ) := K*((n : ℝ)^((m : ℝ)*σ))⁻¹
  apply _root_.RHTower.pm_summable_of_multiplicative_local_bound (weightedNorm f σ)
    (weighted_mul f σ hf) (fun n => mul_nonneg (norm_nonneg _) (rate_nonneg n)) (b := b)
  · intro p hp
    simpa only [weighted_prime,rate] using (localMass ⟨p,hp⟩).1
  · intro n
    exact mul_nonneg hK (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · exact (Real.summable_nat_rpow_inv.mpr hσ).mul_left K
  · intro p hp
    let P : Nat.Primes := ⟨p,hp⟩
    have hl := (localMass P).2
    have hh : ((rate p)^(m : ℕ))=((p : ℝ)^((m : ℝ)*σ))⁻¹ := by
      change ((p : ℝ)^(-σ))^(m : ℕ) = _
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p),show (-σ)*(m : ℕ) = -((m : ℝ)*σ) by ring,
        Real.rpow_neg (Nat.cast_nonneg _)]
    have hd := div_le_div_of_nonneg_left C.property (sub_pos.mpr hρ)
      (sub_le_sub_left (hrate P) 1)
    calc
      _ ≤ 1+(C : ℝ)*(rate p)^(m : ℕ)/(1-rate p) := by
        simpa only [weighted_prime,rate,P] using hl
      _ ≤ 1+b p := by
        have he := mul_le_mul_of_nonneg_right hd (pow_nonneg (rate_nonneg p) (m : ℕ))
        dsimp only [b]
        rw [← hh]
        dsimp only [K] at *
        apply add_le_add_right
        calc
          _ = ((C : ℝ)/(1-rate p))*(rate p)^(m : ℕ) := by ring
          _ ≤ _ := he
      _ ≤ Real.exp (b p) := by simpa only [add_comm] using Real.add_one_le_exp (b p)

/-- Gou's half-plane for every protected denominator, including the unramified
case q=1 and the completely protected case q=0. -/
theorem correction_summable (q : ℕ) (A : ℕ → ℕ → ℂ)
    (hA : ∀ (p : Nat.Primes) (j : ℕ), 0 < j → ‖A p j‖ ≤ 1)
    (σ : ℝ) (hs : 1/2 < σ) : Summable fun n : ℕ => weightedNorm (correction q A) σ n := by
  refine delayed_absolute_convergence (2 : ℕ+) 2 (correction q A)
    (RHTower.Sieve.localEuler_isMultiplicative _) ?_ ?_ σ ?_
  · intro p j hj hk
    change j < 2 at hk
    obtain rfl : j=1 := by omega
    simpa only [pow_one] using correction_prime q A p
  · intro p j hj
    change 2 ≤ j at hj
    obtain ⟨k,rfl⟩ : ∃ k, j=k+1 := ⟨j-1,by omega⟩
    rw [correction_local]
    split
    · simp
    · have hk : 0<k := by omega
      rw [RHTower.Sieve.normalizedPrimePowerValue,if_neg hk.ne']
      have hprod : ‖A p 1*A p k‖≤1 := by
        rw [norm_mul]
        exact mul_le_one₀ (hA p 1 one_pos) (norm_nonneg _) (hA p k hk)
      have hh := (norm_sub_le (A p (k+1)) (A p 1*A p k)).trans
        (add_le_add (hA p (k+1) (Nat.succ_pos k)) hprod)
      change ‖A p (k+1)-A p 1*A p k‖ ≤ (2 : ℝ)
      linarith only [hh]
  · change 1 < (2 : ℝ)*σ
    linarith only [hs]

/-- Euler coefficients that select exactly the prime exponents divisible by m. -/
def powerSelector (m : ℕ+) : ArithmeticFunction ℂ :=
  _root_.RHTower.Sieve.localEuler (fun _ k => if (m : ℕ) ∣ k then 1 else 0)

private theorem selector_local (m : ℕ+) (p : Nat.Primes) (k : ℕ) (hk : 0<k) :
    powerSelector m ((p : ℕ)^k) = if (m : ℕ) ∣ k then 1 else 0 := by
  unfold powerSelector
  rw [RHTower.Sieve.localEuler_prime_pow,if_neg hk.ne']

theorem selector_on_powers (m n : ℕ+) : powerSelector m ((n : ℕ)^(m : ℕ))=1 := by
  change (if (n : ℕ)^(m : ℕ)=0 then (0 : ℂ) else ∏ p ∈ ((n : ℕ)^(m : ℕ)).primeFactors,
    if (m : ℕ) ∣ ((n : ℕ)^(m : ℕ)).factorization p then 1 else 0)=1
  rw [if_neg (pow_ne_zero _ n.pos.ne')]
  apply prod_eq_one
  intro p _
  rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul,if_pos (dvd_mul_right _ _)]

/-- No larger half-plane works uniformly: at the boundary the perfect powers
already reproduce the divergent harmonic series. -/
theorem selector_abscissa (m : ℕ+) (σ : ℝ) :
    (Summable fun n : ℕ => weightedNorm (powerSelector m) σ n) ↔ 1 < (m : ℝ)*σ := by
  constructor
  · intro hs
    have hinj : Function.Injective (fun n : ℕ => (n+1)^(m : ℕ)) :=
      (Nat.pow_left_strictMono m.pos.ne').injective.comp Nat.succ_injective
    have h := hs.comp_injective hinj
    apply Real.summable_nat_rpow_inv.mp
    rw [← summable_nat_add_iff 1]
    refine h.congr fun n => ?_
    change ‖powerSelector m ((n+1)^(m : ℕ))‖*((((n+1)^(m : ℕ) : ℕ) : ℝ)^(-σ)) = _
    have hsel : powerSelector m ((n+1)^(m : ℕ))=1 := selector_on_powers m ⟨n+1,Nat.succ_pos _⟩
    rw [hsel,norm_one,one_mul,Nat.cast_pow,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg _),mul_neg,Real.rpow_neg (Nat.cast_nonneg _)]
  · intro hs
    refine delayed_absolute_convergence m 1 (powerSelector m) (RHTower.Sieve.localEuler_isMultiplicative _) ?_ ?_ σ hs
    · intro p j hj hlt
      rw [selector_local m p j hj,if_neg (fun h => hlt.not_ge (Nat.le_of_dvd hj h))]
    · intro p j hj
      have hj' : 0 < j := m.pos.trans_le hj
      rw [selector_local m p j hj']
      split <;> simp

end GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler

#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.delayed_local_mass
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.delayed_absolute_convergence
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.correction_summable
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.selector_on_powers
#print axioms GaloisForLFunctions.PrimeExponentialSums.RamifiedEuler.selector_abscissa
