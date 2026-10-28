import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveClassesAreValuationCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations
import GaloisForLFunctions.HTGeometry.HardyNumberSpectrum

/-!
# Finite-prime excitations are torsion-adjunction energies

The geometric ground correction cancels the corresponding Euler constant.
Every excited prime contributes its valuation and its tame different. Thus the
local spectral labels are the actual arithmetic adjunction labels.
-/

noncomputable section

open Filter Topology
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory HTGeometry

/-- The critical geometric parameter at a prime. -/
def primeBlaschkeParameter (p : Nat.Primes) : ℝ := 1 / Real.sqrt (p : ℕ)

theorem primeBlaschkeParameter_norm_lt_one (p : Nat.Primes) :
    ‖(primeBlaschkeParameter p : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, primeBlaschkeParameter,
    abs_of_nonneg (inv_sqrt_prime_nonneg (p : ℕ))]
  exact inv_sqrt_prime_lt_one p.property

theorem primeBlaschkeParameter_sq (p : Nat.Primes) :
    primeBlaschkeParameter p ^ 2 = 1 / (p : ℕ) := by
  rw [primeBlaschkeParameter, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem primeBlaschkeGroundCorrection (p : Nat.Primes) :
    primeBlaschkeParameter p ^ 2 / (1 - primeBlaschkeParameter p ^ 2) =
      1 / ((p : ℕ) - (1 : ℝ)) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  rw [primeBlaschkeParameter_sq]
  have hden : 1 - 1 / ((p : ℕ) : ℝ) ≠ 0 := by
    exact (sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp)).mpr hp)).ne'
  field_simp [hden, (zero_lt_one.trans hp).ne', (sub_pos.mpr hp).ne']

/-- Adding the prime's Euler correction leaves exactly the rational excitation weight. -/
theorem hardyNumberEnergy_prime_add (p : Nat.Primes) (k : ℕ) :
    hardyNumberEnergy (primeBlaschkeParameter p) k + 1 / ((p : ℕ) - (1 : ℝ)) =
      (primeExcitationWeight p k : ℝ) := by
  by_cases hk : k = 0
  · subst k
    rw [primeExcitationWeight_zero, Rat.cast_zero]
    change -(primeBlaschkeParameter p ^ 2) / (1 - primeBlaschkeParameter p ^ 2) +
      1 / ((p : ℕ) - (1 : ℝ)) = 0
    rw [neg_div, primeBlaschkeGroundCorrection]
    ring
  · simp only [hardyNumberEnergy, if_neg hk, primeExcitationWeight,
      Rat.cast_add, Rat.cast_natCast,
      Rat.cast_inv, Rat.cast_sub, Rat.cast_one, one_div]

/-- The tame different is the sum of the occupied-prime corrections inside the sieve. -/
theorem tameDifferent_eq_sieve_sum {Q : Finset Nat.Primes} {n : ℕ}
    (hn : SieveSupported Q n) :
    tameDifferent n = ∑ p : Q,
      if n.factorization (p : Nat.Primes) = 0 then 0
      else Real.log ((p : Nat.Primes) : ℕ) / (((p : Nat.Primes) : ℕ) - (1 : ℝ)) := by
  let f : Nat.Primes → ℝ := fun p => if n.factorization (p : ℕ) = 0 then 0
    else Real.log (p : ℕ) / ((p : ℕ) - (1 : ℝ))
  let g : Nat.Primes → ℝ := fun p => Real.log (p : ℕ) / ((p : ℕ) - (1 : ℝ))
  let T : Finset Nat.Primes := Q.filter (fun p : Nat.Primes => n.factorization (p : ℕ) ≠ 0)
  change (∑ p ∈ n.primeFactors, Real.log p / ((p : ℝ) - 1)) = ∑ p : Q, f p
  rw [Finset.sum_coe_sort Q f]
  symm
  trans ∑ p ∈ T, g p
  · dsimp only [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : n.factorization (p : ℕ) = 0 <;> simp [f, g, hp]
  apply Finset.sum_bij (fun (p : Nat.Primes) _ => (p : ℕ))
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hp'
  · intro p _ q _ hpq
    exact Subtype.ext hpq
  · intro p hp
    let pp : Nat.Primes := ⟨p, Nat.prime_of_mem_primeFactors hp⟩
    refine ⟨pp, Finset.mem_filter.mpr ⟨hn.prime_dvd_mem (Nat.dvd_of_mem_primeFactors hp), ?_⟩,
      rfl⟩
    exact Finsupp.mem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
  · intro p hp
    rfl

/-- The rational prime-log energy is logarithmic degree plus the tame different. -/
theorem finitePrimeExcitationEnergy_eq (Q : Finset Nat.Primes) (e : Q → ℕ) :
    finitePrimeExcitationEnergy Q e =
      Real.log (((sieveValuationEquiv Q).symm e : ℕ) : ℝ) +
        tameDifferent ((sieveValuationEquiv Q).symm e : ℕ) := by
  rw [log_sieveValuationEquiv_symm,
    tameDifferent_eq_sieve_sum ((sieveValuationEquiv Q).symm e).property,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hp : (((sieveValuationEquiv Q).symm e : ℕ)).factorization (p : Nat.Primes) = e p :=
    congrFun ((sieveValuationEquiv Q).apply_symm_apply e) p
  rw [hp]
  by_cases he : e p = 0
  · simp [primeExcitationWeight, he]
  · simp only [primeExcitationWeight, if_neg he, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_inv, Rat.cast_sub, Rat.cast_one]
    ring

/-- Arithmetic excitation energies distinguish the actual supported integers. -/
theorem sieveAdjunctionEnergy_injective (Q : Finset Nat.Primes) :
    Function.Injective (fun n : SieveClass Q => Real.log (n : ℕ) + tameDifferent (n : ℕ)) := by
  intro m n h
  apply (sieveValuationEquiv Q).injective
  apply finitePrimeExcitationEnergy_injective Q
  simpa only [finitePrimeExcitationEnergy_eq, Equiv.symm_apply_apply] using h

/-- Positive shifted arithmetic energies have no finite accumulation window. -/
theorem tendsto_sieveAdjunctionEnergy_cofinite (Q : Finset Nat.Primes) :
    Tendsto (fun n : SieveClass Q => 1 + Real.log (n : ℕ) + tameDifferent (n : ℕ))
      cofinite atTop := by
  have hn : Tendsto (fun n : SieveClass Q => (n : ℕ)) cofinite atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact Subtype.val_injective.tendsto_cofinite
  have hlog : Tendsto (fun n : SieveClass Q => Real.log (n : ℕ)) cofinite atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  apply Filter.tendsto_atTop_mono (fun n => ?_) hlog
  linarith only [tameDifferent_nonneg (n : ℕ)]

theorem one_le_sieveAdjunctionEnergy (Q : Finset Nat.Primes) (n : SieveClass Q) :
    1 ≤ 1 + Real.log (n : ℕ) + tameDifferent (n : ℕ) := by
  have hn : (1 : ℕ) ≤ (n : ℕ) := n.property.pos
  have hlog : 0 ≤ Real.log (n : ℕ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  linarith only [hlog, tameDifferent_nonneg (n : ℕ)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
