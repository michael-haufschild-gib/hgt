import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.FiniteSieveProfilesHaveLogarithmicConductorTails
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveEigenbasisIsTheRamanujanBasis
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy

/-!
# A logarithmic moment for the sieve ground distribution

On a divisor-closed set the pole-weighted prime form is twice the logarithmic
moment. Positivity of the sieve operator therefore bounds that moment by its
finite-prime Euler correction, without a primorial cutoff.
-/

noncomputable section
open Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry ArithmeticElectrostatics ArithmeticEffectivityTheory ArithmeticFunction
  ArithmeticIntersectionTheory

private theorem sieveSupported_of_dvd {Q : Finset Nat.Primes} {m n : ℕ}
    (hn : SieveSupported Q n) (hmn : m ∣ n) : SieveSupported Q m := by
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, hmn.trans hk⟩

private theorem poleVector_mul_upKernel {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    poleVector m * poleVector n * upKernel m n =
      if m ∣ n ∧ m ≠ n then Λ (n / m) / (n : ℝ) else 0 := by
  by_cases h : m ∣ n ∧ m ≠ n
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hqR : (0 : ℝ) < ((n / m : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn h.1) hm
    have hnq : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' h.1).symm
    have hsm := (Real.sqrt_pos.mpr hmR).ne'
    have hsq := (Real.sqrt_pos.mpr hqR).ne'
    rw [upKernel, if_pos h, if_pos h, poleVector, poleVector, hnq, Real.sqrt_mul hmR.le]
    field_simp [hsm, hsq, hmR.ne', hqR.ne']
    simp only [Real.sq_sqrt hmR.le, Real.sq_sqrt hqR.le]
    ring
  · simp only [upKernel, if_neg h, mul_zero]

private theorem sum_divisorClosed_pole_down {Q : Finset Nat.Primes}
    (S : Finset (SieveClass Q))
    (hclosed : ∀ n ∈ S, ∀ d : SieveClass Q, (d : ℕ) ∣ (n : ℕ) → d ∈ S)
    {n : SieveClass Q} (hn : n ∈ S) :
    (∑ m ∈ S, poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel m n) =
      Real.log (n : ℕ) / (n : ℕ) := by
  have hterm (m : SieveClass Q) :
      poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel m n =
        if (m : ℕ) ∣ (n : ℕ) then Λ ((n : ℕ) / (m : ℕ)) / (n : ℕ) else 0 := by
    rw [poleVector_mul_upKernel m.property.pos n.property.pos]
    by_cases hmn : (m : ℕ) = (n : ℕ)
    · rw [hmn]
      simp [Nat.div_self n.property.pos]
    · by_cases hd : (m : ℕ) ∣ (n : ℕ)
      · rw [if_pos ⟨hd, hmn⟩, if_pos hd]
      · rw [if_neg (fun h => hd h.1), if_neg hd]
  simp_rw [hterm]
  rw [← sum_filter]
  have hsum : (∑ m ∈ S.filter (fun m : SieveClass Q => (m : ℕ) ∣ (n : ℕ)),
      Λ ((n : ℕ) / (m : ℕ)) / (n : ℕ)) =
        ∑ d ∈ (n : ℕ).divisors, Λ ((n : ℕ) / d) / (n : ℕ) := by
    apply Finset.sum_bij (fun (m : SieveClass Q) _ => (m : ℕ))
    · intro m hm
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hm).2, n.property.pos.ne'⟩
    · intro m _ l _ h
      exact Subtype.ext h
    · intro d hd
      let m : SieveClass Q := ⟨d, sieveSupported_of_dvd n.property (Nat.mem_divisors.mp hd).1⟩
      refine ⟨m, mem_filter.mpr ⟨hclosed n hn m (Nat.mem_divisors.mp hd).1,
        (Nat.mem_divisors.mp hd).1⟩, rfl⟩
    · intro m _
      rfl
  rw [hsum, ← sum_div, Nat.sum_div_divisors (n : ℕ) (fun d => Λ d), vonMangoldt_sum]

/-- Divisor closure makes the downward prime row exact; symmetry pays both orientations. -/
theorem primeForm_divisorClosed_sievePole {Q : Finset Nat.Primes}
    (S : Finset (SieveClass Q))
    (hclosed : ∀ n ∈ S, ∀ d : SieveClass Q, (d : ℕ) ∣ (n : ℕ) → d ∈ S) :
    (∑ m ∈ S, ∑ n ∈ S, poleVector (m : ℕ) * poleVector (n : ℕ) * weilPrimeKernel m n) =
      2 * ∑ n ∈ S, Real.log (n : ℕ) / (n : ℕ) := by
  have hswap : (∑ m ∈ S, ∑ n ∈ S,
      poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel n m) =
        ∑ m ∈ S, ∑ n ∈ S, poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  calc
    _ = (∑ m ∈ S, ∑ n ∈ S, poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel m n) +
        (∑ m ∈ S, ∑ n ∈ S, poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel n m) := by
      simp only [weilPrimeKernel_eq_up_add, mul_add, sum_add_distrib]
    _ = 2 * ∑ m ∈ S, ∑ n ∈ S,
        poleVector (m : ℕ) * poleVector (n : ℕ) * upKernel m n := by rw [hswap]; ring
    _ = _ := by
      congr 1
      rw [sum_comm]
      exact sum_congr rfl fun n hn => sum_divisorClosed_pole_down S hclosed hn

private theorem sum_log_div_sievePole_le {Q : Finset Nat.Primes}
    (S : Finset (SieveClass Q))
    (hclosed : ∀ n ∈ S, ∀ d : SieveClass Q, (d : ℕ) ∣ (n : ℕ) → d ∈ S) :
    (∑ n ∈ S, Real.log (n : ℕ) / (n : ℕ)) ≤
      (sieveEuler Q - Real.eulerMascheroniConstant) * ∑ n ∈ S, 1 / ((n : ℕ) : ℝ) := by
  let b : S → ℝ := fun n => poleVector ((n : SieveClass Q) : ℕ)
  have hs := hasSum_sieveClassVector_conductorEnergy
    (d := fun n : S => (n : SieveClass Q)) Subtype.val_injective b
  have h : 0 ≤
      (∑ n : S, (Real.log ((n : SieveClass Q) : ℕ) +
        (sieveEuler Q - Real.eulerMascheroniConstant)) * b n ^ 2) -
      ∑ m : S, ∑ n : S, b m * b n * weilPrimeKernel (m : SieveClass Q) (n : SieveClass Q) := by
    rw [← hs.tsum_eq]
    exact tsum_nonneg fun m => mul_nonneg
      (add_nonneg (Real.log_natCast_nonneg _) (tameDifferent_nonneg _)) (sq_nonneg _)
  have hdiag : (∑ n : S, (Real.log ((n : SieveClass Q) : ℕ) +
      (sieveEuler Q - Real.eulerMascheroniConstant)) * b n ^ 2) =
      (∑ n ∈ S, Real.log (n : ℕ) / (n : ℕ)) +
        (sieveEuler Q - Real.eulerMascheroniConstant) * ∑ n ∈ S, 1 / ((n : ℕ) : ℝ) := by
    change (∑ n : S, (Real.log ((n : SieveClass Q) : ℕ) +
      (sieveEuler Q - Real.eulerMascheroniConstant)) *
        poleVector ((n : SieveClass Q) : ℕ) ^ 2) = _
    rw [Finset.sum_coe_sort S (fun n : SieveClass Q =>
      (Real.log (n : ℕ) + (sieveEuler Q - Real.eulerMascheroniConstant)) * poleVector (n : ℕ) ^ 2),
      mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun n _ => by rw [poleVector_sq]; ring
  have hprime : (∑ m : S, ∑ n : S,
      b m * b n * weilPrimeKernel (m : SieveClass Q) (n : SieveClass Q)) =
        2 * ∑ n ∈ S, Real.log (n : ℕ) / (n : ℕ) := by
    change (∑ m : S, ∑ n : S, poleVector ((m : SieveClass Q) : ℕ) *
      poleVector ((n : SieveClass Q) : ℕ) *
        weilPrimeKernel (m : SieveClass Q) (n : SieveClass Q)) = _
    calc
      _ = ∑ m ∈ S, ∑ n ∈ S,
          poleVector (m : ℕ) * poleVector (n : ℕ) * weilPrimeKernel m n := by
        rw [Finset.sum_coe_sort S (fun m : SieveClass Q =>
          ∑ n : S, poleVector (m : ℕ) * poleVector ((n : SieveClass Q) : ℕ) *
            weilPrimeKernel m (n : SieveClass Q))]
        exact sum_congr rfl fun m _ => Finset.sum_coe_sort S (fun n : SieveClass Q =>
          poleVector (m : ℕ) * poleVector (n : ℕ) * weilPrimeKernel m n)
      _ = _ := primeForm_divisorClosed_sievePole S hclosed
  rw [hdiag, hprime] at h
  linarith only [h]

/-- Each prime contributes a nonnegative amount above the Euler ground constant. -/
theorem sieveEuler_correction_nonneg (Q : Finset Nat.Primes) :
    0 ≤ sieveEuler Q - Real.eulerMascheroniConstant := by
  have heq : sieveEuler Q - Real.eulerMascheroniConstant =
      ∑ p ∈ Q, Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1) := by unfold sieveEuler; ring
  rw [heq]
  exact sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg _)
    (by have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
        linarith only [hp])

/-- Every finite partial logarithmic moment is bounded by the finite-prime Euler correction. -/
theorem sum_log_mul_sieveClassDensity_le {Q : Finset Nat.Primes}
    (S : Finset (SieveClass Q)) :
    (∑ n ∈ S, Real.log (n : ℕ) * sieveClassDensity Q n) ≤
      sieveEuler Q - Real.eulerMascheroniConstant := by
  let T : Finset (SieveClass Q) :=
    Finset.subtype (SieveSupported Q) (Icc 1 (S.sup (fun n => (n : ℕ))))
  have hmem (n : SieveClass Q) : n ∈ T ↔ (n : ℕ) ≤ S.sup (fun n => (n : ℕ)) := by
    constructor
    · intro hn
      exact (mem_Icc.mp (Finset.mem_subtype.mp hn)).2
    · intro hn
      exact Finset.mem_subtype.mpr (mem_Icc.mpr ⟨n.property.pos, hn⟩)
  have hsub : S ⊆ T := fun n hn => (hmem n).mpr (Finset.le_sup hn)
  have hclosed : ∀ n ∈ T, ∀ d : SieveClass Q, (d : ℕ) ∣ (n : ℕ) → d ∈ T := by
    intro n hn d hdn
    exact (hmem d).mpr ((Nat.le_of_dvd n.property.pos hdn).trans ((hmem n).mp hn))
  have hweighted : (∑ n ∈ T, Real.log (n : ℕ) * sieveClassDensity Q n) ≤
      (sieveEuler Q - Real.eulerMascheroniConstant) * ∑ n ∈ T, sieveClassDensity Q n := by
    calc
      _ = sieveDensity Q * ∑ n ∈ T, Real.log (n : ℕ) / (n : ℕ) := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by unfold sieveClassDensity; ring
      _ ≤ sieveDensity Q * ((sieveEuler Q - Real.eulerMascheroniConstant) *
          ∑ n ∈ T, 1 / ((n : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_log_div_sievePole_le T hclosed) (sieveDensity_pos Q).le
      _ = (sieveEuler Q - Real.eulerMascheroniConstant) *
          (sieveDensity Q * ∑ n ∈ T, 1 / ((n : ℕ) : ℝ)) := by ring
      _ = _ := by
        congr 1
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by unfold sieveClassDensity; ring
  have hmass : (∑ n ∈ T, sieveClassDensity Q n) ≤ 1 := by
    have h := Summable.sum_le_tsum T (fun n _ => (sieveClassDensity_pos n.property).le)
      (hasSum_sieveClassDensity Q).summable
    rwa [(hasSum_sieveClassDensity Q).tsum_eq] at h
  calc
    _ ≤ ∑ n ∈ T, Real.log (n : ℕ) * sieveClassDensity Q n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
        mul_nonneg (Real.log_natCast_nonneg _) (sieveClassDensity_pos n.property).le
    _ ≤ (sieveEuler Q - Real.eulerMascheroniConstant) * ∑ n ∈ T, sieveClassDensity Q n := hweighted
    _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmass (sieveEuler_correction_nonneg Q)

/-- The logarithmic moment is summable, as its nonnegative finite partial sums are uniformly bounded. -/
theorem summable_log_mul_sieveClassDensity (Q : Finset Nat.Primes) :
    Summable (fun n : SieveClass Q => Real.log (n : ℕ) * sieveClassDensity Q n) :=
  summable_of_sum_le
    (fun n => mul_nonneg (Real.log_natCast_nonneg _) (sieveClassDensity_pos n.property).le)
    sum_log_mul_sieveClassDensity_le

/-- The arithmetic ground distribution has a logarithmic moment bounded independently of its primorial. -/
theorem tsum_log_mul_sieveClassDensity_le (Q : Finset Nat.Primes) :
    (∑' n : SieveClass Q, Real.log (n : ℕ) * sieveClassDensity Q n) ≤
      sieveEuler Q - Real.eulerMascheroniConstant :=
  Real.tsum_le_of_sum_le
    (fun n => mul_nonneg (Real.log_natCast_nonneg _) (sieveClassDensity_pos n.property).le)
    sum_log_mul_sieveClassDensity_le

/-- The geometric sieve distribution loses at most its Euler correction divided by the logarithmic cutoff. -/
theorem tsum_sieveClassDensity_above_le (Q : Finset Nat.Primes) {R : ℝ} (hR : 1 < R) :
    (∑' n : SieveClass Q, if R < (n : ℕ) then sieveClassDensity Q n else 0) ≤
      (sieveEuler Q - Real.eulerMascheroniConstant) / Real.log R := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hsum := (summable_log_mul_sieveClassDensity Q).div_const (Real.log R)
  have hdom (n : SieveClass Q) : (if R < (n : ℕ) then sieveClassDensity Q n else 0) ≤
      Real.log (n : ℕ) * sieveClassDensity Q n / Real.log R := by
    by_cases hn : R < (n : ℕ)
    · rw [if_pos hn]
      apply (le_div_iff₀ hlogR).mpr
      calc
        _ = Real.log R * sieveClassDensity Q n := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.log_le_log (zero_lt_one.trans hR) hn.le) (sieveClassDensity_pos n.property).le
    · rw [if_neg hn]
      exact div_nonneg (mul_nonneg (Real.log_natCast_nonneg _)
        (sieveClassDensity_pos n.property).le) hlogR.le
  have htail := Summable.of_nonneg_of_le
    (fun n => by split_ifs <;> first | exact (sieveClassDensity_pos n.property).le | exact le_rfl)
    hdom hsum
  calc
    _ ≤ ∑' n : SieveClass Q, Real.log (n : ℕ) * sieveClassDensity Q n / Real.log R :=
      Summable.tsum_le_tsum hdom htail hsum
    _ = (∑' n : SieveClass Q, Real.log (n : ℕ) * sieveClassDensity Q n) / Real.log R := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right (tsum_log_mul_sieveClassDensity_le Q) hlogR.le

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.primeForm_divisorClosed_sievePole
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.sum_log_mul_sieveClassDensity_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.summable_log_mul_sieveClassDensity
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tsum_log_mul_sieveClassDensity_le
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tsum_sieveClassDensity_above_le
