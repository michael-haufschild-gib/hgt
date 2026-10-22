import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerEulerEnvelope
import GaloisForLFunctions.ArithmeticIncidencePositivity.GlobalIncidenceAllocationCondition
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomEvenPartPotential
import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeWindowOddStrip

/-!
# The incidence ledger with the prime powers eliminated

The ledger of the odd zero form at aperture `r` reads

    Ẑ(F) = pool + crossing potential + Σ_n evenStripGain_n − Σ_n oddStripCost_n
           + gauge remainder − pole charge,

the sums over the relevant shifts `n ≥ 2`, `log n < 2r`, one term per prime power. By the exact
even–odd identity of the atom, the net charge of a shift is the atom times the autocorrelation,

    evenStripGain_n − oddStripCost_n = −2 Λ(n) n^{−1/2} A(log n),

so the net prime charge of the ledger is `−2` times the prime side. The tower law then eliminates
the proper prime powers: the whole cost side is bounded by a functional of the **primes** below the
horizon and their first-power autocorrelations `A(log p)`, with the Euler constants
`log p/(p − 1)` and `√p log p/(p − 1)`.
-/

open MeasureTheory Set
open scoped ArithmeticFunction
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-! ### The autocorrelation at exactly twice the support radius -/

/-- At twice the support radius the autocorrelation already vanishes: the product of the test and
its translate is then supported in a single point. -/
theorem autoCorr_eq_zero_of_support_le {B : ℝ} (hsupp : ∀ x, B < |x| → F x = 0) {t : ℝ}
    (ht : 2 * B ≤ |t|) : autoCorr F t = 0 := by
  have key : ∀ x : ℝ, x ≠ -(t / 2) → F x * F (x + t) = 0 := by
    intro x hx
    by_cases h1 : F x = 0
    · rw [h1, zero_mul]
    by_cases h2 : F (x + t) = 0
    · rw [h2, mul_zero]
    have b1 : |x| ≤ B := not_lt.mp fun h => h1 (hsupp x h)
    have b2 : |x + t| ≤ B := not_lt.mp fun h => h2 (hsupp _ h)
    exact absurd
      (by
        rcases abs_cases x with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
          rcases abs_cases (x + t) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
            rcases abs_cases t with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
              rw [e1] at b1 <;> rw [e2] at b2 <;> rw [e3] at ht <;> linarith)
      hx
  refine integral_eq_zero_of_ae ?_
  have hnull : ({-(t / 2)} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.mpr (measure_singleton _)
  filter_upwards [hnull] with x hx
  exact key x (by simpa using hx)

/-- The prime side is the finite sum over the relevant shifts of the aperture. -/
theorem primeSideCharge_eq_sum_relevantShifts {r : ℝ} (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    primeSideCharge F
      = ∑ n ∈ relevantShifts r, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n) := by
  refine tsum_eq_sum fun n hn => ?_
  rw [mem_relevantShifts] at hn
  by_cases h2 : 2 ≤ n
  · have hlog : 2 * r ≤ Real.log n := by
      by_contra hc
      exact hn ⟨h2, not_le.mp hc⟩
    have hpos : 0 ≤ Real.log n := le_trans (by linarith) hlog
    rw [autoCorr_eq_zero_of_support_le hsupp (by rw [abs_of_nonneg hpos]; exact hlog), mul_zero]
  · rw [show RHTower.vonMangoldtAtom n = 0 by simp [RHTower.vonMangoldtAtom, if_neg h2], zero_mul]

/-! ### The net charge of a shift in the ledger -/

/-- **The net charge of a relevant shift is the atom times the autocorrelation.** For an odd test
supported in `[−r, r]` and a shift with `log n ≤ 2r`,
`evenStripGain_n − oddStripCost_n = −2 Λ(n) n^{−1/2} A(log n)`. -/
theorem evenStripGain_sub_oddStripCost_eq (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x) {r : ℝ}
    (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) {n : ℕ} (hn : Real.log n ≤ 2 * r) :
    evenStripGain F r n - oddStripCost F r n
      = -(2 * (RHTower.vonMangoldtAtom n * autoCorr F (Real.log n))) := by
  have h := integral_mul_shift_eq_two_reflectedOdd_sub hF hodd hr (by linarith) hsupp
    (L := Real.log n)
  have hA : autoCorr F (Real.log n)
      = 2 * (∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2)
        - ∫ a in (Real.log n - r)..r, F a ^ 2 := h
  rw [evenStripGain, oddStripCost, hA]
  ring

/-- **The ledger's net prime charge is `−2` times the prime side.** -/
theorem sum_evenStripGain_sub_sum_oddStripCost (hF : Continuous F) (hodd : ∀ x, F (-x) = -F x)
    {r : ℝ} (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    (∑ n ∈ relevantShifts r, evenStripGain F r n)
        - ∑ n ∈ relevantShifts r, oddStripCost F r n
      = -(2 * primeSideCharge F) := by
  rw [← Finset.sum_sub_distrib, primeSideCharge_eq_sum_relevantShifts hr hsupp,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [mem_relevantShifts] at hn
  exact evenStripGain_sub_oddStripCost_eq hF hodd hr hsupp (le_of_lt hn.2)

/-! ### The ledger with the prime powers eliminated -/

/-- **The incidence ledger bounded by prime data alone.** For an odd `F ∈ C²_c` supported in
`[−r, r]`, every plateau radius `R > r` and every finite set `T` of primes containing all primes
below the horizon `e^{2r}`,

    Ẑ(F) ≥ pool + crossing potential + gauge remainder − pole charge
           − 2 Σ_{p ∈ T} log p/(p − 1) · (A(0) + √p · A(log p)).

No prime power appears on the right: the costs of `p², p³, …` are absorbed into the first-power
autocorrelation of their prime by the tower law. The subtracted sum is the first-power prime side
inflated by `p/(p − 1) ≤ 2` plus `A(0) Σ_{p ∈ T} log p/(p − 1)`, of size `aperture × mass`. -/
theorem fullZeroForm_ge_primeOnlyLedger {r R : ℝ} {T : Finset Nat.Primes} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R)
    (hT : ∀ p : Nat.Primes, Real.log (p : ℕ) ≤ 2 * r → p ∈ T) :
    surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F
        + gaugeRemainder (aperturePlateau r R) F - poleCharge F
        - 2 * ∑ p ∈ T, Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)
            * (autoCorr F 0 + Real.sqrt (p : ℕ) * autoCorr F (Real.log (p : ℕ)))
      ≤ fullZeroForm F := by
  have hcont : Continuous F := hF.continuous
  have hledger := fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp hrR
  have hnet := sum_evenStripGain_sub_sum_oddStripCost hcont hodd hr.le hsupp
  have hbd := primeSideCharge_le_sum_primes hcont hr.le hsupp hT
  rw [hledger]
  linarith only [hnet, hbd]

/-! ### The tower is paid by the strip of its first atom -/

/-- **The tower costs no more than its first atom's strip.** For an odd test supported in `[−r, r]`
and a prime `p`, the charge of the whole tower of `p` obeys

    towerCharge p F ≤ log p/(p − 1) · A(0) + p/(p − 1) · Λ(p) p^{−1/2} · ∫_{S_p} F²,

`S_p = [log p − r, r]` the strip of the first atom. The proper prime powers add nothing beyond the
Euler factor `p/(p − 1) ≤ 2` on the first atom's strip mass. -/
theorem towerCharge_le_firstAtomStrip {p : ℕ} {r : ℝ} (hp : p.Prime) (hF : Continuous F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    towerCharge p F
      ≤ Real.log p / ((p : ℝ) - 1) * autoCorr F 0
        + (p : ℝ) / ((p : ℝ) - 1) * RHTower.vonMangoldtAtom p
          * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsp0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hkey := sub_one_mul_towerCharge_le hp hF hr hsupp
  have hstrip : autoCorr F (Real.log p) ≤ ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2 :=
    integral_mul_shift_le_strip hF hFc hodd hsupp
  -- the atom of a prime is `log p/√p`
  have hatom : RHTower.vonMangoldtAtom p = Real.log p / Real.sqrt p := by
    simp only [RHTower.vonMangoldtAtom, if_pos hp.two_le,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hmul : Real.log p * (Real.sqrt p
        * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2)
      = (p : ℝ) * (RHTower.vonMangoldtAtom p
        * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2) := by
    rw [hatom]
    field_simp
    rw [hsq]
    ring
  have hstep : ((p : ℝ) - 1) * towerCharge p F
      ≤ Real.log p * autoCorr F 0
        + (p : ℝ) * (RHTower.vonMangoldtAtom p
          * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2) := by
    rw [← hmul]
    have h1 : Real.log p * (Real.sqrt p * autoCorr F (Real.log p))
        ≤ Real.log p * (Real.sqrt p * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstrip hsp0.le) hlog.le
    calc ((p : ℝ) - 1) * towerCharge p F
        ≤ Real.log p * (autoCorr F 0 + Real.sqrt p * autoCorr F (Real.log p)) := hkey
      _ = Real.log p * autoCorr F 0 + Real.log p * (Real.sqrt p * autoCorr F (Real.log p)) := by
          ring
      _ ≤ Real.log p * autoCorr F 0
            + Real.log p * (Real.sqrt p * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2) := by
          linarith only [h1]
  have hrhs : Real.log p / ((p : ℝ) - 1) * autoCorr F 0
      + (p : ℝ) / ((p : ℝ) - 1) * RHTower.vonMangoldtAtom p
        * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2
      = (Real.log p * autoCorr F 0
          + (p : ℝ) * (RHTower.vonMangoldtAtom p
            * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2)) / ((p : ℝ) - 1) := by
    field_simp
  rw [hrhs, le_div_iff₀ (by linarith)]
  linarith only [hstep]

/-- The same bound in the ledger's own objects: the tower of `p` costs at most half the Euler
inflation of the **even strip gain** of its first atom, plus an archimedean-size term. Mechanism 35
pays that gain from the atom's own strip, so the ledger's allocation over all prime powers reduces
to one over the primes. -/
theorem towerCharge_le_evenStripGain {p : ℕ} {r : ℝ} (hp : p.Prime) (hF : Continuous F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hpr : Real.log p - r ≤ r) :
    towerCharge p F
      ≤ Real.log p / ((p : ℝ) - 1) * autoCorr F 0
        + (p : ℝ) / (2 * ((p : ℝ) - 1)) * evenStripGain F r p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hgain : evenStripGain F r p
      = 2 * RHTower.vonMangoldtAtom p * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2 := by
    rw [evenStripGain, intervalIntegral.integral_of_le hpr,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h := towerCharge_le_firstAtomStrip hp hF hFc hodd hr hsupp
  rw [hgain]
  have hfac : (p : ℝ) / (2 * ((p : ℝ) - 1))
        * (2 * RHTower.vonMangoldtAtom p * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2)
      = (p : ℝ) / ((p : ℝ) - 1) * RHTower.vonMangoldtAtom p
        * ∫ x in Set.Icc (Real.log p - r) r, F x ^ 2 := by
    field_simp
  rw [hfac]
  exact h

end GaloisForLFunctions.ArithmeticIncidencePositivity
