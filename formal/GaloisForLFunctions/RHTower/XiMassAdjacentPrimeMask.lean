import GaloisForLFunctions.RHTower.XiMassAdjacentPrimeDifference
import GaloisForLFunctions.RHTower.XiMassPrimeMaskL1Quotient
import Mathlib.NumberTheory.Bertrand

/-!
# Actual bounded mask for adjacent-prime Xi mass differences

Reverse critical-coefficient normalization makes each even mask coefficient equal to one and each
odd coefficient a neighboring critical-weight quotient. Bertrand's theorem bounds those quotients
by two. This permits unconditional reindexing from the paired adjacent-difference layer back to an
actual bounded mask on the original marked-prime family. The resulting masked layer inherits a
vertical-height-independent bound from the integral Lipschitz theorem.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Nat.Prime

namespace RHTower

noncomputable section

@[simp] theorem nthPrimeEquiv_apply (n : ℕ) :
    nthPrimeEquiv n = nthPrimeSubtype n := rfl

theorem nthPrimeSubtype_succ_le_two_mul (n : ℕ) :
    (nthPrimeSubtype (n + 1) : ℕ) ≤ 2 * (nthPrimeSubtype n : ℕ) := by
  obtain ⟨q, hq, hpq, hq2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (nthPrimeSubtype n : ℕ)
      (nthPrimeSubtype n).prop.pos.ne'
  have hnext : (nthPrimeSubtype (n + 1) : ℕ) ≤ q := by
    by_contra hnot
    have hqnext : q < Nat.nth Nat.Prime (n + 1) := by
      simpa [nthPrimeSubtype] using Nat.lt_of_not_ge hnot
    have hqprev : q ≤ Nat.nth Nat.Prime n :=
      Nat.le_nth_of_lt_nth_succ hqnext hq
    exact (not_le_of_gt hpq) (by simpa [nthPrimeSubtype] using hqprev)
  exact hnext.trans hq2

theorem xiMassPrimePowerCriticalWeight_le_two_succ (n : ℕ) :
    xiMassPrimePowerCriticalWeight (nthPrimeSubtype n) 0 ≤
      2 * xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 := by
  let p : ℝ := (nthPrimeSubtype n : ℕ)
  let q : ℝ := (nthPrimeSubtype (n + 1) : ℕ)
  have hp0 : 0 < p := nthPrimeSubtype_pos n
  have hq0 : 0 < q := nthPrimeSubtype_pos (n + 1)
  have hpq : p ≤ q := by
    have hnat : (nthPrimeSubtype n : ℕ) ≤
        (nthPrimeSubtype (n + 1) : ℕ) :=
      nthPrimeSubtype_strictMono.monotone (Nat.le_succ n)
    change ((nthPrimeSubtype n : ℕ) : ℝ) ≤
      ((nthPrimeSubtype (n + 1) : ℕ) : ℝ)
    exact_mod_cast hnat
  have hq2p : q ≤ 2 * p := by
    have hnat := nthPrimeSubtype_succ_le_two_mul n
    change ((nthPrimeSubtype (n + 1) : ℕ) : ℝ) ≤
      2 * ((nthPrimeSubtype n : ℕ) : ℝ)
    exact_mod_cast hnat
  have hsqrt : Real.sqrt q ≤ 2 * Real.sqrt p := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsqp := Real.sq_sqrt hp0.le
      nlinarith
  have hinv : p ^ (-(1 / 2 : ℝ)) ≤ 2 * q ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hp0.le, Real.rpow_neg hq0.le]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have hdiv : 1 / Real.sqrt p ≤ 2 / Real.sqrt q :=
      (div_le_div_iff₀ (Real.sqrt_pos.2 hp0) (Real.sqrt_pos.2 hq0)).2 (by
        simpa using hsqrt)
    simpa [div_eq_mul_inv] using hdiv
  have hlog : Real.log p ≤ Real.log q :=
    Real.strictMonoOn_log.monotoneOn hp0 hq0 hpq
  have hp1 : 1 ≤ p := by
    have hnat : 1 ≤ (nthPrimeSubtype n : ℕ) := (nthPrimeSubtype n).prop.one_le
    change (1 : ℝ) ≤ ((nthPrimeSubtype n : ℕ) : ℝ)
    exact_mod_cast hnat
  rw [xiMassPrimePowerCriticalWeight_eq,
    xiMassPrimePowerCriticalWeight_eq]
  norm_num
  change Real.log p * p ^ (-(1 / 2 : ℝ)) ≤
    2 * (Real.log q * q ^ (-(1 / 2 : ℝ)))
  calc
    Real.log p * p ^ (-(1 / 2 : ℝ)) ≤
        Real.log q * p ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    _ ≤ Real.log q * (2 * q ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hinv (Real.log_nonneg (hp1.trans hpq))
    _ = 2 * (Real.log q * q ^ (-(1 / 2 : ℝ))) := by ring

theorem norm_xiMassNthPrimeCriticalCoefficient_div_succ_le_two (n : ℕ) :
    ‖xiMassNthPrimeCriticalCoefficient n /
        xiMassNthPrimeCriticalCoefficient (n + 1)‖ ≤ 2 := by
  have hnum : ‖xiMassNthPrimeCriticalCoefficient n‖ =
      xiMassPrimePowerCriticalWeight (nthPrimeSubtype n) 0 := by
    rw [xiMassNthPrimeCriticalCoefficient, xiMassPrimePowerCriticalWeight, pow_one]
  have hden : ‖xiMassNthPrimeCriticalCoefficient (n + 1)‖ =
      xiMassPrimePowerCriticalWeight (nthPrimeSubtype (n + 1)) 0 := by
    rw [xiMassNthPrimeCriticalCoefficient, xiMassPrimePowerCriticalWeight, pow_one]
  have hdenpos : 0 < ‖xiMassNthPrimeCriticalCoefficient (n + 1)‖ :=
    norm_pos_iff.mpr (by
      simpa [xiMassNthPrimeCriticalCoefficient] using
        xiMassPrimeCriticalTerm_ne_zero (nthPrimeSubtype (n + 1)))
  rw [norm_div, hnum, hden]
  apply (div_le_iff₀ (by simpa [hden] using hdenpos)).2
  simpa [mul_comm] using xiMassPrimePowerCriticalWeight_le_two_succ n

def xiMassUnitAdjacentPrimeAtom (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  xiMassCenteredPrimeAtom a τ (nthPrimeSubtype (2 * n) : ℕ) -
    (xiMassNthPrimeCriticalCoefficient (2 * n) /
      xiMassNthPrimeCriticalCoefficient (2 * n + 1)) *
      xiMassCenteredPrimeAtom a τ (nthPrimeSubtype (2 * n + 1) : ℕ)

theorem xiMassUnitAdjacentPrimeAtom_eq (a : ℝ) (τ : ℂ) (n : ℕ) :
    xiMassUnitAdjacentPrimeAtom a τ n =
      (xiMassNthPrimeCriticalCoefficient (2 * n) /
        xiMassNthPrimeCriticalCoefficient (2 * n + 1)) *
        xiMassBalancedAdjacentPrimeAtom a τ n := by
  unfold xiMassUnitAdjacentPrimeAtom xiMassBalancedAdjacentPrimeAtom
  have heven : xiMassNthPrimeCriticalCoefficient (2 * n) ≠ 0 := by
    simpa [xiMassNthPrimeCriticalCoefficient] using
      xiMassPrimeCriticalTerm_ne_zero (nthPrimeSubtype (2 * n))
  have hodd : xiMassNthPrimeCriticalCoefficient (2 * n + 1) ≠ 0 := by
    simpa [xiMassNthPrimeCriticalCoefficient] using
      xiMassPrimeCriticalTerm_ne_zero (nthPrimeSubtype (2 * n + 1))
  rw [mul_sub, ← mul_assoc, div_mul_div_cancel₀ hodd, div_self heven, one_mul]

def xiMassUnitAdjacentPrimeIndexMask (m : ℕ) : ℂ :=
  if m % 2 = 0 then 1 else
    -(xiMassNthPrimeCriticalCoefficient (m - 1) /
      xiMassNthPrimeCriticalCoefficient m)

def xiMassUnitAdjacentPrimeMask (p : Nat.Primes) : ℂ :=
  xiMassUnitAdjacentPrimeIndexMask (nthPrimeEquiv.symm p)

@[simp] theorem xiMassUnitAdjacentPrimeIndexMask_even (n : ℕ) :
    xiMassUnitAdjacentPrimeIndexMask (2 * n) = 1 := by
  simp [xiMassUnitAdjacentPrimeIndexMask]

@[simp] theorem xiMassUnitAdjacentPrimeIndexMask_odd (n : ℕ) :
    xiMassUnitAdjacentPrimeIndexMask (2 * n + 1) =
      -(xiMassNthPrimeCriticalCoefficient (2 * n) /
        xiMassNthPrimeCriticalCoefficient (2 * n + 1)) := by
  simp [xiMassUnitAdjacentPrimeIndexMask]

@[simp] theorem xiMassUnitAdjacentPrimeMask_even (n : ℕ) :
    xiMassUnitAdjacentPrimeMask (nthPrimeSubtype (2 * n)) = 1 := by
  unfold xiMassUnitAdjacentPrimeMask
  rw [show nthPrimeSubtype (2 * n) = nthPrimeEquiv (2 * n) by rfl]
  rw [nthPrimeEquiv.symm_apply_apply]
  exact xiMassUnitAdjacentPrimeIndexMask_even n

@[simp] theorem xiMassUnitAdjacentPrimeMask_odd (n : ℕ) :
    xiMassUnitAdjacentPrimeMask (nthPrimeSubtype (2 * n + 1)) =
      -(xiMassNthPrimeCriticalCoefficient (2 * n) /
        xiMassNthPrimeCriticalCoefficient (2 * n + 1)) := by
  unfold xiMassUnitAdjacentPrimeMask
  rw [show nthPrimeSubtype (2 * n + 1) = nthPrimeEquiv (2 * n + 1) by rfl]
  rw [nthPrimeEquiv.symm_apply_apply]
  exact xiMassUnitAdjacentPrimeIndexMask_odd n

@[simp] theorem xiMassUnitAdjacentPrimeMask_equiv_even (n : ℕ) :
    xiMassUnitAdjacentPrimeMask (nthPrimeEquiv (2 * n)) = 1 := by
  change xiMassUnitAdjacentPrimeMask (nthPrimeSubtype (2 * n)) = 1
  exact xiMassUnitAdjacentPrimeMask_even n

@[simp] theorem xiMassUnitAdjacentPrimeMask_equiv_odd (n : ℕ) :
    xiMassUnitAdjacentPrimeMask (nthPrimeEquiv (2 * n + 1)) =
      -(xiMassNthPrimeCriticalCoefficient (2 * n) /
        xiMassNthPrimeCriticalCoefficient (2 * n + 1)) := by
  change xiMassUnitAdjacentPrimeMask (nthPrimeSubtype (2 * n + 1)) = _
  exact xiMassUnitAdjacentPrimeMask_odd n

theorem norm_xiMassUnitAdjacentPrimeIndexMask_le_two (m : ℕ) :
    ‖xiMassUnitAdjacentPrimeIndexMask m‖ ≤ 2 := by
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · simp [xiMassUnitAdjacentPrimeIndexMask, hm]
  · have hrepr : m = 2 * (m / 2) + 1 := by omega
    rw [hrepr, xiMassUnitAdjacentPrimeIndexMask_odd, norm_neg]
    simpa [Nat.mul_div_cancel_left] using
      norm_xiMassNthPrimeCriticalCoefficient_div_succ_le_two (2 * (m / 2))

theorem norm_xiMassUnitAdjacentPrimeMask_le_two (p : Nat.Primes) :
    ‖xiMassUnitAdjacentPrimeMask p‖ ≤ 2 :=
  norm_xiMassUnitAdjacentPrimeIndexMask_le_two _

theorem summable_xiMassUnitAdjacentPrimeMaskedAtom
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun p : Nat.Primes =>
      xiMassUnitAdjacentPrimeMask p *
        xiMassCenteredPrimeAtom a τ (p : ℕ)) := by
  have hbase := summable_xiMassValuationOnePrimeAtom hhalf hda hτ
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖xiMassCenteredPrimeAtom a τ (p : ℕ)‖) := summable_norm_iff.mpr hbase
  apply summable_norm_iff.mp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_xiMassUnitAdjacentPrimeMask_le_two p) (norm_nonneg _))
    (hnorm.mul_left 2)

theorem norm_xiMassUnitAdjacentPrimeAtom_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) (n : ℕ) :
    ‖xiMassUnitAdjacentPrimeAtom a ((σ : ℂ) + u * I) n‖ ≤
      32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotentialGap n := by
  rw [xiMassUnitAdjacentPrimeAtom_eq, norm_mul]
  have hratio :=
    norm_xiMassNthPrimeCriticalCoefficient_div_succ_le_two (2 * n)
  have hold := norm_xiMassBalancedAdjacentPrimeAtom_vertical_le ha hσ u n
  calc
    ‖xiMassNthPrimeCriticalCoefficient (2 * n) /
          xiMassNthPrimeCriticalCoefficient (2 * n + 1)‖ *
        ‖xiMassBalancedAdjacentPrimeAtom a ((σ : ℂ) + ↑u * I) n‖ ≤
      2 * (16 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotentialGap n) :=
      mul_le_mul hratio hold (norm_nonneg _) (by norm_num)
    _ = 32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotentialGap n := by ring

theorem summable_norm_xiMassUnitAdjacentPrimeAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun n : ℕ =>
      ‖xiMassUnitAdjacentPrimeAtom a ((σ : ℂ) + u * I) n‖) := by
  let C : ℝ := 32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))
  have hmajor : Summable (fun n : ℕ => C * xiMassAdjacentPrimePotentialGap n) :=
    summable_xiMassAdjacentPrimePotentialGap.mul_left C
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa [C] using
      norm_xiMassUnitAdjacentPrimeAtom_vertical_le ha hσ u n)
    hmajor

theorem summable_xiMassUnitAdjacentPrimeAtom
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    Summable (fun n : ℕ =>
      xiMassUnitAdjacentPrimeAtom a ((σ : ℂ) + u * I) n) :=
  summable_norm_iff.mp
    (summable_norm_xiMassUnitAdjacentPrimeAtom ha hσ u)

def xiMassUnitAdjacentPrimeLayer (a : ℝ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, xiMassUnitAdjacentPrimeAtom a τ n

theorem norm_xiMassUnitAdjacentPrimeLayer_vertical_le
    {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) (u : ℝ) :
    ‖xiMassUnitAdjacentPrimeLayer a ((σ : ℂ) + u * I)‖ ≤
      32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotential 0 := by
  let C : ℝ := 32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|)))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (integral_nonneg fun _ => by positivity)
  have hnorm := summable_norm_xiMassUnitAdjacentPrimeAtom ha hσ u
  have hmajor : Summable (fun n : ℕ => C * xiMassAdjacentPrimePotentialGap n) :=
    summable_xiMassAdjacentPrimePotentialGap.mul_left C
  calc
    ‖xiMassUnitAdjacentPrimeLayer a ((σ : ℂ) + u * I)‖ ≤
        ∑' n : ℕ, ‖xiMassUnitAdjacentPrimeAtom
          a ((σ : ℂ) + u * I) n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, C * xiMassAdjacentPrimePotentialGap n :=
      Summable.tsum_le_tsum
        (fun n => by simpa [C] using
          norm_xiMassUnitAdjacentPrimeAtom_vertical_le ha hσ u n)
        hnorm hmajor
    _ = C * (∑' n : ℕ, xiMassAdjacentPrimePotentialGap n) := tsum_mul_left
    _ ≤ C * xiMassAdjacentPrimePotential 0 :=
      mul_le_mul_of_nonneg_left tsum_xiMassAdjacentPrimePotentialGap_le hC
    _ = 32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
        xiMassAdjacentPrimePotential 0 := rfl

theorem xiMassPrimeMaskedLayer_unitAdjacent_eq
    {a d : ℝ} (hhalf : 1 / 2 < d) (hda : d < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    xiMassPrimeMaskedLayer xiMassUnitAdjacentPrimeMask a τ =
      xiMassUnitAdjacentPrimeLayer a τ := by
  let f : Nat.Primes → ℂ := fun p =>
    xiMassUnitAdjacentPrimeMask p *
      xiMassCenteredPrimeAtom a τ (p : ℕ)
  have hf : Summable f :=
    summable_xiMassUnitAdjacentPrimeMaskedAtom hhalf hda hτ
  have hn : Summable (f ∘ nthPrimeEquiv) :=
    nthPrimeEquiv.summable_iff.mpr hf
  have hprod : Summable ((f ∘ nthPrimeEquiv) ∘ (Nat.divModEquiv 2).symm) :=
    (Nat.divModEquiv 2).symm.summable_iff.mpr hn
  unfold xiMassPrimeMaskedLayer xiMassUnitAdjacentPrimeLayer
  change (∑' p : Nat.Primes, f p) = _
  rw [← nthPrimeEquiv.tsum_eq f]
  change (∑' n : ℕ, (f ∘ nthPrimeEquiv) n) = _
  rw [← (Nat.divModEquiv 2).symm.tsum_eq (f ∘ nthPrimeEquiv)]
  change (∑' p : ℕ × Fin 2,
    ((f ∘ nthPrimeEquiv) ∘ (Nat.divModEquiv 2).symm) p) = _
  rw [hprod.tsum_prod]
  apply tsum_congr
  intro n
  rw [tsum_fintype, Fin.sum_univ_two]
  simp only [Function.comp_apply, Nat.divModEquiv_symm_apply, Fin.isValue,
    Fin.val_zero, Nat.add_zero, Fin.val_one, f]
  rw [show n * 2 = 2 * n by omega]
  rw [xiMassUnitAdjacentPrimeMask_equiv_even,
    xiMassUnitAdjacentPrimeMask_equiv_odd]
  rw [nthPrimeEquiv_apply, nthPrimeEquiv_apply]
  unfold xiMassUnitAdjacentPrimeAtom
  ring

theorem xiMassUnitAdjacentPrimeMask_lineBound
    {a d σ : ℝ} (hhalf : 1 / 2 < d) (hda : d < a) (hσ : 0 < σ) :
    XiMassPrimeMaskedLineBound xiMassUnitAdjacentPrimeMask a σ := by
  have ha : 0 < a := by linarith
  refine ⟨32 * (∫ x : ℝ, |x| * Real.exp (-(σ * |x|))) *
      xiMassAdjacentPrimePotential 0, fun u => ?_⟩
  rw [xiMassPrimeMaskedLayer_unitAdjacent_eq hhalf hda
    (τ := ((σ : ℂ) + u * I)) (by simpa using hσ)]
  exact norm_xiMassUnitAdjacentPrimeLayer_vertical_le ha hσ u

end

end RHTower
