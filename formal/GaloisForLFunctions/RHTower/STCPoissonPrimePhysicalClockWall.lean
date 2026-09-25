import GaloisForLFunctions.RHTower.PrimeLogTripleCluster
import GaloisForLFunctions.RHTower.PoissonScaleHistoryFrame

/-!
# Physical-clock domain wall of the full-aperture prime Poisson kernel

The depth-zero prime source, aggregated over every positive Poisson aperture,
has kernel `4 log(p) log(q) / (sqrt(pq) (log(p)+log(q))²)`. For each fixed
prime `q`, multiplication of its `q`-column by the physical clock `log(p)`
has divergent square energy. This is the concrete basis-vector domain
obstruction behind the all-prime STC transport problem. No Xi-zero or RH
assumption is used.
-/

namespace RHTower

/-- Physical prime clock. -/
noncomputable def stcClock (p : Nat.Primes) : ℝ := Real.log (p : ℝ)

private theorem stcClock_pos (p : Nat.Primes) : 0 < stcClock p := by
  unfold stcClock
  exact Real.log_pos (by exact_mod_cast p.prop.one_lt)

/-- Square energy of the `q`-column after physical-clock multiplication. -/
noncomputable def stcPhysicalColumnEnergy (q p : Nat.Primes) : ℝ :=
  (16 * (stcClock q)^2 / (q : ℝ)) *
    (stcClock p / (stcClock p + stcClock q))^4 / (p : ℝ)

private theorem stcClock_ratio_lower (q p : Nat.Primes) :
    Real.log 2 / (Real.log 2 + stcClock q) ≤
      stcClock p / (stcClock p + stcClock q) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hplog : Real.log 2 ≤ stcClock p := by
    unfold stcClock
    exact Real.log_le_log (by norm_num) hp2
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < stcClock q := stcClock_pos q
  apply (div_le_div_iff₀ (add_pos ha hb) (add_pos (stcClock_pos p) hb)).2
  nlinarith

private theorem stcPhysicalColumnEnergy_lower (q p : Nat.Primes) :
    ((16 * (stcClock q)^2 / (q : ℝ)) *
      (Real.log 2 / (Real.log 2 + stcClock q))^4) * (1 / (p : ℝ)) ≤
        stcPhysicalColumnEnergy q p := by
  have hq : 0 ≤ 16 * (stcClock q)^2 / (q : ℝ) := by positivity
  have hratio := stcClock_ratio_lower q p
  have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < stcClock q := stcClock_pos q
  have hrnn : 0 ≤ Real.log 2 / (Real.log 2 + stcClock q) :=
    div_nonneg ha.le (add_pos ha hb).le
  have hpow := pow_le_pow_left₀ hrnn hratio 4
  unfold stcPhysicalColumnEnergy
  have hp : 0 ≤ (1 / (p : ℝ)) := by positivity
  calc
    (16 * (stcClock q)^2 / (q : ℝ)) *
        (Real.log 2 / (Real.log 2 + stcClock q))^4 * (1 / (p : ℝ))
      ≤ (16 * (stcClock q)^2 / (q : ℝ)) *
          (stcClock p / (stcClock p + stcClock q))^4 * (1 / (p : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hq) hp
    _ = _ := by ring

/-- Every fixed source column fails the physical prime-clock graph norm. -/
theorem not_summable_stcPhysicalColumnEnergy (q : Nat.Primes) :
    ¬ Summable (stcPhysicalColumnEnergy q) := by
  let c : ℝ := (16 * (stcClock q)^2 / (q : ℝ)) *
    (Real.log 2 / (Real.log 2 + stcClock q))^4
  have hcpos : 0 < c := by
    dsimp [c]
    have hq : 0 < stcClock q := stcClock_pos q
    have ha : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hqr : 0 < (q : ℝ) := by exact_mod_cast q.prop.pos
    positivity
  intro hsum
  have hsmall : Summable (fun p : Nat.Primes => c * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      exact stcPhysicalColumnEnergy_lower q p
    · exact hsum
  have hrecip : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) :=
    (summable_mul_left_iff hcpos.ne').mp hsmall
  exact Nat.Primes.not_summable_one_div hrecip

/-- Positive all-aperture prime Poisson Gram coefficient. -/
noncomputable def stcPrimePoissonKernel (p q : Nat.Primes) : ℝ :=
  4 * stcClock p * stcClock q /
    (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) * (stcClock p + stcClock q)^2)

/-- The rational prime kernel is exactly the normalized full Poisson-history Gram. -/
theorem stcPrimePoissonKernel_eq_historyGram (p q : Nat.Primes) :
    stcPrimePoissonKernel p q =
      poissonScaleHistoryGram (stcClock p) (stcClock q) /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)) := by
  rw [poissonScaleHistoryGram_eq (stcClock_pos p) (stcClock_pos q)]
  unfold stcPrimePoissonKernel
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem stcPrimePoissonKernel_physical_energy (q p : Nat.Primes) :
    (stcClock p * stcPrimePoissonKernel p q)^2 =
      stcPhysicalColumnEnergy q p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hq : 0 < (q : ℝ) := by exact_mod_cast q.prop.pos
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hp
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hq
  have hs : 0 < stcClock p + stcClock q := add_pos (stcClock_pos p) (stcClock_pos q)
  have hsqp : (Real.sqrt (p : ℝ))^2 = (p : ℝ) := Real.sq_sqrt hp.le
  have hsqq : (Real.sqrt (q : ℝ))^2 = (q : ℝ) := Real.sq_sqrt hq.le
  unfold stcPrimePoissonKernel stcPhysicalColumnEnergy
  field_simp
  rw [hsqp, hsqq]
  ring

theorem stcPrimePoissonKernel_physical_column_not_summable (q : Nat.Primes) :
    ¬ Summable (fun p : Nat.Primes =>
      (stcClock p * stcPrimePoissonKernel p q)^2) := by
  intro h
  apply not_summable_stcPhysicalColumnEnergy q
  exact h.congr (fun p => (stcPrimePoissonKernel_physical_energy q p))

end RHTower
