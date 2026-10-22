import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerEulerEnvelope

/-!
# The Liouville-twisted tower law: the mechanism reads the sign of the arithmetic

The tower law holds for every ratio with `|z| < 1`, signed ratios included. Taking the **negative**
ratio `z = −p^{−1/2}` turns the geometric tower of a prime into its Liouville twin: the weights
become `λ(p^k) Λ(p^k) p^{−k/2}` with `λ(p^k) = (−1)^k`, the completely multiplicative sign that
replaces the primes' arithmetic by its parity. The law reads

    (p − 1) · C⁻_p(F) ≤ log p · (A(0) − √p · A(log p)),

against the untwisted

    (p − 1) · C_p(F) ≤ log p · (A(0) + √p · A(log p)).

So the two bounds differ by `2 log p √p A(log p)`: wherever the first power is positively charged —
the resonant regime, where the untwisted tower is expensive — the Liouville twin is *strictly
cheaper*, and where it is negatively charged the twin is the expensive one. The envelope therefore
distinguishes the primes from their parity twin at the first power, which is the selectivity audit
the theory asks of every positivity statement: the mechanism is not a formal consequence of
geometric decay, it sees the sign of `A(log p)`.
-/

open MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- The Liouville-twisted tower charge `C⁻_p(F) = Σ_{k ≥ 1} (−1)^k Λ(p^k) p^{−k/2} A(k log p)`:
the tower charge of `p` with the Liouville sign on every power. -/
def twistedTowerCharge (p : ℕ) (F : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, (-1) ^ (k + 1) * RHTower.vonMangoldtAtom (p ^ (k + 1))
    * autoCorr F (((k : ℝ) + 1) * Real.log p)

/-- The twisted tower charge is `log p` times the geometric lag charge at the **negative** ratio
`z = −p^{−1/2}`. -/
theorem twistedTowerCharge_eq_log_mul_geoLagCharge {p : ℕ} (hp : p.Prime) (F : ℝ → ℝ) :
    twistedTowerCharge p F
      = Real.log p * geoLagCharge (-(1 / Real.sqrt p)) (Real.log p) F := by
  rw [twistedTowerCharge, geoLagCharge, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [vonMangoldtAtom_prime_pow hp, neg_pow]
  ring

/-- **The Liouville-twisted tower law.** For every continuous test supported in `[−B, B]` and every
prime `p`,

    (p − 1) · C⁻_p(F) ≤ log p · (A(0) − √p · A(log p)).

The sign of the first-power charge enters with the opposite sign to the untwisted law: the parity
twin of a resonant tower is cheaper than the tower itself. -/
theorem sub_one_mul_twistedTowerCharge_le {p : ℕ} {B : ℝ} (hp : p.Prime) (hF : Continuous F)
    (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) :
    ((p : ℝ) - 1) * twistedTowerCharge p F
      ≤ Real.log p * (autoCorr F 0 - Real.sqrt p * autoCorr F (Real.log p)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hsp1 : 1 < Real.sqrt p := by
    have h := Real.sqrt_lt_sqrt zero_le_one hp1
    simpa using h
  have hsp0 : 0 < Real.sqrt p := by linarith
  have hsq : Real.sqrt p ^ 2 = (p : ℝ) := Real.sq_sqrt hp0.le
  have hz0 : 0 < 1 / Real.sqrt p := by positivity
  have hz1 : 1 / Real.sqrt p < 1 := by rw [div_lt_one hsp0]; exact hsp1
  have hlog : 0 < Real.log p := Real.log_pos hp1
  -- the law at the negative ratio
  have key := one_sub_sq_mul_geoLagCharge_le hF hB hsupp
    (z := -(1 / Real.sqrt p)) (by rw [abs_neg, abs_of_pos hz0]; exact hz1) hlog
  have hz2 : (-(1 / Real.sqrt p)) ^ 2 = 1 / (p : ℝ) := by
    rw [neg_pow, div_pow, one_pow, hsq]
    norm_num
  rw [hz2] at key
  have hps : (p : ℝ) / Real.sqrt p = Real.sqrt p := by
    field_simp
    linear_combination -hsq
  have hT : ((p : ℝ) - 1) * geoLagCharge (-(1 / Real.sqrt p)) (Real.log p) F
      ≤ autoCorr F 0 - Real.sqrt p * autoCorr F (Real.log p) := by
    have h := mul_le_mul_of_nonneg_left key hp0.le
    have e1 : (p : ℝ) * ((1 - 1 / (p : ℝ))
          * geoLagCharge (-(1 / Real.sqrt p)) (Real.log p) F)
        = ((p : ℝ) - 1) * geoLagCharge (-(1 / Real.sqrt p)) (Real.log p) F := by
      field_simp
    have hpne : (p : ℝ) ≠ 0 := hp0.ne'
    have hspne : Real.sqrt p ≠ 0 := hsp0.ne'
    have e2 : (p : ℝ) * (1 / (p : ℝ) * autoCorr F 0
          + -(1 / Real.sqrt p) * autoCorr F (Real.log p))
        = autoCorr F 0 - ((p : ℝ) / Real.sqrt p) * autoCorr F (Real.log p) := by
      rw [mul_add, ← mul_assoc, mul_one_div, div_self hpne, one_mul,
        show (p : ℝ) * (-(1 / Real.sqrt p) * autoCorr F (Real.log p))
            = -(((p : ℝ) / Real.sqrt p) * autoCorr F (Real.log p)) by
          rw [div_eq_mul_inv]; ring]
      ring
    rw [hps] at e2
    rw [e1, e2] at h
    exact h
  calc ((p : ℝ) - 1) * twistedTowerCharge p F
      = Real.log p
          * (((p : ℝ) - 1) * geoLagCharge (-(1 / Real.sqrt p)) (Real.log p) F) := by
        rw [twistedTowerCharge_eq_log_mul_geoLagCharge hp]; ring
    _ ≤ Real.log p * (autoCorr F 0 - Real.sqrt p * autoCorr F (Real.log p)) :=
        mul_le_mul_of_nonneg_left hT hlog.le

/-- **A resonant tower's parity twin is paid by the mass alone.** If the first power of `p` is
nonnegatively charged — the regime in which the untwisted tower is expensive — the Liouville-twisted
tower charge is bounded by `log p · A(0)/(p − 1)` with no resonance term at all. The two laws
therefore separate the primes from their parity model exactly at the sign of `A(log p)`. -/
theorem sub_one_mul_twistedTowerCharge_le_mass {p : ℕ} {B : ℝ} (hp : p.Prime) (hF : Continuous F)
    (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) (hres : 0 ≤ autoCorr F (Real.log p)) :
    ((p : ℝ) - 1) * twistedTowerCharge p F ≤ Real.log p * autoCorr F 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have key := sub_one_mul_twistedTowerCharge_le hp hF hB hsupp
  have hdrop : Real.log p * (autoCorr F 0 - Real.sqrt p * autoCorr F (Real.log p))
      ≤ Real.log p * autoCorr F 0 := by
    have : 0 ≤ Real.sqrt p * autoCorr F (Real.log p) := mul_nonneg hsp hres
    exact mul_le_mul_of_nonneg_left (by linarith) hlog.le
  exact le_trans key hdrop

end GaloisForLFunctions.ArithmeticIncidencePositivity
