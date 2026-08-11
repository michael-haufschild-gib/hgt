import GaloisForLFunctions.RHTower.CriticalHalfDensityPrimeTailResolventLaw

/-!
# The critical prime source carrier is the ideal just above Hilbert–Schmidt

At critical half density the two diagonal source families on the prime-power incidence space
`(p, k)` (the pair `(p, k)` labelling the prime power `p ^ (k+1)`) are

`A e_{p,k} = 1 / ((k+1) √(p^{k+1}))`,   `DA e_{p,k} = log p / √(p^{k+1})`.

Both are `q`-summable exactly when `q > 2`.  Consequently the critical carrier is the concrete
Fréchet ideal `⋂_{q > 2} S_q`: the source is not an absent operator, but it is not
Hilbert–Schmidt either.  The convergence half compares each incidence atom with the ordinary
integer it labels; the divergence half needs only the depth-one subseries and Euler's divergence
of `Σ_p 1/p`.

The same file records the two elementary facts behind the operator-norm exhaustion of the source:
the shifted von Mangoldt coefficients vanish at infinity for every positive shift, and the
logarithmic profile `t ↦ log t · t^{-σ}` is antitone beyond `exp (1/σ)`.
-/

open Filter Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Elementary bounds on the two critical source weights -/

theorem criticalMellinAtomWeight_nonneg' (k : ℕ) : 0 ≤ criticalMellinAtomWeight k :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) ArithmeticFunction.vonMangoldt_nonneg

/-- The square-root von Mangoldt mass is bounded by the logarithmic half-density profile. -/
theorem criticalMellinAtomWeight_le_log (k : ℕ) :
    criticalMellinAtomWeight k ≤ Real.log k * (k : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [criticalMellinAtomWeight, mul_comm]
  exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
    (Real.rpow_nonneg (by positivity) _)

/-- The divided-logarithm source weight is bounded by the pure half-density profile. -/
theorem criticalPrimeTailAtomWeight_le (n : DeningerPrimePowerIndex) :
    criticalPrimeTailAtomWeight n ≤ ((n : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
  have hlogpos : 0 < deningerPrimePowerTime n := deningerPrimePowerTime_pos n
  have hnum : criticalMellinAtomWeight (n : ℕ) ≤
      deningerPrimePowerTime n * ((n : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [deningerPrimePowerTime]
    exact criticalMellinAtomWeight_le_log (n : ℕ)
  rw [criticalPrimeTailAtomWeight, div_le_iff₀ hlogpos]
  linarith

/-! ## The prime-power incidence space -/

/-- The ordinary integer labelled by an incidence coordinate: `(p, k)` labels `p ^ (k+1)`. -/
def criticalIncidenceIndex (pk : Nat.Primes × ℕ) : ℕ :=
  ((deningerEulerPrimePowerIndex pk : DeningerPrimePowerIndex) : ℕ)

theorem criticalIncidenceIndex_injective : Function.Injective criticalIncidenceIndex := by
  intro x y h
  exact deningerEulerPrimePowerIndex_injective (Subtype.ext h)

theorem two_le_criticalIncidenceIndex (pk : Nat.Primes × ℕ) : 2 ≤ criticalIncidenceIndex pk :=
  (deningerEulerPrimePowerIndex pk).property

theorem one_le_criticalIncidenceIndex_real (pk : Nat.Primes × ℕ) :
    (1 : ℝ) ≤ (criticalIncidenceIndex pk : ℝ) := by
  have := two_le_criticalIncidenceIndex pk
  exact_mod_cast Nat.one_le_of_lt (lt_of_lt_of_le Nat.one_lt_two this)

theorem criticalIncidenceIndex_prime (p : Nat.Primes) :
    criticalIncidenceIndex (p, 0) = (p : ℕ) := by
  simp [criticalIncidenceIndex, deningerEulerPrimePowerIndex]

/-- Diagonal coefficient of the critical half-density source operator. -/
def criticalIncidenceDiagonal (pk : Nat.Primes × ℕ) : ℝ :=
  criticalPrimeTailAtomWeight (deningerEulerPrimePowerIndex pk)

/-- Diagonal coefficient of the logarithmically weighted critical source operator. -/
def criticalIncidenceLogDiagonal (pk : Nat.Primes × ℕ) : ℝ :=
  criticalMellinAtomWeight (criticalIncidenceIndex pk)

theorem criticalIncidenceDiagonal_nonneg (pk : Nat.Primes × ℕ) :
    0 ≤ criticalIncidenceDiagonal pk :=
  criticalPrimeTailAtomWeight_nonneg _

theorem criticalIncidenceLogDiagonal_nonneg (pk : Nat.Primes × ℕ) :
    0 ≤ criticalIncidenceLogDiagonal pk :=
  criticalMellinAtomWeight_nonneg' _

theorem criticalIncidenceDiagonal_le (pk : Nat.Primes × ℕ) :
    criticalIncidenceDiagonal pk ≤ (criticalIncidenceIndex pk : ℝ) ^ (-1 / 2 : ℝ) :=
  criticalPrimeTailAtomWeight_le _

theorem criticalIncidenceLogDiagonal_le (pk : Nat.Primes × ℕ) :
    criticalIncidenceLogDiagonal pk ≤
      Real.log (criticalIncidenceIndex pk) * (criticalIncidenceIndex pk : ℝ) ^ (-1 / 2 : ℝ) :=
  criticalMellinAtomWeight_le_log _

/-- At depth one the source diagonal is the exact half-density prime weight. -/
theorem criticalIncidenceDiagonal_depth_one (p : Nat.Primes) :
    criticalIncidenceDiagonal (p, 0) = ((p : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
  have hprime : (p : ℕ).Prime := p.property
  have hlog : Real.log ((p : ℕ) : ℝ) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hprime.two_le
    have : (0 : ℝ) < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by linarith)
    exact ne_of_gt this
  have hmang : ArithmeticFunction.vonMangoldt (criticalIncidenceIndex (p, 0)) =
      Real.log ((p : ℕ) : ℝ) := by
    rw [criticalIncidenceIndex_prime]
    exact ArithmeticFunction.vonMangoldt_apply_prime hprime
  have htime : deningerPrimePowerTime (deningerEulerPrimePowerIndex (p, 0)) =
      Real.log ((p : ℕ) : ℝ) := by
    rw [deningerPrimePowerTime]
    congr 1
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (criticalIncidenceIndex_prime p)
  have hidx : ((deningerEulerPrimePowerIndex (p, 0) : DeningerPrimePowerIndex) : ℕ) = (p : ℕ) :=
    criticalIncidenceIndex_prime p
  rw [criticalIncidenceDiagonal, criticalPrimeTailAtomWeight, criticalMellinAtomWeight,
    htime, hidx]
  rw [show ArithmeticFunction.vonMangoldt ((p : ℕ)) = Real.log ((p : ℕ) : ℝ) from
    ArithmeticFunction.vonMangoldt_apply_prime hprime]
  field_simp

/-- At depth one the logarithmic source diagonal is `log p / √p`. -/
theorem criticalIncidenceLogDiagonal_depth_one (p : Nat.Primes) :
    criticalIncidenceLogDiagonal (p, 0) =
      Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
  have hprime : (p : ℕ).Prime := p.property
  rw [criticalIncidenceLogDiagonal, criticalIncidenceIndex_prime, criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_apply_prime hprime, mul_comm]

/-! ## The depth-one injection and Euler divergence -/

theorem depthOne_injective :
    Function.Injective (fun p : Nat.Primes => ((p, 0) : Nat.Primes × ℕ)) := by
  intro p q h
  exact (Prod.mk.injEq _ _ _ _ ▸ h).1

theorem not_summable_one_div_primes :
    ¬ Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ)) := by
  intro h
  exact not_summable_one_div_on_primes (summable_subtype_iff_indicator.mp h)

/-- Comparison test producing Euler's divergence from any dominating positive prime family. -/
theorem not_summable_of_one_div_le
    {f : Nat.Primes → ℝ} (hf : ∀ p : Nat.Primes, 1 / ((p : ℕ) : ℝ) ≤ f p) :
    ¬ Summable f := by
  intro h
  exact not_summable_one_div_primes
    (Summable.of_nonneg_of_le (fun p => by positivity) hf h)

/-! ## The Schatten characterization -/

theorem summable_criticalIncidenceDiagonal_rpow {q : ℝ} (hq : 2 < q) :
    Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceDiagonal pk ^ q) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-q / 2)) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hcomp := hbase.comp_injective criticalIncidenceIndex_injective
  refine Summable.of_nonneg_of_le
    (fun pk => Real.rpow_nonneg (criticalIncidenceDiagonal_nonneg pk) q) ?_ hcomp
  intro pk
  have hidx : (0 : ℝ) ≤ (criticalIncidenceIndex pk : ℝ) := by positivity
  calc criticalIncidenceDiagonal pk ^ q ≤
      ((criticalIncidenceIndex pk : ℝ) ^ (-1 / 2 : ℝ)) ^ q :=
        Real.rpow_le_rpow (criticalIncidenceDiagonal_nonneg pk)
          (criticalIncidenceDiagonal_le pk) hq0.le
    _ = (criticalIncidenceIndex pk : ℝ) ^ (-q / 2) := by
        rw [← Real.rpow_mul hidx]
        ring_nf

theorem summable_criticalIncidenceLogDiagonal_rpow {q : ℝ} (hq : 2 < q) :
    Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceLogDiagonal pk ^ q) := by
  have hq0 : (0 : ℝ) < q := by linarith
  set ε : ℝ := (q - 2) / (4 * q) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos (by linarith) (by linarith)
  have hbase : Summable (fun n : ℕ => (ε ^ q)⁻¹ * (n : ℝ) ^ (-(q + 2) / 4)) := by
    refine Summable.mul_left _ ?_
    rw [Real.summable_nat_rpow]
    linarith
  have hcomp := hbase.comp_injective criticalIncidenceIndex_injective
  refine Summable.of_nonneg_of_le
    (fun pk => Real.rpow_nonneg (criticalIncidenceLogDiagonal_nonneg pk) q) ?_ hcomp
  intro pk
  have hidx1 : (1 : ℝ) ≤ (criticalIncidenceIndex pk : ℝ) := one_le_criticalIncidenceIndex_real pk
  have hidx : (0 : ℝ) ≤ (criticalIncidenceIndex pk : ℝ) := by linarith
  have hlognn : 0 ≤ Real.log (criticalIncidenceIndex pk : ℝ) := Real.log_nonneg hidx1
  have hpow : (0 : ℝ) ≤ (criticalIncidenceIndex pk : ℝ) ^ (-1 / 2 : ℝ) :=
    Real.rpow_nonneg hidx _
  have hstep1 : criticalIncidenceLogDiagonal pk ^ q ≤
      (Real.log (criticalIncidenceIndex pk : ℝ) *
        (criticalIncidenceIndex pk : ℝ) ^ (-1 / 2 : ℝ)) ^ q :=
    Real.rpow_le_rpow (criticalIncidenceLogDiagonal_nonneg pk)
      (criticalIncidenceLogDiagonal_le pk) hq0.le
  have hsplit : (Real.log (criticalIncidenceIndex pk : ℝ) *
      (criticalIncidenceIndex pk : ℝ) ^ (-1 / 2 : ℝ)) ^ q =
      Real.log (criticalIncidenceIndex pk : ℝ) ^ q *
        (criticalIncidenceIndex pk : ℝ) ^ (-q / 2) := by
    rw [Real.mul_rpow hlognn hpow, ← Real.rpow_mul hidx]
    ring_nf
  have hlogbound : Real.log (criticalIncidenceIndex pk : ℝ) ^ q ≤
      (ε ^ q)⁻¹ * (criticalIncidenceIndex pk : ℝ) ^ ((q - 2) / 4) := by
    have hle : Real.log (criticalIncidenceIndex pk : ℝ) ≤
        (criticalIncidenceIndex pk : ℝ) ^ ε / ε := Real.log_le_rpow_div hidx hεpos
    have hmono := Real.rpow_le_rpow hlognn hle hq0.le
    refine hmono.trans_eq ?_
    rw [Real.div_rpow (Real.rpow_nonneg hidx _) hεpos.le, ← Real.rpow_mul hidx]
    rw [show ε * q = (q - 2) / 4 from by rw [hε]; field_simp]
    ring
  have hfinal : Real.log (criticalIncidenceIndex pk : ℝ) ^ q *
      (criticalIncidenceIndex pk : ℝ) ^ (-q / 2) ≤
      (ε ^ q)⁻¹ * (criticalIncidenceIndex pk : ℝ) ^ (-(q + 2) / 4) := by
    have hpos : (0 : ℝ) ≤ (criticalIncidenceIndex pk : ℝ) ^ (-q / 2) :=
      Real.rpow_nonneg hidx _
    calc Real.log (criticalIncidenceIndex pk : ℝ) ^ q *
        (criticalIncidenceIndex pk : ℝ) ^ (-q / 2) ≤
        ((ε ^ q)⁻¹ * (criticalIncidenceIndex pk : ℝ) ^ ((q - 2) / 4)) *
          (criticalIncidenceIndex pk : ℝ) ^ (-q / 2) :=
          mul_le_mul_of_nonneg_right hlogbound hpos
      _ = (ε ^ q)⁻¹ * (criticalIncidenceIndex pk : ℝ) ^ (-(q + 2) / 4) := by
          rw [mul_assoc, ← Real.rpow_add' hidx (by intro h; linarith [h])]
          congr 2
          ring
  exact hstep1.trans (hsplit.le.trans hfinal)

theorem not_summable_criticalIncidenceDiagonal_rpow {q : ℝ} (_hq0 : 0 < q) (hq : q ≤ 2) :
    ¬ Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceDiagonal pk ^ q) := by
  intro h
  have hdepth := h.comp_injective depthOne_injective
  refine not_summable_of_one_div_le (f := fun p : Nat.Primes =>
    criticalIncidenceDiagonal (p, 0) ^ q) ?_ hdepth
  intro p
  have hprime : (p : ℕ).Prime := p.property
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have := hprime.two_le
    exact_mod_cast Nat.one_le_of_lt (lt_of_lt_of_le Nat.one_lt_two this)
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  rw [criticalIncidenceDiagonal_depth_one, ← Real.rpow_mul hp0.le]
  rw [show (1 : ℝ) / ((p : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ (-1 : ℝ) from by
    rw [Real.rpow_neg_one]; exact one_div _]
  refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
  have : -1 / 2 * q = -(q / 2) := by ring
  rw [this]
  linarith

theorem not_summable_criticalIncidenceLogDiagonal_rpow
    {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 2) :
    ¬ Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceLogDiagonal pk ^ q) := by
  intro h
  have hdepth := h.comp_injective depthOne_injective
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled : Summable (fun p : Nat.Primes =>
      (Real.log 2 ^ q)⁻¹ * criticalIncidenceLogDiagonal (p, 0) ^ q) :=
    hdepth.mul_left _
  refine not_summable_of_one_div_le (f := fun p : Nat.Primes =>
    (Real.log 2 ^ q)⁻¹ * criticalIncidenceLogDiagonal (p, 0) ^ q) ?_ hscaled
  intro p
  have hprime : (p : ℕ).Prime := p.property
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hprime.two_le
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by linarith
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hlogp : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log (by norm_num) hp2
  have hlogq : Real.log 2 ^ q ≤ Real.log ((p : ℕ) : ℝ) ^ q :=
    Real.rpow_le_rpow hlog2.le hlogp hq0.le
  have hlogqpos : (0 : ℝ) < Real.log 2 ^ q := Real.rpow_pos_of_pos hlog2 q
  have hsplit : criticalIncidenceLogDiagonal (p, 0) ^ q =
      Real.log ((p : ℕ) : ℝ) ^ q * ((p : ℕ) : ℝ) ^ (-q / 2) := by
    rw [criticalIncidenceLogDiagonal_depth_one,
      Real.mul_rpow (Real.log_nonneg hp1) (Real.rpow_nonneg hp0.le _),
      ← Real.rpow_mul hp0.le]
    ring_nf
  have hstep : ((p : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-q / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hp1 ?_
    linarith
  have hone : (1 : ℝ) / ((p : ℕ) : ℝ) = ((p : ℕ) : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]; exact one_div _
  rw [hone, hsplit]
  calc ((p : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-q / 2) := hstep
    _ = 1 * ((p : ℕ) : ℝ) ^ (-q / 2) := by ring
    _ ≤ ((Real.log 2 ^ q)⁻¹ * Real.log ((p : ℕ) : ℝ) ^ q) * ((p : ℕ) : ℝ) ^ (-q / 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hp0.le _)
        rw [← div_eq_inv_mul, le_div_iff₀ hlogqpos]
        simpa using hlogq
    _ = (Real.log 2 ^ q)⁻¹ * (Real.log ((p : ℕ) : ℝ) ^ q * ((p : ℕ) : ℝ) ^ (-q / 2)) := by
        ring

/-- **Equation (27), plain source.**  The critical half-density source diagonal is `q`-summable
exactly for `q > 2`. -/
theorem summable_criticalIncidenceDiagonal_rpow_iff {q : ℝ} (hq0 : 0 < q) :
    Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceDiagonal pk ^ q) ↔ 2 < q := by
  refine ⟨fun h => ?_, summable_criticalIncidenceDiagonal_rpow⟩
  by_contra hcon
  exact not_summable_criticalIncidenceDiagonal_rpow hq0 (not_lt.mp hcon) h

/-- **Equation (27), logarithmic source.**  The logarithmically weighted critical diagonal is
`q`-summable exactly for `q > 2`. -/
theorem summable_criticalIncidenceLogDiagonal_rpow_iff {q : ℝ} (hq0 : 0 < q) :
    Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceLogDiagonal pk ^ q) ↔ 2 < q := by
  refine ⟨fun h => ?_, summable_criticalIncidenceLogDiagonal_rpow⟩
  by_contra hcon
  exact not_summable_criticalIncidenceLogDiagonal_rpow hq0 (not_lt.mp hcon) h

/-- **Equation (28).**  The critical carrier lies in every ideal strictly above Hilbert–Schmidt
and in none at or below it. -/
theorem criticalIncidenceDiagonal_mem_intersection :
    (∀ q : ℝ, 2 < q → Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceDiagonal pk ^ q)) ∧
      ¬ Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceDiagonal pk ^ (2 : ℝ)) := by
  refine ⟨fun q hq => summable_criticalIncidenceDiagonal_rpow hq, ?_⟩
  exact not_summable_criticalIncidenceDiagonal_rpow (by norm_num) le_rfl

theorem criticalIncidenceLogDiagonal_mem_intersection :
    (∀ q : ℝ, 2 < q →
        Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceLogDiagonal pk ^ q)) ∧
      ¬ Summable (fun pk : Nat.Primes × ℕ => criticalIncidenceLogDiagonal pk ^ (2 : ℝ)) := by
  refine ⟨fun q hq => summable_criticalIncidenceLogDiagonal_rpow hq, ?_⟩
  exact not_summable_criticalIncidenceLogDiagonal_rpow (by norm_num) le_rfl

/-! ## Operator-norm exhaustion of the source -/

/-- **Equation (23).**  For every positive shift the source diagonal vanishes at infinity. -/
theorem tendsto_vonMangoldt_rpow_atTop {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ))
      atTop (nhds 0) := by
  have hhalf : 0 < σ / 2 := by linarith
  have hmajor : Tendsto (fun n : ℕ => (2 / σ) * (n : ℝ) ^ (-(σ / 2))) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ => ((n : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have := (tendsto_rpow_neg_atTop hhalf).comp hcast
    simpa using this.const_mul (2 / σ)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  · have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ (σ / 2) / (σ / 2) :=
      Real.log_le_rpow_div hn hhalf
    have hmang : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) ^ (σ / 2) / (σ / 2) :=
      ArithmeticFunction.vonMangoldt_le_log.trans hlog
    have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hn _
    calc ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) ≤
        ((n : ℝ) ^ (σ / 2) / (σ / 2)) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hmang hpow
      _ = (2 / σ) * ((n : ℝ) ^ (σ / 2) * (n : ℝ) ^ (-σ)) := by
          rw [div_eq_inv_mul]
          have : (σ / 2 : ℝ)⁻¹ = 2 / σ := by field_simp
          rw [this]
          ring
      _ ≤ (2 / σ) * (n : ℝ) ^ (-(σ / 2)) := by
          rcases eq_or_lt_of_le hn with hzero | hpos
          · have h0 : (n : ℝ) = 0 := hzero.symm
            simp [h0, Real.zero_rpow, ne_of_gt hhalf, ne_of_gt hσ,
              show -(σ / 2) ≠ 0 from by intro hc; linarith [neg_eq_zero.mp hc]]
          · rw [← Real.rpow_add hpos]
            have : σ / 2 + -σ = -(σ / 2) := by ring
            rw [this]

/-- **Equations (24)–(25).**  Beyond `exp (1/σ)` the logarithmic half-density profile is
antitone, so the source tail is controlled by its left endpoint. -/
theorem antitoneOn_log_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun t : ℝ => Real.log t * t ^ (-σ)) (Ici (Real.exp (1 / σ))) := by
  have hepos : 0 < Real.exp (1 / σ) := Real.exp_pos _
  have hderiv : ∀ t ∈ interior (Ici (Real.exp (1 / σ))),
      HasDerivAt (fun x : ℝ => Real.log x * x ^ (-σ))
        ((1 / t) * t ^ (-σ) + Real.log t * (-σ * t ^ (-σ - 1))) t := by
    intro t ht
    have htpos : 0 < t := by
      rw [interior_Ici] at ht
      exact lt_trans hepos ht
    have h1 : HasDerivAt Real.log (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log (ne_of_gt htpos)
    have h2 : HasDerivAt (fun x : ℝ => x ^ (-σ)) (-σ * t ^ (-σ - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htpos))
    exact h1.mul h2
  refine antitoneOn_of_deriv_nonpos (convex_Ici _) ?_ ?_ ?_
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hepos ht
    exact (Real.continuousAt_log (ne_of_gt htpos)).continuousWithinAt.mul
      ((Real.continuousAt_rpow_const t (-σ) (Or.inl (ne_of_gt htpos))).continuousWithinAt)
  · intro t ht
    exact ((hderiv t ht).differentiableAt).differentiableWithinAt
  · intro t ht
    have htpos : 0 < t := by
      rw [interior_Ici] at ht
      exact lt_trans hepos ht
    have hlog : 1 / σ ≤ Real.log t := by
      rw [interior_Ici] at ht
      have := (Real.exp_lt_exp (x := 1 / σ) (y := Real.log t)).mpr
      have hlt : Real.exp (1 / σ) < t := ht
      have := Real.log_lt_log hepos hlt
      rw [Real.log_exp] at this
      exact this.le
    rw [(hderiv t ht).deriv]
    have hpow : (0 : ℝ) < t ^ (-σ - 1) := Real.rpow_pos_of_pos htpos _
    have hfactor : (1 / t) * t ^ (-σ) = t ^ (-σ - 1) := by
      rw [show (-σ - 1 : ℝ) = -σ + (-1) from by ring, Real.rpow_add htpos,
        Real.rpow_neg_one, one_div]
      ring
    rw [hfactor]
    have hσlog : 1 ≤ σ * Real.log t := by
      have := mul_le_mul_of_nonneg_left hlog hσ.le
      rw [mul_one_div, div_self (ne_of_gt hσ)] at this
      exact this
    nlinarith [hpow, hσlog]

end

end RHTower
