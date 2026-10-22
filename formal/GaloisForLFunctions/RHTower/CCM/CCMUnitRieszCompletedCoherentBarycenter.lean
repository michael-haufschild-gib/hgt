import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCoherentOutgoingChargeHankel

/-!
# Completed unit-Riesz coherent barycenter

The completed kernel response already present in the corpus has a nonzero constant tail and hence
is generally not an `L²` amplitude.  This module changes level: coherent increments themselves are
the vectors.  Prime atoms and the exponential polar continuum then form one literal signed
prime-minus-polar barycenter.

Premise-free theorems prove:

* the polar profile is exactly the exponentially weighted continuum of coherent increments;
* the completed barycenter is in `L²(ℝ)` at every finite aperture;
* its incoming half is exactly a moving square-root-weighted von Mangoldt discrepancy;
* its outgoing half is exactly the critical Mellin--Chebyshev resolvent mode; and
* total energy splits orthogonally into incoming bulk plus squared resolvent boundary energy.

Thus the RH-bearing charge has a source-faithful Hilbert carrier before scalar trace or leakage.
The remaining hard problem is a quantitative source-specific bound/order on the incoming bulk,
not construction of a carrier.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def unitExponentialCoherentIncrementState (p s : ℝ) : ℝ :=
  unitExponentialCoherentState 0 s - unitExponentialCoherentState (-p) s

def unitExponentialPolarBarycenter (s : ℝ) : ℝ :=
  if s ≤ 0 then -(2 / 3 : ℝ) * Real.exp s
  else (1 / 3 : ℝ) * Real.exp (-s / 2)

def unitRieszCompletedCoherentBarycenter (N : ℕ) (s : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 2 N,
      (ArithmeticFunction.vonMangoldt k / Real.sqrt N) *
        unitExponentialCoherentIncrementState
          (Real.log N - Real.log k) s) -
    Real.sqrt N * unitExponentialPolarBarycenter s

/-- Square-root-weighted prime mass still causally visible at incoming log-time `-t`. -/
def unitRieszSqrtWeightedPrimePrefix (N : ℕ) (t : NNReal) : ℝ :=
  ∑ k ∈ (Finset.Icc 2 N).filter
      (fun k : ℕ => (t : ℝ) < Real.log N - Real.log k),
    ArithmeticFunction.vonMangoldt k * Real.sqrt k

/-- Exact incoming-half source law.  The completed Hilbert vector is the discrepancy between the
polar `2/3` main profile and a moving square-root-weighted von Mangoldt prefix. -/
theorem unitRieszCompletedCoherentBarycenter_eq_incoming_weightedPrefix
    (N : ℕ) (t : NNReal) :
    unitRieszCompletedCoherentBarycenter (N + 2) (-(t : ℝ)) =
      (2 / 3 : ℝ) * Real.sqrt ((N + 2 : ℕ) : ℝ) * Real.exp (-(t : ℝ)) -
        (Real.exp ((t : ℝ) / 2) / ((N + 2 : ℕ) : ℝ)) *
          unitRieszSqrtWeightedPrimePrefix (N + 2) t := by
  have hXpos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
  have hsqrtXpos : (0 : ℝ) < Real.sqrt ((N + 2 : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr hXpos
  have hexpX : Real.exp (Real.log ((N + 2 : ℕ) : ℝ) / 2) =
      Real.sqrt ((N + 2 : ℕ) : ℝ) := by
    rw [← Real.log_sqrt hXpos.le, Real.exp_log hsqrtXpos]
  have hsum :
      (∑ k ∈ Finset.Icc 2 (N + 2),
          (ArithmeticFunction.vonMangoldt k /
              Real.sqrt ((N + 2 : ℕ) : ℝ)) *
            unitExponentialCoherentIncrementState
              (Real.log ((N + 2 : ℕ) : ℝ) - Real.log k) (-(t : ℝ))) =
        -(Real.exp ((t : ℝ) / 2) / ((N + 2 : ℕ) : ℝ)) *
          unitRieszSqrtWeightedPrimePrefix (N + 2) t := by
    rw [unitRieszSqrtWeightedPrimePrefix, Finset.mul_sum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
    have hsqrtkpos : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr hkpos
    have hexpk : Real.exp (Real.log k / 2) = Real.sqrt k := by
      rw [← Real.log_sqrt hkpos.le, Real.exp_log hsqrtkpos]
    by_cases hcut : (t : ℝ) <
        Real.log ((N + 2 : ℕ) : ℝ) - Real.log k
    · rw [if_pos hcut]
      have hnot0 : ¬ (0 : ℝ) < -(t : ℝ) :=
        not_lt.mpr (neg_nonpos.mpr t.property)
      have hactive :
          -(Real.log ((N + 2 : ℕ) : ℝ) - Real.log k) < -(t : ℝ) := by
        linarith
      simp only [unitExponentialCoherentIncrementState,
        unitExponentialCoherentState, if_neg hnot0, if_pos hactive, zero_sub]
      have hfactor :
          Real.exp (-(-(t : ℝ) -
              -(Real.log ((N + 2 : ℕ) : ℝ) - Real.log k)) / 2) =
            Real.exp ((t : ℝ) / 2) *
              (Real.sqrt k / Real.sqrt ((N + 2 : ℕ) : ℝ)) := by
        calc
          Real.exp (-(-(t : ℝ) -
              -(Real.log ((N + 2 : ℕ) : ℝ) - Real.log k)) / 2) =
              Real.exp ((t : ℝ) / 2) *
                (Real.exp (Real.log k / 2) /
                  Real.exp (Real.log ((N + 2 : ℕ) : ℝ) / 2)) := by
            rw [← Real.exp_sub, ← Real.exp_add]
            congr 1
            ring
          _ = _ := by rw [hexpk, hexpX]
      rw [hfactor]
      have hsquare : Real.sqrt ((N + 2 : ℕ) : ℝ) ^ 2 =
          ((N + 2 : ℕ) : ℝ) := Real.sq_sqrt hXpos.le
      field_simp [hsqrtXpos.ne', hXpos.ne']
      rw [hsquare]
    · rw [if_neg hcut]
      have hnot0 : ¬ (0 : ℝ) < -(t : ℝ) :=
        not_lt.mpr (neg_nonpos.mpr t.property)
      have hinactive : ¬
          -(Real.log ((N + 2 : ℕ) : ℝ) - Real.log k) < -(t : ℝ) := by
        linarith
      simp only [unitExponentialCoherentIncrementState,
        unitExponentialCoherentState, if_neg hnot0, if_neg hinactive,
        sub_zero, mul_zero]
  rw [unitRieszCompletedCoherentBarycenter, hsum]
  have htnonpos : -(t : ℝ) ≤ 0 := neg_nonpos.mpr t.property
  rw [unitExponentialPolarBarycenter, if_pos htnonpos]
  ring

/-- The elementary polar profile is the literal exponentially weighted barycenter of coherent
increments.  This keeps the polar term in the same Hilbert carrier as the prime atoms. -/
theorem integral_unitExponentialCoherentIncrementState (s : ℝ) :
    (∫ p in Ioi (0 : ℝ),
        Real.exp (-p) * unitExponentialCoherentIncrementState p s) =
      unitExponentialPolarBarycenter s := by
  by_cases hs : s ≤ 0
  · let f : ℝ → ℝ := fun p =>
      Real.exp (-p) * unitExponentialCoherentIncrementState p s
    let g : ℝ → ℝ := fun p =>
      -(Real.exp (-s / 2)) * Real.exp (-((3 / 2) * p))
    have hneg : 0 ≤ -s := by linarith
    have hfLeft : ∀ p ∈ Ioc (0 : ℝ) (-s), f p = 0 := by
      intro p hp
      have hnot0 : ¬ (0 : ℝ) < s := not_lt.mpr hs
      have hnps : ¬ -p < s := not_lt.mpr (by linarith [hp.2])
      simp only [f, unitExponentialCoherentIncrementState,
        unitExponentialCoherentState, if_neg hnot0, if_neg hnps, sub_zero, mul_zero]
    have hfRight : ∀ p ∈ Ioi (-s), f p = g p := by
      intro p hp
      have hnot0 : ¬ (0 : ℝ) < s := not_lt.mpr hs
      have hp' : -s < p := hp
      have hnps : -p < s := by linarith
      dsimp only [f, g, unitExponentialCoherentIncrementState,
        unitExponentialCoherentState]
      rw [if_neg hnot0, if_pos hnps, zero_sub]
      have hfactor : Real.exp (-(s - -p) / 2) =
          Real.exp (-s / 2) * Real.exp (-p / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hprod : Real.exp (-p) * Real.exp (-p / 2) =
          Real.exp (-((3 / 2) * p)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hfactor]
      calc
        Real.exp (-p) * -(Real.exp (-s / 2) * Real.exp (-p / 2)) =
            -Real.exp (-s / 2) *
              (Real.exp (-p) * Real.exp (-p / 2)) := by ring
        _ = _ := by rw [hprod]
    have hgInt : IntegrableOn g (Ioi (-s)) := by
      dsimp only [g]
      have hbase : IntegrableOn
          (fun p : ℝ => Real.exp (-((3 / 2) * p))) (Ioi (-s)) := by
        convert exp_neg_integrableOn_Ioi (b := (3 / 2 : ℝ)) (-s)
          (by norm_num) using 1 <;> ring_nf
      exact hbase.const_mul _
    have hfLeftInt : IntegrableOn f (Ioc (0 : ℝ) (-s)) :=
      integrableOn_zero.congr_fun
        (fun p hp => (hfLeft p hp).symm) measurableSet_Ioc
    have hfRightInt : IntegrableOn f (Ioi (-s)) :=
      hgInt.congr_fun (fun p hp => (hfRight p hp).symm) measurableSet_Ioi
    have hsplit : Ioi (0 : ℝ) = Ioc 0 (-s) ∪ Ioi (-s) :=
      (Ioc_union_Ioi_eq_Ioi hneg).symm
    rw [show (∫ p in Ioi (0 : ℝ),
          Real.exp (-p) * unitExponentialCoherentIncrementState p s) =
        ∫ p in Ioi (0 : ℝ), f p from rfl,
      hsplit,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hfLeftInt hfRightInt,
      setIntegral_congr_fun measurableSet_Ioc hfLeft,
      setIntegral_congr_fun measurableSet_Ioi hfRight]
    dsimp only [g]
    rw [integral_zero, zero_add, integral_const_mul,
      integral_Ioi_rexp_neg_mul_shift
        (by norm_num : (0 : ℝ) < 3 / 2) (-s)]
    rw [unitExponentialPolarBarycenter, if_pos hs]
    have hexp : Real.exp (-s / 2) * Real.exp (-((3 / 2) * -s)) =
        Real.exp s := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      -Real.exp (-s / 2) *
          (Real.exp (-((3 / 2) * -s)) / (3 / 2)) =
          -(2 / 3 : ℝ) *
            (Real.exp (-s / 2) * Real.exp (-((3 / 2) * -s))) := by ring
      _ = -(2 / 3 : ℝ) * Real.exp s := by rw [hexp]
  · have hspos : 0 < s := lt_of_not_ge hs
    let f : ℝ → ℝ := fun p =>
      Real.exp (-p) * unitExponentialCoherentIncrementState p s
    let g : ℝ → ℝ := fun p =>
      Real.exp (-s / 2) *
        (Real.exp (-(1 * p)) - Real.exp (-((3 / 2) * p)))
    have hfg : ∀ p ∈ Ioi (0 : ℝ), f p = g p := by
      intro p hp
      dsimp only [f, g]
      have htail : unitExponentialCoherentIncrementState p s =
          Real.exp (-s / 2) * (1 - Real.exp (-p / 2)) := by
        have hps : -p < s := lt_of_le_of_lt (neg_nonpos.mpr hp.le) hspos
        simp only [unitExponentialCoherentIncrementState,
          unitExponentialCoherentState, if_pos hspos, if_pos hps]
        rw [show Real.exp (-(s - -p) / 2) =
            Real.exp (-s / 2) * Real.exp (-p / 2) by
          rw [← Real.exp_add]
          congr 1
          ring]
        ring
      rw [htail]
      have hprod : Real.exp (-p) * Real.exp (-p / 2) =
          Real.exp (-((3 / 2) * p)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        Real.exp (-p) * (Real.exp (-s / 2) * (1 - Real.exp (-p / 2))) =
            Real.exp (-s / 2) *
              (Real.exp (-p) - Real.exp (-p) * Real.exp (-p / 2)) := by ring
        _ = Real.exp (-s / 2) *
              (Real.exp (-p) - Real.exp (-((3 / 2) * p))) := by rw [hprod]
        _ = _ := by rw [show -(1 * p) = -p by ring]
    have h1 : IntegrableOn (fun p : ℝ => Real.exp (-(1 * p))) (Ioi 0) :=
      by
        convert exp_neg_integrableOn_Ioi (b := (1 : ℝ)) 0 one_pos using 1 <;> ring_nf
    have h3 : IntegrableOn
        (fun p : ℝ => Real.exp (-((3 / 2) * p))) (Ioi 0) := by
      convert exp_neg_integrableOn_Ioi (b := (3 / 2 : ℝ)) 0
        (by norm_num) using 1 <;> ring_nf
    rw [show (∫ p in Ioi (0 : ℝ),
          Real.exp (-p) * unitExponentialCoherentIncrementState p s) =
        ∫ p in Ioi (0 : ℝ), f p from rfl,
      setIntegral_congr_fun measurableSet_Ioi hfg]
    dsimp only [g]
    rw [integral_const_mul, integral_sub h1 h3,
      integral_Ioi_rexp_neg_mul_shift one_pos 0,
      integral_Ioi_rexp_neg_mul_shift
        (by norm_num : (0 : ℝ) < 3 / 2) 0,
      unitExponentialPolarBarycenter, if_neg hs]
    norm_num
    ring

theorem measurable_unitExponentialCoherentIncrementState (p : ℝ) :
    Measurable (unitExponentialCoherentIncrementState p) := by
  have hstate (x : ℝ) : Measurable (unitExponentialCoherentState x) := by
    unfold unitExponentialCoherentState
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (by fun_prop) measurable_const
  exact (hstate 0).sub (hstate (-p))

theorem integrable_sq_unitExponentialCoherentIncrementState (p : ℝ) :
    Integrable (fun s : ℝ => unitExponentialCoherentIncrementState p s ^ 2) := by
  have h00 := integrable_unitExponentialCoherentState_mul 0 0
  have h0p := integrable_unitExponentialCoherentState_mul 0 (-p)
  have hp0 := integrable_unitExponentialCoherentState_mul (-p) 0
  have hpp := integrable_unitExponentialCoherentState_mul (-p) (-p)
  have hsum : Integrable (fun s : ℝ =>
      ((unitExponentialCoherentState 0 s * unitExponentialCoherentState 0 s -
        unitExponentialCoherentState 0 s * unitExponentialCoherentState (-p) s) -
        unitExponentialCoherentState (-p) s * unitExponentialCoherentState 0 s) +
        unitExponentialCoherentState (-p) s * unitExponentialCoherentState (-p) s) :=
    ((h00.sub h0p).sub hp0).add hpp
  refine hsum.congr ?_
  filter_upwards with s
  simp only [unitExponentialCoherentIncrementState]
  ring

theorem measurable_unitExponentialPolarBarycenter :
    Measurable unitExponentialPolarBarycenter := by
  unfold unitExponentialPolarBarycenter
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (by fun_prop) (by fun_prop)

theorem integrable_sq_unitExponentialPolarBarycenter :
    Integrable (fun s : ℝ => unitExponentialPolarBarycenter s ^ 2) := by
  have hleftBase : IntegrableOn (fun s : ℝ => Real.exp (2 * s)) (Iic 0) :=
    integrableOn_exp_mul_Iic (by norm_num) 0
  have hleft : IntegrableOn
      (fun s : ℝ => unitExponentialPolarBarycenter s ^ 2) (Iic 0) := by
    refine (hleftBase.const_mul (4 / 9 : ℝ)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    have hs' : s ≤ 0 := hs
    rw [unitExponentialPolarBarycenter, if_pos hs']
    have hexp : Real.exp s ^ 2 = Real.exp (2 * s) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexp]
    norm_num
  have hrightBase : IntegrableOn (fun s : ℝ => Real.exp ((-1) * s)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hright : IntegrableOn
      (fun s : ℝ => unitExponentialPolarBarycenter s ^ 2) (Ioi 0) := by
    refine (hrightBase.const_mul (1 / 9 : ℝ)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs' : 0 < s := hs
    rw [unitExponentialPolarBarycenter, if_neg (not_le_of_gt hs')]
    have hexp : Real.exp (-s / 2) ^ 2 = Real.exp ((-1) * s) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hexp]
    norm_num
  have hunion : IntegrableOn
      (fun s : ℝ => unitExponentialPolarBarycenter s ^ 2)
      (Iic 0 ∪ Ioi 0) := hleft.union hright
  rwa [Iic_union_Ioi, integrableOn_univ] at hunion

/-- The literal completed prime-minus-polar coherent barycenter is a genuine `L²(ℝ)` vector at
every finite aperture. -/
theorem integrable_sq_unitRieszCompletedCoherentBarycenter (N : ℕ) :
    Integrable (fun s : ℝ => unitRieszCompletedCoherentBarycenter N s ^ 2) := by
  let a : ℕ → ℝ → ℝ := fun k s =>
    (ArithmeticFunction.vonMangoldt k / Real.sqrt N) *
      unitExponentialCoherentIncrementState (Real.log N - Real.log k) s
  have haMeas (k : ℕ) : AEStronglyMeasurable (a k) volume := by
    exact ((measurable_unitExponentialCoherentIncrementState
      (Real.log N - Real.log k)).const_mul _).aestronglyMeasurable
  have haSq (k : ℕ) : Integrable (fun s : ℝ => a k s ^ 2) := by
    refine ((integrable_sq_unitExponentialCoherentIncrementState
      (Real.log N - Real.log k)).const_mul
        ((ArithmeticFunction.vonMangoldt k / Real.sqrt N) ^ 2)).congr ?_
    filter_upwards with s
    dsimp only [a]
    ring
  have hconstSq (c : ℝ) {f : ℝ → ℝ}
      (hf : Integrable (fun s => f s ^ 2)) :
      Integrable (fun s => (c * f s) ^ 2) := by
    refine (hf.const_mul (c ^ 2)).congr ?_
    filter_upwards with s
    ring
  have haddSq {f g : ℝ → ℝ}
      (hfm : AEStronglyMeasurable f volume)
      (hgm : AEStronglyMeasurable g volume)
      (hf : Integrable (fun s => f s ^ 2))
      (hg : Integrable (fun s => g s ^ 2)) :
      Integrable (fun s => (f s + g s) ^ 2) := by
    have hmajorant : Integrable (fun s => 2 * f s ^ 2 + 2 * g s ^ 2) :=
      (hf.const_mul 2).add (hg.const_mul 2)
    have htarget : AEStronglyMeasurable (fun s => (f s + g s) ^ 2) volume := by
      exact ((hfm.add hgm).pow 2).congr (Filter.Eventually.of_forall fun _ => rfl)
    refine Integrable.mono' hmajorant htarget ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f s - g s)]
  have hfinite : ∀ S : Finset ℕ,
      AEStronglyMeasurable (fun s : ℝ => ∑ k ∈ S, a k s) volume ∧
        Integrable (fun s : ℝ => (∑ k ∈ S, a k s) ^ 2) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        constructor
        · exact aestronglyMeasurable_const
        · simp
    | @insert k S hk ih =>
        have hsumMeas := ih.1
        have hsumSq := ih.2
        constructor
        · refine ((haMeas k).add hsumMeas).congr ?_
          filter_upwards with s
          simp only [Finset.sum_insert hk, Pi.add_apply]
        · simpa [Finset.sum_insert hk] using
            haddSq (haMeas k) hsumMeas (haSq k) hsumSq
  let prime : ℝ → ℝ := fun s => ∑ k ∈ Finset.Icc 2 N, a k s
  let polar : ℝ → ℝ := fun s => -Real.sqrt N * unitExponentialPolarBarycenter s
  have hprimeMeas : AEStronglyMeasurable prime volume := by
    simpa only [prime] using (hfinite (Finset.Icc 2 N)).1
  have hprimeSq : Integrable (fun s => prime s ^ 2) := by
    simpa only [prime] using (hfinite (Finset.Icc 2 N)).2
  have hpolarMeas : AEStronglyMeasurable polar volume := by
    exact (measurable_unitExponentialPolarBarycenter.const_mul _).aestronglyMeasurable
  have hpolarSq : Integrable (fun s => polar s ^ 2) := by
    exact hconstSq (-Real.sqrt N) integrable_sq_unitExponentialPolarBarycenter
  have htotal := haddSq hprimeMeas hpolarMeas hprimeSq hpolarSq
  refine htotal.congr ?_
  filter_upwards with s
  dsimp only [prime, polar, a, unitRieszCompletedCoherentBarycenter]
  ring

/-- Unconditional source-vector tail law, with the aperture shifted away from the degenerate
natural values. -/
theorem unitRieszCompletedCoherentBarycenter_resolvent_tail (N : ℕ) :
    ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      unitRieszCompletedCoherentBarycenter (N + 2) s =
        (criticalMellinChebyshevResolventSource
            (Real.log ((N + 2 : ℕ) : ℝ)) / 2) *
          Real.exp (-s / 2) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hspos : (0 : ℝ) < s := hs
  have hN : 2 ≤ N + 2 := by omega
  have hNpos : (0 : ℝ) < (N + 2 : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hpolar : unitExponentialPolarBarycenter s =
      (1 / 3 : ℝ) * Real.exp (-s / 2) := by
    simp [unitExponentialPolarBarycenter, not_le_of_gt hspos]
  have hsum :
      (∑ k ∈ Finset.Icc 2 (N + 2),
          (ArithmeticFunction.vonMangoldt k / Real.sqrt (N + 2 : ℕ)) *
            unitExponentialCoherentIncrementState
              (Real.log (N + 2 : ℕ) - Real.log k) s) =
        Real.exp (-s / 2) *
          ∑ k ∈ Finset.Icc 2 (N + 2),
            (ArithmeticFunction.vonMangoldt k / Real.sqrt (N + 2 : ℕ)) *
              (1 - Real.exp (-(Real.log (N + 2 : ℕ) - Real.log k) / 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N + 2 := (Finset.mem_Icc.mp hk).2
    have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk2)
    have hlog : Real.log k ≤ Real.log (N + 2 : ℕ) :=
      Real.strictMonoOn_log.monotoneOn hkpos hNpos (by exact_mod_cast hkN)
    have htail : unitExponentialCoherentIncrementState
        (Real.log (N + 2 : ℕ) - Real.log k) s =
        Real.exp (-s / 2) *
          (1 - Real.exp (-(Real.log (N + 2 : ℕ) - Real.log k) / 2)) := by
      have hp := sub_nonneg.mpr hlog
      have hps : -(Real.log (N + 2 : ℕ) - Real.log k) < s :=
        lt_of_le_of_lt (neg_nonpos.mpr hp) hspos
      simp only [unitExponentialCoherentIncrementState,
        unitExponentialCoherentState, if_pos hspos, if_pos hps]
      rw [show Real.exp
          (-(s - -(Real.log (N + 2 : ℕ) - Real.log k)) / 2) =
          Real.exp (-s / 2) *
            Real.exp (-(Real.log (N + 2 : ℕ) - Real.log k) / 2) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    rw [htail]
    ring
  have hout : unitRieszCompletedCoherentBarycenter (N + 2) s =
      unitRieszCoherentCompletedOutgoingCharge (N + 2) * Real.exp (-s / 2) := by
    rw [unitRieszCompletedCoherentBarycenter,
      unitRieszCoherentCompletedOutgoingCharge,
      unitRieszCoherentPrimeOutgoingCharge,
      unitRieszCoherentPolarOutgoingCharge_eq,
      hpolar, hsum]
    ring
  rw [hout, unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN]

/-- Exact positive-half-line energy of the literal signed prime-minus-polar coherent barycenter. -/
theorem integral_Ioi_sq_unitRieszCompletedCoherentBarycenter (N : ℕ) :
    (∫ s in Ioi (0 : ℝ),
        unitRieszCompletedCoherentBarycenter (N + 2) s ^ 2) =
      (criticalMellinChebyshevResolventSource
        (Real.log ((N + 2 : ℕ) : ℝ)) / 2) ^ 2 := by
  let q : ℝ := criticalMellinChebyshevResolventSource
    (Real.log ((N + 2 : ℕ) : ℝ)) / 2
  have heq :
      (fun s : ℝ => unitRieszCompletedCoherentBarycenter (N + 2) s ^ 2) =ᵐ[
        volume.restrict (Ioi (0 : ℝ))]
        (fun s : ℝ => q ^ 2 * Real.exp (-(1 * s))) := by
    filter_upwards [unitRieszCompletedCoherentBarycenter_resolvent_tail N] with s hs
    rw [hs]
    dsimp only [q]
    rw [mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [integral_congr_ae heq, integral_const_mul,
    integral_Ioi_rexp_neg_mul_shift one_pos 0]
  norm_num [q]

/-- Exact orthogonal bulk--boundary decomposition of completed source energy.  The outgoing summand
is precisely the squared critical resolvent; all remaining energy lies on the incoming half-line. -/
theorem integral_sq_unitRieszCompletedCoherentBarycenter_eq_bulk_add_resolvent
    (N : ℕ) :
    (∫ s : ℝ, unitRieszCompletedCoherentBarycenter (N + 2) s ^ 2) =
      (∫ s in Iic (0 : ℝ),
          unitRieszCompletedCoherentBarycenter (N + 2) s ^ 2) +
        (criticalMellinChebyshevResolventSource
          (Real.log ((N + 2 : ℕ) : ℝ)) / 2) ^ 2 := by
  have hint := integrable_sq_unitRieszCompletedCoherentBarycenter (N + 2)
  rw [← integral_Ioi_sq_unitRieszCompletedCoherentBarycenter N,
    ← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn,
    Iic_union_Ioi, setIntegral_univ]

theorem sq_criticalMellinChebyshevResolventSource_half_le_coherentBarycenterEnergy
    (N : ℕ) :
    (criticalMellinChebyshevResolventSource
      (Real.log ((N + 2 : ℕ) : ℝ)) / 2) ^ 2 ≤
      (∫ s in Iic (0 : ℝ),
          unitRieszCompletedCoherentBarycenter (N + 2) s ^ 2) +
        ∫ s in Ioi (0 : ℝ),
          unitRieszCompletedCoherentBarycenter (N + 2) s ^ 2 := by
  rw [integral_Ioi_sq_unitRieszCompletedCoherentBarycenter]
  exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)

end GaloisForLFunctions.RHTower
