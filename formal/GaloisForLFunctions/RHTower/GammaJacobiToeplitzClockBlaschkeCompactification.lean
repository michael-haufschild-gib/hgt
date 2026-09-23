import GaloisForLFunctions.RHTower.GammaJacobiTailConnectionTransgression
import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Gamma--Jacobi Blaschke compactification of reciprocal Toeplitz clocks

The canonical von Mangoldt Toeplitz counterreader forces reciprocal right-endpoint clock nodes
`1 / log(p+1)` toward the germ origin.  The reciprocal-log Gamma coordinate sends these exact
source nodes to

`r_p = tanh(log(p+1))^(2 : ℕ)`.

They are distinct points of `(0,1)` and their boundary defects are summable over primes.  Their
infinite product is therefore convergent and nonzero.  Thus the Gamma--Jacobi boundary converts
the counterreader's interior zero escape into a Blaschke-admissible boundary packet instead of an
identically-zero analytic germ.  The general Blaschke criterion is classical; this module proves
the unconditional arithmetic source specialization and exact coordinate pushforward.

No Xi zero, RH premise, target moment, prime-distribution estimate, or computation is used.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Reciprocal maximal clock forced by the source edge ending at `p+1`. -/
def vonMangoldtRightEndpointReciprocalClock (p : Nat.Primes) : ℝ :=
  (Real.log (((p : ℕ) + 1 : ℕ) : ℝ))⁻¹

/-- Gamma--Jacobi disk node of the same source endpoint. -/
def gammaJacobiRightEndpointDiskNode (p : Nat.Primes) : ℝ :=
  Real.tanh (Real.log (((p : ℕ) + 1 : ℕ) : ℝ)) ^ (2 : ℕ)

/-- Exact reciprocal-log pushforward from the Toeplitz escape clock to the Gamma--Jacobi disk. -/
theorem gammaJacobiRightEndpointDiskNode_eq_reciprocalClockPushforward
    (p : Nat.Primes) :
    gammaJacobiRightEndpointDiskNode p =
      Real.tanh ((vonMangoldtRightEndpointReciprocalClock p)⁻¹) ^ (2 : ℕ) := by
  rw [gammaJacobiRightEndpointDiskNode, vonMangoldtRightEndpointReciprocalClock, inv_inv]

/-- Closed defect of the hyperbolic disk node at any positive logarithmic source. -/
theorem one_sub_tanh_log_sq_eq (x : ℝ) (hx : 0 < x) :
    1 - Real.tanh (Real.log x) ^ (2 : ℕ) = 4 * x ^ (2 : ℕ) / (x ^ (2 : ℕ) + 1) ^ (2 : ℕ) := by
  rw [HTGeometry.one_sub_tanh_sq, Real.cosh_log hx]
  have hx0 := hx.ne'
  field_simp
  ring

/-- Every right-endpoint node lies strictly inside the positive real disk radius. -/
theorem gammaJacobiRightEndpointDiskNode_mem_Ioo (p : Nat.Primes) :
    gammaJacobiRightEndpointDiskNode p ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx : (1 : ℝ) < (((p : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ p.prop.pos
  have hlog : 0 < Real.log (((p : ℕ) + 1 : ℕ) : ℝ) := Real.log_pos hx
  rw [gammaJacobiRightEndpointDiskNode]
  constructor
  · exact sq_pos_of_pos (tanh_pos_of_pos hlog)
  · have ht := Real.tanh_lt_one (Real.log (((p : ℕ) + 1 : ℕ) : ℝ))
    have hfactor :
        0 < (1 - Real.tanh (Real.log (((p : ℕ) + 1 : ℕ) : ℝ))) *
          (1 + Real.tanh (Real.log (((p : ℕ) + 1 : ℕ) : ℝ))) :=
      mul_pos (sub_pos.mpr ht) (by nlinarith [tanh_pos_of_pos hlog])
    nlinarith

/-- Exact rational boundary defect of the prime-indexed right-endpoint node. -/
theorem one_sub_gammaJacobiRightEndpointDiskNode_eq (p : Nat.Primes) :
    1 - gammaJacobiRightEndpointDiskNode p =
      4 * (((p : ℕ) + 1 : ℕ) : ℝ) ^ (2 : ℕ) /
        ((((p : ℕ) + 1 : ℕ) : ℝ) ^ (2 : ℕ) + 1) ^ (2 : ℕ) := by
  rw [gammaJacobiRightEndpointDiskNode]
  exact one_sub_tanh_log_sq_eq _ (by positivity)

theorem one_sub_gammaJacobiRightEndpointDiskNode_nonneg (p : Nat.Primes) :
    0 ≤ 1 - gammaJacobiRightEndpointDiskNode p := by
  exact sub_nonneg.mpr (gammaJacobiRightEndpointDiskNode_mem_Ioo p).2.le

/-- Elementary `p⁻²` majorant for the Gamma--Jacobi boundary defect. -/
theorem one_sub_gammaJacobiRightEndpointDiskNode_le (p : Nat.Primes) :
    1 - gammaJacobiRightEndpointDiskNode p ≤ 4 * ((p : ℝ) ^ (2 : ℕ))⁻¹ := by
  rw [one_sub_gammaJacobiRightEndpointDiskNode_eq]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hpn : (0 : ℝ) < (((p : ℕ) + 1 : ℕ) : ℝ) := by positivity
  have hle : (p : ℝ) ≤ (((p : ℕ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (p : ℕ)
  rw [show 4 * ((p : ℝ) ^ (2 : ℕ))⁻¹ = 4 / (p : ℝ) ^ (2 : ℕ) by rw [div_eq_mul_inv]]
  rw [le_div_iff₀ (sq_pos_of_pos hp), div_mul_eq_mul_div,
    div_le_iff₀ (sq_pos_of_pos (by positivity :
      0 < (((p : ℕ) + 1 : ℕ) : ℝ) ^ (2 : ℕ) + 1))]
  have hsq : (p : ℝ) ^ (2 : ℕ) ≤ (((p : ℕ) + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (by positivity :
      0 ≤ (((p : ℕ) + 1 : ℕ) : ℝ) + (p : ℝ))]
  have hprod :
      0 ≤ (((p : ℕ) + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
        ((((p : ℕ) + 1 : ℕ) : ℝ) ^ (2 : ℕ) - (p : ℝ) ^ (2 : ℕ)) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsq)
  nlinarith

/-- **Blaschke admissibility.**  The Gamma--Jacobi images of all reciprocal endpoint clocks have
summable distance to the unit-circle boundary. -/
theorem summable_one_sub_gammaJacobiRightEndpointDiskNode :
    Summable (fun p : Nat.Primes =>
      1 - gammaJacobiRightEndpointDiskNode p) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ (2 : ℕ))⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le
    one_sub_gammaJacobiRightEndpointDiskNode_nonneg
    one_sub_gammaJacobiRightEndpointDiskNode_le
    (hprime.mul_left 4)

/-- Distinct prime edges remain distinctly marked after Gamma--Jacobi boundary compactification. -/
theorem gammaJacobiRightEndpointDiskNode_eq_iff
    (p q : Nat.Primes) :
    gammaJacobiRightEndpointDiskNode p =
        gammaJacobiRightEndpointDiskNode q ↔
      p = q := by
  have hpLog : 0 < Real.log (((p : ℕ) + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ p.prop.pos)
  have hqLog : 0 < Real.log (((q : ℕ) + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast Nat.succ_lt_succ q.prop.pos)
  rw [gammaJacobiRightEndpointDiskNode, gammaJacobiRightEndpointDiskNode]
  constructor
  · intro h
    have htanh :
        Real.tanh (Real.log (((p : ℕ) + 1 : ℕ) : ℝ)) =
          Real.tanh (Real.log (((q : ℕ) + 1 : ℕ) : ℝ)) := by
      nlinarith [tanh_pos_of_pos hpLog, tanh_pos_of_pos hqLog]
    have hlog :
        Real.log (((p : ℕ) + 1 : ℕ) : ℝ) =
          Real.log (((q : ℕ) + 1 : ℕ) : ℝ) :=
      Real.tanh_injective htanh
    have hexp := congrArg Real.exp hlog
    rw [Real.exp_log (by positivity : (0 : ℝ) < (((p : ℕ) + 1 : ℕ) : ℝ)),
      Real.exp_log (by positivity : (0 : ℝ) < (((q : ℕ) + 1 : ℕ) : ℝ))] at hexp
    apply Subtype.ext
    exact_mod_cast Nat.succ.inj (by exact_mod_cast hexp)
  · intro h
    subst q
    rfl

/-- The endpoint-node family has a convergent infinite product. -/
theorem multipliable_gammaJacobiRightEndpointDiskNode :
    Multipliable gammaJacobiRightEndpointDiskNode := by
  have hs := summable_one_sub_gammaJacobiRightEndpointDiskNode
  have hneg : Summable (fun p : Nat.Primes =>
      -(1 - gammaJacobiRightEndpointDiskNode p)) := hs.neg
  exact (Real.multipliable_one_add_of_summable hneg).congr (fun p => by ring)

/-- **Nontriviality at the Hardy origin.**  The product of all Gamma--Jacobi endpoint nodes is
nonzero, so the associated prime Blaschke packet does not collapse identically. -/
theorem tprod_gammaJacobiRightEndpointDiskNode_ne_zero :
    ∏' p : Nat.Primes, gammaJacobiRightEndpointDiskNode p ≠ 0 := by
  have hprod := tprod_one_add_ne_zero_of_summable
    (f := fun p : Nat.Primes => -(1 - gammaJacobiRightEndpointDiskNode p))
    (fun p => by
      have hp := (gammaJacobiRightEndpointDiskNode_mem_Ioo p).1.ne'
      convert hp using 1
      ring)
    (by
      have hs := summable_one_sub_gammaJacobiRightEndpointDiskNode
      apply hs.congr
      intro p
      rw [Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (one_sub_gammaJacobiRightEndpointDiskNode_nonneg p)])
  rw [tprod_congr (fun p : Nat.Primes => by ring)] at hprod
  exact hprod

end

end RHTower
