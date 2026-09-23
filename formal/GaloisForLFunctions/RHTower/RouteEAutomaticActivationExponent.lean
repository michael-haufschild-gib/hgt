import GaloisForLFunctions.RHTower.RouteEConditionedSlotDivisors

/-!
# Route E automatic activation exponent from a physical receiver cap

The conditioned-slot-divisor obstruction was stated with a supplied activation exponent
`b i ≤ a i ^ K`.  At one finite physical scale that exponent is automatic if every inactive
integer factor is at least two and active factors are bounded by an integer cap `U`: take
`K = log 2 U + 1`.

Consequently, whenever the singleton slot count dominates this logarithmic exponent, the existing
five-distinct-receiver obstruction applies without a fixed-in-scale power premise.  This is a
finite structural reduction only; it does not estimate a conditioned cell's mass or signed
covariance.
-/

open Finset

namespace RHTower.IntegerCubeAperture

noncomputable section

/-- A uniform integer cap on active factors supplies a logarithmic activation exponent whenever
every inactive factor is at least two. -/
theorem bounded_active_le_inactive_pow_logCap
    {C : Type*} (a b : C → ℕ) (U : ℕ)
    (ha : ∀ i, 2 ≤ a i) (hb : ∀ i, b i ≤ U) :
    ∀ i, b i ≤ a i ^ (Nat.log 2 U + 1) := by
  intro i
  exact le_trans (hb i) <| (calc
    U < 2 ^ (Nat.log 2 U + 1) := by
      simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two U
    _ ≤ a i ^ (Nat.log 2 U + 1) := Nat.pow_le_pow_left (ha i) _).le

/-- A narrow singleton history whose inactive integer factors are all at least two, whose active
factors are capped by `U`, and whose slot count dominates `log₂ U` cannot have five distinct
physical receivers. -/
theorem singleton_history_no_five_of_receiver_cap
    {C : Type*} [Fintype C] [DecidableEq C]
    (m U : ℕ) (k : C → Bool → ℕ) (a b : C → ℕ)
    (history : RouteEComponentHistory (fun _ : C => Bool) m)
    (hmem : history ∈ routeEComponentHistogramCell (fun _ : C => Bool) m k)
    (hone : ∀ i, k i true = 1) (ha : ∀ i, 2 ≤ a i) (hb : ∀ i, b i ≤ U)
    (hm : 10 * (Nat.log 2 U + 2) ≤ m)
    (L W : ℝ) (hL : 0 ≤ L) (hW : 0 ≤ W) (hgap : W ^ (55 : ℕ) < L ^ (30 : ℕ))
    (hwindow : ∀ r, routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i : ℝ) else (a i : ℝ)) history r ∈ Set.Icc L (L + W))
    (e : Fin 5 → Fin m) :
    ¬ Function.Injective (fun r => routeEComponentSlotReceiver (fun _ : C => Bool)
      (fun i z => if z then (b i : ℝ) else (a i : ℝ)) history (e r)) := by
  let K := Nat.log 2 U + 1
  have ha1 : ∀ i, 1 ≤ a i := fun i => (by decide : 1 ≤ 2).trans (ha i)
  have hactivation : ∀ i, b i ≤ a i ^ K := by
    simpa only [K] using bounded_active_le_inactive_pow_logCap a b U ha hb
  have hmK : 10 * (K + 1) ≤ m := by
    simpa only [K, Nat.add_assoc] using hm
  exact singleton_history_no_five_of_power_activation m K k a b history hmem hone ha1
    hactivation hmK L W hL hW hgap hwindow e

end

end RHTower.IntegerCubeAperture
