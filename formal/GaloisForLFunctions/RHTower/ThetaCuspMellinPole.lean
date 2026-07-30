import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeSource
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order

/-!
# Exact finite-prime cusp order

The finite-prime Mellin multiplier has denominator

`∏_{p ≤ N} (1 - exp (-s log p))`.

Every local factor has a simple zero at the cusp point `s = 0`; additivity of analytic order gives
exact denominator order `π(N)`, and inversion gives a pole of order `π(N)`.  This is the exact
order statement in equations (15)--(17) of the pointed theta-cusp card.
-/

noncomputable section

namespace RHTower

/-- The denominator of one finite-prime Euler factor in the cusp coordinate. -/
def finitePrimeCuspEulerFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-s * Real.log p)

/-- The full finite-prime cusp denominator. -/
def finitePrimeCuspDenominator (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ Nat.primesLE N, finitePrimeCuspEulerFactor p s

theorem finitePrimeCuspEulerFactor_analyticAt (p : ℕ) :
    AnalyticAt ℂ (finitePrimeCuspEulerFactor p) 0 := by
  unfold finitePrimeCuspEulerFactor
  fun_prop

@[simp] theorem finitePrimeCuspEulerFactor_zero (p : ℕ) :
    finitePrimeCuspEulerFactor p 0 = 0 := by
  simp [finitePrimeCuspEulerFactor]

theorem hasDerivAt_finitePrimeCuspEulerFactor (p : ℕ) (s : ℂ) :
    HasDerivAt (finitePrimeCuspEulerFactor p)
      ((Real.log p : ℂ) * Complex.exp (-s * Real.log p)) s := by
  unfold finitePrimeCuspEulerFactor
  have hinner : HasDerivAt (fun z : ℂ => -z * (Real.log p : ℂ))
      (-(Real.log p : ℂ)) s := by
    simpa only [Pi.neg_apply, id_eq, neg_mul, one_mul] using
      (((hasDerivAt_id s).neg).mul_const (Real.log p : ℂ))
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (-z * Real.log p))
      (Complex.exp (-s * Real.log p) * (-(Real.log p : ℂ))) s :=
    (Complex.hasDerivAt_exp (-s * Real.log p)).comp s hinner
  apply ((hasDerivAt_const s (1 : ℂ)).sub hexp).congr_deriv
  ring

@[simp] theorem finitePrimeCuspEulerFactor_deriv_zero (p : ℕ) :
    deriv (finitePrimeCuspEulerFactor p) 0 = (Real.log p : ℂ) := by
  rw [(hasDerivAt_finitePrimeCuspEulerFactor p 0).deriv]
  simp

/-- Each retained prime contributes exactly one order of cusp vanishing. -/
theorem finitePrimeCuspEulerFactor_analyticOrderAt_zero {p : ℕ} (hp : p.Prime) :
    analyticOrderAt (finitePrimeCuspEulerFactor p) 0 = 1 := by
  apply (finitePrimeCuspEulerFactor_analyticAt p).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact finitePrimeCuspEulerFactor_zero p
  · rw [finitePrimeCuspEulerFactor_deriv_zero]
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

theorem finitePrimeCuspDenominator_analyticAt (N : ℕ) :
    AnalyticAt ℂ (finitePrimeCuspDenominator N) 0 := by
  unfold finitePrimeCuspDenominator
  exact (Nat.primesLE N).analyticAt_fun_prod fun p hp =>
    finitePrimeCuspEulerFactor_analyticAt p

private theorem finitePrimeCuspDenominator_finset_analyticOrderAt_zero
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    analyticOrderAt
      (fun s : ℂ => ∏ p ∈ S, finitePrimeCuspEulerFactor p s) 0 = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      change analyticOrderAt (fun _ : ℂ => 1) 0 = 0
      exact ((analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ))
        (x := (0 : ℂ))).analyticOrderAt_eq_zero).2 one_ne_zero
  | @insert p S hpS ih =>
      have hp : p.Prime := hS p (by simp)
      have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (by simp [hq])
      simp only [Finset.prod_insert hpS]
      change analyticOrderAt
        (finitePrimeCuspEulerFactor p *
          (fun s : ℂ => ∏ q ∈ S, finitePrimeCuspEulerFactor q s)) 0 = _
      rw [analyticOrderAt_mul (finitePrimeCuspEulerFactor_analyticAt p)
        (S.analyticAt_fun_prod fun q hq => finitePrimeCuspEulerFactor_analyticAt q)]
      rw [finitePrimeCuspEulerFactor_analyticOrderAt_zero hp, ih hS']
      simp [Finset.card_insert_of_notMem hpS, add_comm]

/-- The cusp denominator vanishes to exact order `π(N)`. -/
theorem finitePrimeCuspDenominator_analyticOrderAt_zero (N : ℕ) :
    analyticOrderAt (finitePrimeCuspDenominator N) 0 = Nat.primeCounting N := by
  change analyticOrderAt
    (fun s : ℂ => ∏ p ∈ Nat.primesLE N, finitePrimeCuspEulerFactor p s) 0 = _
  calc
    analyticOrderAt
        (fun s : ℂ => ∏ p ∈ Nat.primesLE N, finitePrimeCuspEulerFactor p s) 0 =
      (Nat.primesLE N).card :=
        finitePrimeCuspDenominator_finset_analyticOrderAt_zero (Nat.primesLE N)
          (fun p hp => (Nat.mem_primesLE.mp hp).2)
    _ = Nat.primeCounting N := by
      exact_mod_cast Nat.primesLE_card_eq_primeCounting N

/-- The reciprocal Euler multiplier has a pole of exact order `π(N)` at the cusp. -/
theorem finitePrimeCuspDenominator_inv_meromorphicOrderAt_zero (N : ℕ) :
    meromorphicOrderAt (finitePrimeCuspDenominator N)⁻¹ 0 =
      -((Nat.primeCounting N : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_inv,
    (finitePrimeCuspDenominator_analyticAt N).meromorphicOrderAt_eq,
    finitePrimeCuspDenominator_analyticOrderAt_zero]
  simp

end RHTower
