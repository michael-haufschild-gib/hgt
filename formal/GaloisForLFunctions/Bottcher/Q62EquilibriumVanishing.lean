/-
# q62 — GAP-A final input reduced to two sharp potential-theory halves

`Q62WeylDischarge` reduced the entire q62 Brolin support route (`LimitingBrolinMeasureAtSupportsJulia`,
valid across all three regimes) to the single input `EquilibriumPotentialVanishesAe c a`:
the equilibrium potential `Uᵘ = logPotential (limitingBrolinMeasureAt c a)` vanishes a.e. on
`filledJulia c` (Frostman's equilibrium identity, `Robin = -log cap K_c = 0`).

This module cuts that input into two named, standard halves and proves the assembly:

* **Half A — the doubling law** `BrolinScalingAt c a`: `−Uᵘ(f_c z) = 2·(−Uᵘ z)` on `K_c`.
  Given it, the bounded forward orbit forces `−Uᵘ ≤ 0` on `K_c` (a positive value doubles
  past the uniform upper bound `log(2·max 2 ‖c‖)`).  So `Uᵘ ≥ 0` on `K_c`.  This half is
  the standard consequence of Brolin `f`-invariance `f_*μ = μ` and the antipodal symmetry
  `(−1)_*μ = μ` (via `f(z)−f(y) = (z−y)(z+y)`), both properties of the equilibrium measure.
* **Half B — Frostman domination** `PotentialDominatedOnFilledJulia c a`: `Uᵘ ≤ 0` on `K_c`
  (the equilibrium-potential maximum principle).

`Uᵘ ≥ 0` and `Uᵘ ≤ 0` give `Uᵘ = 0` on all of `K_c`, hence `EquilibriumPotentialVanishesAe`.
Half A is proved here modulo `BrolinScalingAt`; the two remaining inputs — the doubling law
(from invariance+symmetry) and the domination bound — are the sharp GAP-A frontier.
-/
import GaloisForLFunctions.Bottcher.Q62WeylDischarge

open MeasureTheory Complex Filter Metric Set

namespace Bottcher

noncomputable section

/-- Uniform upper bound on `−Uᵘ` over the filled Julia set for the target-`a` Brolin
measure: `−logPotential μ ≤ log(2·max 2 ‖c‖)` on `K_c` (from the general lower bound on
`logPotential` for any probability measure carried by `K_c`). -/
theorem neg_logPotential_limitingBrolinMeasureAt_upper_bound_of_mem_filledJulia
    {c a z : ℂ} (hz : z ∈ filledJulia c) :
    - logPotential (limitingBrolinMeasureAt c a) z ≤ Real.log (2 * max 2 ‖c‖) := by
  have h := logPotential_lower_bound_of_isProbOn_filledJulia_of_mem_escapeDisk
    (limitingBrolinMeasureAt_isProbOn_filledJulia c a) (mem_escapeDisk_of_mem_filledJulia hz)
  linarith

/-- **The potential doubling law** for the target-`a` limiting Brolin measure on `K_c`:
`−Uᵘ(f_c z) = 2·(−Uᵘ z)`.  The standard consequence of Brolin `f`-invariance and the
antipodal symmetry of the measure (`f(z)−f(y) = (z−y)(z+y)`). -/
def BrolinScalingAt (c a : ℂ) : Prop :=
  ∀ w : ℂ, w ∈ filledJulia c →
    - logPotential (limitingBrolinMeasureAt c a) (quadratic c w) =
      2 * (- logPotential (limitingBrolinMeasureAt c a) w)

/-- **Frostman domination** for the target-`a` limiting Brolin measure: `Uᵘ ≤ 0` on
`K_c` (the equilibrium-potential maximum principle, Robin constant `= 0`). -/
def PotentialDominatedOnFilledJulia (c a : ℂ) : Prop :=
  ∀ z : ℂ, z ∈ filledJulia c → logPotential (limitingBrolinMeasureAt c a) z ≤ 0

/-- **Half A (doubling ⟹ `Uᵘ ≥ 0` on `K_c`).**  From the scaling law: a point of `K_c`
with `−Uᵘ > 0` would double `−Uᵘ` along its bounded forward orbit past the uniform
upper bound.  Hence `−Uᵘ ≤ 0`, i.e. `Uᵘ ≥ 0`, on `K_c`. -/
theorem neg_logPotential_limitingBrolinMeasureAt_nonpos_of_scaling
    {c a z : ℂ} (hzK : z ∈ filledJulia c) (hscale : BrolinScalingAt c a) :
    - logPotential (limitingBrolinMeasureAt c a) z ≤ 0 := by
  by_contra hle
  have hpos : 0 < - logPotential (limitingBrolinMeasureAt c a) z := lt_of_not_ge hle
  set A : ℕ → ℝ :=
    fun n => - logPotential (limitingBrolinMeasureAt c a) ((quadratic c)^[n] z) with hAdef
  have hA : ∀ n : ℕ, A n = (2 ^ n : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z) := by
    intro n
    induction n with
    | zero => simp [hAdef]
    | succ n ih =>
        have hnK : (quadratic c)^[n] z ∈ filledJulia c := filledJulia_forward hzK n
        calc
          A (n + 1)
              = - logPotential (limitingBrolinMeasureAt c a)
                  (quadratic c ((quadratic c)^[n] z)) := by
                    simp [hAdef, Function.iterate_succ_apply']
          _ = 2 * (- logPotential (limitingBrolinMeasureAt c a) ((quadratic c)^[n] z)) :=
                    hscale ((quadratic c)^[n] z) hnK
          _ = 2 * A n := by rw [hAdef]
          _ = 2 * ((2 ^ n : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z)) := by rw [ih]
          _ = (2 ^ (n + 1) : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z) := by
                    rw [pow_succ]; ring
  set B : ℝ := Real.log (2 * max 2 ‖c‖) with hBdef
  have htend :
      Tendsto (fun n : ℕ => (2 ^ n : ℝ) * (- logPotential (limitingBrolinMeasureAt c a) z))
        atTop atTop := by
    simpa [mul_comm] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hpos
  rcases (eventually_atTop.1 (htend.eventually_gt_atTop B)) with ⟨N, hN⟩
  have hNK : (quadratic c)^[N] z ∈ filledJulia c := filledJulia_forward hzK N
  have hbound : A N ≤ B :=
    neg_logPotential_limitingBrolinMeasureAt_upper_bound_of_mem_filledJulia hNK
  have hgt : B < A N := by rw [hA N]; exact hN N le_rfl
  exact not_lt_of_ge hbound hgt

/-- **Assembly: the equilibrium potential vanishes a.e. on `K_c`** from the doubling
law (half A) plus Frostman domination (half B).  In fact it vanishes *everywhere* on
`K_c`; the a.e. form is what the GAP-A Riesz identity consumes. -/
theorem equilibriumPotentialVanishesAe_of_scaling_of_dominated (c a : ℂ)
    (hscale : BrolinScalingAt c a) (hdom : PotentialDominatedOnFilledJulia c a) :
    EquilibriumPotentialVanishesAe c a :=
  ae_of_all _ (fun z hzK => by
    have hge : 0 ≤ logPotential (limitingBrolinMeasureAt c a) z := by
      have h := neg_logPotential_limitingBrolinMeasureAt_nonpos_of_scaling hzK hscale
      linarith
    linarith [hdom z hzK])

/-- **The q62 support datum from the two sharp potential-theory halves**, for every `c`.
Composes with the Frostman-form support route (`Q62WeylDischarge`, Weyl discharged). -/
theorem limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated (c a : ℂ)
    (hscale : BrolinScalingAt c a) (hdom : PotentialDominatedOnFilledJulia c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_equilibriumVanishes c a
    (equilibriumPotentialVanishesAe_of_scaling_of_dominated c a hscale hdom)

/-- `∀`-fixed-point form of the two-half support datum, consumed by the q62 both-connected
capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated
    (c : ℂ) (hscale : ∀ a : ℂ, quadratic c a = a → BrolinScalingAt c a)
    (hdom : ∀ a : ℂ, quadratic c a = a → PotentialDominatedOnFilledJulia c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha => limitingBrolinMeasureAtSupportsJulia_of_scaling_of_dominated c a (hscale a ha) (hdom a ha)

end

end Bottcher
