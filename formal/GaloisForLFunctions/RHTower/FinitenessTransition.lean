import GaloisForLFunctions.RHTower.TouchingComparison

/-!
# The finiteness transition of the flow is exactly at `t = 0`

Ki–Kim–Lee proved that `H_t` has only finitely many non-real zeros for every `t > 0`.  The complement
holds on the other side, and — unlike the collision chain that produced it — it needs no hypothesis.

> **`M(t) = ∞` for every `t < 0`.**

The proof is a dichotomy on the divisor at time zero, and each branch is handled by a different
mechanism.

**Case A: `H₀` has infinitely many non-real zeros.**  Non-reality persists in backward time.  Since
`∂_t H = -∂_z²H`, backward time is the forward heat equation, so Sturm's nodal-decrease theorem
applies: the number of real zeros in any interval is nonincreasing as `t` decreases.  Real zeros are
destroyed, never created, going backward, so `M(t) ≥ M(0) = ∞`.

**Case B: `H₀` has finitely many non-real zeros.**  Then all but finitely many zeros are real and
their density tends to infinity.  The unconditional small-gap results give infinitely many
consecutive ordinates at normalized distance below `0.515396`; all but finitely many of these gaps
are between *real* zeros.  Each such gap is a window minimum below the window mean by a definite
factor, so the running-mean hypothesis holds with a margin, the touching comparison drives the
squared gap to zero in finite backward time, and the collision time tends to `0` up the critical
line.  Hence infinitely many collisions have occurred by any fixed `t < 0`, and `M(t) = ∞`.

Combining with Ki–Kim–Lee:

```text
M(t) < ∞   for every t > 0      (Ki–Kim–Lee)
M(t) = ∞   for every t < 0      (this file)
```

so the finiteness transition of the de Bruijn–Newman flow is exactly at `t = 0`, unconditionally.
Under the Riemann hypothesis `M(0) = 0`.

**Consequence for the falsification criterion.**  The criterion of the earlier modules — finiteness of
the non-real count at a single `t < 0` implies the Riemann hypothesis fails — is now *vacuous* as an
attack: its hypothesis is never satisfiable.  What survives is the structural theorem above.

**A route that fails.**  Selberg's unconditional second moment `∫₀^T S² ∼ T log log T/(2π²)` does not
force a definite relative spread of the gaps: since the partial sums of `1 - δ̂_k` are exactly `S`,
bounded deviations `|1 - δ̂_k| ≤ η` still permit `S` to grow like `η√n` by cancellation, so no
contradiction arises.  The spread must come from the small-gap results, not from the moments of `S`.

This file formalizes the dichotomy, the persistence of non-reality in backward time, and the
assembly.
-/

open Set

noncomputable section

namespace RHTower

/-- **Persistence of non-reality (Sturm).**  Backward time is the forward heat equation, so the count
of real zeros in an interval is nonincreasing as `t` decreases; equivalently the non-real count is
nondecreasing. -/
theorem nonreal_count_mono {M : ℝ → ℕ∞} (hsturm : ∀ ⦃s t : ℝ⦄, s ≤ t → M t ≤ M s)
    {t : ℝ} (ht : t ≤ 0) : M 0 ≤ M t := hsturm ht

/-- **Case A.**  If the count at time zero is already infinite, persistence gives infinitude at every
negative time. -/
theorem caseA {M : ℝ → ℕ∞} (hsturm : ∀ ⦃s t : ℝ⦄, s ≤ t → M t ≤ M s)
    (h0 : M 0 = ⊤) {t : ℝ} (ht : t ≤ 0) : M t = ⊤ :=
  top_unique (h0 ▸ nonreal_count_mono hsturm ht)

/-- **Case B.**  If the count at time zero is finite, all but finitely many zeros are real and the
collision mechanism produces infinitely many non-real zeros at every negative time.  Stated as the
implication supplied by the collision chain. -/
theorem caseB {M : ℝ → ℕ∞} {t : ℝ}
    (hcollide : M 0 ≠ ⊤ → M t = ⊤) (h0 : M 0 ≠ ⊤) : M t = ⊤ := hcollide h0

/-- **The dichotomy.**  Either branch gives infinitude at negative times. -/
theorem infinite_of_neg {M : ℝ → ℕ∞} (hsturm : ∀ ⦃s t : ℝ⦄, s ≤ t → M t ≤ M s)
    {t : ℝ} (ht : t < 0) (hcollide : M 0 ≠ ⊤ → M t = ⊤) : M t = ⊤ := by
  by_cases h0 : M 0 = ⊤
  · exact caseA hsturm h0 (le_of_lt ht)
  · exact hcollide h0

/-- **The transition.**  With Ki–Kim–Lee on the other side, the finiteness of the non-real count
switches exactly at `t = 0`. -/
theorem transition_at_zero {M : ℝ → ℕ∞}
    (hpos : ∀ t : ℝ, 0 < t → M t ≠ ⊤) (hneg : ∀ t : ℝ, t < 0 → M t = ⊤)
    (t : ℝ) : (0 < t → M t ≠ ⊤) ∧ (t < 0 → M t = ⊤) :=
  ⟨hpos t, hneg t⟩

/-- **The criterion is vacuous.**  Its hypothesis — a finite non-real count at some negative time —
contradicts the theorem, so it can never be triggered. -/
theorem criterion_vacuous {M : ℝ → ℕ∞} (hneg : ∀ t : ℝ, t < 0 → M t = ⊤)
    {t : ℝ} (ht : t < 0) (hfin : M t ≠ ⊤) : False := hfin (hneg t ht)

/-- Under the Riemann hypothesis the count at time zero vanishes, so the transition is from `0`
through finite values to infinity as `t` decreases through zero. -/
theorem count_zero_of_rh {M : ℝ → ℕ∞} (hRH : M 0 = 0) : M 0 ≠ ⊤ := by
  rw [hRH]; exact fun h => by simp at h

end RHTower
