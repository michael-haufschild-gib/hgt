# Instant exact complexity forces calibration singularity

- **ID:** `instant-exact-complexity-calibration-singularity-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / robustness boundary / exact-complexity conditioning law
- **Parents:** `algebraic-two-local-instant-exact-complexity.md`,
  `exact-penalty-robust-circuit-bellman-duality.md`
- **Status:** `[PAPER-PROVED] [FRONTIER CORRECTION] [NOVELTY UNVERIFIED] [LEAN CERTIFIED]`
- **Date:** 2026-08-09

## Public sentence

An ordinary rational two-local Hamiltonian can have exponential exact circuit complexity at every
nonzero algebraic instant arbitrarily close to time zero, but every Lipschitz certificate of that
jump must diverge at least inversely with time.  Exact transcendence is therefore provably
incapable of supplying a finite-resolution Brown ramp by continuity.

## Theorem -- certificate condition number of an instant exact jump

Let `(X,d)` be a metric state space, let `G` be a compact inverse-closed continuously acting
isometric gate family, and let `chi` be the reference state.  Suppose `x(t)` satisfies

\[
 d(x(t),\chi)\le v|t|                                             \tag{1}
\]

and has exact circuit complexity

\[
 C_0(x(t))\ge c_t.                                                \tag{2}
\]

Let `phi_t:X->R` be any `lambda_t`-Lipschitz Bellman certificate normalized by
`phi_t(chi)<=0` and satisfying

\[
 \phi_t(gx)\le\phi_t(x)+1\quad(g\in G),
 \qquad \phi_t(x(t))\ge c_t.                                     \tag{3}
\]

Then

\[
 \boxed{
 \lambda_t\ge {c_t\over d(x(t),\chi)}
             \ge {c_t\over v|t|}.}                              \tag{4}
\]

The identical lower bound holds for the penalty parameter of any exact-penalty Bellman value that
equals `C_0(x(t))`.

For the rational two-local Hamiltonian `H_n`, product state `Omega`, and every nonzero algebraic
real `t` from the first parent theorem, take the Hilbert-space norm metric.  Duhamel gives

\[
 \|e^{-itH_n}\Omega-\Omega\|\le |t|\,\|H_n\|_{\rm op},           \tag{5}
\]

while

\[
 C_0(e^{-itH_n}\Omega)\ge {2^n-1\over16}.                       \tag{6}
\]

Hence every such certificate obeys

\[
 \boxed{
 \lambda_{n,t}\ge
 {2^n-1\over16|t|\,\|H_n\|_{\rm op}}.}                          \tag{7}
\]

Since nonzero algebraic times accumulate at zero, no finite `lambda_n` certifies the exact
exponential jump uniformly on any punctured neighborhood of time zero.

## Proof

Lipschitz continuity and `phi_t(chi)<=0` give

\[
 c_t\le\phi_t(x(t))
 \le\phi_t(\chi)+\lambda_t d(x(t),\chi)
 \le\lambda_t d(x(t),\chi).                                    \tag{8}
\]

This proves the first inequality in `(4)`; `(1)` gives the second.  For an exact-penalty value,
the empty word in its defining minimum gives

\[
 V_{\lambda,0}(x(t))\le\lambda d(x(t),\chi),                    \tag{9}
\]

so equality with `C_0(x(t))` yields the same bound.  Equation `(5)` is the standard integral
estimate

\[
 e^{-itH_n}\Omega-\Omega
 =-i\int_0^t H_ne^{-iuH_n}\Omega\,du.                            \tag{10}
\]

Insert `(6)` into `(4)` to obtain `(7)`.

## Interpretation

The theorem identifies a condition number, not a complexity lower bound.  The exact algebraic
orbit is hard at every nonzero algebraic time, yet it lies arbitrarily close to the easy initial
state.  Any exact-complexity calibration must therefore develop exponentially steep metric
gradients.  At fixed positive resolution, the initial epsilon-ball has complexity zero and the
singular certificate carries no robust information.

This is the precise failure mechanism behind the tempting conjecture that Lindemann--Weierstrass
complexity can seed Brown growth.  The replacement problem is not stronger transcendence.  It is
a dimension-uniform separation of the static-local orbit from the positive-radius shallow-circuit
tube.

## Hostile audit

1. Equation `(4)` is elementary once the correct condition number is named.  Candidate novelty is
   the synthesis with the two-local instant-jump theorem, not the Lipschitz inequality alone.
2. The result is a no-go for one proof mechanism, not Brown growth.
3. Exact complexity and algebraic time remain physically discontinuous; no finite-resolution claim
   is inferred.
4. The application inherits every unformalized dependency of
   `algebraic-two-local-instant-exact-complexity.md` and may not enter the final manuscript before
   those dependencies are Lean-proved.  Every statement of *this* card is Lean-certified; the
   inherited dependency is only equation `(6)`, which supplies the value at which `(7)` is
   instantiated, and is not used in any proof here.

## Exact survivor

The robust frontier can be stated without transcendence language:

> Prove a constant-radius, quenched lower bound on the distance from
> `exp(-itH)chi` to every circuit layer below the Brown front, after one common return excision.

Any arithmetic certificate used for that task must carry a dimension-uniform quantitative
separation estimate, not only nonvanishing or algebraic independence.

## Lean certificate

Unconditional and closed in Lean 4; every declaration below has axiom set
`[propext, Classical.choice, Quot.sound]`.

| Card statement | Lean declaration |
|---|---|
| `(1)` linear-in-time approach | hypothesis `dist x chi ≤ v * |t|`; realized for the Schrödinger orbit by `HTGeometry.dist_evolvedState_le` |
| `(3)` Bellman certificate class | `HTGeometry.IsBellmanSubsolution` (in `HTGeometry/ExactPenaltyCircuitBellman.lean`), `HTGeometry.bellmanSubsolution_le_mul_dist` |
| `(4)` first inequality `λ_t ≥ c_t / d(x(t),χ)` | `HTGeometry.div_dist_le_lipschitzConstant_of_certificate` |
| `(4)` second inequality `λ_t ≥ c_t / (v|t|)` | `HTGeometry.div_le_lipschitzConstant_of_linear_approach` |
| `(8)` the Lipschitz chain | `HTGeometry.le_lipschitzConstant_of_certificate`, `HTGeometry.le_mul_lipschitzConstant_of_certificate_of_linear_approach` |
| `(9)` exact-penalty value bounded by the empty word | `HTGeometry.penaltyValue_le_mul_dist`, `HTGeometry.div_dist_le_penalty_of_penaltyValue` |
| `(5)`, `(10)` Duhamel displacement `‖e^{-itH}Ω - Ω‖ ≤ |t| ‖H‖` | `HTGeometry.norm_evolvedState_sub_le`, `HTGeometry.evolvedState_zero_generator`, `HTGeometry.unitaryEvolution_zero` |
| `(7)` `λ_{n,t} ≥ (2^n-1)/(16|t| ‖H_n‖)` | `HTGeometry.instant_jump_condition_number` (general form `HTGeometry.div_le_lipschitzConstant_of_evolvedState`) |
| "no finite `λ_n` certifies uniformly on a punctured neighbourhood of zero" | `HTGeometry.exists_time_lipschitzConstant_gt`, `HTGeometry.exists_time_lipschitzConstant_gt_evolvedState` |

Dependency note.  Equation `(6)`, `C_0(e^{-itH_n}Ω) ≥ (2^n-1)/16`, is the conclusion of the parent
card `algebraic-two-local-instant-exact-complexity.md` and is not re-proved here.  It is not needed
for any statement of *this* card: `(4)` and `(7)` are conditioned on the certificate reaching the
value, which is hypothesis `(3)`, exactly as on paper.  `HTGeometry.instant_jump_condition_number`
is stated at the value `(2^n-1)/16` so that the parent's bound plugs in verbatim once formalized.
This matches hostile-audit item 4 of the card.

New module: `HTGeometry/InstantCalibrationSingularity.lean`.

Reused from the corpus rather than rebuilt: `HTGeometry/ExactPenaltyCircuitBellman.lean`
(`penaltyValue`, `wordCost`, `IsBellmanSubsolution`, `le_lipschitzConstant_of_certificate`,
`le_mul_lipschitzConstant_of_certificate_of_linear_approach`),
`HTGeometry/ObserverProfileStability.lean` (`unitaryEvolution`, `norm_unitaryEvolution_sub_le`)
and `HTGeometry/ObserverInvisibleTubeShortcut.lean`
(`QuantumAlg.norm_unitaryEvolution_mulVec_sub_le`).
