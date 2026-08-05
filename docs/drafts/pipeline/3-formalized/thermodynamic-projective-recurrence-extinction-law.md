# Thermodynamic projective-recurrence extinction law

- **ID:** `thermodynamic-projective-recurrence-extinction-law`
- **Stage:** 3-formalized
- **Type:** THEOREM TARGET / STATIC LOCAL MANY-BODY RECURRENCE
- **Date:** 2026-08-05
- **Status:** `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md`
- **Statement:** At every fixed strict projective resolution, generic static
  nearest-neighbour qudit paths have an exact return-density large-deviation
  law in Hilbert-space dimension, and their return density vanishes doubly
  exponentially in chain length.

## Exact claim

Fix an onsite dimension `q >= 2` and a strict coordinatewise projective
return tolerance `0 < epsilon < 2`. Put

\[
 a_\varepsilon=
 \frac{2\arcsin(\varepsilon/2)}{\pi},
 \qquad
 I(\varepsilon)=-\log a_\varepsilon.
\]

Then `0 < a_epsilon < 1` and `I(epsilon) > 0`. For every `n >= 2`, the
dense residual full-measure maximal subset of the trace-zero static
onsite-plus-nearest-neighbour Hamiltonian space on the open `n`-site
`q`-level path has completed strict-return density

\[
 d_n(\varepsilon)
 =a_\varepsilon^{q^n-1}
 =\exp\!\left[-(q^n-1)I(\varepsilon)\right].       \tag{1}
\]

Consequently

\[
 \lim_{n\to\infty}d_n(\varepsilon)=0,
 \qquad
 \lim_{n\to\infty}
   \frac{-\log d_n(\varepsilon)}{q^n}
 =I(\varepsilon),                                  \tag{2}
\]

and

\[
 \lim_{n\to\infty}
 \frac{\log[-\log d_n(\varepsilon)]}{n}
 =\log q.                                           \tag{3}
\]

Equation (2) is the exact thermodynamic large-deviation rate in Hilbert-space
dimension. Equation (3) says the completed global-return density vanishes
doubly exponentially in physical chain length.

## Internal frontier

- `[CORPUS]` `exists_uniformQuditPathTracelessRecurrenceGeometry_dense_residual_fullMeasure`
  proves the exact finite-volume density in (1), maximal rank `q^n-1`, and
  absence of nonzero exact return.
- `[LOCAL-RESEARCH]` `interaction-topology-universal-quantum-recurrence-law.md`
  already records thermodynamic moment limits for a fixed number of
  disconnected components, but explicitly excludes infinite-volume
  recurrence.
- `[CORPUS]` the stationary spectral-measure laws classify genuine
  infinite-carrier recurrence by pure-point versus atomless spectral mass.
- `[CORPUS]` the infinite l-bit modules construct a genuine quasi-local
  infinite evolution with maximal rank on every finite restriction, but do
  not identify an infinite-volume global recurrence measure.

## External frontier

- `[LITERATURE]` Campos Venuti, *The recurrence time in quantum mechanics*,
  arXiv:1509.04352, derives generally double-exponential recurrence-time
  scaling for generic nonintegrable many-body systems under rational-
  independence and Gaussian approximations.
- `[LITERATURE]` Campos Venuti and Zanardi, arXiv:0907.0683, and Campos
  Venuti et al., arXiv:1104.3232, study long-time Loschmidt-echo
  distributions and their large-system limits, including model-dependent
  exponential, Gaussian, and critical regimes.
- `[LITERATURE]` Karimi et al., *Phys. Rev. Research* 8, L012062 (2026),
  give multiqubit revival scaling for a specific weakly open protocol.

No novelty is claimed for the words “double exponential,” for elementary
power asymptotics, or for a thermodynamic limit of a torus volume. The exact
residue is the unconditional composition with generic all-order maximal
projective rank inside the full static one-dimensional bounded-degree local
Hamiltonian family.

## Hostile attack

1. **Finite-corollary attack.** Equations (1)--(3) follow immediately once
   the finite local theorem is known. Verdict: `[BRIDGE]` as a separate
   mathematical mechanism; useful scope completion, not an independent
   novelty headline.
2. **First-return attack.** Density does not determine first-hitting-time
   distribution or a uniform mixing time. Verdict: claim must remain about
   completed time density only.
3. **Infinite-Hamiltonian attack.** Genericity is stated separately in each
   finite coefficient space and does not construct a translation-invariant
   or norm-convergent infinite-volume Hamiltonian. Verdict: “thermodynamic
   limit” means exact finite-volume scaling of the completed recurrence
   density, not existence of global infinite-volume recurrence.
4. **Order-of-limits attack.** Time completion is taken before `n -> infinity`.
   Reversing limits requires a separately specified compatible Hamiltonian
   sequence and local observable topology. Verdict: state order explicitly.
5. **Target attack.** Coordinatewise projective return is a strong global
   operator-phase target, not a fixed-local-observable return. Verdict: keep
   “global projective” in theorem name and interpretation.

**Verdict:** `SURVIVES AS AN EXACT THERMODYNAMIC COROLLARY; BRIDGE, NOT NEW
MECHANISM`.

## Complete paper proof

Let

\[
 a=a_\varepsilon=\frac{2\arcsin(\varepsilon/2)}{\pi}.
\]

Because `0 < epsilon/2 < 1`, strict monotonicity of `arcsin` on `(-1,1)`
gives

\[
 0<\arcsin(\varepsilon/2)<\pi/2,
\]

and hence `0 < a < 1`. Therefore `log a < 0` and
`I(epsilon)=-log a>0`.

For every fixed `n >= 2`, the formalized generic static-path recurrence law
gives a dense residual full-measure set of trace-zero onsite-plus-edge
Hamiltonians with maximal projective rank `q^n-1` and completed strict-return
density

\[
 d_n(\varepsilon)=a^{q^n-1}.
\]

Since `a>0`, the real power identity gives

\[
 a^{q^n-1}
 =\exp((q^n-1)\log a)
 =\exp(-(q^n-1)I(\varepsilon)),
\]

which proves (1).

Because `q>=2`, `q^n-1 -> infinity`; because `0<a<1`,
`a^{q^n-1}->0`. This proves the first limit in (2). Taking logarithms in
(1) gives the exact identity

\[
 \frac{-\log d_n(\varepsilon)}{q^n}
 =\left(1-q^{-n}\right)I(\varepsilon).
\]

Since `q^{-n}->0`, the right side tends to `I(epsilon)`, proving the second
limit in (2).

Finally,

\[
 \begin{aligned}
 \frac{\log[-\log d_n(\varepsilon)]}{n}
 &=\frac{\log(q^n-1)+\log I(\varepsilon)}{n}\\
 &=\log q+
   \frac{\log(1-q^{-n})}{n}+
   \frac{\log I(\varepsilon)}{n}.
 \end{aligned}
\]

Both remainder terms tend to zero, proving (3).

All limits take completed symmetric-time frequency first at fixed `n`, then
`n -> infinity`. The proof supplies no reversed-limit statement, first-return
distribution, translation-invariant infinite Hamiltonian, or local-observable
thermodynamic law. This closes every stated dependency.

## Formalization target

Implemented in
`formal/GaloisForLFunctions/HTGeometry/ThermodynamicProjectiveRecurrenceExtinctionLaw.lean`.

Load-bearing declarations:

- `thermodynamicProjectiveRecurrenceExtinctionLaw`;
- `quditPathProjectiveReturnDensity_tendsto_zero`;
- `normalized_neg_log_quditPathProjectiveReturnDensity_tendsto_rate`;
- `doubleLog_quditPathProjectiveReturnDensity_tendsto_log_q`.

Direct module compilation and the complete `GaloisForLFunctions.HTGeometry`
area build pass. `scripts/formal_tools.py lint --check-generated` passes.
Every load-bearing `#print axioms` report is exactly
`[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-05 — Card opened after user requested thermodynamic-limit behavior.
  Internal audit separated existing infinite spectral/localized recurrence
  laws from the thermodynamic scaling of the new generic local-path theorem.
