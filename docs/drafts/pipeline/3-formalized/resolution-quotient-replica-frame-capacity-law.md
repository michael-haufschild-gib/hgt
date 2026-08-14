# Resolution-quotient replica frame-capacity law

- **ID:** `resolution-quotient-replica-frame-capacity-law`
- **Stage:** 3-formalized
- **Type:** exact target-geometry theorem / Brown-frontier bridge
- **Parent:** `centralizer-centered-shortcut-history-recurrence-energy-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED SURVIVOR] [BRIDGE]`
  `[APPLICATION NOVELTY UNVERIFIED] [PARENT COMPOSITION FORMALIZED]`
- **Date:** 2026-08-14

## Public sentence

Quantum alternatives must be counted only after observationally indistinguishable alternatives are
identified: replica amplification then turns the resulting distinguishable alternatives into an
inverse-capacity frame.

## Exact frontier

`[CORPUS]` `StaticShortcutRecurrenceEnergyLaw.lean` factorizes every adaptive shortcut history into
conditioned target frame energy times centralizer-centered recurrence energy.

`[CORPUS]` `StaticShortcutReplicaProjectorFrameLaw.lean` identifies the target frame energy exactly
as complete average replica fidelity.

`[OPEN CORE]` The current master card asks for inverse-capacity average replica fidelity of the
occupied shallow-circuit image and a quenched recurrence-energy estimate for an ordinary one-draw
static local Hamiltonian.

## Failure-driven conjecture loop

### C0 -- raw occupied cardinality forces inverse frame energy

For every finite family of distinct normalized rays and a replica order chosen from its cardinality,
the complete average replica fidelity should be `O(1/N)`.

**Verdict:** `[FALSIFIED]`.

Fix `N,r` and `q<1`.  In `C^2`, let

```text
psi_t = (e_0+t e_1)/sqrt(1+t^2),       0<t<tau.
```

Choose `N` distinct parameters in `(0,tau)`.  For `s,t` in that interval,

```text
|<psi_s,psi_t>| >= 1/(1+tau^2),
Fidelity(psi_s,psi_t)^r >= (1+tau^2)^(-2r).
```

Taking `tau` sufficiently small makes every ordered-pair replica fidelity exceed `q`, hence makes
their normalized average exceed `q`.  Distinctness, duplicate removal, and finite replica order do
not imply any inverse-cardinality ceiling.

**Exact why:** raw endpoint count is not observational capacity.  Near-duplicate rays can have
arbitrarily large cardinality and frame energy arbitrarily close to one.

**Representation lesson:** form the finite-resolution quotient before taking replica moments.
Minimum separation is wrong as a hypothesis on an inherited raw target list, but separation is
canonical after replacing that list by a maximal packing at the observer's resolution.

### C1 -- resolution quotient before replica amplification

`[PAPER-PROVED]` A maximal finite-resolution packing of the target image is simultaneously a cover of
the full image and an inverse-capacity replica frame, with an explicit finite-replica remainder.

The C0 obstruction no longer applies: a `delta`-separated packing contains at most one member from
every `delta`-cluster, while its covering property preserves the complete target union with exactly
one `delta` of radius slack.

## Frozen theorem

Let `I` be a nonempty finite type and let `psi_i` be normalized pure states.  Write

```text
P_i = |psi_i><psi_i|
d(i,j) = ||P_i-P_j||_HS.
```

Fix `0<delta<=sqrt(2)`.  Give `I` the pseudometric induced by `i |-> P_i`, and let `S_delta` be a
maximum-cardinality `delta`-separated subset.  Put `N_delta=|S_delta|` and
`kappa_delta=1-delta^2/2`.

Then:

```text
(RQ1)  for every i in I there exists c in S_delta with d(i,c)<=delta;

(RQ2)  for distinct c,e in S_delta,
       Fidelity(psi_c,psi_e) <= kappa_delta;

(RQ3)  F_r(S_delta)
       := N_delta^(-2) sum_(c,e in S_delta)
            Fidelity(psi_c,psi_e)^r
       <= N_delta^(-1)
          +(1-N_delta^(-1)) kappa_delta^r;

(RQ4)  if kappa_delta^r<=N_delta^(-1), then
       F_r(S_delta)<=2 N_delta^(-1).
```

The cover also transfers every complete approximate target event.  For every normalized state
`x`, if `d(P_x,P_i)<=epsilon` for some `i`, then for some `c in S_delta`,

```text
(RQ5)  d(P_x,P_c)<=epsilon+delta.
```

Equivalently,

```text
Fidelity(x,psi_c) >= 1-(epsilon+delta)^2/2.                 (RQ6)
```

If additionally `epsilon+delta<=sqrt(2)`, the right side `a_delta` is nonnegative and the
replica-projector alignment is at least `a_delta^r`.

Consequently, applying the observer--spectral reciprocity law to the center dictionary at replica
order `r` replaces the target factor by at most `2/N_delta` whenever `(RQ4)` holds.  If the
conditioned universal sector is subtracted, its frame energy is smaller still.  Thus a weighted
history of transferred shortcut alignments at level `eta` forces

```text
(eta sum_j w_j)^2
  <= (2/N_delta) R_w,
```

where `R_w` is the same centralizer-centered recurrence energy as in the parent theorem.

## Dependency-closed proof plan

1. Mathlib's maximal-separated-set theorem gives `(RQ1)` and separation of `S_delta`; finiteness of
   `I` makes the packing number finite.  Nonemptiness of `I` makes `N_delta>0`.
2. For normalized projectors,

   ```text
   ||P_c-P_e||_HS^2
     = ||P_c||_HS^2+||P_e||_HS^2-2<P_c,P_e>_HS
     = 2-2 Fidelity(psi_c,psi_e).
   ```

   Separation and `delta>=0` give `(RQ2)`.
3. Split the ordered pair sum in `F_r` into its `N_delta` diagonal pairs and
   `N_delta(N_delta-1)` off-diagonal pairs.  Diagonal fidelity is one.  Since
   `0<=kappa_delta<=1`, `(RQ2)` and monotonicity of `x |-> x^r` give `(RQ3)`.
4. Substitute `kappa_delta^r<=N_delta^(-1)` in `(RQ3)` and use
   `1-N_delta^(-1)<=1` to obtain `(RQ4)`.
5. `(RQ5)` is the triangle inequality followed by `(RQ1)`.  The same projector-distance identity
   gives `(RQ6)`.
6. The parent recurrence law uses the uniform preparation moment of the supplied target family.
   Supply the center dictionary, transfer each shortcut by `(RQ5)--(RQ6)` at replica threshold
   `a_delta^r`, bound its conditioned
   frame energy by its unconditioned frame energy, and apply `(RQ4)`.

## Hostile attack checklist

- **Empty target:** excluded by `Nonempty I`; otherwise inverse cardinality is undefined.
- **Duplicate rays:** induced pseudometric allows zero distance; a separated packing selects at
  most one at positive `delta`, while the cover retains every duplicate.
- **Global phases:** projector coordinates identify them exactly.
- **Radius loss:** explicit and unavoidable; no event is claimed at the original radius.
- **Large replica order:** theorem gives an exact finite-`r` remainder.  Existence of suitable `r`
  follows only for `delta>0`; no uniform system-size rate is inferred without a packing scale.
- **Ambient dimension:** no dimension enters `(RQ1)--(RQ6)`.
- **Circuit labels:** capacity is metric packing of the occupied endpoint image, not word count.
- **Brown onset:** target factor alone does not bound `R_w`; no first-time or ramp claim follows.

## External parentage and priority boundary

- `[LITERATURE]` Maximal separated sets covering a metric set are standard metric-entropy theory;
  mathlib cites Vershynin's *High-Dimensional Probability* for this fact.
- `[LITERATURE]` Tensor-power Gram moments and Welch/frame-potential bounds are classical; see the
  Welch-bound lineage summarized in <https://arxiv.org/abs/2201.00319>.
- `[LITERATURE]` Random/stochastic dynamical complexity results use approximate designs rather than
  this resolution quotient: <https://arxiv.org/abs/2205.09734>.
- `[LOCAL-RESEARCH]` The parent observer--spectral law is the first local place where the target
  factor appears as complete average replica fidelity.  No local card currently performs the
  resolution quotient before that factor.

The metric packing and moment estimate are bridges, not claimed new mathematics in isolation.
Priority of their exact adaptive-static-recurrence composition is unverified.  Scientific value is
the frontier correction: raw target-image anti-concentration is impossible universally, whereas
resolution-quotient inverse capacity is dependency-closed and leaves only the ordinary static-H
recurrence-energy estimate.

## Promotion gates

- [x] exact frontier and falsifier recorded
- [x] replacement claim frozen
- [x] dependency-closed proof survives line-by-line hostile audit
- [x] exact positive-survivor Lean theorem, no proof debt
- [x] umbrella wiring and axiom audit

## Lean certificate

Formalized companion:
`resolution-quotient-replica-frame-capacity-law-formalized.md`.

Module:
`GaloisForLFunctions.HTGeometry.ResolutionQuotientReplicaFrameCapacityLaw`.

Lean proves `(RQ1)--(RQ6)`, the finite-replica frame remainder, the `2/N_delta` regime,
all-replica fidelity transfer, and the capstone substitution of `2/N_delta` into the adaptive
observer--spectral recurrence-energy law.  The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The illustrative C0 qubit family is not a declaration in this
module and must not be advertised as Lean-certified until its separate no-go theorem exists.
