# The Hodge sign of the constructed pairing on the reflection-odd carrier

- **ID:** hodge-sign-wall-constructed-pairing
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, unconditional survivors) + open core (the mass-zero law)
- **Source:** step 3 of the intersection-form programme; successors of
  `gauss-propagated-iterate-log-mean` and `gauss-multiplace-label-faithful-assembly`
- **Statement (what is now proved):** The pairing of the two retained reflection-odd components
  of the source-zero horizontal carrier, weighted by the assembled residue current, is an
  unconditionally positive-semidefinite, reflection-even, label-faithful current with the exact
  critical radical: `H(q,p) = (log 2/2)·current(p)·density(p)·t_q·(p^{t_q} − p^{−t_q}) ≥ 0`
  with `t_q = 2 Re(q) − 1`, `H = 0 ↔ Re(q) = 1/2`, and `H` invariant under the line-conjugate
  reflection.  **The Hodge sign of the constructed pairing holds.**  The Hodge-index
  application — total mass zero, forcing every copy onto the line — is proved equivalent to RH.
- **Open core `[OPEN CORE]` (refined by attempt 4):** the divisor average of the moment-curve
  convexity defect.  The prime side is now completely evaluated: `H` is two-sidedly equivalent
  to the Burnol seam reflection energy, whose full prime sum at a copy equals
  `M(1+2σ) + M(3−2σ) − 2·M(2)` with `M(β) = Σ_p (log p)² p^{−β}` — an explicit strictly convex
  Dirichlet moment curve.  RH ⟺ the divisor annihilates this convexity defect.  What is missing
  is exactly one horizontal divisor transform: an evaluation of `Σ_ρ (samples of Re ρ)` that no
  holomorphic (explicit-formula) channel can perform — formalized as the information-gap
  theorem below.

## The wall, well-posed

Step 3 asked for the Hodge sign of the assembled pairing on the reflection-odd carrier.  The
carrier retains two odd components per Xi copy (the cofinal tail log and the prime-labelled
Gamma Bockstein), both reversing under `ρ ↦ 1 − conj ρ` and both vanishing exactly on the line.
Their product — the natural quadratic pairing of the odd part with itself, weighted by the
strictly positive assembled residue current — is therefore an *odd-square*: nonnegative by
construction-level algebra, even under reflection, zero exactly on the line.  This is created
positivity in the corpus's sense (it is manufactured by pairing the two retained orientations,
not inherited from an ambient cone), and it converts the wall from a sign question into a mass
question:

```
RH  ⟺  the unconditionally nonnegative current H has zero total mass
     ⟺  every label of every copy sits at the bottom of the hyperbolic mass shell t·(p^t−p^{−t}).
```

## Attempts and pivots (this card's audit trail)

**Attempt 1 — self-dual operator subtraction (the conjectured mechanism).**  Finitize the
divergent raw positive corner by exchanging with its Poisson/Fourier dual instead of truncating.
On the theta side this reproduces exactly the classical self-dual representation of the
completed zeta (the `∫₀^∞ = ∫₁^∞ + dual + poles` exchange): it yields manifest FE symmetry at
operator level and reality on the critical line — but the sign of the exchanged remainder
against critical-line oscillation is equivalent to the mass-zero statement itself.  *Exact
failure point: the dual exchange preserves positivity only where the kernel does not oscillate;
making it global is the wall, not a route around it.*

**Attempt 2 — FE as an antiunitary intertwining of the actual compact operator (PT structure).**
An intertwiner implementing `ρ ↦ 1 − conj ρ` on the Hedenmalm theta-source inverse would make RH
an "unbroken-phase" statement.  Killed as a *producer* by the corpus's conjugation-blindness
no-go: any use of the intertwiner that factors through the divisor-level reflection yields no
sign.  Surviving requirement, recorded for future work: the intertwiner must come with a
definitizable Krein structure — which is again the missing positivity, now in Krein form.

**Attempt 3 — trace-identity evaluation of the H-mass.**  The explicit formula (Poisson on the
idele classes — the only ℤ-specific global identity in reach) evaluates holomorphic samples
`∑ g(ρ)²`; the H-mass is a non-holomorphic square (`|odd part|²`-type).  This is the corpus's
`∑g² vs ∑|g|²` gap in exact form.  *Sharpened Poisson conjecture (the successor of the step-3
mechanism conjecture): a bilinear/Poisson upgrade of the explicit formula that reaches one
positive-definite non-holomorphic sample of the divisor — equivalently one trace identity with
target the `H`-mass — closes RH.  Nothing weaker suffices, by the firewall below.*

**Pivot outcome.**  The sign itself is free once the two odd orientations are paired — proved
below.  All difficulty is the mass evaluation; the firewall shows it cannot come from the
pairing's own interface.

**Attempt 4 — the seam-energy pivot (two lanes, one invariant).**  Pushing on the sharpened
Poisson conjecture revealed that the corpus already owns the prime side.  The Burnol
FE–Schwarz seam layer (`orbitwiseScaleSeamCharge`, `XiPrimeSeamReflectionEnergy`,
`XiPrimeSeamPairAsymptotics`) carries a reflection-energy density
`‖seam(p,ρ)‖²/p = (log p)² p^{−2} (p^t + p^{−t} − 2)`, `t = 2 Re ρ − 1` — the centered cosh
defect.  The Hodge mass shape `t(p^t − p^{−t})` and the cosh defect dominate each other with
explicit hyperbolic constants (`log p / 2` one way at every rate; `2√p / log p` the other way
on `|t| ≤ 1`, and every divisor copy lies in the open strip — now also formalized).  Hence
**the Gauss-lane Hodge mass current and the Burnol seam reflection energy are the same
invariant**, two-sidedly, pointwise, unconditionally, and:

```
RH ⟺ prime-2 seam charge = 0 on the divisor
   ⟺ the prime-2 Burnol character is unimodular on the divisor
   ⟺ full prime-summed seam energy = 0 on the divisor
   ⟺ divisor annihilates the moment-curve convexity defect M(1+2σ)+M(3−2σ)−2M(2).
```

The last form is the sharpest: the prime sum is completely evaluated (corpus theorem,
`Σ_p`-side absolutely convergent in the open strip), so the entire open core has been pushed
into the single divisor average `Σ_ρ`.  **Formal fencing of that residue:** the FE-pair sample
`char(ρ)·char(1−ρ) ≡ 1` is constant — divisor-blind — and *no function of it computes the
Hermitian sample* `‖char(ρ)‖` (impossibility theorem).  This is the `Σg²` vs `Σ|g|²` gap as a
theorem about the exact objects of this card.  External anchors for the analytic family:
Weil/Bombieri quadratic functional; Suzuki's screw function (arXiv:2206.03682) parametrizes
divisor-summed cosh defects; Connes–Consani Weil positivity via Sonin/prolate compression
(arXiv:2006.13771, arXiv:2310.18423) is the operator route to the same missing positivity.
Corpus no-gos fencing the divisor average: density envelopes cannot decide it
(`density-envelope-cannot-decide-rh`), and its bilinear/Poisson upgrade lands on
diagonal-vs-off-diagonal separation — the MR/correlation wall
(`mr-bilinear-scope-boundary`, `route-e-dependency-reduced-to-correlations`).

**Attempt 5 — conjugate-pair classification and the coherence budget.**  Two further
unconditional laws price the residual transform (`GaussHodgeCoherenceBudget.lean`):

1. *Conjugate-pair classification.*  The divisor is conjugation-closed
   (`xiZeroCopyConjEquiv`, point law by `rfl`), and at every copy
   `char(ρ)·char(conj ρ) = p^{2 Re ρ − 1}`: the Hermitian sample the transform must reach is
   the holomorphic bilinear kernel evaluated at the conjugate copy pair.  The wall is
   *literally* the conjugate-pair diagonal of a squared explicit formula — the
   pair-correlation classification, as a theorem rather than a remark.
2. *Coherence budget.*  Cauchy–Schwarz on any finite copy family `F` with weights `v`:
   `‖Σ_F v(q)·char(q)‖² ≤ (Σ‖v‖²)·(cosh-defect mass of F + 2·|F|)`.  The Hodge/seam mass is
   an exact upper-bound certificate for zero-side exponential-sum coherence at frequency
   `log p`; under RH the budget collapses to the diagonal count `2·|F|` (square-root
   cancellation per frequency, from mass-zero alone).  This ties the Gauss/Burnol invariant to
   the rectangular `ψ(x) − x` carrier's vocabulary at the finite level.

**The successor gate (exact next `[OPEN CORE]` refinement).**  For finite families the
conjugate-pair diagonal *is* reachable: vertical time-averaging
`(1/T)∫ |Σ_q v_q e^{i Im(ρ_q) t} char(q)|² dt → diagonal` by Kronecker/Weyl character
orthogonality — the corpus's completed-time torus layer owns these assets
(`TorusCharacterMean`, `LinearPhaseObservable`, equidistribution).  Two exact obstructions
remain, both already named in the corpus: (i) the extraction yields a multiplicity-*squared*
diagonal (`m_ρ²` vs `m_ρ`) — the gap closes exactly on zero-simplicity
(`cauchy-core-density-is-zero-simplicity`); (ii) the explicit formula reaches the full zero
sum, so the diagonal identity requires exchanging `T → ∞` with the infinite-divisor
truncation — the exchange the co-Poisson layer proved must be done truncate-first
(`copoisson-mellin-truncate-first`).  The open core is thus a *limit-exchange* statement: an
interchange of the vertical mean with the divisor closure, priced by multiplicity squares.

## Kill-tests passed and formalized

1. **Beurling/interface firewall (formalized).**  The sign, evenness, and radical laws of the
   pairing hold for arbitrary label sizes `s > 1` and arbitrary rate configurations — they are
   pure interface algebra.  An explicit reflection-closed off-line configuration (`t = ±1/2`,
   `s = 2`) has strictly positive mass.  Hence *no proof from the pairing's local interface,
   even assuming closure under the divisor reflection, can force mass-zero*: the step-3 proof
   must consume data distinguishing the actual Xi divisor — global Poisson/bilinear input.
   (`hodgeMass_interface_cannot_force_vanishing`.)
2. **Conjugation blindness (formalized inside the firewall).**  The positive-mass witness is
   closed under `t ↦ −t`: reflection symmetry of the configuration does not reduce the mass,
   because `H` is even.  So `conj ρ = 1 − ρ` alone can never force vanishing — matching the
   corpus's no-go, now at this exact pairing.
3. **Re-encoding audit.**  The mass-zero ⟺ RH equivalence is an RH-equivalent statement and is
   labeled as the open core, not as progress.  What is claimed as progress: the unconditional
   positivity/evenness/radical laws, the closed hyperbolic form, and the firewall — none of
   which were previously formalized for this object.

## Gates
- [x] 0 → 1  wall frozen for the constructed pairing; attempts 1–3 run and recorded
- [x] 1 → 2  unconditional survivors paper-proved (short algebra over the carrier's closed forms)
- [x] 2 → 3  formalized: `RHTower/GaussHodgeMassCurrent.lean`; umbrella-wired; axiom-clean
- [ ] `[OPEN CORE]` the mass-zero trace identity (sharpened Poisson conjecture above)

## Log
- 2026-08-11 — created; attempts 1–3 executed and recorded; Hodge sign proved for the
  constructed pairing (odd-square positivity); mass-zero ⟺ RH formalized; boost-square closed
  form formalized; interface firewall formalized with reflection-closed positive-mass witness.
- 2026-08-11 — attempt 4 (seam-energy pivot) executed: Hodge mass current proved two-sidedly
  equivalent to the Burnol seam reflection energy (`RHTower/GaussHodgeSeamEnergyBridge.lean`,
  with the hyperbolic comparison layer appended to `HTGeometry/HyperbolicBounds.lean`).  New
  unconditional theorems: strip placement of every divisor copy; seam density in cosh-defect
  form; per-scale seam-charge critical-line law; two-sided Hodge↔seam domination with explicit
  constants; RH ⟺ prime-2 seam charge vanishing ⟺ prime-2 character unimodularity ⟺ full seam
  energy vanishing; seam energy at a copy = moment-curve convexity second difference; the
  information-gap impossibility theorem (no function of the FE-pair sample computes the
  Hermitian sample).  Open core refined to the divisor average of the moment-curve convexity
  defect.
- 2026-08-11 — attempt 5 formalized: `RHTower/GaussHodgeCoherenceBudget.lean` (conjugate-pair
  classification `char(ρ)·char(conj ρ) = p^{2Reρ−1}` at copies; Cauchy–Schwarz coherence
  budget; RH collapse to `2·|F|`).  Both new modules + hyperbolic layer build clean,
  umbrella-wired, axiom-audited (`propext, Classical.choice, Quot.sound` only, 17 theorems).
  Successor gate recorded: limit-exchange of the vertical time-mean with the divisor closure,
  priced by multiplicity squares (torus-mean assets; zero-simplicity layer; truncate-first
  no-go).
