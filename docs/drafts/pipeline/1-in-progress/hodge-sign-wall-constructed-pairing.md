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

**Attempt 6 — the truncation exchange is proven (`GaussHodgeVerticalExtraction.lean`).**  The
feared half of the limit-exchange gate is not a wall.  Theorem
(`tendsto_tsum_pencil_cesaro_star_mul` / `_norm_sq`): for ANY absolutely summable coefficient
family on ANY index and ANY unimodular mode family — with no separation, gap, injectivity, or
correlation hypothesis — the Cesàro mean of the squared pencil converges to the equal-mode
pair diagonal.  Proof: dominated convergence over coefficient pairs against the ℓ¹ × ℓ¹
product, the scalar geometric Cesàro law deciding each pair.  (Externally this is Bohr's
almost-periodic Parseval `[REDISCOVERED]`; corpus-new at infinite index without gap
hypotheses — the corpus's own `GeneralizedDirichletMeanValue` is finite-polynomial only.)
Instantiated at the divisor (`tendsto_cesaro_divisorCharPencil_norm_sq`): for every ℓ¹ weight
on the Xi copies, the vertical flow extracts the equal-ordinate pair diagonal from the squared
weighted Burnol character pencil, over the FULL divisor, unconditionally (the strip bound
supplies the uniform character bound).  The reflected partner shares the ordinate
(`xiZeroCopyVerticalMode_lineConjEquiv`), and the reflection-odd `2×2` block of the extracted
diagonal is exactly the centered cosh defect (`charPair_oddBlock`) — the extracted diagonal
carries the Hodge/seam mass, and is nonnegative as a limit of mean squares.

**The wall after attempt 6 — the final relocation.**  With extraction and truncation both
proven, the only unproven step left in the entire chain is *sourcing the pencil*: the vertical
mode `exp(i·Im ρ)` is a conjugate-pair (bilinear) sample of the divisor — `Im ρ` needs `ρ` and
its conjugate zero — and the information-gap theorem proves no holomorphic channel supplies
it.  The open core in final form: **produce the values of the ℓ¹ vertical pencil
`Σ_ρ v_ρ · char(ρ) · e^{i n Im ρ}` from prime-side data** (for one good weight family `v`).
Every other step — extraction, truncation, positivity, the mass identification, the RH
equivalence — is now an unconditional Lean theorem.

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
- 2026-08-11 — attempt 6 formalized: `RHTower/GaussHodgeVerticalExtraction.lean` (ℓ¹ limit
  exchange with no gap/separation/correlation input; divisor instantiation; ordinate-sharing of
  reflected pairs; odd-block = cosh defect; positivity).  Build green, umbrella-wired,
  axiom-clean (6 theorems).  Open core final form: sourcing the ℓ¹ vertical pencil from
  prime-side data — the single remaining unproven step of the whole chain.
- 2026-08-11 — attempt 7 formalized: `RHTower/GaussHodgePencilSourcing.lean`.  The vertical
  mode has a holomorphic FE companion `e^{ρ−1/2}`; the sourcing identity
  `char_p(ρ)·(e^{ρ−1/2})ⁿ = char_{p·eⁿ}(ρ)` shows the companion pencil is the one-variable
  zero current at flowed scales — explicit-formula data; the companion's polar factorization
  exhibits the sourcing defect as the radial mass factor `e^{t/2}`; and **sourcing ⟺ RH** is
  proved in two exact forms (`riemannHypothesis_iff_feMode_eq_verticalMode`,
  `riemannHypothesis_iff_feMode_unimodular`), with the conditional collapse
  (`verticalPencil_eq_flowedScaleCurrent_of_riemannHypothesis`): under RH every value of the
  vertical pencil is prime-side data.  The programme is now one closed equivalence loop, every
  link an unconditional Lean theorem; the single non-circular entry point left is an
  independent evaluation of the vertical pencil, which the formalized information-gap and
  firewall theorems prove must consume bilinear (conjugate-pair) input.

## Where a non-circular formal proof can enter (assessment, 2026-08-11)

Every route in corpus and literature funnels to exactly two dual gates; the loop's theorems
say precisely what each must produce.

**Gate I — cancellation (analytic side).**  By the sourcing module, RH ⟺ every ℓ¹-weighted
flowed-scale zero current `Σ_ρ v_ρ x^{ρ−1/2}`, `x = p·eⁿ`, stays bounded in `n` (converse via
the singleton weight at the right-half representative of an off-line zero; forward trivial
under unimodularity).  Each such current is explicit-formula data, so this gate is an
unconditional O(1)-bound for smoothed prime sums — the rectangular terminus
(`rectangular-programme-terminus`), in the smoothed form that dodges Littlewood's Ω.  The
mechanism it needs is a source of cancellation that does not factor through zero-free regions
(capped: `zero-free-region-exponent-is-the-mr-wall`, `moebius-saving-exponent`), density
envelopes (no-go), or correlations at Montgomery-diagonal strength (the MRBilinear boundary).
No such mechanism exists in corpus or literature; this gate is where the loop says the
analytic lanes must land, not where a proof is visible.

**Gate II — created positivity (spectral/geometric side).**  The two proofs of RH-type
statements that exist in mathematics both enter here, by manufacturing positivity from a
structure exogenous to the divisor interface: the function-field proof via the Hodge index
theorem on the self-product `C×C` (the two-variable object whose diagonal is the otherwise
unreachable conjugate-pair diagonal — exactly what our classification theorem says is
needed), and Connes–Consani's semi-local theorem via Sonin/prolate compression (positivity of
a compressed trace is free *by operator structure* — created, per `five-lanes-one-wall` — and
the labor is the identity with the Weil form, proved so far at the archimedean place plus one
prime).  The corpus's own two entry interfaces have the same shape: `xiWeilPolarization`
(unconditional Hermitian polarization with radical; nonnegativity ⟺ RH; blocked at the
full-test-algebra gate) and the Deninger Green-energy detection hypothesis
(`∀ x, energy x = 0 → x = 0` — definiteness of an energy form).

**Verdict.**  The realistic origin of a formal proof is Gate II in the compression form: what
Connes–Consani lack is exactly what the corpus uniquely owns — the label-faithful multi-place
assembly (step 2) that keeps prime labels and both orientations alive through the place sum,
plus the closed loop pinning what the compressed trace must equal (the H-mass/odd-sector
form).  Formal milestones that assume nothing: (a) bridge the H-mass form to
`xiWeilPolarization` as its reflection-odd sector restriction; (b) formalize semi-local
compressed positivity (CC archimedean case — heavy, unconditional); (c) attack the
multi-place extension of the compressed-trace identity with the assembly machinery — the one
step that is research, not transcription.  The Beurling kill-test passes structurally: the
compressed-trace identity consumes adelic Poisson, which Beurling systems lack.
- 2026-08-11 — attempt 8 (milestone (a)) formalized:
  `RHTower/GaussHodgeWeilPolarizationFusion.lean`.  Hostile check first: the naive "odd-sector
  restriction" is FALSE — the polarization is irreducibly the holomorphic channel (its prime-
  test summand is constantly 1, now a theorem: `xiWeilPairTerm_primeTest`).  The true fusion,
  proved unconditionally and pointwise (no summability hypotheses): the pair-square law
  (`xiWeilPairTerm_add_lineConj` — over each reflection pair, Weil summands = Hermitian pair
  energy − sharp-difference square, for EVERY test); the sharp-difference square of the prime
  test = the centered cosh defect (`norm_sq_primeTest_sub_lineConj`); hence **the H-mass
  density is exactly the per-pair gap between the Hermitian pair energy and the Weil
  polarization value at the prime test** (`massDensity_eq_hermitianPair_sub_weilPair`), and
  **RH ⟺ that gap closes at every copy for the prime-2 test**
  (`riemannHypothesis_iff_hermitianPair_eq_weilPair`).  Bonus: the unconditional
  conjugate-pair eigen-Gram (`xiWeilPolarization_thetaEigen_conjPair_vanishing/_value`) —
  the polarization couples the Hedenmalm eigenfunction at α only to the one at conj α, value
  = multiplicity·XiC′(α)·conj XiC′(conj α); the module's RH-conditional orthogonality is this
  law's collapse onto the diagonal.  The loop and the Weil-positivity interface are now one
  formal object: a Gate-II entry (compressed-trace positivity matching xiWeilPolarization)
  lands directly on the H-mass.
- 2026-08-11 — attempt 9 (the GNS socket): audit first — the corpus ALREADY owned the full
  positivity criterion (`riemannHypothesis_iff_xiWeilPolarization_nonneg`,
  `XiWeilPositivityCriterion.lean`, converse via `xiOffRealSignTest`), so no converse was
  rebuilt.  New module `RHTower/GaussHodgeWeilGNSSocket.lean`:
  `XiWeilSquareRealization` (every square-summable diagonal Weil value is a convergent sum of
  real squares — the coordinate form of a GNS/compressed-trace realization) and the keystones
  `riemannHypothesis_iff_xiWeilSquareRealization` (**RH ⟺ the diagonal Weil form is a sum of
  squares**) and `xiWeilSquareRealization_iff_gaussHodgeMass_vanishing` (a square realization
  ⟺ H-mass vanishing: Gate II lands on the loop).  Any future compressed-positivity
  construction — CC-style Sonin compression extended multi-place, or a geometric self-product
  realization — needs only to hit this socket; everything downstream is unconditional Lean.
  Remaining milestones: (b) archimedean compressed positivity (analytic, heavy), (c) the
  multi-place extension via the assembly machinery (research).
- 2026-08-11 — attempt 10 (the square-realization construction, executed):
  `RHTower/GaussHodgeWeilKreinDecomposition.lean`.  The direct construction produces exactly
  one obstruction, now formalized.  **Krein signature decomposition** (unconditional, every
  square-summable test): `4·Re(xiWeilPolarization F F) = Σ‖pair sum‖² − Σ‖pair difference‖²`
  (`xiWeilPolarization_re_eq_krein`, with pointwise law `xiWeilPairTerm_re` and both sector
  summabilities).  The negative sector's energy density at the prime test is exactly the cosh
  defect (`norm_sq_pairDif_primeTest`): the negative Krein sector IS the Hodge mass sector.
  `riemannHypothesis_iff_forall_pairDifEnergy_eq_zero` (indicator witness for the converse)
  and `xiWeilSquareRealization_iff_forall_pairDifEnergy_eq_zero`: the square realization
  exists ⟺ the negative sector is annihilated ⟺ RH.  Verdict: the construction cannot be
  completed without RH — as the socket iff demands — but it now terminates in the exact
  Pontryagin structure that a definitizable-intertwiner or compressed-trace argument must
  rigidify.  The Krein survivor of attempt 2 is closed into theorems.
- 2026-08-11 — attempt 11 (the fundamental symmetry): `RHTower/GaussHodgeWeilFundamentalSymmetry.lean`.
  The Pontryagin structure of attempt 10 is now a *geometry*, unconditionally.  The parity flip
  `J F = F ∘ conj` is a fundamental symmetry of the Weil form in the exact Krein-space sense:
  J is an involution, J-self-adjoint for the form (`xiWeilPolarization_parityFlip_symm`, by
  divisor reindexing), and the J-twisted form IS the divisor-coordinate ℓ² inner product
  (`xiWeilPolarization_parityFlip_right`, term-by-term).  Consequences, all unconditional:
  the GNS Hilbert space a square realization would generate ALREADY EXISTS — it is ℓ² of
  divisor coordinates carried by the J-metric (`xiWeilParityFlip_hasSum_sq`); divisor-even and
  divisor-odd tests are W-orthogonal for the full sesquilinear form (cross tsums vanish by the
  reindexing involution, no summability needed); W on the even sector is the positive ℓ²
  diagonal — the **unconditional even-sector square realization**
  (`xiWeilEvenSector_hasSum_sq`), and on the odd sector it is minus the ℓ² diagonal; every
  square-summable diagonal splits W-orthogonally into even + odd parts
  (`xiWeilPolarization_parity_decomposition`, via the corpus's sesquilinear additivity), giving
  the complex-valued Krein identity and the reality of the diagonal Weil form
  (`xiWeilPolarization_self_im`).  RH is the degeneracy of the whole structure:
  `riemannHypothesis_iff_forall_divisorOdd_eval_eq_zero` (RH ⟺ every divisor-odd test vanishes
  on the divisor; converse = two-point indicator, no summation) and the capstone
  `riemannHypothesis_iff_polarization_parityFlip_invariant` (**RH ⟺ W is its own J-twist ⟺ the
  Weil form already equals the positive ℓ² form it is J-equivalent to**).  Structure-level this
  is a [BRIDGE] to textbook Krein fundamental-symmetry theory; the corpus-new content is that
  THIS form has THIS explicit fundamental symmetry with ℓ² J-metric and the RH ⟺ J-triviality
  law.  Sharpened [OPEN CORE]: produce a positivity source (compressed trace / intersection
  form) that forces W = its J-twist — i.e., that the fundamental symmetry can be taken to be
  the identity.  All 12 key theorems `[propext, Classical.choice, Quot.sound]`; module wired,
  RHTower umbrella green.
- 2026-08-11 — attempt 12 (entire detection — the producer's burden minimized):
  `RHTower/GaussHodgeWeilEntireDetection.lean`.  Asked for the exogenous reason the odd ℓ²
  sector is null, the honest finding is that no unconditional producer exists in the corpus or
  the literature short of RH itself; the executed best shot instead proves the producer's
  burden is far lighter than the criteria demanded.  All previous converses (positivity
  criterion, odd-vanishing, J-twist invariance) used rough indicator witnesses, so the criteria
  formally required control of arbitrary ℓ² divisor test functions.  New: a
  **multiplicity-exact entire witness** — at any off-line divisor copy, the two terminal
  divided quotients `XiC(z)/(z−α)^m`, `XiC(z)/(z−conj α)^m'` (corpus `xiThetaDividedChain`,
  entire by iterated dslope, nonzero center values, vanishing at every other divisor point via
  the global factorization `XiC = (z−α)^m·chain`), normalized and differenced, give an entire,
  square-summable, divisor-odd test with value 1 at α — no simplicity hypothesis, no
  conjugation symmetry of XiC used (`exists_entire_divisorOdd_unit_test`).  Consequences:
  `riemannHypothesis_iff_xiWeilPolarization_nonneg_entire` (**RH ⟺ Weil positivity on entire
  square-summable tests alone** — Weil positivity cannot fail only on rough tests),
  `riemannHypothesis_iff_forall_entire_divisorOdd_eval_eq_zero` (the odd sector cannot hide
  from analytic tests), `riemannHypothesis_iff_polarization_parityFlip_invariant_entire`.
  Producer statement after this attempt: it suffices to produce positivity of the diagonal
  Weil form on ENTIRE square-summable tests — the class where explicit-formula, compressed-
  trace, and CC-style constructions actually live.  [OPEN CORE] unchanged in substance but
  now minimal in form: an unconditional positivity source for `Re W(F,F)` with F entire.
  All 5 theorems `[propext, Classical.choice, Quot.sound]`; wired; RHTower umbrella green
  (18899 jobs).
- 2026-08-11 — attempt 13 (the positivity source itself — verdict and the two theorems it
  leaves): asked to produce the unconditional positivity source for `Re W(F,F)` on entire
  square-summable tests, the frontier answer is that this is exactly RH
  (`riemannHypothesis_iff_xiWeilPolarization_nonneg_entire`) and no producible source exists in
  the corpus or the formalized literature; the best shot produced the two strongest true
  theorems around the target.  (1) `RHTower/GaussHodgeWeilSymmetryInsufficiency.lean` — **the
  symmetry package cannot source the positivity** (the Davenport–Heilbronn lesson made exact
  and formal): `exists_entire_finiteWeilForm_neg` (any finite conj-stable divisor with an
  off-line point carries an entire polynomial test with Weil diagonal −2; interpolation witness)
  and the capstone `weilPositivity_not_symmetry_consequence` — an explicit entire comparison
  function that is even, conjugation-real, all zeros in the open strip |Im| < 1/2, with an
  off-line reflection-stable quadruple whose finite Weil form fails entire positivity.  Hence
  every producer must consume input distinguishing ξ inside this symmetry class — the Euler
  product — a no-go now closed as theorems, [BRIDGE]/[REDISCOVERED] at concept level
  (Davenport–Heilbronn folklore), corpus-new as formal mathematics.  (2)
  `RHTower/GaussHodgeWeilDeviationMoment.lean` — **the exact quantity the arithmetic must
  control**: the odd part factors as deviation × divided difference
  (`xiWeilOddPart_eq_deviation_mul_dslope`: odd = i·Im(α)·dslope F (conj α) α), giving the
  deviation moment identity `Re W(F,F) = Σ‖even‖² − Σ (Im α_q)²·‖dslope F (conj α_q) α_q‖²`
  — in classical coordinates (Im α)² = (β−1/2)²: the Weil-positivity defect IS the second
  moment of zero deviations weighted by divided differences of the test.  The strip gives the
  unconditional weight bound |Im α| < 1/2 (`abs_xiSpectralPoint_im_lt_half`) and the lower
  bound `Re W(F,F) ≥ Σ‖even‖² − (1/4)·Σ‖dslope‖²`; RH ⟺ the deviation moment vanishes on all
  square-summable tests (`riemannHypothesis_iff_deviation_moment_eq_zero`).  Refined
  [OPEN CORE]: an arithmetic (Euler-product-derived) inequality dominating
  `Σ m(ρ)(β−1/2)²·|ΔF(ρ)|²` by the even energy for entire tests — with the formal proof that
  nothing weaker than arithmetic can do it.  All 7 key theorems
  `[propext, Classical.choice, Quot.sound]`; both modules wired; umbrella green (18904 jobs).
