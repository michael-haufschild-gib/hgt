# Route D Euler-subset positive-lift no-go

- **ID:** `route-d-euler-subset-positive-lift-no-go`
- **Status:** fully proven on paper — Stage 2, awaiting Lean formalization
- **Route:** D — prime–archimedean Hankel sign and reconstruction
- **Opened:** 2026-08-01
- **Computation policy:** no numerical computation; symbolic proof only

## Exact inherited frontier

Route D is already exact at its endpoint:

```text
PrimeArchSourceTraceHankelIntNonnegative
  <-> PrimeArchSourceMomentHankelExactReconstructionPhase
  <-> RH.
```

All existing moment measures, self-adjoint observables, reflection-positive Grams, KMS states,
thermal limits, Sonin carriers, cofinal degree tails, and exact reconstruction phases are
transporters. None creates positivity from the literal prime–Gamma source before comparison.
Finite Hankel blocks do not approach RH, and every infinite exact cofinal degree family reconstructs
the full cone.

Strongest live source-first proposal is off-diagonal channel-mixing repair in
`prime-gamma-reflection-decimation-defect-resolvent-rh.md`. Diagonal positive-log Mellin
unbalancing has divergent energy. Additive successor incidence is positive and summable but loses
Euler multiplication and does not equal target moment packet. Proposed repair mixes prime channels
and includes Gamma/polar modes before taking Hilbert norm.

## External state of art at 2026-08-01

Primary sources checked:

1. Katkova, *Multiple positivity and the Riemann zeta-function*,
   https://arxiv.org/abs/math/0505174. Xi coefficient sequence is PF-infinity exactly under RH;
   fixed-order consecutive Toeplitz minors are eventually positive.
2. Michałowski, *An explicit uniform cubic wedge for consecutive Toeplitz minors of the Riemann
   xi coefficients*, https://arxiv.org/abs/2607.16795. New uniform result proves `D_(r,k)>0` only
   for `k >= 10^18 r^3` and explicitly leaves RH-critical bounded-`k/r` region open. Its
   directed-rounding certificates are outside this card's no-computation proof.
3. Griffin–Ono–Rolen–Thorner–Tripp–Wagner, *Jensen Polynomials for the Riemann Xi Function*,
   https://arxiv.org/abs/1910.01227. Fixed-degree Jensen polynomials are hyperbolic only after a
   sufficiently large shift; full hyperbolicity remains RH.
4. Bickel–Pascoe–Sargent, *Zero-free regions near a line*,
   https://arxiv.org/abs/2108.04807. Tightening finite Hankel relaxations can force hypothetical
   nonreal zeros farther from line, not toward it.
5. Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*,
   https://arxiv.org/abs/2206.03682. Screw-kernel positivity is another exact RH equivalent with
   partial unconditional statements, not a source positivity producer.
6. Connes–Consani, *Weil positivity and Trace formula, the archimedean place*,
   https://arxiv.org/abs/2006.13771, and Connes–Consani–Moscovici, *Zeta zeros and prolate wave
   operators*, https://arxiv.org/abs/2310.18423. Semi-local Hilbert/trace constructions explain
   archimedean positivity and spectral structure; full semi-local Weil positivity remains RH clause.
7. Polson, *Riemann, Thorin, van Dantzig Pairs, Wald Couples and Hadamard Factorisation*,
   https://arxiv.org/abs/1804.10043, revision 8 (2026). GGC/Thorin language packages divisor
   moment criterion but does not produce required positive folded-zero measure from primes.

No checked primary source supplies a fixed-boundary, source-functorial positive lift of
positive-log prime jets, or a completed Green/Schur identity identifying such a lift with
prime–Gamma Hankel moments.

## Fields-medalist question

Given exact frontier, what would a Fields Medal-winning mathematician conjecture?

Not that an unspecified carrier exists. Conjecture a rigidity law for entire source-first design
class: exact Euler-subset additivity and Hilbert positivity cannot coexist with unbounded
positive-log channel transport. Off-diagonal mixing can help only by destroying local Euler
additivity before norm is formed.

## Exact claim

Let `P` be set of primes, `H` a real or complex Hilbert space, `b : H` a fixed completed
Gamma/polar boundary vector, `v_p : H` arbitrary prime-channel output vectors, `B : R`, and

```text
e_r(p) = (Lambda(p)/p) (log p)^(2r)
       = (log p)^(2r+1)/p.
```

Assume exact source functoriality for every finite Euler subproduct:

```text
||b + sum_(p in F) v_p||^2 = B + sum_(p in F) e_r(p)       (E_F)
```

for every finite prime set `F`.

**Euler-subset positive-lift classification/no-go.** Under `(E_F)`:

1. `Re <v_p,v_q> = 0` for every distinct pair `p,q`; this follows from mixed finite difference
   `E_{p,q}-E_p-E_q+E_empty`.
2. Finite completed packet norms are unbounded because `sum_p e_r(p)=infinity`.
3. Consequently no bounded cofinal Hilbert limit, square-summable source packet, or positive cyclic
   vector can satisfy `(E_F)`.

This allows arbitrary infinite-rank mixing inside each `v_p`, arbitrary channel phases, and an
arbitrary fixed Gamma/polar boundary already present before norm. Exact Euler-subset additivity
annihilates every real cross-channel cancellation.

## Heavy-conjecture ladder and hostile attacks

### C0 — diagonal positive-log unbalancing

**Attack:** already false. Its energy is `sum_p (log p)^(2r+1)/p = infinity`.

### C1 — channel-preserving linear mixing

**Attack:** already false. Commutation with every resolved Euler projection forces a diagonal
operator; existing Lean theorem `no_summable_fullyResolvedPrimeChannel_mellinJetRealization`
applies.

### C2 — arbitrary off-diagonal mixing with fixed Gamma/polar boundary

**Attack:** if lift remains exact for every finite Euler subproduct, mixed finite differences force
pairwise real orthogonality. Hence mixing cannot lower total positive energy. This is this card's
claim.

### C3 — additive successor incidence plus finite boundary rank

**Attack:** successor difference kills constant jet. Existing Lean excludes direct target
identification. A finite boundary repair can restore finitely many rows but does not establish
all-order Euler-source identity; fitting target rows would be circular.

### C4 — globally renormalized nonlocal reflection-positive quotient

**Verdict:** survives but is no longer an Euler-subset positive lift. It must combine all primes,
Gamma, and polar modes before positivity and allow finite subproducts to be signed or
non-functorial. This is same global Weil/Deninger positivity clause as RH unless an independent
source construction is supplied.

## Anti-theatre audit

- **New mathematical delta if proved:** extends diagonal/commutant no-go to arbitrary off-diagonal
  channel mixing and arbitrary fixed archimedean boundary by classifying exact Euler-subset
  positive lifts.
- **What it does not prove:** RH, target Hankel positivity, or impossibility of a genuinely global
  nonlocal reflection-positive quotient.
- **Why it matters:** removes top-ranked inherited Route D proposal unless that proposal explicitly
  identifies where Euler-subset additivity is broken before positivity. Merely naming an
  infinite-rank channel mixer is no longer a live mechanism.
- **Falsifier:** two primes with nonzero real cross covariance satisfying all four subset identities,
  or a uniformly bounded family satisfying `(E_F)`.
- **No hidden target input:** theorem uses only Hilbert norm polarization, finite-set additivity,
  `Lambda(p)=log p`, `log p>=log 2`, and divergence of reciprocal primes.

## Paper-proof obligations

- [ ] Prove general four-subset mixed-difference orthogonality lemma with arbitrary baseline vector.
- [ ] Prove nonnegative finite-sum boundedness would imply summability of local energies.
- [ ] Specialize to `primeMellinJetDiagonalEnergy r` and use its unconditional nonsummability.
- [ ] State exact survivor boundary: viable lift must break Euler-subset norm additivity before
      positivity, use non-fixed boundary depending nonlocally on whole Euler product, or leave
      Hilbert positivity until after global completion.
- [ ] Run hostile edge-case audit: complex phases, duplicate primes, empty/singleton sets,
      cutoff-dependent boundary, conditionally convergent vector sums, and nonlinear channel maps.

## Formal target

Planned module:

```text
GaloisForLFunctions.RHTower.PrimeMellinJetEulerSubsetLiftNoGo
```

Planned public results:

```text
eulerSubsetNormSqExact_pairwise_re_inner_zero
not_exists_bounded_eulerSubsetNormSqExact_of_not_summable
no_bounded_primeMellinJet_eulerSubsetPositiveLift
```

## Dependency-closed paper proof

Write

```text
Q(F) = ||b + sum_(p in F) v_p||^2.
```

Assume `Q(F)=B+sum_(p in F)e(p)` for every finite `F`, with `0<=e(p)`.

### Lemma 1 — baseline and mixed finite difference

At `F=empty`, `Q(empty)=||b||^2=B`. For distinct `p,q`, expand four squared norms:

```text
Q({p,q}) - Q({p}) - Q({q}) + Q(empty)
  = 2 Re <v_p,v_q>.
```

Source additivity makes same mixed finite difference

```text
(B+e(p)+e(q))-(B+e(p))-(B+e(q))+B = 0.
```

Hence `Re <v_p,v_q>=0`. Complex imaginary covariances may survive, but they never change a Hilbert
norm and cannot supply cancellation.

### Lemma 2 — nonsummable positive local energy forces unbounded packets

Suppose completed packets were uniformly bounded: `Q(F)<=C` for all finite `F`. Exactness gives

```text
sum_(p in F) e(p) <= C-B
```

for every finite `F`. A nonnegative family is summable exactly when its finite subsums are bounded,
so `e` would be summable. Contradiction. Equivalently, for every `C` some finite `F` has
`C<Q(F)`.

### Theorem — positive-log prime specialization

For every `r>=0`, `e=e_r=primeMellinJetDiagonalEnergy r` is nonnegative and is not summable:

```text
e_r(p) = (log p)^(2r+1)/p
       >= (log 2)^(2r+1)/p,
```

while `sum_p 1/p` diverges. Lemma 2 excludes every uniformly bounded exact Euler-subset lift.
Lemma 1 additionally shows any fixed-boundary additive realization has zero real covariance between
distinct prime outputs. Therefore arbitrary off-diagonal Hilbert mixing cannot repair diagonal
positive-log divergence while retaining exact subsetwise Euler additivity.

## Hostile edge-case audit

1. **Complex phases:** only imaginary cross inner products survive; norm squares see real parts, so
   phases do not change conclusion.
2. **Prime powers or duplicate channels:** restriction to prime singleton slice already diverges.
   Enlarging index set cannot restore boundedness. Finsets correctly avoid duplicate primes.
3. **Empty and singleton subsets:** empty subset forces `B=||b||^2`; singleton identity allows a
   boundary cross term but does not affect global divergence.
4. **Cutoff-dependent boundary:** if exact norm identity still has same positive additive right side,
   norms diverge without any fixed-boundary premise. Such a boundary escapes only by inserting a
   cutoff-dependent signed counterterm, hence abandons positive Euler-subset source law.
5. **Conditionally convergent ordered sums:** arbitrary finite-subset net is unbounded. One chosen
   ordering can converge only through order-dependent cancellation and is not Euler-subset natural.
6. **Nonlinear channel construction:** proof needs no linear map. It needs only additive fixed output
   packets for unions. A genuinely nonlinear `F -> v_F` escapes only by ceasing to be a
   prime-channel incidence lift.
7. **Gamma/polar completion:** arbitrary fixed `b` is included before norm. A boundary depending
   nonlocally on entire Euler product is the surviving global-completion class, not this route's
   proposed source-functorial channel mixer.
8. **Weak inequality instead of equality:** lower bound
   `Q(F)>=B+sum_(p in F)e_r(p)` already gives unboundedness. Exact equality is used only for
   orthogonality classification.

## Positive survivor and exact boundary

Any viable Route D positivity producer must perform at least one of these nonlocal operations:

```text
break Euler-subset norm additivity before positivity;
make boundary depend on whole Euler product rather than a fixed completed mode;
replace additive prime packets by a nonlinear global quotient;
or postpone Hilbert positivity until after signed prime–Gamma completion.
```

Successor incidence realizes first option by replacing multiplicative prime channels with additive
edges, explaining both its finite energy and failure of target identification. Semi-local
Weil/Deninger constructions inhabit last options. No source theorem currently proves their global
positive quotient. This survivor is precise: fixed-boundary off-diagonal channel mixing is retired;
global nonlocal reflection positivity remains the RH-level open core.

## Stage 2 audit

- [x] One exact claim only.
- [x] No numerical computation.
- [x] No RH-equivalent positivity assumed.
- [x] All hypotheses explicit and source-side.
- [x] Complex, boundary, convergence, nonlinear, and index edge cases attacked.
- [x] Positive survivor recorded.
- [x] Paper proof dependency-closed.
- [ ] Lean formalization.
