# Arithmetic Julia normal-cone observability law

- **ID:** `arithmetic-julia-normal-cone-observability-law`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE universal theorem / RH source-completion route
- **Source:** corpus synthesis of arithmetic Schur saturation, Gamma-sewn Julia transport,
  fixed-width divisor tomography, and Xi Ward index quantization
- **Statement:** The actual-prime logarithmic clock is invisible to every finite-jet or bounded
  Hardy completion, but is recovered uniquely as the normalized normal coordinate of the minimal
  two-channel Julia lift; this coordinate transports the literal prime--Gamma Euler exterior
  current, whose fixed-width global scalarization reconstructs the complete off-critical Xi
  divisor and hence its quantized Ward index.

## Goal

Replace two disconnected facts—

1. finite/bounded source completions lose the prime logarithmic clock; and
2. Xi off-line divisor packets carry quantized Ward charge—

by one source-selected completion theorem.  The theorem must construct the missing unbounded
coordinate, prove its minimality and uniqueness, identify its arithmetic boundary without reading
Xi zeros, and then use the explicit formula—not a definition involving the target divisor—to
transport that boundary to a multiplicity-complete off-critical divisor observable.

This is an RH route, not an RH proof.  Its closed mathematical question is:

> What is the minimal completion of the actual-prime Schur source that retains the logarithmic
> clock after all bounded completions have saturated?

The proposed answer is the rank-one Julia normal cone, unique up to the unavoidable orientation.

## Candidate theorem

Let

```text
k_p = (1,p^-1,p^-2,...) in H²,
C_m(d) = sum_p d_p k_p,
L_m(d) = sum_p d_p (log p)p^-m k_p
```

on finitely supported actual-prime packets.

### I. Universal bounded-completion wall

For every finite order `m`,

```text
closure Graph(C_m,L_m) = H² x H².
```

For every nonzero bounded Hilbert-space postprocessor `B`, the completed clock `B L_m` has a
nonzero vertical multivalue and admits no global estimate

```text
||B L_m(d)|| <= M ||C_m(d)||.
```

If `F_n : H² -> K` are bounded maps satisfying

```text
F_n(C_m(d)) -> B(L_m(d))
```

for every finite packet `d`, then `sup_n ||F_n|| = infinity`.  Thus every asymptotically faithful
single-channel recovery must escape every bounded operator ball.

### II. Universal square-root normal-cone law

Let `c_x` be a positive scalar contraction with

```text
c_0=1,
(1-c_x²)/x² -> kappa²,        kappa >= 0.
```

Then the positive defect coordinate

```text
d_x = sqrt(1-c_x²)
```

satisfies `d_x/x -> kappa`.  Among orientation-preserving real two-channel isometries whose first
source-axis coordinate is `c_x`, the Julia rotation

```text
J_x = [[c_x,-d_x],[d_x,c_x]]
```

is unique after requiring positive environment coordinate.  Dimension two is minimal whenever
`0<c_x<1`: no scalar isometric completion exists.

### III. Actual-prime arithmetic specialization

For the Gamma-sewn Möbius valuation compression,

```text
kappa_p = sqrt(3/4) log p.
```

After the universal normalization `sqrt(3/4)`, the Julia environment converges to the literal
prime logarithm.  Applied cellwise to the canonical soft half-weight source, it converges to the
hard von Mangoldt half-weight.  Its calibrated exterior current converges to the literal
prime--Gamma Euler boundary Wronskian.

The completion is necessarily singular in the source topology by Part I, while Part II proves
that its extra rank-one coordinate is the minimal positive isometric escape.

### IV. Divisor and Ward transgression

For every fixed width `L>0`, pair the recovered Euler current with the symmetric two-edge Weil
window and sample at `a=(log n)/2`.  The resulting explicit prime--Gamma sequence has a Dirichlet
continuation whose polar divisor is exactly

```text
{1+w : Xi(1/2+w)=0, Re w>0},
```

with normalized residues equal to analytic multiplicity.  Consequently the recovered source
determines the full off-critical divisor.  Each recovered strict-right upper divisor pair then
has the canonical infinitesimal Julia-defect mass `8 pi`, and the endpoint-weighted total equals
`2 pi` times the complete off-line endpoint charge.

Part IV must be proved as an explicit-formula transport from Part III.  A theorem formed only by
conjoining the existing Julia--Euler limit, fixed-width tomography, and Ward quantization does
not pass.

## Why this could be new

Classical Sz.-Nagy--Foias theory supplies Julia/Halmos unitary dilations for contractions.
Novelty is not claimed there.  Candidate novelty is the conjunction forced by one arithmetic
normal cone:

1. maximal graph saturation of the actual-prime logarithmic clock at every finite order;
2. universal failure of every bounded infinite postprocessing;
3. unique minimal rank-one nonlinear blow-up recovering `log p`;
4. exact landing on the completed Euler exterior current;
5. multiplicity-complete transgression of that recovered current to the off-critical Xi divisor.

No located literature treats this arithmetic singular-completion problem or identifies the Julia
defect normal coordinate with the prime logarithmic clock.

## Hostile rejection gates

- **Classical-dilation objection:** reject if theorem reduces to the scalar Julia matrix identity
  plus substitution `c=c_x(p)`.
- **Conjunction objection:** reject if Part IV lacks an explicit map from the current in Part III
  to the fixed-width source coefficient.
- **Target-reading objection:** reject if any source construction uses Xi zeros, RH, a Ward
  response, or the target divisor.
- **Topology-switch objection:** state source topology and the singular normalization explicitly;
  reject any claim that the completion is bounded there.
- **Minimality objection:** prove both no scalar isometric lift and uniqueness of the positive
  two-channel lift, not merely existence.
- **Significance objection:** a paper ending at `d_x/x -> log p` is operator-theoretic arithmetic
  infrastructure, not a general-journal RH paper.  Divisor-complete explicit-formula transport is
  mandatory.
- **Zero-exclusion honesty:** the theorem constructs a lossless route to the divisor but does not
  prove the recovered divisor empty.  Never present the endpoint weight cap as conflicting with
  `8 pi`; weights decay with zero height.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, hostile gates
- [ ] General square-root normal-cone paper proof
- [ ] Minimality and uniqueness paper proof
- [ ] Unbounded-recovery escape theorem paper proof
- [ ] Exact Part-III-to-Part-IV fixed-width current map
- [ ] Current primary-source novelty audit
- [ ] 1 → 2 fully-proven: dependency-closed paper proof, no target-reading
- [ ] 2 → 3 formalized: exact Lean theorem(s), foreground checks, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and antagonistic general-journal review

## Existing dependency ledger

- `ArithmeticLogClockFiniteJetSaturation.lean`
- `ArithmeticLogClockBoundedCompletionSaturation.lean`
- `PrimeFirstTraceCompleteNoEscapeUniversalityLaw.lean`
- `GammaSewnMobiusJuliaSourceTransport.lean`
- `GammaSewnRecoveredWardParityIndexUniversalityLaw.lean`
- `XiWardInfinitesimalDefectIndexQuantization.lean`
- `XiWardEndpointSourceIndex.lean`
- `docs/drafts/pipeline/4-publication-ready/fixed-width-two-edge-weil-source-spectrum/main.tex`

## Part-III-to-Part-IV bridge proof `[PROVED HERE]`

For `n >= 2`, define the finite-aperture Julia hard coefficient

```text
J_x(n) =
  gammaSewnMobiusJuliaHardHalfWeightTransport
    x (-1/2) (prodNatEquiv.symm(n)) ^ 2,   if n is a prime power,
  0,                                       otherwise.
```

This definition is source-pure.  It uses only the actual-prime Gamma-sewn contraction, its
canonical positive Julia defect, unique factorization, and the damping value `u=-1/2`.

If `n=p^(e+1)`, the normalized Julia-environment theorem gives

```text
J_x(n) -> xiGammaEulerBoundaryRealAmplitude(-1/2,(p,e))^2.
```

The exact amplitude-square law and `Lambda(p^(e+1))=log p` give

```text
xiGammaEulerBoundaryRealAmplitude(-1/2,(p,e))^2
  = (log p / n) exp((log n)/2)
  = Lambda(n)/sqrt(n).
```

If `n` is not a prime power, both `J_x(n)` and `Lambda(n)` vanish.  Hence, for every `n>=2`,

```text
J_x(n) -> Lambda(n)/sqrt(n).                         (B1)
```

For a fixed rectangular window `(L,a)`, put

```text
P_x(L,a) =
  sum_{2 <= n <= floor(exp(2a))}
    J_x(n) R_{L,a}(log n).
```

The sum is finite, so `(B1)` may be passed through it without a domination theorem:

```text
P_x(L,a) -> rectangularPrimeAutocorrelationSum(L,a). (B2)
```

Define the complete finite-aperture recovered source

```text
S_x(L,a) =
  -2 P_x(L,a)
  + 2 rectangularEvenPolarFeature(L,a)^2
  + rectangularGammaPolarCorrection(L,a).
```

The last two terms are source-defined and aperture-exact.  By `(B2)`,

```text
S_x(L,a)
  -> rectangularPrimePolarSourceCoefficient(L,a)
     + rectangularGammaPolarCorrection(L,a).
```

The sharp rectangular explicit formula identifies the right side exactly with the diagonal
Xi--Weil polarization whenever `0<=L<=a`.  Therefore

```text
S_x(L,a) -> Q_L(a).                                  (B3)
```

At logarithmic samples `a=(log n)/2`, the boundary sequence in `(B3)` is the already-proved
prime--Gamma source sequence.  After any admissible finite-prefix deletion, its ordinary
Dirichlet series has canonical meromorphic continuation to `Re s>1`; its simple poles are exactly
the shifted strict-right Xi divisor, and normalized residues are analytic multiplicities.

Thus the Julia normal coordinate is not merely identified with an Euler exterior seam.  Its
squared critical boundary amplitude generates the literal finite von Mangoldt term of a
multiplicity-complete global divisor observable.  This discharges the conjunction objection at
paper level.  No Xi zero or Ward response occurs until after the source sequence has been
constructed and the explicit formula has been applied.

## Log

- 2026-07-28 — created after rejecting a false quantization argument: the unconditional
  endpoint-weighted Ward cap is small, but the positive packet weights decay as height grows, so
  it cannot force zero exclusion.
- 2026-07-28 — exact weld audit found two different Julia objects.  Gamma-sewn recovery preserves
  an already-continued Xi Ward tangent; it does not derive that tangent from the arithmetic Julia
  environment.  Part IV therefore remains a real bridge obligation.
