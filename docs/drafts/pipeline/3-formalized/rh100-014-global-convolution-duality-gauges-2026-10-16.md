# 014 — Global original-source convolution calculus and Paugam gauges

Status: **FORMALIZED**, 2026-10-16. One structural contribution after 013.
Goal count: **14/100**. Nine modules form one construction, not nine contributions.

## Structural result

The original all-weight Meyer source admits centered entire nonlinear
operations on its Mellin transform. Their products are literal, absolutely
convergent source convolutions. The actual Poisson range is a convolution
ideal. Exponential corrections descend independently of the representative
and give continuous automorphisms of the whole original source and quotient.
Weighted inversion is their adjoint for the existing full global Paugam form.
Every anti-invariant original source consequently generates a global
pairing-preserving automorphism. Every finite full-multiplicity native theta
packet is invariant, with an actual compact AC solution for every forcing.

This removes nonlinear source admission, Poisson-boundary compatibility and
global duality compatibility as obstacles for this operator class. It gives
actual kernels, inverses and solutions in the original spaces. No new RH
equivalence, positivity receiver or improved estimate is being counted.

Write V for the original strong-log source, Q for its actual Poisson quotient,
M for Mellin transform, J for weighted inversion, C for convolution and B for
the existing global Hasse Paugam pairing. For every g in V, construct E(g) in V
with M(E(g))=exp(Mg)-1 and put G_g(h)=h+C(E(g),h). The principal conclusions are:

- G_(g+h)=G_g G_h, G_0=identity and G_g inverse=G_(-g), in V and Q.
- Every positive integer root is the admitted gauge at g/(n+1).
- For arbitrary g,f in V there is exactly one h in V satisfying, at every x,
  `h(x) + integral E(g)(t) h(x-t) dt = f(x)`. Every integrand is integrable.
- G_g and its inverse are continuous in the unchanged original source and
  quotient topologies.
- B(C(a,u),v)=B(u,C(Ja,v)) and B(G_g u,v)=B(u,G_(Jg) v).
- B(G_(g-Jg) u,G_(g-Jg) v)=B(u,v) for every g,u,v, with no positivity,
  smallness, simple-zero or spectral-location premise.
- The full jet action preserves every local Xi packet. On every finite native
  theta packet it has a unique literal solution with a compact AC representative.

## Frontier inputs

| Route | Audited source mechanism used |
| --- | --- |
| HF | `DeningerMeyerMellinReconstruction` and `DeningerMeyerMellinStripControl`: faithful entire Mellin transform and literal inverse reconstruction in all weights. |
| HF | `DeningerMeyerGlobalXiSynthesis`: every admitted source with an entire Xi quotient is an actual Poisson boundary; full jets separate all quotient classes. |
| HF | `DeningerMeyerStrongLogFrechet`, `DeningerMeyerStrongLogOperatorContinuity`, and `HTGeometry/FrechetOpenMapping`: original complete topology and continuous Mellin observations. |
| HF + RN | `DeningerMeyerHassePaugamBlocks` and `DeningerMeyerGlobalHassePaugamPairing`: absolutely admitted complementary full-jet pairing, zero radical and original weighted inversion. RN native current factors already separate this form. |
| RN + HF | `PaperThetaMeyerSpatialTransport`, `PaperThetaSpatialSolvability`, `DeningerMeyerHedenmalmSourceRealization` and `DeningerMeyerXiCausalChains`: faithful finite native realization of actual causal classes, all multiplicities, compact AC representatives. |

## Dependency-closed paper proof

1. An original Mellin transform F is rapidly decreasing and bounded on every
   vertical strip. For an entire scalar function phi,
   `phi(F)-phi(0)=F*dslope(phi,0)(F)`. The divided difference is entire and is
   bounded on the compact disc containing that strip's F-image. Multiplication
   by this factor retains every strip decay order. Inverse Mellin reconstruction
   therefore produces an original source for every centered entire operation.
   This argument also admits products of two source transforms.

2. Regard the original sources as Schwartz functions. The Schwartz Fourier
   convolution identity and Mellin/Fourier comparison identify the reconstructed
   product with the literal convolution integral, pointwise. The first source
   is integrable and the translated second source is bounded and measurable,
   so every displayed integrand is genuinely integrable. Faithfulness gives
   bilinearity, associativity and commutativity on actual sources.

3. Every actual boundary has an entire Xi quotient. Multiplying by any source
   transform retains Xi divisibility, and global source-native Xi division
   supplies a genuine cap whose boundary is the convolution. Thus the actual
   Poisson range is an ideal and convolution descends to Q. If F-G is divisible
   by Xi, then
   `exp(F)-exp(G)=(F-G)*exp(G)*dslope(exp,0)(F-G)` is also divisible by Xi.
   Both exponential corrections have already been admitted in V, so the same
   division theorem pays representative independence of exponentiation in Q.

4. The scalar exponential addition identity and faithful Mellin transform give
   the gauge group law and its exact inverse. Scaling g gives every positive
   integer root. Equality of original profiles identifies the inverse with the
   unique solution of the literal integral equation. No convergence of a formal
   source power series or small operator norm is assumed.

5. The graph of convolution by a fixed source is the intersection, over all
   complex s, of the closed scalar equalities
   `M(v)(s)=M(g)(s)*M(u)(s)`. Faithfulness identifies this intersection with the
   actual graph. Its inherited original topology is complete and metrizable.
   The existing Frechet open mapping theorem applied to graph projection gives
   continuity. The exact inverse is another such gauge. The actual quotient
   map then gives continuous equivalences on the original quotient topology.

6. Mellin reflection proves J(C(a,b))=C(Ja,Jb). For each full zero-jet datum,
   Leibniz's rule identifies its Paugam pairing with the top jet of the actual
   alternating convolution class `C(u,Jv)-C(v,Ju)`. Associativity, commutativity
   and J squared=identity give the convolution adjunction in each block.
   The existing absolutely convergent block formula yields global adjunction.
   Exponentiation commutes with J, hence G_g has adjoint G_(Jg). For g-Jg the
   two parameters add to zero, so the group law proves preservation of B.
   The alternating convolution class is not asserted to be a geometric cup.

7. Leibniz's rule gives the complete triangular derivative formula for G_g
   at every Xi point and every slot below its actual multiplicity. Vanishing
   of a full local packet is preserved in both directions. Global Xi synthesis
   and finite-dimensional injectivity identify the finite Hedenmalm range
   exactly with classes whose packets vanish outside the selected finite set.
   Both G_g and G_(-g) preserve this actual range. The faithful native theta
   equivalence therefore realizes an invertible native operator, and the
   existing literal compact representatives give AC solutions for every
   forcing in the packet. No arbitrary infinite native synthesis is used.

## Conjecture loop and failures

- Nuclearity alone was rejected as a new mechanism: `DeningerMeyerNuclear`
  already proves it for the original source and quotients. It does not supply
  the missing ordinary original-Frechet operator trace.
- A local positive Calderon defect was rejected as a genuine middle cup:
  `DeningerMeyerPaugamGradingObstruction` makes it vanish on actual middle
  cycles. The positive survivor here is the actual convolution class and its
  verified adjunction with the already nondegenerate global Paugam form.
- Arbitrary prescribed infinite spectral lifting and a source convolution
  unit were not used. Entire operations start with an admitted source and
  subtract their scalar value at zero. The exponential is an admitted
  correction to identity, with inverse constructed in the same source.
- Nonlinear admission led to exact source inversion; the full jet formula
  then paid native packet invariance. Testing the product against existing
  duality exposed the stronger global adjunction and symplectic gauge theorem.

The corpus search used the documented research command for cup, nuclear,
Euler-source, algebra, strip reconstruction and jet-composition leads.
Searches reported complete available coverage and no errors; compiler-index
freshness was mixed, so direct source inspection and Lean audits decided
applicability. No web, external novelty check or numerical experiment was used.

## Lean artifacts and audits

All files are in `formal/GaloisForLFunctions/RHTower/`:

1. `DeningerMeyerNonlinearMellin.lean`
2. `DeningerMeyerSourceConvolution.lean`
3. `DeningerMeyerConvolutionQuotient.lean`
4. `DeningerMeyerExponentialSolvability.lean`
5. `DeningerMeyerGaugeJets.lean`
6. `DeningerMeyerCohomologyExponential.lean`
7. `DeningerMeyerConvolutionTopology.lean`
8. `DeningerMeyerConvolutionPaugam.lean`
9. `PaperThetaConvolutionGauge.lean`

Every current leaf passed a direct foreground audit from `formal/`:

```
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Leaf>.olean GaloisForLFunctions/RHTower/<Leaf>.lean
```

Final API scratch audit passed. Expanded `#print axioms` audits passed for
all **76 public declarations**, with only `propext`, `Classical.choice` and
`Quot.sound`; no `sorryAx` or added axioms. All nine leaves have one umbrella
import each, fresh artifacts and no trailing whitespace. No heartbeat or
recursion-limit increases, full builds or umbrella builds were used.

`scripts/formal_tools.py lint` ran and returned one unrelated concurrent error:
`GaloisForLFunctions.RHTower.CHMDTranslatedRelativeGraph` was unreachable from
its theorem-area umbrella. It reported no error for this contribution's
modules. Existing large-file warnings remain elsewhere. That concurrent module
was left untouched. All owned foreground processes finished; eleven exact
task scratch files were removed. No commit or push was made.

## Remaining frontier

No positive Hodge form, RH proof, geometric graded cup/arithmetic trace
identification, arbitrary infinite native theta expansion, or directed
nonlinear prime–Gamma work sign follows here. Joint continuity of convolution
as a two-variable map and continuity of nonlinear exponentiation as its
parameter varies are not asserted. The new gauges preserve full local
spectral support; they are not zero-confinement operators.

Routine applications, roots, finite-packet transports and pairing identities
of this same construction belong to 014 and must not be recounted later.
