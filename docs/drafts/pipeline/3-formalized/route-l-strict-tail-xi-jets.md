# Route L: strict arithmetic tails retain Xi jets

Date: 2026-09-11.
Status: formalized; all 22 theorem axiom audits and targeted module build passed. RH remains unproved.
Module: `GaloisForLFunctions.RHTower.MobiusThetaStrictTailXiJetRetention`.

## Question and positive answer

C21 forces bounded prime-cyclic probes to annihilate the leading tensor
image. It does not prove that the remaining source contains no divisor
information. C22 tests that inference on the actual pre-tensor Möbius--theta
source used by Gamma-six.

Let `p>=1` be any ordinary-integer label and `r=mobiusSuccessor(p)` its first
later nonzero Möbius label. At depth `m`, retain every source term with label
strictly greater than `p`. Internal order `k` is introduced in the theta
source before translation and evaluation; no divisor enters the definition.

Put `delta_p(m,w)=M_p(m,w)-mu(p)`, with `M_p` the existing complete residual
multiplier, and `s=1/2+i*w`. In the actual convergence region,

`FL(strictTail_(k,p,m))(w)=delta_p(m,w)*XiC^(k)(w)`.

Every term and its complete tail are absolutely admitted. Exact successor
transport gives

`(r/p)^(m*s)*delta_p(m,w)=M_r(m,w)`.

For every fixed `Re(s)>0`, the right side tends to `mu(r)!=0`. Consequently
`delta_p(m,w)` is eventually nonzero, although it tends to zero. At every Xi
divisor of multiplicity `q`, the adjacent internal source orders `q-1,q`
therefore give an eventually nonzero vertical conormal pair

`(0,delta_p(m,w)*XiC^(q)(w))`.

This holds after every finite head removal, for composite and prime labels,
without assuming a nonvanishing scalar multiplier.

## The same physical Hilbert source

The corresponding complete Hilbert tail is

`T_(p,m)=R_(p,m)-mu(p)*Theta=sum_(n>p) actualTranslatedTerm_(n,m)`.

It tends strongly to zero. Exact physical successor transport gives

`(r/p)^(m/2)*norm(T_(p,m))=norm(R_(r,m))`.

Thus its normalized norm tends to `norm(mu(r)*Theta)>0`; the tail remains
nonzero at every sufficiently large depth. Every internally promoted
Hilbert tail also tends to zero. The Gamma-six countertransported tail in
C20 is exactly `6^(-m/2)*T_(6,m)`.

The representative bridge is explicit. With the corpus's Fourier
normalization, the Hilbert internal tail is almost everywhere
`2*pi*strictTailSource(2*pi*x)`. Its Fourier--Laplace integral with phase
`exp(-i*w*2*pi*x)` therefore equals the strict-tail source integral above.
This is an identity for the same complete source, including the coordinate
factor and every tail term, not a comparison of similar formulas.

The normalized evaluation recovers `mu(r)*XiC^(k)(w)`. Small Hilbert norm
therefore does not justify discarding the tail's finite-depth divisor jets
or its source-dependent singular normalization.

## Dependency-closed proof

1. Use the existing integral norm summability and integrability of every
   complete residual channel. Shift the index by one to retain precisely
   the strict tail. Tonelli domination proves integrability of its sum.
2. Commute the complete admitted series with integration. The existing
   term evaluation and head-plus-tail multiplier identity give `delta*XiC^(k)`.
3. Apply the already proved exact successor transport on its honest
   convergence domain. That domain is eventually reached for every fixed
   `Re(s)>0`. The successor residual tends to its nonzero Möbius coefficient,
   proving eventual nonvanishing and the normalized limit.
4. Specialize only now to each Xi divisor. Lower derivatives vanish and
   the multiplicity derivative is nonzero by the existing divisor theorem;
   the tail multiplier is eventually nonzero by step 3.
5. The actual Hilbert tail equals the complete vector series. Existing
   Tannery domination gives norm decay. Apply norm to the exact physical
   successor source identity. Translation is isometric, so its scalar
   factor gives the displayed exact norm identity and positive limit.
6. Identify the real Hilbert coefficient with the half-density Dirichlet
   coefficient, and carry the translated Schwartz representative through
   the fixed `2*pi` rescaling. Absolute Hilbert norm summability permits
   passage through the whole tail using `Lp.coeFn_tsum`.
7. Almost-everywhere equality of the integrands and the literal change of
   variables cancel the `2*pi` factor, proving the same-source integral
   bridge and Xi-jet landing.

## Scope and remaining obstacle

The conjecture that finite head removal destroys all Xi conormal data is
false for this source. Its positive survivor is the complete strict-tail
source, exact integral, nonzero conormal at every divisor, and forced
successor normalization with its precise physical norm cost.

This does not construct C21's source-to-Sonin quotient map, prove prime
cyclicity or fixed-reader agreement, or identify the full tensor-square
remainder with its required physical reader. The successor normalization
is depth-dependent and singular; it cannot be substituted for a bounded
fixed reader. Internal source jets are not silently replaced by derivatives
of the entire multiplier-times-Xi product. Route L and RH remain open.

## Corpus and external method checks

Two deep/method searches reported partial coverage (706108 ready, 779 stale
method records). The successor search retrieved the actual nonzero Möbius
successor theorem; other elliptic-theta and unrelated source-integral hits
did not supply the desired comparison. All used source, transport, jet,
representative and integral-summability declarations were inspected.

Broad arXiv terms were `sewing`, `observability`, and `reconstruction`.
The [September 9 polyhedral observability paper](https://arxiv.org/html/2609.10096v1)
derives a uniform resolvent estimate using its Laplacian, boundary observation
region and billiard geometry (Proposition 3.1). Those hypotheses supply no
corresponding arithmetic norm comparison here. The tail's exact source
transport and its normalization cost are proved directly; no external
observability premise is imported.

## Verification

- `lake env lean /tmp/route_l_strict_tail_jets.lean`: all 22 theorems passed, no warnings.
- `lake build GaloisForLFunctions.RHTower.MobiusThetaStrictTailXiJetRetention`: passed.
- `lake env lean /tmp/route_l_strict_tail_jets_axioms.lean`: all 22 theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; no added axioms.
- `scripts/formal_tools.py lint`: passed with existing file-size warnings; umbrella import wired.
- No numerical experiment or full build.
