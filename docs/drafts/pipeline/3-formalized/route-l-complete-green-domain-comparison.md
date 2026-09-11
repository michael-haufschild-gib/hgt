# Route L: finite prime Green domains retain full Xi data

- **ID:** L-C38
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; finite-domain classification and explicit complete-source test
- **Depends on:** [C32](../3-formalized/route-l-complete-transgression-physical-balance.md), [C37](../3-formalized/route-l-coherent-joint-source-transport.md)
- **Lean:** `GaloisForLFunctions.RHTower.DeningerFinitePrimeGreenDomainXiJets`
- **RH status:** unproved

Chain: complete original Green/BV source → cyclic/fixed physical-reader
agreement → conormal vanishing → RH. C37's canonical joint-source correction
retains its original normalization bias. C38 attacks a source-domain change:
can original prime Green admission, including collar symmetry, supply the
missing complete-source cancellation?

## Conjecture, failure, and positive survivor

The completed operator in `DeningerMeyerReflectedGaussianCompletedSourceGreen`
is an oriented reflection on the Xi Hilbert carrier, with square minus
identity. Its unconditional primitive does not imply admission to the
separate discrete translation-Green domain. Identifying those domains was
the first failed conjecture.

The next conjecture was that joint admission to the original prime Green
domains imposes the missing finite Xi relation. It fails sharply: every full
finite Xi packet is realized by a literal Meyer source in all specified
finite prime Green domains. This includes every multiplicity coordinate;
prime lists retain order and repetitions. No finite-jet surjectivity premise
is added: source interpolation and the complete triangular translation law
already proved in the corpus construct the preimage.

Adding collar symmetry also fails. An explicit paired depletion of the
original reflected log Gaussian is collar-fixed, lies in all specified
finite prime Green domains, has nonzero Mellin value at every actual Xi
point, and has a nonzero complete Gamma/flux discrepancy. Its normalization
factor and the first nonzero derivative at any order are retained exactly.

The positive survivors are the full finite-jet interpolation theorem, the
exact leading-derivative transport, and the explicit collar-fixed source
with its actual complete boundary. These are formalized, rather than merely
recording a negative statement. No route is retired by this local result.

## Dependency-closed paper proof

Let `H` be the actual all-weight logarithmic Meyer target, `T_c g(t)=g(t-c)`,
`Jg(t)=exp(-t)g(-t)`, and `D_L=1-T_{-L}`. Its image is the original strong-log
Green domain. The corpus gives

`M(T_c g)(s)=exp(cs) M(g)(s)` and `M(Jg)(s)=M(g)(1-s)`.

For a fixed actual Xi point `rho`, the full derivative block of `D_L` is
triangular, with diagonal `1-exp(-L*rho)`. This is nonzero for `L>0`, because
`0<Re(rho)<1` and the modulus of `exp(-L*rho)` is strictly below one. In a
kernel vector, induction on derivative order removes all lower terms and
forces the next coordinate to vanish. Finite dimensionality supplies the
inverse. Composing these inverses for the ordered period list and applying
literal Meyer finite-jet interpolation gives the required source. Commuting
Euler factors put its finite depletion in every selected Green domain.

For any source with all Mellin derivatives below `k` zero at `s`, Leibniz's
formula gives exactly

`M(D_L g)^(k)(s)=(1-exp(-L*s))*M(g)^(k)(s)`.

The actual canonical landing in exponential Schwartz intertwines `D_L`
with the existing periodization defect. Hence a source admitted to the
Green domain for every prime in an infinite prime set has zero
periodization there. The existing cofinal prime tomography theorem forces
the entire original source to be zero. This is an infinite simultaneous
admission statement; no convergence claim about finite interpolants is made.

Now pair the actual source operations:

`E_L = D_L J D_L J`,

`M(E_L g)(s) = A_L(s) M(g)(s)`,

`A_L(s)=(1-exp(-L*s))*(1-exp(-L*(1-s)))`.

`A_L(1-s)=A_L(s)` and Mellin injectivity prove `J E_L=E_L J`.
The same injectivity and scalar multiplication prove `E_L D_M=D_M E_L`.
Thus the ordered product `E_P` lands in every selected original Green
domain and commutes with `J`. Its multiplier is the exact product
`A_P(s)=prod_{L in P} A_L(s)`, including repeated periods. Every factor is
nonzero throughout `0<Re(s)<1`. At any order `k` with all lower source jets
zero, the surviving Leibniz term is exactly

`M(E_P g)^(k)(s)=A_P(s)*M(g)^(k)(s)`.

Apply this to the fixed reflected Gaussian
`g_0(t)=exp(-t/2)*exp(-pi*t^2)`, whose entire Mellin transform is
`exp((s-1/2)^2/(4*pi))`. The explicit source `E_P g_0` is collar-fixed and
retains a nonzero value at every actual Xi point. Such an evaluation
annihilates the literal Poisson range, so this source is not a Poisson
boundary. C32's actual Gamma/flux identity then proves its complete
Gamma and transgression readings are unequal. The final theorem verifies
collar fixedness in the very same Meyer source used by those readers.

There are two distinct constructions here. Finite interpolation can match
exactly the selected full packet of the original Gaussian. The explicit
collar-fixed paired source instead retains the displayed nonzero multiplier.
The theorem does not identify the interpolant with that explicit source,
or either modified source with the complete original Green/BV object.

## Whole-corpus and recent-method audit

Five deep searches, each with a 150-second request budget, inspected all
20 candidate lemmas, all 20 source arguments, available method records,
coverage and freshness. All results were partial, so they are discovery
sources rather than evidence of exhaustive absence. Candidate applicability
was checked against source and in Lean.

| Mechanism query | Index generation | Semantic ready / expected |
| --- | --- | --- |
| complete Green source boundary domain integration limiting trace cyclic physical comparison | 874195 | 2352358 / 2352359 |
| Green primitive actual source Euler flow dissipativity integration boundary positive pairing | 874200 | 2352358 / 2352444 |
| periodization source Green obstruction two irrational periods actual source inverse boundary | 874207 | 2352382 / 2352447 |
| prime periodization depletion preserves nonzero Mellin Xi leading derivative Green domain | 874232 | 2352155 / 2352449 |
| finite triangular jet defect invertible reflected Green domain source exact interpolation | 874294 | 2352508 / 2352561 |

The fourth search proposed leading-coefficient and prime-tomography
ingredients. Generic leading-coefficient lemmas were not substitutes for
the source proof. The applicable ingredients were actual prime tomography,
the confluent Mellin flow law, full finite Xi interpolation, and the
original source Green inverse. The other searches returned no verified
independent producer of the physical comparison.

Broad arXiv terms were `transgression`, `dissipation`, `resonance`, `rigidity`,
and `extension`. The last two searches returned older or irrelevant hits;
no recent result was inferred from their date filters.

[Fuchsian resonance, 2609.00942](https://arxiv.org/html/2609.00942v1),
Theorems 4.2–4.3 and Section 6.6, derives boundary coefficient identities
from a convergent recurrence and an independent global boundary basis.
Simultaneous regularized zeros alone do not determine the limiting ratio;
first variations matter. C38 tests the corresponding full triangular Xi
block. No Fuchsian connection theorem for the RH source is assumed.

[Entropy dissipation, 2608.13332](https://arxiv.org/html/2608.13332v1),
Theorem 4.1, needs a complex-balanced reaction network and a positive floor
or exclusion of boundary equilibria for coercivity. Those hypotheses have
not been derived for this source. Adding transport noise changes the
operator and supplies no comparison preserving the original data.

## Validation and remaining obstacle

The final scratch check passed with empty output using
`lake env lean /tmp/route_l_green_domain_c38.lean`. The new leaf is wired
into `RHTower.lean`. Its targeted final `lake build` passed: only the new
leaf was built (66 seconds); the targeted dependency graph contained
11,391 jobs. No umbrella build was run. Formal lint passed with existing
large-file warnings. The generated API, gaps and overview were refreshed.
The module contains 26 public theorems, one private theorem and four
definitions; duplicate checking found zero collisions among its 31
declarations. Scratch and module are byte-identical, the umbrella import
occurs once, whitespace checks passed, and every owned process finished. No axiom-print
audit, numerical experiment, added axiom, or premise asserting RH,
stationarity, radial balance, or physical-reader agreement was used.

The missing theorem remains comparison of the actual complete original
Green/BV source with the fixed physical reader. Finite original-prime
Green admission and collar symmetry do not supply it. Imposing infinitely
many original Green conditions on one source kills the source itself;
a proposed nonlocal replacement must prove the comparison while retaining
its specified nonzero coefficient and anchor, rather than transferring
admission from either finite construction above.

The next concrete comparison test is the image of this explicit paired
source under the fixed Sonin physical reader, retaining `A_P` and the
original leading Xi derivative. Its Gamma/flux discrepancy and collar
sector are now known; membership of the physical reader in a cancelling
sector still requires proof. This proposed transfer is not yet a theorem.
