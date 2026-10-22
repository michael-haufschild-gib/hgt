# SQB native source resolvent transport

Status: native graph, exact forcing kernel and bounded approximate concentration closed; fixed source, its original cutoff family and unnormalized forcing criterion excluded; independent normalized occurrence open; RH unproved.
Frontier map is read-only.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.

## Closed bridge and remaining occurrence

The completed source correction supplies a nonzero native L² vector V and an
actual entire-domain vector CV. Its entire residual is
`G=V−(2+mu)CV`, with mu the full transformed Xi Casimir.
The [completed native graph audit](../../../3-formalized/sqb-original-source-native-graph.md)
identifies V in the actual native domain and proves `(A−e)V=H`, with
`e=1+(rho/2)(1−rho/2)` and H the complete original cutoff-forcing vector.
For B=A^(-1), it also proves `(1−eB)V=BH`.

The completed `SelbergScatteringForcingTransport` module identifies the
original source with the actual native bounded resolvent `R_e H=V`. It defines
the exact bounded operator `K_q=(I−(2+mu)C)R_e` and proves

`(T−mu)CV = G = K_q H`,

`||(T−mu)U|| = ||C R_e H||^(-1) ||K_q H||`, for U=CV/||CV||.

The denominator is positive. Nonreality of e and every domain and inverse input
are discharged for the actual Xi copies. The new
[complete forcing-kernel audit](../../../3-formalized/sqb-entire-forcing-kernel.md) proves
K_q H≠0 and strictly positive unit residual for this fixed source at every copy.
The scalar rational CFC representation remains optional further work.

The unresolved problem is independent full-Xi occurrence from another suitable
source or a controlled approximate family. The fixed corrected vector cannot
supply exact occurrence, and its constructed normalized cutoff family cannot
supply approximate occurrence, including at critical copies. The exact positive
kernel theorem identifies what cancellation would require for any forcing f:

`K_q f=0 iff f=0 or (Re rho=1/2 and Bf=(5/4+(Im rho)^2/4)^(-1)f)`.

This classifies the required native eigenspace and does not produce its
occupation. No uniform lower bound across arbitrary source families or all Xi copies is claimed.
The full SQB interface remains open.

## Source and domain work

At an actual Xi copy the full principal term is
`Lambda(rho−1)y^(1−rho/2)`. The retained forcing therefore reduces exactly to
that nonzero coefficient times the original differential cutoff commutator.
The existing corpus admits this commutator in the native measure and proves its
smooth height representation. The [completed forcing audit](../../../3-formalized/sqb-original-cutoff-forcing.md)
constructs that exact Hilbert vector and proves it nonzero for every actual Xi
copy. Its complementary height moment is the nonzero boundary value 1−rho,
while its absolutely convergent bilinear pairing with the original scalar
source is zero. That scalar cancellation does not remove the vector forcing.

Native graph admission is proved by compact modular approximants and norm
convergence of both values and complete operator images. The original energy
space remains the closure of modular value-and-gradient core fields.

- [x] Inspect exact source residual and existing native operator definitions.
- [x] Broad OR searches for resolvents, cutoff commutators, domains and exhaustion.
- [x] Identify and admit the full original cutoff forcing as a native vector.
- [x] Prove native graph admission and the actual closed-operator equation.
- [x] Identify the original source with the bounded native resolvent and transport the forcing.
- [x] Classify the exact full-Xi forcing kernel and test the fixed corrected source.
- [x] Construct the actual normalized cutoff family and prove its positive residual limit.
- [x] Recover native spectral concentration from arbitrary bounded entire approximate families.
- [x] Construct the unit forcing family with vanishing numerator and response; audit the normalized quotient.
- [ ] Produce independent normalized full-Xi occurrence using another source or a controlled approximate family.
- [x] Audit all five modules individually; retain unresolved occurrence obligations.

Search metadata: 245 declarations in 82 modules for resolvents, commutators,
spectral multipliers, source cancellation and scattering residues; 438 in 127
modules for operator domains, weak solutions, compact forcing, finite energy,
energy completion and graph closure; 80 in 39 modules for cutoffs, graph
approximation, compact exhaustion, modular partitions, Dirichlet unfolding and
Friedrichs cores. These are index counts, not a claim to have read every proof.

A broader single-word OR search for smoothTransition, cutoff and partition
covered 6,143 declarations in 1,914 modules. It exposed the existing uniform
first-derivative bound and all-order smooth-transition bounds. A further OR
search for periodization, Laplacian, formal adjoints and test separation covered
911 declarations in 258 modules. Inspected actual compact normalization,
modular Laplacian covariance, chart germ locality and finite-sum differentiation.

## Native core implementation

The current construction represents every smooth modular field with compact
quotient support as the full periodization of a compact planar test. A squared
smooth bump covers the retained cell support. Its entire projective orbit sum
p has nonnegative real part and Re p≥1 wherever the original field is nonzero.
The smooth denominator `p+1−smoothTransition(2 Re p−1)` is nonzero everywhere
and equals p on that retained support. Normalized full periodization therefore
recovers the field exactly, including elliptic stabilizer contributions.

The [completed full-core audit](../../../3-formalized/sqb-full-modular-operator-core.md)
proves that representation, native domain membership, commutation of the
literal Laplacian with full compact periodization, preservation of the core
by the Laplacian, and exact native operator action `1−Delta_H`. The noncompact
original source is now admitted by the
[completed graph construction](../../../3-formalized/sqb-original-source-native-graph.md).
The expanding height windows `smoothWeight(a,a)`, a=n+3, glue smoothly on the
whole modular quotient. Their products with the complete original source are
actual compact core fields; bounded multiplier convergence proves their native
L² convergence to V.

## Graph convergence

A broad OR search for approximation, dominated convergence and exhaustion
covered 4,905 declarations in 2,252 modules. An OR search for jets, cusp decay,
tail bounds and derivative bounds covered 21,318 declarations in 3,663 modules.
The inspected full Fourier–Bessel derivative and family-bound theorems admit
the actual weighted vertical derivative D=y∂yR in native L². All signed families
and the original source germ are retained.

Uniform scaled cutoff derivative bounds and strong multiplier convergence
remove both complete product-rule errors:

`A V_n = e V_n + H − (y² beta_n'')V − 2(y beta_n')D → eV+H`.

The original forcing satisfies beta_n H=H for every n. Together with V_n→V
and the actual inverse B A V_n=V_n, this proves B(eV+H)=V, actual native domain
membership, `(A−e)V=H`, and `V−eBV=BH`. These are audited Lean conclusions.

A further broad OR search for resolvents, functional calculus, spectral
multipliers and forcing transport returned 3,478 declarations in 647 modules.
Inspected the generic nonreal self-adjoint resolvent, its bounded realization,
and the existing CFC residual factorization. Search counts describe metadata
coverage, not a claim to have read every declaration.

## Fixed-source occurrence audit

The [fixed-source exact-occurrence mechanism](../../../5-failed/sqb-fixed-corrected-source-exact-occurrence.md)
is closed negatively. Both its obstruction and strongest positive survivor are
paper-proved and audited in Lean. The reciprocal symbol's unique nonnegative
fibre recovers the original covariance eigenspace. Reality and the actual lower
range bound force critical placement for every nonzero full-Xi entire eigenvector.
The native resolvent commutes with B, so the same classification gives the
complete forcing-transport kernel for every native vector.

The original full source has a nonzero closed-cell value strictly below height
2, where the original cutoff forcing is zero. Continuity of actual native
representatives therefore proves H≠cV for every scalar c. The forced native
equation excludes every native eigen-equation for V. The exact fibre theorem
then proves G≠0, K_q H≠0 and strictly positive residual for its actual unit vector
at every Xi copy. This does not exclude arbitrary approximate source families.

Broad OR searches for eigenvectors, spectral fibres, kernel preservation and
source cancellation returned 807 declarations in 373 modules. An OR search for
kernel comparison, kernel inclusion, zero sets and functional calculus returned
569 declarations in 336 modules. Inspected the actual Dini/kernel proof,
reciprocal symbol, full real preimage classifier, native inverse equations and
original source nonvanishing. Counts describe metadata coverage, not a claim to
have read every declaration.

## Original cutoff-family limit

The actual compact source approximants V_n satisfy V_n→V in native norm and are
nonzero for every n because they retain the same nonzero source point below
the transition. The new `SelbergScatteringApproximateSourceResidual` constructs
actual unit domain vectors U_n=C V_n/||C V_n||. Their complete values and actual
entire-operator images converge in native norm to U and T U respectively.
Their full-Xi residual norm therefore converges exactly to ||(T−mu)U||>0.
Increasing these original cutoffs cannot yield approximate occurrence.

This exact positive graph limit is preserved alongside the complete kernel
classification as the obstruction's positive survivor. Other source families
remain open. A broad OR search for normalization and residual/convergence
interfaces covered 3,141 declarations in 1,403 modules; the implementation uses
the already inspected original-source normalization and actual covariance
inverse action, with every nonzero denominator proved. Counts describe metadata.

## Spectral concentration and response normalization

The [completed concentration audit](../../../3-formalized/sqb-native-spectral-concentration.md)
proves that equal continuous spectral zero sets have exactly the same bounded
approximate kernels. The signed regularizer `g/(1+n f²)` gives uniformly small
operator-norm remainders and exact continuous factorization. No spectral gap
or differentiability is assumed.

For the actual entire covariance, this identifies precisely the original
native covariance concentration at `b=(5/4+(Im rho)^2/4)^(-1)`. Every successful
unit entire approximate family u_n forces critical placement and produces
actual native-domain unit vectors `w_n=B u_n/||B u_n||`, with
`||(A−b^(-1))w_n||→0` and `||w_n−u_n||→0`. This recovers the required native
concentration; it does not independently construct u_n.

The actual pre-divisor cusp packets also supply one unit native forcing family
f_n with `||B f_n||≤2/(n+1)`. The exact identity `R_e=(I+e R_e)B` proves
`||R_e f_n||→0`, `||C R_e f_n||→0`, and `||K_q f_n||→0` for every Xi q.
The numerator tends to zero at every complex target, including i. Every
normalization denominator is positive, but it tends to zero. The actual unit
responses have residual at least one at i. Thus
[unnormalized forcing smallness is excluded as an occurrence criterion](../../../5-failed/sqb-unnormalized-forcing-occurrence.md).
The strongest positive survivor retains the unit family, quantitative bound,
exact factorization, full response limits and exact normalized residual quotient.
No normalized full-Xi residual limit is asserted for this family.

Broad OR discovery for concentration, localization, approximate, Weyl and
compactness returned 4,362 declarations in 1,088 modules. Automorphic discovery
returned 11,706 in 1,482; transmutation discovery returned 888 in 155; high
energy, high frequency, escape and covariance discovery returned 4,517 in
1,003. Inspected the actual one-way divided-difference transport, zero-set
kernel proof, original native cusp packets, inverse equations, retained
reflected Mellin moment, and Beta resonance transmutation. Counts describe
metadata coverage, not proof-by-proof inspection of every result.

## Current verification

The concentration and normalization audit contains 34 public declarations in
three modules. Scratch and source checks, isolated sole-target final builds,
all 34 standard-axiom audits, generated index coverage and single umbrella
imports passed. No new module warning or proof debt was introduced. Two builds
replayed 83 cached dependency warnings each. Earlier completed audits cover
29 kernel/source-family declarations, 58 graph/transport declarations and 19
forcing/full-core declarations. No numerical experiment or computed proof
input was used.

The full formal lint invocation reports five unrelated missing umbrella
imports: `GaloisForLFunctions.RHTower.FokasLenellsCauchyModulation`,
`GaloisForLFunctions.RHTower.FokasLenellsOperatorNormCauchy`,
`GaloisForLFunctions.RHTower.FokasLenellsOperatorNormInverse`,
`GaloisForLFunctions.RHTower.FokasLenellsOperatorNormObstruction`, and
`GaloisForLFunctions.RHTower.FokasLenellsOperatorNormRegularity`.
The three new modules have no lint errors. Other-task modules were left untouched.
