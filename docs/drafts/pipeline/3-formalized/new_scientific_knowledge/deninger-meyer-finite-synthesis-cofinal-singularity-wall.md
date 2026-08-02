# Deninger--Meyer finite synthesis and cofinal singularity wall

- **ID:** `deninger-meyer-finite-synthesis-cofinal-singularity-wall`
- **Stage:** 3-formalized
- **Type:** FINITE XI-JET SYNTHESIS / FULL-PRODUCT ADMISSION NO-GO / ALL-ORDERS SINGULARITY
- **Label:** `DAC_DENINGER_MEYER_FINITE_SYNTHESIS_COFINAL_SINGULARITY`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** Literal all-weight Meyer cohomology realizes every finite packet of actual Xi jets
  with exact multiplicity-sensitive Jordan flow, but it cannot realize the unrestricted product
  of all Xi jets. More sharply, every cofinal family of unit interpolants has order-\(n\)
  weighted source cost \(>(j+1)^n\) at stage \(j\), for every \(n>0\). Finite synthesis is exact;
  inverse-limit synthesis is necessarily singular to every finite differential order.

## 1. Literal source and finite divisor packets

Let \({\cal H}_{\rm M}\) be the all-weight logarithmic Meyer target modulo the literal Poisson
range. For an actual Xi divisor point \(\rho\), let
\[
 J_\rho=\{0,\ldots,m_\rho-1\}
\]
be the jet indices below its analytic multiplicity.

For every finite family of distinct actual divisor points
\[
 \rho_1,\ldots,\rho_r
\]
and arbitrary values \(a_{i,k}\in\mathbb C\), \(k\in J_{\rho_i}\), there exists one literal
Meyer class \(u\in{\cal H}_{\rm M}\) such that
\[
 \partial_s^k{\cal M}u(\rho_i)=a_{i,k}
 \quad
 (1\le i\le r,\ k\in J_{\rho_i}).
\]
Equivalently, simultaneous finite jet evaluation is surjective.

Proof is source-native. A linear relation among Mellin jet functionals gives a
polynomial-exponential distribution
\[
 \sum_{i,k}c_{i,k}e^{\rho_i t}t^k.
\]
Testing against compactly supported smooth sources makes this function zero. Its Wronskian at
zero is the transpose of the confluent polynomial jet matrix. Exact determinant is a nonzero
product of factorials and pairwise differences \(\rho_i-\rho_j\). Hence all functionals are
linearly independent, and finite-dimensional duality gives surjectivity.

The common kernel is invariant under literal Meyer dilation. The quotient flow is conjugate to
the direct sum of the multiplicity-sensitive Jordan packet flows. Thus finite synthesis preserves
the actual divisor multiplicities and dynamics; it is not a divisor-indexed ambient space
declared after the fact.

## 2. Unrestricted full product is not source-admissible

For \(g\) in the literal all-weight logarithmic source and
\[
 0\le \sigma\le1,
\]
put
\[
 h_\sigma(t)=e^{\sigma t}g(t),\qquad
 C_1(g)=\int_{\mathbb R}e^{|t|}
   \bigl(|g(t)|+|g'(t)|\bigr)\,dt.
\]
Fourier integration by parts gives the uniform closed-strip estimate
\[
 \boxed{\quad
 |\tau|\,|{\cal M}g(\sigma+i\tau)|\le C_1(g).
 \quad}
\]

Local finiteness and infinitude of the actual Xi divisor provide a sequence
\(\rho_j\) escaping every norm ball. Since \(0<\Re\rho_j<1\),
\[
 |\Im\rho_j|\longrightarrow\infty.
\]
Therefore
\[
 {\cal M}g(\rho_j)\longrightarrow0
\]
for every literal source \(g\).

The result is uniform in a stronger set-theoretic form: for every \(\varepsilon>0\),
\[
 \left\{\rho\in\operatorname{supp}\operatorname{div}(\Xi):
   \varepsilon\le|{\cal M}g(\rho)|\right\}
\]
is finite. Zeroth-jet restriction therefore obeys a canonical \(c_0\)-type admission law on
actual Xi support.

Let
\[
 {\cal P}_{\rm raw}
 =\prod_\rho\prod_{0\le k<m_\rho}\mathbb C.
\]
The constant unit packet belongs to \({\cal P}_{\rm raw}\), but its zeroth coordinates do not
decay on \((\rho_j)\). Hence it is not in the image of literal Meyer cohomology:
\[
 \boxed{\quad
 {\cal H}_{\rm M}\longrightarrow{\cal P}_{\rm raw}
 \text{ is not surjective.}
 \quad}
\]

Every finite projection is surjective, while the unrestricted product map is not. This is an
exact finite/infinite admission boundary, not a dimension comparison.

## 3. All-orders cofinal synthesis singularity

Define the conjugated weighted derivative
\[
 B_\sigma g=\sigma g+g'.
\]
All-weight Meyer decay is stable under \(B_\sigma\), and
\[
 \frac{d^n}{dt^n}\bigl(e^{\sigma t}g(t)\bigr)
 =e^{\sigma t}B_\sigma^ng(t).
\]
Every derivative is integrable. Repeated Fourier integration by parts gives, unconditionally,
\[
 \boxed{\quad
 |\tau|^n\,|{\cal M}g(\sigma+i\tau)|
 \le
 \int_{\mathbb R}
 \left|
 \frac{d^n}{dt^n}\bigl(e^{\sigma t}g(t)\bigr)
 \right|\,dt
 \quad(n\ge0).
 \quad}                                                       \tag{1}
\]

Write the right side as \(C_{n,\sigma}(g)\). Choose actual Xi points with
\[
 |\Im\rho_j|>j+1.
\]
Finite packet surjectivity supplies \(g_j\) satisfying
\[
 {\cal M}g_j(\rho_j)=1.
\]
Equation (1) forces, for every \(n>0\),
\[
 \boxed{\quad
 C_{n,\Re\rho_j}(g_j)>(j+1)^n.
 \quad}                                                       \tag{2}
\]
The same lower bound holds for every other literal unit interpolant at \(\rho_j\), not only the
chosen one.

Thus a cofinal family of finite-stage sections cannot be bounded in the natural mixed-strip
Fréchet source topology. At each positive differential order its cost grows at least as the
matching power of spectral height. No uniformly regular projective-limit section can arise from
these finite quotient splittings.

## 4. Scientific consequence for Route L

The finite quotient and literal one-way Xi inclusion close the consumer-side packet algebra:
actual divisor jets and their exact Jordan flow occur in literal Meyer cohomology without RH,
simplicity, or an abstract divisor carrier.

They also invalidate a previously overlarge target. Route L must not ask an arithmetic source
comparison to be surjective onto the raw product \({\cal P}_{\rm raw}\). That target contains
packets forbidden by literal Meyer decay.

Correct full target must retain a decay-compatible nuclear/Fréchet packet topology. Any
arithmetic-to-Meyer comparison assembled from finite stages must either:

1. preserve this source decay and have no uniformly bounded cofinal section; or
2. use the label-retaining or source-singular transport category isolated by
   `source-horizon-riemann-divisor/main.tex`.

This aligns two independently derived boundaries:

- updated prime-source paper proves nonerasing conservative equivariant descent must retain
  source labels or be singular relative to canonical source norms;
- literal Meyer theorem (2) proves cofinal Xi synthesis is singular to every finite differential
  order.

Neither result constructs the arithmetic comparison. Their conjunction sharply types it.

## 5. Hostile audit

- **Not Meyer's spectral realization renamed.** Meyer already constructs a nuclear Fréchet
  spectral model whose spectrum is the nontrivial zeta divisor with algebraic multiplicity.
- **Not global zeta-zero interpolation renamed.** Bondarenko--Radchenko--Seip already construct
  rapidly decaying entire interpolation functions indexed by zeta zeros and multiplicity jets.
- **Not “Schwartz functions decay.”** New project theorem is the exact conjunction of
  simultaneous literal-Meyer finite quotient surjectivity, raw full-product non-surjectivity,
  finite-superlevel admission, and the universal lower bound (2) for every cofinal unit
  synthesis.
- **Not dimension counting.** Finite surjectivity uses an exact confluent Wronskian.
- **Not one selected bad representative.** Bound (2) holds for every literal source having unit
  value at the selected actual divisor point.
- **Not a full trace-space characterization.** No claim is made that every \(c_0\), Schwartz, or
  other proposed Xi sequence belongs to the image. Exact full trace space remains open.
- **Not arithmetic source descent.** Finite interpolation uses literal Meyer sources. No theorem
  maps Deninger's rational-Witt relevant complex into them.
- **Not RH progress by equivalence.** Positivity, conservative Hodge transport, and zero
  exclusion are absent.

## 6. Novelty audit

Primary-source audit located:

- Meyer’s characterization of the Fourier--Laplace image as entire functions Schwartz on every
  vertical line, and his spectral multiplicity theorem;
- Paugam’s symplectic pairing on the Connes--Meyer spectral realization;
- Bondarenko--Radchenko--Seip’s global Fourier interpolation basis involving all nontrivial zeta
  zeros and multiplicity jets.

These results establish stronger global interpolation structures in adjacent function spaces and
are credited as prior art. No located primary source states the exact quantitative lower bound
(2) for literal Meyer unit interpolants, the resulting no-uniform-section theorem, or its
source-conservation interpretation. Repository search found neither result.

Priority claim is restricted to that quantitative literal-Meyer cofinal singularity and its exact
finite/full admission synthesis. Specialist priority review remains necessary.

## 7. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/DeningerMeyerXiSpectralInclusion.lean`;
- `GaloisForLFunctions/RHTower/DeningerMeyerXiJetPacketSurjectivity.lean`;
- `GaloisForLFunctions/RHTower/DeningerMeyerFiniteXiJetPacket.lean`;
- `GaloisForLFunctions/RHTower/DeningerMeyerFullXiJetAdmissionBoundary.lean`;
- `GaloisForLFunctions/RHTower/DeningerMeyerXiCofinalSynthesisSingularity.lean`.

Capstones:

1. `deningerMeyerXiSupportSpectralJetLM_linearIndependent`;
2. `deningerMeyerXiJetPacketLM_surjective`;
3. `deningerMeyerFiniteXiJetPacketLM_surjective`;
4. `deningerMeyerFiniteXiJetPacketQuotientFlow_conjugacy`;
5. `deningerMeyerStrongLogMellin_xiSupport_superlevel_finite`;
6. `deningerMeyerFullXiJetUnitPacket_not_mem_range`;
7. `deningerMeyerFullXiJetPacketLM_not_surjective`;
8. `abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le`;
9. `deningerMeyerVerticalSobolevCost_gt_pow_of_unit_at_xiEscape`;
10. `deningerMeyerXiCofinalUnitSynthesis_cost_gt_pow`.

No `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, numerical computation, RH, zero
simplicity, positive Hodge premise, inverse Mellin theorem, or global packet-surjectivity premise
is used.

## 8. Exact remaining boundary

Route L still requires the actual sheafified relevant coefficient complex on Deninger's
rational-Witt geometry and a source-defined comparison into the decay-compatible literal Meyer
packet image. It must:

1. retain the updated paper's Boolean shell labels or realize their prescribed singular
   transport;
2. identify closed arithmetic middle boundaries with the comparison kernel;
3. transport Paugam cup/trace parity and weight-one flow;
4. descend to a positive harmonic Hodge completion faithful on the actual decay-compatible image;
5. prove that the already-formalized literal Xi packet inclusion is the image of this arithmetic
   comparison.

Items 2--4 remain the RH-bearing source/Hodge gate.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.
- Andriy Bondarenko, Danylo Radchenko, Kristian Seip,
  *Fourier interpolation with zeros of zeta and L-functions*,
  https://arxiv.org/abs/2005.02996.
- `docs/drafts/pipeline/4-publication-ready/source-horizon-riemann-divisor/main.tex`.
- `docs/drafts/pipeline/4-publication-ready/riemann-source-modular-superselection/main-universal.tex`.

## Log

- 2026-08-01 — Literal one-point and simultaneous finite actual-Xi jet quotients constructed,
  including exact Jordan flow conjugacy.
- 2026-08-01 — Uniform strip estimate, finite-superlevel admission, and raw full-product
  non-surjectivity proved.
- 2026-08-01 — All-orders Fourier estimate and cofinal synthesis cost lower bound proved.
- 2026-08-01 — Primary-source audit corrected novelty boundary to exclude Meyer spectral
  multiplicity and Bondarenko--Radchenko--Seip interpolation.
