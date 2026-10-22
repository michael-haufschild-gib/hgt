# Deninger--Meyer global Poisson cycle classification

- **ID:** `deninger-meyer-global-poisson-cycle-classification`
- **Stage:** 3-formalized
- **Type:** PRIME-SAMPLING COHOMOLOGY NO-GO AND ENDPOINT-GLOBAL POSITIVE SURVIVOR
- **Label:** `DAC_DENINGER_MEYER_GLOBAL_POISSON_CYCLE_CLASSIFICATION`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** Even prime-sampled secondary cycles strictly exceed global Meyer--Poisson cycles.
  Entire space of even zero-endpoint functions vanishing at every prime injects into
  prime-sampled `H¹`. All-radius Calderón defect is therefore a missing differential, not an
  optional regularity condition. After adding it and both Meyer endpoint conditions, every cycle
  is faithfully determined by one collar.

## 1. Prime sampling remains nonconservative after parity

Let
\[
 E_{\mathbb P}
 =\{k:\mathbb R\to\mathbb C:
   k(-x)=k(x),\ k(0)=0,\ k(p)=0\text{ for every prime }p\}.
\]
For \(k\in E_{\mathbb P}\), put \(\iota(k)=(k,0)\). This pair is even. Its secondary value at every
prime is
\[
 p^{-1/2}\bigl(k(p)-p^{-1}0\bigr)T_p(a_p)=0,
\]
so it is a cycle in the parity-corrected prime-sampled complex.

Suppose \(\iota(k)\) were a literal boundary \((Zf,Z\widehat f)\). For every \(x>0\), global
Meyer--Poisson reflection gives
\[
 k(x)=Zf(x)=x^{-1}Z\widehat f(x^{-1})=0.
\]
Evenness gives \(k(x)=0\) for \(x<0\), and endpoint condition gives \(k(0)=0\). Hence \(k=0\).
Therefore
\[
 \boxed{\ E_{\mathbb P}\hookrightarrow H^1_{\rm prime,even}\ }
\]
complex-linearly and injectively.

This is not a density argument. It is an exact cohomology injection. Point mass on \(\{\pm1\}\)
is one explicit nonzero class.

## 2. All-radius defect

Define positive-radius Calderón defect
\[
 \delta_\infty(h)(x)
 =h_+(x)-x^{-1}h_-(x^{-1}),
 \qquad x>0.
\]
It is complex-linear, and every literal Meyer boundary lies in its kernel. On the even Bessel
middle term,
\[
 \ker\delta_\infty
 \subseteq \ker d^1_{\mathbb P}.
\]
Inclusion is strict: point mass on \(\{\pm1\}\) lies in prime-sampled kernel but has
\(\delta_\infty(h)(1)=1\). Thus
\[
 \boxed{\ \ker\delta_\infty
   \subsetneq Z^1_{\rm prime,even}. \ }
\]

This identifies exact missing structure. No topology in which positive-prime evaluation alone
retains arbitrary even algebraic functions can recover global Poisson cycles. A literal source
complex must carry \(\delta_\infty\), an equivalent continuous separating family, or a source
topology/domain on which prime samples determine it.

## 3. Global separated complex

Replacing sparse secondary differential by \(\delta_\infty\) gives
\[
 H_\cap
 \xrightarrow{f\mapsto(Zf,Z\widehat f)}
 {\cal D}^{\rm even}_a
 \xrightarrow{\delta_\infty}
 \mathbb C^{\mathbb R_{>0}}.
\]
Poisson reflection proves composite zero. Degree-one cycles satisfy exact classification
\[
 h\in Z^1_{\rm global}
 \iff
 \forall x>0,\quad h_+(x)=x^{-1}h_-(x^{-1}).
\]

This closes algebraic all-radius cycle law. It does not supply target nuclear topology.

## 4. Endpoint-zero correction

Positive-radius relation does not see \(h_+(0)\) or \(h_-(0)\). Literal Meyer boundaries have both
zero modes equal to zero. Define
\[
 {\cal D}^{\rm end}_a
 =\{h\in{\cal D}^{\rm even}_a:h_+(0)=h_-(0)=0\}.
\]
The literal boundary lands in this domain. Restricting \(\delta_\infty\) gives endpoint-global
complex
\[
 H_\cap\longrightarrow
 {\cal D}^{\rm end}_a
 \xrightarrow{\delta_\infty}
 \mathbb C^{\mathbb R_{>0}}.
\]

Its cycles still obey exact global graph law. Physical-collar projection
\[
 Z^1_{\rm end,global}\longrightarrow(\mathbb R\to\mathbb C),
\qquad (h_+,h_-)\longmapsto h_+
\]
is injective:

- global graph determines \(h_-\) at positive radii from \(h_+\);
- evenness determines negative radii;
- endpoint condition determines radius zero.

Thus corrected two-collar cycle is faithfully one-collar data. This is exact algebraic shape
required for comparison with Meyer's
\[
 H_-/\operatorname{range}Z,
\]
without asserting topological equality.

## 5. Hostile audit

- **Not “primes are not dense.”** New theorem is a linear injection
  \(E_{\mathbb P}\hookrightarrow H^1\) and strict kernel inclusion
  \(\ker\delta_\infty\subsetneq Z^1_{\rm prime,even}\).
- **Not fitted to one witness.** Full subspace \(E_{\mathbb P}\) injects. Point mass proves
  strictness concretely.
- **Not arbitrary extra differential.** \(\delta_\infty\) is exactly source Poisson relation
  already satisfied by every literal Meyer boundary.
- **Not a literal arithmetic relevant complex.** Result is separated radial algebra. Missing
  comparison to Deninger's sheafified rational-Witt geometry, nuclear topology, closed-range
  theorem, cup/Hodge descent, flow, and Xi inclusion remains.
- **No target use.** Packet values, Xi divisor, and desired sign are not used to choose
  \(\delta_\infty\), parity, or endpoint constraints.

## 6. Novelty audit

Repository audit found no prior prime-invisible cohomology injection, strict comparison between
all-radius and prime-sampled Poisson kernels, endpoint-global three-term complex, or one-collar
faithfulness theorem. Classical Poisson summation, Meyer's even endpoint source, and Deninger's
program are parent ingredients and are not claimed new.

Targeted primary-source searches located Meyer, Deninger, Paugam, and rational-Witt sheaf
constructions but no statement of these exact kernel/cohomology classifications. Priority remains
provisional pending specialist review.

## 7. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPrimeSamplingCohomologyObstruction.lean`;
- `GaloisForLFunctions/RHTower/Deninger/DeningerMeyerEndpointGlobalPoissonComplex.lean`.

Capstones:

1. `deningerMeyerPrimeInvisibleEvenH1LM_injective`;
2. `deningerMeyerPrimeInvisibleUnitMass_H1_ne_zero`;
3. `deningerMeyerGlobalPoissonDefect_boundary_zero`;
4. `deningerMeyerGlobalPoissonDefect_ker_lt_cycles`;
5. `deningerMeyerGlobalPoissonThreeTermComplex`;
6. `deningerMeyerGlobalPoissonThreeTerm_cycles1_iff`;
7. `deningerMeyerEndpointGlobalPoissonThreeTermComplex`;
8. `deningerMeyerEndpointGlobalPoisson_cycles1_iff`;
9. `deningerMeyerEndpointGlobalCyclesFirstLM_injective`.

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, numerical computation, Xi divisor, zeta zero,
or RH-equivalent premise is used.

## 8. Exact remaining boundary

Endpoint-global cycles now have correct one-collar algebraic shape, but middle domain remains an
algebraic Bessel domain. Next real gate is a continuous comparison from literal
rational-Witt/relevant sheaf into a nuclear one-collar source whose Poisson image has closed range,
such that:

1. induced two-collar graph is exactly endpoint-global cycle space;
2. arithmetic middle boundaries equal closed range of literal Meyer map;
3. reciprocal Paugam cup/Hodge form is continuous and nondegenerate on resulting quotient.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.
- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  https://arxiv.org/abs/2508.05329.

## Log

- 2026-08-02 — Full prime-invisible even endpoint subspace injected into parity-corrected `H¹`.
- 2026-08-02 — All-radius Calderón defect constructed; its kernel proved strictly smaller than
  prime-sampled cycles.
- 2026-08-02 — Global Poisson complex and exact cycle law constructed.
- 2026-08-02 — Both Meyer endpoints imposed; endpoint-global cycles proved faithfully determined
  by physical collar.
