# Route R rational Cartier prime-dilation landing

- **ID:** `route-r-rational-cartier-prime-dilation-landing`
- **Stage:** 1 — in progress
- **Type:** CONJECTURE RESEARCH / RH-BEARING SOURCE PRODUCER
- **Status:** `[LOCAL-RESEARCH] [OPEN CORE] [CONSUMER FORMALIZED] [NOT RH]`
- **Parent:** `route-r-source-positive-polarization-stokes-flatness.md`
- **Target:** Construct, before divisor specialization, a coefficient-faithful Cartier functor whose
  ordinary-prime specialization is a nonzero rational potential for prime dilation.

## Exact landing

Fix an ordinary prime `p` and `rho : XiDivisorSupport`.  Put

\[
 t_\rho=2\operatorname{Re}\rho-1,\qquad
 g_{p,\rho}=\exp(t_\rho\log p),\qquad
 c_\rho=\Xi^{(m_\rho)}(\rho)\ne0.
\]

Let `d_p` act on `C(z)` by `d_p H(z)=H(pz)`.  The source landing required by this
card is:

> **[CONJECTURE RCPL] Rational Cartier potential landing.**  There is a source-defined assignment,
> constructed from Euler--Gamma--rational-adelic data before selecting `rho`, whose specialization
> gives polynomials `A_{p,rho},B_{p,rho} in C[z]` such that
> \[
> B_{p,\rho}\ne0,\quad B_{p,\rho}(1)\ne0,\quad
> A_{p,\rho}(1)=c_\rho B_{p,\rho}(1),
> \]
> and, for `H_{p,rho}=A_{p,rho}/B_{p,rho}`,
> \[
> d_pH_{p,\rho}=g_{p,\rho}H_{p,\rho}.
> \]
> The construction commutes with the two Gamma orientations: reflection sends `g` to `g^{-1}`
> and the multiplicity-leading coefficient to `(-1)^{m_rho}c_rho`.  It may not inspect
> `Re rho`, the critical-line predicate, the Hodge-mate coefficient, or any equivalent endpoint.

The cross-multiplied equation, which is the formal interface and remains meaningful without
rational-function evaluation, is

\[
 A_{p,\rho}(pz)B_{p,\rho}(z)
 =g_{p,\rho}A_{p,\rho}(z)B_{p,\rho}(pz).
\]

Coefficient faithfulness implies `A_{p,rho} != 0`: the right side of
`A(1)=c_rho B(1)` is nonzero.  Thus zero potential cannot discharge the landing.

## Consumer theorem

> **[THEOREM] Rational prime-orbit rigidity annihilates mate gain.**  If RCPL exists at `(p,rho)`,
> then `g_{p,rho}=1`, hence `Re rho=1/2` and
> `ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho=0`.

### Dependency-closed proof

Write `a=deg A` and `b=deg B`.  Neither polynomial is zero.  Since `p != 0`, composition with
`z -> pz` preserves degree and multiplies leading coefficient by `p^a` or `p^b`.  Comparing
leading coefficients in the cross-multiplied Cartier equation and cancelling
`lc(A)lc(B) != 0` gives

\[
                         p^a=g_{p,\rho}p^b.
\]

All terms are positive real numbers.  Taking logarithms and using `log p > 0` yields

\[
 a\log p=t_\rho\log p+b\log p,
 \qquad t_\rho=a-b\in\mathbf Z.
\]

Every Xi-divisor support point lies in the open critical strip, so `-1<t_rho<1`.  The only integer
in that interval is zero.  Therefore `t_rho=0`, `g_{p,rho}=1`, and the already formalized exact
Route-R endpoint gives `K_{p,rho}=0`.

Conversely, if `K_{p,rho}=0`, then `t_rho=0` and `g_{p,rho}=1`.  The constant presentation
`A=C(c_rho)`, `B=1` is coefficient-faithful and satisfies the dilation equation.  Consequently
existence of the specialized rational potential is equivalent to `K=0`.  This converse is an
interface classification, not a source construction.

## Hostile audit

### Falsity

The consumer is not false: its proof uses only polynomial degree, positivity, and the unconditional
open critical strip.  For an arbitrary exponent outside the strip the sharp classification permits
the monomial solutions `H(z)=c z^k`, with gain `p^k`.

### Circularity

- **Specialized existence alone:** `RH-EQUIVALENT`.  The converse above proves this exactly.
- **Calling it rational because the source is rational-adelic:** `INVALID`.  The existing cofinal
  Mobius--theta landing can erase each fixed finite coefficient before retaining the analytic Xi
  jet; it does not preserve rationality in an auxiliary dilation coordinate.
- **Permitted producer:** a pre-divisor functorial construction of `A,B` with the displayed
  normalization and dilation square, independent of divisor location.  Proving this is the open
  scientific core.

### Rediscovery and external boundary

The rational orbit argument is classical.  Bonnet's 2026 q-difference work supplies a modern
pole-propagation vocabulary; Dreyfus's shift classification leaves an arbitrary constant rank port.
Neither constructs this Euler--Gamma-to-Xi Cartier landing.  Novelty, if any, lies only in the
source producer, not in orbit rigidity or its Lean transcription.

### Two-orientation attack

Merely choosing independent rational potentials in the two Gamma orientations is nonselective:
each can absorb its own scalar normalization.  The producer must be one coefficient-faithful
Cartier comparison whose reflected specialization is functorially determined.  Requiring a common
Laurent coordinate regular at both compactifying faces would also force constancy by the existing
two-face Laurent theorem, but identifying those two oriented coordinates is the same unresolved
Cartier comparison and may not be assumed.

## 2026-08-05 pre-divisor source functor and exact comparison defect

### Candidate RCPL-F1: regular rational family — falsified

Suppose `s` ranges over a connected open set and `A_s,B_s` have continuously varying
coefficients, nonvanishing leading coefficients, and

\[
 A_s(pz)B_s(z)=p^{2\Re s-1}A_s(z)B_s(pz).
\]

The leading-coefficient calculation above gives

\[
                    2\Re s-1=\deg A_s-\deg B_s\in\mathbb Z.
\]

The right side is locally constant while the left side is not. Therefore no regular pre-divisor
family with stable degrees can construct RCPL on a connected spectral domain. Any valid producer
must be singular and divisor-supported: rationality can appear only after Xi specialization, not
as a regular rational family for arbitrary `s`.

Verdict: **FALSIFIED**, with positive survivor "singular specialization is load-bearing."

### Candidate RCPL-F2: canonical source rational functor — proved

The literal degree-one rational-adelic cyclic source already has a functorial rational potential.
For independent jet grade `k`, spectral parameter `w`, and source chain `x`, put

\[
 h_{k,w}(x)=\XiC^{(k)}(w)\,\varepsilon_0^{(1)}(x),
 \qquad H_{k,w,x}(z)=h_{k,w}(x).                              \tag{SF1}
\]

This is linear in `x`, invariant under genuine cyclic rotation because the trace is cyclic, and
is a constant rational function. Hence it has the canonical polynomial presentation

\[
 A_{k,w,x}(z)=h_{k,w}(x),\qquad B_{k,w,x}(z)=1,              \tag{SF2}
\]

with

\[
 H_{k,w,x}(qz)=H_{k,w,x}(z)                                 \tag{SF3}
\]

for every dilation `q`. No divisor is used in `(SF1)`--`(SF3)`.

For the ordinary-prime atom `u_p`, the source theorem
`epsilon_0^(1)(u_p)=1` gives

\[
 h_{m_\rho,w_\rho}(u_p)=
 \XiC^{(m_\rho)}(w_\rho)=c_\rho\ne0.                       \tag{SF4}
\]

Thus coefficient faithfulness and non-erasure are fully source-derived. What is not automatic is
that the physical prime-dilation character acts on this source potential by the same morphism.

### Exact physical comparison defect — proved

Let `g_(p,rho)=p^(2 Re rho-1)`. On the canonical source potential `(SF2)`, physical naturality
has scalar defect

\[
 \begin{aligned}
 \partial^{\rm Cart}_{p,\rho}
   &=H_{m_\rho,w_\rho,u_p}(pz)
     -g_{p,\rho}H_{m_\rho,w_\rho,u_p}(z)\\
   &=(1-g_{p,\rho})c_\rho.
 \end{aligned}                                               \tag{SF5}
\]

The already constructed cofinal relative source landing has canonical readout

\[
 \operatorname{read}_{m}[u_p]_{\rm cof}=(g_{p,\rho}-1)c_\rho.\tag{SF6}
\]

Consequently

\[
 \boxed{\quad
 \partial^{\rm Cart}_{p,\rho}
   =-\operatorname{read}_{m}[u_p]_{\rm cof}.
 \quad}                                                       \tag{SF7}
\]

This is a nondivisive identity before any zero test. Since the cofinal readout is an equivalence
and the generator has period one, the following are equivalent:

1. the canonical source presentation is a physical rational Cartier presentation;
2. its physical naturality defect `(SF5)` vanishes;
3. the explicit cofinal central Bockstein class is null-homologous;
4. `g_(p,rho)=1`;
5. the Route-R Hodge-mate coefficient is zero.

Source rational object, coefficient, cyclic naturality, and exact comparison defect are therefore
constructed. Remaining theorem is not rational-object existence; it is an independent singular
Cartier law annihilating `(SF6)`. Declaring `(SF6)` a boundary would erase the retained period-one
generator and is forbidden.

### Genuine cyclic-coinvariant functor — proved

The representative-level construction now descends through the literal cyclic quotient

\[
 C_{1,\mathrm{cyc}}=C_1/\operatorname{im}(\tau-1).
\]

Cyclicity of `epsilon_0^(1)` makes `h_(k,w)` vanish on every genuine cyclic boundary, so there is a
canonical linear functional `bar h_(k,w)` on `C_(1,cyc)`.  The constant numerator/unit-denominator
presentation is defined directly from `bar h`, not from a chosen representative.  The
ordinary-prime class remains nonzero because its `(k,w)=(0,0)` readout is the proved nonzero
central value `XiC(0)`, and at a divisor its first nonzero readout is still `c_rho`.

The descended physical naturality defect is again exactly `(SF7)`.  Thus genuine cyclic
functoriality, quotient independence, and source non-erasure are closed.  Physical paracyclic
functoriality is not: quotienting by that defect would impose the missing conclusion.

Lean module:
`GaloisForLFunctions/RHTower/RouteRPreDivisorRationalCartierCoinvariantFunctor.lean`.

## Open core

**[OPEN CORE]** Prove, from a singular pre-divisor Cartier/Stokes law independent of divisor
placement, that the cofinal class in `(SF6)` is zero while its period-one source generator remains
retained. By `(SF7)`, this supplies the physical cross-multiplied dilation square for the already
constructed source rational presentation. The proof may not use a critical-line,
fixed-polarization, same-fibre norm, dagger, or `K=0` premise.

## Derived scalar base-change hostile audit

Universal neutral Cartier atom can be represented by two-term complex

\[
  [R\xrightarrow{q-1}R].
\]

This does not by itself solve landing. Under actual scalar specialization
`q ↦ g_(p,rho)`, it becomes

\[
  [\mathbb C\xrightarrow{g_{p,\rho}-1}\mathbb C].
\]

For `g_(p,rho) != 1`, multiplication by its inverse is an explicit two-sided contracting
homotopy. Hence complete derived scalar fibre is acyclic off line. At neutral character,
differential is zero and both distinguished homological orientations survive. Normalized atom
landing is injective exactly when Hodge-mate coefficient vanishes.

This closes a plausible but false shortcut: replacing underived fixed quotient by ordinary
derived scalar base change cannot produce non-erasure. Remaining comparison must be singular and
non-scalar before fixed-fibre specialization; its source-to-physical realization must prove a
controlled failure of scalar base-change exactness rather than assume it.

Lean module:
`GaloisForLFunctions/RHTower/RouteRDerivedScalarCartierBaseChangeWall.lean`.

## Next formal artifact

Formalize:

1. [x] the polynomial-presentation landing proposition;
2. [x] prime-dilation leading-degree rigidity;
3. [x] local equivalences among landing, `K=0`, same-fibre norm identity, source-dagger identity,
   and critical-line placement;
4. [x] global equivalence between universal landing and RH;
5. [ ] pre-divisor source construction of an inhabitant.

Do not add an inhabitant of the landing proposition until the source producer is proved.

## Log

- 2026-08-05 — Exact rational Cartier landing frozen.  Consumer paper proof closed.  Hostile audit
  identifies specialized rationality as RH-equivalent and pre-divisor coefficient-faithful
  rationality preservation as the sole open producer.
- 2026-08-05 — Formalized the rational-function semantics, valuation-at-infinity degree law,
  integer-centered-rate theorem, open-strip annihilation, reflected coefficient parity, local
  equivalences to `K=0`/same-fibre norm/source dagger, and fixed-prime global equivalence to RH.
  No source inhabitant was added.
- 2026-08-05 — Falsified regular connected-family rationalization; proved canonical constant
  rational source functor `(SF1)`--`(SF4)` and identified its physical naturality defect with the
  negative cofinal central-Bockstein coordinate `(SF7)`. This constructs source rational
  presentation but does not assert physical equivariance or global null-homology.
- 2026-08-05 — Descended the construction through genuine degree-one cyclic coinvariants, proved
  retained prime class nonzero there, and showed its physical naturality defect is still `(SF7)`.
