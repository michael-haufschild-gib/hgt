# Prime--archimedean moment pole--residue pinch law

- **ID:** `prime-arch-moment-pole-residue-pinch-law`
- **Stage:** 3-formalized
- **Type:** exact source value relation / residue quantization / top-down RH bridge
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** fully formalized — see the 2026-08-19 section

## Statement

Write

\[
 R=\texttt{primeArchEndpointHausdorffRadius},\qquad
 c_q=\texttt{xiZeroCopyReciprocalSquare}(q),\qquad
 u_q=\frac{c_q}{R},
\]

and form the ordinary normalized moment germ

\[
 M_R(v)=\sum_{n\ge0}
 \frac{\texttt{normalizedPrimeArchMoment}(n)}{R^n}v^n. \tag{1}
\]

The live formal coefficient identity implies, initially near zero,

\[
 \boxed{
 M_R(v)=\sum_q\frac{c_q}{1-u_qv}.
 }                                                       \tag{2}
\]

Since `sum_q |c_q|<infinity` and `u_q -> 0`, the right side extends meromorphically to the whole
`v`-plane.  Group the exact divisor-multiplicity copies by a common nonzero normalized coordinate
`u`, and put

\[
 C_u=\sum_{q:u_q=u}c_q,
 \qquad m_u=\#\{q:u_q=u\}.
\]

Then

\[
 C_u=Ru\,m_u\ne0,                                      \tag{3}
\]

so the poles of `M_R` are exactly

\[
 p_u=\frac1u,
\]

all are simple, and their residues are quantized:

\[
 \boxed{
 \operatorname*{Res}_{v=p_u}M_R(v)=-\frac{C_u}{u}=-R m_u
 \in -R\,\mathbb N_{>0}.
 }                                                       \tag{4}
\]

Thus there is no pole cancellation between multiplicity copies or functional-equation partners.
The residue records the exact total multiplicity of the reciprocal-square fibre and contains no
orientation ambiguity.

The same pole controls the reflected Bernstein pinch.  Its affine amplitude and positive pinch
location are

\[
 B(p)=\frac{1+|p-1|}{|p|},
 \qquad
 \tau(p)=B(p)^{-2}
 =\frac{|p|^2}{(1+|p-1|)^2}.                            \tag{5}
\]

Triangle equality gives

\[
 \boxed{
 B(p)=1\iff p\in[1,\infty).
 }                                                       \tag{6}
\]

Consequently,

\[
 \boxed{
 \mathrm{RH}
 \iff \text{every pole of }M_R\text{ lies in }[1,\infty).
 }                                                       \tag{7}
\]

The useful content is stronger than the ray reformulation.  If `p` is off that ray, then
`tau(p)<1`, and its same-coordinate packet contributes the exact nonzero half-order coefficient

\[
 \boxed{
 \kappa(p)=
 \frac{|\operatorname*{Res}_p M_R|^2(1+|p-1|)}
 {2|p|^2\sqrt{|p-1|}}>0
 }                                                       \tag{8}
\]

to the local factor `(1-t/tau(p))^(-1/2)` of the paired Bernstein susceptibility.  For a maximal
off-ray packet, phase rigidity makes every other term holomorphic at the first pinch, so these
positive coefficients add over poles with the same maximal value of `B(p)` and cannot cancel.

## Exact reflection geometry

The ordinary pole coordinate collapses functional-equation reflection and preserves Schwarz
reflection:

\[
 \boxed{
 p(1-\rho)=p(\rho),\qquad
 p(\bar\rho)=\overline{p(\rho)}.
 }                                                       \tag{9}
\]

Divisor multiplicity is preserved by both reflections.  Equation `(4)` therefore gives

\[
 \operatorname*{Res}_{\bar p}M_R
 =\overline{\operatorname*{Res}_{p}M_R}
 =\operatorname*{Res}_{p}M_R=-Rm_p.                    \tag{10}
\]

Thus an off-real pole and its Schwarz partner have the same pinch radius and the same positive
coefficient `(8)`.  Functional-equation partners have already merged into one fibre residue.
Neither reflection can cancel the oriented branch charge.

## Proof of the source pole law

The formal corpus proves

\[
 \texttt{normalizedPrimeArchMoment}(n)
 =\sum_q c_q^{n+1}.
\]

After division by `R^n`,

\[
 \frac{\texttt{normalizedPrimeArchMoment}(n)}{R^n}
 =\sum_q c_qu_q^n.                                      \tag{11}
\]

Absolute summability permits the geometric-series interchange near zero and gives `(2)`.
On a compact set avoiding all points `1/u_q`, the coordinates with sufficiently small `|u_q|`
have denominators uniformly bounded away from zero.  Only finitely many remaining coordinates
occur, so the series in `(2)` converges normally there.  Since `u_q -> 0`, its possible poles have
no finite accumulation point.  This proves the global meromorphic continuation.

For a fixed fibre, `c_q=Ru` for every copy.  Hence `(3)` holds, and its grouped summand is

\[
 \frac{C_u}{1-uv}.
\]

Its residue at `p_u=1/u` is `-C_u/u=-Rm_u`, proving `(4)` and exactness of the pole set.

Functional-equation reflection changes the centered zero coordinate `rho-1/2` to its negative,
so its reciprocal square and hence `p` are unchanged.  Schwarz reflection conjugates the centered
coordinate, hence conjugates `c`, `u`, and `p`.  The formal divisor reflection laws preserve
multiplicity, and `(4)` is real; this proves `(9)`--`(10)`.

## Proof of the pinch transfer

Substitute `u=1/p` into the affine Bernstein amplitude:

\[
 |u|+|1-u|
 =\frac{1+|p-1|}{|p|}=B(p),
\]

which proves `(5)`.  The triangle inequality gives `|p|<=1+|p-1|`.  Equality holds exactly when
`1` and `p-1` have the same nonnegative real direction, namely when `p` is real and `p>=1`; this
proves `(6)`.

On the critical line, every reciprocal-square coordinate is positive real and at most `R`, hence
every pole lies in `[1,infinity)`.  Conversely, a pole in that ray has positive real reciprocal
coordinate; the formal reciprocal-square orientation equivalence then puts every zero in that
fibre on the critical line.  Because `(4)` prevents missing fibres, this proves `(7)` including
multiplicity.

For an off-ray pole, substitute `u=1/p` and
`C_u=-u Res_p M_R` into the diagonal coefficient from the exact reflected-kernel factorization:

\[
 \frac{|C_u|^2B(p)}{2\sqrt{|u|\,|1-u|}}
 =\frac{|\operatorname*{Res}_pM_R|^2(1+|p-1|)}
 {2|p|^2\sqrt{|p-1|}}.
\]

This is `(8)`.  The exact finite maximal-packet branch decomposition supplies the final
noncancellation statement.

## Top-down use

The open collar problem can now be stated entirely in source singularity language:

```text
prime--Gamma control of the paired diagonal forbids a half-order pinch
  -> no off-ray pole of the ordinary source moment germ can contribute its quantized residue
  -> every source pole lies on [1, infinity)
  -> RH.
```

The hard step is not locating or continuing the one-source poles: `(2)`--`(4)` do that exactly.
It is proving, from the independent prime--Gamma or theta expression, that the conjugate diagonal
pairing is single-valued meromorphic across the pole-pinch locus.  Any purported source theorem
must account for the positive coefficient `(8)` rather than merely continue `M_R` itself.

## Variable warning

The pole coordinate `v` is the ordinary moment variable.  The formal source is the even centered
germ, and locally

\[
 M_R(v)=
 \texttt{normalizedPrimeArchMomentGerm}\!\left(\sqrt{v/R}\right).
\]

Thus `p=1/u=R/c` is a pole in the `v`-plane, not in the centered Xi variable.  Evenness removes
the local square-root choice, but the two variables must not be conflated in a formalization.

## Formal parents

- `formal/GaloisForLFunctions/RHTower/PrimeArchCentralMomentGerm.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`
- `formal/GaloisForLFunctions/RHTower/XiRelativeResolventTrace.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPencil.lean`
- `formal/GaloisForLFunctions/RHTower/BernsteinEllipseRigidity.lean`

## Paper parents

- `prime-arch-bernstein-legendre-double-source-kernel.md`
- `prime-arch-bernstein-mobius-pullback-gutzmer-law.md`
- `prime-arch-bernstein-half-order-pringsheim-singularity.md`

## Gates

- [x] ordinary moment germ reduced to the reciprocal-coordinate resolvent
- [x] global meromorphic regrouping proved on paper
- [x] pole set and multiplicity residues proved exactly
- [x] functional-equation and Schwarz pole reflections proved exactly
- [x] pole-ray RH equivalence proved on paper
- [x] pole position and residue transferred to the exact half-order pinch coefficient
- [ ] Lean formalization
- [ ] independent source-side exclusion of half-order diagonal monodromy
- [ ] RH

## 2026-08-19 — unconditional Lean formalization (stage 3)

`formal/GaloisForLFunctions/RHTower/PrimeArchMomentPoleResidue.lean`.  Every displayed equation of
this card is Lean-proved; `#print axioms` on each capstone reports only
`propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| `m_n = normalizedPrimeArchMoment(n)/R^n`, eq. (1) | `endpointMoment` (`= radiusNormalizedMoment R normalizedPrimeArchMoment`) |
| `u_q = c_q/R` | `xiEndpointNormalizedReciprocalSquare` (pre-existing), `xiEndpointNormalizedReciprocalSquare_mul` |
| eq. (11) | `endpointMoment_eq_tsum` |
| the resolvent `∑_q c_q/(1-u_q v)` | `endpointResolvent`, `resolventTerm` |
| **eq. (2)** | `bernsteinMomentGerm_endpoint_eq_resolvent` |
| the fibre `{q : u_q = u}` and its finiteness | `endpointFibre`, `finite_endpointFibre` |
| **eq. (3)**, `C_u = R u m_u` | `reciprocalSquare_of_mem_fibre`, `tsum_reciprocalSquare_fibre` |
| the normal-convergence tail bounds | `finite_largeCoordinate`, `norm_resolventTerm_le`, `summable_resolventTerm_compl`, `norm_tsum_resolventTerm_compl_le` |
| **eq. (4)**, simple pole with residue `-R m_u` | `tendsto_endpointResolvent_residue` |
| `B(p) = (1+\|p-1\|)/\|p\|`, eq. (5) | `poleAmplitude`, `poleAmplitude_inv` |
| **eq. (6)**, triangle equality on the ray `[1,∞)` | `poleAmplitude_eq_one_iff` |
| **eq. (7)**, the pole-ray RH equivalence | `riemannHypothesis_iff_forall_reciprocalSquare_pos`, `riemannHypothesis_iff_forall_poleAmplitude_eq_one` |
| the positivity characterization behind (7) | `xiCentralReciprocalSquare_pos_iff` |
| **eq. (8)**, the half-order coefficient substitution | `halfOrderCoefficient_substitution` |
| **eq. (9)**, both reflections of the pole coordinate | `xiCentralReciprocalSquare_reflect`, `xiZeroCopyReciprocalSquare_reflectEquiv`, `endpointFibre_reflect_mem` |
| **eq. (10)**, Schwarz partners carry the same multiplicity and residue | `endpointFibre_conj`, `ncard_endpointFibre_conj` |
| variable warning: `M_R(v)` in the square-root coordinate | `bernsteinMomentGerm_primeArch` (in `RHTower/PrimeArchBernsteinMobiusPullbackSource.lean`) |

The residue statement is formalized as the exact limit
`(v - 1/u)·M_R(v) → -R·m_u` as `v → 1/u`, which is the residue of a simple pole and simultaneously
records that no other fibre contributes: the tail is split into a finite large-coordinate part
(continuous at the pole because `u_q ≠ u` there) and a uniformly bounded small-coordinate part.

## Gates

- [x] ordinary moment germ reduced to the reciprocal-coordinate resolvent
- [x] global meromorphic regrouping proved on paper
- [x] pole set and multiplicity residues proved exactly
- [x] functional-equation and Schwarz pole reflections proved exactly
- [x] pole-ray RH equivalence proved on paper
- [x] pole position and residue transferred to the exact half-order pinch coefficient
- [x] Lean formalization
- [ ] independent source-side exclusion of half-order diagonal monodromy  *(declared future research)*
- [ ] RH  *(declared future research)*
