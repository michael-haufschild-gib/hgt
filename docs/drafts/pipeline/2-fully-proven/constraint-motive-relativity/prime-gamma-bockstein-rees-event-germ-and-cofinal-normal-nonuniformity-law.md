# Prime Gamma--Bockstein/Rees event germ and cofinal normal nonuniformity law

- **ID:** `cmr-prime-gamma-bockstein-rees-event-germ-cofinal-normal-nonuniformity`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper) / SOURCE-SPECIFIC CROSS-CHART EVENT LAW
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [PRE-XI] [BRIDGE] [NOT RH]`
  `[FORMAL NORMALIZATION DISCONTINUITY FOUND] [NO LEAN WRITTEN OR BUILT]`
- **Formal parents:**
  `../../../../../formal/GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinDeterminantTransgression.lean`,
  `../../../../../formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldReesCoronaQuotient.lean`,
  `../../../../../formal/GaloisForLFunctions/RHTower/PrimeGammaBocksteinReesCoronaComparison.lean`.
- **Field successor:**
  `../../1-in-progress/constraint-motive-relativity/determinantal-constraint-holography-and-singular-reporter-correspondence-conjecture.md`.

## 1. Result in one sentence

At each prime, the Gamma determinant-transgression coordinate and adjacent-depth Rees normal
coordinate define the same analytic divisor germ under a canonical orientation-reversing
comparison; after removing the reflection-odd minus, the factor is positive. The comparison
constants tend to zero across primes, so local event charts do not glue through any uniformly
invertible unweighted diagonal comparison.

## 2. Two literal pre-divisor coordinates

Fix an ordinary prime `p` and put `L=log p`. The source-selected occupancy Fisher density is

\[
 F_p=\frac{p}{(p+1)^2}.
\tag{GBR.1}
\]

The signed reflected Gamma determinant transgression at real centered grade `t` is

\[
 \beta_p(t)=F_p(p^{-t}-p^t)=-2F_p\sinh(tL).
\tag{GBR.2}
\]

For the adjacent depth cells `(p,0)` and `(p,1)`, the BV masses and Wold--Gamma clocks are

\[
 m_0=1-p^{-1},\qquad m_1=(1-p^{-1})p^{-1},
 \qquad \lambda_0=L,\qquad\lambda_1=2L.
\tag{GBR.3}
\]

Their alternating connection coefficient is therefore

\[
 \theta_p=m_0\lambda_1-m_1\lambda_0
 =(1-p^{-1})L(2-p^{-1}).
\tag{GBR.4}
\]

The scalar weight of the clock-normalized Rees--corona quotient is

\[
 w_p(t)=\frac{t\theta_p}{\lambda_0\lambda_1}
 =\kappa_pt,
 \qquad
 \kappa_p=\frac{(1-p^{-1})(2-p^{-1})}{2L}>0.
\tag{GBR.5}
\]

The full quotient on a physical conormal `c` is `w_p(t)` times the realification of `c`. This
theorem computes its scalar normal law; it does not construct a pre-Xi nonzero physical conormal
or a structural Puiseux event.

All formulas precede Xi specialization. They use only the existing prime activation, Gamma
reflection, adjacent-depth BV mass, and Wold clock definitions.

## 3. Analytic event-germ comparison

Define

\[
 L_p:=\frac{4p^3(\log p)^2}
 {(p+1)^2(p-1)(2p-1)}>0
\tag{GBR.6}
\]

and the entire even function of real `t`

\[
 \widetilde g_p(t)
 :=L_p\frac{\sinh(t\log p)}{t\log p},
\tag{GBR.7}
\]

where the removable value at `t=0` is `L_p`.

### Theorem 3.1

For every real `t`,

\[
 \boxed{\beta_p(t)=-\widetilde g_p(t)w_p(t)}.
\tag{GBR.8}
\]

Moreover `g~_p(t)>0` for every real `t`; hence the two coordinates have the same zero and the same
vanishing order one at `t=0`. Their raw signed coorientations are opposite because of the displayed
minus sign; after removing that explicit reflection-odd sign, they agree through the positive
factor.

#### Proof

For `t!=0`, substitute `(GBR.2)` and `(GBR.5)`:

\[
 -\frac{\beta_p(t)}{w_p(t)}
 =\frac{2F_p\sinh(tL)}{\kappa_pt}
 =\frac{4p^3L^2}{(p+1)^2(p-1)(2p-1)}
   \frac{\sinh(tL)}{tL}
 =\widetilde g_p(t).
\]

Since `sinh x/x` has the entire even extension with value `1` at zero, this equality extends to
`t=0`. It is positive on the real axis. Since `beta'_p(0)=-2F_pL!=0` and
`w'_p(0)=kappa_p>0`, both zeros are simple. QED.

### Corollary 3.2 — exact event derivative

\[
 \beta'_p(0)=-L_pw'_p(0).
\tag{GBR.9}
\]

Thus the local comparison identifies transverse derivatives, not merely zero radicals.

## 4. Discontinuity in the existing formal normalization

The current formal change of coordinates is defined by the quotient `-beta_p(t)/w_p(t)` for
`t!=0`, but is assigned the value `1` at `t=0`. Theorem 3.1 proves that its unique continuous,
indeed real-analytic, event-germ extension has value `L_p`.

### Proposition 4.1

For `p=2`,

\[
 L_2=\frac{32(\log2)^2}{27}<\frac23\ne1.
\tag{GBR.10}
\]

Consequently the present piecewise formal factor is discontinuous at `t=0`.

#### Proof

Substitution in `(GBR.6)` gives the equality. To close the elementary bound, the exponential
series gives

\[
 e^{3/4}>1+\frac34+\frac{(3/4)^2}{2}=\frac{65}{32}>2,
\]

so `log 2<3/4`. Therefore

\[
 L_2<\frac{32(9/16)}{27}=\frac23.
\]

QED.

The existing zero-radical and pointwise nonvanishing theorems remain correct. What fails is the
interpretation of that particular normalization as a continuous transverse event-germ
identification.

No Lean file is edited here by instruction.

## 5. Cofinal normal nonuniformity

### Theorem 5.1

As `p -> infinity` through primes,

\[
 L_p\sim\frac{2(\log p)^2}{p},
 \qquad L_p\longrightarrow0.
\tag{GBR.11}
\]

#### Proof

Divide `(GBR.6)` by `2(log p)^2/p`:

\[
 \frac{L_p}{2(\log p)^2/p}
 =\frac{2p^4}{(p+1)^2(p-1)(2p-1)}\longrightarrow1.
\]

Since `(log p)^2/p ->0`, the second assertion follows. QED.

Let `D_L` be the diagonal map on prime-indexed sequences,

\[
 (D_Lx)_p=L_px_p.
\tag{GBR.12}
\]

### Corollary 5.2

`D_L` is bounded and injective on `ell^2(P)`, `c_0(P)`, and `ell^infty(P)`, but has no bounded
inverse on its range with the inherited norm. Its range is not closed on `ell^2(P)` or `c_0(P)`.

#### Proof

The positive sequence `(L_p)` is bounded and tends to zero, so coordinate multiplication is
bounded and injective. If an inverse on the range were bounded with norm `C`, then applying it to
`L_pe_p` would give

\[
 1=\|e_p\|\le C\|L_pe_p\|=CL_p,
\]

contradicting `L_p->0`. On `ell^2` and `c_0`, the vectors `L_pe_p` converge to zero while their
preimages are unit vectors. Equivalently, if the range were closed, the bounded inverse theorem
would make the inverse on that Banach range bounded, contradicting the preceding estimate. Hence
the range is not closed. QED.

For `ell^infty`, nonexistence of a bounded inverse is the claimed obstruction; no closed-range
statement is needed.

## 6. Meaning for the higher field

This theorem proves three nontrivial facts at once:

1. **Local equivalence:** Gamma determinant transgression and Rees normal response are genuinely
   the same primewise analytic event germ up to a positive factor and orientation sign.
2. **Cofinal singularity:** those local identifications cannot be assembled into a uniformly
   invertible unweighted all-prime chart.
3. **Topology is constitutive:** any global identification must choose source-derived weights,
   a pro/restricted-product topology, a nonclosed correspondence, or another singular completion.

This is not an RH selector. Both coordinates vanish at neutral grade by construction. The new
knowledge is why a primewise exact comparison becomes singular at the all-prime horizon.

## 7. Structural Stokes boundary

The arithmetic common scalar twist changes central determinant holonomy but leaves Puiseux
differences, contacts, coarea, Rees dimensions, capacities, and inertia unchanged. Hence `(GBR.8)`
does not produce a structural Puiseux-cluster split.

The companion paper theorem
`puiseux-cluster-split-one-port-lorentz-exchange-law.md` supplies an explicit countermodel: two
Puiseux configurations have the same central determinant exponent while their one-port gap and
negative index differ. Therefore no rule from common central twist alone to structural Stokes
crossing can exist.

A valid event theory must separate:

- central holonomy response;
- normal/Rees event response;
- structural contact/inertia response.

They may later be related by a source correspondence, but they are not interchangeable data.

## 8. Hostile conjecture loops

1. **The existing piecewise factor is a smooth event coordinate.** False by Proposition 4.1.
2. **Primewise nonzero comparison gives a bounded global equivalence.** False by Corollary 5.2.
3. **A common arithmetic scalar twist changes Stokes inertia.** False by the structural
   central-twist no-go.
4. **The singular global comparison proves criticality.** False; it occurs for the complete
   one-parameter grade family, not only for divisor points.
5. **Any chosen weights repair the field.** False as a source claim. Weights must be derived before
   target comparison, and must preserve coefficient reporters and aperture transitions.
6. **This is only another Route-R computation.** False as a theorem of scope: it compares two
   independently constructed organs—Gamma determinant transgression and Rees normal geometry—and
   derives a cofinal topological obstruction absent from either local chart alone. It still does
   not realize all corpus organs.

## 9. Formalization note

The ingredients are already formalized separately, including the pointwise quotient comparison.
The new paper result identifies the analytic removable value and the cofinal asymptotic. By user
instruction, no Lean code was written or built. Later formalization should introduce a new analytic
extension rather than silently change the old zero-radical coordinate.

## Gates

- [x] literal source formulas checked against formal definitions
- [x] analytic event-germ identity proved
- [x] derivative and coorientation proved
- [x] current normalization discontinuity proved
- [x] cofinal asymptotic proved
- [x] unweighted bounded-inverse obstruction proved
- [x] central-holonomy versus structural-contact boundary stated
- [x] RH/nonselection boundary stated
- [x] hostile independent audit
- [ ] Lean formalization deferred by instruction

## Log

- 2026-08-09 — derived by comparing the formal Gamma determinant transgression with the formal
  adjacent-depth Rees--corona coordinate. The removable event value and cofinal singularity were
  not recorded in either parent.
