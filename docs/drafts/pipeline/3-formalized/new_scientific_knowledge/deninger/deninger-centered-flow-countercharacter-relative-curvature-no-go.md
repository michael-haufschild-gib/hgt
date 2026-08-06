# Deninger centered-flow countercharacter erasure and relative curvature

- **Stage:** 3-formalized

- **ID:** `deninger-centered-flow-countercharacter-relative-curvature-no-go`
- **Route:** L — Deninger/Hodge/cohomological realization
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-03
- **Exact claim:** the canonical centered-flow source countercharacter is the inverse of the
  Deninger half-density mate gain at every integer clock.  Absolute covariant normalization
  therefore flattens the one-sided framed transport at every spectral parameter, while the
  source/reflection polarization of the **relative** raw-to-flat curvature is exactly the
  Deninger tensor-square mate curvature and hence the actual ordered `(2,3)` Gamma boundary.

## 1. Frontier and failed conjecture

Write

\[
 \delta(s)=2\operatorname{Re}s-1,
 \qquad
 \chi_s(n)=\exp\!\bigl(\delta(s)\log n\bigr).
\tag{1}
\]

The previously constructed one-sided framed transport is

\[
 T_s(n)=
 \begin{pmatrix}
  \chi_s(n)n&\chi_s(n)(n-1)\\
  0&1
 \end{pmatrix}.
\tag{2}
\]

Its composition curvature is nonflat, and source/reflection polarization of its reduced
curvature is the Deninger mate detector

\[
 K_n(s)=\chi_s(n)-\chi_s(n)^{-1}.
\tag{3}
\]

The centered-flow construction supplies the canonical source countercharacter

\[
 c_s(n)=
 \exp\!\bigl(E(s)\log n\bigr),
 \qquad
 E(s)=\operatorname{Ent}_{\rm src}(s)=1-2\operatorname{Re}s.
\tag{4}
\]

The live conjecture was:

> `[CONJECTURE — COVARIANT_COUNTERCHARACTER_STOKES_ANNIHILATION]`  The source-normal
> centered-flow countercharacter supplies the singular Stokes normalization that annihilates
> the Deninger curvature while retaining the actual Gamma/Green class.

The conjecture is false.  The countercharacter annihilates the curvature for **every** spectral
parameter, not only at Xi divisor points on the critical line.  It therefore erases the detector
instead of proving its arithmetic vanishing.

## 2. Exact theorem

### Theorem (countercharacter erasure and relative mate recovery)

For every (s\in\mathbb C) and (n\in\mathbb N), define (\chi_s(n)) and (c_s(n)) by
`(1)` and `(4)`.  Let

\[
 \widetilde\chi_s(n)=c_s(n)\chi_s(n)
\tag{5}
\]

and let (A_n) be the flat top-conormal affine transport

\[
 A_n=
 \begin{pmatrix}n&n-1\\0&1\end{pmatrix}.
\tag{6}
\]

Then:

1. **Exact inverse character**
   \[
   c_s(n)=\chi_s(n)^{-1},
   \qquad
   \widetilde\chi_s(n)=1.
   \tag{7}
   \]

2. **Absolute curvature erasure**
   \[
   T_{\widetilde\chi_s}(n)=A_n,
   \qquad
   F_{\widetilde\chi_s}(m,n)=0
   \quad(m,n\in\mathbb N).
   \tag{8}
   \]

3. Let (f_\eta(n)=1-\eta(n)) be reduced one-sided curvature and define the relative
   raw-to-flat class
   \[
   R_s(n)=f_{\chi_s}(n)-f_{\widetilde\chi_s}(n).
   \tag{9}
   \]
   Then
   \[
   R_s(n)=1-\chi_s(n).
   \tag{10}
   \]

4. Critical reflection (s^\#=1-\overline s) exchanges the two characters:
   \[
   \chi_{s^\#}(n)=\chi_s(n)^{-1},
   \qquad
   c_{s^\#}(n)=c_s(n)^{-1}.
   \tag{11}
   \]
   Consequently the reflected relative polarization is
   \[
   R_{s^\#}(n)-R_s(n)
   =\chi_s(n)-\chi_s(n)^{-1}
   =K_n(s).
   \tag{12}
   \]

5. For every actual Xi divisor copy (q), the ordered `(2,3)`
   Gamma/Calderón--Witt boundary coefficient satisfies
   \[
   b_\Gamma(q)
   =c_{23}\bigl(R_{\rho_q^\#}(6)-R_{\rho_q}(6)\bigr),
   \qquad c_{23}>0.
   \tag{13}
   \]
   If (\operatorname{Re}\rho_q\ne\tfrac12), both absolute countertransported framed
   curvatures in `(8)` are zero while (b_\Gamma(q)\ne0).

Hence no arithmetic observation factoring only through the absolutely countertransported
curvature can be coefficient-faithful on the actual Gamma class.  The detector survives only as
the relative raw-to-flat class `(9)` before the covariant quotient.

## 3. Proof

The source entropy identity already proved in the corpus is

\[
 E(s)=1-2\operatorname{Re}s=-\delta(s).
\tag{14}
\]

Substitution in `(4)` gives

\[
 c_s(n)=\exp(-\delta(s)\log n).
\]

The exponential inverse law and `(1)` prove `(7)` without any restriction on (n).  In
particular the countertransported gain in `(5)` is the constant character one.

Substituting this constant character in the one-sided transport `(2)` gives (A_n).  The affine
top-conormal composition law

\[
 A_mA_n=A_{mn}
\tag{15}
\]

therefore proves `(8)`.

By definition,

\[
 f_{\widetilde\chi_s}(n)=1-1=0.
\]

Thus `(9)` is (1-\chi_s(n)), proving `(10)`.

Because

\[
 \delta(1-\overline s)=-\delta(s),
 \qquad
 E(1-\overline s)=-E(s),
\]

the exponential inverse law proves `(11)`.  Applying `(10)` at (s^\#) and at (s) gives

\[
 R_{s^\#}(n)-R_s(n)
 =(1-\chi_s(n)^{-1})-(1-\chi_s(n))
 =\chi_s(n)-\chi_s(n)^{-1},
\]

which is `(12)`.

The already proved Deninger/Gamma identification is

\[
 b_\Gamma(q)=c_{23}K_6(\rho_q),\qquad c_{23}>0.
\tag{16}
\]

Combining `(12)` with `(16)` proves `(13)`.  The exact zero-set theorem for the same actual
Gamma coefficient gives

\[
 b_\Gamma(q)=0
 \quad\Longleftrightarrow\quad
 \operatorname{Re}\rho_q=\tfrac12.
\tag{17}
\]

Therefore an off-line divisor fibre has nonzero Gamma coefficient even though `(8)` has erased
both absolute countertransported curvatures.  A factorization through those absolute curvatures
maps that nonzero coefficient to zero and cannot be coefficient-faithful.  This completes the
proof.

## 4. Hostile audit

1. **Not RH.**  The theorem proves that one natural Stokes normalization is unusable.  It does
   not annihilate the relative class `(12)`.
2. **No hidden use of a zero equation.**  Equations `(7)`--`(12)` hold for every complex
   parameter.  Xi enters only in the already constructed actual Gamma specialization `(13)`.
3. **No positive-conservation shortcut.**  Covariant conservation is precisely the mechanism
   that erases the curvature.  Treating the resulting flat absolute transport as a static
   positive Hodge metric would discard the detector.
4. **No cyclicity shortcut.**  Twisted/paracyclic theory permits a modular character to absorb
   monodromy.  Absolute cyclicity after countertransport therefore does not imply that the raw
   character is unitary.
5. **No scalar rebranding.**  The mathematical delta is the cross-identification of two
   independently constructed source objects—the centered-flow countercharacter and Deninger mate
   gain—and the consequent localization of the actual Gamma class in their relative mapping
   cone.
6. **Coefficient faithfulness is tested on an actual object.**  Off-line nonfaithfulness uses the
   literal ordered `(2,3)` Gamma/Calderón--Witt coefficient and its proved exact zero set, not an
   abstract nonzero vector.

Verdict on the failed conjecture: **FALSE**.

Verdict on the theorem: **SURVIVES PRELIMINARY ATTACK** as a source-specific no-go and relative
classification.  External priority remains unverified.

## 5. Literature boundary

Paracyclic modules and their conversion to cyclic objects are established parent mathematics:

- E. Getzler and J. D. S. Jones, [*The cyclic homology of crossed product
  algebras*](https://eudml.org/doc/153579), J. reine angew. Math. 445 (1993), 161--174.
- A. Connes and H. Moscovici, [*Cyclic Cohomology, Hopf Algebras and the Modular
  Theory*](https://arxiv.org/abs/math/9905013), Lett. Math. Phys. 48 (1999), 97--108.
- R. Ponge, [*Periodicity and cyclic homology. Para-S-modules and perturbation
  lemmas*](https://doi.org/10.4171/JNCG/393), J. Noncommut. Geom. 14 (2020), 1365--1444.

Modular Fredholm modules and KMS-weight representatives of twisted cyclic cocycles are also prior
art:

- A. Rennie, A. Sitarz, and M. Yamashita, [*Twisted Cyclic Cohomology and Modular Fredholm
  Modules*](https://arxiv.org/abs/1111.6328), SIGMA 9 (2013), 051.

Deninger's cohomological program and Burnol's co-Poisson/Sonine systems are the arithmetic parent
directions:

- C. Deninger, [*Some analogies between number theory and dynamical systems on foliated
  spaces*](https://doi.org/10.4171/DMS/1-1/2), Doc. Math. Extra Vol. ICM (1998), 23--46.
- J.-F. Burnol, [*Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*](https://doi.org/10.5802/jtnb.434), J. Théor. Nombres Bordeaux 16 (2004), 65--94.

These sources explain modular absorption, paracyclic defects, Deninger positivity, and
co-Poisson/Sonine completeness separately.  The exact identity between the HGT centered-flow
countercharacter and the inverse framed Deninger mate gain, together with the relative recovery
of the actual ordered Gamma coefficient, was not found in the targeted search.  That is collision
evidence, not a priority proof.

## 6. Positive survivor and exact remaining core

The failed absolute-normalization conjecture supplies a nontrivial positive survivor:

> `[PAPER-PROVED]` The actual Gamma mate detector is the polarization of a **relative
> raw-to-covariantly-flat curvature class**.  It is necessarily erased by absolute centered-flow
> normalization and must be retained before that quotient.

This changes the Route-L construction target.  A surviving singular Stokes object must be a
relative or mapping-cone theory containing all three pieces simultaneously:

1. raw one-sided framed transport (T_s);
2. canonical centered-flow countercharacter (c_s);
3. the gauge-trivialization morphism between (T_s) and the flat affine transport.

It must pair a source-derived relative cyclic/Stokes cocycle with `(12)`, prove arithmetic
annihilation there, and retain completed Xi Green provenance.  An absolute cyclic cocycle on the
countertransported complex is now excluded.

`[OPEN CORE — RELATIVE_COUNTERCHARACTER_STOKES_ANNIHILATION]`

Construct the literal preclosure relative exact couple for the raw/countertransported pair, land
its relative Bockstein coefficient-faithfully in completed Xi Green incidence before diagonal
sewing, and prove an arithmetic source boundary law annihilating the polarized relative class
`(12)` without assuming (K_6(\rho)=0), source-countercharacter triviality, static capacity, or
RH.


- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
