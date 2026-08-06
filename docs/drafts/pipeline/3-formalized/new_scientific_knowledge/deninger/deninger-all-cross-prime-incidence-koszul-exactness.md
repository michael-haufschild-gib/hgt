# Deninger all-cross-prime incidence Koszul exactness

**Route:** L — Deninger/Hodge/cohomological realization  
**Stage:** 3 — formalised in Lean 4  
**Date:** 2026-08-03

## Frontier correction

The completed Calderón--Witt comparison previously constructed for one
ordered pair of distinct primes is coefficient-faithful, but its source
value at every Xi-divisor coordinate is a scalar multiple of one fixed
Milnor-incidence witness.  It is therefore only a rank-one packet line.  It
cannot by itself carry the genuinely off-diagonal prime-packet differential
required by the updated Hellinger--Hodge--Green descent paper.

The missing carrier is the simultaneous completion over **all** ordered
cross-prime incidences.  This note constructs it and computes its canonical
Koszul differential exactly.

## Construction

Let

\[
 I=\{(p,q):p,q\text{ prime},\ p\ne q\}
\]

and let \(w_{p,q}\) be the nonzero ordered Calderón--Witt cross-prime
Milnor-incidence witness already constructed in the algebraic source.  Choose
the canonical full-support square-summable packet horizon

\[
 \eta_i=c\,2^{-(\operatorname{enc}(i)+1)},\qquad
 c=\left\|\bigl(2^{-(\operatorname{enc}(i)+1)}\bigr)_{i\in I}\right\|_2^{-1}.
\]

Thus \(\eta\in\ell^2(I)\), \(\|\eta\|_2=1\), and
\(\eta_i\ne0\) for every \(i\in I\).  Put

\[
 \mathcal P=\ell^2\!\left(\operatorname{Div}(\Xi);\ell^2(I)\right).
\]

For \(x\in\ell^2(\operatorname{Div}(\Xi))\), define

\[
       (\Phi_{\mathrm{CW}}x)(r)_i=x(r)\eta_i.
\tag{1}
\]

The actual algebraic source value of coordinate \((r,i)\) is

\[
       x(r)\eta_i\,w_i.
\tag{2}
\]

Consequently every ordered cross-prime witness occurs with nonzero
coefficient whenever \(x(r)\ne0\); no prime-pair provenance is discarded.

Since \(\|\eta\|_2=1\), Tonelli gives

\[
             \|\Phi_{\mathrm{CW}}x\|_{\mathcal P}=\|x\|_2.
\tag{3}
\]

Hence \(\Phi_{\mathrm{CW}}\) is an isometry and its range is closed.

## Canonical packet differential

Fix the source base pair \(i_0=(2,3)\).  On a packet
\(z\in\ell^2(I)\), define

\[
   (\partial_\eta z)_i
     =\eta_{i_0}z_i-\eta_i z_{i_0}.
\tag{4}
\]

This is a bounded linear operator: it is the difference of scalar
multiplication by \(\eta_{i_0}\) and the rank-one operator
\(z\mapsto z_{i_0}\eta\).  Apply it fibrewise to obtain the completed
all-divisor packet differential

\[
   (\Delta_\eta Z)(r)=\partial_\eta(Z(r)).
\tag{5}
\]

## Theorem (all-cross-prime incidence Koszul exactness)

Unconditionally,

\[
 \Delta_\eta\Phi_{\mathrm{CW}}=0,
 \qquad
 \ker\partial_\eta=\mathbb C\eta,
 \qquad
 \ker\Delta_\eta=\operatorname{ran}\Phi_{\mathrm{CW}}.
\tag{6}
\]

In particular, the completed Xi Green vector mapped into the genuine
all-cross-prime Calderón--Witt incidence completion lies in the kernel of an
explicit source packet differential.

### Proof

For (1), substitute \(z=x(r)\eta\) in (4):

\[
 \eta_{i_0}x(r)\eta_i-\eta_i x(r)\eta_{i_0}=0.
\]

If \(\partial_\eta z=0\), then for every \(i\)

\[
 \eta_{i_0}z_i=\eta_i z_{i_0}.
\]

Since \(\eta_{i_0}\ne0\),

\[
 z_i=(z_{i_0}/\eta_{i_0})\eta_i,
\]

so \(z\in\mathbb C\eta\).  The converse was proved in the first
calculation.  Applying this pointwise to (5), define

\[
 x(r)=Z(r)_{i_0}/\eta_{i_0}.
\]

Coordinate evaluation on \(\ell^2(I)\) is contractive, so

\[
 |x(r)|\le |\eta_{i_0}|^{-1}\|Z(r)\|_2;
\]

hence \(x\in\ell^2(\operatorname{Div}(\Xi))\).  The fibre classification
then gives \(Z=\Phi_{\mathrm{CW}}x\).  This proves the last equality in (6).
The reverse inclusion follows from the first identity. ∎

## What this changes

This closes a real infrastructure gap: Route L now has a simultaneous,
full-support, completed cross-prime incidence carrier and an unconditional
packet-valued differential annihilating the actual completed Green
comparison.

It does **not** prove RH.  Exactness shows why: the kernel of the canonical
packet-compatibility differential is the entire coefficient-bearing Xi
line, not zero.  Pairwise incidence compatibility removes all transverse
prime-packet variation but leaves the scalar Green coefficient untouched.
Therefore no differential generated only by relations (4) can satisfy the
conservativity clause of equation (7.17i).

The remaining hard object is now strictly smaller and uniquely typed: an
additional arithmetic differential on the residual line
\(\mathbb C\eta\), retaining Tate--Milnor/source orientation, whose kernel
on the actual Green sector is zero and whose annihilation of the actual
Green coefficient follows from a source identity independent of critical-line
displacement.

## Hostile audit

- **Not the fixed-pair comparison:** every pair is present simultaneously
  and every horizon coordinate is nonzero.
- **Not scalar trace:** differential is vector-valued and compares ordered
  pair coordinates before scalarization.
- **Not an exact-quotient erasure:** kernel is classified before quotient;
  surviving coefficient line is retained explicitly.
- **Not RH in disguise:** annihilation holds for every Xi coefficient
  vector, and exact kernel computation records resulting lack of
  conservativity.
- **No target-selected zero:** horizon depends only on countable source
  index, never on Xi-zero locations or displacement.

## Novelty audit against local corpus

Existing modules supplied one fixed cross-prime completion, algebraic
all-prime Milnor incidence, packet-grading transport, and exact lower Koszul
degrees.  Corpus search found no simultaneous Hilbert completion over all
ordered cross-prime witnesses, no full-support packet horizon, and no exact
kernel classification for the completed pair-compatibility differential.
The theorem is therefore new relative to the project corpus.  Its novelty
is the exact completed packet resolution and the resulting sharp residual
frontier, not a claim of RH closure.

## Formalization target

```text
formal/GaloisForLFunctions/RHTower/
DeningerCalderonWittAllCrossPrimeIncidenceKoszul.lean
```

Required capstones:

```text
deningerCalderonWittCrossPrimePacketHorizon_norm
deningerCalderonWittCrossPrimePacketHorizon_apply_ne_zero
deningerCalderonWittAllCrossPrimeXiIncidenceComparison
deningerCalderonWittPacketKoszulDifferential
deningerCalderonWittPacketKoszulDifferential_comparison
ker_deningerCalderonWittPacketKoszulDifferential
ker_deningerCalderonWittGlobalPacketKoszulDifferential
```

## Formalization status

Completed unconditionally in the target module.  The formal development
also constructs the continuous actual completed Green map into the
all-cross-prime carrier and proves it is killed by the global packet Koszul
differential.  Local and global kernel equalities, residual coefficient
retraction, full-support horizon, and norm preservation are all checked.

Formalized card:

```text
docs/drafts/pipeline/3-formalized/
deninger-all-cross-prime-incidence-koszul-exactness.md
```

## Strengthening: arithmetic coordinate separation

The simultaneous packet is not merely a formal copy of the ordered prime
pairs.  Let

\[
  \lambda_{p,q}:\mathcal I_{\mathrm{CW}}\longrightarrow\mathbb C
\]

be the normalized Gamma--modular incidence coordinate and let
\(w_{r,s}\) be the actual cross-prime Calderón--Witt witness.  Then

\[
 \boxed{\lambda_{p,q}(w_{r,s})
   =\begin{cases}1,&(p,q)=(r,s),\\0,&(p,q)\ne(r,s).
     \end{cases}}
\tag{7}
\]

Indeed, the unnormalized exterior evaluation is

\[
 c_{p,q}\bigl(D_p(v_0)Q_q(v_1)-D_p(v_1)Q_q(v_0)\bigr),
\]

where \(D_p\) is the defect coordinate and \(Q_q\) is the packet first
mode.  On \(w_{r,s}=\iota_r(d_r)\wedge\iota_s(u_s)\), the mixed legs
vanish, the first remaining factor vanishes unless \(p=r\), and the second
vanishes unless \(q=s\).  In the matching case both unit coordinates are
one and normalization by the nonzero \(c_{p,q}\) gives one.  Notice that
\(w_{q,p}\) is killed by \(\lambda_{p,q}\): the two orientations are
genuinely separated, not duplicate labels.

Consequently the finite source realization

\[
  W:\mathbb C^{(I)}\longrightarrow\mathcal I_{\mathrm{CW}},
  \qquad W(a)=\sum_{i\in I}a_iw_i
\]

has the explicit left inverse \(a\mapsto(\lambda_i(W(a)))_i\).  Therefore

\[
       \lambda_i(W(a))=a_i,\qquad W\text{ is injective},\qquad
       (w_i)_{i\in I}\text{ is linearly independent}.
\tag{8}
\]

This removes the main hostile alternative to the all-pair construction:
its transverse directions are forced by actual source arithmetic.  The
claim is algebraic; no unproved Hilbert topology on the Milnor-incidence
submodule is smuggled into (8).  It strengthens source provenance but does
not alter the exact residual obstruction \(\mathbb C\eta\).

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
