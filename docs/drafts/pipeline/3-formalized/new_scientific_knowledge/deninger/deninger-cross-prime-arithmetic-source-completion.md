# Deninger cross-prime arithmetic source completion

**Stage:** 3 — formalised in Lean 4  
**Date:** 2026-08-03

## Problem

The all-cross-prime Route-L carrier is

\[
  \mathcal P=\ell^2(I),\qquad
  I=\{(p,q):p,q\text{ prime},\ p\ne q\}.
\]

Although each coordinate decoded to an actual Calderón--Witt
Milnor-incidence witness, that alone did not prove that the Hilbert packet
was the completion of a concrete source object.  Distinct labels could in
principle have represented dependent source relations.  A second possible
failure was to reuse the existing oriented boundary as the residual
Route-L differential without checking its continuous extension.

## Actual source coordinates

Let \(w_i\) be the actual cross-prime Gamma witness and \(\lambda_i\) its
normalized Gamma--modular incidence coordinate.  The coordinate-separation
theorem gives

\[
                 \lambda_i(w_j)=\delta_{ij}.
\tag{1}
\]

Hence the source realization

\[
 W:\mathbb C^{(I)}\longrightarrow\mathcal I_{\rm CW},
 \qquad W(a)=\sum_i a_iw_i
\tag{2}
\]

is injective and \((w_i)_{i\in I}\) is linearly independent.

Define the concrete algebraic source

\[
             \mathcal S_{\rm CW}=\operatorname{span}\{w_i:i\in I\}.
\tag{3}
\]

## Theorem 1 (source completion presentation)

There is a canonical linear equivalence

\[
       \mathbb C^{(I)}\simeq\mathcal S_{\rm CW}
\tag{4}
\]

sending the standard basis vector \(e_i\) to \(w_i\).  Under this
equivalence, the coefficient realization

\[
 j:\mathcal S_{\rm CW}\longrightarrow\ell^2(I),
 \qquad j(W(a))=(a_i)_i
\tag{5}
\]

is injective and has dense range.

### Proof

Equation (1) is a left inverse for (2), so (2) is injective.  Its range is
exactly (3), yielding (4).  Formula (5) is injective because coordinate
equality recovers every finite coefficient.  Its range is the finite-support
subspace of \(\ell^2(I)\), whose standard coordinate vectors form a total
Hilbert basis.  Therefore the range is dense. ∎

Thus \(\ell^2(I)\) is a genuine Hilbert completion presentation of the
actual cross-prime source span with its coefficient norm.  No topology on
the ambient algebraic Milnor-incidence module is assumed.

## Theorem 2 (continuous oriented-boundary extension no-go)

Let

\[
 d_1:\bigwedge^2 V_{\rm CW}\longrightarrow A^2_{\rm CW}\times\mathbb C
\]

be the already constructed all-prime oriented source boundary.  Then

\[
                   d_1|_{\mathcal S_{\rm CW}}=0.
\tag{6}
\]

More generally, let \(Y\) be a normed complex space,
\(F:A^2_{\rm CW}\times\mathbb C\to Y\) linear, and
\(B:\ell^2(I)\to Y\) continuous linear.  If

\[
                 B(jx)=F(d_1x)qquad(x\in\mathcal S_{\rm CW}),
\tag{7}
\]

then \(B=0\).

### Proof

The exact oriented source complex has

\[
       \ker d_1=\mathcal I_{\rm CW}.
\]

Every generator \(w_i\), hence all of \(\mathcal S_{\rm CW}\), lies in
the Milnor-incidence subspace, proving (6).  Equations (6)--(7) show that
\(B\) vanishes on \(j(\mathcal S_{\rm CW})\).  This range is dense by
Theorem 1, and a continuous linear map vanishing on a dense subspace is
zero. ∎

## Scientific consequence

This is a strict interface theorem.  The existing one-dimensional top
orientation line does not act on the residual cross-prime coefficient by
continuous extension: its boundary is already zero on the entire dense
arithmetic core.  Reusing that boundary would produce the zero operator,
hence cannot satisfy Route-L conservativity.

Deninger's remaining unique contribution must therefore be a **new
horizontal relative transgression**.  It must compare source data across Xi
divisor/reflection fibres, rather than extend the vertical algebraic
Calderón--Witt boundary.  Its restriction to the dense source core must not
be the old \(d_1\), even though its value on the actual completed Green
primitive must vanish by an arithmetic source identity.

## Hostile audit

- Source object is actual span of constructed Milnor-incidence witnesses.
- Injectivity follows from actual Gamma--modular coordinates, not labels.
- Density is proved from the standard Hilbert basis.
- No ambient incidence norm or unproved completion theorem is assumed.
- No-go applies only to continuous extensions agreeing with old boundary on
  the source core; it does not rule out new relative/horizontal transport.
- Result does not prove RH and does not insert annihilation as a premise.

## Formalization

```text
formal/GaloisForLFunctions/RHTower/
DeningerCalderonWittAllCrossPrimeArithmeticSourceCompletion.lean
```

Formalized card:

```text
docs/drafts/pipeline/3-formalized/
deninger-cross-prime-arithmetic-source-completion.md
```

- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
