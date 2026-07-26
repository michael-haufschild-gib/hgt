# Deninger Weil--Arakelov source resolvent

- **ID:** `deninger-weil-arakelov-source-resolvent`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** `deninger-weil-arakelov-dynamical-lift`
- **Novelty:** `[NEW SYNTHESIS]` explicit Xi-source specialization theorem

## Statement

Let
\[
  H^1_{\mathrm{src}}
  =
  \mathcal O(\mathbb C)/(\Xi_C)
\]
and let \(\Theta\) act by multiplication by
\(\frac12+iz\).  For \(\alpha\in\mathbb C\) with
\(\Xi_C(\alpha)\ne0\), define the divided-difference source
\[
  Q_\alpha(z)
  =
  -\Xi_C(\alpha)^{-1}
    \frac{\Xi_C(z)-\Xi_C(\alpha)}{z-\alpha}
\]
with its removable value at \(z=\alpha\), and put
\[
  R_\alpha=-i\, [Q_\alpha]\in H^1_{\mathrm{src}}.
\]
Then
\[
  \left(\Theta-\left(\frac12+i\alpha\right)\right)R_\alpha=1.
                                                               \tag{1}
\]
Consequently
\[
  \Theta-\left(\frac12+i\alpha\right):
  H^1_{\mathrm{src}}\longrightarrow H^1_{\mathrm{src}}
\]
is a linear equivalence.  Its kernel and cokernel vanish, so the middle part of the
Flach--Morin mapping-fiber specialization is acyclic away from the Xi divisor.

## Proof

The established source Bézout identity is
\[
  (z-\alpha)[Q_\alpha]=1
  \quad\text{in }\mathcal O(\mathbb C)/(\Xi_C).
\]
Also
\[
  \Theta-\left(\frac12+i\alpha\right)=i(z-\alpha).
\]
Multiplication by \(-i[Q_\alpha]\) therefore gives `(1)`, since
\(i(-i)=1\).  The quotient algebra is commutative, so the same element is a left inverse.

## Significance

This proves the exact spectral-support part of the proposed Weil--Arakelov comparison:
nontrivial middle mapping-fiber cohomology can occur only at the source-defined completed-Xi
divisor.  It is stronger than absence of eigenvectors because it proves surjectivity and gives
an explicit inverse.

It does not construct the rational-Witt/Milnor--Witt dynamical lift, Hodge positivity, or the
prime-orbit determinant.

## Formalization

- `[PAPER-PROVED]` Proof above.
- `[LEAN-PROVED]`
  `formal/GaloisForLFunctions/RHTower/DeningerArithmeticWeilArakelovResolvent.lean`.
- Direct verification command:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticWeilArakelovResolvent.lean`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration is present.
