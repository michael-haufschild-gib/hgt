# Monoid bialgebra, Hopf envelope, antipode defect, and one-sided representation law

- **ID:** ULF-BIALG-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** bialgebraic law-genesis fork
- **Statement:** The polynomial monoid bialgebra has no antipode, its Hopf envelope is Laurent localization, and a unilateral-shift representation becomes reversible only after quotienting its Toeplitz defect.
- **Status:** [PAPER-PROVED] [SINGLE-PRODUCER CALIBRATION] [CLASSICAL HOPF/TOEPLITZ PARENTS] [NO LEAN]

## 1. Algebraic setup

Let \(k\) be a field and put \(B=k[t]\). Define

\[
\Delta(t)=t\otimes t,
\qquad
\varepsilon(t)=1,
\tag{1}
\]

and extend \(\Delta\) and \(\varepsilon\) as algebra maps.

## 2. Theorem

1. \((B,\Delta,\varepsilon)\) is a commutative bialgebra.
2. It has no antipode.
3. The localization

   \[
   H=k[t,t^{-1}]
   \tag{2}
   \]

   is a Hopf algebra with \(S_H(t)=t^{-1}\).
4. The inclusion \(B\hookrightarrow H\) is universal among bialgebra maps from \(B\) to Hopf
   algebras: every such map factors uniquely through (2).
5. Algebraically, this is the passage from the positive monoid \(\mathbb N\) to its group
   completion \(\mathbb Z\).
6. Let \(V\) be the unilateral shift on \(\ell^2(\mathbb N_0)\). The representation

   \[
   \rho:B\to B(\ell^2(\mathbb N_0)),
   \qquad
   \rho(t)=V,
   \tag{3}
   \]

   does not extend to \(H\).
7. After passing to the Calkin/Toeplitz boundary, the image \(u=\pi(V)\) is unitary, so (3)
   extends uniquely to a representation of \(H\) with \(t^{-1}\mapsto u^*\).
8. The erased operator defect is

   \[
   1-VV^*=P_{e_0},
   \tag{4}
   \]

   and is invisible in the Hopf-envelope algebra (2).

### Proof

Coassociativity and counitality need only be checked on \(t\):

\[
(\Delta\otimes1)\Delta(t)=t\otimes t\otimes t=(1\otimes\Delta)\Delta(t),
\]

and both counit composites send \(t\) to \(t\). Since the maps are algebra maps, this proves the
bialgebra axioms.

If an antipode \(S_B\) existed, the antipode identity on \(t\) would give

\[
S_B(t)t=1=tS_B(t).
\]

Thus \(t\) would be invertible in \(k[t]\), contradiction. In the Laurent algebra it is invertible,
and \(t\mapsto t^{-1}\) satisfies the antipode identities.

Given a bialgebra map \(f:B\to K\) into a Hopf algebra, \(f(t)\) is group-like. Its inverse is
the antipode value \(S_K(f(t))\). The universal property of localization therefore extends \(f\)
uniquely through \(k[t,t^{-1}]\), proving the Hopf-envelope claim.

A representation of \(H\) must send \(t\) to an invertible operator. The unilateral shift is not
surjective and hence not invertible, proving nonextension of (3). In the Calkin quotient,

\[
\pi(V)^*\pi(V)=1,
\qquad
\pi(V)\pi(V)^*=\pi(1-P_{e_0})=1,
\]

so \(u=\pi(V)\) is unitary and defines the Laurent representation. Equation (4) is the standard
range defect and lies in the compact ideal killed by \(\pi\). QED.

## 3. Exact field lesson

One multiplication/comultiplication law produces:

- directed history through \(\mathbb N\);
- reversible observer history through \(\mathbb Z\);
- an algebraic antipode obstruction;
- one-sided positive operator realizations;
- a boundary quotient where the history becomes unitary.

But the Hopf envelope forgets the size and module structure of the operator defect. Therefore the
bialgebra alone is not a complete field primitive. A representation/fibre functor and its completion
are load-bearing, not optional decoration.

## 4. Hostile scope

- Hopf envelopes and universal quantum semigroups are established theory.
- The bialgebra does not select the unilateral-shift representation.
- Different representations of the same bialgebra have different positivity, defects, and topology.
- No hypertranscendence, proof cost, or arithmetic selector follows from the antipode obstruction.

## 5. External parent

Farinati, `Universal quantum (semi)groups and Hopf envelopes`, arXiv:2008.09937.

## Log

- 2026-08-09 — bialgebra single-producer test proved; representation dependence exposed.
