# Centered KSGNS covariance is canonical and composes by orthogonal Pythagoras

- **ID:** `centered-ksgns-covariance-pythagoras`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `source-generated-ternary-reciprocity-law.md`, hostile source-canonicity audit
- **Statement:** The weighted star-multiplicative defect of a completely positive map is the
  Gram kernel of the orthogonal complement of its normalized cyclic line in the minimal
  Paschke--KSGNS module; for successive unital maps, the centered vector of the composite
  splits orthogonally into transported earlier and later centered vectors.

## Claim status

`[PAPER-PROVED] [REDISCOVERED] [BRIDGE] [LEAN OPEN]`

This is not new scientific knowledge. Paschke--KSGNS existence and uniqueness, functoriality,
and GNS subproduct systems are established operator theory. The centered-complement formulas
below are direct consequences. Their value is a hostile correction: presentation invariance of
the covariance module is automatic once a completely positive event map and its codomain have
already been supplied.

## Theorem 1: canonical centered module

Let \(A,B\) be unital \(C^*\)-algebras and let \(\Phi:A\to B\) be completely positive. Let
\((E_\Phi,\pi_\Phi,\xi_\Phi)\) be its minimal Paschke--KSGNS correspondence:
\[
 \Phi(a)=\langle \xi_\Phi,\pi_\Phi(a)\xi_\Phi\rangle_B,\qquad
 E_\Phi=\overline{\operatorname{span}}\pi_\Phi(A)\xi_\Phi B .
\]
Write \(h=\Phi(1)=\langle\xi_\Phi,\xi_\Phi\rangle_B\), and assume \(h\) is invertible. Then
\[
 \eta_\Phi=\xi_\Phi h^{-1/2}
\]
is a unit vector and
\[
 P_\Phi=\theta_{\eta_\Phi,\eta_\Phi}
\]
is the adjointable orthogonal projection onto \(\xi_\Phi B\). Define
\[
 D_\Phi^h(x)
 =(1-P_\Phi)\pi_\Phi(x)\xi_\Phi
 =\pi_\Phi(x)\xi_\Phi-\xi_\Phi h^{-1}\Phi(x).
 \tag{1}
\]
Then
\[
 \boxed{
 \left\langle D_\Phi^h(x),D_\Phi^h(y)\right\rangle_B
 =\Phi(x^*y)-\Phi(x)^*h^{-1}\Phi(y)
 =\Gamma_\Phi^h(x,y).
 }
 \tag{2}
\]
Moreover,
\[
 L_\Phi^h
 :=\overline{\operatorname{span}}\{D_\Phi^h(x)b:x\in A,\ b\in B\}
 =(1-P_\Phi)E_\Phi
 \tag{3}
\]
is determined by \(\Phi\) up to the unique pointed unitary equivalence supplied by minimal
KSGNS uniqueness. It is therefore independent of Kraus coordinates and of the chosen minimal
Stinespring or KSGNS presentation.

### Proof

Since
\[
\langle\eta_\Phi,\eta_\Phi\rangle
=h^{-1/2}hh^{-1/2}=1,
\]
\(\theta_{\eta_\Phi,\eta_\Phi}\) is a self-adjoint idempotent. For every \(x\in A\),
\[
\begin{aligned}
P_\Phi\pi_\Phi(x)\xi_\Phi
&=\eta_\Phi
  \langle\eta_\Phi,\pi_\Phi(x)\xi_\Phi\rangle\\
&=\xi_\Phi h^{-1/2}h^{-1/2}\Phi(x)
 =\xi_\Phi h^{-1}\Phi(x),
\end{aligned}
\]
which proves (1). Expanding the inner product of the two differences in (1), the two cross
terms are both \(\Phi(x)^*h^{-1}\Phi(y)\), while the final term is
\[
\Phi(x)^*h^{-1}hh^{-1}\Phi(y)
=\Phi(x)^*h^{-1}\Phi(y).
\]
One copy therefore remains subtracted, proving (2). Minimality gives
\[
(1-P_\Phi)E_\Phi
=\overline{(1-P_\Phi)\pi_\Phi(A)\xi_\Phi B},
\]
which is (3). The final assertion follows from uniqueness of the minimal pointed KSGNS
correspondence. \(\square\)

For a unital map, \(h=1\) and
\[
D_\Phi(x)=\pi_\Phi(x)\xi_\Phi-\xi_\Phi\Phi(x),\qquad
\langle D_\Phi(x),D_\Phi(y)\rangle=\Gamma_\Phi(x,y).
\tag{4}
\]

## Theorem 2: orthogonal succession Pythagoras

Let
\[
A\xrightarrow{\Phi}B\xrightarrow{\Psi}C
\]
be unital completely positive maps. There is a canonical isometry of pointed
\(A\)-\(C\) correspondences
\[
V_{\Phi,\Psi}:E_{\Psi\Phi}\longrightarrow E_\Phi\otimes_B E_\Psi
\]
determined on the cyclic span by
\[
V_{\Phi,\Psi}\!\left(\pi_{\Psi\Phi}(a)\xi_{\Psi\Phi}c\right)
=\pi_\Phi(a)\xi_\Phi\otimes\xi_\Psi c.
\tag{5}
\]
For every \(x\in A\),
\[
\boxed{
V_{\Phi,\Psi}D_{\Psi\Phi}(x)
=D_\Phi(x)\otimes\xi_\Psi
 \xi_\Phi\otimes D_\Psi(\Phi(x)).
}
\tag{6}
\]
The two summands are orthogonal. Consequently,
\[
\boxed{
\Gamma_{\Psi\Phi}(x,y)
=\Psi\!\left(\Gamma_\Phi(x,y)\right)
 \Gamma_\Psi(\Phi(x),\Phi(y)).
}
\tag{7}
\]

### Proof

For cyclic generators, the inner product of the proposed right side of (5) is
\[
c^*\Psi\!\left(\Phi(a^*a')\right)c',
\]
which is the KSGNS inner product for \(\Psi\Phi\). Thus (5) extends isometrically.
Add and subtract \(\xi_\Phi\Phi(x)\otimes\xi_\Psi\), and use the balanced tensor relation
\[
\xi_\Phi\Phi(x)\otimes\xi_\Psi
=\xi_\Phi\otimes\pi_\Psi(\Phi(x))\xi_\Psi
\]
to obtain (6). Since
\[
\langle D_\Phi(x),\xi_\Phi\rangle_B=0,
\]
the two summands in (6) are orthogonal. Their two Gram kernels are respectively
\(\Psi(\Gamma_\Phi(x,y))\) and \(\Gamma_\Psi(\Phi(x),\Phi(y))\), proving (7).
\(\square\)

## Weighted succession

Let \(h=\Phi(1)\) and \(k=\Psi(h)\) be invertible. Normalize
\[
\widehat\Phi(a)=h^{-1/2}\Phi(a)h^{-1/2},
\qquad
\widehat\Psi_h(b)
=k^{-1/2}\Psi(h^{1/2}bh^{1/2})k^{-1/2}.
\]
Both maps are unital and
\[
\widehat\Psi_h\widehat\Phi(a)
=k^{-1/2}\Psi(\Phi(a))k^{-1/2}.
\]
Applying Theorem 2 and conjugating by \(h^{1/2}\) and \(k^{1/2}\) gives
\[
\Gamma_{\Psi\Phi}^{k}(x,y)
=\Psi\!\left(\Gamma_\Phi^{h}(x,y)\right)
 \Gamma_\Psi^{k\mid h}(\Phi(x),\Phi(y)),
\tag{8}
\]
where
\[
\Gamma_\Psi^{k\mid h}(b,c)
=\Psi(b^*h^{-1}c)-\Psi(b)^*k^{-1}\Psi(c).
\]
Thus the algebraic weighted chain law already formalized in
`HTGeometry.StarMultiplicativeDefectChain` is the decategorified Gram identity of an
orthogonal decomposition after order-unit normalization.

## Literature boundary

- W. L. Paschke, *Inner product modules over \(B^*\)-algebras*,
  [doi:10.1090/S0002-9947-1973-0355613-0](https://doi.org/10.1090/S0002-9947-1973-0355613-0).
- A. Westerbaan and B. Westerbaan, *Paschke dilations*,
  [arXiv:1603.04353](https://arxiv.org/abs/1603.04353).
- O. Shalit and M. Skeide, *CP-semigroups and dilations, subproduct systems and superproduct
  systems*, [arXiv:2003.05166](https://arxiv.org/abs/2003.05166).
- K. A. Brix, A. Mundey, and A. Rennie, *Morphisms of Cuntz--Pimsner algebras from
  completely positive maps*, [arXiv:2311.16600](https://arxiv.org/abs/2311.16600).
- L. Brady and R. Grady, *Functoriality of the KSGNS construction for intertwiners of strict
  positive \(C^*\)-correspondences*,
  [arXiv:2605.08004](https://arxiv.org/abs/2605.08004).

These sources establish the parent constructions, uniqueness, composition, subproduct systems,
and current functoriality frontier. The centered formulas do not establish physical source
selection.

## Hostile verdict and positive survivor

- **Killed claim:** Presentation invariance of a covariance correspondence for a supplied CP
  event map is candidate-new mathematics.
- **Verdict:** `REDISCOVERED`.
- **Exact why:** Minimal pointed KSGNS already canonically removes dilation and Kraus
  presentation choices; its centered complement has exactly the weighted covariance Gram
  kernel.
- **Strongest positive survivor:** The weighted chain law has an exact orthogonal
  correspondence-level Pythagorean realization.
- **New insight:** Covariance can reconstruct the rejected part of a supplied event, but cannot
  generate the event map, its codomain, or its physical equivalence relation. Source generation
  lies strictly upstream of KSGNS.
- **Lean status:** Equation (8)'s algebraic shadow is `[LEAN-PROVED]` as
  `weightedStarMultiplicativeDefect_comp`. The KSGNS construction, pointed uniqueness, and
  correspondence isometry (5) are not formalized in this corpus. Formalizing only the expansion
  (2) would not certify the canonicity claim.

## Gates

- [x] 0 → 1 in-progress: exact statement and collision isolated
- [x] 1 → 2 fully-proven: dependency-closed proof above
- [ ] 2 → 3 formalized: exact KSGNS construction, uniqueness, and orthogonal isometry
- [ ] 3 → 4 publication-ready: excluded; parent bridge, not standalone scientific discovery

## Log

- 2026-07-30 — proved centered weighted covariance formula and composition Pythagoras on paper;
  hostile audit classified source-canonicity for a supplied CP map as rediscovered KSGNS
  structure.
