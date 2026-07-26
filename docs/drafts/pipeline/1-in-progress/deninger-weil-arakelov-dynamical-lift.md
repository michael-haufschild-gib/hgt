# Deninger dynamical lift of Milnor--Witt Weil--Arakelov cohomology

- **ID:** `deninger-weil-arakelov-dynamical-lift`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** `deninger-rost-schmid-flow-realization`
- **Scope:** direct construction of \(R\alpha_*\mathscr G\) and \(\Theta\)

## Literature boundary

For a proper regular arithmetic scheme \(X\), Flach--Morin define motivic cohomology with
compact support as the mapping fiber of the Beilinson regulator
\[
  R\Gamma_c(X,\mathbb R(n))
  =
  \operatorname{Fib}\!\left(
    R\Gamma(X,\mathbb R(n))
      \longrightarrow
    R\Gamma_D(X/\mathbb R,\mathbb R(n))
  \right).
                                                        \tag{1}
\]
Their Weil--Arakelov complex is
\[
  R\Gamma_{\mathrm{ar},c}(X,\widetilde{\mathbb R}(n))
  =
  R\Gamma_c(X,\mathbb R(n))
    \oplus
  R\Gamma_c(X,\mathbb R(n))[-1],                       \tag{2}
\]
with the acyclic cup-\(\theta\) map from the first summand to the shifted summand.

Their Conjecture 4.1 gives the exact missing bridge to Deninger's theory:
\[
  R\Gamma_{\mathrm{ar},c}(X,\widetilde{\mathbb C}(n))
  \simeq
  \operatorname{Fib}\!\left(
    \Theta-n:R\Gamma_{\mathrm{dyn},c}(X)
      \longrightarrow R\Gamma_{\mathrm{dyn},c}(X)
  \right).                                             \tag{3}
\]
They prove `(3)` for smooth projective varieties over finite fields under finite generation of
Weil--étale cohomology.  For number rings, the motivic/Deligne pairing needed on the
Weil--Arakelov side is known in dimension at most one, but the dynamical lift remains open.

Kolderup--Röndigs--Østvær provide the arithmetic Milnor--Witt spectrum
\[
  \widetilde{\mathsf M\mathbb Z}
  =
  \mathsf M\mathbb Z
    \mathop{\times}^{h}_{\mathsf M\mathbb Z/2}
  \mathsf W\mathbb Z,                                  \tag{4}
\]
and its canonical ordinary projection.  Composing that projection with the Deligne regulator
gives a source-defined Milnor--Witt refinement of `(1)`:
\[
  R\Gamma_{c,\mathrm{MW}}(X,\mathbb R(n))
  :=
  \operatorname{Fib}\!\left(
    R\Gamma(X,\widetilde{\mathsf M\mathbb Z}(n))_{\mathbb R}
      \longrightarrow
    R\Gamma_D(X/\mathbb R,\mathbb R(n))
  \right).                                             \tag{5}
\]
The ordinary channel of `(5)` is `(1)`; its Witt homotopy fiber retains quadratic duality data.

## Conjecture

`[CONJECTURE] [DAC_WEIL_ARAKELOV_DYNAMICAL_LIFT]`

On Deninger's rational-Witt flow space \(X_W\), the derived coefficient system
\(R U_*\widetilde{\mathsf M\mathbb Z}\) admits a reduced leafwise realization
\[
  D_{\mathrm{dyn}}
  =
  \left[
    L^0\xrightarrow{d^0_F}L^1\xrightarrow{d^1_F}L^2
  \right]                                              \tag{6}
\]
and a closed chain endomorphism
\(\Theta=(\Theta^0,\Theta^1,\Theta^2)\) with:

1. \(d^1_Fd^0_F=0\) and
   \[
     \Theta^1d^0_F=d^0_F\Theta^0,\qquad
     \Theta^2d^1_F=d^1_F\Theta^1.
   \]
2. For every \(n\in\mathbb Z\), a natural multiplicative quasi-isomorphism
   \[
     R\Gamma_{\mathrm{ar},c,\mathrm{MW}}
       (X,\widetilde{\mathbb C}(n))
       \xrightarrow{\;\sim\;}
     \operatorname{Fib}(\Theta-n:D_{\mathrm{dyn}}\to D_{\mathrm{dyn}}),
                                                               \tag{7}
   \]
   whose composite through the two terms of the fiber is cup-\(\theta\).
3. Under the ordinary projection in `(4)`, `(7)` is Flach--Morin's bridge `(3)`.
   Under the Witt fiber, it gives the quadratic trace and dualizing twist needed for
   Poincaré duality.
4. The four-term complex underlying the right side of `(7)` is
   \[
   L^0
   \longrightarrow L^1\oplus L^0
   \longrightarrow L^2\oplus L^1
   \longrightarrow L^2,                                \tag{8}
   \]
   with
   \[
   \begin{aligned}
     \delta^0(x)&=(d^0_Fx,(\Theta^0-n)x),\\
     \delta^1(y,x)&=(d^1_Fy,(\Theta^1-n)y-d^0_Fx),\\
     \delta^2(z,y)&=(\Theta^2-n)z-d^1_Fy.
   \end{aligned}
   \]
5. The finite-correspondence Frobenius/Verschiebung action, the
   \(\mathbb Q_{>0}\)-suspension, and the real Deligne boundary construct `(6)` and \(\Theta\)
   before any Xi divisor or zeta zero is evaluated.
6. Reduced cohomology of `(6)` is concentrated in degrees \(0,1,2\), with
   \(H^0\simeq\mathbb C\), \(H^2\simeq\mathbb C(-1)\), and infinite-dimensional \(H^1\).
7. Its cup product and trace are perfect; its archimedean Hodge operator is source-defined,
   positive, and flow-natural.
8. Its distributional trace is the prime-power plus Gamma Lefschetz distribution and its
   regularized alternating determinant is \(\widehat\zeta\).

## Hostile audit

- `(7)` at integral \(n\) controls generalized \(n\)-eigenspaces and special values.  It does
  not determine the nonintegral spectrum, the full determinant, or the zeta zeros.
- Weil--Arakelov complexes are finite-dimensional.  Their existence alone cannot create the
  infinite-dimensional middle dynamical cohomology.
- Families of derived fibers at all integers need not determine a unique
  \(\mathbb C[\Theta]\)-complex.  Prime-orbit trace, growth, closedness, and regularized
  determinant conditions are essential selection data.
- Arakelov/Deligne pairings supply a genuine archimedean boundary and finite-dimensional
  duality, but do not automatically prove a positive flow-natural Hodge operator on
  \(H^1_{\mathrm{dyn}}\).
- Once the spectrum is identified with Xi zeros, positive flow-natural Hodge is RH-bearing.
  It must therefore be constructed and proved on `(6)` before the determinant comparison.
- The ordinary projection of `(4)` sends \(n_\epsilon\) to \(n\), but discarding the Witt
  fiber would also discard the proposed quadratic duality channel.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`.  Equations `(5)`--`(8)` replace an unspecified
“Gamma boundary” with a falsifiable regulator-fiber construction.  Existence of the
monodromic/dynamical lift `(6)`--`(7)`, source Hodge positivity, and the full trace remain open.

## Formal progress

`[LEAN-PROVED] [DAC_WEIL_ARAKELOV_FIBER_ALGEBRA]`
`DeningerArithmeticWeilArakelovFiber.lean` formalizes `(8)` for arbitrary modules and proves both
successive differential compositions vanish from the horizontal complex identities and
\(\Theta\)-commutation.  It also identifies bottom cocycles, both transgression equations, and
the top coboundary submodule.  No spectral, positivity, determinant, or RH assumption occurs.

The older `DeningerArithmeticResidueFlowTotalization.lean` is now correctly classified as the
two-term mapping-fiber prototype, not as the construction of dynamical \(H^0,H^1,H^2\).

## References

- Matthias Flach, Baptiste Morin, *Deninger's conjectures and Weil--Arakelov cohomology*:
  https://www.math.u-bordeaux.fr/~bmorin/Deninger-WA5.pdf
- Andreas Holmström, Jakob Scholbach, *Arakelov motivic cohomology I*:
  https://arxiv.org/abs/1012.2523
- Jakob Scholbach, *Arakelov motivic cohomology II*:
  https://arxiv.org/abs/1205.3890
- Håkon Kolderup, Oliver Röndigs, Paul Arne Østvær,
  *Hermitian K-theory and Milnor-Witt motivic cohomology over Z*:
  https://arxiv.org/abs/2509.16404

## Log

- 2026-07-26 — Opened after correcting the conflation of transverse flow with a
  cohomological differential.  Flach--Morin's homotopy-fiber bridge supplies the exact
  compatibility target for Deninger's \(R\alpha_*\mathscr G\).
