# Hermitian radial line realizes Poisson flow and positive Hodge star

- **ID:** `deninger-hermitian-radial-line-poisson-hodge`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_DENINGER_HERMITIAN_RADIAL_LINE_POISSON_HODGE`
- **Parent:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Statement:** squared norm on a Hermitian complex line converts the
  half-density flow into Meyer's dilation, while its Kähler area has
  weight one and its degree-one Hodge star is positive and squares to
  \(-1\).

## The local line

Let \(L=\mathbb C\) with coordinate \(z=X+iY\), Hermitian norm
\(|z|\), orientation \(dX\wedge dY\), and Kähler form
\[
 \omega=\frac{i}{2}\,dz\wedge d\bar z=dX\wedge dY.               \tag{1}
\]
Put
\[
 x(z)=|z|^2=X^2+Y^2.                                             \tag{2}
\]
For \(t\in\mathbb R\), define the half-density flow
\[
 s_t(z)=e^{t/2}z.                                                \tag{3}
\]

## Theorem

`[PROVED HERE] [DAC_DENINGER_HERMITIAN_RADIAL_LINE_POISSON_HODGE]`

The following identities hold.

1. **Poisson radius**
   \[
   x(s_tz)=e^t x(z).                                             \tag{4}
   \]
   Hence, at \(t=\log n\),
   \[
   s_{\log n}^*(f\circ x)
   =(u\mapsto f(nu))\circ x                                     \tag{5}
   \]
   for every radial test function \(f\).

2. **Weight-one Kähler class**
   \[
   s_t^*\omega=e^t\omega.                                       \tag{6}
   \]

3. **Odd degree-one Hodge operator**
   \[
   *dX=dY,\qquad *dY=-dX,\qquad *^2=-1
   \quad\text{on }\Omega^1(L).                                  \tag{7}
   \]

4. **Positivity**
   for every real one-form \(\alpha=a\,dX+b\,dY\),
   \[
   \alpha\wedge *\alpha
   =(a^2+b^2)\omega,                                            \tag{8}
   \]
   strictly positive wherever \(\alpha\ne0\).

5. **Flow/Hodge compatibility**
   \[
   s_t^**=*s_t^*
   \quad\text{on one-forms}.                                    \tag{9}
   \]

6. **Critical Hilbert measure.**  In polar coordinates
   \(z=r e^{i\theta}\), \(x=r^2\),
   \[
   \omega=r\,dr\wedge d\theta
         =\frac12\,dx\wedge d\theta.                             \tag{10}
   \]
   Therefore every radial function \(F(z)=f(|z|^2)\) satisfies
   \[
   \int_{\mathbb C}|F(z)|^2\,\omega
   =\pi\int_0^\infty|f(x)|^2\,dx.                               \tag{11}
   \]
   Up to the harmless scalar \(\pi\), this is exactly Meyer's
   critical space
   \[
   L^2_{1/2}
   =L^2(\mathbb R_{>0},x\,d^\times x)
   =L^2(\mathbb R_{>0},dx),                                     \tag{12}
   \]
   on which additive Fourier transform and \(J\) are unitary.

All statements glue through unitary transition functions on a
Hermitian line bundle.  Equivalently, they are defined by a principal
\(S^1\)-torsor and its associated complex line.

### Proof

Equation `(4)` is
\[
 |e^{t/2}z|^2=e^t|z|^2,
\]
and `(5)` follows.  Since
\(s_t^*dX=e^{t/2}dX\) and
\(s_t^*dY=e^{t/2}dY\), their wedge gives `(6)`.
Equations `(7)`--`(8)` follow by direct exterior algebra:
\[
 (a\,dX+b\,dY)\wedge(a\,dY-b\,dX)
 =(a^2+b^2)dX\wedge dY.
\]
The same scalar \(e^{t/2}\) multiplies both members of the oriented
orthonormal coframe, proving `(9)`.  Unitary changes of frame preserve
norm, orientation, \(\omega\), and \(*\), so the construction glues.
Finally \(x=r^2\) gives \(dx=2r\,dr\), proving `(10)`; angular
integration gives `(11)`, and `(12)` is the definition of Meyer's
weighted critical Hilbert space.

## Why squared norm is forced

Suppose a scalar radius is \(x=|z|^\delta\) and scalar flow on the line
is \(z\mapsto e^{ct}z\).  Requiring both
\[
 x\mapsto e^t x,\qquad \omega\mapsto e^t\omega
\]
gives
\[
 c\delta=1,\qquad 2c=1.
\]
Thus \(c=\tfrac12\) and \(\delta=2\).  The half-density scaling and
squared Hermitian norm are not optional normalizations.

This is the geometric version of
`DAC_POLARIZED_TRANSFER_HALF_DENSITY`.

## Deninger source specialization

Deninger's exact equivariant exponential sequence and regulator give
the source Tate--Kummer circle torsor
`DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER`.  The
Hilbert--Kummer refinement gives the positive descended radius
\[
 x([P,u])=u\|\ell_P\|.
\]
Therefore the arithmetic leaf construction has an exact target:

1. form the Hermitian line associated to the universal
   Tate--Kummer \(S^1\)-torsor;
2. identify its squared norm with \(u\|\ell_P\|\);
3. extend it through unit amalgamation, prime residues, and the real
   boundary;
4. prove that its leafwise de Rham pushforward is the Poisson--zeta
   relevant complex.

Once steps 1--4 are proved, `(4)`--`(9)` supply the desired
complex-one-dimensional Kähler leaf, weight-one conformal flow, odd
Hodge star, and source positivity simultaneously.

Equation `(11)` additionally proves that the resulting radial source
metric is not an arbitrary Hilbert completion: it is the exact
critical \(L^2_{1/2}\) metric already forced by Meyer's Fourier--Poisson
construction.  The still-open issue is descending its harmonic
orthogonal complement through \(Z(H_\cap)\); completing the raw
cokernel is not justified by `(11)`.

The theorem proves the local and bundle-theoretic geometry.  It does
not assert the global norm/torsor identification in step 2 or the
derived comparison in step 4.

## Hostile audit

- No zeta zero or spectral divisor defines the metric.
- A bare positive radial function is not silently promoted to a line
  bundle; the Tate--Kummer circle torsor is required.
- The line is complex one-dimensional, giving the required real
  leaf dimension two.
- Positivity is source exterior algebra and does not yet imply
  faithfulness on Meyer generalized-zero classes.
- No CCM object or numerical computation occurs.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §12, equivariant Tate exponential sequence and regulator:
  https://arxiv.org/abs/1807.06400
- `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`
- `DAC_POLARIZED_TRANSFER_HALF_DENSITY`

## Log

- 2026-07-27 — Extracted the unique squared-norm/half-density
  Hermitian-line model compatible with both Poisson dilation and
  weight-one Kähler scaling.

## Lean status

### The local Hermitian line landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticHermitianRadialLine.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerHermitianLineRadius`, `deningerHermitianLineScale`, `deningerHermitianLineArea`,
  `deningerHermitianLineHodge` — the squared radius `(2)`, the scalar flow, the oriented Kähler
  area `(1)`, and the degree-one Hodge star `(7)`.
- `deningerHermitianLineRadius_scale`, `deningerHermitianLineArea_scale` — the radius and the area
  scale by the square of the scalar.
- `deningerHermitianLineHodge_sq` — `*² = -1` on one-forms, part of `(7)`.
- `deningerHermitianLineArea_hodge_self`, `deningerHermitianLineHodge_positive` — **`(8)`**:
  `α ∧ *α = (a²+b²) ω`, strictly positive away from zero.
- `deningerHermitianLineHodge_scale` — **`(9)`**: the star commutes with the scalar flow.

### The flow, the critical measure, and the forced exponents landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerHermitianCriticalMeasure.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerKahlerForm_eq` — **`(1)`**: evaluating `(i/2) dz ∧ dz̄` on two tangent vectors gives the
  determinant of their real coordinates, so the Kähler form is the oriented area `dX ∧ dY`.
- `deningerHermitianLineHodge_fst`, `deningerHermitianLineHodge_snd` — **`(7)`** on the coframe:
  `*dX = dY` and `*dY = -dX`.
- `deningerLineHalfDensityFlow` with `deningerLineHalfDensity_sq` — the flow `s_t z = e^{t/2} z` `(3)`.
- `deningerLineHalfDensityFlow_radius` — **`(4)`**: `x(s_t z) = e^t x(z)`.
- `deningerLineHalfDensityFlow_radialPullback` — **`(5)`**: at `t = log n` the pullback of a radial test
  function is its dilate by `n`.
- `deningerLineHalfDensityFlow_area` — **`(6)`**: `s_t^* ω = e^t ω`.
- `deningerLineHalfDensityFlow_hodge` — **`(9)`** for the half-density flow.
- `deningerPolarPoint_hasDerivAt_radial`, `deningerPolarPoint_hasDerivAt_angular`,
  `deningerPolarArea_radial` — **`(10)`**: the polar tangent frame has area `r`, so
  `ω = r dr ∧ dθ`.
- `deningerPolarPoint_hasDerivAt_squared`, `deningerPolarArea_squared` — and in the squared radius
  coordinate the same frame has area `½`, so `ω = ½ dx ∧ dθ`.
- `deningerCriticalMeasure` — **`(11)`**: `∫_ℂ |f(|z|²)|² ω = π ∫_0^∞ |f(x)|² dx`, read off the
  polar reduction `deningerPolarTrace` (polar change of variables, angular measure `2π`, and the
  substitution `x = r²`) applied to the squared modulus.
- `deningerMultiplicativeWeight` — **`(12)`**: weighting the multiplicative Haar density `dx/x` by
  `x` returns Lebesgue measure on the half line, so `L²(ℝ_{>0}, x d^×x) = L²(ℝ_{>0}, dx)`.
- `deningerLineHalfDensity_forced` — **the exponents are forced**: if the flow `z ↦ e^{ct}z` gives both
  the radius of exponent `δ` and the area the weight one, then `c = 1/2` and `δ = 2`.
- `deningerFrameRotation_radius`, `deningerFrameRotation_area`, `deningerFrameRotation_hodge` —
  **the gluing claim**: a unitary change of frame preserves the radius, the Kähler area, and
  commutes with the Hodge star, so the construction descends to a Hermitian line bundle.

### Remaining

Nothing.  Every identity the theorem states is formalized unconditionally, together with the
uniqueness of the exponents and the unitary gluing.  The card's own open items — the global
norm/torsor identification and the derived comparison — are explicitly outside the theorem.
