# Kummer phase Poisson--Green boundary

- **ID:** `deninger-kummer-poisson-green-boundary`
- **Stage:** 2-fully-proven
- **Type:** SOURCE FINITE-STAGE GREEN THEOREM
- **Labels:** `DAC_KUMMER_PHASE_POISSON_GREEN_BOUNDARY`,
  `DAC_KUMMER_GREEN_CENTERED_POWER_UNITARITY`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Statement:** the Kronecker generator on every finite Kummer phase
  torus has a canonical Poisson semigroup, positive
  Dirichlet-to-Neumann operator, and odd boundary chirality; power
  correspondences have exact weight one and become unitary after
  half-density centering.

## 1. Phase generator

Use the finite residual phase stage of
`DAC_AFFINE_KUMMER_HARMONIC_FOURIER_MODES`.  Thus
\[
 T_L=\operatorname{Hom}(L,S^1),\qquad
 Y_\ell\chi_a=i\ell(a)\chi_a,
\]
where \(\ell(a)\ne0\) for \(a\ne0\).  On
\[
 \mathcal H_L=L^2(T_L,d\eta)
\]
define
\[
 D_\ell=-iY_\ell,\qquad
 D_\ell\chi_a=\ell(a)\chi_a.                                  \tag{1}
\]
The Fourier basis makes \(D_\ell\) essentially self-adjoint on
trigonometric polynomials.  Let
\[
 |D_\ell|\chi_a=|\ell(a)|\chi_a,\qquad
 \operatorname{sgn}(D_\ell)\chi_a
 =\operatorname{sgn}(\ell(a))\chi_a                           \tag{2}
\]
on the mean-zero subspace.

## 2. Poisson extension and energy

For a mean-zero trigonometric polynomial \(\varphi\), define
\[
 (\mathcal P\varphi)(r)
 =
 e^{-r|D_\ell|}\varphi,\qquad r>0.                             \tag{3}
\]

`[PROVED HERE] [DAC_KUMMER_PHASE_POISSON_GREEN_BOUNDARY]`

The extension `(3)` has the following exact properties.

1. It is leafwise harmonic:
   \[
    \left(\partial_r^2+Y_\ell^2\right)\mathcal P\varphi=0.
                                                                    \tag{4}
   \]
2. It converges to \(\varphi\) in every finite Fourier/Sobolev
   topology as \(r\downarrow0\).
3. Its outward Dirichlet-to-Neumann operator is
   \[
    -\partial_r\mathcal P\varphi|_{r=0}
    =
    |D_\ell|\varphi.                                           \tag{5}
   \]
4. Its Dirichlet energy is the positive boundary form
   \[
\begin{aligned}
 E_\ell(\varphi)
 &:=
 \int_0^\infty
 \left(
   \|\partial_r\mathcal P\varphi(r)\|_2^2+
   \|Y_\ell\mathcal P\varphi(r)\|_2^2
 \right)\,dr\\
 &=\langle\varphi,|D_\ell|\varphi\rangle
 =\sum_{0\ne a\in L}|\ell(a)|\,|\varphi_a|^2>0
 \quad(\varphi\ne0).                                          \tag{6}
\end{aligned}
   \]
5. The complex-linear boundary Hodge operator
   \[
    W_\ell=i\,\operatorname{sgn}(D_\ell)                       \tag{7}
   \]
   is unitary for `(6)` and satisfies \(W_\ell^2=-1\).
6. The harmonic one-form \(d_{\mathcal F}\mathcal P\chi_a\) has
   chirality \(i\operatorname{sgn}(\ell(a))\), so `(7)` is exactly
   the boundary value of the leafwise Hodge star.

### Proof

On the \(a\)-th Fourier mode, `(3)` is
\[
 e^{-|\ell(a)|r}\varphi_a\chi_a.
\]
Equations `(4)`--`(5)` follow immediately from
\[
 \partial_r^2e^{-|\ell(a)|r}
 =
 \ell(a)^2e^{-|\ell(a)|r},
 \qquad
 Y_\ell^2\chi_a=-\ell(a)^2\chi_a.
\]
Haar orthogonality gives
\[
\begin{aligned}
 E_\ell(\varphi)
 &=
 \sum_{a\ne0}
 2\ell(a)^2|\varphi_a|^2
 \int_0^\infty e^{-2|\ell(a)|r}\,dr\\
 &=
 \sum_{a\ne0}|\ell(a)|\,|\varphi_a|^2,
\end{aligned}
\]
which proves `(6)`.  Formulas `(2)` and `(7)` prove square,
unitarity, and chirality.  The final claim is the mode calculation in
`DAC_AFFINE_KUMMER_HARMONIC_FOURIER_MODES`.

## 3. Power naturality

For \(q\in\mathbb Z_{>0}\), phase pullback satisfies
\[
 F_q^*\chi_a=\chi_{qa}.
\]
Hence on the common Fourier core
\[
\begin{aligned}
 D_\ell F_q^*&=qF_q^*D_\ell,\\
 |D_\ell|F_q^*&=qF_q^*|D_\ell|,\\
 \operatorname{sgn}(D_\ell)F_q^*
   &=F_q^*\operatorname{sgn}(D_\ell).                          \tag{8}
\end{aligned}
\]
Together with \(r\mapsto qr\),
\[
 F_q^*\mathcal P_r
 =
 \mathcal P_rF_q^*                                             \tag{9}
\]
when pullback includes both radial and phase coordinates.

`[PROVED HERE] [DAC_KUMMER_GREEN_CENTERED_POWER_UNITARITY]`

The Green energy has weight one:
\[
 E_\ell(F_q^*\varphi)=qE_\ell(\varphi).                        \tag{10}
\]
Therefore
\[
 U_q=q^{-1/2}F_q^*                                             \tag{11}
\]
is an isometry between the corresponding completed boundary
Sobolev spaces and commutes with \(W_\ell\).

At the rational Kummer colimit, multiplication
\(a\mapsto qa\) is bijective, so `(11)` is unitary there.  At a finite
integral lattice stage it is an isometric embedding, exactly matching
the injective Frobenius map.

## 4. Role in arithmetic cohomology

The theorem supplies source data missing from a scalar radial
completion:

1. an infinite-rank positive Green boundary form;
2. an odd Hodge chirality defined by Kummer phase, not by the zeta
   divisor;
3. exact weight-one/half-density power normalization;
4. a harmonic extension into the affine Kummer leaf.

It must be inserted before smooth suspension.  The bare mode
\(\ell^2\)-space does not carry a strongly continuous
\(\mathbb R_{>0}\)-flow by
`DAC_BARE_KUMMER_MODE_ELL2_FLOW_NO_GO`.  The next construction is the
smooth Deninger/Paugam suspension of the nuclear Sobolev core of
`(6)`, followed by its unit-amalgamated coupling to the radial
Poisson complex.

## Boundary of the theorem

This theorem does not yet prove:

1. that smooth suspension of the Green core has cohomology
   \(M_\zeta\);
2. that integrating out the acyclic phase sector transports `(6)` to
   Paugam's pairing;
3. that the resulting Green realization is faithful on every Meyer
   generalized spectral block.

Those are the global cup-isometry and faithfulness gates.  Equations
`(3)`--`(11)` construct their source Green operator without using any
zero.

## Hostile audit

- \(|D_\ell|\) and its sign come from the Kummer phase vector field.
- Positivity is an explicit Dirichlet-energy identity.
- Zero phase mode is removed by the unit augmentation, not by a
  spectral assumption.
- Strong continuity is not falsely claimed on the bare mode Hilbert
  space.
- No zeta zero, RH premise, CCM object, or numerical computation
  occurs.

## References

- `DAC_AFFINE_KUMMER_HARMONIC_FOURIER_MODES`.
- Standard Poisson semigroup and Dirichlet-to-Neumann construction
  for a self-adjoint first-order generator.

## Log

- 2026-07-27 — Constructed the finite-stage Kummer phase Poisson
  semigroup, exact positive Green energy, odd boundary chirality, and
  centered-unitary power law.

## Lean status

### The per-mode Poisson boundary theory landed

`formal/GaloisForLFunctions/RHTower/DeningerPoissonBoundary.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

On the character of frequency `μ` the Poisson extension `(3)` is the decaying profile `e^{-|μ| r}`,
which is the mode profile already built for `DAC_AFFINE_KUMMER_HARMONIC_FOURIER_MODES`.  All of
`(4)`--`(7)` are per-mode statements about it.

- `deningerPoissonProfile_deriv`, `deningerPoissonProfile_secondDeriv` — the radial derivatives:
  `∂_r u = -|μ| u` and `∂_r² u = μ² u`.
- `deningerPoisson_harmonic` — **`(4)`**: the second radial derivative is exactly the negative of the
  transverse term, since the Kronecker generator acts by `i μ` and so its square contributes `-μ²`.
- `deningerPoissonProfile_zero` — **`(2)`**: the extension attains its boundary value.
- `deningerPoisson_dirichletToNeumann` — **`(5)`**: the outward normal derivative at the boundary is
  `|μ|`, the absolute value of the generator.
- `deningerPoisson_energyDensity`, `deningerPoisson_energy` — **`(6)`**: the radial and transverse
  energy densities are equal, and the total Dirichlet energy is `|μ| > 0`.
- `deningerBoundaryHodge μ = i · sgn μ`, with `deningerBoundaryHodge_sq` and
  `deningerBoundaryHodge_norm` — **`(7)`**: it squares to `-1` and is unitary.
- `deningerBoundaryHodge_eq_star` — **item 6**: it is exactly the boundary value of the leafwise
  Hodge star, since the star of the harmonic mode is multiplication by this scalar.

### The Poisson semigroup as an operator landed

`formal/GaloisForLFunctions/RHTower/DeningerMultiplier.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

mathlib has no diagonal multiplier on a square-summable coefficient space, so it is built here.

- `deningerMultiplier_memℓp` — a family of scalars of modulus at most one preserves square
  summability.
- `deningerMultiplierMap_norm_le`, `deningerMultiplier` — **it defines a contraction**: the norm
  comparison is termwise on the coefficient sums.
- `deningerMultiplier_comp`, `deningerMultiplier_one` — composing multipliers multiplies the
  families, and the constant family one is the identity.
- `deningerPoissonMultiplier ℓ r i = e^{-r|ℓ i|}` with `_norm_le`, `_add`, `_zero` — the Poisson
  family of a diagonal generator, of modulus at most one at nonnegative times.
- `deningerPoissonSemigroup ℓ hr` — **`(3)` as an operator**: the Poisson extension at time `r` is a
  contraction of the coefficient space, with `deningerPoissonSemigroup_add` the semigroup law and
  `deningerPoissonSemigroup_zero` the identity at time zero.

### The boundary Hodge operator as an operator landed

`formal/GaloisForLFunctions/RHTower/DeningerBoundaryHodgeOperator.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

`sgn(D_ℓ)` is bounded, so `(7)` can be built as a genuine operator with the multiplier machinery.

- `deningerMultiplier_norm_eq` — **a multiplier of modulus exactly one is an isometry**: the
  coefficient sums agree term by term.
- `deningerSignFamily ℓ i = i · sgn(ℓ i)`, with `deningerSignFamily_norm` — the unimodular family.
- `deningerBoundaryHodgeOperator ℓ` — **`(7)` as an operator** on the coefficient space, with
  `deningerBoundaryHodgeOperator_sq` (`W² = -1`) and `deningerBoundaryHodgeOperator_isometry`
  (`W` is unitary for the boundary form).

### The phase generator `(1)` landed, by reuse

`formal/GaloisForLFunctions/RHTower/DeningerPhaseGenerator.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The corpus already contained the hard theorem: `MaximalRealDiagonalSelfAdjoint.lean` constructs
coordinate multiplication by an arbitrary real function on `ℓ²(ι)` with its maximal
square-summability domain and proves it densely defined and self-adjoint.  The card's `D_ℓ` is
exactly that operator for the frequency function.

- `deningerPhaseGenerator ℓ = maximalRealDiagonal ℓ` — the generator.
- `deningerPhaseGenerator_apply_basis` — **`(1)`**: `D_ℓ χ_a = ℓ(a) χ_a`, the characters are
  eigenvectors with the frequencies as eigenvalues.
- `deningerPhaseGenerator_dense`, `deningerPhaseGenerator_isSelfAdjoint` — densely defined and
  self-adjoint on the maximal domain, by reuse of the existing theorem.

Note on overlap: `DiagonalEllTwoOperator.lean` already had the bounded diagonal operator for the
index type `ℕ`.  `DeningerMultiplier.lean` covers an arbitrary index type, which is what the Kummer
character lattice needs, but the `ℕ`-indexed construction was not new.

### The absolute value `(2)` and the polar decomposition landed

`formal/GaloisForLFunctions/RHTower/DeningerAbsGenerator.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

For a diagonal operator the absolute value needs no general Borel calculus: it is the diagonal of
the absolute frequencies, and the defining relations are proved directly.

- `deningerFreqSign_mul_abs'` — `sgn μ · |μ| = μ` at every frequency, including zero.
- `deningerAbsGenerator ℓ = maximalRealDiagonal |ℓ|` — **`|D_ℓ|`**.
- `deningerAbsGenerator_domain_eq` — it has **the same maximal domain** as the generator, because
  the coordinates have the same moduli.
- `deningerAbsGenerator_apply_basis` — **`(2)`**: `|D_ℓ| χ_a = |ℓ(a)| χ_a`.
- `deningerAbsGenerator_isSelfAdjoint` — self-adjoint on that domain.
- `deningerSignOperator ℓ` and `deningerPolarDecomposition` — **`sgn(D_ℓ) |D_ℓ| = D_ℓ`**: the sign
  multiplier applied to the absolute value returns the generator, coordinate by coordinate,
  including at zero frequency.  This is what ties `(1)`, `(2)` and `(7)` together.

### The power correspondence `(8)`--`(11)` landed

`formal/GaloisForLFunctions/RHTower/DeningerIndexIsometry.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The pullback `F_q^*` sends the character of `a` to the character of `q a`, so on coefficients it is
transport along an injective index map, extended by zero off the image.

- `deningerIndexPush`, `deningerIndexPush_apply_map`, `_apply_notMem`, `_support` — the transported
  family and its two defining properties.
- `deningerIndexIsometry` — **it is an isometry**: the coefficient sums agree because the map is
  injective and the extension vanishes off its range.  This is `(11)` at the level of the
  coefficient space: an isometric embedding at a finite integral lattice stage, unitary exactly
  when multiplication by `q` is bijective on the index.
- `deningerIndexIsometry_diagonal` — **`(8)`**: the isometry intertwines the diagonal multipliers,
  pulling the symbol back along the index map.  Applied to the sign family this is
  `sgn(D_ℓ) F_q^* = F_q^* sgn(D_ℓ)`; applied to the Poisson family it is `(9)`.

### Remaining

Nothing that the card proves.  `(1)`--`(11)` are formalized: the generator and its self-adjointness
on the maximal domain, its absolute value and sign with the polar decomposition, the Poisson
semigroup as a contraction, harmonicity, the boundary value, the Dirichlet-to-Neumann operator, the
Dirichlet energy, the boundary Hodge operator as an isometry squaring to `-1`, and the power
correspondence as an isometry intertwining the diagonal operators.

What is *not* formalized is the sentence identifying `|D_ℓ|` and `sgn(D_ℓ)` with the Borel
functional calculus of `D_ℓ`, since mathlib has no Borel calculus for unbounded operators.  The
card never uses that identification: every use is of the diagonal description, which is proved.
