# Finite observation resolves replica collisions at the inverse detuning scale

- **ID:** `finite-window-replica-collision-resolution-law`
- **Stage:** 2-fully-proven
- **Type:** DEPENDENCY-CLOSED PAPER PROOF / FINITE-TIME RETURN MOMENTS /
  OPERATIONAL CROSSOVER
- **Date:** 2026-07-30
- **Status:** `[PAPER-PROVED] [BRIDGE] [LEAN THEOREM A COMPLETE]`
  `[LEAN THEOREM B COMPLETE]`
- **Parent:** `local-interaction-replica-collision-extremality.md`

## Theorem A — exact finite-window error certificate

Let
\[
 \mu=\sum_{j=1}^{D}p_j\delta_{E_j},
 \qquad p_j\ge0,\quad\sum_jp_j=1,
\]
and
\[
 F(t)=\left|\sum_jp_je^{-itE_j}\right|^2.
\]
Fix an integer \(m\ge1\). Let \(\mathcal D_m\) be the finite set of
nonzero replica detunings
\[
 \mathcal D_m
 =
 \left\{
 \sum_{r=1}^{m}E_{i_r}-\sum_{r=1}^{m}E_{j_r}
 \ne0
 \right\}.
\]
If \(\mathcal D_m\ne\varnothing\), put
\[
 \delta_m=\min_{\Delta\in\mathcal D_m}|\Delta|>0.
\]
Let
\[
 M_m
 =
 \mathbb P\!\left(
 \sum_{r=1}^{m}E_{X_r}
 =
 \sum_{r=1}^{m}E_{Y_r}
 \right)
\]
for two independent \(m\)-samples from \(\mu\). Then for every \(T>0\),
\[
 \boxed{
 \left|
 \frac1{2T}\int_{-T}^{T}F(t)^m\,dt-M_m
 \right|
 \le
 \min\!\left(1,\frac1{T\delta_m}\right).
 }                                                       \tag{1}
\]
If \(\mathcal D_m=\varnothing\), the finite-window average equals \(M_m=1\)
for every \(T\).

### Proof

Expand the \(m\)-th power by replica multiplicity vectors \(k,\ell\):
\[
 F(t)^m
 =
 \sum_{\substack{|k|=m\\|\ell|=m}}
 w_{k,\ell}e^{-it\Delta_{k,\ell}},
\]
where
\[
 w_{k,\ell}
 =
 {m\choose k}{m\choose\ell}
 \prod_jp_j^{k_j+\ell_j}\ge0
\]
and
\[
 \Delta_{k,\ell}=\sum_j(k_j-\ell_j)E_j.
\]
The weights form a probability distribution:
\[
 \sum_{k,\ell}w_{k,\ell}
 =
 \left(\sum_jp_j\right)^{2m}=1.                        \tag{2}
\]

Symmetric-window integration gives
\[
 \frac1{2T}\int_{-T}^{T}e^{-it\Delta}\,dt
 =
 \begin{cases}
 1,&\Delta=0,\\[2mm]
 \dfrac{\sin(T\Delta)}{T\Delta},&\Delta\ne0.
 \end{cases}                                           \tag{3}
\]
The zero-detuning terms sum exactly to \(M_m\). Therefore, by `(2)` and
\[
 \left|\frac{\sin x}{x}\right|
 \le\min(1,|x|^{-1}),
\]
the absolute remainder is at most
\[
 \sum_{\Delta_{k,\ell}\ne0}
 w_{k,\ell}
 \min\!\left(1,\frac1{T|\Delta_{k,\ell}|}\right)
 \le
 \min\!\left(1,\frac1{T\delta_m}\right).
\]
If every detuning is zero, `(3)` makes the average identically one.
\(\square\)

## Theorem B — fixed-order one-knob robustness

Let \(H(g)=A+gV\) be a finite-dimensional Hermitian affine family.
Assume its symmetric discriminant and every nonconstant balanced rational
relation polynomial restrict to nonzero polynomials in \(g\). Fix
\(M\ge1\) and a compact interval \(J\subset\mathbb R\).

There is a finite set \(R_{M,J}\subset J\) such that for every compact
\[
 K\subset J\setminus R_{M,J}
\]
there is a number \(\delta_{M,K}>0\) satisfying
\[
 |\Delta_{k,\ell}(g)|\ge\delta_{M,K}                   \tag{4}
\]
for every \(g\in K\), every replica order \(1\le m\le M\), and every
nonzero order-\(m\) detuning. Consequently, uniformly for \(g\in K\),
\[
 \boxed{
 \left|
 \frac1{2T}\int_{-T}^{T}F_g(t)^m\,dt-M_m(g)
 \right|
 \le
 \min\!\left(1,\frac1{T\delta_{M,K}}\right)
 }                                                       \tag{5}
\]
for all \(1\le m\le M\) and \(T>0\).

### Proof

For fixed \(M\) and finite spectral dimension, only finitely many
multiplicity pairs occur. For every unequal pair, the corresponding
balanced relation is detected by one symmetric relation polynomial.
After restriction to \(H(g)\), that polynomial has finitely many real
roots because it is nonzero. Add the finitely many roots of the
discriminant and take the finite union over all orders \(m\le M\) and
all multiplicity pairs. This is \(R_{M,J}\).

On its complement the ordered eigenvalues are continuous and every
nontrivial detuning through order \(M\) is nonzero. The minimum of the
finitely many continuous absolute detunings on compact \(K\) is therefore
strictly positive; call it \(\delta_{M,K}\). Apply Theorem A.
\(\square\)

## Interpretation

Exact projective rank is discontinuous under arbitrarily weak interaction,
but finite-order observation is not. At order \(m\), the crossover is
controlled by the smallest nonzero \(m\)-replica detuning:
\[
 T\delta_m\gg1.
\]
This is an exact resolution criterion, not a claim that \(\delta_m\) has a
system-size-independent lower bound. It closes the logical gap between the
completed recurrence law and a finite-window measurement while preserving
the possibility of astronomically slow crossover.

## Hostile audit

1. **Missing normalization factor?** Symmetric integration produces
   \(\sin(T\Delta)/(T\Delta)\) exactly, so the constant in `(1)` is one.
2. **Can signed terms cancel and invalidate the bound?** Cancellation can
   only improve it. The triangle inequality uses nonnegative replica
   weights whose total is one.
3. **Can \(\delta_m\) vanish without an exact resonance?** No at fixed
   finite dimension and replica order; the nonzero detuning set is finite.
4. **Is the one-knob exceptional set countable rather than finite?** Across
   all orders it is countable. For fixed \(M\), only finitely many relation
   polynomials occur, so the exceptional set inside \(J\) is finite.
5. **Does compactness hide a crossing?** Discriminant roots are included in
   \(R_{M,J}\); ordered eigenvalues are continuous everywhere and simple on
   the retained compact set.
6. **Does `(5)` prove experimental feasibility?** It gives an exact
   certificate conditional on the measurable detuning scale. It does not
   promise that the required time is technologically accessible.

No paper-proof dependency remains. This theorem is an operational bridge,
not standalone novelty.

## Gates

- [x] exact sinc expansion
- [x] probability-weight normalization
- [x] sharp inverse-detuning error bound
- [x] finite-order one-knob uniformity
- [x] exact Lean formalization: the unit-constant finite-window certificate is
  complete in `FiniteWindowReplicaCollisionResolution.lean`, and fixed-order
  one-knob uniformity (Theorem B) is complete in
  `FiniteWindowOneKnobUniformity.lean`

## Lean status

Theorem A is `norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le`
(`FiniteWindowReplicaCollisionResolution.lean`): for nonnegative normalized
weights, any positive lower bound on the nonzero order-`n` detunings controls
the symmetric-window error by `min 1 (T δ)⁻¹`.

Theorem B is formalized in `FiniteWindowOneKnobUniformity.lean`:

- `oneKnobDetuning`, `replicaPairIndex` — the knob-dependent detunings and the
  finite index of replica multiplicity pairs through order `M`;
- `ReplicaRelationDetection` — the card's hypothesis as data: a continuous
  nonnegative relation probe, dominated by the detuning, with finite zero set
  unless the detuning vanishes identically on the knob interval;
- `finite_exceptionalKnobSet` — the exceptional set `R_{M,J}` is finite;
- `exists_uniform_replicaDetuning_gap` — on every compact knob set avoiding it,
  one `δ > 0` bounds every retained detuning of every order through `M`;
- `exists_uniform_finiteWindow_certificate` — equation `(5)`: one error bound
  `min 1 (T δ)⁻¹` valid simultaneously for every knob value in the compact set,
  every replica order through `M`, and every window length;
- `affineSpectrum`, `affineRelationPolynomial`, `affineReplicaRelationDetection`,
  `affine_exists_uniform_finiteWindow_certificate` — for a simultaneously
  diagonalized family the detunings are degree-one polynomials in the knob, so
  every hypothesis is discharged and the whole statement is unconditional;
- `diagonal_add_smul_diagonal`, `isHermitian_diagonal_affine` — that family is
  exactly the Hermitian matrix family `A + g V` in diagonal form.

All statements are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

The Hermitian family of Theorem B is handled directly, not only in the
simultaneously diagonalized case.  `HermitianCharpolyFactorization.lean` supplies
two facts that mathlib does not have:

- `isHermitian_charpoly_eq_prod` — the characteristic polynomial of a Hermitian
  matrix splits into the linear factors given by its eigenvalues (conjugating by
  the eigenvector unitary and comparing determinants at every scalar);
- `isHermitian_esymm_eigenvalues_eq_coeff` — Vieta for a Hermitian spectrum: every
  elementary symmetric function of the eigenvalues is, up to sign, a coefficient of
  the characteristic polynomial.

`HermitianKnobRelationPolynomial.lean` turns these into the card's relation
polynomial for `H(g) = A + g V`:

- `knobPolyMatrix`, `knobCharpoly`, `coeff_charpoly_knobMatrix` — the
  characteristic coefficients are polynomials in the knob;
- `relationSymmetric`, `relationSymmetric_isSymmetric`,
  `exists_relationSymmetric_esymmAlgHom` — the product of a balanced linear form
  over all relabellings of the spectrum is symmetric, hence a polynomial in the
  elementary symmetric functions (mathlib's fundamental theorem);
- `knobRelationPolynomial` and **`eval_knobRelationPolynomial`** — the resulting
  polynomial in the knob evaluates to that relabelling product;
- `abs_eigenvalues_le_entrySum`, `abs_hermitianKnobSpectrum_le`,
  **`abs_eval_knobRelationPolynomial_le`** — on a bounded knob range the other
  relabelling factors are bounded, so the relation polynomial is dominated by the
  detuning itself;
- **`hermitianReplicaRelationDetection`** and
  **`hermitian_exists_uniform_finiteWindow_certificate`** — the detection data and
  the uniform certificate for a genuine (not necessarily commuting) Hermitian
  affine family, assuming only the card's own hypothesis that the relation
  polynomials are nonzero.

All statements are axiom-clean.
