# Affine/pro-log prime Hodge overlap

- **ID:** `deninger-affine-pro-log-prime-overlap`
- **Stage:** 3-formalized
- **Type:** SOURCE OVERLAP THEOREM
- **Labels:** `DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP`,
  `DAC_ACTUAL_PRIME_TANGENTIAL_UNITARITY`
- **Parent:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Statement:** on the actual Deninger residue-character locus, the
  normalized generic affine Euler--phase planes converge to the
  pro-log prime-normal complex line; their oriented conformal
  structures and degree-one Hodge stars agree on the overlap.

## 1. Finite log-toric coordinates

Use a finite stage of
`DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.  Choose
\[
 L=\ker\lambda_v\oplus\mathbb Z\pi
\]
and coordinates
\[
 \overline Z_{L,v}
 \cong
 \operatorname{Hom}(\ker\lambda_v,\mathbb C^\times)
 \times\mathbb C_z.                                            \tag{1}
\]
Write a generic point as
\[
 (w_1,\ldots,w_d,z),\qquad z\ne0,
\]
and its logarithmic modulus vector as
\[
 m(P)
 =
 \left(
  L_z,\log|w_1|,\ldots,\log|w_d|
 \right),
 \qquad L_z=-\log|z|.                                          \tag{2}
\]

The actual residue-character locus is
\[
 Y_{L,v}
 =
 \operatorname{Emb}(\overline L_v,\mathbb C^\times)
 \subset D_{L,v}.                                              \tag{3}
\]
The group \(\overline L_v\) is finite.

`[PROVED HERE] [DAC_ACTUAL_PRIME_TANGENTIAL_UNITARITY]`

For every \(y\in Y_{L,v}\), all tangential coordinates have modulus
one.  Consequently, for every net of generic points converging to
\(y\),
\[
 L_z\longrightarrow\infty,\qquad
 \log|w_j|\longrightarrow0,
\]
and hence
\[
 \frac{m(P)}{\|m(P)\|}
 \longrightarrow e_\pi,                                      \tag{4}
\]
where \(e_\pi\) is the positive normal direction.

### Proof

Every value of a character of the finite group
\(\overline L_v\) is a root of unity, so its complex modulus is one.
Convergence in `(1)` gives \(|w_j|\to1\), while \(z\to0\) gives
\(L_z\to\infty\).  Dividing `(2)` by its Euclidean norm proves
`(4)`.  The same argument works for any inner product on the finite
real logarithmic-modulus space because all norms are equivalent and
the tangential part tends to zero.

## 2. Tautological affine complex plane

At a nonunitary generic point, the affine distribution is generated
by simultaneous real-modulus scaling and the matching Kummer phase
flow.  In logarithmic real/phase tangent coordinates its oriented
plane is
\[
 E_{m(P)}
 =
 \operatorname{span}_{\mathbb R}
 \{(m(P),0),(0,m(P))\}.                                       \tag{5}
\]
Its complex structure is
\[
 J(m,0)=(0,m),\qquad J(0,m)=(-m,0).                            \tag{6}
\]

The assignment
\[
 [m]\longmapsto E_m
\]
depends only on the positive projective class of \(m\) and is
continuous into the oriented Grassmannian.  Equation `(4)` therefore
gives
\[
 E_{m(P)}
 \longrightarrow
 E_\pi
 =
 \operatorname{span}_{\mathbb R}
 \{(e_\pi,0),(0,e_\pi)\}.                                     \tag{7}
\]
The plane \(E_\pi\) is exactly the logarithmic normal complex leaf of
`DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION`.

`[PROVED HERE] [DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP]`

The generic affine complex structures, orientations, and
degree-one Hodge stars extend continuously to `(7)` and agree with
the prime-normal cusp star.

### Proof

Choose the normalized oriented coframe on `(5)` obtained from
\(m/\|m\|\).  Its matrix coefficients vary continuously with
\([m]\).  The complex structure `(6)` and the star on the dual
coframe therefore converge to their versions on \(E_\pi\).

More concretely, along a fixed projective direction write
\(m=Rn\).  The affine metric is
\[
 g_{\mathrm{aff}}
 =
 \frac{u}{R}(dR^2+d\tau^2),                                   \tag{8}
\]
where \(\tau\) is phase coordinate in direction \(n\).  Near the
normal ray, \(R=cL_z+o(L_z)\) and
\(\tau=c\theta+o(1)\) for a fixed \(c>0\).  Thus `(8)` is
asymptotic through a positive conformal factor to
\[
 \frac{u}{L_z}(dL_z^2+d\theta^2),                              \tag{9}
\]
the prime cusp metric.  In real dimension two the star on one-forms
depends only on oriented conformal class, so the limiting star is
exactly the one in `(9)`.

## 3. Equivariance and pro-limit

Positive rational power maps multiply the full vector \(m(P)\) by
\(q\).  They do not change its projective class, and both vectors in
`(5)` scale by the same positive factor.  Galois maps permute the
finite residue characters and preserve their unitary tangential
values.  Hence `(4)`--`(9)` are power- and Galois-natural.

Finite-index lattice refinements pull back the normal generator and
tangential unit characters.  The oriented plane and star commute
with these pullbacks.  Therefore the overlap theorem passes to the
filtered pro-log cylinder.

## 4. Consequence

The generic affine distribution and every prime-normal cusp atom now
form one compatible oriented conformal leaf system on the actual
generic-plus-prime Deninger locus.  No interpolation over extra toric
boundary characters is needed: those extra characters were already
removed by restriction to `(3)`.

Remaining geometric gluing concerns:

1. closed relative/rigged domains across the complete cusp;
2. the real orientation-sign endpoint;
3. the global Green/harmonic projection.

The plane and degree-one star themselves are no longer an overlap
conjecture.

## Hostile audit

- Tangential unitarity uses finiteness of the actual residue group,
  not all points of the ambient toric divisor.
- Only oriented conformal/Hodge extension is proved; no smooth
  finite-distance prime point is asserted.
- The metric comparison is used only to identify the conformal star.
- No prime return is mislabeled as an ordinary local diffeomorphism.
- No zeta zero, RH premise, CCM object, or numerical computation
  enters.

## References

- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.
- `DAC_HILBERT_KUMMER_AFFINE_LEAF_DISTRIBUTION`.
- `DAC_PRO_LOG_KUMMER_CUSP_HODGE_EXTENSION`.

## Log

- 2026-07-27 — Proved tangential unitarity on actual residue packets,
  convergence of normalized affine planes to the prime normal line,
  and exact oriented-conformal Hodge overlap through the pro-log
  system.
- 2026-08-02 — Formalized tangential unitarity, the convergence of the
  normalized modulus direction and of the affine frames, and the conformal
  identification of the two stars.

## Lean status

### Both labelled theorems landed

`formal/GaloisForLFunctions/RHTower/DeningerAffinePrimeOverlap.lean`, on top of the cusp module
`DeningerProLogCuspHodge.lean`.  Axiom audit for all 12 declarations:
`propext, Classical.choice, Quot.sound` or less.

`DAC_ACTUAL_PRIME_TANGENTIAL_UNITARITY`:

- `deningerFiniteCharacter_norm_eq_one` — every value of a character of a **finite** group is a
  root of unity, hence has modulus one.  This is the only input about the residue locus `(3)`, and
  it is exactly the card's argument: the group `L̄_v` is finite, so `x ^ card = 1` forces the norm
  of `χ(x)` to be a nonnegative real root of unity.
- `deningerFiniteCharacter_log_eq_zero` — hence the tangential logarithmic coordinates of `(2)`
  vanish on the locus.
- `deningerModulusDirection_tendsto` — **`(4)`**: if the normal coordinate diverges and the
  tangential part tends to zero, the normalized logarithmic modulus vector tends to the positive
  normal generator `e_π`.  Stated for an arbitrary normed tangential space, which covers the card's
  remark that any inner product works since all norms on the finite modulus space are equivalent.

`DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP`:

- `deningerAffinePlane` — the tautological plane `(5)`, the real span of the modulus direction and
  its matching phase direction.
- `deningerAffinePlane_smul_pos` — **the plane depends only on the positive projective class**, so
  the positive rational power maps of §3, which scale the whole modulus vector, do not move it.
- `deningerAffineJ`, `deningerAffineJ_modulus`, `deningerAffineJ_phase`, `deningerAffineJ_sq` — the
  complex structure `(6)` and `J² = -1`.
- `deningerAffineFrame_tendsto` — **`(7)`**: the oriented frame of the affine plane is continuous
  in the modulus direction, so along a net approaching the locus the affine planes converge to the
  normal complex line `E_π`.
- `deningerAffineCusp_conformal` — **`(8)`--`(9)`**: with `R = cL` and `τ = cθ` for a fixed `c > 0`
  the affine metric is `c` times the prime cusp metric, i.e. the two are conformal.
- `deningerAffineCusp_star_agree` — the defining pairing of the degree-one Hodge star is the same
  for both conformal factors, so by the uniqueness of the star (`deningerConformalStar_unique`, in
  the cusp module) the generic affine star and the prime-normal cusp star are the same quarter
  turn.  This is the overlap statement of the card, and it is what removes the overlap conjecture.

### Remaining

Nothing in the two theorems.  The three geometric gluing concerns listed in §4 — closed
relative/rigged domains across the complete cusp, the real orientation-sign endpoint, and the
global Green/harmonic projection — stay open.
