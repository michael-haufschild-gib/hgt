# CCM Rayleigh-excess determinant transfer

- **ID:** `ccm-rayleigh-excess-determinant-transfer`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theory:** the min--max principle and the elementary Rayleigh--Ritz angle bound
- **Statement:** The growing-aperture CCM determinant transfer needs only a quadratic Rayleigh-excess
  estimate. If the normalized prolate seed has Rayleigh excess `O(lambda^(-1))` relative to the true
  even spectral gap, then its Mellin transform converges at the exact projective rate needed to
  transfer the `Xi` divisor.

## Setup

Let `A_lambda` be the self-adjoint continuous restricted Weil operator in the even sector. Assume
its lowest even eigenvalue is simple, with normalized eigenvector `xi_lambda`, and write

```text
epsilon_0(lambda)<epsilon_1(lambda),
Gap_lambda=epsilon_1(lambda)-epsilon_0(lambda).         (1)
```

Let `g_lambda` be the normalized CCM prolate seed in the aperture Hilbert space and put

```text
r_lambda=<A_lambda g_lambda,g_lambda>,
delta_lambda=r_lambda-epsilon_0(lambda)>=0.             (2)
```

## Rayleigh-excess angle theorem

For every `lambda`,

```text
inf_(|c|=1)||g_lambda-c xi_lambda||_2^2
 <=2 delta_lambda/Gap_lambda.                          (3)
```

### Proof

Choose an orthonormal eigenbasis beginning with `xi_lambda` and write

```text
g_lambda=a_0 xi_lambda+sum_(j>=1)a_j xi_j.
```

The spectral theorem gives

```text
delta_lambda
 =sum_(j>=1)(epsilon_j-epsilon_0)|a_j|^2
 >=Gap_lambda sum_(j>=1)|a_j|^2
 =Gap_lambda(1-|a_0|^2).                               (4)
```

After choosing the phase of `xi_lambda`,

```text
inf_(|c|=1)||g_lambda-c xi_lambda||_2^2
 =2(1-|a_0|)
 <=2(1-|a_0|^2).                                      (5)
```

Equations `(4)`--`(5)` prove `(3)`.

## Growing Mellin consequence

If, for every `a<1/2`,

```text
lambda^(2a) delta_lambda/Gap_lambda ->0,               (6)
```

then

```text
lambda^a inf_(|c|=1)||g_lambda-c xi_lambda||_2 ->0     (7)
```

for every `a<1/2`. By `ccm-growing-aperture-mellin-determinant-transfer.md`, `(7)` transfers the
proved prolate-seed Mellin convergence to locally uniform convergence of the normalized true CCM
determinants on every compact substrip of `|Im z|<1/2`.

A convenient sufficient estimate is

```text
delta_lambda/Gap_lambda=O(lambda^(-1)).                (8)
```

which gives projective distance `O(lambda^(-1/2))`.

## Certified-lower-bound form

The unknown ground energy need not be estimated from both sides. If a proved lower bound

```text
L_lambda<=epsilon_0(lambda)                            (9)
```

satisfies

```text
(r_lambda-L_lambda)/Gap_lambda=O(lambda^(-1)),         (10)
```

then `delta_lambda<=r_lambda-L_lambda`, so `(8)` follows. Thus a positive Schur-complement or form
comparison can certify the determinant transfer without estimating the strong operator residual
`||(A_lambda-r_lambda)g_lambda||`.

## Compatibility with the exterior-tail quotient

Choose a global-radical source representative `f_lambda` for the CCM aperture seed and write

```text
E(f_lambda)=a_lambda+b_lambda,
a_lambda=P_lambda E(f_lambda),
b_lambda=(1-P_lambda)E(f_lambda).                      (11)
```

The exact radical quotient identity gives

```text
QW(a_lambda,a_lambda)=QW(b_lambda,b_lambda).           (12)
```

Hence the seed Rayleigh value is intrinsically quadratic in the exterior tail. The target `(10)` is
therefore matched to the geometry of the problem: it asks for quadratic form control of the special
radial-prolate tail. A Davis--Kahan residual estimate instead asks for a linear strong-operator
bound and can lose a square root of the prolate concentration deficit.

This changes the positive open core from

```text
strong residual / gap at Mellin rate
```

to

```text
Rayleigh excess / gap at the squared Mellin rate.      (13)
```

The remaining nontrivial input is a lower bound `(9)` and a gap estimate in the **true** restricted
Weil form, obtained through source-specific bilinear tail control or a Schur complement.

## Relation to the spectral-floor branch

If the same comparison proves `epsilon_0(lambda_j)->0` on a cofinal sequence, then
`ccm-cofinal-weil-spectral-floor-criterion.md` already proves RH and determinant transfer is
unnecessary. The Rayleigh-excess theorem is valuable in the other case: it transfers the divisor
from the prolate seed while using only quadratic form information about its direction.

## Novelty and significance verdict

The angle inequality `(3)` is standard Rayleigh--Ritz theory. Its use with the exact growing Mellin
norm and the CCM exterior-tail identity gives a sharper route specification, but after erasing the
RH vocabulary it remains a textbook variational estimate. It is a bridge, not new scientific
knowledge.

## Lean status

**Superseded, 2026-08-03.**  Formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/CCMRayleighExcessAngle.lean`.  The previous decision anticipated
"an abstract finite-dimensional version of `(3)`"; the version built is **not** finite dimensional —
the spectral half is stated with `HasSum` over an arbitrary index type, so no finite-dimensionality
and no eigenbasis cardinality assumption enters.

- **`gap_mul_one_sub_le_rayleighExcess`** — equation `(4)`: with nonnegative spectral weights summing
  to one and every non-ground eigenvalue at least `Gap` above the bottom,
  `Gap * (1 - w i₀) ≤ r - eps_0`.  Proved by exhibiting the difference as a sum of manifestly
  nonnegative terms, so it needs no reordering and no positivity of the tail sum separately.
- **`norm_sub_smul_sq_eq`**, **`two_sub_two_mul_norm_le_norm_sub_smul_sq`**,
  **`exists_unit_norm_sub_smul_sq_eq`** — equation `(5)` in full: for unit vectors
  `‖g - c ξ‖² = 2 - 2 Re(c ⟪g,ξ⟫)`, the value `2(1 - |⟪g,ξ⟫|)` is a lower bound for every unit phase,
  and it is **attained** at `c = conj⟪g,ξ⟫ / |⟪g,ξ⟫|`.  The card writes `(5)` as an infimum "after
  choosing the phase"; both halves of that infimum are now proved, so `(3)` bounds a genuine
  attained minimum rather than an unproved infimum.
- **`projectiveDistSq_le_two_mul_excess_div_gap`** — equation `(3)`: the angle bound
  `‖g - c ξ‖² ≤ 2 delta / Gap` at the attaining phase.  The step `2(1-t) ≤ 2(1-t²)` uses
  `|⟪g,ξ⟫| ≤ 1`, which is Cauchy–Schwarz for unit vectors.
- **`tendsto_sqrt_of_tendsto_zero`** — equations `(6)`--`(8)`: the squared-rate hypothesis transfers
  to the unsquared projective distance, which is the square-root rate consequence `(7)`.
- **`rayleighExcess_le_of_lower_bound`** — equations `(9)`--`(10)`: any proved lower bound for the
  ground energy bounds the excess, so no two-sided estimate of the unknown eigenvalue is needed.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.

The bridge between the two halves is Parseval, `w i₀ = |⟪g, ξ⟫|²`, which is why the spectral
inequality is stated with the abstract ground weight and the angle bound with the overlap.

Not formalized, and not theorems of this card: the exterior-tail radical identity `(12)`, which is an
imported result of `ccm-weil-exterior-tail-quotient-gate.md`; and the growing Mellin evaluation
interface of `ccm-growing-aperture-mellin-determinant-transfer.md`, which consumes `(7)` rather than
proving it.

## Gates

- [x] quadratic Rayleigh-excess angle bound proved
- [x] exact squared Mellin rate derived
- [x] certified-lower-bound variant proved
- [x] compatibility with the quadratic exterior-tail identity established
- [x] Lean: spectral inequality `(4)` unconditional, arbitrary index type
- [x] Lean: projective distance `(5)` with both the bound and its attaining phase
- [x] Lean: angle bound `(3)` and square-root rate transfer `(7)` unconditional
- [x] Lean: certified-lower-bound variant `(9)`--`(10)` unconditional
- [ ] true Weil lower bound and even spectral gap
- [ ] source-specific radial-prolate Rayleigh-excess estimate `(10)`
- [ ] locally uniform normalized determinant convergence to `Xi`
