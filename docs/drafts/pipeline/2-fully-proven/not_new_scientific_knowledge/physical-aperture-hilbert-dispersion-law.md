# The oriented physical-aperture Hilbert metric and exact response-dispersion law

- **ID:** `physical-aperture-hilbert-dispersion-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NO-GO CLOSURE / FCRJ FRONTIER RECUT
- **Scientific status:** `[PROVED HERE] [SOURCE-SPECIFIC ASSEMBLY]`
  `[PARENT HILBERT GEOMETRY STANDARD] [NOT AN RH PROOF]`
- **Parents:** the corrected FCRJ response-saturation law, the physical prime-endpoint radical,
  and sharp mesh coercivity.
- **Statement:** the true hard-aperture geometry is the oriented centered-indicator embedding in
  the constants quotient of `L2`; its weighted Hilbert variance is exactly the corrected FCRJ
  endpoint energy.

## Goal

Construct the actual Hilbert metric seen by a moving physical aperture without discarding the
orientation of the response.  Then identify exactly what the RH-facing upper bound says in that
metric.

This card also closes two tempting but wrong alternatives:

1. the gap metric between support subspaces, which is discrete for hard cutoffs;
2. the projective/chordal metric between centered aperture lines, which identifies complements
   and therefore loses the sign needed by response joining.

## The true oriented aperture carrier

Let `(X, mu)` be a finite measure space with

```text
A = mu(X),   0 < A < infinity.
```

Work in the real Hilbert space `L2(X,mu)`.  For a measurable aperture `E`, define

```text
kappa_E = 1_E - mu(E)/A,
d_A(E,F) = ||kappa_E-kappa_F||_2.                              (AH1)
```

Equivalently, if `Q` is orthogonal projection away from the constant direction, then
`kappa_E=Q(1_E)`.  The sign is physical: inside the aperture is positive.  In particular,

```text
kappa_(E^c) = -kappa_E.                                       (AH2)
```

Complements are antipodes, not a gauge identification.

### Theorem AH1: exact quotient metric

For measurable apertures `E,F`,

```text
d_A(E,F) = inf_(r in R) ||1_E-1_F-r||_2,                     (AH3)

<kappa_E,kappa_F>
  = mu(E intersect F)-mu(E)mu(F)/A,                           (AH4)

||kappa_E||_2^2
  = mu(E)(A-mu(E))/A,                                         (AH5)

d_A(E,F)^2
  = mu(E symmetric_difference F)
      -(mu(E)-mu(F))^2/A.                                    (AH6)
```

Thus `d_A` is exactly the Hilbert quotient distance in

```text
L2(X,mu) / span{1}.
```

On proper apertures `0<mu(E)<A`, modulo null equality, it is a genuine metric.  On all
measurable sets its only additional identification is the single zero class
`empty_set ~ X`.  The resulting aperture image is closed in the mean-zero Hilbert space and is
therefore complete.

### Proof

The constant vector has squared norm `A`, and its pairing with `f` is `integral f`.  Hence

```text
Qf = f-(integral f/A) 1
```

is the orthogonal projection onto the mean-zero subspace.  Orthogonal projection gives `(AH3)`
and the triangle inequality.  Expanding the pairing of the two centered indicators gives
`(AH4)`; setting `F=E` gives `(AH5)`.  Polarization and

```text
mu(E symmetric_difference F)
  = mu(E)+mu(F)-2mu(E intersect F)
```

give `(AH6)`.

If `d_A(E,F)=0`, then

```text
1_E-1_F = (mu(E)-mu(F))/A
```

almost everywhere.  The left side takes only the values `-1,0,1`.  For two proper apertures the
constant on the right has absolute value strictly less than one, so it must be zero and `E=F`
almost everywhere.  Allowing the endpoint measures `0,A` introduces exactly
`empty_set ~ X`.

For completeness, suppose `kappa_(E_n)` converges in `L2`.  Pass to a subsequence on which
`mu(E_n)/A` converges to `alpha in [0,1]`.  Then the indicators `1_(E_n)` converge in `L2`.
An `L2` limit `u` of indicators satisfies `u^2=u` almost everywhere: the indicators converge in
`L1`, and their squares converge to `u^2` in `L1`.  Hence `u=1_E` almost everywhere for a
measurable `E`, and integration gives `mu(E)/A=alpha`.  The limit is `kappa_E`.

The square in `(AH6)` is not itself a metric.  For disjoint non-null `E,G` and `F=empty_set`,

```text
d_A(E,G)^2-d_A(E,F)^2-d_A(F,G)^2
  = 2mu(E)mu(G)/A > 0.
```

The norm, not the squared norm, is the metric.

## The weighted aperture-dispersion identity

The next theorem is stated first in its exact parent Hilbert form because no positivity or prime
hypothesis is needed.

### Theorem AH2: finite weighted Hilbert variance

Let `v_i` be a finite family in a real inner-product space, let `w_i` be real weights, and put

```text
W = sum_i w_i,
S = sum_i w_i ||v_i||^2.
```

Then

```text
||sum_i w_i v_i||^2
 = W*S - (1/2) sum_(i,j) w_i w_j ||v_i-v_j||^2.              (AH7)
```

If `W` is nonzero and `lambda_i=w_i/W`, this becomes

```text
||sum_i w_i v_i||^2/W^2
 = sum_i lambda_i ||v_i||^2
    -(1/2) sum_(i,j) lambda_i lambda_j ||v_i-v_j||^2.         (AH8)
```

If instead `sum_i w_i=0`, then

```text
sum_(i,j) w_i w_j ||v_i-v_j||^2
 = -2 ||sum_i w_i v_i||^2 <= 0,                              (AH9)
```

so squared Hilbert distance is conditionally negative definite, with equality precisely when
the weighted vector sum vanishes.

### Proof

Polarization gives

```text
2<v_i,v_j> = ||v_i||^2+||v_j||^2-||v_i-v_j||^2.
```

Multiply by `w_i w_j` and sum over the two indices.  Each of the first two radius sums is `W*S`,
while the doubled inner-product sum is

```text
2 <sum_i w_i v_i, sum_j w_j v_j>.
```

This proves `(AH7)`; `(AH8)` and `(AH9)` follow by normalization and `W=0` respectively.

Taking `v_i=kappa_(E_i)` makes `(AH7)` the exact aperture-dispersion identity.  For positive
weights normalized to sum one, the squared norm of the aperture barycenter is the radius moment
minus half the ordered pairwise metric dispersion.

## Exact geometry of equal physical cells

Let `X=(0,A)` with Lebesgue measure, let `0<c<A`, and put

```text
I_s = (s,s+c],   0 <= s <= A-c,
D = c(A-c)/A.
```

For `h=|s-t|`,

```text
d_A(I_s,I_t)^2 = 2 min(h,c),                                  (AH10)

<kappa_(I_s),kappa_(I_t)> = D-min(h,c).                       (AH11)
```

Indeed, both cells have measure `c`, their overlap has measure `max(c-h,0)`, and their symmetric
difference has measure `2min(h,c)`.  Hence for positive weights `lambda_i` summing to one,

```text
||sum_i lambda_i kappa_(I_(s_i))||^2
  = D-sum_(i,j) lambda_i lambda_j min(|s_i-s_j|,c).           (AH12)
```

The right side is automatically nonnegative.  Equality can occur for generic equal cells, for
example a weighted partition of `(0,A)`.  Therefore the prime-endpoint radical theorem remains a
genuine arithmetic input; the metric alone does not provide strictness.

## Exact FCRJ frontier

For each active physical prime `p`, let

```text
I_p=(alpha_p,beta_p],
kappa_p=1_(I_p)-|I_p|/A,
w_p=log(p)/p,
P_M=sum_p w_p kappa_p,
W_M=sum_p w_p,
lambda_p=w_p/W_M.
```

Define the normalized aperture dispersion defect

```text
Disp_M
 = sum_p lambda_p d_A(I_p,empty_set)^2
    -(1/2) sum_(p,q) lambda_p lambda_q d_A(I_p,I_q)^2.        (AH13)
```

Combining `(AH8)` with the already established corrected response identity gives

```text
D_M-R_M^sharp = ||P_M||^2 = W_M^2 Disp_M.                    (AH14)
```

Consequently, for every nonnegative budget `B_M`,

```text
R_M^sharp >= D_M-B_M
  iff Disp_M <= B_M/W_M^2.                                   (AH15)
```

This is the exact RH-facing recut: the remaining response lower bound is a near-maximal weighted
dispersion theorem for the oriented physical aperture cloud.

The physical prime-endpoint radical and mesh theorem give the dependency-closed positive side:

```text
Disp_M > 0                                                   (AH16)
```

for every nonempty active-prime set, and at an endpoint `t` with adjacent cell lengths `L_t,R_t`
and jump `j(t)`,

```text
Disp_M
 >= [L_t R_t/(L_t+R_t)] |j(t)|^2/W_M^2.                     (AH17)
```

If both adjacent lengths are at least `sigma`, then

```text
Disp_M >= sigma |j(t)|^2/(2W_M^2).                           (AH18)
```

Thus finite physical prime clouds have a strict, quantitatively submaximal dispersion.  RH asks
for the opposite-scale upper theorem showing that this positive defect is tiny.

## Wrong-metric no-go closure

### Support-subspace gap is discrete

If an aperture is modeled by the support subspace `L2(E)`, its orthogonal projection is
multiplication by `1_E`.  Therefore

```text
||P_E-P_F||_op = ||1_E-1_F||_infinity,
```

which is zero for null-equivalent apertures and one for every non-null symmetric difference.
This metric cannot see small hard-cutoff motion.

### Projective gap erases the response sign

For a proper aperture, let `Pi_E` project onto the unoriented line `R kappa_E`.  Its chordal/gap
distance is

```text
delta(E,F)
 = sqrt(1-<kappa_E,kappa_F>^2/(||kappa_E||^2||kappa_F||^2)).  (AH19)
```

It identifies `E` and `E^c`.  More decisively, the two equally weighted clouds

```text
(E,E)       and       (E,E^c)
```

have identical projectors, norms, and all projective gap data, while their oriented resultant
energies are respectively

```text
4||kappa_E||^2       and       0.
```

No theorem using only unoriented aperture subspaces can recover the FCRJ response.  The centered
oriented vector is the strongest positive survivor.

## Novelty and significance audit

- Orthogonal quotient metrics, Hilbert variance, conditional negative type, and the gap/chordal
  facts are standard parent Hilbert geometry.
- The exact oriented centered-indicator metric, the truncated equal-cell distance, its FCRJ
  dispersion specialization, and the two wrong-metric no-gos were absent from the live corpus.
- This is a source-specific structural theorem and the correct formal object.  It is not an
  externally new RH estimate and is not claimed as a scientific breakthrough.
- The exact new open core is an arithmetic upper bound on `Disp_M`; another abstract metric lemma
  would not advance it.

## Lean status and gates

- [x] 0 -> 1: exact source-pure object and wrong-metric hostile tests
- [x] 1 -> 2: dependency-closed paper proof `(AH1)`--`(AH18)`
- [ ] 2 -> 3: formalize the centered-indicator formulas, true Hilbert distance, weighted
      dispersion identity, and conditional-negative-type corollary
- [ ] connect the generic metric identity to the concrete clipped-prime endpoint definitions
- [ ] prove a genuinely new arithmetic upper bound on `Disp_M`

## Log

- 2026-07-18 -- Built the oriented quotient metric, proved the exact weighted dispersion law,
  retired support-subspace and projective gap metrics, and recut the FCRJ endpoint energy as the
  positive dispersion defect `(AH14)`.
