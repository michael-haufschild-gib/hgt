# Euler observability deficit is paid by CCM relative negative index

- **ID:** `ccm-euler-observability-relative-index-allocation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the finite Euler observability determinant, the Jacobian rank theorem, and
  the signed-Cauchy realization of a rational relative determinant
- **Statement:** In any source-defined finite CCM realization whose scalar differential jet and
  active relative-determinant coordinates jointly retain all finite Euler directions, the Euler
  directions invisible to the scalar jet inject into the relative state. Consequently their
  dimension is bounded by the negative-square index of the relative logarithmic kernel.

## 1. Source coordinates and scalar observability

Let `lambda_1,...,lambda_k` be positive and linearly independent over `Q`, let

```text
x_i(s)=exp(-lambda_i s),
Delta=-sum_(i=1)^k lambda_i X_i partial_(X_i),              (1)
```

and let `B` be a rational germ regular at `X=0`. For an integer `r>=0`, define the scalar
`r`-jet observation

```text
O_r(B)=(B,Delta B,...,Delta^(r-1)B),                        (2)
```

with the empty tuple when `r=0`, and put

```text
rho_r(B)=rank_C d(O_r(B))_0.                                (3)
```

Thus `rho_r(B)` is the number of infinitesimal Euler directions visible in the chosen scalar
differential jet. Always

```text
rho_r(B)<=min(r,k).                                         (4)
```

When `B` is first-order faithful, the weighted Vandermonde computation in
`finite-euler-exact-differential-order-aperture-law.md` gives

```text
rho_k(B)=k,
ap_C(B(x_1,...,x_k))=k.                                    (5)
```

## 2. A source-defined relative state

Let

```text
C=(C_1,...,C_q):(C^k,0)->(C^q,C(0))                        (6)
```

be a holomorphic germ. In the CCM application, the `C_j` are the active normalized Fourier
residues of a relative determinant after a source-defined deformation by the `k` Euler
parameters. The active pole locations may depend on the external spectral aperture, but they are
distinct at the base point.

Call `(O_r(B),C)` **incidence-faithful at the source point** when

```text
rank_C d(O_r(B),C)_0=k.                                    (7)
```

This is the precise first-order condition saying that scalarization and relative spectral state
together lose no prime direction.

## 3. Exact observability-deficit allocation

`[PROVED]` Under `(7)`, the restriction

```text
dC_0 restricted to ker d(O_r(B))_0                         (8)
```

is injective. Consequently

```text
k-rho_r(B)
 =dim_C ker d(O_r(B))_0
 <=rank_C dC_0
 <=q,                                                      (9)
```

and hence

```text
k<=rho_r(B)+q<=r+q.                                        (10)
```

### Proof

If `u` belongs to the kernel of both `d(O_r(B))_0` and `dC_0`, then `u` belongs to the kernel of
the combined differential in `(7)`. Full rank of that differential makes its kernel zero, so
`u=0`. This proves injectivity in `(8)`. Rank-nullity for `d(O_r(B))_0` gives the equality in
`(9)`; the remaining inequalities and `(10)` follow immediately.

The point of `(9)` is that it counts only the scalar observability **deficit**. Directions already
visible in `O_r(B)` are not charged again to the relative state.

## 4. Relative determinant and negative-square payment

Suppose the state coordinates in `(6)` parameterize the `q` genuine residues of a rational
relative determinant

```text
R(z)=sum_(j=1)^q C_j/(d_j-z),                              (11)
```

at the base source point, where the `d_j` are distinct and real, every `C_j` is nonzero there,
and all zeros of `R` are real. Put

```text
M_R(w)=d/dw log R(-iw),
K_R(w,v)=(M_R(w)+conjugate(M_R(v)))/(w+conjugate(v)).       (12)
```

The signed-Cauchy decomposition in
`ccm-relative-logderivative-coordinate-negative-index-law.md` proves, on every nonempty open node
region in the right half-plane,

```text
ind_- K_R=q.                                                (13)
```

Combining `(9)` and `(13)` gives the mixed allocation law

```text
k-rho_r(B)<=ind_- K_R,                                     (14)
```

or equivalently

```text
k<=rho_r(B)+ind_- K_R.                                     (15)
```

Thus a scalar differential jet may transfer prime incidence into a relative determinant, but it
cannot make the missing incidence disappear: every source direction absent from the scalar jet
requires one independent active residue coordinate, and each such coordinate appears as one
relative negative square.

### Stratified residue law and nearby index birth

The active-coordinate hypothesis above is stronger than a full Fourier-coordinate response. Let

```text
c=(c_1,...,c_M):(C^k,0)->C^M                              (15b)
```

be the complete residue-coordinate germ, allowing some `c_j(0)=0`, and assume

```text
rank d(O_r(B),c)_0=k.                                     (15c)
```

Put `r_c=rank dc_0`. The proof of Section 3 gives

```text
k-rho_r(B)<=r_c.                                          (15d)
```

Choose `r_c` coordinate functions whose differentials are linearly independent. None of these
germs is identically zero. The complement of their zero sets is open dense in a sufficiently
small source neighborhood. At every point `a` in that complement, at least `r_c` residues are
active. If the source-deformed finite determinant remains in the self-adjoint real-zero class,
the relative index theorem gives

```text
ind_- K_(R,a)>=r_c>=k-rho_r(B).                           (15e)
```

Thus `(14)` has the following unconditional support-stratified replacement under `(15c)`:

```text
scalar observability deficit
  -> current active negative index,
     or quantized negative-index birth on an open dense set
        of arbitrarily small source deformations.          (15f)
```

The index at the base point need not already contain every tangent direction. A residue that
vanishes at the base but has nonzero first variation is a dormant channel; it becomes a genuine
pole and contributes one negative square immediately off its zero stratum. Consequently a
source-faithful cofinal topology must retain the residue support stratification, not only the
single integer index at the zeta point.

## 5. Finite-prime specialization

Let `S_P={p:p<=P}` and `k=pi(P)`. For a source-defined CCM family depending holomorphically on the
degree-one Euler parameters at the trivial source point, incidence faithfulness implies

```text
pi(P)-rho_r(B_P)<=ind_- K_(R,P).                            (16)
```

There are two boundary cases.

1. If `B_P` is a first-order-faithful rational Euler readout and its complete scalar jet is kept,
   then `(5)` gives `rho_k(B_P)=pi(P)` and `ap_C(B_P)=pi(P)`. The source has already paid the whole
   finite-prime incidence in scalar differential order. The relative negative index may still be
   needed for divisor transport, but it is not a second payment for the same first-order source
   directions.
2. If scalarization retains only `r` jet coordinates with `rho_r(B_P)<=r`, then

   ```text
   ind_- K_(R,P)>=pi(P)-r.                                 (17)
   ```

   Hence bounded scalar jet depth forces cofinally growing relative Pontryagin index in every
   incidence-faithful realization.

The prime cutoff `P`, the spectral aperture `lambda`, and the Galerkin window `N` are distinct
parameters. Equation `(16)` does not identify `pi(P)` with the number of CCM Fourier coordinates.
It becomes a statement about an actual CCM construction only after a source-defined map from the
Euler parameter germ to the ground-vector residues has been constructed and `(7)` has been
proved.

## 6. Combination with divisor-preserving convergence

Independently of Euler-source incidence, every locally uniform divisor-carrying CCM determinant
limit satisfies, for some fixed `delta>0`,

```text
ind_- K_(R,lambda,N)
 >=2 floor(delta log(lambda)/pi)+1.                         (18)
```

Equations `(16)` and `(18)` are two lower bounds on the same relative index only when the proposed
architecture actually identifies the source-deformed residue family with the divisor-carrying
CCM family. Under that identification, the positive joint carrier law is

```text
ind_- K_R
 >=max(
      pi(P)-rho_r(B_P),
      2 floor(delta log(lambda)/pi)+1
    ).                                                      (19)
```

No sum of the two terms is asserted: without a transversality theorem they may describe the same
state directions.

## 7. Orbit-sensitive source--divisor marking

The allocation theorem is necessary but not sufficient for RH. The finite
divisor--differential-aperture orthogonality law proves that for every nonzero rational base factor
`q`,

```text
ap_K(qf)=ap_K(f).                                           (20)
```

In the FE--Schwarz category, a symmetric orbit polynomial `Q_rho` can insert an arbitrary generic
off-critical quartet while preserving differential aperture, hypertranscendence, order-one
growth, the functional equation, and Schwarz reality. Therefore neither `(15a)` nor the active-pole
count `(13)` is by itself an RH selector. An external orbit factor can preserve the whole source
observability budget while changing the divisor.

The positive additional structure is a **pointed orbit-sensitive incidence**. A successful CCM
carrier must implement at least one of the following operational mechanisms:

1. an exact determinant identity ties the complete divisor to the marked Euler source, so
   multiplication by `Q_rho` leaves the admissible incidence space unless `Q_rho=1`;
2. an inertia-preserving transform carries the complete Euler Pick kernel, in which an off-line
   orbit changes the transverse negative index, into the restricted screw/Weil form;
3. a global trace or moment marking changes under `F->Q_rho F` and is proved to be determined by
   the weighted all-prime source plus archimedean completion.

Thus the genuine CCM carrier has three inseparable coordinates:

```text
prime-source visibility
  + relative spectral-state capacity
  + orbit-sensitive source--divisor marking.               (21)
```

The first is measured by differential aperture or source Jacobian rank, the second by relative
negative index, and the third by the complete determinant/kernel incidence. Polynomial gauge
invariance proves that the third cannot be reconstructed from either of the first two alone.

## 8. The exact open CCM incidence theorem

The missing source theorem is now finite and falsifiable.

At fixed aperture, `ccm-prime-source-ground-incidence-response.md` already constructs the Kato
ground-state response under the simple-isolated hypothesis. The theorem
`ccm-generic-ground-separating-incidence-law.md` proves that this response is injective on an open
dense separating locus, identifies its exceptional Gram-determinant seam, and proves eventual
preservation by the fixed-aperture Galerkin residue vectors.

The exact weighted-Laplace formula identifies the prime-correlation operators in the closed
finite-Weil form with the faithful symmetric compressed-shift carrier, up to fixed nonzero critical
weights.

`[OPEN CORE]` For coupled cutoffs `(P,lambda,N)`, prove that the true finite-Weil ground vector stays
outside the separating seam with the quantitative margin required by the chosen cofinal topology.
The fixed-aperture Galerkin theorem then passes the Kato response to the complete normalized
residue map

```text
Ctilde_(P,lambda,N):(C^(pi(P)),0)->C^(2N+1),                (22)
```

and prove that for a specified scalar source readout `B_P`,

```text
rank d(O_r(B_P),Ctilde_(P,lambda,N))_0=pi(P)                (23)
```

uniformly along a cofinal coupling. In addition, prove that the resulting determinant/kernel
incidence is orbit-sensitive in the sense of Section 7. Equation `(23)` is the required
source-to-spectral rank theorem; orbit sensitivity is the required transverse marking theorem.
If the rank in `(23)` is carried by residues already active at the base point, `(14)` gives the
base Pontryagin-index obligation. Otherwise `(15e)` gives quantized nearby index birth on the
residue-support strata. Positivity still requires the index-matched positive background or a
transport of the complete Euler Pick kernel into the screw spaces without changing inertia.

## 9. Attacks and exact scope

- Dropping `(7)` makes `(14)` false: a constant residue map may forget every source direction while
  retaining any prescribed number of poles.
- Counting poles without a source deformation does not transport prime incidence. The ordinary
  CCM ground vector at the zeta point alone supplies no Jacobian in the Euler parameters.
- Differential aperture and negative-square index are different invariants. They become entries
  of one budget only through the combined incidence differential `(7)`.
- When response enters through a residue vanishing at the base point, the correct payment is
  nearby index birth `(15e)`, not the base active-pole count.
- Even a full-rank combined incidence is transverse-blind unless its determinant or complete
  kernel marking changes under symmetric polynomial orbit insertion.
- A larger index does not imply positivity or RH. It only measures the relative negative carrier
  that the background must cancel.
- The proof of `(9)` is elementary finite-dimensional linear algebra, and `(13)` is standard
  generalized-Nevanlinna theory. This is a route bridge, not new scientific knowledge.

## 10. Lean decision

`RHTower/EulerSourceJetJacobian.lean` already formalizes the nonsingular weighted-Vandermonde
source differential. The tree does not contain the holomorphic CCM source deformation, its
ground-vector residue map, or the analytic signed-Cauchy kernel. Formalizing only `(9)` would be a
linear-algebra wrapper around the missing theorem `(21)`, so no Lean file is added.

## Gates

- [x] scalar observability rank defined
- [x] exact deficit injection into relative state proved
- [x] relative state dimension identified with logarithmic-kernel negative index
- [x] finite-prime mixed allocation law proved under incidence faithfulness
- [x] dormant residue directions converted into open-dense nearby index birth
- [x] prime, spectral-aperture, and Galerkin cutoffs kept distinct
- [x] combined divisor/source lower bound stated without double counting
- [x] orbit-sensitive source--divisor marking isolated as an independent obligation
- [x] fixed-aperture Kato source-to-ground response constructed under simple isolation
- [x] generic separating locus and its determinantal exceptional seam identified
- [x] exact closed-Weil prime correlations identified with the faithful shift carrier
- [x] fixed-aperture incidence passed to all sufficiently large Galerkin residue vectors
- [ ] prove the true cofinal ground state avoids the separating seam quantitatively
- [ ] prove its cofinal incidence rank `(23)`
- [ ] prove its determinant/kernel incidence is sensitive to every symmetric off-line orbit
- [ ] construct the index-matched positive background or an inertia-preserving Euler-to-screw map
- [ ] RH

## Lean status — 2026-08-16

`[FORMALIZED]` — module
`formal/GaloisForLFunctions/RHTower/CCM/CCMEulerObservabilityAllocation.lean`
(5 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

The card's section 3 is exact finite-dimensional linear algebra, and it is now proved in full:

- **`domRestrict_ker_injective`** — **equation (8)**: incidence faithfulness `(7)` (stated as
  triviality of the joint kernel) makes `dC` injective on `ker d(O_r(B))`.
- **`finrank_ker_le_finrank_range`** — **equation (9)**: therefore
  `dim ker d(O_r(B)) ≤ rank dC`.
- **`observability_allocation`** — **equation (10)**: rank–nullity turns this into
  `k ≤ ρ_r(B) + rank dC`, so the scalar observability *deficit* — and only the deficit — is charged
  to the relative state.
- **`index_ge_of_bounded_jet`** — **equation (17)**: a bounded scalar jet depth `ρ_r ≤ r` forces
  `q ≥ k − r`, the cofinally growing relative index.
- **`jet_rank_le`** — **equation (4)**: the scalar jet sees at most `min(r, k)` directions.

The same statements give `(15d)` verbatim for the stratified residue germ `c`, since the proof uses
only the triviality of the joint kernel.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the weighted Vandermonde faithfulness `(5)`;
- the signed-Cauchy relative index theorem `(13)` — the corpus already owns its kernel algebra in
  `RHTower/CCM/CCMRelativeLogDerivCoordinateIndex.lean` (card
  `ccm-relative-logderivative-coordinate-negative-index-law`);
- the residue-birth statement `(15e)` on an open dense set of deformations;
- the divisor-preserving convergence bound `(18)`.
