# Suzuki projective affine-secant tensor lift

- **ID:** `suzuki-projective-affine-secant-tensor-lift`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / FAILED-PLÜCKER POSITIVE SURVIVOR
- **Status:** `[PAPER-PROVED] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-homogeneous-projective-resolvent-plucker-lift.md`
- **Statement:** Plücker chord does not determine affine-sewn Suzuki response; correct exact carrier
  is gauge-covariant marked secant tensor with diagonal, symmetric-pair, alternating-pair, and
  homogeneous Neumann components.

## Goal

Hostile-test current `SUZUKI-PLUCKER-CHRISTOFFEL-DARBOUX-WELD` against exact affine sewing actually
used by jump kernel.  Derive division-free carrier for

```text
I_(alpha,beta)q=[beta q_alpha-alpha q_beta]/(beta-alpha).
```

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: exact algebra, gauge no-go, spectral decomposition, hostile audit
- [x] 2 → 3 formalized: every `[PROVED HERE]` theorem of this card is in Lean with clean axioms
- [ ] 3 → 4 publication-ready: standalone note and priority audit

## Conjecture under test

Current Plücker producer says homogeneous blade `(v,0) wedge (Av,1)` is complete source carrier.
Test invariance under numerator chart shift `B -> B+delta D`.  All Plücker minors remain unchanged,
but every quotient `q_lambda` and its affine intercept increase by `delta`.  If confirmed, Plücker
data are insufficient and marked affine chart must be retained.

## Attack algebra

Put

```text
u_alpha=Av-beta v,       u_beta=Av-alpha v,
n_lambda=B(u_lambda)+c,  d_lambda=D(u_lambda),
q_lambda=n_lambda/d_lambda.
```

Writing `x=Bv`, `X=BAv`, `y=Dv`, `Y=DAv`, expected exact numerator is

```text
I_(alpha,beta)q
=[(X+c)Y-(alpha+beta)xY+alpha beta x y]
 /[(Y-beta y)(Y-alpha y)].                             (T)
```

Unlike alternating Plücker chord, `(T)` has diagonal and symmetric tensor contributions.

## Theorem A: exact affine-secant tensor `[PROVED HERE]`

Let `alpha!=beta`, and assume `D(u_alpha),D(u_beta)!=0`.  With notation above,

```text
[beta q_alpha-alpha q_beta]/(beta-alpha)
 =Q_(alpha,beta)(v)/[D(u_alpha)D(u_beta)],              (1)

Q_(alpha,beta)(v)
 =(B(Av)+c)D(Av)
  -(alpha+beta)B(v)D(Av)
  +alpha beta B(v)D(v).                                (2)
```

Division-free form is

```text
beta [B(u_alpha)+c]D(u_beta)
-alpha[B(u_beta)+c]D(u_alpha)
=(beta-alpha)Q_(alpha,beta)(v).                        (3)
```

### Proof

Set `x=Bv`, `X=BAv`, `y=Dv`, `Y=DAv`, `Z=X+c`.  Then

```text
n_alpha=Z-beta x,     n_beta=Z-alpha x,
d_alpha=Y-beta y,     d_beta=Y-alpha y.
```

Direct expansion gives

```text
beta(Z-beta x)(Y-alpha y)-alpha(Z-alpha x)(Y-beta y)
=(beta-alpha)[ZY-(alpha+beta)xY+alpha beta xy],
```

which proves `(3)`, then `(1)--(2)` after division.

## Theorem B: Plücker gauge no-go `[PROVED HERE]`

For any scalar `delta`, replace `B` by `B_delta=B+delta D`.  Every alternating minor is unchanged:

```text
[B_delta,D](r,s)=[B,D](r,s).                           (4)
```

But

```text
q_lambda^delta=q_lambda+delta,
I_(alpha,beta)q^delta=I_(alpha,beta)q+delta.            (5)
```

Equivalently tensor numerator obeys exact covariance

```text
Q_delta=Q+delta (Y-beta y)(Y-alpha y).                 (6)
```

Therefore no construction depending only on Plücker blade `B wedge D` (even with `c,D` fixed)
can determine affine-sewn response.  It forgets additive affine chart which sewing explicitly
uses.

### Proof

Alternation gives `(D wedge D)=0`, proving `(4)`.  Numerator changes by `delta D(u_lambda)`, so
quotient changes by `delta`; affine weights sum to one, proving `(5)`.  Substitution
`x->x+delta y`, `X->X+delta Y` in `(2)` gives `(6)`.

## Theorem C: exact spectral tensor decomposition `[PROVED HERE]`

On finite simple diagonal block `Ae_i=t_i e_i`, write

```text
v=sum_i v_i e_i,   B(e_i)=b_i,   D(e_i)=d_i,
s_1=alpha+beta,    s_2=alpha beta.
```

Then

```text
Q=sum_i (t_i-alpha)(t_i-beta)b_i d_i v_i^2
  +sum_(i<j) v_i v_j {
      [2t_i t_j-s_1(t_i+t_j)+2s_2]/2
        *(b_i d_j+b_j d_i)
      -s_1(t_j-t_i)/2*(b_i d_j-b_j d_i)}
  +c sum_i t_i d_i v_i.                               (7)
```

Thus correct carrier contains:

1. diagonal tensor terms;
2. symmetric spectral-pair boundary products;
3. alternating Plücker pair products;
4. marked homogeneous Neumann term.

For opposite shifts `alpha=-beta`, `s_1=0`; entire alternating term vanishes while diagonal and
symmetric terms remain.  Exterior-only producer is maximally blind in this chamber.

### Proof

Expand `(2)` as sum over ordered `(i,j)`.  Coefficient of `b_i d_j v_i v_j` is

```text
t_i t_j-s_1 t_j+s_2.
```

Diagonal gives first line.  Pair `(i,j)` with `(j,i)` and split boundary products into symmetric
sum and alternating difference; sum/difference of coefficients are respectively

```text
2t_i t_j-s_1(t_i+t_j)+2s_2,
-s_1(t_j-t_i).
```

Term `cY` gives final homogeneous sum.

## Rank-one physical check `[PROVED HERE]`

If `Av=tv`, `B=L-KA`, and source equation gives

```text
e=(A-alpha)(A-beta)v,
c=K(e)=(t-alpha)(t-beta)K(v),
```

then `(1)` reduces exactly to

```text
I_(alpha,beta)q=L(v)/D(v).                             (8)
```

This matches direct rank-one quotient
`q_lambda=[L(v)-lambda K(v)]/D(v)`.  Plücker chord only sees slope `K(v)/D(v)` and cannot recover
intercept `(8)`.

## Scientific-method outcome

- **Conjecture tested:** homogeneous Plücker blade is complete affine-sewn source carrier.
- **Falsifier:** gauge `(4)--(5)`; rank-one intercept changes while blade does not.
- **Outcome:** conjecture falsified.
- **Strongest positive survivor:** exact marked affine-secant tensor `(2)` with decomposition `(7)`.
- **New frontier conjecture:** `SUZUKI-MARKED-SECANT-CD-WELD` — derive prime--Gamma Green identity
  whose Pick polarization factors tensor `(2)` together with global Xi deficit as positive Gram.

Finite resolvent-jet tomography from sibling card realizes arbitrary spectral vectors.  Bilinear
polarization of those filters now reconstructs every diagonal, symmetric, alternating, and
homogeneous entry in `(7)`.  Correct source test matrix lives in marked tensor space, not exterior
square alone.

## Novelty audit

Affine rational interpolation and tensor symmetrization are classical `[BRIDGE]`.  Corpus Plücker
lift proves exact projective chord but does not compare it to weighted affine intercept used in
jump sewing, perform gauge no-go `(4)--(6)`, or derive tensor decomposition `(7)`.  Candidate
novelty is Suzuki-specific correction and exact frontier replacement.  External priority remains
unverified.

## Lean status

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiProjectiveAffineSecantTensor.lean` proves:

- division-free and quotient affine-secant identities `(1)--(3)`;
- Plücker gauge invariance and marked tensor covariance `(4)--(6)`;
- explicit same-chord/different-affine-tensor no-go witness;
- two-mode symmetric/alternating decomposition and opposite-shift collapse;
- physical rank-one recovery `(8)`;
- field-generic core algebra plus the complex-linear-map cross identity used by Suzuki Fourier
  boundary observations.

Direct Lean check and targeted SOTA build pass.  Axiom audit reports only standard mathlib
foundations `[propext, Classical.choice, Quot.sound]`.

**Formalization complete (verified 2026-07-31).**  Every `[PROVED HERE]` statement of this card is
formalized: Theorem A `(1)`--`(3)` as `suzukiProjectiveAffineSecant_cross_identity` and
`suzukiProjectiveAffineSecant_quotient_identity`; Theorem B `(4)`--`(6)` as
`suzukiProjectiveMinor_affineGauge_invariant`, `suzukiProjectiveResponse_affineGauge_shift` and
`suzukiProjectiveAffineSecantTensor_gauge_covariance`, with the explicit witness
`suzukiProjectiveMinor_same_affineTensor_different`; Theorem C `(7)` as
`suzukiProjectiveAffineSecant_twoMode_pair_decomposition`,
`suzukiProjectiveAffineSecant_oppositeShift_pair_is_symmetric` and
`suzukiProjectiveAffineSecant_finite_spectral_sum`; the rank-one check `(8)` as
`suzukiProjectiveAffineSecant_rankOne_recovers_intercept`.  The Volterra boundary factorization
belongs to the successor conjecture `SUZUKI-MARKED-SECANT-CD-WELD`, not to any theorem stated
here, so it does not gate this card.

## Decisive tests

- `B -> B+delta D` must leave chord invariant but send right side `(T)` to itself plus `delta`.
- Rank-one physical specialization must recover affine numerator intercept `L(v)/D(v)`, not zero.
- Opposite shifts `alpha=-beta` must remove alternating pair coefficient but retain symmetric and
  diagonal terms; any exterior-only formula then fails visibly.
- Neumann constant `c=K(e)` must survive in marked homogeneous term `cY`.
- No division by characteristic allowed in core identity; quotient theorem adds explicit
  nonvanishing denominators only afterward.

## Door passport sketch

- **Door 1:** exact affine sewing and projective resolvent states already corpus-defined.
- **Door 2:** rational interpolation algebra is classical `[BRIDGE]`; candidate novelty is
  source-specific diagnosis that projective Plücker lift loses affine chart required by Suzuki weld.
- **Door 3:** finite exact algebra, no asymptotic/computation.
- **Door 4:** gauge transformation is decisive falsifier.
- **Door 5:** corrected tensor is exact boundary object whose Pick polarization must factor to
  prove jump positivity and RH.

## Log

- 2026-07-22 — Created after finite-jet tomography exposed mismatch between projective chord and
  affine-sewn jump response.
- 2026-07-22 — Exact marked secant formula, gauge no-go, spectral tensor decomposition, and
  rank-one physical check proved.  Plücker-only producer retired; tensor survivor promoted.
- 2026-07-22 — Core algebra, gauge no-go, two-mode split, and rank-one check formalized in Lean;
  SOTA targeted build and axiom audit pass.

### Lean progress — finite spectral sum FORMALIZED
`RHTower/Suzuki/SuzukiAffineSecantSpectralSum.lean` [PROVED HERE], standard axioms [propext, Classical.choice,
Quot.sound], builds clean, formal lint passed. Registered in the RHTower umbrella.
- `suzukiProjectiveAffineSecant_finite_spectral_sum` : with resolvent coordinates given by finite spectral
  sums `x=Σbᵢvᵢ, X=Σtᵢbᵢvᵢ, y=Σdᵢvᵢ, Y=Σtᵢdᵢvᵢ`, the marked affine-secant tensor equals
  `Σᵢ Σⱼ vᵢvⱼbᵢdⱼ(tᵢtⱼ−(α+β)tⱼ+αβ) + c·Σⱼtⱼdⱼvⱼ` — the double sum of per-mode-pair two-mode kernels plus
  the homogeneous c-channel. Generalizes the single-pair split `..._twoMode_pair_decomposition` to the
  whole finite spectrum (proof: `sum_mul_sum` bilinear expansion + per-term `ring`).

This discharges the "full finite spectral sum remain paper/source-level" item (card §Lean status): the
marked tensor's boundary-source reconstruction over the finite eigenmode decomposition is now formalized.
(Remaining out-of-scope items: the Volterra boundary factorization is analytic, and the ultimate RH
positivity goal is open.)

### Lean progress — `(7)`'s diagonal/pair split FORMALIZED

Audit of this card's numbered statements against its two modules
(`RHTower/Suzuki/SuzukiProjectiveAffineSecantTensor.lean`, `RHTower/Suzuki/SuzukiAffineSecantSpectralSum.lean`):
every statement has a declaration. One shape mismatch remained and is now closed.

`(7)` is displayed as a **three-part** decomposition — a per-mode diagonal part, genuine pair terms
over `i < j`, and the homogeneous `c`-channel — whereas `suzukiProjectiveAffineSecant_finite_spectral_sum`
absorbs the diagonal into the full double sum. Added in `RHTower/Suzuki/SuzukiAffineSecantSpectralSum.lean`
[PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `sum_sum_eq_diag_add_offDiag` : `∑ᵢ ∑ⱼ F i j = (∑ᵢ F i i) + ∑ᵢ ∑_{j ≠ i} F i j` — the general
  diagonal split of a finite double sum (proof: `Finset.add_sum_erase` termwise under
  `Finset.sum_add_distrib`).
- `offDiag_sum_eq_sub_diag` : the off-diagonal part as double sum minus diagonal.

Composing the split with the spectral sum puts `(7)` in its displayed shape: the diagonal collects
the `(tᵢ−α)(tᵢ−β)bᵢdᵢvᵢ²` terms, the off-diagonal part carries the spectral gaps `tⱼ − tᵢ` (a
diagonal term of the secant kernel contributes only through its own mode), and the `c`-channel is
untouched. No further gap on this card; gate 2 → 3 stands.
