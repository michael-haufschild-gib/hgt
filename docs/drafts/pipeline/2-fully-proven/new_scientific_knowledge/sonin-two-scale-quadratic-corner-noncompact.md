# Every two-scale Sonin Euler quadratic corner is noncompact

- **ID:** sonin-two-scale-quadratic-corner-noncompact
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` The proof is complete. The theorem closes the explicit
  two-prime product gap in `sonin-euler-metric-corner-noncompact.md`; scientific novelty still
  requires a broad operator-theory and Sonin/prolate literature audit.
- **Parent:** `sonin-euler-metric-corner-noncompact.md`
- **Statement:** For every cutoff `a>0` and every two scales `p,q>1`, if `Q_a` is the orthogonal
  projection onto the even Sonin space and

  `L_r=(1-Q_a)(U_r+U_r^{-1})Q_a`,

  then the quadratic cross-corner `L_p^* L_q` is noncompact. Equivalently, on the concrete
  archimedean Hardy--Titchmarsh line,

  `Pi_a M_(w_p) (1-Pi_a) M_(w_q) Pi_a`

  is noncompact for every `p,q>1`.

## Goal

The one-scale theorem proves that each lower Euler corner is noncompact, but that alone says nothing
about a product of two corners: noncompact operators can have compact, even zero, products. The
unresolved source question is whether two distinct prime scales can cancel after crossing the same
Sonin constraint.

They cannot. The common constraint admits paired exterior shell modes whose two crossed images
converge to the same normalized interior mode. This produces a nonvanishing quadratic matrix
coefficient modulo compact operators.

## Setup

Let

`H=L^2(R)^ev`.

For `a>0`, let `A_a` be multiplication by the indicator of `[-a,a]`, let

`R_a=F^{-1}A_aF`,

and let `Q_a` be the orthogonal projection onto

`S_a=ker(A_a) intersect ker(R_a)`.

For `r>0`, write

`(U_r f)(x)=sqrt(r) f(rx)`.

Then `U_r` is unitary, `U_r^{-1}=U_(1/r)`, and `U_rU_s=U_(rs)`. For `r>1`, put

`D_r=U_r+U_r^{-1}`,

`L_r=(1-Q_a)D_rQ_a`.

The parent theorem proves that every `L_r` is noncompact. The result below determines every entry of
their Calkin Gram matrix.

## Theorem `[PROVED HERE]`

For all `a>0` and `p,q>1`,

`L_p^*L_q = Q_a D_p(1-Q_a)D_qQ_a`

is not compact.

More precisely, there are bounded weakly-null sequences `f_n,k_n in S_a` such that

`<L_p^*L_q f_n,k_n> -> 1`.                                (1)

Consequently the image of `L_p^*L_q` in the Calkin algebra is nonzero for every ordered pair of
scales, including `p != q`.

## Brick 1 `[PROVED]`: a common interior shell has two exterior preimages

Let `m=min(p,q)>1`. Choose real numbers `c,d` with

`a/m < c < d < a`.                                       (2)

Let `v_n` be any orthonormal sequence of even functions supported in the fixed interior shell

`J={x : c<|x|<d}`.

For example, normalized indicators of disjoint symmetric sub-shells give such a sequence. Define

`g_n=U_(1/q)v_n`,

`h_n=U_(1/p)v_n`.                                        (3)

Both sequences are orthonormal. Their supports lie respectively in

`{qc<|x|<qd}` and `{pc<|x|<pd}`.

By (2), `qc>a` and `pc>a`; hence every `g_n` and `h_n` is outside the physical cutoff. Their supports
remain in fixed bounded shells.

The same is true of the further outward translates

`U_(1/q)g_n=U_(1/q^2)v_n`,

`U_(1/p)h_n=U_(1/p^2)v_n`,                               (4)

whose lower support radii are `q^2c>a` and `p^2c>a`.

## Brick 2 `[PROVED]`: every bounded exterior shell sequence is asymptotically Sonin

Let `z_n` be any orthonormal sequence supported in a fixed bounded shell outside `[-a,a]`. The
finite time-band operator

`A_a F 1_shell`

is compact. Therefore

`||R_a z_n||=||A_aFz_n|| -> 0`.

The two-projection correction estimate from the parent theorem gives

`||Q_a z_n-z_n|| -> 0`.                                  (5)

Apply (5) to all four exterior shell sequences in (3)--(4). Put

`f_n=Q_ag_n`,

`k_n=Q_ah_n`.                                             (6)

Then

`||f_n-g_n|| -> 0`, and `||k_n-h_n|| -> 0`.               (7)

Because bounded linear maps preserve weak convergence and orthonormal sequences are weakly null,
both `f_n` and `k_n` are bounded and weakly null in `S_a`.

## Brick 3 `[PROVED HERE]`: the crossed images converge to the same vector

The inward branches of the two dilations agree exactly:

`U_qg_n=v_n=U_ph_n`.                                     (8)

The vector `v_n` is supported inside `[-a,a]`. Since `range(Q_a) subset ker(A_a)`, the physical
subspace `range(A_a)` is orthogonal to `range(Q_a)`. Hence

`Q_av_n=0`, and `(1-Q_a)v_n=v_n`.                         (9)

For the outward branch of `D_qg_n`, (4)--(5) give

`||(1-Q_a)U_(1/q)g_n|| -> 0`.                            (10)

Combining (7)--(10), and using boundedness of `D_q`, yields

`||L_qf_n-v_n||
 <= ||D_q|| ||f_n-g_n|| + ||(1-Q_a)U_(1/q)g_n|| -> 0`.    (11)

The identical argument at scale `p` gives

`||L_pk_n-v_n|| -> 0`.                                   (12)

Thus the two different lower corners have asymptotically the same normalized image on paired
exterior Sonin modes.

## Brick 4 `[PROVED HERE]`: compactness contradicts the surviving matrix coefficient

By the adjoint identity and (11)--(12),

`<L_p^*L_q f_n,k_n>
 = <L_qf_n,L_pk_n>
 -> <v_n,v_n>
 = 1`.                                                    (13)

If `L_p^*L_q` were compact, it would send the bounded weakly-null sequence `f_n` to a norm-null
sequence. Since `k_n` is bounded, the left side of (13) would tend to zero. This contradiction proves
the theorem.

The argument is symmetric in `p,q`; it does not use an adjoint reduction from one order to the
other. The same interior sequence supplies both exterior preimages simultaneously.

## Source transport `[PROVED]`

On the archimedean Hardy--Titchmarsh line, let

`w_r(s)=|1-r^(-1/2-is)|^2
      =1+r^(-1)-r^(-1/2)(r^(is)+r^(-is))`.

Under the exact unitary transport in `HardyTitchmarshEulerConcrete.lean`, the lower metric corner

`C_r=(1-Pi_a)M_(w_r)Pi_a`

pulls back to

`-r^(-1/2)L_r`.

Therefore

`C_p^*C_q
 = Pi_a M_(w_p)(1-Pi_a)M_(w_q)Pi_a`

pulls back to the nonzero scalar multiple

`(pq)^(-1/2)L_p^*L_q`.

Unitary conjugacy and nonzero scalar multiplication preserve noncompactness. Hence every two-scale
quadratic Euler corner on the concrete source carrier is noncompact.

## Attack and exact scope

- `[PROVED]` The theorem includes `p=q`; it strengthens the already-known noncompact diagonal defect
  `L_p^*L_p`.
- `[PROVED]` It also includes `p != q`, which was the open case: two distinct noncompact corners do
  not acquire a compact product through the common Sonin constraint.
- `[PROVED]` The proof is internal to the actual even physical-and-Fourier Sonin carrier. It does not
  infer the result from the raw physical cutoff.
- `[PROVED]` The scales need not be prime or arithmetically independent. Every real `p,q>1` works.
- `[PROVED]` The result is quadratic and multiplicative in the corners, not another finite additive
  Calkin-independence theorem.
- `[OPEN CORE]` It does not determine whether a signed sum of several quadratic products can become
  compact. Entrywise nonvanishing of a Calkin Gram matrix is weaker than its matrix-level
  nondegeneracy.
- `[OPEN CORE]` It does not treat the inverse metric `w_p^(-1)`, a conditionally renormalized
  all-prime product, or the full archimedean/finite-place phase-ratio compensation.

## Significance gate

The parent theorem killed the linear one-prime compact seam but explicitly left open quadratic
two-prime cancellation. The present theorem closes that escape: the quadratic semicommutator of any
two canonical positive Euler metrics remains outside the compact ideal on the actual source carrier.

Thus neither a one-prime determinant nor its most immediate two-prime quadratic repair can use the
unsmoothed Sonin boundary. A viable all-place construction must introduce a cancellation that is not
visible in any individual quadratic Calkin Gram entry: genuinely global summation, nonlinear
archimedean compensation, a different polarization, or additional smoothing.

## Parent-theory and novelty gate

The abstract compactness contradiction is standard. The candidate scientific content is the
source-specific simultaneous-preimage fact: the physical/Fourier Sonin correction preserves two
scale-correlated exterior sequences strongly enough that every cross Gram entry survives in the
Calkin quotient.

Before promotion beyond `[NOVELTY UNVERIFIED]`, the audit must check:

1. Toeplitz--Hankel and truncated Wiener--Hopf product compactness criteria;
2. prolate/Sonin-space operator algebras and time--frequency limiting projections;
3. Connes--Consani quasi-inner local-factor constructions and their semicommutators;
4. limit-operator and localization theorems that may already imply (13) as a routine special case.

## Lean target

A faithful formalization should not introduce a proposition asserting the paired-shell limit. It
should construct the common interior shell and its two exterior dilation preimages, then prove:

1. both preimage sequences and their outward branches converge to the actual even Sonin carrier;
2. the two lower-corner images converge in norm to the same interior shell vector;
3. their inner product tends to `1`;
4. `adjoint(L_p) comp L_q` is noncompact;
5. the exact positive Euler and concrete Hardy--Titchmarsh transports.

The required analytic ingredients already exist in `SoninProjectionCorrection.lean`,
`SoninL2ShellNull.lean`, `SoninEvenCarrier.lean`, and `FiniteEulerCalkinIndependence.lean`. The missing
Lean work is the correlated two-scale shell construction and the quadratic operator packaging.

## Gates

- [x] 0 -> 1: exact two-scale operator and common-interior-shell mechanism isolated
- [x] 1 -> 2: complete paper proof above
- [ ] 2 -> 3: correlated shell sequence and quadratic transport not yet formalized
- [ ] 3 -> 4: primary-literature novelty audit and standalone exposition

## Next conjecture

`[CONJECTURE]` For distinct scales `r_1,...,r_m>1`, the Calkin Gram matrix

`([L_(r_i)^*L_(r_j)])_(i,j)`

is strictly positive over the Calkin algebra: for every nonzero coefficient vector `c`,

`sum_(i,j) conjugate(c_i)c_j L_(r_i)^*L_(r_j)`

is noncompact.

Since the displayed sum is `(sum_i c_iL_(r_i))^*(sum_j c_jL_(r_j))`, the existing finite Calkin
independence strongly suggests this statement, but the implication requires the C*-fact that
`T^*T` compact forces `T` compact. This conjecture may therefore collapse to a standard consequence
and is not claimed as new knowledge.

## Log

- 2026-07-10 — proved the two-scale theorem by paired exterior preimages of one common interior
  shell; no numerical or finite-coefficient experiment used.
