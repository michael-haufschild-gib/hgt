# Exact Essential Norm of Every Two-Scale Sonin Euler Quadratic Corner

- **ID:** sonin-two-scale-quadratic-corner-noncompact
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` The proof is complete and the sharp lower bound is
  formalized in Lean. The theorem closes the explicit two-prime product gap in
  `sonin-euler-metric-corner-noncompact.md`; scientific priority still requires a broader
  operator-theory and Sonin/prolate literature audit.
- **Parent:** `sonin-euler-metric-corner-noncompact.md`
- **Statement:** For every cutoff `a>0` and every two scales `p,q>1`, if `Q_a` is the orthogonal
  projection onto the even Sonin space and

  `L_r=(1-Q_a)(U_r+U_r^{-1})Q_a`,

  then the quadratic cross-corner has exact essential norm

  `||L_p^*L_q||_ess=1`.

  Equivalently, on the concrete
  archimedean Hardy--Titchmarsh line,

  `Pi_a M_(w_p) (1-Pi_a) M_(w_q) Pi_a`

  has essential norm `(pq)^(-1/2)` for every `p,q>1`.

## Goal

The one-scale theorem proves the stronger identity `||L_r||_ess=1`, but the norms of two factors do
not determine the norm or compactness of their product: noncompact operators can have compact, even
zero, products. The unresolved source question is whether two distinct prime scales can cancel after
crossing the same Sonin constraint.

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

The parent theorem proves that every `L_r` has essential norm one. The result below determines the
norm of every entry of their Calkin Gram matrix.

## Theorem `[PROVED HERE]`

For all `a>0` and `p,q>1`,

`||L_p^*L_q||_ess = 1`, where

`L_p^*L_q = Q_a D_p(1-Q_a)D_qQ_a`.

More precisely, there are bounded weakly-null sequences `f_n,k_n in S_a` such that

`<L_p^*L_q f_n,k_n> -> 1`.                                (1)

Consequently, for every compact `K`,

`1 <= ||L_p^*L_q-K||`.                                  (1')

The image of `L_p^*L_q` in the Calkin algebra therefore has norm at least one for every ordered
pair of scales, including `p != q`.

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

The same calculation is quantitatively sharp. Let `K` be any compact operator. Then `Kf_n -> 0`
in norm, while (13) gives

`|<(L_p^*L_q-K)f_n,k_n>| -> 1`.

Since `||f_n||,||k_n||<=1`, the operator norm inequality yields

`1 <= ||L_p^*L_q-K||`.                                  (14)

Taking the infimum over compact `K` proves

`||L_p^*L_q||_ess >= 1`.                                (15)

## Brick 5 `[PROVED HERE]`: the Calkin upper bound is also one

The parent theorem now determines the exact one-scale Calkin norm:

`||L_r||_ess=1` for every `r>1`.                         (16)

Let `pi` be the Calkin quotient. Submultiplicativity and the C-star identity give

`||pi(L_p^*L_q)|| <= ||pi(L_p)|| ||pi(L_q)|| = 1`.       (17)

Combining (15) and (17) yields the exact identity

`||L_p^*L_q||_ess=1`.                                   (18)

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

Unitary conjugacy preserves essential norm. Hence every two-scale quadratic Euler corner on the
concrete source carrier has the exact norm

`||C_p^*C_q||_ess=(pq)^(-1/2)`.                          (19)

## Attack and exact scope

- `[PROVED]` The theorem includes `p=q`; it strengthens the already-known noncompact diagonal defect
  `L_p^*L_p` to exact essential norm one.
- `[PROVED]` It also includes `p != q`, which was the open case: two distinct noncompact corners do
  not acquire a small Calkin product through the common Sonin constraint; every cross entry still
  has norm exactly one.
- `[PROVED]` The proof is internal to the actual even physical-and-Fourier Sonin carrier. It does not
  infer the result from the raw physical cutoff.
- `[PROVED]` The scales need not be prime or arithmetically independent. Every real `p,q>1` works,
  and the dilation-side essential norm is independent of both scales.
- `[PROVED]` The result is quadratic and multiplicative in the corners, not another finite additive
  Calkin-independence theorem.
- `[RESOLVED BY CHILD]` The matrix-level gap is closed for every injective finite prime family by
  `sonin-prime-quadratic-calkin-matrix-injectivity.md`: an arbitrary complex matrix combination of
  the prime Gram entries is compact if and only if its coefficient matrix is zero.
- `[OPEN CORE]` It does not treat the inverse metric `w_p^(-1)`, a conditionally renormalized
  all-prime product, or the full archimedean/finite-place phase-ratio compensation.

## Significance gate

The parent theorem killed the linear one-prime compact seam but explicitly left open quadratic
two-prime cancellation. The present theorem closes that escape sharply: the dilation-side quadratic
semicommutator of any two canonical positive Euler metrics lies at distance exactly one from the
compact ideal, and the source normalization records the exact arithmetic decay `(pq)^(-1/2)`.

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

## Lean realization

`formal/GaloisForLFunctions/RHTower/SoninEulerQuadraticCorner.lean` constructs the common interior
shell and both exterior preimages on the actual even Sonin carrier. It proves:

1. both preimage sequences converge in norm to their Sonin projections;
2. both crossed images converge to the same normalized interior shell vector;
3. a compact operator sends every bounded weakly-null sequence to a norm-null sequence;
4. for every compact `K`,

   `1 <= ||evenCentralSoninQuadraticCorner a p q hp hq-K||`;

5. every ordered dilation quadratic corner and every ordered positive Euler quadratic corner is
   noncompact.

The formal endpoints are
`one_le_norm_evenCentralSoninQuadraticCorner_sub_compact`,
`evenCentralSoninQuadraticCorner_not_isCompactOperator`,
`evenCentralPositiveEulerQuadraticCorner_eq_smul`, and
`evenCentralPositiveEulerQuadraticCorner_not_isCompactOperator`. The concrete source endpoints are
`archimedeanPrimeEulerQuadraticCorner_eq_unitaryPush` and
`archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator`.

Mathlib in this toolchain has the closed subspace of compact operators but no ready Calkin quotient
or essential-norm API. Thus Lean proves the sharp lower bound against **every** compact perturbation.
The matching upper bound `<=1`, obtained on paper from the one-scale Calkin partial-isometry formula,
remains to be encoded. The concrete Hardy--Titchmarsh quadratic operator and its noncompactness are
formalized, while its exact essential-norm value remains paper-level.

## Gates

- [x] 0 -> 1: exact two-scale operator and common-interior-shell mechanism isolated
- [x] 1 -> 2: complete paper proof above
- [ ] 2 -> 3: the sharp compact-distance lower bound and positive Euler noncompactness are formalized;
  the matching Calkin upper bound remains, while concrete Hardy--Titchmarsh quadratic noncompactness
  is encoded
- [ ] 3 -> 4: primary-literature novelty audit and standalone exposition

## Resolved multiplication law

`[PROVED BY CHILD]` The cross element `pi(L_p)^*pi(L_q)` is a partial isometry for every `p,q>1`.
If `m=min(p,q)`, its initial projection is the sum of the physical and Fourier shell projections
from `a*q/m` to `a*q`, and its final projection is the corresponding sum from `a*p/m` to `a*p`.
See `sonin-mixed-calkin-partial-isometry-law.md`.

The remaining multiplication question starts at three mixed Gram factors, where the intermediate
shell-overlap projection depends on three scales and need not collapse to one Gram entry.

## Log

- 2026-07-10 — proved the two-scale theorem by paired exterior preimages of one common interior
  shell; no numerical or finite-coefficient experiment used.
