# Faithful Krein-index escape stratification inside one maximal HT power pro-field

- **ID:** `faithful-krein-index-escape-stratification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; generalized Nevanlinna index; spectral-route boundary
- **Statement:** In one exact maximal-HT differential-translation field and complete power
  pro-field, every finite Krein-index stratum lies in the compact-open closure of every higher
  finite-index stratum.  Hence no norm-continuous family of self-adjoint Fredholm operators can
  realize the faithful index on this class.

## Goal

The measured-index theorem proves that normalized traces miss finite off-line defects.  The remaining
escape route is a faithful integer index, as required by Weil, de Branges, Pontryagin-space, Connes
index, or Hilbert--Pólya implementations.  This theorem asks whether that faithful index can be a
stable continuous spectral invariant of the maximally HT carrier.

The answer is no.  Finite negative directions can escape to infinity without changing any
differential field or power level and without leaving a compact-open neighborhood of the lower-index
carrier.

## Setup

Fix `theta` in the comeager free set of the unit-residue canonical-product theorem in
`herglotz-full-translation-ht-krein-index-orthogonality.md`.  For every `k>=0`, that theorem supplies
a real entire order-one function `F_(theta,k)` whose negative logarithmic derivative

`M_(theta,k)=-F_(theta,k)'/F_(theta,k)`                        (1)

is a generalized Nevanlinna function of exact negative index `k`.  All `F_(theta,k)` have the same
maximal differential-translation field and the same complete power-normalization pro-field.

Fix `r>=1`.  Choose distinct nonzero real numbers `delta_1,...,delta_r` and, for large `T`, put

`t_(q,T)=delta_q+i(T+q)`, `1<=q<=r`,

`A_(r,T)(z)=prod_(q=1)^r`

` ((z-t_(q,T))(z-conj(t_(q,T))))/|t_(q,T)|^2`,                (2)

`F_(theta,k;r,T)=A_(r,T) F_(theta,k)`.                        (3)

The inserted upper-half-plane points are chosen away from the finitely many old nonreal zeros.

## Escape-stratification theorem `[PROVED HERE]`

For every `k>=0` and `r>=1`:

1. `F_(theta,k;r,T)` is real entire of exact order one.
2. Its negative logarithmic derivative has exact Krein index `k+r`.
3. Its full translation orbit is differentially algebraically independent.
4. For every `N>=1`,

   `P_N(F_(theta,k;r,T))=P_N(F_(theta,k))`,                    (4)

   where `P_N(F)=C(z)<T_h(F^N):h in C>`.  Thus the complete inverse power systems are literally
   equal.
5. As `T->infinity`,

   `F_(theta,k;r,T)->F_(theta,k)`                              (5)

   with every derivative uniformly on every compact subset of `C`.

Consequently, inside one fixed maximal-HT power pro-field,

`index-k stratum subset closure(index-(k+r) stratum)`          (6)

for every `k>=0` and `r>=1`.

### Proof

For one factor in (2),

`((z-t)(z-conj t))/|t|^2`

` =1-2 Re(t) z/|t|^2+z^2/|t|^2`.                             (7)

Here `Re(t_(q,T))=delta_q` is fixed while `|t_(q,T)|->infinity`.  Therefore every factor in (2),
and every one of its derivatives, tends uniformly on compacts to `1`; the finite product does too.
This proves (5).  Multiplication by the nonzero polynomial `A_(r,T)` preserves exact entire order
one and Schwarz reality.

Logarithmic differentiation gives

`-F_(theta,k;r,T)'/F_(theta,k;r,T)`

` =M_(theta,k)-A_(r,T)'/A_(r,T)`.                             (8)

Each conjugate zero pair in (2) adds one generalized pole of nonpositive type at the distinct
upper-half-plane point `t_(q,T)`.  The sum-of-kernels estimate gives at most `k+r` negative squares:
the old kernel has `k`, and each rational conjugate-pair summand has at most one.  Conversely, the
old `k` generalized upper-half-plane poles remain, and the `r` new distinct poles each force one
negative square by the Krein--Langer pole-count lower bound.  Thus the index is exactly `k+r`.

Since `A_(r,T)` is a nonzero rational base-field element,

`T_h(F_(theta,k;r,T)^N)`

` =T_h(A_(r,T)^N) T_h(F_(theta,k)^N)`.                        (9)

The first factor and its inverse lie in `C(z)`.  Equation (9) proves (4) generator by generator,
including all divisibility transitions.  At `N=1` it proves equality of the full
differential-translation fields.  Multiplication of each orbit coordinate by an invertible base
element preserves differential algebraic independence in both directions.  This proves all five
claims and (6). `QED`

## Functional-equation-even strengthening `[PROVED HERE]`

For the real even family `E_(theta,k)` of the parent theorem, use instead

`A_(r,T)^even(z)=prod_(q=1)^r`

` ((z^2-t_(q,T)^2)(z^2-conj(t_(q,T))^2))/|t_(q,T)|^4`.        (10)

Every factor is real even, equals `1+O_K(T^(-2))` with all derivatives on a fixed compact `K`, and
inserts the quartet

`{+-t_(q,T),+-conj(t_(q,T))}`.

There are two new upper-half-plane poles per quartet, so the exact index rises from `2k` to
`2(k+r)`.  Every field and power-level argument is unchanged.  Hence, with scalar functional-equation
symmetry imposed,

`index-2k stratum subset closure(index-2(k+r) stratum)`.       (11)

The functional equation preserves parity but supplies no compact-open separation between the
allowed index strata. `QED`

## Lower semicontinuity law `[PROVED HERE]`

Let generalized Nevanlinna kernels `K_n` converge entrywise on every fixed finite node set to `K`,
and let `kappa(K)` denote their negative-square index.  Then

`kappa(K)<=liminf_n kappa(K_n)`.                              (12)

Indeed, if `kappa(K)=k`, some finite Gram matrix of `K` has `k` strictly negative eigenvalues.
Those eigenvalues are separated from zero.  Entrywise convergence of that finite matrix and
continuity of Hermitian eigenvalues imply that the corresponding Gram matrices of `K_n` have at
least `k` negative eigenvalues for all sufficiently large `n`.  This proves (12).

The escape family realizes strict loss by every prescribed finite amount.  Negative index may
disappear at infinity under compact convergence, but it cannot appear spontaneously in the limit.

## Continuous-Fredholm obstruction `[PROVED HERE]`

Let `X_theta` be any compact-open carrier class containing all functions above.  There is no map

`mathcal A:X_theta -> B(H)_sa`                                (13)

with all three properties:

1. `mathcal A` is continuous from compact-open convergence to operator-norm convergence;
2. every `mathcal A(F)` is self-adjoint Fredholm and has finite-dimensional negative spectral
   subspace;
3. the negative Morse index of `mathcal A(F)` equals the exact Krein index of `-F'/F`.

Suppose such a map exists and fix an index-`k` carrier `F`.  Because the self-adjoint operator
`mathcal A(F)` is Fredholm, there is `epsilon>0` for which its spectral subspace in
`[-epsilon,epsilon]` has finite dimension `d`.  For a sufficiently small norm perturbation `B` of
`mathcal A(F)`, positive spectrum above `epsilon` cannot cross below zero.  The min--max principle
therefore bounds the negative Morse index of `B` by `k+d`.

Choose `r>d`.  By (5), the index-`k+r` carriers `F_(theta,k;r,T)` converge to `F`; continuity in
(13) makes their operators eventually lie in that norm neighborhood.  Property 3 gives negative
Morse index `k+r>k+d`, contradicting the bound.  Thus (13) cannot exist. `QED`

Equivalently, a faithful self-adjoint realization on this class must be discontinuous in the
compact-open carrier topology, or it must be non-Fredholm at the selector threshold; in the latter
case `0` lies in its essential spectrum.  A stable gapped Fredholm index cannot carry the exact
off-line count.

## Law extracted

**Faithful-index escape law.**  Maximal HT and every algebraic power normalization are insensitive
to negative directions escaping to spectral infinity.  The faithful integer index is lower
semicontinuous but has arbitrary finite upward jumps in every neighborhood of every finite-index
representative.  Hence it cannot be represented by a continuous Fredholm index on the natural
compact-open HT carrier topology.

This complements measured-index blindness:

- a measured or singular trace erases finite defects by normalization;
- a faithful count retains them, but is necessarily nonlocal, non-Fredholm, or discontinuous.

## Exact RH-route consequence

The theorem excludes implementations of Weil positivity, de Branges/Pontryagin realization,
Hilbert--Pólya, or Connes index theory that require all of the following:

1. the spectral object depends continuously in operator norm on compact-open carrier data;
2. the RH defect is the finite negative Morse/Fredholm index;
3. the spectral object remains Fredholm at index zero;
4. the construction uses only the unpointed maximal-HT power pro-field and scalar functional
   equation.

No such construction can distinguish the exact defect.  The result does **not** exclude the
classical routes themselves.  They can escape by using the distinguished Euler/source realization,
a topology that controls the divisor at infinity, a discontinuous faithful completion, or a
necessarily gapless/non-Fredholm operator.  In particular an actual Hilbert--Pólya operator with a
canonical arithmetic domain is not a compact-open functor of the unpointed HT carrier and is outside
the theorem.

## Parent-theory and novelty verdict

- `[SEARCH]` Langer--Luger--Matsaev explicitly show that a locally uniformly convergent sequence in
  a generalized Nevanlinna class `N_kappa` can have a limit in a lower class `N_kappa'`:
  `https://acta.bibl.u-szeged.hu/16396/`.
- `[SEARCH]` Generalized poles of nonpositive type and their relation to negative index are classical
  Krein--Langer factorization/realization theory; a modern factorization reference is
  `https://doi.org/10.1016/j.indag.2018.08.002`.
- `[SEARCH]` Local constancy/stability of the index for norm-continuous Fredholm families is standard
  Fredholm and spectral-projection theory.
- `[BRIDGE]` The all-level HT field equality and exact-index base family come from the separate
  power-pro-field and Herglotz theorems; the remote normalized factors are elementary.

The exact same-pro-field stratification and multi-route consequence are useful, but the proof is a
direct assembly of known negative-square convergence, rational divisor escape, and Fredholm index
stability.  It fails the parent-theory and anti-theatre novelty gates and is not new scientific
knowledge.

## Lean status

The tree contains finite Krein inertia, measured-index blindness, scalar polarization, and several
finite operator-index lemmas.  It does not formalize the analytic canonical-product family, local
uniform convergence of the remote factors, generalized Nevanlinna negative-square kernels as a
topological class, compact-open function spaces, or continuous self-adjoint Fredholm families.  All
of those layers occur in the exact theorem.  No partial stage-3 promotion is justified.

## Gates

- [x] 0 -> 1: faithful-index continuity question and arbitrary-jump construction isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] parent-theory attack and honest bridge classification
- [ ] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: optional route-boundary integration

## Log

- 2026-07-11 -- Proved arbitrary finite index escape by normalized remote conjugate pairs, preserving
  one maximal-HT field and every power level.
- 2026-07-11 -- Proved the functional-equation-even parity version, lower semicontinuity, and the
  continuous-Fredholm impossibility theorem.
- 2026-07-11 -- Downgraded after parent-theory comparison with convergence of generalized Nevanlinna
  functions and classical Fredholm-index stability.

## Lean status update (2026-08-19) — the card's theorem is formalized

The "Lean status" section above is stale.  Six new unconditional modules (all wired into
`GaloisForLFunctions.HTGeometry`, oleans built, `#print axioms` giving only
`propext, Classical.choice, Quot.sound`) formalize the escape stratification, the lower
semicontinuity law, and the continuous-Fredholm obstruction.

`formal/GaloisForLFunctions/HTGeometry/RemotePairEscapeGauge.lean`
- `remotePairFactor`, `remotePairGauge` — the normalized gauge `A_(r,T)` of equation `(2)`;
- explicit quadratic form, Schwarz reality, exact zero set;
- `neg_logDeriv_remotePairGauge` — `-A'/A` is exactly the Krein multi-pair carrier, equation `(8)`;
- `tendstoLocallyUniformly_finset_prod`, `remotePairGauge_tendstoLocallyUniformly`,
  `remotePairGauge_mul_iteratedDeriv_tendstoLocallyUniformly` — equation `(5)`, all derivatives;
- `evenRemotePairFactor`, `evenRemotePairGauge`, `evenRemotePairGauge_neg`,
  `evenQuartetPoints`, `evenRemotePairGauge_eq_remotePairGauge` — the functional-equation-even
  gauge `(10)` as an instance of the general one at the doubled quartet family, so `(11)` follows
  from the general index arithmetic.

`.../KreinIndexEscapeStratification.lean`
- `differentialAdjoin_range_pow_baseGauge_eq` — equation `(4)` at EVERY power level, fully general:
  a nonzero base-field gauge never changes the differential field generated by the `N`-th powers;
- `multiPairCarrier_append`, `escapeCarrier`, `escapeCarrier_exact_negativeSquares` — exact index
  `k + r`, statement `2`;
- `exists_coercive_bound_on_subspace`, `eventually_negOn_subspace_of_entrywise_tendsto`,
  `eventually_carrier_negativeSquares_witness` — the lower semicontinuity law `(12)`;
- `no_continuous_faithful_krein_index` — the continuous-Fredholm obstruction `(13)`.

`.../FaithfulIndexFredholmObstruction.lean`
- `NegIndexAtMost`, `HasCoerciveComplement` (the uniform-positivity-off-a-finite-dimensional-space
  form of "self-adjoint Fredholm at `0` with finite-dimensional negative spectral subspace"),
  `finrank_le_of_trivial_meet_of_sup_eq_top`, `negIndexAtMost_of_coerciveComplement` (index
  stability under small norm perturbation), `no_faithful_continuous_index_of_unbounded_witness`.

`.../KreinEscapeAnalyticFamily.lean`
- `kreinEscapeCarrier`, `kreinEscapeCarrier_exact_negativeSquares` — statement `2`;
- `kreinEscapeProduct = A_(r,T)·F_(θ,k)`, `kreinEscapeProduct_analytic`,
  `kreinEscapeProduct_orderOneEnvelope`, `kreinEscapeProduct_conj` — statement `1`;
- `neg_logDeriv_kreinEscapeProduct_eq`, `kreinEscapeProduct_eq_zero_iff`;
- `kreinEscapePoint`, `tendsto_normSq_inv_kreinEscapePoint`,
  `kreinEscapeProduct_escape_iteratedDeriv_tendstoLocallyUniformly` — statement `5` in the card's
  exact parameterization `t_(q,T) = δ_q + i(T+q)`.

`.../KreinEscapePowerFieldInvariance.lean`
- `remotePairGaugePoly`, `kreinEscapeTranslateFamily`, `surgeryProductTranslateFamily`,
  `kreinEscapeTranslateFamily_eq_mul`;
- `kreinEscapeTranslateFamily_differentialAdjoin_pow_eq` — statement `4`, equation `(4)`, for every
  `N`;
- `kreinEscapeTranslateFamily_differentialIndependent_iff` — statement `3`.

The base family, its exact index `k`, its order-one divisor package and the comeager-phase full
translation freeness are the pre-existing corpus modules `MovingCanonicalSurgery.lean`,
`MovingCanonicalFullTranslationFreeness.lean`, `MovingEvenCanonicalSurgery.lean` and
`PoleLocalizedExactNegativeSquares.lean`.
