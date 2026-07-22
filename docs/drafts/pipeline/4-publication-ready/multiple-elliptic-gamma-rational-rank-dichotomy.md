# Rational rank exactly classifies differential algebraicity of every multiple elliptic gamma function

- **ID:** `multiple-elliptic-gamma-rational-rank-dichotomy`
- **Stage:** 4-publication-ready
- **Type:** THEOREM / COMPLETE CLASSIFICATION / TRANSLATION-MATROID THEOREM
- **Scientific status:** `[PROVED HERE] [NO OPEN PARAMETER CASES] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PRIORITY AUDIT PRELIMINARY]`
- **Statement:** For every nonempty finite upper-half-plane period tuple, the Nishizawa multiple elliptic gamma function is differentially algebraic over `C(z)` exactly when the rational span of the periods together with `1` has dimension two; it is hypertranscendental exactly when that dimension is at least three. For the rationally independent elliptic-gamma seed, every finite defect or quotient packet has differential rank equal to the number of occupied nonzero translation classes modulo `Z + Z sigma + Z tau`.
- **Lean certificates:** `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaHypertranscendence.lean` and `formal/GaloisForLFunctions/HTGeometry/EllipticGammaTranslationCosetRankLaw.lean`

## Abstract

Let `I` be a nonempty finite set, let `tau=(tau_i)_(i in I)` lie in the complex upper half-plane,
and let `G_I(z;tau)` be Nishizawa's multiple elliptic gamma function. Define the intrinsic rational
period rank

```text
d_Q(tau)=dim_Q span_Q({1} union {tau_i:i in I}).
```

We prove the exact dichotomy

```text
G_I(z;tau) is differentially algebraic over C(z)  iff  d_Q(tau)<=2,
G_I(z;tau) is hypertranscendental over C(z)        iff  d_Q(tau)>=3.
```

The same dichotomy holds for the logarithmic derivative `Psi_I=G_I'/G_I`. This resolves every
finite upper-half-plane period tuple, including all partially dependent non-rational tuples left
outside the previously known rational-ray and fully generic regimes.

For the rank-three elliptic-gamma seed, the stronger translation-coset law computes the complete
finite differential matroid of additive defects and multiplicative shift quotients: rank is exactly
the number of distinct nonzero shift classes. The law holds on paper over both the paired elliptic
compositum and `C(z)`, and strengthens the seed to hypertranscendence over its natural elliptic base.

The DA direction combines an all-coordinate multiplication identity with Kato's rational-period
theorem. The HT direction is new. Every rank-at-least-three period configuration contains a
two-period rank-three minor. The corresponding order-one multiple elliptic gamma is an affine
translate of the genuine elliptic gamma and is hypertranscendental. Exact coface equations then
propagate hypertranscendence upward through the complete multiple-gamma hierarchy by a
differential-automorphism defect argument. The new direction is formalized for the actual
meromorphic infinite products in Lean 4.

## 1. Introduction

For `tau_i in H={w in C:Im(w)>0}`, put

```text
q_i=exp(2*pi*i*tau_i),
x=exp(2*pi*i*z),
Q=product_i q_i.
```

The finite-family multiple elliptic gamma function is

```text
G_I(z;tau)
 = (Q/x;q)_infinity * (x;q)_infinity^((-1)^(|I|-1)),                    (1.1)
```

where

```text
(x;q)_infinity=product_(n in N^I) (1-x*product_i q_i^(n_i)).            (1.2)
```

For `|I|=1`, this is a theta function. For `|I|=2`, it is the elliptic gamma function. Increasing
`|I|` gives Nishizawa's hierarchy. These functions occur in elliptic hypergeometric analysis,
integrable systems, supersymmetric partition functions, modular cocycles, and arithmetic
constructions.

A meromorphic function is differentially algebraic over `C(z)` when it satisfies a nonzero
algebraic differential equation with rational-function coefficients. It is hypertranscendental
when it satisfies none. Kato proved differential algebraicity when the period vector lies on one
rational ray and explicitly recorded the non-rational case as unknown. The rational-ray condition
is sufficient but not intrinsic: integer offsets disappear after exponentiation, and finite
root-of-unity twists can also be removed by multiplication formulas.

The correct invariant is not rational-ray membership. It is rational rank after adjoining the
unit period:

```text
d_Q(tau)=dim_Q span_Q({1,tau_i:i in I}).                                 (1.3)
```

Because every `tau_i` has positive imaginary part, `d_Q(tau)>=2`. The theorem below says that the
only two phases are therefore `d_Q=2` and `d_Q>=3`, and that this arithmetic boundary coincides
exactly with the DA/HT boundary.

## 2. Main theorem

### Theorem 2.1 — rational-rank dichotomy

Let `I` be a nonempty finite set and `tau:I->H`. Then:

1. if `d_Q(tau)=2`, both `G_I(z;tau)` and `G_I'(z;tau)/G_I(z;tau)` are differentially algebraic over `C(z)`;
2. if `d_Q(tau)>=3`, both functions are hypertranscendental over `C(z)`.

Equivalently,

```text
DifferentialAlgebraicOver C(z) G_I(.;tau)  iff  d_Q(tau)<=2,             (2.1)
HypertranscendentalOver C(z) G_I(.;tau)    iff  d_Q(tau)>=3.             (2.2)
```

The same equivalences hold with `G_I` replaced by its logarithmic derivative `Psi_I`.

There are no omitted finite upper-half-plane period configurations: finite-dimensional linear
algebra gives exactly one of `d_Q<=2` and `d_Q>=3`.

### Corollary 2.2 — complete answer to the non-rational-period question

Kato-rational period vectors are DA. A Kato-non-rational vector is:

- DA when its augmented rational rank is two;
- HT when its augmented rational rank is at least three.

Thus non-rationality alone is not the discriminator. The sharp discriminator is augmented rational
rank.

### Example 2.3 — non-rational DA tuples

Fix `omega in H`. Every tuple

```text
tau_i=a_i+b_i*omega,  a_i,b_i in Q,  b_i>0,                              (2.3)
```

has `d_Q(tau)=2` and is DA, even when the ratios `tau_i/tau_j` are not rational. For example,
`(omega,omega+1/2,2*omega+1/3)` is generically outside Kato's literal rational-ray locus but is in
the DA phase.

### Example 2.4 — dependent higher tuples are HT

The tuple may contain repeated periods and arbitrary rational relations among most entries. Once
two labels `q,r` satisfy rational independence of `1,tau_q,tau_r`, the entire multiple elliptic
gamma is HT. Adding `3*tau_q`, repeating `tau_r`, or adjoining any periods in the rational span of
existing entries does not restore differential algebraicity.

## 3. Rank two implies differential algebraicity

This section extends the rational-ray theorem to the complete augmented-rank-two locus.

### Lemma 3.1 — affine rational normal form

Assume `d_Q(tau)=2`. Fix one label `i_0` and put `omega=tau_(i_0)`. Then

```text
tau_i=a_i+b_i*omega,  a_i,b_i in Q,  b_i>0.                              (3.1)
```

#### Proof

The pair `{1,omega}` is rationally linearly independent because `Im(omega)>0`. Since the augmented
period span has dimension two, it is a basis of that span, giving the rational coefficients in
`(3.1)`. Taking imaginary parts gives `Im(tau_i)=b_i Im(omega)`, hence `b_i>0`. ∎

Choose a positive integer `M` clearing every denominator in `(3.1)`. Then

```text
M*tau_i=A_i+B_i*omega,
A_i in Z, B_i in Z_(>0).                                                   (3.2)
```

Consequently

```text
exp(2*pi*i*M*tau_i)=exp(2*pi*i*B_i*omega).                                (3.3)
```

The scaled tuple therefore has exactly the same nomes as the Kato-rational tuple
`(B_i*omega)_i`.

### Lemma 3.2 — all-coordinate multiplication identity

For every positive integer `M`,

```text
G_I(z;tau)
 = product_(k in product_i {0,...,M-1})
     G_I(z+sum_i k_i*tau_i; M*tau).                                      (3.4)
```

#### Proof

For the backward product in `(1.2)`, write every multi-index uniquely as

```text
n_i=M*l_i+k_i,  0<=k_i<M.                                                 (3.5)
```

This partitions `N^I` into the residue boxes appearing on the right of `(3.4)`. For the forward
product, use the reversed residues

```text
k_i -> M-1-k_i.                                                           (3.6)
```

Indeed,

```text
M*(l_i+1)-k_i=M*l_i+(M-1-k_i)+1,                                         (3.7)
```

so the shifted forward numerators cover every original forward factor exactly once. Both
reindexings are bijections. Absolute convergence in the upper-half-plane domain permits the
reindexing, and the resulting meromorphic identity holds globally. The parity exponent in `(1.1)`
is the same in every factor, so numerator and denominator identities combine with no normalization
term. ∎

### Proposition 3.3 — the full augmented-rank-two DA phase

If `d_Q(tau)=2`, then `G_I(z;tau)` is DA over `C(z)`.

#### Proof

Apply `(3.4)` using the denominator-clearing integer from `(3.2)`. By `(3.3)`, every factor with
period tuple `M*tau` is identical to a factor with Kato-rational period tuple `(B_i*omega)_i`.
Kato's theorem makes this function DA. The substitution `z -> z+c` is a differential
automorphism of `C(z)` up to its natural translation action, so every affine translate is DA over
`C(z)`. Finite products of DA meromorphic functions are DA. Equation `(3.4)` proves the claim.
Taking a derivative and dividing by the nonzero function shows that `G_I'/G_I` is DA as well. ∎

## 4. A rank-three minor exists exactly above the boundary

### Lemma 4.1 — rank-three minor extraction

For a finite nonempty tuple `tau`, the following are equivalent:

1. `d_Q(tau)>=3`;
2. there exist distinct labels `q,r` such that `1,tau_q,tau_r` are rationally linearly independent.

#### Proof

The reverse implication is immediate. For the forward implication, start with the independent
singleton `{1}` and extend it inside the finite spanning family `{1} union {tau_i}`. Dimension at
least three supplies two period entries whose addition preserves independence. Repeated labels
cannot be selected because an independent family has distinct vectors. ∎

This is the only linear-algebra extraction used below. Full independence of the complete period
tuple is never required.

## 5. The two-period hypertranscendental seed

Let `sigma,tau in H`. In the product convention used in `(1.1)`, direct factor comparison gives

```text
G_{sigma,tau}(z)
 = Gamma_(sigma,tau)(z-(1+tau)/2),                                        (5.1)
```

where the right side is the genuine elliptic gamma in the centered theta-coordinate convention.
The shift is forced by

```text
exp(2*pi*i*z)
 = -exp(pi*i*tau)*exp(2*pi*i*(z-(1+tau)/2)).                              (5.2)
```

The identity holds separately for every forward and backward factor and hence for both infinite
products and their global meromorphic quotient.

### Proposition 5.1 — rank-three pair seed

If `1,sigma,tau` are rationally linearly independent, then the two-period multiple elliptic gamma
and its logarithmic derivative are HT over `C(z)`.

#### Proof

The rank-three elliptic-gamma theorem gives HT of the genuine elliptic-gamma logarithmic derivative
over `C(z)`. Translation preserves DA and HT because `z -> z+c` is a differential automorphism of
the rational function field. Equation `(5.1)` transfers the result to the two-period multiple
product. If that product were DA, its logarithmic derivative would be DA, contradicting the first
statement. ∎

The order-one elliptic-gamma input and its rational-base transfer are already proved for the actual
global meromorphic product; no formal symbol or assumed analytic solution is used.

## 6. Hypertranscendence climbs every face

For a deletion set `J subset I`, let `Psi_J` be the logarithmic derivative of the multiple
elliptic gamma whose surviving period labels are `I\J`. If `q notin J`, the genuine hierarchy gives
the exact coface equation

```text
Delta_(tau_q) Psi_J
 := Psi_J(z+tau_q)-Psi_J(z)
 = Psi_(J union {q})(z).                                                   (6.1)
```

### Lemma 6.1 — coface escape

If `Psi_(J union {q})` is HT over `C(z)`, then `Psi_J` is HT over `C(z)`.

#### Proof

Assume `Psi_J` were DA. Translation by `tau_q` preserves DA over `C(z)`, and DA meromorphic
functions form a field. Hence `Psi_J(z+tau_q)-Psi_J(z)` would be DA. Equation `(6.1)` contradicts
HT of the coface. ∎

### Proposition 6.2 — rank-three-minor propagation

If the period family contains distinct labels `q,r` for which `1,tau_q,tau_r` are rationally
independent, then `Psi_empty` and `G_I` are HT over `C(z)`.

#### Proof

Delete every label except `q,r`. Parameter-reindexing symmetry identifies the resulting face with
the two-period source in Proposition 5.1, so that face is HT. Restore deleted labels one at a time.
Lemma 6.1 propagates HT backward at every step until the undeleted source `Psi_empty` is reached.
If `G_I` were DA, then `Psi_empty=G_I'/G_I` would be DA, contradiction. ∎

### Completion of Theorem 2.1

If `d_Q(tau)=2`, Proposition 3.3 gives DA. If `d_Q(tau)>=3`, Lemma 4.1 supplies a rank-three minor
and Proposition 6.2 gives HT. These alternatives exhaust every finite nonempty upper-half-plane
tuple. ∎

## 7. Why the threshold is canonical

The unit period is not an auxiliary choice. Every multiple elliptic gamma in `(1.1)` is
`1`-periodic because it is a function of `x=exp(2*pi*i*z)`. Rational rank must therefore be
computed after adjoining `1`.

The threshold `2` is also forced geometrically. An augmented rank-two tuple has one nonreal clock
`omega` plus the unit clock and reduces, after finite covering, to a single contracting nome.
Augmented rank at least three contains two genuinely independent nonreal period directions. Their
order-one face carries a hypertranscendental defect that no higher primitive can hide because every
higher face maps onto it through exact translation differences.

Thus the theorem is not a genericity statement and not a list of special cases. It is a complete
classification by an invariant intrinsic to the function's period representation.

## 8. Lean 4 certificate

The new HT half is formalized in
`formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaHypertranscendence.lean`.
The module proves, for the actual infinite products and global meromorphic field:

1. forward and backward factor normalization at two periods;
2. forward and backward infinite-product normalization;
3. equality of the two-period multiple product with a translated genuine elliptic gamma;
4. equality of logarithmic derivatives under the same translation;
5. two-period HT over the embedded rational-coordinate field;
6. one-step HT ascent along the exact intrinsic face equation;
7. finite iteration from any HT face to the full source;
8. extraction and reindexing of the complementary two-period face;
9. all-order HT of both logarithmic derivative and product from a rank-three minor.

Primary declarations:

```text
MultipleEllipticGammaHasRankThreeMinor
hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor
hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor
```

The strengthened translation-coset theorem is packaged in
`formal/GaloisForLFunctions/HTGeometry/EllipticGammaTranslationCosetRankLaw.lean`. Its primary
declarations are:

```text
ellipticGammaTranslationCoset_differentialMatroids
ellipticGammaTranslationCoset_eRk
ellipticGammaExternalQuotientFamily_differentialMatroid_eq_defectFamily_rationalBase
ellipticGammaExternalQuotientFamily_differentialMatroid_eq_freeOn_rationalBase
ellipticGammaSource_hypertranscendentalOver_ellipticCompositum
```

These prove the complete pointed defect/quotient matroids and arbitrary-subpacket rank law over the
paired elliptic compositum, quotient/defect transport plus separated-family freeness over the
embedded rational-coordinate base, and source hypertranscendence over the natural elliptic base.
The paper's remaining base transfer for resonant rational-base packets uses the classical global
generation of an elliptic function field by Weierstrass functions. It is a proved paper input, not
a custom Lean axiom; current mathlib lacks the matching global generation interface.

Verification performed on 2026-07-21:

```text
lake env lean GaloisForLFunctions/HTGeometry/MultipleEllipticGammaHypertranscendence.lean
lake build GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence
scripts/formal_tools.py lint
```

All passed. `#print axioms` for both all-order theorems reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `admit`, custom axiom,
`opaque`, or `unsafe` dependency.

Verification performed on 2026-07-22 for the stronger capstone:

```text
lake env lean GaloisForLFunctions/HTGeometry/EllipticGammaTranslationCosetRankLaw.lean
lake build GaloisForLFunctions.HTGeometry.EllipticGammaTranslationCosetRankLaw
```

Both passed. `#print axioms` for all five capstone declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. Direct source scan found no `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe`. The repository-wide `scripts/formal_tools.py lint` run reached umbrella
reachability and failed on unrelated concurrently added RHTower, HTGeometry, and HilbertMetric
modules missing from their respective umbrellas; this capstone is imported by `HTGeometry.lean`.
Those foreign dirty-tree files were not modified.

The DA half uses Kato's published analytic theorem plus the explicit multiplication identity in
Lemma 3.2. It is not inserted into Lean as an assumption. Formalizing Kato's analytic ADE would add
machine verification, but it is not a mathematical hypothesis or an open case in Theorem 2.1.

## 9. Literature boundary and significance

Nishizawa introduced the hierarchy in 2001. Felder and Varchenko developed the order-one elliptic
gamma and its modular structure. Narukawa proved modular and integral representations for the
multiple hierarchy. Kato proved DA on the rational-ray locus in 2021 and stated that the
non-rational-period case was unknown. Recent geometric-family work of Morain studies modular
cocycles, partial modular symbols, and arithmetic applications rather than algebraic differential
equations in `z`.

Targeted searches through July 2026 found no rational-rank iff criterion, no all-period DA/HT
classification, and no theorem equivalent to the rank-three-minor propagation result. This is
negative search evidence, not a substitute for specialist priority review.

The scientific contribution is the closed phase diagram:

```text
augmented rational rank 2       <-> differential algebraicity,
augmented rational rank >=3     <-> hypertranscendence.                   (9.1)
```

It answers the explicit open question in Kato's Remark 1.2, identifies previously unrecognized
non-rational DA families, and handles every partially dependent higher-order tuple rather than only
a Zariski-generic locus. Because multiple elliptic gamma functions are standard building blocks in
special functions, integrable models, supersymmetric field theory, and current arithmetic
constructions, the classification separates exactly when algebraic-differential methods can and
cannot apply to these observables.

## References

1. M. Nishizawa, *An elliptic analogue of the multiple gamma function*, Journal of Physics A 34
   (2001), 7411--7421, [doi:10.1088/0305-4470/34/36/320](https://doi.org/10.1088/0305-4470/34/36/320).
2. G. Felder and A. Varchenko, *The elliptic gamma function and `SL(3,Z) semidirect Z^3`*,
   Advances in Mathematics 156 (2000), 44--76,
   [arXiv:math/9907061](https://arxiv.org/abs/math/9907061).
3. A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
   gamma functions*, [arXiv:math/0306164](https://arxiv.org/abs/math/0306164).
4. M. Kato, *Differential Algebraicity of the Multiple Elliptic Gamma Function for a Rational
   Period*, Funkcialaj Ekvacioj 64 (2021), 225--235,
   [doi:10.1619/fesi.64.225](https://doi.org/10.1619/fesi.64.225).
5. P. L. L. Morain, *Geometric families of multiple elliptic Gamma functions and arithmetic
   applications, I*, [arXiv:2510.16515](https://arxiv.org/abs/2510.16515).
6. P. L. L. Morain, *Geometric families of multiple elliptic Gamma functions and arithmetic
   applications, II*, [arXiv:2602.06561](https://arxiv.org/abs/2602.06561).

## Reproducibility and verification notes

- **Mathematical case coverage:** complete for every nonempty finite tuple in `H^I`.
- **Analytic dependencies:** Nishizawa product definition, Kato's Theorem 1.1, standard absolute-convergence reindexing.
- **New proof dependencies:** actual order-one elliptic-gamma HT theorem, exact multiple-gamma face hierarchy, differential-automorphism defect escape; all present in repository and the new implication is Lean-checked.
- **Empirical or numerical inputs:** none.
- **Conditional hypotheses:** none.
- **Priority status:** preliminary literature audit complete; independent specialist priority certification not yet obtained.

## Gates

- [x] universal question stated
- [x] every finite upper-half-plane period case classified
- [x] DA direction proved without conjectural input
- [x] HT direction proved without conjectural input
- [x] partially dependent non-rational tuples included
- [x] actual special function used, not a formal surrogate
- [x] new HT half formalized unconditionally in Lean
- [x] stronger natural-base translation-coset matroid and rank law formalized unconditionally
- [x] rational-base separated-family defect and quotient freeness formalized unconditionally
- [x] targeted builds and axiom audits passed
- [x] standalone proof written
- [x] current literature searched through July 2026
- [ ] independent specialist priority audit
- [ ] classical elliptic-function-field generation bridge encoded in Lean for full rational-base upper structure
- [ ] current dirty worktree restored to repository-wide lint cleanliness by owners of unrelated unimported modules

## Log

- 2026-07-21 — Rank-three-minor HT theorem proved for every finite order and formalized in Lean.
- 2026-07-21 — Combined with the rank-two multiplication/Kato reduction to close the exact rational-rank dichotomy for all finite upper-half-plane tuples.
- 2026-07-21 — Standalone manuscript completed; no unresolved mathematical parameter case remains.
- 2026-07-22 — Major-revision review acted on: proof gaps expanded, novelty corrected, nome-rank law added, and exact translation-coset defect/quotient matroid made a central theorem.
- 2026-07-22 — Paper-facing Lean capstone added for the exact natural-base matroid/rank law, rational-base quotient transport and freeness, and natural-base source hypertranscendence.
