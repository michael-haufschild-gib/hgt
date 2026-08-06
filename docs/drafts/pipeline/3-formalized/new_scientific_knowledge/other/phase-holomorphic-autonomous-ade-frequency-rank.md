# Phase-holomorphic autonomous-ADE frequency rank

- **ID:** `phase-holomorphic-autonomous-ade-frequency-rank`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CROSS-OPERATOR TRANSDUCTION
- **Scientific status:** `[PAPER-PROVED] [FORMALIZED] [NOVELTY UNVERIFIED]`
- **Formal status:** `[FORMALIZED]` — `(6)` is unconditional in Lean 4, axiom-clean
- **Novelty status:** no exact predecessor found in the targeted primary-source audit; do not claim
  novelty before independent expert proof and a broader literature review
- **Statement:** For a quasiperiodic function with a holomorphic phase observable, the rational
  frequency rank is at most its minimal autonomous algebraic-differential order. The equation may
  be implicit and singular.

## Setup

Let

```text
A_rho={z in (C*)^r: exp(-rho_j)<|z_j|<exp(rho_j) for every j}   (1)
```

be a polyannulus containing `T^r`. Let `omega_1,...,omega_r` be rationally independent real
numbers and let `F` be holomorphic on `A_rho`. On a sufficiently narrow horizontal strip put

```text
f(t)=F(exp(i omega_1 t),...,exp(i omega_r t)).                 (2)
```

Write the convergent Laurent expansion

```text
F(z)=sum_(m in Z^r) a_m z^m.                                  (3)
```

Let

```text
Lambda_F=span_Z {m:a_m!=0},
s=rank_Z Lambda_F.                                             (4)
```

Assume that `n` is the least order of a nonzero autonomous algebraic-differential equation for
`f`:

```text
P(f,f',...,f^(n))=0,   P in C[Y_0,...,Y_n].                   (5)
```

## The theorem

`[PAPER-PROVED]` Under `(1)`--`(5)`,

```text
rank_Q Gamma(f)=s<=n.                                         (6)
```

No equation solved for the highest derivative and no initial-value uniqueness are assumed.

## 1. Time differentiation is a torus derivation

Define

```text
delta=sum_(j=1)^r i omega_j z_j partial_(z_j),
F_k=delta^k F.                                                (7)
```

Then

```text
f^(k)(t)=F_k(exp(i omega t)).                                 (8)
```

Every polynomial identity among time jets extends to the whole polyannulus. Indeed, if

```text
P(f,...,f^(q))=0,                                            (9)
```

then `P(F_0,...,F_q)` vanishes on the dense real orbit in `T^r`, hence on the product torus. The
product torus is a uniqueness set for a polyannulus: hold `r-1` unit-circle variables fixed and
apply the one-variable identity theorem in the remaining annulus, then iterate through the
variables. Thus

```text
P(F_0,...,F_q)=0 on A_rho.                                  (10)
```

The converse follows by restriction to the orbit. Minimal autonomous order can therefore be read
from the phase functions `F_k`.

## 2. Minimal differential order is the all-jet transcendence degree

Put

```text
L=C(F_k:k>=0) subset M(A_rho).                               (11)
```

Minimality of `n` says that

```text
F_0,...,F_(n-1) are algebraically independent over C.        (12)
```

Choose an order-`n` relation of minimal positive degree in `Y_n`. Its separant does not vanish
identically:

```text
P_n(F_0,...,F_n)!=0,    P_n=partial P/partial Y_n.            (13)
```

Otherwise `P_n` would be a lower-degree order-`n` identity, contradicting the choice of `P`.
Applying `delta` to `(10)` gives

```text
sum_(j=0)^n P_j(F_0,...,F_n) F_(j+1)=0.                      (14)
```

Solving for the unique occurrence of `F_(n+1)` yields

```text
F_(n+1) in C(F_0,...,F_n).                                  (15)
```

The field on the right is now `delta`-stable: the derivative of each generator lies in it.
Induction puts every higher `F_k` in this field. Since `F_n` is algebraic over the independent
lower packet `(12)`,

```text
trdeg_C L=n.                                                 (16)
```

This is the algebraic transduction half of the theorem.

## 3. The all-jet fibre detects the active Laurent lattice

Define the multiplicative symmetry subgroup

```text
H={h in (C*)^r:h^m=1 for every m in Lambda_F}.               (17)
```

It is an algebraic subgroup of complex dimension `r-s`. Fix `x in T^r`. Suppose `y` is close to
`x` and

```text
F_k(y)=F_k(x) for every k>=0.                                (18)
```

The two holomorphic functions

```text
t |-> F(exp(i omega t)x),
t |-> F(exp(i omega t)y)                                    (19)
```

have identical Taylor series at zero. They agree on their common strip and hence for every real
`t`. Kronecker density gives

```text
F(ax)=F(ay) for every a in T^r.                              (20)
```

Put `h=y/x`. The holomorphic function `z |-> F(hz)-F(z)` on a smaller polyannulus vanishes on the
product torus, hence vanishes identically. Laurent uniqueness now gives

```text
a_m(h^m-1)=0 for every m,                                   (21)
```

so `h in H`. Conversely, `(17)` and `(3)` show that multiplication by every `h in H` fixes `F`
and all `F_k`. Therefore the common all-jet level-set germ at `x` is exactly

```text
xH,   of complex dimension r-s.                             (22)
```

## 4. Noetherianity turns the infinite observation into finite algebraic rank

In the local analytic ring at `x`, let

```text
I_x=(F_k-F_k(x):k>=0).                                      (23)
```

Noetherianity supplies finitely many indices `k_1,...,k_N` generating this ideal. Their common
level-set germ still has dimension `r-s` by `(22)`. The holomorphic fibre-dimension theorem then
shows that the map

```text
z |-> (F_(k_1)(z),...,F_(k_N)(z))                           (24)
```

has differential rank at least `s` at a nearby regular point. Some `s` coordinate functions in
`(24)` have independent differentials there. Their image contains a complex-open set, so those
`s` phase jets satisfy no nonzero polynomial relation. Hence

```text
trdeg_C L>=s.                                                (25)
```

Combining `(16)` and `(25)` gives `s<=n`.

Finally, rational independence of the `omega_j` makes

```text
m |-> m dot omega                                            (26)
```

injective on `Z^r`. The Bohr spectrum in `(2)` is exactly `{m dot omega:a_m!=0}`, so its generated
rational frequency rank is the lattice rank `s`. This completes `(6)`.

## Sharpness

Let `omega_1,...,omega_n` be rationally independent and `a_j!=0`. For

```text
F(z)=sum_(j=1)^n a_j z_j,
f(t)=sum_(j=1)^n a_j exp(i omega_j t),                       (27)
```

the active lattice has rank `n`, while

```text
prod_(j=1)^n (D-i omega_j) f=0                              (28)
```

has order `n`. The Vandermonde matrix recovers the `n` exponentials from the lower `n` jets, and
exponential-polynomial uniqueness makes those exponentials algebraically independent. No
lower-order autonomous equation exists. Equality is therefore attained in `(6)`.

## Hostile audit and surviving frontier

The theorem eliminates every standard transversely holomorphic quasiperiodic, toric, or pole-free
abelian-phase construction as a counterexample to the sharp frequency/order bound.

It does **not** silently promote time-strip holomorphy to phase holomorphy. If the rational basis is
Liouville, decay in `|m dot omega|` need not imply decay in `|m|`; a Bohr hull may be a protorus or
have only a transversely continuous observable. The surviving attacks are therefore:

1. a finite-rank protorus with non-finitely-generated character group;
2. a torus observable that is holomorphic along the dense time orbit but not transversely
   holomorphic;
3. a genuinely wild singular-chart hull.

No exact counterexample of these types was found.

## Hypertranscendence consequence

If a phase-holomorphic carrier has active lattice rank `s`, then every autonomous algebraic
differential equation has order at least `s`. In particular, no fixed order can annihilate a
sequence of such carriers whose active ranks tend to infinity. This is a quantitative
cross-operator transduction from Laurent support to differential complexity.

## Literature and novelty audit

1. G. C. O'Brien, *The frequencies of almost periodic solutions of almost periodic differential
   equations*, J. Austral. Math. Soc. **17** (1974), 332--344,
   <https://doi.org/10.1017/S1446788700017092>. O'Brien proves fewer than `p` frequencies for a
   regular autonomous system in `R^p`; this neither gives the complex half-dimensional bound nor
   handles singular implicit ADEs.

2. M. Abate, *Iteration theory, compactly divergent sequences and commuting holomorphic maps*,
   Ann. Scuola Norm. Sup. Pisa **18** (1991), 167--191,
   <https://www.numdam.org/item/ASNSP_1991_4_18_2_167_0.pdf>. Proposition 2.16 proves the adjacent
   toral-rank bound for relatively compact iterates on a taut Stein manifold by total reality. It
   does not state the Laurent-support/all-jet-stabilizer theorem above.

Targeted searches found no primary source for the exact statement `(6)`. Its proof is short and
uses standard ingredients, so the conservative status is `[NOVELTY UNVERIFIED]`, not a novelty
claim.

## Lean status

`[FORMALIZED]` Equation `(6)` is proved unconditionally in Lean 4 as

```text
GaloisForLFunctions.HTGeometry.rank_bohrFrequencyModule_le_of_realAutonomousAnnihilator
```

in `formal/GaloisForLFunctions/HTGeometry/BohrFrequencyRankLaw.lean`, together with the equality
half

```text
GaloisForLFunctions.HTGeometry.rank_bohrFrequencyModule_eq_rank_activeLattice
```

`#print axioms` on both gives only `propext`, `Classical.choice`, `Quot.sound`: no `sorry`, no
added axiom, no hypothesis interface.  The same holds for the minimality-free form
`rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator` and for the sharpness family
`sharpness_linearObservable`, `not_realAutonomousAnnihilator_linearObservable`.

The hypotheses are the weakest reading of `(1)`--`(5)`: `F` holomorphic on the polyannulus,
`ω` rationally independent, and a nonzero autonomous relation of order `n` holding *along the real
time axis only*.  Minimality of the order is not assumed: an equation free of the top derivative is
an equation of lower order, so the order can always be lowered until the top derivative is present.

Sharpness `(27)`--`(28)` is formalized as well: the exponential sum `∑_j a_j e^{i ω_j t}` with
rationally independent frequencies and no vanishing coefficient has frequency rank exactly the
number of frequencies, satisfies the linear equation of `∏_j (X − i ω_j)`, and satisfies no
autonomous algebraic differential equation of lower order.

Two ingredients of the paper proof were replaced by shorter unconditional arguments rather than
formalized: the Laurent expansion (the active lattice is defined by torus Fourier coefficients,
which mathlib owns) and the local Noetherian fibre-dimension step `(23)`--`(25)` (the differential
rank is bounded below by a Fourier-multiplier computation on the logarithmic coordinate
derivatives).  Neither replacement weakens the statement.

No numerical computation was used in this paper proof.

## Gates

- [x] exact theorem and hypotheses
- [x] singular implicit ADE allowed
- [x] dense-orbit identity extension proved
- [x] all-jet stabilizer identified
- [x] finite-jet reduction proved
- [x] equality family proved
- [x] transversely rough falsifier class isolated
- [x] targeted primary-source audit
- [ ] independent expert proof and broad novelty audit
- [x] unconditional Lean formalization

## Log

- 2026-07-17 -- Proved during programme-2 sharp-frequency research. An initial overclaim of
  equality for every holomorphic phase was killed: holomorphic function fields may have
  transcendence degree greater than the phase dimension. The surviving theorem is the sharp and
  sufficient inequality `s<=n`; equality is retained only for the exponential-polynomial family.

## Lean formalization plan and ledger

The theorem splits into five independent layers.  Each is stated below with its
Lean home; the layers already built are marked.

1. **Frequency rank of the active lattice** — the last paragraph of the proof,
   equation `(26)`.  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/CharacterLatticeFrequencyRank.lean`:
   - `rank_span_int_eq_rank_span_rat` — inside a rational vector space the
     integer span of a set has the same rank as its rational span.  One
     direction is the inclusion of the integer span into the rational span
     together with `IsLocalization.rank_eq` for `ℤ ⊆ ℚ`; the other picks a
     rational basis inside the set and observes that it stays integrally
     independent, by `LinearIndependent.iff_fractionRing`;
   - `ratCharacterDetuning`, `injective_ratCharacterDetuning` — rational
     independence of the frequency family is exactly injectivity of the
     rational detuning functional; the proof clears denominators with a common
     multiple of the coordinate denominators;
   - `rank_span_characterFrequencySet` — for a rationally independent family,
     the rational rank of the frequencies produced by a set of integer
     characters is the integer rank of the lattice that set generates.

2. **Dense-orbit identity extension**, equations `(9)`--`(10)`.  `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/PolyannulusTorusUniqueness.lean`:
   - `logAnnulus`, `isConnected_logAnnulus`, `isPreconnected_logAnnulus` — the
     annulus is the exponential image of a convex strip;
   - `tendsto_smallRotation`, `frequently_eq_zero_of_eqOn_circle` — the unit
     circle accumulates at `1`, so a function vanishing on it vanishes
     frequently in the punctured neighbourhood;
   - `eqOn_zero_logAnnulus` — the one-variable identity theorem on the annulus;
   - `polyannulus`, `unitTorus`, `mixedAnnulus`, `eqOn_zero_mixedAnnulus` and
     **`eqOn_zero_polyannulus_of_eqOn_zero_unitTorus`** — the product torus is
     a uniqueness set for the polyannulus, proved by releasing one coordinate
     at a time;
   - `eqOn_polyannulus_of_eqOn_unitTorus` — the two-function form.

   `formal/GaloisForLFunctions/HTGeometry/TorusOrbitPolyannulusUniqueness.lean`
   closes the passage from the real orbit:
   - `torusOrbitPoint`, `circleCoords`, `circleCoords_finiteClockPhasePoint` —
     the multiplicative realization of the additive phase flow, through
     `fourier 1`;
   - `unitTorus_subset_range_circleCoords` — every point of the multiplicative
     torus is realized, by its argument;
   - `unitTorus_subset_closure_range_torusOrbitPoint` — Kronecker density
     transported multiplicatively from the corpus theorem
     `dense_range_finiteClockPhasePoint`;
   - `isOpen_polyannulus` and
     **`eqOn_zero_polyannulus_of_eqOn_zero_orbit`** — a holomorphic function on
     the polyannulus vanishing along the real orbit vanishes identically.
     This is exactly equation `(10)`.

3. **The torus derivation and the jet identity**, equations `(7)`--`(10)`.
   `[DONE]`
   `formal/GaloisForLFunctions/HTGeometry/TorusDerivationJets.lean`:
   - `phasePoint`, `phaseStrip`, `phasePoint_mem_polyannulus` — the horizontal
     strip of complex times whose phase point stays in the polyannulus;
   - `coordDeriv`, `torusDerivation` (`δ = Σ_j i ω_j z_j ∂_j`),
     `analyticOnNhd_torusDerivation`, `analyticOnNhd_torusDerivation_iterate` —
     the derivation preserves holomorphy, so every time jet is again a phase
     observable;
   - `fderiv_apply_eq_sum`, `hasDerivAt_phasePoint`, **`deriv_phaseFunction`**
     (equation `(7)`) and **`iteratedDeriv_phaseFunction`** with its real form
     `iteratedDeriv_phaseFunction_ofReal` (equation `(8)`).

   `formal/GaloisForLFunctions/HTGeometry/PhaseJetRelationTransfer.lean`:
   - `analyticOnNhd_mvPolynomialEval`, `analyticOnNhd_polynomialEval₂` — a
     polynomial expression in analytic functions is analytic;
   - `phaseJet`, `phaseJetEval`, `analyticOnNhd_phaseJetEval`;
   - `RealAutonomousAnnihilator` — an autonomous relation of order `n` holding
     along the real time axis.  This is the weakest reading of `(5)`, hence the
     strongest form of the theorem;
   - **`realAutonomousAnnihilator_iff_phaseJetEval_eq_zero`** — equations
     `(9)`--`(10)`: an autonomous relation along the real orbit is exactly a
     polynomial identity among the phase jets on the whole polyannulus.

   The corpus already owns the separant step
   (`AutonomousSeparant.exists_minimal_with_separant`) and the jet-field layer
   (`DifferentialIndependence`, `JetPrefixPolynomial`).

4. **The active lattice, its stabilizer, and the all-jet level set**,
   equations `(17)`--`(22)`.  `[DONE]`

   The Laurent expansion is *not* needed.  Every use of the coefficients `a_m`
   is through the torus, so the active lattice is defined by the **Fourier
   coefficients of the restriction of `F` to the product torus** — the same
   numbers, since the torus Fourier coefficient of a function holomorphic on
   the polyannulus is its Laurent coefficient.  Mathlib owns the multivariate
   torus Fourier theory in `Mathlib.Analysis.Fourier.AddCircleMulti`
   (`UnitAddTorus.mFourier`, `mFourierCoeff`, the Hilbert basis `mFourierBasis`).
   This replaces the missing Laurent layer entirely: Mathlib has the
   Cauchy--Goursat theorem for an annulus but no Laurent expansion, in one or
   several variables.

   `formal/GaloisForLFunctions/HTGeometry/ActivePhaseLattice.lean`:
   - `eq_of_mFourierCoeff_eq` — Fourier uniqueness: two continuous functions on
     the product torus with the same coefficients are equal, since the
     monomials are a Hilbert basis of `L²` and a continuous function is
     determined by its class;
   - `fourier_neg_point`, `fourier_add_point`, `mFourier_add_point`,
     `mFourier_neg_point`, `mFourier_apply_zero` — the character laws in the
     *point* variable, which Mathlib states only in the index variable;
   - `torusRestriction`, `continuous_torusRestriction`, `activeCoeff`,
     `activeSupport`, **`activeLattice`** — equation `(4)`;
   - **`eqOn_polyannulus_of_activeCoeff_eq`** — the active coefficients
     determine the phase observable.  This is the Laurent-uniqueness step of
     `(21)`, combined with layer 2;
   - `torusScale`, `torusScale_mem_polyannulus`, `analyticOnNhd_comp_torusScale`,
     `circleCoords_add`, `torusRestriction_comp_torusScale`;
   - **`mFourierCoeff_translate`** — translation multiplies the `m`-th Fourier
     coefficient by the character `m`.  Proved from add-invariance of the Haar
     measure of the torus; no integrability hypothesis is needed, since both
     sides of the substitution and of pulling out the constant are unconditional;
   - `activeCoeff_comp_torusScale` — the same law for active coefficients;
   - **`eqOn_comp_torusScale_iff`** — equations `(20)`--`(21)`: a torus point
     fixes the phase observable exactly when every active character is trivial
     on it.  The symmetry group of a phase observable is the annihilator of its
     active lattice, which is `(17)` and the `(22)` inclusion `xH ⊆` level set.

   `formal/GaloisForLFunctions/HTGeometry/AllJetLevelSet.lean` closes `(22)`:
   - `eqOn_of_iteratedDeriv_eq` — two functions holomorphic on a connected open
     set with the same jets at an interior point agree.  Proved from
     `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` and
     `analyticOrderAt_eq_top`, then propagated by the identity theorem;
   - `convex_phaseStrip`, `isPreconnected_phaseStrip`,
     `analyticOnNhd_phaseFunction` — the time strip is convex, and the
     quasiperiodic function is holomorphic on it;
   - `torusScaleL`, `coordDeriv_comp_torusScale`,
     **`torusDerivation_comp_torusScale`** — multiplicative translation
     commutes with the torus derivation, because the vector fields `z_j ∂_j`
     are translation invariant;
   - `torusDerivation_congr`, `phaseJet_congr`, `phaseJet_comp_torusScale` —
     the jets of a translated observable are the translates of its jets;
   - `iteratedDeriv_phaseFunction_comp_torusScale_zero` — the `k`-th jet of the
     translated quasiperiodic function at time zero is `F_k` at the translating
     torus point;
   - **`eqOn_polyannulus_of_phaseJet_eq`** — equation `(19)`: equal phase jets
     give equal quasiperiodic functions, hence equality along the whole real
     orbit, hence on the polyannulus;
   - **`phaseJet_eq_iff_mFourier_eq_one`** — equation `(22)`: two torus points
     have the same values of every phase jet exactly when their difference
     annihilates every active character.  The all-jet level set through a torus
     point is its coset under the annihilator of the active lattice.

5. **The fibre-dimension step**, equations `(23)`--`(25)`.  `[IN PROGRESS]`

   The plan avoids the local Noetherian reduction of the paper.  Let `d` be the
   maximal dimension of the span of the jet differentials.  If `d < r`, pick `d`
   jets with independent differentials at a point of maximal rank; near that
   point every jet differential lies in their span, so by the implicit function
   theorem the common fibre contains a nonconstant curve along which every jet
   is constant — contradicting the finiteness of the all-jet level set, which is
   `(22)` when the active lattice has full rank.  Hence `d = r`, so `r` jets
   have independent differentials, hence are algebraically independent.

   The algebraic half of that is built:
   `formal/GaloisForLFunctions/HTGeometry/AlgebraicIndependenceFromDifferentials.lean`:
   - `mvPolynomial_eq_zero_of_eqOn_zero_isOpen` — a polynomial vanishing on a
     nonempty open subset of `ℂ^r` is zero.  Polynomial functions are entire and
     `ℂ^r` is connected, so the several-variable identity theorem propagates the
     vanishing, and `MvPolynomial.funext` finishes;
   - `mvPolynomial_eq_zero_of_hasStrictFDerivAt_equiv` and
     `mvPolynomial_eq_zero_of_hasStrictFDerivAt_injective` — at a point where
     the differential is injective the map is open, so a polynomial relation
     would vanish on an open set of the target.  In finitely many variables
     injective implies invertible;
   - **`mvPolynomial_eq_zero_of_family_hasStrictFDerivAt`** — a finite family of
     functions whose assembled differential is injective at a point satisfies no
     nonzero polynomial relation near that point.

   The differentiated relation, equation `(14)`, is built:
   `formal/GaloisForLFunctions/HTGeometry/TorusDerivationLeibniz.lean`:
   - `coordDeriv_add`, `coordDeriv_mul`, `coordDeriv_const`,
     `torusDerivation_add`, `torusDerivation_mul`, `torusDerivation_const` —
     the torus derivation is additive, kills constants and obeys the Leibniz
     rule on the functions holomorphic on an open set;
   - **`torusDerivation_eval_mvPolynomial`** — the chain rule: a polynomial
     expression in holomorphic functions is differentiated through the partial
     derivatives of the polynomial;
   - `torusDerivation_phaseJet` — the derivation shifts the jet index;
   - `jetRelationEval`, `analyticOnNhd_jetRelationEval`, and
     **`torusDerivation_jetRelationEval`** — equation `(14)`: differentiating a
     polynomial relation among the first `N` phase jets replaces each jet by
     its successor, weighted by the corresponding partial derivative.

   The ambient algebra in which transcendence degree is measured is built:
   `formal/GaloisForLFunctions/HTGeometry/PolyannulusFunctionDomain.lean`:
   - `isPreconnected_polyannulus` — a polyannulus is a product of annuli, hence
     connected;
   - `eqOn_zero_of_mul_eqOn_zero` and
     **`eqOn_zero_or_eqOn_zero_of_mul_eqOn_zero`** — on a connected open set the
     holomorphic functions have no zero divisors: if a product vanishes and one
     factor is nonzero somewhere, the other vanishes near that point, hence
     everywhere by the identity theorem;
   - `analyticSubalgebra`, `analyticRestrict` — the restrictions to an open set
     of the functions holomorphic on a neighbourhood of it, as a `ℂ`-subalgebra
     of the functions on that set;
   - **`isDomain_analyticSubalgebra`** and its polyannulus instance — that
     subalgebra is an integral domain.  This is the algebra in which the phase
     jets live and in which `Algebra.trdeg` will be measured.

   The bridge to `AlgebraicIndependent` is built:
   `formal/GaloisForLFunctions/HTGeometry/PhaseJetAlgebra.lean`:
   - `analyticEvalHom`, `analyticEvalHom_aeval` — pointwise evaluation is a
     `ℂ`-algebra homomorphism, so a polynomial relation in the algebra is a
     pointwise polynomial relation;
   - `algebraicIndependent_analyticSubalgebra_iff`, `phaseJetElem`,
     **`algebraicIndependent_phaseJetElem_iff`** — algebraic independence of
     phase jets is exactly the absence of a nonzero polynomial vanishing
     identically on the polyannulus;
   - **`le_of_algebraicIndependent_of_not_algebraicIndependent`** — the counting
     step: an independent family of `m` jets together with the dependence of
     every family of `n + 1` jets gives `m ≤ n`.

   **The transcendence-degree route is not needed.**  Differentiating the
   relation in the *coordinate* directions rather than along `δ` turns the whole
   argument into linear algebra over the gradients:

   - a vanishing polynomial relation `Q(F_{k_0},…,F_{k_N}) = 0` gives
     `∑_i Q_i(F) ∇F_{k_i} = 0` at every point, so at a point where the separant
     `Q_N(F)` is nonzero the top gradient lies in the span of the lower ones;
   - iterating `(14)` and differentiating each iterate puts *every* gradient
     `∇F_k` in the span of `∇F_0,…,∇F_{n-1}`, so the differential rank of the
     whole jet family is at most `n` wherever the separant is nonzero;
   - the differential-rank half of `(23)`--`(25)` produces a point where the
     rank is at least `s`.  Comparing the two gives `s ≤ n` with no field
     theory at all.

   The linear-algebraic machinery for this is built:
   `formal/GaloisForLFunctions/HTGeometry/CoordDerivChainRule.lean`:
   - **`coordDeriv_eval_mvPolynomial`** — the chain rule for a coordinate
     derivative;
   - `gradientVec`, `gradientVec_eval_mvPolynomial` — a polynomial relation
     differentiates to a linear relation among the gradients;
   - **`sum_smul_gradientVec_eq_zero`** — an identically vanishing polynomial
     relation gives a vanishing linear combination of the gradients, with the
     partial derivatives of the relation as coefficients.

   The shift operator that generates the iterated relations is built:
   `formal/GaloisForLFunctions/HTGeometry/JetShiftPolynomial.lean`:
   - `jetShift` — the polynomial operation that differentiating a jet relation
     performs, taking a relation in `N` jets to one in `N + 1` jets;
   - **`jetRelationEval_jetShift`** — the jet shift computes the derivative of a
     jet relation, which is `(14)` in operator form;
   - **`pderiv_last_jetShift`** — the shift preserves the leading coefficient:
     the partial derivative of the shifted relation in its top variable is the
     renamed partial derivative of the original in its own top variable.  So a
     relation whose separant is nonzero at a point yields one relation per jet,
     all with nonvanishing leading coefficient there;
   - `jetShiftIterate` and `jetRelationEval_jetShift_eq_zero` — every iterated
     shift of an identically vanishing relation vanishes identically.

   `jetShiftIter`, `jetRelationEval_jetShiftIter_eq_zero` and
   **`eval_pderiv_last_jetShiftIter`** iterate the shift: every iterate of a
   vanishing relation vanishes, and every iterate has the *same* leading
   coefficient value.  Indexing the iterate as `Fin (N + m + 1)` rather than
   `Fin (N + 1 + m)` keeps `Fin.last (N + m)` definitionally in range.

   The gradient-span induction is built:
   `formal/GaloisForLFunctions/HTGeometry/JetGradientSpan.lean`:
   - `jetGradientSpan` — the span of the gradients of the first `n` phase jets
     at a point;
   - **`gradientVec_top_mem_jetGradientSpan`** — one step: a relation with
     nonvanishing separant puts the top gradient in the span of the lower ones,
     by splitting the differentiated relation with `Fin.sum_univ_castSucc` and
     dividing by the separant;
   - **`gradientVec_mem_jetGradientSpan_of_relation`** — the induction: *every*
     jet gradient lies in the span of the first `n`.  This is the upper bound
     `differential rank ≤ n` wherever the separant is nonzero.

   The field of constants of the derivation is identified:
   `formal/GaloisForLFunctions/HTGeometry/TorusDerivationConstants.lean`:
   - `phaseJet_eq_zero_of_torusDerivation_eq_zero` — all higher jets of a
     derivation-killed observable vanish;
   - **`eq_const_of_torusDerivation_eq_zero`** — for rationally independent
     frequencies a phase observable killed by the torus derivation is constant
     on the polyannulus.  The constants of `δ` are exactly `ℂ`, which is what
     rational independence buys, and is the input to any argument that
     normalizes a `δ`-stable annihilator.

   Still to add: the differential-rank lower bound `≥ s`, the reduction of the
   general case to a full-rank active lattice, and the assembly into `(6)`.

   **Route note for the lower bound.**  The level-set statement `(22)` is proved
   for pairs of *torus* points.  Extending it to a torus point and a nearby
   polyannulus point needs the scaling law `activeCoeff (F ∘ S_h) m = h^m a_m`
   for `h` in the polyannulus rather than on the torus.  That extension does
   *not* need the Laurent expansion either: both sides agree for `h` on the
   torus by `activeCoeff_comp_torusScale`, so torus uniqueness forces them to
   agree everywhere.

   The uniqueness input has been weakened to exactly what a parametric integral
   can supply:
   `formal/GaloisForLFunctions/HTGeometry/PolyannulusSliceUniqueness.lean`:
   - `eqOn_zero_mixedAnnulus_of_slice`,
     **`eqOn_zero_polyannulus_of_slice`**, `eqOn_polyannulus_of_slice` — the
     coordinate-release proof never uses joint analyticity, only the
     one-variable identity theorem on each slice.  So separate holomorphy of
     every coordinate slice already forces a function vanishing on the torus to
     vanish on the polyannulus.

   That one-variable analytic input is now built:
   `formal/GaloisForLFunctions/HTGeometry/TranslatedFourierCoeffAnalytic.lean`:
   - `scaledTorusPoint`, `scaledTorusPoint_mem_polyannulus` — scaling the torus
     by a point of the polyannulus lands in the polyannulus;
   - `translatedIntegrand`, `translatedDerivIntegrand`,
     `continuous_translatedIntegrand`,
     `continuous_translatedDerivIntegrand`,
     `hasDerivAt_translatedIntegrand` — the integrand and its one-coordinate
     derivative, with the chain rule through `fderiv`;
   - **`analyticOnNhd_slice_activeCoeff_comp_torusScale`** — the translated
     Fourier coefficient is holomorphic in each coordinate of the translation.
     Differentiation under the integral sign
     (`hasDerivAt_integral_of_dominated_loc_of_lip`) is dominated by a uniform
     gradient bound on the compact image of a closed ball of translations times
     the torus, and `DifferentiableOn.analyticOnNhd` — available only in one
     complex variable, which is exactly what the slicewise uniqueness theorem
     needs — upgrades it to analyticity.

   The scaling law itself is built:
   `formal/GaloisForLFunctions/HTGeometry/TranslatedActiveCoeffScaling.lean`:
   - `charPow`, `fourier_eq_zpow`, `charPow_circleCoords`, `charPow_update` —
     the monomial `h^m` and its identification with the torus character;
   - `analyticOnNhd_zpow_of_ne_zero`, `ne_zero_of_mem_logAnnulus`;
   - **`activeCoeff_comp_torusScale_polyannulus`** — translating a phase
     observable by *any* point of the polyannulus multiplies its `m`-th active
     coefficient by `h^m`.  On the torus this is Haar invariance; off it, both
     sides are holomorphic in each coordinate of the translation and the torus
     is a uniqueness set for the polyannulus.

   No Laurent expansion is used anywhere in the layer.

   The stabilizer statement for arbitrary scalings follows:
   `formal/GaloisForLFunctions/HTGeometry/GeneralScaleStabilizer.lean`:
   - **`charPow_eq_one_of_eqOn_unitTorus`** — a scaling by *any* point of the
     polyannulus which fixes the observable on the torus annihilates every
     active character.  This is `(21)` without the unit-modulus restriction;
   - `norm_eq_one_of_charPow_eq_one` — the modulus consequence;
   - `analyticOnNhd_comp_torusScale_of_mapsTo`,
     `coordDeriv_comp_torusScale_of_mapsTo`,
     `torusDerivation_comp_torusScale_of_mapsTo`,
     **`phaseJet_comp_torusScale_of_mapsTo`** — scaling commutes with the
     derivation and with every phase jet, for an arbitrary scaling that maps one
     polyannulus into another.  These generalize the unit-modulus versions of
     layer 4 and are what the level-set argument needs at non-torus points.

   The level-set statement at a non-torus point is built:
   `formal/GaloisForLFunctions/HTGeometry/NonTorusLevelSet.lean`:
   - `shrinkRadii`, `abs_log_norm_lt`, `shrinkRadii_pos`, `shrinkRadii_le`,
     `polyannulus_shrinkRadii_subset`,
     `torusScale_mem_polyannulus_of_shrink` — a polyannulus small enough that
     scaling by a given point of the original one still lands inside it;
   - **`charPow_eq_one_of_phaseJet_eq`** — a point of the polyannulus whose
     phase jets all agree with those of the base point annihilates every active
     character.  The translated observable and the observable itself are
     holomorphic on the same smaller polyannulus with the same Taylor series at
     the origin of time, hence agree on the connected strip, hence along the
     real orbit, hence on the smaller polyannulus and in particular on the
     torus, where the scaling law reads off the annihilation.

   This is `(22)` without the restriction that both points lie on the torus,
   which is what the differential-rank argument needs.

   The algebra of the annihilator is built:
   `formal/GaloisForLFunctions/HTGeometry/CharPowAnnihilator.lean`:
   - `charPow_zero`, `charPow_add`, `charPow_zsmul` — `m ↦ h^m` is a
     homomorphism from the integer characters to the nonzero complex numbers;
   - **`charPow_eq_one_of_mem_span`** — annihilating a set annihilates the whole
     lattice it generates, so `(22)` applies to every element of the active
     lattice, not just to the support;
   - `sum_mul_log_norm_eq_zero` — taking moduli turns annihilation into a linear
     condition on the logarithms of the coordinate moduli;
   - **`norm_eq_one_of_annihilates`**, `mem_unitTorus_of_annihilates` — a
     character set whose real span is everything forces an annihilating scaling
     onto the unit torus.  This is the step that converts the full-rank
     hypothesis on the active lattice into discreteness of the all-jet level
     set.

   `formal/GaloisForLFunctions/HTGeometry/LogCoordDerivCoeff.lean`:
   - `logCoordDeriv` — the logarithmic coordinate derivative `z_i ∂_i F`;
   - **`activeCoeff_logCoordDeriv`** — its `m`-th active coefficient is
     `m_i · a_m`.  Proved by differentiating the scaling law at the identity
     translation: `hasDerivAt_slice_activeCoeff` (extracted from the parametric
     integral) gives the derivative as an integral, which is the coefficient of
     the logarithmic derivative, while the right-hand side `w^{m_i} · a_m`
     differentiates to `m_i · a_m`.

   **Revised route for the lower bound — no implicit function theorem needed.**
   Write `v_k(z) := (z_j ∂_j F_k(z))_j ∈ ℂ^r` and `Φ_c := Σ_j c_j · z_j ∂_j F`.
   Then `⟨c, v_k(z)⟩ = δ^k Φ_c (z)`, so `c` annihilates every `v_k(z₀)` exactly
   when all phase jets of `Φ_c` vanish at `z₀`.  By the jets-vanish machinery
   already built, that forces `Φ_c ≡ 0`, and by `activeCoeff_logCoordDeriv` the
   active coefficients of `Φ_c` are `⟨c, m⟩ · a_m`, so `c` annihilates the
   active lattice.  Hence the annihilator of `{v_k(z₀)}` is contained in
   `Λ_F^⊥`, of dimension `r − s`, so the differential rank at *every* point is
   at least `s`.  This replaces the fibre-dimension/constant-rank argument of
   the paper entirely.

   `formal/GaloisForLFunctions/HTGeometry/ActiveCoeffLinearity.lean` supplies
   the multiplier calculus that route needs:
   - `integrable_activeIntegrand`, `activeCoeff_add`, `activeCoeff_const_mul`,
     `activeCoeff_sum` — the active coefficient is an integral, hence linear on
     observables with continuous torus restriction;
   - `analyticOnNhd_logCoordDeriv`;
   - **`activeCoeff_torusDerivation`** — the torus derivation is the Fourier
     multiplier by `i (m · ω)`;
   - **`logCoordDeriv_torusDerivation`** — the logarithmic coordinate
     derivatives commute with the torus derivation.  Both are Fourier
     multipliers, so the two composites have equal active coefficients, and the
     active coefficients determine a holomorphic observable.  This replaces an
     appeal to symmetry of second derivatives.

   `formal/GaloisForLFunctions/HTGeometry/JetLogGradientAnnihilator.lean`
   carries out the annihilator computation:
   - `torusDerivation_const_mul`, `torusDerivation_sum` — linearity of the
     derivation;
   - `logGradPairing` — pairing a covector with the logarithmic coordinate
     derivatives, with `analyticOnNhd_logGradPairing` and
     **`activeCoeff_logGradPairing`**: its `m`-th active coefficient is
     `⟨c, m⟩ · a_m`;
   - **`logGradPairing_phaseJet`** — the pairing commutes with the jets, so
     `⟨c, v_k(z)⟩ = δ^k Φ_c (z)`;
   - `eventuallyEq_zero_of_eqOn_scaled` and
     **`eqOn_zero_of_phaseJet_eq_zero`** — an observable all of whose phase jets
     vanish at *one* point of the polyannulus vanishes identically.  Proved on
     the shrunken polyannulus adapted to that point, then spread by the
     several-variable identity theorem;
   - **`sum_mul_eq_zero_of_annihilates_jetLogGradients`** — a covector
     annihilating every jet logarithmic gradient at one point annihilates the
     whole active support.

   This is the differential-rank lower bound in annihilator form: the
   annihilator of `{v_k(z₀)}` sits inside `Λ_F^⊥`, so the rank is at least `s`
   at *every* point of the polyannulus.

   The numerical bound and the assembly are built:
   `formal/GaloisForLFunctions/HTGeometry/DualAnnihilatorRank.lean`:
   - `finrank_le_of_dualAnnihilator_le`, `dual_apply_eq_sum`,
     **`finrank_span_le_of_annihilator`** — if every covector annihilating one
     family annihilates a second, the second span is no larger.  Pure linear
     algebra, from the dual-annihilator dimension formula.

   `formal/GaloisForLFunctions/HTGeometry/PhaseRankLeAutonomousOrder.lean`:
   - **`finrank_span_jetGradients_le`** — the span of *all* jet gradients has
     dimension at most `n`, since each lies in the span of the first `n`;
   - `twistChar` and **`finrank_span_twistChar_le`** — the span of the active
     support, twisted by the base point, has dimension at most that of the jet
     gradients;
   - **`card_le_of_autonomousRelation`** — `s ≤ n`: any linearly independent
     family of `s` active characters has `s ≤ n` whenever there is a relation of
     order `n` whose separant does not vanish at the base point.

   This is the inequality `(6)` in the form the proof produces it, with the rank
   of the active lattice presented by an independent family of characters.

   The base-change half of the rank bridge is built:
   `formal/GaloisForLFunctions/HTGeometry/IntegerToComplexIndependence.lean`:
   - **`linearIndependent_complex_of_rat`** — a rationally independent family of
     rational coordinate vectors stays independent over `ℂ`.  Injectivity of the
     assembling map gives a *rational* left inverse, whose matrix identity
     persists under the ring homomorphism into `ℂ`; no minors, no flatness, no
     tensor products;
   - **`linearIndependent_complex_of_int`** — combining with the integer-to-
     rational step, an integrally independent family of integer characters is
     complex independent.

   The passage from independent families to the rank of the lattice is built:
   `formal/GaloisForLFunctions/HTGeometry/ActiveLatticeRankBound.lean`:
   - **`rank_span_int_le_of_independent_bound`** — a bound on the size of every
     integrally independent family inside a set of integer characters bounds the
     rank of the lattice it generates.  A rational basis extracted from the set
     is finite, because the rank of a submodule of `ℚ^r` is finite, and each of
     its members pulls back to an integer character of the set;
   - **`rank_activeLattice_le`** — `rank_ℤ Λ_F ≤ n` whenever a jet relation of
     order `n` has nonvanishing separant at a base point.

   Ritt's separant step is isolated from any particular notion of annihilation:
   `formal/GaloisForLFunctions/HTGeometry/AbstractSeparantMinimality.lean`:
   - `exists_minimal_natDegree`, `derivative_not_pred_of_minimal` and
     **`exists_pred_with_separant`** — among the nonzero polynomials satisfying
     a predicate there is one of minimal degree, and if no polynomial of degree
     zero satisfies the predicate then the derivative of a degree-minimal one
     fails it.  The corpus statement for `AutonomousAnnihilator` is the case of
     annihilation along the whole complex line; the phase-jet argument needs the
     case of annihilation along the real time axis only.

   The two presentations of an order-`n` equation are identified:
   `formal/GaloisForLFunctions/HTGeometry/LastVariableJetLift.lean`:
   - `pderiv_last_rename_castSucc`, `pderiv_X_pow_succ_self`;
   - `jetLift` — a univariate polynomial in the top jet with coefficients
     polynomial in the lower jets, read as a polynomial in `n + 1` variables
     whose last variable is the top jet;
   - **`eval_jetLift`** — evaluation of the lift is the two-step evaluation of
     the univariate presentation;
   - **`pderiv_last_jetLift`** — the separant of the equation is the last
     partial derivative of its lift.

   The assembly is built:
   `formal/GaloisForLFunctions/HTGeometry/PhaseRankFromAutonomousEquation.lean`:
   - `jetRelationEval_jetLift`;
   - **`rank_activeLattice_le_of_realAutonomousAnnihilator`** — if the phase
     function satisfies a nonzero autonomous algebraic differential equation of
     order `n` along the real time axis and no such equation is free of the top
     derivative, then `rank_ℤ Λ_F ≤ n`.  A degree-minimal equation has a
     separant which fails to annihilate, so the separant is nonzero at some real
     time, and the rank bound applies at the orbit point of that time.

6. **The Bohr frequency module**, equation `(26)` and the statement `(6)`.
   `[DONE]`

   The Bohr spectrum of `f` is identified with the detunings of the active
   characters.  No unique-ergodicity theorem is needed: uniform approximation by
   trigonometric polynomials computes both sides.

   `formal/GaloisForLFunctions/HTGeometry/TorusCharacterMean.lean`:
   - `exists_mFourier_ne_one` — a nontrivial character is somewhere different
     from `1`, by evaluating at a half-period of a coordinate where the exponent
     does not vanish;
   - **`integral_mFourier`** — a nontrivial character of the product torus has
     mean zero: translating by such a point multiplies the integral by the
     character value, and Haar measure is translation invariant;
   - **`mFourierCoeff_mFourier`** — the Fourier coefficients of a character are
     the Kronecker delta;
   - `norm_mFourierCoeff_le` — a Fourier coefficient is bounded by the supremum
     of the function, since the measure is a probability measure.

   `formal/GaloisForLFunctions/HTGeometry/TorusTrigPolynomial.lean`:
   - `integrable_torus_of_continuous`, `mFourierCoeff_sub`;
   - `torusTrigPoly`, **`mFourierCoeff_torusTrigPoly`** — the Fourier
     coefficients of a trigonometric polynomial are its coefficients;
   - **`exists_torusTrigPoly_approx`** — Stone--Weierstrass on the product
     torus: mathlib's `span_mFourier_closure_eq_top` gives density of the span
     of the characters, and the finitely supported presentation of a member of
     that span is the trigonometric polynomial.

   `formal/GaloisForLFunctions/HTGeometry/WindowAverageApproximation.lean`:
   - `norm_windowAverage_le`, `windowAverage_finset_sum`;
   - **`tendsto_of_approx`** — a function uniformly within `ε` of a convergent
     comparison function, with limit within `ε` of a target, for every `ε`,
     converges to that target;
   - `bohrMean_eq_of_tendsto` — the Bohr mean of a function with convergent
     window averages is their limit.  No almost periodicity is assumed, which is
     what allows the modulated quasiperiodic function to be handled at *every*
     real frequency, not only at the detunings.

   `formal/GaloisForLFunctions/HTGeometry/PhaseFunctionBohrCoefficient.lean`:
   - `injective_finiteTorusCharacterDetuning` — equation `(26)`: rational
     independence makes `m ↦ m · ω` injective;
   - `realPhaseFunction`, `realPhaseFunction_eq`,
     `continuous_realPhaseFunction` — the quasiperiodic function on real time is
     the torus restriction along the phase flow;
   - `mFourier_finiteClockPhasePoint_expChar`,
     **`tendsto_windowAverage_trigPoly`** — a character becomes a pure
     exponential along the flow, so the modulated window averages of a
     trigonometric polynomial converge to the sum of the coefficients whose
     detuning is the modulating frequency;
   - **`tendsto_windowAverage_realPhaseFunction`** — the approximation estimate:
     the difference of the two modulated window averages is a window average of
     a function bounded by `ε`;
   - **`bohrCoefficient_realPhaseFunction`** — the Bohr coefficient at a
     detuning is the corresponding active coefficient;
   - **`bohrCoefficient_realPhaseFunction_eq_zero`** — the Bohr coefficient
     vanishes at every frequency which is not a detuning;
   - **`bohrSpectrum_realPhaseFunction`** — the Bohr spectrum is exactly
     `{m · ω : a_m ≠ 0}`.

   `formal/GaloisForLFunctions/HTGeometry/BohrFrequencyRankLaw.lean`:
   - **`rank_bohrFrequencyModule_eq_rank_activeLattice`** — the rational rank of
     the Bohr frequency module is the integer rank of the active lattice, by
     layer 1 applied to the spectrum identification;
   - **`rank_bohrFrequencyModule_le_of_realAutonomousAnnihilator`** — this is
     `(6)`: `rank_ℚ Γ(f) = s ≤ n`;
   - `not_realAutonomousAnnihilator_of_lt_rank` — the hypertranscendence
     consequence: a frequency rank exceeding `n` excludes every autonomous
     algebraic differential equation of order `n`.

7. **Order minimality is not a hypothesis.**  `[DONE]`

   `formal/GaloisForLFunctions/HTGeometry/LastVariableJetLift.lean` also carries
   the inverse presentation `jetUnlift` with
   **`lastVariableJetLift_jetUnlift`**, so a polynomial in the jets `0,…,m` is a
   univariate polynomial in the top one.

   `formal/GaloisForLFunctions/HTGeometry/MinimalAutonomousOrder.lean`:
   - **`exists_realAutonomousAnnihilator_of_natDegree_zero`** — a relation of
     order `m + 1` free of the top derivative is a relation of order `m`;
   - `natDegree_ne_zero_of_no_lower_annihilator` — at an order below which no
     nonzero relation exists, every nonzero relation has the top derivative
     present; at order zero because a nonzero constant polynomial does not
     vanish, which is `MvPolynomial.funext` on an empty variable set;
   - **`exists_minimal_order_realAutonomousAnnihilator`** — order minimality can
     always be arranged, at an order no larger than the given one.

   Hence the minimality hypothesis disappears from the statement:
   **`rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator`** bounds
   the rational frequency rank by the order of *any* nonzero autonomous
   algebraic differential equation the function satisfies.

8. **Sharpness**, equations `(27)`--`(28)`.  `[DONE]`

   `formal/GaloisForLFunctions/HTGeometry/LinearPhaseObservable.lean`:
   - `linearObservable`, `linearObservableCLM`, `analyticOnNhd_linearObservable`,
     `coordDeriv_linearObservable`, `torusDerivation_linearObservable`;
   - **`phaseJet_linearObservable`** — every phase jet of `∑_j a_j z_j` is again
     linear, with coefficients multiplied by `(i ω_j)^k`;
   - `torusRestriction_linearObservable`, `mFourierCoeff_fintype_sum`,
     **`activeCoeff_linearObservable_single`** — the active coefficient at the
     `j`-th standard character is `a_j`;
   - **`rank_activeLattice_linearObservable`** — with no vanishing coefficient
     the active lattice is the whole character lattice, of rank the number of
     frequencies.

   `formal/GaloisForLFunctions/HTGeometry/PhaseRankSharpness.lean`:
   - `frequencyCharPoly`, `monic_frequencyCharPoly`,
     `natDegree_frequencyCharPoly`, `eval_frequencyCharPoly` — the monic
     polynomial `∏_j (X − i ω_j)`;
   - `linearRelationPoly`, `linearRelationPoly_ne_zero` and
     **`realAutonomousAnnihilator_linearObservable`** — equation `(28)`: the
     exponential sum satisfies the linear autonomous equation of its
     characteristic polynomial, of order the number of frequencies.  Each jet
     contributes `∑_j a_j e^{i ω_j t} (i ω_j)^k`, so the relation evaluates to
     `∑_j a_j e^{i ω_j t} · p(i ω_j) = 0`;
   - **`rank_bohrFrequencyModule_linearObservable`** and
     **`sharpness_linearObservable`** — equation `(27)`: the frequency rank is
     exactly the number of frequencies and an equation of that order exists, so
     equality is attained in `(6)`;
   - **`not_realAutonomousAnnihilator_linearObservable`** — and no autonomous
     algebraic differential equation of lower order annihilates it, which now
     follows from the minimality-free form of the law.

Layers 1--4 are complete, unconditional and axiom-clean.  A structure assuming `s ≤ n`
or assuming the required finite jet rank would be circular and is not counted.
