# Hierarchical Resonance-Breaking Taylor Magnitudes Force Hypertranscendence

- **ID:** `hierarchical-resonance-breaking-taylor-magnitude-hypertranscendence`
- **Stage:** 3-formalized / needs scientific-novelty audit
- **Type:** THEOREM (paper) / GENERAL HT LAW / ASYMPTOTIC-SCALE CONSTRAINT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** Under uniform geometric growth, differential algebraicity forces one fixed balanced integer shift relation to recur within logarithmic width infinitely often. If every fixed shift relation is instead superlogarithmically separated, the Taylor-magnitude profile forces hypertranscendence for every coefficient phase. For an algebraic geometric leading scale, all surviving relations compress to one canonical lower-scale residue.

## Goal

Test whether algebraic relations in a geometric logarithmic-magnitude scale are a genuine escape from the Archimedean tropical bend obstruction. They are not stable. An asymptotically negligible second scale can break every finite relation left by the first scale.

The point is not faster decay: the successive ratio still tends to the prescribed geometric ratio. The new invariant is hierarchical additive rigidity across asymptotic scales.

## Archimedean shift-defect law

For a real sequence `(b_n)` and a nonzero integer Laurent polynomial

`Q(T)=sum_r d_r T^r in Z[T,T^(-1)]`,

define its fixed-shift defect by

`Delta_Q b(n)=sum_r d_r b_(n+r)`.                                            `(SD)`

Call `(b_n)` **logarithmically shift-separated** if, for every such `Q`,

`|Delta_Q b(n)|/log n -> infinity`.                                         `(LSS)`

This is intrinsic to the magnitude profile. It does not refer to a chosen asymptotic decomposition.

## Master theorem `[PROVED HERE] [NOVELTY UNVERIFIED]`

Let `(b_n)` be eventually positive and suppose

`liminf_(n->infinity) b_(n+1)/b_n > 1`                                     `(UG)`

and that `(b_n)` is logarithmically shift-separated. Then every eventually full-support series

`f(z)=sum_(n>=0) a_nz^n`, `|a_n|=exp(-b_n)`

is entire and HT over `C(z)`, for every possible choice of coefficient phases.

## Uniform-geometric DA resonance law `[PROVED HERE] [NOVELTY UNVERIFIED]`

Let `(b_n)` be eventually positive and satisfy `(UG)`. If an eventually full-support series

`f(z)=sum_(n>=0) a_nz^n`, `|a_n|=exp(-b_n)`

is DA over `C(z)`, then there exist a nonzero integer Laurent polynomial

`Q(T)=sum_r d_rT^r in Z[T,T^(-1)]`, with `Q(1)=0`,

a constant `C>0`, and an unbounded sequence of integers `(q_k)` such that

`|Delta_Q b(q_k)| <= C log q_k`.                                           `(DR)`

Thus a DA Taylor-magnitude profile with uniform geometric growth must carry one fixed bounded additive relation which returns to logarithmic width infinitely often. The polynomial `Q` is not allowed to vary with the scale.

## Logarithmic resonance-breaking condition

Fix `lambda>1`. A real sequence `(h_n)` is **logarithmically resonance-breaking at `lambda`** if

`h_n=o(lambda^n)`                                                            `(RB1)`

and, for every nonzero finitely supported integer family `(d_r)` such that

`sum_r d_r lambda^r=0`,

one has

`|sum_r d_r h_(n+r)| / log n -> infinity`.                                  `(RB2)`

The offsets may be negative; all expressions are taken on a sufficiently large tail. Condition `(RB2)` says that every bounded integer resonance surviving the leading geometric scale is broken before the Archimedean separation falls to the logarithmic cancellation width of an ADE.

## Hierarchical verification theorem `[PROVED HERE]`

Fix `lambda>1` and `A>0`, and let `(h_n)` be logarithmically resonance-breaking at `lambda`. Let

`f(z)=sum_(n>=0) a_nz^n`

have eventually nonzero coefficients satisfying

`-log|a_n| = b_n := A lambda^n+h_n`                                         `(1)`

for every sufficiently large `n`. Then `(b_n)` satisfies `(UG)` and `(LSS)`, so `f` is entire and HT over `C(z)` for every possible choice of coefficient phases.

If `lambda` is transcendental, `(RB2)` is vacuous because no nonzero integer Laurent polynomial vanishes at `lambda`; taking `h_n=0` recovers the exact-geometric special case of the stronger Taylor log-ratio algebraicity law.

## Canonical algebraic-ratio resonance residue `[PROVED HERE]`

Suppose `lambda>1` is algebraic, let `m_lambda(T) in Z[T]` be its primitive minimal polynomial, and let `S` denote the forward shift. For a profile satisfying

`b_n/(A lambda^n)->1` for some `A>0`,                                      `(EG)`

define

`Res_lambda(b):=m_lambda(S)b`.                                               `(RR)`

Then `(b_n)` is logarithmically shift-separated if and only if, for every nonzero integer Laurent polynomial `R`,

`|R(S) Res_lambda(b)(n)|/log n -> infinity`.                                `(RRLSS)`

Thus all exact relations in the leading algebraic geometric scale compress to one canonical lower-scale residue.

### Proof

If `(b_n)` satisfies `(LSS)`, apply it to the nonzero Laurent polynomial `m_lambda R`; this gives `(RRLSS)`.

Conversely, fix a nonzero integer Laurent polynomial `Q`. If `Q(lambda)!=0`, condition `(EG)` gives

`Delta_Q b(n)=A lambda^n Q(lambda)+o(lambda^n)`,

so its absolute value is exponentially larger than `log n`. If `Q(lambda)=0`, divisibility by the minimal polynomial in `Q[T,T^(-1)]` gives a nonzero integer `c` and a nonzero integer Laurent polynomial `R` such that

`cQ=m_lambda R`.

Therefore

`c Delta_Q b=R(S) Res_lambda(b)`,

and `(RRLSS)` gives `(LSS)` for `Q`. `square`

## Stretched-exponential corollary `[PROVED HERE]`

For arbitrary

`lambda>1`, `A>0`, `B>0`, and `0<alpha<1`,

every eventually full-support series with

`-log|a_n|=A lambda^n+B exp(n^alpha)`                                       `(2)`

is HT for every phase choice.

In particular, for every phase sequence `(theta_n)`,

`sum_(n>=0) exp(-2^n-exp(sqrt n)) exp(i theta_n) z^n`                        `(3)`

is HT.

## Preliminary resonance-breaking lemma `[PROVED HERE]`

Let `(d_r)` be a nonzero finitely supported family of integers, indexed by fixed integer offsets `r`, and fix `0<alpha<1`. Then there are an integer `j>=0` and a nonzero real constant `C_(d,alpha)` such that

`sum_r d_r exp((q+r)^alpha)`

` = C_(d,alpha) exp(q^alpha) q^(-j(1-alpha))(1+o_(d,alpha)(1))`              `(FD)`

as `q->infinity`. Consequently its absolute value is `omega(log q)`.

### Proof

Let `j` be the least nonnegative integer for which the moment

`M_j=sum_r d_r r^j`

is nonzero. Such a `j` exists: if all moments vanished, the finitely many coefficients `d_r` would vanish by the Vandermonde determinant on their distinct support points.

Put `h(x)=exp(x^alpha)`. Induction on `k` gives, for every fixed `k`,

`h^(k)(x)=alpha^k x^(-k(1-alpha))h(x)(1+O_(k,alpha)(x^(-alpha)))`.            `(4)`

Indeed, differentiating the displayed leading term multiplies it principally by `alpha x^(alpha-1)`; differentiating its power prefactor is smaller by a factor `x^(-alpha)`.

Taylor's theorem at `q`, to any fixed order `K` larger than the support size, gives uniformly over the fixed offsets

`h(q+r)=sum_(k=0)^K r^k h^(k)(q)/k!+O_(d,alpha)(h(q)q^(-(K+1)(1-alpha)))`.    `(5)`

After summing (5) against `d_r`, every term below order `j` vanishes by the minimality of `j`. Formula (4) makes the first surviving term

`M_j alpha^j exp(q^alpha)q^(-j(1-alpha))/j! * (1+o(1))`.

All higher terms and the remainder are smaller because `q^(-(1-alpha))->0`; choose `K>j`. This proves `(FD)`, with `C_(d,alpha)=M_j alpha^j/j!`. Since `exp(q^alpha)q^(-j(1-alpha))/log q->infinity`, the final claim follows. `square`

## Proof of the master theorem

A finite Taylor prefix is irrelevant: subtract it and divide by a power of `z`. Thus work on a full tail satisfying `(UG)` and `(LSS)`. Choose `mu>1` and `n_0` such that

`b_(n+1) >= mu b_n`                                                         `(G)`

for all `n>=n_0`. Hence `b_n` grows at least geometrically, so `b_n/n->infinity` and `f` is entire.

Suppose for contradiction that `f` is DA. By Mahler's integer-normalization theorem it satisfies

`P(z,f,f',...,f^(m))=0`                                                     `(6)`

for a nonzero `P in Z[z,Y_0,...,Y_m]`. Let `D>=1` be the largest total `Y`-degree of `P`.

With the generic series `F=sum_n X_nz^n`, group equal coefficient monomials:

`[z^N]P(z,F,F',...,F^(m))=sum_(nu in A_N)c_(N,nu)X^nu`.                     `(7)`

The `c_(N,nu)` are nonzero integers with polynomially bounded number and size. If the substituted zero-sum identity has a unique smallest valuation

`V_N(nu)=sum_n nu_n b_n`,                                                    `(8)`

then the difference between its two smallest valuations must be `O_P(log N)`. This is the Archimedean tropical bend law: the integer coefficient of the largest atom has modulus at least one, while the total polynomially many remaining weighted atoms can cancel it only when the second atom is within a polynomial factor.

### 1. All minimizing atoms have bounded balanced offsets

The balanced-survival theorem proved in `log-superlacunary-taylor-magnitude-hypertranscendence.md` applies to the generic coefficient polynomial of every integer ADE. It supplies, for every sufficiently large `N`, a surviving degree-`D` atom whose source indices all lie in

`[N/D-C,N/D+C]`                                                             `(9)`

for a fixed `C=C_P`. This is the balanced-survival lemma: after grouping top-degree monomials by their fixed source-sum shift, a nonzero symmetric integer weight polynomial remains; on each coordinate-sum residue class some fixed-offset diagonal is not identically zero.

The witness in (9) has valuation at most `D b_(q+C_0)`, where `q=floor(N/D)` and `C_0` depends only on `P`. If `D>=2`, a lower-degree atom has a source index at least `N/(D-1)-O_P(1)`. Its distance above `q+C_0` tends linearly to infinity, so repeated use of `(G)` makes its valuation exceed the witness by a factor tending exponentially to infinity. When `D=1`, degree-zero atoms disappear for large `N`.

Choose a fixed `C_1>C_0` so large that `mu^(C_1-C_0)>2D`. Any degree-`D` atom whose largest source index exceeds `q+C_1` has valuation at least `b_(q+C_1+1)>2D b_(q+C_0)`, hence exceeds the witness by at least `D b_(q+C_0)`. The fixed source-sum constraint then bounds every source index below as well. Hence every valuation minimizer has the form

`k_i=q+r_i`, `q=floor(N/D)`, `|r_i|<=C'`                                    `(11)`

for a constant `C'=C'_P`. Moreover, since `(G)` gives `b_(q-C')/log N->infinity`, every lower-degree or nonbalanced atom is separated from the balanced minimum by `omega(log N)`.

### 2. Shift separation forbids every bounded bend

Take two distinct grouped atoms satisfying (11), and write `d_r` for the difference of their multiplicities at the offset `r`. Then `(d_r)` is a nonzero finitely supported integer family and

`V_N(nu)-V_N(mu)=sum_r d_r b_(q+r)=Delta_Q b(q)`,                           `(12)`

where `Q(T)=sum_r d_rT^r` is a nonzero integer Laurent polynomial. Condition `(LSS)` says directly that the absolute value of (12) is `omega(log q)=omega(log N)`.

For each residue class of `N modulo D`, only finitely many bounded patterns can occur. The preceding asymptotics are therefore uniform over every pair of distinct candidates after increasing the threshold in `N`. The minimum valuation is unique and its gap from every other atom is `omega(log N)`.

The balanced-survival lemma makes (7) nonzero for every sufficiently large `N`. The superlogarithmic unique-minimum gap contradicts the Archimedean tropical bend law at all such indices. Therefore no ADE exists and `f` is HT. `square`

## Proof of the uniform-geometric DA resonance law

Apply the integer normalization and generic coefficient extraction used in the master theorem to an ADE for `f`. The balanced-survival lemma supplies a nonzero degree-`D` bounded-offset atom at every sufficiently large coefficient index. The coarse comparison in Step 1 of the master proof uses only `(UG)`, so every lower-degree or nonbalanced atom lies `omega(log N)` above the balanced minimum.

The Archimedean tropical bend law therefore forces, for every sufficiently large `N`, two distinct degree-`D` bounded-offset atoms whose valuations differ by `O_P(log N)`. Write their source indices as `q+r_i`, where `q=floor(N/D)` and all offsets range over one fixed finite set. The difference of their multiplicity vectors gives a nonzero integer Laurent polynomial

`Q_N(T)=sum_r d_(N,r)T^r`.

Both atoms have degree `D`, so `sum_r d_(N,r)=0`, equivalently `Q_N(1)=0`. After restricting to one residue class of `N modulo D`, only finitely many ordered pairs of bounded-offset patterns occur. One pair therefore recurs along an unbounded sequence. Its fixed nonzero polynomial `Q` satisfies

`|Delta_Q b(q_k)|=O_P(log q_k)`,

because `N_k=Dq_k+O_P(1)`. Enlarging the implied constant gives `(DR)`. `square`

## Proof of the hierarchical verification theorem

Let `b_n=A lambda^n+h_n`. Condition `(RB1)` gives `(EG)`, and hence `(UG)`. Fix a nonzero integer Laurent polynomial `Q(T)=sum_r d_rT^r`. Then

`Delta_Q b(n)=A lambda^n Q(lambda)+sum_r d_r h_(n+r)`.                       `(13)`

If `Q(lambda)!=0`, the first term has size a positive constant times `lambda^n`, while the second is `o(lambda^n)` by `(RB1)`. If `Q(lambda)=0`, condition `(RB2)` says that the second term divided in absolute value by `log n` tends to infinity. Thus `(LSS)` holds in both cases. The master theorem proves the claim. `square`

## Proof of the stretched-exponential corollary

Take `h_n=B exp(n^alpha)`. Condition `(RB1)` holds because `0<alpha<1` and `lambda>1`. For every nonzero finitely supported integer family `(d_r)`, the preliminary lemma gives

`|sum_r d_r h_(n+r)|`

` = |B C_(d,alpha)| exp(n^alpha)n^(-j(1-alpha))(1+o(1))`,

which divided by `log n` tends to infinity. In particular `(RB2)` holds for every family satisfying a leading resonance. The hierarchical verification theorem proves (2), and (3) follows with `lambda=2`, `A=B=1`, and `alpha=1/2`. `square`

## Boundary attacks

1. **The theorem includes algebraic and rational ratios.** In (3), the leading scale has the exact resonance `2 * 2^n=2^(n+1)`. The smaller `exp(sqrt n)` layer, not transcendence of the ratio, destroys the resonance.
2. **The perturbation is asymptotically negligible.** `exp(n^alpha)/lambda^n->0`, and `b_(n+1)/b_n->lambda`. Thus neither log-superlacunarity nor a transcendental successive ratio proves the result.
3. **Finite polynomial corrections do not suffice universally.** A sufficiently high finite-difference pattern annihilates every fixed polynomial degree. By contrast, the stretched-exponential germ has a nonzero asymptotic response at the first nonvanishing moment of every finite pattern. No corresponding blanket claim is made for arbitrary collections of geometric correction scales.
4. **No converse is claimed.** Removing the resonance-breaking layer makes this proof fail for algebraic `lambda`; it does not make the resulting series DA.
5. **No phase hypothesis is hidden.** Once the unique magnitude-dominant atom is isolated, no choice of phases can cancel it against polynomially bounded integer-weighted competitors.

## General law exposed

The necessary and sufficient directions isolate a hierarchy rather than a single growth threshold:

> In the uniform-geometric regime, DA requires one fixed balanced additive relation to return to `O(log N)` infinitely often. If every fixed relation stays at `omega(log N)`, the profile is phase-uniformly HT. Lower asymptotic scales matter exactly through whether they preserve or break those resonances.

Log-superlacunarity has no leading relations because the largest differing index dominates. A transcendental geometric scale has no Laurent-polynomial relations. The present theorem permits exact leading relations and kills them at the next asymptotic layer. This is the first genuinely resonant stratum of the coefficient-floor program closed by the bend method.

## Consequence for the super-Gaussian program

The profile (1) satisfies `b_n/n^2->infinity`, so it lies in the super-Gaussian class. More generally, every DA profile in the uniform-geometric part of that class must have one recurrent fixed resonance `(DR)`. The remaining open range cannot be described merely by adjacent comparability or even by leading-scale algebraic resonance. A DA counterexample would need logarithmically close bounded convolution relations that persist through every asymptotic layer visible in the coefficient magnitudes.

## Exact RH-route scope

The theorem fixes HT status across the entire phase fiber with moduli `exp(-b_n)`. Therefore an RH implementation whose selector is asserted to factor only through this HT bit, these magnitudes, their Newton envelope, or the two-scale anti-bend data cannot recover phase-sensitive divisor localization on the fiber.

It does not exclude complete Connes, Hilbert--Polya, de Branges, Nyman--Beurling, Weil, Li, or de Bruijn--Newman criteria, which may retain exact spectral, positivity, norm, Euler-product, or divisor information absent from this invariant.

## Parent and novelty status

- Mahler's integer normalization is the essential differential-algebraic parent.
- The finite-difference asymptotic `(FD)` is elementary asymptotic analysis and is not itself claimed new.
- Lipshitz--Rubel support-gap theory does not apply because the series has full support.
- Arithmetic coefficient theorems do not apply because phases and coefficient fields are arbitrary.
- Valiron--Wiman theory constrains maximum terms and growth of selected ADE classes; it does not state the fixed-shift coefficient-defect law for arbitrary ADE order and arbitrary complex phases.
- Shackell's 1995 hierarchy constrains nested asymptotic subterms of nonoscillatory Hardy-field solutions, principally with order-dependent and first-order conclusions. Its object is the asymptotic expansion of the solution itself at infinity, not the sequence of Taylor-coefficient magnitudes or their phase fiber.
- Denef--Lipshitz formal-solution theory and tropical differential algebra study existence, support, or local vanishing orders. No Archimedean `-log|a_n|` shift-separation theorem was located there.
- The scientific candidate is the phase-uniform HT consequence of a hierarchically resonance-breaking magnitude profile. Exact parent-literature and rediscovery audits remain open, so the result stays `[NOVELTY UNVERIFIED]`.

## Lean status

Formalized unconditionally in
`formal/GaloisForLFunctions/HTGeometry/HierarchicalResonanceBreaking.lean`.

The formal module proves the full paper surface:

- `UniformGeometricGrowth` and `LogarithmicallyShiftSeparated` encode the intrinsic magnitude
  hypotheses;
- `near_balanced_atom_count_eq_and_supportMax_lt_of_geometric_lower` and
  `exists_eventually_uniformGeometric_bend_pair_of_positiveJetDegree` prove the bounded-window
  bend from an eventual lower geometric step alone;
- `exists_eventually_uniformGeometric_resonancePolynomial_of_differentiallyAlgebraic` proves the
  fixed nonzero integer-polynomial DA resonance law on an unbounded subsequence;
- `hypertranscendental_of_eventually_uniformGeometric_logarithmicallyShiftSeparated` proves the
  phase-uniform master HT theorem, including finite Taylor-prefix removal;
- `LogarithmicallyResonanceBreakingAt`, `uniformGeometricGrowth_hierarchical`,
  `logarithmicallyShiftSeparated_hierarchical`, and
  `hypertranscendental_of_hierarchical_resonanceBreaking` prove the generic hierarchy theorem;
- `primitiveRationalMinpolyInteger` is a primitive integer normalization of the rational
  minimal polynomial, and `logarithmicallyShiftSeparated_iff_primitiveMinpolyResidue` proves the
  canonical algebraic-ratio residue equivalence using denominator clearing and Gauss
  divisibility;
- `exists_stretchedMoment_ne_of_polynomial`, together with the existing
  `stretchedFiniteDifference_isEquivalent`, supplies the first nonzero finite-difference moment;
- `logarithmicallyShiftSeparated_stretchedExp`,
  `logarithmicallyResonanceBreakingAt_stretchedExp`, and
  `hypertranscendental_of_geometric_add_stretchedExp` prove the complete
  `A * lambda^n + B * exp(n^alpha)` corollary for `lambda>1`, `A,B>0`, and `0<alpha<1`;
- `hypertranscendental_of_twoPow_add_expSqrt` proves the explicit
  `2^n + exp(sqrt n)` example for arbitrary coefficient phases.

The exact leaf target
`+GaloisForLFunctions.HTGeometry.HierarchicalResonanceBreaking` and the direct touched-source
check both pass. The capstones use only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. No full or concurrent Lean build was run.

## Gates

- [x] Exact theorem stated.
- [x] Complete unconditional paper proof.
- [x] Fixed-recurrence necessary law for every DA uniform-geometric profile.
- [x] Rational-ratio resonant example proved HT for every phase.
- [x] Significance gate: an asymptotically negligible second scale destroys every finite leading resonance.
- [ ] Exact parent-theory and literature novelty gates.
- [x] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved hierarchical resonance breaking for `A lambda^n+B exp(n^alpha)`, `0<alpha<1`, and isolated persistence through every asymptotic layer as the remaining DA escape.
- 2026-07-11 — Strengthened the master theorem from exact geometric asymptotics to uniform eventual geometric growth and proved the converse DA law: one fixed balanced integer shift defect must return to `O(log n)` along an infinite subsequence.
