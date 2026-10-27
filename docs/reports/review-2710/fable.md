# Review 2710 — the three walls as one gap, three focus questions, and the field that would close it

Author: Fable. Date: 2026-10-27. Working log: `logs/fable-review-2710-research-log.md`.

## 0. Scope, evidence, labels

Read in full: `docs/reports/rh-current-frontier-map.md`, `docs/reports/rh-killed-routes.md` (including
the scoped catalogue), `docs/reports/review-2710/route-unification-ledger.md`,
`docs/reports/review-2710/walls-ledger.md`, and, because the listed file
`docs/reports/review-2710/hard-obstacles.md` does not exist, the two obstacle documents that do:
`route-obstacles.md` and `obstacles-summary.md`. Also the README of each of the thirty programme
folders named in the brief (list in the log). Corpus research used `scripts/formal_tools.py research`;
the statements of every declaration cited below were confirmed by reading their source text. Nothing
was compiled, no axiom audit was run, no web access. The report does not verify other agents' work: it
takes the ledgers' labels at face value and builds on them.

Labels. [L] formalized in the corpus (per the ledgers, or confirmed in source). [S] scoped or partial
per the ledgers. [C] classical background from the literature, not in the corpus; cite before use.
[R] my own derivation, reading or conjecture; not a theorem anywhere.

Relation to the prior review (`obstacles-summary.md`). It already names three open questions
(alignment at zero ordinates; arithmetic adjunction / positive renormalization of the torsion
diagonal; gauge persistence) and sketches a field, "arithmetic electrostatics of the zero divisor".
Nothing below restates them. Section 1 gives a different account of why the walls exist (three
structural causes behind the fifteen exhaustion laws). Section 2 evaluates candidate mechanisms
against an explicit admissibility test and contains two new computations. Section 3 proposes three
focus questions that are sharper than, or orthogonal to, the prior three. Section 4 designs the field
from the exhaustion laws rather than from the field-of-zeros picture.

## 1. What the corpus has established, on one page

### 1.1 The reduction

Every live route ends at the same place: an exact RH-equivalent receiver (thirty-one of them,
isomorphic under the width functor [L]) plus one missing sign or rate on the arithmetic side. The
sign is always the positivity of one of two forms on tests `f`, with `ρ* = 1 − ρ̄`,
`δ_ρ = Re ρ − 1/2`, and `T_L f = f(· − L)` the Hecke translation (dilation by `e^L`):

* Weil's form `W(f) = Σ_ρ m_ρ f̂(ρ) conj f̂(ρ*)`, the explicit formula. Hecke-equivariant for every
  zero configuration (`T_L` multiplies `f̂(ρ) conj f̂(ρ*)` by `e^{(ρ−1/2)L} e^{conj(ρ*−1/2) L} = 1`),
  computable from primes, positive on squares iff RH.
* The collided form `D(f) = Σ_ρ m_ρ |f̂(ρ)|²`. Positive for every configuration, a logarithmic Sobolev
  norm by the local Weyl law [L], computable from the Laplacian of `log|ξ|` and polynomially many
  theta values [L]; Hecke-equivariant iff RH, with defect
  `E_f(L) = D(T_L f) + D(T_{−L} f) − 2 D(f) = Σ_ρ m_ρ (2 cosh(2 δ_ρ L) − 2) |f̂(ρ)|²`
  (`heckeDefect_eq_second_difference` [L]; the strip bound `heckeDefect_le_strip` and the two-scale
  inequality `heckeDefect_sq_le_two_scale` are the only unconditional controls on it).
* `Re W = D − Δ`, `Δ = Σ_ρ (m_ρ/2) |f̂(ρ) − f̂(ρ*)|² ≥ 0` [L]. RH ⇔ `Δ ≡ 0` ⇔ `W = D`.

So RH is the coincidence of a geometric pairing (equivariant, read from primes) with a spectral
pairing (positive, read from `ξ`). Over `F_q` both are the intersection pairing on the correspondence
lattice of `C × C`; they coincide by construction and the coincidence is positive by the Hodge index
theorem, which rests on Riemann–Roch and an ample class. The corpus has verified that every other
layer of Weil's proof is free over `Z` (identities, the square theorem, the budget, the kernel counts
collided) and that the Rosati positivity, the counting form of it, and the base are each RH
(`route-obstacles.md` layer table).

### 1.2 Three walls, one gap

| wall | ledger statement | the step of Weil's proof it corresponds to | what the corpus proves fails over `Z` |
|---|---|---|---|
| 1, arithmetic sign | the prime-side estimate at the end of every route | none: Lefschetz numbers are counts, so the sign is free | the count (`Λ ≥ 0`, `ψ`, sections) sits on the receiver side; finite apertures read only `λ(n)` for `log n < 2R`; floors must decay doubly exponentially; nonnegative tests are nonselective |
| 3, transfer | no norm, information or budget transfer from averaged, collided or windowed to signed, pointwise or unbounded-aperture | Cauchy–Schwarz for a negative definite form on primitive classes (Castelnuovo–Severi) | the form has signature `(1,1)` on every off-line pair, so it is indefinite on primitive classes exactly when transfer is needed; shared budgets glue only one charge; moments give proportions |
| 14, faithful realization | no carrier that is positive, equivariant and selective at once | the surface `C × C`: finite `Δ² = 2 − 2g`, Riemann–Roch, an ample class | the diagonal self-energy is infinite in all three appearances; RR + Bézout for one cone ⇔ Hodge ⇔ RH; the polarization is soft; states on `Aff(Q)` are induced from dilations |

### 1.3 Fifteen laws, three causes [R]

The ledgers list fifteen exhaustion laws (gauge, hyperbolicity, resonance, conductor, localization,
dominated twins, linear loss, pole order, collision, counting, deformation, renormalization,
completion, detection, statistics). Reading the proofs behind them, each follows from one of three
structural facts about the data every route uses.

* C1, commutativity. The only operators ever applied are Hecke translations `T_x` (`x ∈ Q^×_{>0}`),
  height twists, and the reflection `s ↦ 1 − s̄`. The Hecke semigroup is abelian, so at an off-line
  pair the joint spectral decomposition of the dilations is hyperbolic (the boost lemma: positivity on
  a cyclic span forces `u · conj v = 0`), and any positivity invariant under the algebra is isotropic
  there. Instances: gauge, hyperbolicity, resonance, localization, conductor, deformation, dominated
  twins. The horizon/forcing gap (positivity automatic for `e^a ≲ log γ / 4`, forcing only for
  `e^{2δa} > 768 A log γ`) is the quantitative face of C1: an abelian localizer at height `γ` costs
  `(1/2δ) log log γ` in aperture because its only handle on depth is the hyperbolic growth `e^{2δ u}`.
* C2, trace-linearity. Every receiver is a linear functional of the explicit formula; the only
  invariants available are quadratic forms in `f̂`. A quadratic form on a cone of nonnegative tests is
  monotone in the prime weights ("on nonnegative tests `ζ` is the worst twin"), on finite windows it is
  blind to tempered crystals, under averaging it yields proportions, and it cannot see an integer.
  Instances: counting, statistics, collision, detection, linear loss, completion.
* C3, infinite diagonal. Over `Z` the diagonal has no finite self-intersection: the double pole
  `m²/(s−ρ)²` of `(ζ'/ζ)²`, the torsion self-energy `log(1/(1−r))`, and the absence of a `2 − 2g`.
  Every renormalization that makes a form finite loses its sign at the diagonal. Instances:
  renormalization, pole order, completion, and the rate half of the statistics law (the square-root
  threshold is the scale at which the diagonal regularization and the aperture trade places).

Over `F_q` one object breaks all three at once: the surface `C × C`, on which (C1) the Frobenius
algebra sits inside the non-commutative ring of correspondences, (C2) sections give integer-valued,
non-quadratic invariants through Riemann–Roch, and (C3) the diagonal is a curve with
`Δ² = 2 − 2g` by adjunction. That is the precise sense in which the three walls are one gap.

### 1.4 Assets a new mechanism can use (all [L] unless marked)

* Forcing half: `odd_sector_nonneg_forces_offLine_companion` with its explicit threshold `hbig`;
  the even sector cannot force (`even_sector_summand_nonneg`).
* Twisted explicit formula and horizon positivity (ArithmeticPolarization).
* Landau–Gonek over zeros: `exists_smoothedLandau_le`, `exists_smoothedLandau_neg_le`,
  `exists_zeroSum_dirichletPolynomial_le` (integer frequencies `n ≤ Y`, `Y + 2 ≤ T`, error
  `K Σ |a_n| (√n + √T)`).
* Montgomery's pair correlation at leading order, unconditional in the real parts
  (`tendsto_montgomeryForm_div_leadingOrder`, `pairEntry` uses `x^{ρ + ρ̄' − 1}`), and its uniform
  version on `[a,b] ⊂ (0,1)`.
* Lebesgue large deviations of prime polynomials (`measureReal_large_primePoly_le`, Montgomery–Vaughan
  Gaussian moments) and Selberg near-line density (`exists_selberg_nearLine_zeroDensity`).
* Torsion energies: `weilPrimeKernel_renormalized_torsion_energy`, `torsionEnergy_self_add_log`,
  `orbitIntersection_self`, `log_eval_one_cyclotomic_real` (`log Φ_n(1) = Λ(n)`).
* The Möbius index formula: `moebius_reverse_inclusion_and_index_tfae`,
  `card_le_rank_quotient_paidIdeal_moebius`, `sum_visible_orders_le_rank_quotient_paidIdeal_moebius`,
  `finrank_quotient_paidIdeal_eq_zero_of_receiverBounded`.
* Trans-threshold pair correlation: `CoalescentSurplusAtMost`, `coalescentSurplus`,
  `oddEvenShiftPrimeCoalescentSurplus` [L/S].
* Chiral deformation: `CentralVanishingCeiling`, `HasDirichletLatticeDecay`,
  `tendsto_cube_mul_zero_of_dirichletLatticeDecay`.
* The scaling surface, the signature law, the golden datum, the complex fake, hyperelliptic RH by
  counting, `unitary_of_exteriorDetDeg_nonneg`.
* Bost–Connes and `Aff(Q)`: states induced from dilations; the integer successor forces the Hecke
  weight `(nd)^{−1/2}`; atoms are invisible to the successor.

## 2. Question 1 — is there a mechanism that circumvents or destroys a wall?

### 2.0 Admissibility: what a proposal must survive

The killed-routes ledger is, read positively, a test suite. A candidate mechanism is admissible only if
it passes all six of the following; every killed route fails at least one.

* A1 Selectivity. It must fail on the golden datum (`1 − 5X + 5X²`, `q = 5`: integral Witt series,
  functional equation, nonnegative Beurling counts, positive graph cone with Bézout, impure roots),
  on the complex fake (`q = 16`), and on the Liouville twin at every finite aperture. If the argument
  would go through for those, it proves nothing.
* A2 Non-circularity. The input must not be isomorphic under the width dictionary to a receiver
  (Chebyshev error, width, Baez–Duarte residual, Mertens budget, section functor with RR + Bézout,
  central ceiling, bounded Hecke defect). "Receivers as producers" is the most common failure.
* A3 Not a quadratic form on a commutative algebra. It must involve integers (orders of finite
  groups, dimensions, indices), non-commuting operations (successor with dilation), or two-point
  functions of the zero measure. Otherwise C1 and C2 apply.
* A4 Finite diagonal with bookkeeping. Any renormalization must come with its Hecke-covariance
  cocycle (section 2.1).
* A5 Aperture cost. A localizer at height `γ` must cost polynomially in `log γ`, since the horizon and
  the forcing threshold are separated by the factor `1/(2δ)` in log-aperture.
* A6 Non-graded output. Before RH, the mechanism must yield a statement that is not a proportion, a
  density exponent, or a finite-aperture floor.

### 2.1 Mechanism A: the Hecke cocycle of the torsion regularization (attacks C3, wall 14)

The one place where the corpus holds both a positive form and the actual prime kernel is the torsion
realization of Weil's prime side. The facts, all [L] from
`TheWeilPrimeKernelIsARenormalizedTorsionEnergy.lean` and `TheIntersectionOfTorsionOrbits.lean`:

* `P(m,n) = Λ(n/m) (n/m)^{−1/2}` for `m ∣ n` (symmetrized) is the discrete prime kernel.
* `T_r(m,n) = Σ_{ζ ∈ O_m, η ∈ O_n} −log|1 − r ζ η̄| = Σ_k (r^k/k) c_m(k) c_n(k)` is a Gram matrix of
  Ramanujan sums, hence PSD for `0 ≤ r < 1`; the gcd twist `G(m,n) = gcd(m,n)/φ(gcd)` is PSD; the
  Schur product `Q_r(x) = Σ x_m x_n G(m,n) T_r(m,n)/√(mn)` is PSD.
* `Q_r(x) + log|1−r| Σ x_n² → −Σ x_m x_n P(m,n) − Σ x_n² c(n)` as `r → 1`, with
  `c(n) = I(n,n)/φ(n)` and `I(n,n) = Σ_{ζ ≠ η ∈ O_n} log|ζ − η| = 2 φ(n) log n − kLogKernel(n)`
  (`orbitIntersection_self`), i.e. `I(n,n) = log|disc Φ_n|`.

Closed form of the counterterm [L + C]. From the Möbius transform `kLogKernel(n) = Σ_{d∣n} μ(n/d) d log d`
one gets `kLogKernel(n)/φ(n) = log n + Σ_{p∣n} log p/(p−1)` (checked on prime powers and on `n = 6`),
hence

    c(n) = log n − Σ_{p ∣ n} log p/(p − 1) = (1/φ(n)) · log |d_{Q(ζ_n)}|,

the discriminant of the cyclotomic field per unit degree: the self-intersection of the torsion orbit
`O_n` is the canonical degree of `Q(ζ_n)`. This is an adjunction formula, with the archimedean place
contributing `log n` and each finite place `p ∣ n` contributing `−log p/(p−1)`.

Two derived facts [R], pure bookkeeping on the theorem above. Let `(T_t x)_n = x_{n/t}` if `t ∣ n`,
else `0` (the prime-side Hecke action, `log n ↦ log n + log t`).

1. `P` is exactly Hecke-invariant: `P(tm, tn) = P(m,n)`, so `Σ (T_t x)_m (T_t x)_n P(m,n) = Σ x_m x_n P(m,n)`;
   and `Σ (T_t x)_n² = Σ x_n²`, so the divergent diagonals cancel. Therefore, without any
   renormalization,

       lim_{r→1} [ Q_r(T_t x) − Q_r(x) ] = − Σ_n x_n² β(n,t),
       β(n,t) = c(tn) − c(n) = log t − Σ_{p ∣ t, p ∤ n} log p/(p−1) ≥ c(t) ≥ 0,

   with equality `β = c(t)` when `gcd(n,t) = 1`. Dilation by `t` lowers the renormalized torsion
   energy by the discriminant cocycle; `β(n,t)` is the per-unit-degree log-norm of the relative
   discriminant of `Q(ζ_{tn})/Q(ζ_n)` [C].
2. Along a ladder `n, tn, t²n, …` the second difference of `c` vanishes as soon as every prime of `t`
   divides `n`: the renormalized torsion form is Hecke-balanced to second order off the ramification
   locus. Its failure to be balanced is supported exactly where `Λ` lives, on the prime powers.

Interpretation. The three forms have three Hecke behaviours: `W` invariant; `D` nondecreasing in `|L|`
with `E_f(L) ≥ 0`, zero iff RH; the torsion regularization of `−P` nonincreasing by an explicit
arithmetic cocycle. Positivity (`Q_r ≥ 0`) and Hecke invariance are traded against each other through
cyclotomic discriminants. The obstruction to a "positive renormalization" (the prior review's Q2,
B3.37) is therefore not analytic but arithmetic and cohomological: the potential `c` of the cocycle
is unbounded and non-invariant, and any invariant potential would have to be constant.

Admissibility. A1: the torsion picture realizes `Λ(t) = log|Φ_t(1)| = log N(1 − ζ_t)` as a norm, so it
is selective by construction (a Liouville twin has no torsion realization). A2: no RH input. A3: the
invariant is a cocycle with values in discriminants, not a quadratic form. A4: it is the bookkeeping.
A6: the target output is an identity (section 3, F1), not a grade. What it changes: the type of the
obstruction, from "a sign is missing" to "a cocycle must be trivialized in a positivity-preserving
class", which is a question with finite sub-problems.

### 2.2 Mechanism B: statistics over zero ordinates, and its exact limit (walls 1 and 3)

The walls ledger asks for moments of short prime polynomials over zero ordinates (its W15). The
corpus can almost compute them. For `P(s) = Σ_{p ∈ (N/2, N]} b_p p^{−(s−1/2)}`, `N = e^a`, and
`P̃(s) = Σ conj(b_p) p^{s−1/2}`, one has `P̃(ρ) = conj P(ρ*)`, so the holomorphic sum
`M_k = Σ_ρ m_ρ ŵ(γ/T) (P P̃)^k(ρ)` splits as

    M_k = Σ_{ρ on the line} m ŵ |P(ρ)|^{2k} + Σ_{off-line pairs} 2 m ŵ Re z_ρ^k,
    z_ρ = P(ρ) · conj P(ρ*) = Σ_{m,n} b_m conj(b_n) (n/m)^{δ_ρ} (n/m)^{i γ}.

Moments over zeros collide on the line and are Rosati-paired off it. `M_k` is a sum of smoothed Landau
formulas at the rational points `x = Π n_i / Π m_j`; for a dyadic prime window every such `x ≠ 1`
is a non-integer, so `Λ(x) = 0` and only the diagonal `x = 1` has a main term:
`M_k = ‖P^k‖² (T w(0) log T + c_w T) + O(error)`, valid for `k ≲ L/(4a)`, `L = log T`
[R; the integer-frequency case is `exists_zeroSum_dirichletPolynomial_le` [L], the rational-frequency
assembly is not in the corpus]. Conclusions [R]:

* Zero ordinates are moment-indistinguishable from Lebesgue heights for short prime windows, up to
  exactly the square-root threshold `k ≈ L/(4a)`; there is no prime correction at all for dyadic
  windows. Every moment-based statement about zero ordinates is a statement about Lebesgue heights
  plus the truncation loss `k log k`.
* At an aligned ordinate (all `γ log p` close mod `2π`), `Im z_ρ ≈ 0` and `z_ρ ≈ |P(ρ)|²`, so the
  Rosati moment of an aligned off-line pair is positive and indistinguishable from an on-line one.
* Transfer to the forcing half. An isolated zero at depth `δ` at the minimal forcing aperture
  `a₀ ≈ (log(768 A L a₀^{12}))/(2δ)` forces the autocorrelated prime sum
  `Σ Λ(n) n^{−1/2} 2A(log n) cos(γ₀ log n)` (support `[−2a, 2a]`) to exceed its Lebesgue-typical size by
  the factor `e^{2δa}/poly(a) ≈ L · poly(a)`. Chebyshev with `k = L/(4a)` Gaussian moments bounds the
  number of such ordinates by `T^{1 − δ/2 + o(1)}` at `a = a₀` and by `T^{1 − δ + o(1)}` as `a → √L`
  (isolation radius `e^a`). Both are weaker than Ingham's `T^{3(1/2−δ)/(3/2−δ)}` for every `δ > 0`
  (the inequality `3/2 − 3δ < (1−δ)(3/2−δ)` holds for all `δ > 0`).

So moments cannot resolve alignment, and they cannot beat classical density theorems even for isolated
zeros. The object left is the sign structure of `z_ρ^k` itself, which for a one-window `P` is positive:
the sign needed by the forcing half appears only when the test spans scales `≳ 1/δ`, which is the
forcing threshold. Walls 1 and 3 are the same wall seen from the two sides of the threshold. The one
positive residue: the smoothed Landau formula at rational `x` (no main term) would make the modulus
moments free; it is worth formalizing as a tool, not as a route.

### 2.3 Mechanism C: index theorems (attacks C2, wall 3)

The corpus has an index formula for the Möbius receiver [L]: for `0 < ε < 1/2`, the rank of
`W_{1/2} / paidIdeal(ε)` is bounded below by the number of zeros `ρ` with `1/2 + ε < Re ρ < 1` and
`ζ(ρ − ε) ≠ 0` (`card_le_rank_quotient_paidIdeal_moebius`), by the sum of visible orders, and equals
`0` for all `ε` iff RH (`moebius_reverse_inclusion_and_index_tfae`). This is the analytic index. The
BG README records that the critical paid ideal is not closed and that the defect has continuum
dimension, so the rank is `0` or at least continuum: the formula is Fredholm only after a completion
in which the visible part becomes an integer. Over `F_q` the corresponding index vanishes by Hodge
index, i.e. by Riemann–Roch on `C × C`; the "topological side" is the whole content. Record it as the
algebraic statement of wall 3: an upper bound on the visible index at one `ε < 1/2`, obtained without
passing through the zeros, would be quasi-RH (finitely many zeros to the right of `1/2 + ε`). The
mechanism for such a bound would be a finiteness-of-cohomology theorem (the arithmetic sources of
integers over `Z`: class groups, unit groups, Mordell–Weil), not a positivity.

### 2.4 Mechanism D: the missing base is zero repulsion is additive prime statistics (attacks C1, wall 1)

Deligne's amplification [C] bounds local eigenvalues of a sheaf on a curve by the pole structure of
the Rankin–Selberg tensor powers; its global step (Weil II) is an induction on dimension through a
fibration `X → B` over a curve, which makes the zeros of `ζ_X` the weights of a pushforward sheaf
at points of `B`, hence local. The two inputs are an Euler product with nonnegative coefficients
(free) and the purity of the coinvariants of the tensor powers, which needs big monodromy.

Over `Z` the corpus has shown the exact shadow of each input. `Spec Z` fibres over nothing, so the
zeros are never local eigenvalues: that is AKT's "the only families definable from `ζ` are abelian
twists; a non-abelian base would need additive data", and ACP's "affine maps of `Z` have genus
zero". Tensor powers of `ζ` itself have maximal invariants (pole order `2k`): abelian monodromy, and
AKT's depth-homogeneity (gain `≤ e^{δ · total length}`, free region ending at `X^k ≍ T` for every
`k`) is the resulting no-gain law [L]. The Rankin–Selberg square of the "zero motive" is Montgomery's
pair correlation, formalized unconditionally at leading order for `α < 1` [L]; the smallness of its
diagonal beyond `α = 1`, i.e. repulsion of zeros beyond the square-root threshold, is the `Z`-form of
"purity of coinvariants under big monodromy". TTPC has reduced its `4/3` target to a one-sided bound
on `oddEvenShiftPrimeCoalescentSurplus` [L/S], a statement about odd primes at even shifts, and
Goldston–Montgomery / Montgomery–Soundararajan [C] identify trans-threshold pair correlation with
the variance of primes in short intervals and with averaged Hardy–Littlewood pair counts.

Hence three programmes that look unrelated ask one question: AKT's non-abelian base, TTPC's
coalescent surplus, and THIM/BVI's Class III (Bézout, successor) information are the same object,
"monodromy = repulsion = additive prime correlations". This does not circumvent wall 1; it says which
arithmetic input is the right one, and that it is additive, not multiplicative.

### 2.5 Negative readings that save effort [R]

* Lattice-preserving multipliers (BGG's open problem: prove `CentralVanishingCeiling γ` from
  `HasDirichletLatticeDecay`). Multipliers that preserve Dirichlet log-lattice support are
  themselves Dirichlet series; they commute with Hecke, so by C1 none can contract the coupled class
  at an off-line pair. Expect the multiplier formulation to be rigid (Hamburger's theorem [C] is the
  classical form of this rigidity) and the ceiling to require a deformation acting on the successor
  variable, consistent with BGG's own guiding sentence. `W_β` and the quartet contractions exiting the
  lattice class with `Θ(σ^{−3})` decay is the first symptom.
* The `3 + 4 cos θ + cos 2θ` trick as a localizer at ordinate `γ` is a nonnegative-test positivity paid
  by the pole (APT's subsidy); its reach `c/log t` is the pole's. No trigonometric refinement enters the
  strip (P3 class).
* Positive-definite functions on `Aff(Q)` are exhausted (APD P13–P26): the successor must enter as a
  cocycle, holonomy, or finite-level fibre, never as a state.
* Direct amplification on `ζ` (tensor powers) gives the strip only (AKT); moments over zeros give
  nothing beyond classical densities (2.2).

### 2.6 Verdict on Question 1

No mechanism in sight destroys a wall. Mechanism A is the only one that changes the type of the
obstruction (from a missing sign to a cocycle to be trivialized) and every one of its steps is a finite
computation on existing theorems. Mechanism D identifies the right arithmetic input and shows three
programmes converging on it. Mechanisms B and C are clarifications of walls 1 and 3 that show where
effort is wasted.

## 3. Question 2 — three questions to focus on

Each attacks one cause of 1.3 and one wall of 1.2. Alignment at zero ordinates (the prior review's
Q1) is not among them because it is downstream: it is the prime-side reading of repulsion at a single
ordinate (F2) and of equivariance (F1).

### F1. Equivariant renormalization: trivialize the discriminant cocycle (C3, wall 14)

Statement. Determine whether there is a family `K_r` of PSD kernels on `N × N` with the torsion
construction's divergence profile (`log(1/(1−r))` per unit diagonal mass, uniformly in `n` and in
the finite support) whose renormalized limit is `−P − c₀ · Id` with `c₀` constant, hence
Hecke-invariant; or prove that for every such family the diagonal potential's Hecke variation is
cohomologous to `β`. Then compare with the zero side, where `D` is balanced iff RH.

Why this. It is the only place in the corpus where positivity and the actual prime kernel coexist;
the sign is lost at a place that is now computed and arithmetic (2.1). It is also the one question
whose finite sub-problems are decidable now.

First steps.
1. Formalize the prime-side Hecke action and the derived limit
   `lim [Q_r(T_t x) − Q_r(x)] = −Σ x_n² β(n,t)` from `weilPrimeKernel_renormalized_torsion_energy`.
2. Spectral growth of `P` on ladders versus the potential `c`. Schur's test fails for `P`
   (row sums `Σ_t Λ(t)/√t` diverge), so `P + c₀ Id` has negative directions on long ladders; compute
   the rate at which the most negative eigenvalue of `P` restricted to `{p^j : j ≤ J}` grows in `J`
   and compare with `c(p^J) = J log p − log p/(p−1)`. If the eigenvalue grows faster than `c`, no
   invariant potential exists and the cocycle class of `β` is an obstruction; if slower, an invariant
   PSD regularization is not excluded. This is a finite computation on prime-power ladders.
3. Add the zero mode (the `k = 0` Fourier term, orbit mass `φ(n)`) and the archimedean regularization
   so that the pole and `Γ` terms of the explicit formula appear on the torsion side; compute the Hecke
   cocycle of each local piece and verify they sum to zero (the explicit formula's own equivariance is
   the product formula for these cocycles). Then ask which Hecke-invariant diagonal modifications of
   `−P − c · Id` are renormalized limits of PSD families, and whether `D`, pulled back to prime
   coefficients through the explicit formula, is one.

Success: an identity expressing `E_f(L)` as a torsion-side renormalized second difference plus an
explicit discriminant term; this would be the first equation in the corpus with the Hecke defect on
one side and arithmetic on the other. Failure mode: step 2 shows the spectral growth of `P` exceeds
every potential, in which case the result is a new, sharp law ("no PSD regularization of the prime
kernel is Hecke-invariant"), to be recorded as such.

### F2. Repulsion beyond the threshold from additive prime statistics (C1, wall 1)

Statement. Prove `CoalescentSurplusAtMost β` for some `β ≤ 1/18`: a one-sided bound on the
odd-prime, even-shift coalescent surplus in the `T^{−1+η}` regime. The truth is `−1/144` under
Hardy–Littlewood / GUE; only an upper bound is needed.

Why this. It is the `Z`-form of big monodromy (2.4); three programmes converge on it; Montgomery at
`α < 1` is formalized; and it is the one place where the required input is a one-sided prime-pair
statement, i.e. the domain of sieve lower bounds, which produce nonnegative integers rather than
quadratic forms (A3).

First steps.
1. Write the surplus as an explicit weighted sum over prime pairs `(p, p + 2h)` with the corpus's
   reduction, and isolate the Mertens-type sum that carries its sign (the README records that the
   singular series transfers to a negative Ward–Mertens repulsion sum).
2. Calibrate on the Liouville twin: the twin must violate the bound (A1). The Liouville twin is the
   parity barrier of sieve theory in disguise (sieves cannot separate `Λ` from `λΛ`), so a pure sieve
   argument will stall exactly at the threshold; the bound needs Type II (bilinear) information. BVI
   already locates where it must come from: averaging over moduli / the CRT terminal block, since the
   Weil bound at one prime is order-sharp.
3. Compare the required regime with what unconditional variance results for primes in short intervals
   give on average over the shift.

Success: the first unconditional statement beyond `α = 1` in any form, and the first Class III input
into a zero statement. Failure: a proof that the surplus bound at `1/18` is parity-blocked; that would
be a new wall ("parity = threshold"), sharper than the present wall 1 and worth recording.

### F3. A section functor on the scaling surface with a non-circular Riemann–Roch (C2, wall 3)

Statement. On the scaling surface of `Z` (ACS: cycles `aH + bV + f`, explicit-formula pairing)
construct `h⁰` from cycles to `R_{≥0}`, of the form `log #(finite group)` or a theta log-volume
(AET's theta surface, where `h0(a,d) − h0∨(a,−d) = d` holds exactly), with
(RR) `h⁰(n f) ≥ (n²/2) W(f) − o(n²)` and (B) `h⁰(f) > 0 ⇒ f · H ≥ 0` for the polar class `H`,
such that the RR defect is not a prime-error term. The corpus proves abstract existence ⇔ Hodge ⇔ RH
and that the theta/box functors realize RR with the Chebyshev error `E(s) = e^s + s − 1 − ψ(e^s)` as
defect (circular by A2).

Why this. The sign must come from integers (AET's principle); Riemann–Roch is how dimensions become
inequalities for quadratic forms; it is the single step of Weil's proof the corpus marks as missing.
The arithmetic Riemann–Roch of van der Geer–Schoof / Faltings [C] has the discriminant as its defect,
which is exactly the quantity F1 identifies as the self-intersection of torsion orbits: F1 and F3 are
the two ends of one adjunction formula.

First steps.
1. Identify the canonical class `K` of the scaling surface: the archimedean term of the explicit
   formula (the `Γ`-factor, the relative dualizing sheaf at infinity) is the candidate; test whether
   `h⁰(K − √N · A)` for the box classes (`χ = N`, log-torsion `ψ(N)`) is the log of a finite group.
2. Calibrate on `F_q[t]` (ACG's gauge calibration): the functor must reduce to `dim H⁰` on `C × C`.
3. A1: the golden datum has ampleness and Bézout without RR; the functor must exhibit its RR failure.

Success: an RR inequality with a computable defect that is a discriminant, regulator, or class-number
quantity. Failure: a theorem that every natural `h⁰` on the scaling surface has the Chebyshev error
as defect ("sections over `Z` count primes"); also a new wall statement.

## 4. Question 3 — the field the walls ask for

### 4.1 The questions (the walls, read as questions mathematics cannot currently answer)

* Q-a Can a positive form on an infinite-rank lattice be renormalized while keeping its covariance
  under a commutative semigroup of dilations? Over `Z` the answer is "no, by a cocycle of
  discriminants" (2.1) and the question becomes which cohomology that cocycle lives in. (C3)
* Q-b Where do integers come from, on the prime side, for forms that are not quadratic in a Fourier
  transform? What replaces `dim H⁰`? (C2)
* Q-c What non-commutative structure at the arithmetic point makes the local type at a spectral pair
  elliptic at polynomial cost in `log γ`? The successor is the only candidate and states on `Aff(Q)`
  are exhausted. (C1)
* Q-d What is the base? Over what does `Spec Z` fibre so that global spectral data become local?
  (C1, Deligne)
* Q-e Which statistics of the zero divisor are two-point rather than quadratic, and equivalent to
  additive prime data? (C1/C2)

### 4.2 Point of view

1. Two computations of one number. Every sign is the difference of two computations of one Euler
   characteristic, one geometric (sections, counts, indices), one spectral (eigenvalues). The field
   studies pairs of computations and their defects, not forms. Its central object is the defect
   functional `Δ = D − Re W` and its deformation theory.
2. Equivariance/positivity duality. Every object carries an equivariant pairing and a positive
   pairing; the theory is the theory of their difference. RH is the statement that one object carries
   both. The finite-level models (curves over `F_q`, Dirichlet families, finite prime windows) carry
   both; the field studies the limit in which they separate, and the square-root threshold is the
   separation scale.
3. Renormalization is cohomology. Counterterms are cocycles on the Hecke semigroup with values in
   arithmetic quantities (discriminants, differents, conductors); positivity-preserving
   renormalization means coboundary; the equivariance of the explicit formula is the product formula
   for the local cocycles.
4. Additive structure is monodromy. The successor is the only non-abelian datum. It appears as
   holonomy (BGG), as repulsion (TTPC), as Class III information (THIM, BVI); the field treats
   "repulsion of zeros" and "monodromy of the base" as one invariant.
5. Calibration is an axiom. Every construction must reduce to a step of Weil's proof over `F_q[t]`,
   must fail on the golden datum and the complex fake, and must distinguish `Λ` from `λΛ`.

### 4.3 Objects

* The dilation surface `𝔇` of `Z`. Not constructed; known through charts, each already in the corpus:
  the scaling surface (ACS), the theta surface (AET), the torsion circle with its orbit intersection
  (AET), the gauge torus `(R/Z)^P` (BGG, ACG), the Bohr polydisk and the critical Wiener algebra (AOT),
  the horizon space with affine pushforwards (BG), the `ax + b` crossed product (APD, HTGeometry).
  The field's first task is the transition maps between charts.
* Cycles: Hecke graphs `Γ_x`, torsion orbits `O_n`, tests `f`; the polar class `H`; the archimedean
  class (`Γ`-factor), candidate canonical class `K`.
* Pairings: `W` (geometric), `D` (spectral), the torsion energies `Q_r` (regularized), and the defect
  functional.
* Cocycles: the discriminant cocycle `β`; the Hecke defect `E_f(L)`; gauge charges.
* Section functors: theta `h⁰`, box/lcm classes (`ψ(N) = log |Z / lcm(1..N) Z|`), `log #(Z/Q_N Z)`,
  and their RR defects.
* The zero motive and its Rankin–Selberg square: pair correlation; the coalescent surplus.
* Local types at a spectral pair: hyperbolic (boost, Hecke), elliptic (swap, functional equation),
  unipotent (successor); signatures; the signature law (one positive square plus the negatives).
* Index objects: paid ideals, obstruction hulls, obstruction modules, visible orders.

### 4.4 Language

Intersection numbers for atomic cycles (orbit intersections, `I(m, mt) = φ(m) Λ(t)`); adjunction
(self-intersection equals a log-discriminant); cocycles and coboundaries on the Hecke semigroup with
arithmetic coefficients; defect functionals and their second differences; local types and
signatures; indices, with the `0`/continuum dichotomy resolved by Fredholm completions; thresholds as
a weight variable (the aperture-to-height ratio plays the role of the weight in Weil II: the
square-root threshold is weight `1/2`, the forcing aperture is the weight at which the odd sector
becomes definite).

### 4.5 Foundational principles, each paired with the exhaustion law it is designed to evade

* P1 No positivity without a count or an index. A sign is admitted only as the log of an order, a
  dimension, or an index. (Evades counting and statistics: those laws concern quadratic forms.)
* P2 No count without covariance bookkeeping. Every regularization carries its Hecke cocycle.
  (Evades renormalization and pole order.)
* P3 No localization by multiplicative means. Localizers must involve the successor or finite-level
  fibres. (Evades gauge, hyperbolicity, resonance, conductor, localization.)
* P4 Two-point before one-point. Statements about individual zeros are derived from statements about
  pairs; the forcing half is already a pair statement. (Evades detection and collision.)
* P5 Calibration is mandatory: `F_q`, golden datum, complex fake, Liouville twin. (Evades dominated
  twins and "positive data is not purity".)
* P6 Non-circularity is checked by the width functor: an input is admissible iff it is not
  isomorphic to a receiver. (Evades completion and the twenty-four circular endpoints.)

### 4.6 Criteria for a result to count

* Non-graded: an identity (for instance `E_f(L)` as a torsion-side second difference), a finiteness
  statement (an obstruction module of finite visible rank), the sign of a two-point statistic beyond
  the threshold, or an RR inequality whose defect is not a prime error.
* Selective: it fails on the golden datum and on the Liouville twin.
* Covariant: it comes with its cocycle.
* Calibrated: it reduces to a step of Weil's proof over `F_q`.
* Cost-polynomial: any localization costs polynomially in `log γ`.

### 4.7 Research topics, in order

* T1 Hecke cocycles of torsion regularizations (F1); spectral growth of `P` on ladders against the
  discriminant potential; the zero mode and the archimedean regularization on the torsion side.
* T2 Section functors with discriminant defects (F3); the canonical class of the scaling surface;
  Serre duality on the theta surface.
* T3 The Rankin–Selberg square of the zero motive: the coalescent surplus sign; Type II input against
  parity (F2); odd collisions and intrinsic exterior squares over `Z` (APol's open list;
  `unitary_of_exteriorDetDeg_nonneg` is the `F_q` calibration).
* T4 The successor as a cocycle: cyclic cohomology and index pairings on the `ax + b` crossed product
  (replacing states, which APD exhausted); the holonomy of the Catalan plaquette `{2, 3, 4}` as a
  2-cocycle; what an index pairing with the Möbius receiver's K-class would compute.
* T5 Fredholm completions of the obstruction module: where the `0`/continuum dichotomy becomes an
  integer; relation to the index formula below width (AOT's open problem).
* T6 Transition maps between the charts of `𝔇`, first torsion circle to scaling surface (the orbit
  intersection law against the prime term of `W`), then gauge torus to Bohr polydisk.
* T7 The calibration laboratory: `F_q[t]` gauge calibration; golden datum; complex fake; Liouville
  twin; Dirichlet families, where both equivariance and positivity hold at finite level, studied in the
  degeneration `q → ∞` against `T → ∞` (`sum_Mform_PXc_dirichlet` is the first such mean square).
* T8 Thresholds as weights: a filtration of tests by aperture-to-height ratio; the forcing aperture
  as the weight where the odd sector becomes definite; the square-root threshold as weight `1/2`.

### 4.8 Name, and relation to the prior proposal

Call it arithmetic intersection theory with covariant renormalization, or the theory of the
arithmetic diagonal. The prior review's "arithmetic electrostatics of the zero divisor" is the
zero-side chart of it; the present proposal is organized around the prime side (torsion orbits,
sections, cocycles) and the pairing between the two sides. They are compatible and complementary:
electrostatics supplies the detection theorems (field, reserve, terminals), and this field is meant to
supply the exclusion step, which over `F_q` is an integer.

## 5. Assessment

* The three walls are one gap (1.3): commutativity of the Hecke algebra, trace-linearity of every
  receiver, and the infinite diagonal. Over `F_q` the surface `C × C` removes all three at once.
* The one opportunity that changes the type of the obstruction is Mechanism A: positivity and Hecke
  invariance of the prime kernel are traded through a cocycle of cyclotomic discriminants, computed in
  2.1 from formalized identities. Its first sub-problems are finite computations on prime-power ladders
  and should be done first.
* The decisive arithmetic input, if any is accessible today, is the sign of a two-point prime statistic
  (F2). The parity barrier is where it will stall if it stalls; a stall there is itself a new wall.
* Riemann–Roch over `Z` (F3) is the destination; the corpus has shown which naive functors are
  circular; the next functor to try is one whose defect is a discriminant, because that is the only
  arithmetic quantity the corpus has found playing the role of `2 − 2g`.
* Moments over zero ordinates (2.2) and multiplier deformations (2.5) should not absorb further effort.

## Appendix A. Declarations cited

| declaration | module | what it says |
|---|---|---|
| `odd_sector_nonneg_forces_offLine_companion` | ArithmeticPolarization/TheForcingHalfOfEllipticLocalization | odd-sector nonnegativity at an off-line ordinate plus depth dominance `hbig` forces an off-line companion within `R` |
| `even_sector_summand_nonneg` | same | even-sector summands at ordinate `γ` are `m |tr|² ≥ 0` |
| `exists_zeroSum_dirichletPolynomial_le` | RHTower/ZetaZeroDirichletPolynomialMoment | smoothed Gonek lemma for integer-frequency Dirichlet polynomials over the zeros |
| `exists_smoothedLandau_le`, `_neg_le` | RHTower (smoothed Landau) | smoothed Landau formula, both exponent signs |
| `tendsto_montgomeryForm_div_leadingOrder` | RHTower/MontgomeryPairCorrelationLeadingOrder | `F(T^α, T) / ((T/2π) α log T) → 1`, `0 < α < 1`, no hypothesis on real parts |
| `measureReal_large_primePoly_le` | RHTower/WeilConePrimePolynomialMoments | Lebesgue large deviations of prime polynomials via Gaussian moments |
| `exists_selberg_nearLine_zeroDensity` | RHTower (Selberg density) | near-line zero density with decay `e^{−a/1200}` |
| `weilPrimeKernel_renormalized_torsion_energy` | ArithmeticEffectivityTheory/TheWeilPrimeKernelIsARenormalizedTorsionEnergy | `Q_r ≥ 0` and `Q_r + log|1−r| Σ x² → −P − Σ x_n² I(n,n)/φ(n)` |
| `torsionEnergy_self_add_log` | same | the diagonal torsion energy plus `φ(n) log|1−r|` converges to `−log|disc Φ_n|` |
| `orbitIntersection_self` | ArithmeticEffectivityTheory/TheIntersectionOfTorsionOrbits | `I(n,n) = 2 φ(n) log n − kLogKernel(n)`, the log-discriminant of `Φ_n` |
| `log_eval_one_cyclotomic_real` | (cyclotomic log formulas) | `log Φ_n(1) = Λ(n)` |
| `heckeDefect_eq_second_difference`, `heckeDefect_le_strip`, `heckeDefect_sq_le_two_scale` | (Hecke defect) | the defect formula, the strip bound, the two-scale inequality |
| `moebius_reverse_inclusion_and_index_tfae` | ArithmeticOrientationTheory/AnIndexFormulaForTheActualReceiver | RH ⇔ paid ideal is everything ⇔ obstruction hull empty ⇔ rank of the quotient is `0` |
| `card_le_rank_quotient_paidIdeal_moebius` | ArithmeticOrientationTheory/TheMoebiusReceiverCountsItsOffLineZeros | translated off-line zeros bound the rank below |
| `sum_visible_orders_le_rank_quotient_paidIdeal_moebius` | ArithmeticOrientationTheory/VisiblePoleJetsBoundThePaidIndex | visible orders bound the rank below |
| `CoalescentSurplusAtMost` | ArithmeticCastelnuovoSeveri/CoalescentSurplusAndTransThresholdProportionLaws | the smooth-window coalescent surplus hypothesis at budget `β` |
| `oddEvenShiftPrimeCoalescentSurplus`, `coalescentSurplus` | TransThresholdPairCorrelation | the surplus and its odd-prime even-shift reduction |
| `CentralVanishingCeiling`, `HasDirichletLatticeDecay` | BiarithmeticGaugeGeometry/ChiralDeformationAndNonRigidityOfHeightCoupledSystems | the ceiling on central vanishing over height-coupled systems; `O(2^{−σ})` lattice decay |
| `unitary_of_exteriorDetDeg_nonneg` | (exterior square over `F_q`) | nonnegative exterior determinant degrees force unitarity |
| `sum_Mform_PXc_dirichlet` | (Dirichlet family mean square) | the family mean square over characters mod `q` |

## Appendix B. Gaps in this report

* `hard-obstacles.md` does not exist; `route-obstacles.md` and `obstacles-summary.md` were used.
* Nothing was compiled; [L] labels are the ledgers' or confirmed by reading statements, not by
  building.
* Every [R] item is unproved; the two computations in 2.1 are bookkeeping on formalized theorems and
  should be checked by formalizing them; the estimates in 2.2 are heuristic.
* [C] items rely on the literature as remembered (Deligne, Weil I and II; Goldston–Montgomery 1987;
  Montgomery–Soundararajan 2004; Hamburger 1921; van der Geer–Schoof 2000; the cyclotomic
  discriminant formula) and must be cited from sources before use.
