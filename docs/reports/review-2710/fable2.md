# fable2: a consolidated reading of the RH corpus, and the tools it says are missing

Review 2710. Written 2026-10-27.

## 0. Scope and conventions

Sources read in full: `docs/reports/rh-current-frontier-map.md`, `docs/reports/rh-killed-routes.md`
(the prose; the closing scoped catalogues are lists of no-go numbers), `review-2710/walls-ledger.md`,
`review-2710/route-unification-ledger.md`, and, because `review-2710/hard-obstacles.md` does not
exist, the two documents that carry that content: `review-2710/route-obstacles.md` (titled "Hard
mathematical obstacles: routes, candidates and supporting programmes") and
`review-2710/obstacles-summary.md`. The README of each of the 34 programme folders named in the
brief was read. No other markdown was read.

The Lean corpus was consulted only through `scripts/formal_tools.py research` (26 queries) and by
reading the module headers it surfaced. Nothing was compiled, no axiom audit or `sorry` grep was
run, no umbrella wiring was checked. The brief forbids verifying other agents' work; this report
interprets it.

Tags. [D] stated in the documents read. [L] a Lean declaration surfaced by the corpus search whose
statement I read; the proof was not checked. [M] a recollection of the literature, unverified, no
web. [R] my own reading or proposal. The working log, with every search and every fact extracted,
is `logs/fable2-review-2710.log`.

## 1. The research in one picture

### 1.1 Two forms and one defect

The whole corpus lives between two quadratic forms on the test space.

* The Weil form `W(f) = Σ_ρ f̂(ρ)`: Hecke-equivariant by construction, computed by the explicit
  formula as archimedean minus prime plus pole. `W ≥ 0` on all tests iff RH. [D]
* The collided form `D(f) = Σ_ρ m_ρ |f̂(ρ)|²`: positive by construction, computed from the Laplacian
  of `log|ξ|` through theta prefixes. Hecke-equivariant iff RH. [D]

`Re W = D − Δ`; the Hecke defect of `D` is a moment of inertia of the test; uniform caps on the
defect are zero-free strips. [D] Pairings of a zero with its conjugate (`ρ ↔ ρ̄`, collided) are
automatically positive; pairings with its reflection (`ρ ↔ 1−ρ̄`, Rosati) are positive iff RH. [D]
Everything unconditional in the corpus is a statement about collided pairings or about tests on
which the two kinds of pairing cannot be told apart.

### 1.2 The local type: every symmetry is a boost

At an off-line pair `{ρ, 1−ρ̄}` the Weil form restricted to the two-dimensional fibre has
signature `(1,1)`. The Hecke operators, the archimedean flow and the gauge twists act on that
Lorentz plane as boosts; the functional equation conjugated by the flow swaps the two null
directions; the successor acts unipotently; the circle rotations act elliptically but in the
additive dual `ℚ/ℤ`, not on the fibre. Positivity would force isotropy. [D]

Reading [R]: the symmetry group available to any argument acts on each off-line fibre by a
non-compact group. A form invariant under a boost cannot be definite on the plane the boost
preserves. RH is therefore not a symmetry statement about `W`; it is a symmetry-breaking statement.
Whatever proves it must be something `W` is *not* invariant under.

### 1.3 The gauge torus and the successor connection

The prime gauge torus `Ω = ∏_p S¹` acts on sources by completely multiplicative unit twists.
Multiplicative data determine a source only up to its orbit; square-class couplings are blind; on
nonnegative tests `ζ` is the worst point of its orbit. [D] The margins: the Selberg source keeps a
coefficient margin `2 log² p` under a sign flip at `p`, while the atomic Weil form's margin on the
pair vector at `p` is `4 Λ(p)/√p`, which vanishes with `p`
(`gaugeMargin_window`, `gaugeMargin_atomicWeilForm` [L]). Every real-sign gauge is unitarily
equivalent to the Euler point on ratio shifts and product crossings on every finite horizon
(`realSign_latticeForm_eq` [L]): no form built from diagonal archimedean weights, horizon cutoffs
and multiplicative incidences distinguishes `ζ` from Liouville.

The one structure the torus does not preserve is the successor. The successor connection
`A_ω(n) = conj(χ_ω(n)) χ_ω(n+1)` is flat on `[1, N]` iff `ω(p) = 1` for every prime `p ≤ N+1`
(`succConn_flat_iff_primes_eq_one` [L]); two successor links on `2 → 3 → 4` already reconstruct the
prime phases `ω(2), ω(3)` (`catalan_holonomy_two`, `catalan_holonomy_three` [L]). Dirichlet
characters are the gauge points of the finite subgroups; averaging over the level-`q` subgroup
projects a pair onto congruence, and a successor pair `(n, n+h)` survives exactly when `q ∣ h`,
uniformly in `n`, whereas the archimedean line moves a successor pair by at most `2π|ξ| h/n` and
cannot resolve it (`sum_twist_dirichletGauge_succ`, `norm_archPair_sub_one_le` [L]).

Reading [R]. Which torus points carry a positive Weil form? The Euler point (RH), the Dirichlet
characters (GRH), and nothing else one can name: the Liouville point has `L(s,λ) = ζ(2s)/ζ(s)`, with
a pole on the critical line and zeros on `Re s = 1/4` [M], and its atomic prime form indeed reaches
`−(log N − C)` on the Liouville pole vector (`atomicWeilForm_liouvillePole_le` [L]). A completely
multiplicative function that is periodic is a Dirichlet character [M]. So the positivity locus of
the torus is, as far as anything is known, exactly the **successor-periodic locus**: the points
whose connection is flat for some power `S^q` of the successor, with the Euler point the unique
point flat for `S` itself. Every tool that is torus-invariant is blind to this locus by
construction. Every proof of RH must use the successor. Classical theory uses it exactly once:
periodicity gives Gauss sums gives the functional equation (Poisson summation). One identity is not
a sign.

### 1.4 Renormalization: the rank of the counterterm is the regulator

The programme of RBG and RAPT proves a complete bookkeeping of what each regulator costs. [D][L]

| regulator | counterterm | survival |
|---|---|---|
| Abel (torsion germ) | identity | nothing |
| spacing | scalar, covariant up to tame ramification | indefinite |
| horizon, uniform profiles | polar, rank one | one direction |
| horizon, torsion orbits | unbounded rank (identity on the arithmetic factor ⊗ polar on the scale factor) | nothing of rank `≤ J` suffices |
| lattice germ (archimedean) | rank one, polar hyperplane | the constant mode |

The coupled survival law: a partner whose counterterm has rank `r` pays at most `r` prime
directions, and pays them exactly when matched (`finrank_primeSurvival_le_rank`,
`primeSurvival_rankOne` [L]); the archimedean place, rank one, pays exactly the arithmetic point
`O_1`, the one torsion orbit whose Ramanujan mode is the constant mode
(`primeSurvival_jointGram` [L]). The Hecke cocycle of the torsion renormalization is
`β(n,t) = log t − (tame different)`, and it is not the coboundary of a bounded potential
(`heckeCocycle_eq`, `not_exists_bounded_potential` [L]): no bounded change of the diagonal makes
the renormalized torsion form Hecke-covariant. The covariant counterterm is `log N + O(1)`; the
torsion germ needs `(3/2) log N`; the half-logarithm is the anomaly. [D]

The polar matching is gauge-charged though each place's counterterm is blind: at the Euler point
the prime divergence matches the archimedean polar direction with coefficient `+1`, at the
Liouville point with `−1` (`abs_liouvilleForm_stepProfile_add_le` [L]). Reading [R]: the form's
entire gauge charge at the horizon is concentrated in the single polar direction, and that
direction is exactly the one the pole pays for. On the degree-zero complement, where RH lives, the
gauge charge of the form is of size `4 log p/√p`: invisible. This is the precise content of the
frontier's "no form margin".

### 1.5 Atomic resolution and the spacing scale

The stability law (ArithmeticElectrostatics): put a bump of width `w` with weight `x_n` at each
atom `log n`, `n ≤ N`. For `w ≤ atomicWidth N = N^{−O(1)}` the archimedean self-energy (the Lévy
gain `e^{−1/2} log(δ_N/2w)`) pays the prime form, `M(f) ≥ 0` (`markovEnergy_atomicTest_nonneg`
[L]); adding the pole, `Re W(f) + 2 S(f)² ≥ 0` with a rank-one counterterm, and `Re W(f) ≥ 0` on
the cone `|S| ≤ |C|`, which contains every nonnegative atomic test
(`re_W_add_sinh_sq_nonneg`, `re_W_atomicTest_nonneg_of_nonneg` [L]). This holds for every sign
twin alike. [D] It stops at the spacing `δ_N = log(1 + 1/N) ≍ 1/N`, where the gain is `O(1)` and
the prime counterterm is still `≥ √(log 2 (log N − C))`: "the matching stops exactly where the
tests begin to see the zeros" (module header [L]).

Reading [R]: in Montgomery's coordinates the atoms `n ≤ N` are a Dirichlet polynomial of length
`x = N` and a width `w` resolves heights `T ≍ 1/w`; the spacing scale is `T ≍ N`, that is
`x = T^α` with `α = 1`. The corpus has proved Montgomery's pair-correlation asymptotic
`F(T^α, T) / ((T/2π) α log T) → 1` unconditionally for every `0 < α < 1`, uniformly on compacts,
for all zeros with multiplicity and no hypothesis on their real parts
(`tendsto_montgomeryForm_div_leadingOrder`, `eventually_montgomeryForm_div_leadingOrder_uniform`
[L]); the pair form is a height mean square, hence positive (`montgomeryForm_eq_integral_height`
[L]). The one lossy step is the sharp-window truncation, error `O(x L² log T)`, which at `x = T`
exceeds the main term (`MontgomeryPairFormTruncation` header [L]). The Montgomery–Vaughan Hilbert
inequality with constant 26 and the Landau–Gonek zero sum with error `√n + √T` per coefficient
are in the corpus (`mvHilbert_twentySix`, `exists_zeroSum_dirichletPolynomial_le` [L]). The
corpus is one truncation lemma away from the spacing scale on the zero side.

### 1.6 Weil's argument over ℤ, layer by layer

What transfers: the identities, the square theorem, the budget (free); the Hodge index statement
itself: the positive index of the intersection Gram of the von Mangoldt kernel is at most
`1 + #{ρ : Re ρ > 1/2}` (`posIndex_intersectionGram_le` [L]), so RH is exactly the Hodge index for
the scaling surface; the Hecke correspondence scales the pairing by its degree
(`pair_heckeCorrespondence` [L]). Linear Riemann–Roch holds on the base
(`arithH0_riemannRoch : h⁰(d) − h⁰(−d) = d` [L]); the quadratic one needs a surface. [D]

What does not: the base. Over `𝔽_q` every place acts on one Frobenius ladder and two places share
every lag divisible by `lcm(d, d′)`; over `ℤ` the ladders of distinct primes never charge the same
pair of orders, and the successor joins two different ladders at every step but `1 → 2`
(`frobeniusTower_lcm_ne_zero`, `ladderKernel_mul_ladderKernel_eq_zero`, `sameLadder_succ_iff` [L]).
The same fact in Witt language: the cross-pair Frobenius fibre coefficient at distinct primes is
zero (`deningerBigWittCrossPairFrobeniusFiberCoefficient_zero` [L]), and Witt integrality is not
purity [D]. The diagonal (self-intersection) is regulator-dependent [D]; the self-pairing is
unbounded below on every finite-reading fibre (`scalingSurface_self_pair_unbounded_below…` [L]),
so no finite-rank reading sees the index. "Frobenius at infinity" exists only as the conjugation
involution on the zero copy (`xiZeroCopyConjEquiv` [L]). `ζ` is not the Selberg zeta of a
hyperbolic surface (`false_of_mem_of_primeLengthTraces` [L]).

### 1.7 One wall [R]

The three walls are three faces of one fact. The Euler point is characterized **additively**: it is
the unique flat point of the successor connection. Every positivity tool in the corpus is
**multiplicative**: torus-invariant, hence blind to that characterization.

* W1 (critical arithmetic sign): the sign is a successor datum; the tools are torus-invariant.
* W3 (transfer): the successor is the only carrier of the datum, and it crosses every ladder; nothing
  carries a sign from one local tower to another.
* W14 (realization): the one structure that is simultaneously additive and multiplicative, a ring
  endomorphism (Frobenius), does not exist on `ℤ`; its substitutes (Witt and Adams operations) are
  transverse at distinct primes and give integrality, not purity.

The deepest positive fact the corpus has is therefore the pair of theorems that the archimedean
place pays exactly the arithmetic point `O_1` and that `O_1` is the fixed point of every power map:
the one place where the additive structure (the constant mode `c_1 ≡ 1`, the lattice `[1,N]`) and
the multiplicative structure (the torsion orbits) touch, and it buys one direction, the pole's.

## 2. Question 1: a mechanism that could circumvent a wall

Three candidates, in order of how much of the corpus already points at them. Each is marked by the
wall it attacks, the corpus facts it rests on, what it would prove, the first checkable lemma, and
the criterion that would kill it. None is a proof sketch.

### M1. Positivity by closure: a combinatorial Hodge theory for the Weil form (attacks W14, uses the gauge charge against W1)

**Facts it rests on.** RH is the Hodge index of the scaling surface pairing
(`posIndex_intersectionGram_le` [L]). The pole term of Weil's form is a rank-two form of signature
`(1,1)`, `2C(f)² − 2S(f)²` (`re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq` [L]): this is
the hyperbolic plane `⟨H, V⟩` of the horizontal and vertical fibres of a product surface, with
`H² = V² = 0`, `H·V = 1`. The off-diagonal intersection numbers of distinct atoms are the prime
kernel `Λ(n/m)(n/m)^{−1/2}`, nonnegative at the Euler point and only there: for a twin `ε` they are
`ε(n/m)Λ(n/m)(n/m)^{−1/2}`. The diagonal is free within the regulator class [D]. Positivity is
known on nonnegative tests [L] and after adding one pole direction on atomic tests [L].

**The mechanism.** In the theory of Lorentzian polynomials [M: Brändén–Huh] a homogeneous
polynomial with nonnegative coefficients and M-convex support is Lorentzian when every
`(d−2)`-fold derivative is a quadratic form with at most one positive eigenvalue. Volume polynomials
of projective varieties are Lorentzian (that is the Hodge index, via Khovanskii–Teissier); the class
is closed under products, nonnegative linear substitutions and differentiation; and the Hodge index
for matroids was proved inside this circle of ideas with no variety at all [M: Adiprasito–Huh–Katz].
At degree 2 the Lorentzian condition on a form with nonnegative coefficients is literally "at most
one positive eigenvalue", that is the Hodge index, that is RH; there is no gain. The gain is in the
**closure properties**: a quadratic form that is the Hessian of a degree-`d` Lorentzian polynomial
inherits its signature from the structure of that polynomial, and products of Lorentzian
polynomials in disjoint variables are Lorentzian.

This matches the corpus's own decomposition exactly. The prime kernel is a sum of transverse
towers, one per prime, and the towers of distinct primes never charge the same pair of orders [L].
In the product picture this says the local factors live in **disjoint variables** (one block of
variables per prime), and the Euler product, not the explicit formula's prime sum, is the
decomposition under which positivity is a closure property. Sums of Lorentzian polynomials are not
Lorentzian; products are. The archimedean place is then the only object that sees all primes at
once, and it does so through the scale map `n = ∏ p^{a_p} ↦ Σ a_p log p`, a **nonnegative linear
substitution** of the disjoint prime variables into the single scale variable `u = log n`, which
is again a Lorentzian-preserving operation [M]. The pole term is the hyperbolic plane, the one
positive direction every Lorentzian signature has (the radial direction of the homogeneity).

**What it would prove.** If the atomic Weil form in nef coordinates (atoms plus the two pole
directions, diagonal chosen in the regulator class so that all intersection numbers are
nonnegative) is the Hessian of a polynomial obtained from local Lorentzian factors by products,
nonnegative substitutions and derivatives, then it has at most one positive eigenvalue for every
`N`, which is RH for the `N`-atom truncations and, letting the widths go to the local spacing, RH.

**Why it is not blind.** The hypothesis of the theory is nonnegativity of coefficients. That is
`Λ ≥ 0`, the Euler point. A gauge twist destroys the hypothesis, visibly. This is the first
mechanism in the corpus's vocabulary that consumes the gauge charge at the input instead of
hoping to find it at the output. The failure at the Liouville point (a pole on the line) is
*explained*: negative coefficients.

**First checkable lemma (finite, and over `𝔽_q`).** Over `𝔽_q` the tower kernel on the Frobenius
ladder is `frobeniusTower q d i j = q^{−|i−j|/2}` on lags divisible by `d` [L]. Is the intersection
form on the span of the Frobenius graphs, in nef coordinates `Γ_{F^k} + aH + bV`, the Hessian of a
Lorentzian polynomial built from the **ladder alone**, with no surface? Weil's theorem says the
signature is right; the question is whether a degree-3 or degree-4 lift with M-convex support on
the ladder exists and whether its product over places (disjoint variables) followed by the degree
substitution reproduces the global form. This is a finite computation for small genus and small
`q`, and it decides whether "Hodge index from the ladder" is a thing before anything is asked over
`ℤ`. Over `ℤ`, the parallel computation: for `N ≤ 30`, which diagonals in the regulator class put
the atomic Weil matrix in nef coordinates, and is the resulting quadratic the Hessian of a degree-3
Lorentzian polynomial supported on divisibility chains?

**Unification it buys [R].** The corpus holds two "exactly one positive direction" formulations
proved only asymptotically: the Hodge index of ArithmeticCastelnuovoSeveri (positive index
`≤ 1 + #off-line`) and the Turán/Jensen log-concavity of horizontal slices
(`eventually_volume_sliceCoeff_turanSeq_ge_ninth` [L], a density statement). Real-rooted
polynomials with nonnegative coefficients are Lorentzian [M], and Pólya's criterion (RH iff all
Jensen polynomials of `ξ` are hyperbolic) is a Lorentzian statement about coefficient sequences;
the eventual hyperbolicity theorem [M: Griffin–Ono–Rolen–Zagier] is the exact analogue of the
corpus's "positivity far from the critical regime" (Montgomery `α < 1`, atomic widths
`N^{−O(1)}`). One language for both.

**Kill criterion.** If over `𝔽_q` no bounded-degree lift from the ladder exists and the degree must
grow with the lag (which would mean the Lorentzian structure is Deligne's tensor-power argument in
disguise), the mechanism reduces to the base problem in sharper form: "the degree of the
Lorentzian lift is the weight", and W14 stands. That outcome is itself a positive survivor worth
recording: a quantitative statement of what the base is for.

### M2. The successor-periodic locus and the affine base (attacks W1 and W3)

**Facts it rests on.** The Euler point is the unique flat point of the successor connection and
two successor links reconstruct the prime phases [L]. Dirichlet characters are the finite-subgroup
gauge points, and successor pairs are resolved by finite subgroups and not by the archimedean line
[L]. Cell dilation and successor satisfy the Baumslag–Solitar relation
`cellDilate m (succShift q) = succShift^[m] (cellDilate m q)` [L]. The integer successor forces the
Hecke weight `(nd)^{−1/2}` and the Bost–Connes temperature is the Hecke exponent
(`bc_successor_hecke_exponent` [L]). Liouville flips the polar matching [L]. The Weil bound for
Kloosterman sums, `‖K(ψ,a)‖ ≤ 2√p`, is in the corpus (`kloosterman_weil_bound` [L]): RH over `𝔽_p`
for the one curve whose point count is an additive character twisted by a multiplicative inverse,
an additive-multiplicative positivity living on `ℤ/p`.

**The mechanism.** Stop treating the orders `ℕ` as a multiplicative monoid with an additive
nuisance. The object is the affine monoid `ℕ ⋊ ℕ^×` generated by the successor `S` and the
dilations `M_p`, with the relations `M_p S = S^p M_p` the corpus has already formalized on cells.
Its operator algebra is known [M: the Toeplitz algebra of the affine semigroup over `ℕ`,
Cuntz–Li; Laca–Raeburn's phase transition]: KMS states exist for `β ≥ 1`, are unique for
`1 ≤ β ≤ 2`, and for `β > 2` are indexed by probability measures on the circle, with partition
function `ζ(β − 1)`. In that parametrization the critical strip `0 < Re s < 1` is the uniqueness
interval `1 < β < 2` and the critical line is `β = 3/2` [R, from an unverified recollection of the
parametrization; the point is the shape, a unique state exactly on the strip]. The corpus's two
theorems (the BC successor forcing the exponent `1/2`; the BS relation) are statements about this
one algebra, discovered from two sides.

The proposal: RH as **reflection positivity** of the unique state under the functional-equation
reflection `β ↦ 3 − β`. The corpus's "Frobenius at infinity is conjugation" [L] is the
Osterwalder–Schrader reflection `Θ`; the Rosati pairing `ρ ↔ 1−ρ̄` is `⟨Θf, f⟩`; the collided
pairing `ρ ↔ ρ̄` is `⟨f, f⟩`. In lattice field theory reflection positivity is proved from a
transfer matrix along the time direction, that is from nearest-neighbour structure, that is from
the successor; the Hecke operators are the spatial symmetries, which is why they act as boosts and
never as the proof. The successor would carry the sign (W3 turned into a transfer matrix), and
reconstruction would give the self-adjoint generator (W14 as the Osterwalder–Schrader
reconstruction, a theorem rather than a search for a variety).

**First checkable lemma.** Compute the successor defect of the atomic Weil form,
`W_N(Sx) − W_N(x)`, on the nonnegative cone. The archimedean and pole parts are explicit
(`log(n+1) − log n`). The prime part counts pairs with `(m+1) ∣ (n+1)` against pairs with
`m ∣ n`: a shifted-divisor sum of Titchmarsh type, whose evaluation is Bombieri–Vinogradov
territory [M], the one unconditional tool of GRH strength, and it is the Hardy–Littlewood singular
series over the stabilizers `q ∣ h` the corpus already identified [L]. If the defect has a sign on
a cone, the successor is a monotone direction and the transfer-matrix reading is alive.

**Kill criterion.** If the prime part of the successor defect fluctuates at size `log N` with no
sign on the nonnegative cone, then the connection only labels the Euler point and carries nothing;
W3 stands, and the positive survivor is the exact statement "the successor defect of the Weil
prime form is a shifted-prime correlation", which is a theorem about where the additive
information sits.

### M3. The spacing scale as Montgomery at `α = 1` (pushes the atomic theorem to where the tests see zeros)

**Facts it rests on.** Section 1.5 entirely.

**The mechanism.** Replace the sharp window `0 < γ ≤ T` by a smooth window in the truncation lemma
and supply a zero-density input (Ingham or Carlson type [M]; the corpus has `CarlsonFloor`
material [L]) so that the pair asymptotic extends to `x = T`. Then read the result back through
the explicit formula on atomic tests of width `≍ 1/N`: the unconditional pair asymptotic at
`α = 1` should be equivalent to a defect `o(log N)` in the stability law at the spacing scale
[R: this identification is my reading and is the thing to check first]. This gives a graded ladder
of one finite matrix inequality, the spacing-scale Weil matrix `W_N`:

| defect of `W_N + (rank-one pole counterterm)` at width `≍ δ_N` | equivalent to |
|---|---|
| `O(log N)` | proved for narrow widths [L] |
| `o(log N)` | a zero-density statement (Montgomery at `α = 1`) [R] |
| `O(1)` uniformly in `N` | a uniform cap, hence a zero-free strip [D] |
| `0` | RH |

**Why it matters.** It is the first positivity statement in the corpus's own mechanism (Lévy gain
versus prime counterterm) in the regime where the tests resolve individual zeros, and every rung
below RH is an unconditional theorem nobody has.

**Kill criterion.** If the window weight `w(γ/T)` of the pair form cannot be written as an atomic
test family, the equivalence is heuristic and M3 is a statement about zeros only, still worth
having.

### Which to pursue

M1 first. It is the only one of the three that consumes the gauge charge as a hypothesis, it has a
finite test over `𝔽_q` that decides something before any work over `ℤ`, and it unifies two of the
corpus's own formulations. M3 is the nearest unconditional theorem. M2 is the conceptual frame the
other two should be stated in.

## 3. Question 2: the three open questions

**OQ1. The spacing scale, stated as a finite matrix problem.** For the `N`-atom Weil matrix with
bump width `δ_N/4` (atoms at `log n`, kernel: prime `Λ(n/m)(n/m)^{−1/2}`, archimedean Lévy kernel,
pole `2C² − 2S²`), what is the size of its most negative eigenvalue after the rank-one pole
counterterm, as `N → ∞`? Which vectors are extremal: the oscillating Liouville-type vector, whose
prime form is `−log N` [L] but whose archimedean energy is also of order `log N`, or something
else? The corpus has every ingredient: the prime spectrum fills `[−log N, log N]` with the pole
vector at the top and the Liouville pole vector at the bottom (`atomicWeilForm_spectrum_ends` [L]),
the Hilbert inequality with constant 26 [L], the Lévy gain [L]. The first rung, `o(log N)`, is the
unconditional Montgomery asymptotic at `α = 1`. This is the frontier map's own first question in a
form a computer can attack today.

**OQ2. The positivity locus of the gauge torus.** Prove or refute: a twin `ε` on the torus has a
positive Weil form on degree-zero atomic cycles (for all `N`) only if `ε` is successor-periodic,
that is a Dirichlet character. The direction "periodic ⇒ positive" is GRH and out of reach; the
direction "positive ⇒ periodic" is a statement about *non*-automorphic points and may be
provable: it asks for an explicit negative direction of the Weil form at every non-periodic
point, generalizing the Liouville pole vector [L] to a point with arbitrary holonomy of the
successor connection. A theorem of this shape would be the first unconditional statement that
**locates** the sign of RH on the torus, and it would say in which coordinates the sign must be
read: the holonomy of `succConn`, which the corpus proved reconstructs the prime phases from two
links [L]. Its finite form: for the level-`q` subgroup, the average over `χ mod q` projects the
Weil form onto the sub-progression `n ≡ m mod q` [L]; compute the degree-zero form of that
average and its gauge variation along a holonomy.

**OQ3. The Lorentzian lift of the Frobenius ladder.** Over `𝔽_q`, with the tower kernel
`frobeniusTower` [L] and nef coordinates `Γ_{F^k} + aH + bV`: is the intersection form of a curve
on the span of its Frobenius graphs the Hessian of a Lorentzian polynomial of bounded degree
constructed from the ladder (its lags and the weights `q^{−lag/2}`) with no reference to the
surface `C × C`, and does the construction commute with products over places (disjoint variables)
and with the degree substitution? A yes gives a proof of Weil's theorem for curves of the kind the
corpus could transport, because every input would be a property of a ladder and a positive
kernel; the question over `ℤ` would then be precisely which of the three closure operations
(product, substitution, derivative) fails for transverse ladders, and the corpus's transversality
theorem [L] would be an input rather than an obstruction. A no, with bounded degree impossible,
is the quantitative statement that the base is a weight.

The frontier map's three questions (spacing scale, gauge form margin, interior anti-alignment)
are contained: OQ1 is the first, OQ2 is the second read on the whole torus instead of at one
prime, and interior anti-alignment is the `O(1)` rung of OQ1's ladder.

## 4. Question 3: the field that would supply the tools

Read the walls as questions mathematics has no tools for. W14 asks for a Hodge index without a
variety. W1 asks for a positivity theory whose hypothesis is a sign (a gauge charge), not a
symmetry. W3 asks for a local-to-global principle under which positivity is preserved. There is a
single discipline in which all three are theorems, in a different setting: the theory of
Lorentzian polynomials, real-stable polynomials and combinatorial Hodge theory, where the Hodge
index was proved for matroids with no variety, where nonnegativity of coefficients is the
hypothesis, and where products, nonnegative substitutions and differentiation preserve the
property. It has never been pointed at `ζ`. The field to create is its arithmetic form.

### Name and one-line statement

**Combinatorial Hodge theory of the affine monoid of the integers** (shorter: arithmetic
Lorentzian geometry). Positivity of the Weil form is to be proved as a *closure property* of
elementary positive objects attached to the primes and to the scale, under operations that are
known to preserve Lorentzian signature, with the Euler sign `Λ ≥ 0` as the hypothesis and the
successor as the structure that singles it out.

### The questions it asks

1. Which quadratic forms on the atoms `log n` are Hessians of Lorentzian objects built from local
   factors at the primes and the scale map? (Hodge index without a surface.)
2. What is the positivity locus of the gauge torus, and why is it the successor-periodic locus?
   (The sign as a hypothesis.)
3. Which operations preserve the Lorentzian property on the affine monoid, and is the Euler product
   one of them? (Transfer.)
4. What replaces Frobenius: a symmetry of the Lorentzian structure rather than of the ring `ℤ`?
   (Realization.)
5. What is the arithmetic of the critical regime, the spacing scale `α = 1`, where the atoms
   resolve the zeros? (The regime every present theorem stops in front of.)

### Point of view

Positivity by closure, not by symmetry. The classical proof of RH for curves reads the Hodge index
off a variety; the corpus has shown in forty ways that no variety and no symmetry will be found,
because every symmetry of the form is a boost. The alternative is the one that worked for
matroids: start from objects that are trivially Lorentzian (a single prime's local factor; a
Gaussian), apply only operations proved to preserve the property, and show the Weil form is
reached. In this view the explicit formula is the wrong decomposition (a sum over primes; sums do
not preserve the property) and the Euler product is the right one (a product; products in disjoint
variables do). The archimedean place is not a symmetry and not a kernel but a nonnegative linear
substitution, the scale map, that glues the disjoint prime variables into one line. The pole is
the radial direction of the homogeneity, the one positive eigenvalue every Lorentzian form has.

### Objects

* The affine monoid `ℕ ⋊ ℕ^×` (successor and dilations, the Baumslag–Solitar relations), its
  ladders (one per prime), its cells, and its successor connection on the gauge torus.
* Lorentzian polynomials and forms on the atoms with support in the divisibility poset, in nef
  coordinates: atoms plus the two pole directions `H, V`, with the diagonal chosen in the regulator
  class (the freedom RAPT measured).
* The local germs as the elementary positive objects: the torsion germ with its Ramanujan modes,
  the lattice germ with its constant mode, the Gaussian (theta) at the archimedean place.
* The spacing-scale Weil matrix `W_N` and its graded defect ladder.
* The gauge torus with its finite subgroups (Dirichlet characters) and its successor-periodic locus.
* The scaling surface pairing of ArithmeticCastelnuovoSeveri as the target: its Hodge index is RH.

### Language

Signature and positive index; M-convex support; nef and effective cones; log-concavity, ultra
log-concavity and real-rootedness; hyperbolicity preservers; connection, holonomy and flatness on
the torus; counterterm rank and survival cone; KMS states and reflection positivity for the
dynamical layer; the spacing scale and Montgomery's `α` for the analytic layer.

### Foundational principles

* P1. Positivity is proved by closure under positivity-preserving operations, never read off a
  symmetry of the form.
* P2. The sign is a hypothesis: nonnegative coefficients, which is `Λ ≥ 0`, which is the Euler
  point, which is the flat point of the successor connection. A theory that does not consume this
  hypothesis is torus-invariant and therefore blind (the corpus's forty-four dead mechanisms).
* P3. Local-to-global is multiplicative. The explicit formula's prime sum is a bookkeeping
  identity, not a decomposition under which positivity transfers.
* P4. The archimedean place is a substitution, the scale map, not a kernel to be matched.
* P5. The pole is the hyperbolic plane `⟨H, V⟩`, the single positive direction; the regulator
  freedom of the diagonal is the choice of nef representatives `D + aH + bV`.
* P6. Every statement must be stable under truncation `N → ∞` with widths at the local spacing,
  because that is where the zeros are seen and where every present theorem stops.

### Criteria the field must satisfy

* C1. Reproduce Weil's theorem for curves from the Frobenius ladder with no surface (OQ3).
* C2. Fail visibly at the Liouville point: the hypothesis (nonnegative coefficients) is lost, and
  the pole on the line is the consequence.
* C3. Distinguish Dirichlet characters from non-periodic torus points by the holonomy of the
  successor connection (OQ2).
* C4. Recover every unconditional positivity in the corpus as an "easy closure" statement:
  nonnegative tests, atomic widths `N^{−O(1)}`, Montgomery `α < 1`, eventual hyperbolicity of
  Jensen polynomials, and locate the single missing closure operation at the spacing scale (OQ1).
* C5. No hidden hypotheses: everything stated unconditionally and formalized, in the corpus's
  integrity discipline.
* C6. Produce theorems short of RH on the way: the `o(log N)` and `O(1)` rungs of the defect
  ladder are a zero-density theorem and a zero-free strip.

### Research topics, in order

1. The Lorentzian lift of `frobeniusTower` over `𝔽_q` for small genus: existence, degree, support.
2. Nef coordinates for the atoms over `ℤ`: which diagonals in the regulator class make all
   intersection numbers nonnegative; whether the rank-one pole counterterm `2S²` is the nef shift.
3. Product versus sum: whether the atomic Weil form in nef coordinates is the Hessian of a product
   of local polynomials in disjoint prime variables after the scale substitution.
4. The archimedean factor as a strongly log-concave weight: theta as the Gaussian factor; the
   Lévy gain as its contribution to the signature.
5. The successor as a hyperbolicity preserver on the affine monoid; the successor defect of `W_N`
   as a shifted-prime correlation; its sign on the nonnegative cone (M2's lemma).
6. The positivity locus of the torus: negative directions at every non-periodic point (OQ2).
7. The spacing-scale Weil matrix and Montgomery at `α = 1`: the smooth-window truncation and the
   zero-density input (M3, OQ1).
8. The Jensen/Turán slice statements and the Hodge index as one Lorentzian statement about `ξ`.
9. The Kloosterman bound as the local Lorentzian input at each prime: whether the local factor at
   `p` is Lorentzian *because* of RH over `𝔽_p`, which would make the local-to-global step the
   whole content.
10. The dynamical layer: the KMS states of the affine semigroup algebra on the strip, the
    functional equation as a reflection, and reflection positivity as the statement of RH in that
    algebra; the polarized λ-ring (Witt Frobenii plus a compatible positive form) as the object
    "Frobenius over `ℤ`" would have to be.

### How this field relates to the corpus

It changes no theorem and it keeps every ledger. The corpus's unconditional results are its base
cases; its killed mechanisms are its theorem that symmetry cannot work; its renormalization
bookkeeping is its coordinate system (the regulator class is the nef freedom); its gauge torus with
the successor connection is where the hypothesis lives; its transversality theorem is the reason
the local factors are in disjoint variables; its Hodge-index theorem is the target. What the field
adds is a change of direction: positivity flows from elementary objects to the Weil form through
closure, instead of being sought as an invariant of the Weil form under a group it has none of.

## 5. Appendix: corpus declarations cited

| declaration | module |
|---|---|
| `gaugeMargin_window`, `gaugeMargin_atomicWeilForm` | ArithmeticElectrostatics/TheGaugeMarginOfTheRenormalizedSource, TheGaugeIsInvisibleAtAtomicResolution |
| `markovEnergy_atomicTest_nonneg`, `levyEnergy_atomicTest_ge`, `atomSpacing` | ArithmeticElectrostatics/TheStabilityLawAtAtomicResolution |
| `re_W_atomicTest_eq`, `re_W_add_sinh_sq_nonneg`, `re_W_atomicTest_nonneg_of_nonneg` | ArithmeticElectrostatics/TheWeilFormAtAtomicResolution |
| `finrank_primeSurvival_le_rank`, `primeSurvival_rankOne`, `coupled_torsion_survival` | RenormalizedArithmeticPotentialTheory/TheCoupledSurvivalLaw |
| `primeSurvival_jointGram`, `ramanujanMode_one` | RenormalizedArithmeticPotentialTheory/TheArchimedeanPlacePaysTheArithmeticPoint |
| `horizonCounterterm_rank_unbounded`, `atomicWeilForm_classCombination_ge` | RenormalizedArithmeticPotentialTheory/TheHorizonDivergenceLivesOnTheTorsionOrbits |
| `atomicWeilForm_liouvillePole_le`, `atomicWeilForm_spectrum_ends`, `abs_liouvilleForm_stepProfile_add_le` | RenormalizedArithmeticPotentialTheory/TheLiouvilleGaugeFlipsThePolarDivergence |
| `heckeCocycle_eq`, `not_exists_bounded_potential`, `weilPrimeKernel_mul_left` | ArithmeticIntersectionTheory/TheHeckeCocycleOfRenormalization |
| `ladderKernel_mul_ladderKernel_eq_zero`, `frobeniusTower_lcm_ne_zero`, `sameLadder_succ_iff` | ArithmeticIntersectionTheory/TheBaseAndTheSuccessor |
| `posIndex_intersectionGram_le`, `pair_heckeCorrespondence`, `scalingSurface_self_pair_unbounded_below_on_finite_reading_fibre` | ArithmeticCastelnuovoSeveri |
| `arithH0_riemannRoch`, `poleH0_riemannRoch` | ArithmeticOrientationGeometry/TheThetaH0OfSpecZ |
| `cellDilate_succShift` | RenormalizedBiarithmeticGeometry/LogCellsFixTheGauge |
| `bc_successor_hecke_exponent` | ArithmeticPositiveDuality |
| `succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two/three`, `realSign_latticeForm_eq` | BiarithmeticGaugeGeometry/PrimeGaugeTorusAndVacuumIntertwiners |
| `twist_dirichletGauge`, `sum_twist_dirichletGauge_succ`, `norm_archPair_sub_one_le` | ArithmeticCorrelationGeometry/FiniteGaugeSubgroupsResolveWhatTheArchimedeanLineCannot |
| `tendsto_montgomeryForm_div_leadingOrder`, `eventually_montgomeryForm_div_leadingOrder_uniform`, `montgomeryForm_eq_integral_height` | RHTower/MontgomeryPairCorrelation*, MontgomeryFormHeightMeanSquare |
| `mvHilbert_twentySix`, `exists_zeroSum_dirichletPolynomial_le` | HTGeometry/RiemannGaussian/MontgomeryVaughan/Final, RHTower/ZetaZeroDirichletPolynomialMoment |
| `kloosterman_weil_bound` | RHTower/WeilKloostermanBound |
| `deningerBigWittCrossPairFrobeniusFiberCoefficient_zero`, `xiZeroCopyConjEquiv` | RHTower/Deninger |
| `false_of_mem_of_primeLengthTraces` | RHTower/HyperbolicPrimeLengthSpectrumObstruction |
| `eventually_volume_sliceCoeff_turanSeq_ge_ninth` | RHTower/XiHorizontalSliceLogConcaveDensity |
| `re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq` | RHTower (cited from TheWeilFormAtAtomicResolution) |

Not found in the corpus (open ground for the field): Lorentzian polynomials, M-convexity,
combinatorial Hodge theory of matroids; Alexandrov–Fenchel or Brunn–Minkowski for the Weil form;
reflection positivity or Osterwalder–Schrader; the wreath/affine group representation theory; the
overlap regime `w ≳ δ_N`; Montgomery at `α = 1`.
