# The forward monodromy determines the reflection and the conjugation

- **ID:** gtz-centralizer-and-mirror
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** programme card `gtz-galois-theory-of-zeros-programme.md`, question 6 and the open
  topic "whether conjugation is determined inside `G₊` by its commutation relations".
- **Statement:** `b` a forward time off the branch times, `t > 0` a real one.
  (A) a map of the zeros of `H_b` to themselves that commutes with every element of `G₊(b)` is
  the identity or the reflection `r : z ↦ −z`; the centre of `G₊(b)` is trivial;
  (B) a permutation `σ` of the zeros of `H_t` with `T_γ̄ = σ T_γ σ⁻¹` for every forward loop `γ`
  at `t` (`γ̄` the mirror loop) is `c : z ↦ z̄` or `cr`;
  (C) all zeros of `H_t` are real iff `T_γ̄ = T_γ` for every forward loop at `t`; RH iff this
  holds over every real `t > 0` off the branch times;
  (D) a continuous map of the forward cover `{(τ, z) : H_τ(z) = 0}` to `ℂ` that carries zeros of
  `H_τ` to zeros of `H_τ` is `z` everywhere or `−z` everywhere; one that carries them to zeros
  of `H_τ̄` is `z̄` everywhere or `−z̄` everywhere;
  (E) no zero is a continuous function of the forward time off the branch times;
  (F) the forward cover is connected;
  (G) a monic polynomial `P_τ` of fixed degree `n ≥ 1` with coefficients continuous in the
  forward time off the branch times has, at some time, a root that is not a zero of `H_τ`;
  (H) a continuous function `F(τ, z₁, …, zₙ)` on the configurations of `n` zeros whose value
  is a zero of `H_τ` equals `±zᵢ` for some `i` at every configuration; if the value is a zero
  of `H_τ̄` it equals `±z̄ᵢ`;
  (I) the configurations `(τ, z₁, …, zₙ)` of zeros, no two equal or opposite, form a path
  connected set; a polynomial relation `P_τ(z₁, …, zₙ) = 0` that holds on an open and closed
  nonempty subset of them has `P_τ = 0` at every forward time off the branch times;
  (J) an equivalence relation on the zeros of `H_b` preserved by `G₊(b)` is equality, the
  relation `z' = ±z`, or the relation that identifies all zeros;
  (K) near a configuration the configurations are `(τ, r₁(τ), …, rₙ(τ))` with `rᵢ` analytic; a
  function `F(τ, z₁, …, zₙ)` analytic at every configuration vanishes on every configuration, or
  each configuration has a neighbourhood with no other configuration at which `F` vanishes; a
  polynomial `P_τ` of bounded support with coefficients analytic in the forward time, with
  `P_τ(z₁, …, zₙ) = 0` on configurations accumulating at a configuration, is `0` at every
  forward time off the branch times.

## Goal

The two involutions of the programme are intrinsic to the cover: `r` generates the centralizer
of the monodromy (the deck group), `c` is the mirror intertwiner, unique up to `r`. RH is the
statement that the identity is a mirror intertwiner. No sign and no positivity enters.

## Gates
- [x] 0 → 1
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean (axioms `propext, Classical.choice, Quot.sound`)

## Proof

(A) `G = G₊(b)` contains every signed 3-cycle and is transitive. Let `σ` commute with `G`.
If `σx` is not in the pair of `x`, take two further pairs `s, u`; the signed 3-cycle
`σx → s → u` fixes `x`, so `σx = σ(Tx) = T(σx) = s`, a contradiction. So `σx ∈ {x, −x}` for
every `x`. If `gx₀ = y` then `σy = g(σx₀)`, which is `y` when `σx₀ = x₀` and `−y` when
`σx₀ = −x₀`: the sign is the same at every point. `r ∉ G₊(b)` (it moves infinitely many
zeros), so a central element is `1`.

(B) Conjugation carries a lift of `γ` to a lift of `γ̄`, so `c` is an intertwiner. If `σ` is
one, then for `g = T_γ`: `T_γ̄(σp) = σ(gp)`; conjugating, `T_γ(cσp) = cσ(gp)`, i.e. `cσ`
commutes with `g`. By (A) `cσ ∈ {1, r}`.

(C) If `c = 1` the zeros are real and `T_γ̄ = cT_γc = T_γ`. Conversely the identity is an
intertwiner, so `1 ∈ {c, cr}`; `c = r` is excluded because `c ∈ G₊(t)` and `r ∉ G₊(t)`.

(D) A continuous map `f` of the cover over its base carries a lift `(γ(s), z(s))` to the lift
`f(γ(s), z(s))`. On the fibre over `b` it commutes with `G₊(b)`, so by (A) (for maps) it is
the identity or `r` there. Transport along a path from the time `1/8` carries the case of
that fibre to every fibre. For a mirror map apply this to `z ↦ \overline{f}`.

(E) A section `Z` gives the deck map `(τ, z) ↦ Z(τ)`; by (D) every zero of `H_{1/8}` is
`±Z(1/8)`, but the fibre is infinite. ∎

(F) Let `S` be open and closed in the cover. The map `z` on `S`, `−z` off `S` is continuous
and carries zeros to zeros, so by (D) it is `z` everywhere or `−z` everywhere; no zero over
these times is `0`, so `S` is everything or nothing.

(G) Suppose every root of every `P_τ` is a zero of `H_τ`. The set `S` of the points of the
cover that are roots is closed in the cover (the value `P_τ(z)` is continuous). It is open:
`H_τ₀` has a simple zero at `z₀`, so in a neighbourhood of `(τ₀, z₀)` the zero through it is the
only zero of `H_τ` in a disc of radius `ρ`; a monic polynomial of degree `n` has a root within
`|P(z₀)|^{1/n}` of `z₀` (its value is the product of the distances to the roots), so for `τ`
near `τ₀` the polynomial `P_τ` has a root within `ρ/2` of `z₀`, that root is a zero of `H_τ`,
hence the zero of the chart. By (F) `S` is everything (a fibre is infinite, a polynomial has
`n` roots) or nothing (`P_{1/8}` has a root, which is a zero).

(H) Let `w = F(τ, z)` lie in none of the pairs of the `zᵢ`; take `y` in a further pair. By
the multiple transitivity of `G₊(τ)` some loop `γ` carries `w` to `y` and returns every `zᵢ` to
itself. `F(γ(s), z(s))` is then a lift from `w` to `w`, against uniqueness of lifts.

(I) Two lifts of a forward path that agree at one parameter agree at the start, so lifts that
start in distinct pairs stay in distinct pairs and give a path of configurations. A forward
path between the two times carries the first configuration to one over the second time, and
by multiple transitivity one loop carries that to the second configuration. A relation that
holds on an open and closed nonempty set holds on all configurations; over one time the zeros
with pair number `i` modulo `n` form an infinite set `Sᵢ`, `S₁ × ⋯ × Sₙ` consists of
configurations, and a polynomial that vanishes on a product of infinite sets is zero.

(J) Let the relation hold for `x` and a point `y` of another pair. A signed 3-cycle
`y → u → s` through a fresh pair, or the double flip of the pair of `y` with a fresh pair,
lies in `G₊`, fixes `x` and carries `y` to any `u` off the pair of `x`; applied from `y` it
reaches the pair of `x`, so all zeros are related. If the relation holds only inside pairs and
for one pair, transitivity gives it for every pair.

(K) The implicit function theorem at a simple zero gives an analytic `r` with `H_τ(r(τ)) = 0`,
and the chart of the simple zero says that `r(τ)` is the only zero in a disc. Along the chart
`g(τ) = F(τ, r(τ))` is analytic, so `g = 0` near the time of the configuration or `g ≠ 0` at
the other nearby times; a configuration of the chart over the same time is the configuration
itself. The configurations near which `F` vanishes are therefore open and closed in the
configurations, which are connected (I). For the polynomial, `F(τ, z) = P_τ(z)` is a finite sum
of analytic coefficients times monomials; it vanishes on all configurations, and (I) over one
time gives `P_τ = 0`. ∎

## Lean

| Step | Module | Declaration |
|---|---|---|
| A | `TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros` | `IsWindowedSignedGroup.eq_self_or_eq_flip_of_commute`, `eq_one_or_eq_fibreNeg_of_forall_commute`, `eq_one_of_mem_forwardMonodromy_of_forall_commute` |
| B | same | `transports_pathConj_fibreConj`, `eq_fibreConj_or_eq_fibreConj_mul_fibreNeg` |
| C | same | `fibreConj_eq_one_iff_forall_transports_pathConj`, `riemannHypothesis_iff_forall_transports_pathConj` |
| D | `TheReflectionIsTheOnlySymmetryOfTheHeatCoverOverTheForwardTimes` | `forwardCover`, `Transports.map_forwardCover`, `eq_snd_or_eq_neg_snd_of_continuousOn_forwardCover`, `eq_conj_or_eq_neg_conj_of_continuousOn_forwardCover` |
| E | same | `exists_complexHeat_ne_zero_of_continuousOn` |
| F | `TheHeatCoverOverTheForwardTimesIsConnectedAndHasNoPolynomialFactor` | `forall_mem_or_forall_notMem_forwardCover`, `isConnected_forwardCover` |
| G | same | `exists_isRoot_norm_sub_lt`, `exists_isRoot_complexHeat_ne_zero` |
| H | `AZeroThatIsAContinuousFunctionOfFinitelyManyZerosIsOneOfThemUpToTheSign` | `forwardConfigurations`, `exists_eq_or_eq_neg_of_continuousOn_forwardConfigurations`, `exists_eq_conj_or_eq_neg_conj_of_continuousOn_forwardConfigurations` |
| I | `TheConfigurationsOfZerosInDistinctPairsOverTheForwardTimesAreConnected` | `forwardPairConfigurations`, `IsForwardPath.mem_forwardPairConfigurations`, `joinedIn_forwardPairConfigurations`, `isPathConnected_forwardPairConfigurations`, `eq_zero_of_forall_eval_eq_zero`, `eq_zero_of_eval_eq_zero_on_forwardPairConfigurations` |
| J | `TheOnlyIntermediateCoverOfTheZerosIsTheCoverOfTheSquaredZeros` | `IsWindowedSignedGroup.rel_of_rel_of_pair_ne`, `IsWindowedSignedGroup.invariant_equivalence`, `forwardMonodromy_invariant_equivalence` |
| K | `AnAnalyticRelationAmongZerosInDistinctPairsHoldsOnEveryConfigurationOrOnADiscreteSet` | `exists_analyticAt_zero_chart`, `exists_analyticAt_configuration_chart`, `eventually_eq_zero_or_eventually_ne_zero_of_analyticAt`, `forall_eq_zero_of_frequently_eq_zero`, `forall_eq_zero_or_forall_eventually_ne_zero`, `eq_zero_of_frequently_eval_eq_zero` |

## Open

Analytic relations among several zeros (a holomorphic `Φ(τ, z₁, …, zₙ)` vanishing on a
component of the configurations): needs analytic charts; the charts of the corpus are
continuous. A polynomial factor whose coefficients depend on finitely many zeros. Whether the
analytic relations among `n` zeros are generated by `H_τ(zᵢ)`.
