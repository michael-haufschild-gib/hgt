# Galois theory of the zeros

## Why

The zeros of the zeta function of a curve of genus `g` over `𝔽_q` are the roots of one
polynomial with integer coefficients. The functional equation pairs the roots, so the Galois
group lies in the group of signed permutations `(ℤ/2)^g ⋊ S_g`, and for most curves it is the
whole group. The Riemann hypothesis there says nothing about the size of this group. It says
that two involutions of the roots agree: complex conjugation `c` and the reflection
`r : α ↦ q/α`.

The same two involutions act on the zeros of ζ: `c : ρ ↦ ρ̄` and `r : ρ ↦ 1 − ρ`. RH says
`c = r` on the zeros; equivalently `cr : ρ ↦ 1 − ρ̄`, which keeps the ordinate and reflects
the width, is the identity.

An infinite set of zeros is not the root set of one polynomial, and the zeros are not known to
be algebraic over `ℚ`. The programme therefore works with a compatible system of finite-fibre
equations and the infinite algebraic extension they generate over a named source field, and
with the cover of the zeros of the heat family over the complex times. There are two source
fields, and they are different objects. Over the field `K` of complete-fibre traces the zero
field is `K` itself exactly when RH holds. The prime-trace field `B` of mixed prime traces
contains transcendental numbers; its group acts faithfully on the zeros and keeps the absolute
ordinate. No statement passes between `K`, `B` and the cover without a theorem that carries it.

The programme determines the groups over these bases and classifies the permutations of the
zeros they allow. It has four problems:

1. a presentation of `B` by arithmetic source germs and explicit relations, with controlled
   finite subfields and composita;
2. the finite orbits and stabilizers of the zeros over `B`, read off from the memberships of
   prime values in `B`;
3. the reflection lift: when `r` extends to an automorphism over `B`, decided by the parity of
   the finite square relations among the reflection radicands, and whether a lift is
   conjugation;
4. a comparison between the arithmetic groups and the monodromy of the heat cover, with an
   exact account of what it preserves.

**Limit.** Over `K` the group is trivial exactly when RH holds, over `B` the reflection field
is `B` exactly when RH holds, and on the cover conjugation is the trivial element exactly when
RH holds. The theory supplies a language, criteria and exact forms of RH that use no sign. It
supplies a route only through a restriction that the primes or the branch divisor impose on
the position of `c`, and none is known. Coefficients defined from the zeros one wants, with the
observation that these zeros satisfy the resulting equations, are not such a restriction.

The size of the group carries no restriction. On the cover the group has index at most two in
the group of all signed permutations of finite support, so every signed permutation of a finite
set of pairs occurs, and the reflection and the conjugation are determined by the group: `r`
is its centralizer and the conjugation is its mirror intertwiner. What is left of RH on the
cover is the position of the real axis among the branch times: a forward loop at a real time
and its mirror loop must transport the zeros alike.

## A theory of signed permutations with two marked involutions

Every group of the programme acts on the zeros by signed permutations of pairs, and carries the
two involutions `c` and `r`. There are three tiers.

1. **Finite equations.** The centred Jensen polynomials `P_d` of `Ξ`. Negation symmetry folds
   them, `P₂ₙ = Eₙ(X²)`, so their groups lie in the signed permutations of `n` pairs. The
   group is the whole group `C₂ ≀ S_n` unless the moments of `Φ` are dependent. The
   information is the cycle type of conjugation: `N_d/2` transpositions, where `N_d` is the
   number of nonreal roots.
2. **Fields.** All zeros at once, over a source field. Over the field `K` of complete-fibre
   traces the group is a group of width reflections, trivial iff RH. Over the prime-trace field
   `B` the group acts faithfully, keeps the absolute ordinate and commutes with `r`; the orbit
   of a zero is read off from the prime values of the zero that lie in `B`.
3. **The cover.** The zeros as functions of the complex heat time `τ` of the de Bruijn–Newman
   family `H_τ`. The zeros form a cover of the time plane; its branch points are the
   collisions. `r` is the deck map `z ↦ −z`, and `cr` is the antiholomorphic map
   `(τ, z) ↦ (τ̄, z̄)`. Over the forward half-plane `Re τ > 0` the cover has a monodromy group
   `G₊`, a group of restricted signed permutations of the pairs `{z, −z}`:
   - the *sign part* comes from the collisions at the centre `z = 0`, where the functional
     equation is the local monodromy: a turn around a centre time carries a zero to its
     negative (a *sign flip*);
   - the *permutation part* comes from the collisions away from the centre: a turn around one
     carries a zero out of its pair (an *exchange*);
   - conjugation is the *word* of the turns around the real branch times.

   The turns generate `G₊`, so the first two items describe the whole group. Both parts are
   present: centre times give sign flips, and collisions away from the centre exist at forward
   times of arbitrarily large real part, so `G₊` contains exchanges and is not a group of sign
   flips. These collisions are at nonreal times; RH concerns the positive real axis. `G₊` is
   transitive on the zeros: over the forward half-plane the cover is irreducible.

   The group is known up to one sign. Let `W` be the group of the signed permutations of finite
   support of the pairs. `G₊` contains every signed 3-cycle and every double flip, so it induces
   every signed permutation on every finite set of pairs; it contains an odd permutation of the
   zeros; it is normal of index at most two in `W`; and it is all of `W` as soon as it contains
   the exchange of two pairs. Every turn is an involution: `k` sign flips, `k` the order of
   vanishing of the centre value at its time, and `c` exchanges. `G₊ ≠ W` exactly when one
   parity law holds at all forward times: `c + εk` is even, with one `ε ∈ {0, 1}`; then `G₊` is
   the kernel of one sign character. The cover is rigid: it is connected, its only deck map is
   `r`, its only mirror maps are `cr` and `c`, no zero is a continuous function of the time or
   of finitely many other zeros, no finite set of zeros is the root set of a polynomial with
   coefficients continuous in the time, the configurations of `n` zeros in distinct pairs are
   connected for every `n`, and the squared zeros are the only intermediate cover.

## Objects

Coordinates: `ρ` is a zero of ξ, `w = (ρ − ½)/i = t + iδ` its centred coordinate, `t` the
ordinate, `δ = ½ − Re ρ` the width. Conjugation of `w` is `cr`; negation of `w` is `r`.

| Object | Definition |
|---|---|
| fibre | all zeros with one ordinate `t`, with analytic multiplicity; `P_t` is its monic polynomial |
| fibre source field `K` | generated by the coefficients of all `P_t`; equal to the field of stable prime–archimedean contour moments of complete fibres; `K ⊆ ℝ`, and `t ∈ K` for every occupied ordinate |
| zero field `L` | `ℚ(all w)`; the compositum of the splitting fields of the `P_t` over `K` |
| real fields | `L⁺ = L ∩ ℝ = K(δ_qδ_r)`, the width field `F = K(δ_q)`, the squared-width field `D = K(δ_q²)`, the Gaussian extension `M = L(i)` |
| radicands | `a_q = −δ_q² ∈ D`, with `L = D(√a_q : q)` |
| sign family | a choice `ε_q = ±1` for the nonzero widths; it is admissible if it annihilates every finite square relation `∏_{q∈S} a_q ∈ D^{×2}` |
| ordering | a subsemiring `Q` of a field that contains the squares, not `−1`, and `x` or `−x` for every `x`; `σ_Q ∈ Gal(L/D)` is its conjugation, with signs `sgn_Q(a_q)` |
| prime spectral field `E` | `ℚ(p^ρ : p prime, ρ a zero)` |
| prime trace field `B` | generated by the traces `Σ_{Im ρ = ±t} exp(ρ Σ_p m_p log p)` over all heights and all integer prime vectors `m`; equal to the field of the paired prime source germs of complete fibres; `B ⊆ ℝ` |
| prime values of a zero | for `ρ = β + iγ` and a prime `p`: the weight value `p^{ρ+ρ̄} = p^{2β}`, the width value `p^{2β−1} + p^{1−2β}` and the ordinate value `p^{ρ−ρ̄} + p^{ρ̄−ρ} = 2cos(2γ log p)`, elements of `E ∩ ℝ` |
| residue fields | `F_ρ = B(p^ρ : p)`, `H_ρ = B(p^ρ + p^{1−ρ} : p)`; the reflection field `H` is the compositum of all `H_ρ` |
| even-product field | `K_even = ℚ((ρ−½)(τ−½))` over all pairs of zeros |
| zero motive | `Δ`, the integer span of the zeros; its group algebra `ℂ[Δ]` with the prime translations `T_p[z] = p^z[z]` |
| Jensen equations | the centred reversed sections `P_d` of `Ξ`, their quotients `Eₙ`, `Oₙ`, and the coefficient field `K_J = ℚ(μ₂ₙ/μ₀)` |
| heat cover | the zero set of `(τ,z) ↦ H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` in `ℂ²`, over the plane of complex times `τ` |
| collision | a point `(τ₀, z₀)` of the cover; its order `m` is the order of `z₀` as a zero of `H_τ₀`, and `a = H_τ₀^{(m)}(z₀)`. Every point of the cover is a collision of some order `m ≥ 1`; it is a branch point when `m ≥ 2` |
| blow-up `G` | the analytic function on `ℂ²` with `H_{τ₀+s²}(z₀ + s y) = s^m G(s, y)`; `G(0, y) = (a/m!) Q_m(y)`, `Q_m = e^{−D²}y^m` the Hermite profile |
| sheets | `Z_ρ(s) = z₀ + s y_ρ(s)`, one for each of the `m` simple real roots `ρ` of `Q_m`; `y_ρ` is the analytic branch of `G = 0` through `(0, ρ)` |
| branch times | the complex times at which the family has a multiple zero |
| centre value | `c(τ) = H_τ(0) = ∫ Φ(x) e^{τx²} dx = Σ μ₂ₙ τⁿ/n!`, an entire function; its zeros are the centre times |
| fibre trace | `Σ 1/z²` over the zeros of `H_τ` with multiplicity; a symmetric function of the fibre, hence a single-valued function of the time |
| ramification of a time | the number `M = 2k + 4c` of zeros moved by a small turn around it: `k` flipped pairs, `k` the order of the centre value there, and `c` exchanges of two pairs |
| sign characters | on the signed permutations `W` of finite support: the sign on the pairs, and its product with the sign on the zeros; their kernels are the subgroups of index two of `W` that contain `W⁰` and an odd permutation of the zeros |

Language: *orbit* (of a zero under a group), *width class* (the square class of a radicand),
*reflection kernel* (the group over the field that forgets the orientation of reflection
pairs), *lift* (of `r` or `cr` to a field automorphism), *branch* and *local monodromy* (of
the heat cover at a collision), *turn* (the transport along a small circle around a branch
time), *sign flip* (`z ↦ −z` on one pair), *exchange* (an element that carries a pair to a
different pair), *word* (a product of turns), *restricted* signed permutation (one that moves
finitely many zeros).

## Mechanisms

- **Complete fibres fix the ordinate.** The first trace of a fibre is its mass times its
  ordinate. Every automorphism over `K` therefore preserves each fibre, commutes with
  conjugation and fixes every critical zero.
- **Kummer theory of widths.** `L/D` is generated by square roots. Its group is the group of
  admissible sign families, and conjugation is the constant family `−1`. Relations between
  width classes are the only obstruction to independent reflections.
- **Orderings give automorphisms.** The sign of an ordering is multiplicative and trivial on
  squares, so the signs of the radicands in an ordering of `D` form an admissible family. Its
  automorphism is the conjugation of that ordering. Every element outside a preordering is
  negative in an ordering above it, so a statement for all orderings is a statement on sums of
  squares.
- **Descent of a square class.** All nonzero `δ_q²` lie in one class `ω` of `L⁺`. The group
  over `K` splits off conjugation exactly when `ω` descends to `K`, and exactly then a
  continuous quadratic character detects conjugation.
- **Dedekind independence of prime characters.** Zeros give distinct characters of the free
  group on the primes. Equality of all mixed traces therefore transports a whole prime
  pattern to one zero: an embedding over `B` permutes zeros and keeps the absolute ordinate.
- **Rational weights are fixed.** The unit weight `ρ + (1−ρ)` is fixed, hence every rational
  point of `Δ`. A zero with rational real part has a fixed weight `2 Re ρ`, and its orbit
  cannot leave `{ρ, ρ̄}`.
- **Transcendence of prime powers.** Six exponentials bound the algebraic prime values at a
  zero: three for any zero, two when the real part is irrational.
- **Two primes separate exponents.** `(2^z, 3^z)` determines `z`. Maps commuting with two
  prime translations are diagonal, and conjugation is the only pointed real symmetry.
- **Folding.** `disc Q(X²) = 4ⁿ(−1)ⁿQ(0)·disc(Q)²`: the discriminant of a folded equation
  keeps the branch points and loses the sign of the quotient discriminant.
- **Specialization.** An automorphism over the coefficients of `∏(X² − x_i²)` sends each `x_i`
  to a root `±x_j`; the `2n` signed roots are distinct, so it is a signed permutation. Hence
  the field of the coefficients is the fixed field of the signed permutations. The coefficients
  are algebraically independent, so every folded equation with algebraically independent
  coefficients is a copy of the generic one over an isomorphic base field, with the same
  splitting field and the same group.
- **Parabolic blow-up.** At a collision of order `m` put `τ = τ₀ + s²` and `z = z₀ + s y`. The
  kernel expansion removes the moments of order `< m` and leaves `H = s^m G(s, y)` with `G`
  analytic and `G(0, ·)` the Hermite profile. Its roots are simple, so each continues to an
  analytic sheet: on the double cover in `s` the cover of zeros is unramified.
- **Symmetries of the blow-up.** `G(−s, −y) = (−1)^m G(s, y)` is the deck map of
  `τ = τ₀ + s²`; conjugation carries the blow-up at `(τ₀, z₀)` to the blow-up at `(τ̄₀, z̄₀)`,
  and `y ↦ −y` carries it to the blow-up at `(τ₀, −z₀)`. Uniqueness of the continuous branch
  through a simple root turns each symmetry into a law for the sheets.
- **Counting on a circle.** The number of zeros in a small disc around `z₀` is `m` for all
  nearby times. The `m` sheets are distinct zeros in that disc, so they are all of them, and
  each is simple.
- **Growth in the time.** The centre value has order at most `3/2` and grows faster than every
  exponential along the positive real axis, because the weight has mass arbitrarily far out.
  An entire function of order below two with finitely many zeros is a polynomial times an
  exponential of a linear function, so the centre value has infinitely many zeros.
- **The heat equation in complex time.** `∂_τ H = −∂_z² H`. The time derivatives at a point
  are its even place derivatives, so a collision of order `2k` is a zero of order `k` in the
  time, and the Taylor coefficients of `H_τ` at the centre are the time derivatives of `c`.
- **Charts and continuation.** Near a simple zero the cover is the graph of a function of the
  time, and that zero is the only one in a fixed disc. A continuous family of zeros that enters
  the disc stays on the graph. So lifts of a path of times are unique, a lift extends beyond
  every parameter it reaches, and a lift that stays bounded along a sequence of parameters
  converges to a zero and continues through it. Only escape to infinity ends a lift.
- **Two saddles at forward times.** For `Re τ > 0` the family is a complex Gaussian average of
  ξ over a horizontal line, the sum of two half transforms. Each half transform is ξ at a
  saddle point far to the right, where `ξ'/ξ` is the slope `½ log(s/2π)` up to a small error,
  so near a far place it is one exponential in the place and the time, and the family is a sum
  of two exponentials with frequencies `a` and `−b`. Its far zeros lie in a horizontal strip,
  are spaced by `2π/(a + b)`, and move with the time at the bounded velocity `i(a − b)`. The
  phase between the two exponentials is locked near `2πiℤ` at the zeros, which traps a
  continuous family of zeros in a disc while the time moves a fixed small distance.
- **The census of nonreal zeros across the time `0`.** At a negative real time there are
  infinitely many nonreal zeros, at a positive real time finitely many. Along real times
  conjugation maps lifts to lifts, and a lift that becomes real meets its conjugate, so without
  a collision a nonreal zero stays nonreal. Transport is injective, so between a negative and a
  positive time all but finitely many nonreal zeros collide or escape.
- **Decreasing weights.** In the variable `u = x²` the centre value is the Laplace transform of
  `Φ(√u)/√u`, positive and decreasing because the Riemann kernel decreases on `[0, ∞)`. The
  sine transform of a decreasing function is positive, so at a time with `Re τ ≤ 0` the
  imaginary part of `c(τ)` has the sign of `Im τ`.
- **Far zeros return.** Along a path of times in a box, the trap applies step by step: a zero
  that starts far enough out stays far out, where every zero is simple. So a far zero has a
  lift through simple zeros along every loop of the straight contraction of a loop, also where
  the contraction crosses branch times, and homotopy invariance returns it to itself.
- **Three regions of a turn.** For a small circle around a time `τ₀` the fibre splits into the
  far zeros, the zeros near a simple zero of `H_τ₀`, and the sheets of the collisions at `τ₀`.
  The first two are values of continuous families of simple zeros over a disc of times and
  return; the sheets are reflected. Finiteness of the zeros of `H_τ₀` in a disc makes one
  radius serve the whole fibre.
- **Gluing without homotopy.** Transport is multiplicative for the concatenation of paths, so
  a loop inside the union of two open regions is a product of loops inside the regions and of
  changes of the return path over the intersection. A convex region with one branch time is
  the union of three half-plane parts without branch times; the only junction that is not
  trivial is the turn. A convex region with more branch times is cut by a strip between two
  parallel lines. So a subgroup that contains the small turns, conjugated to the base time,
  contains every loop.
- **A subgroup detects a collision.** The permutations that carry every zero `z` to `±z` form
  a subgroup, and a turn around a time whose collisions are all central lies in it. A loop in
  a convex region whose transport is outside this subgroup therefore encloses a collision
  away from the centre.
- **Two terms at a saddle time.** For `τ = πe^{2a}/a` with `Re a` large and `Im a` just below
  `π/4`, the integral of `H_τ` is moved to the corner path through `0` and through the saddle
  `a` of `τx² − πe^{2x}`. The segment through `0` gives a constant `B₀` (the Gaussian at the
  centre value of `Φ`), the line through `a` gives `S₀e^{iza}` (the Gaussian at the saddle),
  and `H_τ(ζ/a) = B₀ + 2S₀ cos ζ` up to a relative error that is a power of `1/‖τ‖`. The zeros
  near the centre are those of a cosine plus a constant; they collide where `2S₀ = ±B₀`.
- **A loop of saddles.** `(2S₀/B₀)²` is an explicit function `Q(a)` without square roots.
  A loop `a(s)` on which `Q(a(s)) cos² ξ₀(s) ≈ 1`, `ξ₀(s) = e^{iπs}/4`, keeps a zero of `H`
  near `θ + ξ₀(s)` in the variable `ζ = az`, `θ ∈ {π, 2π}`, and returns it near `θ − ξ₀(0)`:
  the zero is carried out of its pair, and the subgroup detector gives the collision. The
  sign of `2S₀ cos ξ₀/B₀` is constant on the loop because a continuous square root of a
  function near `1` cannot change sign.
- **Symmetric functions of a fibre.** Each `H_τ` has order one with logarithmic type, hence a
  genus-one product over its zeros. Dividing the partial fraction of `H_τ'/H_τ` by `z` and
  letting `z → 0` gives the sum of the inverse squares of the zeros as `−H_τ''(0)/H_τ(0)`,
  which the heat equation turns into `c'(τ)/c(τ)`.
- **Conjugate paths.** The lower half circle around a real time is the conjugate of the upper
  one, so conjugation of the fibre before a real branch time is conjugation after it times
  the turn. Passing the real branch times one by one writes conjugation as a word of turns.
- **Window reflections.** Number the zeros of `H_{1/8}` in the order of the real line. The
  loop of saddles of one sign moves the zeros with odd number of a window down by one, the
  other the zeros with even number; several zeros followed through simple zeros along one
  path are transported by one forward path. On the pairs of the window the two elements are
  the reflections `m ↦ −m − 1` and `m ↦ −m`.
- **From window reflections to 3-cycles.** Products of window reflections are translations on
  windows. The commutator of an element with a translate whose support meets its support in
  one point is a 3-cycle; two 3-cycles with a common point give a third by conjugation, which
  is the Euclidean algorithm on the two gaps of a triple; finite support forces the common
  divisor of the gaps to be one. On the zeros, the fourth power of a lift of a 3-cycle of
  pairs is a signed 3-cycle, and conjugating by a flip gives the double flips.
- **A zero of the centre value by the open mapping theorem.** On a disc of saddles
  `c/B₀` is within `1/1024` of `1 − e^{v/2}`, which has a simple zero at `v = 0`; the open
  mapping theorem gives a zero of `c` and the Cauchy estimate makes it simple.
- **Removing exchanges.** Two exchanges of pairs are a product of two signed 3-cycles. An
  involution of the group that flips exactly one pair therefore reduces to the flip alone or
  to the flip times one exchange. In the same way signed 3-cycles and double flips clear the
  moved zeros of any signed permutation off three reference pairs and then on them: modulo
  the group every signed permutation of finite support is `1`, a flip, an exchange, or both.
- **Peeling an involution.** A signed involution of finite support splits along the orbit
  `{z, σz, −z, −σz}` of a moved zero into a flip or an exchange and an involution with fewer
  moved zeros. In a group of index two without exchanges each exchange changes the class, and
  each flip changes it or not, the same for all flips because the group is transitive. So the
  class of an involution is the parity of `c + εk`.
- **Centralizer by transitivity.** A map that commutes with a group containing the signed
  3-cycles keeps every pair, because a 3-cycle through its value and two further pairs fixes
  the argument; transitivity makes its sign constant. A continuous map of the cover over its
  base carries lifts to lifts, so on a fibre it commutes with `G₊`. Applied to the map that is
  `z` on an open and closed set and `−z` off it, this gives connectedness.
- **Roots of a monic polynomial.** A monic polynomial of degree `n` has a root within
  `|P(z₀)|^{1/n}` of `z₀`. So where the roots of a continuous polynomial family are zeros of
  `H_τ`, the roots form an open and closed subset of the cover.
- **Stabilizers.** The elements of `G₊` that fix finitely many given zeros still carry any
  zero outside their pairs to any other. A zero determined by the given ones is one of them.
- **Doubling of displacements.** If `p^{2 Re ρ}` lies in `B`, every automorphism over `B` keeps
  `Re(ρ + ρ̄)`; conjugating by conjugation doubles the displacement of the real part of `ρ`,
  and the displacements are bounded, so they vanish. The argument runs in every subgroup that
  contains conjugation and keeps the weight.
- **Membership is fixedness.** `E/B` is Galois, so an element of `E` lies in `B` iff every
  automorphism fixes it; two primes separate exponents, so an exponent `δ ∈ Δ` is fixed iff
  `2^δ` and `3^δ` lie in `B`.
- **Symmetric values.** An automorphism that fixes `x + x⁻¹` sends `x` to `x` or `x⁻¹`. For the
  ordinate value `x = p^{2iγ}` has modulus one, so `σρ` and `σρ̄` have one real part; distinct
  zeros with ordinates `±γ'` and one real part are conjugate.
- **Kernels by parity.** A subgroup generated by involutions lies in the kernel of a character
  iff every generator does; a signed involution lies in the kernel of `sgn_pairs · sgn_zerosᵋ`
  iff `c + εk` is even. A subgroup of `W` that contains `W⁰` and an odd permutation of the
  zeros is `W` or one of the two kernels.

## Pillar theorems

All statements are unconditional and formalized in this directory unless a different
directory is named.

**The zero field over complete fibres.**
`L/K` is algebraic and normal, and `K = L` iff RH. `Gal(L/K)` embeds as a closed subgroup of
the product over fibres and multiplicities of the signed permutation groups
`C₂ ≀ Sym(B_{t,m})`; conjugation is the constant sign `−1` and is central; every orbit is
finite; the action is not transitive; every critical zero is fixed; every automorphism moves
a zero by less than one. The group is the inverse limit over the height tower, and finite
compatibility of a family of permutations is equivalent to its realization.
([fibre field](TheFieldOfCompleteFibreTraces.lean),
[action](ThePermutationActionOnAllZeroFibres.lean),
[signed permutations](TheSignedPermutationsOfTheZeroFibres.lean),
[composita](TheFiniteSourceCompositaOfTheZeros.lean),
[height tower](TheHeightTowerOfTheZeroField.lean))

**Real structure.** `L⁺ = L ∩ ℝ`, `F = M ∩ ℝ`, `Gal(M/K) ≅ Gal(F/K) × C₂`. One nonzero width
generates `L` over `L⁺`; `M/L⁺` has degree two or four, with the three quadratic subfields
`F`, `L⁺(i)`, `L` in the second case. `r` lifts to `M` iff `−1` is not a square in `L`; the
lift is unique and central, and the fixed fields of `c`, `r`, `cr` are `F`, `L`, `L⁺(i)`.
The Euclidean-continuous automorphisms are exactly `1` and conjugation.
([real subfield](TheMaximalRealSubfieldOfTheZeroField.lean),
[width field](TheRealWidthFieldOfTheZeros.lean),
[width equations](TheSourceEquationsOfTheZeroWidths.lean),
[biquadratic diagram](TheBiquadraticDiagramOfTheZeroField.lean),
[Gaussian extension](TheGaussianExtensionOfTheZeroField.lean),
[involutions](TheGeometricInvolutionsOfTheZeroField.lean),
[Euclidean topology](TheEuclideanTopologyOfTheZeroField.lean))

**Kummer theory.** `Gal(L/D)` is, with its topology, the group of admissible sign families;
every square relation has an even number of factors. The class `ω` is invariant; it descends
to `K` iff the restriction to `L⁺` splits iff a continuous quadratic character takes the
value `−1` on conjugation. The norm of a squared width has class `ω^n`, and a complete
multiplicity block of `r` pairs has class `ω^r`: an odd degree or an odd block forces the
splitting. `D`-linear relations among the zeros split along the width classes.
([sign kernel](TheKummerRelationsOfTheZeroWidths.lean),
[descent](TheDescentOfTheGlobalWidthSquareClass.lean),
[norms](TheSourceNormsOfTheZeroWidthSquares.lean),
[block characters](TheArithmeticSignsOfTheZeroFibres.lean),
[quadratic detection](TheQuadraticCharactersOfConjugation.lean),
[additive relations](TheArithmeticClassesOfAdditiveZeroRelations.lean))

**Orderings.** Every ordering `Q` of `D` defines a conjugation `σ_Q ∈ Gal(L/D)`, an involution
or the identity, which fixes `√a_q` iff `a_q` is positive in `Q`; the real ordering defines
complex conjugation. Every ordering defines complex conjugation iff every squared width is a
sum of squares in `D`. Every ordering defines the identity or complex conjugation iff every
product `a_q a_r` is a sum of squares in `D`. So a square relation `a_q a_r ∈ D²` binds the
signs at `q` and `r` under all automorphisms, and a relation `a_q a_r ∈ ΣD²` binds them under
the conjugations of orderings.
([orderings](TheOrderingsOfTheSquaredWidthFieldAndTheirConjugations.lean))

**The zero motive.** `Δ` is the fibre product of its ordinate and width projections over a
gluing group killed by two. `r` extends to an additive automorphism of `Δ` iff no nonzero
integer is a weight-zero relation. Prime times are Zariski dense in the character group of
`Δ`, also on every two-prime orbit. The maximal quotient with algebraic values at three prime
times is `Δ ∩ ℚ`.
([motive](TheIntegralZeroMotive.lean),
[reflection descent](TheDescentOfFunctionalEquationReflection.lean),
[prime times](ThePrimeTimePointsOfTheZeroMotive.lean),
[arithmetic quotient](TheMaximalArithmeticQuotientOfTheZeroMotive.lean))

**Symmetries of the prime translations.** Complex-linear maps commuting with `T₂`, `T₃` are
diagonal; real ones are diagonal or diagonal composed with conjugation; the only pointed
nonidentity real symmetry is conjugation. Over `ℚ` the commuting endomorphisms are the scalar
embeddings that preserve the joint spectrum `{(2^z,3^z)}`.
([centralizer](TheCentralizerOfPrimeTranslations.lean),
[real structure](TheRealStructureOfPrimeTranslations.lean),
[scalar descent](TheScalarDescentOfPrimeTranslations.lean))

**The group over the prime traces.** `E/B` is algebraic and normal, `B` is real and contains
a transcendental element. `Gal(E/B)` acts faithfully on the zeros, keeps the absolute
ordinate and commutes with `r`; an embedding over `B` sends a zero to a zero with centred
real part `±` the original. `[F_ρ : H_ρ] ≤ 2`, with equality iff some automorphism exchanges
`ρ` and `1 − ρ`. `Gal(E/H)` is the group of sign families on the reflection radicals
`p^ρ − p^{1−ρ}`; `r` lifts to `E/B` iff every square product of their discriminants has an
even number of factors. A zero with rational real part has the orbit `{ρ, ρ̄}`; an orbit that
meets the line lies on it; `H_ρ = B` iff `Re ρ = ½`, and `H = B` iff RH. The layer of zeros
with rational real part is abelian of exponent two with conjugation central. Two algebraic
prime values at a zero force a rational real part. For any one prime `p`, the orbit of `ρ` is
contained in `{ρ, ρ̄}` iff `p^{2 Re ρ} ∈ B`, and it contains a zero of another real part iff
`p^{2 Re ρ} ∉ B`. An exponent `δ ∈ Δ` is fixed by the group iff `2^δ, 3^δ ∈ B`. For one prime
`p` the ordinate value `2cos(2γ log p)` lies in `B` iff every automorphism carries `ρ̄` to the
conjugate of the image of `ρ`; the condition does not depend on `p`, it follows from
`p^{2 Re ρ} ∈ B`, so it holds at every zero with rational real part, and conjugation is central
in the group iff it holds at every zero. The width value `p^{2β−1} + p^{1−2β}` lies in `B` iff
every automorphism agrees on `ρ, ρ̄` with one of `1`, `c`, `r`, `cr`; then the orbit lies in the
quartet `{ρ, ρ̄, 1−ρ, 1−ρ̄}`, and if moreover `p^{2β} ∉ B`, some automorphism acts on `ρ, ρ̄` as
`r` and `ρ` is off the line. Weight, width and ordinate memberships form a chain. The orbit lies
in the quartet iff the ordinate and width values are the two roots of a quadratic over `B`; then
the ordinate value lies in `B` iff the width value does, and otherwise some automorphism is a
partial flip, `σρ̄ = 1 − conj(σρ)`, exchanging the two values. Inside a quartet the orbits are
therefore `{ρ, ρ̄}`, the quartet acted on through `{1, c, r, cr}`, or the quartet with a partial
flip. The stabilizer of `ρ` is `Gal(E/F_ρ)`, and `[F_ρ : B]` is the size of the orbit: finite,
even, and `2` iff `p^{2 Re ρ} ∈ B`. The generators of `B` obey the functional equation
`T_t(n) = n·T_t(1/n)`, `T_{−t} = T_t`, and `T_t(1)` is the number of zeros of ordinate `±t`; the
traces with `t ≥ 0` and `n ≥ 1` generate `B`. Criticality splits into the two problems: `Re ρ = ½`
iff `p^{2 Re ρ} ∈ B` and some automorphism sends `ρ` to `1 − ρ`; RH holds iff `r` lifts to `E/B`
and every weight value lies in `B`. A lift `σ` of `r` agrees with conjugation at `ρ` iff
`p^{2 Re ρ} ∈ B`, and `cσ` fixes exactly the critical zeros. For each height `t` the field
`E_t = B(p^ρ : |Im ρ| = |t|)` is finite Galois over `B`, `Gal(E/E_t)` is the pointwise stabilizer
of the zeros of that height, `[E_t : B]` is even at occupied heights, and `E` is the compositum of
the `E_t`. An orbit leaves the quartet of `ρ` only through another off-line zero of the same
absolute ordinate with a third real part; if the ordinate value lies in `B`, the conjugates of
`p^{2β}` are the weight values of the orbit. The traces of distinct heights are linearly
independent functions of the prime vector. For the zeros `U_t` of ordinate `t`, the product
`A_{t,p}` of their reflection radicals satisfies `c(A_{t,p}) = (−1)^{|U_t|} A_{t,p}`, every
automorphism multiplies it by `±1`, and `|U_t|` is odd iff `½ + it` is a zero; then for a
suitable prime the product of the radicands of height `t` is a negative non-square of `B`. A lift
of `r` acts on every `A_{t,p}` as `c` does.
([spectral field](ThePrimeSpectralFieldOfTheZeros.lean),
[trace group](ThePrimeTraceGaloisGroupOfTheZeros.lean),
[residue fields](ThePrimeResidueFieldsOfTheZeros.lean),
[reflection kernel](ThePrimeReflectionKernelOfTheZeros.lean),
[rational weights](TheRationalWeightsOfPrimeZeroOrbits.lean),
[rational layer](TheRationalResidueLayerOfTheZeros.lean),
[algebraic relations](TheAlgebraicPrimeRelationsOfTheZeros.lean),
[weight criterion](TheOrbitOfAZeroIsItsConjugatePairIffItsWeightLiesInThePrimeTraceField.lean),
[ordinate criterion](ConjugationIsCentralAtAZeroIffItsOrdinateValueLiesInThePrimeTraceField.lean),
[width criterion](TheGroupActsOnAZeroThroughTheTwoInvolutionsIffItsWidthValueLiesInThePrimeTraceField.lean),
[quartet criterion](TheOrbitOfAZeroLiesInItsQuartetIffItsWidthAndOrdinateValuesSolveAQuadraticOverThePrimeTraceField.lean),
[orbit and degree](TheDegreeOfTheResidueFieldOfAZeroIsTheSizeOfItsOrbit.lean),
[functional equation of the traces](TheMixedPrimeTracesSatisfyTheFunctionalEquation.lean),
[identification of a lift](ALiftOfTheReflectionIsConjugationExactlyWhereTheWeightLiesInThePrimeTraceField.lean),
[fibre layers](TheFibreFieldsOverThePrimeTracesAreFiniteGaloisAndGenerateTheSpectralField.lean),
[leaving the quartet](AnOrbitLeavesItsQuartetOnlyThroughAnotherOffLineQuartetOfTheSameOrdinate.lean),
[independence of heights](TheTracesOfDistinctHeightsAreLinearlyIndependent.lean),
[parity of the radicals](TheReflectionRadicalsOfOneHeightCarryTheParityOfItsZeros.lean))

**Arithmetic groups and the heat cover.** Let `φ` be an injective map between the zeros of ξ
and the zeros of `H_b` at a forward time. If `φ` carries the reflection to `z ↦ −z`, every
automorphism over `B` agrees with an element of `G₊(b)` on any finitely many zeros in distinct
reflection pairs. No `φ` from the forward fibre to the zeros of ξ carries `G₊(b)` into the
group over `B` (`G₊` is transitive on an infinite fibre, the orbits over `B` are finite), and
no `φ` from the zeros of ξ to the forward fibre carries conjugation, or any automorphism moving
infinitely many zeros, to an element of `G₊(b)` (those move finitely many zeros). Every zero of
ξ is the limit as `t → 0⁺` of zeros of `H_t` (a Hermite sheet of its collision at the time `0`);
for finitely many zeros `s_i` in distinct reflection pairs and `σ` over `B`, continuations
`w_i(t) → s_i`, `w'_i(t) → σ s_i` are matched by an element of `G₊(t)` at every small real time
`t` off the branch times.
([finite windows](TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre.lean),
[continued windows](TheArithmeticGroupActsOnContinuedWindowsOfZerosAsHeatMonodromy.lean))

**Over `ℚ`.** `[ℚ(ρ−½) : K_even] ≤ 2`; the negation of all centred zeros is a field
automorphism iff an anchor lies outside `K_even`; `K_even ⊆ ℝ` iff RH.
([even products](TheEvenProductFieldOfTheZeros.lean))

**Finite equations.** Folded discriminant identities; every centred Jensen discriminant is
nonnegative, with square class `μ₂ₙ/μ₀` or `(2n+1)μ₂ₙ/μ₀`; the nonreal census of the quotient
equations is monotone and exhausts the off-line divisor. *Calibration:* the generic folded
polynomial `∏ (X² − x_i²)` over the field of its coefficients has the full group of signed
permutations `C₂ ≀ S_n`, of order `2ⁿ n!`; the reflection of all roots is the uniform flip and
is central. This is the group of the function-field case, where RH says that conjugation is
the uniform flip. The generic centred polynomial of degree `d` without folding has the full
symmetric group (`HTGeometry/CenteredGenericGalois`).

*Fundamental theorem and specialization.* A rational function of `x₁, …, x_n` fixed by all
signed permutations is a rational function of the coefficients `γ_k` of `∏ (Y − x_i²)`, and
`[K(x) : K(γ)] = 2ⁿ n!`. A folded equation `X^{2n} + Σ c_k X^{2k}` whose coefficients are
algebraically independent over `K` has the group `C₂ ≀ S_n` over `K(c)`. The centred Jensen
equation of degree `2n` is the folded equation of the coefficients of `E_n`, which are nonzero
rational multiples of `μ₂/μ₀, …, μ₂ₙ/μ₀`. So over the field of its coefficients its group is
`C₂ ≀ S_n`, or these moments satisfy a polynomial relation over `ℚ`.
([folding](FoldedDiscriminant.lean),
[discriminants](CenteredJensenDiscriminant.lean),
[coefficient field](CenteredJensenDiscriminantField.lean),
[census](FoldedJensenExhaustion.lean), [quartets](JensenQuartetExhaustion.lean),
[generic folded group](TheGenericFoldedEquationHasTheFullSignedPermutationGroup.lean),
[fundamental theorem](TheFoldedCoefficientsGenerateTheFixedFieldOfTheSignedPermutations.lean),
[specialization](AFoldedEquationWithIndependentCoefficientsHasTheFullSignedPermutationGroup.lean),
[Jensen equations](TheJensenEquationsHaveTheFullGroupUnlessTheMomentsAreDependent.lean))

**The heat cover.** The family is analytic in complex time and place and vanishes identically
at no time, so every point of the cover is a collision of a finite order. At a collision of
order `m` the blow-up `G` is analytic on `ℂ²` with `G(0, ·) = (a/m!) Q_m`, and through each of
the `m` roots of `Q_m` passes one analytic sheet `Z_ρ` of zeros. For small `s ≠ 0` the sheets
are distinct and simple, and they are all the zeros of `H_{τ₀+s²}` in a fixed disc around `z₀`.

- *Monodromy.* `Z_ρ(−s) = Z_{−ρ}(s)`: one turn of the time around a collision is the
  reflection `ρ ↦ −ρ` of the Hermite roots, `⌊m/2⌋` disjoint transpositions, with a fixed sheet
  exactly when `m` is odd.
- *The two involutions.* Conjugation carries the sheets of a collision to the sheets of the
  conjugate collision; `z ↦ −z` carries the sheets at `z₀` to the sheets at `−z₀`. At a
  collision at the centre `−Z_ρ(s) = Z_ρ(−s)`: the reflection `r` is the local monodromy. At a
  collision at a real time and a real place all `m` zeros are real after the collision, and
  before it conjugation carries the sheet `ρ` to the sheet `−ρ`: conjugation is the local
  monodromy.
- *Branch locus.* The branch points are isolated in `ℂ²` and the branch times are countable.
  The centre value is positive on the real axis and has infinitely many zeros. So the cover has
  infinitely many branch times, none of them real, at which `r` is the local monodromy. RH says
  that no branch time is real and positive.
- *Position of the sign branch points.* `c` maps the closed backward half-plane `Re τ ≤ 0` into
  the slit plane: every centre time has `Re τ > 0` and `Im τ ≠ 0`. Over backward times `√c` is
  single-valued, the sign character of the cover is trivial, and the trace formula has no
  exceptional time.
- *The sign part.* A zero of order `k` of the centre value is a collision of order `2k` at the
  centre, where the turn of the time flips the sign of `k` pairs of zeros: the product of the
  flipped signs is the Kummer character of `√c`. The normalized Taylor coefficients of `c` are
  the normalized even moments, the generators of `K_J`.
- *The cover as a curve.* The cover is singular exactly at the collisions of order at least
  three. A double collision is a fold: the place is a local coordinate and the time has a
  critical point.
- *Continuation along paths.* Along a path of times that avoids the branch times, lifts of a
  zero are unique, transport of zeros is an injective partial map between the two end fibres,
  and a zero either lifts along the whole path or its lift exists on `[0, b)` with modulus
  tending to infinity at `b`; the two cases exclude each other. A loop permutes exactly the
  zeros that escape neither along it nor along its inverse.
- *Forward tameness.* Over a box `{t₀ ≤ Re τ, ‖τ‖ ≤ T₀}`, `t₀ > 0`, the zeros of large modulus
  lie in the strip `|Im z| < 12 + 21T₀` and are simple, and the box contains finitely many
  branch times. No zero escapes along a path of times in `Re τ > 0`. Along a path of forward
  times that avoids the branch times every zero lifts, and transport is a bijection between
  the fibres over the two ends; along a loop it is a permutation of the fibre. The multiple
  zeros form a closed discrete subset of `ℂ²`.
- *The forward monodromy group.* The transports along the loops of forward times based at `τ`
  form a group `G₊(τ)` of permutations of the zeros of `H_τ`. Every element commutes with
  `r : z ↦ −z`: the group consists of signed permutations of the pairs `{z, −z}`. Over a real
  time `t > 0` the involution `cr : z ↦ z̄` is an element of `G₊(t)`: it is the transport
  along a path to a time with real zeros followed by the reversed conjugate path. RH says
  that this element is the identity over every positive real time off the branch times.
  The groups at two base times are conjugate by a transport.
- *Turns.* The circle `τ₀ + r²e^{2πis}` around a forward collision is a forward loop, and its
  transport is the Hermite reflection `Z_ρ ↦ Z_{−ρ}` of the sheets. Conjugated to any base
  time it is an element of `G₊`. A turn around a centre time exchanges a zero with its
  negative; a turn around a collision away from the centre carries a zero out of its pair.
  If `G₊` preserves every pair `{z, −z}`, RH holds.
- *Homotopy invariance.* The simple zeros form a separated local homeomorphism over the
  times. Lifts through simple zeros of a family of paths with fixed ends end at one zero; the
  paths may cross branch times. So transport depends only on the homotopy class of the
  forward path off the branch times, a loop in a convex set of forward times without branch
  times transports every zero to itself, and `G₊` is a quotient of the fundamental group of
  the forward half-plane without the branch times.
- *Finite support.* Every element of `G₊(τ)` moves finitely many zeros: for a box of times and
  a modulus of continuity there is a radius beyond which every loop fixes every zero. Every
  fibre over a forward time off the branch times is infinite, so the reflection `r` is not an
  element of `G₊(τ)`.
- *The turn on the whole fibre.* For every forward time `τ₀` and every small `r`, the turn
  around `τ₀` fixes every zero of `H_{τ₀+r²}` that is not a sheet of a collision of order at
  least two at `τ₀`, and reflects the sheets. At a centre time whose central collision is
  double and is the only collision, the turn is the sign flip of one pair, and `G₊` at every
  base time contains the sign flip of exactly one pair.
- *Generation.* Over a convex open set `D` of forward times, every subgroup that contains the
  transports of arbitrarily small turns around the branch times of `D`, conjugated to the
  base time along paths inside `D`, contains the transport of every forward loop inside `D`.
  `G₊(τ)` is generated by the turns around the forward branch times, conjugated to `τ`.
- *Only a collision off the centre moves a pair.* Over a convex open set of forward times
  whose multiple zeros are all at the centre, every loop carries every zero `z` to `z` or to
  `−z`. So a loop inside a convex region that carries a zero out of its pair certifies a
  multiple zero `ζ ≠ 0` at a time of the region. `G₊` preserves every pair if and only if no
  multiple zero `ζ ≠ 0` exists at a forward time; it is then commutative of exponent two.
- *A collision away from the centre exists.* For `Re a ≥ 50` and
  `1/(4 Re a) ≤ π/4 − Im a ≤ 1/Re a`, at the time `τ = πe^{2a}/a` and for `‖ζ‖ ≤ 8`:
  `‖H_τ(ζ/a) − B₀(a) − 2S₀(a) cos ζ‖ ≤ C (Re a)⁵ e^{−Re a}(‖B₀(a)‖ + ‖S₀(a)‖)`. For every `T`
  there are a time `τ` with `Re τ > T` and a place `ζ ≠ 0` with `H_τ(ζ) = H_τ'(ζ) = 0`. At
  every forward base time off the branch times, `G₊` contains an element that carries a zero
  `z` to a zero other than `±z`: the forward monodromy group does not preserve the pairs.
- *Transitivity.* For every forward time `b` off the branch times and all zeros `p, q` of
  `H_b` some element of `G₊(b)` carries `p` to `q`. Mechanism: at a real saddle `σ` far out the
  cosine term dominates and each strip `πk < Re(σz) < π(k + 1)` of a window holds one zero;
  a path of saddles on which the cosine term dominates keeps each zero in its strip; for each
  sign `ε` a loop of saddles with `2S₀ cos ξ₀(s) ≈ εB₀` exchanges the zeros of two adjacent
  strips, those around `πk` with `cos πk = −ε`, so the two signs together link all strips of
  the window. Along real times `≥ 1/8` the zeros keep sign and order, and a count of the zeros
  of `H_{1/8}` in a disc places every zero of the disc in a strip of the window.
- *The word of conjugation.* Over a real time `t > 0` off the branch times, `cr` is the
  product `λ_m ∘ ⋯ ∘ λ₁` of turn lassos around the real branch times `p₁ < … < p_m` above `t`,
  with tails in a thin box above the real axis. It inverts the turns around real times:
  `(cr) θ (cr) = θ⁻¹`.
- *The even signed permutations.* Finitely many zeros followed through simple zeros along a
  path of forward times, which may cross branch times, are transported by one forward path
  off the branch times. For every window one element of `G₊(1/8)` moves the zeros with odd
  number down by one, another the zeros with even number. A group of permutations of `ℤ` of
  finite support with the window reflections `m ↦ −m − 1`, `m ↦ −m` contains every 3-cycle.
  So `G₊(b)` contains the signed 3-cycle of any three zeros in distinct pairs and the double
  flip of any two pairs: `W⁰ ≤ G₊(b) ≤ W`, with `W⁰` the subgroup of index four of the
  elements even on the zeros and even on the pairs.
- *Multiple transitivity.* Finitely many zeros, no two equal or opposite, are carried to any
  such zeros by one element of `G₊(b)`.
- *The sign of the zeros.* The centre value has simple zeros at forward times of arbitrarily
  large real part; there one pair collides at the centre. The turn around such a time is an
  involution that flips exactly one pair. So `G₊(b)` contains the flip of every single pair,
  or, for all triples of pairs, the flip of one pair times the exchange of the other two. In
  both cases it contains an odd permutation of the zeros.
- *Index at most two.* Of two signed permutations of finite support, one lies in `G₊(b)` or
  their quotient does. `G₊(b)` is normal in `W`. For the exchange `e` of any two pairs
  `W = G₊(b) ∪ G₊(b)e`, and `G₊(b) = W` as soon as it contains one such exchange. So `G₊` is
  `W`, or the kernel of the sign on the pairs, or the kernel of the product of the sign on
  the zeros and the sign on the pairs.
- *The turns and their parity law.* The turn around every forward time is an involution of
  `G₊`. It carries a zero to its negative exactly on the `2k` sheets of the collision at the
  centre, `k` the order of vanishing of the centre value: the sign of a turn on the zeros is
  `(−1)^k`. It moves `M = 2k + 4c` zeros. `G₊ ≠ W` iff there is `ε ∈ {0, 1}` with `c + εk`
  even at every forward time, and then `G₊` is the kernel of `sgn_pairs · sgn_zerosᵋ`. In that
  case `8 ∣ M` off the centre times, in particular at every real
  time, and `M mod 8` is one number, `2` or `6`, at all simple centre times. A turn around
  one double collision off the centre and no other collision is the exchange of two pairs.
- *The two involutions from the group.* A map of the fibre that commutes with `G₊(b)` is the
  identity or `r`, and the centre of `G₊(b)` is trivial. Over a real time `t`, a permutation
  `σ` with `T_γ̄ = σ T_γ σ⁻¹` for every forward loop `γ` and its mirror loop `γ̄` is `cr` or
  `c`. The zeros of `H_t` are all real iff `T_γ̄ = T_γ` for every forward loop at `t`, and RH
  holds iff this is so over every real `t > 0` off the branch times.
- *Rigidity.* Over the forward times off the branch times the cover is connected. A
  continuous map of the cover that carries the zeros of `H_τ` to zeros of `H_τ` is `z`
  everywhere or `−z` everywhere; one that carries them to zeros of `H_τ̄` is `z̄` everywhere or
  `−z̄` everywhere. No zero is a continuous function of the time. A monic polynomial of fixed
  degree with coefficients continuous in the time has, at some time, a root that is not a
  zero. A zero that is a continuous function of the time and of `n` zeros is one of them up
  to the sign. The configurations of `n` zeros, no two equal or opposite, form a path
  connected set for every `n`, and a polynomial relation `P_τ(z₁, …, zₙ) = 0` that holds on an
  open and closed nonempty set of them has `P_τ = 0` at every time: zeros in distinct pairs
  are algebraically independent over the functions of the time. Near a configuration the
  configurations are the graph of analytic functions of the time, so they form an irreducible
  analytic curve: a function analytic at every configuration vanishes on all of them or on a
  discrete set, and a polynomial relation with coefficients analytic in the time that holds
  on configurations accumulating at a configuration is the zero polynomial at every time. An
  equivalence relation on a
  fibre that `G₊` preserves is equality, the relation `z' = ±z`, or everything: the action on
  the pairs is primitive, and the cover of the squared zeros is the only cover between the
  cover of the zeros and the forward times.
- *Real branch times.* If a segment of real times from `a < 0` to `b > 0` contains no branch
  time, then infinitely many nonreal zeros of `H_a` escape along it. So every real
  neighbourhood of the time `0` contains a branch time, or zeros escape along real times
  arbitrarily close to `0`. A real branch time is a collision away from the centre. A nonreal
  zero at a negative time `a` that neither collides nor escapes on `[a, 0]` arrives at a zero
  of ξ off the line. So under RH, for every `a < 0`: a branch time lies in `[a, 0]`, or every
  nonreal zero of `H_a` escapes before the time `0`.
- *The fibre and its trace.* `H_τ(z) = Σ_k (−1)^k c^{(k)}(τ) z^{2k}/(2k)!`: over every time
  the equation of the fibre has the jet of `c` as coefficients. For every complex time
  `‖H_τ(z)‖ ≤ exp(C(1+‖z‖)log(2+‖z‖))`. Where `c(τ) ≠ 0` the fibre trace is
  `Σ 1/z² = c'(τ)/c(τ)`. At a centre time where `k` pairs collide, `(τ − τ₀) Σ 1/z² → k`: the
  trace is meromorphic in the time, its poles are the branch points with monodromy `r`, and
  the residue is the number of sign changes.

In `RHTower`: after every positive time there are finitely many real collisions, and the
number of nonreal zeros at a positive time is the number of sheets moved by the later real
collisions.
([heat cover](TheHeatCoverOfTheZeros.lean),
[Hermite monodromy](TheHermiteMonodromyOfACollision.lean),
[exhaustion and branch points](TheSheetsOfACollisionAreAllItsZeros.lean),
[central collisions](TheFunctionalEquationIsAMonodromyOfTheHeatCover.lean),
[centre value](TheCentreValueIsTheEquationOfTheSignBranchPoints.lean),
[fibre trace](TheTraceOfAFibreOfTheHeatCover.lean),
[position of the centre times](TheSignBranchPointsLieInTheForwardHalfPlane.lean),
[continuation](AZeroContinuesAlongAPathOfTimesUntilItEscapes.lean),
[real branch times](RealBranchTimesAccumulateAtTheTimeOfXiUnlessZerosEscape.lean),
[Gaussian average](TheHeatFamilyAtForwardTimesIsAComplexGaussianAverageOfXi.lean),
[saddle value](TheHalfTransformIsXiAtTheSaddlePoint.lean),
[strip](TheReflectedHalfTransformIsDominated.lean),
[local exponential](TheHalfTransformIsLocallyAnExponential.lean),
[far zeros](FarZerosAtForwardTimesAreSimple.lean),
[no escape](NoZeroEscapesOverForwardTimes.lean),
[forward monodromy group](TheTransportsOverForwardTimesFormAGroup.lean),
[conjugation](ConjugationOfTheZerosIsAMonodromyOfTheHeatCover.lean),
[turns](TheTurnAroundAForwardBranchTimeIsANontrivialForwardMonodromy.lean),
[homotopy invariance](TheTransportOfAZeroDependsOnlyOnTheHomotopyClass.lean),
[finite support](EveryForwardMonodromyMovesFinitelyManyZeros.lean),
[the turn on the whole fibre](TheTurnAroundABranchTimeMovesOnlyTheSheetsOfItsCollisions.lean),
[gluing](TheMonodromyOverAUnionOfTwoRegionsComesFromTheRegions.lean),
[generation](TheTurnsGenerateTheForwardMonodromyGroup.lean),
[pairs](OnlyACollisionOffTheCentreMovesAPair.lean),
[corner path](TheHeatFamilyIsAnIntegralThroughTheOriginAndTheSaddle.lean),
[Gaussian at the saddle](TheGaussianAtTheSaddleOfTheKernel.lean),
[bulk term](TheSegmentThroughTheOriginIsAGaussianAtTheCentreValue.lean),
[saddle term](TheLineThroughTheSaddleIsAGaussianAtTheSaddleValue.lean),
[two-term model](TheHeatFamilyAtASaddleTimeIsAConstantPlusACosine.lean),
[loop of saddles](ALoopOfSaddlesTurnsTheSquaredRatioOfTheTwoTermsAroundOne.lean),
[collision away from the centre](ACollisionAwayFromTheCentreExistsAtAForwardTime.lean),
[simple joins](AZeroFollowedThroughSimpleZerosIsMovedByTheForwardMonodromy.lean),
[tracking](AZeroAloneInAMovingRegionIsFollowedThroughSimpleZeros.lean),
[signed loops](ForEachSignALoopOfSaddlesTurnsTheRatioOfTheTwoTerms.lean),
[strips](AZeroOfAStripStaysInItsStripWhereTheCosineTermDominates.lean),
[exchange of strips](ASignedLoopOfSaddlesExchangesTheZerosOfTwoAdjacentStrips.lean),
[real times](TransportAlongRealTimesKeepsTheOrderOfTheZeros.lean),
[real saddles](AtARealSaddleEachStripOfTheWindowHoldsOneZero.lean),
[transitivity](TheForwardMonodromyGroupIsTransitiveOnTheZeros.lean),
[word of conjugation](ConjugationOfTheZerosIsTheWordOfTheTurnsAroundTheRealBranchTimes.lean),
[several zeros](SeveralZerosFollowedThroughSimpleZerosAreMovedByOneForwardMonodromy.lean),
[numbering](TheNumberOfAZeroInTheOrderOfTheRealLineIsItsStripAtARealSaddle.lean),
[parity shifts](OneForwardMonodromyMovesTheZerosOfOneParityOfAWindowDownByOne.lean),
[3-cycles on `ℤ`](AFinitaryGroupOnTheIntegersWithWindowReflectionsContainsEveryThreeCycle.lean),
[signed groups](AFinitaryGroupOfSignedPermutationsWithWindowReflectionsContainsTheEvenOnes.lean),
[even signed permutations](TheForwardMonodromyGroupContainsTheEvenSignedPermutationsOfTheZeros.lean),
[multiple transitivity](TheForwardMonodromyGroupMovesFinitelyManyZerosInDistinctPairsAtWill.lean),
[simple centre zero](TheCentreValueHasASimpleZeroAtAForwardTime.lean),
[one flipped pair](TheTurnAroundACollisionOfOnePairAtTheCentreFlipsExactlyOnePair.lean),
[removing exchanges](AnInvolutionWithOneFlippedPairGivesTheFlipOfOnePairUpToOneExchange.lean),
[flip up to exchange](TheForwardMonodromyGroupContainsTheFlipOfEveryPairUpToOneExchange.lean),
[normal form](ASignedGroupWithTheEvenPermutationsAndAFlipUpToAnExchangeHasIndexAtMostTwo.lean),
[index two](TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport.lean),
[parity of the quartets](AnOddNumberOfQuartetsOfNonrealZerosAtARealTimeGivesEverySignedPermutation.lean),
[isolated double collision](TheTurnAroundAnIsolatedDoubleCollisionOffTheCentreIsTheExchangeOfTwoPairs.lean),
[turns are involutions](EveryTurnIsAnInvolutionThatFlipsAsManyPairsAsTheOrderOfTheCentreValue.lean),
[parity of involutions](TheInvolutionsOfAProperForwardMonodromyGroupObeyAParityLaw.lean),
[parity law of the turns](TheTurnsOfAProperForwardMonodromyGroupObeyAParityLaw.lean),
[sign of finite support](APermutationOfFiniteSupportHasAMultiplicativeSign.lean),
[sign characters](TheSignedPermutationsOfFiniteSupportHaveTwoSignCharacters.lean),
[parity criterion](TheForwardMonodromyGroupIsProperExactlyWhenItsTurnsObeyOneParityLaw.lean),
[centralizer and mirror](TheForwardMonodromyDeterminesTheReflectionAndTheConjugationOfTheZeros.lean),
[deck maps](TheReflectionIsTheOnlySymmetryOfTheHeatCoverOverTheForwardTimes.lean),
[connectedness](TheHeatCoverOverTheForwardTimesIsConnectedAndHasNoPolynomialFactor.lean),
[independence](AZeroThatIsAContinuousFunctionOfFinitelyManyZerosIsOneOfThemUpToTheSign.lean),
[configurations](TheConfigurationsOfZerosInDistinctPairsOverTheForwardTimesAreConnected.lean),
[intermediate covers](TheOnlyIntermediateCoverOfTheZerosIsTheCoverOfTheSquaredZeros.lean),
[analytic relations](AnAnalyticRelationAmongZerosInDistinctPairsHoldsOnEveryConfigurationOrOnADiscreteSet.lean))

## Criteria

- **Q1** The base field is defined from the primes or from complete fibres, never from
  single zeros. The base of the cover is a named region of times.
- **Q2** Every statement names its base. Over `K` the group is trivial iff RH; over a smaller
  field or on the cover a large group is compatible with RH.
- **Q3** A classification names the classes of conjugation and of the reflection.
- **Q4** The theory reproduces the curve case with its signed-permutation group.
- **Q5** A statement that forces the two involutions to agree must fail for a configuration
  with a quartet: the zero set of a two-sided edit of the primes with a fake pair, or a heat
  family with a quartet, to which every construction of the theory applies as well.
- **Q6** A transitive action on the zeros over `K` is excluded; nothing may assume one.
- **Q7** `K`, `B` and the base of the cover are kept apart. A statement passes from one to
  another only through a theorem that names the map and what it preserves.

## Problems

Each problem names its base. The calibration questions concern the finite equations and `K`.

1. **A presentation of `B`.** `B` is generated by the paired prime source germs of complete
   fibres: the mixed trace at the height `t` and the prime vector `m` is the sum of the
   continued source germs of the fibres at `t` and `−t` with the weight `exp(z Σ m_p log p)`.
   Settled: the traces are real; the prime values of each fibre are the roots of one polynomial
   over `B`; the functional equation gives `T_t(n) = n·T_t(1/n)` and `T_{−t} = T_t`; `T_t(1)`
   counts the zeros of ordinate `±t`; the traces with `t ≥ 0`, `n ≥ 1` generate `B`. The finite
   layers: `F_ρ = B(2^ρ, 3^ρ)` is finite over `B` of degree the size of the orbit, and `E` is the
   compositum of the finite Galois layers `E_t = B(p^ρ : |Im ρ| = |t|)`. Across heights there is
   no linear relation: the trace functions of distinct heights are linearly independent. Open:
   algebraic relations among the traces of different heights (a transcendence question), and
   the position of the prime values of one zero over the field of the traces of finitely many
   heights. An equality of fields restates the definition;
   a relation that is not a consequence of the definition and the functional equation is the
   objective.
2. **Orbits and stabilizers over `B`.** Settled: membership is fixedness; the stabilizer of `ρ`
   is `Gal(E/F_ρ)` and `[F_ρ : B]` is the size of the orbit, finite and even; for one prime `p`
   the orbit of `ρ` is `{ρ, ρ̄}` iff `p^{2 Re ρ} ∈ B` iff `[F_ρ : B] = 2`; the ordinate value
   `u = 2cos(2γ log p)` lies in `B` iff the image of `ρ̄` is the conjugate of the image of `ρ`
   under every automorphism, and conjugation is central iff this holds at every zero; the width
   value `v = p^{2β−1} + p^{1−2β}` lies in `B` iff every automorphism acts on `ρ, ρ̄` as one of
   `1, c, r, cr`; weight ⇒ width ⇒ ordinate, and a width without weight realizes `r` on the
   quartet of an off-line zero; the orbit lies in the quartet iff `u + v, uv ∈ B`, and then the
   three orbit types are separated by `p^{2β}` and `v`. An orbit leaves the quartet only if two
   distinct off-line quartets share an absolute ordinate; when conjugation is central at `ρ` it
   leaves exactly when `p^{2β}` has a conjugate other than `p^{2β}`, `p^{2−2β}`. So leaving the
   quartet is reduced to a coincidence of ordinates in the zero configuration. Open: which prime
   values of a zero with irrational real part lie in `B`. The pair criterion does
   not force the weight `p`, so it does not give `Re ρ = ½`.
3. **The reflection lift.** Settled: `H_ρ = B` iff `Re ρ = ½`; `Gal(E/H)` is the group of sign
   families on the reflection radicals `p^ρ − p^{1−ρ}`; `r` lifts to `E/B` iff every square
   product of their discriminants has an even number of factors. A lift `σ` is conjugation at
   `ρ` iff `p^{2 Re ρ} ∈ B`, so the identification of a lift with conjugation is the weight
   problem of 2; RH iff `r` lifts and all weights lie in `B`; under a lift `cσ` fixes exactly the
   critical zeros. Source parity: the product of the radicands of the zeros of ordinate `t` is
   `A_{t,p}²` with `c(A_{t,p}) = (−1)^{|U_t|} A_{t,p}`, and `|U_t|` is odd iff `½ + it` is a zero;
   then the product is a negative non-square of `B` for a suitable `p`, and a lift of `r` acts on
   `A_{t,p}` as `c`. This class is compatible with a lift and does not force criticality. Open: a
   source restriction that separates the lift from conjugation.
4. **Arithmetic groups and the heat cover.** The heat group is known up to one sign. `G₊(τ)`
   is a group of signed permutations of the pairs, the same up to conjugation at every base
   time and generated by the turns around the forward branch times; every turn is an
   involution; `W⁰ ≤ G₊ ≤ W` with index at most two, `G₊` contains an odd permutation of the
   zeros, is transitive and multiply transitive on the pairs with all signs; `G₊ = W` iff it
   contains the exchange of two pairs, and `G₊ ≠ W` iff one parity law `c + εk ≡ 0 (mod 2)`
   holds at all forward times, `G₊` being then the kernel of `sgn_pairs · sgn_zerosᵋ`. `cr`
   is the word of the turns around the real branch times, `r` is the centralizer of `G₊`, and
   RH says that every forward loop at a real time and its mirror loop transport the zeros
   alike. Open: the sign (one forward time with `8 ∤ M` off the centre times, two simple
   centre times with different `M mod 8`, or an odd number of quartets of nonreal zeros at one
   real time gives `G₊ = W`), and a comparison with the groups over `K` and `B`. These act on
   the zeros of ξ, the fibre at the time `0`, keep every ordinate class and commute with `c`
   or `r`; `G₊` acts on a fibre at a forward time and is primitive on the pairs. Settled: an
   injective identification of the fibres that respects the reflection makes every
   automorphism over `B` a heat monodromy on every finite window, and no identification carries
   one group into the other on a whole fibre; along continuations of the zeros from the time
   `0`, every automorphism over `B` is matched on each finite window by heat monodromies at all
   small real times. Open: the sign, which needs the full fibre at one turn (the
   two-term model controls a window near the centre; the zeros between the window and the far
   zeros are not controlled at a model collision time), and a time `t₀` uniform in the window.

Calibration questions.

- **Independence of the moments.** Are the normalized moments `μ₂/μ₀, …, μ₂ₙ/μ₀` of `Φ`
  algebraically independent at each degree? The group of the Jensen equation of degree `2n`
  over the field of its coefficients is `C₂ ≀ S_n` unless they satisfy a polynomial relation
  over `ℚ`. Already whether `μ₂/μ₀` is a square in `K_J` is not known.
- **Degree.** Is `[L:K]` one or infinite? A finite nontrivial degree is the Galois form of a
  finite stratum.
- **Sums of squares.** Is every squared width a sum of squares in `D`? This holds iff every
  ordering of `D` induces complex conjugation; an ordering in which two squared widths have
  different signs exists iff some product `δ_q²δ_r²` is not a sum of squares in `D`.

## Milestones

| | Milestone | State |
|---|---|---|
| M1 | the zero field over `K` and its criteria | formalized |
| M2 | the group over `B`: faithful action, residue and reflection fields, rational layer | formalized |
| M3 | orbits over `B` by the weight and ordinate values; centrality of conjugation | formalized |
| M4 | the orbit types inside a quartet: pair, Klein action, partial flip | formalized |
| M5 | stabilizers and degrees: `[F_ρ : B] = |G·ρ|`; finite Galois layers `E_t` | formalized |
| M6 | orbits that leave the quartet: reduced to a coincidence of ordinates of off-line quartets | formalized |
| M7 | relations among the traces from the functional equation; half the generators | formalized |
| M8 | relations among the traces of different heights: none linear | formalized |
| M8′ | algebraic relations among the traces of different heights | open |
| M9 | RH splits into the reflection lift and the weights; a lift is `c` where the weight is in `B` | formalized |
| M10 | the source class of the radicands of one height (parity of its zeros) | formalized |
| M10′ | a source-derived restriction that forces the lift of `r` to be `c` | open |
| M11 | the Jensen dichotomy: full group or dependent moments | formalized |
| M12 | the forward monodromy group with the turns and conjugation as elements; a collision away from the centre | formalized |
| M13 | `W⁰ ≤ G₊`, an odd permutation, index at most two, `G₊ ≠ W` iff one parity law | formalized |
| M14 | the two involutions from `G₊`; rigidity and connectedness of the cover | formalized |
| M15 | the sign: whether `G₊ = W` | open |
| M16 | `G₊` and the group over `B`: finite windows yes, whole fibres no | formalized |
| M17 | specialization from the time `0` on continued windows of zeros (multiple zeros included) | formalized |
| M17′ | a time `t₀` uniform in growing windows (non-escape near the time `0`) | open |
| M18 | independence of the moments at low degree; the degree over `K` | open |

## Tools

Infinite Galois theory through finite subextensions (the Krull topology, inverse limits over
the height tower, finite composita, membership as fixedness); Kummer theory of square classes
(width classes, reflection radicands, descent); divisor-valued source moments (complete-fibre
traces and paired prime source germs); arithmetic presentations of the base fields; analytic
specialization (genericity for the finite equations, and from the heat cover to fixed fibres);
the Artin–Schreier theory of real fields (orderings and the conjugations they define);
transcendence of prime powers and the separation of exponents by two primes; transport along
paths of times, with its homotopy invariance; Hermite blow-ups; words of local monodromies;
gluing of the monodromy over open regions; subgroups as detectors of collisions; saddle-point
asymptotics of the heat family at complex times of large modulus, with the minimum-modulus
principle to place zeros and continuity to follow them; permutation groups of finite support
(3-cycles from window reflections, normal forms modulo a subgroup, centralizers, the sign on
the zeros and the sign on the pairs); the open mapping theorem applied to an approximate
model; roots of monic polynomials. A tool belongs here when it is applied to one of the four
problems.

## Traps

- The functional equation, the Gamma factor and the zero count admit models with zeros off
  the line; so do Euler products over the rational primes with a count rate.
- Fixing every single zero defines the trivial group before any arithmetic enters. Fixing
  aggregate traces is a different requirement.
- The zeros are not known to be algebraic; a splitting field over an unspecified field is not
  an arithmetic object. An infinite zero set is not the root set of one polynomial.
- `K` and `B` are different fields. `K = L` is equivalent to RH; `B` contains transcendental
  numbers and its group keeps the absolute ordinate. A theorem over one is not a theorem over
  the other.
- Coefficients defined from the desired zeros satisfy the polynomial they define; a
  restriction must come from a source (primes, complete fibres, the branch divisor).
- An orbit `{ρ, ρ̄}` does not give `Re ρ = ½`: the pair criterion asks `p^{2 Re ρ} ∈ B`, not
  `p^{2 Re ρ} = p`, and every membership criterion holds at every zero with rational real part.
- A lift of `r` over `B` is not conjugation. Criticality needs a theorem identifying the lift
  with `c`.
- The heat monodromy acts on a fibre at a forward time and is generated by turns around
  complex times; field automorphisms act on the fibre at the time `0`. The two have different
  domains, and a comparison needs a named map.
- Centrality of conjugation does not give purity: it holds over `K` unconditionally.
- A large group does not contradict RH and a small group does not prove it; the statement is
  always the position of `c` relative to `r`.
- Membership of conjugation in `G₊` and its commutation with the reflection do not make it
  trivial. Triviality of the whole group `G₊` is false: every centre time gives a sign flip.
- A statement on the cover that uses no feature of `Φ` cannot produce an exchange. The family
  `(τ − τ₀)^{ν/2} f(z/√(τ − τ₀))`, `f` an even solution of Weber's equation, solves the same
  heat equation, has infinitely many sheets `z² = ρ_j²(τ − τ₀)`, and no collision away from
  the centre; for a polynomial this is the Hermite case, the only one with a single centre
  time.
- Trace positivity of the reflection is Weil's criterion; renaming it proves nothing.
- A finite window, a bounded degree or finitely many prime times does not replace a theorem
  on the whole divisor without a proved uniform passage.
- Changing `ρ` to `w` involves `i`: the two generate the same field over `ℚ` only after `i`
  is adjoined.
- The monodromy of a cover is taken over complex parameters. Real-time statements about
  collisions describe conjugation, not the monodromy group.
- A collision at the centre is not a failure of RH. It happens at a nonreal time and realizes
  `r`. Only a collision at a positive real time contradicts RH. Collisions away from the
  centre exist at nonreal forward times; "`G₊` preserves the pairs" is false and is not a
  form of RH.
- The ratio `2S₀/B₀` of the two terms involves two square roots. Statements about its sign
  go through the square `Q` and a continuity argument, or through a fixed branch on a region
  where the radicands have positive real part.
- A branch time may carry several collisions. In the two-term model all collisions near
  `ζ ∈ πℤ` of one sign happen at one time up to the error of the model, so the turn around
  such a time is known on a window of zeros, not on the fibre, and its sign on the pairs is
  not known. A statement on a turn must cover every collision at its time.
- The size of `G₊` is not a form of RH and gives no route to it: at index at most two in `W`
  every signed permutation of a finite set of pairs occurs. RH is the value of one element.
- The rigidity statements are on continuous single-valued maps over the forward times off the
  branch times and on polynomial relations. Analytic relations among several zeros exist:
  `H_τ(zᵢ) = 0`. The identity theorem on the configurations says that a relation persists,
  not that it is trivial.
- The heat cover has infinitely many sheets and is not proper over the time plane. The local
  theory gives uniqueness of lifts and continuation up to escape; that no zero leaves every
  compact set along a compact path of times is a theorem only for `Re τ > 0`.
- The branch times are discrete in the forward half-plane, not in the time plane unless zeros
  escape: the time `0` is a limit of real branch times or zeros escape near it. Far zeros at
  times with `Re τ ≤ 0` are as hard to control as the zeros of ζ.
- Barriers do not prove non-escape: over a set of times with interior a far zero sweeps a
  region larger than the spacing of the zeros, so no circle is free of zeros for all times.
  The family varies on the time scale `1/log²‖z‖`; only the phase between the two exponentials
  is stable.

## Open research topics

- Any automorphism of `L/K` or `E/B` other than conjugation, or its exclusion.
- The square-class relations among the widths of two fibres, and among the reflection
  discriminants of two zeros.
- Algebraic relations among the mixed prime traces of different heights (linear relations are
  excluded): the transcendence degree of the field of the traces of finitely many heights, and
  the degree of the prime values of one zero over such a field.
- The image of `G` in the signed permutations of the reflection pairs of one height; for an
  isolated quartet the degree `[E_t : B] ∈ {2, 4, 8}` of the three orbit types.
- Which of the weight, width and ordinate values of a zero with irrational real part lie in `B`;
  a source restriction on the reflection radicands beyond the parity class of one height.
- Algebraic relations among the normalized moments `μ₂ₙ/μ₀`, which decide whether a Jensen
  equation is generic.
- The collisions away from the centre as a set. The central branch times are the zeros of one
  function of the time, the centre value; for the others no such function is known. The
  known ones lie near the times with `2S₀ = ±B₀`, in the direction of the imaginary axis.
  Which sign occurs on a given loop of saddles.
- The sign on the pairs. Existence statements, each of which gives `G₊ = W`: a forward time
  off the centre times whose ramification is not divisible by `8`, for instance one double
  collision away from the centre and no other collision; two simple centre times with
  different ramification modulo `8`; a real time with an odd number of quartets of nonreal
  zeros. A centre time at which the central collision is double and no other collision
  happens gives the flip of a single pair, not the sign on the pairs.
- A property of the branch divisor that makes the transports of a forward loop at a real time
  and of its mirror loop agree; a mirror-symmetric presentation of `G₊` by turns.
- The ideal of the analytic relations among `n` zeros in distinct pairs. A relation that
  holds on a non-discrete set of configurations holds on all of them, and polynomial relations
  with analytic coefficients are trivial; `H_τ(zᵢ)` are relations, and whether they generate
  all of them is open.
- Non-escape and accumulation of branch times at times with `Re τ ≤ 0`; control of transport
  as `τ → 0`.
- Simplicity of every zero of the centre value (all central collisions double; simple zeros
  exist at forward times of arbitrarily large real part), and the position of the centre
  times inside the forward half-plane.
- Whether the squared widths and their pairwise products are sums of squares in `D`. Orderings
  of `K` and `B`, where the conjugation of an ordering is a class of involutions and needs
  real closures.
- A decomposition or Frobenius structure at a prime.
- A specialization from the heat cover at forward times to the fibre at the time `0` on growing
  windows. On a whole fibre none exists (the orbits over `B` are finite, `G₊` is transitive,
  conjugation moves every zero of ξ); on finite windows every automorphism over `B` is a heat
  monodromy.

## Place in the wider research

`ArithmeticCastelnuovoSeveri` owns the Weil form on the zeros and its index laws; the trace form
of the reflection is that form. `RHTower` and `NodalGeometryOfTheDeBruijnFlow` own the heat
family at real times, its collision counts and their Hermite limits; this programme extends the
family to complex time and owns its cover of zeros. `HTGeometry` owns the generic Galois groups
and the analytic implicit-function tools. `TranscendenceTheoryOfThePrimeOrbit` owns the
six-exponentials input. `WorldsOfTheZeroConfiguration` supplies the edits against which Q5 is
tested. `RHTower/Artin` owns the characters of covers. This programme owns the fields generated
by the zeros, their groups, the lifts of the two involutions, and the monodromy reading of
collisions.

## Contribution and success criteria

A contribution answers a part of one of the four problems or a calibration question, reaches a
milestone, builds a tool and applies it to one of the problems, or classifies an obstruction
together with its strongest positive survivor. It concerns the whole divisor, the whole family,
or a generic object that calibrates them, and it names its base: a field, or a region of times.
It passes Q1–Q7. New terminology, isolated finite examples, constants, and restatements of known
criteria for RH do not qualify.

Every claim is a Lean theorem without added premises. Modules live in this directory and are
imported by `../GaloisTheoryOfZeros.lean`.

**First breakthrough.** A source-derived restriction on the reflection square classes or on
the prime weights that is not the corresponding zero-location criterion rewritten.

The programme is complete when each problem has an answer or an exact reduction to a named
statement outside Galois theory, and each tool has an application. A restriction from the
primes that locates conjugation would be a proof of RH; the programme does not claim one.
