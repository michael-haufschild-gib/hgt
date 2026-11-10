# Absolute Geometry of Spec ℤ (AGZ)

Namespace `GaloisForLFunctions.AbsoluteGeometryOfSpecZ`; umbrella `AbsoluteGeometryOfSpecZ.lean`.
Specification: §2.14 of
[the review-1011 summary](../../../docs/reports/review-1011/obstacles-summary.md); background:
§9 of [the review-1011 report](../../../docs/reports/review-1011/fable.md). Paper proofs:
`docs/drafts/pipeline/3-formalized/agz-absolute-geometry-of-spec-z.md`.

The programme is this folder together with
[`HodgeTheoryOfAFixedPart`](../HodgeTheoryOfAFixedPart/README.md), which holds the pairing on
real divisors at finite scale. [`SelectiveArithmetic`](../SelectiveArithmetic/README.md) is its
test bench.

Every theorem named here is proved in Lean without hypothesis. "corpus" marks a theorem of
another folder, **[C]** published mathematics that is not in the corpus, **open** a statement
that is not proved.

## 1. Aim

Both proofs of the Riemann hypothesis for a curve `C/𝔽_q` take place on the surface `C × C`.
Weil uses the Hodge index theorem for the graphs of the Frobenius; Stepanov uses a section of
small degree that vanishes to high order where a graph meets the diagonal. `ζ` is rigid: no
family of twists or covers replaces the base, and `ζ` is the fixed part of every arithmetic
family. So the object has to be a product of `Spec ℤ` with itself.

**The aim** is a geometry in which `Spec ℤ` has a product with itself and the inequality of
Castelnuovo and Severi on that product is a theorem. It is not a definition of `𝔽₁`.

The object exists and its pairing is computed. **What is missing is one property of the square
that is an inequality**: a positive class, a path, a height or a count whose positivity is not
the statement to be proved. Every structure found so far is an identity (the product formula,
the complementary carry, the payment of the contacts) or a receiver, with one exception of
bounded range: the length of the tree of `2` (§7, construction I).

## 2. The picture

### 2.1 The square

Three rings, each mapping to the next: `Spec 𝒢 → Spec T → S_q`.

- **The arithmetic square** `𝒢 = W(ℤ)` in ghost coordinates: integer sequences `(x_n)` with
  `p^{v_p(n)+1} ∣ x_{pn} − x_n`. It is the cofree ring with commuting Frobenius lifts over `ℤ`.
  Its components `x ↦ x_n` are the Frobenius graphs `Γ_n`; the diagonal is `Γ_1`. Two graphs
  are glued exactly along `Spec ℤ/J(m, n)`, and `Γ_1 ∩ Γ_n` has order `e^{Λ(n)}`. The square is
  a curve, not a surface: the first `N` graphs form a lattice of index `N!`, and `log N!` is
  the number of zeros of `ζ` below the height `2πN` up to `O(log N)`.
- **The Adams ring** `T`: the constants (Teichmüller points), the integer Dirichlet
  polynomials. It sees an integer-norm system only through its norms.
- **The toric surface of a base** `S_q = Spec ℤ[Y]` with the sections `Y = qⁿ`: a diagonal with
  a normal direction and a bilinear count of sections, and no primitive part.

No one of the three carries contacts, jets and a diagonal together, and no object of finite
type carries the contacts: the fibre of the square over every prime is infinite. Two subrings
of `𝒢` carry the contacts with an exact count of sections: the **orbit ring with a base**
`𝒪_q` (at the level `M` it is `τ(M)` lines; with the weight lines of the pole plane and of the
jets it is one ring `𝒮_q`, stable under the shifts) and the **planar square** (unit masses,
every contact paid). On both the count returns an identity: the product formula on the tower,
an equality of ideals on the planar square.

### 2.2 The pairing

A **degree point** is the integer `n` at the position `log n` with the mass `1/n`; all of them
form the **comb of the integers**. In the unitary normalization

  `Γ_m · Γ_{mk} / √(m · mk) = Λ(k)/√k + ω(log k)`:

the **contact** of the two graphs in the square, plus the **jet**, the Lévy density of Weil's
archimedean form. The jets are weights `−2j` of the same Frobenius on the same sequence ring;
the pole plane is the weights `0, 1`.

A **packet** `f ∈ C²_c` of the logarithmic coordinate puts `f(log(n/N))` on the point `n`. As
`N → ∞`,

  jets + contacts − `Σ (f_n²/n)·log(n/2π)`  →  `2 d₁ d₂ − Z(f)`,

with the degrees `d₁ = ∫ f e^{−u/2}`, `d₂ = ∫ f e^{u/2}` and the sum over the zeros
`Z(f) = Σ_ρ m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)`. The **counterterm** `log(n/2π)` is the logarithm of
the density of the comb over `2π`. Its divergent part `log n = Σ_p v_p(n) log p` is the
logarithm of the gluing index of `Γ_n` and the sum of the Busemann functions of the trees of
the primes: the finite places supply the counterterm of the archimedean diagonal. The jets
carry the mean of the zero sum, the contacts its fluctuation.

### 2.3 The one inequality

**Bézout on the comb**: `D·D ≤ 2 d₁ d₂` for the limit of the pairing on every packet. This is
the inequality of Castelnuovo and Severi on the degree points, and it is the Riemann
hypothesis. Proved without hypothesis:

- it holds on every packet of length at most `181/250`, with the margin `∫f²/5000`; this length
  exceeds `log 2`, so the contact of `Γ_m` and `Γ_{2m}` enters;
- it holds on every packet up to the defect `Σ_ρ m_ρ |f̂(γ_ρ) − f̂(conj γ_ρ)|²/4`, to which a
  zero on the line contributes nothing;
- it can fail only in finite rank: on every finite family of packets the defect
  `2 d₁ d₂ − D·D` has at most as many negative squares as `ζ` has zeros to the right of the
  line;
- it is decided by the contacts: with the contact at the prime `2` reversed it fails inside
  the proved range;
- the count of sections does not give it: on every ring of sections the forced zeros on a
  graph are the powers of its contact with the diagonal.

### 2.4 What is forced

On the comb of the integers Bézout fixes every free parameter of the pairing.

| Datum | Statement | Lean |
|---|---|---|
| Contact weights | Bézout for a weight `w` iff RH and `w = Λ` | `combBezout_iff` |
| Constant | with the counterterm `log(n/2π) − c`: iff `c ≤ 0` and RH | `combBezoutShift_iff` |
| Scale | with the contacts `(1 + ε)Λ + δ`: fails for every constant unless `ε = 0` | `combBezoutScaled_iff` |
| Tree lengths | a tree of `p` glued with the edge length `ℓ`: iff RH and `ℓ = log p` | `treeBezout_iff` |
| Exchange law | contacts `Λ + δ`, counterterm `log(n/2π) + c`: iff RH and `sup P_δ ≤ c` | `combBezoutWith_iff` |
| Conductor | for a quadratic ring a smaller conductor in the counterterm fails | `exists_packet_quadraticForm_pos` |

At a finite aperture the admissible weights are a convex body, the window cone, with `Λ`
inside it wherever `Λ` has a margin; the body shrinks to the point `Λ` as the aperture grows
(`combBezoutAt_iff_mem_windowCone`).

### 2.5 What `Spec ℤ` over `𝔽₁` is like

Each clause is a reading of theorems of §6.

1. A curve of infinite genus with a genus function: `g(n) = 1 + (n/2) log(n/2π)` at the degree
   point `n`, negative exactly at `n = 2, 3`.
2. Its Frobenius is a monoid at the finite places and a flow at infinity. No map is a Frobenius
   at two primes: order `m` on a set `S` of primes costs `m·θ(S)`.
3. Its square is of infinite type. The prime part of an intersection number is a contact
   order, the archimedean part a jet (a Newtonian multipole on an axis of `ℝ³`), the diagonal
   the density of a comb.
4. Passing from `𝔽_p[T]` to `ℤ` is a deformation by the carry, a cocycle that is not a
   coboundary: `𝔽₁` does not remove it.
5. Extensions of the base are covers with ramification, not extensions of constants: the
   conductors are the ramification term of the genus, and `ζ` is the fixed part of every
   family of covers, of weight one over the degree.

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Arithmetic square | `ghostRing`, `IsGhost` | `𝒢`: sequences with `p^{v_p(n)+1} ∣ x_{pn} − x_n` |
| Frobenius, Verschiebung | `frobenius`, `verschiebung` | `(F_k x)_n = x_{kn}`; `(V_k x)_n = k·x_{n/k}` on multiples of `k` |
| Graph, contact ideal | `ghostComponent`, `graphIdeal` | `Γ_n`; `J(m, n)` generated by `x_m − x_n` |
| Orbit, necklace coordinates | `orbit`, `necklace` | `e_d = V_d 1`; `x_n = Σ_{d ∣ n} d·b_d` |
| Constants, `p`-derivation | `teichmuller`, `delta` | `[a]_n = aⁿ`; `δ_p x = (F_p x − x^p)/p` |
| Weights, jets | `weight`, `tau`, `jetKernel`, `levyKernel` | `χ_z = (n^z)_n`; `½(1/\|m−n\| + 1/(m+n))`; the same over `√(mn)` |
| Tower and its weight lines | `orbitBaseRing`, `towerWeightRing` | `𝒪_q`; the real algebra `𝒮_q` generated by `𝒪_q`, `χ_1`, `χ_{−2}` |
| Paying ring, planar square | `primeCoord`, `payingRing`, `planarSquare` | `y_p = Σ_j e_{p^j}`; `ℤ[y_p]`; sections that are polynomials in the node on every chain |
| Carries | `wittCarry`, `digitCarry`, `carryTerm` | defects of additivity; the `Λ`-weighted carries of `N + N` |
| Packet on the comb | `degreeSample`, `degreeForm`, `weightedContact` | `f(log(n/N))`; jets minus counterterm; contacts with weights `w(k)/√k` |
| Autocorrelation | `packetAutocorr` | `h_f(x) = ∫ f(u) f(u + x) du` |
| Zero sum, defect | `zeroSum`, `offLineDefect` | `Z(f)`; `Σ_ρ m_ρ\|f̂(γ_ρ) − f̂(conj γ_ρ)\|²/4` |
| Bézout and its variants | `CombBezout`, `CombBezoutAt`, `CombBezoutShift`, `CombBezoutWith`, `CombBezoutScaled` | on all packets; at an aperture; with another constant; with a pair `(δ, c)`; with scaled contacts |
| Tree with an edge length | `treeDeviation`, `busemannMass`, `TreeBezout`, `TreeBezoutAt`, `treeGenerator` | contacts `ℓ` along the chains of `p`; `v_p(n)` against the masses; `E_p(f) = ∫f²/(p−1) − (2/√p)·h_f(log p)` |
| Other combs | `combForm`, `squareForm`, `multiplePairing`, `baseCombRate` | `e^{ℤ/N}`; the squares; the multiples of `g`; `q^ℤ` |
| Genus | `genus` | `1 + (n/2)(d log(n/2π) + R)` on a ring of degree `d` with conductor product `e^R` |
| Square of a number ring | `idealGhostRing`, `ringWeight`, `ringForm`, `ringZeroSum`, `ringConfig` | congruences over ideals; contacts `Λ(1 + Σ_i Re χ_i)`; the pairing; the zeros of `ζ Π L(s, χ_i)` |
| Twisted part | `twistWeight`, `twistedForm`, `twistedZeroSum` | contacts `Λ Re χ`, counterterm `log(qn/2π)`, no pole plane |
| Functions on two graphs | `pairRing`, `graphPair` | pairs of integers congruent modulo `J(m, n)` |

## 4. Language

- **Contact order** of two graphs at `p`: the exponent of `p` in `J(m, n)`. **Chain** at `p`:
  the graphs `Γ_{m p^l}`, `p ∤ m`. **Node**: the value `p + ⋯ + p^l` of `y_p` on a graph of a
  chain. **Paid contact**: a section that vanishes on a set of graphs is at least as large on
  another graph as its contacts with the set.
- **Weight** `z`: `F_n` acts by `n^z`. **Transposition** `F ↔ V` is `z ↦ 1 − z`, the functional
  equation.
- **Comb**: a set of degree points with masses. **Counterterm** of a comb: the logarithm of its
  density over `2π`.
- **Packet**: `f ∈ C²_c` sampled on a comb at a scale. **Degrees** `d₁, d₂`; **length**: the
  length of an interval containing the support; **aperture**: half the length. **Packet of
  degree zero**: `d₁ = d₂ = 0`. **Step packet**: constant on the blocks of a window.
- **Bézout at an aperture**: the inequality on the packets of that aperture. **Margin**: `c₀`
  with `D·D ≤ 2 d₁ d₂ − c₀ ∫f²` there.
- **Index** of a square: the largest number of negative squares of `2 d₁ d₂ − D·D` on a finite
  family of tests.
- **Pair** `(δ, c)`: a deviation of the contacts and a constant added to the counterterm.
  **Symbol** `P_δ(τ) = Σ 2 δ(n) n^{−1/2} cos(τ log n)`; its supremum is the **price** of `δ`.
- **Edge length** of a glued tree: the weight of its contacts along a chain; `log p` on the
  square. **Generator**: the derivative of the functional in the edge length. **Threshold
  length** `ℓ*(L)`: the least edge length of the tree of `2` with Bézout on the packets of
  length `L`.
- **Genus** of a degree point: one plus `n/2` times the coefficient of the mass at `n`.
  **Ramification term**: the sum of the logarithms of the conductors.
- **Twisted part**: the part of the pairing of a ring with the contacts `Λ Re χ`. **Trivial
  aperture** of a conductor `q`: `log log q + o(1)`, up to which the sizes of the contacts
  decide the sign.

## 5. Mechanisms

1. **Dwork congruences are the gluing.** `Γ_n` carries `Σ_{k ∣ n} Λ(k) = log n` conditions, the
   density of zeros at the height `2πn`.
2. **`F V = n`.** `F_{gn} V_{gm} = g·V_m F_n` for coprime `m, n`: a common factor of two degrees
   is a multiplicity. On a weight line `F_n = n^z` forces `V_n = n^{1−z}`.
3. **Support separates the two fibres.** A Verschiebung with the projection formula lives on
   multiples; the one of the jets is perfect. They share the Frobenius, and no duality glues
   them.
4. **Restriction to a graph.** An ideal power restricts to the power of the restriction, so the
   forced zeros of `I^ℓ` on `Γ_n` are `J(1, n)^ℓ`, attained: Stepanov's inequality is the
   product formula.
5. **Lévy–Khintchine on a comb.** `C_m C_n = ½(C_m² + C_n²) − ½(C_m − C_n)²` turns the jets into
   rows on the masses minus half a Dirichlet form; the row minus `log(density/2π)` is Weil's
   constant.
6. **A contact carries one mass.** `Σ_m f_m f_{mk}/m` is a Riemann sum of `f(u) f(u + log k)`:
   pairs in divisibility give the autocorrelation at the logarithms of the integers.
7. **Translation.** `Z(f)` does not change when a packet is translated, so positivity of Weil's
   functional on tests supported in `[−a, a]` is Bézout on the packets of length `2a`, wherever
   they sit.
8. **`Re(a·conj b) ≥ −|a − b|²/4`** on each summand of `Z(f)`; on the line `a = b`.
9. **The signature law.** The Gram matrix of the pole plane and of packets has `1 + κ` positive
   squares, `κ` the number of negative squares of Weil's Gram matrix; on the kernel of the
   evaluations at the zeros to the right of the line Weil's form is a sum of squares.
10. **Concentration in the radical.** Tests divisible by Riemann's kernel have a negligible zero
    sum and concentrate at any frequency. On them the functional of a pair `(δ, c)` is the
    energy of `c − P_δ`, so every wrong datum is refuted on a packet of degree zero.
11. **The pole against two distant bumps.** For `g + s·g(· − T)` the pole term grows like
    `e^{T/2}` and the zero sum is `o(e^{T/2})` (every zero has `|Im γ| < ½`): an uncancelled
    pole term decides the sign.
12. **The mean of a valuation against a first contact.** `v_p(n)` has the mean `1/(p − 1)`
    against the masses of a packet; at a displacement of half its length the autocorrelation
    is at most half the mass, so the first contact of `p` is at most `∫f²/√p`. The difference
    is positive for `p = 2` only.
13. **An affine family with a positive generator** is nonnegative from a threshold on and has
    one point of degeneration.
14. **A number ring on the comb of the integers.** Counted by norms, the ideals have the
    contacts `Λ(1 + Σ Re χ_i)`. Each twisted part brings one copy of the jets and `log q_i`
    times the mass (Riemann–Hurwitz), has no pole plane, and the forms of a family add with
    the multiplicities of common zeros added.
15. **A chain lies on a line.** In the coordinates `y_p` the graphs of a chain differ in `Y_p`
    alone, at the nodes; a polynomial vanishing at some nodes is divisible at another by the
    product of the differences, which is every contact of the chain.
16. **The carry.** The Witt carry is the digit carry plus the coboundary of the Fermat
    quotient; among the `p` additions of `1` one carries, so the cocycle is not a coboundary;
    by Stirling the carry term and the window count of `N + N` are complementary.
17. **Two graphs are an order of rank two.** Multiplication by a section `(a, b)` has the
    determinant `a b` in lattice coordinates: the count does not see the contact.
18. **Pigeonhole on a fibre.** Graphs of distinct degrees prime to `p` are distinct points of
    the fibre over `p`; a ring with finitely many `𝔽_p`-points identifies two of them.

## 6. Pillar theorems

| Area | Theorem | Lean |
|---|---|---|
| The square | necklace decomposition; cofreeness; `F V = n` with the gcd twist | `isGhost_iff_exists_necklace`, `ghostLift_unique`, `frobenius_verschiebung_of_coprime` |
| | `log #(ℤ/J(1, n)) = Λ(n)`; contact orders; two graphs meet at one prime at most | `log_card_quotient_graphIdeal_one`, `graphIdeal_mul_prime_pow`, `graphIdeal_eq_top_or` |
| | gluing index `N!`; it counts the zeros up to the remainder `S`, which is unbounded | `det_necklaceMatrix`, `tendsto_log_factorial_sub_xiZeroCount_add_rvmRemainder`, `exists_lt_abs_gluingCount_sub_xiZeroCount` |
| | no object of finite type carries the contacts | `infinite_ringHom_ghostRing_zmod`, `FrobeniusLifts.exists_contact_not_in_square` |
| Sections | forced zeros on a graph are the powers of its contact with the diagonal, on every ring with two `ℤ`-points | `map_ker_pow_eq_contact_pow` |
| | the tower: contacts of the square, exact count on independent lines, product formula; not of finite type; one ring with the pole plane and the jets | `span_orbitBaseRing_sub_eq_graphIdeal`, `card_image_orbitLatticeMap`, `shift_mem_towerWeightRing` |
| Paid contacts | the planar square has the contact ideals of the square, and the values of the sections vanishing on a set of graphs are the product of the contact ideals | `planarContact_eq_graphIdeal`, `planarValues_eq_prod` |
| The fibre at infinity | the jets are the Lévy measure of Weil's archimedean form; no Witt Verschiebung carries them | `levyKernel_eq_archLevyDensity`, `not_exists_projection_verschiebung_frobeniusIntersection` |
| | the unitary intersection number is contact plus Lévy density | `frobeniusIntersection_div_sqrt` |
| The comb | Weil's archimedean form of a packet is the finite part of the jets with the counterterm `log(density/2π)`: on the integers, on `e^{ℤ/N}`, on the squares, on the multiples of `g` | `tendsto_degreeForm`, `tendsto_combForm`, `tendsto_squareForm`, `tendsto_multiplePairing_sub_density_counterterm` |
| | the counterterm belongs to the comb, not to the point | `not_exists_counterterm_of_two_combs` |
| The pairing | jets + contacts − counterterm `→ 2 d₁ d₂ − Z(f)` | `tendsto_degreeForm_add_contacts`, `tendsto_degreePairing_degrees_sub_zeroSum` |
| | Bézout ⇔ RH | `riemannHypothesis_iff_degreePairing_le_degrees` |
| | Bézout up to the defect of the off-line zeros; on packets of length `≤ 181/250` | `tendsto_degreePairing_le_degrees_add_offLineDefect`, `tendsto_degreePairing_le_degrees_of_width` |
| | the index law: at most `#{Re ρ > ½}` negative squares | `negIndex_defect_packets_le`, `riemannHypothesis_iff_one_positive_square_packets` |
| | no gap on packets of degree zero | `exists_primitive_packet_zeroSum_lt` |
| Forced data | weights, constant, scale, tree lengths, exchange law | §2.4 |
| | a reversed contact at `2` fails | `exists_packet_degreePairing_gt_of_flippedContact` |
| The tree of `2` | on packets of length `≤ log 4` the generator is `≥ (1 − 1/√2)∫f²`; Bézout is monotone in the length, holds for long trees, and exactly from a threshold on | `treeGenerator_two_ge`, `treeBezoutAt_two_mono`, `exists_treeBezoutAt_two`, `exists_treeThreshold_two` |
| | a margin of the square at a length is a threshold below `log 2` | `exists_margin_iff_exists_treeBezoutAt_two_lt` |
| | at an odd prime the generator is negative on two bumps and long trees fail | `exists_packet_treeGenerator_neg`, `exists_not_treeBezoutAt_of_three_le` |
| Carries | the Witt carry is the digit carry up to the Fermat quotient; the carry is a cocycle and not a coboundary; carry and window count are complementary | `prime_dvd_wittCarry_sub`, `digitCarry_not_coboundary`, `tendsto_carryDefect_add_windowDefect` |
| Counts | on two graphs a section `x` has `\|x_m x_n\|` residues: quadratic on rays, blind to the contact, not a form | `card_quotient_graphPair`, `exists_not_parallelogram_pairRing` |
| Number rings | over a Dedekind domain graphs meet in the prime ideals; an orbit exists iff the ideal is principal | `idealContact_prime_pow`, `exists_idealOrbit_generator_iff` |
| | the pairing of a ring with primitive characters `χ_i` tends to `2 d₁ d₂` minus the zero sum of `ζ Π L(s, χ_i)` | `tendsto_ringForm_add_contact` |
| | Riemann–Hurwitz for the counterterm; the genus | `riemannHurwitz`, `combForm_singleton` |
| | the exact index is the number of distinct zeros to the right of the line; a cover bounds its base | `exists_le_negIndex_ringDefect_iff`, `riemannHypothesis_of_ringDefect` |
| | in a tower the form of `ζ` has weight one over the degree | `tendsto_ringZeroSum_div_degree_sub` |
| Twisted parts | nonpositive up to the trivial aperture, uniformly in the character | `exists_uniform_trivial_conductor_aperture` |
| | a real zero is one square of explicit depth and repels the others | `re_Wsummand_real_zero_pair_ge_neg_two_pairEnergy`, `exists_twistedComb_square_margin` |
| Integer-norm systems | the square sees a system through its norms; on its own comb the system of the squares fails Bézout | `ghostLift_adams_X_eq_of_eq`, `exists_packet_squarePairing_gt` |

In the continuation and the corpus: the normal form at finite scale, block averages, the comb
`q^ℤ` of a curve as a Toeplitz form whose sign is purity (`HodgeTheoryOfAFixedPart`); the
contacts of a prime as chain squares minus the diagonal and the jets as even Newtonian
multipoles (`HodgeTheoryOfAFixedPart`); the cost `m·θ(S)` of order `m` at the primes of `S`
(`SignFreePurityMechanisms`).

## 7. Constructions

Each construction asks for a property that is an inequality and has a kill condition.

| | Deliverable | Kill condition | State |
|---|---|---|---|
| I | a Lefschetz operator or a path on the comb lattice: the inequality at a base point and a transport that is not RH | every candidate has transport equivalent to RH | dilation, overlap flow, coupling Laplacian: equivalent to RH (corpus). The length of the tree of `2` is a monotone path on packets shorter than `log 4`. Odd trees fail |
| II | the archimedean fibre glued to the trees so that the glued form is the comb form | every gluing is the pairing itself or fails | invariant gluings have a constant diagonal; along the comb every free parameter is forced (§2.4) |
| III | Stepanov on the planar square: a small section vanishing on a window | the forced value is the product of the contact ideals and is attained | closed: `planarValues_eq_prod` |
| IV | the index law for the squares of a tower | the form of `ζ` has weight `1/[K:ℚ]` in the limit | closed: `tendsto_ringZeroSum_div_degree_sub` |
| V | Bézout for an integer-norm system on its own comb | the jets of the comb are not those of the system | closed for the squares: `exists_packet_squarePairing_gt` |
| VI | natural numbers on the rays `Γ_1 + Γ_p` with a quadratic Tate limit | no definition without the form | the count of the object is the split norm; a count with the pairing as limit is open |

**The path at `2`.** A tree of `p` glued with the edge length `ℓ` has the contacts `ℓ` along
the chains of `p` and the counterterm `log(n/2π) − (log p − ℓ) v_p(n)`. On packets of length at
most `2 log p` the functional is affine in `ℓ`: `Z(f) + (ℓ − log p)·E_p(f)`. For `p = 2` the
generator `E₂` is a positive form, so Bézout is monotone in `ℓ`, holds for long trees without
hypothesis, and holds exactly for `ℓ ≥ ℓ*(L)`. Bézout for the square at the length `L` is the
statement `ℓ*(L) ≤ log 2`; it is proved for `L ≤ 181/250`. The path ends at `log 4`, where the
second point of a chain is seen, and has no analogue at an odd prime, where the first contact
`∫f²/√p` exceeds the mean `∫f²/(p − 1)` of the Busemann function.

The constructions that fixed the object (Frobenius lifts, carries, the surface, the
archimedean fibre, a second dimension, number rings, curves) are closed; their survivors are
the pillars of §6.

## 8. Criteria

A construction is read against twelve criteria; the pairing of the degree points meets each.

| # | Criterion | Reading |
|---|---|---|
| C1 | reproduces Weil and Stepanov for curves | point counts are effective elements; on the comb `q^ℤ` the pairing is a Toeplitz form whose sign is purity |
| C2 | counts alone are not enough | the golden datum is effective, has the functional equation, and is not pure |
| C3 | uses the functional equation | every weight but `Λ` fails; the Liouville twist fails at the first rung |
| C4 | uses the Euler product | a reversed contact fails |
| C5 | sees the exact normalization | `Λ(k)/√k`, the constant `2π`, the scale, the conductor are forced |
| C6 | infinite type | a finite fibre forces a contact that is not Weil's |
| C7 | the diagonal is the density of a comb | every other counterterm leaves a term of the size of the mass |
| C8 | positivity is derived, and not from a section count | on the tower and on the planar square the count is an identity |
| C9 | selective only where a contact enters; no margin | below the first contact every weight passes; on packets of degree zero there is no gap |
| C10 | on a number ring it gives the index of each character, or uses the pole plane | the twisted parts have no pole plane and separate exact indices |
| C11 | below the trivial aperture it proves nothing that the dominated box does not have | up to `log log q − o(1)` every system with contacts bounded by `Λ` is positive |
| C12 | at finite scale it is a statement on block-constant divisors | on divisors with vanishing block sums the inequality holds; block averages decide (continuation) |

## 9. Questions, order of work, decisive test

| # | Question | State |
|---|---|---|
| 1 | Bézout from a property of the object; a height or a path | RH. Known end points of a path: long trees of `2` at length `≤ log 4`; short windows; a large conductor mass (test bench); curves. Known rigidity: weights, constant, scale and the lengths of the odd trees admit no deformation |
| 2 | the block-constant form at every `K, R`; its limit matrices; the converse | block averages decide and a lower bound at arbitrarily large block sizes gives RH (continuation). Open: the limit matrices on step packets, and the inequality at finite scale from RH |
| 3 | Hecke characters, ideals as degree points, one ring that is not abelian | abelian rings: pairing, genus, exact index. Open: the explicit formula of a Hecke `L`-function; the corpus has the completed functional equation (`HeckeLFunctions`) |
| 4 | a count with the pairing as its limit | RH iff a count with values in `ℕ` has the integer probes as Tate limit (corpus). The count of the object is the split norm. No construction |
| 5 | the Li ladder as comb forms of tails | first rung: the flat tail has the form `2 + γ − log 4π` per degree point (continuation). Higher rungs open |
| 6 | a path at an odd prime, or its impossibility | the tree length fails at every odd prime. Other families: open |

**Order of work.** The limit matrices of the block-constant form (question 2); a path at an
odd prime (question 6); Hecke characters and one ring that is not abelian (question 3); a
count (question 4).

**The decisive test.** A construction whose Bézout holds for an integer-norm system with an
off-line pair, for the Liouville twist at the first rung of the conductor ladder, or for a
wrong constant, is wrong. The pairing of the degree points passes all three without
hypothesis. The test for a wrong constant is meant with the contacts fixed: wrong contacts
with a larger counterterm pass, under RH, from the supremum of their symbol on.

## 10. Traps

| Trap | Truth |
|---|---|
| The square is a surface | it is a curve, the union of the Frobenius graphs; and not the trace of a regular surface: the gluing at `2` is too loose |
| The point count is a cardinality | it is the logarithm of the order of a fixed scheme plus a trace; `Λ` is not a trace of any order |
| High multiplicity can be cheap | first order at every prime is one condition; every further order is an independent condition at each prime |
| More sections give a count that gives the sign | the forced zeros on a graph are attained; Stepanov's inequality is the product formula |
| The functional equation exchanges primes and Gamma factor | it is `F ↔ V` and preserves each |
| One Verschiebung glues the archimedean fibre | Witt's is supported on multiples, the jets' is perfect |
| Inverting the Frobenius makes the square translation invariant | it makes every graph equal to the diagonal |
| The diagonal entry is a number attached to the degree point | it is attached to the comb: `log(density/2π)` |
| Leaving the diagonal out is a finite part | it leaves a term of the size of the mass times `log N` |
| A surface of finite type can carry the contacts | its fibres are finite; two graphs of degree prime to `p` then meet at `p` |
| A contact pairs two degree points like a jet | a jet is a density on pairs and carries both masses; a contact carries one |
| The inequality is a property of the shape of the pairing | it holds with the contact at `2` and fails with its negative |
| Short packets say nothing on the primes | the proved length `181/250` exceeds `log 2` |
| The inequality has slack that an estimate could use | a bound `D·D ≤ 2 d₁ d₂ + c ∫f²` for all packets is the inequality itself |
| The constant `2π` is a normalization | it is the threshold of the inequality |
| A wrong contact is refuted whatever the constant | with a larger counterterm it passes from the supremum of its symbol on; a common factor on all contacts is refuted for every constant |
| At a finite aperture Bézout singles out `Λ` | it holds for a convex body of weights; only the limit of the apertures is the point `Λ` |
| A deformation with a positive generator and a base point proves the inequality | it gives a threshold; the inequality is a statement about the threshold at one length |
| The length of a tree is a monotone parameter | only for `p = 2` and only while the point `4` of a chain is not seen |
| A count with quadratic growth gives the pairing | the count on two graphs is `\|x_m x_n\|`, the same for every contact, and not a quadratic form |
| A number ring needs its own comb | counted by norms its ideals sit on the comb of the integers; the discriminant is a density, the ramification term of the genus |
| A ring can satisfy the inequality while `ℤ` does not | negative squares of the square of `ℤ` are negative squares of every ring over it |
| A tower of covers replaces the extension of constants | per degree the form of `ζ` has the weight `1/[K:ℚ]` |
| The index of a ring is the sum of the indices of its characters | it is the number of distinct zeros; a shared zero is one negative square |
| An integer-norm system passes on its own comb when its zeros lie on a line | the system of the squares fails: the comb gives its density, and the jets are those of the norms |
| The sizes of the contacts can pass the trivial aperture | the systems `Λ`, `−Λ` and the Liouville twist with a conductor fail beyond it (test bench) |
| The carries can be removed by another choice of digits | the carry is a cocycle that is not a coboundary |

## 11. Open problems and research topics

**The limit matrices of the block-constant form (question 2).** At finite scale the pairing is
one matrix on the real divisors of a window. On the divisors that are constant on the `3KR`
blocks of `(RB, (3K+1)RB]`, a lower bound `−η Σσ²` at arbitrarily large block sizes, for every
`K, R, η`, gives RH (continuation). *Open:* the limit of the form on these divisors as a
finite matrix on step packets, with entries the jump forms of flat packets, the overlap
lengths with the weights of the primes below `3K + 1`, and the two pole moments; and the
converse, that RH gives the lower bound at every `K, R`. Each matrix is a finite statement. A
decision would be: RH iff Weil's form is nonnegative on step packets of `3KR` blocks for all
`K, R`.

**A path (questions 1 and 6).** A one-parameter family of squares through that of `ℤ` along
which the index is constant and which ends at a square where the inequality is known; or a
group with a doubling on which the defect is a canonical height. *Proved:* the path at `2` up
to the length `log 4`; no deformation of weights, constant, scale or odd tree lengths. *Open:*
the threshold `ℓ*(L)` for `181/250 < L ≤ log 4`; a family whose generator stays positive when
the second point of a chain is seen; a family at an odd prime, or a proof that none exists in
a stated class; a path that moves the archimedean fibre.

**Hecke characters and a ring that is not abelian (question 3).** Two ideals of one norm are
one point of the comb of norms; the pairings twisted by the characters of the class group are
those of Hecke `L`-functions, and a ring that is not abelian brings its Dedekind zeta function
and Artin `L`-functions. *Open:* the explicit formula of a Hecke `L`-function with its zeros as
a tempered configuration; then the pairing, the genus and the exact index for the ideals of a
class and for one ring that is not abelian. Also open on abelian rings: small conductors on
short packets, the exact index on real packets, the units of a real quadratic ring.

**A count (question 4).** Natural numbers on the rays of `Γ_1 + Γ_p`, defined without the form,
whose Tate limit is the pairing. *Proved:* the count on two graphs is the split norm; on the
tower and on the planar square the counts are exact and give identities. *Open:* a count on
three or more graphs; a count of sections in an archimedean box on the ring of two graphs,
where the contact is the index of the order in `ℤ × ℤ`. A decision would be a count whose
second-order term is the logarithm of that index with the sign of the pairing.

**The Li ladder (question 5).** The comb form of the flat tail is twice the first Li
coefficient [C]. *Open:* the higher coefficients as comb forms of tails.

**Combs.** *Open:* the comb of the `a`-th powers for real `a > 0`; combs with a regularly
varying density; combs without a density (the integers prime to `3`); a system with a repeated
norm.

**The planar square.** *Open:* what its gluing index counts; an invariant that selects the
nodes; a metric whose pairing is the jets (on the projective line none exists, corpus).

**The exceptional square.** For a real primitive character of conductor `q`, the sign of the
twisted part at the apertures `log log q + C` is the generalized Riemann hypothesis of
`L(s, χ)`; proved up to the trivial aperture by the sizes of the contacts alone. Beyond it a
proof has to use the signs of `χ` at the primes below `(log q)²`; this is the Landau–Siegel
problem.

**Bézout for all packets** is the Riemann hypothesis. Nothing in this folder proves it or
claims to.

## 12. Context

| Programme | Interface |
|---|---|
| HodgeTheoryOfAFixedPart | second half of the programme: the normal form on real divisors, block averages, short windows, the comb of a curve, chain squares, Newtonian multipoles |
| SelectiveArithmetic | test bench: weight systems with a conductor, the dominated box, the trivial aperture, the Liouville twist |
| RHTower | the explicit formula, Weil's functional and its symbol form, the uniqueness of `Λ` in the Weil cone, radical tests, the zero count |
| ArithmeticCastelnuovoSeveri | the inequality on the scaling surface; the exact index law of a tempered configuration; the golden datum |
| CriticalHardyTheoryOfTheWindowCone | the window cone of weights positive at an aperture |
| SelectivePositivityAndThresholdLaws | the certificate of positivity at the aperture `181/500` |
| HodgeTheoryWithoutVarieties | the Kähler package of the divisibility complex; hard Lefschetz along the overlap flow as RH |
| CountingHolography | a count with the integer probes as Tate limit exists iff RH |
| SignFreePurityMechanisms | `δ_p` on `ℤ`; the cost `m·θ(S)` |
| HeckeLFunctions | ray class characters, their `L`-functions and the completed functional equation |
| SurfaceOfSpecZ, HyperbolicArakelovTheory | Weil's pairing of the Frobenius graphs; the coupled critical kernel of the adelic carrier |

AGZ supplies the square with its contacts and gluing index, the comb calculus of finite parts,
the pairing of the degree points with its zero sum and its index, and the forced data. Its
open statement, Bézout on the comb, is the Hodge index of `ArithmeticCastelnuovoSeveri` and
the positivity of Weil's functional in `RHTower`; what AGZ adds is the object on which it is an
intersection inequality, the proof that the count on that object does not give it, and the
proof that it is decided by the contacts and by the comb.

## 13. Contributions

A contribution

- is unconditional: no hypothesis, no axiom, nothing assumed for `ζ`;
- names what it addresses: a question of §9, a construction of §7 with its kill condition, a
  criterion, or a topic of §11;
- states its objects in the language of §3–§4: which comb, which contacts, which jets, which
  counterterm;
- supplies a step of Weil's or of Stepanov's argument on the object, or proves with its exact
  price that the step is absent;
- passes the decisive test when it concerns the sign, and says where an argument for Bézout
  fails for a weight other than `Λ`, for a reversed contact and for a wrong constant.

Not contributions: finite truncations with no limit; better constants in a proved bound that
open no new length; a restatement of an equivalence with the Riemann hypothesis.
