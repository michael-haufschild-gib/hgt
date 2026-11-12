# Absolute Geometry of Spec ℤ (AGZ)

Namespace `GaloisForLFunctions.AbsoluteGeometryOfSpecZ`; umbrella `AbsoluteGeometryOfSpecZ.lean`.
Specification: §2.14 of
[the review-1211 summary](../../../docs/reports/review-1211/obstacles-summary.md). Paper proofs:
`docs/drafts/pipeline/3-formalized/agz-absolute-geometry-of-spec-z.md`.

The programme is this folder together with
[`HodgeTheoryOfAFixedPart`](../HodgeTheoryOfAFixedPart/README.md), which holds the pairing on
real divisors at finite scale and the index of the finite comb. Its test benches are
[`SelectiveArithmetic`](../SelectiveArithmetic/README.md) (weight systems with a conductor),
[`FloorFreeArithmetic`](../FloorFreeArithmetic/README.md) (finite layers, certificates) and
[`WorldsOfTheZeroConfiguration`](../WorldsOfTheZeroConfiguration/README.md) (models over the
rational primes: edits with a finite layer, fakes).

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
the complementary carry, the payment of the contacts) or a receiver. Two families of squares
through that of `ℤ` are monotone with a base point that needs no hypothesis: the length of the
tree of `2`, and at every prime a contact paid at its price (§7, construction I). On both the
square of `ℤ` is the hardest member.

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
  graph are the powers of its contact with the diagonal;
- it is a statement about finite matrices: it holds iff Weil's form is nonnegative on step
  packets, and iff at every large scale the form on the comb is at least `−η Σ c_n²` on all
  real divisors of a window. The matrices are explicit (§2.6), and the first two with contacts
  are positive with a margin: on the three unit blocks of `(1, 4]` and on the six of `(1, 7]`.

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
3. Its square is of infinite type and **rigid**. The prime part of an intersection number is a
   contact order, the archimedean part a jet (a Newtonian multipole on an axis of `ℝ³`), the
   diagonal the density of a comb. The square is not a member of a family: constant, contacts,
   tree lengths and prices are forced, and every path through it is the Riemann hypothesis at
   each parameter.
4. Its Néron–Severi lattice is the same for every number ring up to the density of the comb.
   The index is the number of distinct zeros to the right of the line, for each Hecke character
   and for the Artin character of degree two of the cube roots of two. For a virtual character,
   a quotient of `L`-functions, it counts zeros and poles: every point right of the line with
   net multiplicity not zero, and every pole on the line. At finite scale the lattice is a
   weighted graph with a potential: the blocks of a window, joined by the jets and by the floor
   maps. Its Hodge index is a count of bound states: RH says that the well of every window
   holds exactly one (§2.6).
5. Its sections count like a curve, not like a surface: the volume over the gluing index, with
   no quadratic term.
6. Its index is a Morse index of the aperture and a Maslov index with a two-dimensional polar
   shadow: at every energy the negative index of Weil's
   form at an aperture is the sum of the numbers of null modes of the smaller apertures, a
   finite sum (`negativeRank_eq_sum_nullity`). At the energy zero the null modes of all
   apertures together count the zeros to the right of the line. The Riemann hypothesis is the
   statement that the path has no conjugate point. The index is a crossing number in a
   symplectic space: the conormals of the apertures are a path of Lagrangian subspaces that
   does not depend on the primes, the graph of Weil's operator is one fixed Lagrangian, and the
   null modes are their crossings. The same index counts the eigenvalues below the energy: the
   number of null modes met between two points of the (aperture, energy) plane does not depend
   on the monotone path. The poles see a part of the path of dimension two, the polar
   Lagrangian, an even line and an odd line; it meets the charge axis exactly at the charged
   null modes, and a neutral null mode is invisible to it.
7. Its zero width is the growth of one comb, read on one sequence of tails: the power tail of exponent `a`,
   `0 < a < ½`, is `O(N^{σ+ε})` for every `ε > 0` iff no zero has real part above `1 − a + σ`.
8. Passing from `𝔽_p[T]` to `ℤ` is a deformation by the carry, a cocycle that is not a
   coboundary; it keeps the lattice and loses the count. Extensions of the base are covers
   with ramification, not extensions of constants, and `ζ` is the fixed part of every family
   of covers, of weight one over the degree.
9. What distinguishes `ℤ` from its imitations is the exact count and the functional equation
   as an identity, not a count rate: a bounded count error identifies the rational primes, and at every
   exponent above `½` there are systems with integer norms, a count with that power saving,
   and a zero that `ζ` does not have (test bench).

### 2.6 The matrix at finite scale

On the unit blocks `(a, a + 1]`, `a = R, …, R + J − 1`, Weil's form `𝔚_Q` of a step packet is
the quadratic form of the **block matrix**

  `m(a, b) = d(a) + d(b) + δ_{ab} ϱ(a) − J(a, b) − Σ_{k ≤ Q} (Λ(k)/k)·[⌊b/k⌋ = a]`,  `a ≤ b`.

- `d(a) = log((a + 1)/a)`: the degrees; `d ⊗ 1 + 1 ⊗ d` is the pole plane.
- `ϱ(a) = ∫_a^{a+1} log(x/2π) dx + 1 − γ`: the density of the comb, on the diagonal.
- `J(a, b) = ½(D(a + b + 1) + D(b − a))`, `D` the second difference of `n log n`: the jets.
- The contacts are the graphs of the **floor maps** `b ↦ ⌊b/k⌋`, with the weights `Λ(k)/k`:
  the block `b` lies in the `k`-fold dilate of the block `a` iff `⌊b/k⌋ = a`. For a prime `p`
  the maps `b ↦ ⌊b/p^j⌋` are the ancestors in the `p`-ary tree on the integers, so at finite
  scale the tree of `p` is this tree, with the weight `log p / p^j` on the ancestor of order
  `j`.

So the step-packet matrices are the intersection matrices of the blocks under these
correspondences (`packetForm_stepPacket_eq_sum_blockMatrix`). Without the degrees the matrix
is a potential plus the Dirichlet form of a weighted graph: the jets join every pair of blocks
and the floor maps join a block to its images, with positive weights. The degrees add the
product of the two charges of the packet, a hyperbolic plane: Weil's form of the two poles
`s = 0, 1` of the completed zeta function. So the neutral part is the form of a divisor, the
zeros minus the poles; on smooth tests it is the archimedean-minus-prime energy of the corpus
(`markovEnergy`). Its largest number of negative squares on smooth tests is one plus the number
of zeros right of the line: RH holds iff the neutral part has one negative square, the
signature of an intersection form on a surface. This is the one-bound-state law of the corpus
(`riemannHypothesis_iff_not_exists_negDef_markovPlane`, `RHTower`), with the count. The same
index law holds at finite scale: over all windows the block matrices have as many negative
squares as there are zeros right of the line, and their neutral parts one more, the square of
the pole. The two charges of a packet are its pairings with two ideal classes, the block one
and a far dyadic window, which span a hyperbolic plane in the limit. So RH holds iff the
neutral part of the block matrix of every window `(R, R + J]` with `R ≤ J` has exactly one
negative square. Without RH it has exactly one on the windows with `R ≤ J ≤ 53R/50`, at every
block size. On one window the index of the block matrix is bounded by the Morse index of the
aperture path: at most the number of null modes below any aperture wider than half the length
of the window.
On every window of ratio at most `103/50` the matrix is at least `1/5000`, at every block size.
At every ratio it is nonnegative on the thin step packets: those that vanish off the first
blocks above each multiple of the block size, a fraction of the block that depends on the
ratio.
On the blocks `1, 2, 3` with `Q = 4` the matrix is at least `1/20`, on the blocks `1, …, 6`
with `Q = 7` at least `1/100`; the second is not diagonally dominant. On the blocks `2, …, 7`
with `Q = 4`, the window of ratio four on blocks of half the size, it is at least `1/100`; the
least eigenvalue falls from near `0.069` to near `0.03`. The matrices of one
window ratio form a tower: translation by `log m` refines the blocks above `R` into the blocks
above `mR`, so the matrix above `R` is a compression of the matrix above `mR`, and a margin on
the finer blocks is a margin on the coarser ones.
The coarse blocks decide the tower. With `E_Q = 3 + Q/4 + 2ψ(Q) + log 4π` and
`C_Q = 12 + 2Q + 2ψ(Q)`: on a refinement of the blocks above `R` the matrix is at least
`log R − E_Q` on the step functions whose sums over the blocks above `R` vanish; a margin `μ`
above `R` is a margin `μ − ε` on every refinement once `log R ≥ E_Q + C_Q²/ε + μ`. So the
margins of a tower converge at a logarithmic rate, the sign of `𝔚_Q` with a margin on all step
packets of a window is a statement about one matrix, and at every block size the matrices of
ratio at most `Q` have at most `(Q − 1)⌈e^{E_Q}⌉` negative squares.

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
| Weil's form of a bounded packet | `packetForm`, `flatPacket`, `stepPacket` | `𝔚_Q(g)`: pole term, `A(0) h_g(0)`, the jump integral of `h_g`, the contacts up to `Q`; `e^{u/2}` on a window; a combination of flat packets of adjacent windows |
| Divisors on blocks | `windowDivisor`, `nestedCoeff` | `1` on `(A, B]`; the coefficients of a block-constant divisor on nested windows |
| Block matrix | `blockMatrix`, `blockDegree`, `blockDensity`, `blockJet`, `floorContact`, `windowClosed` | the matrix of `𝔚_Q` on step packets and its four parts; the closed form of `𝔚_Q` on a window |
| Aperture path | `negativeRank`, `weilNullity` (corpus), `resonantBelow`, `eigenvaluesBelow` | the negative index and the number of null modes of Weil's form restricted to an aperture, at an energy; the resonant apertures below an aperture; the eigenvalues below an energy |
| Lagrangians of the path | `sympForm`, `weilGraph`, `apertureConormal`, `apertureCrossing` | `ω((x, y), (x′, y′)) = ⟨y, x′⟩ − ⟨x, y′⟩` on `H_b × H_b`; the graph of Weil's operator at `b`; `H_a × H_aᗮ` for `a ≤ b`; the dimension of their crossing |
| Charges | `polarCharge`, `polarLagrangian`, `chargedNullity`, `neutralNullity` | the two pole coefficients of a vector; the pairs (charges, forcing) of the solutions of the forced equation, a Lagrangian plane in `ℂ² × ℂ²`; the dimension of the charges of the null modes; the dimension of the null modes without charge |
| Bézout and its variants | `CombBezout`, `CombBezoutAt`, `CombBezoutShift`, `CombBezoutWith`, `CombBezoutScaled` | on all packets; at an aperture; with another constant; with a pair `(δ, c)`; with scaled contacts |
| Tree with an edge length | `treeDeviation`, `busemannMass`, `TreeBezout`, `TreeBezoutAt`, `treeGenerator` | contacts `ℓ` along the chains of `p`; `v_p(n)` against the masses; `E_p(f) = ∫f²/(p−1) − (2/√p)·h_f(log p)` |
| Contact at its price | `contactAt`, `priceGenerator`, `PriceBezoutAt` | the contact at `n₀` changed by `t`, the counterterm raised by `2\|t\|/√n₀`; `(\|t\|/√n₀)∫(f(u + log n₀) − sgn(t) f(u))²`; Bézout at a length along the path |
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
  family of tests. **Index at an aperture**: the same on tests of that aperture. **Null mode**:
  a test of an aperture that pairs to zero with every test of the aperture. **Resonant** (or
  **conjugate**) **aperture**: one that carries a null mode.
- **Charge** of a vector: its two pole coefficients. A null mode is **charged** if its charge is
  not zero, **neutral** otherwise. **Forcing**: a combination of the two pole profiles on the
  right of the equation of a null mode. **Eigenvalue** at an aperture: an energy with a null
  mode. **Pole-vanishing ground energy** `μ₀(a)`: the floor of Weil's form on the vectors
  without charge (corpus).
- **Block**: the interval `(a, a + 1]`. **Floor map** of `k`: `b ↦ ⌊b/k⌋` on the blocks.
- **Pair** `(δ, c)`: a deviation of the contacts and a constant added to the counterterm.
  **Symbol** `P_δ(τ) = Σ 2 δ(n) n^{−1/2} cos(τ log n)`; its supremum is the **price** of `δ`.
- **Path of the price** at `n₀`: the squares with the contact at `n₀` changed by `t` and the
  counterterm raised by the price `2|t|/√n₀`.
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
19. **The polar identity.** A quadratic form on combinations of nested windows is determined by
    its values on single windows: `q(Σ τ_j v_j) = ½ Σ τ_j τ_l (q(v_j) + q(v_l) − q(v_l − v_j))`,
    and a difference of nested flat packets is the flat packet of the window between their
    ends. It holds for the form on the comb and for its limit, so limits on single windows
    give the limit matrices.
20. **Smoothing does not increase the jump integral.** By Jensen with a weight of integral
    one, `h(0) − h(x)` of a smoothed packet is at most that of the packet, at every `x`; the
    other terms of Weil's form converge. So positivity passes from smooth packets to step
    packets.
21. **A price minus its contact is a square.** `(2/√n₀)(|t| h(0) − t h(log n₀))` is
    `(|t|/√n₀)∫(f(u + log n₀) ∓ f(u))²`, and a packet of length at most `m log n₀` is a sum of
    `m` such differences: the square bounds the mass.
22. **Two lines weigh the zeros.** For an entire function of order one the difference of the
    integrals of `H · E'/E` over `Re s = c` and `Re s = 1 − c` is `2π Σ_ρ H(ρ)`; a functional
    equation folds the two lines into one, and on it `E'/E` is poles, Gamma factors and a
    Dirichlet series. A conjugation makes the zeros a configuration closed under `ρ ↦ 1 − ρ̄`.
    Nothing else of the function is used, so every Hecke `L`-function is covered at once.
23. **Raising the scale differentiates a tail.** On `[1, N]`, `log((N+1)/m) = log(N/m) + η_N`
    with `η_N = log(1 + 1/N)`, and `log^k((N+1)/m)` vanishes at `m = N + 1` for `k ≥ 1`. So the
    form of two logarithmic tails at scale `N + 1` is a binomial combination of the forms at
    scale `N`, exactly; since `N η_N → 1`, its increment tends to
    `k β(k−1, l) + l β(k, l−1)` and Cesàro gives the limit per degree point. On the zeros the
    same recursion is `ρ + (1 − ρ) = 1`. Only the flat tail needs analysis, and it pairs through
    its row: von Mangoldt's formula for `ψ` at the ratio `N/n`.

24. **The dilate of a block is a union of blocks.** The contact of `k` between two windows is
    the overlap `(b/k − a)⁺`; its mixed second difference at integer ends is `−1/k` if
    `⌊b/k⌋ = a` and `0` otherwise. So the contacts of a step packet are the graphs of the
    floor maps, and pole term and jets are mixed second differences of `x log x`.
25. **An interval matrix with a Cholesky certificate.** Each entry of a block matrix is an
    integer combination of `γ`, `log π` and logarithms of primes, enclosed within `10⁻⁴` of a
    decimal; the decimal matrix minus the margin is a sum of squares plus a diagonally
    dominant remainder.
26. **The index at an aperture is attained strictly inside.** The negative index is attained on
    finitely many smooth packets with compact support in the open aperture; they live in a
    smaller aperture with the same form and the same mass. With the jump to the right (the
    nullity) and the logarithmic floor of the ground energy at small apertures, an induction
    on the index gives the law of a Morse index.

27. **A pole is a zero with the sign reversed.** In the coordinates of the zeros, the form of a
    quotient is `⟨T x, y⟩` with `(T x)_τ = s_τ x_{1−τ̄}`, `s = −1` at a pole. Off the line the
    pair `τ, 1 − τ̄` is a hyperbolic plane for either sign: one negative square. On the line a
    zero is a positive square and a pole a negative one. Common zeros cancel before counting.

28. **A compression is a crossing.** For a self-adjoint `T` on `H` and a closed subspace `K`,
    the graph of `T` and the conormal `K × Kᗮ` are Lagrangian in `H × H`, and they meet in the
    `x ∈ K` with `T x ⊥ K`: the null space of the form of `T` on `K`. Weil's operator at a
    larger aperture compresses to Weil's operator at a smaller one, so one graph meets the
    conormals of all smaller apertures in their null modes.

29. **The polar relation.** For a self-adjoint `T = 1 − compact` and a charge map `d` to a
    finite-dimensional space, the pairs `(d ξ, y)` with `T ξ = d† y` form a Lagrangian
    subspace: isotropic by symmetry of `T`, half-dimensional because the range of `T` is the
    orthogonal complement of its kernel. It meets the charge axis in `d(ker T)` and the forcing
    axis in the null vectors of the form of `T` on `ker d`. It sees a null vector only through
    its charge. With a symmetry that exchanges the two charges, an isotropic plane in
    `ℂ² × ℂ²` is the sum of a line of equal pairs and a line of opposite pairs: two pairs of
    one parity `(s, t)`, `(s′, t′)` are isotropic iff `t̄ s′ = s̄ t′`, so they are proportional.

30. **One counting law, two directions.** A count on the line that grows by the jump across
    every point, is constant just below, jumps by exactly the jump just above and vanishes
    somewhere is the sum of the jumps below. In the aperture the jump is the nullity (strict
    interior, compact limit); in the energy as well (a negative form on a finite-dimensional
    space is uniformly negative; extra negative unit vectors have a weak limit that is a null
    mode orthogonal to itself).

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
| Finite scale | on divisors constant on blocks the form on the comb, per block point, tends to Weil's form of the step packet, uniformly in the coefficients; the entries are elementary | `tendsto_combForm_blockFunction_div`, `eventually_abs_combForm_nested_sub_le`, `packetForm_flatPacket_eq` |
| | under RH Weil's form is nonnegative on bounded packets that are not smooth | `packetForm_nonneg_of_riemannHypothesis` |
| | RH ⇔ Weil's form is nonnegative on the step packets of `3KR` blocks, all `K, R` | `riemannHypothesis_iff_forall_packetForm_stepPacket_nonneg` |
| | RH ⇔ at every large scale `2 d₁ d₂ − D·D ≥ −η Σ c_n²` on all real divisors of a window | `riemannHypothesis_iff_eventually_combForm_ge` |
| | the matrix of `𝔚_Q` on step packets is the block matrix of the degrees, the density, the jets and the floor maps | `packetForm_stepPacket_eq_sum_blockMatrix`, `windowClosed_mixed` |
| | the first windows with contacts: `𝔚_4 ≥ (1/20) Σσ_j²` on the three blocks of `(1, 4]`, `𝔚_7 ≥ (1/100) Σσ_j²` on the six blocks of `(1, 7]`, `𝔚_4 ≥ (1/100) Σσ_j²` on the six blocks of `(2, 8]`; on the comb, divisors constant on the three blocks of `(B, 4B]` have form `≥ (1/40) B Σσ_j²` for `B ≥ 300000`, on the six blocks of `(B, 7B]` and of `(2B, 8B]` form `≥ (1/200) B Σσ_j²` for `B ≥ 3000000` | `packetForm_stepPacket_ratioFour_ge`, `packetForm_stepPacket_ratioSeven_ge`, `packetForm_stepPacket_ratioFour_fine_ge`, `combForm_ratioFour_ge`, `combForm_ratioSeven_ge`, `combForm_ratioFour_fine_ge` |
| | the tower of a window: `𝔚_Q` of a step packet above `R` is `𝔚_Q` of its refinement above `mR`; a margin on finer blocks is a margin on coarser blocks | `packetForm_stepPacket_refine`, `sum_blockMatrix_refine`, `margin_of_refined_margin` |
| | on `[1, N]` the form is a quadratic form in the increments of the divisor, with the rows of the flat tails (the remainders of the prime number theorem) as coefficients | `combForm_Icc_eq_sum_increments` |
| | the explicit error: on `J` blocks of `B` points above `RB` the form per block point differs from `𝔚_Q` of the step packet by at most `6(J+1)·(2X + 16(1 + log 2XB) + 2ψ(Q))/B · Σσ_j²`, `X = R + J`; a margin of the matrix gives the sign of the comb at explicit block sizes, and conversely | `abs_combForm_blockFunction_div_sub_le`, `le_combForm_of_packetForm_ge`, `packetForm_ge_of_combForm_ge` |
| Tails | Weil's form of two logarithmic tails per degree point: `𝔚_{[1,N]}(log^k(N/·), log^l(N/·))/N → k! l! Re Σ_ρ ρ^{−k−1}(1−ρ)^{−l−1}` | `tendsto_logTailForm_div_zeroMoment` |
| | the Li ladder: the form of the Laguerre tail `P_n(log(N/m))` per degree point tends to `Re 2λ_n`, without damping or smoothing | `tendsto_combForm_laguerreTail_div` |
| | the row of the flat tail is `1/t − ψ(1/t) − ½ log(1−t²) − log 2π` in the coordinate `t = n/N`; its Mellin transform is `Σ_ρ 1/(ρ(s−ρ))` and its logarithmic moments are `j! Σ_ρ 1/(ρ(1−ρ)^{j+1})` | `mellin_rowProfile`, `rowMoment_eq_tsum` |
| | the scaling recursion: the forms of all logarithmic tails are determined by their pairings with the flat tail | `logTailForm_succ`, `tendsto_logTailForm_div` |
| | power tails `F_a(N)`, the form of `(N/n)^a` on `[1, N]` per degree point, `0 < a < ½`: growth at every rate above `σ` iff no zero has real part above `1 − a + σ`; the tails converge exactly for `a < ½ − w`, `w` the width of the zeros; RH iff every tail converges | `powerCombTailGrowth_iff_zeroHalfPlane`, `powerCombConvergenceRadius_eq_half_sub_zeroWidth`, `riemannHypothesis_iff_all_powerCombTails_converge` |
| The aperture path | at every energy the negative index at an aperture is the sum of the nullities of the resonant apertures below it; the index is attained at a smaller aperture; it vanishes at small apertures | `negativeRank_eq_sum_nullity`, `exists_smaller_aperture_negativeRank_eq`, `exists_aperture_negativeRank_eq_zero` |
| | RH iff no aperture carries a null mode at the energy zero | `riemannHypothesis_iff_forall_weilNullity_zero` |
| | the far end: `ζ` has at least `r` distinct zeros right of the line iff some finite set of apertures carries `r` null modes in total; the index exhausts the zeros | `nat_le_rightZeros_iff_exists_sum_nullity`, `iSup_negativeRank_zero_eq_rightZeros` |
| | the Gram matrix of `𝔚_Q − E` on the flat packets of nested windows in `(x₀, X]` has at most as many negative squares as the path has null modes below any aperture wider than `½ log(X/x₀)` | `negIndex_nestedStepGram_le_sum_nullity` |
| | the index as a crossing number: in `H_b × H_b` the graph of Weil's operator and the conormals of the apertures `a ≤ b` are Lagrangian, the path of conormals is increasing and ends at `H_b × 0`, its crossing with the graph at `a` is the space of null modes at `a`, and the index at `b` is the number of crossings | `mem_weilGraph_iff_forall_sympForm`, `mem_apertureConormal_iff_forall_sympForm`, `finrank_weilGraph_inf_apertureConormal`, `negativeRank_eq_sum_apertureCrossing` |
| | the index in the energy: the number of eigenvalues below `E`, with multiplicity; the ground energy is the lowest eigenvalue | `negativeRank_eq_sum_eigenvalues`, `weilNullity_groundEnergy_pos` |
| | two paths, one index: the null modes met along the apertures up to `b` at the energy `E` are as many as the eigenvalues below `E` at `b`; on a rectangle of apertures and energies the two monotone paths meet equally many null modes | `sum_nullity_apertures_eq_sum_eigenvalues`, `null_modes_along_two_paths` |
| The charge of a null mode | the polar Lagrangian of an aperture is a Lagrangian plane in `ℂ² × ℂ²`; it meets the charge axis in the charges of the null modes and the forcing axis in the null modes of the form on the vectors without charge; nullity = charged nullity + neutral nullity, charged nullity `≤ 2` | `finrank_polarLagrangian`, `polarLagrangian_isotropic`, `mem_nullCharges_iff`, `exists_forcing_iff_constrained_null`, `weilNullity_eq_charged_add_neutral` |
| | a null mode at an energy below `μ₀(a)` is charged; up to `μ₀(a)` the index is at most two; the ground modes are all charged iff `μ(a) < μ₀(a)` | `neutralNullity_eq_zero_of_lt_polarGroundEnergy`, `negativeRank_le_two_of_le_polarGroundEnergy`, `neutralNullity_groundEnergy_eq_zero_iff` |
| | below `μ₀(b)` the index at `b` is the number of crossings of the polar Lagrangian with the charge axis; without hypothesis for `b ≤ ½(log 2 + 1/50)` and `E < 1/20` | `negativeRank_eq_sum_chargedNullity_of_lt_polarGroundEnergy`, `negativeRank_eq_sum_chargedNullity_of_le_primeTwo` |
| | parity: Weil's operator commutes with the reflection of the aperture, which exchanges the two charges; the polar Lagrangian is an even line and an odd line; a charged null mode has a charged null mode of pure parity; a crossing of dimension two is an even and an odd charged null mode at one aperture | `operator_reflection`, `finrank_polarLagrangian_inf_parityPairs`, `exists_pureParity_charged_null_mode`, `exists_even_odd_charged_of_chargedNullity_two` |
| | the nullities are not all even: on a short aperture the null space at the ground energy is a line, and just above that energy the path meets exactly one null mode, of nullity one | `exists_weilNullity_groundEnergy_eq_one`, `exists_single_simple_null_mode` |
| | up to the ground energy the polar Lagrangian is the graph of a positive form on the forcings: every forcing has one charge, their pairing is the maximum of `2 Re⟨y, d u⟩ − ⟨T u, u⟩`, positive, and increasing in the aperture | `exists_mem_polarLagrangian_of_lt_ground`, `forced_variational`, `re_inner_forcing_charge_pos`, `re_inner_forcing_charge_mono` |
| The block matrix as a Dirichlet form | on step packets Weil's form is `2 c₀ c₁ + Σ V_j σ_j² + ½ Σ w_{jl}(σ_j − σ_l)²`: the product of the two charges, a potential, and the Dirichlet form of a weighted graph on the blocks whose weights, the jets and the contacts, are positive; the neutral part does not increase under the modulus | `sum_blockMatrix_eq_charges_potential_dirichlet`, `blockWeight_pos`, `sum_neutralBlock_abs_le`, `sum_sum_mul_eq_doob` |
| | the neutral part is Lorentzian on the first step packets of ratio four and seven: positive with the margin of the block matrix where a charge vanishes, negative on the first block | `sum_neutralBlock_four_ge`, `sum_neutralBlock_seven_ge`, `sum_neutralBlock_four_fine_ge`, `neutralBlock_one_one_neg` |
| | a vector that minimises the neutral part among the vectors of its length has entries of one sign, so both its charges are nonzero with one sign: the block matrix is strictly above its neutral part there | `neutral_minimizer_one_sign`, `charges_mul_pos_of_neutral_minimizer`, `sum_neutralBlock_lt_sum_blockMatrix_of_minimizer` |
| | without RH: at every block size the block matrix is at least `1/5000` on every window `(R, R + J]` with `50J ≤ 53R`; at every ratio, `𝔚_4` among them, it is nonnegative on the thin step packets, which vanish off the first `c` blocks above each multiple of the block size `B`, `log(1 + c/B)` small | `sum_blockMatrix_ge_of_short`, `exists_forall_packetForm_thin_stepPacket_nonneg_ratio` |
| | on a window with `4J ≤ R` the block matrix is negative off the diagonal and its ground vector has one sign and is charged, at every block size; two forms with one negative square each, coupled through minus the product of their charges, have one negative square together iff `αβ ≥ 1` | `charges_mul_pos_of_blockMatrix_minimizer`, `hermNegIndex_glued_eq_one`, `hermNegIndex_glued_eq_two` |
| | the coarse blocks of a ratio: coercivity `log R − E_Q` on the step functions of a refinement with vanishing sums over the blocks above `R`; a margin above `R` survives every refinement up to `C_Q²/(log R − E_Q − μ)`; at most `(Q − 1)⌈e^{E_Q}⌉` negative squares at every block size | `packetForm_coarseNeutral_ge`, `packetForm_refined_ge_of_margin`, `hermNegIndex_blockWindow_le_uniform` |
| | the neutral part is Weil's form of the zeros minus the poles `s = 0, 1`, the archimedean-minus-prime energy; on smooth tests its index is one plus the number of zeros right of the line; the same for the Dedekind zeta function of every number field | `neutralForm_stepPacket`, `neutralForm_eq_markovEnergy`, `exists_le_negIndex_neutralGram_iff`, `forall_negIndex_dedekind_sub_poleConfig_le_one_iff` |
| | a block and a far window pair by minus the product of their charges (Mertens with Euler's constant, the prime number theorem), so the pole adds one negative square: over all windows the block matrices have as many negative squares as there are zeros right of the line and the neutral parts one more; RH iff the neutral part of every window with `R ≤ J` has exactly one, and without RH it has exactly one for `R ≤ J ≤ 53R/50` | `tendsto_sum_Ico_neutralBlock_div`, `exists_le_hermNegIndex_blockWindow_iff`, `exists_le_hermNegIndex_neutralWindow_iff`, `riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`, `hermNegIndex_neutralWindow_eq_one` |
| Forced data | weights, constant, scale, tree lengths, exchange law | §2.4 |
| | a reversed contact at `2` fails | `exists_packet_degreePairing_gt_of_flippedContact` |
| The tree of `2` | on packets of length `≤ log 4` the generator is `≥ (1 − 1/√2)∫f²`; Bézout is monotone in the length, holds for long trees, and exactly from a threshold on | `treeGenerator_two_ge`, `treeBezoutAt_two_mono`, `exists_treeBezoutAt_two`, `exists_treeThreshold_two` |
| | a margin of the square at a length is a threshold below `log 2` | `exists_margin_iff_exists_treeBezoutAt_two_lt` |
| | at an odd prime the generator is negative on two bumps and long trees fail | `exists_packet_treeGenerator_neg`, `exists_not_treeBezoutAt_of_three_le` |
| The path of the price | at every `n₀` the functional is `Z` plus a square that bounds the mass at each length; monotone, with a base point and a threshold at each length; on all packets it is RH | `pairForm_contactAt_price`, `priceGenerator_ge_of_length`, `exists_priceBezoutAt`, `exists_priceThreshold`, `combBezoutWith_contactAt_price_iff` |
| Carries | the Witt carry is the digit carry up to the Fermat quotient; the carry is a cocycle and not a coboundary; carry and window count are complementary | `prime_dvd_wittCarry_sub`, `digitCarry_not_coboundary`, `tendsto_carryDefect_add_windowDefect` |
| Counts | on two graphs a section `x` has `\|x_m x_n\|` residues: quadratic on rays, blind to the contact, not a form | `card_quotient_graphPair`, `exists_not_parallelogram_pairRing` |
| | the sections with values in a box number the volume over the gluing index, exactly: on two graphs the area over `#(ℤ/J)`, on the first `N` graphs the volume over `N!`; the contacts enter once, as a constant | `card_filter_mem_alignedBox_mul_index`, `card_pairRing_box`, `index_sectionLattice`, `log_card_sections_alignedBox` |
| Number rings | over a Dedekind domain graphs meet in the prime ideals; an orbit exists iff the ideal is principal | `idealContact_prime_pow`, `exists_idealOrbit_generator_iff` |
| | the pairing of a ring with primitive characters `χ_i` tends to `2 d₁ d₂` minus the zero sum of `ζ Π L(s, χ_i)` | `tendsto_ringForm_add_contact` |
| | Riemann–Hurwitz for the counterterm; the genus | `riemannHurwitz`, `combForm_singleton` |
| | the exact index is the number of distinct zeros to the right of the line; a cover bounds its base | `exists_le_negIndex_ringDefect_iff`, `riemannHypothesis_of_ringDefect` |
| | in a tower the form of `ζ` has weight one over the degree | `tendsto_ringZeroSum_div_degree_sub` |
| Every number ring | the zeros of the completed `L`-function of a primitive ray class character are a tempered configuration and satisfy Weil's explicit formula, with the contacts `Λ_ψ(n) = Σ_{N𝔭^k = n} ψ(𝔭)^k log N𝔭` | `heckeZeros`, `temperedConfig_heckeZeros`, `W_heckeZeros_eq` |
| | the Hodge index of a Hecke character is the number of distinct zeros to the right of the line | `exists_le_negIndex_heckeGram_iff`, `forall_negIndex_heckeGram_eq_zero_iff` |
| | the ideals counted by norms: `d` times the jets of `ℤ`, minus the jets `1/(m + n)` of the factors `Γ_ℝ(s + 1)`, the counterterm with `log N`, twice the contacts `Re Λ_ψ` tend to `m_ψ 2 d₁ d₂ − Z_ψ(f)` | `heckeSymbol_eq`, `heckeZeroSum_eq_heckePacketForm`, `tendsto_heckeForm_add_idealContact` |
| | for any number field, abelian or not: the square through its ideals tends to `2 d₁ d₂ − Z_K(f)` and has the index of its Dedekind zeta function; class characters are primitive | `tendsto_ringForm_add_idealContact`, `exists_le_negIndex_dedekindGram_iff`, `heckeFiniteConductor_trivialModulus` |
| | below the first contact (packets shorter than `log 2`): `Z_ψ(f) ≥ m_ψ 2d₁d₂ + (log N − (d − c) log 128π − c log 4π)∫f²`; for `\|d_K\| ≥ (128π)^{r₁+r₂−1}(4π)^{r₂}` the inequality holds on the square of the ring with the margin `∫f²/5000` | `heckeZeroSum_ge_of_no_contact`, `heckeZeroSum_nonneg_of_no_contact`, `tendsto_ringForm_le_degrees_of_short` |
| | summed over the `h` class characters the contacts keep the principal prime powers; `h` times the pairing of the ring with these contacts tends to `2d₁d₂ − Σ_ψ Z_ψ(f)`, and its index is the number of distinct zeros to the right of the line of all `L(s, ψ)` | `sum_heckeMangoldt_trivialModulus`, `classTrivialContact_eq`, `tendsto_ringForm_add_classTrivialContact`, `exists_le_negIndex_classGram_iff` |
| An extension that is not abelian | the splitting field of `X³ − 2` has the group `S₃`; its character `ρ` of degree two has the contacts `(#{x ∈ 𝔽_{p^m} : x³ = 2} − 1) log p`, which are the von Mangoldt function of the cubic character of `2`, a ray class character modulo `6` of `ℚ(ω)`; Weil's explicit formula and the index law for `ρ` | `exists_not_commute_cubeRootsOfTwo`, `heckeMangoldt_cubicTwoHecke`, `W_artinZeros_eq`, `exists_le_negIndex_artinGram_iff` |
| Virtual characters | for tempered configurations `A`, `B`, the form `W_A − W_B` has `n` negative squares on some family iff `A − B` has `n` defect points: points right of the line with net multiplicity `≠ 0`, points on the line with net multiplicity `< 0`; it has none iff the quotient has neither zero nor pole off the line and no pole on it | `exists_le_negIndex_sub_zeroGram_iff`, `forall_negIndex_sub_zeroGram_eq_zero_iff` |
| | the same for quotients of products of `L`-functions, and for the relative square of two number rings | `exists_le_negIndex_quotient_iff`, `exists_le_negIndex_relativeSquare_iff`, `forall_negIndex_relativeSquare_eq_zero_iff` |
| | the contacts of a number ring are its point counts: `Σ_{N𝔭^k = p^m} log N𝔭 = #Hom(𝓞_K, 𝔽_{p^m}) · log p`; the relative square of two number rings at finite scale has the contacts `(N_m^L(p) − N_m^K(p)) log p` and no pole plane | `idealContact_prime_pow_eq_natCard_ringHom`, `tendsto_relativeForm_add_relativeContact` |
| Order one | two vertical lines weigh the zeros of an entire function of order one; with a functional equation and a conjugation the zeros are a tempered configuration with Weil's explicit formula | `hasSum_zeros_two_lines`, `hasSum_zeros_explicit`, `zerosConfig`, `temperedConfig_zerosConfig` |
| Twisted parts | nonpositive up to the trivial aperture, uniformly in the character | `exists_uniform_trivial_conductor_aperture` |
| | a real zero is one square of explicit depth and repels the others | `re_Wsummand_real_zero_pair_ge_neg_two_pairEnergy`, `exists_twistedComb_square_margin` |
| Integer-norm systems | the square sees a system through its norms; on its own comb the system of the squares fails Bézout | `ghostLift_adams_X_eq_of_eq`, `exists_packet_squarePairing_gt` |

In the continuation and the corpus: the normal form at finite scale, block averages, the comb
`q^ℤ` of a curve as a Toeplitz form whose sign is purity, the contacts of a prime as chain
squares minus the diagonal and the jets as even Newtonian multipoles; RH iff every ratio
window has a positive mass floor `γ(Q) Σc²` at all large scales
(`riemannHypothesis_iff_ratioWindow_positive_mass_floor`); the robust index of the finite comb
counts the zeros to the right of the line (`nat_le_rightZeros_iff_eventual_robustCombIndex`)
(all `HodgeTheoryOfAFixedPart`); the index of the restricted form in the aperture with its
jump law (`ArithmeticContinuationAndCriticalEnergy`); the cost `m·θ(S)` of order `m` at the
primes of `S` (`SignFreePurityMechanisms`).

## 7. Constructions

Each construction asks for a property that is an inequality and has a kill condition.

| | Deliverable | Kill condition | State |
|---|---|---|---|
| I | a path on the comb lattice: the inequality at a base point and a transport that is not RH | every candidate has transport equivalent to RH | closed. Dilation, overlap flow, coupling Laplacian: equivalent to RH (corpus). The length of the tree of `2` is monotone on packets shorter than `log 4`; odd trees fail. The path of the price is monotone at every `n₀ ≥ 2` and is RH at every parameter |
| II | the archimedean fibre glued to the trees so that the glued form is the comb form | every gluing is the pairing itself or fails | invariant gluings have a constant diagonal; along the comb every free parameter is forced (§2.4) |
| III | Stepanov on the planar square: a small section vanishing on a window | the forced value is the product of the contact ideals and is attained | closed: `planarValues_eq_prod` |
| IV | the index law per character on squares of towers, class fields and Galois extensions | the form of `ζ` has weight `1/[K:ℚ]`, `1/h` | closed for Hecke characters, class characters, the character of degree two of `X³ − 2`, and for every virtual character of Hecke characters (zeros and poles), with the contacts of a number ring as its point counts. Open: Brauer induction and the reciprocity that make an Artin character such a virtual character (A150) |
| V | Bézout for an integer-norm system on its own comb | the jets of the comb are not those of the system | closed for the squares: `exists_packet_squarePairing_gt` |
| VI | a count: natural numbers with a quadratic Tate limit | no definition without the form | the count on the object is linear (split norm; volume over the gluing index); counts on the surviving prime rays exist iff RH (corpus). Open: a definition without the form |
| VII | finite scale: the inequality in finite rank | the finite statement is the inequality at its length | closed as an equivalence with explicit errors; the matrices are those of the floor maps; `𝔚_4` and `𝔚_7` are positive with a margin on unit blocks; every window of ratio at most `103/50` has the margin `1/5000` at every block size; the neutral part is the form of the zeros minus the poles, and RH is its signature, on smooth tests and on the windows at finite scale; the margin of a ratio at every block size is decided by one matrix, at a scale `R` with `log R ≥ E_Q + 2C_Q²/μ₀ + μ₀`. Open: ratio above `103/50` at every block size; first all blocks at the ratio four, where the index is between `0` and `300000` (A146) |
| VIII | the index as a topological invariant: index zero from the ends of the aperture path | the invariant is the index and its far end carries the zeros | closed as Morse = Maslov. The index is a Morse index: the sum of the nullities of the conjugate apertures, at every energy; the near end is zero and the far end is the number of zeros right of the line. The symplectic structure exists and is defined from the places: the index is the number of crossings of the aperture conormals with the graph of Weil's operator, and it is the same along every monotone path in the (aperture, energy) plane. The invariant does not fix its own value: index zero is RH |
| IX | the width on the tails | the growth of the tail is the zero-free half-plane | closed as an equivalence on one sequence (`powerCombTailGrowth_iff_zeroHalfPlane`) |
| X | bound states: the Hodge index as the number of bound states of the floor-map graph of a window, counted from its potential and its edge weights | the count is the index: one on the certified windows, and a wrong weight, constant or tree length gives a second | proposed. Built: the potential and the Dirichlet form with positive weights; the ground vector of the neutral part has one sign and is charged; one bound state on the certified windows; the refinement tower; a block and a far window couple by minus the product of their charges; coercivity on the coarse-neutral part and the bound `(Q − 1)⌈e^{E_Q}⌉` at each ratio; the gluing lemma for a coupling that is exactly the product of the charges. Open: a count from the potential and the weights; the gluing of two actual windows; the first window that could hold a second bound state |

**The path at `2`.** A tree of `p` glued with the edge length `ℓ` has the contacts `ℓ` along
the chains of `p` and the counterterm `log(n/2π) − (log p − ℓ) v_p(n)`. On packets of length at
most `2 log p` the functional is affine in `ℓ`: `Z(f) + (ℓ − log p)·E_p(f)`. For `p = 2` the
generator `E₂` is a positive form, so Bézout is monotone in `ℓ`, holds for long trees without
hypothesis, and holds exactly for `ℓ ≥ ℓ*(L)`. Bézout for the square at the length `L` is the
statement `ℓ*(L) ≤ log 2`; it is proved for `L ≤ 181/250`. The path ends at `log 4`, where the
second point of a chain is seen, and has no analogue at an odd prime, where the first contact
`∫f²/√p` exceeds the mean `∫f²/(p − 1)` of the Busemann function.

**The path of the price.** Change the contact at `n₀` by `t` and raise the counterterm by its
price `2|t|/√n₀`. The functional is `Z(f) + (|t|/√n₀)∫(f(u + log n₀) − sgn(t) f(u))²`: the
square of `ℤ` plus a square, at every prime and on all packets. On packets of length `L` the
square is at least a multiple of the mass, so far along the path Bézout holds without
hypothesis, and it holds exactly from a threshold on; Bézout for `ℤ` at the length `L` is the
statement that the threshold is `0`. On all packets every member of the path is equivalent to
RH. So a path at an odd prime exists when the counterterm moves at the price of the contact;
it does not exist when the counterterm follows the product formula.

The constructions that fixed the object (Frobenius lifts, carries, the surface, the
archimedean fibre, a second dimension, number rings, curves) are closed; their survivors are
the pillars of §6.

## 8. Criteria

A construction is read against sixteen criteria; the pairing of the degree points meets each.

| # | Criterion | Reading |
|---|---|---|
| C1 | reproduces Weil and Stepanov for curves | point counts are effective elements; on the comb `q^ℤ` the pairing is a Toeplitz form whose sign is purity |
| C2 | counts alone are not enough, and a count rate is not enough | the golden datum is effective, has the functional equation, and is not pure; fakes have a count with a power saving and a zero that `ζ` lacks (test bench) |
| C3 | uses the functional equation as an identity | every weight but `Λ` fails; edits with a finite layer fail; the Liouville twist fails at the first rung |
| C4 | uses the Euler product on the function | a reversed contact fails |
| C5 | sees the exact normalization | `Λ(k)/√k`, the constant `2π`, the scale, the conductor are forced |
| C6 | infinite type | a finite fibre forces a contact that is not Weil's |
| C7 | the diagonal is the density of a comb, with discriminant and conductor | every other counterterm leaves a term of the size of the mass |
| C8 | positivity is derived, and not from a section count | on the tower and on the planar square the count is an identity; in aligned boxes it is the volume over the gluing index |
| C9 | selective only where a contact enters; no margin | below the first contact every weight passes; on packets of degree zero there is no gap |
| C10 | additive over the constituents of a number ring, zeros and poles counted | the twisted parts have no pole plane and separate exact indices; a quotient of `L`-functions has the index of its zeros and poles |
| C11 | below the trivial aperture it proves nothing that the dominated box does not have | up to `log log q − o(1)` every system with contacts bounded by `Λ` is positive |
| C12 | at finite scale it is the index of the neutral part | on block-constant divisors the form tends to Weil's form of the step packet with an explicit error; RH iff the neutral part of every window has exactly one negative square |
| C13 | it is a statement at the point: no deformation of the square transports it | every path through the square of `ℤ` is RH at each parameter |
| C14 | a quadratic count | the counts on the object are linear |
| C15 | treats neutral null modes | the index is the sum of the nullities below (`negativeRank_eq_sum_nullity`); the polar Lagrangian sees the charged null modes only |
| C16 | its comb grows at the rate of the width | `powerCombTailGrowth_iff_zeroHalfPlane` |

## 9. Questions, order of work, decisive test

| # | Question | State |
|---|---|---|
| 1 | a count quadratic in the divisor, with the pairing as its Tate limit | Open. On the object every count is linear: the split norm on two graphs, the volume over the gluing index in a box. A count with values in `ℕ` and the integer probes as Tate limit exists iff RH (corpus) |
| 2 | Bézout from a property of the object | RH. Every structure found is an identity or a receiver; weights, constant, scale, tree lengths and prices admit no deformation |
| 3 | the bound-state count of the floor-map graph: the number of negative squares of the neutral part of a window, from its potential and its edge weights | The neutral part of the block matrix is a potential plus the Dirichlet form of a weighted graph, with positive weights on the jets and on the floor maps `b ↦ ⌊b/k⌋` (`sum_blockMatrix_eq_charges_potential_dirichlet`); its ground vector has one sign and is charged (`neutral_minimizer_one_sign`). It is Weil's form of the zeros minus the poles, and over all windows it has one negative square more than there are zeros right of the line (`exists_le_hermNegIndex_neutralWindow_iff`): RH iff the graph of every window with `R ≤ J` holds exactly one bound state (`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`). One bound state is proved on the windows of ratio at most `103/50` at every block size (`hermNegIndex_neutralWindow_eq_one`). The neutral part is invariant under refinement, a block and a far window couple by minus the product of their charges (`tendsto_sum_Ico_neutralBlock_div`), and at every block size a window of ratio at most `Q` has at most `(Q − 1)⌈e^{E_Q}⌉` negative squares of the block matrix and one more of the neutral part. Gluing: two forms with one negative square each, nonnegative where their charges vanish and coupled through minus the product of the charges, hold one bound state together iff the product of their susceptibilities `α = u·A⁻¹u`, `β = v·B⁻¹v` is at least one, and two otherwise (`hermNegIndex_glued_eq_one`, `hermNegIndex_glued_eq_two`). Open: a count in terms of the potential and the weights; the gluing of two actual windows, whose coupling is the product of the charges only in the mean; the first window that could hold a second |
| 4 | Brauer induction: the index law for every Artin character (A150) | Proved: the index law of a virtual character. For a quotient of products of Hecke `L`-functions the index is the number of zeros and poles right of the line plus the number of poles on it (`exists_le_negIndex_quotient_iff`); so Bézout for an Artin character is the Riemann hypothesis of its `L`-function together with Artin's conjecture on the line. Proved for one character that is not abelian (degree two, monomial). The contacts of a number ring are its point counts over the finite fields, and the relative square of two number rings has the differences of the point counts as contacts (`idealContact_prime_pow_eq_natCard_ringHom`, `tendsto_relativeForm_add_relativeContact`). Open (classical, not in the corpus): Brauer's induction theorem; the identification of an induced character with a Hecke character |
| 5 | the sign of `𝔚_4` at every block size (A146) | `𝔚_4 ≥ 1/20` on the three blocks of `(1, 4]` and `≥ 1/100` on the six blocks of `(2, 8]`; `𝔚_7 ≥ 1/100` on the six blocks of `(1, 7]`. At every block size: the matrices of ratio at most `103/50` are at least `1/5000` (`sum_blockMatrix_ge_of_short`); the matrices of every ratio are nonnegative on thin step packets (`exists_forall_packetForm_thin_stepPacket_nonneg_ratio`); a margin `μ₀` above a scale `R` with `log R ≥ E_Q + 2C_Q²/μ₀ + μ₀` is a margin `μ₀/2` on every refinement (`packetForm_refined_ge_half_of_margin`); `𝔚_4` has at most `300000` negative squares (`hermNegIndex_blockWindow_ratioFour_le`). Open: no negative square at every block size, by certified margins up to the transfer threshold or by a sharper transfer |
| 6 | charged ground states (B104) | Nullity = charged nullity + neutral nullity, and the charged null modes are the crossings of the polar Lagrangian with the charge axis. A null mode at an energy below the pole-vanishing ground energy `μ₀(a)` is charged, and the ground modes at `a` are all charged iff `μ(a) < μ₀(a)` (`neutralNullity_groundEnergy_eq_zero_iff`). Proved for every aperture up to `½(log 2 + 1/50)` at energies below `1/20`. At finite scale the ground vector of the neutral part has one sign and is charged; the block matrix adds the product of the charges, which favours charges of opposite sign. On a window `(R, R + J]` with `4J ≤ R` the jets win: the block matrix is negative off the diagonal, and at every block size its ground vector has one sign and is charged (`blockMatrix_neg_of_narrow`, `charges_mul_pos_of_blockMatrix_minimizer`). Open: whether `μ(a) = μ₀(a)` can occur; first, the ground vector of the block matrix on windows of ratio above `5/4`, where the matrix has entries of both signs |

Settled, and now part of §6: the limit matrices at finite scale and the converse; Hecke
characters, ideals as degree points and a ring that is not abelian; the Li ladder on the
Laguerre tails and the width on the power tails; a path at an odd prime (the price path); the
index as a homotopy invariant of the aperture path, a Morse index and a Maslov index
(`negativeRank_eq_sum_apertureCrossing`, `null_modes_along_two_paths`), whose value zero is RH
and is not produced by the invariance.

**Order of work.** The sign of `𝔚_4` at every block size (A146); Brauer induction (A150); a
gluing lemma for two windows; charged ground vectors at finite scale (B104).

**The decisive test.** A construction whose Bézout holds for an edit with a finite layer, for
a fake, for the Liouville twist at the first rung of the conductor ladder, for a wrong
constant, or along a path of squares, is wrong. On the comb of the integers the pairing rejects
each: Bézout for a weight is RH and the weight `Λ` (`combBezout_iff`), so the contacts of any
other system fail; a counterterm lowered by a positive constant fails (`combBezoutShift_iff`);
a contact changed without its price fails (`combBezoutWith_contactAt_iff`), and with its price
it is RH at every parameter; the Liouville twist fails just above the trivial aperture (test
bench). The test for a wrong constant is meant with the contacts fixed: wrong contacts with a
larger counterterm pass, under RH, from the supremum of their symbol on.

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
| A monotone path through the square of `ℤ` is special to the prime `2` | a contact paid at its price is a monotone path at every prime; special to `2` is the path whose counterterm follows the product formula |
| The inequality at finite scale is stronger than its limit | under RH it holds at all large scales up to `η Σ c_n²`, for every real divisor of a window |
| Weil's form needs smooth packets | in the coordinate of the autocorrelation it is defined on step packets, and it is their form that the finite matrices converge to |
| A count of sections in a box sees the intersection numbers | its logarithm is the volume minus the sum of the contacts: one constant, the same for every box, with the sign opposite to the pairing |
| A count with quadratic growth gives the pairing | the count on two graphs is `\|x_m x_n\|`, the same for every contact, and not a quadratic form |
| A number ring needs its own comb | counted by norms its ideals sit on the comb of the integers; the discriminant is a density, the ramification term of the genus |
| A ring that is not abelian needs its Artin `L`-functions before it has a square | counted by norms its ideals pair with the zeros of its Dedekind zeta function; signature, discriminant and the prime ideals are all that enter |
| A ring can satisfy the inequality while `ℤ` does not | negative squares of the square of `ℤ` are negative squares of every abelian ring over it (its zeta function is `ζ` times Dirichlet `L`-functions); for a ring that is not abelian this is Dedekind's conjecture `ζ ∣ ζ_K` |
| A tower of covers replaces the extension of constants | per degree the form of `ζ` has the weight `1/[K:ℚ]` |
| The index of a ring is the sum of the indices of its characters | it is the number of distinct zeros; a shared zero is one negative square |
| An Artin character has an index only if its `L`-function is entire | as a virtual character it has the index of its zeros and poles; a pole on the line is a negative square, a pole right of the line counts like a zero |
| An integer-norm system passes on its own comb when its zeros lie on a line | the system of the squares fails: the comb gives its density, and the jets are those of the norms |
| The sizes of the contacts can pass the trivial aperture | the systems `Λ`, `−Λ` and the Liouville twist with a conductor fail beyond it (test bench) |
| The carries can be removed by another choice of digits | the carry is a cocycle that is not a coboundary |
| The first windows with contacts lie within the proved lengths | `(1, 4]` has the length `log 4`, beyond every length with a sign for all packets; the sign is proved there on step packets of unit blocks only |
| A step-packet matrix is diagonally dominant | on the six blocks of `(1, 7]` the first block has the diagonal `0.19` and off-diagonal entries of size up to `0.19`; the certificate is a Cholesky factorization |
| The index jumps where a zero is seen | it jumps at an aperture with a null mode, by the number of null modes; a zero off the line is one unit of the total |
| A power tail of small exponent converges | it converges exactly for `a < ½ − w`: its growth is the width of the zeros |
| A count rate identifies the integers | at every exponent above `½` a system with integer norms has that count rate and a zero that `ζ` lacks; a bounded count error identifies the rational primes (test bench) |
| A path of squares transports the inequality | every path through the square of `ℤ` in the corpus is RH at each parameter |
| A tail with a jump needs an explicit formula for test functions with a jump | the scaling recursion reduces every logarithmic tail to the flat tail, whose row is explicit at finite scale |

## 11. Open problems and research topics

**The step-packet matrices (question 5, A146).** RH holds iff for all `K, R` the matrix of Weil's form
on the step packets of the `3KR` blocks of `(R, (3K+1)R]` is nonnegative. Its entries are
elementary: `2 log(b/a)(b − a)`, the closed form of the jets on flat packets, and the overlaps
`(b/k − a)⁺` with the weights `Λ(k)`, `k ≤ 3K + 1`. The comb at block size `B` is within an
explicit error of the matrix. On unit blocks the matrix is `d ⊗ 1 + 1 ⊗ d + ϱ − J − C`: degrees,
density, jets, and the graphs of the floor maps (§2.6). *Proved:* on `R = 1` the matrices of
ratio four and seven are positive with the margins `1/20` and `1/100` (least eigenvalues near
`0.069` and `0.028`); on `R = 2` the matrix of ratio four is positive with the margin `1/100`
(least eigenvalue near `0.03`); a margin above `mR` implies the same margin above `R`; every
window of ratio at most `103/50` has the margin `1/5000` at every block size, and its neutral
part has exactly one negative square; RH is the statement that the neutral part, the form of
the zeros minus the poles, has one negative square, on smooth tests and on every window with
`R ≤ J` at finite scale; at every ratio the matrices are nonnegative on thin step packets; the
margins of a tower decrease by at most `C_Q²/(log R − E_Q − μ)` from the scale `R` on, and the
index at a ratio is bounded at every block size.
*Open:* the windows of ratio four and seven on finer blocks (matrices
of size `3R` and `6R`, whose margins decrease along divisibility to the bottom of Weil's form
on the window); whether the cone of step packets has a description in which the entries are
positive term by term.

**Bound states of the floor-map graph (question 3).** On a window the neutral part is
`Σ V_j σ_j² + ½ Σ w_{jl}(σ_j − σ_l)²`, a discrete Schrödinger operator: the vertices are the
blocks, the edges the jets (every pair) and the graphs of the floor maps, the weights `w > 0`,
the potential `V` the row sums. *Proved:* the decomposition; a ground vector has one sign and is
charged; one bound state on the windows of ratio at most `103/50` at every block size and on
the first blocks of the ratios four and seven; invariance under refinement; the cross term of a
block and a far window is minus the product of their charges; on the part of a refinement that
is neutral on the coarse blocks the form is at least `log R − E_Q`, so the bound states live on
the coarse blocks and there are at most `(Q − 1)⌈e^{E_Q}⌉ + 1` of them at a ratio; two wells
with one bound state each, coupled through minus the product of their charges, hold one bound
state together iff `αβ ≥ 1`, with `α`, `β` the susceptibilities of the two charges. *Open:* a
count of the bound states from `V` and `w` (of the type of Bargmann or Cwikel, Lieb and
Rozenblum) that is one on the certified windows and two for a wrong weight, constant or tree
length; the gluing of two actual windows: a block and a far window couple by minus the product
of their charges in the mean, and the difference is the fluctuation of the contacts; the first
window that could hold a second bound state.

**The aperture path and charged ground states (question 6).** Weil's form restricted to the aperture `a` and shifted by
an energy `E` has finitely many negative squares and finitely many null modes. *Proved:* the
index at `b` is the sum of the nullities of the apertures below `b`, at every energy: the
number of eigenvalues below a level is the number of null modes at that level met on the way.
RH iff no aperture has a null mode at the energy zero. The two ends: the index is zero at
small apertures, and the sum of all nullities at the energy zero is the number of distinct
zeros to the right of the line.
The null modes are the crossings of the conormals of the apertures with the graph of Weil's
operator, and the index is also the number of eigenvalues below the energy: on a rectangle of
apertures and energies the two monotone paths meet equally many null modes. In the space of
charges and forcings, `ℂ² × ℂ²`, each aperture has a Lagrangian plane that meets the charge
axis in the charges of its null modes; a null mode below the pole-vanishing ground energy is
charged, and there the index is at most two.
The plane is an even line and an odd line. The nullities are not all even: a short aperture has
a simple ground mode.
*Open:* whether a ground mode can be neutral, that is whether `μ(a) = μ₀(a)` can occur (B104);
the differential equation of the two lines in the aperture (a Hamiltonian) beyond the first
conjugate aperture; whether the even and the odd line cross the charge axis at different
apertures.

**A property of the object (question 2).** A one-parameter family of squares through that of `ℤ` which ends at
a square where the inequality is known and along which the inequality can be transported; or
a group with a doubling on which the defect is a canonical height. *Proved:* two monotone
paths with base points, the tree of `2` below the length `log 4` and the price of a contact at
every prime; on both the square of `ℤ` is the end where the generator has been used up, and
the inequality there is the statement that the threshold is at the end. *Open:* a bound for a
threshold without a certificate, that is a lower bound for `inf Z(f)/E(f)` over the packets of
a length; the least constant that makes a contact a square at a given length (it is below the
price and tends to it); a path that moves the archimedean fibre.

**Number rings and Artin characters (question 4, A150).** Two ideals of one norm are one point of the comb of norms, and
the square of a number ring is seen through the contacts `Σ_{N𝔭^k = n} log N𝔭`. *Proved* for
every number field and every primitive ray class character `ψ`: the explicit formula, the
tempered configuration of the zeros, the exact index, and the pairing at finite scale. The jets
depend on the signature (`d` copies of the jets of `ℤ`, less `1/(m + n)` for each factor
`Γ_ℝ(s + 1)`; a complex place carries `1/|m − n|`), the counterterm on discriminant and
conductor, the contacts on the values of `ψ` at the prime ideals. Class group and units do not
enter the square of the ring; summed over the class characters the contacts keep the principal
prime powers, with one pole plane for `h` copies of the jets. The contacts of the ring are
its point counts: at `p^m` the contact order is `log p` times the number of ring homomorphisms
from the ring of integers to the field with `p^m` elements, `Σ_{d ∣ m} d a_d(p)` with `a_d(p)`
primes of norm `p^d` (`idealContact_prime_pow_eq_natCard_ringHom`); over `ℤ`, which has one
point in every finite field, they are `(N_m(p) − 1) log p`. Below the first contact a large
discriminant gives the inequality. For the splitting field of `X³ − 2` the character of degree two is induced
from the cubic character of `2` over `ℚ(ω)`: its contacts are point counts of `x³ = 2`, and its
index is the number of distinct zeros of its `L`-function to the right of the line. A character
that is not monomial has an `L`-function that is a quotient of products of Hecke `L`-functions;
for every such quotient the index of the difference of the forms is the number of its zeros and
poles right of the line plus the number of its poles on the line, common zeros cancelled. For
two number rings the relative form `W_{ζ_L} − W_{ζ_K}` has no negative square iff the zeta
functions agree right of the line and `ζ_K` divides `ζ_L` on it; at finite scale the relative
square has the differences of the jets and of the counterterms, the contacts
`(N_m^L(p) − N_m^K(p)) log p` and no pole plane (`tendsto_relativeForm_add_relativeContact`).
*Open:* Brauer's theorem and
the reciprocity law that turn an Artin character into such a quotient (classical, not in the
corpus); the
zeros of the completion as zeros of a continuation of `ζ_K` itself; small discriminants on short packets (below
`(128π)^{r₁+r₂−1}(4π)^{r₂}` the places do not pay for themselves); the units of a real
quadratic ring.

**A count (question 1).** Natural numbers on the rays of `Γ_1 + Γ_p`, defined without the form,
whose Tate limit is the pairing. *Proved:* the count of residues on two graphs is the split
norm; the count of sections in a box, on two graphs and on the first `N`, is the volume over
the gluing index, an identity on boxes aligned with the index; on the tower and on the planar
square the counts are exact and give identities. So on the object the logarithm of every count
is affine in the multiplicities, and the contacts enter it once with the sign of a condition.
*Open:* a count quadratic in the divisor, defined without the form; by the corpus a count with
the integer probes as Tate limit exists iff RH.

**Tails.** The `n`-th tail has the Laguerre polynomial of `log(N/m)` as
its coordinates, and its transform at a zero is `1 − (1 − 1/ρ)^n`. *Proved:* the form of the
Laguerre tail per degree point tends to `Re 2λ_n`, for every `n`. Three steps. (i) Raising the
scale by one shifts `log(N/m)` by `log(1 + 1/N)` and a tail of positive degree vanishes at its
own scale: an exact recursion in `N`, which with Cesàro summation reduces every pair of
logarithmic tails to the pairings with the flat tail. (ii) The flat tail pairs through its row,
the remainder of the prime number theorem at `N/n` plus the jets; against `log^j(N/n)` the row
has a limit by the hyperbola method and the prime number theorem with error `x e^{−c√log x}`.
(iii) The Mellin transform of the row is `Σ_ρ 1/(ρ(s − ρ))` for `s > 1`; its moments at `s = 1`,
a boundary point, are read off with exact remainders on both sides. No explicit formula for a
test function with a jump enters. The power tails `(N/n)^a`, `0 < a < ½`, read the width: the
degree point `1` has the weight `N^a`, and the tail grows at the rate `σ` iff no zero has real
part above `1 − a + σ`; it converges exactly for `a < ½ − w`. *Open:* the boundary `a = ½ − w`;
a tail whose growth is bounded without a zero-free half-plane.

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
| FloorFreeArithmetic | test bench: finite layers and their models; a feasible weight system at every aperture is RH, and feasible systems converge to `Λ` |
| WorldsOfTheZeroConfiguration | test bench: the models over the rational primes, edits with a finite layer, fakes; what a finite layer and a tail can and cannot keep |
| SumProductArithmeticOfTheLogarithm | a bounded count error identifies the rational primes; fakes at every exponent above `½` |
| ArithmeticContinuationAndCriticalEnergy | the restricted form in the aperture: its index, its null modes, the jump law |
| RHTower | the explicit formula, Weil's functional and its symbol form, the uniqueness of `Λ` in the Weil cone, radical tests, the zero count |
| ArithmeticCastelnuovoSeveri | the inequality on the scaling surface; the exact index law of a tempered configuration; the golden datum |
| ArithmeticLorentzianGeometry, RHTower | the Hodge index of the scaling surface as hyperbolicity of every finite Gram matrix, the pole plane, the atomic intersection Gram; the one-bound-state law of the archimedean-minus-prime energy. The neutral part of the step-packet matrices is that energy on step packets |
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
