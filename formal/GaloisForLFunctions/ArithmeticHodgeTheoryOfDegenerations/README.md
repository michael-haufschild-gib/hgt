# Arithmetic Hodge Theory of Degenerations (AHD)

Namespace `GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations`; umbrella
`ArithmeticHodgeTheoryOfDegenerations.lean`. Every theorem is unconditional. Theorems named
`riemannHypothesis_iff_*` are proved equivalences, not proofs of RH.

## 1. Motivation

The corpus has reduced RH to one even integer: `κ`, the number of distinct zeros right of the
critical line, read on the pole-orthogonal hyperplane `v₁^⊥` of one degenerating family of finite
quadratic forms, the complete Weil matrices `W_{φ,c,N}` (atoms of a profile `φ` of width `c/N` at
`log n`, `n ≤ N`, normalized by the atom mass). It has also proved why every producer of positivity
met so far stops short:

- **Edge logic.** A statement proved without zero information holds on every datum sharing that
  information, so it stops below the edge of the off-line members; an integer read at an
  RH-complete resolution is RH. Only a statement that holds at the edge *by structure* can cross:
  an identity, an inherited polarization, or an integer with a structural bound.
- **Exclusions.** Estimates lose to the doubly exponential aperture ceiling; soft structure holds
  on the golden fake; local and semilocal pieces and trace carriers `1 − P − P̂` carry no
  positivity; deformation is free; tensor amplification is all-or-nothing; approximation by RH-true
  objects lands in the Laguerre–Pólya class.

Over `𝔽_q` the three proofs of RH rest on objects `ℤ` lacks: intersection numbers that are counts
(Weil), auxiliary sections whose vanishing is counted (Stepanov–Bombieri), and tensor powers of a
realization with Euler products (Deligne). In each the sign is a **structure theorem** (the Hodge
index on `C × C`), not an inequality. Over `ℤ` the corpus has the algebra of that structure
(correspondences, λ-ring, Rosati involution, Lefschetz traces, theorem of the square), Tate's limit
law naming the missing input (a naive height), and, in ADT, the first piece of its geometry: the
rescaled limit of the complete family is a polarized structure with the dilation semigroup as
monodromy.

**AHD's thesis.** The missing object is an arithmetic Hodge theory of the degeneration of the
scaling surface along the resolution axis: a degenerating polarized family with the dilation
semigroup as monodromy, whose positivity is carried through the critical curve
`c^{β+1} ≍ log N` by one of three carriers —

- **A. a count**: a cardinality or log-count (a naive height on correspondences), whose Tate limit
  is Rosati positivity;
- **B. an inherited polarization**: a polarized second-order term of the degeneration at the
  critical curve, inherited by the nearby fibres;
- **C. an integer with a structural bound**: a window index forced to `0` by a source-defined
  sectorial structure —

with one global gluing (one negative square at the pole, distinct primes coupled only through `∞`)
and calibrations over `𝔽_q` and on the fakes. ADT is the first construction (the rescaled limit).
AHD identifies the first-order structure as a count, locates exactly where the zeros enter the
second order, computes the second-order term at the critical curve exactly (Weil's form plus the
monodromy derivative of the first-order count), and isolates the one theorem the field still needs.

## 2. The degeneration and its two scales

The complete family is Weil's form on atomic tests. On the zero side each point `ρ` of the zero
configuration contributes, for the atomic test of weights `x`, the atom factor `ĝ(γ_ρ) conj ĝ(γ̄_ρ)`
times the Dirichlet factor `D_x(γ_ρ) D_x(γ_{1−ρ})`, `D_x(γ_ρ) = Σ x_n n^{ρ−½}` (SSHA
`Wsummand_atomicTest`). For the atom `g = φ(·/w)` the atom factor is `w² φ̂(wγ) conj φ̂(wγ̄)`, and the
normalized contribution is `m_ρ (c/N) φ̂(wγ) conj φ̂(wγ̄)/∫φ² · D_x(γ_ρ) D_x(γ_{1−ρ})`. Two scales
live in the family.

- **The bulk** (conductor sector). Ramanujan packets `r_e(n) = c_e(n)/√(φ(e) n log N)` spread over
  `[0, log N]`. Their energies degenerate like `c^{−β}`; after rescaling they converge to the
  Jordan form (ADT). The Dirichlet factor of `r_e` is the conductor Dirichlet polynomial
  `D_e(s;N) = Σ_{n≤N} c_e(n) n^{s−1}`, and **only the pole conductor has a horizon term**:
  `D_e(s;N) − [e = 1]N^s/s → ζ(1 − s) J_s(e)` on the open strip. An individual point of the strip
  therefore enters a fixed packet only through the pole coefficient, with weight `1/(ρ(1 − ρ))` of
  positive real part.
- **The horizon layer** (top blocks `n ∈ [N e^{−A}, N]`). The vectors `x_n = h(log(n/N))/√n`
  synthesize the test `H(y) = e^{y/2} h(y)` at the horizon. Their Dirichlet factors are Riemann sums,
  `N^{−s} D_x(γ_s) → ĥ(s) = ∫ h(y) e^{sy} dy`, and an individual point enters through Weil's summand
  `W_ρ(H, H) = m_ρ ĥ(ρ) ĥ(1 − ρ)`: a square on the line, indefinite for an off-line quadruple.
  Over windows of zeros these summands exhaust Weil's form of `H`.

The first order of the degeneration is a count: the Jordan coefficient is the point count of
projective space, `J(m) = J(1) · #ℙ⁷(ℤ/m)`. The sign question lives in the second order, and there
it lives in the horizon layer. On the arithmetic side the horizon layer is computed exactly. Its
energy against the atom spectrum is, by Plancherel and Poisson summation on the atom grid, the
Riemann sum of `∫ H²` plus the **aliasing** of the grid harmonics; below the grid the block is the
Riemann sum of the synthesized test; above it the symbol is `log N/2π` up to `O(c^{−p})`. Hence:

**c⁻¹⟨Wx, x⟩ = κ_φ Q(H) − log N · N⁻¹ Σ_n h(log(n/N))² E₁'(cn/N) + o(1),**

where `E₁` is the conductor-one bulk energy, whose rescaled limit is `J(1)`. **The aliasing that a
horizon block pays at depth `y` is the dilation derivative of the bulk energy at the local overlap
`c e^y`.** For the tilted spline (`β = 7`) this is exact at the critical curve `c⁸ = K log N`:

**c⁻¹⟨Wx, x⟩ → κ_φ Q(H) + (7 J(1)/K) ∫ e^{−8y} H(y)² dy.**

More generally, for every profile whose bulk energy has the rescaled limit `s^β E₁(s) → J`, at
`c^{β+1} = K log N`: **c⁻¹⟨Wx, x⟩ → κ_φ Q(H) + (β J/K) ∫ e^{−(β+1)y} H(y)² dy.** The second-order
term of the degeneration on a horizon window is Weil's form plus `β J/K` times a positive weighted
norm, determined by the first-order data `(β, J)` of the bulk; its critical multiple is
`K*(H) = β J ‖H‖²_{−(β+1)}/(κ_φ |Q(H)|)`.

## 3. Objects

| Object | Lean | Meaning |
|---|---|---|
| Complete Weil family | RAPT `completeWeilMatrix` | the variation over the resolution plane |
| Zero configuration, Weil summand | Zeta23 `ZeroConfig`, `ZeroConfig.Wsummand`, `ZeroConfig.W` | `W_ρ(f,g) = m_ρ f̂(γ_ρ) conj ĝ(γ̄_ρ)` |
| Atomic Dirichlet polynomial | SSHA `dirichletPoly` | `D_x(z) = Σ_{n≤N} x_n e^{iz log n}` |
| Conductor Dirichlet polynomial | `conductorDirichlet` | `D_e(s;N) = Σ_{n≤N} c_e(n) n^{s−1}` |
| Horizon term, complex Jordan totient | `horizonTerm`, `jordanC` | `[e = 1]N^s/s`; `J_s(e) = Σ_{d∣e} μ(e/d) d^s` |
| Packet weights, pole coefficient | `packetWeights`, `poleCoefficient` | `Σ_{e∈E} y_e r_e`; `[1 ∈ E] y_1` |
| Bulk ledger | `bulkLedger` | contribution of `ρ` to the normalized complete form of a packet |
| Horizon weights, profile, transform | `horizonWeights`, `horizonProfile`, `horizonTransform` | `h(log(n/N))/√n`; `h(log x) x^{s−1}`; `ĥ(s)` |
| Synthesized test | `halfWeight` | `H(y) = e^{y/2} h(y)` |
| Horizon ledger | `horizonLedger` | contribution of `ρ` to the normalized complete form of a horizon block |
| Quadratic forms, admissible multiples | `qform`, `QNonneg`, `admissible` | `{K ≥ 0 : J + K X ⪰ 0}` |
| Primitive vectors, projective points | `IsPrimitiveVec`, `PrimVec`, `ProjPoints` | `(ℤ/m)^k` primitive; `ℙ^{k−1}(ℤ/m)` |
| Symbol of the localized explicit formula | `nuSymbol` | `ν_X = μ + P_X` |
| Centred horizon test, pole amplitudes | `centredHorizonTest`, `alphaPlus`, `alphaMinus` | `T_N(u + log N)`; `φ̂(±iw/2) D_x(±i/2)` (divided by `N` for `−`) |
| Symbol integrand, aliasing integrand | `horizonSymbolIntegrand`, `aliasIntegrand` | `‖φ̂(wτ)‖² |D_x(τ)|²/N ν(τ)`; its absolute value at `±τ` |
| Window start, window constant, aliasing constant | `windowStart`, `windowConst`, `aliasConst` | `⌈N e^{−A}⌉`; `L e^{3A/2} + B e^{A/2}`; `K_al` |
| Aliasing density | `aliasDensity` | `a_φ(s) = Σ_{k≥1} |φ̂(2πks)|²`, the grid harmonics at overlap `s`; `= −(∫φ²/2) E₁'(s)` |
| Block energy, part below the grid | `blockEnergy`, `lowPart` | `∫ |φ̂(wτ)|² |D_x|²/N` over `ℝ` and over `|τ| ≤ Ne^{−A}` |
| Aliasing functional | `horizonAlias` | `𝒜_N = (2/N) Σ_n h(log(n/N))² a_φ(cn/N)` |
| Tapered, logarithmic, aliasing weights | `taperedProfile`, `logProfile`, `aliasWeight` | `e^{−y/2}h(y)`; `g(log x)`; `h(y)² e^{−8y}` |
| Conductor-one Jordan coefficient of the tilted spline | `tiltedJordanOne` | `J(1) = (2/∫φ²) A_φ ζ(8) = lim c⁷ E₁(c)` |
| Completed shell energy (bulk, conductor one) | RAPT `completedShellEnergy` | `E₁(s)`, positive, antitone, `→ 0` |
| Jordan coefficient | ADT `jordanCoefficient`, `jordanTotient` | `J(m) = lim c⁷E_m(c)`; `J_k(m)` |
| Window aliasing | `windowAlias` | `h(log x)² a_φ(c max(x, e^{−A}))`, the integrand of `𝒜_N` |
| Second-order limit, pencil and horizon Gram matrices | `secondOrderLimit`, `pencilGram`, `horizonGram`, `horizonTest` | `κQ(H) + (βJ/K)‖H‖²_{−(β+1)}`; its polarization on a family; Weil's Gram matrix of the horizon tests |
| Weil and aliasing parts of the pencil | `weilWindowGram`, `aliasGram` | `κ W(H_i, H_j)`; `∫ e^{−(β+1)y} H_i H_j` |
| Twisted windows | `twistedWeights`, `MeanZeroTwist`, `twistedLedger` | `χ(n) h(log(n/N))/√n` with `χ` periodic of mean zero |
| Unimodular vectors, projective space over a ring | `Unimodular`, `ProjSpace` | `R^k` entries generating `R`; modulo `Rˣ` |
| Möbius horizons | RAPT `mobiusHorizon`, `horizonBoundary` | exact zero-side reading of atomic vectors |
| Correspondences, Rosati form, naive height | AET `intRosatiForm`, `tateLimit` | carrier A |
| Jump count | LST `jumpCount` | the primitive `h¹` of a prime-free cycle |
| Glued state | AKG `archGlue`, `weilArchState` | the one negative square |
| Window index | WD `fredholmIndex`, `wienerHopfLift` | carrier C |

## 4. Language

- **Resolution** `(c, N)`; **universal regime**, **edge**, **RH regime** as in EHT.
- **Critical curve**: `c^{β+1} = K log N` (`c⁸ = K log N` for the tilted spline); `K` is its
  **multiple**.
- **Bulk / horizon layer**: Ramanujan packets of fixed conductor / vectors supported in
  `[N e^{−A}, N]`; **window** of the block: `[−A, 0]` in `y = log(n/N)`.
- **Horizon term** of a packet: the part of its Dirichlet factor growing like `N^{Re s}`.
- **Ledger**: the contribution of an individual point (or a finite window of points) of the zero
  configuration to a family of vectors, after the natural rescaling (`log N/c` for the bulk, `1/c`
  for the horizon layer).
- **Second-order term**: the limit of `c^β` times the extension data along the critical curve;
  **admissible multiples** of a pair (polarization `J`, second-order term `X`): `K` with
  `J + K X ⪰ 0`; the **critical multiple** is their supremum.
- **Aliasing energy**: the contribution of the frequencies of a horizon block near the atom grid
  (`|τ| ≳ N`), where the atoms undersample the synthesized test; its **density** `a_φ(s)` at
  overlap `s` is the sum of the grid harmonics `|φ̂(2πks)|²`, `k ≥ 1`.
- **Local overlap** of a horizon block at depth `y = log(n/N)`: `c e^y`, the number of atoms that
  overlap at `log n`.
- **Carrier**: count (A), inherited polarization (B), integer with a structural bound (C).

## 5. Mechanisms

**A. Count.** naive height ⇒ Tate limit `≥ 0` ⇒ Rosati positivity at a cycle ⇒ orbit Hodge index
⇒ RH (AET, AOG). At first order the degeneration is a count: `J_k(m)` counts primitive vectors of
`(ℤ/m)^k`, units act freely, so `J_k(m)/φ(m) = #ℙ^{k−1}(ℤ/m)`; the weight strings are the Hensel
towers of `ℙ^{k−1}` (`#ℙ^{k−1}(𝔽_p) = [k]_p` at the bottom, `p^{k−1}` lifts per step) and the tensor
law is the Chinese remainder theorem. The limiting polarization is positive because it is a
cardinality.

**B. Degeneration.** rescaled limit (count of `ℙ^β`) ⇒ second-order term at the critical curve ⇒
polarized? ⇒ inheritance ⇒ RH. The zero side splits the second order into ledgers:
- **Bulk.** `D_e(s;N) = Σ_{d∣e} μ(e/d) d^s H(s; ⌊N/d⌋)`, `H(s;M) = ζ(1 − s) + M^s/s + o(1)`; the
  boundary terms add to `(N^s/s)Σ_{d∣e} μ(e/d) = [e = 1]N^s/s`. Hence
  `(log N/N) D_x(γ_ρ) D_x(γ_{1−ρ}) → y_1²/(ρ(1 − ρ))` for every point of the open strip, and
  `Re 1/(ρ(1 − ρ)) = (β(1−β) + γ²)/|ρ(1−ρ)|² > 0`. Each point, on the line or off it, is a positive
  rank-one gluing at the pole; distinct conductors are never coupled by a zero.
- **Horizon.** `N^{−s} D_x(γ_s)` is the Riemann sum of `h(log x) x^{s−1}` on `[0,1]`, whose integral
  is `ĥ(s)` by `x = e^y`; the contribution of `ρ`, divided by `c`, tends to
  `((∫φ)²/∫φ²) W_ρ(H, H)`. Windows of zeros exhaust Weil's form of `H`.
- **Arithmetic side of the horizon.** With the localized explicit formula
  `Q(f) = pole terms + ∫ |f̂(τ)|² ν(τ) dτ`, `ν = μ + P_{e^{2a}}`, the recentred block has transform
  `e^{−iτ log N} w φ̂(wτ) D_x(τ)`: its pole amplitudes are `√N w φ̂(±iw/2) D_x(±i/2)` with
  `D_x(i/2) → ĥ(0)`, `D_x(−i/2)/N → ĥ(1)`; below the grid `|D_x(τ)|²/N → |ĥ(½+iτ)|²` with domination
  `C/(1+τ²)` (Kuzmin–Landau and summation by parts); above it
  `∫_{|τ|>Ne^{−A}} ‖φ̂(wτ)‖² |D_x|²/N |ν| ≤ 2K_al(A_ν + 2 + log N)/c^p` (dyadic windows, sharp mean-value
  theorem). Hence `|c⁻¹⟨Wx,x⟩ − κ Q(H)| ≤ ε + K(1 + log N)/c^p` eventually.
- **Coercivity of the aliasing.** For the tilted spline `‖φ̂(u)‖² ≥ (sinh⁸1/64)(1 + |u|)^{−8}`, the
  symbol is `≥ log N/(4π)` on windows above the grid, and the mean-value theorem holds from below
  on a window `[U, 2U]` with `U ≍ N`, where `Σ x_n² → ∫ h²`. One such window already carries
  `a log N/c⁸` of the off-window integral, `a > 0`; everything off the window is nonnegative.
- **The exact second order.** (i) Plancherel: `∫ |φ̂(wτ)|² |D_x|²/N = (2π/c) Σ_{m,n} x_m x_n G(N log(m/n)/c)`,
  `G` the autocorrelation of `φ`. (ii) Linearize `N log(m/n)/c ≈ (m − n)/a_n`, `a_n = cn/N`, on the
  `O(c)` neighbours that `G` sees (`O(c N^{−3/2})` per entry), and sum by Poisson on `ℤ/a_n`:
  `Σ_j G(j/a) = a((∫φ)² + 2 a_φ(a))`. (iii) Below the grid, effective Riemann sums
  (`|N^{−s}D_x − ĥ(s)| ≤ (L + |s−1|B)e^{2A}/N`) and the Kuzmin–Landau tail give the low part to
  `O(√(c/N) + R^{−1/2} + R²/N)`. (iv) Above the grid `ν = log N/2π + O(1 + log(|τ|/N))`, and the
  dyadic blocks with weights `V + j` cost `O(c^{−p})`. Together:
  `c⁻¹⟨Wx,x⟩ − κ Q(H) − (log N/∫φ²) 𝒜_N → 0` whenever `c → ∞`, `c(log N)²/N → 0`.
- **The aliasing is the monodromy derivative of the bulk.** The increment law of the completed shell
  energy, read harmonic by harmonic, is `E₁(c) − E₁(C) = (2/∫φ²) ∫_c^C a_φ`, so
  `E₁'(s) = −(2/∫φ²) a_φ(s)`: the aliasing density is the rate at which the conductor-one bulk energy
  decreases under dilation, and `𝒜_N` tests it against the window mass at the local overlaps.
- **The constant.** For the tilted spline `|φ̂(2πt)|² = (1/64) q(πt/4)(1 + (πt/4)²)^{−4}` with
  `π`-periodic `q`. On a window the `k`-th harmonic oscillates with frequency `≍ c`; cell-by-cell
  averaging over periods of `q` against the slowly varying weight gives its mean `μ_q`, Riemann sums
  see the oscillation only through `c/N`, and the harmonics sum to `ζ(8)`:
  `c⁸ 𝒜_N → 2(1/64)(4/π)⁸ μ_q ζ(8) ∫ e^{−7y} h² = 7 J(1) ∫φ² · ∫ e^{−8y} H²`. The factor
  `7 = β` is the pointwise density `−d/ds(J(1) s^{−7})` against the tail integral of the bulk.
- **The bulk determines the second order.** For any profile with `|φ̂|² ≲ (1+|u|)^{−p}`, `p > 4`, the
  aliasing density is bounded and Lipschitz above any overlap, so the window sum is a Riemann sum
  up to `O(c^{β+2}/N)`; integrating by parts against `E₁(cx)` turns the window average of
  `a_φ(cx) = −(∫φ²/2)E₁'(cx)` into `c^{−β}` times the window average of `F'(x) · c^β E₁(cx)`, and
  `c^β E₁(cx) → J x^{−β}` uniformly on the window. A second integration by parts gives
  `β J ∫ e^{−(β+1)y} H²`. No equidistribution and no property of `φ` beyond its first-order limit.
- **Critical multiples.** If the rescaled family converges to `J + K X`, positive definiteness is
  inherited and a negative direction is eventually negative; for `J ⪰ 0` the admissible multiples
  form a closed initial segment, positive semidefinite terms never remove a multiple, and negative
  directions persist as `K` grows.

**C. Integer.** source-defined sectorial multiplier ⇒ window index `0` on every window ⇒ RH (WD).
In AHD's language a horizon window `H` has the exact critical multiple
`K*(H) = 7 J(1) ‖H‖²_{−8}/(κ |Q(H)|)` (`+∞` when `Q(H) ≥ 0`): the block is positive below it and
negative above it. On a family of windows the second-order term polarizes to the **pencil Gram
matrix** `P_K = κ Q(H_i, H_j) + (βJ/K)⟨H_i, H_j⟩_{−(β+1)}`, the entrywise limit of the normalized
horizon Gram matrices `G_N` of the complete family. The **window index** `ind₋(P_K)` is read by the
complete family (eventually `ind₋(P_K) ≤ ind₋(G_N)`, lower semicontinuity). The pencil splits as
`P_K = κ W(H) + (βJ/K) A(H)`, Weil's Gram matrix of the synthesized tests plus the positive
semidefinite aliasing Gram matrix, so the window index is nondecreasing in `K` and equals
`ind₋ W(H)` for all large `K`. Translates of the cubic spline moved into one window carry every
finite part of the index of Weil's form (AOG), so **some family of windows has window index `≥ n`
iff `ζ` has at least `n` right zeros**: the window index is the counting function of the right zeros
read through the degeneration, and RH is its vanishing.

**G. Gluing.** One rank-one gluing at the pole creates the Mertens function (Redheffer, ADT) and
the one extra negative square (`κ + 1`, AKG). The zero ledger of the bulk is itself a rank-one
gluing at the pole, of positive sign.

**Cal. Calibration.** The ledger theorems hold for every zero configuration: they carry no
selection. The count law holds over every finite commutative ring — units act freely on unimodular
vectors, and over a local ring `#ℙ^{k−1}(R)(|R| − |𝔪|) = |R|^k − |𝔪|^k` — so the first-order structure
is the same over the residue rings of `ℤ` and of `𝔽_q[T]`. The aliasing constant `βJ` is a property
of the profile and the bulk. Selection enters the degeneration only through Weil's form `Q(H)` of
the untwisted horizon windows; twisted horizon windows are zero-blind.

## 6. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| What is the first-order structure of the degeneration, and why is it polarized? | The point count of projective space: `J(m) = J(1) #ℙ⁷(ℤ/m)`, `#ℙ^{k−1}(ℤ/m) φ(m) = J_k(m)`. Weight strings are Hensel towers, the tensor law is CRT. It is positive because it is a cardinality. | `jordanCoefficient_eq_projPoints`, `natCard_projPoints_mul_totient`, `natCard_primVec_eq_jordanTotient`, `projPoints_prime_mul`, `projPoints_prime_pow_succ`, `primVecCRT` |
| How do the zeros enter the second-order term of fixed packets? | Only through the pole coefficient: `(log N/c) W_ρ/∫g² → m_ρ κ y_1²/(ρ(1−ρ))`, real part `> 0`; at the critical curve `c⁷ W_ρ/∫g² → K m_ρ κ y_1²/(ρ(1−ρ))`. Same for every finite window. | `tendsto_bulkLedger`, `tendsto_bulkLedger_criticalCurve`, `tendsto_sum_bulkLedger`, `re_sum_mult_div_nonneg` |
| Which directions of the complete family see an individual zero? | Only the untwisted horizon windows: there `W_ρ/(c∫g²) → κ W_ρ(H,H)`, Weil's summand of the synthesized test. Fixed conductor packets see a zero only through the pole, with positive weight; horizon windows twisted by a mean-zero periodic weight (Ramanujan sums `c_m`, `m ≥ 2`; nonprincipal characters) see no point of the strip: their twisted Riemann sums are `O(1/N)`. | `tendsto_horizonLedger`, `Wsummand_halfWeight`, `tendsto_bulkLedger`, `tendsto_twistedLedger`, `norm_twistedRiemannSum_le` |
| Is the horizon layer Weil's form? | Yes. In the iterated limit (horizon, then window of zeros) windows exhaust `κ W(H,H)`. Directly: past the critical curve (`(1+log N)/c^p → 0`) `c⁻¹⟨Wx,x⟩ → κ Q(H)`; at `c^p/log N → K_c` it is `κ Q(H)` up to `K/K_c`; for every schedule the error is `ε + K(1+log N)/c^p`. | `horizon_layer_two_sided`, `tendsto_horizon_layer_supercritical`, `horizon_layer_criticalCurve`, `horizon_window_exhaustion` |
| What is the second-order term at the critical curve (obstacles summary 2.5.4)? | On horizon blocks, exactly: `c⁻¹⟨Wx,x⟩ → κ Q(H) + (βJ/K) ∫ e^{−(β+1)y} H²` along `c^{β+1}/log N → K`, for every profile with bulk limit `s^β E₁(s) → J` (tilted spline: `β = 7`, `J = J(1)`). For every profile and every schedule with `c → ∞`, `c(log N)²/N → 0`: `c⁻¹⟨Wx,x⟩ = κ Q(H) − log N · N⁻¹ Σ_n h(log(n/N))² E₁'(cn/N) + o(1)`. | `horizon_layer_criticalCurve_of_regularBulk`, `horizon_layer_criticalCurve_exact`, `horizon_layer_sharp`, `horizon_layer_sharp_bulk`, `horizonForm_eq` |
| Which structure polarizes the second-order term? | The first-order count, through the monodromy. The aliasing density is the dilation derivative of the bulk energy, `a_φ = −(∫φ²/2) E₁'`, positive because `E₁` is antitone; its window average at the local overlaps `c e^y` is `β J(1)` times `‖H‖²_{−8}`. So the second-order term is a pencil: Weil's form plus `1/K` times a positive definite form built from `J(1)`. It is positive at every multiple iff `Q ≥ 0` on horizon windows, i.e. iff RH. On the bulk, the zero charge is the Li-type pole charge (positive per zero). | `hasDerivAt_completedShellEnergy`, `aliasLimit_eq`, `tendsto_rpow_seven_mul_completedShellEnergy_tilted`, `re_inv_mul_one_sub_pos`, `riemannHypothesis_iff_horizon_layer` |
| What is the integer of the degeneration (carrier C)? | The window index `ind₋(P_K)` of the pencil Gram matrix of a family of windows at multiple `K`: the complete family reads it (`ind₋(P_K) ≤ ind₋(G_N)` eventually); it is nondecreasing in `K` and equals Weil's index on the family for large `K`; some family has window index `≥ n` iff `ζ` has `≥ n` right zeros; it vanishes for all families and multiples iff RH. | `tendsto_horizonGram`, `eventually_hermNegIndex_pencilGram_le`, `pencilGram_eq`, `hermNegIndex_pencilGram_mono`, `eventually_hermNegIndex_pencilGram_eq`, `windowIndex_law`, `riemannHypothesis_iff_windowIndex_eq_zero` |
| What is the critical multiple of a window? | Exactly `K*(H) = 7 J(1) ‖H‖²_{−8}/(κ |Q(H)|)` for `Q(H) < 0` (`+∞` otherwise): positive below, negative above. Before the exact constant: coercive bounds `κ Q(H) + a/K ≤ · ≤ κ Q(H) + b/K`. | `criticalMultiple_exact`, `horizon_layer_coercive`, `horizon_layer_lower_criticalCurve`, `horizon_layer_criticalCurve` |
| Where does the horizon term of a conductor live? | Only at `e = 1`: `D_e(s;N) − [e=1]N^s/s → ζ(1−s)J_s(e)`. | `tendsto_conductorDirichlet_sub_horizonTerm`, `conductorDirichlet_eq` |
| Is positivity at one fixed multiple of the critical curve RH? | No: positivity at multiple `K` is `κ Q(H) ≥ −7J(1)‖H‖²_{−8}/K` on every window (sub-RH); every window with `Q(H) < 0` turns negative past `K*(H)`. RH is positivity at every multiple. | `criticalMultiple_exact`, `weilQuad_halfWeight_ge_of_horizon_nonneg`, `eventually_horizon_neg_of_weilQuad_neg` |
| What does a second-order term do to positivity? | Admissible multiples form a closed initial segment; inheritance below the critical multiple, failure above; negative directions persist. | `admissible_of_le`, `isClosed_admissible`, `admissible_mono`, `neg_persists`, `eventually_pos_of_tendsto`, `eventually_not_nonneg_of_tendsto` |
| Can the ledger or the first-order count select `ζ`? | No: the ledgers hold for every zero configuration, and the count law holds over every finite commutative ring — `#Unimod(R^k) = #ℙ^{k−1}(R)·#Rˣ`, over a local ring `#ℙ^{k−1}(R)(|R| − |𝔪|) = |R|^k − |𝔪|^k` — so over the residue rings of `𝔽_q[T]`, where RH holds, the first-order structure is the same. | statements quantified over `ZeroConfig`; `natCard_unimodular_eq`, `natCard_unimodular_local`, `natCard_projSpace_local` |
| How do the prime atoms of the jump measure enter, and what pays the creation potential `−2Σ Λ(n)/√n`? | On a window of length `A` every prime power `n > e^A` makes a jump that leaves the window and costs exactly `2Λ(n)/√n ‖H‖²`, the creation it adds: the Markov form of a window is that of level `⌊e^A⌋`. At second order the primes enter only through `Q(H)`: the correction `(7J(1)/K)‖H‖²_{−8}` is prime-free (the aliasing is paid by the Gamma factor, `ν ≈ log N/2π`). What pays the creation potential of the primes `≤ e^A` is the open sign question itself. | `primeJump_departing_eq`, `markovForm_eq_of_level`, `weilQuad_halfWeight_eq_markovForm`, `horizon_layer_criticalCurve_exact` |
| What set does `τ_x(ξ ⋆ ξ′)` count; what are Stepanov's sections over `ℤ`? (AET, ACP) | A naive height on correspondences exists for a cycle iff its orbit Hodge index holds, and for every cycle iff RH; on curves it exists iff the Frobenius is unitary. Stepanov over `ℤ` bounds `log(1/∫P)` by `ψ(n+1)` and pays the primitive `h¹` of hyperelliptic curves of every genus; the sign over `ℤ` is not produced. The degeneration adds: the first-order count is `#ℙ⁷(ℤ/m)`, zero-blind. | AET `orbitHodgeIndex_iff_exists_naiveHeight`, `riemannHypothesis_iff_forall_exists_naiveHeight`, `exists_naiveHeight_iff_unitary`, `log_inv_integral_le_psi`; LST `hyperelliptic_primitiveH1_nonneg` |
| Which lattice carries the sections of a class of degree `a`, with what metric? (LST) | A lattice whose rank grows with one fibre degree and whose Gaussian scale grows with the other; bounded rank never satisfies the Riemann inequality. On the pole plane it is the tensor square of the base, the Gamma factor its Gaussian weight. | LST `not_riemannInequality_of_bounded_rank`, `kunnethH0_add_neg`, `latticeH0_riemannRoch` |
| What is the logarithmic completion of the isotropic count, and does it commute with boost averaging? (LST) | The isotropic count of the split plane is the divisor count `Γ(σ)(2π)^{−σ}ζ(σ)²` with a double pole, not Poisson-dual; its completion is the logarithm of pole-plane Riemann–Roch. Boost averaging produces `K(s,w)ζ(s+w)ζ(s−w)`: the Euler product appears only after the boost transform. | LST `mellin_coneCount`, `not_exists_FEPair_coneCount`, `integral_splitSeries_mul_exp_eq_zeta` |
| Why `ζ` and not an Epstein function? (LST) | Definite counts are fakes; a fixed boost `|u| > 1` is a rectangular definite lattice and fake; the self-dual point has no real zeros; only the boost transform carries the Euler product. In AHD: selection enters only through `Q(H)` in the second-order term; the ledgers, the count and the aliasing constant hold for every configuration. | LST `exists_epsteinLambda_eq_zero`, `exists_boost_offLine_zero`, `epsteinLambda_one_neg`; `horizon_layer_criticalCurve_exact` |

## 7. Tools

**Developed.**
- Conductor Dirichlet polynomials: Möbius splitting through partial zeta sums, the horizon law with
  the complex Jordan totient (`conductorDirichlet_eq`, `tendsto_conductorDirichlet_sub_horizonTerm`).
- Packet calculus on the zero side: Dirichlet factors of packets, the conjugate factor
  `conj D_x(γ̄_ρ) = D_x(γ_{1−ρ})`, pole parts of packets (`dirichletPoly_packetWeights`,
  `conj_dirichletPoly_conj_gammaOf`, `tendsto_packetLedger`).
- Riemann sums of horizon profiles and the substitution `x = e^y` (`tendsto_riemannSum_Icc_complex`,
  `riemannSum_horizonProfile`, `integral_horizonProfile`).
- Ledger limits in the overlap: atom factor continuity, `∫ g(u/w)² = w∫g²`
  (`log_div_mul_bulkLedger`, `inv_mul_horizonLedger`, `integral_atomDilate_sq`).
- Critical-multiple calculus of finite quadratic forms (`TheCriticalMultiple`).
- Point counts of projective spaces over `ℤ/m`: primitive vectors, CRT, prime powers via reduction
  mod `p`, free unit action and orbit count (`TheJordanLimitCountsProjectiveSpace`).
- Kuzmin–Landau for `n^{iτ}` on a window and summation by parts with smooth weights
  (`norm_partial_cpow_le`, `norm_sum_mul_le_of_partial`, `variation_horizonWeights_le`).
- Lower bounds: the mean-value theorem from below on one window, Riemann sums of `h(log x)²/x`,
  the spline transform from below, the symbol above the archimedean horizon
  (`integral_window_ge`, `tendsto_sum_horizonWeights_sq`, `tiltedUnitSpline_lower`, `nuSymbol_ge`).
- Dyadic summation of a nonnegative tail against the sharp mean-value theorem
  (`integral_Ioi_le_of_dyadic`, `integral_window_le`, `block_bound_le`, `tsum_blocks_le`).
- The localized explicit formula for real tests and for recentred atomic tests
  (`weilQuad_eq_pole_add_symbol`, `paperFT_comp_add`, `horizonForm_eq`).
- Plancherel for horizon blocks and Poisson summation of the atom autocorrelation on `ℤ/a`, with
  linearization of `log(m/n)` on the neighbours the autocorrelation sees (`blockEnergy_eq`,
  `tsum_shellAutocorr_eq`, `abs_row_sub_le`, `abs_blockEnergy_sub_le`).
- Effective Riemann sums of horizon profiles from derivative bounds (`lipschitzWith_horizonProfile`,
  `norm_riemannSum_sub_le`) and the sharp part below the grid (`abs_lowPart_sub_le`).
- Dyadic tails with block-local weights `V + j` (`integral_aliasing_le_of_blocks`), the symbol as
  `log|τ|/2π + O(1)` (`exists_abs_mu_sub_log_le`, `abs_nuSymbol_sub_log_le`).
- Harmonic calculus of the bulk energy: `E₁' = −(2/∫φ²) a_φ` (`hasDerivAt_completedShellEnergy`).
- Integration by parts of window averages against the bulk energy, uniform rescaled limits on
  windows (`integral_windowAlias_eq`, `tendsto_window_bulk`, `integral_logProfileDeriv_mul_rpow`);
  Lipschitz and size bounds of the aliasing density (`abs_aliasDensity_sub_le`, `aliasDensity_le`).
- Equidistribution of a periodic numerator against window weights (`abs_integral_mul_numerator_sub_le`,
  `tendsto_modulated`) and Tannery over the grid harmonics (`tendsto_rpow_eight_mul_horizonAlias`).
- Gram matrices of horizon families and their limits; the window index by lower semicontinuity
  (`horizonGram_apply`, `tendsto_horizonGram`, `eventually_hermNegIndex_pencilGram_le`).
- Bounded primitives of mean-zero periodic twists and summation by parts against complex profiles
  (`abs_sum_range_le`, `norm_sum_mul_real_le`, `norm_twistedRiemannSum_le`).
- Counting unimodular vectors over finite rings (`natCard_unimodular_eq`, `natCard_unimodular_local`).

**Developed in neighbouring programmes and used here.** Néron–Tate theory and the Tate limit law on
correspondences (AET); Arakelov `h⁰` of lattices of growing rank, Künneth Riemann–Roch, the
isotropic cone count and the boost transform (LST); the Lévy–Khintchine form of Weil's functional
and its Markov splitting (RHTower `WeilMarkovPoleCapacity`); lower semicontinuity of the index
(HKT); the index bound by the right zeros (ACS); Wiener–Hopf and Szegő factorization (CDG/WD);
Stepanov over `ℤ` (AET) and over curves (LST).

**To build.**
- Uniform ledgers: explicit horizon-law remainders `O(|s|σ(e)N^{Re s−1})` with the zero-free region,
  summed over zeros up to a growing height.
- Twisted horizon windows are zero-blind (proved); their aliasing remains: Poisson summation of the
  atom autocorrelation on residue classes should identify their second-order term with the
  conductor-`m` count `β J(m)/K ‖H‖²` and no Weil's form.
- The function-field complete family and its horizon layer; Zwegers–Vignéras completions of the
  isotropic count.

## 8. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Count law: the Jordan limit counts `ℙ⁷(ℤ/m)`; Hensel towers; CRT | `jordanCoefficient_eq_projPoints`, `natCard_projPoints_mul_totient`, `projPoints_prime_mul`, `projPoints_prime_pow_succ`, `primVecCRT` | proved |
| Horizon law: only the pole conductor has a horizon term | `tendsto_conductorDirichlet_sub_horizonTerm`, `tendsto_conductorDirichlet_of_zeta_eq_zero` | proved |
| Bulk zero ledger, at every schedule and at the critical curve; positivity of the pole charge | `tendsto_bulkLedger`, `tendsto_bulkLedger_criticalCurve`, `re_inv_mul_one_sub_pos`, `tendsto_sum_bulkLedger` | proved |
| Horizon ledger: Weil summands of the synthesized test | `tendsto_horizonLedger`, `Wsummand_halfWeight`, `tendsto_horizonDirichlet` | proved |
| Twisted horizon windows are zero-blind | `tendsto_twistedLedger`, `norm_twistedRiemannSum_le`, `abs_sum_range_le` | proved |
| Exhaustion: windows of zeros give Weil's form of the synthesized test | `horizon_window_exhaustion`, `tendsto_sum_horizonLedger` | proved |
| Critical-multiple calculus | `admissible_of_le`, `isClosed_admissible`, `admissible_mono`, `neg_persists`, `eventually_pos_of_tendsto`, `eventually_not_nonneg_of_tendsto` | proved |
| Horizon layer past the critical curve = Weil's form; at it, up to `O(1/K)` | `horizon_layer_two_sided`, `tendsto_horizon_layer_supercritical`, `horizon_layer_criticalCurve` | proved |
| Exact horizon formula on the arithmetic side | `horizonForm_eq`, `weilQuad_eq_pole_add_symbol`, `weilQuad_halfWeight_eq` | proved |
| Kuzmin–Landau decay below the grid; aliasing tail above it | `norm_horizonDirichlet_le_div`, `horizonDirichlet_sq_div_le`, `integral_aliasing_le` | proved |
| The horizon criterion: RH iff every horizon block is nonnegative past the critical curve | `riemannHypothesis_iff_horizon_layer`, `riemannHypothesis_iff_halfWeight_nonneg` | equivalence |
| Coercivity: the aliasing part is at least `a log N/c⁸`; sandwich `κQ(H) + a/K ≤ · ≤ κQ(H) + b/K`; subcritical positivity | `horizon_layer_coercive`, `horizon_layer_lower_criticalCurve`, `eventually_horizon_pos_of_small_multiple`, `aliasing_lower` | proved |
| Critical multiple of a window: one multiple controls Weil's form up to `O(1/K)`; a negative window is negative at every multiple `K > K₀/(κ|Q(H)|)` | `weilQuad_halfWeight_ge_of_horizon_nonneg`, `eventually_horizon_neg_of_weilQuad_neg` | proved |
| Exact energy of a horizon block: Riemann sum of `∫H²` plus `2π𝒜_N` up to `O(c/N)` | `abs_blockEnergy_sub_le`, `blockEnergy_eq`, `tsum_shellAutocorr_eq` | proved |
| The second-order term: `c⁻¹⟨Wx,x⟩ − κQ(H) − (log N/∫φ²)𝒜_N → 0` | `horizon_layer_sharp`, `abs_lowPart_sub_le`, `abs_remainder_le`, `tendsto_log_mul_energyDefect` | proved |
| The aliasing is the dilation derivative of the bulk: `E₁' = −(2/∫φ²) a_φ` | `hasDerivAt_completedShellEnergy`, `sub_eq_integral_aliasDensity`, `horizon_layer_sharp_bulk` | proved |
| Conjecture HB, sharp form: at `c⁸/log N → K`, `c⁻¹⟨Wx,x⟩ → κQ(H) + (7J(1)/K)‖H‖²_{−8}` | `horizon_layer_criticalCurve_exact`, `tendsto_rpow_eight_mul_horizonAlias`, `aliasLimit_eq` | proved |
| Exact critical multiple `K*(H) = 7J(1)‖H‖²_{−8}/(κ|Q(H)|)` | `criticalMultiple_exact` | proved |
| The bulk determines the second order: `s^β E₁ → J` gives `κQ(H) + (βJ/K)‖H‖²_{−(β+1)}` | `horizon_layer_criticalCurve_of_regularBulk`, `tendsto_rpow_mul_horizonAlias_of_regularBulk`, `integral_windowAlias_eq`, `abs_aliasDensity_sub_le` | proved |
| Calibration: the count law over every finite ring; Hensel law over every finite local ring | `natCard_unimodular_eq`, `natCard_unimodular_local`, `natCard_projSpace_local` | proved |
| The window index: Gram matrices converge to the pencil; the index is read by the family and bounded by the right zeros | `tendsto_horizonGram`, `pencilGram_isHermitian`, `eventually_hermNegIndex_pencilGram_le`, `hermNegIndex_pencilGram_le_offLineCount` | proved |
| The window index law: `P_K = κW(H) + (βJ/K)A(H)`, `A ⪰ 0`; monotone in `K`; Weil's index for large `K`; index `≥ n` on some family iff `≥ n` right zeros | `pencilGram_eq`, `hermQuad_aliasGram_nonneg`, `hermNegIndex_pencilGram_mono`, `eventually_hermNegIndex_pencilGram_eq`, `windowIndex_law`, `riemannHypothesis_iff_windowIndex_eq_zero` | proved |
| The primes of a window: departing jumps pay their creation; Markov form at level `⌊e^A⌋` | `primeJump_departing_eq`, `markovForm_eq_of_level`, `weilQuad_halfWeight_eq_markovForm` | proved |

## 9. Open research topics

1. **The window index as a counting function.** Proved: monotone in `K`, Weil's index for large
   `K`, exhaustion of the right zeros. Open: the jump multiples of a family (its critical multiples,
   the generalized eigenvalues of `κW(H)` against `A(H)`) and the growth of the index with the window
   width `A` (Landau–Widom: the Shannon number plus the resolved-zero defect).
2. **Bulk second order.** The collective `1/log N` term of fixed packets (the high zeros, read on the
   arithmetic side through primes in progressions to the moduli `e e'`).
3. **Uniform bulk ledger.** All zeros of height `≤ N^{1/2−ε}` together contribute `o(c/log N)` to every
   pole-orthogonal fixed packet (horizon-law remainders, zero-free region, `Σ m_ρ/(1 + γ²) < ∞`).
4. **Count past first order.** A count (cardinality or log-count) for the second-order term, or the
   classification of counts with a Poisson-type duality that read the test component.
5. **Prime atoms in the jump measure.** The primes beyond a window pay their own creation potential
   (proved); a count that pays the creation potential of the primes `≤ e^A` acting on a window, and
   the count of the first Hecke graph `T₂`, are open.
6. **The integer**: a sectorial multiplier at logarithmic resolution (WD).
7. **Calibration** over `𝔽_q(T)`: the count law is proved over every finite ring; the function-field
   complete family, its horizon layer and its second-order term (where the sign is known) are open.

## 10. Traps

| Trap | Truth |
|---|---|
| The rescaled limit polarizes the edge | It is a point count, zero-blind; zeros enter at the quantum `1/log N` |
| Fixed packets will see an off-line zero at the critical curve | A point of the strip enters a fixed packet only through the pole, with positive real weight |
| The Ramanujan basis reads the horizon | Its packets are smooth in `log n`; only the pole packet has a horizon term |
| The second-order term is one more estimate | On the zero side it is an identity per zero; on the arithmetic side it is Weil's form of the synthesized test plus a positive-order aliasing term |
| Horizon blocks are positive at fixed overlap, so they cannot carry RH | At fixed overlap the aliasing energy `≍ c^{−β} log N` dominates; past the critical curve it vanishes and the block is Weil's form |
| A count built from the base sees the sign | Bidegree counts are constant on primitive classes (LST); the first-order count is zero-blind |
| A trace identity is positivity | `1 − P − P̂` is negative on time-limited vectors |
| Local positivity glues | One rank-one gluing creates `M(N)` and one negative square |
| Soft laws select | Ledgers and counts hold on every configuration and every quotient |
| The aliasing is an error term to be estimated | It is the monodromy derivative of the bulk count, exactly; it is positive and computable |
| The sharp constant depends on the zeros | It is `β J(1)`, a property of the profile and the bulk; the zeros enter only through `Q(H)` |

## 11. Context

| Neighbour | Interface |
|---|---|
| ArithmeticDegenerationTheory | rescaled limit, monodromy, weight strings, inheritance radius, Redheffer gluing; AHD reads its Jordan form as a point count |
| RenormalizedArithmeticPotentialTheory | complete Weil matrix, packets, Möbius horizons (`mobiusHorizon`), Li charge of the pole mode |
| SpacingScaleHarmonicAnalysis | atomic dictionary: `dirichletPoly`, `Wsummand_atomicTest`, `paperFT_atomDilate` |
| EdgeHodgeTheory | edge logic, windows (`sinc_window_opens`), crossings, integer readings |
| HodgeTheoryWithoutVarieties | stars, gcd strata, cross-conductor deviation bound |
| ArithmeticOrientationGeometry, ArithmeticCastelnuovoSeveri | scaling datum, configurations, `weilQuad_eq_zetaW`, golden fake |
| ArithmeticEffectivityTheory | naive heights, Tate limit law, Stepanov over `ℤ` |
| LatticeSectionTheory | lattice `h⁰`, Künneth RR, jump counts |
| AdelicKreinGeometry | glued archimedean state, index `κ + 1` |
| ConjugateDiagonalGeometry (WD) | window index, Szegő factorization |
| RHTower | partial zeta sums (`zetaStripError`), Euler–Maclaurin carriers, summability of Weil series, the Markov splitting of Weil's form (`weil_eq_markovForm_add_pole`), the symbol bounds `mu_ge_log`, `abs_PX_le` |
| RenormalizedArithmeticPotentialTheory (completed shells) | the completed shell energy `E₁`, its increment law and positive Fourier series, Poisson on the lattice `ℤ/s` (`hasSum_shellSpectrum_int`): AHD differentiates it (`E₁' = −(2/∫φ²) a_φ`) |
| EffectiveArithmeticHodgeTheory, HeckeKreinToeplitz | polarization of `weilQuad` on real tests, lower semicontinuity of the index, schedules reaching the index |
| ArithmeticCastelnuovoSeveri | `weilGram`, the index bound by the right zeros (`negIndex_weilGram_le_offLineCount`) |

## 12. Success criteria

| Criterion | Status |
|---|---|
| First-order structure identified as a count | proved: `#ℙ⁷(ℤ/m)` |
| How zeros enter the second order, packets that see a zero classified | proved per zero and per window: bulk (pole only, positive), untwisted horizon windows (Weil summands), twisted horizon windows (none) |
| Second-order term at the critical curve identified | horizon layer: exactly `κ Q(H) + (βJ/K)‖H‖²_{−(β+1)}` for every profile with bulk limit `s^βE₁ → J` (proved; tilted spline `7J(1)`); bulk second order: open |
| A count reading the primes inside the jump measure, creation potential paid on a window | the primes beyond the window pay their own creation (proved); a count for the primes inside it: open (corpus foothold on prime-free cycles) |
| Gluing theorem with exactly one negative square | AKG `κ + 1`; zero ledger of the bulk is a positive pole gluing |
| An integer with a structural bound | the window index `ind₋(P_K)`: read by the complete family, monotone in the multiple, its supremum over families is the number of right zeros, RH iff it vanishes (proved); a source-defined bound forcing it to `0` (WD's sectorial multiplier): open |
| Calibrations separating `ζ` from the fakes | negative result: ledgers, the count law (over every finite ring, so over `𝔽_q[T]`) and the aliasing constant carry no selection; selection enters only through `Q(H)` |

## 13. What counts as a contribution

A contribution is an unconditional Lean theorem in this folder, wired into the umbrella, that
meets at least one criterion below and says which kind of statement it is (identity, inherited
polarization, integer invariant, estimate with its regime, equivalence, or no-go with its positive
survivor).

1. `h⁰` from arithmetic counts; `h¹ ≥ 0` because it is a dimension, a cardinality or a log-count.
2. A Riemann–Roch identity at every degree by a Poisson-type duality on lattices of growing rank.
3. Primitive `h¹` of a test class `= ½W(f, f)`; for graph classes a height equal to the Lefschetz
   trace up to bounded error.
4. A degeneration statement: rescaled limits, second-order terms, ledgers, inheritance, critical
   multiples.
5. Calibrations over curves, on prime-free cycles, on the fakes.
6. It avoids the proved no-gos: cones, bidegree counts, fixed rank, definite counts, Siegel
   majorants at a fixed boost, ordinary Poisson pairs for the isotropic count, semilocal positive
   carriers, trace carriers `1 − P − P̂`, separable gluing, free deformation.
7. Selection: it fails for the golden fake, prime flips and Epstein lattices beyond the self-dual
   point, and reproduces Weil and Stepanov over `𝔽_q`.
8. Gluing: global, one negative square at the pole, distinct primes coupled through `∞`.
9. Consistency with quantization: the defect it forces to zero is the window index.

Restatements of neighbouring programmes and numerical certificates do not count.

## 14. Big picture

The complete Weil family degenerates along the resolution axis. Its first-order structure is a
count: after rescaling, the energy of conductor `m` is `J(1)` times the number of points of `ℙ⁷`
over `ℤ/m`, weight strings are Hensel towers and the tensor law is the Chinese remainder theorem.
This is the arithmetic analogue of a nilpotent orbit, and its polarization is positive for the
reason Weil's intersection numbers are: it is a cardinality.

The zeros enter at second order, and the zero side says exactly where. A fixed conductor packet
reads a zero through its Dirichlet polynomial, whose horizon terms cancel by `Σ_{d∣e} μ(e/d) = 0`
unless the conductor is the pole; every point of the strip is therefore a positive rank-one charge
on the pole of the bulk, and no fixed packet can see an off-line zero. A horizon block reads a zero
through Weil's summand of the test it synthesizes, and windows of zeros exhaust Weil's form; a
horizon block twisted by a Ramanujan sum or a character reads no zero at all.

On the arithmetic side the horizon layer is computed exactly. Below the atom grid the block is the
Riemann sum of the synthesized test; its total energy is, by Plancherel and Poisson summation on the
atom grid, that Riemann sum plus the aliasing of the grid harmonics; above the grid the symbol is
`log N/2π`. The aliasing that a horizon block pays at depth `y` is the dilation derivative of the
bulk energy at the local overlap `c e^y`. So the second-order term of the degeneration on a horizon
window is Weil's form of the synthesized test plus the monodromy derivative of the first-order
count: for every profile with bulk limit `s^β E₁(s) → J` it is exactly
`κ Q(H) + (β J/K) ∫ e^{−(β+1)y} H²` at the multiple `K` of the critical curve (`7 J(1)` for the tilted
spline). This pencil is polarized at every multiple exactly when Weil's form is
nonnegative on horizon windows, which is RH; every window with `Q(H) < 0` has the finite critical
multiple `β J ‖H‖²_{−(β+1)}/(κ|Q(H)|)`. On families of windows the negative index of the pencil is
read by the complete family, grows with the multiple, and its supremum over families is exactly the
number of right zeros. The count of the first
order pays the second order at small multiples and nothing at large ones. What the field has not yet built is a mechanism that forces
the sign of `Q` on horizon windows: a count of the second order that sees the zeros.
