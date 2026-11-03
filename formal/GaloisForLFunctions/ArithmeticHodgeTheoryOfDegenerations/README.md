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

For the tilted spline the next term resolves equality. Put `M_j = ∫e^{−jy}H²`,
`B = 7J(1)M_8` and `D = tiltedNextAliasCoefficient > 0`. If `K_N = c_N⁸/log N → K > 0`,
then `c_N²(E_N − κ_φQ(H) − B/K_N) → −DM_10/K`.
On the canonical clock `c_N = max(1,(K log N)^{1/8})`, every nonzero window has eventually
positive energy exactly when its leading pencil is positive; a zero pencil has eventually
negative energy (`canonicalCriticalClock_phase_diagram`). At equality, the clocks
`max(1,c_N+d/c_N)` instead give scaled limit `−(8Bd+DM_10)/K`; two explicit choices of `d`
give opposite signs at the same limiting ratio (`critical_ratio_equality_admits_both_signs`).

On the twisted directions the count reappears at second order. The window twisted by the
conductor-two Ramanujan sum `c₂(n) = (−1)^n` has no Weil term, and at `c⁸ = K log N`

**c⁻¹⟨Wx, x⟩ → (7 J(2)/K) ∫ e^{−8y} H(y)² dy,   J(2) = J(1) · #ℙ⁷(𝔽₂) = 255 J(1):**

the second-order term of the conductor-two window is the first-order count of conductor two. The
same holds at every prime: the window twisted by `c_p(n) = p·1_{p|n} − 1` has second-order term
`7 (p − 1) J(p)/K ∫ e^{−8y} H²`, with `(p − 1) J(p) = J(1) φ(p) #ℙ⁷(𝔽_p)` and `p − 1` the mass of `c_p`;
for every `d ≥ 2` the window twisted by `d·1_{d|n} − 1` carries `(7/K) Σ_{e|d, e>1} φ(e) J(e)`, the
conductor counts of the divisors of `d`; and for every conductor `m ≥ 2` the Ramanujan window
`c_m(n) h/√n` carries exactly

**c⁻¹⟨Wx, x⟩ → (7 φ(m) J(m)/K) ∫ e^{−8y} H(y)² dy,   φ(m) J(m) = J(1) φ(m) #ℙ⁷(ℤ/m):**

the count of the first order at every conductor. On a Ramanujan expansion `χ = Σ_m a_m c_m` the
second-order form is diagonal: `→ (7/K) Σ_m a_m² φ(m) J(m) ‖H‖²_{−8}` (Parseval for the count). More
generally a mean-zero periodic twist carries the Ramanujan expansion of its autocorrelation
evaluated on the counts: if `C_χ = Σ_m b_m c_m`, its window has `(7/K) Σ_m b_m φ(m) J(m) ‖H‖²_{−8}`;
the Legendre symbol of `p` has `C = c_p/p` and carries the conductor-`p` count with weight `1/p`.
For every mean-zero `M`-periodic twist, whatever its autocorrelation, the energy is its spectrum:
the mode `k/M` meets the harmonics of the atom grid at the shifted frequencies `j + k/M`, and the
window carries

**c⁻¹⟨Wx, x⟩ → (β A_φ/(K ∫φ²)) Σ_{0<k<M} |χ̂(k)|² (ζ(β+1, k/M) + ζ(β+1, 1 − k/M)) ‖H‖²_{−(β+1)},**

`A_φ = lim x^β T(x)` the tail constant, `ζ(s, u) = Σ_{n≥0} (n + u)^{−s}` the Hurwitz sum. Since
`J = (2A_φ/∫φ²) ζ(β+1)`, the coefficient is `βJ/K` times the **spectral constant**
`Σ_k |χ̂(k)|² (ζ(β+1, k/M) + ζ(β+1, 1 − k/M))/(2ζ(β+1))`; for `c_m` the spectrum is the indicator of
the units mod `m` and the spectral constant is the Jordan totient `J_{β+1}(m)`. The spectral sum is
at least `2 M⁻¹ Σ χ²` (Parseval), so every nonzero twist is coercive at second order.

The conductors do not interact: an untwisted window `x = h/√n` and a window `y = χ(n) g/√n` twisted
by a Ramanujan expansion `χ = Σ_{m ≥ 2} a_m c_m` are orthogonal at second order, so

**c⁻¹⟨W(x+y), x+y⟩ → κ_φ Q(H) + (7 J(1)/K) ‖H‖²_{−8} + (7/K) Σ_m a_m² φ(m) J(m) ‖G‖²_{−8}:**

the second-order form is block-diagonal by conductor, Weil's form living only on the conductor-one
block and the conductor-`m` count on the conductor-`m` block.

Inside a conductor the characters refine the count. For a primitive character `ψ` mod `q` the
spectrum of `Re(cψ)` is read by the Gauss sum, and the second order is the unit count corrected by
an `L`-value of the squared character,

**(βA_φ/(K ∫φ²)) (|c|² ζ(β+1) J_{β+1}(q)/q + q^{β−1} Re(c² ψ̄(−1) τ(ψ)² L(β+1, ψ̄²))) ‖H‖²_{−(β+1)},**

so the circle of twists `Re(e^{iθ}ψ)` sweeps the unit count `± q^{β}‖L(β+1, ψ̄²)‖/q`; characters of
opposite parity are orthogonal and characters of equal parity couple through `L(β+1, ψ̄₁ψ₂)` and
`L(β+1, ψ̄₁ψ̄₂)`. A single frequency `α`, rational or not (`2α ∉ ℤ`), carries the Hurwitz form
`½(ζ(β+1, u) + ζ(β+1, 1 − u))` of `u = {α}`: the form a Frobenius angle `u` carries in the rescaled
limit of a curve over `𝔽_q`; distinct frequencies are orthogonal, so the horizon layer is graded by
frequency as it is by conductor.

Where the sign of the second order is controlled, positivity passes to the nearby fibres
(mechanism B): on every independent family twisted by a nonzero periodic or trigonometric twist
(any twist with a positive scalar second order), on untwisted
windows of length `≤ 3/5`, on the cosh hyperplane of the first-prime windows (length
`< log 2 + 1/50`, where the window index is at most one), and on windows of every length below the
aperture-independent multiple `K₀ = βJ/(κC(β+1))`, for `β > 0`, where
`C(p) = |Ω(0)| + 2Σ Λ(n)n^{−(p+1)/2} + 1/(p+1) + 1/(p−1)`.
The weighted floor `Q(H) ≥ −C(p)∫e^{−py}H²` holds on every window for `p > 1`.
Each fixed family inherits positivity below this same multiple; its starting index may depend on
the family. RH is inheritance at every multiple on every window.

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
| Conductor twists | `altSign`, `primeTwist` | `(−1)^n = c₂(n)`; `d·1_{d|n} − 1` (`= c_p` for `d = p` prime) |
| Recentred block, symbol integrand for arbitrary weights | `centredAtomicTest`, `symbolW`, `aliasIntegrandW` | `T_N(u + log N)`; `‖φ̂(wτ)‖² |D_x|²/N ν` |
| Archimedean horizon | `archHorizon` | `τ₀(a)` beyond which the symbol of `[−a, a]` is nonnegative |
| Ramanujan twist, Ramanujan expansion, quadratic character | `ramTwist`, `ramComb`, `legTwist` | `c_m(n) = Σ_{de=m} μ(d) e [e ∣ n]`; `Σ_{m∈S} a_m c_m`; `(n/p)` |
| Fourier coefficient, power of a mode, spectral sum | `twistCoeff`, `twistPower`, `twistSpectralSum` | `S_k = Σ_{n<M} χ(n) e(kn/M)`; `|χ̂(k)|² = |S_k|²/M²`; `Σ_{0<k<M} |χ̂(k)|² (ζ(s, k/M) + ζ(s, 1 − k/M))` |
| Cosh moment of a window, cosh hyperplane of a family | `coshMoment`, `coshHyperplane` | `ℓ(h) = ∫ H(u − A/2) cosh(u/2)`, `H = e^{y/2}h`; `{x : Σ_i ℓ(h_i) x_i = 0}` |
| Character twist, `L`-series of the squared character | `charTwist`, `charSqL` | `n ↦ Re(cψ(n))`; `Σ_j ψ̄(j)² j^{−s}` |
| Cosine twist of frequency `a/M`; frequency twist | `cosTwist`; `freqTwist`, `freqAlias` | `n ↦ cos(2πan/M)`; `n ↦ cos(2πnα)`, `½(𝒜^{(u)} + 𝒜^{(1−u)})` |
| Trigonometric twist, its oscillation constant and aliasing | `trigTwist`, `trigOsc`, `trigAlias` | `Σ_k a_k cos(2πnα_k)`; the bound on the off-diagonal partial sums; `Σ_k a_k² · freqAlias` |
| Cross power, polarized Weil form, Dirichlet series of a sequence | `crossPower`, `weilCross`, `dirichletL` | `Re(S_j S̄'_j)/M²`; `(Q(f+g) − Q(f−g))/4`; `Σ_j f(j) j^{−s}` |
| Lag series of an eigenvalue, atom energy of a curve | `lagSeries`, `curveAtomEnergy` | `Φ_β(w) = Σ_j w G(j log q/w) β^j`; `E(w) = log q Σ_m w G(m log q/w) t_{|m|}` |
| Fractional Frobenius angle, curve bulk, Hurwitz form of the angles | `frobeniusShift`, `curveBulk`, `curveHurwitzForm` | `{arg β/2π}`; `Σ_i |Σ x_k β_i^k|² (E_{u_i} + E_{1−u_i})`; the same with `ζ(s, ·)` |
| Lattice test of a curve | `curveLatticeTest` | `Σ_{k<n} x_k g_w(· − k log q)`: atoms of width `w` on the norm lattice |
| Shifted density, shifted bulk, Hurwitz sum | `twistDensity`, `twistBulk`, `hurwitzSum` | `D_u(s) = Σ_{n≥0} |φ̂(2πs(n+u))|²`; `E_u(s) = Σ T(s(n+u))/(n+u)`, `E_u' = −D_u`; `ζ(k, u) = Σ (n+u)^{−k}` |
| Window average of a density, spectral aliasing of a twist | `densityAlias`, `twistAlias` | `N⁻¹ Σ_n h(log(n/N))² a(cn/N)`; `Σ_k |χ̂(k)|² (𝒜^{(k/M)} + 𝒜^{(1−k/M)})` |
| Period mean, periodic extension, autocorrelation | `periodMean`, `periodicExt`, `autoCorr` | `M⁻¹Σ_{r<M} ψ(r)`; `χ(δ mod M)`; `C_χ(δ) = M⁻¹Σ_r χ(r)χ(r+δ)` |
| Aliasing of a Ramanujan window | `ramAlias` | `Σ_{de=m} μ(d) 𝒜_N(c/e)` |
| Polarized pole part, product window | `poleRe`, `prodWindow`, `invWindow` | `Re(Ŵ(i/2) + Ŵ(−i/2))`; `h(log x) g(log x)`; `h(log x)²/x` |
| Mixed and twisted Gram matrices and their limits | `mixedGram`, `twistGram`, `mixedLimitGram`, `twistLimitGram` | Gram matrices of families of untwisted and twisted blocks; `fromBlocks P_K 0 0 (Λ A(G))` |
| Relative matrix and eigenvalues | `relMatrix`, `relEigenvalues` | `A^{−1/2} W A^{−1/2}` and its spectrum; jump multiples `βJ/(−λ_i)` |
| Window of a test | `windowOfTest` | `e^{−y/2} r(y + a)`: a test on `[−a, a]` as a window on `[−2a, 0]` |
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
- **Conductor** of a twisted window: the conductor of its Ramanujan twist; the **Ramanujan
  spectrum** of a periodic twist: the coefficients `b_m` of its autocorrelation `C_χ = Σ b_m c_m`.
- **Offset**: `δ = m − n` in a row of a block; for a periodic twist the double sum is organized by
  offsets, each offset contributing the autocorrelation `C_χ(δ)`.
- **Spectrum** of a periodic twist: the powers `|χ̂(k)|²` of its modes `k/M`; its **spectral
  constant** at exponent `s`: `Σ_k |χ̂(k)|² (ζ(s, k/M) + ζ(s, 1 − k/M))/(2ζ(s))`, the factor by which
  its second-order term exceeds the untwisted aliasing coefficient `βJ/K`.
- **Mixed family**: untwisted windows together with twisted windows; its **graded limit** is the
  block-diagonal second-order Gram matrix.
- **Jump multiple** of a family: a multiple at which the window index jumps, `βJ/(−λ_i)`.
- **Resolved zero** at level `a`: a right zero below the Nyquist height `πe^{2a−3/4}` that the
  level-`a` Weil form sees as a negative square.
- **Killing potential** of the pencil: the aliasing part `(βJ/K) e^{−(β+1)y}`, the zero-order
  term added to Weil's (Lévy–Khintchine) form on a window; mechanism B is positivity of the
  Schrödinger form `κQ + V_K`, RH its positivity at `V = 0`; the **uniform multiple**
  `K₀ = βJ/(κC(β+1))`, for `β > 0`, is independent of aperture because the full
  exponential weight bounds both the prime correlations and the pole moments.
- **Cosh hyperplane** of a family of windows: the coefficient vectors whose synthesized test has
  vanishing centred cosh moment; there Weil's form is coercive below `log 2 + 1/50`.
- **Cross spectrum** of two twists: `Re(S_j S̄'_j)/M²`; its Dirichlet series is their polarized
  second order. **Parity** of a character `ψ`: the sign `ψ(−1)`.
- **Lag series** of an eigenvalue `β` of a curve: `Φ_β(w) = Σ_j w G(j log q/w) β^j`, the factor by
  which `β` enters the lattice Gram matrix at width `w`.

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
  rank-one gluing at the pole; distinct conductors are never coupled by a zero. Uniformly: at a
  zero, Euler–Maclaurin of order `m` bounds `D_e(ρ;N) − [e=1]N^ρ/ρ` by `C_{e,m} N^{β−1}` as long as
  `|ρ| ≤ N^{1−1/(2m+2)}`; with the zero count, all zeros of height `≤ N^θ`, `θ < 1`, together give
  exactly `κ y_1² Σ_ρ m_ρ/(ρ(1−ρ)) = κ y_1² (2 + γ − log 4π)`.
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
- **Twisted windows.** A mean-zero `m`-periodic twist has a bounded primitive; summation by parts
  against the Lipschitz profile `h(log x) x^{s−1}` makes every twisted Riemann sum `O(1/N)` on
  `0 ≤ Re s ≤ 2`. Hence a twisted window sees no point of the strip, and its transform is `O(1/N)`
  on the low frequencies and at the pole values. Beyond the archimedean horizon the symbol is
  nonnegative, so the twisted window is positive at every resolution up to `O(N^{−2})`. Its mass
  is `Σ x_n² → μ_χ ∫ h²` (the twist `χ² − μ_χ` has mean zero), so the mean-value theorem from
  below puts `a log N/c⁸` on one dyadic window above the grid: the second-order term of a twisted
  window is at least `a/K` at the multiple `K` of the critical curve.
- **The conductor-two window.** For `x_n = (−1)^n h(log(n/N))/√n` the rows of Plancherel's
  double sum carry the sign `(−1)^{m−n}`, and Poisson summation on `ℤ/a` and `2ℤ/a` gives
  `Σ_j (−1)^j G(j/a) = 2a(a_φ(a/2) − a_φ(a))`: the energy is `2π(𝒜_N(c/2) − 𝒜_N(c))` with no
  Riemann-sum main term. Below the first resonance `|τ| ≤ (π/2) N e^{−A}` the phase increments of
  `(−1)^n n^{iτ}` stay in `[1/4, 1/2]` (Kuzmin–Landau), so the low frequencies cost `O(log N/N)`;
  above it the dyadic tail costs `O(c^{−p})`. Hence `c⁻¹⟨Wx,x⟩ − (log N/∫φ²)(𝒜_N(c/2) − 𝒜_N(c)) → 0`,
  and the bulk limit at the overlaps `c` and `c/2` gives `(2^{β+1} − 1)βJ/K ‖H‖²_{−(β+1)}`.
- **The prime window.** For `c_p = p·1_{p|n} − 1` the twisted double sum splits into a block on
  `pℤ`, two mixed blocks and the full block; using the symmetry of the autocorrelation every row is
  centred at its own index, so the lattice sums are Poisson sums on `ℤ/(a/p)` and `ℤ/a`; sums over
  `pℤ` of Lipschitz profiles equidistribute. The energy is `2π(𝒜_N(c/p) − 𝒜_N(c))`. Below the
  first resonance, Kuzmin–Landau on `n` and on the cofactor `n/p` together with the twisted Riemann
  sums below `√N` leave `O(N^{−1/2})`. Hence the second-order term `(p^{β+1} − 1)βJ/K ‖H‖²`.
- **Periodic twists and their autocorrelation.** Linearize each row entrywise to
  `y_n Σ_{|δ|≤⌈c⌉} χ(n+δ) G(δ/a_n)`; for each offset `δ` the sequence `χ(n)χ(n+δ)` is periodic and the
  profile `h(log x)²/x · G(δ/(cx))` is Lipschitz uniformly in `δ`, so the sum over `n` equidistributes
  to the autocorrelation `C_χ(δ)`. No Poisson summation on shifted lattices is needed. For the
  Ramanujan sum `C = c_m` (roots of unity), whose divisor expansion turns the offset sum into Poisson
  sums on the lattices `eℤ`, `e | m`; `Σ μ = 0` removes the zero modes.
- **The conductor grading.** Polarize the sharp forms of an untwisted block `x` and a prime block
  `y`. Each piece of the polarized form is a mixed product with one prime factor: the pole values
  pair a Riemann sum with a twisted Riemann sum; below the first resonance AM–GM with weight
  `N^{1/4}` pairs the untwisted domination `C/(1 + τ²)` with the quiet energy `O(N^{−1/2})` of `y`;
  the mixed energy is `(2π/c) Σ_n y_n Σ_m x_m G_{mn}`, whose untwisted rows are smooth, so `c_p`
  integrates to `0` against the product window by equidistribution on `pℤ`. With the
  parallelogram law the limit of `x + y` is the sum of the two blocks.
- **Frequencies without periodicity.** For `cos(2πnα)` the energy law equidistributes the
  oscillation `½cos(2π(2n + δ)α)` of `χ(n)χ(n+δ)` by summation by parts (partial sums
  `≤ 1/|sin 2πα|`), the pole terms use the bounded primitive `≤ 1/|sin πα|`, and the quiet region is
  Kuzmin–Landau for the phases `(n₀ + j)α + τ log(n₀ + j)/2π`, whose increments stay in
  `[(1 − u)/2, 1 − u]` mod `1`: one frequency has one resonance and no `1/τ` loss.
- **Characters and Gauss sums.** For `ψ` primitive mod `q`, `Σ_b ψ(b) e(kb/q) = ψ̄(k) τ(ψ)` and
  conjugation gives `Σ_b ψ̄(b) e(kb/q) = ψ(−1)ψ(k) τ̄`, so the mode `k/q` of `Re ψ` has power
  `[(k,q)=1]/(2q) + Re(ψ̄(−1)ψ̄(k)²τ²)/(2q²)`; with `|τ|² = q` the spectral Dirichlet series splits
  into the unit count and `Re(ψ̄(−1)τ² L(s, ψ̄²))`: the phase of the spectrum is a character, and
  summing it against `j^{−s}` produces the `L`-function of its square.
- **An aperture-independent floor.** With `M_p = ∫e^{−py}H²`, weighted Young gives
  `|∫H(y)H(y+t)| ≤ e^{−pt/2}M_p`. Thus the prime debit is bounded by the convergent
  series `2ΣΛ(n)n^{−(p+1)/2}M_p`, while weighted Cauchy–Schwarz bounds the two pole moments
  by `M_p/(p±1)`. The archimedean jump energy is nonnegative. Hence `Q ≥ −C(p)M_p`
  for `p > 1`, and `P_K ≥ (βJ/K − κC(β+1))A(H)` on every aperture.
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
read through the degeneration, and RH is its vanishing. Structural bounds hold unconditionally
where Weil's form is controlled: the index vanishes below the uniform multiple
`K₀ = βJ/(κC(β+1))` on windows of every length, vanishes on windows of length `≤ 3/5`,
and is at most one on smooth windows of length `< log 2 + 1/50`, where the pencil is positive
definite on the cosh hyperplane (codimension one).

**G. Gluing.** One rank-one gluing at the pole creates the Mertens function (Redheffer, ADT) and
the one extra negative square (`κ + 1`, AKG). The zero ledger of the bulk is itself a rank-one
gluing at the pole, of positive sign.

**Cal. Calibration.** The ledger theorems hold for every zero configuration: they carry no
selection. The count law holds over every finite commutative ring — units act freely on unimodular
vectors, and over a local ring `#ℙ^{k−1}(R)(|R| − |𝔪|) = |R|^k − |𝔪|^k` — so the first-order structure
is the same over the residue rings of `ℤ` and of `𝔽_q[T]`. The aliasing constant `βJ` is a property
of the profile and the bulk. Selection enters the degeneration only through Weil's form `Q(H)` of
the untwisted horizon windows; twisted horizon windows are zero-blind. Over `𝔽_q` the type of the
degeneration selects: a pure curve degenerates completely, while for one Frobenius orbit
`β, β⁻¹` the dilation acts by a scalar on the span Gram matrix, so the golden fake keeps one
negative square at every width and its scale grows like `w e^{εw}`.

## 6. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| What is the first-order structure of the degeneration, and why is it polarized? | The point count of projective space: `J(m) = J(1) #ℙ⁷(ℤ/m)`, `#ℙ^{k−1}(ℤ/m) φ(m) = J_k(m)`. Weight strings are Hensel towers, the tensor law is CRT. It is positive because it is a cardinality. | `jordanCoefficient_eq_projPoints`, `natCard_projPoints_mul_totient`, `natCard_primVec_eq_jordanTotient`, `projPoints_prime_mul`, `projPoints_prime_pow_succ`, `primVecCRT` |
| How do the zeros enter the second-order term of fixed packets? | Only through the pole coefficient: `(log N/c) W_ρ/∫g² → m_ρ κ y_1²/(ρ(1−ρ))`, real part `> 0`; at the critical curve `c⁷ W_ρ/∫g² → K m_ρ κ y_1²/(ρ(1−ρ))`. Same for every finite window. | `tendsto_bulkLedger`, `tendsto_bulkLedger_criticalCurve`, `tendsto_sum_bulkLedger`, `re_sum_mult_div_nonneg` |
| What do the low zeros give a packet carrying the pole? | Exactly the archimedean genus, up to every height `N^θ`, `θ < 1` (`tendsto_sum_bulkLedger_belowResolution`, Euler–Maclaurin at order `m ≥ 1/(1−θ)` makes the remainders uniform in `ρ`): the zeros of height `≤ N^θ`, `θ < 2/3` in the second-order version, together contribute `(c/log N) κ y_1² Σ_ρ m_ρ/(ρ(1−ρ)) + o(c/log N)`, and `Σ_ρ m_ρ/(ρ(1−ρ)) = 2 + γ − log 4π = 2λ₁ > 0` (Hadamard product of `ξ`). Per zero the error is `m_ρ(C₁c/N + C₂(|y_1| + |ρ|²/N)/N)`: the horizon terms multiply to `y_1² N/(ρ(1−ρ))`, the remainders are explicit. | `tendsto_sum_bulkLedger_lowZeros_genus`, `tendsto_sum_bulkLedger_lowZeros_genus_rpow`, `tendsto_sum_bulkLedger_lowZeros_pole`, `tsum_mult_div_zero_mul_one_sub_eq`, `norm_log_div_mul_bulkLedger_sub_le` |
| Do the low zeros, all together, enter a pole-free packet? | No, uniformly up to height `N^θ`, `θ < 2/3`: at a zero, second-order Euler–Maclaurin gives `‖D_e(ρ;N) − [e=1]N^ρ/ρ‖ ≤ 4e³(5+|ρ|)N^{β−1}` with no loss near the edges of the strip, so each zero contributes `≤ C m_ρ(6+|ρ|)²/N²` to `(log N/c)W/∫g²`; the zero count `#{|γ| ≤ T} ≪ T log T` and `m_ρ ≪ log|γ|` sum this to `O(T³ log² T/N²)`. The bulk away from the pole sees zeros only near the resolution height `N/c`. | `tendsto_sum_bulkLedger_lowZeros`, `tendsto_sum_bulkLedger_lowZeros_rpow`, `norm_log_div_mul_bulkLedger_le`, `norm_conductorDirichlet_sub_horizonTerm_le`, `norm_zetaStripError_le` |
| Which directions of the complete family see an individual zero? | Only the untwisted horizon windows: there `W_ρ/(c∫g²) → κ W_ρ(H,H)`, Weil's summand of the synthesized test. Fixed conductor packets see a zero only through the pole, with positive weight; horizon windows twisted by a mean-zero periodic weight (Ramanujan sums `c_m`, `m ≥ 2`; nonprincipal characters) see no point of the strip: their twisted Riemann sums are `O(1/N)`. | `tendsto_horizonLedger`, `Wsummand_halfWeight`, `tendsto_bulkLedger`, `tendsto_twistedLedger`, `norm_twistedRiemannSum_le` |
| What is the second-order term of a general twisted window? | The Ramanujan expansion of its autocorrelation evaluated on the counts: if `C_χ = Σ_m b_m c_m` (an even autocorrelation), the window has `(Σ_m b_m J_{β+1}(m)) βJ/K ‖H‖²`. Every mean-zero periodic block is quiet below `N e^{−A}/M` (Kuzmin–Landau on residue classes with a real shift). The Legendre symbol of `p` has autocorrelation `c_p/p` (Jacobsthal), so its window carries the conductor-`p` count with weight `1/p`. | `evenTwist_layer_criticalCurve_of_regularBulk`, `legendre_layer_criticalCurve_of_regularBulk`, `autoCorr_legTwist`, `exists_periodicLow_energy_le` |
| What is the second-order term of an arbitrary periodic twist (autocorrelation not a Ramanujan expansion)? | Its spectrum paired with Hurwitz constants: the discrete Fourier transform diagonalizes the autocorrelation, `Σ_{k<M} |S_k|² e(kδ/M) = M² C_χ(δ)`; Poisson summation on the shifted lattice `j + k/M` turns the offset sums into the shifted densities `D_u(s) = Σ_{n≥0} |φ̂(2πs(n+u))|²`; each is the dilation derivative of a shifted bulk `E_u(s) = Σ T(s(n+u))/(n+u)` with `s^β E_u → A_φ ζ(β+1, u)`. So `c⁻¹⟨Wx,x⟩/∫g² → (βA_φ/(K∫φ²)) Σ_k |χ̂(k)|² (ζ(β+1,k/M) + ζ(β+1,1−k/M)) ‖H‖²`, for every profile with a regular spectral tail; positive for every nonzero twist. For the real part of a primitive Dirichlet character `ψ` mod `q` the spectrum carries the phase `ψ̄(k)²τ(ψ)²`, and the second order is the count `ζ(β+1)J_{β+1}(q)/q` plus the `L`-value `q^{β−1}Re(ψ̄(−1)τ(ψ)²L(β+1, ψ̄²))` of the squared character. | `periodicTwist_layer_criticalCurve_of_regularTail`, `periodicTwist_layer_criticalCurve_exact`, `abs_twistEnergy_sub_le`, `sum_normSq_twistCoeff_mul_cexp`, `hasSum_shellSpectrum_shift`, `tendsto_rpow_mul_twistBulk`, `twistSpectralSum_ge`, `charTwist_layer_criticalCurve` |
| How does the complete family read a curve over `𝔽_q`? | Through its Frobenius angles, exactly as a periodic twist is read over `ℤ`: on lattice tests `Σ_k x_k g_w(· − k log q)` of any atom width, `W = w² Σ_i S_{θ_i}(w/log q)|Σ_k x_k β_i^k|²`, `β_i = e(θ_i)`, by the explicit formula of the curve, the lag correlations of the atoms and Poisson summation on the shifted lattices `j + θ_i`; positive at every width for a pure curve. At narrow width it is ACS's `log q‖g‖² spanGram` (finite monodromy). | `W_curveLatticeTest`, `re_W_curveLatticeTest_nonneg`, `hasSum_lag_unitCircle`, `weilTest_curveLatticeTest` |
| What is the limiting structure of the fakes? | Over `𝔽_q` the type of the degeneration selects. A pure curve without the eigenvalue `1` degenerates completely: `W(T_x, T_x) → 0` on every lattice test as the atoms widen. The golden fake does not degenerate: at every width the Gram matrix of its lattice atoms is `E(w)/2` times the span Gram matrix of the narrow tower (the two lag series `Φ_φ = Φ_{φ⁻¹}` agree because `G` is even), a fixed hyperbolic plane with one negative square, scaled by `E(w) ≥ c w e^{εw}`: no rescaled limit at any polynomial rate. Over `ℤ` a prime flip leaves an overlap-independent indefinite residue (ADT). | `tendsto_W_curveLatticeTest_pure`, `goldenDatum_towerGram_eq_smul_spanGram`, `goldenDatum_negIndex_dilation`, `goldenDatum_curveAtomEnergy_ge`; ADT `primeFlip_degenerates_indefinitely` |
| Do Ramanujan windows of different conductors interact? | No: `Σ_{r<M} c_m(r) c_{m'}(r+s) = [m = m'] M c_m(s)` at every offset (primitive roots of distinct orders never multiply to `1`), so the autocorrelation of a Ramanujan expansion is `Σ a_m² c_m` and its second-order form is `(Σ_m a_m² J_{β+1}(m)) βJ/K ‖H‖²`: diagonal in the Ramanujan basis, with the conductor counts as eigenvalues. Characters of one modulus behave differently: windows twisted by characters of opposite parity are orthogonal at second order, but characters of equal parity are coupled through `L(s, ψ̄₁ψ₂)` and `L(s, ψ̄₁ψ̄₂)`. | `ramComb_layer_criticalCurve_of_regularBulk`, `ramComb_layer_criticalCurve_exact`, `sum_ramTwist_mul_ramTwist_add`, `autoCorr_ramComb`, `crossSpectralSum_charTwist`, `cross_layer_charTwist_opposite_parity` |
| Do the twisted directions interact with the untwisted ones? | Not at second order, for every mean-zero periodic twist whose block is quiet below its first resonance (`cross_layer_vanishes_of_twist`); in particular for every Ramanujan expansion, giving the full conductor decomposition `κQ(H) + (βJ/K)‖H‖² + (Σ_m a_m² J_{β+1}(m))(βJ/K)‖G‖²` (`graded_ramComb_criticalCurve_of_regularBulk`, `graded_ramComb_criticalCurve_exact`). For `x = h/√n` and `y = c_p(n) g/√n`, `c⁻¹(Q(x+y) − Q(x−y))/∫g² → 0` along every resolution with `c → ∞`, `c log²N/N → 0`. The mixed pole terms are products of a Riemann sum and a twisted Riemann sum (`O(1/N)`), the quiet region couples a dominated untwisted block (`|D_x|²/N ≤ C/(1+τ²)`) with a prime block of quiet energy `O(N^{−1/2})` (AM–GM: `O(N^{−1/4})`), and the mixed energy is `O(c/N)` because `c_p` has mean zero on the smooth untwisted rows. So the second-order form of the span is the direct sum `κQ(H) + (βJ/K)‖H‖² + (p^{β+1} − 1)(βJ/K)‖G‖²`. | `cross_layer_vanishes`, `exists_abs_crossPole_le`, `exists_quietCross_le`, `exists_abs_crossEnergy_le`, `atomForm_parallelogram`, `graded_layer_criticalCurve_of_regularBulk`, `graded_layer_criticalCurve_exact` |
| Where do the negative directions of the horizon layer live? | Only on untwisted windows. On a mixed family (untwisted windows and windows twisted by a Ramanujan expansion) the normalized Gram matrices converge to `fromBlocks P_K 0 0 (Λ A(G))`, `Λ ≥ 0`, whose index is exactly the window index `ind₋(P_K)`: twisted windows never add a negative square (`mixed_windowIndex`, `tendsto_mixedGram`). A window twisted by a mean-zero periodic weight has transform `O(1/N)` at low frequencies and at the pole values, and the symbol is nonnegative beyond the archimedean horizon `τ₀(A)`; so at every resolution `0 < c ≤ N` its normalized form is `≥ −C₀(L_h + B_h)²/N²`. Its second-order term is strictly positive: one dyadic window above the grid carries `a log N/c⁸`, so at the multiple `K` of the critical curve it is `≥ a/K − ε`. | `twisted_horizon_form_ge`, `eventually_twisted_horizon_form_ge`, `exists_weilQuad_ge_of_lowFrequency`, `twisted_horizon_layer_coercive`, `twisted_horizon_layer_criticalCurve_ge` |
| Is the horizon layer Weil's form? | Yes. In the iterated limit (horizon, then window of zeros) windows exhaust `κ W(H,H)`. Directly: past the critical curve (`(1+log N)/c^p → 0`) `c⁻¹⟨Wx,x⟩ → κ Q(H)`; at `c^p/log N → K_c` it is `κ Q(H)` up to `K/K_c`; for every schedule the error is `ε + K(1+log N)/c^p`. | `horizon_layer_two_sided`, `tendsto_horizon_layer_supercritical`, `horizon_layer_criticalCurve`, `horizon_window_exhaustion` |
| What is the second-order term at the critical curve (obstacles summary 2.5.4)? | On horizon blocks, exactly: `c⁻¹⟨Wx,x⟩ → κ Q(H) + (βJ/K) ∫ e^{−(β+1)y} H²` along `c^{β+1}/log N → K`, for every profile with bulk limit `s^β E₁(s) → J` (tilted spline: `β = 7`, `J = J(1)`). For every profile and every schedule with `c → ∞`, `c(log N)²/N → 0`: `c⁻¹⟨Wx,x⟩ = κ Q(H) − log N · N⁻¹ Σ_n h(log(n/N))² E₁'(cn/N) + o(1)`. | `horizon_layer_criticalCurve_of_regularBulk`, `horizon_layer_criticalCurve_exact`, `horizon_layer_sharp`, `horizon_layer_sharp_bulk`, `horizonForm_eq` |
| Is there a count past first order? | On the twisted directions, yes: the conductor-two window `(−1)^n h(log(n/N))/√n` has second-order term exactly `(2^{β+1} − 1) β J/K ‖H‖²_{−(β+1)}`, for the tilted spline `7 J(2)/K ‖H‖²_{−8}` with `J(2) = J(1) #ℙ⁷(𝔽₂)`, the first-order count of conductor two; at every prime the `c_p` window has `(p^{β+1} − 1) β J/K ‖H‖²`, i.e. `7 (p − 1) J(p)/K ‖H‖²_{−8}`; at every conductor `m ≥ 2` the Ramanujan window has `J_{β+1}(m) β J/K ‖H‖²`, i.e. `7 φ(m) J(m)/K ‖H‖²_{−8}`. Mechanism: the energy of a periodic twist is computed by its autocorrelation, and the autocorrelation of `c_m` is `c_m` itself (orthogonality of roots of unity), so the energy is `2π Σ_{de=m} μ(d) 𝒜_N(c/e)`. The alternating sign keeps the odd half-harmonics of the atom grid: `Σ_j (−1)^j G(j/a) = 2a(a_φ(a/2) − a_φ(a))`. On untwisted windows the second order is `κQ(H)` plus the count term, and `Q(H)` is not a count. | `alternating_layer_criticalCurve_exact`, `alternating_layer_criticalCurve_of_regularBulk`, `alternating_layer_sharp`, `tsum_altSign_shellAutocorr`, `jordanCoefficient_two`, `prime_layer_criticalCurve_exact`, `prime_layer_sharp`, `jordanCoefficient_prime`, `ram_layer_criticalCurve_exact`, `ram_layer_criticalCurve_of_regularBulk`, `periodicEnergy_le`, `autoCorr_ramTwist` |
| Which structure polarizes the second-order term? | The first-order count, through the monodromy. The aliasing density is the dilation derivative of the bulk energy, `a_φ = −(∫φ²/2) E₁'`, positive because `E₁` is antitone; its window average at the local overlaps `c e^y` is `β J(1)` times `‖H‖²_{−8}`. So the second-order term is a pencil: Weil's form plus `1/K` times a positive definite form built from `J(1)`. It is positive at every multiple iff `Q ≥ 0` on horizon windows, i.e. iff RH. On the bulk, the zero charge is the Li-type pole charge (positive per zero). | `hasDerivAt_completedShellEnergy`, `aliasLimit_eq`, `tendsto_rpow_seven_mul_completedShellEnergy_tilted`, `re_inv_mul_one_sub_pos`, `riemannHypothesis_iff_horizon_layer` |
| What is the integer of the degeneration (carrier C)? | The window index `ind₋(P_K)` of the pencil Gram matrix of a family of windows at multiple `K`: the complete family reads it (`ind₋(P_K) ≤ ind₋(G_N)` eventually); it is nondecreasing in `K` and equals Weil's index on the family for large `K`; some family has window index `≥ n` iff `ζ` has `≥ n` right zeros; windows of length `A` have index `≤ 1 + 2A T(A/2)/π` (Shannon number) and, for suitable families, `≥` the number of right zeros resolved at level `A/2` (below the Nyquist height `πe^{A−3/4}`); it vanishes for all families and multiples iff RH. On an independent family it is a step function of the multiple: `ind₋(P_K) = #{i : λ_i < 0, βJ/(−λ_i) < K}`, `λ_i` the eigenvalues of `A(H)^{−1/2} κW(H) A(H)^{−1/2}`, so it jumps by one at each jump multiple `K_i = βJ/(−λ_i)`, the critical multiple of the `i`-th relative eigen-window. On smooth windows of length `< log 2 + 1/50` it is at most one, eventually for the complete family as well, the only possible negative direction transverse to the cosh hyperplane (`eventually_hermNegIndex_horizonGram_le_one`). | `tendsto_horizonGram`, `eventually_hermNegIndex_pencilGram_le`, `pencilGram_eq`, `hermNegIndex_pencilGram_mono`, `eventually_hermNegIndex_pencilGram_eq`, `windowIndex_law`, `riemannHypothesis_iff_windowIndex_eq_zero`, `hermNegIndex_pencilGram_le_shannon`, `windowIndex_eq_card_jumpMultiples`, `hermNegIndex_add_smul_posDef`, `aliasGram_posDef`, `exists_windows_resolving_rightZeros`, `exists_windows_le_weilNegIndex` |
| What is the critical multiple of a window? | Exactly `K*(H) = 7 J(1) ‖H‖²_{−8}/(κ |Q(H)|)` for `Q(H) < 0` (`+∞` otherwise): positive below, negative above. Before the exact constant: coercive bounds `κ Q(H) + a/K ≤ · ≤ κ Q(H) + b/K`. | `criticalMultiple_exact`, `horizon_layer_coercive`, `horizon_layer_lower_criticalCurve`, `horizon_layer_criticalCurve` |
| Where does the horizon term of a conductor live? | Only at `e = 1`: `D_e(s;N) − [e=1]N^s/s → ζ(1−s)J_s(e)`. | `tendsto_conductorDirichlet_sub_horizonTerm`, `conductorDirichlet_eq` |
| Is positivity at one fixed multiple of the critical curve RH? | No: positivity at multiple `K` is `κ Q(H) ≥ −7J(1)‖H‖²_{−8}/K` on every window (sub-RH); every window with `Q(H) < 0` turns negative past `K*(H)`. RH is positivity at every multiple. | `criticalMultiple_exact`, `weilQuad_halfWeight_ge_of_horizon_nonneg`, `eventually_horizon_neg_of_weilQuad_neg` |
| Does inheritance (mechanism B) hold anywhere unconditionally? | On every family of untwisted horizon windows of length `≤ 3/5`: Weil's form is nonnegative on such windows (CWS), so `P_K = κW(H) + (βJ/K)A(H)` is positive definite at every multiple and the complete family is eventually positive definite on the family (`short_windows_inherit`, `short_windows_inherit_exact`, `hermQuad_weilWindowGram_nonneg`). Up to the length `log 2 + 1/50`, past the first prime, on the cosh hyperplane `Σ_i ℓ_i x_i = 0` of smooth families (`ℓ_i` the cosh moments of the centred tests), where Weil's form is coercive (CWS): the pencil is positive definite there at every multiple, the complete family is eventually positive definite on the hyperplane, and so its window index is eventually `≤ 1` (`pencilGram_isPosDefOn_coshHyperplane`, `eventually_isPosDefOn_coshHyperplane`, `eventually_hermNegIndex_horizonGram_le_one`). On the twisted sector, yes: for an independent family twisted by a nonzero Ramanujan expansion the second-order limit is `Λ A(G)`, `Λ = (Σ a_m² J_{β+1}(m))βJ/K > 0`, positive definite; positive definiteness is open, so along the critical curve the Gram matrix of the complete family on the family is eventually positive definite; the same holds for every nonzero mean-zero periodic twist with `Λ_χ = (βA_φ/(K∫φ²)) S_{β+1}(χ)` (`periodic_twisted_sector_inherits`). On windows of every length, below the same multiple `K₀ = βJ/(κC(β+1))`, for `β > 0`: the exponential weighted floor makes every independent finite pencil positive definite. Each fixed family then inherits positivity (`below_apertureIndependentMultiple_inherit`); the tilted-spline theorem discharges the profile and bulk inputs (`tilted_exists_positive_multiple_inheriting_all_windows`). On the conductor-one block inheritance at every multiple holds exactly when `Q ≥ 0` on windows, i.e. RH. | `twisted_sector_inherits`, `twisted_sector_inherits_exact`, `eventually_hermQuad_pos_of_tendsto` |
| What does a second-order term do to positivity? | Admissible multiples form a closed initial segment; inheritance below the critical multiple, failure above; negative directions persist. | `admissible_of_le`, `isClosed_admissible`, `admissible_mono`, `neg_persists`, `eventually_pos_of_tendsto`, `eventually_not_nonneg_of_tendsto` |
| Can the ledger or the first-order count select `ζ`? | No: the ledgers hold for every zero configuration, and the count law holds over every finite commutative ring — `#Unimod(R^k) = #ℙ^{k−1}(R)·#Rˣ`, over a local ring `#ℙ^{k−1}(R)(|R| − |𝔪|) = |R|^k − |𝔪|^k` — so over the residue rings of `𝔽_q[T]`, where RH holds, the first-order structure is the same. | statements quantified over `ZeroConfig`; `natCard_unimodular_eq`, `natCard_unimodular_local`, `natCard_projSpace_local` |
| How do the prime atoms of the jump measure enter, and what pays the creation potential `−2Σ Λ(n)/√n`? | On a window of length `A` every prime power `n > e^A` makes a jump that leaves the window and costs exactly `2Λ(n)/√n ‖H‖²`, the creation it adds: the Markov form of a window is that of level `⌊e^A⌋`. At second order the primes enter only through `Q(H)`: the correction `(7J(1)/K)‖H‖²_{−8}` is prime-free (the aliasing is paid by the Gamma factor, `ν ≈ log N/2π`). What pays the creation potential of the primes `≤ e^A` is the open sign question itself. The primes inside every window are paid at the same small multiples: the weighted correlation bound sums to `2ΣΛ(n)n^{−(β+2)/2}`, so below `K₀ = βJ/(κC(β+1))` the aliasing count pays all prime correlations and both pole moments, independently of aperture; on the first-prime windows the cosh hyperplane absorbs the prime `2` at every multiple. | `primeJump_departing_eq`, `markovForm_eq_of_level`, `weilQuad_halfWeight_eq_markovForm`, `horizon_layer_criticalCurve_exact`, `pencilGram_posDef_below_uniformMultiple`, `pencilGram_isPosDefOn_coshHyperplane` |
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
- Sublattice rows and equidistribution on `pℤ` (`abs_subRow_sub_le`, `abs_sum_dvd_sub_le`,
  `sum_sum_primeTwist_eq`); Kuzmin–Landau for `c_p(n) n^{iτ}` (`norm_partial_primeTwist_cpow_le`);
  set integrals split at `√N` against a Cauchy kernel (`setIntegral_Icc_le_of_split`).
- Alternating lattice sums by two Poisson summations (`tsum_altSign_shellAutocorr`); Kuzmin–Landau
  for `(−1)^n n^{iτ}` (`norm_partial_altSign_cpow_le`); Plancherel, the form identity and the dyadic
  remainder for arbitrary window weights (`atomEnergy_eq`, `atomForm_eq`, `abs_remainderW_le`).
- Weil's form above the archimedean horizon: for tests supported in `[−a, a]` the symbol is
  nonnegative beyond `τ₀(a)`, and `Q(f) ≥ −2|f̂(i/2)||f̂(−i/2)| − M_a sup_{|τ|≤τ₀} |f̂|²`
  (`nuSymbol_nonneg_of_archHorizon_le`, `exists_weilQuad_ge_of_lowFrequency`); recentred atomic
  tests with arbitrary window weights (`centredAtomicTest`, `paperFT_centredAtomicTest`).
- The pencil split and positive semidefinite weighted Gram matrices on windows (`pencilGram_eq`,
  `hermQuad_weightGram_nonneg`).
- Windows from tests and real parts of negative families (`windowOfTest`, `weilGram_windowOfTest`,
  `le_hermNegIndex_reIm`): transport of finite-level indices of `ζ` to windows of a given length.
- Openness of positive definiteness under entrywise limits (`eventually_hermQuad_pos_of_tendsto`,
  lower semicontinuity of the positive index), also on a subspace through compression by a basis
  (`eventually_isPosDefOn_of_tendsto`, `hermQuad_compress`); inertia against a positive subspace,
  `ind₋ + dim U ≤ card` (`hermNegIndex_add_finrank_le`).
- Euler–Maclaurin on the strip at second order (`norm_zetaStripError_le`) and at every order with
  constants uniform in the height (`norm_zetaStripError_le_order`) and explicit conductor
  polynomials at zeros (`norm_conductorDirichlet_sub_horizonTerm_le`), summed with the zero count.
- Discrete Fourier analysis of twists and Poisson summation on shifted lattices
  (`sum_normSq_twistCoeff_mul_cexp`, `hasSum_shellSpectrum_shift`); window limits of densities with
  a regular bulk (`tendsto_rpow_mul_densityAlias`).
- Inertia of a pencil against a positive definite form: `ind₋(W + tB) = #{λ_i + t < 0}` for the
  relative eigenvalues, via `B^{1/2}`-congruence and the spectral theorem
  (`hermNegIndex_add_smul_posDef`, `relMatrix`); positive definiteness of weighted Gram matrices of
  independent windows (`aliasGram_posDef`, `hermQuad_weightGram_eq`).
- The energy law of periodic twists (`periodicEnergy_le`): periodic equidistribution against
  Lipschitz profiles (`abs_sum_periodic_sub_le`), rows of bounded twists (`abs_twistRow_sub_le`), the
  offset reindexing (`sum_offset_eq`), uniform Lipschitz offset profiles (`abs_offsetProfile_sub_le`).
- Ramanujan sums as twists: autocorrelation by roots of unity (`sum_ramTwist_mul_add`), divisor
  lattice sums in the offset (`sum_offset_dvd_eq`), Kuzmin–Landau on sublattices
  (`norm_partial_dvd_cpow_le`, `norm_partial_ramTwist_cpow_le`).
- Kuzmin–Landau with a real shift and on residue classes (`norm_partial_cpow_real_le`,
  `norm_partial_shift_dvd_cpow_le`, `norm_partial_periodic_cpow_le`); the quiet region of every
  mean-zero periodic block (`exists_periodicLow_energy_le`).
- The sharp form of a twisted window from its energy and its quiet region
  (`twisted_layer_sharp_of_energy`); orthogonality of Ramanujan sums at every offset
  (`sum_ramTwist_mul_ramTwist_add`); Cauchy–Schwarz over conductors for quiet energies
  (`exists_ramCombLow_energy_le`).
- Polarization of block forms: linearity of block transforms in the weights, the polarized pole
  part, AM–GM for polarized energies, the mixed Plancherel identity, the parallelogram law
  (`paperFT_centredAtomicTest_add`, `abs_pole_add_sub_le`, `abs_polar_le`, `crossEnergy_eq`,
  `atomForm_parallelogram`); bounded untwisted Riemann sums (`norm_horizonRiemannSum_le`); the
  remainder above the cut uniformly in the weights (`tendsto_remainderW`).

- Twists beyond periodicity: the sharp form of a twisted window for any bounded twist with bounded
  partial sums (`twisted_layer_sharp_of_energy_of_bounded`, `norm_twistedRiemannSum_le_of_primitive`,
  `exists_abs_twistedPole_le_of_primitive`); Kuzmin–Landau with a rotation
  (`norm_partial_rot_le`, `norm_partial_freqTwist_cpow_le`); oscillations against Lipschitz profiles
  (`abs_sum_cos_mul_le`).
- Gauss sums of primitive characters as spectra (`twistCoeff_charTwist`), cross spectra and the
  polarized second order (`crossPower`, `cross_layer_criticalCurve`).

**Developed in neighbouring programmes and used here.** Néron–Tate theory and the Tate limit law on
correspondences (AET); Arakelov `h⁰` of lattices of growing rank, Künneth Riemann–Roch, the
isotropic cone count and the boost transform (LST); the Lévy–Khintchine form of Weil's functional
and its Markov splitting (RHTower `WeilMarkovPoleCapacity`); lower semicontinuity of the index
(HKT); the index bound by the right zeros (ACS); Wiener–Hopf and Szegő factorization (CDG/WD);
Stepanov over `ℤ` (AET) and over curves (LST).

**To build.**
- The ledger at the resolution height `|γ| ≍ N/c`: mean values of conductor polynomials over the
  zeros where the atoms resolve them.
- The function-field complete family and its horizon layer; Zwegers–Vignéras completions of the
  isotropic count.

## 8. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Count law: the Jordan limit counts `ℙ⁷(ℤ/m)`; Hensel towers; CRT | `jordanCoefficient_eq_projPoints`, `natCard_projPoints_mul_totient`, `projPoints_prime_mul`, `projPoints_prime_pow_succ`, `primVecCRT` | proved |
| Horizon law: only the pole conductor has a horizon term | `tendsto_conductorDirichlet_sub_horizonTerm`, `tendsto_conductorDirichlet_of_zeta_eq_zero` | proved |
| Bulk zero ledger, at every schedule and at the critical curve; positivity of the pole charge | `tendsto_bulkLedger`, `tendsto_bulkLedger_criticalCurve`, `re_inv_mul_one_sub_pos`, `tendsto_sum_bulkLedger` | proved |
| The curve family is stationary along the horizon: Weil's form of a curve is invariant under translating both tests, so a lattice window reads the same form at every horizon and the only degeneration is in the atom width | `W_curveConfig_translate_translate` | proved |
| One Frobenius orbit makes the dilation scalar: for a datum with eigenvalues `β, β⁻¹` (elliptic curves, genus-one fakes) the lattice Gram matrix at every width is `E(w)/2 · spanGram`; the golden fake is self-similar with one negative square from window `2` on; for every curve `W(f_k, f_l) = log q Σ_i β_i^{k−l} Φ_{β_i}(w)`, `Φ_{β⁻¹} = Φ_β` | `towerGram_eq_smul_spanGram_of_orbit`, `goldenDatum_towerGram_eq_smul_spanGram`, `goldenDatum_negIndex_dilation`, `W_curveConfig_translate_atom`, `lagSeries_inv` | proved |
| Degeneration selects the pure curves: a pure curve without the eigenvalue `1` has `W(T_x, T_x) → 0` on every lattice test; the golden fake has `W(g_w, g_w) ≥ c w e^{εw}` and `W/w^k → ∞` for every `k` | `tendsto_W_curveLatticeTest_pure`, `goldenDatum_curveAtomEnergy_ge`, `tendsto_goldenDatum_W_div_pow`, `W_curveConfig_atom` | proved |
| The monodromy rate of a curve is its zero width: with `R = max|β_i|`, `δ = log R/log q = max|Re s − ½|`, tests of length `ℓ` have `|W(f, f)| ≤ (2ℓ + log q) N e^{δℓ}‖f‖²`; for `R > 1` and every `ε > 0`, eventually some tests of length `ℓ` reach `Re W ≤ −e^{(δ−ε)ℓ}‖f‖²` and `Re W ≥ e^{(δ−ε)ℓ}‖f‖²` (Turán); a pure curve grows linearly | `curve_monodromy_rate`, `norm_W_curveConfig_le_exp`, `exists_lagTests_two_sided`, `norm_W_curveConfig_le_of_pure` | proved |
| The rescaled limit of a curve is the Hurwitz form of its Frobenius angles: `a^β E_x(a) → A_φ Σ_i |Σ x_k β_i^k|² (ζ(β+1,u_i) + ζ(β+1,1−u_i))`, `W = −w² E_x'` | `tendsto_rpow_mul_curveBulk`, `hasDerivAt_curveBulk`, `W_curveLatticeTest_eq_density` | proved |
| The Frobenius angles diagonalize the curve family: `W(T_x,T_x) = w² Σ_i S_{θ_i}(w/log q)|Σ x_k β_i^k|²` at every atom width; positive for pure curves | `W_curveLatticeTest`, `re_W_curveLatticeTest_nonneg` | proved |
| The bulk below the resolution height: for every `θ < 1` and `c log² N/N^{1−θ} → 0`, the zeros of height `≤ N^θ` give `κ y_1²(2 + γ − log 4π)` at the pole and nothing to pole-free packets | `tendsto_sum_bulkLedger_belowResolution`, `tendsto_sum_bulkLedger_belowResolution_poleFree`, `norm_zetaStripError_le_order`, `norm_conductorDirichlet_sub_horizonTerm_le_order` | proved |
| The bulk at the pole reads the archimedean genus: the zeros of height `≤ N^θ`, `θ < 2/3`, contribute `κ y_1² (2 + γ − log 4π)` in total | `tendsto_sum_bulkLedger_lowZeros_genus_rpow`, `tendsto_sum_bulkLedger_lowZeros_pole`, `tsum_mult_div_zero_mul_one_sub_eq` | proved |
| The bulk is blind to the low zeros: all zeros of height `≤ N^θ`, `θ < 2/3`, contribute `o(c/log N)` together to every pole-free packet | `tendsto_sum_bulkLedger_lowZeros_rpow`, `tendsto_sum_bulkLedger_lowZeros`, `norm_log_div_mul_bulkLedger_le` | proved |
| Horizon ledger: Weil summands of the synthesized test | `tendsto_horizonLedger`, `Wsummand_halfWeight`, `tendsto_horizonDirichlet` | proved |
| Twisted horizon windows are zero-blind | `tendsto_twistedLedger`, `norm_twistedRiemannSum_le`, `abs_sum_range_le` | proved |
| Twisted horizon windows are positive at every resolution, up to `O(N^{−2})` | `twisted_horizon_form_ge`, `exists_weilQuad_ge_of_lowFrequency`, `nuSymbol_nonneg_of_archHorizon_le` | proved |
| Twisted horizon windows are coercive: second-order term `≥ a/K` at the critical curve | `twisted_horizon_layer_coercive`, `twisted_horizon_layer_criticalCurve_ge`, `tendsto_sum_twistedWeights_sq` | proved |
| The conductor-two window counts the conductor-two points: `c⁻¹⟨Wx,x⟩ → 7J(2)/K ‖H‖²_{−8}` | `alternating_layer_criticalCurve_exact`, `alternating_layer_sharp`, `abs_altEnergy_sub_le`, `norm_dirichletPoly_alt_le` | proved |
| The prime window counts `ℙ⁷(𝔽_p)`: `c⁻¹⟨Wx,x⟩ → 7(p−1)J(p)/K ‖H‖²_{−8}` for every prime `p` | `prime_layer_criticalCurve_exact`, `prime_layer_sharp`, `abs_primeEnergy_sub_le`, `exists_primeLow_energy_le` | proved |
| Divisor windows sum the divisor counts: `→ (7/K) Σ_{e|d,e>1} φ(e)J(e) ‖H‖²_{−8}` for every `d ≥ 2` | `divisor_layer_criticalCurve_exact`, `sum_divisors_jordanTotient`, `totient_mul_jordanCoefficient` | proved |
| The Ramanujan window counts every conductor: `c⁻¹⟨Wx,x⟩ → J_{β+1}(m)βJ/K ‖H‖²`, tilted `7φ(m)J(m)/K ‖H‖²_{−8}`, every `m ≥ 2` | `ram_layer_criticalCurve_exact`, `ram_layer_criticalCurve_of_regularBulk`, `ram_layer_sharp`, `abs_ramEnergy_sub_le`, `autoCorr_ramTwist` | proved |
| Every periodic twist with even autocorrelation `C_χ = Σ b_m c_m` has second order `(Σ b_m J_{β+1}(m)) βJ/K ‖H‖²`; the Legendre symbol `(·/p)` carries `(p^{β+1} − 1)/p` | `evenTwist_layer_criticalCurve_of_regularBulk`, `legendre_layer_criticalCurve_of_regularBulk`, `autoCorr_legTwist`, `exists_periodicLow_energy_le`, `norm_partial_periodic_cpow_le` | proved |
| The horizon layer is graded by frequency: a trigonometric twist `Σ_k a_k cos(2πnα_k)` with distinct frequency classes (`α_k + α_l ∉ ℤ`, `α_k − α_l ∉ ℤ` for `k ≠ l`) has second-order coefficient `(βA_φ/(K∫φ²)) Σ_k a_k² · ½(ζ(β+1, u_k) + ζ(β+1, 1 − u_k))`: distinct frequencies are orthogonal, as distinct conductors are | `trigTwist_layer_criticalCurve`, `abs_trigEnergy_sub_le`, `trigEnergy_le`, `abs_offsetSum_trig_sub_le`, `exists_trigLow_energy_le` | proved |
| Every frequency acts as a Frobenius angle: for every real `α` with `2α ∉ ℤ`, `u = {α}`, the window twisted by `cos(2πnα)` has second-order coefficient `(βA_φ/(K∫φ²)) · ½(ζ(β+1, u) + ζ(β+1, 1 − u))`, continuous in `u`, the same for rational and irrational frequencies | `freqTwist_layer_criticalCurve`, `abs_freqEnergy_sub_le`, `freqEnergy_le`, `exists_freqLow_energy_le`, `norm_partial_rot_le` | proved |
| The frequency of a twist acts as a Frobenius angle: the window twisted by `cos(2πan/M)`, `0 < a < M`, `2a ≠ M`, has spectrum `1/4` at `k = a, M − a` and second-order coefficient `(βA_φ/(K∫φ²)) · ½(ζ(β+1, u) + ζ(β+1, 1 − u))`, `u = a/M`: the Hurwitz form of the frequency, as for a Frobenius angle over `𝔽_q` | `cosTwist_layer_criticalCurve`, `twistSpectralSum_cosTwist`, `twistPower_cosTwist` | proved |
| The character windows are graded by parity: the polarized second order of two twisted windows is the cross-spectral sum `2M^s Σ_j Re(S_j S̄'_j)/M² j^{−s}`; for primitive `ψ₁, ψ₂` mod `q` it is `(1 + ψ₁(−1)ψ₂(−1)) q^s/(2q²) Re(c₁c̄₂τ₁τ̄₂L(s, ψ̄₁ψ₂) + c₁c₂ψ̄₂(−1)τ₁τ₂L(s, ψ̄₁ψ̄₂))`: opposite parity is orthogonal, equal parity couples through `L`-values | `cross_layer_criticalCurve`, `crossSpectralSum_charTwist`, `crossPower_charTwist`, `cross_layer_charTwist_opposite_parity` | proved |
| The second order of a character window reads an `L`-value: for `ψ` primitive mod `q` and `c ∈ ℂ`, the window twisted by `Re(cψ)` has spectrum `|χ̂(k)|² = |c|²[(k,q)=1]/(2q) + Re(c²ψ̄(−1)ψ̄(k)²τ²)/(2q²)` and spectral sum `|c|²ζ(s)J_s(q)/q + q^{s−2} Re(c²ψ̄(−1)τ(ψ)²L(s, ψ̄²))`, `s = β+1`; on the circle `|c| = 1` it ranges exactly over `ζ(s)J_s(q)/q ± q^{s−1}‖L(s, ψ̄²)‖`: the character pair splits the unit count by the `L`-value | `charTwist_layer_criticalCurve`, `twistSpectralSum_charTwist`, `exists_charTwist_extremal`, `abs_twistSpectralSum_charTwist_sub_le`, `twistPower_charTwist` | proved |
| The spectrum of `c_m` is the unit group, `|χ̂(j)|² = [(j,m)=1]`, and its spectral sum is `2ζ(s)J_s(m)`: the spectral and the energy-law derivations of the Ramanujan second order agree | `twistPower_ramTwist`, `twistCoeff_ramTwist`, `twistSpectralSum_ramTwist`, `ramTwist_spectral_limit_eq` | proved |
| The counting reading: the spectral sum is the Dirichlet series of the power spectrum, `Σ_k |χ̂(k)|²(ζ(s,k/M) + ζ(s,1−k/M)) = 2M^s Σ_j |χ̂(j)|² j^{−s}` | `twistSpectralSum_eq_dirichlet`, `periodicTwist_layer_criticalCurve_dirichlet`, `twistPower_reflect`, `hurwitzSum_div_eq` | proved |
| Every mean-zero periodic twist: `c⁻¹⟨Wx,x⟩/∫g² → (βA_φ/(K∫φ²)) Σ_{0<k<M} |χ̂(k)|² (ζ(β+1,k/M) + ζ(β+1,1−k/M)) ‖H‖²_{−(β+1)}`; the spectral sum is `≥ 2M⁻¹Σχ²` | `periodicTwist_layer_criticalCurve_of_regularTail`, `periodicTwist_layer_criticalCurve_exact`, `twistSpectralSum_ge` | proved |
| The energy of a twist is its spectrum: `E_N = 2π Σ_{0<k<M} |χ̂(k)|² (𝒜^{(k/M)} + 𝒜^{(1−k/M)}) + O(c/N)`; Poisson on shifted lattices; Parseval | `abs_twistEnergy_sub_le`, `sum_offset_twist_eq`, `hasSum_shellSpectrum_shift`, `sum_normSq_twistCoeff_mul_cexp`, `sum_twistPower` | proved |
| A density that is the dilation derivative of a regular bulk has window limit `βJ` | `tendsto_rpow_mul_densityAlias`, `integral_densityWindow_eq`, `hasDerivAt_twistBulk`, `hasDerivAt_spectralTail` | proved |
| Parseval for the count: the second-order form of a Ramanujan expansion `Σ_m a_m c_m` is `(Σ_m a_m² J_{β+1}(m)) βJ/K ‖H‖²`, tilted `(7/K) Σ a_m² φ(m)J(m)` | `ramComb_layer_criticalCurve_of_regularBulk`, `ramComb_layer_criticalCurve_exact`, `sum_ramTwist_mul_ramTwist_add`, `autoCorr_ramComb`, `twisted_layer_sharp_of_energy` | proved |
| The energy of a periodic twist is its autocorrelation: `E_N = (2π/c) Σ_n y_n² Σ_{|δ|≤⌈c⌉} C_χ(δ) G(δ/a_n) + O(c/N)` | `periodicEnergy_le`, `abs_offsetSum_sub_le`, `abs_sum_periodic_sub_le`, `abs_twistRow_sub_le` | proved |
| The horizon layer is graded by conductor: untwisted and prime windows are orthogonal at second order, `x + y → κQ(H) + 7J(1)/K ‖H‖²_{−8} + 7(p−1)J(p)/K ‖G‖²_{−8}` | `cross_layer_vanishes`, `graded_layer_criticalCurve_of_regularBulk`, `graded_layer_criticalCurve_exact`, `atomForm_parallelogram` | proved |
| One critical multiple pays every window: for `β > 0`, `Q ≥ −C(β+1)‖·‖²_{−(β+1)}` with `C` independent of aperture; one positive range of `K` makes every independent finite pencil positive definite, and each fixed family inherits positivity | `hermQuad_weilWindowGram_ge_aliasGram`, `exists_positive_multiple_for_all_windows`, `tilted_exists_positive_multiple_inheriting_all_windows`, `below_apertureIndependentMultiple_inherit` | proved |
| The count pays the second order below a uniform multiple: on windows of every length `A`, Weil's floor `Q(F) ≥ −(10 + 72e^{A/2})‖F‖²` and `A(H) ⪰ ‖·‖²` make the pencil positive definite for `κ(10 + 72e^{A/2})K < βJ`; the window index vanishes and the complete family is eventually positive definite there, also on mixed families with Ramanujan-twisted windows | `below_uniformMultiple_inherit`, `mixed_below_uniformMultiple_inherit`, `pencilGram_posDef_below_uniformMultiple`, `hermNegIndex_pencilGram_eq_zero_below_uniformMultiple`, `weilQuad_window_ge` | proved |
| The window index is at most one below `log 2 + 1/50`: on every independent family of smooth windows of that length the pencil is positive definite on the cosh hyperplane, has at most one negative square, and the complete family eventually has at most one | `eventually_hermNegIndex_horizonGram_le_one`, `eventually_isPosDefOn_coshHyperplane`, `hermNegIndex_pencilGram_le_one`, `pencilGram_isPosDefOn_coshHyperplane`, `hermQuad_weilWindowGram_nonneg_of_cosh` | proved |
| The scalar inheritance principle: a twist whose every window has the second order `Λ‖H‖²_{−(β+1)}`, `Λ > 0`, inherits the polarization on every independent family; hence every nonzero trigonometric twist with distinct frequency classes does | `twisted_sector_inherits_of_scalar`, `tendsto_twistGram_of_scalar`, `trig_twisted_sector_inherits` | proved |
| Every periodic twisted sector inherits the polarization: for every nonzero mean-zero periodic twist the Gram limit of an independent twisted family is `Λ_χ A(G)`, `Λ_χ = (βA_φ/(K∫φ²)) S_{β+1}(χ) > 0`, and the complete family is eventually positive definite on it (characters and cosines included) | `periodic_twisted_sector_inherits`, `tendsto_twistGram_periodic` | proved |
| Mechanism B on short windows: the complete family is eventually positive definite on every independent family of horizon windows of length `≤ 3/5`, untwisted or mixed with windows twisted by a nonzero Ramanujan expansion | `short_windows_inherit`, `short_windows_inherit_exact`, `mixed_short_windows_inherit`, `hermQuad_weilWindowGram_nonneg` | proved |
| Mechanism B on the twisted sector: the complete family is eventually positive definite on every independent family twisted by a nonzero Ramanujan expansion (the count polarizes, nearby fibres inherit) | `twisted_sector_inherits`, `twisted_sector_inherits_exact`, `eventually_hermQuad_pos_of_tendsto`, `tendsto_twistGram` | proved |
| Twisted windows add no negative squares: mixed Gram matrices → `fromBlocks P_K 0 0 (Λ A(G))`, index `ind₋(P_K)` | `mixed_windowIndex`, `tendsto_mixedGram`, `hermNegIndex_mixedLimitGram` | proved |
| The conductor decomposition: for every Ramanujan expansion, `x + y → κQ(H) + 7J(1)/K ‖H‖²_{−8} + (7/K)Σ_m a_m² φ(m)J(m) ‖G‖²_{−8}`; untwisted ⊥ every mean-zero quiet twist | `graded_ramComb_criticalCurve_exact`, `graded_ramComb_criticalCurve_of_regularBulk`, `graded_layer_of_twist`, `cross_layer_vanishes_of_twist` | proved |
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
| The window index law: `P_K = κW(H) + (βJ/K)A(H)`, `A ⪰ 0`; monotone in `K`; Weil's index for large `K`; index `≥ n` on some family iff `≥ n` right zeros; Shannon bound `1 + 2A T(A/2)/π` for windows of length `A`; on an independent family the index counts the jump multiples `βJ/(−λ_i) < K` | `pencilGram_eq`, `hermQuad_aliasGram_nonneg`, `hermNegIndex_pencilGram_mono`, `eventually_hermNegIndex_pencilGram_eq`, `windowIndex_law`, `riemannHypothesis_iff_windowIndex_eq_zero`, `hermNegIndex_pencilGram_le_shannon`, `windowIndex_eq_card_jumpMultiples`, `hermNegIndex_add_smul_posDef`, `aliasGram_posDef`, `exists_windows_resolving_rightZeros`, `exists_windows_le_weilNegIndex` | proved |
| The primes of a window: departing jumps pay their creation; Markov form at level `⌊e^A⌋` | `primeJump_departing_eq`, `markovForm_eq_of_level`, `weilQuad_halfWeight_eq_markovForm` | proved |

## 9. Open research topics

1. **The window index as a counting function.** The index is bracketed by the right zeros a window
   length resolves and its Shannon number, vanishes below the aperture-independent multiple `K₀`, and is at
   most one on the first-prime windows. Open: close the gap between the resolved-zero count and the
   Shannon number, and locate the jump multiples `βJ/(−λ_i)` in terms of the right zeros.
2. **Bulk second order.** The collective `1/log N` term of fixed packets: the high zeros, read on the
   arithmetic side through primes in progressions to the moduli `e e'` (it needs Mertens constants in
   progressions).
3. **The ledger at the resolution height.** Below every height `N^θ`, `θ < 1`, the zeros are blind
   to pole-free packets and give the archimedean genus at the pole, so the count and the second order
   live on the zeros of height `≍ N/c`. Open: their ledger, i.e. mean values of conductor
   polynomials over the zeros the atoms resolve.
4. **A count for `κ Q(H)`.** On the twisted directions the second order is a count (Jordan totients,
   spectral Dirichlet series) or a count corrected by `L`-values of squared characters, bounded by
   the count. Open: a count, or a cardinality, carrying Weil's form on the untwisted windows; this is
   the RH-hard core of mechanism A inside the degeneration.
5. **Prime atoms in the jump measure.** The primes beyond a window pay their own creation, and on the
   first-prime windows the cosh hyperplane absorbs the prime `2`. Open: a count paying the creation
   potential of all primes `≤ e^A` acting on a window, and the count of the first Hecke graph `T₂`.
6. **The integer.** A source-defined bound forcing the window index to `0` at every multiple: a
   sectorial multiplier at logarithmic resolution (WD).
7. **Fakes and calibration.** Over `𝔽_q` the curve family is diagonal in the Frobenius angles, its
   rescaled limit is their Hurwitz form, a single orbit dilates by a scalar, and degeneration
   separates the pure curves from the golden fake; along the horizon a curve's family is stationary
   (translation invariance), so its only degeneration is in the atom width; and over `ℤ` a twist of
   any real frequency `u` carries the Hurwitz form of `u`, rational or not; the exponential rate of
   every curve is its zero width. Open: the complete family over `𝔽_q(T)`, horizon and bulk.

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
| Twisting the horizon window by a Ramanujan sum or a character transports the sign question | Twisted windows see no zero and are positive at every resolution; the sign question lives only on untwisted windows |
| The second order of a twisted window is always a count | For Ramanujan expansions it is (Jordan totients); for a complex character `ψ` it is the unit count plus `Re(c²ψ̄(−1)τ(ψ)²L(s, ψ̄²))`, an `L`-value of the squared character, bounded by the count, so positivity survives but the count alone does not describe it |
| Unconditional inheritance at small multiples gives RH | One fixed positive range `0 < K < βJ/(κC(β+1))` works on all window lengths. RH requires every positive multiple; finite-`N` convergence here remains family by family |
| A fake curve degenerates like a curve | A pure curve degenerates completely; the golden fake is self-similar, a fixed hyperbolic plane scaled by `E(w) ≥ c w e^{εw}`: no rescaled limit at any polynomial rate |

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
| ArithmeticCastelnuovoSeveri | `weilGram`, the index bound by the right zeros (`negIndex_weilGram_le_offLineCount`); the curve calibration: tower Gram `= log q‖g‖² spanGram`, index `= #{|β| > 1}` (`curve_towerGram_eq_smul_spanGram`, `curve_tower_pontryagin_law`), finite monodromy |

## 12. Success criteria

| Criterion | Status |
|---|---|
| First-order structure identified as a count | proved: `#ℙ⁷(ℤ/m)` |
| How zeros enter the second order, packets that see a zero classified | proved per zero and per window: bulk (pole only, positive), untwisted horizon windows (Weil summands), twisted horizon windows (none; their second-order term is positive, `≥ a/K`); uniformly over all zeros below `N^θ`, `θ < 1`: pole-free packets see none of them and the pole reads exactly the archimedean genus `κ y_1²(2 + γ − log 4π)` (proved) |
| Second-order term at the critical curve identified | horizon layer: exactly `κ Q(H) + (βJ/K)‖H‖²_{−(β+1)}` for every profile with bulk limit `s^βE₁ → J` (proved; tilted spline `7J(1)`); conductor-`m` Ramanujan windows: exactly `J_{β+1}(m)βJ/K ‖H‖²`, i.e. `7φ(m)J(m)/K` (proved for every `m ≥ 2`); every mean-zero periodic twist: `(βA_φ/(K∫φ²)) Σ_k |χ̂(k)|²(ζ(β+1,k/M) + ζ(β+1,1−k/M)) ‖H‖²`, positive for `χ ≠ 0` (proved; Ramanujan expansions give the Jordan totients, quadratic characters included; the twist `Re(cψ)` of a primitive character gives the unit count plus `q^{s−2}Re(c²ψ̄(−1)τ(ψ)²L(s, ψ̄²))`); the conductor decomposition untwisted ⊕ Ramanujan expansions, block-diagonal (proved); bulk second order: open |
| A count reading the primes inside the jump measure, creation potential paid on a window | the primes beyond the window pay their own creation (proved); on the first-prime windows (length `< log 2 + 1/50`) the cosh hyperplane absorbs the prime `2` and mechanism B holds there (proved, from CWS coercivity); a count for the primes inside a general window: open |
| Gluing theorem with exactly one negative square | AKG `κ + 1`; the zero ledger of the bulk is a positive pole gluing, computed: the low zeros give `κ y_1² (2 + γ − log 4π)` |
| An integer with a structural bound | the window index `ind₋(P_K)`: read by the complete family, monotone in the multiple, a step function jumping at the critical multiples `βJ/(−λ_i)` of an independent family, its supremum over families is the number of right zeros, between the resolved right zeros and the Shannon number on windows of a given length, unchanged by adding twisted windows, RH iff it vanishes, `0` below the uniform multiple `K₀ = βJ/(κC(β+1))` on windows of every length `A`, `0` on windows of length `≤ 3/5` and `≤ 1` on smooth windows of length `< log 2 + 1/50`, the only possible negative direction transverse to the cosh hyperplane (proved); a source-defined bound forcing it to `0` (WD's sectorial multiplier): open |
| Calibrations separating `ζ` from the fakes | negative result: ledgers, the count law (over every finite ring, so over `𝔽_q[T]`) and the aliasing constant carry no selection; selection enters only through `Q(H)`. Over a pure curve the family is diagonal in the Frobenius angles at every resolution and positive, and its rescaled limit is the Hurwitz form of the angles (proved); degeneration selects the pure curves: complete degeneration for a pure curve, exponential growth for the golden fake, whose limiting structure is a fixed hyperbolic plane scaled by `E(w)` (proved); finite monodromy and the window index `#{|β| > 1}` (ACS) |

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
horizon block twisted by a Ramanujan sum or a character reads no zero at all, is positive at every
resolution, and at the critical curve the window of prime conductor `p` carries exactly the
conductor-`p` count `7 (p − 1) J(p)/K ‖H‖²_{−8}`, and the Ramanujan window of every conductor `m`
carries `7 φ(m) J(m)/K ‖H‖²_{−8}`: the count of the first order reappears at second order on the
twisted directions. Distinct conductors are orthogonal at second order (Ramanujan sums of distinct
conductors at every offset, the untwisted block against every mean-zero twist), so the second-order
form is block-diagonal by conductor: Weil's form lives on the conductor-one block alone, and every
other block carries exactly its count. Inside a conductor block the characters refine the count:
the window of `Re(cψ)` carries the unit count corrected by the `L`-value `L(s, ψ̄²)` of the squared
character, characters of opposite parity are orthogonal and characters of equal parity couple
through `L`-values of their products; a single frequency `u` carries the Hurwitz form of `u`, the
form a Frobenius angle `u` carries over `𝔽_q`.

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
read by the complete family, jumps exactly at the critical multiples of the relative eigen-windows,
lies between the right zeros a window length resolves and its Shannon number, does not change when
twisted windows are added, and its supremum over families is exactly the number of right zeros. The
count of the first order pays the second order at small multiples, below the uniform multiple
`K₀ = βJ/(κC(β+1))` on windows of every length `A`; positivity at all multiples remains RH. On
every twisted block it is the whole second order. Every mean-zero periodic twist is read through its
spectrum: the mode `k/M` meets the atom harmonics at the shifted frequencies `j + k/M`, and the
second-order term is the power `|χ̂(k)|²` against Hurwitz constants; on independent twisted families
this form is positive definite and the nearby fibres inherit it, so mechanism B holds on the whole
twisted sector, and on every family of windows of length `≤ 3/5`, where Weil's form is known to be
nonnegative; up to `log 2 + 1/50` it holds on the cosh hyperplane, so there the window index is at
most one. Over a curve the Frobenius angles play the role of the frequencies: the family of
lattice tests is diagonal in them at every resolution, and its rescaled limit under dilation is the
Hurwitz form of the angles, as the Jordan-totient form is over `ℤ`. The type of the degeneration
selects: a pure curve degenerates completely, the golden fake grows exponentially, its outer
eigenvalue acting as monodromy of infinite order on a fixed hyperbolic plane. The exponential rate
of every curve is its zero width `max|Re s − ½|`, in both signs: the extreme values of Weil's form
on tests of length `ℓ` are `e^{δℓ}` up to polynomial factors, and `δ = 0` exactly for the pure
curves.

Below the resolution height the bulk is computed as well. Euler–Maclaurin at every order makes the
remainders of the conductor polynomials uniform in the zero, so the zeros of height `≤ N^θ`,
`θ < 1`, give a pole-free packet nothing and the pole exactly `κ y_1² (2 + γ − log 4π)`, the
archimedean genus. Everything else in the bulk lives on the zeros the atoms resolve, at height
`N/c`. What the field has not yet built is a mechanism that forces the sign of `Q` on horizon
windows: a count of the second order that sees the zeros.
