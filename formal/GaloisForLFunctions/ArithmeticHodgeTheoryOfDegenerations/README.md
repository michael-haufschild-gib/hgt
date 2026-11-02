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
second order, and isolates the one theorem the field still needs.

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
it lives in the horizon layer. On the arithmetic side the horizon layer is computed exactly: below
the atom grid (`|τ| ≤ N e^{−A}`) the block's Dirichlet polynomial is a Riemann sum of `ĥ` and is
small by Kuzmin–Landau; above it the atoms alias, and the aliasing tail is bounded by mean values
of Dirichlet polynomials and the decay `(1 + |u|)^{−p}` of the atom transform. **Past the critical
curve the horizon layer, divided by the overlap, converges to `κ_φ Q(H)`; at the critical curve
`c⁸ = K log N` it lies between `κ_φ Q(H) + a/K` and `κ_φ Q(H) + b/K` with `0 < a ≤ b`.** The
second-order term of the degeneration is Weil's form on the horizon windows plus a coercive aliasing
term of exact order `1/K`.

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
| Jordan coefficient | ADT `jordanCoefficient`, `jordanTotient` | `J(m) = lim c⁷E_m(c)`; `J_k(m)` |
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
  (`|τ| ≳ N`), where the atoms undersample the synthesized test.
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
- **Critical multiples.** If the rescaled family converges to `J + K X`, positive definiteness is
  inherited and a negative direction is eventually negative; for `J ⪰ 0` the admissible multiples
  form a closed initial segment, positive semidefinite terms never remove a multiple, and negative
  directions persist as `K` grows.

**C. Integer.** source-defined sectorial multiplier ⇒ window index `0` on every window ⇒ RH (WD).
In AHD's language the integer is the number of critical multiples below `K` of a horizon window:
it is `0` for every window and every `K` exactly under RH, and grows to the number of seen right
zeros as `K → ∞`.

**G. Gluing.** One rank-one gluing at the pole creates the Mertens function (Redheffer, ADT) and
the one extra negative square (`κ + 1`, AKG). The zero ledger of the bulk is itself a rank-one
gluing at the pole, of positive sign.

**Cal. Calibration.** The ledger theorems hold for every zero configuration: they carry no
selection. The count law holds for every quotient of `ℤ`: it carries no selection either. Selection
must come from the bulk second-order term or from a carrier.

## 6. Questions and answers

| Question | Answer | Lean |
|---|---|---|
| What is the first-order structure of the degeneration, and why is it polarized? | The point count of projective space: `J(m) = J(1) #ℙ⁷(ℤ/m)`, `#ℙ^{k−1}(ℤ/m) φ(m) = J_k(m)`. Weight strings are Hensel towers, the tensor law is CRT. It is positive because it is a cardinality. | `jordanCoefficient_eq_projPoints`, `natCard_projPoints_mul_totient`, `natCard_primVec_eq_jordanTotient`, `projPoints_prime_mul`, `projPoints_prime_pow_succ`, `primVecCRT` |
| How do the zeros enter the second-order term of fixed packets? | Only through the pole coefficient: `(log N/c) W_ρ/∫g² → m_ρ κ y_1²/(ρ(1−ρ))`, real part `> 0`; at the critical curve `c⁷ W_ρ/∫g² → K m_ρ κ y_1²/(ρ(1−ρ))`. Same for every finite window. | `tendsto_bulkLedger`, `tendsto_bulkLedger_criticalCurve`, `tendsto_sum_bulkLedger`, `re_sum_mult_div_nonneg` |
| Which packets can see an individual zero? | Not fixed conductor packets (positive pole charge only). Horizon blocks: `W_ρ/(c∫g²) → κ W_ρ(H,H)`, Weil's summand of the synthesized test. | `tendsto_horizonLedger`, `Wsummand_halfWeight` |
| Is the horizon layer Weil's form? | Yes. In the iterated limit (horizon, then window of zeros) windows exhaust `κ W(H,H)`. Directly: past the critical curve (`(1+log N)/c^p → 0`) `c⁻¹⟨Wx,x⟩ → κ Q(H)`; at `c^p/log N → K_c` it is `κ Q(H)` up to `K/K_c`; for every schedule the error is `ε + K(1+log N)/c^p`. | `horizon_layer_two_sided`, `tendsto_horizon_layer_supercritical`, `horizon_layer_criticalCurve`, `horizon_window_exhaustion` |
| What is the second-order term at the critical curve (obstacles summary 2.5.4)? | On horizon blocks: Weil's form of the synthesized test (window radius `A/2`, any `A`) plus a coercive aliasing term of exact order `1/K`: eventually `κ Q(H) + a/K − ε ≤ c⁻¹⟨Wx,x⟩ ≤ κ Q(H) + b/K + ε`. At small multiples every horizon block is positive; at large multiples it is Weil's criterion. | `horizonForm_eq`, `integral_aliasing_le`, `horizon_layer_coercive`, `horizon_layer_lower_criticalCurve`, `horizon_layer_criticalCurve`, `eventually_horizon_pos_of_small_multiple` |
| Which structure polarizes the second-order term? | On the bulk, the Li-type pole charge (positive per zero). On the horizon layer, the aliasing energy at finite `K` and nothing else at `K = ∞`: the limit is Weil's form, polarized exactly under RH. | `re_inv_mul_one_sub_pos`, `horizon_layer_coercive`, `riemannHypothesis_iff_horizon_layer` |
| Where does the horizon term of a conductor live? | Only at `e = 1`: `D_e(s;N) − [e=1]N^s/s → ζ(1−s)J_s(e)`. | `tendsto_conductorDirichlet_sub_horizonTerm`, `conductorDirichlet_eq` |
| Is positivity at one fixed multiple of the critical curve RH? | No: it gives `κ Q(H) ≥ −K/K_c` on every window (sub-RH); conversely every window with `Q(H) < 0` is negative at every multiple `K_c > K/(κ|Q(H)|)`. RH is positivity at every multiple. | `weilQuad_halfWeight_ge_of_horizon_nonneg`, `eventually_horizon_neg_of_weilQuad_neg` |
| What does a second-order term do to positivity? | Admissible multiples form a closed initial segment; inheritance below the critical multiple, failure above; negative directions persist. | `admissible_of_le`, `isClosed_admissible`, `admissible_mono`, `neg_persists`, `eventually_pos_of_tendsto`, `eventually_not_nonneg_of_tendsto` |
| Can the ledger or the first-order count select `ζ`? | No: both hold for every zero configuration and every quotient of `ℤ`. | statements quantified over `ZeroConfig`; `natCard_primVec_eq_jordanTotient` |

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

**To build.**
- The exact aliasing energy of a horizon block: stationary phase in the chirp bands
  `τ ∈ [2πkN e^{−A}, 2πkN]`.
- Uniform ledgers: explicit horizon-law remainders `O(|s|σ(e)N^{Re s−1})` with the zero-free region,
  summed over zeros up to a growing height.
- Nilpotent-orbit and `SL₂`-orbit models (Schmid, Cattani–Kaplan–Schmid); Néron–Tate on
  `ℤ[ℚ_{>0}^×]`; Arakelov `h⁰` on lattices of growing rank; Zwegers–Vignéras and Voronoi; Lévy
  forms with prime atoms; Wiener–Hopf factorization; function-field calibration.

## 8. Pillar theorems

| Pillar | Lean | Status |
|---|---|---|
| Count law: the Jordan limit counts `ℙ⁷(ℤ/m)`; Hensel towers; CRT | `jordanCoefficient_eq_projPoints`, `natCard_projPoints_mul_totient`, `projPoints_prime_mul`, `projPoints_prime_pow_succ`, `primVecCRT` | proved |
| Horizon law: only the pole conductor has a horizon term | `tendsto_conductorDirichlet_sub_horizonTerm`, `tendsto_conductorDirichlet_of_zeta_eq_zero` | proved |
| Bulk zero ledger, at every schedule and at the critical curve; positivity of the pole charge | `tendsto_bulkLedger`, `tendsto_bulkLedger_criticalCurve`, `re_inv_mul_one_sub_pos`, `tendsto_sum_bulkLedger` | proved |
| Horizon ledger: Weil summands of the synthesized test | `tendsto_horizonLedger`, `Wsummand_halfWeight`, `tendsto_horizonDirichlet` | proved |
| Exhaustion: windows of zeros give Weil's form of the synthesized test | `horizon_window_exhaustion`, `tendsto_sum_horizonLedger` | proved |
| Critical-multiple calculus | `admissible_of_le`, `isClosed_admissible`, `admissible_mono`, `neg_persists`, `eventually_pos_of_tendsto`, `eventually_not_nonneg_of_tendsto` | proved |
| Horizon layer past the critical curve = Weil's form; at it, up to `O(1/K)` | `horizon_layer_two_sided`, `tendsto_horizon_layer_supercritical`, `horizon_layer_criticalCurve` | proved |
| Exact horizon formula on the arithmetic side | `horizonForm_eq`, `weilQuad_eq_pole_add_symbol`, `weilQuad_halfWeight_eq` | proved |
| Kuzmin–Landau decay below the grid; aliasing tail above it | `norm_horizonDirichlet_le_div`, `horizonDirichlet_sq_div_le`, `integral_aliasing_le` | proved |
| The horizon criterion: RH iff every horizon block is nonnegative past the critical curve | `riemannHypothesis_iff_horizon_layer`, `riemannHypothesis_iff_halfWeight_nonneg` | equivalence |
| Coercivity: the aliasing part is at least `a log N/c⁸`; sandwich `κQ(H) + a/K ≤ · ≤ κQ(H) + b/K`; subcritical positivity | `horizon_layer_coercive`, `horizon_layer_lower_criticalCurve`, `eventually_horizon_pos_of_small_multiple`, `aliasing_lower` | proved |
| Critical multiple of a window: one multiple controls Weil's form up to `O(1/K)`; a negative window is negative at every multiple `K > K₀/(κ|Q(H)|)` | `weilQuad_halfWeight_ge_of_horizon_nonneg`, `eventually_horizon_neg_of_weilQuad_neg` | proved |
| Exact aliasing constant at the critical curve (Conjecture HB, sharp form: `a = b`) | — | open |

## 9. Open research topics

1. **Conjecture HB, sharp form.** The sandwich gives
   `κ_φ Q(H) + a/K ≤ c⁻¹⟨Wx,x⟩ ≤ κ_φ Q(H) + b/K` at `c^p = K log N`. The sharp form identifies the term:
   `c⁻¹⟨Wx,x⟩ − κ_φ Q(H) → K⁻¹ 𝒜_φ(H)` with `𝒜_φ(H) = a_φ ∫ e^{−(β+1)y} H(y)² dy`, `a_φ > 0` — the local
   pole energy `E_1(c e^y)` of the atoms at depth `y`, read in the chirp bands `τ ∈ [2πkNe^{−A}, 2πkN]`
   by stationary phase. It would make the critical multiple of a window the ratio of the aliasing
   norm to the negative part of Weil's form.
2. **Bulk second order.** The collective `1/log N` term of fixed packets (the high zeros, read on the
   arithmetic side through primes in progressions to the moduli `e e'`).
3. **Uniform bulk ledger.** All zeros of height `≤ N^{1/2−ε}` together contribute `o(c/log N)` to every
   pole-orthogonal fixed packet (horizon-law remainders, zero-free region, `Σ m_ρ/(1 + γ²) < ∞`).
4. **Count past first order.** A count (cardinality or log-count) for the second-order term, or the
   classification of counts with a Poisson-type duality that read the test component.
5. **Prime atoms in the jump measure** and the creation potential (corpus: RAPT/RHTower Markov
   forms); the count of the first Hecke graph `T₂`.
6. **The integer**: a sectorial multiplier at logarithmic resolution (WD).
7. **Calibration** over `𝔽_q(T)`: the count law over `𝔽_q[T]/m` and the function-field horizon layer.

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
| RHTower | partial zeta sums (`zetaStripError`), Euler–Maclaurin carriers, summability of Weil series |

## 12. Success criteria

| Criterion | Status |
|---|---|
| First-order structure identified as a count | proved: `#ℙ⁷(ℤ/m)` |
| How zeros enter the second order, packets that see a zero classified | proved per zero and per window: bulk (pole only, positive), horizon layer (Weil summands) |
| Second-order term at the critical curve identified | horizon layer: Weil's form plus a coercive term of exact order `1/K` (proved), exact past the critical curve (proved); sharp aliasing constant and bulk second order: open |
| A count reading the primes inside the jump measure, creation potential paid on a window | open (corpus foothold on prime-free cycles) |
| Gluing theorem with exactly one negative square | AKG `κ + 1`; zero ledger of the bulk is a positive pole gluing |
| An integer with a structural bound | open |
| Calibrations separating `ζ` from the fakes | negative result: ledgers and counts carry no selection |

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
through Weil's summand of the test it synthesizes, and windows of zeros exhaust Weil's form.

On the arithmetic side the horizon layer is computed exactly. Below the atom grid the block is a
smooth test seen at the density `log n`; above it the atoms alias, and the aliasing costs at most
`(log N)/c^p` after division by the overlap. Past the critical curve the horizon layer of the
complete family, divided by the overlap, converges to `(∫φ)²/∫φ²` times Weil's form of the
synthesized test; at the critical curve it is Weil's form plus a coercive aliasing term of exact
order `1/K`. The second-order term of the degeneration is Weil's form on the horizon windows,
carried over the Jordan polarization of the bulk; at small multiples the aliasing pays any negative
part, at large multiples nothing does, and RH is the statement that every horizon block is nonnegative past the critical curve. What
the field has not yet built is a mechanism that forces this sign: the count of the second order.
