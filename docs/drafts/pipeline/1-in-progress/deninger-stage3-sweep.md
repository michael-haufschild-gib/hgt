# Deninger folder: stage 2 → stage 3 sweep

- **ID:** `deninger-stage3-sweep`
- **Stage:** 1-in-progress
- **Type:** WORK CARD (formalization sweep)
- **Target:** every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger`
  formalized unconditionally in Lean and moved to `3-formalized/new_scientific_knowledge/deninger`.

## Rules in force

- Lean proofs unconditional: no `sorry`, no `axiom`, no unproved analytic premise, no added
  hypothesis that is not part of the *statement* of the object.
- Verify every mathlib name in a `/tmp` scratch file before use.
- Build in the foreground, one process; `lake env lean <file>` while iterating, `lake build` for
  the audit; wire new modules into `RHTower.lean` (shared file — other sessions edit it too, so
  re-check for duplicate import lines after appending).
- Axiom audit must show exactly `propext, Classical.choice, Quot.sound`.

## Done

| Card | Modules |
|---|---|
| `deninger-cross-prime-closed-relation-saturation` | `RHTower/DeningerCalderonWittCrossPrimeClosedRelationNoGo` (extended with consequences 2 and 4) |
| `deninger-prime-log-height-kothe-calderon-source` | `RHTower/DeningerPrimeLogHeight`, `DeningerKotheComplete`, `DeningerPrimeLogHeightKothe`, `…Convolution`, `…Green`, `…Forms`, `…Mellin`, `…Power`, `…Cartan` (all new) |
| `deninger-balanced-word-height-bar-strict-contraction` | `RHTower/DeningerWordHeight`, `DeningerBarWord`, `DeningerBarInsert`, `DeningerBarSlice`, `DeningerBarDifferential`, `DeningerBarUnit`, `DeningerBarContraction`, `DeningerBarSector`, `DeningerBarFace`, `DeningerBarInsertComm`, `DeningerBarFibre`, `DeningerBarSquareZero`, `DeningerBarAlgebra`, `DeningerBarPower` (all new) |
| `deninger-linearized-milnor-first-sullivan-strict-primitive` | `RHTower/DeningerSetIndexedLinearization`, `DeningerExteriorPairSum`, `DeningerWordAlternating`, `DeningerSullivanPrimitive`, `DeningerSuspendedSource`, `DeningerSuspendedAlternating`, `DeningerSuspendedProduct`, `DeningerSuspendedPrimitive` (all new) |

## Reusable infrastructure now available

- `DeningerLattice = Nat.Primes →₀ ℤ`, `deningerHeight`, `deningerFreq`, with
  `deningerHeight_add_le`, `deningerHeight_nsmul`, `deningerHeight_inv_le_abs_freq`,
  `abs_deningerFreq_le_log_height`, `deningerHeight_summable_inv_sq`.
- `deningerKothe_exists_limit` (sequential completeness of any Köthe space),
  `deningerKothe_exists_finite_approx` (density of the finitely supported vectors),
  `DeningerKotheTendsto.coord`.
- `deningerHeightMul` : multiplier calculus with the exact seminorm loss.
- `deningerHeightConv` : convolution with submultiplicative seminorms, commutative, associative,
  unital.

## Remaining cards and what each needs

Numbering is the folder order; 13 cards remain in stage 2.

### The `S_exp(ℝ)` / Meyer analytic block (cards 1--7 below)

The shared layer now exists: `RHTower/DeningerExpSchwartz` gives `H_- = S_exp(ℝ)` as
`DeningerExpSchwartz`, a **subspace of `𝓢(ℝ, ℂ)`** cut out by `∀ A n, ∃ C, ∀ x,
e^{A|x|} ‖D^n f(x)‖ ≤ C` (so it inherits the whole Schwartz linear structure and the Schwartz
embedding is definitional), the translation `deningerShift` with `deningerShift_mem`, and
`deningerPeriodizationDefect L = 1 - τ_L` as `DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz`.
The one estimate everything rests on is `A|x| ≤ A|x+L| + |A||L|`, valid for both signs of `A`.
What else exists and must not be rebuilt:

- `RHTower/DeningerMeyerCap` and the whole `DeningerMeyer*` / `DeningerPoisson*` family
  (`DeningerMeyerCap`, `deningerMeyerCap_mem_iff`, `deningerPoissonLM` — the operator `Z` —
  `deningerPoissonSchwartz`, `deningerCapSchwartz`, `DeningerRadialNuclear`,
  `DeningerPoissonFourierReflection`, `DeningerPoissonInjective`, `DeningerPoissonCokernel`,
  `DeningerMeyerDilationFlow`, `DeningerMeyerRadialEndpoints`).  `H_∩` of the cards **is**
  `DeningerMeyerCap` and `Z` **is** `deningerPoissonLM`.
- `HTGeometry` strong-continuity of the dilation group, and mathlib's `SchwartzMap`,
  `fourierIntegral`, Poisson summation.

1. `deninger-euler-depleted-meyer-periodization-extension` — `S_exp(ℝ)`, `τ_L`, `Δ_p = 1 - τ_L`
   are **built**; what is left is the strict nuclear extension and the zero-periodization sector.
2. `deninger-cofinal-prime-periodization-tomography-instability` — cofinal tomography, nonclosed
   range, compact-orbit weight-zero no-go.
3. `deninger-half-density-floquet-euler-boundary-dichotomy` — half-density Floquet trace, all-prime
   Hilbert energy, Neumann inverse, leakage scalar `1 - p^{-1/2}`.
4. `deninger-cofinal-floquet-secondary-poisson-graph` — full-circle half-density lift, radical =
   reflected Calderón graph.
5. `deninger-critical-floquet-von-mangoldt-renormalization-wall` — diagonal subtraction, von
   Mangoldt autocorrelation, sign wall.
6. `deninger-mobius-fourier-commutator-poisson-kernel` — the analytic hub of the block.  Its four
   labelled theorems, in increasing cost:
   - `(6)` real-Fourier covariance `𝔖_μ(Jh) = -F(𝔖_μ h)` — pure formal consequence of `F² =`
     reflection and evenness once `𝔖_μ` is defined.  Cheapest.
   - `(34)`--`(35)` the causal von Mangoldt endpoint anomaly — **DONE**,
     `RHTower/DeningerCausalVonMangoldtWall`.  No distribution theory was needed: testing against
     `φ` makes it a numerical series.  `(41)` is then immediate from `(12)`.
   - `(45)` the Möbius connection identity.  mathlib has `ArithmeticFunction.log_mul_moebius_eq_vonMangoldt`
     (`log * μ = Λ`); convolving `(μ log) * ζ = -Λ` with `μ` gives `Λ * μ = -μ log`, which is `(44)`.
     Only a Fubini on a fixed positive ray is left.
   - `(8)` the unconditional saving — **DONE**, `RHTower/DeningerMertensSummatory`.  `M` itself is
     corpus-owned (`Sieve.mertensM`); only the transport to integer arguments and the `/N²` shape
     were new.
   - `(9)` the convergence — **DONE** in discrete form, `RHTower/DeningerMertensInvSquare`
     (`deningerMertensM_invSq_summable : ∑_N |M(N)|/N² < ∞`).  Condensation is essential: no power
     comparison works, since `exp(-c(log N)^{1/3})` dominates every `N^{-ε}`.  The condensed series
     `∑_k exp(-c k^{1/3})` is elementary — one term of the exponential series plus `x^{7/3} ≥ x²`.
   - `(11)`--`(12)` the all-moment `L¹` domain and zero mass — both arithmetic inputs are now
     built; what is left is the analytic step, discrete Abel summation
     `f_h(x) = -∑_n M(n)(H_h((n+1)x) - H_h(nx))` plus a decreasing majorant `G` for `H_h'`, so that
     `∫_0^∞ x G(nx) dx = n^{-2} ∫ y G(y) dy` feeds `(9)`.  `(15)` needs `1/ζ(σ) → 0` as `σ ↓ 1`.
   - `(5)` the exact kernel.  The hard one: Fourier-inversion bootstrap `(23)`--`(24)` then Poisson
     summation `(26)`.  Do it last.
7. `deninger-euler-gamma-mobius-connection-transgression` — all-prime Euler connection, strict
   PNT endpoint, Green–Stokes law.
8. `deninger-source-poisson-chain-lift-obstruction` — the TFAE is *formal* once `(5)` of card 6 is
   available; everything else it needs is already in the Meyer/Poisson family.

### The higher-structure block

9. `deninger-algebraic-cyclotomic-milnor-amplitude` — headline `(1)` `K_q^M(F) ⊗ ℝ = 0` for
   algebraic `F/ℚ`, `q ≥ 2`.  Bass–Tate + Garland/Borel; **the only genuinely research-scale gate
   in the folder.**  The corpus already owns Milnor `K`-theory and `HTGeometry/MilnorWittKTheory`.
10. `deninger-derived-rank-quotient-universal-property` — `E_∞`/∞-category statements.
11. `deninger-selective-positive-cell-h0-preservation` — its one-categorical shadow is **already
    formalized** (`DeningerPositiveCellDegreeZero`, `DeningerPositiveCellEquivariance`,
    `DeningerPrincipalConormal`, `DeningerMonicKaehlerLine`, `HTGeometry/MilnorWittKTheory`); what
    is left is the Milnor–Witt *sheaf* layer (oriented fundamental class, determinant twist, Gysin).
12. `deninger-pro-log-stein-kummer-residue-square` — log de Rham / coherent sheaves; the corpus's
    log-geometry layer (19 modules) is the starting point.
13. `deninger-strict-pro-log-collar-trace-kernel` — coherent sheaves and log de Rham complexes.

## Gates

- [x] 4 of 17 cards promoted
- [x] entire word-height algebra built
- [x] `b² = 0` for the bar differential
- [x] `S_exp(ℝ)` layer built — `RHTower/DeningerExpSchwartz`
- [ ] Möbius–Fourier commutator built (unlocks cards 6--8 of the analytic block); its section 5
  (`(34)`--`(35)`, the causal endpoint anomaly) is done
- [ ] the higher-structure block

## Log

- 2026-08-10 — Built `(9)` in discrete form (`RHTower/DeningerMertensInvSquare`).  Worth
  remembering *why* condensation: `∑_N exp(-c(log N)^{1/3})/N` fails every power comparison because
  `exp(-c(log N)^{1/3})` dominates `N^{-ε}` for every `ε`; only the dyadic grouping separates it,
  and the condensed series is elementary from one term of the exponential series.
- 2026-08-10 — Built `(8)` in summatory form (`RHTower/DeningerMertensSummatory`).  **Caught a
  duplication mid-write**: the Möbius summatory function is already corpus-owned as
  `Sieve.mertensM` (in `Sieve/MoebiusMaximalWindow.lean`, with `mertensSup` and the PNT form
  `tendsto_abs_mertensM_div`); the first draft redefined it.  Grep `def.*[Mm]ertens` before adding
  anything summatory-shaped.
- 2026-08-10 — Built `(44)`--`(45)`, the Möbius connection (`RHTower/DeningerMobiusConnection`).
  Trap worth remembering: `ArithmeticFunction R` has its own `Neg` instance, *not* the ring's
  `HasDistribNeg` one, so `neg_mul` will not rewrite `(-f) * g` into `-(f * g)` and `ring` fails on
  the convolution ring.  Carry the sign inside `pmul` and every identity stays sign-free.
- 2026-08-10 — Built the product-fibre interchange and the pointwise Möbius right inverse
  (`RHTower/DeningerMobiusRightInverse`).  The interchange is cleanest as a *sigma decomposition*:
  the map `⟨N, q ∈ N.divisorsAntidiagonal⟩ ↦ q` is injective with range the nonzero-product locus,
  so `Function.Injective.tsum_eq` plus `Summable.tsum_sigma` does it — no fibrewise-summation
  machinery.  Shifting the outer index by one (`(n,k) ↦ (n+1,k)`) avoids needing `tsum_eq_zero_add`
  and its extra summability side condition.
- 2026-08-10 — Built the canonical Möbius preimage (`RHTower/DeningerMobiusPreimage`).  The point
  is that absolute convergence on a ray needs no cancellation in `μ` at all: pulling back along
  `log` turns the exponential weight into two-sided power decay, and the inverse-square half alone
  gives `‖H_h(nx)‖ ≤ (C/x²)/n²`.
- 2026-08-10 — Built the shared `S_exp(ℝ)` layer (`RHTower/DeningerExpSchwartz`).  Realizing it as a
  *submodule of `𝓢(ℝ, ℂ)`* rather than a new structure removed the whole module/topology
  boilerplate and makes the Schwartz embedding definitional.
- 2026-08-10 — Built section 5 of the Möbius–Fourier card (`RHTower/DeningerCausalVonMangoldtWall`).
  Two corpus assets carried it: `Sieve.summable_log_div_sq` and `Sieve.mertensFirst_lower`.  The
  distributional statement `(34)` needs no distribution theory — testing against `φ` makes it a
  numerical series, and the only input is the mean-value bound at the origin.
- 2026-08-10 — Promoted `deninger-linearized-milnor-first-sullivan-strict-primitive`.  The card's
  `(7)` asks for an odd derivation extending `d(sigma omega) = omega`; **the corpus already owned
  one** (`HTGeometry.deningerOddDerivation`, with `_leibniz`, `_ι`, `_algebraMap`, `_comp_self`),
  so `d h = id` reduced to the two-coproduct identity.  The topological half needed a new alphabet:
  `DeningerSusp = Γ ⊕ (Γ × Γ)` with `H(inr(m,n)) = H(m)H(n)`, whose letterwise counting series is
  `S + S²` — finite, so the same geometric argument gives nuclearity.  Two facts made the
  estimates trivial rather than combinatorial: expanding a head pair preserves the product height
  exactly (so it costs exactly one factor `R`), and on the alternating part all `binom(r,2)` terms
  of the averaged primitive coincide, so the average is one term.
- 2026-08-10 — Promoted `deninger-balanced-word-height-bar-strict-contraction`.  The alphabet
  `{1} ⊔ (Γ∖{0})` is `Γ` with the zero character as the unit; the fibre of the `j`-th face is then
  the pair of unit insertions at `j` and `j+1`.  `b² = 0` follows from the simplicial pairing
  `(j,j') ↦ (j'-1,j)` on double fibres, matched by `deningerInsertUnit_comm`.
- 2026-08-10 — Swept the folder, promoted `deninger-cross-prime-closed-relation-saturation` and
  `deninger-prime-log-height-kothe-calderon-source`, and built the reusable Köthe completeness,
  density, multiplier and convolution layers listed above.
