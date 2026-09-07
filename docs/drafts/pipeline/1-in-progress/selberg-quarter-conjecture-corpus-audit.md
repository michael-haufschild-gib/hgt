# Selberg quarter conjecture: corpus and proof-chain audit

- **ID:** SELBERG-QUARTER-AUDIT
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User-requested corpus investigation, 2026-09-07.
- **Statement:** Determine which existing Lean results can support a proof that every nonzero weight-zero Maass cusp form for a congruence subgroup has positive hyperbolic Laplacian eigenvalue at least 1/4; distinguish formalization gaps from open mathematics.

## Plan

1. [x] Search the declaration corpus and prior research; inspect exact hypotheses.
2. [x] Check primary literature and assemble candidate proof chains.
3. [x] Audit relevant Lean declarations and record proven inputs, missing foundations, and open mathematical steps.

## Status

Investigation complete; conjecture remains open. No dependency-closed proof chain was found in the corpus. Existing results plus the formalization follow-up below supply the algebraic homogeneous-space dictionary; a concrete analytic Maass cusp realization with real `C²` regularity, positive-Laplacian eigen-equation, and decay at every integral cusp; explicit spherical principal/complementary-series Harish-Chandra modules; their exact unitarity interval and irreducibility there; scalar symmetric-power exponent amplification; symmetric-power character algebra; Gamma/Dirichlet-series infrastructure; and actual Eisenstein calculations. They do not supply Fourier zero-term/quotient-`L²` equivalence, the Laplacian-to-derived-Casimir theorem, the generic-unitary classification theorem for arbitrary `GL(n,ℝ)` representations, or the arithmetic exclusion of complementary-series cusp representations.

The research candidate remains at stage 1. This is an audit and infrastructure formalization, not a paper proof or a formalization of Selberg's conjecture.

## Target and normalization

Let Γ be a congruence subgroup of SL₂(ℤ), with positive hyperbolic Laplacian

`Δ = −y²(∂ₓ² + ∂ᵧ²)`.

For every nonzero weight-zero Maass cusp eigenfunction `f`, the target is
`Δf = λf ⇒ λ ≥ 1/4`. Constants have eigenvalue zero and are excluded. Cuspidality requires the constant Fourier term to vanish at every cusp.

Write `λ = s(1−s)`. An exceptional eigenvalue has
`λ = 1/4 − ν²`, `0 < ν < 1/2`, and `s = 1/2 ± ν`.
The conjecture excludes these representations from the congruence cuspidal spectrum. Self-adjointness and nonnegativity alone allow this interval.

The established general benchmark is Kim–Sarnak's `ν ≤ 7/64`, giving
`λ ≥ 1/4 − (7/64)² = 975/4096 = 0.238037109375`.
No accepted improvement to the full quarter bound was found in the literature search. The unresolved range after that benchmark is `0 < ν ≤ 7/64`.
[Sarnak, equations (24)–(25)](https://publications.ias.edu/sites/default/files/FieldNotesCurrent.pdf).

## Corpus search and scope

Used `python3 scripts/formal_tools.py research` for 16 queries. The first query refreshed the index; subsequent queries used `--no-refresh`. Focused queries used AND matching, `--limit 100`, and one or two declarations per module to discover candidate modules; exact source reads then audited the cited claims. Broad discovery was not an exhaustive audit of every unrelated spectral or Casimir theorem.

| Query | Matching declarations | Modules | Interpretation |
|---|---:|---:|---|
| `selberg eigenvalue` | 7 | 2 | Scalar spectral-parameter modules |
| `"symmetric power"` | 17 | 9 | Includes Satake/Chebyshev algebra |
| `"maass" "cusp"` | 167 | 12 | Mostly Eisenstein raising/lowering and cusp expansions |
| `"congruence subgroup"` | 4 | 2 | Own-tree hits are unrelated local-field unit filtrations |
| `"kuznetsov"` | 1 | 1 | Finite Kloosterman carrier; missing spectral average explicitly recorded |
| `"selberg trace"` | 2 | 1 | Abstract Connes kernel periodization |
| `"ramanujan" "conjecture"` | 0 | 0 | Does not establish absence alone; checked related source directly |
| `"selberg" "pole"` | 49 | 19 | Selberg-class Gamma and continuation infrastructure |
| `"pole purchase"` | 20 | 3 | Conditional positivity and width bounds |
| `"amplifier" "escape"` | 0 | 0 | No direct result |
| `"spectral gap"` | 230 | 86 | Many unrelated graph, prolate, and finite-dimensional results |
| `"poincare" "inequality"` | 5 | 3 | Circle/torus inequalities |
| `"casimir"` | 553 | 59 | Mostly finite-dimensional/quantum and other geometric operators |
| `"hecke"` | 3 | 1 | No Maass Hecke-operator theory found |
| `"laplacian" "hyperbolic"` | 16 | 7 | Actual Eisenstein equations and local geometric models |

The initial OR discovery query returned 3897 matches across 1354 modules; it served only to choose focused queries. Supplementary `rg` searches checked own-tree source, mathlib source, and prior pipeline documents. Search counts are a dated snapshot, not a proof of nonexistence under all possible terminology.

`docs/architecture.md` and `docs/testing.md` were absent. Read project entrypoints and relevant Serena memories. Old August memories saying there is no Selberg-class layer are stale; current source contains one. Old documents claiming there are no Eisenstein series are likewise too broad now.

## What is actually proved

Paths below are relative to the repository root.

| Existing result | Exact content | Missing connection |
|---|---|---|
| `HTGeometry/SelbergSpectralParameter.lean`, `GaloisForLFunctions.HTGeometry.selbergSmallEigenvalue_offCritical` | For a real number `0 < λ < 1/4`, both `1/2 ± sqrt(1/4−λ)` are distinct real off-critical points in `(0,1)` | Does not assert any such number occurs, or cannot occur, as an automorphic eigenvalue |
| `RHTower/SelbergExceptionalAnalogy.lean`, `RHTower.spectralPoint_mem_Ioo`, `RHTower.no_real_preimage` | Exceptional scalar parameters and impossibility of a genuinely complex offset squaring to a real number | Reality still permits real complementary parameters |
| Same file, `RHTower.simple_pole_no_exceptional` | `m = 1+j` and `m = 1` imply `j = 0` | No automorphic proof of the budget identity; no constructed exceptional eigenvalue count |
| `RHTower/SatakeSymPower.lean`, `GaloisForLFunctions.symPowerGL2_eq_chebyshevS` | Symmetric-power character of `(z,z⁻¹)` equals the corresponding Chebyshev polynomial | No automorphic representation or lift is constructed |
| Same file, `GaloisForLFunctions.symPowerGL2_norm_le` | Character norm is at most `k+1` under `‖z‖=1` | Unit-modulus Satake parameters are an input; using this as Ramanujan would be circular |
| `RHTower/SatakeReality.lean`, `GaloisForLFunctions.selfDual_moment_real` | Conjugation-invariant multisets have real power sums | Reality is weaker than unit-modulus parameters |
| `RHTower/ConnesSelbergPeriodization.lean`, `GaloisForLFunctions.RHTower.connes_selberg_trace` | Diagonal integral of a periodized kernel equals the sum of translated diagonal integrals, under measurability and summability | Not the hyperbolic Selberg trace formula with cusp spectrum, scattering, and orbital terms |
| `RHTower/ThetaCuspHawkingBMEisensteinActualEigenEquation.lean`, `RHTower.d4BM_rawEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue` | Primitive Poincaré Eisenstein sum satisfies `y²(∂ₓ²+∂ᵧ²)E=s(s−1)E` for `Re(s)>1`, with actual derivative and convergence work | Different Laplacian sign; Eisenstein family in a convergence chamber, not the general cuspidal spectrum |
| `RHTower/ThetaCuspHawkingBMAngularScalarEquation.lean`, `RHTower.D4BMAngularSeries.scalarCusp_hyperbolicLaplacian` | Full explicit scalar Eisenstein cusp field satisfies the actual coordinate eigen-equation on `y>0` | “Cusp field” includes constant terms; it is not a theorem about Maass cusp forms |
| `RHTower/SelbergClass/Basic.lean` and descendants | Pole-safe continuation, Gamma products, functional equations, and many downstream analytic consequences for supplied class data | No construction of arbitrary Maass L-functions or their symmetric powers |
| `HTGeometry/FiniteAmplifierFrame.lean`, `HTGeometry.frame_width_of_exclusion` | Width bound inside an explicitly hypothesized finite pole/zero channel model | No theorem that every possible Selberg proof belongs to that model |
| `HTGeometry/ShiftLatticeVerification.lean` | Degree-two, conductor-one shift-spectrum gap and growth constant independent of archimedean parameter | This observable cannot distinguish `ν=0` from `ν>0` by its value alone |
| `RHTower/MaassHomogeneousSpaceCorrespondence.lean` and `RHTower/CongruenceMaassCorrespondence.lean` | Exact equivalence between Γ-invariant functions on the upper half-plane and right-stabilizer-fixed vectors in the right-regular function representation, specialized to `Gamma`, `Gamma0`, and `Gamma1` | Smoothness, moderate growth, cuspidality, square-integrability, and Laplace/Casimir compatibility are not yet represented |
| `RHTower/MaassSpectralTransport.lean` | Conjugates any linear operator across the homogeneous-space equivalence and proves exact preservation of eigen-equations, nonzero eigenvectors, and eigenvalues | The concrete hyperbolic Laplacian still must be proved equal to the automorphic Casimir under this transport |
| `RHTower/MaassCuspAutomorphicCorrespondence.lean` | Defines the positive hyperbolic Laplacian through real Fréchet derivatives, real `C²` Maass eigenfunctions, and decay after every integral cusp scaling; gives an exact equivalence with spherical automorphic vectors for arbitrary real subgroups and for `Gamma`, `Gamma0`, and `Gamma1` | Pointwise cusp decay is not yet proved equivalent to zero Fourier constant terms or quotient `L²`; the concrete Laplacian is not yet identified with the derived right-regular Casimir |
| `RHTower/MaassCyclicAutomorphicRepresentation.lean` | Takes the group-algebra span of the nonzero spherical Maass vector and constructs its actual cyclic right-regular subrepresentation; proves both generator and subrepresentation are nonzero | Does not give irreducible decomposition, Hilbert completion, adelization, or local factorization |
| `RHTower/AutomorphicCoinduction.lean` | Identifies the right-regular automorphic function representation with mathlib's algebraic coinduced representation | No topology, Hilbert completion, irreducible decomposition, or local-global restricted tensor product |
| `RHTower/RealUpperBorelPrincipalSeries.lean` | Constructs the real upper Borel, its positive real-power characters, their exact unitary locus `{0}`, and the associated algebraically coinduced principal series | Does not identify algebraic coinduction with the explicit spherical Harish-Chandra model or formalize the full unitary dual |
| `RHTower/RankOneComplementarySeriesBound.lean` | The first spherical raising-norm factor is `1/4−ν²`; its factorized quadratic form is positive definite exactly when `|ν| < 1/2` | This file isolates only the first obstruction; the ambient invariant form and adjointness are supplied by the complementary-series modules below |
| `RHTower/RealSphericalHarishChandra.lean` | Constructs the spherical finite-support `K`-type model, proves the three `sl₂` commutators, computes Casimir scalar `s²/4`, and proves the shifted Casimir acts by Selberg eigenvalue `1/4−ν²` at `s=2ν` | Does not connect the algebraic Casimir to the coordinate hyperbolic Laplacian or identify this explicit model with algebraic coinduction |
| `RHTower/RealSphericalIrreducibility.lean` | Proves every `(𝔤,K)`-submodule is bottom or top for `|s|<1`, by extracting one nonzero `K`-type and generating all integer `K`-types with nonvanishing raising/lowering coefficients | Irreducibility is for the explicit spherical algebraic model; no Hilbert completion or classification of arbitrary local representations |
| `RHTower/RealSphericalUnitarity.lean`, `RealSphericalComplementaryWeights.lean`, and `RealSphericalComplementarySeries.lean` | Derive necessity of `|s|<1`, construct positive product weights and the diagonal invariant Hermitian form for every parameter in that interval, and prove the exact unitarity loci `(-1,1)` and `(-1/2,1/2)` | Exact for the explicit spherical `SL₂(ℝ)` Harish-Chandra model; no arbitrary `GL(n,ℝ)` generic-unitary classification or Hilbert completion |
| `RHTower/SymmetricPowerArchimedeanExponents.lean` | Positive-degree `d` exponent packet is `(d-2j)ν`; its generic half-strip locus is exactly `|ν| < 1/(2d)`, and membership for all degrees or all even degrees forces `ν=0` and hence `λ=1/4` | No automorphic symmetric-power lift or infinity-parameter compatibility is constructed |
| `RHTower/GenericUnitaryExponentBounds.lean` | A finite packet of explicit spherical rank-one models is unitarizable iff every exponent lies in `(-1/2,1/2)`; for symmetric-power packets, all positive degrees or all even degrees have exact locus `{0}` | The theorem does not prove that an arbitrary generic unitary `GL(n,ℝ)` representation decomposes into these rank-one models; that is the missing local classification bridge |
| `RHTower/SphericalExponentPacketUnitarity.lean` | Builds one product Harish-Chandra model and one Hermitian form for a finite exponent packet; proves existence of a positive invariant form iff every exponent lies in `(-1/2,1/2)`, and proves exact `{0}` loci for all/all-even symmetric-power degrees | This closes the full explicit product-model statement, but does not identify arbitrary generic `GL(n,ℝ)` representations with that model |
| `RHTower/SelbergExceptionalSphericalModel.lean` | For every bundled `0<λ<1/4`, constructs `ν=sqrt(1/4−λ)∈(0,1/2)`, proves the spherical model is unitarizable and irreducible with shifted Casimir `λ`, and proves some positive even symmetric-power packet is nonunitarizable | To contradict automorphy, one still needs actual compatible unitary symmetric-power lifts and the local compatibility theorem |

All source paths in the first column start with `formal/GaloisForLFunctions/`.

Mathlib already defines `CongruenceSubgroup.Gamma`, `Gamma0`, and `Gamma1`, with finite-index infrastructure in `formal/.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`. The group definitions do not need to be recreated.

Another assumption trap: `SelbergGammaData.mu_re_nonneg` is a structure field. In the natural even-Maass factor `Γ((s+ν)/2)Γ((s−ν)/2)`, one shift is negative if `ν>0`. Thus constructing that particular presentation as this class datum already excludes the exceptional even case. For odd parity, shifts `(1±ν)/2` need not be negative; class membership is not itself a universal proof of the eigenvalue conjecture.

`SelbergLedgerCeiling.lean` proves inequalities for an explicit Poisson-kernel model. Its broad trace-formula interpretation is not a formalized spectral dictionary. Neither those inequalities nor the finite-amplifier frame establish a universal impossibility theorem for other approaches.

## Chain A: symmetric-power amplification

The standard conceptual route is

`Maass cusp eigenfunction → cuspidal GL₂ representation → compatible symmetric-power lifts of unbounded degree → archimedean generic-unitary bounds → ν=0 → λ≥1/4`.

For hypothetical exceptional parameter `ν>0`, degree `m` has real exponents
`mν,(m−2)ν,…,−mν`. Suitable unitary generic lifts impose `mν<1/2`. An unbounded set of such degrees is incompatible with positive `ν`. Even degrees suffice and remove the parity character at infinity. The lift must match the infinity parameter, not merely almost all finite primes. Noncuspidal lifts require their isobaric constituents and normalization to be controlled.
[Sarnak, Section 1, especially (13) and (18)](https://publications.ias.edu/sites/default/files/FieldNotesCurrent.pdf).

- **Known mathematics needing Lean infrastructure:** Maass/automorphic dictionary, local representation theory, symmetric-power parameter matching, and generic unitary exponent bounds.
- **Open mathematical input:** construct the required lifts for general Maass forms in unbounded degree, with the stated local compatibility and constituent control.
- **Corpus reuse:** symmetric-power/Chebyshev algebra and final scalar manipulations. These are a small part of the analytic burden.
- **Quantifier check:** one fixed-degree lift only bounds `ν`; it does not force `ν=0` through this argument. This is a limitation of this argument, not a no-go theorem for every finite construction.

Newton–Thorne's all-degree symmetric-power results concern holomorphic modular forms; they cannot be applied to arbitrary weight-zero Maass forms.
[Newton–Thorne](https://arxiv.org/abs/1912.11261).

## Chain B: eliminate forced zeros using character twists

A more focused analytic target is suggested by the Luo–Rudnick–Sarnak method. For exceptional `π` with parameter `ν`, the archimedean Rankin–Selberg factor has the form

`Γ_R(s+2ν) Γ_R(s)^2 Γ_R(s−2ν)`.

It has a pole at `σ₀=2ν`. Twisting by a primitive even Dirichlet character preserves that infinity factor. Holomorphy of the completed twisted product at `σ₀∈(0,1)` forces its finite part to vanish there. Therefore a theorem producing one admissible character `χ` with

`L_finite(2ν,(π⊗χ)×π̃) ≠ 0`

would exclude the exceptional form. The character can be chosen with sufficiently large conductor to avoid self-twist complications. This is a sufficient target, not a proved nonvanishing theorem. It specializes the classical pole/forced-zero mechanism; the new burden is nonvanishing down to arbitrarily small positive `2ν`.
[Luo–Rudnick–Sarnak, introduction and (1.4)–(1.5)](https://www.math.tau.ac.il/~rudnick/papers/lrsGAFA.pdf).

- **Known mathematics needing Lean infrastructure:** actual twisted Rankin–Selberg L-functions, Gamma-factor identification, analytic continuation and holomorphy.
- **Open mathematical input:** sufficiently strong twist-family nonvanishing, with no positive lower cutoff on the parameter being excluded. Existing nonvanishing only in a restricted region gives partial bounds.
- **Corpus reuse:** meromorphic orders, Gamma poles, Dirichlet characters, finite sums, and analytic estimates. Actual automorphic coefficients still need to enter the formal model.
- **Research assessment:** this is a narrower target to investigate than full functoriality. No existing corpus theorem was found that proves the required family nonvanishing.

## Chain C: trace-formula certificates or a sharp quadratic-form inequality

The direct spectral route would build the actual cuspidal spectral decomposition and Selberg/Kuznetsov formula, then produce admissible arithmetic test functions that exclude each interval `[975/4096,1/4−ε]`, for every level and every `ε>0`.

One sufficient certificate would be a nonnegative cuspidal spectral sum with weight at least one on the forbidden interval and total strictly below one. Trace normalization, continuous-spectrum subtraction, multiplicities, oldforms, characters, and all cusps must be accounted for. Establishing these certificates uniformly enough to cover every level and arbitrarily small `ε` is the open input; writing down a trace identity alone is not it.

This approach does prove finite-level results: Booker–Lee–Strömbergsson establish the conjecture for `Γ₁(N)` with `N≤880`, and `Γ(N)` with `N≤226`. Their Theorem 1.1 is unconditional; the separate Artin classification theorem has an Artin-conjecture assumption.
[Booker–Lee–Strömbergsson, Theorem 1.1](https://arxiv.org/html/1803.06016v2).

Equivalent variational target on the cuspidal form domain:

`∫ |∇_hyp f|² dμ ≥ (1/4) ∫ |f|² dμ`.

This is a reformulation, not an intermediate breakthrough. A new congruence/Hecke-sensitive mechanism must produce the quarter constant. Existing circle/torus Poincaré inequalities and finite matrix Casimir gaps do not transfer to these quotients without a proved comparison. Nonnegativity of Δ only gives the zero lower bound.

The Kloosterman modules contain useful exact finite identities, but `RHTower/Sieve/KloostermanSharedHybridCollapse.lean` explicitly distinguishes their inverse-residue correlation from the missing Kuznetsov spectral average.

## Recommended next work

1. Prove Fourier zero-constant-term and quotient-`L²` consequences for the new analytic Maass cusp interface, then identify its coordinate positive Laplacian with the derived right-regular Casimir.
2. Identify the algebraically coinduced real principal series with the explicit spherical Harish-Chandra model and formalize only the needed generic `GL(n,ℝ)` classification theorem. Do not package exponent bounds as structure fields.
3. For a theorem achievable without solving a new conjecture, target a known fixed-level quarter bound or a precisely chosen published spectral/trace theorem. This is still substantial formalization work.
4. For research toward the full conjecture, audit Chain B's actual twist-family mean and its error terms, or identify an independent source of unbounded compatible lifts for Chain A. Further generic positivity wrappers do not close either input.

## Verification and limitations

Ran `lake env lean /tmp/selberg_corpus_audit.lean` from `formal/`; exit 0. Imported the cited modules, checked mathlib group names and parameter fields, and ran `#print axioms` on 13 relevant declarations. All reported only subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or extra mathematical axiom appeared. This checks the imported declarations in the installed build, not a fresh full-project rebuild or formal validation of every proposed mathematical chain.

Ran `python3 scripts/formal_tools.py lint`; exit 1. At that snapshot the error was:

`owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ChiLogDerivHigherDerivatives`

The gate also reported pre-existing large-file warnings. This audit did not modify the unrelated module or umbrella. Concurrent unrelated repository edits were present.

Post-formalization audit ran `lake env lean` and targeted `lake build` for every new Chain A module;
all passed. Capstone `#print axioms` checks reported only `propext`, `Classical.choice`, and
`Quot.sound`. The final `python3 scripts/formal_tools.py lint` run passed with existing large-file
warnings.

Excluded the search result *On Exceptional Maass Forms*, arXiv:2011.09054, from the proof chain: its current arXiv page marks it withdrawn. Search abstracts alone are not evidence of an available theorem.
[Withdrawal status](https://arxiv.org/abs/2011.09054).

## Log

- 2026-09-07 — Created before substantive proof-chain analysis. Ran `scripts/formal_tools.py research` and direct source searches.
- 2026-09-07 — Completed 16-query audit, primary-source checks, and 13-declaration Lean axiom inspection. Recorded three conditional routes, actual corpus reuse, formalization gaps, and open mathematical inputs. No proof of Selberg's conjecture found or claimed.
- 2026-09-07 — Added ten closed Lean infrastructure modules for Chain A: homogeneous-space and congruence correspondences, spectral transport, algebraic coinduction, real-Borel principal-series characters, the spherical Harish-Chandra model and shifted-Casimir calculation, invariant-form unitarity obstruction, rank-one positivity, finite-packet positivity, and all-degree symmetric-power exponent amplification. Targeted builds passed. Capstone `#print axioms` checks reported only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-09-07 — Added analytic Maass cusp/spherical-automorphic correspondence and its nonzero cyclic right-regular representation; explicit complementary-series product weights and invariant positive Hermitian form; exact spherical unitarity locus; complementary-interval `(𝔤,K)`-irreducibility; exact finite-packet/symmetric-power rank-one unitarizability loci; a single positive invariant form on the full product packet with exact half-strip criterion; and the exceptional-eigenvalue-to-local-model bridge proving failure in some even symmetric-power degree. Targeted builds passed; capstone axiom checks again reported only `propext`, `Classical.choice`, and `Quot.sound`.
