# Architecture Guide for Agents

**Purpose**: Tell an agent where new output goes, how the Lean ledger and the research drafts
are organized, and how to add to each.
**Read this when**: starting a work session, adding a theorem, or writing/extending a draft.
**Stack**: Lean 4 + mathlib `v4.30.0` (the ledger); Markdown drafts (the field); `mpmath` for
numeric pre-certification (run on runpods, not committed unless archived).

## Two channels, one rule

This project has exactly two kinds of output. Decide which you are producing **before** you write.

| You are producing… | Goes in | Truth standard |
|---|---|---|
| A machine-checked elementary fact | `formal/GaloisForLFunctions/` + the audit | Must build, zero `sorry`, axiom-clean |
| A new object / conjecture / brick / "what if" | `docs/drafts/<name>.md` | Air-marked; conjectural is fine, mislabeling is not |
| A precise statement of where the difficulty sits | the relevant draft, a new `## n. Brick #k` section | Honest tiering; never claim near-closed |

Never let the two blur. A Tier C statement (RH, LI, DSS, the spectral Tannakian category) is
**never** a Lean theorem and **never** an `axiom`. See `@docs/meta/styleguide.md`.

## Repo map

| Path | Purpose |
|---|---|
| `formal/GaloisForLFunctions.lean` | Library root; imports the formal modules. |
| `formal/GaloisForLFunctions/Core.lean` | Tier A core: `σ`-involution, `cpow` inversion/critical-line, `ℚ`-LI of `{log p}`, prime products. |
| `formal/GaloisForLFunctions/OrbitFreeness.lean` | Additive corollaries of `ℚ`-LI (the "no diagonal resonance" form). |
| `formal/GaloisForLFunctions/EulerProduct.lean` | The field's First Theorem: Euler product ⟺ Bohr-lift factorization; the pre-spectral firewall, including a concrete mod-5 fake coefficient witness. |
| `formal/GaloisForLFunctions/MultiQDifference.lean` | Local first-order `q`-difference equation for the Euler factor. |
| `formal/GaloisForLFunctions/ArchimedeanLane.lean` | Exact coordinate identity for the archimedean additive shift: `p^{-(s+1)} = p^{-1}p^{-s}` for each prime and as a simultaneous function equality; not the Gamma-factor shift, completed category, FE, or RH. |
| `formal/GaloisForLFunctions/Resonance.lean` | Finite-support resonance bookkeeping: coordinate vs diagonal resonance lattices, plus the arithmetic prime-log annihilator `Λ=0` and its finite slices. |
| `formal/GaloisForLFunctions/FlatConnection.lean` | Pairwise cocycle/curvature algebra, finite-truncation integrability, and the finite co-extension flatness identity for a fundamental-solution symbol. |
| `formal/GaloisForLFunctions/HolonomyAbelian.lean` | Group-theory core of abelian holonomy: homomorphic images of commutative groups are abelian, and pairwise-commuting monodromy generators generate an abelian subgroup; not PV/Tannakian realization or eigenvalue-lattice classification. |
| `formal/GaloisForLFunctions/DSSDeterminant.lean` | DSS determinant criterion skeleton: nontrivial kernel iff determinant zero. |
| `formal/GaloisForLFunctions/MultiplicityEstimate.lean` | Concrete DSS auxiliary-vanishing determinant criterion for `V_{j,n}=N_n^{z_j}`. |
| `formal/GaloisForLFunctions/SecularMoments.lean` | Object-X Li/secular pointwise triangular identities in both directions, plus conjugate-pair moment realness. |
| `formal/GaloisForLFunctions/SecularNewton.lean` | Finite secular Newton duality between power sums and elementary symmetric coefficients. |
| `formal/GaloisForLFunctions/MultisetNewton.lean` | Newton's identities transferred from symmetric polynomials to finite multisets; B29 inversion engine only. |
| `formal/GaloisForLFunctions/MomentReconstruction.lean` | Finite Newton recursion linking power sums and elementary symmetric functions. |
| `formal/GaloisForLFunctions/SpectralTorelli.lean` | Finite spectral polynomial faithfulness, constant-term/Vieta product bridge, and self-dual coefficient reality; not infinite reconstruction. |
| `formal/GaloisForLFunctions/SpectrumGenericity.lean` | Finite DSS genericity face: elementary-symmetric spectrum coordinates of `n` indeterminate points are algebraically independent over `ℚ`; not infinite DSS or RH. |
| `formal/GaloisForLFunctions/PowerSumTorelli.lean` | Finite power-sum Torelli: first `n` power sums determine an `n`-point multiset, distinct configurations are separated by a bounded moment, and the second/third Newton-Girard secular identities. |
| `formal/GaloisForLFunctions/SmoothNumbers.lean` | Bijection between finite prime-exponent vectors and bounded smooth frequencies; diagonal auxiliary-form identity. |
| `formal/GaloisForLFunctions/RankOneCohomology.lean` | Rank-one scalar cocycles, coboundaries, and Picard quotient skeleton. |
| `formal/GaloisForLFunctions/KoszulCohomology.lean` | Additive first Koszul differentials plus finite Koszul Euler-characteristic rank count. |
| `formal/GaloisForLFunctions/DiagonalCharacter.lean` | Bohr character and finite auxiliary sums on the diagonal become Dirichlet monomials/polynomials. |
| `formal/GaloisForLFunctions/BoundaryModulus.lean` | Scalar boundary-radius normalization and the diagonal `Re(s)=1/2` unit-norm criterion. |
| `formal/GaloisForLFunctions/SatakeTensor.lean` | Finite diagonal Satake tensor parameters and local-factor double product. |
| `formal/GaloisForLFunctions/SatakeInterval.lean` | Unitary `GL₂` Satake parameter trace is real and lies in `[-2,2]`; not Sato-Tate equidistribution or Ramanujan for automorphic forms. |
| `formal/GaloisForLFunctions/ExteriorSatake.lean` | Finite exterior/Adams Satake coefficient skeleton: local-factor coefficients are signed elementary symmetric data, the top exterior power is the Satake product, exterior powers and local-factor coefficients vanish above rank, and unitary exterior/power-sum data obey binomial/rank norm bounds. |
| `formal/GaloisForLFunctions/LocalFactorDuality.lean` | Inversion-closed/self-dual Satake multisets give equal local factors after `α ↦ α⁻¹`; not the global functional equation. |
| `formal/GaloisForLFunctions/CompleteHomogeneous.lean` | General `Symᵏ` Satake character as complete-homogeneous symmetric evaluation, with `Sym⁰`/`Sym¹` base cases, the unitary dimension/norm bound, and the degree-one `h₁=e₁` bridge to exterior data. |
| `formal/GaloisForLFunctions/WCoordinate.lean` | Li/Bombieri-Lagarias `w=1-1/z` scalar identities: norm-square defect and FE inversion. |
| `formal/GaloisForLFunctions/ArakelovW.lean` | Arakelov/Cayley `w=1-1/ρ` coordinate: FE inversion, critical-line unit circle, right-half-plane disk test, and injectivity. |
| `formal/GaloisForLFunctions/SigmaOrbit.lean` | The critical line as the fixed locus of the FE-conjugation involution `σ ∘ conj`. |
| `formal/GaloisForLFunctions/BerryKeating.lean` | Scalar Berry-Keating coordinate `u=s(1-s)`: FE invariance, critical-line formula `1/4+γ²`, positive-ray floor, and guarded off-line non-reality; no Hilbert-Polya operator. |
| `formal/GaloisForLFunctions/CarrierPickKernel.lean` | Finite carrier Pick/Herglotz skeleton: real/lower-half-plane poles give Herglotz/PSD witnesses; upper-half-plane single and conjugate-pair poles break it in one-point tests, with explicit negative Pick vectors. |
| `formal/GaloisForLFunctions/CarrierCauchy.lean` | Carrier Cauchy specialization: the FE multi-pair carrier vectors `{w_i=e_i+a_i, u_i=e_i-a_i}` are linearly independent for distinct off-line poles and `2k` noncolliding nodes, yielding exact negative inertia `k` for the factored finite carrier matrix; not the infinite carrier or RH. |
| `formal/GaloisForLFunctions/SecularHankel.lean` | Finite real-spectrum Hankel moment matrix as a positive-semidefinite Gram matrix. |
| `formal/GaloisForLFunctions/KreinLangerInertia.lean` | Abstract real and complex Hermitian inertia bounds, one-point and diagonal-block negative subspace witnesses, rank-one/factored lower-bound bridge lemmas, conditional exact inertia from surjective factored evaluation maps, square Cauchy linear independence, square and rectangular linear-independence-to-evaluation-surjectivity bridges, standalone FE conjugate-pair factorization, and explicit FE conjugate-pair/multi-pair `κ₋`/`κ₊` upper-bound factorizations. |
| `formal/GaloisForLFunctions/MeasureCarrier.lean` | Stage-2 measure carrier infrastructure: finite measures on `ℝ` give Herglotz carriers and Hermitian/positive-semidefinite Pick-kernel matrices with Hadamard closure; finite spectra are atomic measures; not the raw `ξ` zero-counting measure. |
| `formal/GaloisForLFunctions/CayleySchur.lean` | Pointwise Cayley/Schur disk bridge, upper-half-plane to open-disk Cayley map, Blaschke factor/product bounds, finite truncated Szegő kernel positivity plus Hadamard closure, forward factored-Schur direction, and de Branges-Rovnyak diagonal nonnegativity; not full de Branges/Krein-Langer converse theory. |
| `formal/GaloisForLFunctions/MultiplierScaling.lean` | Finite polynomial scaling floor: nonzero real substitution `x ↦ c x` preserves real-rootedness. |
| `formal/GaloisForLFunctions/FieldConjectures.lean` | Statement-level Lean `Prop`s for DSS and the realization problem, plus the proved finite carrier alias `carrierHerglotz_iff_onLine`; no conjecture axioms. |
| `formal/GaloisForLFunctions/AdamsOperations.lean` | Finite Satake Adams/power-sum algebra: tensor multiplicativity, contragredient conjugation, self-dual norm-square identities, Satake-side nonnegative second moments, tensor determinant formula, isobaric additivity, and Adams composition/unit laws. |
| `formal/GaloisForLFunctions/SymPowerPlethysm.lean` | Finite `GL₂` symmetric-power/Chebyshev plethysm identities for the prime/Satake side; not zero-side period comparison. |
| `formal/GaloisForLFunctions/SatakeSymPower.lean` | `GL₂` symmetric-power character equals Chebyshev `S_k` of the trace, with dimension `k+1` and the unitary temperedness bound; not Sato-Tate equidistribution or Ramanujan. |
| `formal/GaloisForLFunctions/SuperzetaResolvent.lean` | B23 verdict witness: the per-zero geometric series is the resolvent `(1−rX)⁻¹`, the superzeta generating function is the additive resolvent trace `Σᵢ(1−rᵢX)⁻¹` (not a product), and its `k`-th coefficient is the secular power sum `P_k=Σᵢrᵢᵏ`; the finite spectral-side witness that the superzeta carries no Euler product, not the analytic continuation or no-second-`G_L` claim. |
| `formal/GaloisForLFunctions/SatoTateMoment.lean` | D3 §3′ Sato–Tate analytic core: the Sato–Tate measure moments vanish, `∫₀^π U_k(cosθ)·(2/π)sin²θ dθ = δ_{k,0}`, and the full orthonormality `∫₀^π U_j U_k (2/π)sin²θ dθ = δ_{j,k}` (the `U_k`=Symᵏ are μ_ST's orthogonal polynomials / spectral basis), with the supporting cosine/Fourier orthogonality lemmas (`∫cos(cθ)=sin(cπ)/c`, `∫sin(mθ)sin(nθ)=(π/2)δ_{m,n}`); the measure-side only, not the prime-average convergence (BLGHT) or the equidistribution theorem. |
| `formal/GaloisForLFunctions/SatakeReality.lean` | Self-dual/conjugation-invariant finite Satake multisets have real moments; not Sato-Tate or Ramanujan. |
| `formal/GaloisForLFunctions/FunctionalEquationParity.lean` | Negation/FE-reflection symmetric finite multisets have vanishing odd and centered odd power sums; FE parity bookkeeping only. |
| `formal/GaloisForLFunctions/ExteriorParity.lean` | Exterior-power parity skeleton: `∧ⁿ(c·id)=cⁿ·id` and `∧ⁿ(-id)=(-1)ⁿ·id`; no full cohomology ring. |
| `formal/GaloisForLFunctions/OscillatorAlgebra.lean` | Coefficient-sequence oscillator algebra skeleton: `[X,Y]=-4H`, `[H,X]=2X`, `[H,Y]=-2Y`; no Weil representation or Hodge-Riemann positivity. |
| `formal/GaloisForLFunctions/EHKoszulDuality.lean` | The `e–h` (`∧•`/`Sym•`) Koszul duality welding B30 to B5: the geometric series inverts a local factor in `ℂ⟦X⟧`, the `∧•`/`Sym•` generating series have coefficients `(−1)ᵏeₖ`/`hₖ` (complete-homogeneous generating function via the `Sym↔Finsupp` multiplicity bijection), and `Σ_{i+j=k}(−1)ⁱeᵢhⱼ=0` for `k≥1`; finite Satake-side shadow only, not the infinite-prime Koszul-homology limit (`ω`). |
| `formal/lakefile.toml`, `lean-toolchain` | Pinned build config (`v4.30.0`). |
| `scripts/check_axioms.sh` | The axiom + `sorry` audit (the ledger gate). |
| `docs/drafts/` | The five founding drafts of the field (the SEARCH channel). |
| `docs/meta/styleguide.md` | Immutable Lean + draft style rules. |
| `README.md` | Public scope: the draft↔Lean theorem ledger table. Keep it in sync when a theorem lands. |

Detailed per-file contents and domain boundaries: Serena memory `codebase_structure`.

## The field in one screen

The drafts build *multi-`q`-difference Galois theory for L-functions*. Minimal vocabulary
(full glossary: Serena memory `field_vocabulary`):

- **The object.** `L(s)=∏_p L_p(p^{-s})` lifted to the infinite polydisc `𝔻^∞` via `x_p:=p^{-s}`
  (the Bohr lift), pulled back along the **diagonal** `s↦(p^{-s})_p`. The field's sole object
  is this diagonal ∩ the zero-variety, pinned `σ`-real.
- **The wings.** `G_L = (𝕋^∞, multiplicative wing) ×_seam (W_ℝ, archimedean wing) ⋊ ⟨σ⟩`.
  Multiplicative wing = **free** (dense flow by unique factorization) and **zero-blind**;
  archimedean wing = **the frontier** (zeros, positivity, transcendence). The **seam** is the
  additive↔multiplicative gluing where the difficulty lives.
- **The tiers** (`infinite-base-…-L-functions.md` §12 — the formalization compass):
  - **Tier A** — formalizable now (elementary; mathlib has the tools). *This is the Lean tree.*
  - **Tier B** — deferred (needs infrastructure mathlib may lack; build behind A).
  - **Tier C** — open frontier (archimedean positivity, DSS, RH). Never a Lean theorem.
- **Bricks.** Drafts advance by numbered "Brick #k" sections, each computing or stating one
  load-bearing fact, ending with a `**House status**` line tracking what checks.

### The eight drafts

| Draft | Role |
|---|---|
| `infinite-base-difference-galois-for-L-functions.md` | District D2: the RH spine (11 bricks), the formalization tiers (§12). The Lean tree formalizes its Tier A. |
| `hypertranscendental_galois_field_foundations.md` | The foundations: objects, DSS conjecture, fake classification, the spectral Tannakian gap, the height wall + secular-constants resolution. |
| `multi-q-difference-galois-foundations.md` | The general discipline (D1): infinite-base `q`-difference modules; boundary = ergodic theory. |
| `automorphic-continent-rankin-selberg-ramanujan.md` | District D3: the Langlands world as rank-`d` multi-`q` modules — Ramanujan=Lyapunov boundedness, Rankin–Selberg=`⊗`, functoriality=Tannakian morphisms, Sato–Tate=eigenphase equidistribution, CM/non-CM=the D5 §8/§10 dynamics. Candidate Langlands group = a difference-Galois group. |
| `transcendence-theory-nonholonomic-functions.md` | District D4: infinite-base Siegel–Shidlovsky for non-holonomic values. |
| `dynamics-continent-lyapunov-avila-morales-ramis.md` | District D5: boundary cocycles, Lyapunov exponents, the difference Morales–Ramis correspondence; welds the three continents at the zeros (`spec(H_L)=Spec(L)`). Carries a runpod Lyapunov referee certificate (§8). |
| `geometric-rosetta-function-field-continent.md` | District D6: the function-field Rosetta stone — over `F_q(C)` the keystone is Grothendieck's theorem, RH is Deligne (Weil II), Ramanujan is purity, Conjecture 4 is monodromy-Tannakian. Localizes the entire `ℚ`-frontier to one missing brick: the `F₁` cohomology-with-Frobenius. |
| `rh-holographic-pseudorandom-boundary.md` | The "embassy" (D7): RH as boundary unitarity / iterated-logarithm; explicitly SEARCH, not ledger. |

## How to add a Lean theorem (Tier A/B only)

**Pre-flight (mandatory):**
1. Confirm the statement is Tier A or a provable Tier B fragment. If it is Tier C, it does **not** go in Lean — write it in a draft.
2. Numerically pre-certify the statement with `mpmath` if it has any numeric content.
3. Verify every mathlib name you intend to use against this toolchain with a scratch file
   (`cd formal && lake env lean /tmp/probe.lean` containing `have := @Some.Name`). Do **not**
   trust recalled mathlib names. See `@docs/testing.md`.

**Template** (match the surrounding file; full conventions in `lean_proof_conventions`):

```lean
/-- One-line statement of what this is, in the field's vocabulary. -/
theorem my_new_fact (args) : conclusion := by
  ...
```

**Steps:**
1. Pick the module by topic (Core / OrbitFreeness / EulerProduct / MultiQDifference), or add a
   new `GaloisForLFunctions/<Name>.lean` and `import` it from `GaloisForLFunctions.lean`.
2. Place it inside `namespace GaloisForLFunctions` / `noncomputable section`, with a `/-- … -/` docstring.
3. `cd formal && lake build` — must compile clean.
4. If the theorem is citable (a brick), add its name to `scripts/check_axioms.sh`, **bump the
   expected count**, and run `bash scripts/check_axioms.sh` — must say PASS.
5. Update the `README.md` ledger table (draft target ↔ Lean theorem name).
6. If it closes a draft brick, change that brick from "draft-claimed" to "ledger-proven" in the draft.

## How to extend a draft

1. Add a new `## n. Brick #k (status): <claim>` section at EOF (append-only: use a here-doc).
2. Air-mark every claim: `[THEOREM]` / `[PROVED HERE]` / `[CONJECTURE]` / `[OPEN CORE]`, or an
   explicit "verified / open" split. State which wing and which side of the seam it addresses.
3. End with a `**House status**` line: which bricks check, what the open core now is.
4. Cross-reference companion drafts by filename. Keep the status banner at the top honest.

Full draft conventions: Serena memory `draft_writing_conventions`.

## Common mistakes

- **Don't** add a `sorry` "to be closed later", or an `axiom` for a conjecture. **Do** leave Tier C in the drafts.
- **Don't** trust a recalled mathlib lemma name. **Do** probe it with `lake env lean` first.
- **Don't** call a draft brick "ledger-proven" until the audit is green. **Do** keep the README table truthful.
- **Don't** import parent-workspace files or paste private logs here. **Do** keep this subtree standalone.
- **Don't** edit the tree to run `#print axioms`. **Do** use a `/tmp` scratch file.

## On-Demand References

| Domain | Serena memory |
|---|---|
| Per-file contents, domain boundaries | `codebase_structure` |
| Lean idioms, name-verification workflow, audit-script mechanics | `lean_proof_conventions` |
| Field glossary (wings, seam, tiers, `G_L`, DSS, fakes, `P_k`) | `field_vocabulary` |
| Draft status banners, air-marking grades, brick/house format | `draft_writing_conventions` |
