# New-route conjecture loop (route 3 successor search)

- **ID:** new-route-conjecture-loop
- **Stage:** 1-in-progress
- **Type:** hgtl7 conjecture loop — conjecture → proof or kill → pivot, until a new route survives
- **Source:** route 3 (`docs/reports/route-proposals/route3.md`) residuals; frontier LA, WD; user directive 2026-09-26
- **Statement:** find a producer mechanism, not a receiver, whose open step is not excluded by a countermodel

## Rules of the loop
- Each cycle states one exact conjecture, its mechanism, the attack, a verdict
  (`FALSE` / `CIRCULAR` / `REDISCOVERED` / `BRIDGE` / `INSIGNIFICANT` / `SURVIVES`), and the survivor.
- Kill standard: a countermodel satisfying every input the producer consumes, or a false intermediate claim.
  "Open step ⇔ RH" is a reduction, not a kill.
- A receiver (a new equivalent of RH) is recorded as `BRIDGE` and does not end the loop.

## Cycles

### C1 — Gröchenig PF₁: `Λ = 𝓕⁻¹[1/ξ(½+·)] ≥ 0`
- **Conjecture.** `τ ↦ 1/ξ(½+τ)` is positive definite on ℝ (the Pólya-frequency order-one shadow of
  Gröchenig's criterion "RH ⟺ Λ is a Pólya frequency function", arXiv 2007.12889, which states that even
  PF₁ is unknown).
- **Attack.** Contour shift: for `|x| > π/4`, `Λ(x) = Σ_ρ e^{−|γ_ρ||x|} e^{± i b_ρ x} R_ρ`, where `b_ρ = β−½`.
  The leading term is set by the zeros of smallest ordinate; it is positive iff those are critical (for a
  simple critical lowest zero the coefficient is `−1/Ξ'(γ₁) > 0`). An off-line quadruple at height `γ > γ₁`
  enters with relative size `e^{−(γ−γ₁)|x|}` and is dominated: its factor
  `𝓕⁻¹[|1+τ²/ρ²|^{−2}] ∝ e^{−γ|x|}(γ sin b|x| + b cos b|x|)` has negative lobes of size `e^{−γπ/b}`, below
  the `e^{−γ₁π/b}` tail of the critical part.
- **Verdict.** `INSIGNIFICANT` for RH. PF₁ is decided by the lowest zeros, which is a finite
  verification (a computation, excluded). Every fixed PF order is blind to off-line zeros above a height
  proportional to the order, the same angle blindness as Katkova's `ξ₁ ∈ PF₄₄` (Taylor sequence) and the
  corpus's KR-JPR (Jensen `d = o(n)`).
- **Survivor.** Countermodel for "PF_m ⇒ RH" at any fixed `m`: a critical PF_∞ product times one
  off-line quadruple at height `γ* ≫ m/b*`.

### C2 — height-shifted Gröchenig functions
- **Conjecture.** For every `T` outside the ordinate set, `τ ↦ sgn Ξ(T) / ξ(½+τ+iT)` is positive definite,
  and this family of order-one conditions detects off-line zeros at every height.
- **Mechanism.** `ξ(½+τ+iT) = Ξ(T−iτ)` and `Ξ(T+s)` is real entire of order one. Under RH it is in the
  Laguerre–Pólya class, so Schoenberg makes `1/Ξ(T+s)` the Laplace transform of a PF_∞ density
  `Λ_T` (a signed sum of independent exponentials with rates `|γ_k − T|`). Positive definiteness is then
  Bochner. Conversely, PF₁ of `Λ_T` plus Landau's theorem for two-sided Laplace transforms of positive
  functions forces the singularities nearest the imaginary axis (the zeros of nearest ordinate on each side
  of `T`) to include real points. Letting `T` range over the Voronoi cell of each ordinate gives:
  **PF₁ at every height ⇒ every zero ordinate carries a critical zero.**
- **Cluster law (exact).** For a cluster of `m` critical zeros and off-line pairs `γ ± i b_j` of
  multiplicity `k_j` at one ordinate, the leading asymptotic of `Λ_T` is the inverse Laplace transform of
  `1/(s^m Π(s²+b_j²)^{k_j})`.
  - `m = 0`: purely oscillating, so PF₁ fails. Lone off-line pairs are detected.
  - `m = k = 1`: gives `(1−cos bx)/b² ≥ 0`, so PF₁ holds on the boundary and PF₂ fails (log-concavity
    breaks at the zeros `2πℤ/b`).
  - `m = 1, k = 2`: gives `(1 − cos bx − (bx/2) sin bx)/b⁴`, negative infinitely often.
  - In general PF₁ needs critical multiplicity to dominate the off-line multiplicity at every ordinate, and
    PF₂ additionally excludes the triple cluster "simple critical plus simple off-line pair".
- **Verdict.** `BRIDGE` (receiver). The detection is exact exponential separation of the nearest cluster
  as `x → ∞`, with no log loss, but proving positivity at large `x` near an ordinate *is* the cluster
  statement. There is no producer.
- **Survivor.** "PF₁ at all heights ⇒ no ordinate is dominated by off-line zeros" (necessity proved
  above; sufficiency open). Correction (same day): the combination "PF₁(∀T) ∧ ordinate injectivity"
  adds nothing, because ordinate injectivity alone is RH (an off-line `ρ` and its reflection `1−ρ̄` share
  an ordinate). PF₁(∀T) only forces a critical companion at every off-line ordinate.

### C3 — Hermite–Biehler pair from a shifted line
- **Conjecture.** `E_h(z) = ξ(½+h−iz)` is Hermite–Biehler for some fixed `h ∈ (0,½)` by an argument using
  only the Euler product on `Re s > 1` and the FE.
- **Attack.** HB for `E_h` means `|ξ(½+h+y+it)| > |ξ(½+h−y+it)|` for `y > 0`. By the Hadamard product
  this holds iff no zero has `Re ρ > ½+h`. So the family `h ↦ E_h` is exactly the zero-free-strip ladder
  (Lagarias 2006; the same ladder as PM's "rigidity at exponent a").
- **Verdict.** `REDISCOVERED`. Any fixed `h < ½` is quasi-RH, and no mechanism is known for it (MUST-261).

### C4 — which input class could reach case (c) of the deformation law
- **Conjecture.** "Beurling multiplicativity + positivity of Λ + a Riemann-type FE" is a class of case (c)
  of the deformation law: large, with every member satisfying RH.
- **Attack.** The classical region is optimal for Beurling systems (Diamond–Montgomery–Vorhauer), so
  multiplicativity plus integer counting gives no strip. Vinogradov–Korobov beats the Beurling-optimal
  region by using the additive structure of `ℤ`. Adding a degree-one FE to Beurling data forces the
  integers to be a self-dual Poisson (crystalline) set; the only positive-integer-weight example with
  multiplicative support is `ℤ`, which is Hamburger-rigid (case (b)). Degree-`d` FE with Beurling form
  gives Dedekind-type functions, for which GRH is open.
- **Verdict.** `REDISCOVERED` (it is the deformation-obstruction law, MUST-389). Open side question:
  Beurling–Hamburger rigidity (Beurling system + degree-one FE ⇒ ζ); not RH-relevant.

### C5 — Littlewood mean of `log|ζ|` on the line
- **Conjecture.** `∫_T^{2T} log|ζ(½+it)| dt = o(T)`, so off-line zeros have total displacement
  `Σ(β−½)₊ = o(T)` at every scale.
- **Attack.** Littlewood's lemma gives `2π Σ_{T<γ≤2T}(β−½)₊ = ∫_T^{2T} log|ζ(½+it)|dt + O(log T)`.
  A Selberg/Levinson mollifier gives `≤ (T/2) log(mollified mean square)`, which is `(T/2) log(1+1/θ)` for
  length `θ`. `o(T)` needs mollified mean square `→ 1`, i.e. `θ → ∞`, which is the MC terminus. Even
  `o(T)` is a density statement: finitely many off-line zeros cost `O(1)`.
- **Verdict.** `REDISCOVERED` (the mollified-second-moment terminus) and `INSIGNIFICANT` for exactness.

### C6 — Deligne's tensor-power amplification over short-interval families
- **Conjecture.** The Weil I/II amplification transfers: `2k`-th moments of
  `E_H(x) = ψ(x+H)−ψ(x)−H` over `x ∈ [X,2X]`, with Gaussian (Hardy–Littlewood) size
  `μ_{2k}(H log X)^k`, bound an off-line zero better as `k → ∞`.
- **Attack.** An off-line zero adds `≈ H x^{ρ−1}` to `E_H(x)` at every `x`, coherently, of size
  `X^{θ+β−1}` for `H = X^θ`. The moment bound fails iff `2k(θ+β−1) > kθ`, iff `β > 1 − θ/2`, the same
  threshold for every `k`. Hardy–Littlewood with square-root error supplies the second moment only for
  `θ < ½`, because the errors accumulate as `H² X^{½+ε}`, so the result is `β ≤ ¾`.
- **Verdict.** `FALSE` as an amplifier (the argument is `k`-blind). Deligne amplifies because a bad
  eigenvalue is *fibrewise* (a local Frobenius eigenvalue at one point of the base), bounded against a
  global `H²_c` of fixed weight offset. ζ's zeros are global (`H¹` of the base itself), so they enter
  every fibre coherently.
- **Survivor.** An exact requirement: amplification needs ζ's zeros realised as local eigenvalues over a
  base different from `Spec ℤ`, i.e. the missing product `Spec ℤ × Spec ℤ` (MUST-390).

### C7 — family version: Dirichlet characters mod `q` as the base
- **Conjecture.** Take the base to be the characters mod `q`, the fibres `L(s,χ)`, and the "trace" the
  explicit-formula sum `S_χ(x) = Σ_ρ x^{ρ_χ−½} ĝ(ρ_χ)`. Orthogonality computes
  `Σ_χ|S_χ(x)|^{2k} ≈ φ(q) k! (log x)^k`, and a single bad fibre is dominated as in Deligne.
- **Attack.** Orthogonality gives the moment only for `x^k < q` (the diagonal range, Deligne's `H²_c`
  term). There a bad zero gives `x^{2k(β−½)} = q^{2(β−½)}`, which is `≤ φ(q)` for every `β ≤ 1`: no
  information. Beyond `x^k ≥ q` the off-diagonal terms *are* the zeros (the `H¹` term), and bounding them
  is GRH-strength (large sieve past `N ≈ q`).
- **Verdict.** `FALSE` (blind range). The family moments available unconditionally are exactly Deligne's
  `H²` side. The `H¹` side, where Deligne has cohomological purity, is the open core.
- **Survivor.** Same as C6: the amplification's missing input is purity of an `H¹` computed by something
  other than the zeros.

### C8 — Deligne–Langlands–Serre via a Rankin–Selberg series of the explicit-formula error
- **Conjecture (corpus-grounded: Weil/Krein landing, MUST-390).** With `E(x) = Σ_ρ x^{ρ−½} ĝ(ρ)`, the
  positive Dirichlet series `R(s) = Σ_p |E(p)|² p^{−s}` (Rankin's trick on the "local system" whose
  Frobenius at `p` is `p^{ρ−½}`) has an a priori continuation to `Re s > 1`. Its `k`-th symmetric
  powers would then give purity, as in Serre's Ramanujan argument.
- **Attack.** `Σ_p p^{ρ+ρ̄'−1−s}` is the prime zeta function at `s+1−ρ−ρ̄'`, whose logarithmic
  singularity sits at `s = ρ+ρ̄'`, real part `1+b+b'`. The diagonal `ρ=ρ'` gives a real singularity at
  `1+2b`, so by Landau the abscissa of `R` is exactly `1 + 2 max(β−½)`. The required continuation is
  RH verbatim. In the automorphic analogue the continuation comes from an integral representation
  (unfolding). No automorphic object carries ζ's zeros as Satake parameters: the residues of `E(z,s)`
  at `s = ρ/2` have Satake modulus `p^{β/2−½} ≠ 1` for every `β`.
- **Verdict.** `CIRCULAR`. The Deligne/Langlands mechanism needs an integral representation of `R`
  independent of the zeros, which is the second base of C6/C7 again.

### C9 — route 3's slice-local argument principle
- **Conjecture (route-3 card open core).** A slice-local count on `Im s = t` excludes collisions
  without estimates.
- **Attack.** `G_t(u) = ξ(½+√u+it) ξ(½−√u+it)` is entire in `u` and equals `|ξ(½+x+it)|²` at `u = x²`.
  A critical zero gives a root `u = −(γ−t)² ≤ 0`. An off-line zero `½+b+iγ` gives
  `u = (b + i(γ−t))²`, which is real positive exactly when `γ = t`, i.e. at a collision (`u = b²`).
  The coefficients are `c_k(t) = (−1)^k Σ_j (−1)^j Ξ^{(j)}Ξ^{(2k−j)}/(j!(2k−j)!)`, so
  `c₀ = Ξ(t)²` and `c₁ = Ξ'² − ΞΞ''`: they are the higher Laguerre expressions. Nonnegative coefficients
  at `t` exclude a collision at `t` (with `c₀ > 0`). Conversely a collision forces a sign change: a small
  `b` makes `L₁(t) < 0`, and a triple cluster (`Ξ(t) = 0`) is caught by `L₂`, matching C2's PF₂ finding.
- **Verdict.** `REDISCOVERED` (Csordas–Varga's Laguerre hierarchy, the corpus's `LocalHermitePositivity`).
  Route 3's slice-local open core is exactly the Laguerre hierarchy of LA evaluated at the slice height.
  The other suggested direction (transversality) is void by EOC-F6.
- **Survivor.** An exact dictionary: collision at ordinate `t` ⟺ positive real root of `G_t` ⟺ a sign
  change in `(L_k(t))_k`. Routes 3 and LA share one open core.
- **Lean [L].** The sufficiency half is formalised, axiom-clean: `RHTower/XiHorizontalSliceTaylorPositivity.lean`
  (`re_eq_half_of_xiSliceCoeff_nonneg`, `slice_collision_free_of_xiSliceCoeff_nonneg`,
  `riemannHypothesis_of_xiSliceCoeff_nonneg`).
- **Converse [L] (same day).** `XiHorizontalSliceTaylorPositivityConverse.lean` proves
  `riemannHypothesis_iff_xiSliceCoeff_nonneg`, so the slice criterion is an exact equivalence.

### C10 — which Laguerre order sees a planted off-line zero (theta-power lab, CANNOT-468)
- **Conjecture.** The off-line zeros that Bohr–Jessen plants in `Λ_a` (transcendental `a`) violate the
  first Laguerre inequality, which would kill LA's theta-specific producer (modularity, cusp regularity,
  positivity).
- **Attack.** At the ordinate `γ` of a pair with displacement `b`, `G_γ(u) = (u−b²)² P(u)`, where `P`
  carries the roots `−d_j²` from critical neighbours at ordinate distance `d_j`. With spacing
  `2π/log T`, `P(u) ≈ [sinh(π√(cu))/(π√(cu))]²` with `c ≍ (log T)²`, so `p_k/p_{k−1} ≈ c/(4k²)`. The
  coefficient `c_k = p_{k−2}[(1−b²r_{k−1})² − b⁴ r_{k−1}(r_{k−1}−r_k)]` first turns negative where
  `r_k ≈ 1/b²`, i.e. at `k* ≍ b log T`. A saddle-point check gives the same index: `G_t(x²)` grows like
  `T^{x}`, so saddle radius `x_k ≈ 2k/log T`, and it equals `b` at `k ≈ b log T / 2`.
- **Verdict.** `FALSE`. Universality plants zeros at fixed displacement `b` and large height `T`, so the
  first failing Laguerre order is `≍ b log T ≫ 1`. `L₁` stays positive (neighbour mass `≍ (log T)²`
  versus the pair's `2/b²`), and the lab does not kill LA's first-order target.
- **Survivor (detection-index law, heuristic for typical neighbour spacing).** An off-line pair is first
  seen by the Laguerre expression of order `≍` (displacement)/(mean spacing). RH up to height `T` is
  Laguerre positivity to order `≍ ½ log T` on `[0,T]`. The first inequality alone certifies only
  near-line pairs, `b ≲ 1/log T`, consistent with `XiLaguerreSeparation`.
- **Unconditional bonus (standard).** If every zero satisfies `|γ − t| > |β − ½|`, all roots of `G_t` lie in
  `Re u < 0`. `G_t` has genus 0 in `u`, so every coefficient `c_k(t)` is positive: all Laguerre expressions
  are positive at such `t`. With `|γ| ≥ 4` (corpus) this covers `|t| < 7/2`. It is the corpus's Hadamard
  disk picture (`XiHadamardPairSignLaw`), so `REDISCOVERED`.

### C11 — the first slice coefficient through the harmonic identity
- **Conjecture.** `ΔG = 4|F'|²` for `G(x,t) = |ξ(½+x+it)|²` gives the sign of the `x²` coefficient
  `c₂(t) = Ξ'² − ΞΞ''` from vertical data, uniformly in height.
- **Attack.** At `x = 0`: `ΔG = 4Ξ'(t)²` and `∂_t²G = 2(Ξ'² + ΞΞ'')`, so `∂_x²G = 2(Ξ'² − ΞΞ'')`, the same
  quantity. `G` is even in `x`, so `c₂ ≥ 0` means `x = 0` is a local minimum of the slice. That is the
  small-`x` limit of `∂_x log G = 2 Re(ξ'/ξ)(½+x+it) ≥ 0`, the Hadamard sign. The Hadamard sign is proved
  exactly where the unit window around `t` has only critical copies.
- **Verdict.** `CIRCULAR` (collapses to the Hadamard receiver `XiHadamardSharpRegion`). The coefficient
  positivity of `G_t` is also local: all `c_n(t) > 0` as soon as every zero with `|γ−t| ≤ ½` is critical,
  because the roots `(β−½+i(γ−t))²` then lie in `Re u < 0` and `G_t` has genus 0. So the slice test at `t`
  certifies exactly what it assumes about the zeros within `½` of `t`.

### C12 — additive-structure input (Vinogradov–Korobov) for the first slice coefficient
- **Conjecture.** Exponential-sum control beyond the Beurling-optimal region (VK) bounds `c₂(t)` from
  below uniformly in height.
- **Attack.** `c₂/Ξ² = Σ_ρ Re (t − z_ρ)^{−2}` is negative only through zeros with `|γ−t| < |β−½|`, and at
  the ordinate of a lone pair it is `−2/b² + Σ_others`, where `Σ_others ≍ (log t)²`. A violation therefore
  needs `b ≲ 1/log t`: a near-*critical*-line zero. VK excludes zeros with
  `β > 1 − c(log γ)^{−2/3}(log log γ)^{−1/3}`, i.e. near the 1-line, where `b ≈ ½` and the pair is
  harmless to `c₂`.
- **Verdict.** `INSIGNIFICANT`: every known zero-free input acts at the wrong end of the strip. The
  first slice coefficient's open core is exactly the mirror region `0 < |β − ½| ≲ 1/log γ`, for which no
  method exists (`XiLaguerreSeparation` records the same requirement).
- **Katkova extension (standard, records the PF picture per height).** By Schoenberg's Theorem B, the
  coefficient sequence of `G_t` is `PF_m` whenever every zero has `|γ−t| ≥ cot(π/(2(m+1)))·|β−½|`.
  `m = 1` is the cone condition of C11. Dense ordinates make this vacuous above height `4`.

### C13 — Kurokawa tensor square with a positive Euler product
- **Conjecture.** An `H¹⊗H¹` zeta with divisor `{ρ+ρ'}` and a positive Euler product gives RH by Landau
  alone, since `ρ+ρ̄ = 2β` is real.
- **Attack.** Landau fixes only the location of the real singularity, not its value. RH needs the
  abscissa `≤ 1` a priori. The primitive part's logarithm is `Σ_x |E(x)|² x^{−s}`, with abscissa
  `1+2max(β−½)` (C8). The corpus retired the multiple-sine / absolute-tensor route
  (`5-failed/euler-triptic-continuation-anomaly-rh.md`).
- **Verdict.** `CIRCULAR` (same object as C8).

### C14 — rank–trace inertia against the Laguerre test (complementary blindness)
- **Conjecture.** The Alpöge–Furman / Zeta-23 inertia bound (vendored at `.lake/packages/Zeta23`), localised
  at critical density, bounds the number of mirror-region pairs, the only pairs that break the first
  slice coefficient.
- **Attack.** A near-line pair (`δ log T ≪ 1`) has Gram block `2(aaᵀ−bbᵀ)` equal to a rank-one PSD
  block up to `O((δL)²)`. The signature still counts it as `(1,1)`, but two trace moments cannot
  separate it from a double critical zero (`inertia-robust-mollified-simple-zeros.md`). Far pairs are
  visible to the moments and invisible to `L₁` (C10). The two tools see complementary sets, and neither
  bound is sharp enough on the other's set.
- **Verdict.** `FALSE` as a combination. The exact meta-wall behind it: the explicit formula is exact,
  but a length-`T` prime side can only be *estimated*, to `o(N)` at best (even Hardy–Littlewood gives
  "100% on the line"). `K(T) < 2` needs error `< 2` in a quantity of size `N`. Every exact route-3
  producer must therefore supply an exact sign or an exact evaluation of a prime sum of length `≍ T`,
  i.e. an arithmetic identity.

### C15 — sign-structured test functions (Odlyzko/Delsarte form of that identity)
- **Conjecture.** Take `g = h*h̃`, `ĝ ≥ 0` on the strip, `g ≤ 0` on `|x| ≥ log 2`. The prime side then has a
  sign and can be dropped, so `Σ_ρ ĝ(ρ) ≤ A(g)` with `A` archimedean. If off-line pairs gave
  `ĝ ≳ e^{bS}` while `A(g) = poly(S)`, RH would follow as `S → ∞`.
- **Attack.** The pair term is `2·𝓕[g cosh(b·)](γ)`. On `|x| ≥ log 2`, `g cosh(b·) ≤ 0`, so growth
  `e^{bS}` must come from the region the sign constraint forces negative. At an unknown ordinate `γ` its
  cosine transform has no sign. This is the Odlyzko–Poitou–Serre mechanism, which yields only
  1-line-type regions.
- **Verdict.** `REDISCOVERED` (corpus "uniform certificate program: positivity points the wrong way";
  CANNOT-341, no-go-472).

### C16 — Chebyshev's exact identities as the arithmetic input C14 asks for
- **Conjecture.** The factorial-ratio identities give exact prime-side information of length `x`, e.g.
  `Σ_{n≤x} Λ(n)[⌊x/n⌋ odd] = log(⌊x⌋!/⌊x/2⌋!²)`. They sign the dyadic defect of the alternating
  Nyman–Beurling witnesses (PM).
- **Attack.** `{y} − 2{y/2} = −[⌊y⌋ odd]`, so `φ_a(t) = −[⌊1/(at)⌋ odd]` and the identity reads
  `Σ_n Λ(n) φ_n(t) = −log(⌊1/t⌋!/⌊1/(2t)⌋!²)`: one element of the NB span. Its Mellin transform is
  `(1−2^{1−s}) ζ'(s)/s`. Witnesses are orthogonal to it automatically, so it adds no constraint.
  Orthogonality to all `φ_a` is equivalent to `Σ_n (−1)^{n+1} F(na) = 0` for `a ≥ 1`, with
  `F(y) = ∫_0^{1/y} w`. Its solutions are indexed by the zeros of `(1−2^{1−s})ζ(s)`, as before.
- **Verdict.** `REDISCOVERED` (EOC-F11, CANNOT-LIN1). Exact identities live inside the NB span; the RH
  content is the closure, not any single identity.

### C17 — pair (Montgomery-form) realisations of the collision charge: KR-R3's live residual
- **Conjecture.** The unconditional Montgomery form
  `F(x,T) = Σ_{ρ,ρ'} x^{ρ+ρ̄'−1} w(ρ+ρ̄'−1)` (BGSTB) isolates `K(T)`. A collision pair contributes the
  `x`-independent term `w(0)`, since `ρ + (1−ρ) − 1 = 0`.
- **Attack.**
  - For `α ≤ 1`, the exact on-line part of `F` fluctuates around its smooth asymptotic by amounts that
    grow with `T`, the same order as `S(T)`-type fluctuations, `≫ 2`. So `+2` per collision is buried
    even with exact prime sums.
  - As `x → ∞` at fixed `T`, the on-line cross terms `x^{i(γ−γ')}` average out, but off-line diagonals
    `x^{2(β−½)}` grow. The Cesàro limit is `Σ_γ H_γ²` if RH holds and `∞` otherwise: the growth
    dichotomy again (EOC-F5).
- **Verdict.** Reduction, not a kill (kill standard). Pair realisations are density-only at bandwidth
  `≤ 1` and a growth criterion at bandwidth `→ ∞`; the residual joins the holomorphic single-sum case.

### C18 — a Stepanov auxiliary on the slice (corpus: `StepanovHyperelliptic`, `StepanovCount`)
- **Conjecture.** An exact ℚ-identity plays the role of `x^q = x` on the slice: an auxiliary entire
  function built from `G_t` and arithmetic data vanishes to high order at every positive root
  `u = (β−½)²` and has too little growth to do so.
- **Attack.** Stepanov uses two exact relations valid at *every* rational point: `x^q = x`, and
  `d/dx(x^{qj}) = 0` (inseparability). The auxiliary `Σ(r_j + s_j g)x^{qj}` then vanishes to order `M`
  at all points with `g = 1`, and degree counting bounds the count by `q + O(√q)`. At a zero of `ξ`
  the only exact relations are `ξ(ρ) = 0` and its FE/conjugation images, which hold at every zero, so
  they cannot separate off-line from on-line roots. The ℚ-substitute for `x^q − x` in Chebyshev form
  (`lcm(1..N)`) has size `e^{ψ(N)}`, and `√X` precision there is one-sided Nyman–Beurling (EOC-F11,
  CANNOT-LIN1). `G_t` has the extra symmetry `u` real ⇒ `G_t(u) ≥ 0` for `u ≥ 0`, but that is
  positivity, not a vanishing relation.
- **Verdict.** `FALSE` (no Frobenius-type relation at the roots). The exact missing input is an
  identity valid at all points of a "base" that degenerates at on-line roots and not at off-line ones.
  This is the C6/C7 second base again, now in Stepanov form.

### C19 — positivity-preserving source approximants of the slice product (producer shape of EOC-F24)
- **Conjecture.** A natural source scheme gives entire `F_N → g_t` (locally uniformly) with nonnegative
  Taylor coefficients at `0`, which by the Lean equivalence would prove RH.
- **Attack (three natural schemes).**
  - *Theta truncation* `Φ_N = Σ_{n≤N} φ_n`: `φ_n(u) ≈ −3πn²e^{5u/2}` as `u → −∞`, so the transform
    converges only for `Re z > −5/2`. Symmetrising leaves exponential tails, the transform is not entire,
    and the cone is not even defined. Only the full theta sum (Poisson / FE) is entire.
  - *Dirichlet-polynomial / Riemann–Siegel truncations*: the coefficients have no sign, and smoothed
    versions converge but carry `n^{−it}` phases with no positivity.
  - *de Bruijn–Newman heat flow* `H_λ`, `λ ↓ 0`: the cone holds for `λ ≥ Λ`, so reaching `λ = 0` is
    `Λ ≤ 0`, i.e. RH.
- **Verdict.** `FALSE` for the natural schemes. Entireness forces the full FE (all `n`); the cone
  forces real-rootedness-type structure; the only known cone-preserving families (Pólya's fake ξ, `H_λ`
  for `λ ≥ Λ`) are not built from primes or are circular.

### C20 — local Euler-factor surgery against the slice cone
- **Conjecture.** Removing or adding finitely many local Euler factors (FE-symmetrised) keeps the slice
  cone, and so gives Euler-built cone-preserving approximants.
- **Attack.**
  - Removal: `ξ·(1−p^{−s})(1−p^{s−1})` has new zeros at `Re s = 0, 1`, `Im s = 2πk/log p`, displacement
    `½`, i.e. cone apices at `t = 2πk/log p`. Positivity then fails at those heights by the Lean
    contrapositive (applied to the modified function).
  - Addition: division introduces poles, so the function is not entire.
  - FE-symmetric factors with only critical zeros (`p^{s−½} + p^{½−s} − 2cos α`) preserve the cone,
    but they carry no arithmetic of `ξ`.
- **Verdict.** `FALSE` (the single-prime deformation of the deformation law, in slice form).
- **Formal by-product [L].** Per-zero cone criterion and an unconditional all-order Laguerre band
  `|t| ≤ 233/20` (`XiHorizontalSliceConeCriterion.lean`, EOC-F25).

### C21 — pushing the unconditional band with the fourth reciprocal-trace budget
- **Conjecture.** The corpus's critical band (`XiFourthTraceExtendedCriticalLineBand`: an off-line atom
  `> 9/200000` against the source moment `< 9/50000`), fed through the cone criterion, extends the
  all-order band past `233/20`.
- **Attack.** The atom of an off-line copy decays with height like a fourth reciprocal power. Each
  band is therefore a fixed-height exclusion whose reach is set by the numeric size of the source
  moment. The cone criterion needs `|Im ρ − t| ≥ |Re ρ − ½|` for zeros near `t`, which is the same
  information near `t`. Crossing the first ordinate `≈ 14.13` needs finer source constants at each step
  (a finite verification).
- **Verdict.** `INSIGNIFICANT` (wall 1, height-local).

### C22 — density form of the slice criterion (paper)
- **Statement.** For large `T`, all Taylor coefficients of the slice product at `t` (all Laguerre
  expressions of every order) are nonnegative for every `t ∈ [T, 2T]` outside a set of measure
  `≤ (1/2π) · log(mollified mean square) · T + o(T)`.
- **Proof sketch.** By EOC-F25 the failure set at height `t` needs a zero inside the cone at `t`. The
  failure set is therefore contained in `⋃ (γ − |β−½|, γ + |β−½|)` over off-line pairs. Its measure is
  `≤ Σ_{β>½} 2(β−½)`. Littlewood's lemma with a mollifier `M` (`M(1)=1`) gives
  `2π Σ_{T<γ≤2T, β>½}(β−½) ≤ (T/2) log((1/T)∫|ζM|²) + o(T)`. With Selberg/Conrey mean squares
  `≈ 3` (resp. `≈ 2.75`), the failure measure is `≤ 0.175T` (resp. `≤ 0.161T`): the full hierarchy holds on
  at least `82%` of heights.
- **Verdict.** `SURVIVES` as a paper corollary (density, wall 3; no RH content). The Lean version needs
  the mollified second moment, the corpus's MC terminus, so it cannot close unconditionally yet.
  Recorded as the density shadow of route 3.
- **Lean [L] (same day).** `XiHorizontalSliceDensityFromMeanSquare.lean`:
  `exists_volume_sliceFailure_le_of_line_meanSquare`, with the mean square as an explicit hypothesis.

### C23 — a Rodgers–Tao-type contradiction in the forward direction (`Λ ≤ 0`)
- **Conjecture.** As Rodgers–Tao derive `Λ ≥ 0` from unconditional zero statistics under the backward
  heat flow, an off-line zero (`Λ > 0`) contradicts an unconditional statistic under the forward flow.
- **Attack.** For `t > 0` the de Bruijn–Newman approximant evaluates the Dirichlet series at
  `σ_eff ≈ ½ + (t/4) log(x/4π)`. The first term dominates, and all zeros are real, only above
  `x ≳ e^{2/t}`. Below that height `H_t` inherits `ξ`'s zeros up to small motion, so `Λ ≤ t` is
  RH for `ξ` up to height `≈ e^{2/t}` (Polymath 15 closes `t = 0.2` with numerics). An off-line pair of
  displacement `b` is absorbed by forward time `≤ b²/2`. No unconditional statistic is violated by a
  sparse set of such pairs: forward relaxation erases them, and density statistics cannot see them.
- **Verdict.** `REDISCOVERED` (Polymath 15 / Ki–Kim–Lee structure: wall 1 plus 1-line dominance). The
  asymmetry is exact. Backward flow creates collisions from generic statistics, which is how
  Rodgers–Tao win. Forward flow destroys them, so a contradiction would need a statistic sensitive to
  one pair, i.e. RH.

### C24 — moment form of the slice criterion
- **Conjecture.** The slice coefficients are moments,
  `c_{2k}(t) = (1/(2k)!) ∫ d^{2k} K_t(d) dd` with
  `K_t(d) = ½∫ Φ₀((s+d)/2) Φ₀((s−d)/2) cos(ts) ds`, and a sign structure of `K_t` (positive tails
  dominating a negative core) gives all moments `≥ 0`.
- **Attack.** `K_t` is, up to a constant, the cosine transform in `σ` of `Ξ(t+σ)Ξ(t−σ)`. Pointwise
  positivity of `K_t` is a Wigner-positivity statement, ruled out by Hudson's theorem (`Φ₀` is not a
  Gaussian). For large `|d|` the product `Φ₀((s+d)/2)Φ₀((s−d)/2) ≈ exp(−2πe^{s} cosh d)` concentrates at
  `s ≈ −|d|` with `O(1)` width, so `K_t(d) ≈ A(d) cos(t|d| + φ)`: the tails oscillate at frequency `t`
  and do not dominate with a sign. High moments are decided by that phase.
- **Verdict.** `BRIDGE` (a dual form of the Lean equivalence). The oscillation frequency `t` of the tails
  is the ordinate; the moment signs carry the full content.

### C25 — transplanting the proven RH-analogue mechanisms onto one slice
- **Conjecture.** One of the mechanisms that *prove* an RH-analogue in a corpus toy model works on the
  slice at a single height.
- **Attack (each mechanism at its failure point).**
  - *Hermite–Biehler with an FE-breaking gain* (Lagarias–Suzuki constant terms
    `y^u ξ(1+2u) + y^{−u} ξ(1−2u)`, RH for every `y > 0`). The HB inequality
    `|ξ(w+1)/ξ(w)| > y^{−Re w}` holds because the numerator sits in the zero-free half-plane
    (`Re(w+1) ≥ 1`) and the Gamma gain `|t|^{1/2}` beats the convexity bound for `|ζ(w)|`. On the slice of
    `ξ` itself the two HB sides are equal by the FE (`|ξ(½−x+it)| = |ξ(½+x+it)|`). A shift `h` makes
    the numerator `ζ(½+h+x+it)` vanish at an off-line zero unless `h ≥ ½`.
  - *Stepanov/Frobenius* (C18): no Frobenius relation holds at the roots.
  - *Dominance* (Rankin–Swinnerton-Dyer arcs, period polynomials, de Bruijn–Newman `t > 0` at large
    height): on the slice no term dominates (Gram's law fails; `Σ n^{−1/2} ≍ 2√N`).
  - *Sturm–Liouville / ODE* (Pólya's fake ξ via Bessel `K`): `Ξ` is hypertranscendental (corpus HT
    lanes), so there is no ODE.
  - *Finite-aperture Weil positivity* (Connes–Consani `√2`, corpus prime-2 extension): height-local.
- **Verdict.** `REDISCOVERED`. This is the corpus's terminal classification ULF-TERM-001
  (four theorem-closed producer kinds, two doors). The slice form adds one precise remark: HB is
  degenerate *exactly* on the slice, because the FE equates the two sides there.

### C26 — high-order slice positivity at every height (door-2 integer made finite)
- **Conjecture (new, paper).** There are absolute constants `C, t₀` such that for `|t| ≥ t₀` and every
  `k ≥ C log|t|` the slice coefficient `c_k(t)` (the coefficient of `x^{2k}` in `ξ(½+x+it)ξ(½−x+it)`) is
  strictly positive, unconditionally. `C = ¾` plus an absolute margin should do.
- **Why (saddle point, paper sketch).** Write `c_k = (R^{−2k}/2π)∫_{−π}^{π} g_t(Re^{iθ}) e^{−2ikθ} dθ`.
  - By the FE, `|g_t(Re^{iθ})| = |ξ(½+|a|+i(t+c))|·|ξ(½+|a|+i(t−c))|` with `a = R cos θ`,
    `c = R sin θ`.
  - Stirling makes the exponential parts `e^{−π|τ|/4}` sum to `e^{−πt/2}`, independent of `θ`, and
    leaves `t^{|a|}`. So `|g_t(Re^{iθ})|/g_t(R) ≈ t^{−R(1−|cos θ|)} · (ζ-ratio)`: Gaussian angular decay
    of width `(R log t)^{−1/2}` at the two saddles `θ = 0, π`, which add because `g_t` is even.
  - Choose `R = R_k` by `R·d/dR log g_t(R) = 2k`, so `R_k ≈ 2k/log t`. For `k ≥ ¾ log t`, `R_k ≥ 3/2` and
    the saddle sits at `Re s ≥ 2`, where `ζ` is bounded above and below.
  - Near `θ = ±π/2` the points enter the strip. There `|ζ| ≤ C t^{1/4} log t` (convexity), but the
    suppression is `t^{−R(1−|cos θ|)} ≤ t^{−R/2} ≤ t^{−3/4}`, which beats `t^{1/2} log² t` against the
    main-term width `(R log t)^{−1/2}`.
  - The main term is positive: `g_t(R) > 0`, the linear phase cancels by the choice of `R`, and the
    quadratic phase has real part `≈ −R log t < 0`.
- **Consequences.**
  1. **RH ⟺ for every `t`, the first `O(log(|t|+2))` slice coefficients at `t` are `≥ 0`.** Combined
     with the Lean equivalence, the RH content at height `t` sits in finitely many (`≍ log t`) explicit
     differential expressions of `Ξ` at `t`. This matches the detection-index law (C10): pairs of
     displacement `b ≤ ½` are detected at order `≍ b log t ≤ ½ log t`.
  2. **Door-2 integer.** `V(t) :=` the number of sign changes of `(c_k(t))_{k ≤ C log t}` is a finite,
     locally computable, *even* integer (Descartes–Laguerre: `V ≡ #positive roots = 2·#collision pairs
     (mod 2)`), with `V(t) ≥ 2P(t)` and RH ⟺ `V ≡ 0`. It has the same full-quantum margin as route 3's
     `K(T) < 2`, but it is defined pointwise from derivatives of `Ξ` at `t`, with no zero enumeration and
     no averaging (walls 2–3 do not apply to the definition).
- **Verdict.** `SURVIVES` (paper sketch). Open core: a source-side bound `V(t) < 2`, i.e. sign control of
  `≍ log t` Laguerre expressions at `t`. That is still RH-strength, but finite at each height.
  Next: a complete paper proof with explicit constants, a novelty check (GORZ covers the `t = 0`
  Jensen axis, not the height-local order axis), then Lean.

## Diagnosis after C1–C5: the four walls the loop keeps hitting
1. **Height-local blindness.** Every fixed-order or fixed-aperture condition (PF_m, Jensen degree `d`,
   Weil support `S`) sees only zeros below a height tied to the order.
2. **Holomorphic dichotomy.** A holomorphic source realisation of a quantized invariant is `0` or `∞`
   (EOC-F5, F13), a growth criterion.
3. **Averages give density.** Mean-square, mollifier and large-deviation inputs give `O(T)` or `o(T)`
   off-line mass, never zero. A single zero costs `O(1)` in every average.
4. **Deformation.** Inputs lacking FE, the Euler product or additive structure admit off-line
   countermodels (DH, Beurling, single-prime deformation). Inputs with all three are Hamburger-rigid, and
   there is no intermediate class.

A new route must break one wall by a mechanism, not by a sharper estimate. Wall 4 says the mechanism must
*construct* a family (case (c)); walls 1–3 say it must be exact, pointwise and height-uniform.

## Log
- 2026-09-26 — loop opened; C1 `INSIGNIFICANT`, C2 `BRIDGE`, C3–C5 `REDISCOVERED`; four-wall diagnosis; C6–C7 `FALSE` (Deligne amplification is k-blind / range-blind over ℚ); C8 `CIRCULAR`; C9 `REDISCOVERED` (route-3 slice core = LA Laguerre hierarchy); C10 `FALSE` + detection-index law k* ≍ b log T; C9 Lean (XiHorizontalSliceTaylorPositivity); C11 `CIRCULAR`; C12 `INSIGNIFICANT` (zero-free inputs act near the 1-line; the slice core is the mirror region); C13 `CIRCULAR`; C14 `FALSE` (exactness vs estimation meta-wall); C15 `REDISCOVERED`; C16 `REDISCOVERED`; C17 reduction (KR-R3 pair residual = density/growth); C18 `FALSE` (no Frobenius relation at roots); slice equivalence closed in Lean (EOC-F24); C19 `FALSE` (natural cone-preserving approximants); C20 `FALSE` + Lean cone criterion (EOC-F25); C21 `INSIGNIFICANT`; C22 density corollary (paper, then Lean conditional, EOC-F26); C23 `REDISCOVERED`; C24 `BRIDGE` (moment form; tails oscillate at the ordinate); C25 `REDISCOVERED` (= ULF-TERM-001); C26 `SURVIVES` (high-order slice positivity; finite door-2 integer).
- 2026-09-26 — **C26 PROVED and formalized** (`3-formalized/high-order-slice-positivity.md`). `RHTower.exists_riemannHypothesis_iff_low_order_xiSliceCoeff_nonneg`: `∃ K κ, RH ⟺ ∀ t ≥ 0, ∀ k < max(K, κ log t), c_{2k}(t) ≥ 0`, axiom-clean. The door-2 integer `V(t)` (sign changes among the first `κ log t` coefficients) is now a finite, pointwise, even integer, and RH ⟺ `V ≡ 0`. The next cycle (C27) must attack the finite low-order window itself.

### C27 — sharp window: positivity for every saddle radius `R_k > ½`
- Conjecture: for every `ε > 0` there is `t₀(ε)` such that `c_{2k}(t) > 0` whenever `t ≥ t₀` and the saddle radius satisfies `R_k ≥ ½ + ε`. Equivalently `k ≳ (¼ + ε/2) log t`.
- Paper argument:
  - The Stirling gain on the arc is `(R − a) log(t/2π)`.
  - The ζ loss under the convexity bound is at most `(½ − a) log t` at abscissa `½ + a`.
  - The net exponent is `≤ −(R − ½) log t`.
  - The core disc lies in `Re s ≥ 1 + ε/2`, where `ζ'/ζ` is `O(1/ε)`.
- Why the threshold `½` is exact for this method: for `R < ½` the saddle point `½ + R + it` lies in the critical strip. The core then needs a zero-free disc around it plus a lower bound on `|ζ|` there. That is local zero-freeness on the segment `(½, 1) + it`. By the detection law, an off-line pair of displacement `b` is seen at `R ≈ b`, exactly in that range.
- Verdict: `SURVIVES` on paper but `INSIGNIFICANT` relative to the core. It only improves `κ` to about `¼`. Not formalized.
- **Relentless interrogation.** What kills it is that inside the window the saddle point sits in the strip. So the window IS local zero-freeness (four walls, wall 1). There is no stronger slice conjecture that avoids this: any positivity proof of a window coefficient needs `|ζ|` bounded below near `½ + R + it`.

### C28 — unconditional density of fully slice-positive heights
- Claim: by the cone criterion, `c_n(t) ≥ 0` for all `n` outside `⋃_ρ (γ − b_ρ, γ + b_ρ)`, a set of measure `≤ 2 Σ_{γ ≤ T} (β − ½)⁺`.
- Kill: the explicit off-line first moment in the corpus (`SingleInputOffLineMomentConstant`) is conditional on the mollified mean-square gates. This is the conditional density consumer C22 again.
- Verdict: `REDISCOVERED` (= C22 / EOC-F26). It is density only (wall 3).

### Slice-route closure (no-go discipline)
- Positive survivor: C26, proved and formalized as `exists_riemannHypothesis_iff_low_order_xiSliceCoeff_nonneg`.
- Exact boundary: the RH-bearing window is the set of orders whose saddle point lies in the critical strip (C27). There, window positivity is equivalent to local zero-freeness of `(½, 1) + it`.
- The slice form of route 3 therefore has no independent content beyond C26. Route 3 as a whole:
  - two-prime excess: `KR-R3` (holomorphic 0/∞, second moment density-only);
  - slice form: closed here.
- Status: route 3's residual is RH-strength in every form found so far. The loop continues on a new route.
- 2026-09-26 — pivot (user direction): first Laguerre inequality at every height, card `first-laguerre-all-heights.md`.
  - Open in the literature.
  - Failure set = isolated near-line FE pairs (near-double zeros).
  - Not implied by the analytic inputs (Hadamard surgery).
  - Mechanisms M1–M6: circular, insignificant or false.
