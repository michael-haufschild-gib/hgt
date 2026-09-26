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
- 2026-09-26 — loop opened; C1 `INSIGNIFICANT`, C2 `BRIDGE`, C3–C5 `REDISCOVERED`; four-wall diagnosis; C6–C7 `FALSE` (Deligne amplification is k-blind / range-blind over ℚ); C8 `CIRCULAR`; C9 `REDISCOVERED` (route-3 slice core = LA Laguerre hierarchy); C10 `FALSE` + detection-index law k* ≍ b log T; C9 Lean (XiHorizontalSliceTaylorPositivity); C11 `CIRCULAR`; C12 `INSIGNIFICANT` (zero-free inputs act near the 1-line; the slice core is the mirror region); C13 `CIRCULAR`; C14 `FALSE` (exactness vs estimation meta-wall); C15 `REDISCOVERED`; C16 `REDISCOVERED`; C17 reduction (KR-R3 pair residual = density/growth); C18 `FALSE` (no Frobenius relation at roots); slice equivalence closed in Lean (EOC-F24); C19 `FALSE` (natural cone-preserving approximants).
