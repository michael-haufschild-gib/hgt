# 08 — The Conjectures Required (Open-Conjecture Inventory)

> **Scope.** The open conjectures the programme depends on: the carrier-synthesis set (C1–C6), the RH
> bridge (B1–B3, with the confinement Lemma the open core), **the one wall in its named forms** (§3),
> the named / coordinate conjectures (§4), and the acceptance gatekeepers (§5). Every item is
> `[CONJECTURE]` / `[OPEN CORE]`; kill criteria are quoted. No proof of RH is claimed.

---

## §1 — Carrier-synthesis conjectures C1–C6

Each bundles `[OBSERVED]` catalog items into one statement, with the experiment that adjudicates it
and the observation that falsifies it.

- **C1 — the carrier is a *non-scalar holonomy* class, not a scalar 2-form. `[CONJECTURE]`** The signed
  object whose strip integral is positive for true continuation and negative for every finite-Euler /
  random-phase surrogate is the holonomy, not `ω = dO∧dφ` (the scalar 2-form is **falsified** across all
  tested variants; a minimal counterexample gives opposite-sign values). *Native-HT framing dropped*
  (see §1 note below).
- **C2 — the carrier is the holonomy of the affine weld connection, trivialized on `σ=½` by the
  Γ-cocycle. `[CONJECTURE — load-bearing]`** *Target: name the cohomology group.* *Kill:* if it is
  `∮ d arg = 2πi(#zeros−#poles)` (winding number) it reduces; the conjecture requires the
  **non-integer / continuous** part orthogonal to the winding number.
- **C3 — long-run coherence = the H¹/Sobolev regularity gap of one meromorphic phase. `[CONJECTURE]`**
  One seminorm `‖∂_t arg(Γ∞+P)‖` predicts all of Group B. *Kill:* reproduced by a smooth
  amplitude-matched non-HT analytic surrogate ⟹ "analytic ≠ truncated," known.
- **C4 — the weld is 2-D rigid: a divergent cross-lane correlation length `ξ_σ`. `[CONJECTURE]`** Large
  in the strip, `O(1)` at `σ>1`, because `∂_s` couples neighbouring σ-lanes. *Kill:* if `ξ_σ` is set by
  zero-spacing alone, it reduces to zero-statistics.
- **C5 — a genuine crossover scale `σ* ∈ (½,1)`. `[CONJECTURE]`** A non-analytic kink (coherence
  alive→dead), possibly `σ*=3/4` or the `Σp^{−2σ}~loglog` region. *Kill:* a smooth analytic fade with
  no distinguished `σ*`.
- **C6 — one inverse problem: realize `Γ∞+ζ'/ζ` from primes + a boundary cocycle. `[CONJECTURE]`** The
  carrier is the obstruction class to reconstructing the weld from finite-prime data by local/scalar
  means; the Γ-factor is the unique additive cocycle that closes it. *Kill:* a bounded-order nonlocal
  kernel that portably reconstructs the carrier (would be D-algebraic, contradicting Hölder).

> **§1 note — native-HT resolved (no).** No FE-exact, ζ-exact-zeros, *non*-HT object exists: by Hadamard
> every such object is `e^{q((s−½)²)}ξ`, still HT (`ζ'/ζ` untouched; `HT ± D-alg = HT`). So the carrier
> and GPT's `𝔗_ξ` are **invariant** under the rung-1 surrogate ⟹ `{zeros, FE, source-measure}` detectors
> are **divisor geometry, not transcendence**. `𝔗_ξ` relocates to Conjecture C (the bridge). ξ's HT is
> the *arithmetic* of `{γ_n}` = APEX-A. Geometry → B/C; arithmetic → A; they meet at the divisor.

---

## §2 — The RH bridge (B1–B3)

- **B1 — source-measure bridge (the dream). `[CONJECTURE — the hard arrow]`** The completed transport
  features **force** `supp μ_ξ ⊂ {Re=½}`. Hardest step: upgrading generic-window signatures to all-scale
  off-seam exclusion.
- **B2 — the two-lemma bridge. `[CONJECTURE + OPEN CORE]`** *Lemma 1 (detect):* off-line `ρ` ⟹ an
  off-seam transport defect (local proof via `ξ'/ξ~m/(s−ρ)`; global half open). *Lemma 2 (confine):*
  all source-carrying coupled-lane transport defects are confined to `Re=½`. **Lemma 2 is THE open core.**
  - *Sharp restatement (the Shifted Reciprocal-Seam Positivity Theorem).* Lemma 2 is **not** "phase ⟹
    RH", "FID positivity ⟹ RH" (FID is RH-empty, §3), "pole-cancellation ⟹ positivity", "bulk kernel ⟹
    `κ₋=0`", nor "unshifted Hankel tower PSD". It is, precisely:
    > `completion + explicit formula + canonical boundary extension ⟹` for every real polynomial
    > `p(y)=Σc_i y^i`, both shifted square-tests `Q_0[p]=Σ_{i,j}c_ic_jT_{i+j+1} ≥ 0` **and**
    > `Q_1[p]=Σ_{i,j}c_ic_jT_{i+j+2} ≥ 0` (equivalently `[T_{i+j+1}], [T_{i+j+2}] ⪰ 0 ∀d`).
    *(Source-aware: requiring **both** towers is the abstract/source-forgotten form; for the actual zero
    divisor all-order `Q_0[p]≥0` alone already forces every `y_ρ∈ℝ_{>0}` — a real `p` isolates any
    negative-real atom or non-real conjugate pair to make `Q_0<0` — hence `Q_0` alone implies RH.)*
    Candidate subclaims: (i) total positivity / variation-diminishing of the integer→zero transform;
    (ii) a **source-built** faithful `κ₋` read off `{T_k}` (no zero-feeding), with the boundary localized
    to a Weyl-PSD theorem (§4); (iii) no off-seam signed defect survives the reciprocal seam chart. The
    object to prove is the shifted square-test form `Q_0`, not more phase features.
  - *Candidate proof shapes for `Q_0≥0` (source-built, none assuming zero locations).* (a) **A direct
    square identity** `Q_0[p] = ∫|𝒦_p(x)|² dμ_{arch/prime}(x) ≥ 0` — map `p(y) ↦` an explicit-formula test
    function `h_p` whose zero-side sum is `Q_0[p]` and whose arch/prime side is manifestly a square (the
    map must be built from the completed weld, since ordinary Weil positivity is already RH-equivalent and
    cannot be smuggled in). (b) **A positivity-preserving explicit-formula transfer** integer/prime
    reciprocal moments `→ T_k` carrying the `Q_0` tests across (using the *actual* explicit formula, not an
    abstract cone — the FID integer side is positive but RH-empty). (c) **Positive Jacobi / Stieltjes
    continued-fraction parameters** for `m_n=T_{n+1}` derived directly from `Ξ` without assuming RH
    (`β_n>0`); a breakdown localizes where positivity fails. *(Numerically `β_n>0` holds, but the sequence
    `T_k=2Σγ^{−2k}` is dominated by the single lowest-zero atom `y_1=1/γ_1²` — `T_k→2y_1^k`, next atom
    suppressed by `(y_1/y_2)^k=2.2^k` — so the recurrence is catastrophically ill-conditioned (`α_n` leave
    the support `[0,y_1]` at the precision wall, ~80 guard digits/order). **Atom deflation does not fix
    this** — subtracting dominant atoms (`T_k^{(r)}=T_k−2Σ_{n≤r}y_n^k`) or Christoffel-transforming
    (`∏(y−y_j)q`) makes the conditioning **strictly worse** (`cond 5.6e30→1.9e40`/`2.0e38` as `r:0→10`/`5`),
    since the atoms cluster ever-tighter toward the hard edge (`y_n/y_{n+1}→1`). The ill-conditioning is
    **intrinsic to the divisor geometry**, so a numerical/deflated-recurrence proof coordinate is dead; the
    handle must be analytic (the closed-form `S_k` / the rank-1-pole structure of route (d)).)* (d)
    **Contradiction-localization:** a
    `Q_0[p]<0` direction must violate a completed explicit-formula constraint — the local twin is
    `D₂(R)=Σ m_ρ(β_ρ−½)²`. The **arch/prime split** `Q_0[p] = Q_arch[p] + Q_prime[p]` (`T^A_k=(−1)^kS_k^A`,
    `S_k=−[w^{2k−1}](A+P)`) is **not** structureless cancellation: the archimedean Hankel `[T^A_{i+j+1}]`
    has signature **exactly `(d,1)` `[PROVED, all d — archimedean rank-one theorem]`** — one negative direction, and
    it *is* the pole-evaluation vector `u_i=(−4)^i` (`y=−4` is the `s=1` pole image, `⟨c,u⟩=p(−4)`), the rest
    positive-definite; the prime Hankel is indefinite; the two sum to PD `Q_0`. The archimedean half has an
    **exact closed form**, proved for every `d`:
    `Q_arch[p] = −4·p(−4)² + Σ_{j≥1}(2j+½)^{−2}·p(−(2j+½)^{−2})²` (matrix form `H_d^A = R_d^A − 4uuᵀ`,
    `R_d^A=Σ_{j≥1}(2j+½)^{−2}v_jv_jᵀ`) — a positive sum of squares over the **trivial-zero divisor** (images
    `y_j=−(2j+½)^{−2}`, tight cluster in `(−0.16,0)`) minus one rank-1 square at the pole `y=−4` (coefficient
    exactly `−4 = y·mass`). Proof: `R_d^A≻0` (a nonzero deg-`d` poly can't vanish at the infinitely many distinct
    `y_j`) ⟹ at most one negative eigenvalue; `uᵀH_d^A u = uᵀR_d^A u − 4(uᵀu)² < 1−4 < 0` ⟹ at least one; so
    `(d,1)`. Identity cross-checked to `1e-62`. *Proof-shape, corrected:* the rank-1 pole strip is
    exact but **not a reduction** — restricting `H_d^{(0)}` to `u^⊥` keeps it PD yet improves conditioning by
    only a fixed `~10^{6.5}` factor (residual still hard-edge/FID-like, `[verified d≤6]`), and the most-dangerous
    direction is `0.97·u` with `|Q_arch/Q_prime|=1.0` (**prime-delicate**, not arch-dominated). So "deflate the
    pole, then prove residual PSD" does not well-condition Part B; the genuine target is the **named inequality
    on `u^⊥`**: `∀p` with `p(−4)=0`, `Q_prime[p] + Σ_{j≥1}(2j+½)^{−2}p(−(2j+½)^{−2})² ≥ 0` — the prime form's
    negativity absorbed by the (small) trivial-zero budget. An off-line zero injects a negative direction
    **orthogonal** to `u` (overlap `≤0.06`), so Part A (pole, RH-independent) and Part B (the RH-sensitive
    defect) act on essentially orthogonal subspaces.
  - *No-go on the naive route.* Pole-cancellation / finiteness alone does **not** give positivity: a
    positive cutoff measure `μ_L = L·δ_0 + δ_1` has raw Hankel determinant `L > 0` (PSD for every `L`),
    yet renormalizing its infinite zeroth moment to `0` leaves `[[0,1],[1,1]]`, determinant `−1` (not
    PSD). So the bridge cannot proceed by "cancel the `s=1` pole, then test PSD" — it must establish
    positivity **directly in the shifted `k≥1` moment space** (square test functions), consistent with
    the `T_0=∞` exclusion in §3.
  - *Quantifier reduction (forward coordinate). `[THEOREM]`* "`D₂(R)=0` for **every** admissible window"
    is equivalent to "`D₂(R)=0` on a **countable basis of rational rectangles** whose boundaries avoid
    zeros": for a discrete divisor, any off-seam zero's atomic mass `m_ρ(β−½)²>0` is isolated by such a
    rectangle (seam atoms contribute `0`; boundary-hits repaired by shrinking). This removes the
    uncountable-window quantifier as an obstruction — it does **not** prove `D₂=0`.
- **B3 — contrapositive. `[CONJECTURE]`** `off-line zero ⟺ off-seam source-carrying defect` (nonzero
  logarithmic residue; a random artifact does not count).

---

## §3 — THE ONE WALL (apex inventory): one object, one wall, many names

**One object.** `Ξ(w):=ξ(½+w)` is even, entire, order 1; its divisor `𝒟={ρ−½}` is the whole content,
**fixed by the constraint** `ι:s↦1−s` (⟺ `Ξ` even) and the completion `Λ=Γ∞·ζ` — no generative flow.

**One wall (= RH).** In the reciprocal seam-squared coordinate `y_ρ:=−(ρ−½)^{−2}` (the unique chart
where the value-sums converge absolutely from the first order; the forward `Σ(ρ−½)^k` **diverges** — the
false "regularization" trail):
```
   RH ⟺ every y_ρ real-positive ⟺ {T_k}_{k≥1}, T_k:=Σ_ρ m_ρ y_ρ^k, is a STIELTJES moment sequence
      ⟺ the shifted Hankel towers [T_{i+j+1}]_{i,j≥0} and [T_{i+j+2}]_{i,j≥0} are PSD to ALL orders.
```
> *(The zero-th moment `T_0 = Σ_ρ 1 = ∞` is excluded: the measure `Σ_ρ δ_{y_ρ}` has infinite total mass
> but finite moments for `k≥1`. **No finite `T_0` repair is a hidden alternative**: a finite all-order
> extension would have a finite representing measure, contradicting the infinite mass, and the Schur
> thresholds `a_d = b_d^T C_d^{-1} b_d` diverge (e.g. `a_d = d(2d+3)/2` for `y_n=1/n²`). So the relevant
> towers are the **shifted** ones of the sequence `(T_1,T_2,…)` — `[T_{i+j+1}]` (Hamburger) and
> `[T_{i+j+2}]` (Stieltjes) — not the unshifted `[T_{i+j}]_{i,j≥0}`. Because
> the divisor is **infinite**, the correct target is **strict positive-definiteness**, not mere semidefiniteness:
> a singular block would force a finite-atomic representing measure (a finite recurrence / rational moment
> generating function), incompatible with ξ's infinitely many zeros — singular/flat blocks are finite-atomic
> countermodels or truncation artifacts, not part of the infinite-divisor theorem.)*

- **APEX-B — faithful positivity. `[OPEN CORE]`** Equivalent all-scale forms:
  `κ₋=0` (faithful Krein–Langer index, = #off-line pairs) ⟺ `Q_W⪰0` (explicit-formula form, signature
  `(1|∞)`) ⟺ `m_ξ∈N₀` ⟺ **`det H_d≥0 ∀d,t`** (uniform-in-`d` Laguerre–Turán/Hankel; `d=2` classical,
  the **uniformity is the open core**, numerically a sparse/sub-grid/collective resonance) ⟺ uniform
  Jensen / Laguerre–Pólya. **SOTA = Griffin–Ono–Rolen–Zagier 2019** (fixed-`d` proven). **Construction
  (Master 2) = Connes–Consani 2014–2026** (Riemann–Roch / Jacobian of `\overline{Specℤ}`, prolate
  operator) — the corpus's largest lag and the strongest handle.
- **The atlas (one wall, many names).** `M_k/D₂` (local, Conj-C), `S_k/T_k` (global reciprocal), `λ_n`
  (Li), `a_n / J_{d,n}` (Jensen), `H_d` (Hankel), `Q_W` (Weil), `κ₋` are **coordinate charts on one
  divisor**, Newton-conjugate (`M_k=p_k`; `S_k=−k[w^{2k}]logΞ`; `λ_n=Σ_jC(n,j)(−1)^{j+1}σ_j`). **Finite
  low-order passport ⟹ seam-blind** (positive-dimensional moment fibre; `K=2` quartet counterexample);
  only all-order data = RH.
- **The charts are RH-equivalent but do not transfer term-by-term (the Li↔Hankel kernel is signed and
  infinite).** The Li kernel `L_n(y)=2−2C_n((4−y)/(4+y))` (nonnegative on `y>0`) expands in the
  reciprocal-moment basis with **signed** coefficients (`c_{n,1}=n²`, `c_{n,2}=−n²(n²+2)/12`, …), so Li
  positivity `λ_n≥0` is **not** a coefficientwise-positive combination of the `T_k`: the Li→`T_k` bridge
  is infinite and signed, needing the full rational kernel or a separate positivity-preserving argument,
  not a chart-to-chart coefficient comparison.
- **Low-order charts need canonical normalization.** `P_1` is not an ordinary convergent `Σ_ρ ρ^{−1}`:
  Hadamard gives `P_1 = −b = 1 + γ_E/2 − log(2√π)`, and only `P_k` (`k≥2`) are absolutely convergent
  zero-sums — so any `λ_1`/`P_1` comparison requires the Hadamard finite-part. And the transform is
  gauge-sensitive: a zero-free multiplier `δλ_n = c n²` (which moves no zero) inverts to phantom
  `δP_1=c, δP_2=−2c, δP_{≥3}=0`; the atlas must fix canonical `ξ`, use divisor-defined Li coefficients,
  or subtract the zero-free gauge before any low-order identity is read.
- **The seam cancellation (weld = phase-defect = entireness).** Split `Ξ'/Ξ=A+P` (`A` archimedean Γ/poles,
  `P=ζ'/ζ`): `S_k=S_k^A+S_k^P`, halves `≍2^{2k}` (nearest singularity = the `s=1` pole, distance ½),
  residue `S_k≍γ_1^{−2k}` (`ξ'/ξ` poles only at zeros, distance `γ_1≈14.13`). They cancel to depth
  `2·(4γ_1²)^{−k}≈2·800^{−k}` — the `(s−1)·ζ` pole-cancellation that makes `ξ` entire, read at value level
  (= phase-defect `Δ_k∼k`). *Numerics corollary:* seam-Taylor `S_k` needs `≳2.9k` guard digits.
- **Fused closed form (ties B to A). `[PROVED — certified k≤6]`**
  `Σ_ρ(ρ−½)^{−2k} = 2^{2k} − ¼(2^{2k}−1)ζ(2k) − 2^{2k−2}β(2k) − (2(2k−1)!)^{−1}(ζ'/ζ)^{(2k−1)}(½)`
  (`β`=Dirichlet beta, `β(2)=G`). The zero-side power sum splits into **three arithmetically distinct
  constant-families**: π-periods `ζ(2k)`, the Catalan-family `β(2k)` (**not** a known π-period), and the
  prime `(ζ'/ζ)`-derivatives — a concrete value-relation feeding APEX-A.
- **FID = same instrument on the integer divisor.** `ζ(2k+1)=∫y^k dν`, `ν=Σ_m(1/m)δ_{1/m²}≥0` ⟹ the FID
  Hankel is PSD **unconditionally** (RH-empty: integers on the positive axis for trivial reasons; peeling
  only reconditions). In fact the shifted FID Hankel `H_FID[i,j]=ζ(2(i+j)+3)=Σ_n n^{−3}(n^{−2})^{i+j}` is
  **strictly totally positive** (Cauchy–Binet / generalized Vandermonde), yet *still* RH-empty: it
  certifies only the integer divisor `y_n=n^{−2}>0`, not the zero divisor `y_ρ=−(ρ−½)^{−2}`. So the bridge
  is **not** a stronger abstract positivity cone — the **FID⟹RH content is the integer↔zero map (the
  explicit formula / the weld split), never positivity of `ζ(odd)`**. (FID is sufficient-if-built, not
  equivalent.)

- **APEX-A — Schanuel-for-prime-logs (value / transcendence axis). `[OPEN CORE — Fields Medal]`**
  `corank^{(T)}=∞ ∀T≥2 ⟺ {log p}` ℚ-**algebraically** independent ⟺ `trdeg=∞ ⟺ DSS`. First rung
  `corank^{(2)}` open even for `{log 2, log 3}` (Gelfond–Schneider climbs only the pairwise-homogeneous
  bottom). Bigraded form **∧** `{γ_n}` alg-indep over `ℚ({log p})` = the exponential / Stieltjes column
  (`γ_E∉ℚ` open since 1734). **Role scoped:** "why the value detector is hard," *not* a necessary RH
  route. The fused form above exhibits the constant-families this axis must separate.
  No *value-arithmetic* detector separates ζ from a same-density random divisor. The seam values
  `{S_k = Σ(ρ−½)^{−2k}}` are arithmetically rigid — no integer relation with `π^{2k}` (degree-1) or in
  `{1,S_1,S_2,S_1²}` (degree-2) — unlike an arithmetic-progression divisor `γ_n=n`, whose
  `S_k = (−1)^k ζ(2k) ∈ ℚ·π^{2k}` collapse to exact relations (`π²+6S_1=0`, `5S_2=2S_1²`); ζ's complexity
  sits in the Catalan-family `β(2k)` and the prime-side term of the fused form. But this rigidity is
  **generic** — a same-density random divisor (generically ℚ-independent ordinates) shares it. The one
  structure that distinguishes ζ is the **explicit formula** `Σ_ρ h(γ_ρ) = arch − Σ_p (log p)…`: a
  relation of the zeros to the *external* set `{log p}`, which a random divisor lacks — prime-duality
  (B/C structure), not value-transcendence. So the open transcendence question (are `{log p}`
  ℚ-algebraically independent?) is about the primes' own independence, not a ζ-vs-random discriminator.
  This separator lives entirely in the **long-range order** of the ordinates: a divisor with ζ's *exact*
  gap distribution but randomly permuted gaps carries no prime resonance, so the distinction is invisible
  to every spacing / pair-correlation statistic, and its discrimination from such a control grows with the
  number of zeros rather than saturating.
- **APEX-C — universal orthogonality. `[CONJECTURE — strongly supported]`** No positive-definite
  polarization on any object of `𝓜` (the prime category) is RH-equivalent; every known criterion is
  archimedean. *Kill:* a genuine Source-B positivity criterion for RH (none in 150 years).
- **APEX-D — C5★ native weld / branchhood lock. `[OPEN CORE]`** The keystone weld theorem coupling the
  one non-CC (archimedean) lane to the CC (prime) lanes **jointly and irreducibly** (the combination-mode
  / joint-`σ_p` statement no single-prime parent can pose).
- **APEX-E — no prime-built generative flow. `[CONJECTURE — framing]`** No prime-built, order-preserving,
  generative one-parameter self-adjoint flow has the zeros as spectrum with self-adjointness ⟺ RH; any
  genuine Hilbert–Pólya realization is **archimedean positivity** (`κ₋=0` / Weil / `ι` unitary), not an
  evolution. *Support:* APEX-C, the constraint-not-flow theorem (Source-B flow spectrum `{log p}`,
  RH-blind), the archimedean Connes–Consani operators. *Kill:* such an operator. *Scope:* does **not** ban
  heat-flow / de Bruijn–Newman / archimedean positivity operators.

> **Two apexes joined ONLY at the seam.** `ω=0 ⇏ RH` (Davenport–Heilbronn is crystalline with off-line
> zeros; over `F_q` realization and RH hold for separate reasons) ⟹ **APEX-A (realization) and APEX-B
> (positivity) are distinct apexes**, welded only at the single archimedean locus `Re(s)=½`.

---

## §4 — Named / coordinate conjectures (most are coordinate-readings of the apexes)

- **Source-built faithful index (Master 2). `[CONJECTURE]`** Euler/PNT/Γ/FE data source-build a
  Jacobi/Loewner/Krein/**Hodge** object whose faithful negative-square index = the off-line zero count,
  forced to `0` by a **source-built polarization** (Hodge index, signature `(1,ρ−1)` — Sylvester, not an
  estimate; `J` a source-built complex structure). *Kill:* construction needs zero locations, or reduces
  to a measured trace / RH-equivalent restatement.
  - *Boundary localization.* The Euler/explicit-formula **bulk alone does not determine `κ₋`**: for a
    positive bulk `B>0` with finite boundary channels `V` and Hermitian boundary matrix `C` (the
    Γ/pole/archimedean extension), `H = B + V C V*` has, by Schur complement,
    `inertia(H) = inertia(B) + inertia(−C^{-1} − V*B^{-1}V) − inertia(−C^{-1})`; in the destabilizing
    case `C<0`, `κ₋(H) = κ₋(−C^{-1} − V*B^{-1}V)`. A rank-one boundary change crosses a Krein threshold
    `α_c = −1/⟨v,B^{-1}v⟩` and flips the inertia. So **source-built `κ₋=0` localizes to a finite-rank
    completed-boundary Weyl-PSD theorem** (`−C^{-1} − V*B^{-1}V ⪰ 0`); the boundary extension/domain is
    the remaining object, and a bulk-only construction is underdetermined. The boundary certificate must
    further be **uniform in scale**: a static finite-rank Schur check does not suffice under
    amplification — for `H(t)=I−ε e^{κt}vv*`, any finite audit horizon `T` is passed by taking
    `ε=e^{−κ(T+1)}`, yet a negative direction appears at larger `t`. So the theorem needs a
    **scale-independent boundary Weyl inequality** (a uniform amplification bound, or a canonical fixed
    extension), not a finite audit.
- **One object, two entrances. `[CONJECTURE]`** The Jacobi–Loewner–Krein–Hodge route and the
  Jensen / Laguerre–Pólya / Pólya–Schur route are two presentations of the same completed
  archimedean-polarized object. *Kill:* an invariant in one route untranslatable to the other.
- **ROUTE-C.** `A_arch − Σ_{p∈S}P_p ≥ 0 as S→all primes ⟺ RH`. *live.*
- **`D_∞` period-domain.** `RH ⟺ F_ζ` elliptic with period point interior to `D_∞=Sp_∞(ℝ)/U(∞)`;
  off-line zero = boundary direction.
- **Two-variable kernel.** `K_MS(s,w)~(1−Θ(s)\overline{Θ(w)})/(s+\bar w−1) ∈ N₀ ⟺ RH`.
- **DSS-cross.** Modulo the Grothendieck period conjecture, `DSS ⟺ {γ_n}` alg-indep over the period field
  (= APEX-A exponential column).
- **Jensen TP-defect = `2κ₋`.** `#non-real Jensen roots → 2κ₋`; `=0 ∀(d,n) ⟺ LP ⟺ RH` (verified: control
  0, off-line pair exactly 2).
- **Meta-principle.** *"Regularization manufactures transcendence"* — ζ-regularization / Hadamard
  finite-part is transcendence-creating; the `s=1`-Laurent (Stieltjes) is the instance.

---

## §5 — Gatekeepers (acceptance gates a valid test must pass)

Not carrier facts — required controls; many sharpen the conjecture definitions.

- **Affine passport `Π(S)=(|S|, Σ_{m∈S}m)`** — every affine tangent-volume observable factors through it
  (shift `−|S|log p`); the RH/holonomy content is the **shape beyond `Π(S)`**. Any determinant-volume /
  summed-Lyapunov experiment is RH-blind until `Π(S)` is subtracted.
- **APEX-B detector must be sign-changing AND scale-matched** — `C_a(τ)=2(a²−τ²)/(a²+τ²)²`, width `≈a/2`;
  broad averages cancel it (`8a → 0.016` of peak). A faithful positivity detector is local, not a mean.
- **Charts are blind without certificates:** anisotropic Jensen radius (direction-wise, not scalar
  margin); regularization fidelity (ridge `H+εI` ≠ congruence ⟹ regularized-object evidence); annular
  collar-clearance (source-to-contour radius lower bound; quadrature accuracy ≠ contour admissibility);
  guard-band invariance; per-lane-spectrum + cross-lane memory-kernel; multiscale (one-scale smoothing
  falsely merges off-seam pairs); height-coverage/mask; sampling-retention; recurrence (de-periodize the
  log grid); domain-corank leak `T/(N+T)`.
- **Value-axis ergodicity** — exact shell minima / meet-in-the-middle, not random residual histograms
  (random misses exact by `>10⁷×`).
- **Conjecture-E kill gate** — cluster-aggregated out-of-sample zero **and** spacing survival vs
  same-capacity non-prime decoys; numerical-representation passport (solver/precision/rcond/ridge) with a
  finite-window ladder (a single window or asymptotic-looking pass is insufficient).
- **`𝓜⁺` objectwise compatibility** — Γ/prime compatibility certified fiberwise/objectwise, copy-sector
  stable, with a closed-fiber reserve (iterated Γ/prime squares stay below threshold under endogenous
  update); an ensemble-zero commutator is not a weld category.

---

## §6 — Dependency and the one priority order

```
   C1,C7  ── (native-HT resolved = no) ──►  C1 = non-scalar holonomy form
   C2,C6  ── name the cohomology group ──►  reduces if = winding number
   C3,C4,C5 ── one functional each ──►  Groups B / C / the crossover
   B1,B2,B3 ── the RH arrow ──►  Lemma 2 (confine) = OPEN CORE
   APEX-A  ── Schanuel-for-prime-logs ──►  DSS / value axis    (Baker floor proven, ⊊ this)
   APEX-B  ── κ₋=0 / det H_d≥0 ∀d ──►  RH / positivity         (d=2 proven, uniformity open; build = Connes–Consani)
   APEX-C  ── no Source-B positivity ──►  the wall is archimedean
   APEX-D  ── C5★ joint-σ_p weld ──►  the native branchhood lock
   APEX-E  ── no prime-built flow ──►  Hilbert–Pólya is archimedean positivity, not evolution
   joined ONLY at the seam:  ω=0 ⇏ RH  ⟹  APEX-A and APEX-B are distinct apexes.
```

**Priority.** (1) **C2 holonomy modulo `Π(S)`** on a de-periodized log grid; (2) **source-built Jacobi
positivity** (Master 2 — the concrete faithful-index target) → the **Connes–Consani** handle; (3)
**uniform Jensen / `det H_d≥0 ∀d`** (port the GORZ asymptotic, with the anisotropic-radius + fidelity
gates); (4) the **sign-changing scale-matched APEX-B detector** with coverage — noting **FID positivity
is RH-empty; the bridge is the explicit-formula integer↔zero map**; (5) the **global seam confinement**
B2 / Lemma 2.
