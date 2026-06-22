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
    the `T_0=∞` exclusion in §3. *Form-level no-go (sharper):* with `H^A=I−2uuᵀ`, `H^P=2uuᵀ−3I` the poles
    cancel yet `H^A+H^P=−2I≺0`, so pole cancellation `⇏` positivity at the quadratic-form level; and since
    `H_d^0=R_d^A+R_d^P` is *already* pole-free (`H^A=R^A−2uuᵀ`, `H^P=+2uuᵀ+R^P`), there is **no** reduced
    residual: the correct pole-quotient is the Schur complement `Schur_u(H_d^0)`, and `Schur_u⪰0 ⟺ H_d^0⪰0`.
    So `R_d:=H_d^0` and `R_d⪰0` *is* the `Q_0` wall, not a reduction of it.
  - *The `ζ`-vs-`β` opposition is a residue-class artifact, not a battlefield. `[verified d=4,6,8]`* In the fused
    split `Q_arch=Q_pole+Q_ζ+Q_β`, the pair `Q_ζ+Q_β` is **positive-definite** (inertia `(d+1,0)`, `= 4p(−4)²+
    R_d^A`); the `ζ`/`β` halves are `R_d^A`(+pole square) split by character mod 4 (`β=L(·,χ₄)`), individually
    signed but summing PD. So the only RH content is `Q_prime` vs `R_d^A` (the named `u^⊥` inequality above), and
    it is **tight** (the prime saturates the budget to `~24` digits on the worst residual direction; no soft bound
    `Q_prime≥−(1−ε)R_d^A` survives). *Candidate proof shapes for the tight residual (proof must be exact):*
    (1) a **square identity** `R_d[p]=∫|𝒦_p|²dμ`; (2) a **positive transfer** integer/prime-side→zero-side (not
    FID, which is RH-empty); (3) a **Weil-form pullback** — a test function `h_p` with `Q_0[p]=Q_W[h_p]` and the
    completed explicit formula giving `Q_W[h_p]≥0`; (4) a **source-built index** `Q_ξ` with `neg(Q_ξ)=#`off-line
    pairs, then `Q_ξ⪰0`.
  - *Square identity (cand. 1), pushed: it is only PARTIAL from source `[DERIVED + verified d=4,6,8]`.* A full
    `Q_0[p]=∫|p|²dμ` (`μ≥0`) is RH. But `R_d^A=∫|p|²dμ_triv` (`μ_triv=Σ_{j≥1}(2j+½)^{−2}δ_{y_j}`, an explicit
    **positive** measure, `M^A` verified PD), so the proved split gives `Q_0[p]=∫|p|²dμ_triv + R^P[p]` — an explicit
    positive-measure square **plus** the prime residual `R^P:=H_d^0−M^A`, which carries all RH content. `R^P` is
    **high-rank and predominantly negative** (inertia `(1,4)/(2,5)/(2,7)` at `d=4/6/8`, only `1–2` tiny-positive
    modes, stable `min`-eig `≈−0.2565`) — *not* a low-rank correction. And for polynomial tests `R^P` is fixed by
    the explicit formula (nontrivial- minus trivial-zero moments): the prime side supplies **no second positive
    measure**, so the square cannot be completed from source without `μ_0≥0` (= RH). The honest target is a measure
    /transfer proof that the (small, hard-edge) trivial-zero square `M^A` dominates the full-dimensional negative
    `R^P` everywhere — exactly, per the tightness.
  - *The cleanest finite shadow, the ranked proof menu, and the three-stratum divisor. `[SYNTHESIS — gpt/37]`*
    The domination `M^A ⪰ −R^P` is cleanest as **one-sided Loewner**:
    `K_d := M_triv^{−1/2}(−R^P)M_triv^{−1/2}`, RH ⟺ `λ_max(K_d) ≤ 1 ∀d` (only the negative directions matter —
    the prime may overshoot on the positive side). The sharpening on the *proof object*: not "find some
    positivity" but **source-build a factorization/contraction giving `I−K_d⪰0` at zero margin** (the tightness
    forbids any slack — no `Q_prime ≥ −(1−ε)R_d^A` survives). The divisor is **three-stratum** — pole `y=−4`
    (entireness `u`), trivial chain `y_j=−(2j+½)^{−2}` (positive protector `μ_triv`), nontrivial
    `y_ρ=−(ρ−½)^{−2}` (to be forced onto `ℝ_{>0}`); **RH divisor** = Stieltjes positivity of the nontrivial
    divisor, **proof divisor** = the trivial-zero divisor as a boundary protector (RH = "the completed
    reciprocal divisor is a positive Stieltjes divisor once the `y=−4` pole boundary is absorbed"). Candidate
    shapes, **ranked**: (1) one-sided Loewner / boundary-Weyl `K⪯I` — `K_d` as a compression of a single
    **non-compact** completed-boundary `K` (corner-concentration ⟹ essential-spectrum-like `λ_max→1`); (2)
    Weil-pullback `p↦h_p` with `Q_0[p]=Q_W[h_p]`; (3) discriminant / Gram–Heine ladder past `d=1`; (4) direct
    Jacobi / Hankel-det (lowest — hard-edge ill-conditioned). Forward route-killers in `research-topics.md`
    #35–44; the decisive fork is whether the **Dirichlet/DH** test makes `K_d⪯I` a real **source gate** (genuine
    Euler-product `L` pass, Davenport–Heilbronn fails by `λ_max>1`) or whether broad hard-edge fakes also
    dominate (then the theorem to find is *why the explicit formula puts `ζ` in that domination class*).
  - *Fork RESOLVED empirically `[2026-06-22 battery — exact ζ/L moments; logs/gpt37-computations-worklog.md]`.*
    Both branches partly hold, and the verdict is the **second**: (i) the bridge structure **reproduces for every
    genuine completed `L`** (vanishing margin + pole-aligned `u`, overlap 0.97–0.99) — the mechanism is
    **Euler-product-family general**, not ζ-specific; but the exponent is **protector/parity-set** (ζ 3.41, odd-`χ`
    3.90, even-`χ` 5.05 at equal density), not a universal density constant. (ii) The **real Davenport–Heilbronn**
    counterexample (first off-line zero `γ=85.7,σ=0.808`; even completion validated to `10^{−360}`) is **NOT
    detected by `K_d` through d=55** (its reciprocal atom `Im(y)≈10^{−6}` sits at the hard edge; `d*≈55` by the
    detection law) — so `K_d⪯I` is faithful but **height-limited: not a finite-`d` source gate**. (iii)
    **Jittered-ζ** (positions kept, correlations destroyed) reproduces ζ's margin law to **4–5 digits** ⟹ the
    numerics carry **zero prime/correlation content**. Net: the operative open theorem is exactly *"why the explicit
    formula puts `ζ` in the domination class"* — **at the level of the all-order sign**, never a finite-`d` gate.
    (Ranked-route updates: route 2 Weil-pullback is **inadmissible** — `h_p` has a pole at `t=0⟺s=½`, needs a de
    Branges/Krein limit, boundary at the **seam centre**; route 1 is favored — `K` non-compact (`λ_max→1`), and
    `R^P` is **near-tridiagonal/Jacobi (99.994% banded) in the protector-point `(y+0.16)` basis**, rank-1 in norm
    but full-rank in sign.)
  - *Purified target — a single named operator. `[SYNTHESIS — gpt/38]`* The battery's net effect is a
    **purification**: with every finite-`d`/conditioning/margin/correlation observable demoted, B1–B3 reduce to one
    statement — *the completed explicit formula produces a **noncompact self-adjoint contraction**
    `K = M_triv^{−1/2}(−R^P)M_triv^{−1/2}` with `K ⪯ I`, `‖K‖=1`, `1∈σ_ess(K)`, finite sections `K_d=P_d K P_d^*`,
    built without zero-feeding.* RH `⟺ λ_min(I−K_d)>0 ∀d` (**sign, not rate**), so the proof is **boundary
    monotonicity / Weyl positivity**, never a spectral-gap / `λ_max≤1−ε` estimate (comp7: `λ_max→1`, noncompact).
    The **proof divisor** is a four-point *compactified reciprocal-boundary* divisor — seam centre `y=∞` (s=½, the
    de Branges/Krein boundary where the Weil-pullback breaks) + pole `y=−4` (Part A, closed) + first trivial-zero
    protector `y=−0.16` (exterior Christoffel point) + hard edge `y=0⁺` — controlling the nontrivial divisor (the
    object, not the proof divisor). Smoking gun: the **first trivial zero `−0.16` controls the whole hard edge `0⁺`**
    (`1/margin=(2.5)^{−2}K_{ν'}(−0.16,−0.16)`). Forward operator-identity computations: `research-topics.md` #45–52.
  - *Operator-identity battery — the boundary-Weyl theorem is RANK-ONE. `[2026-06-22, VERIFIED d=8,12,16]`* `H^0=
    H0_minus+(2.5)^{−2}vv^T`, `v=e(−0.16)`, with **inertia(H0_minus)=(d,1)** (one defect); RH `⟺` the **scalar**
    `s(d)=(2.5)^{−2}+1/(v^T H0_minus^{−1}v)≥0`, `s(d)=(2.5)^{−2}·margin→0⁺` — operator face = moment face = scalar
    boundary face. The datum `(y=−0.16, mass (2.5)^{−2})` is **exactly critical** (a_c(−0.16)=0.16, deficit=0.16·
    margin) and `y_*=−0.16` **minimizes** a_c over the exterior (optimal control point). Both band- and low-rank
    approximations are **dead** (dropping the 0.8% off-Jacobi tail flips margin +10^{−40}→−10^{16}; every rank-`r<d+1`
    truncation gives the wrong sign). No-margin exponent law: **α≈4.31+½ln|y_*|** (archimedean-protector-set). So
    the target is a **source-built RANK-ONE boundary-Weyl contraction**: build bulk H0_minus (inertia (d,1)) + the
    single boundary atom from Γ/pole/FE/EF without zero-feeding, prove `s(d)≥0 ∀d` keeping the exact sign tail.
  - *Collapse to a scalar gap — the "one theorem before RH", rank-one form. `[SYNTHESIS — gpt/39]`* The bridge
    collapses one level further: the **proof divisor reduces to the single rank-one exterior datum**
    `a_*δ_{y_*}=0.16·δ_{−0.16}` (the pole `y=−4` is automatic Part-A bookkeeping; the rest of the trivial chain is
    background; **`j=1` is the active gate**), and RH becomes a **scalar** inequality: `H^0_d=H^-_d+0.16·v_*v_*^T`,
    `inertia(H^-_d)=(d,1)`, the first-trivial-zero atom repairs the one bulk defect, leaving the **Weyl gap**
    `s_d=0.16·margin_d>0 ∀d` (`a_*−a_c(d;y_*)=0.16·margin_d`, →0⁺). **RH ⟺ the scalar Weyl gap created by the first
    trivial zero stays positive at every degree.** Open faces: (i) source-build `H^-_d` + the boundary `m`-function
    at `y=−0.16` without zero-feeding; (ii) weld route-2 — the seam-centre (`s=½`) de Branges/Krein regularization
    of the Weil pullback must produce exactly this rank-one boundary condition (`FP_{s=½}Q_W[h_p] → H^-_d+0.16 v_*v_*^T`,
    gap `s_d`). Forward computations: `research-topics.md` #53–59.
  - *The four-piece proof program — the Rank-one Γ-boundary Weyl Bridge. `[gpt/41 + gpt/proof4]`* B1–B3 now have a
    named four-piece structure: **(A)** reciprocal chart, target `Q_0[p]≥0 ∀p`; **(B)** **Γ boundary split**
    `H^0_d=H^-_d+a_*v_*v_*^T`, the atom = the first Γ-trivial-zero term (source-built, no zero-feeding — comp57);
    **(C)** **one-defect bulk theorem** `inertia(H^-_d)=(d,1) ∀d` (verified ζ/real-`L`/DH; "removing the first
    Γ-boundary atom leaves exactly one negative square" — the Krein/Weyl localization the corpus expected); **(D)**
    **scalar Weyl gap theorem** `s_d=a_*+1/m_d=1/K_{ν'}(y_*)=a_*·margin_d>0 ∀d`. New reduction (given C):
    **`Q_0[p]≥0 ∀p ⟺ s_d>0 ∀d`**. **Named fake-family gate: `s_d=0`** (DH crosses at d=62, inertia (d,1) preserved
    — separates DH at a *structural* gate, satisfying the corpus's fake-family-separation requirement). The exponent
    is now **derived**: `α_d(y_*)≈4+[4(1−ln2)+2ln|y_*|]/L̄_d` (no universal ½). **The remaining paper theorem** is a
    finite-part identity: source-identify the Hankel tail `μ_E` (comp56) as the seam-centre finite-part boundary
    distribution and prove `FP_{w=0}Q_W[h_p]=Q_0[p]−a_*p(y_*)²`, hence `s_d>0`. Only "prove (all-`d`)" remains.
  - *The seam finite-part construction — built; the open content is now the scalar positivity alone. `[gpt/proof5–8]`*
    **(i) Lemma 1 `[VERIFIED — comp60]`:** `Q_0[p]=−Res_{w=0}[h_p·(Ξ'/Ξ)]`, `h_p=−w^{−2}p(−w^{−2})²` — the bridge
    form is a seam-centre residue of the COMPLETED `Ξ'/Ξ`; `Ξ'/Ξ=A+P ⟹ Q_0=Q_A+Q_P` source-side. **(ii) the canonical
    finite part exists `[gpt/proof7]`:** admissible even approximants `h^{ε,R}=t^{−2}p(t^{−2})q(t^{−2})η(t/ε)ψ(t/R)`
    give a Hadamard expansion with only odd powers and `B=0` (no log) by evenness; the finite part is `η`- and
    `ψ`-independent (no `u^{−1}` term for even jets), has an `R→∞` limit, and is necessarily **Hankel** — the analytic
    proof of `E_{ij}=f(i+j)`. Gauge `Ξ→e^{q(w²)}Ξ` shifts it by a local Hankel counterterm fixed by canonical
    `ξ`-normalization ⟹ the finite part is **unique** (canonicality settled). **(iii) `E=μ_E` `[gpt/proof8 — proved,
    cond.]`:** with the source-defined Green split `R^P=J+𝓑` (`J` Jacobi, `𝓑` seam), `𝓑_{ij}=e^{fp}_{i+j}` (from the
    source prime-residual distribution, not zero-fed); `J` Jacobi + both Hankel ⟹ `E=𝓑=μ_E` on all `i+j≥2` (the
    `i+j=0,1` entries pinned by canonical `ξ` + the Γ-atom). So "what is `E`" is closed: source-built `μ_E`. **Open:
    `s_d>0 ∀d`** alone — the RH-bearing positivity of `H^-=J+μ_E+μ_{≥2}` after the `a_*δ_{y_*}` repair.
  - *The `χ₄`/character-decomposition route is DEMOTED `[evaluated, d=4,6,8]`.* `β=L(2k,χ₄)` and the arch budget is
    the quarter-integer Hurwitz tower `S_k^A=2^{2k+1}−2^{−2k}ζ(2k,¼)`, whose mod-4 split is principal `ζ` (all odd
    integers) `+` `χ₄` `β` (`ζ(2k,¼)±ζ(2k,¾)`). But character decomposition **breaks** the manifest positivity:
    `inertia(H^ζ)=(d+1,0)` (PD, the all-odd-integer budget) while `inertia(H^β)=`indefinite (`≈(d−1,⌈d/2⌉)`, stable
    `min`-eig `≈−0.226`); their sum (the `1`-mod-`4` residue-class budget) is PD only because it is a *positive
    measure*. So splitting by character turns "a positive measure has a PSD Hankel" (trivial) into "a PD principal
    sector dominates an indefinite `χ₄` sector" (harder). **Positivity lives in the residue-class measure cone, not
    the character/spectral basis** — the Dirichlet split is a dual operation that does not respect the
    positive-measure cone. Mild salvage: the regrouping `Q_0^{res}=Q_ζ(all-odd PD) + (Q_β+Q_prime)` is cleaner than
    `ζ`-vs-`β`, but still RH-equivalent and tight. So the proof must stay in the **measure/support** representation
    (square test functions over the actual divisor), not a character basis.
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
