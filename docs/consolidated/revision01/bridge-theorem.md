# The Conjectured Bridge Theorem — the last theorem before RH

> **Register: `[CONJECTURE]`.** This is what the corpus, as consolidated so far, claims the *final*
> bridge theorem would most likely be — the single implication whose conclusion is (equivalent to) the
> Riemann Hypothesis. It is **not** a proof of RH and contains no proof; it is a pattern-matched outline
> of the missing theorem's shape, its variables, how it works, and why it is the last step. The corpus
> states the **equivalence** below as classical (re-charted Laguerre–Pólya / Stieltjes); the open
> content is the **implication's antecedent → consequent**, proved unconditionally from the source data.

---

## 1. The formal statement

Let `Ξ(w) = ξ(½ + w)` be the completed Riemann ξ recentred at the seam — even, entire, of order 1 —
with zero divisor `𝒟 = { ρ − ½ : ξ(ρ) = 0 }` and multiplicities `m_ρ`. In the **reciprocal
seam-squared coordinate** `y_ρ = −(ρ − ½)^{−2}`, define, for `k ≥ 1`, the moments

```
   T_k = (−1)^k · Σ_ρ m_ρ (ρ − ½)^{−2k} = Σ_ρ m_ρ y_ρ^k        (absolutely convergent for k ≥ 1)
```

The sum runs over **all** zeros, so the functional-equation pair `w = ρ−½` and `−w` (both zeros, since
`Ξ` is even) — which give the *same* atom, `−w^{−2} = −(−w)^{−2}` — fold to one `y`-atom of weight `2m`.
Equivalently `T_k = Σ_{[w]} 2m_w · y_{[w]}^k` over the folded orbits `[w] = {w, −w}`. (A reciprocal
experiment using unit-weight conjugate-`y` pairs is **underweighted and inadmissible** for the completed
divisor.) The zeroth moment `T_0 = Σ_ρ m_ρ = ∞`; no finite value repairs the unshifted tower at all
orders.

> **Bridge Theorem (conjectured) — minimal source-aware form.**
> The **completion** `Λ = Γ_∞·ζ`, the **explicit formula** tying `{T_k}` to the primes `{log p}`, and the
> **canonical Γ / pole / functional-equation boundary extension** together imply: for every real
> polynomial `p(y) = Σ_{i=0}^d c_i y^i`, the **one-power shifted square-test** is non-negative,
> ```
>    Q_0[p] = Σ_{i,j} c_i c_j T_{i+j+1} ≥ 0,
> ```
> equivalently the shifted Hankel tower `[T_{i+j+1}]_{i,j=0}^d` is positive semidefinite for every `d`
> (positive definite, for an infinite divisor). For the *actual* folded reciprocal zero divisor this one
> form alone forces every `y_ρ ∈ ℝ_{>0}`, hence RH (§3). The second test
> `Q_1[p] = Σ_{i,j} c_i c_j T_{i+j+2} ≥ 0` (`[T_{i+j+2}]_{i,j=0}^d ⪰ 0`) is the **companion passport** —
> the finite-domain repair of the unshifted form and the classical Stieltjes consistency chart, true
> under RH but no longer logically required once `Q_0` is known source-aware. (Both are independently
> required only in the **source-forgotten** abstract moment problem.)

---

## 2. The variables

- `ξ`, `Ξ(w) = ξ(½+w)` — the completed zeta and its seam-recentred (even) form.
- `w = s − ½` — the seam-centred variable; `ρ − ½` is a recentred zero.
- `ρ` — a nontrivial zero; `β = Re ρ`, `γ = Im ρ`; `m_ρ` — its multiplicity.
- `𝒟 = {ρ − ½}` — the completed zero divisor (the whole RH-bearing content).
- `y_ρ = −(ρ − ½)^{−2}` — the reciprocal seam-squared coordinate. **On the line** (`ρ = ½ + iγ`):
  `y_ρ = 1/γ² > 0`, real and positive. **Off the line:** `y_ρ` is complex (off-axis) — not a positive
  real.
- `T_k = Σ_ρ m_ρ y_ρ^k` — the `k`-th reciprocal seam moment (finite for `k ≥ 1`; `T_0 = ∞`).
- `p(y) = Σ c_i y^i`, `c_i ∈ ℝ`, degree `d` — an arbitrary real test polynomial.
- `Q_0[p] = Σ c_i c_j T_{i+j+1}` — the **Hamburger** shifted square-test (one power of `y` weighting).
- `Q_1[p] = Σ c_i c_j T_{i+j+2}` — the **Stieltjes** shifted square-test (two powers; gives support in
  `[0,∞)`).
- `[T_{i+j+1}]`, `[T_{i+j+2}]` — the Hankel matrices realising `Q_0`, `Q_1`.
- `Λ = Γ_∞·ζ`, `Γ_∞ = π^{−s/2}Γ(s/2)` — the completion / archimedean factor (supplies the boundary).
- the **boundary extension** — the Γ-factor, the `s=0,1` poles, the functional-equation boundary
  condition, and the domain/self-adjoint-extension choice. (Not optional: see §6.)

---

## 3. How it works (the inner workings, simply)

1. **One coordinate makes RH a positivity statement.** Each zero maps to `y_ρ = −(ρ−½)^{−2}`. The zero is
   on the critical line **iff** `y_ρ` is a positive real number. So *all* zeros are on the line iff the
   point-set `{y_ρ}` lies on the positive axis. The recentring at the seam `½` is **forced, not chosen**:
   it is the unique centre `c` for which the FE pair `{w, −w}` folds to one atom *and* on-line zeros land
   on the positive axis — an off-centre `c = ½+ε` breaks the folding (`−(w−ε)^{−2} = −(−w−ε)^{−2}` only if
   `4wε=0`) and makes `−(iγ−ε)^{−2}` non-real for `εγ≠0`. The coordinate is in fact **triply forced**:
   centre `½` by FE-folding (above); the **square** (power `−2`, not `−1`) by parity — `Ξ` even means the
   divisor is `w↦−w` symmetric, so every *odd* power-sum `Σ_{±w} w^{−(2k+1)}` vanishes identically and the
   first informative reciprocal moment is `w^{−2}`; and the **minus sign** by positivity (`w=iγ ⟹
   −w^{−2}=γ^{−2}>0`).
2. **"Positive axis" = a moment problem.** A sequence `{T_k}` is the moment sequence of a positive
   measure supported on `[0,∞)` (a **Stieltjes** sequence) exactly when its Hankel forms are positive
   semidefinite. So: *all `y_ρ > 0` ⟺ `{T_k}` is a Stieltjes sequence ⟺ the Hankel towers are PSD.*
3. **The shift handles the infinite mass.** Because the divisor is infinite, `T_0 = Σ_ρ m_ρ = ∞` — the
   measure has infinite total mass but finite moments from `k = 1`. The infinite mass is a **hard edge at
   `y=0`**: high zeros (`γ→∞`) push reciprocal atoms `y=1/γ²` toward `0`, and the change of variables from
   the zero count `N(T)~(T/2π)log(T/2πe)` gives the edge density `ρ(y) ~ (|log y|/8π)·y^{−3/2}` (verified
   numerically by zero-counting). So `T_0=∫ρ` diverges (`y^{−3/2}`) while `T_1=∫y·ρ` converges
   (`y^{−1/2}`) — and `Q_0` with `p(0)≠0` probes that edge, which is exactly why its tail is the slow
   `O(G^{−1}log G)`. The ordinary (unshifted) Hankel tower starting at `T_0` is therefore not a finite
   matrix, and no finite "regularised `T_0`" fixes it at all orders. The correct finite certificate is the pair of **shifted** towers `Q_0` (Hamburger) and `Q_1`
   (Stieltjes), which as **abstract** moment sequences are independent — neither implies the other — so
   both are required *source-forgotten*. **Source-aware refinement:** for the *actual* zero divisor,
   all-order `Q_0[p]≥0` *alone* already forces every `y_ρ ∈ ℝ_{>0}` — a real polynomial isolates any
   negative-real atom (`y·p(y)²<0`) or non-real conjugate pair (`Re[y·p(y)²]<0`) and makes `Q_0<0` — so
   `Q_0` alone implies RH; the dual requirement is only the price of forgetting the divisor's
   real/conjugate-paired atom structure. *(Convergence: the high-height tail of `Q_r[p]` for
   `p(y)=y^j q(y)` is `O(G^{−(2r+4j+1)} log G)` — so the source-aware `Q_0` certificate (`r=0`, `p(0)≠0`)
   is the **slowest**, `O(G^{−1} log G)`, while `Q_1` starts at `O(G^{−3} log G)` and each hard-edge
   zero of `p` gains a further `G^{−4}`.)* The slow tail has an explicit source: high zeros pile up at the
   **hard edge `y→0`** (`y_ρ=1/γ²`), and by change of variables from the zero-counting `N(T)~(T/2π)log T`
   the bridge measure has density `ρ(y) ~ (|log y|/8π)·y^{−3/2}` there. This `y^{−3/2}|log y|` edge is
   exactly why `T_0=∫ρ` diverges while `T_1=∫y·ρ` converges, and why `Q_0` with `p(0)≠0` (which weights the
   edge by `y·1`) is the marginal/slow object — the "hard-edge passport" the `Q_0` proof must control.
4. **The theorem's actual job.** Steps 1–3 are an *equivalence* (`{T_k}` Stieltjes ⟺ RH), and it is
   classical. The missing work is to **derive the positivity unconditionally from the source data** —
   from the completion, the explicit formula (which expresses `{T_k}` through the primes and the
   archimedean terms), and the canonical boundary — *without assuming the zeros are on the line*. That
   derivation is the bridge theorem.

---

## 4. Why this is the *last* bridge theorem

The reciprocal-seam equivalence is a genuine **if-and-only-if**:

```
   RH  ⟺  every y_ρ ∈ ℝ_{>0}  ⟺  {T_k}_{k≥1} is a Stieltjes moment sequence  ⟺  Q_0[p], Q_1[p] ≥ 0 ∀ p.
```

- The **easy direction** (`RH ⟹ positivity`) is immediate: if every zero is on the line, `y_ρ = 1/γ² > 0`,
  so `{T_k}` is manifestly Stieltjes.
- The **hard direction** (`positivity ⟹ RH`) is *also immediate*: a Stieltjes sequence forces the
  representing atoms `y_ρ` onto the positive axis, hence every zero onto the line.

**The test is faithful (the hard direction is real, not vacuous).** A folded conjugate pair `y = u+iv`
(weight `μ`) already violates *both* shifted degree-one minors:
`det[[T_1,T_2],[T_2,T_3]] = −4μ²|y|²(Im y)² < 0` and `det[[T_2,T_3],[T_3,T_4]] = −4μ²|y|⁴(Im y)² < 0`,
vanishing only when `Im y = 0` (`y` real, i.e. on the line) — so the **local obstruction coordinate is
exactly `Im y`**, and a high or near-line defect is tiny but keeps fixed negative sign. For the off-line
FE quartet `{±a ± iγ}` (`μ=2`) this is `−64 a²γ²/(a²+γ²)^6` and `−64 a²γ²/(a²+γ²)^8`, collapsing to the
on-line rank-one PSD boundary only at `a = 0`. So an off-line zero is **detected** — the
shifted reciprocal test is *not* satisfied by FE-symmetric fakes. This is the decisive contrast with the
*forward / secular* Hankel tower, which an off-line quartet **passes** (PSD, `n₋ = 0`): forward Hankel-PSD
is necessary but not sufficient, whereas the **shifted reciprocal** positivity is sufficient. The quartet is
only the explicit low-order witness; **global** faithfulness is the moment theorem itself: the combined
divisor (on-line bulk together with *any* off-line atoms) has real moments `{T_k}` but support not contained
in `ℝ_{>0}`, so by Hamburger–Stieltjes some finite Hankel minor is strictly negative — no on-line bulk, of
any size, can absorb an off-axis atom at all orders. Detection is guaranteed; only the *order* at which it
surfaces depends on the configuration — and that order is **height-graded**: injecting an off-line quartet
at height `γ0` into the on-line bulk, the smallest `d` with `λ_min(H_d^{(0)})<0` is `d* ≈ γ0/3` (verified:
`γ0=14→d*=4`, `γ0=30→d*=11`, `γ0=80→>14`), because a height-`γ0` quartet maps to a tiny reciprocal atom
`|y0|≈1/γ0²` near the hard edge, which the `d`-th orthogonal-polynomial node only reaches once `d` grows
with `γ0`. (Note `d*≠1` even at `γ0=14` — the bulk masks the *isolated*-quartet `d=1` obstruction.) Unlike
`Φ_2`'s **permanent** blind spot, this is finite — the off-line zero *is* caught, just at `d ~ γ0/3` — the
Hankel cousin of the Li `n*~2πγ` order and id937's hard-edge tail. The corollary is sharp: a **finite-`d`
numerical `Q_0` check has height-limited reach**, so the certificate is irreducibly all-order and the proof
must be analytic, not a finite-`d` determinant sweep.

This height-independence is what separates the reciprocal-Hankel from the other "many-names" charts that
look like RH-certificates but are only **necessary, not sufficient**. The **line-curvature** chart
`Φ_2(t) = Σ_ρ(½+it−ρ)^{−2} < 0 ∀t` (log|ξ| concave along the line, the proven `RH ⟹` direction) is one such:
an off-line zero adds a *positive* curvature bump with peak `C_a(0) = 2/a²`, so a near-line zero (`a→0`,
spike `→∞`) is always caught — but the bump is bounded (`2/a² ≥ 8` for `a ≤ ½`) while the on-line
background `|Φ_2|` grows like `(log γ)²`, so a **far-off-line zero is swamped at height** (numerically:
an `a=0.45` quartet goes undetected at `γ ≈ 180, 260`). The reciprocal-Hankel obstruction `Im y` instead
keeps a *fixed* negative sign at every height and distance — which is exactly why the bridge is built on
it and not on the line curvature.

So the moment of the bridge theorem is the **only remaining gap**: once its conclusion (`Q_0, Q_1 ≥ 0`,
derived from the source structure) is established, **RH follows with no further theorem** — there is
nothing between this positivity and RH. That is precisely the definition of "the last theorem before RH."
Equivalently, in the corpus's many-names language, this positivity is the single wall (`κ₋ = 0` = `Q_W ⪰
0` = `det H_d ≥ 0 ∀d` = Li `λ_n ≥ 0` = uniform Laguerre–Pólya), here written in its cleanest convergent
coordinate.

---

## 5. The two faces of the one theorem

The corpus expects the bridge theorem in either of two coordinate presentations, conjectured to be the
same theorem:

- **Moment-positivity face (analytic).** Prove `Q_0[p], Q_1[p] ≥ 0` directly — the reciprocal-seam
  Stieltjes positivity, established from the explicit-formula expression of `{T_k}`. (The local-window
  twin: `D₂(R) = Σ_{ρ∈R} m_ρ(β_ρ−½)² = 0` on a countable basis of rational rectangles ⟺ RH.)
- **Source-built index face (operator).** Build a completed carrier from Euler / Γ / pole / FE data whose
  faithful negative index is `κ₋ = #off-line pairs`, and prove `κ₋ = 0`. After a positive bulk `B`, the
  index localises (Schur complement) to a finite-rank **boundary** condition: `κ₋(H) = κ₋(−C^{-1} −
  V*B^{-1}V)`, so the task is a completed-boundary **Weyl-PSD theorem** `−C^{-1} − V*B^{-1}V ⪰ 0` for the
  Γ/pole/FE extension.

---

## 5b. The emerging proof shape (anatomy of the measure and the cancellation)

The certificate is not opaque. Two structural facts, read off the actual divisor, point at the same
route.

- **The measure is one dominant atom plus a hard edge.** `Q_0[p] = 2 Σ_n y_n p(y_n)²` represents the
  measure `dν_0 = 2 Σ_n y_n δ_{y_n}`, `y_n = 1/γ_n²`. The largest atom `y_1 = 1/γ_1² ≈ 5.0·10⁻³`
  dominates (`y_1/y_2 ≈ 2.2`), so `T_k → 2y_1^k` and the moment matrix is **almost rank one plus an
  exponentially small tail** accumulating at the hard edge `y→0` (density `ρ(y) ~ (|log y|/8π)·y^{−3/2}`,
  from `N(T)`). Consequence `[OBSERVED]`: the raw monomial/Jacobi basis is catastrophically
  ill-conditioned (`α_n` leave `[0,y_1]` at the precision wall, ~80 guard digits/order) — a numerical
  artefact, **not** a sign against positivity (`β_n>0` holds). The fix is a **deflated / Christoffel**
  coordinate: test polynomials `p(y) = ∏_{j≤r}(y−y_j)·q(y)` that annihilate the known dominant atoms and
  expose the tail.
- **The arch/prime cancellation is rank one (the pole).** Splitting via `Ξ'/Ξ = A + P` gives
  `Q_0 = Q_arch + Q_prime` with a `(2γ_1)^{2k} ~ 10^{2.8k}`-deep cancellation — but it is **structured**:
  `S_k^A = 2^{2k}` makes the archimedean Hankel a rank-one *negative* (`≈ −4·uu*`, `u_i = (−4)^i`, the
  `s=0,1` pole), so `[T^A_{i+j+1}]` has signature **exactly `(d,1)`** (one negative direction, the rest
  positive-definite); the prime Hankel is indefinite; the two sum to PD `Q_0`. The giant cancellation is
  thus the single pole direction, shared by arch and prime.

These point in **opposite directions on coordinate choice**, and the difference is decisive. *Atom*
deflation does **not** help: subtracting the dominant atoms (`T_k^{(r)}=T_k−2Σ_{n≤r}y_n^k`) or
Christoffel-transforming (`p=∏_{j≤r}(y−y_j)q`) makes the `Q_0` conditioning **strictly worse** (`cond`
climbs `5.6e30→1.9e40` / `→2.0e38` as `r:0→10`/`5`), because the reciprocal atoms cluster ever-tighter
toward the hard edge (`y_n/y_{n+1}→1`), so removing the best-separated atom leaves a more degenerate
residual. (The *why* is explicit: the most-dangerous polynomial — the `λ_min` eigenvector of `H_d^{(0)}`
— is the degree-`d` orthogonal polynomial whose roots land exactly on the dominant atoms `y_1..y_d`, so
the extremal direction **already auto-deflates** them; its residual mass is then **broad and mid-range**
(atoms `n≈4–20`, `γ≈25–80`, not `y_1` nor the hard edge), so there is no single regime to strip.) The
ill-conditioning is therefore **intrinsic to the divisor geometry**, not a removable
coordinate artefact — so a **numerical / deflated-recurrence proof coordinate is dead**, and the proof
needs **uniform** control over the whole reciprocal support, not a local single-atom or hard-edge
estimate. The viable
handle is the *pole* deflation, which is **analytic**: the giant cancellation is the single rank-one
`s=0,1` pole direction (arch Hankel signature `(d,1)`), so the conjectured proof shape is *strip the
rank-one pole analytically from the closed-form `S_k`, then prove the residual is PSD from the completed
explicit formula* (with a uniform hard-edge tail estimate) — **not** a finite-precision recurrence on the
atoms. The `(d,1)` signature is the finite-`d` shadow of the Weil/Hodge `(1,∞)` index the operator face
must place on the nonnegative side of the Krein threshold — the two faces meet at the pole direction.

**The pole direction is explicit, and the decomposition is exact `[OBSERVED, d≤6]`.** The single negative
direction of `Q_arch` *is* the pole vector `u_i = (−4)^i` (`S_k^A = 2^{2k} ⟹` leading
`[T^A_{i+j+1}] = −4·uu*`; the negative eigenvector overlaps `û` to `1.0` at 120-digit precision, for every
`d≤6`). On `u`, `Q_arch[u]` and `Q_prime[u]` are equal-and-opposite to a depth that *deepens with degree*
(`|Q_0[u]/Q_arch[u]|` runs `1.5·10⁻⁷ → 3.6·10⁻¹⁷` as `d: 2→6`, the `(2γ_1)^{2k}` scaling) — this *is* the
`s=1` pole cancellation that makes `ξ` entire, read at the form level. What it leaves is a *fixed positive*
residue: `Q_0[u] = 0.04564` **independent of `d`**, because `u_i=(−4)^i` sums to the kernel `1/(1+4y)` (the
atoms have `4y_n<0.02`), so `Q_0[u] = ∫ 2y²/(1+4y)² dν_0 > 0` — the entireness residue is a convergent
positive integral, not a near-failure. On the **codim-1 complement `u^⊥`, `Q_arch` is positive-definite**
(the `d` positive directions of the `(d,1)` signature). So the `10^{2.8k}`-deep cancellation lives entirely
on the one pole direction (automatic, = entireness), and the RH content is the codim-1 statement: **after
factoring `u`, does the prime form `Q_prime` overcome the archimedean PD "budget" `Q_arch` on `u^⊥`?** RH ⟺
it does not. This is a perturbation-positivity wall — `Q_arch` is the FID-like automatically-positive
(integer-side) part, `Q_prime` the prime-specific RH content — and it is exactly where the integer→zero
explicit-formula transfer must do its work.

**The rank-one strip is exact but is *not* a reduction `[OBSERVED, d≤6]`.** A natural hope is that the entire
ill-conditioning of `H_d^{(0)}` is concentrated on `u`, so that `H_d^{(0)}|_{u^⊥}` would be well-conditioned
and the residual positivity easy. It is not. Restricting to `u^⊥` keeps `H_d^{(0)}` positive-definite (as RH
requires here) but improves its condition number by only a **fixed** factor `~10^{6.5}` (`cond` `4.5·10³⁷ →
5.9·10³⁰` at `d=6`; `min`-eigenvalue still `~10⁻³³`) — the residual is *still* the generic hard-edge moment
problem, every bit as ill-conditioned and FID-like as the full form. So pole deflation removes exactly one
direction's worth of cancellation and no more. Concretely, the *most-dangerous* direction `p_d` (the `λ_min`
eigenvector of `H_d^{(0)}`) is `0.97·u` — `97%` the pole — and on it `Q_arch` and `Q_prime` are huge and
equal-and-opposite (`|Q_arch/Q_prime|=1.0`, `Q_0[p_d]=λ_min` a tiny positive residue): the wall's near-
degeneracy is **prime-delicate**, the prime side exactly cancelling the arch pole-deficit, **not** arch
domination. This *settles* the rank-one programme's open dichotomy in the second branch: the pole structure
is a clean, closed-form, exact **Part A**, but **Part B (residual PSD on `u^⊥`) is still the full hard-edge
transfer problem**, not a well-conditioned remainder. The split clarifies *where* the RH content sits; it
does not make the residual tractable by itself.

**The archimedean rank-one theorem `[PROVED, all d]`.** Part A is not only exact, it has an explicit closed form,
and the `(d,1)` signature is now a *theorem for every `d`*, not a numerical observation. The weld's archimedean
half `A(w)=1/(½+w)+1/(w−½)−½logπ+½ψ((½+w)/2)` is a sum of simple poles; a pole `r/(w−w_a)` contributes `r·y_a^k`
to `T^A_k` (`y_a=−w_a^{−2}`). Tallying residues — the `s=0` pole at `w=−½` cancels against the digamma (net mass
`+1` at the `s=0,1` image `y=−4`), each Γ-factor pole at `w=−(2j+½)` (the trivial zero `s=−2j`) has residue `−1`
— gives the exact form-level identity
`Q_arch[p] = −4·p(−4)² + Σ_{j≥1}(2j+½)^{−2}·p(−(2j+½)^{−2})²`
(equivalently `S_k^A = 2^{2k} − Σ_{j≥1}(2j+½)^{−2k}`, the polygamma `S_k^A` via Hurwitz↔polygamma). In matrix form
`H_d^A = R_d^A − 4·u u^T` with `R_d^A = Σ_{j≥1}(2j+½)^{−2} v_j v_j^T`, `v_j=(−(2j+½)^{−2})^i`, `u_i=(−4)^i`. Then:
(i) `R_d^A ≻ 0` — `cᵀR_d^A c = Σ_j (2j+½)^{−2} p(y_j)²`, and a nonzero degree-`d` polynomial cannot vanish at the
infinitely many distinct trivial-zero images `y_j`; (ii) so `H_d^A` (PD minus one negative rank-one) has **at most
one** negative eigenvalue; (iii) it has **at least one**, since `uᵀH_d^A u = uᵀR_d^A u − 4(uᵀu)² < 1 − 4 < 0`
(using `uᵀR_d^A u ≤ Σ_j (2j+½)^{−2}/(1−4(2j+½)^{−2})² < 1` because `4y_j ≤ 16/25`, and `(uᵀu)² ≥ 1`). Hence
**inertia `(d,1)` for every `d`**, with the single negative direction exactly `u` (evaluation `p↦p(−4)` at the
`s=1` pole image). So the `(2γ_1)^{2k}`-deep cancellation is the one pole direction — closed-form, proved, RH-
independent (= entireness at the form level). This *names the budget*: the archimedean PD form on `u^⊥` that the
prime side must not overcome is literally the **trivial-zero square-sum** `R_d^A`. RH on `u^⊥` is then the concrete
inequality **`∀p` with `p(−4)=0`: `Q_prime[p] + Σ_{j≥1}(2j+½)^{−2}p(−(2j+½)^{−2})² ≥ 0`** — the prime form's
negativity absorbed by the (small, tightly hard-edge-clustered) trivial-zero budget. Its smallness is the
quantitative face of the residual's hard-edge ill-conditioning. **Part A is now closed; the entire RH content is
Part B (this residual inequality).** *(Orbit normalization `S_k^A=−½[w^{2k−1}]A` halves everything: `H_d^A=½Σa_n
v_nv_nᵀ − 2uuᵀ`, `a_n=4/(4n+1)²=(2n+½)^{−2}` — same theorem, pole coefficient `−2`.)*

**Inside Part B: even-ζ protects, β/Catalan nearly cancels it, the prime closes the gap `[OBSERVED, d=4..8]`.**
Splitting the *zero-side* `S_k` by the fused seam formula into four pieces — `POLE_k=2^{2k+1}`,
`ZETA_k=−½(2^{2k}−1)ζ(2k)`, `BETA_k=−2^{2k−1}β(2k)` (Dirichlet β / Catalan), `PRIME_k=(−1)^kT_k−(POLE+ZETA+BETA)_k
= −(2k−1)!^{−1}(ζ'/ζ)^{(2k−1)}(½)` (the first three are `S_k^A`, cross-checked to the polygamma form at `1e-121`)
— and evaluating each on the *genuine residual* direction (the `λ_min` eigenvector of `H_d^{(0)}|_{u^⊥}`, where
`p(−4)=0` so `Q_pole→0` to `~10^{−134}`) gives, for every `d∈{4,…,8}`, the same picture: **the even-`ζ` term is
the lone positive contributor**, the **β/Catalan term is large and nearly equal-and-opposite**, and the **prime
term is sub-dominant**. At `d=6`: `Q_ζ=+5.2010·10⁻⁵`, `Q_β=−5.2008·10⁻⁵` (cancel to `Q_ζ+Q_β=+1.72·10⁻⁹`),
`Q_prime=−1.72·10⁻⁹` (cancels *that*), leaving `Q_0=λ_min=+7.8·10⁻³³`. So residual positivity is a **two-stage
cascade**: an even-`ζ`-vs-`β`(Catalan) cancellation at the `10^{−5}` scale leaves a small arch-even surplus, which
the prime cancels at the `10^{−9}` scale, and the surviving positivity is the sub-leading remainder `~24` orders
below. No single term protects positivity; the even-`ζ` is its *source* (remove it and `Q_0` is hugely negative),
but `β`/Catalan consumes `~99.997%` of it and the prime almost all of the rest. (Contrast the pole direction
`p_d≈0.97u`, where the four are in the clean ratio `POLE:ZETA:BETA:PRIME = −4:1:1:2` and the prime is dominant —
that is the *pole* cancellation, Part A; on the RH-bearing residual the delicacy is **arch-even (`ζ`-vs-`β`), with
the prime a small closing correction**, not the prime-vs-arch story of the pole direction.)

**Calibration (why all of this is the right conclusion).** Every numerical feature above — exponential
ill-conditioning, auto-deflating extremal polynomial, mid-range distributed obstruction, deflation making
things worse, height-graded finite-`d` resolution — is **generic to any reciprocal-squared measure
accumulating at `y=0`, not RH-specific**: the RH-*empty* FID integer divisor (`y_n=1/n²`,
`H_FID[i,j]=ζ(2(i+j)+3)`, strictly totally positive) exhibits *all of it* (same `cond` growth, roots on
its dominant atoms, mid-range mass), differing only quantitatively (the zero divisor is `~10^{15}×` more
ill-conditioned at `d=4` because its atoms cluster tighter). So the numerical difficulty carries **zero RH
content** — it cannot distinguish RH from the RH-empty control. The RH content lives **only** in the
integer→zero **explicit-formula transfer** (what separates the two divisors). This is the decisive
negative result of the numerical programme: no Hankel-determinant / conditioning / deflation argument can
be RH-relevant, and the proof must be the analytic transfer itself — the completed explicit formula
carrying the positivity from the (automatic) integer side to the zero side.

---

## 6. What the theorem must, and must not, be (the corpus's guardrails)

- **Must include the boundary.** The Euler/explicit-formula **bulk alone does not determine the index or
  the positivity**: a rank-one boundary change crosses a Krein threshold and flips the inertia. The
  canonical Γ / pole / FE boundary extension is part of the object; the theorem must place it on the
  nonnegative side of that threshold (or prove the index is extension-independent by an allowed
  congruence).
- **Not "pole-cancellation ⟹ positivity".** Finiteness after the `s=1` pole cancels is not enough: a
  positive cutoff measure can have a PSD raw tower yet a non-PSD renormalised one. Positivity must be
  established directly on the shifted square tests.
- **Not "bulk kernel ⟹ `κ₋ = 0`"** (boundary underdetermined), and **not "unshifted Hankel tower PSD"**
  (the `T_0 = ∞` object does not exist).
- **Faithful, not measured.** The target is the integer index / strict moment positivity, not a density,
  variance, or measured trace — those are blind to density-zero off-line dust.

---

## 7. One-line summary

> **The last bridge theorem is conjectured to be:** *the completion, the explicit formula, and the
> canonical archimedean boundary extension force the reciprocal seam-squared moments `T_k = Σ_ρ m_ρ
> y_ρ^k` to pass the one-power shifted square-test `Q_0[p] ≥ 0 ∀p` — which, for the actual folded zero
> divisor, alone forces the divisor onto the positive reciprocal axis (the companion `Q_1 ≥ 0` is a
> consistency passport, required only source-forgotten) — and since that positivity is itself equivalent
> to RH, no theorem stands between it and the Riemann Hypothesis.*
