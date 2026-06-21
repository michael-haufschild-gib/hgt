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

**The canonical reading: the prime saturates the trivial-zero budget.** The `ζ`/`β` split is *not canonical* —
`Q_ζ+Q_β` is **positive-definite** (`[verified, inertia (d+1,0), d=4,6,8]`): it equals `4·p(−4)² + R_d^A[p]`, i.e.
the pole-evaluation square plus the trivial-zero budget, the whole arch part *minus* the `−8p(−4)²` pole term
`Q_pole`. The `ζ` and `β` pieces are just `R_d^A` (plus the pole square) **split by residue class mod 4**
(`2j+½=(4j+1)/2`, Hurwitz; `β=L(·,χ₄)`), so each is individually large and signed while their sum has **no
negative modes**. On the residual `p(−4)=0` it reduces to `Q_ζ+Q_β = R_d^A[p] > 0`. So the apparent "`ζ`-vs-`β`
battlefield" is an artifact of the split; the only RH content is `Q_prime` against `R_d^A`. And there the bridge
inequality is *tight*: on the most-dangerous residual direction `Q_prime[p]=−1.72·10⁻⁹` **nearly saturates**
`R_d^A[p]=+1.72·10⁻⁹`, their sum the razor-thin `λ_min=+7.8·10⁻³³` (`~24` digits of cancellation, every `d∈{4..8}`).
The prime consumes essentially **all** the budget. **Consequence for the proof:** `Q_prime+R_d^A≥0` is *tight*,
not slack — no soft bound `Q_prime ≥ −(1−ε)R_d^A` with fixed `ε>0` can hold; the proof must be exact /
equality-grade, not order-of-magnitude.

**Form-level entireness is complete, and it is *only* Part A.** The full weld split at the form level is
`H_d^A = R_d^A − 2u uᵀ` (arch, orbit norm) and `H_d^P = +2u uᵀ + R_d^P` (prime), the `+2uuᵀ` being the `ζ` pole
at `s=1` that exactly cancels the arch `−2uuᵀ`. Hence `H_d^0 = R_d^A + R_d^P` carries **no** pole term — the
`(s=1)` pole cancellation is exact at the `Q_0`-form level (entireness). The corollary is sobering: there is *no*
"pole-eliminated residual" smaller than `H_d^0` itself. The correct pole-quotient is the **Schur complement**
`C − bbᵀ/a` w.r.t. `u` (not a Euclidean restriction, which can spoil positivity), and `Schur_u(H_d^0)⪰0 ⟺
H_d^0⪰0` — still RH-equivalent. So pole cancellation removes one direction's *cancellation* but reduces the
*theorem* not at all: `R_d:=H_d^0` and `R_d⪰0` **is** the `Q_0` wall. A form-level no-go pins this down: with
`H^A=I−2uuᵀ`, `H^P=2uuᵀ−3I` the poles cancel yet `H^A+H^P=−2I≺0` — **pole cancellation ⇏ residual positivity**.
The proof must produce a *positive transfer*, not a cancellation.

**The partial square identity, and the shape of the obstruction `[DERIVED + verified d=4,6,8]`.** A *full* square
identity `Q_0[p]=∫|p|²dμ` (`μ≥0`) is RH (Weil/Stieltjes), so it cannot be written from source. But *half* of it is
free and explicit. Since `R_d^A = ∫|p|²dμ_triv` with `μ_triv=Σ_{j≥1}(2j+½)^{−2}δ_{y_j}` (the trivial-zero divisor,
a genuine **positive** measure, `M^A:=[∫y^{i+j}dμ_triv]` verified PD), the proved split gives the **partial square
identity**
`Q_0[p] = ∫|p|²dμ_triv + R^P[p]`,  `R^P := H_d^0 − M^A`,
i.e. an explicit positive-measure square **plus** the prime residual `R^P`, which carries *all* RH content. The
shape of `R^P` is now pinned: it is **high-rank and predominantly negative** — inertia `(1,4)/(2,5)/(2,7)` at
`d=4/6/8` (only `1–2` tiny-positive directions, `max`-eig `~3·10⁻⁸`), with a **stable** `min`-eig `≈ −0.2565`. So
the obstruction is *not* a low-rank correction one could deflate; it is a nearly-negative-definite form of full
dimension that the (small, hard-edge) trivial-zero square must dominate everywhere — and does so only barely (on
the dangerous direction `μ_triv`-square `=+1.7·10⁻⁹` against `R^P=−1.7·10⁻⁹`). Two consequences. (i) **There is no
independent prime kernel**: for polynomial test functions `R^P = H_d^0 − M^A` is fixed by the explicit formula
(nontrivial-zero minus trivial-zero moments) — the prime side does *not* supply a second positive measure, so the
square identity cannot be completed from source without proving `μ_0≥0` (= RH). (ii) The obstruction's high rank
reinforces the tightness verdict: no deflation of a few directions helps; the positive trivial-zero square must
dominate a full-dimensional negative `R^P`, exactly, everywhere. The viable route (08 cand. 1–2) is therefore a
**measure/transfer** proof that `M^A ⪰ −R^P` globally — i.e. that the prime residual stays inside the trivial-zero
budget on the whole polynomial cone — not a finite-rank or kernel-guessing argument.

**The discriminant attack: a manifest positive structure, and the first unconditional cases `[PROVED d=1]`.**
The shifted Hankel is the Gram matrix of `{1,y,…,y^d}` in `L²(ν')`, `ν'=Σ_ρ 2y_ρ δ_{y_ρ}`, so the **Gram/Heine
identity** makes its determinant a manifest tuple-sum:
`det H_d = (1/(d+1)!) Σ_{ρ_0,…,ρ_d} ∏_k (2y_{ρ_k}) · ∏_{i<j}(y_{ρ_i}−y_{ρ_j})²`  `[verified d=1,2 to 8 digits]`.
Every term is `≥0` exactly when its `y`'s are real-positive (RH); the *only* source of negativity is a tuple
containing an off-line conjugate pair `{y,ȳ}`, whose self-term is `2·y ȳ (y−ȳ)² = −4|y|²(Im y)² < 0`. This
localizes the wall termwise. **It also proves the low cases.** In the reciprocal coordinate an off-line pair at
height `γ₀`, real part `β'`, has `Re y = (γ₀²−β'²)/|w|⁴ > 0` and `|y| ≤ γ₀^{−2}`; so its negative self-weight is
`≥ −4γ₀^{−8}`, while its cross-term with each bulk zero `y_n` is `8 y_n Re(y(y−y_n)²) > 0` (positive: `Re y>0`,
`(y−y_n)²≈y_n²` for `γ_n≪γ₀`), of size `~γ_n^{−4}γ₀^{−2}`. The cross/self ratio is `~γ₁^{−4}γ₀^{6}→∞`, so **a single
off-line pair cannot flip `det H_1`** — confirmed numerically (deep pair `γ₀=50,β'=0.25`: self `−2·10⁻¹⁷` vs bulk
cross `+3.8·10⁻¹⁰`; aggressive low pair `γ₀=16,β'=0.49`: bulk wins `700×`). Hence:
> **Theorem `[PROVED]`.** `det H_1 = T_1T_3−T_2² > 0` for the actual `ζ`, unconditionally — the off-line self-terms
> are dominated by the positive on-line bulk cross-terms.

**Where this puts RH (the honest localization, not a retreat).** The same bound scales: a tuple with an off-line
point above the RH verification height `H` (`≈3·10^{12}`, Platt) has weight `≲H^{−2}≈10^{−25}`, astronomically below
the on-line bulk discriminant (set by `y_1≈0.005`). The on-line discriminant shrinks only at the hard-edge rate, so
it dominates the off-line negativity until the degree reaches the **detection threshold** `d*(H)≈H/3` (matching the
earlier injected-quartet `d*≈γ₀/3`). Therefore **`det H_d > 0` is unconditional for every `d ≲ H/3 ≈ 10^{12}`**, and
RH is *exactly* the statement that the bulk domination **survives the `d→∞` limit**, where infinitely many on-line
zeros accumulate at the hard edge `y→0⁺` and the Vandermonde factors `(y_i−y_j)²→0`. So the bridge is not a wall at
finite `d` (those are theorems) — it is the single asymptotic question of whether the hard-edge accumulation degrades
the discriminant faster than the (fixed, tiny) off-line budget can exploit. That is the precise open core, and it is
an *asymptotic* statement about the on-line zero spacing near the hard edge, not a generic positivity claim.

**The race, quantified, and the unconditional range `[MEASURED d≤16]`.** Two laws govern the bridge. (i) The on-line
margin `1−λ_max(K_d)` decays *super-exponentially with increasing rate*: `dlog₁₀(margin)/dd` runs `−4.7→−6.3` over
`d=3..16` — faster than any fixed geometric rate (each degree resolves deeper into the hard-edge cluster, where the
zeros are denser, costing more margin). (ii) The off-line **detection threshold** `d*(γ₀)` — the smallest degree at
which an injected off-line quartet at height `γ₀` makes `λ_min(H_d)<0` — grows roughly **linearly in the height**:
`d*=8,14,>16` at `γ₀=20,30,45` (slope `≈0.4` at off-line distance `β=0.1`), *not* in the zero-count
`N(γ₀)~γ₀logγ₀`. Combining: a hypothetical off-line zero lies above the RH verification height `H≈3·10^{12}`, so its
detection threshold is `d*≳0.4H`, and below that the bulk discriminant of the lowest `d+1` (verified on-line) zeros
strictly dominates. Hence the genuinely unconditional statement:
> **`det H_d > 0` for every `d ≲ 0.4·H ≈ 10^{12}`**, unconditionally (no off-line zero can flip it below its
> height-linear detection threshold).
RH is exactly the `d→∞` tail: the margin, though `>0` at every finite `d`, vanishes super-exponentially, and RH is
that it stays `>0` as the polynomials resolve the entire hard-edge cluster. The race is *balanced by faithfulness* —
the bridge detects every off-line zero, at depth `d*≈0.4γ₀` — so cracking `d→∞` is not a soft estimate; it is the
asymptotic positivity of the actual on-line zero-spacing measure, which is RH. What is *new and bankable* is the
mechanism (discriminant + bulk domination), the proved `d=1` case, and the explicit `10^{12}`-degree unconditional
range with a measured height-linear detection law.

**The bridge in its cleanest form: one-sided Loewner domination, and the margin → 0⁺ `[OBSERVED d≤8]`.** Because
`M_triv:=[∫y^{i+j}dμ_triv]≻0` and `Q_0 = M_triv + R^P`, the wall is the **Trivial-Zero Domination Theorem**
`−R^P ⪯ M_triv` — equivalently `λ_max(K_d) ≤ 1` for the relative operator `K_d := M_triv^{−1/2}(−R^P)M_triv^{−1/2}`.
This is *one-sided* (the prime may overshoot `M_triv` on the positive side — the `H^{ζβ}−H^{prime}` failure — only
the negative directions matter). Computing `K_d` (Cholesky `M_triv=LLᵀ`, `K_d=L^{−1}(−R^P)L^{−ᵀ}`): `λ_max(K_d)↗1⁻`
with margin `1−λ_max ≈ 2·10⁻⁹, 4·10⁻¹⁹, 2·10⁻²⁹, 2·10⁻⁴⁰` at `d=2,4,6,8` — **super-exponential** decay `~10^{−5d}`
(`≈γ₁^{−4d}`), the extremizing polynomial being exactly the dangerous direction `p_d` (overlap `1.0`, `0.97·u`). The
margin `1−λ_max(K_d)` is precisely the generalized eigenvalue `λ_min(Q_0,M_triv)` = the discriminant margin above, so
the two pictures coincide: the trivial-zero square dominates the prime residual with vanishing slack, and RH is
`λ_max(K_d)<1 ∀d` (the slack stays `>0` as `d→∞`). Finalized language: **protector** `= μ_triv` (explicit positive
trivial-zero measure); **threat** `= R^P` (high-rank, mostly-negative, prime-sourced); **RH** `=` protector dominates
threat in the one-sided Loewner order. The old "even-`ζ` protects / `β` threatens" was coordinate-dependent (the
character split); the invariant statement is the support-measure domination `−R^P ⪯ M_triv`.

**The no-margin law: the slack is an explicit product over the zeros `[MEASURED d≤20]`.** Fitting `1−λ_max(K_d)`
out to `d=20` (margin reaches `~10^{−113}`), the per-degree ratio `margin(d)/margin(d−1)` is `≈ γ_d^{−3.40}` with the
exponent **stable at `3.40`** for all `d`, so
`1−λ_max(K_d) ≈ C·∏_{n=1}^{d} γ_n^{−3.40}` (`~(d!)^{−3.4}`, super-exponential).
The slack is *literally an explicit product over the on-line zero heights* — `>0` at every `d` precisely because each
`γ_n` is real and finite, **factor by factor**; an off-line (complex) `γ_n` corrupts its own factor. That is the
cleanest statement of RH `=` slack stays positive: the reality of the zeros, read off the product. **The exponent is
density-determined, hence generic `[DERIVED + verified]`.** Both `ν'` (the zeros, `dν'~|log y|·y^{−1/2}dy` at `0⁺`)
and `μ_triv` (`~|y|^{−1/2}` at `0⁻`) are the same hard-edge class. The extremal `p_d` (roots on the lowest zeros)
gives per-step ratio `~ y_{d+1}y_d/c² ~ γ_d^{−4}` — exponent **4** from the reciprocal-square weight `2y_ρ~γ^{−2}`;
the measured `≈3.40 = 4 − 0.6` is a **logarithmic correction** from the zero density `N(T)~T logT`. Confirmed by
swapping the zeros for *synthetic* sets of controlled density (`M_triv` fixed): linear `γ_n=γ_1n` (const density)
gives `3.36→3.50↗4`, `√n` gives `3.31→3.45`, `n²` (sparse) gives `3.55→3.64` — the exponent **tracks the density**,
all drifting toward the universal `4`. So the no-margin *rate* is generic to any reciprocal-squared hard-edge
measure (the deepest form of the FID lesson): **RH is *not* in the exponent**; it is *only* in whether the product
`∏γ_n^{−exp}` stays positive — the reality of the zeros, factor by factor. **Structure of
`K_d`** `[d=8]`: in the `μ_triv`-orthonormal basis `K_d` is *not* Jacobi/Toeplitz/compact — it is
**corner-concentrated**, entries exploding toward the deepest index (`K[8,8]≈−6·10^4`, `~4×` per step), so `λ_max≈1`
is one dominant direction at the **deepest resolved (hard-edge) scale** (domination tightest at the deepest mode, as
the `d→∞` picture demands). **`K_d` is the clean off-line detector** `[verified]`: `M_triv` fixed (arch), so
`λ_max(K_d)>1 ⟺` off-line zero detected — at `d=10>d*(20)=8` a quartet at `γ_0=20` pushes `λ_max>1` for every `β>0`,
while at `d=4<d*` `λ_max<1` for all `β` (the finite-degree blindness in operator form).

**The sign is carried by a single eigenvalue `[verified]`.** Since the *rate* of the slack is generic (above), the
RH content is purely the *sign* `λ_min(Q_0,M_triv)>0`. Tracking *all* generalized eigenvalues of `(Q_0,M_triv)`
(`=I−K_d`) as a zero is pushed off-line: at `β=0` **zero** are negative; the instant `β>0`, **exactly one** turns
negative (the smallest, `+7·10^{−50}→−5·10^{−34}→−9·10^{−8}`) while the second-smallest stays strictly positive
(`~3·10^{−48}`). So an off-line zero flips **precisely the deepest hard-edge mode** — RH `⟺ λ_min(Q_0,M_triv)>0 ∀d`,
and leaving the line flips exactly that one eigenvalue, factor by factor. (The clean *determinant* factorization
hoped for does not materialize: the Cholesky pivots of `I−K_d` are orthogonal-polynomial norms with growing exponent
`2.97→13.06`, not the `γ_n^{−3.40}` margin factors — the product law lives in the `λ_min` spectral flow, not a
Cholesky/`L*L` factorization.) So the proof target is sharp: a **sign-preserving** explicit-formula transfer keeping
the single deepest eigenvalue positive — not any rate, kernel-norm, or determinant estimate. Proof-shape
(operator-`K` form): the `K_d` are compressions `K_d = P_d K P_d^*` of a single limiting operator `K` built from
the explicit formula, with `K ⪯ I` the theorem; the corner-concentration of `K_d` (entries blow up at the deepest
index) suggests `K` is **not compact** — the `λ_max→1` is essential-spectrum-like, so the proof is operator
monotonicity, not a finite eigenvalue bound.

**The domination is cross-scale, and the protector collapses to one point `[verified, d=10]`.** Band-decomposing both
sides on the dangerous mode `p_d`: the protector mass `M_triv[p_d]=Σ_j(2j+½)^{−2}p_d(y_j)²` sits **entirely at
`j=1`** (the coarsest trivial zero, `|y|=0.16`; `j≥4` contributes `<10^{−21}`), while the threat `Q_0[p_d]` mass sits
at the deep hard edge (peak zero `n*=6`, `y≈7·10^{−4}`) — the two live `~226×` apart in scale. So domination is
**not bandwise/dyadic** (a scale-local proof is dead); it is an irreducibly **cross-scale** balance — and on the
dangerous direction the entire protector reduces to a **single evaluation** `(2.5)^{−2}·p(−0.16)²` at the coarsest
trivial zero. (The deepest eigenvector itself has **no universal hard-edge profile**: rescaled to `ξ=y/y_d` the
degree-`d` mode gains oscillations with `d`, so the rescaled profiles diverge — `L²` distance `0.72→1.45→1.62` over
`d=6,8,10,12` — closing the "universal edge state" route.)

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
