# The Conjectured Bridge Theorem

> **Register: `[CONJECTURE]`.** This is what the corpus, as consolidated so far, claims the missing
> bridge theorem would most likely be — the single implication whose conclusion is (equivalent to) the
> Riemann Hypothesis. It is **not** a proof of RH and contains no proof; it is a pattern-matched outline
> of the missing theorem's shape, its variables, and how it is expected to work. The corpus
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
> form alone forces every `y_ρ ∈ ℝ_{>0}`, hence RH (§3; the `Q_0≥0 ⟹ RH` half is **`[PROVED — gpt/proof12]`** by
> classical moment theory — the open content is the converse, source-built `Q_0≥0`). The second test
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
   both are required *source-forgotten*. **Source-aware refinement `[PROVED — gpt/proof12; classical moment theory]`:**
   for the *actual* zero divisor, all-order `Q_0[p]≥0` *alone* already forces every `y_ρ ∈ ℝ_{>0}`, hence RH. Rigorous
   mechanism (proof12): `Q_0⪰0` ⟺ `[T_{i+j+1}]⪰0` ⟹ (Hamburger/Riesz) a positive measure `μ` on `ℝ` with
   `∫xⁿdμ=T_{n+1}`, compactly supported on `[−R,R]` (`R=sup|y_ρ|<∞` since `ξ(½)≠0`); the divisor generating function
   `G(z)=Σ_α M_α y_α/(1−y_α z)` is meromorphic with poles at `1/y_α`, while `G(z)=∫dμ/(1−xz)` is the Cauchy transform
   of a positive real-line measure — holomorphic off `ℝ`, so a **non-real atom (non-real pole) is impossible** (Step 3);
   then `μ=ν:=Σ_α M_α y_α δ_{y_α}` by Weierstrass (equal compactly-supported moments), and `μ≥0` with `M_α>0` forces
   `y_α>0` (Step 4). The dual `Q_1` requirement is only the price of forgetting the divisor's real/conjugate-paired
   structure. *(This is the `⟹` half — the rigorous write-up of the reduction; the hard `⟸` direction, source-built
   `Q_0≥0`, is untouched and remains the open bridge.)* *(Convergence: the high-height tail of `Q_r[p]` for
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

So the moment of the bridge theorem is the **remaining bridge gap**: once its conclusion (`Q_0, Q_1 ≥ 0`,
derived from the source structure) is established, **RH follows by the equivalence already recorded above**.
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

**The discriminant attack: a manifest tuple structure, with the low-case sign shortcut removed.**
The shifted Hankel is the Gram matrix of `{1,y,…,y^d}` in `L²(ν')`, `ν'=Σ_ρ 2y_ρ δ_{y_ρ}`, so the **Gram/Heine
identity** makes its determinant a manifest tuple-sum:
`det H_d = (1/(d+1)!) Σ_{ρ_0,…,ρ_d} ∏_k (2y_{ρ_k}) · ∏_{i<j}(y_{ρ_i}−y_{ρ_j})²`  `[verified d=1,2 to 8 digits]`.
Every term is `≥0` exactly when its `y`'s are real-positive (RH); the *only* source of negativity is a tuple
containing an off-line conjugate pair `{y,ȳ}`, whose self-term is `2·y ȳ (y−ȳ)² = −4|y|²(Im y)² < 0`. This
localizes the wall termwise. **Correction (2026-06-24).** The earlier termwise low-case proof overstated the
cross-term sign. In the reciprocal coordinate an off-line pair at height `γ₀`, real part `β'`, has
`Re y = (γ₀²−β'²)/|w|⁴ > 0` and `|y| ≤ γ₀^{−2}`, so its negative self-weight is `≥ −4γ₀^{−8}`. But
`Re(y(y−y_n)²)>0` is **not** implied by `Re y>0`; `discriminant-bulk-cross-sign-needs-scale-separation.md`
gives the exact counterexample. The usable replacement is the exact interval in
`discriminant-cross-positive-interval.md`: for `y=u+iv`, `a=|v|`, `r=|y|`,
the cross term is positive for every `x>x_+(y)`, where
`x_+(y)=(u²−a²+ar)/u`, and the simpler sufficient bound is `x≥1.18|y|`.
This is relevant for hypothetical off-line zeros far above the verified low-zero bulk, but it is not a global
termwise proof.
> **Status.** The discriminant identity and the local off-axis negative term are proved. The unconditional
> statement `det H_1 = T_1T_3−T_2² > 0` for actual `ζ` is not promoted by the termwise argument above until a
> full summed domination estimate or another source proof is supplied. The valid degree-one replacement is
> `degree-one-discriminant-tail-stability.md`: split the verified positive real bulk from the remaining tail and
> prove an explicit determinant-margin inequality. The all-degree finite-height replacement is
> `finite-degree-shifted-hankel-tail-stability.md`: prove that the verified bulk eigenvalue margin dominates an
> explicit tail matrix norm. But `monomial-tail-gate-height-linear-no-go.md` shows that the monomial absolute-tail
> version cannot prove a height-linear range; any serious version must be relative/orthogonal-polynomial/source-Weyl.

**Where this puts RH (the current localization, not a retreat).** The scale bound suggests a real finite-range
mechanism: an off-line point above the RH verification height `H` (`≈3·10^{12}`, Platt) has reciprocal size
`≲H^{−2}≈10^{−25}`, while the lowest verified on-line atoms are far larger. In that high/low regime the cross terms
with those low atoms are positive by the `1.18|y|` criterion. What is not yet proved is the global tuple or summed
domination estimate needed to promote this scale fact to `det H_d>0` for every degree below a height-dependent
threshold. Thus `d*(H)≈H/3` is a candidate detection/localization law until the summed inequality is supplied. The
open core is whether hard-edge accumulation of on-line zeros erodes the discriminant faster than the off-line budget
can be dominated; this is an asymptotic statement about the on-line zero spacing near `y=0⁺`, not a generic positivity
claim.

**The race, quantified, as evidence `[MEASURED d≤16]`.** Two laws govern the candidate bridge. (i) The on-line
margin `1−λ_max(K_d)` decays *super-exponentially with increasing rate*: `dlog₁₀(margin)/dd` runs `−4.7→−6.3` over
`d=3..16` — faster than any fixed geometric rate (each degree resolves deeper into the hard-edge cluster, where the
zeros are denser, costing more margin). (ii) The off-line **detection threshold** `d*(γ₀)` — the smallest degree at
which an injected off-line quartet at height `γ₀` makes `λ_min(H_d)<0` — grows roughly **linearly in the height**:
`d*=8,14,>16` at `γ₀=20,30,45` (slope `≈0.4` at off-line distance `β=0.1`), *not* in the zero-count
`N(γ₀)~γ₀logγ₀`. Combining: a hypothetical off-line zero lies above the RH verification height `H≈3·10^{12}`, so its
detection threshold is expected to be `d*≳0.4H`. This is evidence for a finite-range domination theorem, not that
the theorem has already been proved. RH is exactly the `d→∞` tail: the margin, though positive in the measured
finite windows, vanishes super-exponentially, and RH is that it stays positive as the polynomials resolve the entire
hard-edge cluster. What is currently bankable is the mechanism (Gram/Heine identity plus local off-axis negative
term), the exact cross-positive interval, the degree-one and finite-degree tail-stability gates, the monomial-gate
no-go, the finite-degree height-limited perturbation theorem, and the measured height-linear detection law. The
unproved step is the source-level relative domination estimate for the actual divisor.

**The bridge in its cleanest form: one-sided Loewner domination, and the margin → 0⁺ `[OBSERVED d≤8]`.** Because
`M_triv:=[∫y^{i+j}dμ_triv]≻0` and `Q_0 = M_triv + R^P`, the wall is the **Trivial-Zero Domination Theorem**
`−R^P ⪯ M_triv` — equivalently `λ_max(K_d) ≤ 1` for the relative operator `K_d := M_triv^{−1/2}(−R^P)M_triv^{−1/2}`.
This is *one-sided* (the prime may overshoot `M_triv` on the positive side — the `H^{ζβ}−H^{prime}` failure — only
the negative directions matter). Computing `K_d` (Cholesky `M_triv=LLᵀ`, `K_d=L^{−1}(−R^P)L^{−ᵀ}`): `λ_max(K_d)↗1⁻`
with margin `1−λ_max ≈ 2·10⁻⁹, 4·10⁻¹⁹, 2·10⁻²⁹, 2·10⁻⁴⁰` at `d=2,4,6,8` — **super-exponential** decay `~10^{−5d}`
(`≈γ₁^{−4d}`), the extremizing polynomial being exactly the dangerous direction `p_d` (overlap `1.0`, `0.97·u`). The
margin `1−λ_max(K_d)` is precisely the generalized eigenvalue `λ_min(Q_0,M_triv)` = the discriminant margin above, so
the two pictures coincide: the trivial-zero square dominates the prime residual with vanishing slack, and RH is
`λ_max(K_d)<1 ∀d` (the slack stays `>0` as `d→∞`). Current language: **protector** `= μ_triv` (explicit positive
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
all drifting toward the universal `4`. *(Refined 2026-06-22: across the completed-`L` family the exponent is
**protector/parity-set, not universal** — ζ≈3.41, odd-`χ`≈3.90, even-`χ`≈5.05 at equal density — and for ζ it
creeps only 3.41→3.48 over d=2→50; see "Empirical refinements" below. RH stays in the sign, not the rate.)* So the no-margin *rate* is generic to any reciprocal-squared hard-edge
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

**The margin is an inverse Christoffel function `[DERIVED + verified to 6 digits]`.** The moment matrix of the zero
measure `ν'=Σ_ρ 2y_ρ δ_{y_ρ}` is exactly `H_d^0` (`∫y^{i+j}dν'=T_{i+j+1}`), so its degree-`d` reproducing
(Christoffel–Darboux) kernel at a point is `K_{ν'}(y_*,y_*) = e(y_*)ᵀ(H_d^0)^{−1}e(y_*) = max_p p(y_*)²/Q_0[p]`,
`e(y_*)=(y_*^i)`. The single-point protector then gives the exact identity (verified):
`1/margin = (2.5)^{−2}·K_{ν'}(−0.16,−0.16)` (`=1.27007·10^{51}` both ways at `d=10`), with the trivial-zero sum
`Σ_j(2j+½)^{−2}K_{ν'}(y_j,y_j)` dominated by `j=1` (the profile drops `~10` orders per `j`). So the bridge margin
**is** the inverse Christoffel function of the zero measure, evaluated at the coarsest trivial zero `y=−0.16`, a
point **exterior** to `supp(ν')=(0,y_1]`. Two consequences: (i) the *sign* — `K_{ν'}(y_*,y_*)=e^ᵀ(H^0)^{−1}e ≥ 0 ⟺
H^0⪰0 ⟺ ν'` a positive measure `⟺` zeros real — is RH (a Christoffel/reproducing kernel is positive iff its measure
is). (ii) the *growth* of `K_{ν'}(−0.16,−0.16)` is **not** a clean endpoint Green's function: because the atoms
accumulate at the hard edge `0`, the exterior growth is faster than `e^{2d·g}` and **tracks the zero density**
`[verified]` — `K^{1/(2d)}` does not converge and differs between `ζ` and a same-support linear-density divisor
(rate ratio `0.60→0.21` over `d=2..14`), matching the synthetic-density spread of the per-step exponent (Arc Q).
So the Christoffel form re-confirms density-tracking growth (generic band, not a fixed constant) and isolates the RH
content cleanly in the **sign** of the kernel — `K_{ν'}>0 ⟺` zeros real. *Caveat `[verified]`:* the sign that matters
is the sign of the *form* `H^0`, not of `K_{ν'}(y,y)` as a function on `ℝ`. The real-axis kernel `K(y)=e(y)ᵀ(H^0)^{−1}
e(y)` stays **positive for all real `y`** even with an injected off-line zero (`d>d*`, `H^0` indefinite): the flipped
eigenvalue (`~10^{−21}`) contributes `~10^{21}` at the aligned point `y=−0.16` against positive terms `~10^{51}`, so
the defect is sub-threshold on the moment curve `{e(y)}`. The off-line negativity lives in a polynomial-*eigenvector*
direction off that curve. So `K(y)>0 ∀y∈ℝ` is **necessary but not sufficient** — the faithful detector is the single
flipped generalized eigenvalue, not the real-axis kernel.

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

**The irreducible in one line, and the three-stratum divisor it lives on `[SYNTHESIS — gpt/37]`.** Strip the
scaffolding and the missing theorem is a single statement: **the completed explicit formula is a one-sided
Loewner domination theorem.** The carrier is found, the coordinate is found, the pole direction `u=(−4)^i` is
found, the archimedean budget `M_triv` is found; the one open piece is the *exact source-built domination of
the prime residual by the trivial-zero budget*, `−R^P ⪯ M_triv` — equivalently
`λ_max(K_d) ≤ 1 ∀d`, `K_d = M_triv^{−1/2}(−R^P)M_triv^{−1/2}` (one-sided: the prime may overshoot `M_triv` on
the positive side; only the negative directions count). The sharpening this forces on the *form* of the
proof: it is **not** "find some positivity" but "**source-build a factorization or contraction** giving
`I − K_d ⪰ 0` with **zero margin**" — the old outer-function / square-root / `g`-construction demand, now
pinned to a contraction with no slack to spend (the prime saturates the budget to `~24` digits on the worst
residual direction, so any route needing a fixed spectral gap or domination reserve is the wrong shape).

The object this lives on is a **three-stratum reciprocal boundary divisor**: the **pole** atom at `y=−4` (the
`s=0,1` entireness direction `u`), the **trivial-zero chain** `y_j=−(2j+½)^{−2}` (the explicit *positive*
protector `μ_triv`, tightly clustered in `(−0.16,0)`), and the **nontrivial zero divisor** `y_ρ=−(ρ−½)^{−2}`
(the stratum to be forced onto `ℝ_{>0}`). In this chart RH is not "zeros on the line" directly — it is "**the
completed reciprocal divisor is a positive Stieltjes divisor once the pole boundary is absorbed**." This
splits two divisors the analysis had been conflating: the **RH divisor** is the Stieltjes positivity of the
folded *nontrivial* divisor; the **proof divisor** is the archimedean *trivial-zero* divisor acting as a
boundary protector. *(Falsifiable `[OPEN — computation #36]`:* on the dangerous mode the protector mass
collapses to the single coarsest trivial zero `y=−0.16`; if that `j=1` collapse spreads across many trivial
zeros at higher `d`, the exterior-Christoffel single-boundary-evaluation route weakens and the proof needs the
*whole* trivial-zero measure.) Speculatively the hidden object is **relative** —
`𝒟_rel = 𝒟_nontriv ⊘ 𝒟_triv ⊘ 𝒟_pole`, presented not as a literal signed divisor but as a spectral-shift /
Schur-complement object whose finite shadows are exactly `M_triv + R^P` (= the operator face's
`−C^{−1} − V*B^{−1}V`, §5).

**The ranked proof-shape menu `[STRATEGIC — gpt/37]`.** Among the source-built routes for the residual
inequality, ordered by current odds:
1. **One-sided Loewner / boundary-Weyl domination** — identify `K_d` as the compression `P_d K P_d^*` of a
   single completed-boundary operator `K` built from the explicit formula, and prove `K ⪯ I` by operator
   monotonicity. The corner-concentration of `K_d` (entries blow up at the deepest index) says `K` is **not
   compact**, so `λ_max→1` is essential-spectrum-like — an operator inequality, not a finite eigenvalue bound.
2. **Weil-form pullback** `p ↦ h_p` — construct an explicit-formula test function with `Q_0[p]=Q_W[h_p]`, then
   read positivity off the completed explicit formula. A forced *negative* boundary term would make the
   boundary-Weyl formulation mandatory (or push the proof into a limiting de Branges/Krein space).
3. **Discriminant / Gram–Heine asymptotics** — the tuple-sum `det H_d` with off-line negativity only from
   conjugate-pair tuples; viable only after the exact cross-positive interval is combined with a summed
   finite-`d` domination theorem and a uniform degree-to-height mechanism. Fixed finite degrees are explicitly
   height-limited (`finite-degree-reciprocal-tests-height-limited.md`).
4. **Direct Jacobi / Hankel-determinant** — lowest odds: the raw recurrence coordinate is intrinsically
   hard-edge ill-conditioned (above) and not proof-shaped.

**What the forward computations must decide (route-killers, not more evidence) `[AGENDA — gpt/37]`.** The
load-bearing experiments are listed in `research-topics.md` (#35–44); the five that move first are the
high-degree `K_d` spectral law (does `λ_max→1` with no compactness, fixing route 1?), the **Dirichlet/DH
generalization** (does every genuine Euler-product completed `L` pass `K_d⪯I` while Davenport–Heilbronn fails
by `λ_max>1`? — this would turn the bridge from "beautiful coordinate" into a real **source gate**), the
Weil-pullback construction, the coarsest-trivial-zero protector test, and the detection law `d*(γ,β)`. The
decisive fork: if `M_triv ⪰ −R^P` holds for *broad hard-edge fake divisors with no prime structure*, the
domination is generic and the next theorem to find is **why the explicit formula places `ζ` in that
domination class**; if instead genuine `L`-functions pass and DH fails sharply, the domination *is* the source
gate, and the target is the contraction `K ⪯ I` itself.

**Empirical refinements `[2026-06-22 computation battery — gpt/37 agenda #35–44, exact ζ/L moments]`.** A
high-precision run of the whole agenda (`logs/gpt37-computations-worklog.md`) sharpened, corrected, and
extended this section:
- **Margin exponent `[CORRECTED + REFINED]`.** With *exact* ζ moments `T_k=2Σγ^{−2k}` (from `c_{2k}=[w^{2k}]
  logΞ`, no zero-truncation — an 80-zero truncation alone corrupts `T_1` by **15%**), the per-degree exponent
  in `margin(d)/margin(d−1)≈γ_d^{−e_d}` is **≈3.41 (d≤29) rising glacially to ≈3.48 (d≤50)** — *stable,
  logarithmically slow*, **not** the spurious drift to 3.7 that a truncated `T_1` manufactures. Across the
  **completed-`L` family** the exponent is **protector/parity-locked, not a universal density constant**:
  ζ ≈3.41, odd-`χ` (a=1) ≈3.90, even-`χ` (a=0) ≈5.05 — same zero density, different archimedean protector
  `b=(a+½)/2`, different rate. So the no-margin *rate* is set by the **archimedean protector's hard-edge
  geometry**, refining "density-determined, →4 universal." (RH stays purely in the **sign**.)
- **The numerics carry zero RH/prime content `[VERIFIED — current form]`.** ζ-actual and **jittered-ζ** (zero
  positions kept, *correlations destroyed*) give an identical margin law to **4–5 digits** (overlap
  0.97157≈0.97156); it is a **pure functional of the density profile**. The prime/correlation structure — the
  actual RH content — is invisible to every margin / conditioning / overlap observable here.
- **`λ_max(K_d)→1` with no compactness `[VERIFIED to d=50]`.** Margin `>0` but `~(d!)^{−3.5}`; corner
  concentration `K_dd/K_00 ~ margin^{−0.38}` (1.4·10^{125} at d=50). Confirms `K` non-compact ⟹ the
  essential-spectrum / boundary-Weyl route (ranked route 1).
- **Dangerous direction = the pole vector, universally `[VERIFIED]`.** Overlap with `u=(−4)^i` is **0.972 (ζ,
  stable to d=50)** and **0.97–0.99 for every Dirichlet `L`** — *including odd-`χ` where `y=−4` is not in the
  protector support at all*. So `u` is a **geometric exterior-point feature** of the hard-edge moment problem,
  not the arithmetic pole.
- **Protector collapses to one point, to high `d` `[VERIFIED to d=50]`.** On the dangerous mode the protector
  mass is **100% at `j=1` (the coarsest trivial zero `y=−0.16`)** at every `d=10..50`; the
  exterior-Christoffel single-boundary route is robust, not low-degree numerology. The identity
  `1/margin = (2.5)^{−2}·K_{ν'}(−0.16,−0.16)` is verified to **rel 1.7·10^{−21} at d=20**.
- **`R^P` is rank-1 in norm, full-rank in sign `[VERIFIED]`.** Eigenvalue *magnitudes* decay
  super-exponentially (dominant `−0.2565`, then `10^{−3},10^{−7.5},…`) — energetically rank-1 — while the
  *inertia* stays high-rank ((2,5)/(2,7)/(3,8) at d=6/8/10). The RH-bearing positivity lives in the
  **exponentially-suppressed mixed-sign tail**, which any low-rank / deflation approximation discards — *why*
  deflation cannot help. `R^P` is **near-tridiagonal (99.994% of its energy banded) in the protector-point
  `(y+0.16)^i` basis** — a concrete lead for the operator route.
- **Detection law `[REFINED]`.** `d*(γ,δ)` is **mildly super-linear** (`d*/γ` rises 0.36→0.55 over γ=20→60,
  α≈1.2–1.3), with a **weak, height-fading** off-line-distance dependence — refining the linear `d*~γ0/3`.
- **The `L`-function source gate is all-order, not finite-`d` `[VERIFIED — route-refiner]`.** The bridge
  structure **reproduces for every genuine completed `L`** (Euler-product-family general). But the *real*
  Davenport–Heilbronn counterexample (first off-line zero `γ=85.7, σ=0.808`; faithful even completion
  validated to `10^{−360}`, `|f(0.808517+85.699348 i)|=6.5·10^{−7}`) is **not detected by `K_d` through
  d=55** — its reciprocal atom has `Im(y)≈10^{−6}` buried at the hard edge, and `d*(85.7,0.31)≈55` (matching
  the detection law). So the reciprocal trivial-zero domination is faithful but height-limited: it does **not
  finitely separate DH from a genuine `L`**. The "source gate" is the **same all-order wall** in `L`-function
  clothes — corroborating "the certificate is irreducibly all-order; the proof must be analytic, not a
  finite-`d` sweep."
- **Weil-pullback is inadmissible; the missing boundary is at the seam centre `[VERIFIED]`.** The pullback
  test function `h_p(t)=(1/t²)p(1/t²)²=Σ_m b_m t^{−2m}` has a pole of order `2(2d+1)` at `t=0 ⟺ s=½` (the seam
  **centre**, `y=∞`) — **not** a classical Weil test function; the pullback exists only per-moment via the
  explicit-formula closed form `S_m`, so a de Branges/Krein limiting framework is required and its boundary
  acts at **`s=½`** (not the pole `y=−4`). (Cross-check: `PRIME_k` from `(ζ'/ζ)^{(2k−1)}(½)=(2k)!g_{2k}`
  matches `(−1)^kT_k−(POLE+ZETA+BETA)_k` to `10^{−141}`, independently validating the moments and the split.)

**Purification — the missing object is now a completed operator/form obligation `[SYNTHESIS — gpt/38]`.** The battery's net
effect is a *purification*: every finite-`d`, conditioning, margin, correlation, and rate observable is demoted
(prime-blind, density/protector-set, generic), leaving exactly one RH-bearing object — the **all-order sign**.
The bridge is no longer "find the source gate" or "detect Euler structure in finite `K_d`"; it is precisely
> **construct the completed boundary operator `K`, or its closed form replacement, and prove the contraction/sign theorem.**
Concretely: *the completed explicit formula is expected to produce a **noncompact self-adjoint contraction**
`K = M_triv^{−1/2}(−R^P)M_triv^{−1/2}` whose finite sections are the `K_d` (`K_d = P_d K P_d^*`), with `K ⪯ I`,
`1 ∈ σ_ess(K)`, built **without zero-feeding**.* comp7 (`λ_max→1`, no compactness, no slack) forces this: the
proof must be **boundary monotonicity / Weyl positivity**, never an eigenvalue / spectral-gap estimate
(`λ_max ≤ 1−ε` is impossible). `relative-contraction-compression-exhaustion.md` makes the operator burden exact:
finite compressions are equivalent to `K⪯I` only after a bounded self-adjoint source operator, or the correct closed
form replacement, has been constructed on the `M_triv` completion. `one-sided-compression-bound-not-bounded-operator.md`
adds the domain warning: a one-sided upper form bound on polynomials is not a bounded contraction unless a lower
bound, boundedness theorem, or closed-form construction is supplied. RH `⟺ λ_min(I−K_d) > 0 ∀d` — the sign, not
the rate.

**The proof divisor is a four-point *compactified reciprocal-boundary* divisor `[SYNTHESIS — gpt/38, revises the
three-stratum].`** The nontrivial zero divisor `y_ρ=−(ρ−½)^{−2}` is the **object being controlled**, not the
proof divisor. The proof divisor is the **boundary**:
```
   y = ∞   ⟷  seam centre s=½         (where the Weil-pullback breaks: the de Branges/Krein boundary)
   y = −4  ⟷  pole / entireness        (Part A, closed/automatic)
   y = −0.16 = −(2.5)^{−2} ⟷ first trivial-zero protector  (the exterior Christoffel point)
   y = 0⁺  ⟷  hard edge                (where the nontrivial atoms accumulate; where the zero margin is born)
```
The strange cross-scale content, isolated: **the first trivial zero `−0.16` controls the entire deep hard edge
`0⁺`** — `1/margin = (2.5)^{−2} K_{ν'}(−0.16,−0.16)`, an inverse exterior Christoffel function at a single point
**outside** `supp(ν')`. (Not prime correlations, not GUE, not density, not finite `d`.)

**Proof shape, updated `[STRATEGIC — gpt/38]`.** (A) arch split closed (pole rank-one + trivial-zero square).
(B) normalize to the noncompact contraction `K_d ⪯ I`; the limit `K ⪯ I`, `‖K‖=1` is the theorem. (C) the
natural operator coordinate is the **protector-point shift `x = y + 0.16`** (comp14: `R^P` 99.994% tridiagonal
there) — but the proof needs the *exact near-Jacobi core PLUS the sign-preserving tail* (comp16: a band
approximation reproduces the rate and **loses RH**). (D) regularize the Weil pullback by **promoting its
seam-centre pole to a boundary vector at `s=½`** (de Branges/Krein), not removing it; the experimental identity
to chase is `finite-part Q_W[h_p^reg] = I − K_d`. (E) prove **sign, not rate** (`λ_min(I−K_d)>0 ∀d`).

**Updated slogan.** Old: "the prime residual is trying to eat the trivial-zero budget." New:
> *The first trivial zero supplies an exterior boundary evaluation whose inverse Christoffel function controls
> the hard-edge reciprocal zero measure; RH is the all-order positivity of that **noncompact boundary-Weyl
> contraction** — `1/(1−λ_max(K_d)) = (2.5)^{−2}K_{ν'}(−0.16,−0.16)` (the finite Christoffel face) and `K ⪯ I`
> (the proof theorem). Not a source gate — a **source-built all-order sign transfer**.*

**Operator-identity battery `[2026-06-22 gpt/38 agenda #45–52; logs/gpt37-computations-worklog.md]`.** Running the
agenda turned the boundary-Weyl picture from conjecture into measured structure:
- **The boundary-Weyl theorem is RANK-ONE `[VERIFIED d=8,12,16]`.** `H^0 = H0_minus + (2.5)^{−2} v v^T`,
  `v=e(−0.16)`, and `H0_minus` has inertia **`(d,1)`** — exactly one defect. RH positivity of `H^0` reduces to a
  **scalar** boundary condition `s(d)=(2.5)^{−2}+1/(v^T H0_minus^{−1}v) ≥ 0`, with `s(d)=(2.5)^{−2}·margin → 0⁺`.
  The completed-boundary Weyl PSD theorem is a **single Weyl function at one exterior point** — operator face =
  moment face = scalar boundary face.
- **The first trivial zero is the critical/optimal boundary datum `[VERIFIED]`.** The critical mass
  `a_c(−0.16)=0.16` **exactly** (deficit `=0.16·margin`), and `y_*=−0.16` **minimizes** `a_c(y_*)` over the whole
  exterior axis — the canonical datum `(y=−0.16, mass (2.5)^{−2})` is the cheapest exterior control point and is
  exactly critical at every degree (explains comp10's collapse-to-`j=1` structurally).
- **Sign-exact, never approximate `[VERIFIED]`.** In the protector coordinate `R^P = J + E` with `J` a
  geometrically-decaying Jacobi matrix (`99.992%` of the norm) — but dropping the `0.8%` tail `E` flips
  `margin: +10^{−40}→−10^{16}` (comp45), and **every** rank-`r<d+1` spectral truncation gives the **wrong sign**
  (comp50). Both band and low-rank routes are **formally dead**; the proof must be sign-exact over the full
  operator, exactly as a noncompact boundary-Weyl theorem requires.
- **The no-margin exponent is a clean archimedean law `[DERIVED]`.** Sweeping a synthetic protector with coarsest
  atom `y_*`, the rate is `α ≈ 4.31 + ½·ln|y_*|` (fits ζ/odd-χ/even-χ at `y_*=−0.16/−0.444/−4` to 3 digits) — set
  entirely by the Γ-factor's coarsest trivial-zero image, slope `½` from the reciprocal square. No universal `4`;
  `α` spans `2.8→5+`. The rate is archimedean-general; only the sign is RH.
- **Discriminant schema reusable `[VERIFIED]`.** The Gram–Heine tuple identity holds at `d=3,4` (every `det H_d` a
  manifestly-positive tuple-sum on RH); `det H_4 > 0` unconditional for off-line height `γ≥16` (ladder: `d=2` all,
  `d=3,4` for `γ≥16`).

So the proof target is now concrete: **a source-built rank-one boundary-Weyl contraction** — build the bulk
`H0_minus` (inertia `(d,1)`) and the single boundary atom `(y=−0.16, mass (2.5)^{−2})` from Γ/pole/FE/explicit-
formula data *without zero-feeding*, in the protector coordinate `x=y+0.16`, and prove the scalar Weyl function
`s(d) ≥ 0 ∀d` (`= (2.5)^{−2}·margin`) while keeping the exact sign-carrying tail.

**The collapse to a rank-one SCALAR boundary-Weyl theorem `[SYNTHESIS — gpt/39]`.** The battery collapses the
bridge one more level: from "prove a noncompact boundary-Weyl *operator* inequality" to "**prove a rank-one
*scalar* boundary-Weyl inequality at `y=−0.16`**." The bulk may stay infinite-dimensional and noncompact, but
the **boundary decision is scalar**. The residual wall reorganizes as `H^0_d = H^-_d + a_* v_* v_*^T` with
`inertia(H^-_d)=(d,1)` (one negative bulk square), `v_*=(1,y_*,y_*^2,…)`, `y_*=−0.16`, `a_*=(2.5)^{−2}=0.16`,
and the entire RH content is the **scalar Weyl gap** `s_d = a_*·margin_d > 0 ∀d` (`→0⁺`) — i.e. the
first-trivial-zero boundary atom must stay just above the rank-one Weyl threshold `a_c(d;y_*)` at every degree
(`a_* − a_c(d;y_*) = a_*·margin_d`). **The proof divisor reduces to the single rank-one exterior datum**
`a_*δ_{y_*} = 0.16·δ_{−0.16}`: of the four compactification landmarks (seam centre `y=∞`, pole `y=−4`, first
trivial zero `y=−0.16`, hard edge `y=0⁺`), the pole is automatic Part-A bookkeeping and the rest of the trivial
chain is background — **`j=1` is the active rank-one gate**. The first trivial zero is no longer "a protector";
it is the **critical Weyl boundary condition** for the whole reciprocal hard edge.

> **The "one theorem before RH", rank-one form (gpt/39).** *In the reciprocal seam-squared coordinate, the
> completed explicit formula splits the shifted zero-moment form into a bulk `H^-_d` with exactly one negative
> square plus the canonical first-trivial-zero boundary atom `0.16·v_{−0.16}v_{−0.16}^T`; the scalar Weyl gap
> `s_d = 0.16·margin_d` is positive for every `d`; hence `H^0_d ⪰ 0 ∀d`, hence `Q_0[p]≥0 ∀p`, hence the folded
> reciprocal zero divisor lies on `ℝ_{>0}`, hence RH.* Slogan: **RH is the all-degree positivity of the scalar
> Weyl gap created by the first trivial zero.** The two open faces: (i) **source-build** the bulk `H^-_d` and the
> boundary `m`-function at `y=−0.16` from Γ/pole/FE/EF without zero-feeding; (ii) identify the seam-centre
> (`s=½`) de Branges/Krein regularization of the Weil pullback as exactly this rank-one boundary condition
> (the route-2↔route-1 weld). Supporting geometry — Jacobi banding, low-rank norm, the `α=4.31+½ln|y_*|` rate,
> finite Gram–Heine — is NOT the central theorem.

**Scalar Weyl m-function battery `[2026-06-22 gpt/39 agenda #53–56; logs/gpt37-computations-worklog.md]`.** The
agenda identified the scalar Weyl object and proved the two faces are one number:
- **The rank-one Schur gap = the inverse exterior Christoffel kernel `[PROVED — Sherman–Morrison; verified to
  10^{−103}]`.** With `H^0_d = H^-_d + a_* v_* v_*^T` (`v_*=e(−0.16)`, `a_*=0.16`, `inertia(H^-_d)=(d,1)`), put
  `m=v_*^T(H^-_d)^{−1}v_*`; Sherman–Morrison gives `v_*^T(H^0_d)^{−1}v_* = m/(1+a_*m)`, so **exactly**
  > `s_d = a_* + 1/m` (rank-one Schur) `= 1/(v_*^T(H^0_d)^{−1}v_*) = 1/K_{ν'}(−0.16,−0.16)` (inverse exterior
  > Christoffel),  and in the RH/PSD regime `= (2.5)^{−2}·margin_d` (comp52).
  The **moment face** (`K_{ν'}=e^T(H^0)^{−1}e`, the reproducing kernel of the zero measure `ν'`) and the
  **operator face** (the rank-one Schur gap) are thus one object. RH `⟺ s_d = a_*·margin_d > 0 ∀d` (the
  generalized-eigenvalue margin is the faithful detector; the Christoffel identity gives the source-facing form).
- **The rank-one boundary theorem is completed-Euler-product-general `[VERIFIED d=8,12; complex self-dual comp75]`.**
  For every real primitive Dirichlet `L` (and ζ), removing the single coarsest trivial-zero atom (`y_{*,χ}=−(a+½)^{−2}`,
  `a_{*,χ}=|y_{*,χ}|`; even-χ `−4`, odd-χ `−4/9`, ζ `−0.16`) leaves `inertia(H^-_χ)=(d,1)`, and
  `s_{χ,d}=1/K_{ν'_χ}(y_{*,χ})=a_{*,χ}·margin_χ`. **The Γ-factor selects the boundary datum** — the same `y_{*,χ}`
  that sets the exponent law `α=4.31+½ln|y_*|` — so the bridge is a uniform feature of the completed-`L` family.
  comp75 extends this to a **complex self-dual product** `Λ(s,χ)Λ(s,χ̄)` (χ mod 5, order 4): still `N₁`, `inertia(H^-)=(d,1)`,
  `s_d>0` — the squared Γ stays **rank-one** because χ,χ̄ share one parity/Γ-channel. The rank equals the number of
  **distinct Γ-shift values**; a genuine two-channel object (e.g. GL(2) `Γ_ℝ(s)Γ_ℝ(s+1)`) would give rank-two/`N₂`.
- **The sign-essential tail is a Hankel functional `[VERIFIED]`.** In the protector coordinate `R^P = J + E`
  (`J` the decaying Jacobi core, comp45), `E` is **exactly Hankel** (`E_{ij}=f(i+j)`, deviation `~10^{−175}`) — the
  finite-section moment matrix of a single signed functional `μ_E`. `μ_E` is now **identified** (`E=μ_E`, gpt/proof8)
  and **demoted to anatomy** (gpt/43): it is the seam Hankel *shadow* of the Krein signed measure `σ=ν'−a_*δ_{y_*}`,
  not the fake-family gate (DH shares it, comp69). See the Krein–Langer current-sharp-form block in §5b.
- **`y=−0.16` is not a smooth critical point `[VERIFIED]`.** `∂_y a_c(d;−0.16) ≈ 2d` (linear in `d`, not 0); the
  comp48 minimality is a valid-window edge effect. So the analytic entrance is the inverse-Christoffel identity
  above, not a stationarity condition.

So the proof object narrows to a **single scalar Weyl `m`-function — the inverse exterior Christoffel kernel
`1/K_{ν'}(y_{*,χ})` at the Γ-selected first trivial zero** — whose positivity at every degree is RH. The open
faces: source-build `K_{ν'}(y_{*,χ})` (equivalently the bulk `H^-` plus the Hankel tail `μ_E`) from
Γ/pole/FE/explicit-formula data without zero-feeding, and weld the seam-centre Weil-pullback regularization to it.

- **The boundary is source-built; the defect is prime-sourced `[VERIFIED]`.** The boundary atom `a_*v_*v_*^T` is
  **exactly the `j=1` term** of the archimedean square-sum `Q_arch=−4p(−4)²+Σ_{j≥1}(2j+½)^{−2}p(y_j)²` (rel `0`)
  — so the boundary is built from the **Γ-factor (first trivial zero), no zero-feeding**. The bulk splits as
  `H^- = M_triv^{(j≥2)} + R^P` with `M_triv^{(j≥2)} ≻ 0` (the `j≥2` trivial budget) and `R^P` the prime residual;
  adding `R^P` creates **exactly one** negative direction (`inertia(H^-)=(d,1)`). So: *boundary = archimedean
  `j=1` trivial zero (source-built); defect = prime residual; RH = the `j=1` atom repairs that prime-sourced
  defect at all `d`* (`s_d>0`). Only the repair's **success** needs the zeros — that is RH. (This is the
  computable half of the Weil-pullback weld; the de Branges/Krein seam-centre construction realizing
  `FP_{s=½}Q_W[h_p] → H^- + a_*v_*v_*^T` remains paper-math, now with a source-identified target.)
- **Even fake-family failure speaks the boundary language `[VERIFIED — DH, d*=62]`.** The real
  Davenport–Heilbronn off-line zero (`γ=85.7`) is caught at `d*=62`: the scalar gap `s_d=a_*·margin` stays
  positive through `d=61` then **flips negative at `d=62`**, while `inertia(H^-)=(d,1)` **persists throughout**.
  DH fails by the **boundary atom becoming insufficient** (`a_*<a_c`, `s_d<0`), not by a second bulk defect — the
  exact rank-one Weyl-threshold crossing. (Build via a batched Hurwitz–Taylor routine, `2026-06-22-hurwitz-batch.py`,
  all `M` coefficients in one Euler–Maclaurin sweep — removes the L-function moment-build bottleneck.)

**The exponent law DERIVED, and the four-piece proof shape `[gpt/proof4 + gpt/41]`.**
- **The parity exponent is derived, not fitted `[DERIVED]`.** The empirical `α≈4.31+½ln|y_*|` (comp49) is the
  `L̄_d≈4` specialization of the exterior-Christoffel asymptotic
  > `α_d(y_*) ≈ 4 + [4(1−ln2) + 2ln|y_*|] / L̄_d`,  `L̄_d = (1/d)Σ_{j≤d} ln γ_j`,
  with three explicit origins: **base 4** = the reciprocal-square weight (`x_j=γ_j^{−2} ⟹ x_j²=γ_j^{−4}`);
  **`4(1−ln2)≈1.227`** = the hard-edge Vandermonde/spacing correction (`2∫_0^1 log(1−t²)dt = −4(1−ln2)`, via the
  quantile `x_{d+1}/x_j≈(j/(d+1))²`); **`2ln|y_*|`** = the exterior-Christoffel normalization (`p(−a)=1 ⟹
  ∏(a+x_j)^{−2}~a^{−2d}`). Checks: ζ `3.391`, odd-χ `3.901`, even-χ `5.000` (obs `3.41/3.90/5.05`). *Caveat:* the
  slope `½` is `2/L̄_d` at the tested `L̄_d≈4`; since `L̄_d` grows with `d`, the slope **drifts downward** at
  astronomically large `d` — there is **no universal ½**, confirming "the rate is generic hard-edge geometry, the
  sign is RH."
- **The four-piece proof shape `[gpt/41]`.** **(A)** the reciprocal chart, target `Q_0[p]≥0 ∀p`. **(B)** the **Γ
  boundary split** `H^0_d = H^-_d + a_*v_*v_*^T` with `a_*v_*v_*^T` the first Γ-trivial-zero atom (source-built,
  comp57). **(C)** the **one-defect bulk theorem** `inertia(H^-_d)=(d,1) ∀d` (verified ζ, real `L`, and DH through
  the crossing — "removing the first Γ-boundary atom leaves exactly one negative square"). **(D)** the **scalar
  Weyl gap theorem** `s_d = a_*+1/m_d = 1/K_{ν'}(y_*) = a_*·margin_d > 0 ∀d` (`m_d=v_*^T(H^-_d)^{−1}v_*`). The new
  reduction (given C): **`Q_0[p]≥0 ∀p ⟺ s_d>0 ∀d`** — the *Rank-one Γ-boundary Weyl Bridge*.
- **The fake-family gate is the integer `κ₋`; `s_d=0` is its rank-one shadow `[VERIFIED — DH at d=62; refined comp81]`.**
  A valid source-built object must separate DH-style fakes at a *named structural gate*. For DH (a real off-line zero)
  `κ₋(H^-)` stays `1` and the scalar `s_d` crosses `0` at `d=62` (height-limited detection). But comp81 shows a
  *global* sign-fake (prime sign reversed) jumps to `κ₋=2` **with `s_d>0`** — the rank-one Γ-atom repairs only one of
  the two negative squares, so `H^0` is not PSD while the scalar `s_d` is blind to it. **The faithful separator is the
  integer `κ₋` (= 2·#off-line pairs; lens 4, comp72); `s_d=0` is its height-limited scalar shadow** — watch the index,
  not the scalar.
- **The `μ_E` identification — done, then demoted `[gpt/proof8, gpt/43]`.** The chain `regularized Weil pullback ⟹
  seam-centre finite part ⟹ E_{ij}=f(i+j) ⟹ H^-_d=J+E+(Γ/pole pieces)` is now constructed (proof7) and the tail
  identified (`E=μ_E`, proof8). gpt/43 then *demotes* `μ_E` from "the missing theorem" to **anatomy** — the seam
  Hankel shadow of `σ=ν'−a_*δ_{y_*}`, not the fake-family gate (the gate is `s_d=0` alone; DH shares the tail). The
  live theorem is the scalar sign `s_d>0`, not the tail identity. (See the Krein–Langer current-sharp-form block below.)

So the conjectured rank-one form of the bridge is the **Rank-one Gamma-boundary Weyl Bridge**: *Gamma supplies the
boundary atom; the primes create the bulk defect; the bridge assertion is that the Gamma atom repairs it at every
degree* (`s_d>0 ∀d`). Current evidence locates the scalar and its fake-family behavior; the open content is still
the all-level proof of `s_d>0`, via the seam-centre finite-part identity or an equivalent source construction.

**The seam finite-part construction — built, and the tail identified `[gpt/proof5–8]`.** The Weil-pullback route is
now a constructed regulator/finite-part lemma; the open content has narrowed to the scalar positivity alone.
- **Lemma 1 — seam-residue identity `[VERIFIED — comp60]`.** With `h_p(w)=−w^{−2}p(−w^{−2})²` (`= y·p(y)²`) and
  `M_Ξ(w):=(1/2w)·Ξ'(w)/Ξ(w) = Σ_{k≥0}(−1)^k (T_{k+1}/2)\,w^{2k}` (completed log-derivative generates the reciprocal
  moments; coefficient `(−1)^k T_{k+1}/2` in the folded convention `T_k=2Σγ^{−2k}`), the bridge form is a single
  residue at the seam centre `w=0`: `Q_0[p] = −Res_{w=0}[h_p·(Ξ'/Ξ)]`. Splitting `Ξ'/Ξ=A+P` gives `Q_0=Q_A+Q_P`,
  `Q_A` the closed archimedean rank-one form `−4p(−4)²+Σ_{j≥1}a_jp(y_j)²`; extracting the `j=1` atom yields the
  rank-one split `H^0_d=H^-_d+a_*v_*v_*^T` — all source-side.
- **The canonical finite part exists and is regulator-independent `[gpt/proof7]`.** Admissible even approximants
  `h_{p,q}^{ε,R}(t)=t^{−2}p(t^{−2})q(t^{−2})·η(t/ε)·ψ(t/R)` (smooth, compactly supported, zero near `t=0`) give the
  Hadamard expansion `Q_W[h^{ε,R}]=Σ_m A_m ε^{−m}+B·logε+C_R+o(1)` with **only odd powers** `m∈{1,…,4d+1}` and
  **`B=0` by evenness** (no log divergence in the canonical symmetric scheme). The finite part
  `𝔉[p,q]=FP_{ε=0,R=∞}Q_W`: (i) has an `R→∞` limit (zero/arch tails `O(log R/R)`); (ii) is **independent of the seam
  cutoff `η`** (the only possible finite remainder needs a `u^{−1}` term, `2r−2n−2=−1`, with no integer solution for
  even jets); (iii) is **independent of the window `ψ`**; (iv) is necessarily a **Hankel** form
  `𝔉[p,q]=Σ_{ij}c_id_j 𝔣_{i+j}` (seam-local reads only Laurent `i+j` — the analytic proof of the observed
  `E_{ij}=f(i+j)`). The only freedom is a zero-free gauge `Ξ→e^{q(w²)}Ξ`, whose counterterm is now **exact** (next
  bullet). So the canonicality concern is settled: with canonical `ξ` the finite part is unique.
- **The canonical-gauge extraction lemma — proved and verified `[gpt/proof9 — PROVED; comp71 — VERIFIED; gpt/proof13
  — independently re-derived]`.** Under the zero-free even gauge `Ξ↦e^{q(w²)}Ξ`, `q(w²)=Σ_{r≥1}a_r w^{2r}`, the
  extracted reciprocal moments shift by the **exact diagonal law**
  > `T_k ↦ T_k + 2k(−1)^{k+1} a_k`  (only `a_k` moves `T_k`),
  so on the shifted tower the counterterm is the explicit Hankel `(Δ_q H^{(0)})_{ij}=2(i+j+1)(−1)^{i+j+2}a_{i+j+1}`.
  Mechanism: `T_k=2(−1)^{k+1}k·c_{2k}`, `c_{2k}=[w^{2k}]logΞ`, and `logΞ↦logΞ+q(w²)` shifts `c_{2k}↦c_{2k}+a_k`. The
  **canonical extraction** is `T_k^can = T_k^raw − 2k(−1)^{k+1}a_k`, i.e. fix `a_r≡0` = the completed Riemann
  `ξ`-normalization. comp71 confirms this at the actual `Ξ` for `k=1..6` (closed form, diagonality, Hankel
  counterterm, canonical recovery — all exact; the `T_1↦T_1+2c` of comp68 is the `k=1` case). Consequence: the
  source-extraction lemma is well-defined — **never read raw low-order Taylor coefficients without first fixing
  canonical `ξ`**; any other representative is corrected by an explicit, subtractable, diagonal counterterm.
- **The tail IS the boundary distribution — `E = μ_E` `[gpt/proof8 — proved, conditional on the source-defined `J`]`.**
  With the source-defined Green decomposition `R^P = J + 𝓑` (`J` the interior Jacobi part, `𝓑` the seam boundary
  form), the boundary moments `e_n^{fp}=FP⟨𝒲_P, φ_n⟩` (`𝒲_P` the source prime-residual distribution, **not**
  zero-fed; `φ_n(w)=−w^{−2}(−w^{−2}+a_*)^n`) give `𝓑_{ij}=e^{fp}_{i+j}`. Since `J` is Jacobi (`J_{ij}=0` for
  `|i−j|>1`) and both `E,𝓑` are Hankel, they agree on every off-tridiagonal entry, hence on all anti-diagonals
  `i+j≥2`; the `i+j=0,1` entries are pinned by the canonical `ξ`-gauge + the explicit `j=1` Γ-atom subtraction.
  Therefore the **computed Hankel tail `E` IS the seam finite-part boundary distribution `μ_E`** (projectively —
  finite sections are compressions of the infinite functional). This closes "what is `E`": source-built `μ_E`, not a
  fitted remainder. (Boundary-triple reading: the Green trace collapses to `Γ_0 F_p=p(y_*)`, Γ selecting `Θ=a_*=0.16`
  — the rank-one atom is the boundary condition of a self-adjoint extension.)

> **SOTA flag `[§10]`:** the moments `T_k=2Σγ^{−2k}` are the **Voros secondary-zeta values `Z(2k)`** (Mellin 1917;
> Voros 2010), the criterion `Q_0≥0⟺RH` is in the known Weil/Li/Csordas–Varga moment-positivity family (and is the
> Hamburger "real-support" test in disguise), and the boundary-Weyl/positivity framing overlaps the published
> canonical-system RH of **Suzuki (arXiv:1204.1827)**. Nearly all the apparatus below is classical, reassembled in the
> seam coordinate; the *only* non-reducing target is the apex `s_d>0 ∀d`. **Prolate-compression check (§5 of
> no-roleplay-items):** the archimedean protector lattice `2|w|=4N+1` IS the Connes–Consani–Moscovici prolate Hermite
> grading (`a_*` = the N=1 level); but the prolate Sonin compression is *unconditional* archimedean positivity, so only
> the budget `a_*` matches — the RH content `s_d>0` is the **semilocal** prolate (arXiv:2310.18423), not the
> archimedean one.

**The current sharp form — a Krein–Langer rank-one signed moment problem `[gpt/43, synthesizing comp63–70]`.** The
finite anatomy collapses to one clean object: `H^-_d` is the moment matrix of a **signed** measure,
> `H^-_d = M_d(σ)`, `σ = ν' − a_*δ_{y_*}`, `ν' = Σ_ρ 2y_ρ δ_{y_ρ}`, `y_ρ=−(ρ−½)^{−2}`, `y_*=−0.16`, `a_*=0.16`,
and `H^0_d = M_d(σ)+a_*v_*v_*^T = M_d(ν')`. So the boundary atom is literally the **negative atom of a signed moment
problem**: positive reciprocal zero measure *minus* one exterior Γ-boundary atom. The bridge is the transition
> `σ ∈ Π₁  ──(+a_*δ_{y_*})──▶  ν' ∈ Π₀`,
i.e. `m_σ(z)=∫dσ/(t−z) ∈ N₁` (one negative square, carried by the Γ-boundary channel) becomes `N₀`/PSD after the
canonical Γ atom is added back. This is a **boundary-Weyl theorem, not a bulk positivity estimate**: the bulk alone is
underdetermined; the finite-rank Γ extension crosses the Krein threshold.
  - **The `N₁` carrier theorem — PROVED `[gpt/proof10, conditional on the 1-dim seam quotient]`.** From three local
    inputs — the **one-dimensional seam boundary quotient** `𝒦_max/𝒦_min≅ℂ` (deficiency index one at the finite-part
    seam), the Green identity with boundary trace `Γ_0 F_p = p(y_*)`, and the Γ-selected atom `a_*|p(y_*)|²` — it
    follows that `κ₋(H^-_d)≤1` (one-dim quotient) and `=1` (the Γ defect is active, the Schur scalar is negative), so
    **`inertia(H^-_d)=(d,1)` is now an operator-domain theorem**, `m_σ∈N₁`, not just the experimental matrix pattern.
    This discharges gpt/43's feeder sub-theorem (b), modulo the one local hypothesis (the seam quotient is exactly
    one-dimensional). `[SOTA — §10: the abstract rank-one Π₁→Π₀ transition is Derkach–Hassi–de Snoo, J. Funct. Anal.
    188 (2002) 317; proof10 is the ζ-specialization, not the abstract theorem. Heed the Conrey–Li (arXiv:math/9812166)
    no-go that de Branges positivity FAILS for ξ.]` comp65/66/72 corroborate: for ζ the Pick `κ=1` is **stable** (`M≤30`, `N≤400`); an off-line
    zero raises `κ` to `2` in the *infinite* Cauchy-transform Pick kernel when sampled near `1/γ₀²` — a
    resolution-limited fake detector complementary to the height-limited finite `s_d`, the tail `μ_E` unchanged (comp69).
    comp81 makes the same point at the moment level: reversing the prime sign jumps `κ₋(H^-)` from `1` to `2` while
    `s_d` stays `>0` — **the index `κ₋` is the separator, the scalar `s_d` its rank-one shadow.**
- **`μ_E` is demoted to anatomy `[gpt/43, comp63/64/69]`.** The identified tail (`E=μ_E`, §above) is the **seam
  Hankel *shadow* of the signed measure `σ`** in the protector/Jacobi split — *not* a fourth divisor and *not* the
  fake-family gate (DH and genuine odd-`χ` share the tail, comp69; the tail is `γ_1`-dominated and not elementary,
  comp64). The gate is `s_d=0` alone.
- **The scalar apex, as a reproducing-kernel (Christoffel/Uvarov) statement.** `m_d(y)=K_{H^0}(y,y) −
  s_d·(v(y)^T(H^0)^{−1}v_*)²` (comp70 — a positive Christoffel kernel minus one ultra-thin negative dip at `y_*`,
  width `~margin→0`). The dip is **universal and parabolic** (comp74): rescaled `P(Y)=4Y²−1` to `~10^{−15}` across
  `d=8..28`, with depth pinned at `m_d(y_*)=−1/a_*=−6.25 ∀d` (the no-margin identity `a_*m_d→−1 ⟺ s_d→0`) and only
  the curvature-controlled width `w_d=2√(2|m_d(y_*)|/m_d''(y_*))~s_d^{≈0.45}` shrinking — so the whole no-margin
  geometry collapses to one `d`-scalar, the inverse-Christoffel curvature `m_d''(y_*)`. comp70 is now a **proved
  Christoffel/Uvarov boundary-removal kernel theorem `[gpt/proof11, exact ∀d; SOTA — this IS Uvarov's 1969 formula
  (USSR Comp. Math. Math. Phys. 9), Hankel form Krattenthaler arXiv:2103.03969 — a re-derivation, cite it, claim no
  novelty]`**: the kernel of `{p:p(y_*)=0}` is
  > `K^crit_d(y,z) = K_{ν',d}(y,z) − K_{ν',d}(y,y_*)K_{ν',d}(y_*,z) / K_{ν',d}(y_*,y_*)`,
  the diagonal of which is comp70's identity (a standard RKHS one-point projection — proved, not a numerical
  accident). The *actual* signed `Π₁` kernel is an **infinitesimal over-subtraction** beyond it, `K_{H^-,d}=K^crit_d
  − [s_d²/(a_*−s_d)]·K_{ν'}(·,y_*)K_{ν'}(y_*,·)` — one order smaller than the critical projector, which is why the dip
  is vanishingly thin (comp74). In the no-margin limit `K_{ν',d}(y_*,y_*)→∞`, so the literal kernel quotient is
  read via the **normalized boundary vector** `ψ_{*,d}=K_d(·,y_*)/√K_d(y_*,y_*)`: `K^crit_d=K_d^0−ψ_{*,d}ψ_{*,d}`
  persists as a rank-one direction while `s_d=1/K_d(y_*,y_*)→0⁺`. The apex is exactly `K_{ν'}(y_*,y_*)>0 ∀d`, i.e.
  **the source-built scalar Weyl positivity** `s_d = a_*+1/m_d = 1/K_{ν'}(y_*) > 0 ∀d`. `N₁` anatomy alone is *not*
  enough (DH shares it) — and **real-axis kernel positivity alone is insufficient**: an off-line defect can live in a
  polynomial-eigenvector direction off the moment curve (comp72's `κ=2`), so the Euler-product / polarization
  ingredient must enter exactly at this scalar repair sign.
  - **Determinant face `[comp80; CLASSICAL — organizational, not novel]`.** `s_d = −det(H^0_d)/det(B_d)` (`B_d`=
    `H^0_d` bordered by `v_*=(y_*^i)`, the Cramer/Uvarov border; verified to rel `~10^{−120}`), and
    `det(H^0)=det(H^-)(1+a_*m_d)` (matrix-determinant lemma). `det(H^0_d)>0 ∀d` is the Hankel-determinant (Hamburger)
    positivity of the shifted seam-moment sequence `T_k` (`= H^0` PSD `= Q_0≥0`); `det(H^-)<0` (inertia `(d,1)`), so
    `1+a_*m_d=det(H^0)/det(H^-)<0→0⁻` is the Krein threshold in determinant form (no-margin = `det(H^0)` vanishing
    relative to `det(H^-)`). These are one-line consequences of Cramer + the matrix-determinant lemma + the classical
    "Hankel PSD ⟺ Hankel-determinant positivity" / Krein–Langer apparatus — *reduces-to-known*, value is purely
    internal (places `s_d` in the classical OP/Christoffel toolkit). It is **not** the Pólya–Jensen criterion (which
    is Hankel/Turán positivity of ξ's Taylor coefficients — a different sequence); both are "RH as Hankel positivity,"
    cousins under one classical principle, not the same object.
- **The three divisors (do not conflate) `[gpt/43]`.** (1) the **RH divisor** `𝒟_RH={y_ρ}`, RH ⟺ `𝒟_RH⊂ℝ_{>0}`;
  (2) the **Γ-boundary divisor** `a_*δ_{y_*}=0.16·δ_{−0.16}` (first Γ-trivial-zero atom, the rank-one repair);
  (3) the **Krein signed divisor** `σ=ν'−a_*δ_{y_*}` — the rank-one (`N=1`) *channel shadow* `[corrected gpt/48]`. The
  **full proof divisor is the completed semilocal index carrier** (with integer index `κ₋`); `σ` is only its `N=1`
  projection, blind to negative directions off the `v_*` channel (comp81).
- **Promote rank-one Uvarov to a finite-rank boundary Weyl `[gpt/48; tested comp82]`.** The faithful object is
  matrix-valued: replace `a_*v_*v_*^T` by `VCV^*` over the **prolate `4N+1` channels** `v_N=v(y_N)`, `y_N=−(2N+½)^{−2}`
  (`N=0` pole/entireness, `N=1` the `a_*` atom, `N≥2` the protector tail), `C=diag(a_N)`; the gate is the **matrix**
  Schur complement `S_r=C^{−1}+V^*B^{−1}V`, `κ₋(S_r)=0`. The scalar `s_d` is the `r=0` (`N=1`) compression. **comp82
  result:** the `4N+1` basis is **faithful** (every fake's negative direction lies in the channel span — sign-fake →
  `N=0`, off-line zero → the channel matching its height) **but height-limited**: the channel index needed = the
  defect's height (same `d*≈γ0/3` law), so a finite-`r` truncation is *not* a finite-rank shortcut. The scalar `s_d`
  (`N=1` only) is blind to both `N=0` (pole) and `N≥3` (high-height) defects. **Scalar-shadow lemma
  `[gpt/48]`:** `s_d>0 ⟹ κ₋=0` holds *only* given `inertia(H^-)=(d,1)` **and** the negative space being rank-one
  exhausted by `v_*`; precisely `s_d>0 ∧ κ₋(v_*^⊥)=0 ⟺ κ₋=0`. comp81 is the countercase (`κ₋=2`, `s_d>0`).

So the construction (admissibility, canonical finite part, Hankel, `E=μ_E`, the rank-one scalar) is **established
anatomy / one `N=1` channel**; the live theorem is the **integer faithful index `κ₋=0 ∀d`** of the completed
**semilocal** carrier (Γ/pole/FE archimedean budget **+ finite-place correction**), of which `s_d>0` is the
height-limited rank-one shadow. The corrected name is the **Faithful semilocal Uvarov–Krein index theorem** — the
RH-bearing positivity apex (B), now stated on the index, not the scalar.

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

> **The bridge theorem is conjectured to be:** *the completion, the explicit formula, and the
> canonical archimedean boundary extension force the reciprocal seam-squared moments `T_k = Σ_ρ m_ρ
> y_ρ^k` to pass the one-power shifted square-test `Q_0[p] ≥ 0 ∀p` — which, for the actual folded zero
> divisor, alone forces the divisor onto the positive reciprocal axis (the companion `Q_1 ≥ 0` is a
> consistency passport, required only source-forgotten) — and since that positivity is itself equivalent
> to RH, the implication to the Riemann Hypothesis would be immediate.*

> **Current form (rank-one boundary-Weyl, post-2026-06-22 battery + gpt/39):** *that all-order `Q_0[p]≥0`
> reduces, at each degree, to a **single scalar inequality** — the completed explicit formula splits the
> shifted moment matrix as `H^0_d = H^-_d + 0.16·v_{−0.16}v_{−0.16}^T` with `inertia(H^-_d)=(d,1)` (one
> negative bulk square), and the canonical first-trivial-zero boundary atom repairs exactly that one defect,
> leaving the scalar Weyl gap `s_d = 0.16·margin_d > 0`. RH ⟺ that gap stays positive at every degree (it
> →0⁺). Equivalently: **RH is the all-degree positivity of the scalar Weyl gap created by the first trivial
> zero `y=−0.16`** — a source-built rank-one completed-boundary Weyl theorem.* This is the **Rank-one Γ-boundary
> Weyl Bridge** (gpt/41): *Γ supplies the exact boundary atom, the primes create exactly one bulk defect, RH says
> the Γ atom repairs it at every degree.* Its new content is the reduction **`Q_0[p]≥0 ∀p ⟺ s_d>0 ∀d`** (given the
> one-defect bulk theorem `inertia(H^-_d)=(d,1)`); the four-piece proof shape + derived exponent law are in §5b.

> **Current sharp form (Krein–Langer rank-one signed moment problem, gpt/43):** *`H^-_d` is the moment matrix of the
> **signed** measure `σ = ν' − a_*δ_{y_*}` (positive reciprocal zero measure minus one exterior Γ-boundary atom), so
> `H^0_d = M_d(σ)+a_*v_*v_*^T = M_d(ν')`. The bridge is the Krein transition `σ∈Π₁ ──(+a_*δ_{y_*})──▶ ν'∈Π₀`:
> `m_σ=∫dσ/(t−z)∈N₁` (one negative square, comp65/66) becomes `N₀`/PSD after the canonical Γ atom is added. The apex
> is the Uvarov one-point boundary-removal positivity `K_{ν'}(y_*,y_*)>0 ∀d`, i.e. `s_d=1/K_{ν'}(y_*)>0 ∀d`. The
> Hankel tail `μ_E` is the seam shadow of `σ`, anatomy — not the gate (DH shares it); the gate and fake-family
> separator is the scalar sign `s_d=0`.* This is the **positivity apex (B)**; the value/transcendence apex (A) is
> distinct and joined only at the seam (DH is the standing witness that the functional equation alone does not force RH).
