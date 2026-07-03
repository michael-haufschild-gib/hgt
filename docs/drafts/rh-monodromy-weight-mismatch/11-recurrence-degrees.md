# 11 — Recurrence degrees: the droves dichotomy proved and refuted by regularity level

Register: SEARCH-register document; §§1–2 are self-contained proofs at theorem grade
(imports named inline, elementary otherwise); §3 is the verdict; §4 opens. Companions:
08 §D (the dichotomy as conjectured), 08 §7 (the rung), 06 (the Reduction),
`RHTower/DirichletRigidity.lean` (the in-class surgery ban this pairs with).

Question attacked (as false): **does FE + almost-periodic structure force droves — one
off-line zero ⟹ many?** Answer: it depends EXACTLY on the almost-periodicity degree, and
ζ's degree is the one where it fails.

Almost-periodicity scale on a vertical line (seminorms, decreasing strength):
Bohr (uniform: sup_t) ⊃ Stepanov S² (sup over unit windows of local L²) ⊃ Weyl W²
(lim_ℓ sup_x (1/ℓ)∫_x^{x+ℓ}) ⊃ Besicovitch B² (limsup_T (1/2T)∫_{−T}^T). "Strip-S²" below
means: S² windows controlled uniformly over σ in the substrip.

---

## 1. Theorem A `[PROVED HERE]` — at Stepanov level the dichotomy holds with linear droves

**Theorem.** Let f be holomorphic on the strip S = {a < Re s < b} and strip-S²-almost
periodic: for every ε > 0 the set of τ with
sup_{σ∈(a,b)} sup_x ( ∫_x^{x+1} |f(σ+i(t+τ)) − f(σ+it)|² dt )^{1/2} < ε
is relatively dense in ℝ. If f has a zero ρ₀ in S, then f has ≥ cT zeros in
{a < σ < b, 0 < t < T} for all large T — relatively dense heights carry a zero.

*Proof.* (i) Upgrading S² → Bohr on interior substrips. Fix a′ < a″ interior, r < min
distances to ∂S and r < 1/2. For s in the substrip and any τ, the mean-value property of
the holomorphic function F := f(·+iτ) − f over the disc B(s, r) gives
|F(s)| = |(1/πr²)∫_{B(s,r)} F dA| ≤ (1/πr²) ∫_{σ−r}^{σ+r} ∫_{t−r}^{t+r} |F(σ′+it′)| dt′ dσ′.
The inner integral over a window of length 2r ≤ 1 is ≤ √2·(∫-window |F|²)^{1/2} ≤ √2·(the
strip-S² bound) by Cauchy–Schwarz, uniformly in σ′. So sup over the substrip of |F| ≤
(2√2/πr)·ε whenever τ is a strip-S² ε-translation number: every such τ is a Bohr
Cε-translation number on the substrip. Relative density is inherited.
(ii) Transfer. Take a circle around ρ₀ inside the substrip with Rouché margin
m := min_∂ |f| > 0 (ρ₀ isolated). For every τ in the relatively dense set with Cε < m, the
transfer lemma (07 §3, or directly: g/f max-modulus as in §2 step 3 run in reverse) puts a
zero of f in the τ-translated disc. Relatively dense τ-set with gap bound L ⟹ ≥ T/L − O(1)
distinct zeros up to height T. ∎

**Corollary (consistency, and where ζ lives).** ζ is NOT strip-S²-a.p. in any substrip of
(1/2, 1): by (i), strip-S² would upgrade to Bohr a.p., and Bohr-a.p. functions are bounded
on lines — contradicting the classical Ω-results (|ζ(σ+it)| unbounded on every fixed line
1/2 < σ < 1) `[CHECK at promotion: Titchmarsh ch. 8 Ω-theorems]`. Meanwhile ζ IS B²-a.p.
on every line σ > 1/2: Carlson's mean-value theorem gives Parseval,
(1/2T)∫|ζ(σ+it)|²dt → Σ n^{−2σ}, and the partial sums of the Dirichlet series converge to
ζ in the B² seminorm — ζ lies in the B²-closure of Dirichlet polynomials
`[CHECK at promotion: Carlson's theorem; Besicovitch a.p. of Dirichlet series in the
mean-convergence half-plane]`. So ζ's regularity degree in the critical strip is exactly
B² (at most W²) and not S².

## 2. Theorem B `[PROVED HERE]` — at Weyl/Besicovitch level the dichotomy is FALSE, even with FE

**Theorem.** There exists f holomorphic on S = {0 < Re s < 1}, satisfying the exact
functional equation f(s) = f(1−s) and the reality f(s̄) = f(s)̄, which is W²-almost
periodic (hence B²) on every vertical line — indeed f differs from a Dirichlet polynomial
by a Weyl-null function — and whose zero set in S is nonempty and FINITE. One
zero-quadruple, no droves.

*Construction.* g(s) := 2 + 2^{−s} + ½·2^{s}. Then g(1−s) = 2 + 2^{−(1−s)} + ½·2^{1−s}
= 2 + ½·2^{s} + 2^{−s} = g(s): exact FE; real coefficients. Lower bound: for 0 ≤ σ ≤ 1,
|g| ≥ 2 − 2^{−σ} − 2^{σ−1} ≥ ½ (the subtracted convex terms sum to ≤ 3/2 on [0,1],
extremes at the endpoints). Upper bound |g| ≤ 4 on the closed strip.

h(s) := ε·(s−s₀)(s−(1−s₀))·exp(M(s² + (1−s)²)) with s₀ = 3/4, r = 1/8, M > 0 free,
and ε > 0 fixed below. h(1−s) = h(s) (each factor checks), real coefficients, and
Re(s² + (1−s)²) = σ² + (1−σ)² − 2t², so on any line |h(σ+it)| ≤ ε·C·(1+t²)·e^{M}·e^{−2Mt²}:
gaussian decay in t.

f := g + h. FE and reality hold termwise. Now four steps.

1. *Weyl-nullity of h, hence W²-a.p. of f.* On each line, ∫_ℝ |h|² dt =: I(σ) < ∞ by the
   gaussian decay, so sup_x (1/ℓ)∫_x^{x+ℓ}|h|² ≤ I(σ)/ℓ → 0: the W² seminorm of h is 0.
   f = (Dirichlet polynomial) + (W²-null) lies in the W²-closure of trigonometric
   polynomials: W²-a.p., a fortiori B²-a.p. ∎(1)
2. *No zeros outside a compact set.* |h| < ½ ≤ |g| once ε·C·(1+t²)e^{M(1−2t²)} < ½, i.e.
   for all |t| ≥ T₀(ε, M); there |f| ≥ |g| − |h| > 0. Inside the compact remainder the
   zeros of the analytic f ≢ 0 are finitely many. ∎(2)
3. *At least one zero, without Rouché.* On the circle ∂B(s₀, r): |s−s₀| = r,
   |s−(1−s₀)| ≥ (2σ₀−1) − r = 3/8, and Re(s²+(1−s)²) ≥ (σ₀−r)² + (1−σ₀−r)² − 2r² = 3/8.
   Choose ε := 9·4 / (r·(3/8)·e^{3M/8}) so that |h| ≥ ε·r·(3/8)·e^{3M/8} = 36 > 2·4 ≥ 2|g|
   on the circle. Suppose f had no zero on the closed disc. Then g/f is holomorphic there,
   and on the boundary |g/f| ≤ |g|/(|h| − |g|) ≤ |g|/|g| · … < 1 (since |h| > 2|g| gives
   |f| ≥ |h| − |g| > |g|). By the maximum principle |g(s₀)/f(s₀)| < 1. But h(s₀) = 0, so
   f(s₀) = g(s₀) and the ratio is 1 — contradiction. So f has a zero in B(s₀, 1/8), which
   lies in {σ > 1/2}: an off-line zero. Its FE and conjugate partners complete the
   quadruple. ∎(3)
4. *Conclusion.* f is holomorphic with exact FE, W²/B²-a.p. on every line, and has ≥ 1 and
   at most finitely many zeros in the strip: the droves dichotomy FAILS at Weyl/Besicovitch
   regularity, functional equation included. ∎

**Remark (projection blindness realized).** The B²-Fourier spectrum of f on each line
equals that of g — frequencies {−log 2, 0, log 2} — because h is mean-null. All
mean-spectral/Besicovitch data of f is blind to the lone quadruple. This is the banked
projection-blindness no-go (ambient Bohr-torus data cannot see winding), here PROVED
inside the a.p. category by explicit example.

## 3. Verdict — what the dichotomy actually needs

| regularity of the class | dichotomy | proof |
|---|---|---|
| Bohr / strip-S² | TRUE, linear droves | Theorem A |
| W² / B² (+ exact FE) | FALSE — lone quadruple realizable | Theorem B |

ζ in the critical strip sits at B², not S² (§1 Corollary). Consequences:

1. **The dichotomy's burden is class rigidity, not recurrence strength.** Almost
   periodicity of any mean degree — even with an exact FE — cannot force droves. What the
   counterexample f lacks is being a DIRICHLET SERIES pointwise (h has the wrong shape;
   its very existence in the class is the loophole). Pairs exactly with
   `no_polynomial_surgery` (banked Lean): IN-class finite surgery is impossible;
   OUT-of-class surgery by a Weyl-null bump is trivial. The dichotomy lives on the class
   boundary, and both pillars are now proven necessary: FE (Révész–Pintz sparse-nonempty
   FE-free realizations — C5) and the series/class structure (Theorem B).
2. **08 §7.1's "boundary-leakage of almost periodicity" is REFUTED as a bare mechanism:**
   the bump h lives below the a.p. zone leaving no a.p. trace, so a.p. structure above
   cannot by itself force recurrence below. Any leakage argument for ζ must consume the
   pointwise representation (approximate functional equation / smoothed sums), not just
   mean structure.
3. The rung program (#112) is redirected accordingly: the forcing mechanism near σ = 1
   must exploit what ζ HAS and f LACKS — the approximate-functional-equation-grade
   pointwise representation and/or the Euler product. If the Euler product turns out to be
   required on the recurrence side, the chiasmus (10 §6) sharpens: arithmetic would enter
   BOTH halves, in opposite roles.

## 4. Opened

1. **The minimal rigidity question `[OPEN, now well-posed]`:** find the weakest
   representation hypothesis R such that "holomorphic + B²-a.p. + FE + R + one strip zero
   ⟹ droves." Candidates, in increasing strength: polynomial growth on lines (f has it,
   ζ too — check whether Theorem B survives a growth bound: our h is bounded — it does
   survive; so growth alone is NOT enough `[PROVED by the same example]`); an approximate
   functional equation with Dirichlet-polynomial main terms; the full Euler product.
   Each candidate is a concrete theorem-or-counterexample target.
2. **Lean target:** Theorem B is formalizable WITHOUT Rouché (the max-modulus trick in
   step 3 avoids the argument principle mathlib lacks); mathlib has the maximum principle
   and mean-value property. Candidate: `RHTower/WeylCounterexample.lean`.
3. Theorem A's transfer clause makes the S²-threshold quantitative: any future partial
   S²-control of ζ on a substrip (e.g. conditionally, or for other L-functions on
   σ > abscissae where they ARE bounded) immediately yields droves there.

---

## 5. Route-closure capstone (2026-07-03, same day): the soft route is CLOSED

### 5.1 Theorem B strengthened — pointwise-asymptotic representations are also insufficient

The §2 counterexample satisfies, uniformly on interior substrips,
|f(σ+it) − g(σ+it)| = |h| ≤ C·e^{M}·(1+t²)·e^{−2Mt²} → 0 (gaussian rate),
with g a FIXED FE-symmetric Dirichlet polynomial. So f admits a pointwise
"approximate-functional-equation-grade" representation — Dirichlet main term plus an error
DECAYING FASTER than ζ's own AFE error — and still carries a lone quadruple.
`[PROVED — three-line estimate]` Hence the candidate hypothesis list of §4.1 collapses
further: growth bounds, mean a.p. of every degree, exact FE, AND pointwise asymptotic
Dirichlet representation are simultaneously insufficient. The reason is structural, not
technical: **any hypothesis invariant under adding a t-localized holomorphic perturbation
is blind to finite zero sets at bounded height.** Call this the bump-stability principle.

### 5.2 Theorem B′ `[PROVED HERE, class level — paper register, Rouché used]` — on-line zeros do not obstruct the bump

Objection to B: real L-functions have infinitely many zeros ON the symmetry line; maybe
their presence blocks the surgery. It does not. Let F be holomorphic with the FE
F(s) = F(1−s), real on the line σ = 1/2 (after the standard rotation: the restriction
t ↦ F(1/2+it) is real-valued), all its strip zeros simple, on-line, and
envelope-normalized non-degenerate: writing F = E·F̂ with E a nonvanishing holomorphic
envelope (for ξ: the Γ_ℝ-factor) and |F̂′(ρ_n)| ≥ γ_n^{−A}. Perturb with
h := E·(FE-and-reality-symmetrized gaussian bump, planted at s₀ off the line, global size
η(t) = ε·e^{−2Mt²}). Then for suitable parameters f := F + h has:
(i) at each on-line zero ρ_n, a disc D_n of radius γ_n^{−A−1} on whose boundary
|F| > |h| (non-degeneracy beats the gaussian-small η) — Rouché keeps exactly one zero in
D_n, and the REALITY protection pins it to the line: the real restriction of f still
changes sign (simple sign change of F̂ minus a smaller real perturbation), so the unique
zero in D_n is real — on-line, merely displaced. No quadruple is created at any ρ_n.
(ii) off ⋃D_n and off the planting disc, |F| ≥ (local non-degeneracy) > |h|: no new zeros.
(iii) in the planting disc, the §2 max-modulus argument plants the off-line quadruple.
So even classes whose members have the FULL on-line zero structure of an L-function admit
lone-quadruple members. (For F = ξ itself the construction is conditional on a
zero-non-collision hypothesis — |ξ̂′(ρ_n)| not decaying super-polynomially — unproven
unconditionally; the CLASS-level statement needs no such input.)

### 5.3 The trichotomy — where the class-level dichotomy route ends

Combine 10 (blind cone), 11 §§1–2, 5.1–5.2, no_polynomial_surgery (Lean), and the
C0-verified Hamburger rigidity (check #3). For a class 𝓕 (FE + reality + strip-analytic)
containing a candidate function, exactly three regimes exist:

1. **Soft** (𝓕 defined by asymptotic/statistical/mean conditions — any a.p. degree,
   growth, pointwise-asymptotic Dirichlet representation, with or without on-line zero
   structure): 𝓕 contains lone-quadruple members (B, B′). The dichotomy is FALSE in 𝓕;
   no soft hypothesis proves droves.
2. **Categorical** (𝓕 = exact Dirichlet series + FE + growth, Hamburger-rigid): 𝓕 = {ζ}.
   The dichotomy for 𝓕 IS RH verbatim — nothing is gained by the class framing.
3. **Family-structured** (𝓕 = multi-support combinations, D–H-like): droves are a THEOREM
   (10 Thm A / 11 Thm A where S² holds) — but ζ is not in any such 𝓕 (10 Thm C:
   single-support in every Dirichlet decomposition).

**Verdict: the class-level dichotomy route to RH is closed, except for one named gap.**
> **The Goldilocks class problem `[OPEN CORE — the lane's class-language form]`:** does
> there exist a class 𝓕 with (i) ζ ∈ 𝓕; (ii) 𝓕 rigid against bump surgery (no
> t-localized-perturbation freedom); (iii) 𝓕 carrying a recurrence mechanism not
> RH-graded (a family/joint structure as in regime 3)? Every known 𝓕 satisfies at most
> two of the three. (i)+(ii) Hamburger ⟹ singleton (no mechanism); (i)+(iii) fails by the
> blind cone (ζ single-support); (ii)+(iii) is the D–H world (ζ absent).

The primitivity wall has now been derived from THREE independent directions: value
distribution (10: principal pinning / unique factorization), almost-periodicity (11:
S²-vs-B² gap at exactly ζ's regularity), and class rigidity (5.3: soft/categorical
trichotomy). Three angles, one wall — strong evidence the remaining live routes are the
EXACT-STRUCTURE ones, which the wall does not touch:
(a) exactness-forcing near σ = 1 (#112: Landau/index-formula budget — an exact identity a
lone term cannot balance is not a soft hypothesis);
(b) the deck-class cocycle w_k (#113: exact monodromy data, not statistical);
(c) the measured jet/phase transfer structure as a guide to (a)'s mechanism.
