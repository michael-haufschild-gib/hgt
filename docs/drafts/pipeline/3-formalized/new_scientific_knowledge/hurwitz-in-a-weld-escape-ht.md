# Hurwitz ζ(s,a) in a: the weld as exponent-escape up the s-ladder

- **ID:** hurwitz-in-a-weld-escape-ht
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) — full HT-in-a of the Hurwitz ladder for `s ∉ ℚ`; minimal weld-model for 𝓜⁺
- **Source:** Turing, 2026-06-24. Entropy draw (seed 1410371457939118431): object=Hurwitz-zeta, move=revisualise, domains=tensegrity+renormalization.

## The object and the weld

ζ(s,a) = Σ_{n≥0}(n+a)^{−s}. As a function of **a** (s fixed, generic), the differential
generator does not close — it escapes up the s-ladder:

  **Weld:**     ∂_a ζ(s,a) = −s·ζ(s+1,a)
  **Escape:**   ∂_a^k ζ(s,a) = (−1)^k (s)_k ζ(s+k,a),   (s)_k = rising factorial.

So the order-k jet of ζ(·,a) in a is the **shift-family** {ζ(s+k,a)}_{k≥0} — distinct
Hurwitz functions, one per rung. This is the cleanest possible instance of the founding
metaphor: ∂_a is a flow that never returns to a finite-dim a-slice; the object is fixed by
the constraint-lattice across s, not propagated in a. (Tensegrity reframe: a-shifts are the
*rigid* members — ζ(s,a+1)=ζ(s,a)−a^{−s}, finite power sums — the transcendence lives in the
*floppy* s-direction, coupled by the single brace above.)

`[VERIFIED — mpmath dps=30]` All three identities, s=2.5:
- weld ∂_a ζ = −s ζ(s+1,a): match (a=1.3).
- escape k=3: ∂_a³ζ = (−1)³(s)_3 ζ(s+3,a): match.
- leading singularity ζ(s,a) ~ (a+n)^{−s} near a=−n (n=0,3): ratio→1.0 (eps 1e-2→1e-6).

## Argument toward HT in a (generic s) — PARTIAL

**Claim [CONJECTURE]:** for generic (transcendental) s, ζ(s,a) satisfies no algebraic ODE
in a — i.e. {ζ(s+k,a)}_{k≥0} are ℂ(a)-algebraically independent.

**Step 1 (done).** Any algebraic ODE of order N in a is, via Escape, a polynomial relation
  P(a; ζ(s,a),…,ζ(s+N,a)) = 0,  coefficients in ℂ(a)  (the (s)_k are constants).

**Step 2 (done — corrects a too-quick first pass).** Monomials ∏ζ(s+k,a)^{e_k} carry leading
exponent −(d·s+w) at each pole a=−n, where d=Σe_k (degree), w=Σk·e_k (weight). Distinct
monomials of equal (d,w) **collide** (e.g. ζ(s)ζ(s+2) vs ζ(s+1)², both −(2s+2)). So the naive
"distinct exponents" kill fails. What survives: for generic s, the values {d·s+w} are distinct
across (d,w) (s transcendental ⟹ ds+w=d's+w' ⟺ d=d',w=w'). Hence the relation is
**graded-homogeneous at every pole**: each (d,w)-piece vanishes separately.

**Step 3 (done).** Each (d,w)-piece, near a=−n, is (a+n)^{−(ds+w)}·[Σ_{α:(d,w)} c_α(a)·(1+O(a+n))].
Vanishing ⟹ Σ_{α:(d,w)} c_α(−n)=0 for ALL n≥0. The coefficient-sum is rational in a and
vanishes at infinitely many points ⟹ **Σ_{α:(d,w)} c_α(a) ≡ 0** for each (d,w).

**Step 4 (OPEN CORE).** Step 3 kills the coefficient-*sum* per grade, not each c_α (the
monomials in a fixed (d,w) are distinct functions). Separation requires the **subleading**
expansion ζ(s+k,a)=(a+n)^{−(s+k)}+R_{n,k}(a): the first correction has exponent
−((d−1)s+(w−k)), landing in the lower grade (d−1,w−k) — a triangular/renormalization coupling.
Conjecture: induction on (d,w) down this triangle forces every c_α≡0, closing HT. NOT done.

## Gates / status

- [x] weld, escape, leading-singularity identities verified numerically
- [x] Steps 1–3 (graded-homogeneity + per-grade coefficient-sum ≡0)
- [x] Step 4 CLOSED (2026-07-11), superseded by the delocalized-monodromy proof — all degrees
  at once, `s ∉ ℚ` (see "FULL CLOSURE" section)
- [x] literature check (2026-07-11): fixed-`s` ladder independence not located; Ostrowski 1920 /
  Mordukhai-Boltovskoi 1914 cover only the joint two-variable PDE statement (see verdict section)
- [x] Lean formalization, unconditional and axiom-clean (2026-07-11): see Formalization section

## Novelty / significance (self-graded, critical)

- **Novelty: LOW–MEDIUM, borderline-promptable.** Integer-s reduces to Hölder (ψ^{(k)} HT). Generic-s
  Hurwitz/Lerch HT is plausibly in the literature; the exponent-escape+graded-induction method is
  elementary. A competent search might produce the *result*. The card ships only if Step 4 closes
  AND the literature check returns empty, OR if the **weld-model framing** itself is the contribution.
- **Significance: SOLID for the branch.** This is the minimal clean model of the 𝓜⁺ seam — a
  differential generator whose image is a *shift* of a neighboring object, never closing. Whatever
  proves HT here is the template for the seam where ∂_s meets {σ_p}. The value is the *object*, not
  the (possibly-known) HT verdict.

## Log

- 2026-06-24 — Turing: opened from entropy draw. Identities verified (mpmath). Self-corrected the
  exponent argument (graded collision). Banked Steps 1–3; Step 4 (subleading triangular induction)
  is the open core. Honest novelty: borderline; significance from the weld-model framing.

## Step 4 progress — descent refined + moment/positivity structure (2026-06-24, Turing)

Attacked the open core directly (team dormant). Three genuine advances:

**(A) The descent has a clean top.** Over all monomials ∏ζ(s+k,a)^{e_k}, the most-singular
exponent at a pole a=−n is −(d·s+w) with the largest d·s+w. For top degree D and top rung N
this is −D(s+N), carried by the UNIQUE monomial ζ(s+N,a)^D (all degree on the highest rung).
Nothing else reaches it (corrections only add positive powers (a+n)^{s+k}). So its coefficient
≡0 outright — the descent's first step needs no collision handling.

**(B) Collisions are subleading-separated.** Same-grade monomials (e.g. ζ(s)ζ(s+2), ζ(s+1)²,
both grade (2,2), leading (a+n)^{−(2s+2)}) separate at first subleading order: their corrections
sit at exponents −(s+2) vs −(s+1) respectively (different for generic s), feeding the triangular
(d,w)→(d−1,w−k) system. The simplest collision is excluded WITHOUT numerics: strict log-convexity
of s↦ζ(s,a) (Cauchy–Schwarz on the measure Σδ_{log(n+a)}, not a point mass) gives
ζ(s+1,a)² − ζ(s,a)ζ(s+2,a) < 0 strictly (Turán). No grade-(2,2) relation.

**(C) Moment/positivity reframing `[VERIFIED — mpmath]`.** Γ(s)ζ(s,a) = ∫₀^∞ t^{s−1}e^{−at}/(1−e^{−t})dt
(match at (s,a)=(2.5,1.3),(3.2,0.7)). So m_k(a) := Γ(s+k)ζ(s+k,a) are the moments ∫t^k dν_a of the
POSITIVE infinite-support measure ν_a = t^{s−1}e^{−at}/(1−e^{−t})dt, and ∂_a = −(×t) IS the escape
ladder. Hankel determinants det[m_{i+j}] verified strictly positive (sizes 2,3,4 → 1.52, 8.87, 402.7).
Infinite support ⟹ no vanishing Hankel determinant ⟹ no constant-coefficient linear recurrence among
{m_k} *in k*. **[CORRECTION 2026-06-24, Turing — invalid inference retracted.]** This does NOT prove
"no linear ODE in a": Hankel positivity is a statement about the moment SEQUENCE in k (ν_a infinite-
support), whereas a linear ODE is a ℂ(a)-LINEAR relation Σ q_j(a) f_j(a)=0 among the functions
(⟺ ∫Q_a(t)dν_a=0, one scalar condition — easily satisfiable, does not force Q_a≡0). The two are
logically independent; the implication asserted here was a non-sequitur.
**Correct proof that there is no linear ODE in a (distinct exponents):** at a=−n the terms
q_j(−n)(a+n)^{−(s+j)} have DISTINCT non-integer exponents −(s+j) (generic s), hence are ℂ-linearly
independent ⟹ each q_j(−n)=0 for all large n ⟹ each q_j≡0 (rational, ∞ zeros). This is the degree-1
case of the descent (no collisions). Hankel positivity remains a TRUE separate fact (ν_a infinite-
support), just not the lemma that closes degree-1.

**Net:** HT-in-a (generic s) now reduces to ONE lemma — the graded triangular system of (A)+(B)
has full rank at every grade, forcing each c_α≡0. Degree-1 is done (C); the top of every degree is
done (A); the simplest nonlinear collision is done (B/Turán). Open: the general grade-(d,w) rank.
This is a bounded linear-algebra statement, no longer a vague "transcendence" gap.

- 2026-06-24 — Turing: Step 4 advanced. Degree-1 closed via DISTINCT EXPONENTS (see §C correction —
  the earlier "via Hankel positivity" was an invalid inference, retracted same day); descent top +
  simplest collision closed. Remaining open core = graded triangular rank lemma.

## Rank-lemma attack → reduction to the log-derivative (2026-06-24, Turing)

Attacked the grade-(d,w) rank lemma directly. Outcome: a clean reduction + one shortcut ruled out.

**Ratios carry the homogeneous core `[VERIFIED — mpmath]`.** Degree-homogeneous relations among
{f_k=ζ(s+k,a)} ⟺ algebraic relations among ratios u_k=f_k/f_0. The irrational exponent cancels in
the ratio: u_k ~ (a+n)^{−k} near a=−n (INTEGER poles; verified k=1,2,3, n=0,2, ratio→1.0). Since
f_k=(−1)^k/(s)_k·f_0^{(k)}, u_k ∝ f_0^{(k)}/f_0 = Bell-polynomial in L:=∂_a log ζ(s,a) and its
derivatives. Hence the reduction chain:

  ζ(s,a) HT-in-a (homog. core)  ⟺  L=∂_a log ζ(s,a) is HT  ⟺  {u_k} alg. independent /ℂ(a).

**L not DA of order 1 — PROVED.** A Riccati L'=a_0+a_1 L+a_2 L² forces c_0 f_0+c_1 f_1+c_2 f_2=0,
a LINEAR relation among {f_k} — already killed by the distinct-exponent argument (degree-1, §C as corrected). So order-1 closes
and recovers the log-derivative (ψ-analog) result. [Connects to 1-in-progress/log-derivative-ht-theory.md.]

**Malmquist/movable-singularity shortcut RULED OUT.** Tempting to kill all orders via "movable
singularities of algebraic ODEs have rational leading exponent (dominant-balance p=ℤ/ℤ), but ζ's
exponent −s is irrational." It fails: ζ(s,·)'s ONLY singularities are the fixed a=−n, all with the
SAME exponent −s, and the most-singular (top-grade) part of any P is degree-homogeneous, for which
the dominant balance leaves p unconstrained — so p=−s is allowed, no contradiction. The shortcut that
worked at order 1 (Malmquist, this session's ade-boundary line) does NOT generalize here; the integer
poles of the ratios u_k are exactly why the exponent tool is exhausted.

**Open core, sharpened:** L=∂_a log ζ(s,a) is not DA of order ≥2 (equiv. {u_k} alg. indep. at
degree ≥2). Integer poles ⟹ a NEW tool is needed (growth/Nevanlinna of L, or a relation between the
a-zeros of ζ(s,·) and the poles — L's residues are −s at a=−n and +1 at each a-zero of ζ(s,·)).

- 2026-06-24 — Turing: reduced the homogeneous core to log-derivative HT; order-1 proved via Hankel;
  irrational-exponent shortcut ruled out; open core = L not-DA-order-≥2, needs a non-singularity tool.

## 2026-06-24 Haiku audit: weld identity known; linear case repaired; nonlinear rank still open

Status: second-agent audit / route sharpening.

### Literature status

The differential-difference weld identity is known in the Lerch-function literature.
Lagarias--Li's Lerch work states raising/lowering differential-difference equations;
in their notation `D_L^+ zeta = -s zeta(s+1,...)`, and the Lerch transcendent also
satisfies the corresponding linear PDE. Thus the identity

`partial_a zeta(s,a) = -s zeta(s+1,a)`

is a good minimal model for the HGT weld, but it is not by itself new.

First-pass search did not locate a theorem exactly matching this card's strongest
fixed-`s`, parameter-`a` claim: algebraic independence over `C(a)` of the finite
shift ladder `{zeta(s+k,a)}` for generic `s`. Nearby literature instead covers
Lerch/Hurwitz value distribution, universality, and functional independence in
the `s` variable or in larger Lerch families. Novelty is therefore still open,
but source risk is high.

### Correction to the moment/Hankel claim

The moment representation is correct:

`Gamma(s+k) zeta(s+k,a) = int_0^infty t^k t^{s-1} e^{-a t}/(1-e^{-t}) dt`.

Strict Hankel positivity for this positive infinite-support measure proves that,
for a fixed `a`, the moment sequence has no nontrivial constant-coefficient finite
linear recurrence. It does **not** by itself rule out a linear ODE in `a`, because
a linear ODE gives

`sum_{k=0}^N q_k(a) zeta(s+k,a) = 0`

with rational/polynomial coefficient functions `q_k(a)`, not constants.

So the phrase "no LINEAR ODE in a, unconditionally" is too strong if justified
only by Hankel positivity.

### Repaired degree-one proof

The degree-one case is still easy, by the singularity ladder.

Assume `s` is not a non-positive integer and

`sum_{k=0}^N q_k(a) zeta(s+k,a) = 0`, with `q_k in C(a)`.

Choose `N` maximal with `q_N` nonzero. At every sufficiently large integer `n`
where no `q_k` has a pole, put `x=a+n`. Near `a=-n`,

`zeta(s+k,a) = x^{-s-k} + holomorphic terms`.

The exponent `-s-N` is strictly more singular than all `-s-k` for `k<N`, so the
coefficient `q_N(-n)` must vanish for infinitely many `n`. Hence `q_N=0`, a
contradiction. Descending proves all `q_k=0`.

Thus no rational-coefficient linear ODE follows from local branch singularities,
not from the Hankel determinant argument.

### Nonlinear Step 4 remains open

The nonlinear case still needs the claimed triangular/full-rank descent inside
each `(degree, weight)` collision class. Current progress proves coefficient-sum
conditions and some top/simple collision cases, but it does not yet prove that
every monomial coefficient vanishes. A proof must explicitly handle:

1. rational coefficient functions evaluated at all `a=-n`;
2. collisions such as `zeta(s) zeta(s+2)` vs. `zeta(s+1)^2` in every grade;
3. subleading regular-part data
   `R_{n,k}^{(j)} = partial_a^j (zeta(s+k,a) - (a+n)^(-s-k))|_{a=-n}`;
4. a finite-rank statement showing these subleading data separate all monomials
   in the collision class.

Corrected status: degree one is proved by the singularity ladder; the weld model
is significant; the full HT claim remains `1-in-progress` pending the nonlinear
rank lemma and literature check.

Sources checked in this audit include Lagarias--Li, *The Lerch Zeta Function II.
Analytic Continuation* (arXiv:1005.4967), Lagarias--Li, *The Lerch Zeta Function
III* (Ramanujan J. 2015 / arXiv:1506.06161), Nagoshi 2019 on Lerch zeta-functions
and derivatives, and Garbaliauskiene--Macaitiene--Siauciunas 2023 for the broader
functional-independence reference trail.

## Cold-probe promptability check (2026-06-24, Turing)

Fired an independent cold check (GPT-5.1 via OpenRouter, zero context): "Is ζ(s,a) hypertranscendental
in a for generic irrational s? Give the proof if known." Result, verbatim-summary:
- It RECITES the promptable part: the weld ∂_a ζ(s,a)=−s ζ(s+1,a), and "infinite system linking
  ζ(s+k,a), not a closed ODE in ζ(s,a) alone."
- It produces NONE of the content here: no order-1 proof, no Hankel/moment argument, no log-derivative
  reduction. It concludes: "this is open as far as current literature indicates ... no concrete proof
  of hypertranscendence (nor a counterexample) exists ... regard as open."

**Novelty grade, revised (was LOW–MEDIUM):**
- The weld/escape identities: PROMPTABLE (cold model recites them). Unchanged.
- The order-1 HT proof (Hankel positivity ⟹ no linear ODE) + the reduction to log-derivative HT:
  **NOT promptable** — a strong cold model produces neither and calls the problem open. Grade → MEDIUM.
- Caveat (kept honest): a cold model's "open" is evidence of non-promptability, NOT proof of literature-
  novelty (model recall is bounded). A definitive novelty claim still needs a real literature pass; but
  for the lab's question — knowledge "not a prompt away" — the probe answers YES for the proof content.

This is the cleanest agentic-vs-cold separation banked this session: the promptable structural setup vs.
the non-promptable verified proof (Hankel positivity was numerically certified; the cold model had no
route to it).

- 2026-06-24 — Turing: cold probe ⟹ order-1 proof + reduction are not promptable (GPT-5.1 calls it open);
  novelty of the PROOF content upgraded to MEDIUM. Weld identities remain promptable.

## 2026-06-24 Haiku progress: monodromy-line lemma and the exact nonlinear gate

Status: proved necessary condition / proof-route sharpening. This does not close HT.

Let `F_k(a)=zeta(s+k,a)` for `0<=k<=N`, and fix `s` with `exp(-2 pi i s)` of infinite order
(for example `s notin Q`). Near a branch point `a=-n`, put `x=a+n`. On a chosen local branch,

`F_k(-n+x)=x^{-s-k}+R_{n,k}(x)`,

where `R_{n,k}` is holomorphic at `x=0` after removing the `n`th singular term. Write

`H_k(x)=x^{-s-k}`, `R_n(x)=(R_{n,0}(x),...,R_{n,N}(x))`, and
`H(x)=(H_0(x),...,H_N(x))`.

### Lemma: any algebraic relation vanishes on the local monodromy line

If `P(a,Y_0,...,Y_N)` is a rational-coefficient polynomial relation with

`P(a,F_0(a),...,F_N(a))=0`,

then for every `n` outside the finite pole set of the coefficients and for all sufficiently small `x`,

`P(-n+x, R_n(x)+T H(x)) identically 0 as a polynomial in T`.

Proof. A positive loop around `x=0` sends each singular term `x^{-s-k}` to
`q x^{-s-k}`, with the same `q=exp(-2 pi i s)` for every integer `k`, and leaves the regular part
`R_{n,k}` unchanged. After `m` loops, the same global relation gives

`P(-n+x, R_n(x)+q^m H(x))=0`

for every integer `m`. Since `q` has infinite order, the values `{q^m}` are infinite. The left side is a
polynomial in `T`, so it vanishes identically. ∎

Equivalently, for every `j>=0`,

`(H(x) . partial_Y)^j P(-n+x,R_n(x)) = 0`.

The old leading-grade cancellation is the top `T`-coefficient of this lemma. The nonlinear problem is no longer
best phrased as informal subleading expansion bookkeeping; it is the following Zariski-density gate:

> Prove that, for generic `s`, the union of local monodromy lines
> `L_{n,x}={R_n(x)+T H(x): T in C}` over infinitely many `n` and small `x` is Zariski dense in the finite
> shift-ladder space `(Y_0,...,Y_N)` over `C(a)`, for every finite `N`.

If this density holds, no nonzero `P` can exist, so the finite ladder is algebraically independent and the
fixed-`s` Hurwitz function is HT in `a`.

This lemma explains both what the existing partial proof really proves and what remains:

1. The degree-one proof is the easiest density shadow: the top rung has a unique most singular direction.
2. Same `(degree, weight)` collisions are exactly polynomials vanishing on the rational-normal leading
   direction `H=x^{-s}(1,x^{-1},...,x^{-N})`.
3. The regular parts `R_{n,k}` and the `x`-dependence of the monodromy line are what must break those leading
   rational-normal collisions.

Next proof target: prove the density gate first for `N=2`, where the only leading quadratic collision is
`Y_0Y_2-Y_1^2`; this should recover and sharpen the Turan/log-convexity check already in the card.

## 2026-06-24 Haiku progress: quadratic N=2 density shadow

Status: bounded theorem inside the monodromy-line program; this does not prove full HT.

Let `F_k(a)=zeta(s+k,a)` for `k=0,1,2`. For `Re(s)>1` and `s notin Z`, there is no nonzero polynomial relation of total `Y`-degree at most two

`P(a,F_0(a),F_1(a),F_2(a))=0`, with `P in C(a)[Y_0,Y_1,Y_2]`.

Equivalently, the order-two algebraic ODEs for `zeta(s,a)` whose polynomial degree in `(y,y',y'')` is at most two are excluded in this half-plane after the escape identity.

### Proof

Clear denominators in the rational coefficients and avoid the finite set of poles. Near `a=-n`, put `x=a+n` and write

`F_k(-n+x)=x^{-s-k}+R_{n,k}(x)`,

with `R_{n,k}` holomorphic at `x=0` after the local singular term is removed.

For a quadratic relation, the leading exponents of quadratic monomials are `-2s-w`, where `w=i+j` for `F_iF_j`. Since `s` is nonintegral, these do not collide with linear or constant exponents. The weights `w=0,1,3,4` each have a unique quadratic monomial, so their coefficients vanish identically. At weight `w=2`, the only leading collision is

`F_0F_2` versus `F_1^2`,

and the leading condition gives `q_{02}+q_{11}=0`. Thus any remaining quadratic part is

`q(a)(F_0F_2-F_1^2)`.

So a surviving relation would have the form

`q(a)(F_0F_2-F_1^2)+l_0(a)F_0+l_1(a)F_1+l_2(a)F_2+c(a)=0`.

But

`F_0F_2-F_1^2 = x^{-s-2}R_{n,0}(0)+O(x^{-s-1})`

because the leading rational-normal term cancels: `x^{-s}x^{-s-2}-x^{-s-1}x^{-s-1}=0`, and the next most singular term is `x^{-s-2}R_{n,0}(0)`. The coefficient of `x^{-s-2}` in the displayed relation is therefore

`q(-n)R_{n,0}(0)+l_2(-n)=0`

for all large `n`.

If `q` were nonzero, this would force the sequence `R_{n,0}(0)` to agree at all large integers with a rational function of `n`. But for the chosen branch,

`R_{n,0}(0)=zeta(s)+eta H_n^{(s)}`, where `eta=exp(epsilon pi i s)` for the fixed local branch
and `epsilon in {+1,-1}`,

so

`R_{n,0}(0)-R_{n-1,0}(0)=eta n^{-s}`.

A finite difference of a rational function has an asymptotic expansion in integral powers of `n`; it cannot equal `eta n^{-s}` for nonintegral `s`. Hence `q=0`, and then `l_2(-n)=0` for infinitely many `n`, so `l_2=0`. The remaining linear relation is killed by the degree-one distinct-exponent argument already recorded in the card.

Thus no degree-`<=2` relation exists. The proof also explains why the old Turan/log-convex check was only the visible face of the first collision: the real separator is not positivity, but the non-rationally-interpolable regular-part sequence `R_{n,0}(0)`.

### Anti-theatre status

This is a native weld/escape result, not an RH mirror. Its falsification point is explicit: if `R_{n,0}(0)` were rationally interpolable, the quadratic collision could be absorbed into a lower-degree term. The finite-difference obstruction blocks that. The result remains narrow: higher-degree relations and the full `N=2` Zariski-density gate are still open.

## 2026-06-24 Haiku next gate: all-N quadratic tail independence

Created `hurwitz-quadratic-all-n-tail-independence.md` as the next precise proof obligation after the proven `N=2` quadratic shadow.

The proposed all-`N` quadratic theorem is:

`{zeta(s+k,a)}_{0<=k<=N}` has no nonzero `C(a)`-polynomial relation of total degree `<=2`, for `Re(s)>1` and `s notin Z`.

The reduction is now concrete. Quadratic leading terms only impose anti-diagonal cancellation on the rational-normal direction. The local-orbit/filtration descent then produces rational interpolation equations involving

`R_{n,k}(0)=zeta(s+k)+eta_k H_n^{(s+k)}`.

So the open core is the rational-tail independence lemma:

If rational functions `r_0,...,r_M,R` satisfy

`sum_j r_j(n) H_n^{(s+j)} = R(n)`

for all large integers `n`, then every `r_j=0`.

This is the correct non-theatre continuation of the `N=2` proof. The possible failure mode is explicit: rational coefficients across several shift-columns might cancel the nonintegral harmonic tails. If that cancellation exists, the all-`N` quadratic claim fails; if the tail lemma holds, the row descent should close degree two for every finite ladder.

## 2026-06-24 Haiku promotion: all-N quadratic gate closed

Promoted `hurwitz-quadratic-all-n-tail-independence.md` to `../2-fully-proven/`.

Result: for `Re(s)>1`, `s notin Z`, and every finite `N`, the shift ladder

`{zeta(s+k,a)}_{0<=k<=N}`

has no nonzero `C(a)`-polynomial relation of total `Y`-degree `<=2`.

Proof structure:

1. The rational-tail independence lemma is proved by ordinary generating functions. A rational interpolation relation among `H_n^(s+j)` becomes

   `sum_j p_j(theta)(Li_{s+j}(z)/(1-z)) in C(z)`.

2. In `z=e^(-mu)`, the noninteger branch part is

   `sum_j p_j(-D)(Gamma(1-s-j) mu^(s+j-1)/(1-e^(-mu)))`.

   If this branch part vanished, inspect the nonzero pole tower `mu=2 pi i m` of `(1-e^(-mu))^(-1)`. The highest derivative order gives a polynomial in `mu_m` with infinitely many roots, so the top operator coefficients vanish; descending kills all `p_j`.

3. The local-orbit descent is the right proof shape: when `exp(-2*pi*i*s)` has at least three distinct powers, the monodromy orbit gives the full quadratic line; in the order-two case the orbit still gives the `T^1` coefficient and the local exponent filtration recovers the missing `T^2` coefficient. The resulting `T^1` identity descends column by column; each row is exactly a rational-tail interpolation equation, so the tail lemma kills the remaining quadratic and linear coefficients.

This is still not full HT: degree `>=3` relations remain open. But the first uniform nonlinear gate in the Hurwitz weld model is now closed without computation and without an RH-equivalent target.

## 2026-07-11 FULL CLOSURE — multi-branch-point deformation kills every degree at once

Status: **the card's open core is closed.** The graded rank lemma, the G-product null spaces,
the rational-tail machinery, and the Zariski-density gate are all bypassed by one structural
move: **delocalize the monodromy.** Every previous attack localized at a single branch point
`a = -n`, where the deformation direction is a single point of the rational normal curve and
same-grade monomials collide. Using loops at `N+1` DIFFERENT branch points simultaneously gives
`N+1` distinct points on the rational normal curve — a Vandermonde system — and the affine orbit
of the ladder becomes the whole of `C^{N+1}` at every base point. No collision analysis survives
to be needed.

### Theorem A (ladder independence) `[PROVED HERE]`

Let `Re(s) > 1` and `s notin Q`. For every `N >= 0` there is no nonzero
`P in C(a)[Y_0,...,Y_N]` with

`P(a; zeta(s,a), zeta(s+1,a), ..., zeta(s+N,a)) = 0`  for all `a` in the upper half-plane `U`.

Equivalently, the shift ladder `{zeta(s+k,a)}_{k>=0}` is algebraically independent over `C(a)`.

### Theorem B (hypertranscendence in `a`) `[PROVED HERE]`

Under the same hypotheses, `a |-> zeta(s,a)` satisfies no algebraic differential equation over
`C(a)`: via the escape identity `partial_a^k zeta(s,a) = (-1)^k (s)_k zeta(s+k,a)` any algebraic
ODE of order `N` becomes a ladder relation; the change of variables `Y_k -> (-1)^k (s)_k Y_k` is
invertible because `(s)_k != 0` (`s notin Z_{<=0}`), so Theorem A forces the zero ODE.

### Proof of Theorem A

Notation: `F_k(a) = zeta(s+k,a) = sum_{m>=0} (m+a)^{-s-k}` (principal branches; the series
converges locally uniformly on `C \ (-infty,0]`, so each `F_k` is holomorphic there, in
particular on `U`). Suppose `P != 0`; clear denominators so `P in C[a][Y_0..Y_N]`. Fix `M = N`
and define the **deformation family**: for `c = (c_0,...,c_M) in C^{M+1}`

`F_k^c(a) := F_k(a) + sum_{n=0}^{M} (c_n - 1) (a+n)^{-s-k}`,   holomorphic on `U`,  `F^1 = F`.

Write `q = exp(-2 pi i s)`.

**Claim 1 (deformation invariance).** For every `(m_0,...,m_M) in N^{M+1}`:
`P(a; F^{(q^{m_0},...,q^{m_M})}(a)) = 0` on `U`.

Induction on `m_0 + ... + m_M`; base case is the hypothesis. Step: assume the relation for `c`,
increment coordinate `n <= M`. Substitute `a = -n + e^z` and work on the half-plane
`D = {Re z < -log 2}` (so `x = e^z` has `0 < |x| < 1/2 <=` distance to every other branch
point) and its sub-strip `D+ = D ∩ {0 < Im z < pi}` (there `Im x > 0`, so `a in U`).

(i) On `D+`, for each `k`:
`F_k^c(-n+e^z) = c_n e^{-(s+k)z} + T_{n,k}^c(e^z)`,
where `T_{n,k}^c(x) = sum_{m>=0, m != n} (m-n)^{-s-k} (1 + x/(m-n))^{-s-k}
+ sum_{n'<=M, n' != n} (c_{n'}-1) (n'-n)^{-s-k} (1 + x/(n'-n))^{-s-k}`.
This uses: `(e^z)^{-s-k} = e^{-(s+k)z}` for `Im z in (-pi, pi]`; the principal-branch product
split `(w+x)^c = w^c (1+x/w)^c` for real `w != 0` and `Im x > 0` (arg addition stays in the
principal window: for `w < 0` the arg sum is `pi + (negative small)`); and absorption of the
`n' = n` deformation term into `c_n e^{-(s+k)z}`.

(ii) `G(z) := P(-n+e^z; (c_n e^{-(s+k)z} + T_{n,k}^c(e^z))_k)` is holomorphic on `D`: each
`T_{n,k}^c` is holomorphic on `{|x| < 1/2}` (every base `1 + x/(m-n)` stays in the right
half-plane; Weierstrass M-test against `sum ||(m-n)^{-s-k}||`), the singular exponentials are
entire, and polynomial coefficients are entire. `G = 0` on the open sub-strip `D+` by (i) and
the induction hypothesis; `D` is connected; hence `G = 0` on all of `D` (identity theorem).

(iii) `D` is `2 pi i`-shift-invariant, and `G(z + 2 pi i)` equals the same expression with
`c_n` replaced by `q c_n`: the tails and coefficients depend on `z` only through `e^z`
(periodic), while `e^{-(s+k)(z+2 pi i)} = e^{-2 pi i s} e^{-(s+k)z}` (the integer part of the
exponent drops out — the SAME multiplier `q` on every rung; this is the diagonal monodromy of
the weld). Hence the `c'`-relation, `c' = (..., q c_n, ...)`, holds on `D`.

(iv) Restrict to `D+` and reverse (i): `P(a; F^{c'}(a)) = 0` on the open set
`V_n = {-n + x : 0 < |x| < 1/2, Im x > 0} subset U`. The function `a |-> P(a; F^{c'}(a))` is
holomorphic on the connected set `U` and vanishes on `V_n`, hence on all of `U`. Induction
closes. ∎

**Claim 2.** `s notin Q` implies `m |-> q^m` is injective on `N`, so `Q_set = {q^m}` is
infinite. (`q^{m} = q^{m'}` forces `exp(-2 pi i s (m-m')) = 1`, i.e. `s(m-m') in Z`.)

**Claim 3 (grid to all of `C^{M+1}`).** Fix `a in U`. `Lambda(c) := P(a; F^c(a))` is a
polynomial in `(c_0,...,c_M)` vanishing on `Q_set^{M+1}` (Claims 1–2); a polynomial vanishing
on a product of infinite sets is identically zero. So `P(a; F^lambda(a)) = 0` for ALL
`lambda in C^{M+1}` and all `a in U`.

**Claim 4 (Vandermonde surjectivity — the density gate, closed).** Fix `a in U`. The affine
map `lambda |-> (F_k^lambda(a))_{k<=N}` from `C^{M+1}` to `C^{N+1}` is ONTO: its linear part
has matrix `W_{k,n} = (a+n)^{-s-k} = (a+n)^{-s} u_n^k` with `u_n = (a+n)^{-1}` pairwise
distinct and `(a+n)^{-s} != 0`, so (with `M = N`) `det W^T = prod_n (a+n)^{-s} ·
prod_{n<n'} (u_{n'} - u_n) != 0`. The deformation directions at the `N+1` branch points are
`N+1` DISTINCT points of the rational normal curve — this is where delocalization dissolves
the single-point collision problem. Hence `P(a; y) = 0` for every `y in C^{N+1}`.

**Claim 5 (kill).** For each monomial index `beta`, the coefficient `p_beta in C[a]` vanishes
at every `a in U`, hence `p_beta = 0`. So `P = 0`, contradiction. ∎

### Theorem A' (coefficient upgrade) `[PROVED HERE — paper level]`

The same proof runs verbatim with coefficients in the field `M_0` of meromorphic functions on
`C \ {0,-1,-2,...}` that are single-valued there (write each coefficient as a ratio of
holomorphic functions on this domain and clear denominators; single-valuedness = the
`2 pi i`-periodicity used in step (iii); the puncture `x = 0` is never hit since `x = e^z`).
`M_0` contains `C(a)`, `e^a`, `Gamma(a)`, `psi(a)` and all polygammas — i.e. the whole
INTEGER ladder `zeta(m,a)`, `m in Z_{>=2}`. Consequence: **the irrational ladder is
algebraically independent over the field generated by the integer ladder** — the weld
separates the `s notin Q` rungs from the Hoelder/polygamma (DA-side) rungs. No mixed relation
exists.

### Corollary (rational non-integer `s`) `[PROVED HERE]`

For `s = p/r` in lowest terms, `r >= 2`: `q` is a primitive `r`-th root of unity, the grid has
`r` points per coordinate, and the same argument kills every relation of total `Y`-degree
`< r`. (Consistent with and complementary to the banked all-N quadratic theorem, which covers
degree `<= 2` for ALL non-integer `s` including half-integers.) The residual object for
rational `s` — the `q`-invariant relation ideal at degree `>= r` — is genuinely open.

### Where the previous machinery stands

- Degree-1 distinct-exponent argument, the `N=2` density shadow, the all-N quadratic gate
  (rational-tail lemma + row descent): all SUBSUMED for `s notin Q` by Theorem A; they remain
  the only results covering `s in Q \ Z` (degree <= 2), and the rational-tail lemma is the
  natural tool for the rational-`s` residual above.
- The 0-backlog card `hurwitz-degree3-pochhammer-obstacle.md` (G-product null spaces, zeta-value
  transcendence lemma): SUPERSEDED — its open lemma is not needed on any route to HT for
  `s notin Q`.
- The monodromy-line lemma (single-point orbit) was the correct object seen through a keyhole:
  its Zariski-density gate is exactly Claim 4, provable only after delocalizing to many branch
  points.

### Literature verdict (promotion gate, 2026-07-11)

- Hilbert's problem / Mordukhai-Boltovskoi 1914 / Ostrowski 1920 (Math. Z. 8, 241–298; English
  translation+commentary arXiv:2211.02088): the TWO-variable function `sum x^n n^{-s}` satisfies
  no algebraic PDE jointly in `(x,s)`. This does not contain the fixed-`s` one-variable
  statement (its relations have coefficients polynomial in both variables; a fixed
  transcendental `s`-value is outside its quantifier).
- Fractional-polylog monodromy: known (Costin–Garoufalidis, Resurgence of the fractional
  polylogarithms). LINEAR independence of polylogs/hyperlogarithms with shifts: known
  (Deneufchatel–Duchamp–Minh–Solomon; arXiv:2202.13931). The fixed-`s` ALGEBRAIC independence
  of the Hurwitz shift ladder over `C(a)` was not located in any pass (this session's three
  searches, the 2026-06-24 audit, the cold GPT-5.1 probe which called it open).
- Verdict: method classical in flavor (abelian ray monodromy + Vandermonde), theorem apparently
  unrecorded. Novelty MEDIUM, significance for the branch HIGH (the founding weld model is now
  a fully proven HT instance, with a reusable delocalization engine).

### What this OPENS (next generative moves)

1. **Root-of-unity monodromy object** (rational non-integer `s`): the relation ideal is
   constrained to the `mu_r`-invariant subring; conjecture `[CONJECTURE]`: still zero, and the
   banked rational-tail lemma is the right second-generation tool (tail data breaks what the
   finite orbit cannot).
2. **Joint multi-base ladders** `[CONJECTURE]`: for `s, s'` with `1, s, s'` Q-linearly
   independent, the deformation multipliers `(q_s^m, q_{s'}^m)` are Zariski-dense in a
   2-torus, and the doubled Vandermonde should give algebraic independence of the JOINT ladder
   `{zeta(s+k,a)} ∪ {zeta(s'+k,a)}`. New object: the subtorus of multiplicative relations
   among weld multipliers as THE invariant of a multi-weld.
3. **The engine, axiomatized**: "abelian ray monodromy + one singular direction per branch
   point on a rational normal curve" is a portable schema — candidate next instances: Lerch
   `Phi(z,s,a)` in `a`; fractional polylog ladder in `z` at fixed `s notin Q` (branch points
   `0,1` only — needs the multi-point trick at derived singularities); Barnes `zeta_2(s,a,w)`
   in `a` (double ladder).

- 2026-07-11 — Fable: card CLOSED at all degrees for `s notin Q` by delocalized monodromy +
  Vandermonde; literature gate run (no exact match found); Lean formalization of Theorem A
  against genuine `hzeta` started (deformation bridge + grid + Vandermonde endgame).

## Formalization (2026-07-11) — unconditional, axiom-clean, arbitrary degree

The full Theorem A is formalized against the genuine `hzeta s a = Σ' m, (m+a)^{-s}`:

- `formal/GaloisForLFunctions/Hurwitz/LadderDeformation.lean` — the deformation family
  `dzeta c k a = hzeta (s+k) a + Σ_{n≤M} (c_n − 1)(n+a)^{-(s+k)}`; `hzeta` and the family are
  differentiable on the upper half-plane (`hzeta_differentiableOn`, per-point M-test).
- `formal/GaloisForLFunctions/Hurwitz/LadderDeformationBridge.lean` — the one-point monodromy
  move `relA_move`: in the `z = log(a+n)` coordinate the deformed ladder is
  `c_n e^{-(s+k)z} + (periodic analytic)`, the relation extends to the half-plane
  `Re z < -log 2` by the identity theorem, the shift `z ↦ z+2πi` multiplies `c_n` by
  `q = e^{-2πis}`, and the updated relation propagates back to the whole upper half-plane.
  `relA_grid` iterates the move over the full grid `(q^{m_0},…,q^{m_M})`.
- `formal/GaloisForLFunctions/Hurwitz/LadderIndependence.lean` — the endgame: `mv_grid_zero`
  (multivariate polynomial vanishing on a product of infinite sets is zero),
  `monoScalar_pow_injective` (`s ∉ ℚ` ⟹ the grid is infinite per coordinate),
  `ladder_matrix_surjective` (the transposed-Vandermonde × diagonal factorization of
  `W_{k,n} = (n+a)^{-(s+k)}`), and the capstones:

  **`HurwitzLadder.hurwitz_ladder_independence`** — hypotheses `1 < Re s` and
  `∀ r : ℚ, (r:ℂ) ≠ s` only: any `P : MvPolynomial (Fin (N+1)) (Polynomial ℂ)` with
  `P(a; hzeta s a, …, hzeta (s+N) a) = 0` on the upper half-plane is zero. NO degree bound.

  **`HurwitzLadder.hurwitz_ladder_independence_near_ray`** — same conclusion with the
  relation hypothesis only on one punctured upper half-disc at a single branch point `-n₀`.

- Card wrappers registered in `FullyProvenNewTargets`:
  `HurwitzLadderFullIndependenceTarget` / `hurwitz_ladder_full_independence` and the near-ray
  forms.
- Axioms: `[propext, Classical.choice, Quot.sound]` on every theorem; Hurwitz area build and
  `formal lint --check-generated` green. The Lean statement subsumes the degree-≤2 capstone
  `hurwitz_allN_hzeta_unconditional` for `s ∉ ℚ`; the old quadratic machinery remains the only
  coverage of `s ∈ ℚ ∖ ℤ`.
- The escape identity `∂_a hzeta = -s·hzeta(s+1,·)` (hence the ODE-form corollary, Theorem B)
  is paper-level; formalizing it needs termwise differentiation of the `hzeta` series
  (mathlib `SmoothSeries` machinery) — natural next Lean brick.

- 2026-07-11 — Fable: Theorem A formalized unconditionally at arbitrary degree (three new
  modules, 15 theorems, axiom-clean); card promoted 1-in-progress → 3-formalized
  (new_scientific_knowledge). Backlog card `hurwitz-degree3-pochhammer-obstacle` retired as
  superseded.
