# Feigenbaum dyadic values and the hypertranscendence question

- **ID:** feigenbaum-ht-ade-continuation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Source:** Wheeler id=1719 / Turing id=1697 / Feigenbaum backlog card

## Statement

The Feigenbaum fixed-point function g — the unique normalized solution of
  g(x) = −α g(g(x/α)),   g(0) = 1,   α≈2.502907875
extended to its maximal complex domain D (Epstein–Lascoux 1981, Buff) — is
hypertranscendental: it satisfies no algebraic differential equation (ADE) of any
finite order over ℂ(x).

The HT assertion remains `[CONJECTURE]`.  The exact value relations below are independent of that
assertion and are the current proved content of this card.

## Exact Feigenbaum value-relation ledger

Put

```text
lambda=-1/alpha.
```

The normalized functional equation is equivalently

```text
g(g(x))=lambda g(alpha x),   g(0)=1,   alpha lambda=-1.     (V1)
```

It forces the following values.

1. **Critical value and multiplier `[SEARCH]`.** Evaluation at zero and comparison of the first
   nonzero critical jet give

   ```text
   g(1)=lambda=-1/alpha.                                    (V2)
   ```

   If the critical point at zero has exact order `m`, so
   `g(x)=1+c x^m+O(x^(m+1))` with `c!=0`, then

   ```text
   g'(1)=-alpha^(m-1).                                      (V3)
   ```

   For the quadratic Feigenbaum fixed point, `m=2` and `g'(1)=-alpha`.  Campanino--Epstein--Ruelle
   state the equivalent relations `g(1)+lambda=0` and `lambda g'(1)+1=0` for this case.

2. **Dyadic iterate value law `[PROVED HERE] [NOVELTY UNVERIFIED]`.** Evenness and (V1) imply, for
   every `n>=0`,

   ```text
   g^[2^n](x)=lambda^n g(alpha^n x),                         (V4)
   g^[2^n](0)=lambda^n.                                     (V5)
   ```

   Here `g^[k]` denotes the `k`-fold compositional iterate.  The induction uses
   `alpha^n lambda^n=(-1)^n`; evenness removes that sign before one more use of (V1).

3. **Postcritical derivative-product law `[PROVED HERE] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC
   KNOWLEDGE]`.** Assume the critical point is quadratic, so `g'(0)=0` and `g''(0)!=0`. Then for
   every `n>=0`,

   ```text
   product_(j=1)^(2^n-1) g'(g^[j](0))=(-alpha)^n.            (V6)
   ```

   To prove it, write `g^[2^n]=h_n o g` with `h_n=g^[2^n-1]`.  The second-order chain rule at
   zero and (V4) give

   ```text
   h_n'(1) g''(0)=lambda^n alpha^(2n) g''(0).
   ```

   Cancellation of the nonzero quadratic jet yields

   ```text
   h_n'(1)=lambda^n alpha^(2n)=(-alpha)^n,
   ```

   while the ordinary iterate chain rule identifies `h_n'(1)` with the product in (V6).
   Consequently, for the real normalized fixed point,

   ```text
   sum_(j=1)^(2^n-1) log|g'(g^[j](0))|=n log alpha,
   |product_(j=1)^(2^n-1) g'(g^[j](0))|
      =(2^n)^(log(alpha)/log(2)).                             (V7)
   ```

   Thus `alpha` is exactly the dyadic polynomial-growth exponent of the postcritical derivative
   product.  The corresponding Lyapunov average is `n log(alpha)/(2^n-1)` and tends to zero.

Relations (V2)--(V7) are value identities.  They do not imply differential algebraicity or
hypertranscendence and are not evidence for either conclusion without an additional theorem about
relations among the resulting values.

The algebraic content (V2), (V4), and (V5) is formalized in
`GaloisForLFunctions.FeigenbaumValueRelations` as `feigenbaum_critical_value`,
`feigenbaum_dyadic_iterate`, `feigenbaum_dyadic_critical_value`,
`feigenbaum_quadratic_postcritical_deriv`, and
`feigenbaum_quadratic_postcritical_product`.  The derivative-product theorem has its own stage-3
card at
`../3-formalized/new_scientific_knowledge/feigenbaum-postcritical-derivative-product-law.md`.
The dyadic and derivative-product theorems are axiom-clean apart from Lean's standard `propext`,
`Classical.choice`, and quotient soundness; the critical-value theorem uses no axioms.

Primary normalization source: M. Campanino, H. Epstein, D. Ruelle, *On Feigenbaum's Functional
Equation*, IHES/P/80/32 (1980), equations (7)--(8) and the theorem on page 6.  The quadratic values
(V2)--(V3) are `[SEARCH]`.  Exact searches did not locate the all-`n` dyadic formula (V4), so its
scientific novelty remains unverified rather than asserted.  Focused searches for the exact
postcritical product (V6) and its exponent interpretation (V7) located the functional equation,
standard iterate-multiplier facts, and literature on zero Lyapunov exponent and multifractality,
but no statement of (V6) or (V7).  Their novelty label remains provisional pending specialist
review.

## Required inputs (to verify before promoting)

1. **Epstein–Lascoux noncontinuability**: g is analytic on D, bounded (g ∈ H^∞(D)),
   and D is a bounded Jordan domain with rectifiable boundary ∂D. g has no analytic
   continuation past ANY point of ∂D. [Source: Epstein–Lascoux 1981; Buff for maximal W_c]

2. **D is a Jordan domain with rectifiable boundary**: needed for Fatou's theorem.
   [Source: Epstein's quasiconformal constructions; ∂D = Feigenbaum Julia set, a Jordan curve]

## Proof [PROVED HERE modulo verification of inputs 1–2]

Assume for contradiction: P(x, g(x), g'(x), ..., g^{(n)}(x)) = 0 on D, with
P ∈ ℂ[x, y₀, ..., y_n] nonzero and irreducible over ℂ(x, y₀, ..., y_{n-1}).

**Step 1 (Singular set is discrete).**
Define Q(x) = (∂P/∂y_n)(x, g(x), g'(x), ..., g^{(n)}(x)) on D.
Since P is irreducible over ℂ(x, y₀,...,y_{n-1}), its discriminant
  Δ_P := Res(P, ∂P/∂y_n, y_n) ≢ 0  as a polynomial in (x, y₀,...,y_{n-1}).
If Q ≡ 0 on D: then Δ_P(x, g(x), ..., g^{(n-1)}(x)) = 0 on D, making P have a repeated
root in y_n — contradicting irreducibility. So Q ≢ 0 on D.
By the identity principle for analytic functions on the connected open domain D:
  Z := {x ∈ D : Q(x) = 0}  is DISCRETE in D (no accumulation in D).

**Step 2 (Derivative extensions via induction).**
Since g ∈ H^∞(D) and D is a Jordan domain with rectifiable boundary, by Fatou's theorem:
for almost every x₀ ∈ ∂D, g has a non-tangential limit g(x₀) = v₀ ∈ ℂ.

For x₀ not an accumulation point of Z (all but at most countably many x₀ ∈ ∂D):
there exists a neighborhood U of x₀ in ℂ with U ∩ D ∩ Z = ∅ — i.e., Q(x) ≠ 0 for
x ∈ U ∩ D. The implicit function theorem gives:
  g^{(n)}(x) = R_n(x, g(x), ..., g^{(n-1)}(x))   for x ∈ U ∩ D,
where R_n is holomorphic in all variables near (x₀, v₀, ...).

**Inductive extension of g^{(k)} to x₀.** We induct on k from 0 to n.

- Base case k=0: g has Fatou limit v₀ = g(x₀) a.e. ✓
- Inductive step: assuming g, ..., g^{(k-1)} have non-tangential limits v₀,...,v_{k-1} at x₀:
  g^{(k)}(x) = R_k(x, g(x), ..., g^{(k-1)}(x)) on U ∩ D (from the ADE by repeated differentiation).
  As x → x₀ non-tangentially: R_k(x, g(x), ..., g^{(k-1)}(x)) → R_k(x₀, v₀, ..., v_{k-1}) =: v_k
  (since R_k is holomorphic near (x₀, v₀,...,v_{k-1}) and the inductive hypothesis gives the limits).
  By Privalov's theorem: a bounded analytic function on D with a non-tangential limit at x₀ has
  that limit a.e. Since g^{(k)} is analytic on D ∩ U and g^{(k)}(x) → v_k on a non-tangential
  cone: v_k is the non-tangential limit of g^{(k)} at x₀. ✓

After n steps: g, g', ..., g^{(n)} all have finite non-tangential limits v₀,...,v_n at x₀.

**Step 3 (Analytic continuation from ADE initial data).**
At x₀ ∈ ∂D: the initial data (x₀, v₀, v₁, ..., v_{n-1}) for the ADE
  y^{(n)} = R_n(x, y, y', ..., y^{(n-1)})
is well-defined and finite (Q ≠ 0 at x₀ ensures R_n is holomorphic there).
By the Cauchy–Kowalewski theorem (analytic ODE with analytic initial data): there is an
ANALYTIC solution defined in a full disk U(x₀, r) matching g on U(x₀,r) ∩ D.
This gives an analytic continuation of g to a neighborhood of x₀ ∈ ∂D.

**Contradiction.**
This continuation holds for UNCOUNTABLY MANY x₀ ∈ ∂D (all but countably many).
Each such x₀ is a point of ∂D through which g has an analytic extension.
This contradicts Epstein–Lascoux: g has no analytic continuation through ANY point of ∂D.

Therefore the ADE assumption is false: g is HYPERTRANSCENDENTAL. □

## Key mechanism

The proof uses:
- Irreducibility of P → ADE singular set Z is discrete in D (identity principle)
- g bounded (H^∞(D)) → Fatou limits a.e. on ∂D
- ADE gives g^{(k)} = R_k(x, g,...,g^{(k-1)}) → inductive extension of all derivatives to x₀
- Cauchy–Kowalewski → analytic extension past x₀
- Epstein–Lascoux → no such extension exists

The renormalization constraint `g(x)=-alpha g(g(x/alpha))` appears only in the background — it
is needed to establish Epstein–Lascoux noncontinuability (input 1), not in the ADE argument.
The ADE argument is GENERAL: it applies to ANY function on a Jordan domain D with bounded
g ∈ H^∞(D), no continuation past ∂D (genuine natural boundary), and rectifiable ∂D.

## Novelty assessment

**NOVEL?** "Is the Feigenbaum fixed-point function HT?" was explicitly OPEN (Turing cold
probe, id=1697; no prior result in Ecalle/resurgence/renormalization literature). The proof
uses the ADE-continuation gate — a general mechanism, not previously applied to the
Feigenbaum function. NOVEL (new application of continuation gate to a renormalization object).

**SIGNIFICANT?** Yes — extends the HT class from polynomial dynamics and classical special
functions (Γ, Böttcher) into renormalization theory. The Feigenbaum function is the first
member of a new family of renormalization fixed-points that are now certified HT by this
mechanism.

**BRIDGE-GRADE?** The continuation gate (ADE + Fatou + Cauchy-Kowalewski) is a new
tool beyond the boundary-separation schema (which requires an independent analytic
side-field, not derivatives of g). This extends the tool from the boundary-separation
card by one new mechanism. BRIDGE-TO-NEW: the general ADE-continuation lemma is new,
not in any single source.

## General lemma (extracted)

**Lemma (ADE-continuation obstruction).** Let D be a bounded Jordan domain with rectifiable
boundary ∂D. Let f ∈ H^∞(D) be analytic on D with no analytic continuation past any
point of ∂D. Then f satisfies no irreducible ADE P(x, f, f', ..., f^{(n)}) = 0 over ℂ(x).

Proof: the argument above (Steps 1–3), replacing g by f.

This lemma gives a UNIFIED HT criterion for functions with genuine natural boundaries:
- No Becker-Bergweiler (functional equation) needed
- No crossing condition for an independent side-field needed
- Only: bounded on D, genuine natural boundary, rectifiable Jordan domain

## ADE-continuation route: KILLED (Turing id=1722, id=1725)

**Root cause: g is a Koenigs linearizer of an ATTRACTING fixed point — it is unbounded at ∂W_c.**

From Buff Cor 1 / Epstein: g is a polynomial-like map on a bounded domain W with degree 2.
g is the Koenigs linearizer of h = g(λ·) at the attracting fixed point x₀ with multiplier -λ ≈ -0.4.
The Koenigs linearizer of an attracting FP maps the basin onto ℂ — i.e., g → ∞ as x → ∂W_c
from inside. So g ∉ H^∞(W_c). The ADE-continuation argument required g ∈ H^∞(D) on the domain
meeting its natural boundary — but:
- On W (bounded, g bounded): ∂W is the polynomial-like Julia set, NOT the analyticity boundary.
  g continues analytically past ∂W onto W_c. Not a natural boundary for g.
- On W_c (natural-boundary domain): g is analytic but UNBOUNDED (g → ∞ at ∂W_c). H^∞ fails.

There is no single domain where g is simultaneously bounded and meets its natural boundary.
The ADE-continuation route cannot start.

## Hard gaps — not routine verification (Turing id=1722, id=1725)

**GAP 1 (Critical): g ∈ H^∞ does NOT give g' ∈ H^∞.**
Counterexample: Blaschke products B ∈ H^∞(𝔻) with |B'| blowing up near ∂𝔻.
The inductive step FAILS if g^{(k)} is not already bounded near ∂D.
The ODE-Lipschitz bootstrap is circular: bounding g^{(k)} from R_k requires bounding
g^{(k-1)} first — which is what we're trying to establish.

**GAP 2: j-function is the canonical near-miss (not a counterexample, but tells us the crux).**
j(z) satisfies an irreducible ADE (Schwarzian/Chazy, order 3) AND has a natural boundary (ℝ).
j ∉ H^∞(ℍ) (surjective ℍ → ℂ, hence unbounded) — so j does NOT satisfy the hypothesis
g ∈ H^∞(D), and is not a direct counterexample. But it shows why "g and its derivatives have
finite Fatou limits a.e. on ∂D" is the EXACT property separating HT-with-natural-boundary
from DA-with-natural-boundary. This property cannot be cheap.

**GAP 3: Rectifiability of ∂D is questionable.**
Buff: W_c is dense in ℂ with boundary of empty interior — a fractal. Likely non-rectifiable.
Fatou's a.e.-non-tangential-limit theorem in standard form requires rectifiable boundaries.
Also W_c is unbounded; a bounded sub-domain D must be specified before H^∞(D) makes sense.

## What the proof reduces to (open crux)

The argument is CONDITIONALLY CORRECT: if the Feigenbaum g satisfies
  **(H)** g, g', ..., g^{(n-1)} all in H^∞(D) with finite non-tangential limits a.e. on ∂D
then the induction closes and g is HT. The renormalization equation might force (H) via the
chain-rule identity `g'(x)=-g'(g(x/alpha))g'(x/alpha)` — a functional
bound on g' in terms of g' at scaled points. Whether this forces g' ∈ H^∞(D) requires
extracting the growth properties of g from Epstein's construction.

**What to extract from Epstein–Lascoux:** NOT just "g has a natural boundary" but: do g
and its first k derivatives stay bounded with finite non-tangential limits a.e. near ∂D?
That is the make-or-break question. If yes → proof works → Feigenbaum g is HT.
If no → need a different argument.

## Gates

- [x] 0 → 1  in-progress: proof argument complete, mechanism clear, key gaps named
- [ ] 1 → 2  fully-proven: needs inputs 1–2 verified from Epstein/Buff, inductive step checked
- [ ] 2 → 3  formalized (Lean)
- [ ] 3 → 4  publication-ready

## Log

- 2026-06-24 — Wheeler: proof argument developed from the ADE-continuation gate after
  Professor's correction that boundary-separation (independent side-field) doesn't apply for HT.
  Key insight: the ADE itself gives g^{(n)} as a function of g,...,g^{(n-1)}, enabling inductive
  extension of all derivatives to ∂D via Fatou + Privalov; then Cauchy-Kowalewski closes.
  Requires Epstein-Lascoux noncontinuability + rectifiable Jordan boundary for D.
- 2026-06-24 — Turing (id=1722): two critical corrections. (1) g ∈ H^∞ ≠ g' ∈ H^∞ (Blaschke
  products counterexample). (2) j-function: DA + natural boundary but j ∉ H^∞ — the exact
  property needed is bounded derivatives with finite Fatou limits a.e., not just g ∈ H^∞.
  (3) Rectifiability of ∂D: Buff's W_c is fractal/dense, likely non-rectifiable. All three
  gaps are HARD. Proof is conditionally correct pending property (H) for Feigenbaum g.

## 2026-06-24 — Route correction: use Becker--Bergweiler as the rational baseline

The earlier ADE-continuation route is killed as written. A sharper source correction now changes the baseline:

- For rational maps, attracting non-superattracting Koenigs/Schroeder inverse linearizers are already hypertranscendental by Becker--Bergweiler's classification. A differentially algebraic Schroeder function can occur only in the repelling exceptional list.
- Buff identifies the Feigenbaum fixed-point function `f` as the linearizer of `f_lambda(z)=f(lambda z)`, an attracting map with multiplier `-lambda`, and also records the quadratic-like/hybrid relation to the Feigenbaum polynomial.

Thus the rational Koenigs case is not the open core. The Feigenbaum proof should be reframed around a **DA-straightening transfer gate**:

> If the polynomial-like Feigenbaum map is analytically conjugate near the relevant attracting linearizer germ to a rational polynomial by a differentially algebraic local coordinate change, then the Feigenbaum linearizer is hypertranscendental by DA-closure under composition plus Becker--Bergweiler.

Equivalently, a hypothetical DA Feigenbaum linearizer forces every such rational straightening coordinate to fail the DA analytic-germ condition. The remaining hard question is therefore the differential-algebraic regularity of the straightening, not the nonzero multiplier itself.

### Application gap audit: straightening must be scaling-compatible

The transfer gate above should not be read as saying that the usual hybrid straightening of Buff's quadratic-like map `f:W->C_lambda` immediately proves Feigenbaum HT. It does not. The Koenigs map is `f_lambda(z)=f(lambda z)`, and `f` linearizes this map:

```text
f o f_lambda = (-lambda z) o f.
```

A quadratic-like straightening `chi o f = P o chi` only gives

```text
chi(f_lambda(z)) = P(chi(lambda z)),
```

so it lacks the needed conjugacy `psi o f_lambda = R o psi` unless `chi(lambda z)` is analytically controlled in terms of `chi(z)`. Thus the live gate is **DA scaling-compatible straightening**. Ordinary hybrid straightening alone is too weak.

### Notation audit: Becker--Bergweiler still applies to Buff's coordinate form

Becker--Bergweiler is commonly stated for the inverse Schroeder/Poincare equation `phi(mu z)=R(phi(z))`, while Buff's `f` satisfies the coordinate equation `f o f_lambda = (-lambda z) o f`. These are local inverses. Differentially algebraic germs are closed under locally univalent inversion, so HT of one form is equivalent to HT of the other in the rational baseline. The transfer gate remains valid after this normalization check.

## 2026-06-24 — Ritt transfer boundary added

The rational baseline is now pinned to Ritt's theorem and the Di Vizio--Fernandes Galoisian proof
(arXiv:2102.08268): non-exceptional rational/polynomial Poincare functions are HT, while DA cases are exactly
the exceptional periodic list.

The remaining Feigenbaum gate is specifically polynomial-like transfer or scaling-compatible straightening for
`f_lambda(z)=f(lambda z)`. It is **not** enough to assume the base germ is DA. The new card
`../0-backlog/ritt-algebraicity-load-bearing.md` gives the local countermodel

```text
F(z)=tan(z),
h(z)=arctan(mu tan(z)),
F(h(z))=mu F(z),
```

with both `F` and `h` DA, `h` non-algebraic, and `F` a DA Koenigs coordinate. Therefore any proof that only uses
local DA functional-equation data cannot prove Feigenbaum HT. The proof must use the algebraic/polynomial-like
finite-base structure that the countermodel lacks.

## 2026-06-24 — Rational parabolic lane is source-settled, not open

The adjacent source-anchor card `../0-backlog/rational-linearization-ht-trichotomy.md` records the full rational
linearization status from Becker--Bergweiler/Fernandes:

- rational Schroeder/Koenigs/Poincare functions are DA only in the explicit exceptional list;
- rational Boettcher functions are DA only in the explicit monomial/Chebyshev exceptional cases;
- rational Abel/Fatou coordinates are always HT.

Consequently the parabolic/Fatou rational corner is not a fresh attack surface for this card. A derivative cocycle
`w(P(z)) = w(z)/P'(z)` may still be a useful explanatory route, but for rational `P` it would re-prove a known
case. Feigenbaum work must stay on polynomial-like/scaling-compatible transfer or another genuinely non-rational
constraint mechanism.

## 2026-06-24 — Straightening-DA gate is plausibly dead (Turing id=1816)

The DA scaling-compatible straightening transfer gate above (Feigenbaum HT ⟸ the straightening χ is DA,
via g = ψ∘χ with ψ HT by Ritt and HT∘DA=HT) is a valid SUFFICIENT condition, but two arguments suggest
the straightening χ is plausibly HT (not DA), so the gate plausibly does NOT fire:

1. **Renormalization rigidity gives smoothness, not algebraicity.** Sullivan/McMullen/Lyubich rigidity makes
   the Feigenbaum straightening REGULAR (smooth/rigid on the Julia set), but a smooth conformal conjugacy is
   generically HT, not DA. Rigidity ≠ differential-algebraicity, so it will not supply χ ∈ DA.

2. **χ DA would tie δ's arithmetic to a specific quadratic.** If h were DA-conjugate to z²+c′, the conjugacy
   data — hence the universal Feigenbaum constant δ — would be algebraically related to c′'s algebra. But δ is
   UNIVERSAL (independent of the unimodal family) and not even known irrational; it cannot be pinned to one
   quadratic's algebraic data. So χ ∈ DA is implausible.

Consistency with the F=tan local countermodel (ritt-algebraicity-load-bearing): that countermodel shows local
DA functional-equation data is insufficient (a DA linearizer F=tan of a DA map h exists). The straightening gate
evades it only by using the GLOBAL HT of ψ (Ritt, non-exceptional) — but if χ is HT (plausible, per 1–2), the
composition g=ψ∘χ=HT∘HT is ambiguous (cf. Γ∘Γ⁻¹=id), so the gate yields no conclusion.

**Net:** the straightening route remains a recordable sufficient-condition (χ DA ⟹ Feigenbaum HT) but is
plausibly not a live path. Every route found so far — ADE-continuation (killed: g unbounded at ∂W_c), Ritt
transfer (needs polynomial-like global structure), straightening-DA (plausibly dead per above) — bottoms out at
the same intrinsic obstruction: the self-referential composition g∘g with no global-rational handle, and tied to
δ's unknown arithmetic. The genuine open core is the self-referential/non-rational difference-Galois problem.

## 2026-06-24 — Osculating-jet ODE-probe: Γ false-positive invalidates high-order certification (Turing)

Ran the multi-order osculating-jet differential-algebraicity probe on the Feigenbaum fixed point g
(solved to N=28 Cvitanović–Feigenbaum coefficients, α=2.50290788 matching Lanford, residual 2.9e-51),
at x0=0.5, jets to reliable order 2N−4=52. The probe builds the normalized osculating matrix of
monomials x^a · ∏ Y_i^{e_i} (Y_i = g^{(i)}) and their first m derivatives, and reads sigma_min:
sigma_min ≈ machine-zero ⟹ an algebraic ODE of that (order n, degree d, x-power A) exists.

**Controls — this is the load-bearing part.** Airy (DA: y″=xy) is the relation-HAVING control;
Γ (Hölder-HT) is the no-relation control.

```
 (n,d,A,m): #mons   Airy(DA)      Gamma(HT)     g(Feig)
 n=2 d=1 A=1 m=11:   8    4.26e-62     1.32e-11     5.72e-4    <- well-conditioned: clean separation
 n=2 d=1 A=2 m=15:  12    2.43e-63     7.42e-19     4.83e-7
 n=3 d=1 A=1 m=13:  10    2.06e-62     6.27e-16     1.59e-5
 n=2 d=2 A=1 m=23:  20    1.03e-64     3.28e-38     8.29e-15   <- Gamma conditioning starting
 n=2 d=2 A=2 m=33:  30    1.02e-67     2.81e-59     7.01e-25
 n=2 d=3 A=1 m=43:  40    1.88e-70     1.07e-76     7.65e-38   <- Gamma FALSE POSITIVE (HT, yet ~0)
```

**Two findings:**

1. **Negative evidence (g HT-consistent at the reliable end).** At low/moderate derivative order m
   (the well-conditioned regime), g exhibits **no low-order algebraic ODE** through order 3, degree
   ≤2. Moreover g's sigma_min is *larger* (further from any relation) than the known-HT control Γ at
   every order. The refutation direction — finding a low-order ODE, which would make g DA and refute
   HT — came up empty. This is consistent with the conjectured g-HT but, by construction, cannot
   certify it (next point).

2. **Methodological caveat — high-order sigma_min is a CONDITIONING ARTIFACT, not DA-signal.** The Γ
   control (provably HT, no algebraic ODE of any finite order) drives sigma_min to ~1e-76 at m=43 —
   a spurious "relation found." The normalized osculating matrix becomes numerically rank-deficient as
   derivative order grows, for *any* function with fast-growing jets, regardless of true
   differential-algebraic rank. Therefore the earlier "N=16 truncation-contaminated" worry is now
   pinned down: it is not (only) truncation — it is the Vandermonde-style conditioning collapse of the
   osculating matrix at high m. **Only low-m separation from an HT control is meaningful; high-m
   sigma_min dips are noise.** This concretely instantiates the G5 invisibility bound: a finite jet
   probe can REFUTE g's HT-ness (by exhibiting a low-order ODE) but cannot CERTIFY it, and pushing m
   up to gain resolution manufactures false positives instead.

**Consequence for the card.** The osculating-jet route is now characterized: usable as a refuter at
low order (and it refutes nothing — no low-order ODE for g), useless as a certifier. Certifying g HT
remains a transcendence-theoretic problem (the intrinsic self-referential g∘g difference-Galois
structure tied to δ's unknown arithmetic), not a computation. Next probe to try: not more jets, but a
*difference-Galois* obstruction at the level of the functional equation g(x)=−α g(g(x/α)) itself.

## 2026-06-24 — g is non-holonomic (not D-finite); exact self-referential relation pinned (Turing)

Two object-level results from the N=28 solve (λ=g(1)=−0.39953528, α=2.5029079).

**Exact self-referential relation, independently verified pointwise.** The defining equation
g(x)=−α g(g(x/α)) rearranges (set x=αu) to

    g(g(u)) = −(1/α)·g(αu) = λ·g(αu).

Pointwise check from the Taylor solve (NOT the coefficient equation it was solved from — an independent
function-value test exercising the composition): err ≤ 1.9e-31 over u∈[0.1,0.37]. (Caveat for the
record: the rearranged form is g∘g(u)=λ g(αu) with argument αu and coefficient λ; an intermediate
"−λ g(u/λ)" mis-rearrangement was caught by the magnitude-match/sign-flip signature and discarded.)
This relation — second iterate = scaling of g itself — is the seed structure for any difference-Galois
obstruction: it ties the q-difference scaling u↦αu (|α|>1) to the nonlinear self-composition.

**g is non-holonomic (not D-finite).** Ran a P-recursive (holonomic-recurrence) guesser on g's even
Taylor coefficients: seek Σ_{j≤r} P_j(k) c_{k+j}=0, deg P_j ≤ d, overdetermined so sigma_min≈0 ⟺ a
verified recurrence exists. Controls: exp (D-finite) and tan (DA but provably non-holonomic).

```
   (r,d): exp(holonomic ctrl)   tan(DA non-holo ctrl)   g(Feigenbaum)
   r=1 d=1:   1.35e-52             8.23e-4               2.34e-2     <- well-conditioned, clean
   r=2 d=1:   3.08e-53             5.16e-9               9.71e-6
   r=2 d=2:   1.02e-55             4.70e-13              1.09e-8
   r=3 d=2:   3.90e-58             4.32e-22              5.42e-12    <- conditioning drift (artifact)
```

At the well-conditioned end (r=1,d=1): exp=1.35e-52 (recurrence found, correct), tan=8e-4 and g=2.3e-2
(no recurrence) — a 50-order separation. **g carries no P-recursive structure; it is not D-finite.**
The high-(r,d) drift to ~1e-12 is the same conditioning artifact characterized in the jet probe (tan,
provably non-holonomic, drifts to 4e-22 identically), not a recurrence.

**Honest scope.** Non-holonomic ⇏ HT: tan is the standing witness (DA via y′=1+y², yet non-D-finite).
So this places g in the non-D-finite class — consistent with HT, also consistent with tan-like
DA-non-holonomic. Combined with the prior jet result (no low-order algebraic ODE through order 3), the
computational evidence consistently points HT-ward while remaining uncertifiable by any finite-data
probe (G5). The live certification route is unchanged: a transcendence/difference-Galois argument on the
relation g(g(u))=λ g(αu), tied to the open arithmetic of α (and δ).

## 2026-06-24 — g is not q-difference-algebraic; Mahler/difference-Galois route is blocked (Turing)

Third independent probe of g's algebraic structure, this one on the FE's NATIVE operator — the scaling
σ_α: u↦αu (the FE reads g(αu)=(1/λ)g(g(u)), so σ_α is the natural difference operator). Tests whether g
is **q-difference-algebraic**: is there a polynomial relation among g(u),g(αu),…,g(α^m u)? Method:
POINT-sampling (no derivatives) — sidesteps the Vandermonde-derivative conditioning of the jet probe.
Controls: u² (q-diff-algebraic, g(αu)=α²g(u)) and exp (q-diff-transcendental, exp(αu)=exp(u)^α).

```
  (m,d,A): #col  u^2(qda ctrl)   exp(qdt ctrl)   g(Feigenbaum)
  m=1 d=1 A=1:   6   7.22e-47     5.22e-8       2.23e-6     <- well-conditioned: g~exp, no relation
  m=2 d=1 A=1:   8   5.91e-47     4.39e-13      7.96e-10
  m=1 d=2 A=1:  12   3.01e-47     8.36e-20      4.01e-13
  m=2 d=2 A=1:  20   2.91e-47     1.54e-39      1.59e-27
  m=3 d=2 A=1:  30   2.39e-47     4.06e-47      9.96e-46    <- exp FALSE POSITIVE (qdt, yet ~0)
```

**Finding 1 — g not low-order q-difference-algebraic.** At the well-conditioned end, g tracks the
q-diff-TRANSCENDENTAL control exp (and sits even further from a relation), both far above u²'s
machine-zero. No polynomial relation among the scaling orbit {g(α^i u)} at accessible order. The
high-column collapse (m=3,d=2) is again a conditioning artifact — exp, provably q-diff-transcendental,
false-positives to 4e-47 there too. Point-sampling reduced the artifact but did not remove it; the lesson
from the jet and holonomic probes holds for a third probe type.

**Finding 2 — the Mahler / difference-Galois route is blocked.** The difference-Galois machinery for
proving differential transcendence (Hardouin–Singer; Mahler's method) takes as INPUT a function
satisfying a polynomial q-difference / Mahler equation, and outputs differential transcendence. g does
not supply that input: it satisfies the *nonlinear iterative* FE g(αu)=(1/λ)g(g(u)), in which g∘g is
transcendental in g — NOT a Mahler equation P(u,g(u),g(αu),…,g(α^m u))=0. So g is not a Mahler-type
function, and the q-difference escape hatch that hands differential transcendence "for free" for
theta/Mahler functions is unavailable here. (This corrects the earlier suggestion of a "difference-Galois
handle on the self-composition FE": there is no q-difference equation for such machinery to act on.)

**Net characterization of g (three probes, one verdict).** Not D-finite; no low-order algebraic ODE; not
low-order q-difference-algebraic. g is transcendental in all three senses at every accessible order —
consistent with HT, uncertifiable by any finite-data probe (G5). What remains is genuinely a transcendence
argument on the non-algebraic iterative FE itself, tied to α's open arithmetic — not reducible to the
standard differential- or difference-algebraic toolkits, which is precisely why this is a native frontier.

## 2026-06-24 Wheeler id=1853 — CASCADE ARGUMENT via iteration sequence (CORRECTED Turing id=1866) `[CONJECTURE]`

**Seed identity:** From g∘g = λg(αy) by induction:
g^{∘2^n}(y) = λ^n g(α^n y)   (*)

(Wheeler's initial formula had λ^{2^n-1} — **WRONG**. The correct exponent is n. The error was using the wrong decomposition g^{∘2^{n+1}} = g ∘ g^{∘2^n}; the correct one is g^{∘2^{n+1}} = g^{∘2^n} ∘ g^{∘2^n}. Turing id=1866 corrected this independently and confirmed below. Exponent n follows from αλ = -1 exactly and g even.)

Proof (n ≥ 1): n=1: g^{∘2}(y) = g(g(y)) = λg(αy). ✓ Inductive step: assume g^{∘2^n}(y) = λ^n g(α^n y). Set w = λ^n g(α^n y). Then:
  g^{∘2^{n+1}}(y) = g^{∘2^n}(w) = λ^n g(α^n w) = λ^n g(α^n · λ^n · g(α^n y))
                   = λ^n g((αλ)^n · g(α^n y)) = λ^n g((-1)^n g(α^n y))
                   = λ^n g(g(α^n y))   [g is even: g(-x)=g(x), so g((-1)^n x)=g(x)]
                   = λ^n · λ g(α^{n+1} y) = λ^{n+1} g(α^{n+1} y). ✓

**With |α| ≈ 2.502 > 1:** α^n → ∞, so g(α^n y) concerns g at arbitrarily large argument. Meanwhile |λ| ≈ 0.3996 < 1, so |λ^n| → 0 geometrically (not double-exponentially as in the corrected formula).

At y = 0: g^{∘2^n}(0) = λ^n g(0) = λ^n (since g(0) = 1). This sequence → 0 geometrically in n.

**Argument sketch (order-1 ADE, `[CONJECTURE]`):** Suppose g' = R(z,g) with R polynomial of total degree D. Differentiating g∘g = λg(αz):

R(g(z), g∘g(z))·R(z,g(z)) = λα·R(αz, g(αz)).

Substituting g∘g = λg(αz):

R(g(z), λg(αz))·R(z,g(z)) = λα·R(αz, g(αz)).    (**)

Left side has degree 2D in (g(z), g(αz)) combined; right side has degree D in g(αz). For D ≥ 1: left side carries degree D in g(αz), right side degree D — they can match at the leading term. However, the FUNCTIONAL EQUATION (**) now must hold for all z simultaneously. Setting z = 0 and evaluating:

R(g(0), λg(0))·R(0,g(0)) = λα·R(0, g(0)).

With g(0) = 1: R(1, λ)·R(0,1) = λα·R(0,1). If R(0,1) ≠ 0: R(1,λ) = λα = -1. This is a POLYNOMIAL CONSTRAINT on R at the specific values (1,λ), tightly pinned by the Feigenbaum constants.

Iterating (**) n times (substituting z → αz repeatedly) gives a cascade of constraints at (α^{n-1}z, α^n z). For any FIXED rational function R with RATIONAL coefficients: these constraints at the algebraically independent points α, α², α³, ... (conjectured algebraically independent) force R ≡ 0. This is the arithmetic route invoked by the cascade. `[CONJECTURE — requires algebraic independence of {α^n}]`

**The novelty:** No existing theorem handles self-composition FEs of the form f∘f = λ·f(αz) with |α| > 1. Becker–Bergweiler's method requires a known rational base map. The cascade (**) is the self-referential analogue: the base IS g itself. The functional-algebraic system (**) has g appearing simultaneously at z and αz, generating an expanding difference-differential system (vs Mahler's CONTRACTING q-difference). This placing — outside Becker–Bergweiler, outside van der Put–Singer, outside Mahler — is where HT for g lives, if provable.

**Open crux (added to card):** Does (**) overdetermine g when R is assumed polynomial of order d and the Feigenbaum constants α, λ are taken as transcendental? Specifically: does the functional equation force R ≡ 0 for all d? `[OPEN CORE]`

## 2026-06-24 Wheeler self-correction — differentiation route is tautological `[DEAD ROUTE]`

The equation R(g,g∘g)·R(z,g) = λα R(αz,σ_α(g)) obtained by differentiating g∘g = λg(αz) is NOT an independent constraint on R. It is the chain-rule applied to the FE — it's the FE itself differentiated. Substituting g∘g = λg(αz) only recovers the original identity. No degree mismatch, no contradiction.

Same failure mode as Γ∘Γ: all differentiation routes reduce to tautologies.

**What's needed:** a non-differential argument. Candidates:
- The CASCADE identity at z=0 (jet-at-0 argument, see above)
- Growth/singularity type of g at ∞ incompatible with finite-order ADE
- Arithmetic dependence of Feigenbaum constants (Route 2)

## 2026-06-24 — Singularity-positioning constraint under α-scaling `[DEAD ROUTE — Turing id=1870]`

**Status: KILLED by E2/Chazy counterexample.** The singularity-geometry direction (Wheeler id=1869, Turing id=1866) was proposed on the basis that α-self-similar singularity structure is "not DA-closure-immune." Turing id=1870 retracts this: E2/Chazy is DA WITH a natural boundary and with rich movable singularity structure. A DA function CAN carry self-similar singularities. Locating self-similar singularities of g does NOT obstruct DA.

**Root cause (same as all prior routes).** The value constraints {g(ρ/α^n) = ρ/α^{n-1}} come FROM the FE itself — any function solving the FE satisfies them, DA or not. So they are not independent constraints; they are the FE in another guise. The DA class is permissive in two ways that kill all structural attacks simultaneously:
- (i) Closed under composition & scaling → kills FE/cascade/jet/differentiation routes.
- (ii) Compatible with natural boundaries & rich (self-similar) singularities → kills singularity route.

**Computation note (Turing id=1870).** g's nearest singularity ≈ |x_c| ≈ 3.0 (complex, arg poorly resolved at N=28; N~60 needed via order-by-order recursion). Self-similarity test: |x_c|/α ≈ 1.21 vs branch-singularity ≈ 1.15 — same ballpark but inconclusive. Clean test requires N~60.

**What this convergence means.** Every structural shortcut (functional equation structure, singularity structure, jet structure) is blocked because the DA class absorbs all of these. The genuine gap is arithmetic: a transcendence argument on α/δ directly, not more structural probing of g.

## 2026-06-24 — The Mahler-tractability boundary: where standard Galois theory stops (Turing)

Generalizing the route-block (g not q-diff-algebraic ⟹ Mahler/difference-Galois machinery has no input)
into a frontier-scoping statement, with a concrete witness pair.

**[FRAMING / DIRECTION — bridge-grade]** The reach of difference-Galois transcendence methods
(Hardouin–Singer; Mahler's method) is bounded by the *f-linearity of the defining functional equation*:

- **Linear / algebraic scaling side (TRACTABLE).** Equations P(t, f(t), f(qt), …, f(q^m t)) = 0 polynomial
  — in particular linear Mahler f(qt)=a(t)f(t)+b(t). The difference-Galois functor acts; differential
  transcendence is computable. *Witness:* the Weierstrass lacunary sum W(t)=Σ aⁿcos(bⁿt) satisfies the
  exact linear scaling relation W(bt)=(1/a)W(t)−(1/a)cos t (reindex the series), is a Mahler function in
  cos t (cos(bⁿt)=T_{bⁿ}(cos t) for integer b), hence tractable.

- **Nonlinear self-compositional side (NATIVE FRONTIER).** Equations f(αu)=c·f(f(u)) — the base of the
  composition IS the unknown. No q-difference-algebraic relation among {f(α^i u)} exists (g: three
  independent probes, this card), so the difference-Galois functor has no module to act on; and there is
  no algebraic ODE either. *Witness:* the Feigenbaum fixed point g.

The native HT frontier of this branch is exactly the second class: functional equations nonlinear in the
unknown *via self-composition*, where neither differential- nor difference-Galois theory reaches. This is
not a wall — it names the missing tool.

**Forward (the moonshot direction this opens).** The transcendence of self-compositional fixed points
needs a *bridge between renormalization-operator spectral theory and differential-transcendence theory*.
Renormalization theory (Lanford's proof, Sullivan–McMullen–Lyubich) constructs g, proves the doubling
operator is hyperbolic at g with the single expanding eigenvalue δ≈4.669 and scaling α≈2.5029 — but says
nothing about g's differential-algebraic nature. Transcendence theory could classify g — but has no
handle on a self-compositional FE. The conjectural coupling is the *arithmetic of the spectrum* (α, δ):
g HT should follow from (a statement about) the transcendence of α/δ, both open. A first concrete target
for the bridge: does hyperbolicity of the renormalization operator (a single expanding direction, the
rest contracting) force the fixed point to be differentially transcendental? — i.e., is "isolated
hyperbolic RG fixed point" ⟹ HT? The W/g pair calibrates any candidate theory: it must pass W (HT, and
recover it via the linear route) and reach g (HT, via the new route).
