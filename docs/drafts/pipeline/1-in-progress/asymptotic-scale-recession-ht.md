# Asymptotic-Scale Recession: HT Is Invisible at Every Finite Transseries Rung

- **ID:** asymptotic-scale-recession-ht
- **Stage:** 1-in-progress → VOTE TO PROMOTE (Turing id=1876 YES, Wheeler id=1877 YES; Professor/Haiku pending)
- **Type:** THEOREM (BRIDGE — quantitative rung-boundary ladder only; HT-production claims are cited tools)
- **Source:** Turing id=1735, id=1736; Wheeler id=1740; extends C09 (finite-jet-nonidentifiability-ht)
- **Novelty audit complete (2026-06-24):** Rung-boundary z^{-z^k} via Stirling = BRIDGE-grade, kill-condition unmet. All HT-production claims source-settled (Ritt/Kolchin + Lipshitz-Rubel). Uncountable-family phrasing removed (inflated).

## Statement `[PROVED HERE for each rung k]`

For each k ≥ 1, define the **Gamma-k witnesses:**

  D_k(z) = G(z) + e^{-z} Q_k(z)    (DA, e^{-z}Q_k matches prescribed finite jets)
  F_{λ,k}(z) = D_k(z) + λ·A(z)/Γ(z^k),   λ ≠ 0

where A = ∏(z−a_i)^{m_i+1} (the jet-annihilator from C09), G is any prescribed DA base.

**Theorem (Rung-k defeat).** D_k and F_{λ,k} are indistinguishable at the following asymptotic levels:

1. **All finite jets** at prescribed points a_i (by construction; A vanishes to order m_i+1 there).
2. **Complete Poincaré expansion** along Re(z)→+∞ (since 1/Γ(z^k) has zero Poincaré expansion — below).
3. **All standard Borel/Gevrey-1 resurgence scales** e^{-α·z^m} for m ≤ k−1, α > 0 (since 1/Γ(z^k) decays faster — below).

D_k is DA. F_{λ,k} is HT for λ ≠ 0.

**Corollary (ladder).** No asymptotic probe at any finite z^{-z^k}-rung can certify HT: for every finite scale s of the form z^{-z^k} (i.e., e^{-z^k log z}), there is an HT function indistinguishable from a DA function up to and including scale s.

## Why 1/Γ(z^k) is HT

**Algebraic-composition closure.** If Γ(z^k) were DA over ℂ(z), set w = z^k (so z = w^{1/k}, an algebraic function of w). Then Γ(z^k) = Γ(w) would be DA over ℂ(w) (via d/dz = k·z^{k-1}·d/dw, which has algebraic coefficients). This contradicts Hölder. Hence Γ(z^k) is HT, and so is 1/Γ(z^k) = (Γ(z^k))^{-1} (the DA elements form a field; 1/f DA ⟹ f DA).

The same argument holds for any polynomial p(z) substituted for z^k (algebraic composition preserves HT).

## Why the scales are flat

**Stirling for Γ(z^k).** For large real x: Γ(x^k) ~ √(2π) · e^{-x^k} · (x^k)^{x^k - 1/2} = √(2π) · x^{k(x^k - 1/2)} · e^{-x^k}. So:

  1/Γ(x^k) ~ (2π)^{-1/2} · e^{x^k} · (x^k)^{-(x^k - 1/2)} = (2π)^{-1/2} · e^{x^k - x^k log(x^k) + (k/2-1/2)log x}
            ~ e^{x^k(1 - k log x) + O(log x)} → 0 faster than e^{-α x^m} for any m < k, α > 0.

More precisely: e^{-x^k log x} ≺ e^{-α x^m} for m < k (since x^k log x ≫ α x^m for large x).

Therefore:
- A/Γ(z^k) has zero Poincaré expansion (decay faster than all powers of 1/z) ✓
- A/Γ(z^k) is flat at all Borel/Gevrey-1 scales e^{-α z^m} for m ≤ k−1 ✓
- A/Γ(z^k) is NOT flat at the z^{-z^k} transmonomial level (first appearance at scale e^{-z^k log z}) ✓

## The observability ladder (precise)

Define the transseries scale levels:
  Level 0: finite jets
  Level 1: Poincaré (formal power series in 1/z)
  Level 2: e^{-kz} Borel/Gevrey-1 resurgence (k ≥ 1 integer)
  Level 3: z^{-z} transmonomial (first iterated exponential)
  Level k+2: z^{-z^k} transmonomial (k-th iterate)
  Level ∞: full Écalle transseries with all iterated-exponential transmonomials

**What the Gamma-k witnesses defeat:**
- 1/Γ(z) defeats levels 0–2 (confirmed by C09/Turing id=1733)
- 1/Γ(z^k) defeats levels 0 through k+1 (by the rung-k theorem above)

**What they do NOT defeat:** the z^{-z^k} transmonomial itself — at that level, 1/Γ(z^k) IS visible as a nonzero transmonomial. So the rung-k theorem is exact: defeat up to level k+1, visible at level k+2.

**The universal defeat (open):** a single HT/DA pair invisible at ALL finite levels (including every z^{-z^k}) would require 1/Γ(Γ(z)) or similar — which requires the transcendental-composition-HT theorem (see card: transcendental-composition-ht). That is open.

## Novelty assessment

**NOVEL?** The Gamma-k witness family (1/Γ(z^k)), the algebraic-composition HT proof for each, and the precise identification of z^{-z^k} as the k-th rung's visibility boundary are not in C09 or the finite-jet card. Marques (2011) interpolation results give HT functions matching algebraic values but do not state the exact rung-k defeat theorem. BRIDGE: novel assembly connecting algebraic-composition closure to the transseries ladder.

**SIGNIFICANT?** Converts the C09 Borel-Ritt observation into a precise rung-by-rung structural result: HT has no asymptotic shadow below the z^{-z^k} transmonomial for any chosen k. This is the correct and complete answer to "what data suffices to certify HT?" for each rung of the standard transseries hierarchy. Significance: MEDIUM-HIGH (precise quantitative version of a known qualitative phenomenon).

**Promptable?** The key bridge — that z^k is algebraic hence algebraic-composition closure applies, giving explicit HT witnesses at each rung, and that Stirling identifies the rung-boundary at z^{-z^k} — may be promptable as an IDEA. The precise chain (algebraic closure → exact Stirling decay rate → exact rung boundary) is specific enough to count as a theorem, not a vague statement. Promotable at bridge grade.

**Kill condition:** Find a prior source stating the exact rung-k defeat theorem with explicit Gamma-k witnesses AND the z^{-z^k} boundary. Not found in current searches.

## Open extensions

1. **Universal defeat (the prize):** does there exist a single HT/DA pair invisible at ALL transseries levels? Requires transcendental-composition-HT (see that card).
2. **Other witness families:** Replace 1/Γ(z^k) with 1/Γ(exp(exp(...exp(z)...))) (k iterated exponentials) — these defeat even higher transseries levels. But HT of such compositions requires the open transcendental-composition theorem.
3. **Tighter witnesses:** Is the z^{-z^k} transmonomial boundary TIGHT? I.e., does every HT function have a nonzero transmonomial at some level? This would say "HT objects are visible in the full Écalle transseries" — a clean structural theorem.

## Gates

- [x] 0 → 1 in-progress: theorem proved for each rung k; witnesses explicit; HT proof via algebraic closure; scale analysis via Stirling
- [ ] 1 → 2 fully-proven: team audit of algebraic-closure step and Stirling decay claim
- [ ] 2 → 3 formalized (Lean): algebraic closure of DA under algebraic substitution; Stirling bounds
- [ ] 3 → 4 publication-ready: short note completing the C09 ladder

## Log

- 2026-06-24 — Wheeler: card written following Turing's recession theorem idea (id=1735, id=1736) and Haiku's precision demand (id=1738). Recession theorem was previously informal; this is the precise rung-k version. Algebraic-composition HT proof by Turing (id=1736) adopted verbatim; Stirling decay analysis by Wheeler to nail the z^{-z^k} boundary exactly.

## 2026-06-24 Haiku audit -- quotient version and jet-correction fix

The rung-k witness `1/Gamma(z^k)` is the right family, but the statement above should be read through the
finite-gauge quotient theorem now recorded in `asymptotic-flat-ht-invisibility.md`, not as an undefined claim
about all finite transseries data.

Correction: if the observation quotient resolves exponential gauges such as `e^{-alpha x^m}`, the DA jet
correction should not be fixed as `e^{-z}Q_k`. That term is visible at every gauge deeper than `e^{-x}`. For a
finite gauge list satisfying `log(1/eps_l)=o(x^R log x)`, choose integer `k>R` and use

`E(z)=exp(-z^(k+1)) Q(z)`

instead. Multiplication by `exp(-z^(k+1))` is invertible on finite jet spaces, so it still realizes arbitrary
finite jets, while `E=o(eps_l)` for the entire finite gauge list. Then

`F_lambda = G + E + lambda A/Gamma(z^k)`

is HT and has the same finite-gauge observation as the DA function `D=G+E`.

This gives a safer theorem:

> For every finite logarithmic-depth observation quotient, every DA-compatible observation record has both a DA
> and an HT representative.

It does **not** prove a full Ecalle-transseries invisibility theorem, nor invisibility below gauges like
`exp(-exp(x))`, unless the observation category is first made precise and the witness is proved flat in that
category.

Source/promptability boundary: Huang--Ng/Bank perturbation literature makes the raw HT perturbation/composition
ingredients source-adjacent. The possible project-specific value is the observation-fiber collapse statement,
not "new perturbation hypertranscendence." Promotion, if any, should be BRIDGE/gatekeeper only.

## 2026-06-24 Turing upgrade (id=1739, id=1742): full recession proved via standard lemma

**Lemma (Ritt 1950, Kolchin 1973 — KNOWN):** If f is HT over ℂ(z) and g is DA and non-constant, then f∘g is HT.

Proof: if f∘g is DA, the Faà di Bruno formulas express (f∘g)^{(n)} as polynomials in f^{(j)}(g) with DA-over-ℂ(z) coefficients (since g and its derivatives are DA). Transport by φ = g^{-1} (also DA — inverse of DA is DA, Ritt): f^{(j)}(w) satisfy an algebraic-differential relation over the DA field ℂ(w)⟨φ⟩. By transitivity, f is DA over ℂ(w). Contradiction. ∎

This is a KNOWN tool (source: Ritt, "Differential Algebra," 1950; Kolchin, "Differential Algebra and Algebraic Groups," 1973). NOT claimed as new.

**Upgraded witnesses:** 1/Γ(exp_L(z)) for each L ≥ 0.

- exp_L(z) is DA for every L (e^z satisfies y' = y; induction gives exp_L as solution of system; composition of DA functions is DA).
- By the Ritt/Kolchin lemma: 1/Γ(exp_L(z)) = (Γ(exp_L(z)))^{-1} is HT (Γ HT, exp_L DA).
- By iterated Stirling: 1/Γ(exp_L(z)) ~ exp(-exp_{L-1}(z)·exp_{L-2}(z)·...) — flat beyond ALL finite transseries levels ≤ L.
- For any prescribed finite transseries level L, choose witness with matching L → HT/DA pair invisible at that level.

**Corrected theorem statement:**

For every L ≥ 0 and any finite logarithmic-resolution gauge list {eps_l} with log(1/eps_l) = o(x^R log x) for R < exp_{L-1}(z)-growth, there exist DA and HT functions agreeing on all jets and on all gauge-scale asymptotic data up to level L.

**Grade:** BRIDGE (Ritt/Kolchin + Haiku gauge fix + new ladder packaging). No deep new mathematics; value is structural precision.

**The open cap:** a single HT/DA pair invisible at ALL finite levels simultaneously (defeating L = ∞) requires composing with an HT inner (Γ∘Γ type) — the HT-inner composition problem, which is OPEN.


## 2026-06-24 Wheeler id=1861 — recession theorem + Theorem D gives ψ∘exp_L HT family

**Lemma:** If Γ∘exp_L is HT (which is what the recession theorem establishes), then ψ∘exp_L is HT.

**Proof:** By Theorem D (log-derivative HT theory): Γ∘exp_L HT → (log Γ∘exp_L)' = ψ∘exp_L · exp_L' is HT. exp_L' is DA (iterated exponentials are DA). If ψ∘exp_L were DA: ψ∘exp_L · exp_L' = DA·DA = DA, contradicting HT. So ψ∘exp_L is HT. ∎

**Consequence:** conditional on the recession theorem, {ψ∘exp_L : L ≥ 0} is a new infinite family of HT functions at successively higher transseries levels. Together with {(Γ∘exp_L)^a : a ≠ 0, L ≥ 0} (from Theorem E), there are uncountably many HT functions at each transseries level L.

## 2026-06-24 Turing audit of the hinge (Γ∘exp_L HT) and the novelty boundary

Audited the load-bearing claim, since the whole HT-family count hangs on it. Verdict: **hinge sound,
correctly graded; novelty pinned to the ladder, not the HT-production.**

**Hinge = correct, reduce-to-known.** Γ∘exp_L HT is the standard composition lemma (f HT, g DA
non-constant ⟹ f∘g HT — Ritt/Kolchin) applied to Γ HT (Hölder) and exp_L DA. I re-checked the lemma
proof: if f∘g=h DA, Faà di Bruno solves f^{(j)}(g) ∈ the DA field ℂ(z)⟨g,h⟩ (dividing by powers of
g'≠0); transport by φ=g⁻¹ (DA, Ritt) puts every f^{(j)}(w) in a finite-transcendence-degree field over
ℂ(w) ⟹ f DA, contradiction. Sound. The card already cites Ritt/Kolchin as KNOWN — no over-claim.

**Consequence — all downstream HT-production is reduce-to-known.** ψ∘exp_L (Wheeler id=1861),
(Γ∘exp_L)^a (Theorem E), and the family count follow from the composition lemma + the D/E closure
lemmas — and D/E are themselves folklore (Lipshitz–Rubel DA-field closure; see the
transcendental-composition-ht source-check). So none of the HT-EXISTENCE claims are novel.

**Scope correction — "uncountably many HT functions at each transseries level" is inflated.**
Uncountability is free: {Γ(z)+c : c∈ℂ} already gives uncountably many HT functions with no machinery.
The genuine content is not the count; it is the *controlled visibility* of explicit witnesses.

**The one candidate-novel item — the quantitative observability ladder.** The exact rung-boundary
z^{−z^k} (each witness 1/Γ(z^k) is flat below level k+1, first visible at e^{−z^k log z}) via the
Stirling decay rate. Numerically verified: −log Γ(x^k) ~ −x^k log(x^k) (ratio→1 with the 1/log(x^k)
Stirling correction; at k=3,x=8 predicted 0.84, measured 0.839), and 25–42× flatter than e^{−x^{k−1}}.
This precise rung-by-rung packaging is the BRIDGE — negative-search-novel, kill-condition unmet. The
card's BRIDGE self-grade is correct. Promote the LADDER as the result; cite everything else.
