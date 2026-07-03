# c8 — Turán power-sum method and a t-aspect Deuring–Heilbronn analogue for ζ?

Verified-reading delegate note. Question: has Turán's power-sum method ever produced a
**t-aspect** clustering/repulsion theorem *for ζ itself* of the shape "one zero of ζ(s) with
Re s near 1 at height t₀ forces OTHER zeros nearby (clustering) or forces a widened zero-free
region elsewhere (repulsion)" — a Deuring–Heilbronn analogue in the t-aspect, proved via power sums?

All quotes below are verbatim from fetched sources (Wikipedia raw wikitext, or `pdftotext -layout`
extraction of the arXiv PDF). pdftotext extraction may carry minor layout/glyph artifacts
(e.g. `6=` for ≠, split fractions); these are flagged where present and do not alter the mathematical
content. Nothing here is from recall.

---

## Item 1 — Turán's First and Second Main Theorems of the power-sum method

### 1a. Classical statements (secondary source: Wikipedia, "Turán's method", raw wikitext)

Source: `https://en.wikipedia.org/wiki/Tur%C3%A1n%27s_method?action=raw` (fetched verbatim wikitext).

**First theorem** (applies when |zₙ| ≥ 1):

> The first result applies to sums ''s''<sub>ν</sub> where <math>|z_n| \ge 1</math> for all&nbsp;''n''.  For any range of ''ν'' of length ''N'', say ''ν''&nbsp;=&nbsp;''M''&nbsp;+&nbsp;1,&nbsp;...,&nbsp;''M''&nbsp;+&nbsp;''N'', there is some ''ν'' with |''s''<sub>''ν''</sub>| at least ''c''(''M'',&nbsp;''N'')|''s''<sub>0</sub>| where
>
> :<math> c(M,N) = \left({ \sum_{k=0}^{N-1} \binom{M+k}{k} 2^k }\right)^{-1} \ . </math>

**Second theorem** (applies when |zₙ| ≤ 1):

> The second result applies to sums ''s''<sub>ν</sub> where <math>|z_n| \le 1</math> for all&nbsp;''n''.  Assume that the ''z'' are ordered in decreasing absolute value and scaled so that |''z''<sub>1</sub>| = 1.  Then there is some ν with
>
> :<math> |s_\nu| \ge 2 \left({ \frac{N}{8e(M+N)} }\right)^N \min_{1\le j\le N} \left\vert{\sum_{n=1}^j b_n }\right\vert \ . </math>

Reading: for s_ν = Σ_{n=1}^N b_n z_n^ν over a window of ν of length N starting after M, the second
main theorem gives the one-sided lower bound
  max_{M<ν≤M+N} |s_ν| ≥ 2·(N/(8e(M+N)))^N · min_{1≤j≤N} |Σ_{n=1}^j b_n|,
under |z_n| ≤ 1, |z_1| = 1. This is the "min-of-partial-sums" one-sided version with explicit
constants requested.

### 1b. A working "new version" with explicit constants (primary source, verbatim PDF)

Source: H. Kadiri, N. Ng, P.-J. Wong, "The least prime ideal in the Chebotarev density theorem",
arXiv:1902.08640v1, §2.1 (pdftotext extraction).

> **Theorem 2.2.** Let ε > 0. For any j ∈ N, set sj = Σ_{n≥1} bn zn^j, and assume that
>   (i) zn ∈ C and |zn| ≤ |z1| for every n ≥ 1 where z1 6= 0,
>   (ii) each bn is non-negative and b1 > 0.
> Set M = b1^{-1} Σ_{n≥1} bn|zn|/(|z1|+|zn|). Then there exists j with 1 ≤ j ≤ (8 + ε)M such that
>            Re(sj) ≥ (b1 ε / (32 + 4ε)) |z1|^j .

(`6=` above is a pdftotext rendering of `≠`.) The paper states this "refines [9, Theorem 4.2]"
(Lagarias–Montgomery–Odlyzko-type) and reduces the constants 12, 48 of [13, Thm 2.3] (Zaman) to 8, 32.

### 1c. A modified Cassels/Turán one-sided power-sum theorem (primary source, verbatim PDF)

Source: Sz. Gy. Révész, "Oscillation of the remainder term in the prime number theorem of Beurling,
'caused by a given ζ-zero'", arXiv:2202.01837v3, Lemma 3 (pdftotext extraction).

> **Lemma 3 (Modified Cassels' power-sum theorem).** If 1 ≤ k, n ∈ N, and w1 = ··· = wk = 1,
> w_{k+2j} = w_{k+2j−1} (j = 1, …, n) are k + 2n complex numbers with wℓ = rℓ e^{iαℓ},
> (|αℓ| ≤ π, ℓ = 1, …, k + 2n) then for any H > 0 we have
>            max_{H≤L≤(2n+1)H} ℜ( Σ_{ℓ=1}^{k+2n} rℓ^L e^{iαℓ L} ) ≥ k.

STATUS Item 1: VERIFIED-FETCHED. Classical First/Second Main Theorem (Wikipedia raw wikitext, with
constants c(M,N), the 2·(N/(8e(M+N)))^N·min_j|Σb_n| second-main form) plus two explicit working
variants from arXiv PDFs (Kadiri–Ng–Wong Thm 2.2; Révész Lemma 3). No unfetched recall used.

---

## Item 2 — A t-aspect "one ζ-zero near σ=1 forces clustering / repulsion of OTHER zeros"?

Nothing of this exact shape was found in any fetched source. The two nearest fetched results are
(A) a q-aspect (exceptional-real-zero) Deuring–Heilbronn theorem for a Dedekind ζ_L, proved via the
Turán power sum method — the repulsion is driven by the **real exceptional zero β₁**, not by a zero
at height t₀; and (B) a t-aspect single-zero theorem whose consequence is **oscillation of
ψ(x)−x**, not clustering/repulsion of other zeros. Neither is the requested object.

### 2A. Closest match — Deuring–Heilbronn via Turán power sums, but q-aspect (real exceptional zero)

Source: Kadiri–Ng–Wong, arXiv:1902.08640v1, §2.2 (pdftotext extraction).

Framing (verbatim):

> Our main improvement is a stronger zero-repulsion theorem than in [13].

> The Deuring-Heilbronn phenomenon roughly asserts that if an exceptional zero β1 exists then the
> zero-free region for ζL(s) [is widened].

The quantitative theorem (verbatim):

> **Theorem 2.6.** Let c ≥ 2, η ∈ (0,1), T ≥ 1, and 0 < ε < 1. Suppose that β1 = 1 − λL1 is an
> exceptional zero of ζL(s) and ρ′ = β′ + iγ′ is another zero of ζL(s) with |γ′| ≤ T. Write
> β′ = 1 − λ′/L. Then either β′ ≤ 1 − η or there exist positive effectively computable constants C
> and κ such that
>            λ′ ≥ (1/C) log(κ λ1^{-1}),   C = C(c, η, T, ε) = A a (16 + 4ε)/(c − 1),
> where a and A are defined in (2.10) and (2.12).

with sample constants (verbatim):

> C(5, 0.5, 1, ε̃) = 14.1439…, C(5.2, 0.1, 1, ε̃) = 12.2618…, [ε̃ = 10^{-11}]

Why this is NOT the requested object: the *forcing* zero here is β₁ = 1 − λ_{L1}, the **real
exceptional (Siegel) zero on the 1-line** of a Dedekind zeta ζ_L — this is the classical
q-aspect / conductor-aspect Deuring–Heilbronn. The repelled zero ρ′ may sit at height |γ′| ≤ T, but
the mechanism is "an exceptional real zero repels others," which has **no t-aspect analogue for ζ
itself** (ζ has no exceptional zero). The section is literally titled "Deuring-Heilbronn via the
Turán Power Sum method," confirming the power-sum route, but the result is q-aspect, not t-aspect.

### 2B. Closest t-aspect single-zero theorem — but consequence is oscillation of ψ(x)−x, not clustering

Source: Sz. Gy. Révész, arXiv:2202.01837v3 (pdftotext extraction). Historical attribution (verbatim):

> In the classical case of the Riemann zeta function the problem of Littlewood was first answered by
> Turán [63]. Applying his celebrated power sum method [62],[61] Turán could prove an oscillation
> result essentially meaning ∆(x) = Ω(x^{β0 −ε}) for all ε > 0 and with an effective, explicit lower
> bound and localization. The Turán result then was sharpened in several steps [58], [31] until
> Pintz [38] reached |∆(x)| ≥ (1 − ε) x^{β0}/|ρ0|, fully exploiting the presence of the term
> belonging to ρ0.

Main theorem for ζ (verbatim):

> **Theorem 1.** Let ζ(ρ0) = 0 with ρ0 = β0 + iγ0 be a zero of the Riemann zeta function. Then for
> arbitrary ε > 0 we have for some suitable, arbitrarily large values of x the lower estimate
>            |∆(x)| ≥ (π/2 − ε) x^{β0}/|ρ0| .        [∆(x) := ψ(x) − x]

Why this is NOT the requested object: the input IS a single ζ-zero ρ₀ = β₀ + iγ₀ at height γ₀ (a
genuine t-aspect single-zero hypothesis), and the proof IS via Turán's power sum method — but the
CONSEQUENCE is an Ω-oscillation of the prime-counting error term ∆(x) = ψ(x) − x, i.e. a statement
about primes, NOT about the location/clustering/repulsion of OTHER zeros of ζ. The single zero
"forces" large oscillations of ψ(x)−x, not neighbouring zeros.

Corroborating (fetched, WebFetch summary of arXiv:2411.13791, "Zero-density estimates and the
optimality of the error term in the PNT"): it cites "Pintz [20, Theorem 2] that if there exists
infinitely many zeros ρ=β+it of ζ(s) such that β≥1−η(|t|), then Δᵢ(x)=Ω±(exp(−(1+ε)ω(x)))" — again a
zeros→prime-oscillation implication (and it needs *infinitely many* zeros), not zeros→zeros.

STATUS Item 2: NEGATIVE for the requested t-aspect zeros-force-zeros (clustering/repulsion) theorem
for ζ via power sums. PARTIAL/closest: (A) power-sum Deuring–Heilbronn exists but is q-aspect
exceptional-real-zero repulsion for ζ_L (Kadiri–Ng–Wong Thm 2.6); (B) t-aspect single-zero power-sum
theorem exists but its consequence is oscillation of ψ(x)−x (Révész Thm 1; Turán/Pintz lineage).

---

## Item 3 — Negative record: queries run, sources fetched, closest statements

**No fetched source states**: "one zero of ζ(s) with Re s near 1 at height t₀ forces OTHER ζ-zeros
nearby (clustering) or a widened zero-free region elsewhere (repulsion)," proved via power sums —
i.e. a genuine t-aspect Deuring–Heilbronn analogue *for ζ, zeros-forcing-zeros*. What exists is
(a) q-aspect exceptional-zero DH repulsion for L/Dedekind ζ (2A), and (b) t-aspect single-zero →
ψ(x)−x oscillation (2B). The zeros-force-other-zeros t-aspect statement for ζ was not found.

### Queries run (WebSearch)
1. `Turán second main theorem power sum method lower bound max nu constants survey`
2. `Turán power sum method zeros zeta clustering repulsion Deuring-Heilbronn t-aspect`
3. `Pintz power sum method density theorem zero-free region remainder prime number formula`
4. `Pintz single zero zeta beta near 1 oscillation psi(x)-x Omega result power sum`
5. `Turán power sum one zeta zero height t forces many zeros clustering critical strip`

### Sources fetched / extracted
- Wikipedia "Turán's method" (article + raw wikitext) — VERIFIED (Item 1 classical statements).
- arXiv:1902.08640v1 Kadiri–Ng–Wong, "Least prime ideal in the Chebotarev density theorem"
  — pdftotext VERIFIED (Thm 2.2 power sum; Thm 2.6 q-aspect DH repulsion).
- arXiv:2202.01837v3 Révész, "Oscillation … 'caused by a given ζ-zero'"
  — pdftotext VERIFIED (Thm 1; Lemma 3 modified Cassels/Turán power sum; Turán/Pintz attribution).
- arXiv:2411.13791 "Zero-density estimates and optimality of the PNT error term"
  — WebFetch summary only (Pintz [20, Thm 2] zeros→Ω± oscillation citation). PARTIAL.
- arXiv:1003.0098 (Cheng, "Analytic implications …") — WebFetch: paper withdrawn; cites Turán 1950
  "ψ-form implies no zeros of ζ(s) for ℜ(s) > h(t)"; no zeros-force-zeros theorem. PARTIAL.
- arXiv:0704.1879 (Andersson, "Lower bounds in some power sum problems") — pdftotext: min-norm pure
  power-sum variants, not the classical min-partial-sum second main theorem; math glyphs extracted
  poorly. Not used for Item 1 statements.
- Search-surface only (not individually fetched, listed for completeness): arXiv:1508.00287,
  1807.00508, 1604.01750 (Chebotarev least-prime, same q-aspect DH-via-power-sum family);
  1912.00853, 2202.01837, 2207.00665, 2507.13780 (zeros ↔ PNT-error oscillation family);
  2511.20059, 2603.28104 (Goldston–Suriajaya zeta-zeros-on-line, counting not forcing);
  2503.15449 (pair correlation — statistical, not power-sum forcing).

STATUS Item 3: NEGATIVE recorded with full query list. Closest fetched positives are the two boxed
theorems in 2A (q-aspect DH repulsion, power sum) and 2B (t-aspect single-zero → ψ(x)−x oscillation,
power sum). No t-aspect zeros-force-zeros clustering/repulsion theorem for ζ via power sums was found
in any fetched source.

---

### One-line synthesis
Turán's power-sum method HAS produced (i) a q-aspect Deuring–Heilbronn zero-repulsion theorem
(exceptional real zero β₁ repels other zeros of ζ_L; Kadiri–Ng–Wong Thm 2.6, constants ≈14.14), and
(ii) a t-aspect single-ζ-zero theorem (Révész Thm 1, Turán→Pintz: |ψ(x)−x| ≥ (π/2−ε)x^{β0}/|ρ0|).
It has NOT (in fetched sources) produced the requested hybrid: a t-aspect statement where one ζ-zero
near σ=1 at height t₀ forces OTHER ζ-zeros (clustering) or a widened zero-free region elsewhere
(repulsion). That specific object is the gap.
