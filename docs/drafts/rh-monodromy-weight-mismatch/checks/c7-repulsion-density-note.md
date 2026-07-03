# c7 — Repulsion & zero-density note (verified-fetched classical statements)

Verification-reading delegate note. Every quote below was FETCHED and read this session
(WebFetch, or `pdftotext` on the PDF that WebFetch saved to disk). Nothing here is recalled.
Where a symbol looks odd it is a faithful `pdftotext` extraction artifact (σ, ≪, ≤, ε, α, β, γ, η, χ),
not a paraphrase. No interpretation, no RH editorializing — statements only.

---

## Item 1 — Halász–Turán / Vinogradov-type zero-density near σ = 1 for ζ

**STATUS: VERIFIED-FETCHED** (exact exponent shape and an explicit constant both obtained verbatim).

### 1a. The near-σ=1 shape  N(σ,T) ≪ T^{c(1−σ)^{3/2}}(log T)^B — explicit form

Source: **C. Bellotti, "Explicit zero density estimate near unity", arXiv:2311.05136 (Nov 2023)**
(fetched PDF → pdftotext). Abstract:

> "We will provide the first explicit zero-density estimate for ζ of the form
>  N (σ, T ) ≤ C T^{B(1−σ)^{3/2}} (log T )^C."

Its clean single-term result (Theorem 1.2), which is the sharpest *explicit* bound of this shape:

> **Theorem 1.2.** For every σ ∈ [0.98, 1] and T ≥ 3, the following zero-density estimate holds
> uniformly:
>   N (σ, T ) ≤ C1′ · T^{57.8875(1−σ)^{3/2}} · (log T )^{10393/900},   (1.2)
> where C1′ = 2.15·10^23 if 3·10^12 < T ≤ e^46.2; 1.89·10^23 if e^46.2 < T ≤ e^170.2;
> 4.42·10^22 if e^170.2 < T ≤ e^481958; 4.72·10^20 if T > e^481958.

with the paper's own gloss:

> "the exponent 10393/900 = 11.547 . . . for the factor log T is less than 11.548, which improves
>  the best-known exponent equal to 15 due to Ivic"

Its sharper two-term Theorem 1.1 (same 57.8875 exponent, cases with 19703/1800 etc.):

> **Theorem 1.1.** For every σ ∈ [0.98, 1] and T ≥ 3 ... N (σ, T ) ≤
>  (C1 T^{57.8875(1−σ)^{3/2}} (log T)^{19703/1800} + C2 T^{33.08(1−σ)^{3/2}} (log T)^{503/45}
>   + 0.27 (log T)^{14/10}) log log T,   where C2 = 7.65·10^10 [C1 piecewise 4.68·10^23 … 9.77·10^21].

On the **non-explicit** (sharpest-in-principle) side, the same paper records:

> "The best non-explicit zero-density estimate of this form is due to Heath-Brown [HB17] ...
>  ζ(σ + it) ≪ t^{B(1−σ)^{3/2}+ε}, where the exponent B turns out to be much smaller (B < 1/2)
>  than the currently best-known value for B in Richert's bound, that is B = 4.43795 [Bel23]."

Underlying large-values input is the Vinogradov–Korobov / **Richert bound**
|ζ(σ+it)| ≤ A|t|^{B(1−σ)^{3/2}}(log|t|)^{2/3} (quoted in the same intro).

### 1b. The classical uniform (log-carrying) family — Ingham / Huxley

Source: **C. Bellotti, "An explicit log-free zero density estimate for the Riemann zeta-function",
arXiv:2405.12545**, introduction (fetched PDF → pdftotext):

> "the sharpest uniform non-explicit bound for N (σ, T ) which holds for every 1/2 < σ ≤ 1 and
>  T > 0 is N (σ, T ) ≪ T^{12(1−σ)/5+ε}, which can be obtained ([Ivi03]) by combining Ingham's
>  estimate [Ing40] N (σ, T ) ≪ T^{3(1−σ)/(2−σ)} log^5 T for 1/2 ≤ σ ≤ 3/4 with Huxley's one
>  [Hux71] N (σ, T ) ≪ T^{3(1−σ)/(3σ−1)} log^{44} T, which holds for 3/4 ≤ σ ≤ 1."

Ingham's density-from-Lindelöf connection (same intro):

> "he proved [Ing37] that if ζ(1/2 + it) ≪ t^{c+ǫ} for a certain constant c, then
>  N (σ, T ) ≪ T^{(2+4c)(1−σ)} (log T )^5. In particular, the Lindelöf Hypothesis ζ(1/2+it) ≪ t^ǫ
>  implies the Density Hypothesis."

### 1c. Corroboration — Analytic Number Theory Exponent Database

Source: **teorth.github.io/expdb, "11 Zero density theorems"** (WebFetch). Writing A(σ) for the
exponent in N(σ,T) ≪ T^{A(σ)(1−σ)+o(1)}:

> Theorem 11.14 (Ingham's Second Bound): "For any 1/2 < σ < 1, one has A(σ) ≤ 3/(2−σ)."
> Theorem 11.15 (Huxley Bound): "For any 1/2 < σ < 1, one has A(σ) ≤ 3/(3σ−1)."

and the Halász–Turán large-values form near the 1-line, A(1−η) ≤ C·η^{1/2}, with C improved to
58.05 (Ford 2002), 5.03 (Heath-Brown 2017), > 3√2 ≈ 4.24 (Pintz 2023). [WebFetch rendering of
the blueprint; the η^{1/2} exponent on A(σ) is what produces the (1−σ)^{3/2} shape in N(σ,T).]

**Exponent-shape summary (item 1):** near σ=1 the true shape is
N(σ,T) ≪ T^{c(1−σ)^{3/2}}(log T)^B; sharpest explicit constant fetched = c = 57.8875,
B = 10393/900 ≈ 11.547, valid σ ∈ [0.98,1], T ≥ 3 (Bellotti 2311.05136, Thm 1.2). Best
non-explicit constant c < 1/2 (Heath-Brown 2017, via ζ ≪ t^{B(1−σ)^{3/2}+ε}). The uniform
whole-strip fallback is the log-carrying T^{(12/5)(1−σ)+ε} (Ingham+Huxley, Ivić 2003).

---

## Item 2 — Log-free zero-density theorems for Dirichlet L-functions (Linnik/Jutila/…)

**STATUS: VERIFIED-FETCHED** (classical log-free forms + best explicit hybrid constants obtained
verbatim; the specific Iwaniec–Kowalski *theorem number* is PARTIAL — the fetched source cites
"[IK04, Section 18.2]" for the Huxley form and "Chapter 18 of [IK04]" for the log-free Linnik
application, but I did not fetch IK itself to read a "Theorem 18.x" label).

Source: **"Log-free zero density estimates for automorphic L-functions", arXiv:2004.14410, §2
"The general setting of zero density estimates"** (fetched PDF → pdftotext). With
N_q(α,T) = Σ_{χ mod q} N(α,T,χ), N(α,T,χ) = #{ρ : L(ρ,χ)=0, ℜρ ≥ α, |ℑρ| ≤ T}:

Huxley (log-carrying) form, attributed to IK Ch. 18:

> "In this case, the Huxley density estimate is  N_q(α, T ) ≪ (qT )^{12/5 (1−α)} (log qT )^A
>  where A is an absolute constant; see [IK04, Section 18.2]."

The **log-free** form needed for Linnik's theorem (NO log factor):

> "in the proof of the Linnik's theorem (see e.g., Chapter 18 of [IK04]), one needs a log-free
>  zero density estimate on average for Dirichlet L-functions of the form
>  N_q(α, T ) ≪ (qT )^{c(α)(1−α)}."

Montgomery's hybrid (log-carrying):

> "A 'hybrid' density estimate of Montgomery [Mon69] is
>  Σ_{q≤Q} Σ*_{χ(mod q)} N (α, T, χ) ≪ (Q^2 T )^{5/2 (1−α)} (log QT )^c,   for some c > 0"

The **log-free hybrid** and its best classical explicit constants — this is the sharpest classical
(qT)^{c(1−σ)} statement with named constants:

> "There can also be log-free zero density estimates on average, which are hybrid in conductor,
>  such as   Σ_{q≤Q} Σ*_{χ(mod q)} N (α, T, χ) ≪ (Q^{c1} T^{c2})^{1−α}   (2.1)
>  for some c1 , c2 > 0. Gallagher [Gal70] proved this hybrid version (2.1) for some constants
>  c1 , c2 and Selberg [Sel72] proved c1 = 5 + ε, c2 = 3 + ε suffice. Jutila [Jut78] refined the
>  estimate and obtained c1 = 4 + ε, c2 = 2 + ε; these works are closely related to the method of
>  this paper."

Corroborating pointer (WebSearch, not deep-fetched): the plain single-modulus Linnik log-free
statement is usually quoted as "there is an effectively computable c_3 such that
Σ_{χ(mod q)} N(σ,T,χ) ≪ (qT)^{c_3(1−σ)} (T ≥ 1)"; first proved by **Linnik (1944)**; **Gallagher
[Gal70]** gave the large-sieve proof "near σ=1" (per arXiv:2004.14410 intro line 19).

**Exponent-shape summary (item 2):** log-free = N_q(σ,T) ≪ (qT)^{c(1−σ)}, no log factor, valid
1/2 ≤ σ ≤ 1, T ≥ 1. Best *explicit* named classical constants are in the conductor-hybrid form
(Q^{c1}T^{c2})^{1−σ}: Selberg c1=5+ε, c2=3+ε; **Jutila (best classical) c1=4+ε, c2=2+ε**.
Original existence: Linnik 1944 (ineffective/effective-with-nonexplicit-constant).

---

## Item 3 — Deuring–Heilbronn phenomenon, and the ζ t-aspect analogue search

**STATUS (classical statement): VERIFIED-FETCHED.**
**STATUS (ζ t-aspect analogue): NEGATIVE SEARCH RESULT — none found.**

### 3a. Classical Deuring–Heilbronn repulsion (q-aspect, across L-functions mod q)

Source: **Terence Tao, blog tag "deuring-heilbronn-repulsion" (terrytao.wordpress.com)** (WebFetch).
With an exceptional (Landau–Siegel) real zero written β = 1 − ε/log q:

> Theorem 9: "all other zeroes σ+it of L-functions of modulus q are such that
>  σ ≤ 1 − c log(1/ε) / log(q(2+|t|))"

i.e. the ordinary zero-free region σ ≤ 1 − c/log(qT) is **widened by the multiplicative repulsion
factor log(1/ε)**. [WebFetch rendering of the blog's Theorem 9; ε is the exceptional zero's
distance-to-1 in units of 1/log q.]

Explicit modern version, source: **"Explicit Deuring–Heilbronn phenomenon for Dirichlet
L-functions", arXiv:2410.06082** (WebFetch of the HTML). For q > 400,000, T ≥ 4, given a
Landau–Siegel zero β₁ with 1 − 1/(10 log q) < β₁ < 1 − B/(q^ε(log q)²):

> **Theorem 1.3:** if ρ = β + iγ is any other zero with β > 1/2, |γ| ≤ T, then
>  β < 1 − log( θ / (4(1−β₁) log M) ) / log M,   where M = K q^{8θ+2ε} T^{4θ}.

Repulsion factor θ/(4(1−β₁)log M): smaller (1−β₁) forces β further from 1. The paper is
"exclusively about Dirichlet L-functions modulo q" and (per its own text, via WebFetch)
**does not discuss any ζ t-aspect analogue.**

### 3b. Does a ζ t-aspect analogue exist? — NEGATIVE

Question posed by the lane: "if ζ has a hypothetical zero very close to σ=1 at height t₀, are
ζ-zeros at other heights repelled (or attracted)?" I found **no theorem of this form** in what I
could fetch. What actually exists is uniformly a **q-aspect / cross-family** statement: an
exceptional *real* zero of *one* L(s,χ) mod q repels zeros of the *other* L-functions of the *same
modulus q* (and, in the Lagarias–Montgomery–Odlyzko / Chebotarev setting, zeros of a Dedekind
ζ_K / a family). The mechanism is intrinsically a *real zero within a family of distinct
L-functions*, not a *single* ζ repelling itself along its own critical strip in the t-direction.

Nearest fetched neighbours (all still q-aspect / family, NOT a single-ζ t-aspect theorem):
- Lagarias–Montgomery–Odlyzko: a real zero ω₀ of a Dedekind ζ_L forces ζ_L(σ+it) ≠ 0 in a
  widened region except at ω₀ (family/Chebotarev; WebSearch surfacing).
- "Repulsive behavior in an exceptional family", arXiv:1108.6272 (exceptional *family*, WebSearch).
- Statistical (unconditional) ζ–ζ repulsion is a *different* object: GUE / Montgomery pair
  correlation gives level repulsion between neighbouring ζ zeros, but that is not a
  Deuring–Heilbronn-type *conditional* theorem "one near-1 zero at t₀ ⇒ others at t≠t₀ moved".

Search queries actually run this session for the ζ t-aspect analogue (all negative for a
single-ζ t-aspect repulsion theorem):
1. `Deuring-Heilbronn phenomenon exceptional zero repulsion statement zero-free region Siegel zero`
2. `Deuring-Heilbronn analogue Riemann zeta function t-aspect hypothetical zero near sigma=1 repels vertical distribution zeros`
3. `no known repulsion zeros Riemann zeta same L-function different heights t-aspect Deuring-Heilbronn does not apply single zeta`
4. WebFetch of arXiv:2410.06082 — checked for ζ t-aspect discussion: none (Dirichlet mod q only).
5. WebFetch of Tao's deuring-heilbronn-repulsion blog tag — checked for ζ t-aspect: none.

**Verdict (item 3):** Classical Deuring–Heilbronn = VERIFIED-FETCHED (q-aspect, cross-family,
repulsion factor log(1/ε)). A ζ *t-aspect* self-repulsion analogue = NOT FOUND in fetched sources;
recorded as a negative search result with the queries above.

---

### Sources fetched (for re-verification)
- arXiv:2311.05136 — Bellotti, "Explicit zero density estimate near unity" (item 1, Thm 1.1/1.2).
- arXiv:2405.12545 — Bellotti, "An explicit log-free zero density estimate for ζ" (item 1, intro).
- teorth.github.io/expdb, ch.11 "Zero density theorems" (item 1, Ingham/Huxley/Halász–Turán).
- arXiv:2004.14410 — "Log-free zero density estimates for automorphic L-functions" (item 2, §2).
- terrytao.wordpress.com tag deuring-heilbronn-repulsion (item 3, Theorem 9).
- arXiv:2410.06082 — "Explicit Deuring–Heilbronn phenomenon for Dirichlet L-functions" (item 3, Thm 1.3).
Unfetched-as-primary (cited only): Iwaniec–Kowalski, "Analytic Number Theory", Ch. 18 / §18.2 —
referenced by arXiv:2004.14410 but not itself opened, so IK theorem-number labels are PARTIAL.
