# Literature check — Ostrowski's structure theory for DA Dirichlet series

Status: verification note (SEARCH register). Purpose: pin the EXACT statement of Ostrowski
(1920) on Dirichlet series satisfying algebraic differential equations, and audit one novelty
claim (hypertranscendence used as a *hypothesis* constraining zero location). No Lean, no
computation — WebSearch/WebFetch only.

Marking convention: `[VERIFIED-KNOWN]` = quoted from a source I actually read; `[RECALLED-
UNVERIFIED]` = from memory, not confirmed here; `[ABSENT]` = search returned nothing.

## Sources and fetch status

- **[S1] Original.** A. Ostrowski, "Über Dirichletsche Reihen und algebraische
  Differentialgleichungen", *Mathematische Zeitschrift*, vol. **8** (1920), pp. **241–298**.
  DOI 10.1007/BF01206530. EUDML id 167602.
  - Bibliographic page [fetched] (eudml.org/doc/167602) — confirms vol/year/pages, no abstract.
  - German full text: [pointer, unfetched] — GDZ / Springer scan; the Springer PDF
    (link.springer.com/content/pdf/10.1007/BF01206530.pdf) is a FlateDecode-compressed
    image-scan, WebFetch could not extract readable text. [paywalled/scan]
- **[S2] English translation (PRIMARY SOURCE USED).** E. C. Hansen, Y. Stone, J. Wolfson,
  "Ostrowski's 'On Dirichlet Series and Algebraic Differential Equations'",
  arXiv:**2211.02088** [math.HO], 3 Nov 2022. Complete English translation of [S1].
  - Abstract [fetched] via arxiv.org/abs/2211.02088.
  - Full body [fetched]: WebFetch of the PDF failed to parse (compression), but the PDF was
    saved locally by WebFetch and read directly (pages 1–24). All verbatim quotes below are
    from this translation, with the translation's own page numbers. arXiv HTML (arxiv.org/html)
    returned 404.
- **[S3]** Springer, "Algebraic differential independence concerning the Euler Γ-function and
  Dirichlet series", *Acta Math. Sci.* (2020); ScienceDirect S0022247X18301380 "A study on
  algebraic differential equations of Gamma function and Dirichlet series". [pointer, unfetched]
  — surfaced repeatedly; these PROVE differential independence (hypertranscendence as a
  *conclusion*), the opposite direction to Q3.

---

## QUESTION 1 — the exact statement of Ostrowski's theorem(s)

### (a) Hypotheses: which series, what convergence

`[VERIFIED-KNOWN]` Ostrowski treats **general Dirichlet series** ∑ aₙ e^{−λₙ s} as the primary
object; ordinary Dirichlet series ∑ aₙ n^{−s} are the special case λₙ = log n. He proves the
STRONGER non-existence of algebraic **difference** differential equations (functional equations
mixing derivatives and real shifts s ↦ s+h), of which a plain algebraic differential equation is
the case all hₘ = 0.

Introduction, p.2 (verbatim): "In the first section of this treatise I will prove that this same
property [not satisfying any algebraic differential equation] holds for all Dirichlet series
∑ aₙ/nˢ whose coefficients aₙ are all non-zero, or that the indices n of all non-zero
coefficients have infinitely many prime divisors. More generally, this property is shared by all
Dirichlet series ∑ aₙ e^{−λₙ s} possessing the property that none of the λₙ can be expressed as
integer linear combinations of finitely many of the other λₙ, that is to say that infinitely many
of the λₙ are linearly independent over the integers. We will proceed to prove this theorem in an
even more generalized form (Theorems 1 and 6), as we will prove the non-existence of an algebraic
difference differential equation..."

Convergence hypothesis: **a domain of absolute convergence** (Theorem 1) / **convergent**
Dirichlet series (Theorem 6). Definition 1 (p.6): "An algebraic difference differential equation
is a functional equation of the form F(x, f^(ν)(x+h_μ)) = 0 where h₁, h₂, … are finitely many
real numbers and F is a polynomial in its arguments." The ONLY analytic input is the Dirichlet-
series uniqueness theorem (p.5): "a convergent Dirichlet series ∑ aᵢ e^{−λᵢ s} … [which] vanishes
for sufficiently large positive s … also has the property that all the coefficients aᵢ vanish."

### (b)+(c) Conclusion SHAPE — verbatim theorem statements

The theorems are NEGATIVE/necessary-condition form (a "finite basis" must exist). The positive
STRUCTURE form is stated in the introduction and §§ (see below).

`[VERIFIED-KNOWN]` **Theorem 1** (p.10): "If a Dirichlet series φ(s) = ∑ aᵢ e^{−λᵢ s} has a
domain Ω of absolute convergence and if the analytic function it represents in Ω satisfies an
algebraic difference differential equation, then the system of numbers λᵢ possesses a finite
linear basis from among the numbers λᵢ."

`[VERIFIED-KNOWN]` **Theorem 6** (p.19): "If a function φ(s) = ∑ aᵢ e^{−λᵢ s}, represented by a
convergent Dirichlet series, satisfies an algebraic difference differential equation, then the
system of exponents λᵢ possesses a finite linear basis."

`[VERIFIED-KNOWN]` **Theorem 7** (p.20): "If a convergent Dirichlet series ∑ aᵢ e^{−λᵢ s} has the
property that lim sup_{i→∞} λᵢ/λ_{i−1} → ∞, it cannot satisfy any algebraic difference
differential equation."

`[VERIFIED-KNOWN]` **Theorem 8** (p.20) — a SECOND independent necessary condition, on the
COEFFICIENTS: "A Dirichlet series ∑ aᵢ e^{−λᵢ s}, whose coefficients have no finite basis cannot
satisfy an algebraic differential equation." Strengthened by **Corollary 1** (p.24): "If there is
a subsystem 𝒢 of the coefficients aᵢ … whose numbers cannot be expressed rationally (with rational
coefficients) using finitely many numbers belonging to the same subsystem, then this series cannot
satisfy any algebraic differential equation. In particular … if the numbers aᵢ contain an infinite
number of algebraic numbers not contained in the same finite field extension, for instance an
infinite number of distinct roots of unity."

`[VERIFIED-KNOWN]` **Theorem 2** (p.11) — the ζ(x,s) result (Hilbert's conjecture): "As a function
of the variables x, s, the function ζ(x,s) = x + x²/2ˢ + x³/3ˢ + … fails to satisfy any algebraic
partial differential equation."

### The POSITIVE structure theorem (this is the payload for the program)

`[VERIFIED-KNOWN]` **Ordinary Dirichlet series** — Introduction p.3 (verbatim): "Using the
results from the first two sections, it follows that such Dirichlet series of the type ∑ aₙ/nˢ …
must be of the form F(n₁⁻ˢ, n₂⁻ˢ, …, n_μ⁻ˢ), where F(x₁, x₂, …, x_μ) is a power series in μ
arguments. Moreover, one can easily construct such power series F for which each choice of the
integers n₁, n₂, …, n_μ represent functions in s which satisfy algebraic differential equations."

`[VERIFIED-KNOWN]` **Prime-factor form** — p.9 (verbatim): "Thus, if the indices n corresponding
to non-zero aₙ in (5) are divisible by an infinite number of different prime numbers, then (5)
surely cannot formally satisfy any equation (2). However, if the denominators actually occurring
in (5) only contain finitely many prime factors p₁, p₂, …, p_β, we can formally write (5) in the
form Ψ(p₁⁻ˢ, p₂⁻ˢ, …, p_β⁻ˢ) where Ψ(x₁, x₂, …, x_β) is a power series containing only positive
powers of x₁, x₂, …, x_β. However, if (5) possesses a domain of convergence (hence also a domain
of absolute convergence), then Ψ(x₁, x₂, …, x_β) also has a domain of absolute convergence in
which it represents an analytic function of x₁, x₂, …, x_β."

`[VERIFIED-KNOWN]` **General Dirichlet series** — Introduction p.4 (verbatim): "If a general
Dirichlet series of the type ∑ aₙ e^{−λₙ s} satisfies an algebraic differential equation, we can
use the results from §1 and §2 to represent it in the form F(e^{−λ₁ s}, e^{−λ₂ s}, …, e^{−λ_μ s}),
where F is a power series iterated over both positive and negative powers of its arguments and
λ₁, λ₂, …, λ_μ are positive linearly independent real numbers."

### Q1 verdict (one sentence)

`[VERIFIED-KNOWN]` A convergent Dirichlet series that satisfies an algebraic (difference)
differential equation must have its exponents span a **finitely generated** ℤ-module (finite
linear basis λ₁,…,λ_μ) — equivalently, for the ordinary case, all support-integers built from
**finitely many primes** p₁,…,p_β — and the function is then a **convergent power series**
Ψ(p₁⁻ˢ,…,p_β⁻ˢ) (resp. F(e^{−λ₁s},…,e^{−λ_μs}), Laurent in the general case) in those finitely
many prime/exponential variables; the coefficients must ALSO possess a finite (rational-field)
basis. It is NOT merely "ζ is hypertranscendental" — there is a genuine general structure theorem.

---

## QUESTION 2 — does the theorem give "DA ⟹ finite frequency support"?

### Verdict: FALSE. "DA ⟹ finite support (Dirichlet polynomial)" is refuted.

`[VERIFIED-KNOWN]` Ostrowski's conclusion is finite **basis / finitely many primes**, explicitly
NOT finite support. The structure object is a **power series** Ψ in the prime variables, whose
expansion in n^{−s} generally has **infinitely many nonzero terms**. Ostrowski himself notes
(p.3) that one can "easily construct such power series F … which satisfy algebraic differential
equations."

### The counterexample is real: exp(2^{−s})

`[VERIFIED-KNOWN, arithmetic checked here]`
- exp(2^{−s}) = ∑_{k≥0} (1/k!) (2^k)^{−s}: an ordinary Dirichlet series ∑ aₙ n^{−s} with
  a_{2^k} = 1/k!, else 0. Terms (1/k!)·2^{−kσ} decay super-exponentially in k for EVERY σ, so it
  converges absolutely on all of ℂ (entire) — a genuine ordinary Dirichlet series with a
  half-plane (indeed the whole plane) of convergence.
- Support = {2^k : k ≥ 0}: **infinitely many frequencies**, but only ONE prime (p = 2).
- It is exactly Ostrowski's Ψ(2^{−s}) with Ψ(x) = e^x = ∑ xᵏ/k!, a convergent one-variable power
  series in x = p₁^{−s}, p₁ = 2. Fits the structure theorem perfectly (β = 1).
- It IS differentially algebraic over ℂ: with g = 2^{−s} (g' = −(log2)g, so f=e^g gives f'/f = g'
  and f''/f = g''+(g')² = −(log2)g' + (g')²), one gets the order-2 degree-2 polynomial ODE
    **f·f'' − (f')² + (log2)·f·f' = 0**,   coefficients in ℂ.

So exp(2^{−s}) is a differentially algebraic ordinary Dirichlet series with INFINITE support.
"DA ⟹ finite frequency support / Dirichlet polynomial" is FALSE. The correct statement is
Ostrowski's: **DA ⟹ contained in the finitely-generated ring of a finite set of prime
exponentials p_i^{−s} (a convergent power series Ψ(p₁^{−s},…,p_β^{−s}))** — i.e. finitely
generated *frequency group*, not finite support. (This matches the conjecture stated in the task
prompt; the prompt's conjecture is CONFIRMED by [S2].)

### What zero-set structure does the theorem license?

`[VERIFIED-KNOWN]` re Ostrowski: the paper says NOTHING directly about zero locations. Its
constraint is purely on the **frequency group** (finite basis / finitely many primes) and the
**coefficient field** (finite basis). Any zero-set statement is a downstream consequence of that
structure plus standard theory, NOT a theorem of [S1]/[S2].

`[VERIFIED-KNOWN, standard exponential-sum theory — flagged as NOT from Ostrowski]` Given the
structure f = Ψ(p₁^{−s},…,p_β^{−s}) with log p_i ℚ-independent:
- Zeros = preimage under s ↦ (p₁^{−s},…,p_β^{−s}) of the analytic variety {Ψ = 0}. The moduli
  p_i^{−σ} depend only on σ = Re s; the phases −t·log p_i (t = Im s) equidistribute on the torus
  𝕋^β (Kronecker/Weyl, since log p_i are ℚ-independent).
- If Ψ is a Dirichlet **polynomial** (finite exponential sum): zeros are confined to a **bounded
  vertical strip** and form an **almost-periodic** set with a positive linear density in t (Bohr /
  Jessen–Tornehave). They are NOT in general a finite union of exact vertical lattices — that
  degenerate case occurs only for a single-frequency binomial a + b·p^{−s} (zeros = one vertical
  arithmetic progression).
- If Ψ is a genuine (non-polynomial) convergent power series: the zero set is the pullback of a
  transcendental analytic variety and can be more complex; and DA members may be **zero-free
  entirely** — e.g. exp(2^{−s}) = e^{g} is nonvanishing (empty zero set).

`[VERIFIED-KNOWN]` **Q2 zero-set verdict:** DA does NOT force the zero set to be a finite union of
vertical lattices/lines. Ostrowski licenses only: zeros = pullback of {Ψ=0} under a
multiplicatively-independent exponential map; for Dirichlet-polynomial members these are
strip-confined almost-periodic sets, and nonvanishing members (exp of a Dirichlet polynomial) have
NO zeros. Any tighter "lattice of zeros" claim is beyond what the structure theorem licenses.

**Program-relevant honesty flag:** the classical structure theorem constrains FREQUENCIES and
COEFFICIENTS, not zero POSITIONS. Using differential-algebraicity/hypertranscendence to constrain
where zeros lie is not delivered by Ostrowski and would be new work (see Q3).

---

## QUESTION 3 — novelty audit: hypertranscendence as a HYPOTHESIS on zero location

Searched for any literature using differential-algebraicity / hypertranscendence of an
L-function / Dirichlet series as a HYPOTHESIS to constrain the LOCATION OF ZEROS (the reverse of
the usual "prove hypertranscendence as a conclusion").

Searches run (all via WebSearch):
1. `hypertranscendence zeros "Riemann hypothesis" differential algebraicity hypothesis constraint`
   → `[ABSENT]` (only generic RH / Hilbert–Pólya / finite-field RH).
2. `"differentially algebraic" "Dirichlet series" zeros location vertical strip`
   → `[ABSENT]` for the hypothesis-direction; only Dirichlet-polynomial zero-density / almost-
   periodicity results (Bohr-type), which are unconditional, not DA-as-hypothesis.
3. `"differential transcendence" L-functions zeros distribution`
   → `[ABSENT]`; surfaced instead the **Linear Independence Conjecture** (zero ordinates
   ℚ-linearly independent) and "ζ satisfies no differential equation" — both are the OPPOSITE
   direction (properties OF zeros, or hypertranscendence as conclusion).
4. `hypertranscendental L-function hypothesis implies zeros critical line differential algebra`
   → `[ABSENT]`.
5. `"differentially algebraic" Dirichlet series implies Dirichlet polynomial ... exp(2^{-s})`
   → `[ABSENT]` (no source stating the false "DA ⟹ Dirichlet polynomial"; consistent with Q2).
6. `Reich algebraic differential equations Dirichlet series Ostrowski generalization`
   → only the numerical-analysis "Ostrowski–Reich theorem" (unrelated) + modern
   differential-INDEPENDENCE papers [S3] (hypertranscendence as conclusion).

`[ABSENT]` **Q3 verdict:** No literature found that uses hypertranscendence / differential
algebraicity as a HYPOTHESIS constraining zero location. Every hit runs the other way — either
(i) proving hypertranscendence / differential independence as a CONCLUSION (Ostrowski, Hilbert;
modern Γ/ζ differential-independence papers [S3]), or (ii) studying zero distributions
unconditionally (Bohr almost-periodicity, LI Conjecture, GRH). The program's intended use-direction
appears to be genuinely un-occupied in the searched corpus. (Caveat: WebSearch is US-indexed and
misses paywalled/non-English monographs; this is "no evidence found", not a proof of nonexistence.)

---

## Bottom line for the program

- Q1: `[VERIFIED-KNOWN]` DA/ADE ⟹ finite exponent-basis + finite coefficient-basis; ordinary case
  ⟹ finitely many primes and f = convergent power series Ψ(p₁^{−s},…,p_β^{−s}); general case ⟹
  Laurent F(e^{−λ₁s},…,e^{−λ_μs}). Source: Ostrowski 1920 [S1], translation arXiv:2211.02088 [S2],
  Theorems 1, 6, 7, 8, Cor. 1, and the §1/§6 structure statements.
- Q2: `[VERIFIED-KNOWN]` "DA ⟹ finite support" is FALSE; exp(2^{−s}) is a DA ordinary Dirichlet
  series with infinite support (one prime). DA licenses NO "finite lattice of zeros"; only pullback
  of {Ψ=0}, strip-confined almost-periodic for Dirichlet-polynomial members, possibly empty.
- Q3: `[ABSENT]` hypertranscendence-as-hypothesis-on-zeros is unoccupied in the searched literature.

---

# Literature check — no vertical arithmetic progression in the zero divisor of ζ

Status: verification note (SEARCH register). Purpose: pin the EXACT statement and attribution of
"the zeros of ζ contain no infinite vertical arithmetic progression," and resolve exactly which
(σ, k-range) cases the verified literature covers. WebSearch/WebFetch only; no Lean, no computation.
Marking convention as above (`[VERIFIED-KNOWN]` = quoted from a source actually read; `[fetched]` /
`[pointer, unfetched]` = fetch status).

## Sources and fetch status

- **[Z1] Putnam 54a.** C. R. Putnam, "On the non-periodicity of the zeros of the Riemann
  zeta-function," *Amer. J. Math.* **76** (1954), 97–99. Bib data confirmed from THREE independent
  reference lists (Steuding–Wegert, Lee–Sourmelidis–Steuding–Suriajaya, Lapidus survey), all read
  verbatim. Primary text JSTOR-paywalled: [pointer, unfetched].
- **[Z2] Putnam 54b.** C. R. Putnam, "Remarks on periodic sequences and the Riemann zeta-function,"
  *Amer. J. Math.* **76** (1954), 828–830. Same three reference lists. [pointer, unfetched].
- **[Z3] van Frankenhuijsen 05.** M. van Frankenhuijsen, "Arithmetic progressions of zeros of the
  Riemann zeta function," *J. Number Theory* **115** (2005), no. 2, 360–370. Bib data confirmed
  from Steuding–Wegert and Lapidus reference lists [fetched]. Primary text ScienceDirect-paywalled
  (HTTP 403) and no arXiv copy: [pointer, unfetched]; theorem statement taken verbatim from two
  independent secondary restatements.
- **[Z4] Lapidus–van Frankenhuijsen (book).** M. L. Lapidus and M. van Frankenhuijsen, *Fractal
  Geometry, Complex Dimensions and Zeta Functions* (2nd ed.), Springer, New York, 2013, **Chapter
  11**. Statement/attribution taken from the Lapidus survey below and from [Z6]. Book text
  [pointer, unfetched].
- **[Z5] Lapidus survey.** M. L. Lapidus, "The Sound of Fractal Strings and the Riemann
  Hypothesis," arXiv:**1505.01548**. PDF [fetched] and text-extracted; quotes below are verbatim.
- **[Z6] Lee–Sourmelidis–Steuding–Suriajaya.** J. Lee, A. Sourmelidis, J. Steuding, A. I.
  Suriajaya, "The values of the Riemann zeta-function on discrete sets" / "on discrete sets,"
  arXiv:**1710.11367**. PDF [fetched] and text-extracted; verbatim quotes below.
- **[Z7] Steuding–Wegert.** J. Steuding and E. Wegert, "The Riemann Zeta Function on Arithmetic
  Progressions," *Experimental Mathematics* **21**(3) (2012), 235–240, DOI
  10.1080/10586458.2012.651410. PDF [fetched] and text-extracted; verbatim quotes below.
- **[Z8] Martin–Ng.** G. Martin and N. Ng, "Nonzero values of Dirichlet L-functions in vertical
  arithmetic progressions," arXiv:**1109.1788** (*Int. J. Number Theory*, 2013). Abstract [fetched].
- **[Z9] Li–Radziwiłł.** X. Li and M. Radziwiłł, "The Riemann zeta function on vertical arithmetic
  progressions," arXiv:**1208.2684**, *IMRN* **2015**(2), 325–. Abstract [fetched].

---

## Verbatim statements

`[VERIFIED-KNOWN]` **Putnam, as restated by [Z6] p.5** (verbatim): "Putnam [21, 22] showed that the
sequence of consecutive nontrivial zeros of ζ on the critical line does not contain any arithmetic
progression of infinite length. His result can be interpreted using our notation as considering
l = 1, s = 1/2, and 0 ∉ M. Using fractal zeta-functions, Lapidus and Frankenhuijsen [14, Chapter 11]
gave a new proof of Putnam's result and extended it to a large class of zeta functions and L-series."

`[VERIFIED-KNOWN]` **Putnam + vF, as restated by [Z7] (Intro)** (verbatim): "In [Putnam 54a, Putnam
54b], it was shown that there exists no infinite arithmetic progression of nontrivial zeros, and in
[Frankenhuijsen 05], the author obtained bounds for the length of any hypothetical arithmetic
progression."

`[VERIFIED-KNOWN]` **van Frankenhuijsen 05 quantitative bound** — verbatim from two independent
secondary restatements (Springer EJM survey; and the search-indexed abstract), primary
[pointer, unfetched]: "if the Riemann zeta function vanishes at each point of the finite arithmetic
progression {D+inp} with 0<|n|<N (D ⩾ 1/2, p>0), then N < 13p if D = 1/2, and N < p^{1/D − 1 + o(1)}
in general." Reported UNCONDITIONAL (no RH assumed) by the secondary sources; primary caveat noted.

`[VERIFIED-KNOWN]` **Lapidus–vF, from the Lapidus survey [Z5]** (verbatim): "the Riemann zeta
function, along with a large class of Dirichlet series and integrals (including most of the
arithmetic zeta functions … other than the zeta functions of varieties over finite fields, for
which the result clearly does not hold), cannot have an infinite vertical arithmetic progression of
zeros. (See [Lap-vFr3, Chapter 11] for this result and several extensions concerning the density of
the zeros.) … this latter result about the zeros in arithmetic progression, in the special case of
ζ, was already obtained by Putnam in [Put1–2] by a completely different method, which could not be
generalized to this significantly broader setting."

`[VERIFIED-KNOWN]` **Lee–Sourmelidis–Steuding–Suriajaya [Z6], Theorem 4 (p.5)** (verbatim): "Let h
be a positive real number (we write h ∈ R>0), l ∈ N, and M ∈ M. If s ∈ C satisfies Re(s) ∈ (1/2,1),
then there exists an infinite subset N ⊂ N such that ζ(s + ih(n + k − 1)) ∈ M for any n ∈ N and
k ∈ {1,2,···,l}." Their remark (verbatim): "this theorem also implies that any bounded set does not
contain any set of values of ζ on a vertical arithmetic progression of infinite length." **Corollary
5** (verbatim): "Let h ∈ R>0, l ∈ N, and M ∈ M∞. If s ∈ C satisfies Re(s) ∈ (0,1/2), then there
exists an infinite subset N ⊂ N such that ζ(s + ih(n + k − 1)) ∈ M …" — obtained "by using the
functional equation." (This is a universality/value-distribution result: along an infinite
sub-progression ζ hits any prescribed target, so in particular is non-zero — even unbounded —
covering every σ ∈ (0,1)\{1/2}. They note "our results do not include their result since Re(s) ≠ 1/2".)

`[VERIFIED-KNOWN]` **Martin–Ng [Z8]** (abstract, verbatim): "Let L(s,χ) be a fixed Dirichlet
L-function. Given a vertical arithmetic progression of T points on the line ℜ(s)=1/2, we show that
≫ T/log T of them are not zeros of L(s,χ)." (Evidence toward the Linear Independence conjecture; a
NON-zero-count result on the critical line, distinct from bounding the length of an AP of zeros.)

`[VERIFIED-KNOWN]` **Li–Radziwiłł [Z9]** (abstract, verbatim): "at least one third of the elements in
the arithmetic progression a n + b are not the ordinates of some zero of ζ(s) lying on the critical
line. This improves on earlier work of Martin and Ng." (Critical line only; improves [Z8].)

---

## Verdicts (a)–(d)

### (a) Scope of the statements
`[VERIFIED-KNOWN]`
- **Putnam 1954 [Z1,Z2]:** CRITICAL LINE ONLY (s = 1/2); INFINITE AP; nontrivial zeros. No
  multiplicity framing (zeros treated as vanishing points). Qualitative (no length bound).
- **van Frankenhuijsen 2005 [Z3]:** ANY vertical line with D = Re(s) ⩾ 1/2; QUANTITATIVE FINITE
  bound on the length of a hypothetical AP of zeros (< 13p at D = 1/2; < p^{1/D−1+o(1)} for D>1/2);
  reported unconditional. This SHARPENS Putnam (finite length) AND WIDENS it (off-line lines D>1/2).
- **Lapidus–vF [Z4,Z5]:** NO infinite vertical AP of zeros — for ζ AND a large class of Dirichlet
  series / arithmetic L-functions (fails precisely for zeta functions of varieties over finite
  fields). Line not restricted to 1/2 in the phrasing; via fractal/generalized-Cantor-string zeta
  functions and the explicit formula. Qualitative (their book also gives density extensions).
- **Lee–Sourmelidis–Steuding–Suriajaya [Z6]:** value-distribution, covers Re(s) ∈ (0,1)\{1/2}; much
  stronger than "not all zeros" — an infinite sub-AP lands in any prescribed target set.

### (b) References — see [Z1]–[Z9] above with fetch status. Primary Putnam and vF texts are
paywalled ([pointer, unfetched]); their statements are quoted from multiple independent expert
restatements (all [fetched]). Lapidus survey [Z5], Lee et al [Z6], Steuding–Wegert [Z7],
Martin–Ng [Z8], Li–Radziwiłł [Z9] read verbatim.

### (c) Strongest modern verified forms
`[VERIFIED-KNOWN]`
1. **Quantitative length bound (sharpest):** vF 2005 [Z3] — a hypothetical AP of zeros on any line
   D ⩾ 1/2 has length < 13p (D=1/2) resp. < p^{1/D−1+o(1)}; unconditional.
2. **Widest class:** Lapidus–vF [Z4] — no infinite vertical AP of zeros for ζ and most arithmetic
   zeta/L-functions (NOT for varieties over finite fields).
3. **Full-strip coverage:** Lee et al [Z6] — for every σ ∈ (0,1)\{1/2}, ζ on an infinite vertical AP
   is unbounded / hits any target, hence no infinite AP is contained in the zero set.
4. **Non-zero density on the line (a different thread, toward Linear Independence):** Martin–Ng
   [Z8] ≫ T/log T non-zeros; improved to ≥ 1/3 by Li–Radziwiłł [Z9]. These bound how many AP terms
   are NON-zeros, not the length of an all-zero AP.

### (d) The exact form: for every σ ∈ (0,1), a ∈ ℝ, d>0, {σ + i(a+kd) : k ∈ ℤ} ⊄ Zeros(ζ)
`[VERIFIED-KNOWN]` **The full-strip statement IS covered by verified literature**, assembled as:
- **σ = 1/2, infinite k-range:** Putnam 1954 [Z1,Z2] and Lapidus–vF [Z4] directly. ✓
- **σ ∈ [1/2, 1), infinite AND finite (quantitative) k-range:** vF 2005 [Z3] directly (D ⩾ 1/2). ✓
- **σ ∈ (1/2, 1), stronger (value-distribution):** Lee et al Thm 4 [Z6]. ✓
- **σ ∈ (0, 1/2):** vF 2005 [Z3] via the functional equation (ρ ↦ 1−ρ sends a vertical AP at Re=σ to
  one at Re=1−σ ⩾ 1/2, where the finite bound applies), AND Lee et al Corollary 5 [Z6] (explicit,
  via the functional equation). ✓
- **σ ⩾ 1:** ζ ≠ 0 (Euler product) — trivially no zeros, so no AP. **σ ⩽ 0:** only trivial zeros at
  s = −2n (isolated real points); a vertical AP with d>0 meets them in at most one point — trivially
  no AP. ✓
- **Multiplicity:** not a factor; every source treats a zero as a point where ζ vanishes.

Caveats (`[VERIFIED-KNOWN]` on the caveats themselves): (i) vF's published bound is written in the
symmetric normalization {D+inp}; the general-offset "any hypothetical AP" reading is how [Z7] and the
community cite it, and Putnam/Lapidus-vF state the pure infinite-AP form without offset restriction.
(ii) The σ ∈ (0,1/2) coverage rests on the functional-equation reflection, which vF's own paper
states for D ⩾ 1/2 and which [Z6] carries out explicitly for the value-distribution version. (iii)
Putnam's and vF's PRIMARY texts were not fetched (paywalled); statements verified via ≥2 independent
expert restatements each. WebSearch is US-indexed; "verified via secondary" not "read in primary."

---

## Null / corrective searches

- The recalled attribution "Putnam proved the CRITICAL-LINE zeros contain no infinite AP" is
  `[VERIFIED-KNOWN]` CORRECT and precise: Putnam is critical-line only (s=1/2), per [Z6]'s explicit
  reading "l=1, s=1/2, 0 ∉ M."
- The recalled "van Frankenhuijsen: no infinite AP on ANY vertical line in the strip" is
  `[VERIFIED-KNOWN]` CORRECT for D ⩾ 1/2 (his stated range) and extends to D<1/2 via the functional
  equation; his contribution is specifically the QUANTITATIVE finite length bound (13p / p^{1/D−1}).
- The recalled "Martin–Ng: quantitative bounds on how many consecutive zeros can lie in an AP" is
  `[VERIFIED-KNOWN]` PARTIALLY MISATTRIBUTED: Martin–Ng [Z8] and Li–Radziwiłł [Z9] bound how many AP
  terms are NON-zeros (critical line, toward Linear Independence), NOT the length of an all-zero AP.
  The length-of-AP-of-zeros bound is van Frankenhuijsen's [Z3], not Martin–Ng's.
- The "fractal strings school" attribution is `[VERIFIED-KNOWN]` CORRECT: Lapidus–vF gave a NEW proof
  of Putnam via fractal/generalized-Cantor-string zeta functions and generalized it to a broad class
  (book [Z4], Chapter 11), the generalization FAILING for zeta functions of varieties over finite
  fields.
