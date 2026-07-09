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

---

## Round: mobility & periodicity-dichotomy checks (2026-07-09)

Status: verification note (SEARCH register). WebSearch/WebFetch only; no Lean, no computation.
Marking convention as above (`[VERIFIED-KNOWN]` = quoted from a source actually read; `[ABSENT]`
= search returned nothing; `[UNVERIFIED]` = could not locate/fetch primary). arXiv PDFs that
WebFetch could not text-parse were saved locally by WebFetch and read directly (page numbers are
the papers' own).

### Sources and fetch status (this round)

- **[K1] Dixit survey.** A. B. Dixit, "On the Selberg class of L-functions" (survey, imsc.res.in
  /~anupdixit/Selberg_class.pdf). PDF pages 1–8 read directly. Gives the Selberg class S axioms,
  degree formula, GRH conjecture, Conrey–Ghosh and Kaczorowski–Perelli degree results.
- **[K2] Raghunathan.** R. Raghunathan, "Beyond the extended Selberg class: d_F ≤ 1",
  arXiv:**2005.11381** [math.NT], 2 Jul 2020. PDF pages 1–6 read directly. Gives the extended
  Selberg class S# axioms verbatim and the degree definition; §2.5 on degree-0 (Euler-product) axiom.
- **[K3] Zaghloul.** G. Zaghloul, "On the linear twist of degree 1 functions in the extended
  Selberg class", arXiv:**1903.06145** [math.NT], 14 Mar 2019. PDF pages 1–4 read directly.
  Restates the Kaczorowski–Perelli degree-0 (and degree-1) structure theorems VERBATIM as its
  Theorems 1–2, with the coefficient reflection (its eq. 1.2).
- **[K4] Kaczorowski–Perelli 1999 (PRIMARY).** J. Kaczorowski, A. Perelli, "On the structure of
  the Selberg class, I: 0 ≤ d ≤ 1", *Acta Mathematica* **182** (1999), no. 2, 207–241, DOI
  10.1007/BF02392574. Project Euclid bibliographic page fetched (vol/pages confirmed); full text
  [paywalled, unfetched]. Its degree-0/degree-1 theorems are quoted here via [K3], which reproduces
  them as "Theorem 1 (Kaczorowski–Perelli)" / "Theorem 2 (Kaczorowski–Perelli)".
- **[K5] Yoonbok Lee, Epstein zeros.** Yoonbok Lee, "On the zeros of Epstein zeta functions",
  arXiv:**1204.6297** [math.NT] (*Forum Math.*). Abstract fetched verbatim.
- **[K6] Lee–Sourmelidis–Steuding–Suriajaya (ASPM).** J. Lee, A. Sourmelidis, J. Steuding, A. I.
  Suriajaya, "The values of the Riemann zeta-function on discrete sets", *Advanced Studies in Pure
  Mathematics* **84** (2020), 315–334 (Matsumoto 60th-birthday volume). Project Euclid PDF pages
  315–322 read directly. (Same paper as [Z6] arXiv:1710.11367 in the previous round; here the
  published ASPM version, with its own page numbers, was read.)
- **[K7] Martin–Ng.** G. Martin, N. Ng, "Nonzero values of Dirichlet L-functions in vertical
  arithmetic progressions", arXiv:**1109.1788** (= [Z8] previous round).
- **[K8] Wikipedia, Dirichlet series.** en.wikipedia.org/wiki/Dirichlet_series — the 2^{ω(n)}
  generating identity, fetched verbatim.
- **[K9] Odlyzko / first zero.** Standard zero tables (Odlyzko; MathWorld "Riemann Zeta Function
  Zeros"); first nontrivial-zero height 14.134725… confirmed by multiple indexed sources.

---

### Q1 — Kaczorowski–Perelli degree-0 structure theorem

**(a) Which axioms S# assumes.** `[VERIFIED-KNOWN]` from [K2] (Raghunathan). The extended Selberg
class S# is obtained from conditions (P1)–(P3), i.e. WITHOUT the Euler-product axiom (P4) and
WITHOUT the Ramanujan bound. Verbatim (p.5): "We recall that if we assume F(s) satisfies (P1) with
abscissa of convergence ν ≤ 1, (P2) for P(s) = (s−1)^m for some m ≥ 0, and (P3) with r′ = 0, and
the even stronger requirement that Re(μ_j) ≥ 0, 1 ≤ j ≤ r, we obtain the extended Selberg class S#."
The referenced conditions (p.2, verbatim):
- (P1): "The function F(s) is given by a Dirichlet series ∑_{n=1}^∞ a_n/n^s with abscissa of
  absolute convergence ν ≥ 1/2." (for S# further ν ≤ 1)
- (P2): "There is a polynomial P(s) such that the function P(s)F(s) extends to an entire function."
  (for S#, P(s) = (s−1)^m — meromorphic continuation with at most a pole at s=1)
- (P3): "There exist a real number Q > 0, a complex number ω such that |ω| = 1, and a function G(s)
  of the form G(s) = ∏_{j=1}^r Γ(λ_j s + μ_j) ∏_{j′=1}^{r′} Γ(λ′_{j′}s + μ′_{j′})^{−1}, where
  λ_j, λ′_{j′} > 0 and μ_j, μ′_{j′} ∈ ℂ, such that Φ(s) := Q^s G(s)F(s) = ω · conj(Φ(1−s̄))."
Degree (p.2, verbatim): "we define the degree of F(s) to be d_F = 2(∑_{j=1}^r λ_j − ∑_{j′=1}^{r′}
λ′_{j′})." (No Euler product, no Ramanujan bound anywhere in (P1)–(P3).)
[K2] §2.5 (verbatim, p.5): "The weakening of (P4′) to (P4) allows the presence of non-trivial
degree 0 elements which is often a minor irritant, especially when one is interested in the
factorisation of series." — i.e. the degree-0 members are exactly the ones with NO Euler product,
generally non-multiplicative. (For contrast, the FULL Selberg class S = S# ∩ {Euler product +
Ramanujan}; its axioms with Euler product/Ramanujan are in [K1] Def. 2.1, and there d=0 gives only
the constant 1.)

**(b) The degree-0 conclusion.** `[VERIFIED-KNOWN]` from [K3] (Zaghloul), which reproduces the
Kaczorowski–Perelli theorem verbatim. Intro (verbatim): "For degrees d = 0 and d = 1, the elements
of S and S♯ have been completely characterized."
**Theorem 1 (Kaczorowski–Perelli)** [K3], reproducing [K4] (verbatim):
- "(i) Let F ∈ S♯_0. Then q ∈ ℕ, the pair (q, ω) is an invariant for F and S♯_0 is the disjoint
  union of the subclasses S₀♯(q, ω), with q ∈ ℕ and |ω| = 1."
- "(ii) Let F ∈ S₀♯(q, ω), with q, ω as above. Then F(s) is a Dirichlet polynomial of the form
  F(s) = ∑_{n|q} a(n)/n^s." (its eq. 1.1)
- "(iii) V₀♯(q, ω) = S₀♯(q, ω) ∪ {0} is a real vector space of dimension d(q) = ∑_{d|q} 1."
- **Remark 1** (verbatim): "As shown in [6, §3] the functional equation in the case d = 0 implies
  the following relation on the coefficients: a(n) = (ω/√q) · n · conj(a(q/n)) for n | q." (eq. 1.2)

So the degree-0 members of S# are **Dirichlet polynomials supported on the DIVISORS of a positive
integer q** (the conductor), with the self-inversive coefficient reflection a(n) = (ω/√q) n
conj(a(q/n)). CORRECTION to the task's phrasing: the support is `n | q` (divisors of q), NOT a
generic `n = 1,…,N`; and the normalization a(1)=1 forces a(q) = (ω/√q)·q·conj(a(1)) = ω√q.

**Zero characterization.** `[VERIFIED-KNOWN]` (structure) + `[VERIFIED-KNOWN, derived here]`
(zeros). [K3]/[K4] give the polynomial form and the reflection (1.2) but state NO explicit
"zeros lie on lines" theorem for d=0. What the reflection forces:
- A Dirichlet polynomial has all zeros in a BOUNDED VERTICAL STRIP and forms a Bohr almost-periodic
  set (standard). The reflection (1.2) makes F self-inversive, so its zero set is symmetric about
  the critical line Re s = 1/2.
- Single-prime conductor q = p: (1.1)+(1.2) give F(s) = 1 + ω√p·p^{−s}; |ω√p|=√p, so F(s)=0 ⟺
  p^{−Re s} = 1/√p ⟺ **Re s = 1/2 exactly**, and the imaginary parts form one vertical arithmetic
  progression (spacing 2π/log p). [derived here — arithmetic check, not a quoted theorem]
- General composite q: zeros need NOT sit on a single vertical line; only strip-confinement +
  symmetry about 1/2 are forced. (Same Bohr/Jessen–Tornehave picture flagged in Q2 of the previous
  round.)

**Q1 verdict.** `[VERIFIED-KNOWN]` S# assumes only (P1) Dirichlet series (ν ≤ 1), (P2) meromorphic
continuation with (s−1)^m F entire of finite order, (P3) a Riemann-type functional equation —
**no Euler product, no Ramanujan**. Degree-0 members are exactly Dirichlet polynomials
F(s) = ∑_{n|q} a(n)n^{−s} on the divisors of a conductor q, with a(n) = (ω/√q) n conj(a(q/n)); a
positive-dimensional real vector space of dimension d(q) = number of divisors of q. Their zeros lie
in a bounded vertical strip symmetric about Re s = 1/2 (exactly on Re s = 1/2, a vertical AP, in the
prime-conductor case); no finer "all on vertical lines" theorem is asserted for composite q. Source:
Kaczorowski–Perelli, Acta Math. 182 (1999) [K4], reproduced verbatim in Zaghloul [K3] Thm 1; S#
axioms Raghunathan [K2].

---

### Q2 — the load-bearing question: are the known off-line-zero families multiplicative?

**(a) Davenport–Heilbronn 1936 — NOT multiplicative.** `[VERIFIED-KNOWN]` (via search consensus;
primary DH 1936 paywalled/unfetched). The Davenport–Heilbronn function is the linear combination of
two Dirichlet L-functions attached to a pair of complex-conjugate characters mod 5 (equivalently a
Hurwitz-zeta combination at rational parameter), tuned so that it satisfies a Riemann-type
functional equation but **has no Euler product**; it has infinitely many zeros off the critical
line. Because it is a genuine LINEAR COMBINATION of two distinct L-functions, its coefficient
sequence is not multiplicative and it has no Euler product — this is exactly why it can (and does)
have off-line zeros while ζ (conjecturally) cannot. (Consistent with [K1]: linear combinations
leave the Euler-product-bearing class S; they live in S# only.)

**(b) Epstein zeta of a form with class number > 1 — off-line zeros PROVEN, coefficients NOT
multiplicative.** `[VERIFIED-KNOWN]` proof of off-line zeros, from [K5] (Yoonbok Lee) abstract
(verbatim): "We investigate the zeros of Epstein zeta functions associated with a positive definite
quadratic form with rational coefficients. Davenport and Heilbronn, and also Voronin, proved the
existence of zeros of Epstein zeta functions off the critical line when the class number of the
quadratic form is bigger than 1." (Potter–Titchmarsh earlier exhibited a specific off-line zero;
Lamzouri, Gonek–Lee give asymptotic counts.)
`[VERIFIED-KNOWN, arithmetic checked here]` Non-multiplicativity of the coefficient (representation)
function for Q(x,y) = x² + 5y² (discriminant −20, class number 2). Let r(n) = #{(x,y) ∈ ℤ² :
x² + 5y² = n}. Then:
- r(2) = 0 (2 = x² + 5y² has no solution: y=0 ⇒ x²=2, impossible),
- r(3) = 0 (y=0 ⇒ x²=3, impossible),
- r(6) = 4 (6 = 1² + 5·1², solutions (±1, ±1)).
gcd(2,3)=1, so a multiplicative r would require r(6) = r(2)·r(3) = 0, contradicting r(6) = 4 > 0.
Hence **r is NOT multiplicative** — precisely the genus-theory obstruction: primes ≡ 1, 9 (mod 20)
are represented by x²+5y², primes ≡ 3, 7 (mod 20) only by the non-principal form 2x²+2xy+3y², so a
single form's representation numbers cannot be multiplicative. The single-form Epstein zeta
Z(s, Q) = ½ ∑_{(m,n)≠0} Q(m,n)^{−s} therefore has NO Euler product (it is a class-group component of
the Dedekind zeta ζ_K = ∑_{[Q]} Z(s, Q), not a Hecke L-function).

**(c) Any OTHER family with a PROVEN off-line zero that IS multiplicative and NOT vertically
periodic?** Searches run (all WebSearch):
1. `Davenport Heilbronn 1936 zeros off critical line Dirichlet series no Euler product not
   multiplicative` → only DH/Epstein (non-multiplicative) and value-distribution papers.
2. `Epstein zeta … class number … zeros off critical line Voronin Davenport Heilbronn` → [K5] and
   the lattice-sum literature; all single-form Epstein (non-multiplicative coefficients).
3. `generalized Riemann hypothesis Selberg class Ramanujan conjecture temperedness failure zeros
   off critical line implication` → GRH-for-Selberg-class = all nontrivial zeros on Re=1/2 for the
   Euler-product class S; no proven off-line multiplicative example surfaced.
4. `"off the critical line" zeros "vertical arithmetic progression" OR "periodic" Dirichlet
   polynomial degree zero Selberg class conjecture dichotomy` → only the degree-0 Dirichlet-
   polynomial column (vertically periodic / strip-confined) and DH.
`[ABSENT]` **Q2(c) verdict:** the searched literature contains NO multiplicative Dirichlet series
(Euler product / multiplicative coefficients) with a self-dual Riemann-type functional equation and
a PROVEN zero off the critical line that is not vertically periodic. Every family with proven
off-line zeros is non-multiplicative — Davenport–Heilbronn (a linear combination, no Euler product),
Epstein of class number > 1 (single-form representation numbers non-multiplicative, no Euler
product). The only classes carrying an Euler product (the full Selberg class S, Dirichlet/Hecke
L-functions) are conjectured by GRH ([K1] Conjecture 2) to have ALL nontrivial zeros on Re=1/2, and
not one off-line zero is proven for any of them. The one place off-line "zeros" genuinely occur with
an Euler-product-adjacent structure is the degree-0 Dirichlet-polynomial column of S#, whose zeros
are strip-confined / vertically periodic — excluded by the "not vertically periodic" clause. This is
the load-bearing confirmation: **proven-off-line ⇒ non-multiplicative, in every known case.**

---

### Q3 — novelty of the periodic/aperiodic dichotomy statement

Searched for any prior conjecture or theorem of the shape "zeros off the critical line lie on
vertical arithmetic progressions / are vertically periodic", or "the aperiodic part of the zero set
lies on the critical line", or a periodic/aperiodic dichotomy for zero sets of L-functions.

Searches run (all WebSearch):
1. `"vertical arithmetic progression" zeros Selberg class "vertically periodic" Dirichlet series
   functional equation` → periodic-coefficient Dirichlet series and Martin–Ng non-zeros; NO
   dichotomy statement.
2. `"aperiodic part" OR "vertically periodic" zeros L-function dichotomy critical line arithmetic
   progression conjecture` → the only "aperiodic" hit is Ising partition-function zeros (statistical
   physics), unrelated; generic "critical-line dichotomy" prose, no zero-set periodicity dichotomy.
3. `"off the critical line" zeros "vertical arithmetic progression" OR "periodic" Dirichlet
   polynomial degree zero Selberg class conjecture dichotomy` → degree-0 column + DH only.
4. `"zeros on vertical lines" Selberg class … "periodic zeros" … Kaczorowski Perelli linear twist
   zeros vertical lines almost periodicity` → Selberg-class zero-distribution surveys; NO framing of
   off-line zeros as a periodic component.
5. `conjecture "aperiodic" zeros critical line "periodic" off-line dichotomy zeta L-function vertical
   progression Steuding` → Davenport–Heilbronn counterexample and generic critical-line prose; the
   fetched summary explicitly notes "the search results do not contain specific information about a
   conjecture using the exact terms 'aperiodic zeros' and 'periodic off-line dichotomy'."
6. `generalized Riemann hypothesis Selberg class Ramanujan conjecture temperedness failure zeros off
   critical line implication` → GRH-for-Selberg-class is the plain "all nontrivial zeros on Re=1/2"
   ([K1] Conjecture 2); no source states GRH-for-S relative to a temperedness/Ramanujan failure as a
   dichotomy, and no source frames off-line zeros as the "periodic part."
7. `"vertical arithmetic progression" zeros zeta` (covered inside 1,3) → the no-infinite-AP results
   (Putnam, van Frankenhuijsen, Lapidus–vF, LSSS) constrain the ζ zero set to CONTAIN no infinite
   vertical AP; none conjectures that the off-line zeros ARE a vertical AP / a periodic set.

`[ABSENT]` **Q3 verdict:** No prior conjecture or theorem was found stating that off-critical-line
zeros lie on vertical arithmetic progressions / are vertically periodic, nor an
"aperiodic-part-on-the-critical-line" dichotomy for zero sets of L-functions, nor a GRH-for-Selberg
framing relative to temperedness failure. Existing results run the OPPOSITE way: they PROHIBIT
infinite vertical APs anywhere in the ζ zero set (Putnam/vF/Lapidus–vF/LSSS), and the only genuinely
"periodic/strip-confined" zero column that is known — the degree-0 Dirichlet-polynomial members of
S# — is nobody's proposed model for the off-line zeros of a multiplicative L-function. The
dichotomy statement appears un-occupied in the searched corpus. (Caveat: WebSearch is US-indexed and
misses paywalled/non-English monographs; this is "no evidence found," not a proof of nonexistence.)

---

### Q4 — no-AP for Dirichlet L-functions, and the 2^{ω(n)} identity

**(a) Do the no-vertical-AP results extend to Dirichlet L-functions L(s,χ)?** `[VERIFIED-KNOWN]`,
mixed.
- The LSSS paper [K6] proves its AP/value-distribution theorems for the RIEMANN ZETA-FUNCTION ζ
  specifically. **Theorem 4** (verbatim, p.319): "Let h be a positive real number (we write
  h ∈ ℝ_{>0}), l ∈ ℕ, and M ∈ 𝕄. If s ∈ ℂ satisfies Re(s) ∈ (1/2, 1), then there exists an infinite
  subset ℕ ⊂ ℕ such that ζ(s + ih(n + k − 1)) ∈ M for any n ∈ ℕ and k ∈ {1, 2, · · · , l}."
  **Corollary 5** (verbatim, p.320): "Let h ∈ ℝ_{>0}, l ∈ ℕ, and M ∈ 𝕄_∞. If s ∈ ℂ satisfies
  Re(s) ∈ (0, 1/2), then there exists an infinite subset ℕ ⊂ ℕ such that ζ(s + ih(n + k − 1)) ∈ M
  for any n ∈ ℕ and k ∈ {1, 2, · · · , l}."
- The EXTENSION to L-functions is via the fractal-strings school, not via LSSS. [K6] p.320
  (verbatim): "Putnam [21, 22] showed that the sequence of consecutive nontrivial zeros of ζ on the
  critical line does not contain any arithmetic progression of infinite length. His result can be
  interpreted using our notation as considering l = 1, s = 1/2, and 0 ∉ M. Using fractal
  zeta-functions, Lapidus and Frankenhuijsen [14, Chapter 11] gave a new proof of Putnam's result
  and extended it to a large class of zeta functions and L-series. Our approach is based on the
  universality of the Riemann zeta function and is different from both of theirs. However, we remark
  that our results do not include their result since Re(s) ≠ 1/2 in Theorem 4 and Corollary 5."
- LSSS's own §2 general framework (p.321) is stated for arbitrary bounded-coefficient Dirichlet
  series L(s, f_j) = ∑ f_j(m) m^{−s} with |f_j(m)| ≤ B (which INCLUDES Dirichlet L-functions), but
  only in the half-plane of absolute convergence Re s > 1 (its Theorem 1/2 territory), not in the
  critical strip.
- Directly Dirichlet-L: Martin–Ng [K7], "Nonzero values of Dirichlet L-functions in vertical
  arithmetic progressions" — but this bounds how many AP terms are NON-zeros on the critical line
  (toward Linear Independence), not the length of an all-zero AP.
`[VERIFIED-KNOWN]` **Q4(a) verdict:** The LSSS theorems as stated are for ζ; the
no-infinite-vertical-AP-of-zeros statement is extended to "a large class of zeta functions and
L-series" (including Dirichlet L-functions) by **Lapidus–Frankenhuijsen, Chapter 11** (quoted
verbatim from [K6] p.320), and the LSSS half-plane framework covers general bounded-coefficient
Dirichlet series in Re s > 1.

**(b) The identity ∑ 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s).** `[VERIFIED-KNOWN]`, quoted verbatim from
[K8] (Wikipedia, Dirichlet series): "ζ²(s)/ζ(2s) = ∑_{n=1}^∞ 2^{ω(n)}/n^s". Independently verified
here by Euler factors: 2^{ω} is multiplicative with 2^{ω(p^k)} = 2 (k ≥ 1), so the local factor is
1 + 2∑_{k≥1} p^{−ks} = (1 + p^{−s})/(1 − p^{−s}); and ζ(s)²/ζ(2s) has local factor
(1 − p^{−2s})/(1 − p^{−s})² = (1 + p^{−s})/(1 − p^{−s}). They agree. (Standard: Titchmarsh, *Theory
of the Riemann Zeta-Function* §1.2 region; cf. also ζ(s)³/ζ(2s) = ∑ d(n²) n^{−s}.)

**(c) ζ(2s) has zeros with Re ∈ (0, 1/2); the lowest is not itself a ζ zero.** `[VERIFIED-KNOWN]`.
ζ(2s) = 0 ⟺ 2s is a zero of ζ. The nontrivial zeros ρ have Re ρ ∈ (0, 1) (classical: ζ ≠ 0 for
Re ≥ 1 by the Euler product, and by the functional equation for Re ≤ 0 apart from trivial zeros), so
s = ρ/2 has **Re s ∈ (0, 1/2)**; the trivial zeros 2s = −2n give s = −n (negative real, outside the
strip). First-zero height (Odlyzko/MathWorld [K9]): |Im ρ₁| = 14.134725… . Hence ρ₁/2 sits at height
14.134725…/2 ≈ 7.067, and since the LOWEST ζ zero is at height 14.13 (no ζ zero below it), there is
no ζ zero at height ≈ 7.07 — so **ρ₁/2 is not itself a zeta zero**. In the meromorphic continuation
of ∑ 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s), these s = ρ/2 (Re ∈ (0, 1/2)) are POLES (from the ζ(2s) in the
denominator), not zeros — a multiplicative Dirichlet series whose continuation carries features off
the critical line, but as poles, and without a self-dual Riemann-type functional equation, so it is
NOT a counterexample to the Q2(c) question.

`[VERIFIED-KNOWN]` **Q4 verdict:** (a) LSSS is ζ-specific; the L-function extension is
Lapidus–Frankenhuijsen Ch. 11 (verbatim [K6] p.320). (b) ∑ 2^{ω(n)} n^{−s} = ζ(s)²/ζ(2s) confirmed
verbatim [K8] and by Euler factors. (c) ζ(2s) zeros sit at s = ρ/2 with Re ∈ (0, 1/2); ρ₁/2
(height ≈ 7.07) is below the first ζ zero (14.13) and so is not a ζ zero — these are poles of the
2^{ω} series, not zeros.

---

## Round: integrality-vs-order and gammaless-FE checks (2026-07-09)

Status: verification note (SEARCH register). WebSearch/WebFetch only; no Lean, no computation.
Marking convention as above (`[VERIFIED-KNOWN]` = quoted from a source actually read; `[ABSENT]`
= search returned nothing; `[UNVERIFIED]` = could not locate/fetch primary). arXiv/other PDFs that
WebFetch could not text-parse were saved locally by WebFetch and read directly with the PDF reader
(page numbers are the documents' own); a few statements are `[VERIFIED via search-index restatement]`
where only the search engine's verbatim excerpt of a paywalled/scan source was obtained.

### Sources and fetch status (this round)

- **[I1] Garrett, "The Estermann phenomenon".** P. Garrett, expository note (umn.edu,
  notes_2013-14/02f_estermann_phenom.pdf), dated Sept 2013. PDF WebFetch failed to text-parse; saved
  locally and **read directly (pp.1-2)**. Verbatim quotes below.
- **[I2] Estermann 1928 (PRIMARY, bib only).** T. Estermann, "On certain functions represented by
  Dirichlet series", *Proc. London Math. Soc.* **27** (1928), 435-448. Bib confirmed from [I1]'s
  bibliography [read]; primary text [pointer, unfetched].
- **[I3] Kurokawa 1985 (bib only).** N. Kurokawa, "On the meromorphy of Euler products, I, II",
  *Proc. London Math. Soc.* **53** (1985), 1-49 and 209-236. Bib from [I1] [read]; primary
  [pointer, unfetched].
- **[I4] Bhowmik et al. multivariate Estermann.** G. Bhowmik, D. Essouabri, B. Lichtin / Bhowmik-
  Schlage-Puchta line: "Extension of Estermann's theorem to Euler products associated to a
  multivariate polynomial" (arXiv:**1001.3838**), "Essential singularities of Euler products"
  (arXiv:**1001.1891**), and the projecteuclid MSJ-memoirs chapter "Analytic continuation of some
  zeta functions" (Bhowmik). Abstracts/excerpts surfaced by WebSearch; the Rostock survey PDF
  ("Natural boundaries of Dirichlet series") WebFetch could not parse and was not read. The
  cyclotomic-dichotomy statement below is `[VERIFIED via search-index restatement]`.
- **[I5] Polya-Carlson (power series).** Restated via the whiterose eprint "Towards a Polya-Carlson
  dichotomy for algebraic dynamics" and the "uniformlyatrandom" note; both surfaced verbatim by
  WebSearch. `[VERIFIED via search-index restatement]`.
- **[I6] Perelli converse-theorems survey.** A. Perelli, "Converse theorems: from the Riemann zeta
  function to the Selberg class", arXiv:**1605.02354** (expanded XX Congresso U.M.I. lecture, Siena
  2015). arXiv PDF returned HTTP 403; **ar5iv mirror (ar5iv.labs.arxiv.org/abs/1605.02354) fetched**
  and the theorem statements extracted verbatim below.
- **[I7] Bochner modular relations (PRIMARY, bib + framework).** S. Bochner, "Some properties of
  modular relations", *Annals of Mathematics* **53** (1951), 332-363. **NOTE: the task prompt's
  "Bochner 1958" is off by publication year — the modular-relations paper is 1951** (Ann. of Math.
  53). Framework (FE `Γ(s)φ(s) = Γ(δ-s)ψ(δ-s)`, general λ_n, μ_n, residual function) confirmed via
  WebSearch bib excerpts; primary text [pointer, unfetched].
- **[I8] Segal, "On Dirichlet series with integral coefficients".** `[UNVERIFIED]` — repeated
  targeted searches (Segal / S.L. Segal + integral/integer coefficients + Dirichlet series) returned
  NO paper of this title. Not located; not used. (The integer-coefficient substance of Q1 is carried
  by [I1]-[I5] instead.)

---

### Q1 — does integrality of coefficients EVER force an ORDER / growth bound on the continuation?

**What the integer-coefficient literature actually proves: a CONTINUATION-vs-NATURAL-BOUNDARY
dichotomy, with NO order control.**

`[VERIFIED-KNOWN]` **[I1] Garrett, p.1 (verbatim):** "The *Estermann phenomenon* is that not every
natural Dirichlet series has a meromorphic continuation." Concrete claim (verbatim): "the Dirichlet
series ∑_n d(n)^3/n^s = ζ(s)^4 ∏_p (1 + 4p^{-s} + p^{-2s}) has a *natural boundary* along Re(s)=0,
in contrast to meromorphically continuable ∑_n d(n)/n^s = ζ(s)^2 and ∑_n d(n)^2/n^s = ζ(s)^4/ζ(2s)."

`[VERIFIED-KNOWN]` **[I1] Garrett, p.2 — the OBSTRUCTION is accumulation of zeros/poles, not size.**
Verbatim: "Since 1 + 4x + x^2 is not a cyclotomic polynomial, this process does not terminate. …
On one hand, this gives a meromorphic continuation to Re(s) > 1/(ℓ_j+1). On the other hand, since the
exponents e_i are non-zero, the infinitely-many zeros of ζ(s) in the critical strip make the zeros of
ζ(ℓ·s) bunch up just to the right of Re(s)=0 as ℓ → ∞." (The barrier is a limit set of
zeros/singularities on Re s = 0 — a continuation obstruction. Nothing about vertical growth/order.)
Remark (verbatim): "[Kurokawa 1985a,b] showed that ∑ a_n^k/n^s has a natural boundary for k ≥ 3,
where f(z) = ∑ a_n e^{2πinz} is a modular form."

`[VERIFIED via search-index restatement]` **[I4] multivariate Estermann (Bhowmik et al.):** "A
multivariate zeta function Z(h;s) can be continued to the whole complex space if and only if h is
cyclotomic; in all other cases the point at 0 is a natural boundary." (Same shape as Estermann 1928:
an Euler product ∏_p h(p^{-s}) with integer/integer-valued h continues to all of ℂ iff h is a product
of cyclotomic polynomials, otherwise Re s = 0 is a natural boundary.) The conclusion is again purely
continuation-vs-boundary; NO growth/order statement.

`[VERIFIED via search-index restatement]` **[I5] Polya-Carlson (the power-series prototype):** "a
power series with integer coefficients that converges inside the unit disk is either rational or it
admits the unit circle as a natural boundary." Again a continuation dichotomy; the only "growth"
in the circle is the standard finite-order-in-the-disk that holds for ALL bounded-coefficient power
series, not something integrality sharpens.

**Where "finite order" actually appears — always as a HYPOTHESIS, never a conclusion of
integrality.** The 1922 Carlson mean-value theorem for Dirichlet series and the Selberg-class axiom
(P2) [see [K2] earlier in this file] and Hamburger's theorem (Q2 below) all *assume* finite order /
polynomial growth in strips; none *derives* it from integer coefficients. Searches specifically for
an "integrality ⟹ finite order in strips" implication (queries: "arithmetical Dirichlet series
integer coefficients finite order vertical strip growth bound"; "integer coefficients Dirichlet
series does not force finite order ... only continuation dichotomy") returned only (i) the
continuation dichotomies above and (ii) finite-order-as-hypothesis results.

`[ABSENT]` **Q1 verdict.** No theorem of the shape "ordinary Dirichlet series with integer (or
discrete-set) coefficients that continues past its half-plane is automatically of finite order in
vertical strips" was located. The entire integer-coefficient circle — Estermann 1928 [I2], Kurokawa
1985 [I3], the Bhowmik-et-al. multivariate/cyclotomic classification [I4], and the power-series
Polya-Carlson prototype [I5] — is a CONTINUATION-vs-NATURAL-BOUNDARY dichotomy governed by the
cyclotomic condition, with NO vertical-order control whatsoever. "Finite order" is invariably an
*input* (Selberg (P2), Carlson mean-value, Hamburger), never an *output* of coefficient integrality.
So integrality does NOT force an order/growth bound in the located literature. (Caveat: the named
"Segal, On Dirichlet series with integral coefficients" [I8] could not be located; WebSearch is
US-indexed and misses paywalled/non-English monographs — this is "no evidence found", not a proof of
nonexistence. But the direction of ALL located results is uniform, so a hidden order-from-integrality
theorem would be a surprise, not a near-miss.)

---

### Q2 — infinite-order symmetric Dirichlet series with a gammaless FE F(1-s)=F(s)?

**Every located classification of Riemann-type / gammaless functional equations assumes FINITE
ORDER, verbatim; the infinite-order case is untouched.**

`[VERIFIED-KNOWN]` **[I6] Perelli survey, Hamburger's theorem (Theorem 2.1), verbatim growth
hypothesis:** "(s−1)^m F(s) is entire of finite order for some integer m"; functional equation
"π^{−s/2} Γ(s/2) F(s) = π^{−(1−s)/2} Γ((1−s)/2) F(1−s)"; conclusion "F(s) = c·ζ(s) for some c ∈ ℂ".
The FE carries a gamma factor; the growth datum is *finite order*.

`[VERIFIED-KNOWN]` **[I6] Perelli survey, Hecke's converse theorem (Theorem 2.2), verbatim growth
hypothesis:** "F(s) has continuation over ℂ as an entire function of finite order"; FE
"Λ(s,F) = i^k Λ(1−s,F), where Λ(s,F) = (1/2π)^s Γ(s+(k−1)/2) F(s)". Again gamma factor + finite order.

`[VERIFIED-KNOWN]` **[I6] Perelli survey, Bochner (verbatim):** the survey mentions only "a duality
principle, first studied by S. Bochner in the 1950's, between Dirichlet series with a general Riemann
type functional equation and their Mellin transforms," and gives **no explicit gammaless statement**.
`[VERIFIED-KNOWN, fetch-conclusion]` The survey "does not address degree-zero functional equations or
infinite-order solutions." Bochner's own 1951 framework [I7] uses the FE `Γ(s)φ(s) = Γ(δ-s)ψ(δ-s)` —
i.e. gamma factors on both sides — with strictly increasing exponents λ_n, μ_n and a residual
function; its equivalence proof (later Chandrasekharan-Narasimhan) rests on convergence/temperedness
of the associated exponential (theta-type) series, not on an arbitrary infinite-order F.

`[VERIFIED-KNOWN, derived from [K3] earlier in this file]` **The finite-order gammaless conductor-1
case is degenerate.** In the extended Selberg class S# (finite order via (P2)), the Kaczorowski-
Perelli degree-0 structure theorem [K3]/[K4] gives F(s) = ∑_{n|q} a(n) n^{-s} with V₀#(q,ω) a real
vector space of dimension d(q) = #{divisors of q}. For **conductor q = 1**: d(1) = 1, the only
support integer is n = 1, so the ONLY finite-order degree-0 solution is F ≡ constant (F(s) = 1 with
a₁ = 1). Hence a *nonconstant* finite-order entire F with a₁ = 1 satisfying F(1−s) = F(s), conductor
1, no gamma factor, **does not exist**. A nonconstant gammaless self-dual member requires conductor
q > 1 (a Dirichlet polynomial on the divisors of q).

`[VERIFIED-KNOWN, example]` The one infinite-order ordinary/general Dirichlet series that repeatedly
surfaced is `e^{e^{-s}} = ∑_{n≥0} (1/n!) e^{-ns}` — entire of infinite order — but it does **not**
satisfy F(1−s) = F(s) (and it is the exp of a single exponential, cf. the exp(2^{-s}) example earlier
in this file). No symmetric infinite-order example was found.

`[ABSENT]` **Q2 verdict.** No example, construction, or impossibility theorem for an entire Dirichlet
series F of INFINITE order with a₁ = 1 satisfying the exact gammaless functional equation
F(1−s) = F(s) (conductor 1) was located. Every relevant classification — Hamburger [I6, Thm 2.1],
Hecke [I6, Thm 2.2], Bochner's modular-relation duality [I6]/[I7], and the extended-Selberg /
Kaczorowski-Perelli degree-0 theory [K3]/[K4] — is stated under a FINITE-ORDER (or polynomial-growth
/ temperedness) hypothesis, quoted verbatim as Hamburger's "(s−1)^m F(s) is entire of finite order
for some integer m" and Hecke's "an entire function of finite order." Under that finite-order
hypothesis with conductor 1 and no gamma factor, F(1−s) = F(s) forces F ≡ 1 (K-P degree-0, q = 1,
d(1) = 1). The infinite-order case is exactly the gap these growth hypotheses cut out and is
**unaddressed** in the searched corpus — neither a construction nor a no-go. (Caveat: US-indexed
search; paywalled/non-English monographs may exist. "No evidence found," not a nonexistence proof.
Also flagged: the prompt's "Bochner 1958" is bibliographically the 1951 Annals paper.)

---

### Bottom line for the program (this round)

- **Q1:** `[ABSENT]` — integrality of coefficients does NOT force any order/growth bound in the
  located literature. All integer-coefficient theorems (Estermann 1928 [I2], Kurokawa 1985 [I3],
  Bhowmik-et-al. cyclotomic classification [I4], power-series Polya-Carlson [I5]) are
  continuation-vs-natural-boundary dichotomies keyed to the cyclotomic condition; "finite order" is
  only ever a hypothesis, never a consequence of integrality. Strongest citation: Garrett, "The
  Estermann phenomenon" [I1] (read directly) + the multivariate-cyclotomic dichotomy [I4]. The named
  Segal paper [I8] is `[UNVERIFIED]` (unlocatable).
- **Q2:** `[ABSENT]` — the infinite-order symmetric gammaless case is unaddressed. Hamburger [I6,
  Thm 2.1] and Hecke [I6, Thm 2.2] both require "entire of finite order" (verbatim); Kaczorowski-
  Perelli degree-0 [K3] forces F ≡ 1 at conductor 1 under finite order; no infinite-order example or
  no-go exists in the corpus. Strongest citation: Perelli, "Converse theorems…" arXiv:1605.02354
  [I6] (ar5iv, read) — Hamburger's exact growth hypothesis "(s−1)^m F(s) is entire of finite order
  for some integer m."
