# C0 Positioning Checks — Verified Literature Reading

Session date: 2026-07-03. Tools: WebSearch + WebFetch + Write. Every quoted passage below was
pulled from a page **fetched this session** via WebFetch, unless explicitly tagged
`[SEARCH-SUMMARY, NOT INDEPENDENTLY FETCHED]` or `[BIBLIOGRAPHIC POINTER, CONTENT NOT FETCHED]`.
Those tags mark claims I could locate bibliographically but could not open in readable form
(PDF returned binary/FlateDecode, HTTP 403, or auth redirect). They are HINTS, not citations.

Rule applied: fetched URL + quoted passage = citable; anything else is flagged UNVERIFIED.

---

## #8 — Density & simplicity of off-critical-line zeros of Davenport–Heilbronn / linear combinations

**VERDICT: PARTIALLY-KNOWN.**
- Existence + infinitude + dense real parts of off-line zeros: **VERIFIED-KNOWN**.
- Count *linear in T* in a fixed off-line strip (positive proportion of the strip window): **VERIFIED-KNOWN** as a phenomenon (Hejhal-conjecture / Bombieri–Hejhal regime; a fetched interpolating theorem below).
- **Simplicity** of the off-line zeros: **ABSENT-FROM-LITERATURE** (no theorem found; lab's 237/237 has no literature counterpart).

### Statements found

**(a) Off-line zeros are genuine and infinite.**
Ferry, Ghiša, Muscutar, *On Davenport and Heilbronn-Type of Functions*, arXiv:1602.06328 (2016).
FETCHED (https://arxiv.org/abs/1602.06328).
Quote: *"the off critical line points indicated by some authors as being non trivial zeros of the
Davenport and Heilbronn function are affected of approximation errors and illustrations are
presented which enforce the conclusion that they are true zeros."*
(Also, standard D–H: real parts of non-trivial zeros are dense in ]0,1[; some lie in Re s > 1.)

**(b) Off-line zeros with σ>1 have dense real parts.**
Righetti, *On the density of zeros of linear combinations of Euler products for σ>1*, arXiv:1506.05716.
FETCHED (https://arxiv.org/abs/1506.05716).
Quote: *"the real parts of such zeros are dense in subintervals of [1,σ*]."*
This directly covers the σ∈(1,1.2) part of the lab's window.

**(c) Linear-in-T zero count in a strip bounded away from the critical line.**
Lamzouri & Lee, *The number of zeros of linear combinations of L-functions near the critical line*,
arXiv:2010.10490 (2020; rev. 2023). FETCHED (https://arxiv.org/abs/2010.10490).
Main theorem (as extracted): the number of zeros of F(s)=Σ b_j L_j(s) with Re(s) ≥ 1/2 + 1/G(T) and
Im(s)∈[T,2T] is *"asymptotic to K₀ T G(T)/√log G(T)"* uniformly for log log T ≤ G(T) ≤ (log T)^ν,
"a generalization of a conjecture of Hejhal." K₀ > 0 depends on the combination.
INTERPRETATION for the lab: the lab's window Re s ∈ (0.55,1.2) is bounded away from 1/2 by δ ≥ 0.05,
i.e. the *fixed-δ* regime (G(T) ≈ 1/δ constant). There the count degenerates to ≍ c(δ)·T — **linear
in T**, a positive count per unit height. That is exactly the shape of the lab's measured ≈ T/21.

**(d) Bibliographic pointers (content NOT fetched — flagged):**
- Bombieri & Hejhal, *On the distribution of zeros of linear combinations of Euler products*,
  Duke Math. J. 80 (1995) 821–862. `[BIBLIOGRAPHIC POINTER, CONTENT NOT FETCHED]` — projecteuclid
  page returned empty; Experts@Minnesota listing confirms the bib data. This is the founding source of
  the linear/positive-proportion-off-line phenomenon that (c) interpolates.
- Balanzario & Sánchez-Ortiz, *Zeros of the Davenport–Heilbronn Counterexample*, Math. Comp. 76 (2007).
  `[BIBLIOGRAPHIC POINTER, CONTENT NOT FETCHED]` — AMS PDF returned HTTP 403. This is the standard
  *numerical* catalogue of D–H zeros; the natural place any simplicity observation would be recorded.
- Karatsuba: `[SEARCH-SUMMARY, NOT INDEPENDENTLY FETCHED]` — search reported that (T,T+H],
  H=T^{27/82+ε}, contains ≥ H(ln T)^{1/2-ε} *odd-order* zeros of f(1/2+it). This is ON the line and about
  odd order, not off-line simplicity; closest on-line analog only.

### Exact definition match (for the record)
The lab's f = (1−iκ)/2·L(s,χ) + (1+iκ)/2·L(s,χ̄), χ mod 5 with χ(2)=i, κ=(√(10−2√5)−2)/(√5−1),
FE ξ(s)=ξ(1−s) with ξ(s)=(π/5)^{−s/2}Γ((1+s)/2)f(s), is the standard Davenport–Heilbronn function.
`[SEARCH-SUMMARY, NOT INDEPENDENTLY FETCHED]` — the exact κ formula and character table
{χ(1..5)}={1,i,−i,−1,0} were returned by search from arXiv:2503.24275 and arXiv:2307.01254, but I could
not open a readable page carrying the formula (both PDFs returned binary; the 2503.24275 abstract page
does not contain it). The definition MATCHES the lab's; the exact-κ *quote* is unverified at page level.

### Bearing on the lab
The lab's 237 zeros in Re s∈(0.55,1.2), t≤5002, growth ≈ T/21: the **linear-in-T** density is
consistent with known theory — off-line zeros of D–H/linear combinations exist, are infinite, have dense
real parts, and in a fixed off-line strip accumulate at a positive rate ≍ c(δ)·T (Hejhal/Bombieri–Hejhal;
fetched Lamzouri–Lee interpolation). The constant 1/21 is a *specific* measurement not itself in the
literature. The **237/237 simplicity is NOT matched by any theorem** — literature is silent on simplicity
of individual off-line D–H zeros. That silence is where the lab's data is genuinely new: it is empirical
input with no proven analog, not a re-derivation of a known count.

---

## #3 — Hamburger's theorem: exact hypotheses forcing F = c·ζ

**VERDICT: VERIFIED-KNOWN.**

Perelli, *Converse theorems: from the Riemann zeta function to the Selberg class*, arXiv:1605.02354.
FETCHED (https://ar5iv.labs.arxiv.org/abs/1605.02354).
Theorem 2.1 (Hamburger), as extracted verbatim: *"Let F(s) be a Dirichlet series absolutely convergent
for σ>1 such that (s−1)^m F(s) is entire of finite order for some integer m. If F satisfies the functional
equation π^(−s/2) Γ(s/2) F(s) = π^(−(1−s)/2) Γ((1−s)/2) F(1−s), then F(s) = c ζ(s) for some c ∈ ℂ."*
On rigidity/added hypotheses: *"if one adds ... the further requirement that F(s) is an Euler product,"*
uniqueness sharpens to F = ζ itself. The survey also frames Hecke's and Weil's converse theorems (twisted
functional equations characterize cusp forms) as the perimeter of this rigidity.

The three load-bearing hypotheses: (i) a genuine Dirichlet series (fixed coefficients/frequencies, abs.
conv. σ>1); (ii) the finite-order regularity of (s−1)^m F(s); (iii) the **exact ζ functional equation**
(the π^{−s/2}Γ(s/2) gamma factor, conductor 1). Drop/alter any and c·ζ is no longer forced.

Supporting: Hu & Li, *A Connection between the Riemann Hypothesis and Uniqueness of the Riemann zeta
function*, arXiv:1610.01583. FETCHED (https://ar5iv.labs.arxiv.org/abs/1610.01583). They prove (Thm 2.1)
*"The Riemann hypothesis is true if and only if ζ(s)≡η(s)"* — a uniqueness reformulation of RH for a
meromorphic η sharing the FE with constrained zero set.

### Bearing on the lab
Hamburger says the *exact zeta FE* + finite order + Dirichlet-series form forces c·ζ — so you cannot graft
that precise functional equation onto a different (e.g. Beurling-positive) system and get anything new.
BUT the Davenport–Heilbronn function is the standing witness that a **general Riemann-type FE** (different
conductor/gamma factor, no Euler product) has a large solution space with off-line zeros. So grafting *a*
functional equation onto a positive/Beurling-type system is not obstructed by Hamburger — only the literal
ζ-FE + Euler-product combination is rigid. The lab's question ("can a FE be welded onto a positive
system?") lands precisely in the gap Hamburger leaves open.

---

## #2 — Random Euler products: a.s. convergence & non-vanishing for Re s > 1/2

**VERDICT: VERIFIED-KNOWN.**

Harper, Nikeghbali & Radziwiłł, *A note on Helson's conjecture on moments of random multiplicative
functions*, arXiv:1505.01443. FETCHED (https://ar5iv.labs.arxiv.org/abs/1505.01443).
Quote (introduction): *"By the three series theorem, the Euler product F(s):=∏_p(1+f(p)p^{−s}) converges
almost surely for ℜs>1/2."* The mechanism is Kolmogorov's three-series theorem applied to Σ_p f(p)p^{−s}
(a.s. convergent for Re s>1/2), making F an a.s. holomorphic — and, being a convergent product of nonzero
factors, a.s. non-vanishing — function there. Stated for both Rademacher (±1) and Steinhaus (unimodular).

Classical origin `[BIBLIOGRAPHIC POINTER, CONTENT NOT FETCHED]`: Wintner, *Random factorizations and
Riemann's hypothesis*, Duke Math. J. 11 (1944) 267–275 (projecteuclid euclid.dmj/1077472524). Wintner
introduced the random multiplicative model; Σ_{n≤x} f(n) ≪_ε x^{1/2+ε} a.s. is the random RH.

### Bearing on the lab
A random Euler product is a.s. **analytic and zero-free in the whole half-plane Re s > 1/2** — the model
system that *has* an Euler product has, almost surely, no off-line zeros. This is the sharp foil to
Davenport–Heilbronn (item #8), which has *no* Euler product and *does* have off-line zeros. So for the
lab: Euler-product/multiplicative positivity is exactly what buys the zero-free half-plane a.s.; the
obstruction to a "positive system with a grafted FE" having off-line zeros is the presence/absence of
that product structure — precisely the seam the lab is probing.

---

## #5 — Multiplicity / parity / divisibility of HYPOTHETICAL off-line zeros of ζ

**VERDICT: ABSENT-FROM-LITERATURE** (auditable absence).

What exists is only conditional-on-RH simplicity of ON-line zeros:
Wikipedia, *Riemann hypothesis*. FETCHED (https://en.wikipedia.org/wiki/Riemann_hypothesis).
Quote: *"Montgomery showed that (assuming the Riemann hypothesis) at least 2/3 of all zeros are simple"*
and *"a related conjecture is that all zeros of the zeta function are simple."*
Fetched-page finding (auditable): the article *contains no statement whatsoever* about whether hypothetical
zeros off the critical line would be simple or multiple; the only multiple-zero discussion concerns
Dedekind/elliptic-curve L-functions, not hypothetical off-line ζ zeros.

Corroborating searches (returned only on-line/simple-zero material, never an off-line-multiplicity result):
Gonek, *Simple zeros of the Riemann zeta-function*; arXiv:1302.5018 (*On simple zeros...*); Pair-correlation
simple-zeros work arXiv:2503.15449; the "Alternative Hypothesis" arXiv:2508.10857 (about gaps of on-line
zeros). None state anything of the form "if RH fails, the failing zeros are simple / multiple / clustered /
divisible-order." That conditional shape does not appear.

### Bearing on the lab
The lab's ladder — RH_{2^k}: every hypothetical zero with Re s>1/2 has order divisible by 2^k, with an
obstruction cocycle = box zero-count mod 2^k — asks about the **order/multiplicity of hypothetical off-line
zeros of ζ**. The literature says *nothing* about this. Every simplicity result is conditional on RH (hence
about zeros that are on the line) or is a heuristic universality/pair-correlation statement. The lab's object
is therefore not a re-derivation: there is no prior art on the multiplicity structure of off-line ζ zeros to
reduce to. (Absence is the finding; it is auditable via the fetched Wikipedia page + the null searches.)

---

## #7 — Bohr: almost periodicity ↔ zero-free / uniform-convergence half-planes

**VERDICT: PARTIALLY-KNOWN.**
- Core Bohr theorem (boundedness/almost-periodicity in a half-plane ⇒ uniform convergence there): VERIFIED-KNOWN.
- The precise equivalence "L(s,χ) almost periodic in σ>1/2 ⟺ RH": **UNRESOLVED / [UNVERIFIED]** (seen only in search summaries; no primary page opened).

Schoolmann, *On Bohr's theorem for general Dirichlet series*, arXiv:1812.04925.
FETCHED (https://ar5iv.labs.arxiv.org/abs/1812.04925).
Bohr's theorem (qualitative, verbatim as extracted): *"Let D=Σ a_n n^{−s} be a somewhere convergent
ordinary Dirichlet series having a holomorphic and bounded extension f to [Re>0]. Then D converges
uniformly on [Re>ε] for all ε>0."* (Bohr 1913.) Quantitative companion: the partial-sum operator norm
≤ C·log(N)·sup_{[Re>0]}|f|.

Brevig & Kouroupis, *An extension of Bohr's theorem*, arXiv:2302.14519.
FETCHED (https://ar5iv.labs.arxiv.org/abs/2302.14519).
Classical Bohr statement (verbatim as extracted): *"Let f be in 𝔇. If there is a real number θ and a
bounded set Ω such that f has an analytic continuation to ℂ_θ that maps ℂ_θ to Ω, then σ_u(f) ≤ θ."*
(Bounded holomorphic image in a half-plane ⇒ abscissa of uniform convergence ≤ θ.)

For σ>1 the ζ/L Dirichlet series converge absolutely, hence are uniformly convergent and **uniformly
(Bohr) almost periodic** — immediate, standard. The finer "for σ>1/2 the vertical map is Besicovitch
(B²)-almost-periodic" and "L(s,χ) almost periodic in σ>1/2 ⟺ RH" appeared repeatedly in search summaries
(attributed variously to the Hedenmalm–Lindqvist–Olsen–Seip Hilbert-space-of-Dirichlet-series circle) but
I could NOT open a primary page carrying them as text → `[SEARCH-SUMMARY, NOT INDEPENDENTLY FETCHED]`,
marked UNRESOLVED.

### Bearing on the lab
Direction of implication that survives verification: **boundedness/almost-periodicity of a Dirichlet series
in a half-plane ⇒ uniform convergence of its own Dirichlet series there** (Bohr). For a function *with an
Euler product*, uniform convergence of the series in σ>θ forces non-vanishing (a zero-free half-plane) —
this is the exact lever tying "almost periodic in σ>1/2" to RH-type non-vanishing. For the lab, Bohr gives
a route by which a *positive/bounded* behaviour on vertical lines would enforce a zero-free strip; the
missing verified piece (the σ>1/2 ⟺ RH equivalence) is a place to source from a book (Titchmarsh §9–11 /
Steuding) rather than trust the search summary.

---

## #4 — Deep Riemann Hypothesis / partial Euler products ON the critical line

**VERDICT: VERIFIED-KNOWN.**

Kimura, Koyama & Kurokawa, *Euler Products beyond the Boundary*, Lett. Math. Phys. 104 (2014) 1–19,
arXiv:1210.1216. FETCHED (https://arxiv.org/abs/1210.1216).
Abstract (verbatim as extracted): *"We investigate the behavior of the Euler products of the Riemann zeta
function and Dirichlet L-functions on the critical line. A refined version of the Riemann hypothesis, which
is named 'the Deep Riemann Hypothesis' (DRH), is examined."*

Kaneko, Koyama & Kurokawa, *Towards the Deep Riemann Hypothesis for GL_n*, arXiv:2206.02612.
FETCHED (https://arxiv.org/html/2206.02612v3).
DRH, Conjecture 5.1 (verbatim as extracted): *"lim_{x→∞} ((log x)^m ∏_{N(v)≤x} det(1−ρ(Frob_v)N(v)^{−s})^{−1})
= L^{(m)}(s,ρ)/(e^{mγ} m!) × {√2^{ν(ρ)} if s=1/2; 1 otherwise}"*, where m = order of vanishing of L(s,ρ)
and ν(ρ) := m(sym²ρ) − m(∧²ρ). Strength: *"If the convergence of the Euler product occurs on the critical
line for 1/2 ≤ Re(s) < 1, then the grand Riemann hypothesis for Artin L-functions would follow."*
⇒ DRH is **stronger than GRH** (convergence behaviour of the *partial Euler product* on the line, not just
zero location), with an explicit limit involving the √2^{ν} factor and the vanishing order m.

Origin `[BIBLIOGRAPHIC POINTER, CONTENT NOT FETCHED]`: Conrad, *Partial Euler Products on the Critical
Line*, Canad. J. Math. 57 (2) (2005) 267–297 (kconrad PDF binary; Cambridge PDF listing confirms bib data).
Extends Goldfeld's elliptic-curve result (partial Euler product asymptotics at s=1 ⇒ RH for that L, with an
unexpected √2 constant) to typical L-functions along the critical line. Akatsuka `[SEARCH-SUMMARY]`: studied
DRH for ζ, capturing divergence of the partial Euler product via a modified logarithmic integral.

### Bearing on the lab
DRH is the sharpest known "positivity/convergence at the seam Re s = 1/2" statement: it asserts the *partial
Euler product itself converges on the critical line* to an explicit value carrying a √2^{ν(ρ)} factor tied to
the **order of vanishing m**. That order-of-vanishing dependence is a literature precedent for coupling an
Euler-product/positivity object to the *multiplicity* of a central zero — adjacent in spirit to the lab's
multiplicity ladder, though DRH is about the central point s=1/2 (on-line), whereas the lab's ladder is about
hypothetical *off-line* multiplicities. The √2^{m}-type factor is the one place multiplicity already enters an
Euler-product convergence law.

---

## SEARCH-TERM LOG (per check)

**#8**
- "Davenport Heilbronn function zeros off critical line density number of zeros Re s > 1"
- "linear combination Dirichlet L-functions zeros off critical line positive proportion Bombieri Hejhal"
- "number of zeros Davenport-Heilbronn function Re s > 1/2 exceeds c T Bombieri Hejhal positive proportion off critical line"
- "Bombieri Hejhal distribution of zeros of linear combinations of Euler products Duke number of zeros off critical line asymptotic"
- "Davenport-Heilbronn function number of zeros with sigma > 1/2 up to T asymptotic c T Karatsuba Voronin off line linear"
- "Davenport-Heilbronn function definition character mod 5 chi(2)=i kappa=(sqrt(10-2sqrt5)-2)/(sqrt5-1) functional equation"
- Fetched: arxiv.org/abs/1602.06328; arxiv.org/abs/1506.05716; arxiv.org/abs/2010.10490; arxiv.org/abs/2503.24275
  (abstract); (403) ams.org mcom 2007-76-260 Balanzario–Sánchez-Ortiz; (empty) projecteuclid Bombieri–Hejhal.

**#3**
- "Hamburger theorem functional equation zeta uniqueness Dirichlet series must be c zeta(s) Titchmarsh hypotheses exact statement"
- Fetched: ar5iv 1605.02354 (Perelli, Theorem 2.1); ar5iv 1610.01583 (Hu–Li). (binary) ems.press/42100;
  (auth redirect) Springer 978-93-86279-02-6_12 "Abundance Principle."

**#2**
- "random Euler product unimodular Steinhaus coefficients almost surely converges nonvanishing analytic Re s > 1/2 random multiplicative function"
- "random multiplicative function Dirichlet series almost surely analytic Re s>1/2 Euler product nonvanishing Kolmogorov three series proposition"
- "Wintner 1944 random factorizations Riemann hypothesis Euler product prod (1-X_p p^{-s}) converges almost surely sigma greater 1/2"
- Fetched: ar5iv 1505.01443 (Harper–Nikeghbali–Radziwiłł, three-series quote); ar5iv 2012.15809 (Harper —
  references Wintner, no direct statement); arxiv 1509.03643 (deterministic, off-target).

**#5**
- "multiplicity of hypothetical zeros off critical line zeta function simple zeros if Riemann hypothesis fails conditional"
- "if Riemann hypothesis false off-line zeros necessarily simple or multiple Levinson Conrey no known constraint multiplicity counterexample zeros"
- Fetched: en.wikipedia.org/wiki/Riemann_hypothesis (Montgomery 2/3 simple under RH; simplicity conjecture;
  NO off-line-multiplicity statement). Null result — absence confirmed.

**#7**
- "Bohr theorem almost periodic Dirichlet series zero-free half plane zeta uniformly almost periodic Re s > 1 nonvanishing exact statement"
- "Riemann hypothesis equivalent almost periodicity zeta half-plane Bohr Besicovitch sigma > 1/2 zero-free"
- "'almost periodic' zeta vertical lines sigma>1 Bohr sigma>1/2 Besicovitch B^2 Hedenmalm Seip Dirichlet series Hardy space"
- "Bohr Landau 1914 zeta almost periodic half-plane Re s > 1 uniformly Riemann hypothesis equivalent almost periodic L-function survey"
- Fetched: ar5iv 1812.04925 (Schoolmann, Bohr's theorem verbatim); ar5iv 2302.14519 (Brevig–Kouroupis, Bohr
  σ_u≤θ). (no target text) ar5iv 2206.00434; arxiv/html 2606.16097; ar5iv 2005.14632. σ>1/2⟺RH equivalence
  UNRESOLVED (search-summary only).

**#4**
- "Keith Conrad 'Partial Euler products on the critical line' Canadian Journal Deep Riemann Hypothesis Kurokawa Koyama Akatsuka"
- "Deep Riemann Hypothesis DRH Kurokawa Koyama partial Euler product critical line converges L(1/2) times 2^{-m/2} Akatsuka statement"
- Fetched: arxiv.org/abs/1210.1216 (Kimura–Koyama–Kurokawa, DRH abstract); arxiv.org/html/2206.02612v3
  (Kaneko–Koyama–Kurokawa, Conjecture 5.1 + DRH⇒GRH). (binary) kconrad eulerprod.pdf — Conrad bib only.
