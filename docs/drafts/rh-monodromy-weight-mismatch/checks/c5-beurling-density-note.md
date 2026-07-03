# C5 — Beurling side calibration for the "droves dichotomy"

**Task.** Verify (1) the density/count of off-line zeros in Diamond–Montgomery–Vorhauer (DMV)
and successor Beurling constructions, and (2) whether any Beurling generalized number system
carries a Riemann-type functional equation (FE). Every claim below carries a URL fetched THIS
session plus a verbatim quoted passage. Recalled anchors were treated as hints only.

**Session note on evidence quality.** arXiv PDFs returned as compressed binary and were
unquotable; I used arXiv `/abs/` and `/html/` pages instead (verbatim). Springer full texts are
paywalled (marked). Two secondary details rest only on the WebSearch engine's synthesized answer
(not a page I fetched byte-for-byte) — they are flagged `[SEARCH-SYNTH, not fetched-verbatim]`.

---

## Sub-question 1 — Density/count of off-line zeros in Beurling constructions

### VERDICT: **VERIFIED-KNOWN**

The off-line zero count in the FE-free Beurling world spans the *entire* range the FE-dichotomy
forbids as a middle: **ZERO** off-line zeros (RH constructions), **finitely many / none** in
right strips, up to **infinitely many** clustering at a curve `σ = 1 − f(log t)`. Critically,
**no Riemann–von Mangoldt asymptotic count exists**, and this non-existence is *explicitly
attributed to the absence of a functional equation*. No proven linear-in-T "drove" lower bound;
only Carlson-type upper bounds.

### Exact statements + citations

**(a) DMV / successor: infinitely many zeros on a curve approaching the 1-line, none to its right.**
Fetched: https://arxiv.org/html/2507.13780 ("On the connection between zero-free regions and the
error term in the PNT", 2025), which builds on DMV:
> "ζ𝒫(s) has infinitely many zeros on the contour σ=1−f(log|t|), and none to the right of this contour."
> "The proof of our Theorem 1.6 heavily relies on their construction" (Diamond–Montgomery–Vorhauer).

DMV-specific curve `σ = 1 − a/log t` (a=1), original paper *Beurling primes with large oscillation*,
Math. Ann. **334** (2006) 1–36: **[SEARCH-SYNTH, not fetched-verbatim]** — "zeta function has
infinitely many zeros on the curve σ = 1−1/log t and no zeros to the right of the curve"
(Springer landing page https://link.springer.com/article/10.1007/s00208-005-0638-2, paywalled;
the *contour* form is corroborated verbatim by the fetched 2507.13780 quote above).

**(b) Successor with RH — i.e. ZERO off-line zeros — and large oscillation.**
Fetched: https://arxiv.org/abs/2004.11501 (Broucke, Debruyne, Vindas, *Beurling integers with RH
and large oscillation*, 2020). Abstract verbatim:
> "We construct a Beurling generalized number system satisfying the Riemann hypothesis and whose
> integer counting function displays extremal oscillation… The prime counting function… satisfies
> π(x)=Li(x)+O(√x), while its integer counting function satisfies the oscillation estimate
> N(x)=ρx+Ω±(x exp(−c√log x log log x))… combines saddle-point analysis with the
> Diamond–Montgomery–Vorhauer probabilistic method."

So the FE-free world contains systems with **no off-line zeros at all** yet large oscillation.

**(c) THE calibrating quote — finite/zero off-line counts occur, and NO asymptotic count exists.**
Fetched: https://arxiv.org/html/2407.12746v1 (Révész–Pintz, *New zero-density estimates for the
Beurling ζ function*, 2024), Conclusion. Both verbatim:
> "Contrary to zeta functions with a functional equation, there is no asymptotic formula for the
> number of zeroes of a Beurling zeta function in the critical strip or in a halfplane strictly in
> the critical strip."
> "Beurling systems with only finitely many zeroes (or no zeroes at all) do exist, see [19],
> Theorem 7.4. (though one may recall that these phenomenon is known only for θ≥1/2 and strips
> ℜs≥σ>θ)."

Same page, the classical count it is contrasted against, verbatim:
> "the number of zeroes of the Riemann zeta function up to height T is asymptotically N(T)∼(T/2π)log T".

**(d) Only UPPER bounds on off-line density (Carlson-type); no lower "drove" bound.**
Fetched: https://arxiv.org/abs/2211.08716 (Broucke–Debruyne, 2022), verbatim:
> "N(α, T) ≪ T^(c(1−α)/(1−θ)) log^9 T, for a constant c arbitrarily close to 4".
Fetched: https://arxiv.org/html/2407.12746v1, verbatim: "N(σ,T)≪_{η,ε}T^{B_ℬ(η)η+ε}" with
`B_ℬ(η)=2/(1−θ−η)` in the small-η range. Fetched: https://arxiv.org/abs/2209.01689
(Révész, *Carlson-type zero-density theorem for the Beurling ζ*, 2022), verbatim:
> "In a previous paper we proved a Carlson type density theorem for zeroes in the critical strip
> for Beurling zeta functions satisfying Axiom A of Knopfmacher."
These are one-sided (≪) upper bounds — they cap density, they do not force zeros to exist.

**(e) Density/clustering *near the 1-line*, proven WITHOUT a functional equation.**
Fetched: https://arxiv.org/abs/2012.09045 (Révész, *Distribution of Beurling primes and zeroes of
the Beurling zeta function I*, 2020/2022). Abstract verbatim:
> "We prove three results on the density resp. local density and clustering of zeros of the
> Beurling zeta function ζ(s) close to the one-line σ:=ℜs=1."
Fetched summary of same page: Theorem 4 gives "a zero density estimate, which is a complement to
known results for the Selberg class" and "these contributions apply to Beurling zeta functions
without relying on functional equation properties"; Theorem 6 generalizes Ramachandra clustering.

**(f) The "single prescribed off-line zero" regime — suggestive but NOT a clean isolated-zero theorem.**
Fetched: https://arxiv.org/abs/2202.01837 (Révész, *Oscillation… "caused by a given zeta-zero"*,
2022). Abstract verbatim:
> "given a zero ρ₀ of the Beurling zeta function ζ_P… the corresponding error term Δ_P(x)…shows
> oscillation… as large as (π/2−ε) x^(ℜ ρ₀)/|ρ₀|… there exists a Beurling number system with primes
> P, such that |Δ_P(x)| ≤ (π/2+ε)x^(ℜ ρ₀)/|ρ₀|… coupled by… the prime random approximation result
> of Broucke and Vindas, who sharpened the… construction due to Diamond, Montgomery and Vorhauer."
Note: this realizes a *prescribed* off-line zero's oscillation, but the abstract does **not** pin
the full zero set to that single zero, so it is not (yet) a proven "exactly-one off-line zero"
example. The clean isolated-finite case is covered by (c)'s reference [19, Thm 7.4] in right strips.

### Bearing on the dichotomy
Direct calibration hit: the FE-free Beurling class *realizes the forbidden middle* — sparse-but-
nonempty (indeed finite, or zero) off-line zeros exist — and the authors state **verbatim** that
the absence of an asymptotic zero count (the very thing that underwrites a linear-in-T "drove") is
what distinguishes Beurling from "zeta functions with a functional equation." This is strong
evidence that the **functional equation is the load-bearing axiom** behind the droves dichotomy.

---

## Sub-question 2 — Beurling generalized number system with a functional equation

### VERDICT: **PARTIALLY-KNOWN** (existence of a generalized FE is *characterized* in the literature — this is the "gold" testbed; exact conditions UNRESOLVED behind paywall)

Contrary to the expected "essentially nothing," a generalized functional equation for Beurling
zeta functions **is** treated in the literature: Hilberdink–Lapidus characterize when one exists,
in the fractal-membrane setting. Simultaneously, the entire modern density program (sub-q1) treats
FE-absence as the *default* and states the contrast explicitly.

### Exact statements + citations

**(a) A generalized FE is CHARACTERIZED (Hilberdink–Lapidus).**
Fetched: https://arxiv.org/abs/math/0410270 (Hilberdink & Lapidus, *Beurling Zeta Functions,
Generalised Primes, and Fractal Membranes*, 2004; Acta Appl. Math. 94 (2006) 21–48). Abstract
verbatim:
> "Under appropriate assumptions, we establish various analytic properties of ζ_𝒫(s), including its
> analytic continuation and we characterise the existence of a suitable generalised functional
> equation."
> "Some of the above results may be relevant to the second author's theory of 'fractal membranes',
> whose spectral partition functions are precisely given by Beurling zeta functions."

Form of that FE — **[SEARCH-SYNTH, not fetched-verbatim]** (WebSearch engine's rendering of the
arXiv PDF, which I could not fetch as text): it "connects a suitable completion of the Beurling
zeta function ζ(s) associated to the g-prime system P to that of ζ∗(s), associated to a 'dual
system' P∗ which involves in general a continuous g-prime system." i.e. the generalized FE relates
a system to its *dual* (generally a different, continuous system); a self-referential FE ζ(s)↔ζ(1−s)
would require **self-duality**. Exact conditions **UNRESOLVED** — full text paywalled
(Springer https://link.springer.com/article/10.1007/s10440-006-9063-0 redirects to an auth wall;
CentAUR https://centaur.reading.ac.uk/5075/ fetched: "Full text not archived in this repository").

**(b) FE-absence is the operative default in the zero-distribution literature.**
Fetched verbatim (repeated from sub-q1): https://arxiv.org/html/2407.12746v1 —
> "Contrary to zeta functions with a functional equation, there is no asymptotic formula for the
> number of zeroes of a Beurling zeta function…"
and the Révész program (https://arxiv.org/abs/2012.09045) proves its zero results "without relying
on functional equation properties." So *generic* Beurling systems carry no usable FE; the FE is a
special (fractal-membrane / self-dual-type) structure, not a feature of the class.

### Bearing on the dichotomy
This is the GOLD flagged in the task: Hilberdink–Lapidus's characterized-FE / fractal-membrane
generalized-prime systems are a **candidate testbed class** — Beurling systems that *do* carry a
Riemann-type FE — on which the droves dichotomy can be tested directly. If the dichotomy is
FE-driven, these FE-carrying Beurling zetas should show droves-or-none, while their FE-free cousins
(sub-q1) demonstrably show the sparse middle. Next generative move: obtain the full Hilberdink–
Lapidus text to extract the exact self-duality/condition, and check whether any of their FE systems
has a *constructed* off-line zero (would be the first FE-carrying non-lattice testbed).

---

## Search-term log
- WebSearch: `"Diamond Montgomery Vorhauer "Beurling primes with large oscillation" zeta zeros"`
- WebSearch: `Broucke Debruyne Vindas Beurling zeta zeros density oscillation`
- WebSearch: `Beurling generalized number system zeta functional equation`
- WebSearch: `Diamond Montgomery Vorhauer Beurling zeta number of zeros N(T) curve sigma=1-a/log t count height T`
- WebSearch: `Révész "Density estimates for the zeros of the Beurling" critical strip arXiv Carlson`
- WebSearch: `Hilberdink Lapidus Beurling zeta "functional equation" self-dual symmetric generalized prime condition exists`
- WebSearch: `Beurling zeta "functional equation" dual continuous generalized prime system Hilberdink Lapidus condition holds`
- WebFetch (verbatim, used): arxiv.org/abs/2012.09045 · arxiv.org/abs/2004.11501 · arxiv.org/abs/2202.01837 ·
  arxiv.org/abs/2211.08716 · arxiv.org/html/2407.12746v1 · arxiv.org/abs/math/0410270 ·
  arxiv.org/html/2507.13780 · arxiv.org/abs/2209.01689 · centaur.reading.ac.uk/5075/
- WebFetch (failed/binary/paywall): arxiv.org/pdf/2012.09045, /pdf/2004.11501, /pdf/math/0410270 (binary PDF);
  arxiv.org/html/2012.09045 & /html/math/0410270 (404); link.springer.com/…/s10440-006-9063-0 (auth redirect);
  en.wikipedia.org/wiki/Beurling_zeta_function (stub, no FE/zero-count); emergentmind.com/topics/beurling-zeta-functions
  (no FE, no total-count statement); arxiv.org/abs/2102.08478 (turned out to be Broucke–Vindas random-approx, not density).

## UNRESOLVED / [UNVERIFIED] items
- Exact conditions & analytic form of the Hilberdink–Lapidus generalized FE (self-duality clause,
  gamma-factor shape) — full text paywalled; dual-system description is SEARCH-SYNTH only.
- DMV original `σ = 1 − 1/log t` curve wording — SEARCH-SYNTH; the equivalent *contour* statement is
  fetched-verbatim from 2507.13780.
- Content of reference [19] Theorem 7.4 (the finite/no-zero existence result) — cited by 2407.12746,
  not independently fetched.
- No fetched source gives a *lower* bound forcing ≫T off-line zeros for any Beurling system
  (consistent with: none exists — only Carlson-type upper bounds are proven).
