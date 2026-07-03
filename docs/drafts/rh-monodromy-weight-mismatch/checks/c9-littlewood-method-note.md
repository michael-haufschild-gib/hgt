# c9 — How Littlewood's 1922 zero-free region is actually PROVED (verified reading)

Objective: record, verbatim from arXiv / open-access sources only, the *mechanism* of
Littlewood's zero-free region β ≤ 1 − c·loglog t / log t, so a recurrence-based lane can
audit whether it coincides. Central question: does the proof use (i) a
Diophantine/Kronecker step (approximate t·log p by integers so p^{−it} ≈ 1, hence
ζ(σ+it) ≈ ζ(σ) large), or (ii) purely exponential-sum / upper-bound-on-ζ machinery?

All quotes are from the fetched open-access page named at each block. Nothing here is
recalled from Titchmarsh §5 (not fetchable); mechanism is reconstructed only from fetched text.

---

## Item 1 — Statement and proof mechanism of Littlewood's zero-free region

### Statement (verbatim)

Source: Mossinghoff–Trudgian–Yang, "Zero-free regions for the Riemann zeta function,"
arXiv:1910.08205 (fetched HTML), historical Table 1:

> de la Vallée Poussin (1899): "1−β≤c/log|t|"
> Littlewood (1922): "1−β≤c·log log|t|/log|t|"
> Chudakov (1938): "1−β≤c/(log|t|)^(3/4+ε)"

Source: WebSearch aggregate (Yang 2023 explicit constant, as cited across
arXiv:1910.08205 / arXiv:2212.06867 discussion):

> "for e^{170.2} < |T| ≤ e^{481958}, the Littlewood zero-free region gives
> σ ≥ 1 − (log log|T|)/(21.233 log|T|)"

Source: arXiv:2603.21490 ("Zero-free regions inspired by work of Heath-Brown," fetched HTML),
its equation (3):

> "σ > 1 − log log t/(21.233 log t), t ≥ 3"

### Mechanism (verbatim)

Source: "The zero-free region of the Riemann zeta function," Vigorous Handwaving blog
(fetched HTML) — classical de la Vallée Poussin / Littlewood argument:

> "Consider the trigonometric polynomial 3+4cos(θ)+cos(2θ) = 2(1+2cos(θ)+cos²(θ)) =
> 2(1+cos(theta))² ≥ 0"

> "−3ζ'(σ)/ζ(σ) − 4Re(ζ'(σ+iγ)/ζ(σ+iγ)) − Re(ζ'(σ+2iγ)/ζ(σ+2iγ)) =
> Σ_{p,m} [log(p)/p^{mσ}(3+4cos(mγlog(p))+2cos(2mγlog(p)))]" — RHS non-negative.

> "Due to the pole of ζ'(s)/ζ(s) at s=1 we have that ... for σ₀ close to one, we can use
> a/(σ₀−1) for some a, as an upper bound on ζ'(s)/ζ(s)."

The blog's own summary of the method (fetched, verbatim paraphrase field):

> "The derivation does not employ Diophantine approximation of t·log p. Instead, it relies
> on: bounds on ζ(s) derived from exponential sum estimates, the Cauchy integral formula ...
> and the Borel-Carathéodory theorem applied to log(ζ(s)) after removing zeros."

Source: arXiv:2603.21490 (fetched HTML) — the modern trig-polynomial framing and an explicit
statement about Kronecker:

> "P(θ) = ∑_{0≤k≤K} a_k cos(kθ), satisfying P(θ) ≥ 0 ... generalizes the classical
> 3 + 4cos θ + cos 2θ ... Σ_{n≥1} Λ(n)n⁻ˢ f(log n) P(t log n) ≥ 0."

> "No Diophantine/Kronecker approximation step is used; the method relies entirely on
> Dirichlet series bounds and polynomial positivity."

Source: WebSearch aggregate on the loglog improvement's ingredient:

> "The derivation of Littlewood's zero-free region requires sub-convexity bounds for the
> zeta function with k ≥ 4, which involve estimates on the growth of ζ(σ + it)."

### Reading of the mechanism

The width of the zero-free region is produced by feeding an UPPER bound on |ζ(σ+it)| (equiv.
on Re(−ζ'/ζ) / the local zero count) near σ=1 into the 3+4cos+cos2θ non-negativity balanced
against the 3/(σ−1) pole term. de la Vallée Poussin uses the crude upper bound O(log t) ⇒
width c/log t. Littlewood's loglog improvement comes from a SHARPER upper bound on ζ's growth
near the 1-line (subconvexity / exponential-sum growth estimates, per the search aggregate),
which shrinks the loss factor from log t to loglog t in the numerator. The step is an
upper-bound-on-ζ step throughout; the recurrence/Kronecker idea (making p^{−it}≈1 so ζ is
LARGE) is a LOWER bound and would be the wrong sign for a zero-free (upper) argument.

STATUS item 1: Mechanism (ii). The proof is 3+4cos+cos2θ positivity + an UPPER bound on |ζ|
near σ=1 (Littlewood's loglog = a sharper such upper bound), NOT (i). Multiple fetched
sources state explicitly that NO Diophantine/Kronecker step is used
(Vigorous Handwaving blog; arXiv:2603.21490). Exact "bootstrap vs Vinogradov-exponential-sum"
provenance of Littlewood's specific loglog upper bound was NOT pinned in a fetched full-text
open-access derivation (Titchmarsh §5 / §3.10 and Kadiri BIRS PDF not machine-readable); the
fetched sources agree only that the ingredient is a growth/subconvexity UPPER bound on ζ.

Negative queries (item 1, did not yield a machine-readable full derivation):
- Tao 254A Notes 2 (terrytao.wordpress.com/2014/12/09) — no zero-free-region construction on page.
- arXiv:1910.08205 body — gives Table 1 statement only, "does not provide the derivations."
- arXiv:2212.06867 /html/ — HTTP 404 (no HTML build).
- Kadiri BIRS 23ss001 PDF — binary, not parsed.
- arXiv:math/0501232 PDF, arXiv:1207.4336 PDF, arXiv:2311.16371 PDF — binary FlateDecode, not parsed.

---

## Item 2 — "ζ(σ+it) large / ≈ ζ(σ) on a Kronecker-recurrence set" and how set density enters

This is the DUAL (lower-bound / Ω) direction. Fetched sources place Kronecker/Diophantine
recurrence here, never in the zero-free-region argument of Item 1.

### Classical Ω / recurrence statements (verbatim)

Source: arXiv:2404.17250 ("Omega Theorems for Logarithmic Derivatives ... Near the 1-line,"
fetched HTML) — introduction's history:

> Landau (1911): "proved that there exists a positive constant k₁ such that
> |ζ′(s)/ζ(s)| ≥ k₁ log₂ t has a solution" for σ > 1.

> Bohr-Landau (1913): "|ζ′(s)/ζ(s)| ≥ (log t)^{k₂θ} has a solution s=σ+it in the region
> {σ+it: σ ≥ 1−θ, t ≥ τ}" for θ ∈ (0, 1/2).

Source: arXiv:2311.16371 (fetched HTML/search) — the value-side Ω:

> "Bohr proved that the values ζ(1+it) are dense in ℂ, and Bohr and Landau proved the
> corresponding omega-estimates ζ(1+it) = Ω(log log t) and ζ(1+it)⁻¹ = Ω(log log t)."

Source: WebSearch aggregate (Littlewood 1925 / Levinson / Granville–Soundararajan lineage):

> "In 1925, Littlewood showed that there exist arbitrarily large t for which
> |ζ(1+it)| ≥ {1+o(1)} e^γ log₂ t."
> "In 2006, Granville and Soundararajan obtained max_{t∈[1,T]} |ζ(1+it)| ≥
> e^γ { log₂ T + log₃ T − log₄ T + O(1) }."

### The Kronecker/Diophantine mechanism itself (verbatim attribution)

Source: Steuding, "Extremal values of Dirichlet L-functions in the half-plane of absolute
convergence," J. Théor. Nombres Bordeaux (2004), DOI 10.5802/jtnb.444 (open-access abstract,
fetched): the abstract states the main result uses

> "an effective version of Kronecker's approximation theorem"

to demonstrate extremal (large) values of Dirichlet L-functions near σ = 1+. This is the
Diophantine step — simultaneous approximation of the {log p} phases so that the Euler factors
align — applied to produce large VALUES, not to locate/exclude zeros. (Full body not
machine-readable; abstract confirms the instrument and its target = extremal values.)

### How the recurrence set's density / gaps enter (verbatim)

Source: arXiv:2404.17250 (fetched HTML), Theorem 1.2 (under RH):

> "meas(ℳ(T,x)) ≥ T^{1−(1−β)e^{−x}+o(1)}"

interpreted in the fetched text as: "This exponential decay factor e^{−x} characterizes how
the measure of large-value sets diminishes." I.e. the larger the demanded value threshold x,
the SMALLER (rarer) the set of admissible t — the density of the recurrence set decays and
this trade-off is exactly what caps the achievable size (≈ e^γ log y when p^{−it}≈1 is forced
for all p ≤ y). The modern proofs REPLACE the classical Kronecker step by a resonance method:

> arXiv:2404.17250: "we will employ long resonator methods ... to resonate with logarithmic
> derivatives" — "a deliberate departure from earlier Kronecker-type techniques toward modern
> resonance machinery developed by Voronin (1988) and Soundararajan."

STATUS item 2: The recurrence/Kronecker idea is the LOWER-bound (Ω / extremal-value) machine —
Bohr (density of values), Landau 1911 and Bohr–Landau 1913 (|ζ'/ζ| large), ζ(1+it)=Ω(loglog t),
Littlewood 1925 |ζ(1+it)| ≥ (1+o(1))e^γ log₂ t. Density of the recurrence set enters as an
inverse trade-off: a larger forced value ⟺ a rarer/lower-density set of good t, quantified in
fetched form by meas(ℳ(T,x)) ≥ T^{1−(1−β)e^{−x}+o(1)}. This is the OPPOSITE sign to the Item-1
zero-free argument; the two never share a step in any fetched source.

Negative queries (item 2):
- Full verbatim body of the classical Kronecker "align all p^{−it} ≈ 1 ⇒ ∏_{p≤y}(1−1/p)^{−1}
  ~ e^γ log y" construction was NOT obtained in machine-readable form; Steuding jtnb.444 body
  and Granville–Sound math/0501232 PDF did not parse. Instrument (Kronecker) and target
  (extremal values) are confirmed from abstracts/introductions only.

---

## Item 3 — Does any fetched source derive CLUSTERING of hypothetical zeros from recurrence?

Source: arXiv:2404.17250 (fetched HTML):

> "The authors explicitly frame these as omega theorems for logarithmic derivatives — these
> establish lower bounds on maximal values, not zero-free regions ... measuring oscillatory
> behavior of the logarithmic derivative function itself rather than constraints on zero
> locations."

Source: arXiv:1703.08315 (Bondarenko–Seip, "Extreme values of ζ on the 1-line," fetched):

> "The provided content does not discuss clustering of zeta zeros near hypothetical zeros or
> any related phenomena. The paper focuses exclusively on extreme values of ζ."

Source: arXiv:2311.16371 (fetched):

> "The paper makes no reference to clustering of zeros near hypothetical zeros or companion
> zeros derived from recurrence relations. The focus remains on bounding logarithmic
> derivatives ... rather than zero distribution arguments."

STATUS item 3: NEGATIVE. No fetched source derives clustering / companion zeros near a
hypothetical zero from recurrence ideas. Every recurrence/Kronecker-driven output found is one
of exactly two kinds: (a) large VALUES of |ζ| / Ω-oscillations on and near the 1-line
(Bohr–Landau, Littlewood 1925, resonance method), and (b) universality-type density of values
(Bohr). Zero LOCATION control comes solely from the DUAL upper-bound / 3+4cos+cos2θ machine of
Item 1, which contains no recurrence step. A recurrence→zero-clustering bridge, if it exists,
is NOT present in the fetched open-access corpus and would be new relative to it.

Negative queries (item 3): searches on "Kronecker recurrence companion zeros clustering
hypothetical zero" and the extremal-value / Ω-theorem papers (1703.08315, 2311.16371,
2404.17250, math/0501232) returned zero-free regions or Ω-oscillations only — no clustering.
