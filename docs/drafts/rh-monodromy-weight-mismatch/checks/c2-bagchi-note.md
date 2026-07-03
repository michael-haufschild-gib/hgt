# C2 — Verified Literature Reading: Bagchi strong recurrence vs. the mod-2^k / RH_{2^k} ladder

Positioning check. Every evidentiary claim below carries a URL fetched in THIS session plus a
quoted passage from that fetch. Where the WebFetch summarizer paraphrased rather than returned a
clean verbatim string, the quote is tagged **[fetch-summarized]** and treated as weaker than a
verbatim string. Primary Bagchi sources (thesis, Springer/Acta page) were NOT directly fetchable —
see UNRESOLVED — so their bibliographic data is reported only where an *independently fetched*
secondary source reproduced it.

---

## 1. One-line verdict per question

- **(a) Bagchi's theorem — CONFIRMED as recalled.** Bagchi's theorem is exactly: *strong recurrence*
  = sup-norm self-approximation of ζ(s+iτ) by ζ(s) on compact subsets K (connected complement) of
  the open strip 1/2 < Re s < 1, ε-close for a set of τ of **positive lower density**, and this is
  **equivalent to RH**. Corroborated by two independently fetched secondary sources (Matsumoto survey;
  Sourmelidis 2023).

- **(b) Proof mechanism — CONFIRMED, and it does NOT coarsen the count.** The (self-approximation ⇒ RH)
  direction passes through **zero-counting + Rouché's theorem + a zero-density estimate**. The count
  used is the *full* integer number of zeros (≈ cT, forced to infinity), contradicting N(σ,T)=o(T)
  for σ>1/2. **No mod-2, mod-2^k, parity, winding-number-valued, or multiplicity-divisibility
  coarsening appears** — the argument needs the raw magnitude of the count, not its residue.

- **(c) Follow-ups — none state a coarsened / graded-ladder / analytic-root version.** The
  self-approximation follow-up line (Nakamura, Pańkowski, Laurinčikas) generalizes the *shift
  parameter* (rational/irrational d), not the zero-count invariant. No fetched source states
  "RH_{2^k}: 2^k divides every off-line zero's order", nor the equivalence with an analytic 2^k-th
  root of ξ on Re s > 1/2, nor any mod-2^k reduction of a strip zero count.

---

## 2. Overall NOVELTY VERDICT

**ABSENT-FROM-LITERATURE** — for the specific package *"mod-2^k coarsening of the strip zero count +
graded RH_{2^k} ladder + analytic 2^k-th root of ξ on Re s > 1/2"*.

Justification:
1. The Bagchi / strong-recurrence proof that most resembles the lab's winding-number cocycle **counts
   zeros with full multiplicity and drives that count to infinity** (Rouché ⇒ ≈cT zeros ⇒ contradicts
   zero-density). It never reduces the count modulo anything. The lab's move — keeping only w_k(T) =
   (zero count) mod 2^k as the RH obstruction — is a genuinely different operation on the same
   argument-principle integer. (Fetched: Sourmelidis 2023, verbatim below.)
2. Targeted searches for the coarsened/graded objects ("2^k-th root of xi analytic", "mod 2 / parity
   zero count cocycle", "order divisible by 2^k", "analytic square root of completed zeta",
   "RH_{2^k}") returned only the standard, *un-graded* facts: RH ⟺ all ξ-zeros real; the *simple-zeros
   conjecture* (all zeros simple — a k→∞-flavoured but ungraded and independent statement); and the
   textbook argument-principle full count N(T). No graded ladder, no analytic-root equivalence.

Caveats bounding the verdict:
- The **un-coarsened ingredients are standard**: the argument principle / winding number as a full
  zero count is textbook; "all nontrivial zeros simple" is a classical conjecture. Novelty rests on
  the *mod-2^k reduction* and the *analytic-2^k-th-root ⟺ divisibility-of-orders ⟺ RH ladder*, not on
  any single ingredient.
- Verdict is ABSENT rather than a stronger claim because two primary/near-primary sources could not be
  fetched (Bagchi's Acta paper behind Springer auth; the 2024 MDPI Laurinčikas review 403'd). Neither
  is expected to contain a mod-2^k construction (both are self-approximation papers), but they are
  logged UNRESOLVED rather than asserted clean.

---

## 3. Evidence (per source: bibliographic data + fetched URL + supporting quotes)

### S1 — Matsumoto, survey on universality (fetched)
- **Bibliographic:** Kohji Matsumoto, "A survey on the theory of universality for zeta and
  $L$-functions", arXiv:1407.4216 (2014); proceedings, 7th China–Japan Seminar.
- **Fetched URL:** https://ar5iv.labs.arxiv.org/abs/1407.4216  (ar5iv HTML mirror; original
  arxiv.org/pdf/1407.4216 downloaded but returned non-extractable binary).
- **Supporting quotes [fetch-summarized]:**
  - Definition: "a Dirichlet series φ(s) satisfies strong recurrence in D(a,b) if for any compact
    K⊂D(a,b) with connected complement and any ε>0, the set of τ where sup_{s∈K}|φ(s+iτ)−φ(s)|<ε has
    positive lower density".
  - Equivalence: "the strong recurrence for ζ(s) is equivalent to the Riemann Hypothesis".
  - Bagchi cited as an unpublished thesis, contents "carefully expounded in" Laurinčikas's 1996
    textbook.
  - Proof techniques: the fetch reported the strong-recurrence discussion "does not explicitly
    mention" Rouché / argument principle / zero-density / parity / multiplicity in that section
    (consistent with a survey that states the equivalence without re-deriving it).

### S2 — Sourmelidis, "Continuous and discrete universality of zeta-functions" (fetched; LOAD-BEARING)
- **Bibliographic:** Athanasios Sourmelidis, "Continuous and discrete universality of zeta-functions:
  Two sides of the same coin?", arXiv:2308.07031 (2023).  (Title/author/abstract confirmed via a
  second fetch of https://arxiv.org/abs/2308.07031.)
- **Fetched URL:** https://ar5iv.labs.arxiv.org/abs/2308.07031
- **Supporting quotes:**
  - Strong-recurrence statement: **Statement 2** = "For any admissible (K,ζ,ε):
    lim inf_{T→∞} (1/T) meas{τ∈[0,T]: max_{s∈K}|ζ(s+iτ)-ζ(s)|<ε} > 0", on the strip
    𝒟={s: 1/2<σ<1}, equivalent to **Statement 1 (RH)**.
  - **Proof mechanism (this is the decisive quote for (b)):** the (self-approximation ⇒ RH) direction —
    "assuming that (3) holds but (1) does not, it would imply by Rouché's theorem the existence of at
    least cT many zeros in the rectangle 1/2<σ<1, 0<t<T, for some c>0 and infinitely many T. But these
    would contradict classic zero-density estimates of ζ(s) in the half-plane σ>1/2".
    → Confirms the mechanism is Rouché + FULL zero count + zero-density; the count is used at full
    magnitude (cT), never reduced mod 2^k or by parity.
  - Bagchi references as listed by this paper: [1] PhD thesis, Indian Statistical Institute-Kolkata,
    1981; [2] "A joint universality theorem for Dirichlet L-functions", Math. Z. 181:319–334, 1982;
    [3] "Recurrence in topological dynamics and the Riemann hypothesis", Acta Math. Hung.
    50:227–240, 1987.

### S3 — Nakamura & Pańkowski, "Self-Approximation for the Riemann Zeta Function" (fetched)
- **Bibliographic:** Takashi Nakamura and Łukasz Pańkowski, "Self-Approximation for the Riemann Zeta
  Function", Bulletin of the Australian Mathematical Society, vol. 87, issue 3 (2013), pp. 452–461,
  DOI 10.1017/S0004972712000846 (online 31 Oct 2012).
- **Fetched URL:**
  https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/selfapproximation-for-the-riemann-zeta-function/FF06DD5E3DC92036F95F873D7DEBE253
- **Supporting quotes:**
  - Abstract: "In the paper we deal with self-approximation of the Riemann zeta function in the half
    plane Re s>1 and in the right half of the critical strip."
  - Fetch reported the article "does not ... mention Rouché's theorem, the argument principle,
    zero-counting, winding numbers, zero-density, or multiplicity/parity of zeros" — i.e. this
    follow-up generalizes the *shift*, and introduces **no** coarsened zero-count invariant. Supports (c).

### S4 — Search-level corroboration of the equivalence and the simple-zeros (ungraded) conjecture
- **Fetched search page context** (WebSearch result set, query in §5): the standard equivalences
  returned are ungraded — "RH is equivalent to the statement that all of the zeros of the Riemann
  ξ(z) function are real"; and "all of the (nontrivial) zeros of ζ(s) are simple ... equivalently ...
  all of the zeros of Ξ(s) are simple." No graded "order divisible by 2^k" or analytic-root
  statement surfaced. (These came through WebSearch summaries, not a single fetched page — logged as
  search evidence in §5, not as a per-page quote.)

---

## 4. UNRESOLVED

1. **Bagchi (1987), Acta Math. Hungar. 50, 227–240** — primary source. Springer page
   https://link.springer.com/article/10.1007/BF01903937 redirected to an auth endpoint (HTTP 303 to
   idp.springer.com); **not fetched**. Bibliographic data (vol 50, pp 227–240, 1987) is reported only
   because the *fetched* Sourmelidis reference list (S2, ref [3]) reproduces it; the article's own
   text/theorem was not read directly.
2. **Bagchi (1981) PhD thesis, ISI Calcutta/Kolkata** — "The statistical behaviour and universality
   properties of the Riemann zeta-function and other allied Dirichlet series." Unpublished; **not
   fetched**. Existence/title corroborated by S1 (unpublished thesis, expounded in Laurinčikas 1996)
   and S2 ref [1]. Cannot confirm the thesis's internal proof does not coarsen a count — but the
   secondary expositions (S1, S2) show the standard argument does not.
3. **Laurinčikas, "Remarks on the Connection of the Riemann Hypothesis to Self-Approximation",
   Computation 12(8):164 (2024)** — MDPI page https://www.mdpi.com/2079-3197/12/8/164 and its /htm
   and /htm variants all returned **HTTP 403**; **not fetched**. Author "Laurinčikas, A." and the
   framing "RH ⟺ self-approximation of ζ(s) by shifts ζ(s+iτ)" came from the WebSearch snippet only,
   NOT a fetched page → treat author attribution as [UNVERIFIED].
4. **Matsumoto survey definition quotes (S1)** are **[fetch-summarized]**, not confirmed verbatim
   (the PDF was binary; the ar5iv fetch paraphrased). The equivalence and the Bagchi-thesis
   attribution are corroborated by S2, but the exact wording of the strong-recurrence definition in
   S1 is not a confirmed verbatim string.
5. **Nakamura, Pańkowski "generalized strong recurrence" arXiv papers** (1006.3184, 1006.1507,
   1203.1393) — appeared in search but the direct PDF (arxiv.org/pdf/1006.3184) returned HTTP 404
   this session; **not fetched**. Their titles indicate shift-parameter generalizations, not
   zero-count coarsening, but this is inference from titles, not read text.

---

## 5. Search-term log (for auditability of absence claims)

WebSearch queries run this session:
1. `Bagchi strong recurrence Riemann hypothesis self-approximation zeta function`
2. `Bagchi "Recurrence in topological dynamics and the Riemann hypothesis"`
3. `"2^k-th root" xi analytic Riemann hypothesis multiplicity zeros equivalent`
4. `parity multiplicity hypothetical zeros zeta off critical line simple zeros equivalent Riemann hypothesis`
5. `Matsumoto survey universality zeta functions Bagchi theorem strong recurrence arxiv`
6. `"Remarks on the Connection of the Riemann Hypothesis to Self-Approximation" MDPI Computation author`
7. `self-approximation zeta Bagchi proof Rouché theorem zero-density estimate implies Riemann hypothesis`
8. `"analytic square root" OR "holomorphic square root" zeta xi function Riemann hypothesis zeros even order`
9. `winding number argument principle number of zeros mod 2 parity Riemann zeta critical strip cocycle`
10. `Riemann hypothesis equivalent "every zero" even multiplicity order divisible by four analytic root of completed zeta half-plane`

WebFetch targets (result in parentheses):
- link.springer.com/article/10.1007/BF01903937 (303 auth redirect — UNRESOLVED)
- mdpi.com/2079-3197/12/8/164 and /htm (403 — UNRESOLVED)
- arxiv.org/pdf/1006.3184 (404)
- arxiv.org/pdf/1407.4216 (binary, non-extractable)
- math.nagoya-u.ac.jp/~kohjimat/Nicchuu13.pdf (binary, non-extractable)
- ar5iv.labs.arxiv.org/abs/1407.4216 (OK — S1)
- ar5iv.labs.arxiv.org/abs/2308.07031 (OK — S2, load-bearing)
- arxiv.org/abs/2308.07031 (OK — S2 bibliographic confirmation)
- cambridge.org/.../selfapproximation-for-the-riemann-zeta-function/... (OK — S3)

Absence claim rests on: queries 3, 4, 8, 9, 10 returning only ungraded/standard equivalences (all
ξ-zeros real; simple-zeros conjecture; textbook argument-principle full count) with zero hits for a
mod-2^k coarsening, a graded RH_{2^k} ladder, an analytic 2^k-th root of ξ, or a parity/winding-valued
zero-count cocycle — combined with the fetched Sourmelidis passage (S2) showing the actual Bagchi-style
argument uses the full, un-reduced integer count.

---

## ADDENDUM (2026-07-03, post-delegation) — the limsup/liminf nuance, verified

Second reader (GPT, user-relayed) flagged a refinement missed above; re-fetched and
CONFIRMED verbatim against ar5iv 2308.07031 (Sourmelidis):

> "Bagchi proves only (1)⇔(3) but the statement cited mostly in the relevant literature
> is (1)⇔(2)."

where (2) is the liminf (positive LOWER density) self-approximation condition and (3) the
limsup (positive UPPER density) one. So: **Bagchi's original topological-dynamics
equivalence is RH ⟺ the limsup/upper-density recurrence**; the liminf form standard in
later literature follows from RH via Voronin universality (and liminf ⟹ limsup trivially).

Consequence for the lane: the Reduction's open core (R_k) has been restated in the
positive-UPPER-density register (see 06-reduction.md §2) — weaker than the bounded-gaps
form first drafted, and exactly matching the register Bagchi actually proved, one
coarsening down.

Bibliographic additions relayed by the second reader from Springer pages (not fetched
here — [UNVERIFIED-page, reported]): Bagchi 1987 Acta Math. Hungar. 50:227–240, DOI
10.1007/BF01903937, received 1984-10-20, published Sept 1987; Steuding, Value-Distribution
of L-Functions, LNM 1877, Springer 2007, DOI 10.1007/978-3-540-44822-8. Consistent with
the fetched Sourmelidis reference list (S2).
