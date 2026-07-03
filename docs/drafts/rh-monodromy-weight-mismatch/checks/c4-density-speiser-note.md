# C4 — Density / Speiser / Levinson–Montgomery: verified literature reading

Four bundled positioning checks for the RH-adjacent reduction (zero-density input (D) + open
recurrence). Every claim below carries a URL fetched THIS session and a verbatim quoted passage.
PDFs on arXiv/journal hosts returned undecodable binary to the fetcher; readable text was obtained
from the ar5iv HTML mirror (`ar5iv.labs.arxiv.org`) and from Tao's WordPress HTML. Anything not
fetched is marked [UNVERIFIED].

---

## CHECK 1 — Where density proofs consume multiplicativity

**VERDICT: VERIFIED-KNOWN.**

**Named step where the Euler product enters:** the **mollifier / zero-detecting polynomial with
Möbius coefficients** `μ(n)`. These coefficients are exactly the Dirichlet coefficients of
`1/ζ(s) = Π_p (1 − p^{-s})` — i.e. the Euler product itself. The two other candidate ingredients —
the mean-value theorem for Dirichlet polynomials and the approximate functional equation — do **not**
use multiplicativity.

### Source A (primary exposition): Terence Tao, "A computation-outsourced discussion of zero density theorems for the Riemann zeta function" (2024)
URL fetched: https://terrytao.wordpress.com/2024/07/07/a-computation-outsourced-discussion-of-zero-density-theorems-for-the-riemann-zeta-function/

- Mollifier step (this is the Möbius/Euler-product ingredient). Quoted:
  > "However, this can be fixed by the standard device of introducing a 'mollifier' to eliminate the role of small primes."

  and the explicit form:
  > "one can multiply [(5)] by `Σ_{n ≤ T^ε} μ(n)/n^{β+iγ}` for a small ε, which morally speaking has the effect of eliminating…"
  (the fetch reports this "eliminates the contribution of those terms n with 1 < n ≤ T^ε").

- Mean-value theorem — orthogonality, NOT multiplicativity. Quoted (from the first fetch pass):
  > "The standard L² mean value theorem for Dirichlet series tells us that … by using the approximate orthogonality properties of the function t ↦ 1/n^{it}."

- Approximate functional equation — present but not load-bearing. Quoted:
  > "The approximate functional equation for the Riemann zeta function morally tells us that C₁(σ,α) = C₁(1/2 + α/(1−α)(σ−1/2), 1−α)"
  with the remark that "we will not have much use for this symmetry."

- Exponent recovered (Ingham/Huxley line). Quoted:
  > "the Huxley bound A(σ) ≤ 3/(2−σ)"

**Reading of the step (my analysis, labelled [CONJECTURE] — not a fetched claim):** the mollifier can
be *formed* for any Dirichlet series (a Dirichlet inverse always exists when a(1)≠0), so the mere
existence of `M` is generic. Multiplicativity is load-bearing one level down: for ζ the inverse
coefficients are `μ(n)` with `|μ(n)| ≤ 1` (bounded, multiplicative), which is what keeps the mollified
mean square `∫|ζM|²` at size `O(T^{1+ε})`. For an FE-only series the Dirichlet-inverse coefficients
can grow, and that mean value — hence the density bound — is what breaks. The fetched sources locate
the Möbius ingredient exactly; the "why bounded" refinement is reasoning, not quoted.

### Literature explicitly saying density/RH arguments fail for Davenport–Heilbronn *because of the missing Euler product*
URL fetched: https://ar5iv.labs.arxiv.org/abs/math/0311162  (Ivić, "On some reasons for doubting the Riemann hypothesis")
Quoted:
> "the number of zeros of f(s) for which σ>1 and 0<t=ℑm s≤T is ≫ T"
> "What is the most important difference between ζ(s) and f(s) which is accountable for the difference of distribution of zeros …? It is most likely that the answer is the lack of the Euler product for f(s) …"
> "the influence of the Euler product for ζ(s) will not extend all the way to the line σ=1/2."

**Bearing:** the Euler product enters density proofs at the **mollifier's Möbius coefficients (= the
coefficients of 1/ζ = Π_p(1−p^{-s}))**; mean-value theorems and the approximate functional equation
are FE/orthogonality-only and go through for any FE series. The Davenport–Heilbronn breakdown is
attributed in the literature (Ivić) precisely to the absence of that Euler product.

---

## CHECK 2 — Bombieri–Hejhal fixed-strip count

**VERDICT: PARTIALLY-KNOWN** (Bombieri–Hejhal's own 1995 Duke paper NOT fetched — projecteuclid
returned empty again; the precise statements below come from a fetched survey introduction that
states them, plus a fetched separate source for the off-line count).

**Key correction to the recalled framing:** the "≫ T zeros off the critical line in a fixed strip"
is a **THEOREM, unconditional**, but it is **NOT** Bombieri–Hejhal — it is Voronin, generalised by
Lee–Nakamura–Pańkowski. Bombieri–Hejhal's contribution is the *opposite* direction: the **conditional**
"100% of zeros ON the line" (Montgomery's conjecture), under GRH + a zero-spacing hypothesis. The two
coexist because `≫ T` is lower order than the total `~ (T/2π) log T`.

### Source: Lamzouri–Lee, "The number of zeros of linear combinations of L-functions near the critical line", arXiv:2010.10490
URL fetched: https://ar5iv.labs.arxiv.org/abs/2010.10490

- Off-line count (unconditional theorem, in any fixed strip `1/2 < σ₁ < σ₂ < 1`). Quoted:
  > "Voronin [24] proved that N_E(σ₁,σ₂,T) ≫ T for any 1/2<σ₁<σ₂<1 fixed"
  > "Lee, Nakamura and Pańkowski [16] generalized Voronin's result to zeros of linear combinations of L-functions in the strip 1/2<σ₁<σ₂<1 … they established that N_F(σ₁,σ₂,T) ≫ T"

- On-line "100%" — Montgomery's CONJECTURE, Bombieri–Hejhal's CONDITIONAL proof. Quoted:
  > "Although linear combinations of L-functions have many zeros off the critical line, it was conjectured by Montgomery that 100% of the zeros of F(s) lie on the critical line, if the L_j are primitive L-functions satisfying assumptions A1 and A2 below."
  > "Bombieri and Hejhal [1] established this conjecture if the L_j satisfy the assumptions A1, A2, A3 and A5 below, conditionally on the GRH and a zero-spacing hypothesis for each of the L_j."

Corroborating off-line count for the Davenport–Heilbronn function itself (fetched):
URL: https://ar5iv.labs.arxiv.org/abs/math/0311162 — "the number of zeros of f(s) for which σ>1 and 0<t≤T is ≫ T".

**Bearing:** YES, `≫ T` off-line zeros in every fixed strip `1/2 < σ₁ < σ₂ < 1` is **PROVEN
unconditionally** (Voronin; Lee–Nakamura–Pańkowski) for linear combinations of L-functions — this
is the density-theorem violation the lab certified numerically, and it needs no hypothesis. The
"almost all on the line / 100%" statement is a *conjecture* (Montgomery) proved only conditionally
(GRH + zero-spacing) by Bombieri–Hejhal under structural assumptions A1,A2,A3,A5 on the constituents.
The exact `N_off ≍ ?` asymptotic constant from BH's original paper remains [UNVERIFIED] here.

---

## CHECK 3 — Speiser's theorem, exact statement

**VERDICT: VERIFIED-KNOWN** (two independent fetched sources agree).

**Statement:** RH ⟺ ζ′(s) has **no non-real zeros** in the OPEN strip `0 < Re s < 1/2`. The qualifier
"non-real" is essential (it excludes ζ′'s real zeros, which sit on the negative axis / between trivial
zeros); the region is the open left half of the critical strip.

### Source A: arXiv:math/0701726 (zeros of ζ′ near the critical line)
URL fetched: https://ar5iv.labs.arxiv.org/abs/math/0701726
Quoted:
> "A. Speiser [13] has a theorem which says that RH is equivalent to the nonexistence of nonreal zeros of ζ′(s) in Re(s)<1/2."

### Source B: arXiv:1904.03123 (extended Selberg class zeta-functions and their derivatives)
URL fetched: https://ar5iv.labs.arxiv.org/abs/1904.03123
Quoted:
> "Speiser [17] showed that the Riemann hypothesis (RH) is equivalent to the absence of non-real zeros of the derivative of the Riemann zeta-function ζ(s) left of the critical line σ=1/2."

**Bearing:** exact region confirmed OPEN `0 < Re s < 1/2`; "non-real / nonreal zeros" is the correct
trivial-exception qualifier. Original: A. Speiser, "Geometrisches zur Riemannschen Zetafunktion",
Math. Ann. 110 (1935) [publication details from search HINT, page not fetched — [UNVERIFIED]].

---

## CHECK 4 — Levinson–Montgomery quantitative pairing

**VERDICT: VERIFIED-KNOWN** (exact statement fetched verbatim).

**Statement:** with `N⁻(T)` = #{zeros of ζ(s) in `0<t<T, 0<σ<1/2`} and `N₁⁻(T)` = #{zeros of ζ′(s)
in the same region},
> **N₁⁻(T) = N⁻(T) + O(log T).**

So ζ and ζ′ have the same number of zeros left of the critical line, up to `O(log T)` — the
quantitative form of Speiser.

### Source: arXiv:1904.03123, introduction (citing Levinson–Montgomery 1974)
URL fetched: https://ar5iv.labs.arxiv.org/abs/1904.03123
Quoted verbatim (as rendered by the fetch; the "N(T)" on the RHS is `N⁻(T)`):
> "Let N⁻(T) be the number of zeros of ζ(s) in R: 0<t<T, 0<σ<1/2. Let N₁⁻(T) be the number of zeros of ζ′(s) in R. Then N₁⁻(T) = N⁻(T) + O(log T)."

### Related L–M refinement (fetched, same authors' 1974 paper)
URL fetched: https://ar5iv.labs.arxiv.org/abs/math/0701726
Quoted:
> "N. Levinson and H. L. Montgomery [8] proved that for nonreal zeros of ζ′(s) the average value of β′ with 0<γ′⩽T is 1/2 + log log T / log T."

**Bearing:** the recalled shape is CONFIRMED — error term is exactly `O(log T)`, region is the open
left half-strip `0<σ<1/2`, `0<t<T`. Publication: Levinson & Montgomery, "Zeros of the derivatives of
the Riemann zeta-function", Acta Math. 133 (1974), pp. 49–65 [page range from search HINT +
projecteuclid `euclid.acta/1485889821`; the L–M paper itself was not fetched — the *statement* above
is fetched from the citing paper 1904.03123]. Later refinement: the "average β′ = 1/2 + loglog T/log T"
result (also L–M 1974) sharpens the picture near the line; modern work (Suriajaya; Goldston–Suriajaya)
continues the count of ζ′-zeros near σ=1/2.

---

## BONUS — "L(s,χ)/ζ almost-periodic (Bohr/Besicovitch) in σ>1/2 ⟺ (G)RH"

**VERDICT: UNRESOLVED.** No fetchable primary/textbook statement of the *equivalence* was located.
The fetched RH survey explicitly contained no such theorem:
URL fetched: https://arxiv.org/html/2602.04022 — the fetch reports "no explicit statement of an
equivalence between the Riemann Hypothesis and almost-periodicity … The document mentions the
Bohr–Landau program … references the Borchsenius–Jessen theorem … but these concern value
distribution and universality rather than stating an equivalence with RH." Search surfaced only
Bohr-equivalence-relation papers (arXiv:1711.04122, 1801.08864), not the RH equivalence. Marked
[UNVERIFIED]; would need Titchmarsh Ch. XI or Bohr's original to confirm.

---

## Search-term log
- "zero-density theorem Riemann zeta mollifier Möbius coefficients Euler product multiplicativity proof"
- "Bombieri Heilbronn distribution zeros linear combinations Euler products Duke 1995 zeros strip theorem statement"
- "Speiser theorem Riemann hypothesis equivalent zeta derivative no zeros left critical strip statement"
- "Levinson Montgomery zeros derivatives Riemann zeta function Acta Mathematica 1974 counting left critical line"
- "Righetti zeros linear combinations L-functions Bombieri Hejhal positive proportion off critical line strip statement arxiv"
- "Levinson Montgomery N_1(T) zeros zeta prime left critical line O(log T) number of zeros Re s < 1/2 comparison"
- "Suriajaya Levinson and Montgomery zeta zeta' same number zeros sigma < 1/2 O(log T) quantitative Speiser"
- "Davenport-Heilbronn function number of zeros sigma > 1/2 gg T strip positive proportion off critical line theorem"
- "Bohr Besicovitch almost periodic Dirichlet series Riemann hypothesis equivalent 1/zeta sigma > 1/2 theorem"

## URLs actually fetched this session
- https://terrytao.wordpress.com/2024/07/07/a-computation-outsourced-discussion-of-zero-density-theorems-for-the-riemann-zeta-function/  (Check 1 — mollifier/Möbius, mean value, approx FE, Huxley exponent)
- https://ar5iv.labs.arxiv.org/abs/math/0311162  (Check 1/2 — Davenport–Heilbronn ≫T off-line + "lack of Euler product")
- https://ar5iv.labs.arxiv.org/abs/2010.10490  (Check 2 — Voronin/LNP ≫T; Montgomery conj; Bombieri–Hejhal conditional 100%)
- https://ar5iv.labs.arxiv.org/abs/math/0701726  (Check 3 Speiser; Check 4 L–M average β′)
- https://ar5iv.labs.arxiv.org/abs/1904.03123  (Check 3 Speiser; Check 4 exact N₁⁻(T)=N⁻(T)+O(log T))
- https://arxiv.org/html/2602.04022  (Bonus — no equivalence found)
- (empty/undecodable, noted: projecteuclid Duke BH `.short`; arxiv.org/pdf of 2010.10490, math/0701726, 2311.10285, 1904.03123, 1902.03064; kurims kokyuroku 2013-05.pdf; farr-pauli PDF)
