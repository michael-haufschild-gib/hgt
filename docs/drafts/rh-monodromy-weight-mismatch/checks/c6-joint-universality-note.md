# C6 — Verified literature reading: two classical imports for the DH self-return proof

Date: 2026-07-03. All quotes below are from URLs fetched THIS session (WebFetch downloaded the
arXiv PDFs; the binary was rendered page-by-page via the PDF reader). Page numbers are the
printed page numbers of each paper.

Primary source (authoritative survey, fetched + read in full over the relevant sections):
- **Matsumoto, "A survey on the theory of universality for zeta and L-functions", arXiv:1407.4216** (2014).
  URL fetched: `https://arxiv.org/pdf/1407.4216`
Corroborating source (second independent statement, fetched + read):
- **Lee–Nakamura–Pańkowski, "Selberg's orthonormality conjecture and joint universality of L-functions", arXiv:1503.03620** (v3, 2015).
  URL fetched: `https://arxiv.org/pdf/1503.03620`
Also fetched (context, not load-bearing): `https://arxiv.org/abs/1006.1507` (Garunkštis, self-approximation — a *different* notion L(s+iτ) vs L(s+idτ), and its Thm 1 has a known gap).

Shared definitions (Matsumoto p.2, verbatim):
> "For any subset K ⊂ ℂ, let H^c(K) be the set of continuous functions defined on K, and are
> holomorphic in the interior of K, and let H₀^c(K) be the set of all elements of H^c(K) which are
> non-vanishing on K. By meas S we mean the usual Lebesgue measure of the set S."
> "D(a,b) = {s ∈ ℂ | a < σ < b}."

So the admissibility class **H₀^c(K)** = {continuous on K, holomorphic in interior of K, non-vanishing on K};
**H^c(K)** drops the non-vanishing requirement. `D(1/2,1)` = open strip 1/2 < Re s < 1.

---

## CHECK 1 — Joint universality of Dirichlet L-functions, positive-lower-density form

### VERDICT: **VERIFIED-KNOWN**

**Exact statement (Matsumoto, Theorem 7, p.11, verbatim):**
> "**Theorem 7.** (Voronin, Gonek, Bagchi) *Let χ₁,…,χ_r be pairwise non-equivalent Dirichlet
> characters, and L(s,χ₁),…,L(s,χ_r) the corresponding Dirichlet L-functions. Then the joint
> universality holds for L(s,χ₁),…,L(s,χ_r) in the region D(1/2,1).*"

Preamble giving the attribution (Matsumoto p.11, verbatim):
> "The joint universality for Dirichlet L-functions was already obtained in the first decade by
> Voronin [206][207][208], Gonek [40], and Bagchi [3][4], independently of each other."

The meaning of "joint universality holds" is fixed by the definition on p.10 (eq. (4.1), verbatim):
> "Let K₁,…,K_r be compact subsets of D(a,b) with connected complements, and f_j ∈ H₀^c(K_j)
> (1 ≤ j ≤ r). If Dirichlet series φ₁(s),…,φ_r(s) satisfy
> liminf_{T→∞} (1/T) meas{ τ ∈ [0,T] | sup_{s∈K_j} |φ_j(s+iτ) − f_j(s)| < ε (1 ≤ j ≤ r) } > 0
> for any ε > 0, we call the joint universality holds for φ₁(s),…,φ_r(s) in the region D(a,b)."

**(a) Attribution.** Voronin (1975 thesis/papers), Gonek (1979 thesis), Bagchi (1981 thesis) —
independently. Corroborated by Lee–Nakamura–Pańkowski p.3 (verbatim):
> "Voronin in [20] (see also [8, Chapter VII, Theorem 3.2.1]) proved also the so-called joint
> universality theorem for Dirichlet L-functions associated with pairwise non-equivalent Dirichlet
> characters. Roughly speaking, he proved that any collection of analytic non-vanishing functions
> f₁, f₂,…,f_n can be approximated, in the Voronin sense, by the shift L(s+iτ;χ₁), L(s+iτ;χ₂),…,
> L(s+iτ;χ_n), where χ₁,…,χ_n are pairwise non-equivalent Dirichlet characters."

**(b) Density form = LOWER density (liminf), not upper.** The `liminf_{T→∞} (1/T) meas{…} > 0`
in (4.1) is positive lower density. Confirmed a second time by LNP p.1 (verbatim, single-function
modern form): "∀_{ε>0} liminf_{T→∞} (1/T) meas{τ ∈ [0,T] : max_{s∈K}|ζ(s+iτ)−f(s)| < ε} > 0,
where meas{·} denotes the Lebesgue real measure." (Cf. also Matsumoto Thm 1 (1.2), same liminf shape.)

**(c) Target admissibility per component = H₀^c(K_j):** continuous on K_j, analytic in the interior,
**non-vanishing on K_j**. Each K_j compact ⊂ D(1/2,1) with connected complement. (This is the
standard Voronin class; the joint version keeps the per-component non-vanishing requirement — it is
NOT strong for L-functions with Euler product.)

**(d) Same-modulus distinct characters qualify.** The only condition is "pairwise non-equivalent."
Standard definition (not printed verbatim in either fetched source, but a definitional fact, not a
citation): two Dirichlet characters are *equivalent* iff induced by the same primitive character;
hence *distinct primitive* characters are automatically non-equivalent. χ and χ̄ mod 5 are both
primitive (5 prime, χ non-principal ⇒ primitive) and distinct (χ has order 4, so χ ≠ χ̄ = χ³) ⇒
**pairwise non-equivalent** ⇒ Theorem 7 applies with r = 2. The proof's independence input is the
orthogonality of characters (Matsumoto p.11: "this is embodied by the orthogonality relation of
Dirichlet characters, which is essentially used in the proof").

**Lab usage covered?** YES, fully. The lab needs joint self-returns of the pair
(L(s+iτ,χ), L(s+iτ,χ̄)) on a small disc K ⊂ D(1/2,1). Self-approximation targets are the functions'
own restrictions g₁ = L(·,χ)|_K, g₂ = L(·,χ̄)|_K, which are non-vanishing on the closed disc by
hypothesis (Z) ⇒ g_j ∈ H₀^c(K). A closed disc has connected complement. Theorem 7 (r=2, K₁=K₂=K)
then yields liminf-positive density of τ with sup_K|L(s+iτ,χ)−g₁|<ε AND sup_K|L(s+iτ,χ̄)−g₂|<ε.
That is exactly "the component pair self-returns on the disc with positive lower density,"
conditional on both components zero-free on K. The two imports the lab lists (joint universality +
zero-free ⇒ self-return targets admissible) are precisely Theorem 7 with self-targets.

---

## CHECK 2 — Hurwitz zeta strong universality (rational parameter), and the joint family

### VERDICT (single-function strong universality): **VERIFIED-KNOWN**
### VERDICT (joint family {ζ(s,a/q)}_a, and the "principal-wall" prediction): **PARTIALLY-KNOWN** — obstruction + mechanism confirmed; the exact "principal-direction ⇒ nonvanishing targets" clause is the lab's own (mechanically consistent) reading, not printed verbatim.

**Exact single-function statement (Matsumoto, Theorem 10, p.13, verbatim):**
> "**Theorem 10.** (Bagchi [3], Gonek [40]) *Let K be a compact subset of D(1/2,1) with connected
> complement, and f ∈ H^c(K). Then for any ε > 0,*
> liminf_{T→∞} (1/T) meas{ τ ∈ [0,T] | sup_{s∈K} |ζ(s+iτ,α) − f(s)| < ε } > 0
> *holds, provided α is transcendental or rational (≠ 1, 1/2).*"

Note the target class is **H^c(K)** (no non-vanishing) — this is *strong* universality. Matsumoto
p.14 (verbatim):
> "A remarkable point is that, in the statement of Theorem 10, we do not assume that the target
> function f(s) is non-vanishing on K. This is a big difference from Theorem 1, and when a
> universality-type theorem holds without the non-vanishing assumption, we call it a *strong
> universality theorem*."

**Attribution:** Bagchi (1981 thesis) and Gonek (1979 thesis), independently. NOT Sander–Steuding.
**Excluded parameters:** α = 1 and α = 1/2 (the two cases where ζ(s,α) reduces to an Euler-product
function: ζ(s,1)=ζ(s), ζ(s,1/2)=(2^s−1)ζ(s)). Also stated: "algebraic irrational α is still open."
Strip: D(1/2,1).

**Rational reduction mechanism (Matsumoto p.14, eq. (5.2), verbatim):**
> "when α = a/b is rational, then in view of the formula
> ζ(s,a/b) = (b^s/φ(b)) Σ_{χ (mod b)} χ̄(a) L(s,χ),
> we can reduce the problem to the joint universality of Dirichlet L-functions, so we can apply
> Theorem 7."

### Joint version for the family {ζ(s,a/q)}_a and the principal wall

The fetched material bears directly on the lab's principal-wall prediction:

1. **Joint-strong-universality theorems for Hurwitz/Lerch require log-linear-independence that
   FAILS for common-denominator rationals.** Matsumoto Theorem 15 (Laurinčikas–Skerstonaitė, p.17,
   verbatim):
   > "**Theorem 15.** … *Assume that the elements of the set {log(n+α_j) | 1 ≤ j ≤ r, n ∈ ℕ₀} are
   > linearly independent over ℚ. Then the joint strong universality holds for
   > ζ(s,α₁,𝔅₁),…,ζ(s,α_r,𝔅_r) in the region D(1/2,1).* In the case 𝔅_j = {1}_{n=0}^∞ … (that is,
   > the case of Hurwitz zeta-functions), the above result was already given in Laurinčikas [91]."
   For a fixed denominator q and α_j = a_j/q, the numbers log(n + a_j/q) = log((qn+a_j)/q) are
   ℚ-linearly dependent (shared prime logs) ⇒ the hypothesis of Theorem 15 is NOT met ⇒ this route
   gives NO joint strong universality for {ζ(s,a/q)}_a.

2. **Relations among the functions positively OBSTRUCT joint universality.** Matsumoto p.19 (verbatim):
   > "If there is some relation among several Dirichlet series, then the behaviour of those Dirichlet
   > series cannot be independent of each other, so the joint universality among them cannot be
   > expected. Nakamura [168] pointed out that some collections of Lerch zeta-functions cannot be
   > jointly universal, because of the inversion formula among Lerch zeta-functions."
   Corroborated by LNP p.3 (verbatim, concrete relation-obstruction example):
   > "The second author in [13] Example 7.5 observed that, for non-principle Dirichlet character χ,
   > the Dirichlet L-functions L(s,χ) and L(s−i,χ) cannot be jointly universal…"

**Consistency with the lab's principal-wall prediction.** The family {ζ(s,a/q)}_a is a *fixed
invertible linear image* of {L(s,χ) : χ mod q} via (5.2). One of those directions is the principal
character χ₀, whose L-function L(s,χ₀) = ζ(s)·∏_{p|q}(1−p^{-s}) carries the Riemann ζ (Euler product,
pole at s=1) and admits only the *weak* (non-vanishing-target) universality of Theorem 1, never
strong universality. Hence any joint approximation of a target tuple (f_a)_a is reachable only when
its χ₀-component (≈ the a-average, the "principal direction") is non-vanishing — a target tuple whose
principal combination has a zero is unreachable. That is exactly the lab's "principal wall." The
fetched statements **confirm the obstruction exists and its mechanism** (the inversion formula (5.2)
+ Nakamura's relation obstruction + failure of the log-independence hypothesis), which is consistent
with — and supplies the precise mechanism for — the lab's prediction. The survey does **not** print
the clause "the principal-character direction must be restricted to non-vanishing targets" verbatim;
that granularity is the lab's own reading of (5.2), and it is mechanically consistent with everything
fetched. So: principal-wall prediction = **CONSISTENT / supported, not verbatim at finest grain.**

**Lab usage covered?** Single ζ(s,a/q) strong universality (targets may have zeros, α = a/q ≠ 1,1/2):
YES (Theorem 10). A *fully strong* joint universality for the whole family {ζ(s,a/q)}_a (all
components allowed zeros): the fetched material says this should NOT hold (relation obstruction); a
surviving joint statement must constrain the χ₀/principal direction to non-vanishing targets — which
matches the lab's principal-wall argument rather than refuting it.

---

## Search-term log

WebSearch queries run this session:
1. `joint universality Dirichlet L-functions positive lower density Voronin Bagchi statement`
2. `Matsumoto survey value-distribution zeta L-functions joint universality arXiv 1407.4216`
3. `Hurwitz zeta function strong universality rational parameter Bagchi target functions zeros`
4. `"equivalent" Dirichlet characters joint universality "induced by the same primitive" non-equivalent condition`
5. `Nakamura Lerch zeta functions not jointly universal inversion formula obstruction rational parameters`

URLs fetched this session (WebFetch):
- `https://arxiv.org/pdf/1407.4216` (Matsumoto survey — PDF downloaded, read as pages 1–6, 10–19). LOAD-BEARING.
- `https://arxiv.org/pdf/1503.03620` (Lee–Nakamura–Pańkowski — PDF downloaded, read as pages 1–3). CORROBORATING.
- `https://arxiv.org/abs/1006.1507` (Garunkštis self-approximation — abstract only; different notion, Thm 1 has a known gap). CONTEXT.

Unverified / not needed from primary theses (Voronin 1975, Gonek 1979 thesis, Bagchi 1981 thesis):
the survey + LNP are the modern fetchable statements and carry the attributions; the original theses
were not fetched and are cited here only as attribution, per the survey. Steuding LNM 1877 and the
Laurinčikas–Garbaliauskienė textbook were NOT fetched → treated as [UNVERIFIED] as primary sources
(not required; the two arXiv sources fully cover both checks).
