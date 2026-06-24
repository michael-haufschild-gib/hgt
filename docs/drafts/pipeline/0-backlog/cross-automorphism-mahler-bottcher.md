# Cross-Automorphism Mahler Independence for Böttcher Coordinates

- **ID:** cross-automorphism-mahler-bottcher
- **Stage:** 0-backlog
- **Type:** OPEN QUESTION → CANDIDATE THEOREM
- **Source:** Wheeler id=1632, Turing id=1637 / hgt session 2026-06-24

## The Question

Standard Mahler theory (Adamczewski–Faverjon, Nguyen arXiv:1310.2329) handles algebraic
independence of functions satisfying Mahler equations with the SAME automorphism. Nguyen Cor 5.1
proves {ψ_c : c ≠ 0,−2} algebraically independent as functions of t, where each ψ_c satisfies

    ψ_c(t²) = ψ_c(t)² + c.

The automorphism t ↦ t² is IDENTICAL for all c. The multi-function Mahler independence follows
from this common automorphism structure.

For the inverse Böttcher coordinates φ_c = ψ_c^{−1}, the functional equation is

    φ_c(f_c(z)) = φ_c(z)²,    f_c(z) = z² + c.

The automorphisms f_{c_i}(z) = z² + c_i are DISTINCT for distinct c_i. This is the
"cross-automorphism" case: different Mahler automorphisms for different functions.

**Open question (Wheeler id=1632):** Does Mahler theory extend to prove algebraic independence
of functions satisfying Mahler equations with DISTINCT polynomial automorphisms?

## Why this is genuinely hard (not search)

Standard Mahler method proof sketch for SAME automorphism σ: given P(F₁,...,F_n) = 0,
apply σ repeatedly to get P(F₁(σ^k(z)),...,F_n(σ^k(z))) = 0. Each F_i(σ^k(z)) = G_i(F_i(z))
for a known rational function G_i (from iterating the Mahler equation). As k → ∞, the
substitution z → σ^k(z) drives to 0 (or ∞), and analytic estimates give contradiction.

For DIFFERENT automorphisms σ_i: applying σ₁ to P(φ_{c₁}(z), φ_{c₂}(z)) = 0 gives
P(φ_{c₁}(z)², φ_{c₂}(f_{c₁}(z))) = 0.

The "alien" term φ_{c₂}(f_{c₁}(z)) appears — the Böttcher coordinate of f_{c₂} evaluated
at f_{c₁}-orbit points. Define G_n(z) = φ_{c₂}(f_{c₁}^n(z)). Then:
- G_0 = φ_{c₂}(z)
- G_{n+1} ≠ G_n(z)² in general (since f_{c₁} ≠ f_{c₂})

The f_{c₂}-Mahler equation does NOT simplify G_n; you are generating an INFINITE tower of new
functions, not a finite orbit. The standard Mahler argument breaks here.

## Key asymptotic observation [CONJECTURE]

Near ∞: φ_{c₂}(w) = w + c₂/(2w) + O(w^{−3}). So:

    G_n(z) = φ_{c₂}(f_{c₁}^n(z)) = f_{c₁}^n(z) · (1 + c₂/(2(f_{c₁}^n(z))²) + O(|f_{c₁}^n|^{−4})).

Meanwhile φ_{c₁}(z)^{2^n} ≈ f_{c₁}^n(z) to leading order (since φ_{c₁}(z) ≈ z · (corrections)).

So G_n(z) / φ_{c₁}(z)^{2^n} → 1 as n → ∞. The ratio is 1 + O(|f_{c₁}^n(z)|^{−2}).

If P(φ_{c₁}(z)^{2^n}, G_n(z)) = 0, writing G_n = φ_{c₁}^{2^n}(1 + error) with error → 0:

    P(u, u(1+ε_n)) = 0,   u = φ_{c₁}(z)^{2^n}.

For the leading homogeneous part P_d(1,1) must be 0. This is a constraint on P_d, not a
contradiction automatically (P_d(1,1) = 0 defines a specific locus in parameter space of P).

**The gap:** the ratio G_n/φ_{c₁}^{2^n} → 1 gives a constraint but not an immediate
contradiction unless we can show P has no factor vanishing at (1:1) in ℙ¹, i.e., (Y−X) ∤ P.
But (Y−X) | P would mean φ_{c₂}(z) = φ_{c₁}(z) identically, which is false for c₁ ≠ c₂.
So the degree-1 case is covered. Higher degree requires showing the limit is not just (1:1).

[OPEN CORE: does the ratio G_n/φ_{c₁}^{2^n} → a nontrivial algebraic function of φ_{c₁}(z)
or does it converge to 1 in all algebraic coordinates? If it has a nontrivial limit, the
leading-homogeneous-part argument might close.]

## Alternative route: independence via the formal power series ring

Both φ_{c₁}(z) and φ_{c₂}(z) are formal Laurent series in 1/z near z = ∞:
    φ_c(z) = z + c/(2z) - c²/(8z³) + ...  (Faber polynomial expansion)

[CONJECTURE] The formal power series φ_{c₁}, φ_{c₂} ∈ ℂ[[1/z, z]] are algebraically
independent over ℚ̄(c₁,c₂,z) as formal series.

This is a formal analog of the function-field theorem, but it bypasses complex-analytic
arguments entirely. It might be accessible via graded coefficient analysis: if P(z,φ_{c₁},φ_{c₂})=0,
then comparing coefficients of z^{-n} in the Laurent expansion gives polynomial relations among the
Faber polynomial coefficients, which are known to be algebraically independent over ℚ̄.

[Sub-question: Are the Faber polynomial coefficients of φ_c, as polynomials in c, algebraically
independent over ℚ̄ as c varies? This is a commutative-algebra question about the Faber
polynomial family.]

## Connection to Dynamical Mordell-Lang

If φ_{c₁} and φ_{c₂} satisfied an algebraic relation, after iterating f_{c₁} we'd have:
    P(φ_{c₁}(z)^{2^n}, φ_{c₂}(f_{c₁}^n(z))) = 0.

The orbit {f_{c₁}^n(z)} intersects the algebraic curve P = 0 in the (Y₁,Y₂)-plane in an
orbit-like fashion. The dynamical Mordell-Lang conjecture (proved for polynomials in characteristic 0
by Bell–Ghioca–Tucker 2010, generalized by Favre–Jonsson type results) controls when an orbit
has infinitely many intersections with an algebraic subvariety. If the orbit {f_{c₁}^n(z_0)} is
Zariski-dense in ℂ (which it is for non-preperiodic z_0), then DML-type arguments might force
the algebraic subvariety to be "large" in a controlled sense.

[CONJECTURE] The cross-automorphism independence follows from a DML-type theorem applied to the
joint (z, φ_{c₂}(z)) curve in ℂ² and the f_{c₁}-orbit hitting it infinitely often.

## Why it would be NOVEL × SIGNIFICANT if resolved

- NOVEL: The distinct-automorphism case is explicitly NOT covered by Nguyen's Mahler machinery,
  which requires the same automorphism. An algebraic proof would not reduce to the known corpus
  (confirmed by team audit: Adamczewski–Faverjon, Mahler, Nguyen all require a single map).
- SIGNIFICANT: It would close Q6.2 for ALL c₁,c₂ (connected AND disconnected, c_i ∈ M or not),
  replacing the geometric route (which needs Green-crossing for disconnected). It would also give
  a purely algebraic proof of the connected theorem, independent of complex analysis.

## Priority

High. The geometric connected-case proof is done (2-fully-proven). The remaining frontier is:
1. (Easier) Disconnected case via Green-crossing lemma.
2. (Deeper) All-c via cross-automorphism Mahler.

The cross-automorphism Mahler direction, if successful, supersedes both.

## Attacks to try

1. Faber coefficient algebraic independence (formal algebra).
2. Ratio G_n/φ_{c₁}^{2^n} limit analysis (leading-term argument).
3. DML-type theorem applied to the cross-orbit curve.
4. Weil restriction / algebraic geometry approach: view the pair (φ_{c₁},φ_{c₂}) as a section
   of a product of algebraic groups (moduli spaces of degree-2 polynomials), and use arithmetic
   geometry to control algebraic relations.

## ψ-substitution reformulation (Wheeler id=1678)

For c₁ ≠ c₂ both ∉ M (the close-pair case where no natural-boundary crossing exists):
Set z = ψ_{c₁}(w) in P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0. For |w| > max(r₁, r₂):
ψ_{c₁}(w) ∈ Δ_{c₁} ∩ Δ_{c₂} (verified: G_{c₂}(ψ_{c₁}(w)) ≈ log|w| > G_{c₂}(0)).
The relation becomes:
  P(ψ_{c₁}(w), w, Q(w)) = 0  where Q(w) = φ_{c₂}(ψ_{c₁}(w)).

So: Q is algebraic over ℂ(w, ψ_{c₁}(w)) iff φ_{c₁} and φ_{c₂} are algebraically dependent.

The HT of φ_{c₂} over ℂ(y) (for y-variable) says φ_{c₂}(y) is transcendental over ℂ(y). But Q(w) = φ_{c₂}(y(w)) with y(w) = ψ_{c₁}(w): this doesn't directly give "Q transcendental over ℂ(w, y(w))" because the map w ↦ y(w) is NOT surjective onto ℂ (only hits an open subset of ℂ), so specialization from ℂ(y) to ℂ(w, y(w)) doesn't directly work.

**HT composition lemma [OPEN CORE]:** If f is HT over ℂ(y) and g: ℂ → ℂ is a conformal map with Zariski-dense image, then f(g(z)) is transcendental over ℂ(z, g(z)).

This would close the close-pair case via the ψ-substitution (ψ_{c₁} maps {|w|>r₁} conformally onto Δ_{c₁}, which is Zariski-dense in ℂ since Δ_{c₁} is open). BUT: the specialization argument fails unless A(w, y, f(y)) = B(y, f(y)) (no w-dependence). The equation A = P(ψ_{c₁}(w), w, Q(w)) = 0 DOES depend on w. So the composition lemma as stated doesn't reduce to the y-only transcendence.

**Remark:** The ψ-substitution is an ISOMORPHIC reformulation of the original problem, not a simplification. It connects the close-pair Q6.2 to the question: "is φ_{c₂}(y) transcendental over ℂ(y, w) when y = ψ_{c₁}(w)?" — a question about the differential/algebraic Galois group of the pair (ψ_{c₁}(w), φ_{c₂}(ψ_{c₁}(w))) as functions of w.

## Log

- 2026-06-24 — Created. Wheeler id=1632 first proposed the direction; Turing id=1637 confirmed
  it is outside existing Mahler/A-F machinery. Team consensus: this is the "genuine novelty
  frontier" beyond the cross-corpus bridge theorem.
- 2026-06-24 — Wheeler id=1678: ψ-substitution reformulation added. Shows the close-pair
  case reduces to the HT composition lemma (φ_{c₂}(ψ_{c₁}(w)) transcendental over
  ℂ(w, ψ_{c₁}(w))). The lemma requires new methods; existing HT transcendence doesn't suffice.

## Asymptotic cross-orbit analysis (Wheeler 2026-06-24)

**Partial result from the n→∞ orbit limit.**

If P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0, apply z ↦ f_{c₁}^n to get:
  P(f_{c₁}^n(z), φ_{c₁}(z)^{2^n}, G_n(z)) = 0
where G_n = φ_{c₂}(f_{c₁}^n(z)).

Near ∞: f_{c₁}^n(z) = W + c₁/(2W) + O(W^{-3}) and G_n = W + c₂/(2W) + O(W^{-3}) where
W = φ_{c₁}(z)^{2^n}. Substituting and expanding in 1/W:

P(W + c₁/(2W), W, W + c₂/(2W)) = P(W,W,W) + (c₁·P_z + c₂·P_{Y₂})(W,W,W)·W^{-2} + O(W^{d-4}) = 0.

**Forced constraints (two, in order of 1/W):**

(C1) P(z,z,z) ≡ 0 as a polynomial in z. [From the leading term: P(W,W,W) must vanish for all large W.]

(C2) c₁·(∂P/∂z)(z,z,z) + c₂·(∂P/∂Y₂)(z,z,z) ≡ 0 as polynomials. [From the 1/W² term.]

**What C1 gives:** P(z,z,z) ≡ 0 means P ∈ (Y₁ - z, Y₂ - z) as an ideal in ℂ[z, Y₁, Y₂]:
  P = (Y₁ - z)·A + (Y₂ - z)·B.
Then: (φ_{c₁}-z)·A + (φ_{c₂}-z)·B = 0. Near ∞: (c₁/(2z))·A_0 + (c₂/(2z))·B_0 + O(z^{-2}) = 0,
so c₁·A_0 + c₂·B_0 = 0 where A_0, B_0 are leading values of A, B.

**Obstruction to completing the argument:** (C1) and (C2) give necessary conditions on P but not
a full contradiction for fixed c₁ ≠ c₂. Continuing to higher orders generates more constraints
(each order gives: c₁·(higher partial) + c₂·(higher partial) ≡ 0), which involve c₁/c₂ = fixed
ratio. Whether the infinite system forces P = 0 depends on the algebraic independence of the Faber
coefficients a_k(c₁) and a_k(c₂) as complex numbers (not as polynomials in c).

**Conclusion:** the cross-orbit approach gives partial obstructions but does not currently close the
close-pair case. The Faber coefficient algebraic independence question (attack 1 in the main card)
remains the key.

