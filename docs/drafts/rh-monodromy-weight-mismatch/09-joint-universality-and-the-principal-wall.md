# 09 — Local transfers from joint universality, and the principal wall

Register: SEARCH-register document. §1 is a theorem modulo two named classical imports
(exact statements to re-verify at promotion, marked [CHECK]); §2 is a structural analysis
locating the ζ-obstruction in representation terms; §3 opens the next objects. Companions:
07 §3 (transfer lemma), 08 (mechanism ranking), `computations/R6LOC-RESULTS.md` (the
measured instance this explains).

---

## 1. The family theorem: (H-loc) holds for Davenport–Heilbronn `[THEOREM modulo imports]`

Setup. f = c₁·L(s, χ) + c₂·L(s, χ̄) with χ the (non-principal) character mod 5 with
χ(2) = i, c₁ = (1−iκ)/2, c₂ = (1+iκ)/2. Fix a certified off-line zero ρ₀ of f and a
closed disc D̄ = B̄(ρ₀, r) inside the strip, with margin m := min_{∂B} |f| > 0, subject to:

(Z) both L(s, χ) and L(s, χ̄) are zero-free on D̄.

**Theorem.** Assume (Z). Then for every ε > 0 the return set
{τ ∈ ℝ : sup_{s ∈ D̄} |f(s + iτ) − f(s)| < ε}
has positive lower density. In particular, taking ε < m, every return transfers the seed
by the Rouché lemma (07 §3): the f-defect set at this seed's parameters has positive lower
density — (H-loc) holds at every (Z)-admissible seed of the family.

*Proof.* The pair (L(·, χ), L(·, χ̄)) consists of L-functions of distinct (hence
non-equivalent) Dirichlet characters, so the **joint universality theorem** applies
`[CHECK: Voronin 1975 joint universality for distinct Dirichlet L-functions; positive
LOWER density form as in the Laurinčikas/Steuding expositions]`: for any compact K with
connected complement and any pair of targets continuous and NON-VANISHING on K, analytic
in its interior, the set of τ for which both L(· + iτ, χ), L(· + iτ, χ̄) are ε′-close to
the targets on K has positive lower density. Take K = D̄ (closed disc: connected
complement), targets = (L(·, χ)|_{D̄}, L(·, χ̄)|_{D̄}) — admissible EXACTLY by (Z). For
such τ,
sup_{D̄} |f(s+iτ) − f(s)| ≤ |c₁| sup_{D̄} |L(s+iτ,χ) − L(s,χ)| + |c₂| sup_{D̄} |L(s+iτ,χ̄) − L(s,χ̄)|
< (|c₁| + |c₂|) ε′,
and ε′ := ε/(|c₁|+|c₂|) gives the claim. The transfer clause is 07 §3 verbatim. ∎

Status of (Z): for the concrete disc B̄(0.8085 + 85.699i, 0.15) it is numerically verified
in range (GRH for mod-5 characters verified far beyond t ≈ 86); as a hypothesis it is
per-disc and checkable — the theorem is unconditional except for this explicit,
machine-checkable clause and the two classical imports.

Consequences.
1. **The family's measured recurrence is now explained, not just observed**: defect
   recurrence in the D–H family is sustained by positive-density local self-returns of
   the component pair — the R6-loc certified transfer (τ = 91.005, r = 0.15) is a visible
   member of a positive-density return set.
2. **The R6 (big-box) negative is reinterpreted**: positive density exists at every ε,
   but the return frequency degrades with contour size and tolerance; τ ≤ 400 was simply
   below the first big-box return. Sample-scale negatives do not contradict the theorem.
3. **R7's pre-registration upgrades to a test of the imports**: the transfer graph should
   be dense on pairs whose discs satisfy (Z). A measured sparse graph would FALSIFY the
   import chain — a genuine falsification channel.

Why this does not reduce to known: Bagchi-type strong recurrence for a SINGLE function in
the strip is RH(χ)-equivalent territory; here the seed's vanishing is carried by the
COMBINATION while both component targets stay nonvanishing — the mechanism threads
universality's nonvanishing hypothesis through the split. The lane's contribution is the
weld: (joint universality) + (Rouché transfer of the coarse invariant) ⟹ positive-density
defect recurrence in an FE family — the proven half of the family picture.

## 2. The principal wall — why the same proof cannot run for ζ

Try to transpose: write ζ as a combination over a modulus q,
ζ(s) = q^{−s} Σ_{a=1}^{q} ζ(s, a/q),
and decompose the Hurwitz family over characters mod q: span{ζ(s, a/q)} =
span{L(s, χ) : χ mod q} (plus imprimitivity bookkeeping). Individual Hurwitz zetas with
rational parameter are STRONGLY universal (targets with zeros allowed)
`[CHECK: Bagchi/Gonek, rational-parameter Hurwitz universality]` — which is exactly why
such functions provably have off-line zeros. One might hope: self-approximate the VECTOR
(ζ(·, a/q))_a on a seed disc, sum, and transfer a hypothetical ζ-seed — (H-loc) for ζ,
hence (with the quantified Reduction) RH.

**The wall.** The joint theorems for the Hurwitz/L-basis demand nonvanishing targets in
each PRIMITIVE L-direction — and the change of basis puts ζ itself (times finitely many
explicit Euler factors) in the PRINCIPAL-character direction. Self-approximation at a
ζ-seed requires the principal-direction target to be a function VANISHING on the disc
(it contains the seed) — precisely the excluded case. The non-principal directions'
freedom (the source of "strong" universality for individual Hurwitz zetas) cannot absorb
the seed: the seed's vanishing is a constraint on the FULL sum, and the principal
component is pinned to ζ's own translate. Every modulus q erects the SAME wall.

Consistency check (this had to happen): were the wall absent, the argument would prove RH
unconditionally, contradicting Bagchi's equivalence (strong recurrence of ζ ⟺ RH). Our
chain independently re-derives the necessity of a wall and NAMES it:

> **(H-loc for ζ) ⟺ self-approximation in the principal direction at a vanishing target.**

The open core of M1, in representation terms: universality theory handles every direction
of the decomposition except the one-dimensional principal line, and the seed sits exactly
there. (Note the alignment with the banked projection-blindness no-go — the ambient torus
sees all non-principal directions; what it cannot see is precisely what lives on the
principal line.)

## 3. Opened

1. **Multi-modulus covering `[CONJECTURE space]`**: the principal directions of different
   moduli q are different lines in different decompositions. Does some finite family of
   decompositions have principal walls with empty joint constraint on the seed jet? The
   expected obstruction: all principal lines contain the same invariant vector (the
   a₁ = 1 coefficient direction / the constant 1 in the Selberg-class sense). Sharp
   sub-question, new object: **which linear functionals of the local jet are
   universality-blind?** — the "blind cone". If the blind cone is exactly the principal
   line for every decomposition, the wall is representation-independent and (H-loc for ζ)
   is irreducibly principal; if not, a covering attack exists. Either answer is structure.
2. **Primitivity grading `[CONJECTURE]`**: in the Selberg-class family picture (00 §7),
   "provable (H-loc) via component splitting" should align exactly with NON-primitivity
   (≥ 2 jointly-universal components carrying the seed), and the principal wall with
   primitivity. D–H (non-primitive, two components) vs ζ (primitive) instantiates both
   cells. Testable inside the family: Epstein zetas of class number > 1 (non-primitive
   splittings exist) should show dense transfer graphs; degree-1 primitives should not.
3. **R7 as import-test**: run the transfer graph on (Z)-admissible pairs; density is now a
   PREDICTION of §1, not a guess (chunk 0 = zero localization running).
