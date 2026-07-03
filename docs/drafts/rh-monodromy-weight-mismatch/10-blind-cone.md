# 10 — The blind cone: 09 §3.1 answered

Register: SEARCH-register document. §§2–4 are theorems modulo NAMED imports (marked); §5 is a
derivation with an explicit computed witness; §6 is structure; §7 opens. Companions: 09
(family theorem + principal wall), 07 §3 (transfer lemma), 06 §6 (quantified Reduction),
`computations/R8-RESULTS.md` (the phase data §7.1 consumes).

Question answered (09 §3.1): *which linear functionals of the local jet are
universality-blind — and is the blind cone the same for every decomposition?*

---

## 1. Setup: the modulus-q system and its steering basis

Fix q. The system is the Hurwitz family F_q = {ζ(s, a/q)}_{a=1..q} together with all
ℂ-linear functionals c ↦ g_c(s) = Σ_a c_a ζ(s, a/q), considered on the strip
1/2 < Re s < 1. Two functionals are EQUIVALENT if their g's differ by a factor analytic,
nonvanishing, and bounded away from 0 on every compact of the strip (elementary factors:
q^s, 1 − p^{−s}, finite Euler products) — equivalent functionals have identical strip zero
sets and identical (H-loc) status, since Rouché data passes through nonvanishing factors.

Change of basis (coprime block): ζ(s, a/q) = (q^s/φ(q)) Σ_{χ mod q} χ̄(a) L(s, χ) for
gcd(a,q) = 1; non-coprime a reduce to Hurwitz functions of smaller modulus, so by induction
every g_c collects, up to equivalence, to a combination over the CANONICAL COORDINATES: the
L(s, χ*) for primitive χ* of conductor dividing q, together with ζ itself (the trivial
direction). Call the set of coordinates with nonzero collected coefficient the SUPPORT of c.

Definition. c is **blind** if the joint-universality toolkit cannot certify (H-loc) at any
off-line seed of g_c; **steerable** otherwise.

## 2. Theorem A — support ≥ 2 is steerable `[THEOREM modulo verified import + (Z')]`

**Theorem.** Let g = Σ_{j=1}^r c_j L_j (r ≥ 2, canonical coordinates, pairwise
non-equivalent). Let ρ₀ be a zero of g on a closed disc D̄ in the strip satisfying

(Z′) every component L_j is zero-free on D̄.

Then the local self-return set {τ : sup_{D̄} |g(s+iτ) − g(s)| < ε} has positive lower density
for every ε > 0; for ε < the Rouché margin, every return transfers the seed (07 §3). (H-loc)
holds at every (Z′)-admissible seed.

*Proof.* Verbatim the 09 §1 proof with r targets: joint universality
[VERIFIED 2026-07-03 — C6, Matsumoto Thm 7: pairwise non-equivalent characters, positive
lower density, nonvanishing targets; sub-case flag: when ζ itself is in the support the
tuple includes the trivial character — standard statements admit it, re-verify the exact
hypothesis at promotion] applied to self-targets (L_j|_D̄)_j, admissible exactly by (Z′);
triangle inequality with ε′ = ε/Σ|c_j|. ∎

D–H is the case r = 2, q = 5. Note the mechanism: the seed's vanishing is carried by the
COMBINATION while every coordinate stays nonvanishing — r ≥ 2 is what makes (Z′) compatible
with g(ρ₀) = 0.

## 3. Theorem B — single lines are RH-grade `[THEOREM modulo density import]`

**Theorem.** Let g be equivalent to c·L(χ) (support = one line). Then:
(i) (Z′) is UNSATISFIABLE at any seed — a zero of g on the disc IS a zero of the unique
component, so the nonvanishing-target hypothesis fails at every seed. The toolkit of
Theorem A certifies nothing: the line is blind, and blindness is intrinsic
(hypothesis-violation), not a gap in technique.
(ii) Proving (H-loc) at the line's hypothetical off-line seeds by ANY means proves RH(χ):
positive-density returns at an off-line zero β₀ > 1/2 transfer the defect (07 §3) to ≫ T
disjoint heights up to T, contradicting the Carlson-type zero-density bound
N_χ(σ₀, T) = o(T) `[CHECK at promotion: standard density theorem for Dirichlet L-functions,
same import class as 06's Carlson/Ingham]` via the quantified Reduction (06 §6 verbatim with
L(χ) in place of ξ). Hence no off-line seed exists — RH(χ).

So the dichotomy is exact: off the lines, (H-loc) is a theorem; on the lines, (H-loc) IS the
Riemann hypothesis of that line. (This recovers Bagchi's equivalence shape through the
transfer-lemma route, independently of his tightness argument — the consistency 09 §2
demanded.)

## 4. Theorem C — the cone is the same for every q `[DERIVATION, no analytic imports]`

**The blind cone of the modulus-q system is the finite union of its canonical coordinate
lines. ζ lies on one of them — the trivial/principal line — for EVERY q.**

*Proof.* §1's collection: any functional's support is well-defined up to equivalence; Theorem
A steers everything of support ≥ 2; Theorem B blinds every line. For ζ: the collection of ζ
in the modulus-q system is q^{−s}·(all-ones functional), which collects to
L(s, χ₀)·(elementary) = ζ·(elementary) — support = {ζ}, a single canonical line, for every
modulus simultaneously. ∎

**Consequence — 09 §3.1 resolved on the yes-branch.** Multi-modulus covering is impossible:
the hoped-for family of decompositions whose principal walls have empty joint constraint
does not exist, because the ζ-line is a CANONICAL COORDINATE of every finite Dirichlet
decomposition at once — the invariant-vector obstruction 09 §3.1 anticipated is the actual
mechanism. The wall is representation-independent; (H-loc for ζ) is irreducibly principal
within the Dirichlet world. The primitivity grading (09 §3.2) is now a THEOREM inside this
world: steerable = non-primitive (support ≥ 2), blind = primitive (one line).

## 5. The same wall in Hurwitz coordinates: unique factorization `[DERIVATION + witness]`

The individually-STRONGLY-universal Hurwitz basis (Thm 10, verified: rational a/q ≠ 1, 1/2,
vanishing targets allowed) looks like an escape — its coordinates can hit vanishing targets.
It is not, and the reason is arithmetic, not analytic.

Take q = 3. With L₀ = L(·,χ₀), L₁ = L(·,χ₁) (χ₁ the quadratic character mod 3):
ζ(s,1/3) = (3^s/2)(L₀ + L₁), ζ(s,2/3) = (3^s/2)(L₀ − L₁), so
> ζ(s,1/3) + ζ(s,2/3) = 3^s·L₀(s) = (3^s − 1)·ζ(s),
and 3^s − 1 is nonvanishing on the strip. The strongly-universal pair is a ROTATION of
(L₀, L₁); the sum functional collapses back to the principal line. Joint STRONG universality
of the pair AT SELF-TARGETS is the one missing tool: it would give positive-density
self-returns at a hypothetical ζ-seed, hence (06 §6 + 07 §3) contradict Carlson density,
hence prove RH outright. So its known sufficient condition MUST fail — and it does,
explicitly. The joint-strong theorems (Matsumoto Thm 15, verified via C6) require the
ℚ-linear independence of {log(n + α_j)}_{n≥0, j}. For (α₁, α₂) = (1/3, 2/3):

> **log(0 + 2/3) + log(2 + 2/3) = 2·log(1 + 1/3)**, i.e. (2/3)(8/3) = (4/3)², i.e. 2·8 = 4².

A nontrivial ℤ-relation; the hypothesis fails. And the general mechanism: relations
∏(nᵢ + a/q)^{εᵢ} = 1 are exactly multiplicative relations among rationals with denominator
q — which exist precisely because integers FACTOR. For transcendental α there are none:
∏(nᵢ + α)^{εᵢ} = 1 forces the rational function ∏(X + nᵢ)^{εᵢ} − 1 to vanish at a
transcendental point, hence identically, hence all εᵢ = 0 (distinct linear factors). That is
why strong universality at transcendental α is provable directly while at rational α it
routes through the L-decomposition — circularly, back into the principal pinning.

**The wall's carrier is the fundamental theorem of arithmetic.** Principal-direction pinning
(character coordinates) and log-dependence (Hurwitz coordinates) are one fact in two bases,
and the fact is: composites factor. Lean witnesses for both sides of this dichotomy:
`RHTower/LogIndependence.lean` (the explicit q = 3 relation; the transcendental-shift
independence).

## 6. The chiasmus `[STRUCTURE]`

Across the lane's Reduction the same arithmetic acts with OPPOSITE signs:
- (D) density o(T): multiplicativity is the ENGINE — Euler enters through the μ(n) mollifier
  (C4-verified, 06); without it no density theorem.
- (R_k) recurrence: multiplicativity is the OBSTRUCTION — unique factorization creates the
  log-relations that break joint-strong universality on the principal line (§5).

RH, in this lane's coordinates, sits pinched between the two faces of one structure: the
multiplicative integers power the half that counts zeros and block the half that would
recur them. A proof through M1 must either find recurrence input that is not
universality-shaped (§7.1) or change the arithmetic itself (§7.2).

## 7. Opened

1. **Phase-weighted universality `[new object]`.** R8 (chunk 0) measured that actual returns
   select on jet PHASE: the transfer classes are arg f′-clusters, floor ≈ |Δ arg f′|
   (derived to first order in R8-RESULTS). Universality theorems are jet-blind — they
   approximate values on discs, with no control of the direction the return lands in. A
   universality statement WITH a jet-direction constraint (does the return set conditioned
   on |Δ arg f′| < δ still have positive density?) is strictly new tooling; its
   principal-line restriction is exactly what (H-loc for ζ) lacks. Delegatable [CHECK]:
   literature on joint universality of (L, L′) / derivative universality — does any known
   statement control arg f′ at returns?
2. **The Beurling trichotomy (B1 × B2 collision — task #96 aimed).** In a Beurling system,
   FTA is a DESIGN CHOICE. No generalized-number system can have all three of: (i)
   Carlson-type density o(T); (ii) a steerable zeta-analog (support ≥ 2 in a
   jointly-strongly-universal basis — possible iff the system's log-relation module is
   trivial enough, e.g. prime-supported frequencies: {log(p/q) : p prime ≠ q} IS
   ℚ-independent, by the same FTA argument that kills composite support); (iii) an off-line
   zero. Systems built to violate RH (Diamond-type) must therefore fail (i) or (ii) — WHICH
   one fails, as the system's arithmetic is dialed, is a measurable diagnostic of what
   carries RH. First move: the Hilberdink–Lapidus FE-class reading (board #96), now with a
   sharp question to ask of each system.
3. **Minimal relation-blindness `[CONJECTURE]`, with a proved miniature `[DERIVATION]`.**
   ζ's Dirichlet series is supported on ALL integers; the obstruction of §5 is carried by
   composite support. Conjecture: the wall is not an accumulation of relations but is
   present in each single one — the blind cone is "locally principal" and any covering-style
   attack dies at the FIRST relation, not asymptotically.
   The two-frequency miniature is already a theorem modulo Kronecker: on a vertical line,
   g_A(σ+it) = a·2^{−σ}z + b·4^{−σ}z² with z = 2^{−it} — the SINGLE relation 4 = 2² pins the
   value orbit to the algebraic curve (z, z²), one real dimension; whereas
   g_B(σ+it) = a·2^{−σ}z + b·3^{−σ}w has (z, w) dense in the 2-torus (Kronecker + the
   ℚ-independence of log 2, log 3 — the prime instance of
   `RHTower.log_prime_shifts_independent`), so the value set fills the full 2-dimensional
   region. One relation costs exactly one steering dimension; steering onto a generic target
   (in particular a vanishing one) is lost at the first relation. What remains open is the
   INFINITE-frequency version: whether the relation module's rank deficit equals the lost
   steering codimension for genuine Dirichlet series (the "rank–codimension law").
