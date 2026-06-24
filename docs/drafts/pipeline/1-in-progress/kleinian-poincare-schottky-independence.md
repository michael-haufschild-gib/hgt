# Algebraic Independence of Poincaré Series — Schottky Case

- **ID:** kleinian-poincare-schottky-independence
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Source:** Wheeler id=1663, id=1665 / backlog card `kleinian-poincare-independence.md` / hgt session 2026-06-24

## Statement

Let Γ₁, Γ₂ be Schottky groups with disjoint limit sets Λ(Γ₁) ∩ Λ(Γ₂) = ∅, and
∞ ∈ Ω(Γ₁) (standard setting: ∞ lies in the domain of discontinuity of Γ₁).
For k ≥ 1 (assuming absolute convergence of the series):

  θ_{Γ₁,k}(z) and θ_{Γ₂,k}(z) are algebraically independent over ℂ(z),

where θ_{Γ,k}(z) = Σ_{γ=(a b;c d)∈Γ} (cz+d)^{−2k}.

## Background

Poincaré series θ_{Γ,k}:
- Converge absolutely on Ω(Γ) = ℂ̂ \ Λ(Γ) for k > δ(Γ)/2 (δ = Hausdorff dim of Λ(Γ))
- Have poles at Γ·∞ when ∞ ∈ Ω(Γ): the γ = (a b;c d)-term (cz+d)^{-2k} has a
  pole at z = γ^{-1}(∞) = −d/c (since γ maps −d/c ↦ ∞). The set of all poles is
  {γ^{-1}(∞) : γ ∈ Γ} = Γ^{-1}·∞ = Γ·∞ (since Γ is a group). Note: γ(∞) = a/c
  (distinct from γ^{-1}(∞) = −d/c in general).
- For Schottky groups with ∞ ∈ Ω(Γ): the ∞-stabilizer Γ_∞ = {id} (no non-identity
  element of a standard Schottky group fixes ∞). Hence c ≠ 0 for all γ ≠ id, so:
  (i) A_γ = c^{-2k} ≠ 0 (each pole has nonzero Laurent coefficient), and
  (ii) distinct γ give distinct poles: γ₁^{-1}(∞) = γ₂^{-1}(∞) ⟺ γ₂γ₁^{-1}(∞) = ∞
       ⟺ γ₂γ₁^{-1} ∈ Γ_∞ = {id} ⟺ γ₁ = γ₂.
- The pole set Γ·∞ accumulates at Λ(Γ) (orbit of any point in Ω(Γ) under a
  non-elementary group accumulates at Λ(Γ))

Key fact: θ_{Γ,k} is TRANSCENDENTAL over ℂ(z) for non-elementary Γ. Proof: it has
infinitely many poles at Γ·∞ (a discrete infinite set). Any function algebraic over
ℂ(z) has finitely many singularities. So θ_{Γ,k} is transcendental over ℂ(z). ✓

## Proof (pole-accumulation argument)

Assume for contradiction: P(z, θ_{Γ₁,k}(z), θ_{Γ₂,k}(z)) = 0 for all z ∈ Ω(Γ₁) ∩ Ω(Γ₂),
where P ∈ ℂ[z,Y,Z] is nonzero, degree d in Y.

Write P(z,Y,Z) = Σ_{i=0}^{d} Y^i · Q_i(z,Z) where Q_d ≢ 0.

**Step 1 (Crossing).**
Since Λ(Γ₁) ∩ Λ(Γ₂) = ∅: Λ(Γ₁) ⊂ ℂ̂ \ Λ(Γ₂) = Ω(Γ₂). So Λ(Γ₁) ⊂ Ω(Γ₂).
In particular: Γ₁·∞ accumulates at Λ(Γ₁) ⊂ Ω(Γ₂). Since Ω(Γ₂) is open:
Γ₁·∞ ∩ Ω(Γ₂) is infinite and accumulates at Λ(Γ₁) ∩ Ω(Γ₂) ≠ ∅. ✓

**Step 2 (Pole order constraint).**
Choose a point λ ∈ Λ(Γ₁). Since Λ(Γ₁) ∩ Λ(Γ₂) = ∅, we have λ ∈ Ω(Γ₂).
The orbit Γ₂·∞ is locally finite in Ω(Γ₂), so there is a small neighborhood U compactly
contained in Ω(Γ₂) such that U contains only finitely many Γ₂-poles. Since Γ₁·∞
accumulates at λ, there are infinitely many Γ₁-poles z_n = γ_n^{-1}(∞) in U, and
after deleting those finitely many Γ₂-poles we still have an infinite sequence z_n → λ
at which θ₂ is analytic.

At each such pole z_n = γ_n^{-1}(∞) ∈ Γ₁^{-1}·∞ ∩ Ω(Γ₂) = Γ₁·∞ ∩ Ω(Γ₂):
only the γ_n-term of θ_{Γ₁,k} has a singularity at z_n (all other terms are analytic
there, by distinctness of poles from Background). So θ_{Γ₁,k}(z) ~ A_n/(z-z_n)^{2k}
with A_n = c_n^{-2k} ≠ 0 (since c_n ≠ 0 for Schottky groups, from Background).

P(z, θ₁(z), θ₂(z)) ≡ 0 as a meromorphic identity on Ω(Γ₁) ∩ Ω(Γ₂).
θ₂ is meromorphic on Ω(Γ₂) with poles only at Γ₂·∞, and the chosen z_n avoid these
poles. Hence θ₂ is analytic at z_n with θ₂(z_n) ∈ ℂ.
The leading Laurent coefficient of P(z, θ₁(z), θ₂(z)) at z_n (order 2kd) is:

  A_n^d · Q_d(z_n, θ₂(z_n)) = A_n^d · Σ_j P_{d,j}(z_n) θ₂(z_n)^j.

For the identity P(...) ≡ 0 to hold (no pole of order 2kd): this must equal 0.
Since A_n ≠ 0: Q_d(z_n, θ₂(z_n)) = 0 for every n. [★]

**Step 3 (Identity principle + contradiction).**
Define h(z) := Q_d(z, θ₂(z)) = Σ_j P_{d,j}(z) θ₂(z)^j.
This is MEROMORPHIC on Ω(Γ₂) (polynomial in the meromorphic θ₂ with polynomial coeff).

From [★]: h(z_n) = 0 for the chosen infinite sequence z_n → λ in Ω(Γ₂), and the z_n
avoid the poles of θ₂. Thus h has an infinite zero-set accumulating at λ ∈ Ω(Γ₂).
By the identity principle for meromorphic functions (vanishing on a set with accumulation
point in the domain implies identically zero):
h ≡ 0 on Ω(Γ₂).

So: Q_d(z, θ₂(z)) = Σ_j P_{d,j}(z) θ₂(z)^j = 0 identically on Ω(Γ₂).
Since Q_d ≢ 0 (as P has degree d in Y, so Q_d = Σ_j P_{d,j}(z) Z^j ≢ 0):
this is a polynomial relation for θ₂ = θ_{Γ₂,k}. Hence θ_{Γ₂,k} is ALGEBRAIC over ℂ(z).

CONTRADICTION: θ_{Γ₂,k} is transcendental over ℂ(z) (infinitely many poles at Γ₂·∞). ✓

Therefore P = 0 has no solution; θ_{Γ₁,k} ⊥ θ_{Γ₂,k}. □

## Proof mechanism: pole-accumulation

The argument is NOT divergence (θ → ∞ at Λ) but pole-accumulation:
- θ_{Γ₁,k} has actual POLES at Γ₁·∞ ⊂ Ω(Γ₂) (discrete but accumulating at Λ(Γ₁))
- An algebraic relation between θ₁ and θ₂ propagates the pole structure to a
  polynomial equation in θ₂ alone
- θ₂ transcendental → no polynomial relation exists → contradiction

This avoids E-vS, Kleinian rigidity, and any divergence argument. The only tools:
- Poles of θ_{Γ₁,k} are at Γ₁·∞ (direct from the series definition)
- Γ₁·∞ accumulates at Λ(Γ₁) (standard Kleinian group fact)
- Identity principle for analytic functions (standard complex analysis)
- Transcendence of individual θ_{Γ,k} (from infinitely many poles)

## Comparison with Q6.2 (Böttcher)

| Q6.2 Böttcher | Kleinian Poincaré (Schottky) |
|---|---|
| φ_c has natural boundary J_c | θ_{Γ,k} has poles at Γ·∞ ⊂ Ω(Γ) |
| J_c ∩ Ω_{c₂} ≠ ∅ (crossing, hard) | Λ(Γ₁) ∩ Ω(Γ₂) ≠ ∅ (automatic for disjoint limit sets) |
| E-vS rigidity needed | NOT needed (poles accumulate, IFT forces algebraic relation on θ₂) |
| Cantor vs connected distinction | No such distinction here |
| BOUNDED-type (|φ_c|=1 on J_c) | POLE type (θ → ∞ along Γ·∞) |

The Kleinian proof is strictly simpler than Q6.2 because:
1. Crossing is free (disjoint limit sets)
2. The "natural boundary" is not needed — POLES of θ₁ in the domain of θ₂ suffice
3. E-vS rigidity plays no role

## Novelty assessment

**NOVEL?** "Algebraic independence of Poincaré series for distinct Kleinian groups" is
not in the automorphic forms literature (which studies values, L-functions, not function-
field independence of the functions themselves). The pole-accumulation mechanism is a
new application of the identity principle to Poincaré series. Grade: HIGH.

**SIGNIFICANT?** Demonstrates the natural-boundary/pole-accumulation technique is
portable beyond polynomial dynamics. Shows Böttcher (bounded-type, needs E-vS) and
Poincaré series (pole-type, needs only crossing) are two instances of the same criterion
in different regimes. Grade: MEDIUM-HIGH (technique-portability, not core hgt).

**Bridge vs. deep-new?** The argument uses only standard facts (poles of Poincaré series,
identity principle, transcendence from poles). It is BRIDGE-GRADE (novel assembly of
known tools into a new result, not new machinery). This is consistent with the hgt
criterion: a cross-corpus bridge is still novel if the question wasn't known before.

## Open extensions

1. **General non-elementary Kleinian groups** (not just Schottky, not just disjoint limit
   sets): crossing condition Λ(Γ₁) ∩ Ω(Γ₂) ≠ ∅ needs work; Schottky case bypasses this.
2. **n-function generalization**: θ_{Γ₁,k},...,θ_{Γ_n,k} algebraically independent for
   n distinct non-elementary groups. Induction + simultaneous crossing lemma.
3. **Same group, different weights**: θ_{Γ,k₁} ⊥ θ_{Γ,k₂} for k₁ ≠ k₂?
   Both have the SAME poles at Γ·∞ → the pole-accumulation argument doesn't apply.
   A different mechanism is needed.

## Gates

- [x] 0 → 1  in-progress: proof complete, crossing verified for Schottky case
- [ ] 1 → 2  fully-proven: awaiting team verification (Turing, Professor, Haiku)

## Novelty kill-gate (2026-06-24)

Three targeted searches (Haiku id=1694, Professor id=1695):

1. "algebraic independence Poincaré series Kleinian groups" — returns transcendence of
   individual VALUES (Shiga 1988 type results), not function-field independence of the
   FUNCTIONS θ_{Γ,k} themselves over ℂ(z).
2. "function field independence automorphic forms" — returns Shimura, Hecke eigensystems,
   algebraic independence of PERIODS (Baker–Wüstholz etc.), not independence of the
   automorphic functions as functions of z.
3. "Poincaré series distinct groups disjoint limit sets" — returns Maskit combination
   theorem, Patterson–Sullivan theory, no algebraic-independence result.

Negative search evidence: no prior result found for the algebraic independence of
θ_{Γ₁,k} and θ_{Γ₂,k} as functions over ℂ(z) for distinct Kleinian groups with disjoint
limit sets. The pole-accumulation mechanism (identity principle forcing h ≡ 0 → algebraic
relation on θ₂ alone → transcendence contradiction) appears absent from the automorphic
forms / Kleinian groups literature.

GRADE: BRIDGE-GRADE (novel question, elementary mechanism). Not a deep new theorem, but a
new result for a classical function family via a cross-corpus bridge.

Source-kill status: SURVIVES (negative evidence only; further search possible but no
positive hit found).

## Log

- 2026-06-24 — Backlog card created (Wheeler id=1663).
- 2026-06-24 — Divergence type vs bounded type distinction identified (Wheeler id=1665).
- 2026-06-24 — Wheeler: worked out pole-accumulation proof (cleaner than divergence);
  moved to 1-in-progress. Schottky + disjoint limit sets case is the first closed instance.
- 2026-06-24 — Wheeler: fixed three proof-text gaps raised by Haiku id=1694 and
  Professor id=1695: (i) pole notation γ^{-1}(∞)=−d/c vs γ(∞)=a/c; (ii) non-cancellation
  via trivial ∞-stabilizer and distinct-poles argument for Schottky groups; (iii) identity
  principle applied to the meromorphic h (not analytic), with zero-set accumulating at
  Λ(Γ₁)∩Ω(Γ₂) after removing the at-most-countable Γ₂-pole obstruction set.
  Novelty kill-gate attempted: SURVIVES. Re-vote requested from Professor and Haiku.
- 2026-06-24 — Turing (id=1697): voted YES on Schottky case before the notation fix,
  having independently verified the main steps (stabilizer argument, leading coefficient,
  identity principle). Turing's scrutiny matched the corrected proof.
- 2026-06-24 — Professor: fixed a remaining zero-subsequence bug. The previous text
  incorrectly used "countable minus countable" to keep infinitely many Γ₁-poles away
  from Γ₂-poles. The repair uses local finiteness of Γ₂·∞ inside Ω(Γ₂): near any
  λ ∈ Λ(Γ₁) ⊂ Ω(Γ₂), only finitely many Γ₂-poles occur, while Γ₁·∞ has infinitely
  many poles accumulating at λ.
