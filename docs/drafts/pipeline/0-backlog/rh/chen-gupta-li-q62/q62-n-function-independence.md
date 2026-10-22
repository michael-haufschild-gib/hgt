# Q6.2 — n-Function Böttcher Independence

- **ID:** q62-n-function-independence
- **Stage:** 0-backlog
- **Type:** OPEN CANDIDATE
- **Source:** Nguyen arXiv:1310.2329 Question 6.2 / inverse-Böttcher lane (n-function generalization)

## Statement (target)

For distinct c₁,...,c_n ∈ M \ {0,−2} (all n≥2), the inverse Böttcher coordinates
φ_{c₁}(z),...,φ_{c_n}(z) are algebraically independent over Q̄(c₁,...,c_n,z).

The n=2 case is proved: `2-fully-proven/q62-bottcher-independence-natural-boundary.md`.

## Inductive structure

Assume φ_{c₁},...,φ_{c_{n-1}} algebraically independent over Q̄(z) (inductive hypothesis).
Suppose P(z, φ_{c₁},...,φ_{c_n}) = 0 with P ∈ Q̄(c₁,...,c_n)[z,Y₁,...,Y_n] \ {0}, P
irreducible with positive degree in Y_n (= variable for φ_{c_n}).

The proof requires finding z₀ where:
(a) z₀ ∈ J_{c_n}  [needed for Step 2: φ_{c_n} has no analytic continuation past J_{c_n}]
(b) z₀ ∈ ∩_{j<n} Ω_{c_j}  [needed for Step 3: all other φ_{c_j} analytic at z₀]
(c) z₀ ∉ Bad  [bad locus = coefficient poles + discriminant zeros, locally discrete]

(c) follows from (a)+(b) once J_{c_n} ∩ (∩_{j<n} Ω_{c_j}) is uncountable.

## Key open lemma (simultaneous crossing)

**Lemma [OPEN]:** For distinct c₁,...,c_n ∈ M \ {0,−2}:

  J_{c_n} ∩ (∩_{j<n} Ω_{c_j}) = J_{c_n} \ (∪_{j<n} K_{c_j}) ≠ ∅.

## What's known

- n=2: J_{c₂} ∩ Ω_{c₁} ≠ ∅. Proof: suppose J_{c₂} ⊂ K_{c₁}; fullness gives K_{c₂} ⊂ K_{c₁};
  energy test (Riesz-Jensen mixing) gives cap(K_{c₁}) > 1; contradicts Pritsker. ✓
- Pairwise crossings: J_{c_n} ∩ Ω_{c_j} ≠ ∅ for each j<n. But simultaneous intersection needs
  J_{c_n} ∩ ∩_j Ω_{c_j} = J_{c_n} \ ∪_j K_{c_j} ≠ ∅.

## Why the n=2 argument doesn't immediately extend

The n=2 proof works by: J_{c_n} ⊂ K_{c_j} ⟹ K_{c_n} ⊂ K_{c_j} (fullness of K_{c_j}) ⟹
cap(K_{c_j}) > cap(K_{c_n}) = 1. Contradiction.

For n≥3: J_{c_n} ⊂ ∪_j K_{c_j} does NOT imply K_{c_n} ⊂ K_{c_j} for any single j (the Julia set
could be "split" among multiple filled Julia sets). The energy argument cannot be applied to the
individual K_{c_j}.

## Approaches to try

**Approach 1 (Baire):**
Claim: J_{c_n} ∩ Ω_{c_j} is open and DENSE in J_{c_n} for each j.
- Open: Ω_{c_j} is open.
- Dense = K_{c_j} ∩ J_{c_n} has empty interior in J_{c_n}.

If both hold, Baire's theorem (J_{c_n} a compact metric space, hence Baire) gives:
∩_{j<n} (J_{c_n} ∩ Ω_{c_j}) is dense in J_{c_n}, hence nonempty.

Sub-claim needed: K_{c_j} ∩ J_{c_n} has empty interior in J_{c_n}.

Evidence for sub-claim: Let U ⊂ K_{c_j} ∩ J_{c_n} be relatively open in J_{c_n}. Since
f_{c_n}|_{J_{c_n}} is topologically transitive (classical fact for any polynomial Julia set),
the forward orbit ∪_k f_{c_n}^k(U) is dense in J_{c_n}. In particular, the orbit visits
J_{c_n} ∩ Ω_{c_j} (which is nonempty by the pairwise crossing). So the orbit of U under
f_{c_n} leaves K_{c_j}. But this means only that f_{c_n}^k(U) ⊄ K_{c_j} for some k — it does
NOT immediately mean U doesn't exist, only that the orbit escapes K_{c_j}.

[The sub-claim is plausible but not immediately proved by topological transitivity alone.]

**Approach 2 (Topological):**
J_{c_n} is connected (for c_n ∈ M). If J_{c_n} ⊂ ∪_{j<n} K_{c_j} and the K_{c_j} are pairwise
disjoint: J_{c_n} is connected, so it must be entirely in one K_{c_j} — contradicting pairwise
crossing. ✓ for PAIRWISE DISJOINT K_{c_j}.

For K_{c_j} that overlap: J_{c_n} could be partly in K_{c₁} ∩ K_{c₂}, partly in K_{c₁} \ K_{c₂},
etc. The connectedness argument fails if the K_{c_j} mutually overlap.

When are K_{c₁} and K_{c₂} disjoint? For c₁, c₂ ∈ M with K_{c₁} ∩ K_{c₂} = ∅: 
by the 2-function energy argument, cap(K_{c₁} ∪ K_{c₂}) > max(cap K_{c₁}, cap K_{c₂}) = 1
(for disjoint sets of positive capacity, capacity is superadditive). But cap(K_{c_j}) = 1 already.
Hmm: for disjoint compact sets A, B: cap(A ∪ B) ≥ max(cap A, cap B). But equality is possible.

[Pairwise disjointness of the K_{c_j} is a strong hypothesis that doesn't hold for all parameters.]

**Approach 3 (Measure: for Baire sub-claim via equilibrium measure):**
The equilibrium measure μ_{c_n} of K_{c_n} is supported on J_{c_n} (since K_{c_n} is connected).
If K_{c_j} ∩ J_{c_n} has nonempty interior in J_{c_n}: it supports positive μ_{c_n}-mass.
By ergodicity of μ_{c_n} w.r.t. f_{c_n}: the orbit of μ_{c_n}-a.e. point equidistributes on
J_{c_n}. But the forward orbit might leave K_{c_j}...

[Measure approach runs into the same orbit-escape issue as Approach 1.]

**Approach 4 (New algebraic route - cross-automorphism Mahler):**
See `0-backlog/cross-automorphism-mahler-bottcher.md`. A purely algebraic proof of algebraic
independence for ALL c (connected and disconnected) via a cross-automorphism Mahler theorem
would bypass the simultaneous crossing issue entirely. If provable, supersedes all geometry.

## Priority

Medium. The n=2 (connected) and the Green-crossing (disconnected u₀⊥φ_b) are the more
immediately productive results. The n-function case is a natural extension but has a genuine
open lemma. 

## Log

- 2026-06-24 — Created. n=2 connected case proved and promoted. n-function case open.
  Simultaneous crossing lemma identified as the key obstacle.
