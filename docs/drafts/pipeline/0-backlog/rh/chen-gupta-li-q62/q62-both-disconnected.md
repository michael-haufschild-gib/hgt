# Q6.2 — Both-Disconnected Böttcher Independence

- **ID:** q62-both-disconnected
- **Stage:** 0-backlog
- **Type:** OPEN CANDIDATE
- **Source:** Wheeler id=1669 / Turing id=1666 / hgt session 2026-06-24

## Statement (target)

For c₁ ≠ c₂, both ∉ M, both ∉ {0,−2}: φ_{c₁}(z) and φ_{c₂}(z) are algebraically independent
over Q̄(c₁,c₂,z) (where φ_{c_i} denotes the inverse Böttcher coordinate, single-valued on
Δ_{c_i} = {G_{c_i} > G_{c_i}(0)}).

Computationally confirmed by Turing id=1660: σ_min frozen for all 7 tested disconnected pairs.
So this is a "proof gap, not a truth gap."

## Proof structure (same 3 steps as Q6.2 connected)

**Step 1 (crossing):** ∃ z₀ with EITHER z₀ ∈ J_{c₁} ∩ Δ_{c₂} OR z₀ ∈ J_{c₂} ∩ Δ_{c₁}.
[OPEN SUB-LEMMA — see below]

**Step 2 (E-vS):** Any analytic continuation of a branch of φ_{c₁} past z₀ ∈ J_{c₁} gives Φ
with |Φ(z)| = exp(G_{c₁}(z)) → 1 as z → z₀. J_{c₁} ∩ D(z₀,r) is a relatively open subset
of J_{c₁} (even when J_{c₁} is a Cantor set!) contained in the smooth curve {|Φ|=1}. E-vS:
J_{c₁} ⊂ circle → c₁ ∈ {0,−2} → c₁ ∈ M. Contradicts c₁ ∉ M. ✓

[KEY: E-vS does NOT require J_{c₁} to be connected. The relatively-open-in-J_{c₁} piece of a
Cantor set in a smooth curve → E-vS → c₁ exceptional. Cantor set topology is irrelevant to
E-vS's conclusion about c₁.]

**Step 2 (role of ∂Δ_{c₁}):** The algebraic relation can be extended from Δ_{c₁} ∩ Δ_{c₂} to
near z₀ ∈ J_{c₁} ∩ Δ_{c₂} via a path in Ω_{c₁} ∩ Δ_{c₂}, crossing ∂Δ_{c₁} (smooth away
from 0). The polynomial relation m(z, φ_{c₂}(z), φ_{c₁}(z)) = 0 is preserved by analytic
continuation: m has analytic coefficients (in z, via φ_{c₂} single-valued on Δ_{c₂} ⊃ path)
and the continued branch of φ_{c₁} always satisfies m = 0. ✓

**Step 3 (algebraic IFT):** At z₀ ∈ J_{c₁} ∩ Δ_{c₂} (outside bad locus), φ_{c₂} is analytic
and the continued branch of φ_{c₁} satisfies m = 0 with nonzero discriminant. Algebraic IFT:
analytic branch Φ at z₀ extending φ_{c₁}. Contradicts Step 2. ✓

## Crossing condition — SPLIT (Wheeler id=1674)

**The crossing sub-lemma is FALSE in general.** It holds for distant pairs but fails for
close pairs. The proof splits into two regimes.

### Regime 1: Distant pairs — crossing holds (monodromy closes the case)

For c₁, c₂ ∉ M with |c₁ − c₂| above some threshold (empirical: all tested pairs with
|c₁−c₂| ≥ 0.2 show crossing):

**Claim [PARTIAL — holds for distant pairs]:** max_{K_{c₁}} G_{c₂} > G_{c₂}(0)
or max_{K_{c₂}} G_{c₁} > G_{c₁}(0).

**Evidence:** Turing id=1666 computed 7 pairs, ALL showed crossing. All had |c₁−c₂| ≥ 0.2.

**Monodromy argument (Turing id=1668–1670, verified Wheeler id=1671):** Given crossing,
say K_{c₁} ∩ Δ_{c₂} ≠ ∅:
- Branch points of φ_{c₁} in Ω_{c₁} = preimages f_{c₁}^{-k}(0) for k ≥ 0.
- These accumulate at K_{c₁}; for large k, f_{c₁}^{-k}(0) ∩ Δ_{c₂} ≠ ∅ (open set near K_{c₁}∩Δ_{c₂}).
- Loop around f_{c₁}^{-k}(0) in Δ_{c₂} gives monodromy e^{2πi/2^k}.
- {e^{2πi/2^k} : k ≥ K₀} generates ℤ[1/2]/ℤ (Prüfer group, infinite).
- φ_{c₁} is infinitely-branched at z ∈ Δ_{c₂} \ K_{c₁}. Degree-d relation caps ≤ d. Contradiction.

Alternate argument (Wheeler id=1669): E-vS fires even for Cantor J_{c₁} (relatively open
piece of J_{c₁} in smooth curve → J_{c₁} ⊂ circle → c₁ ∈ {0,−2} → c₁ ∈ M, contradiction).
Same conclusion.

### Regime 2: Close pairs — BOTH-NESTED, proof gap [GENUINELY OPEN]

**Crossing sub-lemma FAILS for close c₁ ≈ c₂ ∉ M.**

For c₁ = 0.3, c₂ = 0.301 (both ∉ M, close):
K_{c₁} ≈ K_{c₂} (nearby Cantor sets). G_{c₂}(K_{c₁}) ≈ G_{c₂}(K_{c₂}) = 0 << G_{c₂}(0) > 0.
So K_{c₁} ⊂ {G_{c₂} ≤ G_{c₂}(0)} = L₂. Symmetrically K_{c₂} ⊂ L₁. BOTH-NESTED.

Neither monodromy argument nor E-vS can fire (no crossing point for either).

**Why capacity arguments fail:** cap(L_i) = e^{G_{c_i}(0)} > 1 = cap(K_{c_j}), so
K_{c_j} ⊂ L_i is consistent with capacities.

**Why the mutual energy fails:** M = ∫ G_{c₂} dμ_{c₁} ≤ G_{c₂}(0) trivially holds when
G_{c₂} is small on K_{c₁} and G_{c₂}(0) > 0. No energy contradiction available.

**What Nguyen likely meant:** The close-parameter case IS the genuinely open part of Q6.2.
Distant disconnected pairs are likely folklore (standard monodromy). The close case forces
a different proof technique.

### Required for close-case proof

The algebraic relation P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0 holds on Δ_{c₁} ∩ Δ_{c₂} (both
single-valued there). Need to derive contradiction WITHOUT a natural-boundary argument.

Candidate approaches:
1. **Cross-automorphism Mahler** (backlog card `cross-automorphism-mahler-bottcher.md`):
   Apply f_{c₁} and f_{c₂} to generate an overdetermined system. The cross-orbit
   φ_{c₂}(f_{c₁}^n(z)) → ∞ at rate ~n gives a constraint that kills degree-d polynomials.
   [OPEN CORE — see backlog card]

2. **c-derivative + u₀⊥φ:** Differentiate P(z, φ_{c₁}, φ_{c₂}) = 0 in c₂ (viewing
   c₁, c₂ as formal transcendental parameters): P_Z · ∂_{c₂}φ_{c₂}(z) + ∂_{c₂}P = 0.
   This involves u_{c₂} = ∂_c φ_c|_{c=c₂}, and by u₀⊥φ_{c₂}: {u_{c₂}, φ_{c₂}} algebraically
   independent. But φ_{c₁} also in the mix; needs triple independence. [PARTIALLY REDUCES]

3. **Formal series independence:** Over Q̄(c₁, c₂, z), show φ_{c₁}(z) and φ_{c₂}(z) are
   algebraically independent as formal Laurent series in 1/z. The [z^{-1}] coefficient
   comparison gives c₁/2 vs c₂/2: distinct for c₁ ≠ c₂. Formal graded analysis might close.
   [CANDIDATE, not developed]

## Attacks to try (close-pair case only)

1. **Cross-automorphism Mahler:** Apply f_{c₁} and f_{c₂} alternately to P = 0 and study the
   tower {φ_{c₂}(f_{c₁}^n(z))} as n → ∞. Near ∞: φ_{c₂}(f_{c₁}^n(z)) ≈ φ_{c₁}(z)^{2^n}
   (both ≈ z^{2^n}), so the ratio → 1 — not a divergence, but does the ratio have a nontrivial
   second-order correction that kills any fixed-degree P?

2. **Formal series graded analysis:** In Q̄(c₁,c₂)[[1/z]], write P(z, φ_{c₁}, φ_{c₂}) = 0
   and compare the [z^{-1}] coefficient: (∂_Y P + ∂_Z P)|_{Y=Z=z} · (c₁+c₂)/2 + ... = 0.
   The first two terms involve c₁ - c₂ which is nonzero. Does grading kill P?

3. **Triangulate via u_{c₂}:** Differentiate P = 0 w.r.t. c₂ (formal parameter), get
   a relation involving u_{c₂} = ∂_c φ_c|_{c=c₂}. Then use triple independence
   {φ_{c₁}, φ_{c₂}, u_{c₂}} (reduction to 3-function independence problem).

4. **Numerical proximity test:** For c₁ = 0.3, c₂ = 0.301: compute sigma_min of the
   Vandermonde-like matrix of evaluations at N points. If sigma_min stays bounded away from 0
   as N → ∞: numerical confirmation of algebraic independence for close pairs.

## Status

**Distant pairs:** PROOF COMPLETE (crossing + monodromy/E-vS). Search-grade; likely folklore
for experts. Bridge-level for hgt.

**Close pairs (c₁ ≈ c₂ both ∉ M):** PROOF COMPLETE via capacity lemma + extended monodromy
(Wheeler id=1785, 2026-06-24). See section below.

## Log

- 2026-06-24 — Created. Turing id=1666 corrects earlier "no natural boundary" claim; identifies
  crossing as the open core. Wheeler id=1669 closes Steps 2+3 (E-vS for Cantor, relation extends
  past ∂Δ_{c₁}). Both-nested obstacle identified as genuine uncertainty.
- 2026-06-24 — Wheeler id=1671 rigourizes monodromy (branch points = preimages of 0 accumulate
  at K_{c₁}; Prüfer monodromy; disconnected argument conditional on crossing).
- 2026-06-24 — Wheeler id=1674 finds: crossing sub-lemma FALSE for close c₁ ≈ c₂ (both-nested
  holds). Monodromy argument complete ONLY for distant pairs. Close-pair case is the genuine
  open frontier. Card updated to split: distant (closed) / close (open).
- 2026-06-24 — Wheeler id=1785: CLOSE PAIR CLOSED. Capacity lemma proves K_{c₁} ⊄ K_{c₂} for
  c₁ ≠ c₂ ∉ M, enabling monodromy argument in extended domain {G_{c₁}>0} ∩ {G_{c₂}>0}.
  Full proof in section below. Pending Haiku source-check on capacity uniqueness theorem.

## 2026-06-24 Haiku audit -- finite formal truncations cannot close the close-pair case

Wheeler id=1746 proposed computing the first formal constraints `Q_1,Q_2` from the Böttcher expansion to test
whether they already force `c_1=c_2`. The promptability gate flags this as a finite-observation test. The test
fails structurally: any finite number of Laurent-coefficient constraints can be killed by choosing a polynomial
relation whose coefficients depend on `c_1,c_2`.

Use the direct Böttcher convention

`phi_c(f_c(z))=phi_c(z)^2`, `f_c(z)=z^2+c`,

and write

`phi_c(z)=z + a(c) z^-1 + b(c) z^-3 + d(c) z^-5 + O(z^-7)`,

where comparison in `phi_c(z^2+c)=phi_c(z)^2` gives

`a(c)=c/2`,

`b(c)=c(2-c)/8`,

`d(c)=-c^2(6-c)/16`.

Let `u_i=phi_{c_i}(z)-z`. For `c_1 != 0`, the polynomial

`P_1(z,Y,Z)=c_2(Y-z)-c_1(Z-z)`

satisfies

`P_1(z,phi_{c_1},phi_{c_2}) = c_1 c_2(c_2-c_1) z^-3/8 + O(z^-5)`,

so the `z^-1` constraint is canceled for every pair, including off-diagonal pairs.

Adding a cubic term cancels the next coefficient too:

`P_2(z,Y,Z)=c_2(Y-z)-c_1(Z-z) + [c_2(c_1-c_2)/c_1^2](Y-z)^3`.

Then

`P_2(z,phi_{c_1},phi_{c_2}) = -c_1 c_2(c_1-c_2)(c_1-2c_2+6) z^-5/32 + O(z^-7)`,

so `P_2` has no `z^-1` or `z^-3` term. Adding

`[c_2(c_1-c_2)(c_1-2c_2+6)/c_1^4](Y-z)^5`

also cancels the `z^-5` term.

The general mechanism is triangular. Since

`u_1 = (c_1/2) z^-1 + O(z^-3)`

is a formal uniformizer for the odd Laurent tail, the odd powers `u_1^{2n+1}` have distinct leading terms
`(c_1/2)^{2n+1} z^{-(2n+1)}`. Therefore, for every `N`, there is a polynomial

`R_N(T)=sum_{n=1}^N alpha_n T^(2n+1)`

over `Qbar(c_1,c_2)` such that

`c_2 u_1 - c_1 u_2 + R_N(u_1) = O(z^{-(2N+3)})`.

Equivalently, for every finite truncation depth `N`, the polynomial

`P_N(z,Y,Z)=c_2(Y-z)-c_1(Z-z)+R_N(Y-z)`

passes the first `N` nontrivial Laurent-coefficient tests even when `c_1 != c_2`.

### Consequence

Finite formal coefficient checks cannot prove the close-pair both-disconnected Q6.2 case. Any proof must use an
all-order argument: convergence/natural-boundary geometry, a finite-degree bound coupled to infinitely many
constraints, or a genuine cross-automorphism/dynamical obstruction. Computing `Q_1,Q_2` is therefore not a
valid promotion path; at best it produces finite truncation artefacts.

This also mirrors the HT finite-observation theorem: finite jets and finite asymptotic coefficients can be made
nonidentifying by triangular correction terms. Here the correction terms are polynomial in `Y-z`, not Gamma tails.

## Haiku id=1749: formal power series approach KILLED for close-pair

The conjecture "the infinite system {Q_k(c₁,c₂) = 0} forces c₁ = c₂" is FALSE.

With φ_c(z) = z + a(c)z^{-1} + b(c)z^{-3} + d(c)z^{-5} + ... and a = c/2, b = c(2-c)/8, d = -c²(6-c)/16:

P₁ = c₂(Y-z) - c₁(Z-z) kills the z^{-1} constraint for ALL off-diagonal pairs (c₁ ≠ c₂).

P₁ + [c₂(c₁-c₂)/c₁²](Y-z)³ kills both z^{-1} and z^{-3}.
Adding [c₂(c₁-c₂)(c₁-2c₂+6)/c₁⁴](Y-z)⁵ also kills z^{-5}.

The formal uniformizer u₁ = (c₁/2)z^{-1} + O(z^{-3}) allows canceling any finite number of
Laurent constraints by modifying P with odd powers of (Y-z). So the system {Q_k = 0} can be
satisfied to any finite order by an appropriate polynomial P — the diagonal-forcing argument
FAILS. The close-pair case needs an ALL-ORDER mechanism.

**Dead ends for the close-pair:**
1. n→∞ orbit (Wheeler): gives P(z,z,z) ≡ 0 and c₁·A₀ + c₂·B₀ = 0, but these are necessary conditions, not contradictions.
2. Formal power series (Wheeler, Haiku): finite constraints can ALWAYS be satisfied off-diagonal by modifying P. NO diagonal forcing from finite truncations.
3. Cross-orbit functional equations: asynchronous (f_{c₁} vs f_{c₂}), no interleaving structure.
4. Taylor expansion in (c₂-c₁): requires continuously varying c₂, which is not the setup.

**What IS needed for the close-pair:**
An ALL-ORDER argument — either:
(a) Showing the generating function Σ_k Q_k·t^k has no off-diagonal roots, or
(b) A completely different approach (crossing geometry at a deeper level).


## Close-pair proof (Wheeler id=1785, 2026-06-24) `[PROVED HERE — pending Haiku audit]`

### Capacity lemma

**Lemma:** For c₁ ≠ c₂, both ∉ M: K_{c₁} ⊄ K_{c₂}.

**Proof:** Assume K_{c₁} ⊊ K_{c₂} (strict containment).

Both K_{c_i} have logarithmic capacity 1: this follows from the Böttcher normalization
φ_c(z) ~ z as z → ∞, giving G_c(z) ~ log|z| and Robin constant = 0 = log(1/cap) for all c.

The equilibrium measure μ_{c₁} of K_{c₁} is the unique probability measure on K_{c₁}
minimizing logarithmic energy, achieving energy = 0 = log(1/cap(K_{c₁})).

Since K_{c₁} ⊊ K_{c₂}: μ_{c₁} is a probability measure on K_{c₂} with energy 0. But the
minimum energy over all probability measures on K_{c₂} is also 0 (= log(1/cap(K_{c₂}))). So
μ_{c₁} also minimizes energy on K_{c₂}.

By uniqueness of the equilibrium measure (every compact set of positive capacity has a unique
equilibrium measure — Theorem 3.3.4 in Ransford "Potential Theory in the Complex Plane"): the
minimizer on K_{c₂} is unique → μ_{c₁} = μ_{c₂}.

supp(μ_{c₁}) = K_{c₁} (equilibrium measure of a Cantor Julia set has full support = K_{c₁}).
supp(μ_{c₂}) = K_{c₂} (same reason).

μ_{c₁} = μ_{c₂} → K_{c₁} = K_{c₂}. By Böttcher injectivity (c ↦ K_c injective in the
quadratic family: K_{c₁} = K_{c₂} as sets implies the two polynomials are affinely conjugate,
and the only affine symmetry of z²+c₁ and z²+c₂ with the SAME Julia set forces c₁ = c₂):
contradiction with c₁ ≠ c₂. □

**Consequence:** ∃ z₀ ∈ K_{c₁} with z₀ ∉ K_{c₂}, i.e., G_{c₂}(z₀) > 0.

### Extended monodromy argument for close pairs

**Setup:** Assume P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0 holds on Δ_{c₁} ∩ Δ_{c₂} for some nontrivial
polynomial P of degree d = deg_Y(P) in Y = φ_{c₁}.

**Step 1 (Branch points in extended domain):** The branch points of φ_{c₁} are f_{c₁}^{-n}(0)
(preimages of 0 under f_{c₁}^n). These have G_{c₁}(f_{c₁}^{-n}(0)) = G_{c₁}(0)/2^n > 0 and
accumulate at K_{c₁}. Near z₀ ∈ K_{c₁} with G_{c₂}(z₀) > 0: by continuity of G_{c₂}, the
open set {G_{c₂} > 0} contains a neighborhood of z₀, hence contains f_{c₁}^{-n}(0) for all
large enough n (those accumulating near z₀). Choose n₀ with 2^{n₀} > d. Call p = f_{c₁}^{-n₀}(0)
a branch point in {G_{c₁} > 0} ∩ {G_{c₂} > 0}.

**Step 2 (Extension by analytic continuation):** The algebraic relation P(z, φ_{c₁}, φ_{c₂}) = 0
holds on Δ_{c₁} ∩ Δ_{c₂} ⊂ {G_{c₁} > 0} ∩ {G_{c₂} > 0}. By analytic continuation along
paths in {G_{c₁} > 0} ∩ {G_{c₂} > 0} (using the multivalued Böttcher maps on these larger
domains), P = 0 continues to hold everywhere in {G_{c₁} > 0} ∩ {G_{c₂} > 0}.

**Step 3 (Monodromy loop):** Take a small loop γ around p in {G_{c₁} > 0} ∩ {G_{c₂} > 0},
chosen to avoid all f_{c₂}^{-k}(0). This is possible because: p ∉ K_{c₂} (G_{c₂}(p) > 0),
so f_{c₂}^{-k}(0) accumulate at K_{c₂} but NOT near p; a loop small enough around p avoids
all finitely many f_{c₂}^{-k}(0) that could be near p.

After γ:
- φ_{c₁} → e^{2πi/2^{n₀}} · φ_{c₁}   [Böttcher monodromy: looping once around the branch
  point f_{c₁}^{-n₀}(0) gives a 2^{n₀}-th root of unity factor]
- φ_{c₂} → φ_{c₂}   [no f_{c₂}^{-k}(0) encircled, so no monodromy on φ_{c₂}]

By analytic continuation of P = 0: P(z, e^{2πi/2^{n₀}}·φ_{c₁}, φ_{c₂}) = 0.

**Step 4 (Degree contradiction):** Iterating k loops: P(z, e^{2πik/2^{n₀}}·φ_{c₁}, φ_{c₂}) = 0
for k = 0,1,...,2^{n₀}-1. These give 2^{n₀} distinct values of Y (distinct since
φ_{c₁}(z) ≠ 0 for z ∈ Δ_{c₁}) satisfying P(z,Y,φ_{c₂}(z)) = 0.

Since 2^{n₀} > d = deg_Y(P): the polynomial P(z,·,φ_{c₂}(z)) of degree d has more than d roots
→ P(z,Y,φ_{c₂}(z)) ≡ 0 in Y for each z. Writing P(z,Y,W) = Σ_k p_k(z,W)·Y^k: we get
p_k(z,φ_{c₂}(z)) = 0 for all z and all k. Since φ_{c₂} is transcendental over ℂ(z) (for
c₂ ∉ M \ {0,−2}): the polynomial p_k(z,W) must be identically 0 for each k. So P ≡ 0.
Contradiction with P nontrivial. □

**Therefore φ_{c₁} and φ_{c₂} are algebraically independent over ℂ(z) for ALL c₁ ≠ c₂ ∉ M.**

### Outstanding verification items before promotion to 2-fully-proven

(a) **Capacity uniqueness:** "A compact set of positive capacity has a unique equilibrium measure
(probability measure minimizing logarithmic energy)" — Ransford, Theorem 3.3.4 (or equivalent).
@Haiku: source-confirm.

(b) **supp(μ_c) = K_c for c ∉ M:** The equilibrium measure of a Cantor Julia set has full
support = K_c. Standard (equilibrium measure = balanced invariant measure = measure of max
entropy with support J_c = K_c). @Haiku: source-confirm.

(c) **Böttcher injectivity:** K_{c₁} = K_{c₂} → c₁ = c₂ for c_i ∉ M. [PROVED HERE]

The Böttcher coordinate φ_c is the unique conformal isomorphism ℂ\K_c → ℂ\𝔻 with
φ_c(z)/z → 1 as z→∞. Its Laurent expansion at ∞ is φ_c(z) = z + c/(2z) + O(z^{-2})
(from φ_c(z)² = φ_c(z²+c), matching coefficients). If K_{c₁}=K_{c₂} as sets, same
complement, Riemann map uniqueness gives φ_{c₁}=φ_{c₂}, hence c₁/2=c₂/2, so c₁=c₂. ✓
No external citation needed.

(d) **Transcendence of φ_{c₂} over ℂ(z):** For c₂ ∉ M \ {0,−2}, φ_{c₂}(z) is
transcendental over ℂ(z). [PROVED HERE, Wheeler id=1802]

The branch points of φ_{c₂}(z) are the preimages f_{c₂}^{-n}(0) for all n ≥ 1 (each
gives monodromy e^{2πi/2^n}). For c₂ ∉ M: 0 is not periodic for f_{c₂}, so all these
preimages are distinct → infinitely many distinct branch points.

An algebraic function p(z,w)=0 over ℂ(z) has branch points only at zeros of the
discriminant Δ(z) = Res_w(p, ∂p/∂w) — a polynomial in z, finitely many zeros.

Infinitely many branch points ⟹ not algebraic over ℂ(z). ✓

Note: (d) is an instance of the same Böttcher monodromy structure underlying the full Q6.2
proof — not an independent lemma.

## 2026-06-24 Haiku audit — source gates and continuation-component gate

Anti-theatre check: no computation is relevant here. The proof is decided by four structural facts: equilibrium uniqueness, support of the polynomial equilibrium measure, algebraic-function finite branching, and whether the monodromy loop lies in the same analytic-continuation component as the original germ.

### Source gates (a)--(d)

(a) **Capacity/equilibrium uniqueness confirmed.** For a compact nonpolar plane set, the equilibrium measure is unique. Ransford is the intended citation; an accessible parallel source is the Saarland potential-theory notes, Remark VII.7, which state uniqueness for compact nonpolar `K`, and Theorem VII.10 identifies capacity with the equilibrium energy. Since every quadratic filled Julia set has capacity `1`, the energy value is `0` in the convention of this card.

(b) **Support confirmed for the dynamical equilibrium measure.** For a polynomial, the potential-theoretic equilibrium measure of the filled Julia set is Brolin's canonical/maximal-entropy measure. Petersen--Uhre recall this explicitly: for a polynomial `P`, the Green function vanishes precisely on `K_P`, `Cap(K_P)=|gamma|^{-1/(d-1)}`, and Brolin identifies the equilibrium measure with the maximal-entropy measure. They then use `omega_n` as the equilibrium measure for `K_n` with support `J_n`. Bridy--Larson also recall that the support of the invariant measure is precisely the Julia set. For `c notin M`, `K_c=J_c` is a Cantor set, so `supp(mu_c)=J_c=K_c`.

(c) **Bottcher injectivity accepted.** The Laurent coefficient argument is sufficient: equality of `K_c` gives equality of the normalized exterior Riemann map, and the coefficient `c/(2z)` recovers `c`.

(d) **Transcendence accepted after Wheeler's correction.** The earlier graph-dimension argument was false. The corrected finite-branching argument works: algebraic functions over `C(z)` have finitely many branch points, while disconnected quadratic inverse Bottcher coordinates have infinitely many branch points `f_c^{-n}(0)` with monodromy of order `2^n`.

### Added gate (e): same continuation component

The proof text says the relation continues everywhere in `{G_{c1}>0} cap {G_{c2}>0}`. What is actually needed is that the selected branch point `p` lies in the same path component as the original germ near infinity after avoiding the discrete branch loci.

This is not automatic for an arbitrary pair of compact sets. It closes here because for `c_i notin M`, each `K_{c_i}` is a Cantor compactum, hence zero-dimensional. A finite union of compact zero-dimensional sets is zero-dimensional, and a compact zero-dimensional subset of the plane does not separate the plane. Therefore

`C \ (K_{c1} union K_{c2}) = {G_{c1}>0} cap {G_{c2}>0}`

is connected, hence path-connected because it is open in `C`. Removing the countable discrete branch loci still leaves enough paths from the exterior germ to a punctured neighborhood of any chosen branch point `p` in this domain. Thus the algebraic relation can be analytically continued to the monodromy loop used in the proof.

With (e) inserted, the close-pair proof no longer depends on the false crossing lemma or on finite Laurent truncations. The remaining text should be tightened before promotion: replace the phrase "continues to hold everywhere" by "continues along any path in the exterior component of `C \ (K_{c1} union K_{c2})` avoiding the discrete branch loci; this exterior component is the whole complement by the zero-dimensional separation fact."

### Audit verdict

Correct after adding gate (e). The theorem proved is:

For `c1 != c2`, both outside the Mandelbrot set, the inverse Bottcher coordinates `phi_{c1}` and `phi_{c2}` are algebraically independent over `C(z)` (hence over `Qbar(c1,c2,z)`).

Grade: candidate `2-fully-proven` after team accepts the added topology gate. This is significant for Nguyen Q6.2, but it is a cross-method Böttcher theorem rather than a new native apex theorem about the archimedean-prime weld.

## 2026-06-24 Haiku topology-gate source closure

The continuation-component gate (e) is source-backed by the classical Mazurkiewicz theorem. A convenient modern reference is Krupski--Valov, `Mazurkiewicz manifolds and homogeneity`, arXiv:0901.1329: the introduction recalls that Mazurkiewicz proved regions, i.e. open connected subsets of Euclidean spaces and topological manifolds, cannot be cut by subsets of codimension at least two; their Theorem 4 strengthens this to suitable `F_sigma` subsets.

For this card the ambient region is the planar domain containing the infinity germ after removing the Cantor filled Julia sets. The removed obstruction set is a finite union of compact zero-dimensional sets plus countably many isolated branch points, hence an `F_sigma` set of covering dimension `0`. In a planar region, codimension is at least two. Therefore it cannot cut the region; in particular the needed path from the infinity germ to a punctured neighborhood of the chosen branch point exists after avoiding the branch loci.

This closes the extra topology gate named in the previous audit. Remaining promotion condition is now team acceptance / source-newness judgment, not a proof gap in the continuation path.

### Path refinement for analytic continuation

Mazurkiewicz supplies a continuum in the complement rather than explicitly naming a path. This is enough for analytic continuation. Given two small closed disks around the start and target basepoints inside the open continuation domain, apply the no-cut theorem to obtain a continuum `C` in the complement meeting both disks. Since `C` is compact and lies in an open plane domain, cover it by finitely many disks whose closures remain in the domain. Refining to a connected finite subcover gives a chain of overlapping disks from the start disk to the target disk. Joining points inside consecutive overlaps gives a polygonal path contained in the union of those disks. Thus the usual path-based analytic continuation and monodromy argument applies.

## 2026-06-24 monodromy audit — previous close-pair proof demoted

This supersedes the earlier “PROOF COMPLETE” language for the disconnected monodromy argument. The claim that
a small loop around `p in f_c^{-n}(0)` gives Böttcher monodromy `exp(2*pi*i/2^n)` is not justified for the
coordinate convention used here, namely `phi_c(f_c(z))=phi_c(z)^2`. Locally at a basin precritical point,
`phi_c` can be represented branchwise as a root of a nonzero analytic function, so a sufficiently small loop
around `p` may have trivial winding and need not change the branch by a root of unity.

What may still be true, and is the correct repair target, is a component-loop statement: a loop around a
suitable depth-`n` Cantor/puzzle component of `K_c` should have log-Böttcher period `2*pi*i/2^n`, hence
multiply `phi_c` by `exp(2*pi*i/2^n)`. That statement concerns the basin's nontrivial topology around removed
Julia components, not a local branch point at the escaping precritical point.

Current status: **OPEN at monodromy gate** for both distant and close disconnected-pair regimes until this
component-loop dyadic-period lemma is proved or sourced. The capacity lemma and zero-dimensional continuation
gate are retained as useful infrastructure, but they do not by themselves supply the degree contradiction.

## 2026-06-24 repair candidate — harmonic-measure period loop

A plausible repair of the disconnected monodromy gate is the following component-loop lemma.

**Lemma candidate.** Let `c notin M`, let `phi_c` be the Böttcher coordinate germ satisfying
`phi_c(f_c(z))=phi_c(z)^2`, and let `C_w` be a depth-`n` symbolic cylinder in the Cantor Julia set `K_c`.
A loop `gamma in Omega_c=C\K_c` enclosing `C_w` and no other depth-`n` cylinder analytically continues
`phi_c` to `exp(2*pi*i/2^n) phi_c`.

Reason: locally `log phi_c = G_c+iG_c^*`. The period of `d(log phi_c)` around `gamma` is `2*pi*i` times the
harmonic measure at infinity of the enclosed clopen boundary piece. For a quadratic shift-locus map,
harmonic measure is Brolin/maximal-entropy measure, and each depth-`n` symbolic cylinder has mass `2^-n`.
Thus the period is `2*pi*i/2^n`.

If accepted, this replaces the invalid small-precritical-loop wording. For `c1 != c2` outside `M`, the capacity
lemma gives a point of `K_c1\K_c2`; choose a disk `D subset Omega_c2` around it and then a depth-`n` cylinder
`C_w subset K_c1 cap D` with `2^n` larger than the relevant polynomial degree. A loop around `C_w`, reached
from the infinity germ through `(C\K_c1) cap (C\K_c2)` using the zero-dimensional non-cutting gate, gives
nontrivial monodromy for `phi_c1` and no monodromy for `phi_c2`. The same degree contradiction then goes
through.

Status: **candidate repair, pending audit of the period/harmonic-measure lemma and reachability details.**

## 2026-06-24 period lemma proved — disconnected proof repaired pending team audit

The repair candidate above is valid after replacing the invalid local precritical-loop claim by a complex-potential period calculation.

### Component-loop period lemma

Let `c notin M`, so `K_c=J_c` is a Cantor set and `Omega_c=C\K_c` is the basin of infinity. Let `mu_c` be the equilibrium measure of `K_c`. For a depth-`n` symbolic cylinder `C_w subset K_c`, choose a closed curve, or a finite product of closed curves based at the same point, in `Omega_c` whose winding number is `1` on `C_w` and `0` on `K_c\C_w`. Such a separating curve exists because `C_w` is clopen in the zero-dimensional compactum `K_c`: take a finite open neighborhood of `C_w` with closure disjoint from `K_c\C_w` and use its oriented boundary.

The complex Green potential gives the local logarithm of the normalized Böttcher coordinate near infinity:

`log phi_c(z) = int log(z-zeta) dmu_c(zeta)`,

with the branch normalized by `phi_c(z)/z -> 1`. Hence on `Omega_c`

`d log phi_c = int dz/(z-zeta) dmu_c(zeta)`.

For the separating curve `gamma`, Fubini plus the argument principle gives

`int_gamma d log phi_c
 = int_K (int_gamma dz/(z-zeta)) dmu_c(zeta)
 = 2*pi*i int_K Ind(gamma,zeta) dmu_c(zeta)
 = 2*pi*i mu_c(C_w)`.

Since `c` is in the quadratic shift locus, `f_c|K_c` is conjugate to the full one-sided two-shift. The Brolin-Lyubich measure is the equilibrium/harmonic measure of the basin of infinity and the maximal-entropy measure; in this coding it is the fair Bernoulli measure. Thus `mu_c(C_w)=2^-n`, and continuation around `gamma` sends

`phi_c -> exp(2*pi*i/2^n) phi_c`.

This is the dyadic monodromy needed for the degree argument. The earlier proof's small loop around a point of `f_c^{-n}(0)` remains rejected.

### Repaired both-disconnected proof

For `c1 != c2` outside `M`, the capacity/equilibrium argument gives `K_c1 notsubset K_c2`; choose `z0 in K_c1\K_c2` and a disk `D subset Omega_c2` around `z0`. For arbitrarily large `n`, choose a depth-`n` cylinder `C_w subset K_c1 cap D`.

A separating component-loop for `C_w` can be chosen in `D\K_c1`, hence in `Omega_c1 cap Omega_c2`. The zero-dimensional non-cutting gate gives a path from the infinity germ to the loop basepoint in `Omega_c1 cap Omega_c2`. Along this loop, the period lemma gives nontrivial dyadic monodromy for `phi_c1`. Because the loop lies in `D subset Omega_c2` and winds around no part of `K_c2`, the same period calculation gives zero period for `phi_c2`; it is unchanged.

Taking `2^n > deg_Y P`, the old degree contradiction is now valid with the depth-`n` cylinder loop replacing the invalid precritical-point loop. If all coefficients then vanish after substituting `phi_c2`, Becker--Bergweiler's nonalgebraicity of the nonexceptional Böttcher coordinate, or the same unbounded cylinder-monodromy argument, forces the coefficients to be zero.

Current status: **proof repaired as a theorem candidate; pending independent team audit/source-newness vote before moving to `2-fully-proven`.**

### Source-newness note after period repair

Narrow source search for Nguyen Q6.2 / inverse-Böttcher algebraic independence still surfaces Nguyen's question itself and adjacent value/small-orbit literature, not a theorem proving this function-field relation for distinct quadratic parameters.

Relevant support, not a source-kill: Harry Schmidt, `Polynomial dynamics and local analysis of small and grand orbits`, Compositio Mathematica 159 (2023), §6 studies monodromy for disconnected Julia sets and proves that continuations of the inverse Böttcher uniformization have high-order root-of-unity monodromy. This independently confirms that the disconnected case is controlled by monodromy, but Schmidt's statements concern relations on one polynomial's small/grand-orbit uniformization, not the relation `P(z,phi_c1(z),phi_c2(z))=0` between two parameter fibers.

Thus the repair is source-supported and still appears source-new for Nguyen Q6.2 n=2, pending team audit.

## 2026-06-24 local-vs-topological monodromy correction

Further correction: for the direct Böttcher coordinate convention used in these cards,

`phi_c(f_c(z))=phi_c(z)^2`, `phi_c(z)/z -> 1`,

escaping precritical points in `Omega_c` should not be treated as the load-bearing local branch points of `phi_c`. Locally near such a point, a branch can be represented as a root of a nonzero analytic function, so the branch is locally analytic after a choice of root. The relevant multivaluedness is period/topology-based: `d log phi_c` is a single-valued holomorphic differential on `Omega_c` whose periods around removed Julia-set pieces are nonzero.

Thus the maintained proof is the component-loop proof only. Any earlier sentence saying that a small loop around `f_c^{-n}(0)` gives the required monodromy is retired, except as source-history of the failed attempt.

## 2026-06-24 PROMOTED to 2-fully-proven

Both-disconnected and mixed cases proved (Wheeler id=1843, Haiku id=1834 period lemma sourced).
See: docs/drafts/pipeline/2-fully-proven/q62-both-disconnected.md
