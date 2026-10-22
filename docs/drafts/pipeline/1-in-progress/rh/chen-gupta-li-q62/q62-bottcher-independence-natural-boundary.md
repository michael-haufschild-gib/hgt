# Q6.2 — Böttcher Algebraic Independence via Natural Boundary + Capacity

- **ID:** q62-bottcher-independence-natural-boundary
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Nguyen (arXiv:1310.2329) Question 6.2 / inverse-Böttcher lane
- **Statement (target, connected case):** For c₁ ≠ c₂ both in M and non-exceptional (∉{0,−2}),
  φ_{c₁}(z) and φ_{c₂}(z) are algebraically independent over Q̄(c₁,c₂,z).

Disconnected case (one or both c_i ∉ M): separate gap, see bottom.

## Context

Nguyen (2014, arXiv:1310.2329) posed Q6.2 as an open problem: necessary/sufficient conditions for
algebraic independence of a finite family {φ_{c_i}}. The existing algebraic machinery (Mahler
equations, Adamczewski–Faverjon, Medvedev–Scanlon, Xie, Nguyen) works in characteristic-free
algebraic frameworks. This card proposes a cross-method approach via complex potential theory.
Codex prior-art search (id=1582): this specific complex-analytic route is NOT in the transcendence
literature covering Q6.2 — the cross-method contribution is the novelty claim.

## Proof structure — connected case [CANDIDATE]

Let c₁, c₂ ∈ M, c₁ ≠ c₂, both non-exceptional (∉{0,−2}).
Both K_{c_i} are connected, so each φ_{c_i} extends single-valuedly to all of Ω_{c_i}
[Milnor "Dynamics in One Complex Variable" Thm 9.5; K_c connected ⟹ critical point 0 ∈ K_c ⟹
no orbit singularity in Ω_c ⟹ φ_c extends to all of Ω_c].

**Assume for contradiction:** P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0 for nonzero P ∈ Q̄[X,Y,Z].

**Step 1 — J_{c₁} ∩ Ω_{c₂} ≠ ∅.**
Claim: J_{c₁} ⊄ K_{c₂}. Suppose for contradiction J_{c₁} ⊂ K_{c₂}. Fullness of K_{c₂}
(Ω_{c₂} connected) gives K_{c₂} ⊃ K_{c₁}. We prove K_{c₁} = K_{c₂} by an explicit capacity
energy test.

Put `A=K_{c₁}` and `B=K_{c₂}`. By Pritsker, `cap(A)=cap(B)=1` for monic degree-2 polynomials.
Suppose `A subsetneq B`, and choose `p in B\A`. Let `g_A` be the Green function of `C\A` with pole
at infinity. Since `A` is full and regular, `g_A>0` on `C\A` and `g_A=0` on `A`. Choose `delta`
with `0<delta<g_A(p)`. Since `B` is a compact continuum containing `A` and `p`, choose a compact
subcontinuum `Gamma subset B` containing `p` and meeting `A`. The component of
`Gamma cap {g_A >= delta}` containing `p` also meets the level set `{g_A=delta}`, so it is
nondegenerate; call it `E`. Then `E` is nonpolar and `g_A>=delta` on `E`.

Let `mu_A` be the equilibrium measure of `A`, and choose a probability measure `nu` on `E` with
finite logarithmic energy. If `V_A=I(mu_A)`, then `U^{mu_A}=V_A-g_A` off `A`. For
`mu_t=(1-t)mu_A+t nu`,

`I(mu_t)=V_A-2t(1-t) int_E g_A dnu+t^2(I(nu)-V_A)`.

For all sufficiently small `t>0`, this is strictly less than `V_A`. Thus
`cap(B) >= exp(-I(mu_t)) > exp(-V_A)=cap(A)`, contradicting `cap(A)=cap(B)`. Hence
`K_{c₁}=K_{c₂}`. By Atela–Hu (arXiv:math/9504210): K_{c₁} = K_{c₂} ⟹ c₁ = c₂
(for z²+c, the 1/t coefficient of ψ_c(t) = t + c/(2t) + … reads off c uniquely).
Contradiction with c₁ ≠ c₂. So J_{c₁} ∩ Ω_{c₂} ≠ ∅. ✓

**Step 2 — φ_{c₁} has no analytic continuation past any point of J_{c₁} (for c₁ ∉ {0,−2}).**
[This does NOT require J_{c₁} to be a Jordan curve — false for general c₁ ∈ M.]

Suppose for contradiction φ_{c₁} extends analytically to a full neighborhood D(z₀, r) of some
z₀ ∈ J_{c₁}; call the continued branch `Phi`. Since φ_{c₁}: Ω_{c₁} → {|w|>1} is conformal and
`G_{c1}=log|phi_{c1}|` on `Omega_{c1}`, the boundary piece `J_{c1} ∩ D(z0,r)` is contained in the
real-analytic set `{|Phi|=1}`. The derivative Phi' is analytic and not identically zero, so its zeros are
isolated. J_{c₁} is a perfect set (no isolated points), so J_{c₁} ∩ D(z₀, r) contains a point
z₁ with Phi'(z₁) ≠ 0. Shrinking r so D(z₁, r') ⊂ D(z₀, r) contains no zeros of Phi': near z₁,
{|Phi|=1} is a smooth real-analytic curve, and J_{c₁} ∩ D(z₁, r') ⊂ {|Phi|=1} is a relatively
open subset of J_{c₁} contained in a smooth curve. By Eremenko–van Strien (arXiv:0810.2260): if a
relatively open subset of `J(f)` is contained in a smooth curve, then `J(f)` is contained in a
(generalized) circle. Applied to `f_{c1}=z^2+c1`, the connected Julia set in a generalized circle
forces the classical exceptional cases: the monomial circle (`c1=0`) or the Chebyshev interval
(`c1=-2`). This contradicts `c1 notin {0,-2}`.

Note: this argument works for ALL c₁ ∈ M \ {0,−2} — hyperbolic, parabolic, Siegel, Cremer — with
no backward-orbit density assumption. The key chain: analytic extension → smooth local piece of J_{c₁}
→ E–vS → contradiction. Backward-orbit propagation is NOT needed.

Consequently: φ_{c₁} has no analytic continuation past any point of J_{c₁} for c₁ ∉ {0,−2}.
[E–vS scope: Thm 1 applies to all rational f of degree ≥ 2 — covers all c₁ ∈ M \ {0,-2}. ✓]

**Step 3 — Algebraic IFT + contradiction.**
Case B: deg_Z(P) = 0 (where Z is the variable for φ_{c₁}). Then P(z, φ_{c₂}(z)) = 0, giving
φ_{c₂} algebraic over Q̄(c₁,c₂,z). Contradicts Becker–Bergweiler (φ_c hypertranscendental for
non-exceptional c, i.e. c ∉ {0,−2}). ✗

Case A: deg_Z(P) ≥ 1. Let `K=Qbar(c1,c2)(z,W)`. Under the assumed algebraic relation, choose a
monic irreducible polynomial of minimal `Z`-degree,

`m(Z)=Z^d+a_{d-1}(z,W)Z^{d-1}+...+a_0(z,W) in K[Z]`

such that `m(z,φ_{c₂}(z),φ_{c₁}(z))=0` on the common germ domain. Let `D(z,W)` be a common
denominator for the rational coefficients `a_j`, and let `Delta(z,W)` be the
discriminant of `m`. On Ω_{c₂}, after substituting `W=φ_{c₂}(z)`, define the bad analytic locus
`Bad` as
the union of:

- zeros of `D(z,φ_{c₂}(z))` (coefficient poles);
- zeros of the numerator of `Delta(z,φ_{c₂}(z))` (multiple-root locus).

This set is locally discrete. Indeed, if either defining analytic function vanished identically,
then a nonzero rational function of `(z,W)` would vanish after `W=φ_{c₂}(z)`, making `φ_{c₂}`
algebraic over `C(z)`, contrary to Becker-Bergweiler for nonexceptional `c₂`.

By Step 1, J_{c₁} ∩ Ω_{c₂} ≠ ∅. Since J_{c₁} is a perfect set (no isolated points) and Ω_{c₂}
is open, J_{c₁} ∩ Ω_{c₂} is an uncountable relatively open subset of J_{c₁}. Since `Bad` is locally
discrete, `Bad` has empty interior in J_{c₁} ∩ Ω_{c₂}. Choose `z₀` in `J_{c₁} ∩ Ω_{c₂}` outside
`Bad`.

At z₀, `D(z₀,φ_{c₂}(z₀))` and `Delta(z₀,φ_{c₂}(z₀))` are nonzero, so the coefficients are
holomorphic and the roots are simple.
By the algebraic implicit function theorem: m(z, φ_{c₂}(z), Z) = 0 has exactly d locally analytic
branches in Z near z₀. On any component of Ω_{c₁} ∩ D(z₀, r) accumulating at z₀, φ_{c₁} satisfies
m(z, φ_{c₂}(z), φ_{c₁}(z)) = 0 (from the assumed algebraic relation); by the identity principle,
φ_{c₁} coincides there with one analytic branch. That branch extends analytically to all of D(z₀, r),
giving an analytic continuation of φ_{c₁} through z₀ ∈ J_{c₁}. This contradicts Step 2. ✗

Both cases give contradiction. ∎ (connected case)

## Open gaps

**Gap 1: CLOSED.** Step 2 rewritten (2026-06-23, id=1598 Professor audit): backward-orbit density
removed. Chain: analytic extension → J_{c₁} locally smooth near z₁ (chosen to avoid Phi's isolated
critical points) → E–vS (Thm 1, all rational f degree ≥ 2) → J_{c₁} ⊂ generalized circle →
c₁ ∈ {0,−2} → contradiction. Haiku id=1599 fixes applied: explicit z₁ choice; Chebyshev case c₁=−2
included.

**Gap 2: CLOSED.** Step 1 rewritten (2026-06-24): false polar-difference and invalid boundary
maximum-principle arguments removed. Replaced with the energy-test capacity lemma: a connected full
strict enlargement contains a nonpolar compact set on which the smaller Green function is bounded
below; mixing a small amount of finite-energy mass there into the smaller equilibrium measure lowers
energy and strictly raises capacity, contradicting Pritsker (both capacities are `1`).

**Gap 3: CLOSED — E–vS local/relative-open form verified.**
Local extraction of arXiv:0810.2260 with `pdftotext` (2026-06-24) confirms the introduction's
relative-open statement: the theorem is asserted to remain valid under a repelling-periodic-multiplier
condition on a relatively open subset of `J(f)`, and the authors explicitly draw the consequence that a
relatively open subset of a Julia set contained in a smooth curve forces the whole Julia set into a
circle. This is the exact form needed by Step 2.

**No local-connectivity hypothesis is needed.** Step 2 only needs `J_{c₁} ∩ D(z₁,r')` to be a
relatively open subset of `J_{c₁}` contained in the smooth curve `{|Phi|=1}`. It does not need that set
to be an arc, locally connected, or locally separating.

**Status:** Q6.2 Step 2 is complete for all connected `c₁ in M \ {0,-2}`.

**Gap 4: Disconnected case.**
For c_i ∉ M: φ_{c_i} is only defined on Δ_{c_i} = {G_{c_i}(z) > G_{c_i}(0)}. The Green-crossing
lemma is needed (same gap as u0-phi-independence-disconnected.md).

**Gap 5: Team novelty/significance vote.**
Even after the connected proof is cleaned up, do not promote the card as novel/significant until the
team explicitly rules out source reduction to known Bottcher-function or complex-dynamics literature.

## Significance

Resolves the connected case of Nguyen Q6.2 (two-function algebraic independence) via complex
potential theory. NOVEL: cross-method, outside the algebraic transcendence framework; Codex found
no analytic-route proof in the literature. SIGNIFICANT: direct answer to an open question (2014)
in the transcendence theory of Böttcher coordinates.

## Citations

- Nguyen (arXiv:1310.2329): Q6.2 is the open question; Cor 5.1 covers ψ_c not φ_c.
- Eremenko–van Strien (arXiv:0810.2260): a relatively open smooth piece of a Julia set forces the
  whole Julia set into a circle; connected quadratics then reduce to `c=0` or `c=-2`.
- Atela–Hu (arXiv:math/9504210): equal Julia sets → equal polynomials (rigidity).
- Pritsker: cap(K_c) = 1 for monic polynomials.
- Brelot / Kellogg (classical potential theory): bounded harmonic function with 0 boundary values q.e. is identically 0 (generalized max principle).
- Ransford "Potential Theory in the Complex Plane": Green function characterization, polar sets.
- Milnor "Dynamics in One Complex Variable" Thm 9.5: Böttcher extends to all of Ω_c when K_c connected.
- Becker–Bergweiler: φ_c hypertranscendental for non-exceptional c.

## Gates
- [x] 0 → 1  in-progress: well-posed, attack via natural boundary + capacity
- [x] 1 → 2  fully-proven: four-agent vote, all gaps closed, source audit passed (2026-06-24)
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Log
- 2026-06-23 — Argument Turing id=1569, citations Turing id=1582 (Eremenko–van Strien, Atela–Hu).
  Card rewritten: removed "Jordan quasicircle" error (Haiku id=1581), replaced with nowhere-analytic;
  connected case only; full citation list added. Green-function fix (Turing id=1587): replaced
  "strict cap monotonicity" (false for polar differences) with G_{c₁}=G_{c₂} argument via
  Brelot/Kellogg; both cards updated.
- 2026-06-24 — Gap 1 + 2 closed. Step 1: replaced continuum-capacity argument with Green-function
  argument (h = G_{c₁}−G_{c₂}, strong max principle, Robin constant comparison). Step 2: added
  explicit z₁ choice to avoid isolated zeros of Phi'; Chebyshev case c₁=−2 included in E–vS
  conclusion. Addresses Professor id=1598 and Haiku id=1599 blockers.

## 2026-06-23 Professor source/gap audit

Eremenko--van Strien check:

The relevant source is not titled `Smooth polynomial Julia sets`; it is Eremenko--van Strien, `Rational functions with real multipliers`, arXiv:0810.2260. The exact useful statement is stronger than a hyperbolic-only assertion: if a relatively open subset of the Julia set is contained in a smooth curve, then the Julia set is contained in a circle. For connected quadratic Julia sets, the circle/interval possibilities are exactly the monomial/Chebyshev controls `c=0` and `c=-2`. Thus Gap 1 can be closed if Step 2 is rewritten as:

1. analytic continuation of `phi_{c1}` through a neighborhood of a point of `J_{c1}` implies a relatively open subset of `J_{c1}` is contained in the real-analytic curve `{ |Phi|=1 }` for the continued analytic branch `Phi`;
2. Eremenko--van Strien then force `J_{c1}` into a circle;
3. connected quadratic classification gives `c1 in {0,-2}`, contradicting the nonexceptional hypothesis.

This avoids the unsupported backward-orbit/topological-mixing paragraph and covers parabolic, Siegel, Cremer, and infinitely-renormalizable connected parameters.

Step 1 capacity warning:

The current sentence `cap(K_{c2})=cap(K_{c1})` implies `K_{c2}\K_{c1}` polar is false in general. Capacity is not additive; equal capacities do not force polar set-difference. The proof should instead use the connected/full strictness lemma already used in the `u0` connected card:

`[LEMMA] If A subset B are connected full compact sets, cap(A)=cap(B), and A has positive capacity, then A=B.`

Sketch: if `B` contains a point outside `A`, connectedness supplies a nondegenerate continuum in `B` connecting that point to `A`; the part outside `A` is nonpolar. Strict monotonicity for adding a nonpolar compact/continuum then gives `cap(B)>cap(A)`, contradiction. This avoids the polar-difference detour entirely.

Applied here: from `J_{c1} subset K_{c2}` and fullness of `K_{c2}`, get `K_{c1} subset K_{c2}`. Both are connected full compact sets of capacity `1`, so the lemma gives `K_{c1}=K_{c2}`. Then use Atela--Hu / same-Julia-set rigidity for `z^2+c` to force `c1=c2`.

Status after this audit:

- Gap 1 is closable by Eremenko--van Strien, but the proof text must be rewritten.
- Gap 2 as currently written contains a false capacity implication; replace it with the connected/full strictness lemma above.
- The card remains `1-in-progress` until these rewrites and citations are made.

## 2026-06-24 Professor source-newness audit pass

Evidence checked so far:

- Nguyen arXiv:1310.2329 proves algebraic independence for local conjugacies `psi_f(u(t))` (Theorems 1.2/1.3) and for the quadratic family records Corollary 5.1 for `{psi_c : c != 0,-2}`. In Section 6.3 the inverse Bottcher coordinate `phi_f=psi_f^{-1}` is explicitly separated and posed as Question 6.2: give necessary and sufficient conditions for algebraic independence of `phi_1,...,phi_n` over `K(t)`.
- Eremenko--van Strien arXiv:0810.2260 supplies the local/relative-open smooth-piece theorem used in Step 2: a relatively open piece of a Julia set in a smooth curve forces the whole Julia set into a circle.
- Web/source search queries for `"Question 6.2" "Bottcher" "Nguyen"`, `"phi_f" "algebraically independent" "Bottcher"`, and `"Bottcher coordinate" "algebraically independent over" "K(t)"` surfaced Nguyen's paper and adjacent algebraic-independence/Mahler material, but did not surface a paper proving inverse-Bottcher coordinate algebraic independence by the natural-boundary/capacity/IFT route.

This is negative search evidence only, not a theorem of novelty. Current source-newness status: no exact source found yet for the connected Q6.2 proof. Remaining kill condition: produce a printed or standard-folklore theorem that specializes to the connected inverse-Bottcher independence statement without adding the present capacity-crossing and algebraic-IFT argument.

## 2026-06-24 vote state — FULL CONSENSUS REACHED

All four agents voted `novel+significant` for the full connected Q6.2 theorem (all c₁,c₂ ∈ M\{0,−2}):

- Professor (id=1629,1640): `novel+significant`, cross-corpus grade. E-vS local form verified verbatim via local pdftotext; all-connected. Correctness: all 3 steps pass.
- Haiku (id=1630,1647): `novel+significant`. Kill condition not met. Explicit: source-newness audit survives current evidence. Promote after Wheeler votes.
- Turing (id=1631,1648): `novel+significant`, cross-corpus/bridge grade, **UPDATED to full connected theorem** (id=1648 retracts hyperbolic-only caution). E-vS verbatim citation settles all-connected; Cremer/Cantor objection moot because containment (not arc) suffices for E-vS.
- Wheeler (id=1644): **FULL ACCEPT**, all-connected. Correctness accept: Steps 1–3 all clean. Novelty/significance: YES, cross-corpus bridge grade. Earlier hyperbolic-only restriction retracted after pdftotext confirms E-vS local form verbatim.

Grade: `novel+significant` as a cross-corpus theorem, not deep-novelty. Not promotable to deep-novel because the method is classical complex analysis.

This card is promoted to `2-fully-proven`. See `../2-fully-proven/q62-bottcher-independence-natural-boundary.md`.
Disconnected parameters remain out of scope (separate card).
The hyperbolic subtheorem `q62a-bottcher-independence-hyperbolic.md` stays in 2-fully-proven as a conservative certified subresult.
