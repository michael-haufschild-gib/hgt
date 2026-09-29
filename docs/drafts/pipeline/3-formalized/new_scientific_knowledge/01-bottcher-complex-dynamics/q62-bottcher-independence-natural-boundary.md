# Q6.2 — Böttcher Algebraic Independence (Connected Case)

- **ID:** q62-bottcher-independence-natural-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Nguyen arXiv:1310.2329 Question 6.2 / inverse-Böttcher lane
- **Statement:** For c₁ ≠ c₂ both in M \ {0,−2}, the inverse Böttcher coordinates φ_{c₁}(z)
  and φ_{c₂}(z) are algebraically independent over Q̄(c₁,c₂,z).

Disconnected parameters (c_i ∉ M): separate open card. Hyperbolic subtheorem: q62a-bottcher-independence-hyperbolic.md.

## Goal

Resolve Nguyen Question 6.2 for the full connected nonexceptional parameter locus, using complex
potential theory rather than the algebraic/Mahler machinery of the source paper. Nguyen proves
algebraic independence for the local conjugacies ψ_c(u(t)) (Cor 5.1) and explicitly separates
the inverse Böttcher coordinate φ_c = ψ_c⁻¹, asking for necessary and sufficient conditions for
algebraic independence of the φ_i. No existing source was found resolving this function-field
relation by the natural-boundary/capacity/algebraic-IFT route.

## Proof

Let c₁, c₂ ∈ M, c₁ ≠ c₂, both ∉ {0,−2}. Write K_i = K_{c_i} for filled Julia sets,
J_i = ∂K_i for Julia sets, Ω_i = ℂ \ K_i for basins of infinity. Since c_i ∈ M the filled Julia
set K_i is connected; the unique finite critical point 0 lies in K_i; so φ_{c_i} extends
single-valuedly to all of Ω_i (Milnor, Dynamics in One Complex Variable, Thm 9.5).

**Assume for contradiction:** P(z, φ_{c₁}(z), φ_{c₂}(z)) = 0 for nonzero P ∈ Q̄(c₁,c₂)[z,Y,Z].

### Step 1 — J_{c₁} ∩ Ω_{c₂} ≠ ∅

Suppose J_{c₁} ⊂ K_{c₂}. Since K_{c₂} is full (Ω_{c₂} connected), K_{c₁} ⊂ K_{c₂}.

Both K_{c_i} are connected full compact sets of logarithmic capacity 1 (Pritsker; monic
degree-2 polynomials). Suppose K_{c₁} ⊊ K_{c₂}; choose p ∈ K_{c₂} \ K_{c₁}. Let g_A be the
Green function of ℂ \ K_{c₁} with pole at ∞; g_A > 0 on ℂ \ K_{c₁}, g_A = 0 on K_{c₁}.
Choose δ with 0 < δ < g_A(p). Since K_{c₂} is a compact continuum containing K_{c₁} and p,
choose a compact subcontinuum Γ ⊂ K_{c₂} containing p and meeting K_{c₁}. The component of
Γ ∩ {g_A ≥ δ} containing p is nondegenerate; call it E. Then E is nonpolar and g_A ≥ δ on E.

Let μ_A = equilibrium measure of K_{c₁}, ν = finite-energy probability measure on E,
V_A = I(μ_A). For μ_t = (1−t)μ_A + tν:

I(μ_t) = V_A − 2t(1−t)∫_E g_A dν + t²(I(ν) − V_A).

Since ∫_E g_A dν ≥ δ > 0, we have I(μ_t) < V_A for all small t > 0. Thus
cap(K_{c₂}) ≥ exp(−I(μ_t)) > exp(−V_A) = cap(K_{c₁}) = 1, contradicting cap(K_{c₂}) = 1.

Hence K_{c₁} = K_{c₂}. By Atela–Hu (arXiv:math/9504210): equal filled Julia sets in the
quadratic family z² + c force c₁ = c₂ (the 1/t coefficient of ψ_c(t) uniquely reads off c).
Contradiction. So J_{c₁} ∩ Ω_{c₂} ≠ ∅. ✓

### Step 2 — φ_{c₁} has no analytic continuation past any point of J_{c₁}

Suppose φ_{c₁} extends analytically to a disk D(z₀, r) with z₀ ∈ J_{c₁}; call the branch Φ.
Since G_{c₁} = log|φ_{c₁}| on Ω_{c₁} and G_{c₁} = 0 on J_{c₁}, the set J_{c₁} ∩ D(z₀,r) lies
in {|Φ| = 1}, a real-analytic curve.

Φ' is analytic and not identically zero, so its zeros are isolated. J_{c₁} is a perfect set
(no isolated points), so J_{c₁} ∩ D(z₀,r) contains a point z₁ with Φ'(z₁) ≠ 0. Shrink to
D(z₁,r') with no zeros of Φ': near z₁, {|Φ| = 1} is a smooth real-analytic curve, and
J_{c₁} ∩ D(z₁,r') is a relatively open subset of J_{c₁} contained in a smooth curve.

By Eremenko–van Strien (arXiv:0810.2260, introduction after Corollary 1, verbatim):
"It follows that even if a relatively open set of the Julia set is contained in a smooth
curve, then the Julia set is contained in a circle."

Applied to f_{c₁} = z² + c₁: J_{c₁} ⊂ circle forces the classical exceptional cases c₁ = 0
(monomial, J = unit circle) or c₁ = −2 (Chebyshev, J = interval [−2,2]). This contradicts
c₁ ∉ {0,−2}.

Note: the E–vS argument uses containment in a smooth curve, not arc topology. No local
connectivity hypothesis on J_{c₁} is needed. The statement holds for hyperbolic, parabolic,
Siegel, Cremer, and infinitely-renormalizable parameters alike. ✓

### Step 3 — Algebraic relation forces forbidden continuation

**Case B (deg_Z P = 0):** P(z, φ_{c₂}(z)) = 0, making φ_{c₂} algebraic over Q̄(c₁,c₂,z).
Contradicts Becker–Bergweiler (φ_c hypertranscendental for non-exceptional c). ✗

**Case A (deg_Z P ≥ 1):** Let K = Q̄(c₁,c₂)(z,W). Choose a monic irreducible polynomial of
minimal Z-degree over K:

m(Z) = Z^d + a_{d-1}(z,W)Z^{d-1} + … + a_0(z,W) ∈ K[Z]

with m(z, φ_{c₂}(z), φ_{c₁}(z)) = 0 on the germ domain. Let D(z,W) be a common denominator
for the rational coefficients a_j, and Δ(z,W) the discriminant of m. Define the bad locus Bad
as the union, in Ω_{c₂}, of:

- zeros of D(z, φ_{c₂}(z)) (coefficient poles);
- zeros of the numerator of Δ(z, φ_{c₂}(z)) (multiple-root locus).

Bad is locally discrete: if either defining function vanished identically, a nonzero rational
function of (z,W) would vanish after W = φ_{c₂}(z), making φ_{c₂} algebraic over ℂ(z),
contradicting Becker–Bergweiler for nonexceptional c₂.

By Step 1, J_{c₁} ∩ Ω_{c₂} ≠ ∅; since J_{c₁} is perfect and Ω_{c₂} is open, J_{c₁} ∩ Ω_{c₂}
is an uncountable relatively open subset of J_{c₁}. A locally discrete set has empty interior in
J_{c₁} ∩ Ω_{c₂}. Choose z₀ ∈ J_{c₁} ∩ Ω_{c₂} \ Bad.

At z₀: D(z₀, φ_{c₂}(z₀)) ≠ 0 and Δ(z₀, φ_{c₂}(z₀)) ≠ 0, so the coefficients are holomorphic
and the roots of m are simple. By the algebraic implicit function theorem, m(z, φ_{c₂}(z), Z) = 0
has exactly d locally analytic branches near z₀. On any component of Ω_{c₁} ∩ D(z₀,r)
accumulating at z₀, φ_{c₁} satisfies m(z, φ_{c₂}(z), φ_{c₁}(z)) = 0; by the identity principle,
φ_{c₁} coincides with one analytic branch near z₀. That branch extends analytically through
z₀ ∈ J_{c₁}, contradicting Step 2. ✗

Both cases yield contradiction. ∎

## Source Boundary

- Nguyen arXiv:1310.2329: proves the ψ_c(u(t)) conjugacy results; Question 6.2 explicitly separates inverse Böttcher coordinate φ_c = ψ_c⁻¹ as an open problem.
- Eremenko–van Strien arXiv:0810.2260: supplies the relative-open smooth-piece rigidity; verbatim text confirmed in introduction via pdftotext.
- Atela–Hu arXiv:math/9504210: equal filled Julia sets → equal polynomials (quadratic rigidity).
- Pritsker: cap(K_c) = 1 for monic polynomial Julia sets.
- Milnor, Dynamics in One Complex Variable, Thm 9.5: Böttcher extends to all of Ω_c when K_c connected.
- Becker–Bergweiler: φ_c hypertranscendental for non-exceptional c.

Source-newness audit (Professor id=1629, Haiku id=1630, Turing id=1631, codex web-search):
Targeted searches for "Question 6.2 Bottcher Nguyen", "phi_f algebraically independent Bottcher",
"Bottcher coordinate algebraically independent over K(t)" surfaced Nguyen and adjacent
Mahler/algebraic-independence material; no paper proving inverse-Böttcher coordinate algebraic
independence by the natural-boundary/capacity/IFT route was found. Kill condition: produce a
printed or standard-folklore theorem that specializes to this function-field relation for
distinct connected nonexceptional quadratic parameters without adding the current capacity-crossing
and algebraic-IFT argument. No such source was produced.

## Novelty / Significance Vote

Consensus grade: `novel+significant` as a **cross-corpus theorem**, not a deep-new-mathematics claim.

- Professor (id=1629, 1640): `novel+significant`, cross-corpus grade. Correctness: all 3 steps pass. Source audit passed.
- Haiku (id=1630, 1647): `novel+significant`. Kill condition not met. Correctness accepted.
- Turing (id=1631, 1648): `novel+significant`, cross-corpus/bridge grade. **Updated (id=1648) to full connected theorem** after E-vS verbatim citation settles all-connected; Cremer/Cantor objection resolved (E-vS needs containment, not arc topology).
- Wheeler (id=1644): **FULL ACCEPT**, all-connected. Correctness: all steps clean. Novelty: YES, cross-corpus bridge. Hyperbolic-only restriction retracted after pdftotext confirms E-vS local form verbatim.

Deep-novelty grade: LOWER. The method (potential theory + E–vS smooth-piece rigidity + algebraic IFT) is classical complex analysis; a complex-dynamicist familiar with Nguyen's question could in principle derive it. The result is novel as a bridge between algebraic transcendence and complex dynamics, not as new mathematics within either corpus.

Theatre test: the team's source audit is the kill gate. Failure mode would be to accept a "probably not in the literature" guess. The confirmed kill condition (exact printed source implying this relation without this argument) was not triggered.

## Gates

- [x] 0 → 1 in-progress: well-posed; target is Nguyen Q6.2 inverse-Böttcher independence.
- [x] 1 → 2 fully-proven: complete proof for all c₁,c₂ ∈ M \ {0,−2}; four-agent vote recorded (2026-06-24).
- [x] 2 → 3 formalized: `Bottcher.noRelation_phiMero_of_mem_mandelbrot` (2026-09-29).
- [ ] 3 → 4 publication-ready: standalone paper with full citations and formal proof plan.

## Log

- 2026-06-24 — Promoted from 1-in-progress after full consensus (four-agent explicit vote). Proof
  developed over two sessions: Step 1 energy test (Professor), Step 2 E-vS local form
  (Turing id=1569, Professor audit, E-vS verbatim confirmation by Wheeler pdftotext), Step 3 bad
  locus (Turing, Haiku cleanup). E-vS scope extends to all-connected (not just hyperbolic) because
  the theorem requires containment in a smooth curve, not arc topology or local connectivity.
  The hyperbolic subtheorem is also recorded separately in q62a-bottcher-independence-hyperbolic.md.

## 2026-07-02 Formalization audit — Step 3 gap found (identity-theorem propagation)

Formalization (Fable) surfaced a gap in Step 3 as written. The sentence "On any component of
Ω_{c₁} ∩ D(z₀, r) accumulating at z₀, φ_{c₁} satisfies m(z, φ_{c₂}(z), φ_{c₁}(z)) = 0 (from the
assumed algebraic relation)" is unjustified: the relation holds a priori on the common far-field
germ domain and propagates by the identity theorem only through the connected component **W** of
Ω_{c₁} ∩ Ω_{c₂} containing the far field. Components of Ω_{c₁} ∩ D(z₀,r) lying in *bounded*
components ("holes") of ℂ ∖ (K_{c₁} ∪ K_{c₂}) carry no relation data. Since both K_{c_i} are
full, holes exist only when K_{c₁} ∩ K_{c₂} ≠ ∅ — but for real pairs the filled sets always
overlap, so the gap is in the main case, not an edge case.

Repair (recorded as the root-limit pigeonhole route, task P0):

1. z₀ must be chosen on ∂W ∖ K_{c₂} (exists: first-exit path argument) with a **hole-free**
   ball B(z₀,r) (open input: docs/open-problems/03-hole-free-accessible-tip.md; automatic
   when K_{c₁} ∩ K_{c₂} = ∅).
2. Then every w ∈ J_{c₁} ∩ B(z₀,r) is a limit of W-points; φ_{c₁}-values along such limits
   accumulate on the root set of the specialized minimal polynomial with modulus
   e^{G_{c₁}(w)} = 1 (root-limit lemma — bypasses the per-component branch-selection entirely),
   so J_{c₁} ∩ B ⊆ ⋃_i {|g_i| = 1} for the finitely many local algebraic branches g_i.
3. Baire pigeonhole on the perfect set J_{c₁} ∩ B puts a relatively open piece of J_{c₁} inside
   one smooth curve; Step 2 (E–vS) then applies as before.

Status impact: the connected theorem stands **unconditionally when K_{c₁} ∩ K_{c₂} = ∅**, and
is conditional on the hole-free accessible tip (open problem 03) when the filled sets overlap.
The card should not be cited as a complete proof for overlapping pairs until 03 is settled.
Next moves are queued as tasks P0–P6 (formalization) and problem 03 (mathematics).

## Lean formalization (stage 3, 2026-09-29)

Unconditional; every capstone depends only on `[propext, Classical.choice, Quot.sound]`.  Wired into
`GaloisForLFunctions.Bottcher`.

**The 2026-07-02 Step 3 gap is closed, by a different route.**  The relation propagates only through
the far-field component `W` of `Ω_{c₁} ∩ Ω_{c₂}`, and holes may exist.  The Lean proof never needs a
hole-free tip: it needs only *one* access region.  If a holomorphic `g` with `g'(z₀) ≠ 0` at a Julia
point `z₀` equals the Böttcher branch `φ_{c₁}` on some open `A ⊆ Ω_{c₁}` with `z₀ ∈ closure A`, then
in the `w`-plane the local inverse of `g` equals `ψ_{c₁} = φ_{c₁}⁻¹` on `g(A)`, an open subset of the
*connected* lune `ball(g z₀, ε) ∩ {|w| > 1}` — so `ψ_{c₁}` continues across an arc of the circle,
contradicting the natural boundary of the even disk model `h(t) = tψ(1/t)`.  Holes of the
common basin are invisible there.  Smooth-piece (Eremenko–van Strien) rigidity is not used, and
neither is capacity theory.

| Card claim | Lean |
|---|---|
| **Theorem**: `c₁ ≠ c₂ ∈ M ∖ {0,−2}` ⟹ `φ_{c₁}, φ_{c₂}` algebraically independent over `ℂ(z)` (hence over `Q̄(c₁,c₂,z)`) | `Bottcher.noRelation_phiMero_of_mem_mandelbrot` (`Q62BothConnectedIndependence`) |
| Step 1: `J_{c₁} ∩ Ω_{c₂} ≠ ∅`, i.e. `K_{c₁} ⊄ K_{c₂}` (proved by the removable singularity at `∞` + maximum principle instead of capacity) | `not_filledJulia_subset_of_mem_mandelbrot`, `exists_frontier_filledJulia_not_mem_of_mem_mandelbrot`, `greenFunctionDyn_eq_of_filledJulia_subset` (`FilledJuliaNoContainment`) |
| Equal filled Julia sets force `c₁ = c₂` | `c_eq_of_filledJulia_eq'` (corpus) |
| Step 2: `φ_{c₁}` does not continue across any Julia point — and the stronger one-access-region form | `hnb_of_mem_mandelbrot_connected` (corpus); `false_of_continuation_on_open_approach` (`Q62ApproachNaturalBoundary`) |
| Step 3, Case B: `φ_{c₂}` transcendental over `ℂ(z)` | `phiMero_transcendental_of_mem_mandelbrot` (corpus) |
| Step 3, Case A: bad locus discrete; branch continuation at a generic Julia point of the common frontier | `hno_of_connected_of_mem_filledJulia_not_mem` (squarefree bad locus `primitiveSqfreeBad_of_sparse_relation`, perfect component frontiers `frontier_connectedComponentIn_inter_no_isolated`, analytic branch family `analyticAt_branch_of_separable`) |
