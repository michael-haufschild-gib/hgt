# ADE Bounded-Jet Natural-Boundary Bridge Lemma

- **ID:** ade-boundary-hinf-ht
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (BRIDGE / NOT-NEW)
- **Source:** Wheeler id=1881, id=1891, id=1903 (candidate); Turing id=1914, id=1915, id=1916
  (companion-system closure, source read, hypothesis sharpening). Hille (tool, step 4);
  Fatou+F&M Riesz (step 3); irreducibility/resultant argument (step 2).
- **Statement (sharpened — 2026-06-24 Turing):** Let f be holomorphic on D={|z|<1}, with
  minimal IRREDUCIBLE differential annihilator P(z, f, …, f^{(n)}) = 0 over ℂ(z) (order n ≥ 1).
  Suppose f, f′, …, f^{(n)} ∈ H^∞(D) (the order-n jet — Hypothesis H). Then ∂D is not a
  natural boundary of f. Equivalently: any analytic f with a natural boundary and bounded order-n
  jet is hypertranscendental.

## Goal

Record the classical bridge lemma cleanly and keep it out of the `new/` bucket. The theorem is useful:
bounded jet control plus an algebraic differential equation gives a companion-system continuation
mechanism, so a bounded-jet natural-boundary function is hypertranscendental. But the proof uses standard
complex ODE continuation, Hardy/Fatou boundary limits, and the usual separant/minimality argument; it is
not counted as new knowledge under the project novelty gate.

## The classical n=1 case (REDUCE-TO-KNOWN — do not re-prove)

For n=1: f satisfies P(z,f,f')=0, polynomial ODE. By Painlevé–Ince (classical): solutions have
only isolated movable singularities — they can be analytically continued to a neighborhood of
any non-fixed singular point. A natural boundary contains no isolated-singularity arc ⟹ f
extends analytically past every boundary point ⟹ ∂D is NOT a natural boundary. Contradiction.
Result: DA+n=1 is incompatible with natural boundary at ∂D, REGARDLESS of H^∞ (H^∞ not needed).

This is CLASSICAL. Source: Painlevé 1888, Ince "Ordinary Differential Equations" Ch.XIV.
Hypothesis H is unnecessary here. The n=1 case has zero novelty.

## The n≥2 case under bounded-jet Hypothesis H

**Why H^∞ matters for n≥2:** For n≥2, Painlevé-type singularity analysis no longer rules
out natural boundaries automatically. Chazy's third-order ADE has solutions with natural
boundaries precisely because f, f', f'' are NOT in H^∞ (they blow up as z → ∂D). Hypothesis
H (all derivatives bounded) is the assumption that excludes the Chazy-type blow-up and allows
the Fatou-boundary argument to work.

**Proof sketch (Fatou + Cauchy-Kowalewski):**

Suppose f is DA of order n ≥ 2, f^{(j)} ∈ H^∞(D) for j = 0,...,n-1, and ∂D is a natural
boundary of f.

1. **Fatou limits:** Since f^{(j)} ∈ H^∞(D), by Fatou's theorem each f^{(j)} has non-tangential
   boundary limits at a.e. ζ ∈ ∂D. Call these limits v_j(ζ) = lim_{r→1⁻} f^{(j)}(rζ).

2. **ODE at the boundary:** The polynomial ODE P(z, f, ..., f^{(n)}) = 0 gives (away from the
   fixed singular set Σ ⊂ ℂ of the ODE, which is finite and algebraic):
     f^{(n)} = F(z, f, f', ..., f^{(n-1)})
   where F is a rational function of z and the lower derivatives (the leading coefficient of P
   in f^{(n)} is nonzero away from Σ).

3. **Cauchy-Kowalewski extension:** For a.e. ζ ∈ ∂D ∖ Σ: the initial data (v_0(ζ), ..., v_{n-1}(ζ))
   is finite (by Fatou), and F(z, v_0, ..., v_{n-1}) is analytic in z near ζ (ODE coefficients
   analytic at ζ ∉ Σ). By the Cauchy-Kowalewski theorem, there exists a unique local analytic
   function h defined in a neighborhood U_ζ of ζ with:
     h^{(j)}(ζ) = v_j(ζ) for j = 0,...,n-1,
     P(z, h, h', ..., h^{(n)}) = 0 on U_ζ.

4. **Uniqueness gives extension:** On the intersection U_ζ ∩ D (a non-tangential region at ζ),
   f has the same Fatou limits as h, and both satisfy the same n-th order ODE with the same
   initial data at ζ. By ODE uniqueness: f ≡ h on the non-tangential sector at ζ. Hence h IS
   the analytic continuation of f to U_ζ.

5. **Contradiction:** This holds for a.e. ζ ∈ ∂D. The function f extends analytically past
   a.e. boundary point ⟹ ∂D is NOT a natural boundary. Contradiction. ∎

**Chazy verification:** Chazy's equation f''' = 2f·f'' - 3(f')² has solutions with natural
boundary at the hexagonal lattice circle. But for Chazy solutions: f, f', f'' grow without
bound as z approaches ∂D (the singularities accumulate and |f(z)| → ∞). So f^{(j)} ∉ H^∞(D)
— Hypothesis H FAILS. The theorem correctly does not apply.

## Bucket disposition

**NOT-NEW / BRIDGE.** The corrected proof is a standard classical continuation argument once the claim is
stated: reduce the ADE to a first-order analytic companion system off the separant locus, use bounded
Hardy/Nevanlinna boundary control to find a good boundary approach, anchor the IVP at an interior point,
and cross the boundary using a uniform analytic-ODE existence radius.

The useful content is the reusable lemma and the warning that boundary-limit IVP data are illegitimate.
The former frontier about `f in H^infinity` alone is now closed, and strengthened to arbitrarily long
fixed bounded jets, in `finite-hardy-jet-da-natural-boundary-saturation.md`.

## Superseded crux notes

These notes record the earlier proof gaps. The active disposition is the NOT-NEW / BRIDGE classification
above; the former fixed-depth frontier is closed by the repeated-`E_2` counterexamples cited above.

- **Source check (gate 0->1):** the source check was not used to certify novelty; the theorem is classified
  as a bridge lemma.

- **Step 4 gap:** The uniqueness of ODE solutions requires that the initial data at ζ ∈ ∂D
  uniquely determines f. For ODEs with fixed singularities in Σ: C-K gives a local solution,
  but the initial data might not be in the domain of analyticity of F (if F has a singularity
  at v_j). Need: v_j(ζ) ≠ singularity of F for a.e. ζ. This follows if the set {ζ : v_j(ζ)
  = pole of F} has measure zero — plausible since the poles of F are isolated values.

- **Step 4 gap (alternate):** Does Fatou boundary data uniquely determine the analytic
  continuation? Answer: yes, by ODE uniqueness — IF the ODE has a unique solution for given
  initial data. For nonlinear ODEs, uniqueness holds locally (Cauchy-Kowalewski) but may break
  at movable singularities of the solution. If the solution has no singularities in D (which
  is GUARANTEED by H^∞: all f^{(j)} bounded ⟹ no poles in D), then no movable singularity
  hits D, and local uniqueness extends to global.

- **H^infinity for all derivatives:** superseded by the finite order-`n` jet statement below.  The stronger
  weakening to any fixed derivative depth is false by the explicit repeated-`E_2` primitives in
  `finite-hardy-jet-da-natural-boundary-saturation.md`.

## Connection to transcendental-composition-ht

If H = Γ∘Γ were both DA AND H^∞ on some disk, then this theorem would give H HT — contradicting
DA. So the theorem is relevant IF we can show Γ∘Γ is H^∞ on some disk. But Γ∘Γ has a natural
boundary at the boundary of the domain where Γ maps into D(Γ) (a complicated set determined
by Γ's singularities). This connection is speculative but worth tracking.

## Gates

- [x] 0 -> 1 in-progress: proof route identified; false boundary-IVP route rejected.
- [x] 1 -> 2 fully-proven bridge: companion-system proof with interior anchor and bounded-jet hypothesis.
- [x] 2 -> 3 formalized: complete, unconditional (see **Lean formalization** below).
- [ ] 3 -> 4 publication-ready: only as a cited bridge lemma or appendix, not as a new result.

## Log

- 2026-06-24 — Wheeler id=1881: noted n=1 is classical (Painlevé/Ince). Source check requested
  in id=1891 for n≥2. No response yet.
- 2026-06-24 — Wheeler id=1903: opened this card as BRIDGE CANDIDATE. Proof sketch via
  Fatou+C-K written. Source check (Hille 1976 / Valiron) pending = gate 0→1.

## Fake-proof stress test (Wheeler, 2026-06-24 — monotone method move)

**Attempted counterexample:** Is there a second-order polynomial ODE with an H^∞ solution
having a natural boundary at ∂D?

**Attempt 1 — Linear ODEs (second order):** Solutions of y'' + p(z)y' + q(z)y = 0 with
p, q analytic on D extend analytically by the ODE itself (Cauchy uniqueness away from fixed
singularities). No natural boundary at ∂D. Consistent with theorem.

**Attempt 2 — Painlevé-I (f'' = 6f² + z):** Solutions have movable double poles. A solution
with NO poles in D satisfies f ∈ H^∞(D) and f'' = 6f² + z ∈ H^∞(D) (since f is bounded). Do
such solutions exist? Yes: the tritronquée solutions of Painlevé-I are entire (no poles at all)
⟹ H^∞ on every disk. Does any H^∞ Painlevé-I solution have a natural boundary at ∂D? NO:
by the C-K argument (Fatou limits of f and f' → local ODE extension at a.e. ζ ∈ ∂D), ∂D
cannot be a natural boundary. Consistent with theorem.

**Attempt 3 — Mahler equations and functional equations:** f(z²) = f(z) - z (Mahler) has
solutions with natural boundaries (lacunary series Σ z^{2^n}). BUT these satisfy FUNCTIONAL
equations (z ↦ z²), not polynomial ODEs. The ADE-boundary theorem does not apply. No contradiction.

**Verdict:** Could not construct any counterexample — every candidate either fails H^∞ (has
poles) or fails the natural boundary condition (analytic extension exists). The theorem is
well-supported by the fake-proof attack. The Painlevé analysis is the key: movable poles (the
only natural way to get bad behavior in nonlinear ODE solutions) violate H^∞; without movable
poles, the C-K extension works. Hypothesis H is exactly the condition ruling out movable poles.

**Monotone invariant:** Cap(E_r) = capacity of {ζ ∈ ∂D : f not extensible at ζ}. Under the
theorem's hypothesis: H^∞ → Fatou limits a.e. → C-K extension → Cap(E_1) = 0. Natural
boundary → Cap(E_1) = 1. These can't both hold. The "monotone decrease" is of Cap(E_r) → 0
as the H^∞ condition strips non-extensible points; the theorem says it reaches zero.

## 2026-06-24 Turing — proposed proof CLOSURE (companion-system IVP, not CK) + generalization to all n

**The Fatou→Cauchy-Kowalewski step is a non-sequitur** (CK needs analytic arc-data; Fatou gives only a.e.
measurable point-limits). Counterexample-to-the-method: f(z)=Σ_k 2^{−k²}z^{2^k} has ALL derivatives in H^∞
yet a natural boundary (lacunary, HT) — so the Fatou step without DA would falsely continue it. DA must do
the work; here is how.

**Right tool: the first-order companion system + analytic ODE-IVP (point data — Fatou suffices).**
Let F = (f, f′, …, f^{(n−1)}) : D → ℂ^n. Then F′ = Φ(z,F), Φ(z,w) = (w₁,…,w_{n−1}, R(z,w)), with R the
algebraic root of the (minimal) ODE P(z,·)=0 in y^{(n)} — analytic where the separant ∂P/∂y^{(n)} ≠ 0.

**Closure via uniform existence radius from boundedness (Hypothesis H):**
1. At a.e. boundary ζ: F(ζ) exists (Fatou, since each f^{(j)}∈H^∞); separant∘f ≢ 0 (minimality of P), so
   separant(ζ) ≠ 0 for a.e. ζ ⟹ Φ analytic near (ζ, F(ζ)).
2. Near a good ζ, F stays in a compact K_ζ ⊂ {Φ analytic} (F bounded + continuous radial limit) ⟹ the
   analytic-ODE IVP existence radius is ≥ δ_ζ > 0 UNIFORMLY for initial data in K_ζ (Hille, ODE in the
   complex domain: the existence disk depends on dist to Φ-singularities and sup|Φ|, both controlled on K_ζ).
3. Anchor the IVP at an INTERIOR point z₁ near ζ with dist(z₁, ∂D) < δ_ζ. Its unique solution equals F on
   B(z₁,δ_ζ)∩D and is analytic on ALL of B(z₁,δ_ζ), which crosses ∂D. So F (hence f) continues across ζ.

Anchoring at an interior z₁ (genuine jet, no Fatou-limit matching) sidesteps the boundary-matching subtlety;
the uniform δ_ζ — which exists precisely because H confines F to the analyticity region — carries the
continuation past ∂D. Continuation on a positive-measure arc ⟹ ∂D not a natural boundary ⟹ contradiction ⟹
f HT. ∎ (proposed)

**Generalizes to all n ≥ 1**: the companion-system argument is uniform in n; the Painlevé/Ince case-split
(n=1 only) is unnecessary — n=1 is a corollary. Chazy/E2 are excluded by failing H (derivatives blow up),
consistent.

**To verify before 1→2:** (a) minimality of P for the separant∘f ≢ 0 step; (b) the precise analytic-ODE
uniform-existence-radius citation (Hille Ch. on the complex-domain existence theorem); (c) that F's good-ζ
radial limit lands at positive distance from the separant-zero locus for a.e. ζ. Flagged to Wheeler (owner).

### Self-attack refinement (Turing, same day) — P must be minimal IRREDUCIBLE (rules out singular solutions)

Attacking the closure: the step "separant∘f ≢ 0 by minimality" is WRONG with only minimal-ORDER P. f could
be a SINGULAR solution (separant S=∂P/∂y^{(n)} ≡ 0 identically along f — an envelope), where Φ degenerates
along F and the companion-system argument collapses.

**Fix: take P the minimal IRREDUCIBLE differential polynomial annihilating f** (free — take the minimal
irreducible factor of any annihilator). Then P, S are coprime in y^{(n)} (irreducible ⟹ no repeated
y^{(n)}-factor), so the resultant Res_{y^{(n)}}(P, S) ≢ 0 is a differential polynomial of order ≤ n−1. Since
f^{(n)}(z) is a common y^{(n)}-root of P and S at each z when S∘f ≡ 0, that resultant vanishes on f ⟹ f is DA
of order ≤ n−1, contradicting minimality. Hence S∘f ≢ 0: f is NOT a singular solution, and the R-branch
through F is single-valued near a.e. good ζ. The closure is then airtight.

**Refined theorem statement:** f DA with minimal IRREDUCIBLE annihilator P (order n ≥ 1), all f^{(j)} ∈ H^∞(D)
⟹ ∂D is not a natural boundary ⟹ f is HT. (The n≥2 restriction and the Painlevé case-split are unnecessary;
n=1 is a corollary.)

Three other load-bearing steps survived self-attack: (i) uniform existence radius at good ζ (F's continuous
radial limit lands at positive distance from the separant-zero locus); (ii) the IVP solution analytic on the
full existence disk; (iii) one regular boundary point already contradicts a natural boundary.

## 2026-06-24 Turing — CONSOLIDATED clean proof (supersedes the two working notes above; for 1→2)

**Theorem.** Let f be holomorphic on the unit disk D, with minimal IRREDUCIBLE differential annihilator
P(z, f, …, f^{(n)}) = 0 over ℂ(z) (order n ≥ 1). Suppose the order-`n` jet
f, f′, …, f^{(n)} ∈ H^∞(D). Then ∂D is not a natural boundary of f. Equivalently: a DA function whose
order-`n` jet is bounded on D has no natural boundary — so any f with a natural boundary and bounded
order-`n` jet is hypertranscendental.

**Proof.**
1. *Companion system.* Where the separant S := ∂P/∂y^{(n)} is nonzero, solve P=0 for y^{(n)} = R(z, y, …,
   y^{(n−1)}), R analytic (an algebraic-function branch). With F := (f, f′, …, f^{(n−1)}): D → ℂ^n, then
   F′ = Φ(z, F), Φ(z,w) = (w₁, …, w_{n−1}, R(z,w)), analytic where S ≠ 0.

2. *S∘f ≢ 0 (no singular solution).* If S∘f ≡ 0 then f^{(n)}(z) is, at each z, a common y^{(n)}-root of P
   and S; since P is irreducible, P and S are coprime in y^{(n)}, so Res_{y^{(n)}}(P,S) ≢ 0 is a differential
   polynomial of order ≤ n−1 vanishing on f — contradicting minimality. Hence S∘f ≢ 0.

3. *Good boundary points have full measure.* Each f^{(j)} ∈ H^∞ ⟹ (Fatou) the radial limit f^{(j)}(ζ) exists
   for a.e. ζ ∈ ∂D, so the boundary jet F(ζ) exists a.e. Also S∘f is a polynomial in the f^{(j)} ∈ H^∞, hence
   S∘f ∈ H^∞; being ≢0, it has nonzero radial limit a.e. (F. & M. Riesz). So for a.e. ζ ("good ζ"): F(ζ)
   exists and S(ζ, F(ζ)) ≠ 0, hence Φ is analytic on a polydisc about (ζ, F(ζ)).

4. *Uniform existence radius from boundedness.* Fix a good ζ. As z → ζ radially, F(z) → F(ζ), staying in a
   compact K_ζ ⊂ {Φ analytic} at positive distance from the singular locus; sup|Φ| is bounded on a polydisc
   about K_ζ. By the analytic-ODE existence theorem (Hille, *ODE in the Complex Domain*), the IVP
   F′=Φ(z,F), F(z₀)=w₀ has, for (z₀,w₀) in this regime, a solution analytic on a disk of radius ≥ δ_ζ > 0,
   uniform in z₀ along a radial segment ending at ζ.

5. *Continuation.* Take z₁ on that segment with dist(z₁, ∂D) < δ_ζ. The IVP solution through (z₁, F(z₁))
   equals F on B(z₁, δ_ζ) ∩ D (uniqueness) and is analytic on all of B(z₁, δ_ζ) (the existence radius keeps
   it inside the analyticity polydisc). B(z₁, δ_ζ) crosses ∂D, so F — hence f — continues analytically across
   the good point ζ. A single such regular boundary point already contradicts "natural boundary." ∎

**Grade:** NOT-NEW / BRIDGE. Classical tools: Hille analytic continuation; Fatou / F.&M.Riesz;
resultant/minimality. Useful caution: the proof must use a companion-system IVP anchored at an interior
point, not Cauchy-Kowalewski from boundary Fatou data. Uniform in n (n=1 a corollary; Painlevé case-split
unnecessary). Witness that DA is essential: Σ_k 2^{−k²}z^{2^k} has all jets in H^∞ and a natural boundary,
but is hypertranscendental, so no companion system exists.

## 2026-06-24 Turing — source-read notes (Hille/Malmquist/Chazy/movable-singularity)

Direct read of the cold-probe's "closest tools," no prior covering the theorem found:
- **Chazy** (canonical algebraic ODE with a natural boundary): general solution meromorphic inside a movable
  disk with poles ACCUMULATING at the boundary ⟹ derivatives unbounded there ⟹ fails Hypothesis H. So the
  literature has the *example*, and it confirms the contrapositive: a natural boundary of an algebraic-ODE
  solution comes WITH unbounded derivatives. Our theorem is the general obstruction ("boundedness ⟹ no
  Chazy-type natural boundary"), which is not stated as such.
- **Malmquist** (Wikipedia + arXiv:2509.18649 Malmquist–Yosida–Schwarzian): first-order, *meromorphic* (or
  algebroid) solutions, restricting equation form — different regime, adjacent-not-covering.
- **Filipuk–Halburd, arXiv:0804.2859** (movable algebraic singularities of 2nd-order ODEs): interior movable
  singularities reachable along finite-length curves are algebraic branch points (finite Laurent in
  fractional power). About INTERIOR singularities / specific classes, not the boundedness→no-natural-boundary
  statement, though thematically related (it tames interior movable singularities; we tame the boundary via H).
- **Hille, ODE in the Complex Domain**: supplies the analytic-continuation existence theorem used in step 4
  (the uniform existence radius). The continuation tool, not the conclusion.

Disposition after later audit: do not use these notes to claim novelty. They support the bridge proof and
the surrounding landscape, but the theorem itself is classified as NOT-NEW / BRIDGE.

## 2026-06-24 Turing — HYPOTHESIS SHARPENING: order-n jet suffices (not all derivatives)

Wheeler's hypothesis "all f^{(j)} ∈ H^∞" (infinitely many conditions) can be weakened to the FINITE
hypothesis: **f, f′, …, f^{(n)} ∈ H^∞(D)** (the order-n jet — n+1 functions). The proof uses the derivatives
only through these two places:

1. **Companion-system + boundary jet:** needs F = (f,…,f^{(n−1)}) ∈ H^∞ — so its radial limit F(ζ) exists
   a.e. (Fatou) and it stays in a compact analyticity region. Uses derivatives up to order n−1.
2. **Separant nonzero a.e.:** the step "S∘f has nonzero boundary limit a.e." needs S∘f of bounded type
   (Nevanlinna), so that radial-limit-zero on a positive-measure set forces S∘f ≡ 0 (Lusin–Privalov /
   F.&M. Riesz). S = ∂P/∂y^{(n)} is a polynomial in f,…,f^{(n)}; if all of these ∈ H^∞ ⊂ N, then S∘f ∈ H^∞ ⊂ N.
   Uses derivative of order n.

Nothing in the continuation argument touches f^{(n+1)}, f^{(n+2)}, … — and indeed those CAN blow up at ∂D
(near the bad locus where the leading coefficient / separant → 0) without affecting the conclusion. So
"all f^{(j)} ∈ H^∞" is strictly stronger than needed.

**Sharpened theorem:** f DA with minimal irreducible annihilator P of order n, and **f, f′, …, f^{(n)} ∈ H^∞(D)**
⟹ ∂D is not a natural boundary ⟹ f HT.

## Closed frontier

The conjecture "does `f in H^infinity` alone suffice?" is false.  The explicit repeated-`E_2`
primitives in `finite-hardy-jet-da-natural-boundary-saturation.md` are DA, have arbitrarily long
fixed bounded jets, and retain the unit circle as a natural boundary.  This theorem card therefore
keeps the sharp order-adaptive bounded-jet bridge lemma.

## Lean formalization

The consolidated proof is formalized unconditionally in Lean 4.  Every capstone is audited at
`[propext, Classical.choice, Quot.sound]`.

**A shortcut found while formalizing.**  The card's proof uses Fatou boundary jets plus F. & M.
Riesz solely to produce, arbitrarily close to `∂D`, one point where the separant evaluation is
bounded away from zero.  Since that evaluation `g` is holomorphic on `D` and `g` is not
identically zero, the **maximum modulus principle** on `{|z| ≤ r}` already gives, on *every*
circle, a point `z₁` with `|g(z₁)| ≥ |g(z₀)|` — a uniform lower bound with no boundary values, no
Nevanlinna class and no almost-everywhere statement.  Since a single regular boundary point
already contradicts a natural boundary, nothing is lost.  Likewise the separant step is proved
from *leader-degree minimality* rather than from irreducibility plus a resultant: the separant
`∂P/∂y_n` is nonzero in characteristic zero and has strictly smaller leader degree, which is
exactly what Ritt reduction supplies, so the Gauss/Bezout/resultant machinery is not needed.

| Card step | Lean declaration | Module |
|---|---|---|
| companion system `F' = Φ(z,F)` | `companionVec` (autonomous: `z` is carried as a state coordinate) | `HTGeometry/BoundedJetNaturalBoundary.lean` |
| the jet solves it | `odeJet`, `odeJetDeriv`, `hasDerivAt_odeJet_full`, `hasDerivAt_odeJet` | same |
| differentiating `P = 0` to `S·f⁽ⁿ⁺¹⁾ = N` | `jetSeparant`, `jetNumerator`, `differentiated_relation` | same |
| step 2, `S ∘ f ≢ 0` | `IsLeaderMinimalAnnihilator`, `separant_ne_zero_of_leaderMinimal`, `exists_leaderMinimalAnnihilator` | `HTGeometry/MinimalAnnihilatorSeparant.lean` |
| step 3, a good point near the boundary | `exists_norm_ge_on_sphere` (maximum modulus) | `HTGeometry/BoundedJetNaturalBoundary.lean` |
| step 4, uniform existence radius (Hille) | `exists_analytic_ode_solution` | `HTGeometry/AnalyticODEExistence.lean` |
| ODE uniqueness | `ode_solution_unique` | same |
| step 5, continuation across `∂D` | `exists_analytic_continuation_of_bounded_jet`, `exists_analytic_continuation_of_annihilator`, `exists_analytic_continuation_of_leaderMinimal`, `exists_analytic_continuation_of_minimal_order` | `HTGeometry/BoundedJetNaturalBoundary.lean`, `MinimalAnnihilatorSeparant.lean` |

Supporting infrastructure built for this card (both were mathlib gaps):

- `HTGeometry/AnalyticODEExistence.lean` — local existence **with a radius depending only on the
  polydisc data** `(ρ, ρ', M, L)`, and local uniqueness, for a holomorphic ODE on a complex Banach
  space.  Picard iteration on `DifferentiableOn.isExactOn_ball`, limit by
  `tendstoUniformlyOn_tsum` and `TendstoLocallyUniformlyOn.differentiableOn/.deriv`; uniqueness by
  the `(δL)^k` iteration, no Gronwall.  `Mathlib/Analysis/ODE/` is real-variable Picard–Lindelöf
  only.
- `HTGeometry/MvPolynomialSmooth.lean` — `contDiff_mvPolynomial_eval`,
  `differentiable_mvPolynomial_eval`, uniform bound and Lipschitz estimates on closed balls, and
  the multivariate chain rule along a holomorphic curve
  (`hasDerivAt_mvPolynomial_eval_comp`).

The statement formalized is uniform in `n` (so the classical `n = 1` Painlevé–Ince case is a
corollary, exactly as the card says), and the hypothesis used is the card's sharpened one: only
the order-`n` jet `f, f', …, f⁽ⁿ⁾` needs to be bounded, which is what `‖odeJet f n z‖ ≤ M`
records.
