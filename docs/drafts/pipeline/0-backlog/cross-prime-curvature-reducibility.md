# Cross-prime curvature reducibility — the curvature-language carrier of C5★

- **ID:** cross-prime-curvature-reducibility
- **Stage:** 0-backlog
- **Type:** CANDIDATE (native C5 carrier — needs the arithmetic module pinned)
- **Priority:** FOUNDATIONAL
- **Source:** follow-up from `../2-fully-proven/c3-gluing-invariants-bridge.md` (the C3 dividing line);
  ../../door/door-C5-irreducibility-and-door-2-retest.md (combination-mode criterion, "forward" line);
  00-status rows #113, #115; sibling of `../1-in-progress/combination-mode-baker-reducibility.md`
- **Statement (to shape).** For a **coordinate-dependent** rank-`≥2` arithmetic multi-`q` module the
  non-flat curvature `F_{pq}(x) = A_q^{-1}σ_q(A_p)^{-1}A_pσ_p(A_q)` carries genuine **cross-prime
  combination modes**. Conjecture: the curvature is `L²`/analytically **trivializable** (the connection is
  reducible to flat/diagonal) iff a **uniform Baker bound** holds across the primes — the curvature-
  language form of **C5★**, on a specific RH-relevant module.

## Goal
The C3 analysis isolated *where* the native arithmetic lives: **constant** matrices make `σ_p` inert
(curvature `= [A_p,A_q]`, pure character variety, BRIDGE — `../2-fully-proven/c3-gluing-invariants-bridge.md`);
the arithmetic only appears once `A_q` depends on `x_p` (cross-coordinate), so that `σ_p(A_q) ≠ A_q` and
`F_{pq}` genuinely involves the rescaling. This card develops that curvature route as a **second,
independent carrier** of C5★ — complementary to the finite-free / Hankel carrier already pinned in
`../1-in-progress/finite-free-convolution-flow.md`. Two independent carriers of the same native crux is a
strength: they cross-check the "Baker essential, infinite-base uniformity irremovable" claim from
different objects (curvature/connection vs real-rootedness/moments).

## Door passport
- **Door-1/4:** the curvature `F_{pq}` is intrinsically a **two-prime** object — no single-prime parent
  has it (curvature needs ≥2 directions); coordinate-dependence puts it in the infinite/arithmetic zone.
- **Door-2:** the *qualitative* "flat ⟺ commute / `Λ={0}`" is BRIDGE; the **quantitative** trivialization
  (regularity of the gauge solving `F_{pq}=` coboundary, governed by `|m·ℓ|` ≥ Baker) is the C5★ content.
  The test = the same as C5★: finite-base = `𝕋^d` KAM + Baker (two parents, BRIDGE); infinite-base
  **uniform** = no single parent.
- **Door-3:** the curvature class is a native invariant *iff* its arithmetic trivialization-obstruction
  is (i.e. iff C5★) — consistent with the proven `C3-native ⟺ C5★`.

## Approach
1. **Pin an RH-relevant module.** The curvature is only RH/G2-relevant for a *specific* arithmetic
   rank-`≥2` module, not an arbitrary one. Candidates: `Sym²` / `∧²` of the rank-1 `M_ζ`; the
   Rankin–Selberg `ζ×ζ` (moment) module (`ζ(s)ζ(s+α)`, off-diagonal `d(n)` carry mixed-sign modes);
   a rank-2 with deliberate cross-dependence `A_q(x_p,x_q)`.
2. **Compute `F_{pq}` and its Fourier support.** Confirm genuine combination modes (`m_pδ_p+m_qδ_q`,
   mixed sign) appear — the near-resonances `p^a≈q^b` — not just axis modes.
3. **State the reducibility dichotomy** (curvature trivializable ⟺ uniform Baker), reuse **Lemma R**
   (`../1-in-progress/combination-mode-baker-reducibility.md`) for the finite-base half + Liouville
   counterexample.
4. **Door-2 the infinite-base uniform case**; if Baker-essential and uniformity irremovable, it is a C5
   theorem in curvature language. Cross-check against the finite-free carrier's verdict.

## Gates
- [ ] 0 → 1  in-progress: RH-relevant module pinned; `F_{pq}` computed; combination-mode support
  confirmed; the reducibility dichotomy stated; Door passport sharpened
- [ ] 1 → 2  fully-proven: finite-base reducibility ⟺ Baker proven on this module; infinite-base uniform
  case resolved (= C5★ in curvature language) or handed to the C5★ effort
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Cross-references
- `../1-in-progress/combination-mode-baker-reducibility.md` (C5★) and
  `../1-in-progress/finite-free-convolution-flow.md` (the other carrier) — **coordinate with these; do
  not duplicate.** This card is the curvature/connection realization to cross-check them.
- `../2-fully-proven/c3-gluing-invariants-bridge.md` — establishes constant-matrix curvature is BRIDGE,
  motivating the coordinate-dependent object here.
- `../0-backlog/multi-q-shafarevich-gluing-group.md` — `F_{pq}` is the curvature face of `Ш`.

## Log
- 2026-06-19 — created in 0-backlog as a follow-up to the C3 resolution. Develops the curvature-language
  carrier of C5★ that the C3 analysis pinpointed (coordinate-dependent `F_{pq}` is where the arithmetic
  lives; constant = BRIDGE). Complementary to the finite-free carrier; first step = pin an RH-relevant
  rank-≥2 arithmetic module.
