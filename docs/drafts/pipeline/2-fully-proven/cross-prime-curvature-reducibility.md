# Cross-prime curvature reducibility — the curvature-language carrier of C5★

- **ID:** cross-prime-curvature-reducibility
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, structural) — Door grade **BRIDGE / RH-blind** (terminal: curvature
  reducibility is the integrability/A2 face, not a second C5 carrier; see Resolution §1–§5 below)
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
- [x] 0 → 1  in-progress: minimal curvature module pinned (rank-2 unipotent extension); `F_{pq}` computed
  (Resolution §1); combination-mode support confirmed (§2, support-2 mixed-sign); reducibility dichotomy
  stated (§3); Door passport sharpened (§4–§5).
- [x] 1 → 2  fully-proven (terminal): `F_{pq}=I+φ_{pq}E` computed; trivializability ⟺ coboundary
  `b_p=(σ_p-1)f` ⟺ uniform Baker — the same `L²`-coboundary as #111/#113; **RH-blind** (A1/A2,
  faces-orthogonality #54). Verdict: **BRIDGE, not a second C5 carrier**; arithmetic residue = C5★ apex.
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the nilpotent curvature identity:
  `upperUnipotentE_mul` proves `(I+aE)(I+bE)=I+(a+b)E`, and
  `upperUnipotentE_curvature_eq` proves
  `(I-b_qE)(I-σ_q(b_p)E)(I+b_pE)(I+σ_p(b_q)E)
   = I+(b_p+σ_p(b_q)-b_q-σ_q(b_p))E` over `2×2` upper-unipotent matrices.
  Remaining Lean targets: the semilinear `σ_p` action on scalar functions, Fourier-support/combination-mode
  reading, the coboundary/trivializability equivalence, and the RH-blind A1/A2 verdict.
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

## Resolution — curvature reducibility is the integrability (A2) face, RH-blind — Wheeler, 2026-06-19

**Verdict: cross-prime curvature reducibility is NOT a second independent C5 carrier.** It is the
curvature-language restatement of the **integrability (A2)** face, RH-blind by the same mechanism that sank
the erosion cocycle (#111) and the finite-free coboundary (#113). Genuine combination modes do appear
(Door-1/4 confirmed), but **trivializability is a coboundary/variance question, orthogonal to the
single-orbit positivity that is RH** (faces-orthogonality #54). Grade **BRIDGE / RH-blind** (terminal).

### §1 Curvature of the minimal module — computed `[PROVED HERE]`
Connection convention (support-log §16): `σ_p` acts semilinearly with matrix `A_p`; zero-curvature
`F_{pq} := A_q^{-1}σ_q(A_p)^{-1}A_pσ_p(A_q) = I ⟺ A_pσ_p(A_q)=A_qσ_q(A_p)`. The **minimal**
curvature-capable arithmetic module is the **rank-2 unipotent extension**
`A_p = I + b_p E`, `E=\begin{psmallmatrix}0&1\\0&0\end{psmallmatrix}` (`E²=0`), `b_p` a scalar on
`𝕋^∞` (the extension class of two rank-1 lines; **constant `b_p`** = the #115 BRIDGE case). Nilpotent
algebra `(I+αE)(I+βE)=I+(α+β)E` gives, with no approximation:
> `A_pσ_p(A_q) = I+(b_p+σ_p(b_q))E`, `A_qσ_q(A_p) = I+(b_q+σ_q(b_p))E`, and
> **`F_{pq} = I + φ_{pq}E`,  `φ_{pq} = (1-σ_q)b_p − (1-σ_p)b_q`.**

`φ_{pq}` is the discrete **curl** of the 1-form `(b_p)_p`. So **flat `F_{pq}=I ⟺ (1-σ_q)b_p=(1-σ_p)b_q ∀p,q`**
= the 1-form is **closed** — the integrability (A2) condition.

### §2 Genuine combination modes (Door-1/4 ✓)
If `b_p` depends on the **other** coordinate `x_q` (the cross-dependence the C3 analysis isolated as where
arithmetic lives), then `σ_q(b_p)≠b_p`, so in Fourier on `𝕋^∞`, `φ_{pq}` carries modes with **both** `p`- and
`q`-components — genuine support-2 **mixed-sign** combination modes (`b_p` real ⟹ both signs), the
near-resonances `p^a≈q^b`. (Constant `b_p` ⟹ `σ_q(b_p)=b_p` ⟹ `φ_{pq}≡0`, trivially flat — the pure
character-variety #115 degeneration.) So `F_{pq}` is an **irreducibly two-prime** object — no single-prime
parent — confirming Door-1/4.

### §3 Trivializability = a coboundary problem (the dichotomy)
Gauge `g=I+fE` acts by `A_p ↦ gA_pσ_p(g)^{-1} = I+(b_p−(σ_p−1)f)E`. So the connection is **reducible to
flat ⟺ `b_p=(σ_p−1)f` for a single scalar `f` on `𝕋^∞`** — i.e. the 1-form `(b_p)` is a **coboundary**
(exact). In Fourier this is `f̂(m)(λ_p(m)−1)=b̂_p(m)` with small divisor `|m·ℓ|` (resonance `m·ℓ≈0`);
`L²`-solvable `⟺ Σ_m|b̂(m)|²/|m·ℓ|² < ∞ ⟺` a **uniform Baker/integer-gap bound** on `|m·ℓ|` across primes.
This is **the card's "reducible ⟺ uniform Baker" dichotomy, made precise** — and it is *literally* the same
coboundary structure as the erosion cocycle (#111: `L²`-reducible iff `σ≥½`, BRIDGE, axis-mode) and the
finite-free coboundary (#113: abscissa `¾`, BRIDGE). Finite-base = `𝕋^d` KAM + Baker (two parents, BRIDGE);
the infinite-base uniform case is exactly #111/#113's object.

### §4 Why this is RH-blind (the A1/A2 punchline)
The coboundary `L²`-norm `Σ_m|b̂(m)|²/|m·ℓ|²` is a `𝕋^∞`-**variance** (second-moment) quantity — the
**integrability / A2** face. RH is the **single-orbit sign / positivity** — the **localization / A1** face.
By **faces-orthogonality (#54, A⊥B)** and the Weyl argument of #113 Step 4 (the orbit equidistributes, so
`L²` controls the *typical fluctuation* of the curvature/coboundary, **not** the pointwise sign — a bounded
coboundary can still change sign), **curvature-trivializability cannot see RH.** This is the same A1/A2
blindness, now read on the connection: *reducibility (A2) ⊥ RH (A1).*

### §5 Net — closes the "second carrier" hope; sharpens C5⇔apex
C5★/RH does **not** live in curvature-reducibility. The arithmetic residue (the actual RH content) is the
**positivity apex** = C5★ — consistent with #117 (`Ш` curvature face: arithmetic residue = C5★ by direct
coboundary, **no surplus**) and #71/#27 (`ω∈H²` localized as the archimedean class). The curvature route is
therefore the **curvature-language restatement of the same apex**, with the reducibility framing RH-blind
exactly as in #113 — **not** an independent carrier. **The verdict is module-independent** (an A1/A2
structural fact): pinning a richer RH-relevant module (`Sym²M_ζ`, Rankin–Selberg `ζ(s)ζ(s+α)`) only enriches
the combination modes of §2, leaving §3–§4 unchanged. Two "independent carriers" (curvature, finite-free)
thus **cross-check to the same conclusion**: the reducibility/coboundary handle is RH-blind; RH is the
single-orbit positivity, which is the apex.

**Door-2 (final).** Qualitative flat⟺commute = BRIDGE (#115); quantitative reducible⟺uniform-Baker =
the #111/#113 coboundary = BRIDGE and RH-blind. No native C5 theorem sits in the curvature-reducibility
route. **Terminal grade: BRIDGE / RH-blind.**

## Log (cont.)
- 2026-06-19 (Wheeler) — **Resolved → BRIDGE / RH-blind (terminal).** Computed `F_{pq}=I+φ_{pq}E`,
  `φ_{pq}=(1-σ_q)b_p-(1-σ_p)b_q` (discrete curl) for the minimal rank-2 unipotent extension `A_p=I+b_pE`.
  Genuine support-2 mixed-sign combination modes when `b_p` is cross-dependent (Door-1/4 ✓; constant=#115
  BRIDGE). Trivializability ⟺ `b_p=(σ_p-1)f` = coboundary = the same `L²`-coboundary/variance structure as
  the erosion cocycle (#111) and finite-free reducibility (#113), `L²`-solvable ⟺ uniform Baker — the card's
  dichotomy, made precise. **RH-blind** by faces-orthogonality (#54) + the #113 Weyl single-orbit-sign
  argument: reducibility (A2) ⊥ RH (A1). So curvature reducibility is NOT a second independent C5 carrier —
  it restates the same apex; arithmetic residue = C5★ (consistent #117). Verdict module-independent. Moved
  1-in-progress → 2-fully-proven.
- 2026-06-19 (Leaner) — added Lean anchors `upperUnipotentE_mul` and `upperUnipotentE_curvature_eq` in
  `formal/GaloisForLFunctions/CrossPrimeCurvature.lean`, formalizing the square-zero upper-unipotent matrix
  algebra behind §1: `(I+aE)(I+bE)=I+(a+b)E` and
  `(I-b_qE)(I-σ_q(b_p)E)(I+b_pE)(I+σ_p(b_q)E)=I+(b_p+σ_p(b_q)-b_q-σ_q(b_p))E`. Added the module to the root
  import and axiom audit. `cd formal && lake env lean GaloisForLFunctions/CrossPrimeCurvature.lean`,
  `cd formal && lake build`, and `bash scripts/check_axioms.sh` pass with 252 audited theorem outputs and no
  `sorry`. Card remains in `2-fully-proven`; the semilinear action, Fourier-support reading,
  coboundary/trivializability equivalence, and RH-blind A1/A2 verdict are not fully Lean-formalized.
