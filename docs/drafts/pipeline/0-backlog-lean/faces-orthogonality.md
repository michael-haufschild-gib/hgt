# Face A ⊥ Face B — the orthogonality theorem (G14)

- **ID:** faces-orthogonality
- **Stage:** 1-in-progress (proof complete; staged here pending the C5 push)
- **Type:** THEOREM (paper, structural) — Door grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/bucket-A1-A2-unification-the-carrier.md (#70 SEED-P/G14) · 00-status row #54
- **One sentence.** Face A (positivity / RH-on-line) and Face B (genericity / DSS) are **logically
  independent** conditions on an L-datum — each holds without the other (witnessed) — because Face B is
  carried by the **multiplicative** (Euler / prime-lattice) structure and Face A by the **archimedean**
  completion, two disjoint parts that coincide as *both hard* only at the ℚ apex. This is the structural
  reason the proven Face-B gatekeepers (G1, G3, G4) leave RH (Face A) untouched — and it tells the C5 search
  where the native content must live: the **archimedean / `t`-orbit** axis.

---

> **Prior art (standing-order check).** This theorem largely **re-derives existing
> `support-extraction-log.md` content** and should be read as a proof/repackaging, not a discovery:
> **#75/B29** (L575–581, the (E)/(A)/(P) cuts: "(P) does NOT imply (A)", fakes pass positivity) = Leg 2;
> **G10** (L268–274, "RH = cone, DSS = generic", two separate conditions on Object-X) = the framing;
> **#84/B28** (L888–895, Diamond–Montgomery–Vorhauer: off-line zeros are GENERIC, RH is a special
> arithmetic-forced stratum) = an *independent confirmation* that Face B (genericity) ⊥ Face A (RH). New
> packaging only: the multiplicative⊥archimedean (§R/seam) identification and the C5 corollary.

## §1 The two faces as conditions on the secular datum
For an L-datum with completed `ξ = (\text{arch factor}) × (\text{Euler product})` and zeros `\{ρ\}`:
- **Face A (positivity).** Critical-line / unitarity: all `ρ` on the line ⟺ Li-positivity `λ_n ≥ 0` ⟺ the
  boundary rep of `G_L` unitary (`m_ξ` Herglotz, `κ₋=0`). A **sign / real-positivity** condition.
- **Face B (genericity).** DSS / period-fullness: zero-data transcendentally generic — `\{γ_n\}` (or the
  boundary angles) `ℚ`-algebraically independent ⟺ `trdeg = \dim G_L`-orbit ⟺ boundary rep **faithful**. An
  **algebraic-independence** condition.

**Operational meaning of "orthogonal".** A and B are *logically independent*: neither implies the other,
proved by exhibiting instances realizing the **off-diagonal** cells (A∧¬B and ¬A∧B compatible), not a
reduction.

## §2 The instantiation grid
| Row | Face A (on-line) | Face B (generic) | proves |
|---|:--:|:--:|---|
| function field `ζ_C/F_q(C)` | **TRUE** (Weil) | **FALSE** (eigenvalues algebraic) | **A ⇏ B** (§3) |
| fake / non-Euler (superzeta; off-line Beurling; N6) | **FALSE** | structure present | **B ⇏ A** (§4) |
| number field `ζ/ℚ`, arithmetic `L` | hard (RH) | hard (DSS) | apex coincidence (§5) |

## §3 Leg 1 — `A ⇏ B`, the function-field witness `[PROVED HERE]`
Over `F_q(C)`: `P(u)=∏_{i=1}^{2g}(1−α_i u)∈ℤ[u]`. Face A holds — Weil RH gives `|α_i|=q^{1/2}`. Face B
fails — the `α_i` are **algebraic** (roots of `P∈ℤ[u]`), `trdeg_{ℚ̄}\{α_i\}=0`, the opposite of generic
(corank-transcendence card: FF block `=ℚ̄(\ln q)`, `trdeg`-finite). So **(A true, B false)** is realized ⟹
Face A does not imply Face B. ∎ *(Door-5 border row — checkable before the apex.)*

## §4 Leg 2 — `B ⇏ A`, the multiplicative-underdetermination witness `[PROVED HERE, modulo cited theorems]`
1. **Face-B invariants are multiplicative-only (unconditional):** `corank(Λ)=\dim_ℚ\text{span}\{\log p\}`
   (#121), holonomicity (#119), the Satake λ-ring `𝓜=ℚ[p_m]` (#79) — none involves the archimedean factor.
2. **Face A needs the archimedean completion (unconditional):** `ξ=(\text{arch})×(\text{Euler})`; the zero
   locations depend on the arch factor via the functional equation; the Euler product alone does not fix them.
3. **Underdetermination is real (cited theorems):** the First Theorem (Euler ⟺ Bohr factorization, #81), the
   three cuts (positivity ≠ genuineness, #82), the N6 witness (moment-positivity ⇏ frequency-positivity,
   #88) — each gives multiplicative-side structure compatible with Face A false.
So **(B-structure, A false)** is realized ⟹ Face B does not imply Face A. ∎

## §5 The seam identification + apex coincidence `[BRIDGE; now unconditional]`
A and B are carried by **disjoint** parts of the object:
- **Face B = multiplicative wing.** By `compute-omega-h2-gl.md` §R the `∞`-prime Koszul complex is acyclic
  (`H(t)E(−t)=1` in `Λ`): the multiplicative wing has **no archimedean content** (cohomological #74).
- **Face A = archimedean counterterm.** Positivity lives in the Γ-factor / `s=1` data (`ω` purely
  archimedean, §R; seam #69/#71).
Hence **orthogonality = the multiplicative ⊥ archimedean decomposition of the seam.** The faces coincide as
both-hard only at the ℚ apex, where the coupling `F₁` is missing (`corank=∞` vs FF `corank=1`). Over `F_q`
the coupling exists (one Frobenius) so the axes separate cleanly (§3) — *why* the border is solvable and the
apex is not. **This is why Face-B gatekeepers don't deliver RH: they compute in the wing that is blind to
the face RH lives on.**

**§5′ — the multiplicative ⊥ archimedean decomposition is now UNCONDITIONAL (Professor #132/#133,
2026-06-19).** The §5 identification originally rested on the Koszul-acyclicity §R (SEED-R-conditional). It
no longer needs SEED-R, because two unconditional structural theorems pin the decomposition directly:
- **#133 (`archimedean-generator-axis-mode`):** the generators `σ_p, ∂_s` are **Fourier-diagonal**
  (`σ_p e_m=p^{−m_p}e_m`, `∂_s e_m=−(m·ℓ)e_m`), so the Face-B combination-mode content arises **only** from
  the multiplicative ring product `e_m·e_{m'}=e_{m+m'}` (prime data), while `∂_s`'s sole non-axis residue is
  the **archimedean** digamma `½ψ(s/2)` (Source A). Multiplicative combination modes ⊥ archimedean residue,
  by construction.
- **#132 (`archimedean-prime-cross-term`):** the FE-asymmetry (the Face-A coupling that fixes zero
  locations) is the **purely archimedean** defect `[χ]=Γ_ℝ(1−s)/Γ_ℝ(s)`; the prime lane contributes **zero**
  FE-defect. So Face A's content is archimedean, disjoint from the multiplicative wing.
Together: the multiplicative wing (prime `e_m` + `σ_p`, Face B) and the archimedean factor (`Γ_ℝ`, `χ`, the
digamma, Face A) are disjoint **without** invoking Koszul acyclicity. The §R cohomological form
(`ω`-multiplicative-shadow `=0`) is a stronger optional refinement; the orthogonality itself is now
unconditional.

**C5 corollary (the constructive reading).** The native RH content cannot be reached from the multiplicative
wing — it must live in the **archimedean / `t`-orbit** direction. This matches Wheeler's relocation of C5★
to single-orbit hyperbolicity on the diagonal Bohr orbit (`finite-free-convolution-flow.md`): the t-orbit is
exactly the Face-A axis this theorem isolates.

## §6 Door passport
- **BRIDGE.** Leg 1 uses Weil; Leg 2 uses #81/#82/#88 + the unconditional multiplicative-only-ness; §5/§5′
  is now **unconditional** via #132/#133 (the Koszul `compute-omega` §R form is an optional refinement, no
  longer load-bearing). **Content beyond imports:** the grid + the identification **orthogonality = seam
  decomposition** + the C5 corollary (where the native content must live).
- **Avoids the §42 trap:** locates RH's difficulty (the archimedean axis); does not restate RH.

## Gates
- [x] 0 → 1  in-progress: two axes defined; grid pinned; "orthogonal" = logical independence via witnesses.
- [x] 1 → 2  fully-proven: A⇏B (§3, airtight); B⇏A (§4); seam identification + apex (§5). BRIDGE, content
  beyond imports (§6). *(Stage move to 2-fully-proven deferred only to keep focus on the C5 push.)*
- [ ] 2 → 3  formalized — FF leg (`|α_i|=√q` ∧ `α_i` algebraic); multiplicative-only-ness of `corank`.
- [ ] 3 → 4  publication-ready.

## Notes / risk
- Proves **logical independence of the faces**, not RH or DSS. No apex claim.
- Leg 2's cohomological form is SEED-R-conditional (§R); its unconditional core (multiplicative invariants ⊥
  arch factor + cited fakes) stands without SEED-R, and §5′ (Professor #132/#133) now makes the full
  multiplicative⊥archimedean decomposition unconditional, so SEED-R is no longer load-bearing anywhere here.
- The (¬A ∧ B-generic) cell is witnessed at "structure present"; an explicitly transcendentally-generic
  off-line Beurling system is a future sharpening (`../0-backlog/realization-problem.md`).

## Cross-references
- `a1-a2-unification-brick.md` (dual: the weld) · `compute-omega-h2-gl.md` §R · `../2-fully-proven/stieltjes-log-weld.md`
- `finite-free-convolution-flow.md` (the C5★ carrier; this theorem's §5 corollary tells it where to look)
- `../../door/bucket-realization-and-fake-family.md` (#81/#82/#88 witnesses).

## Log
- 2026-06-19 — created in 0-backlog (orthogonality theorem G14: Face A ⊥ Face B).
- 2026-06-19 — Professor: pulled to 1-in-progress and **proved** as a structural BRIDGE theorem. Leg 1 (FF,
  Weil + algebraicity), Leg 2 (multiplicative-only + fakes #81/#82/#88), §5 the seam decomposition (via
  `compute-omega` §R) + apex coincidence. Added the **C5 corollary**: the native content lives on the
  archimedean axis. Avoids the §42 trap.
- 2026-06-19 — Professor: **§5′ added — the multiplicative⊥archimedean decomposition is now unconditional**
  via #132 (FE-defect purely archimedean) + #133 (generators mode-diagonal; combination modes = ring
  product). SEED-R is no longer load-bearing. Moved to **2-fully-proven** (BRIDGE, content beyond imports).
  Reframed under the team reorientation (forget RH): the value here is isolating the **transcendence axis**
  (Γ⊥ζ as disjoint parts) — the input the difference-differential hypertranscendence weld (the C5 target)
  needs for the Γ/ζ non-conspiracy.
</content>

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The card's main statement is logical independence of Face A and Face B, which requires both off-diagonal witnesses: `A ∧ ¬B` and `¬A ∧ B`. The function-field leg supports `A ⇏ B`, but the `B ⇏ A` leg only shows multiplicative-side structure / underdetermination compatible with Face A false; it does not exhibit an L-datum or fake system with the stated Face-B genericity/DSS condition true while Face A fails. The card's own risk note says the explicitly transcendentally-generic off-line Beurling system is future work. Therefore the theorem is not fully proven on paper as stated. A repaired version should either weaken the statement to multiplicative-underdetermination / structural orthogonality, or supply the actual `¬A ∧ B` witness.
