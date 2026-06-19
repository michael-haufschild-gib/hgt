# Two sources of hypertranscendence — the complete σ-orbit-balance invariant that separates Source A (Γ) from Source B (primes)

- **ID:** two-sources-of-hypertranscendence
- **Stage:** 2-fully-proven — the framing is now **grounded by a proven invariant**: the
  complete, decidable CC-criterion (per-σ-orbit degree-0 balance of the multiplier divisor), which strictly
  strengthens the multiplier-dichotomy card's sufficient degree-at-∞ test and pins Λ's unique Source-A place.
- **Type:** THEOREM (paper) + FRAMING — **grade BRIDGE** (the criterion is the classical rational
  shift-summability/Abramov condition in divisor form; the *organizing payload* — that this single invariant
  is the archimedean–prime divide and localizes the unique Source-A place — is the new content).
- **Priority:** FOUNDATIONAL — the re-centered "reason the field exists," now with a proven invariant.
- **Source:** the 2026-06-19 Hölder-recentering of `../../00-core-vision.md` + `../../00-charter-wall-and-door.md`
  §2; corpus #90 §64 / SEED-G (two sources; Γ = unique non-constant polynomial multiplier); companion theorem
  `../2-fully-proven/multiplier-dichotomy-theorem.md` (the sufficient dichotomy this card completes);
  classical: Abramov rational summability / the shift-coboundary criterion; 00-status rows #2, #3, #130.
- **Provenance (standing-order corpus check):** the two-source *framing* is #90 §64 (SEED-G) / 00-status #130.
  The *sufficient* dichotomy (constant/coboundary ⟹ holonomic; degree-∞ ≠ 0 ⟹ non-CC) is the companion
  card. **New here:** the **complete** invariant — `a` is CC ⟺ `div(a)` has degree 0 on every σ-orbit — and
  its consequence that the σ-orbit-balance is the exact, decidable Source-A/B classifier with `Λ`'s unique
  Source-A place localized to the orbit `ℤ` of the Γ-multiplier. Corpus search (Abramov/summable/telescoping/
  orbit-degree) returns only the companion dichotomy card — not previously stated.

---

## The two sources (the framing this card grounds)

The hypertranscendence of the completed `Λ = Γ·ζ` splits by the **multiplier type** of the rank-1 difference
operators:
- **Source A — the archimedean `Γ`.** One shift operator `s↦s+1` with a **non-constant polynomial**
  multiplier `a = s/2π` (`Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`). Differential-hypertranscendent (Hölder 1887),
  difference-tame. The unique non-CC place.
- **Source B — the infinite prime base.** Infinitely many `q`-dilations `σ_p : x_p↦p^{-1}x_p` with
  **constant** multipliers. Per-lane holonomic (CC), decoupling — BRIDGE in isolation.

The functional equation `Λ(s)=Λ(1−s)` **welds** them; **C5 is the weld, not either source** (charter §5).

## The complete invariant (the proven content)

Let `(K,σ) = (ℂ(z), z↦z+1)`, `a ∈ K^×` the multiplier of a rank-1 module. Recall (companion card) `a` is
**constant-up-to-coboundary (CC)** if `a = c·σ(g)/g` for some `c∈ℂ^×`, `g∈ℂ(z)^×`; CC ⟺ the module is
gauge-trivial ⟺ holonomic/DA (Source B); non-CC ⟺ hypertranscendental (Source A, via Hölder/ADH). The
companion card proved the *sufficient* obstruction `deg_∞(a)≠0 ⟹ non-CC`. The **complete** criterion:

> **Theorem (σ-orbit-balance = the complete CC-invariant). [PROVED HERE]**
> Write `div(a) = Σ_{β∈ℂ} ord_β(a)·[β]` (finite). `σ` acts by `β↦β+1`; its orbits are the cosets
> `O = β+ℤ`. For an orbit `O` set the **orbit-degree** `deg_O(a) := Σ_{γ∈O} ord_γ(a)` (a finite sum).
> Then
> **`a` is CC  ⟺  `deg_O(a) = 0` for every σ-orbit `O`.**
> Equivalently, the rank-1 module is **holonomic (Source B) ⟺ the multiplier divisor is σ-orbit-balanced**;
> otherwise it is **hypertranscendental (Source A)**. The condition is **decidable** (`a` has finitely many
> zeros/poles, meeting finitely many orbits; check each orbit's degree).

### Proof
**(⟸)** Suppose `deg_O(a)=0` for every orbit. Fix an orbit `O=β+ℤ`; the restriction `div_O(a)=Σ_n m_{β+n}[β+n]`
is a degree-0 divisor on `O` (`Σ_n m_{β+n}=0`). The shift-difference map `Δ:[γ]↦[γ-1]-[γ]` on the free abelian
group `ℤ^{(O)}` has image **exactly** the degree-0 (augmentation-kernel) subgroup — every finite degree-0
divisor on `ℤ` telescopes into a `ℤ`-combination of consecutive differences `[γ-1]-[γ]`. So there is
`g_O = ∏_{γ∈O}(z-γ)^{n_γ}` (finite) with `div(g_O(z+1)/g_O(z)) = div_O(a)` (since
`div((z-γ+1)/(z-γ)) = [γ-1]-[γ]`). Take `g = ∏_O g_O` (finite product). Then `a·g(z)/g(z+1)` has trivial
divisor on `ℂ`, hence is a constant `c∈ℂ^×` (`a≠0`); i.e. `a = c·g(z+1)/g(z)`. CC. ∎

**(⟹)** If `a = c·σ(g)/g`, then `div(a) = σ^{-1}(div g) − div g`. Since `σ` permutes each orbit `O` into
itself, `deg_O(σ^{-1}(div g)) = deg_O(div g)`, so `deg_O(a) = deg_O(div g) − deg_O(div g) = 0` for every `O`. ∎

### Consequences
1. **Recovers the companion obstruction as a shadow.** `deg_∞(a) = −Σ_{β} ord_β(a) = −Σ_O deg_O(a)`. If every
   `deg_O=0` then `deg_∞=0`; so `deg_∞(a)≠0 ⟹ some deg_O≠0 ⟹ non-CC`. The companion card's degree-at-∞ test
   is the **total** (summed-over-orbits) coarse shadow of the **per-orbit** complete invariant.
2. **Λ's unique Source-A place, localized.** The Γ-multiplier `a(z)=z` has `div(z)=[0]−[∞]`; on the finite
   orbit `O₀=0+ℤ=ℤ` the only finite zero/pole is the simple zero at `0`, so `deg_{O₀}(z)=+1≠0` — **non-CC,
   with the imbalance localized to the single orbit `ℤ`**. Every prime lane is CC (constant multiplier:
   `div = 0` on every finite orbit; or the Euler factor `(1-x)/(1-qx)`, a pure coboundary). So among the
   places of `Λ`, the archimedean place is the **unique** σ-orbit-*unbalanced* (Source-A) place, and the
   imbalance is concentrated on one orbit — a sharp, computable witness for the seam.
3. **`q`-difference (prime-lane) analog.** For `σ_q:x↦qx` (`q=p^{-1}`, not a root of unity), orbits are the
   multiplicative cosets `q^{ℤ}·β`; the identical argument gives **`a` is CC ⟺ `div(a)` has degree 0 on every
   `q`-orbit**. Constant multipliers and the Euler coboundaries satisfy it trivially — Source B is orbit-
   balanced on every multiplicative orbit, confirming per-lane holonomicity from the invariant side.

## The weld localization (where C5 lives, now sharpened)

The complete invariant makes the Source-A/B split a clean dichotomy of *places by one computable number per
orbit*. Hence the keystone weld is exactly:
> **C5 = a theorem coupling the single σ-orbit-unbalanced (non-CC, archimedean) lane to the orbit-balanced
> (CC, prime) lanes, jointly and irreducibly** — `{the one non-CC place} × {the CC places}`, welded by the FE.
The seam / corank-`∞−1` gap / missing-single-Frobenius are three readings of this single orbit-imbalance:
over `F_q` **every** place is a Frobenius power (constant multiplier) ⟹ **all orbit-balanced** ⟹ no Source-A
place ⟹ no weld (corank 1, holonomic, Weil). The "missing single Frobenius" over ℚ **is** the missing
orbit-balancing of the archimedean lane.

## Door passport — BRIDGE
- **Door-2 (master key): FAILS → BRIDGE.** The orbit-balance criterion is the classical rational
  shift-summability / Abramov coboundary condition (divisor form). Stripped of the multi-`q` words it is
  difference algebra + divisor bookkeeping — a single parent. The *organizing payload* (one invariant = the
  archimedean/prime divide; the unique Source-A place localized) is the new content, but it classifies the
  borders — not a joint-`σ_p` weld theorem. BRIDGE, like the companion dichotomy and §59/§60.
- **Door-4:** lives at the borders (Source A = differential Galois; Source B = decoupling), defining the zone
  the weld sits between — not in the weld itself.
- **Door-5:** ✓ over `F_q` all places are orbit-balanced (constant Frobenius multipliers) ⟹ holonomic/Weil;
  predicts the `corank` 1 vs ∞ split (#121). The invariant is the discriminating quantity.

## What is proved here vs imported
- **PROVED HERE:** the complete σ-orbit-balance criterion (both directions + decidability); the recovery of
  the degree-∞ test as its total shadow; the localization of `Λ`'s unique Source-A place to the orbit `ℤ`;
  the `q`-orbit analog for the prime lanes; the weld localization `{one non-CC}×{CC}`.
- **IMPORT:** non-CC ⟹ hypertranscendental (Hölder 1887 for `Γ`; ADH/Hardouin–Singer general) — via the
  companion card. The orbit-balance condition itself is the classical Abramov criterion (cited).

## Gates
- [x] 0 → 1  in-progress: two-source decomposition + multiplier dichotomy stated; Source A = border,
  Source B = BRIDGE, weld = native pinned; Door passport; G1 re-reading (companion card).
- [x] 1 → 2  fully-proven: the **complete** CC-invariant (per-σ-orbit degree-0 balance) proved (both
  directions, decidable); degree-∞ recovered as its shadow; `Λ`'s unique Source-A place localized to orbit
  `ℤ`; `q`-orbit analog; weld localized as `{one non-CC}×{CC}`. **Grade BRIDGE.**
- [ ] 2 → 3  formalized: Lean anchor **DONE** for the finite augmentation-kernel core:
  `orbitDegree_zero`, `orbitDegree_single`, `orbitDegree_add`, and `orbitDegree_sub` provide the finite
  orbit-degree algebra; `orbitDegree_single_sub_single` proves balanced point-masses have orbit degree zero;
  `eq_sum_single_sub_base_of_orbitDegree_zero` proves that any integer-valued finitely supported orbit
  divisor of degree zero decomposes as a finite sum of balanced point-masses against a base point; and
  `orbitDegree_intShiftCoboundary` proves the consecutive-shift coboundary half `im(Δ) ⊆ ker(deg)` on the
  integer orbit. `sum_intShiftTerm_right` proves a concrete reverse-telescoping fragment:
  `n[base+k]-n[base]` is a finite sum of consecutive shift differences. Remaining Lean targets:
  rational-function divisor/orbit infrastructure; assembling arbitrary integer-orbit degree-zero divisors
  into consecutive shifts; the CC equivalence for `ℂ(z)^×`; the `q`-orbit analog; and the marked
  Hölder/ADH hypertranscendence import.
- [ ] 3 → 4  publication-ready: "the σ-orbit-balance invariant: a decidable classifier of the two sources of
  hypertranscendence and the location of the keystone weld."

## Cross-references
- `../2-fully-proven/multiplier-dichotomy-theorem.md` — the companion sufficient dichotomy this card completes
  (degree-∞ ⊂ per-orbit).
- `../../00-core-vision.md`, `../../00-charter-wall-and-door.md` §2/§3/§5 — the re-centered vision/charter.
- `../../door/bucket-archimedean-generator.md`, `archimedean-prime-cross-term.md` (Professor) — the weld's
  concrete object the localization points to. **Coordinate; do not duplicate.**
- `../2-fully-proven/function-field-holonomicity-degeneration.md` (#121) — the all-orbit-balanced `F_q`
  degeneration the Door-5 shadow recovers.

## Log
- 2026-06-19 — created in 0-backlog as the foundational framing of the Hölder-recentering.
- 2026-06-19 — DeWitt: pulled to in-progress; **proved → 2-fully-proven (BRIDGE)**. Banked the **complete**
  CC-invariant: `a` is constant×shift-coboundary ⟺ `div(a)` is σ-orbit-balanced (`deg_O=0 ∀O`), both
  directions + decidability (the rational shift-summability/Abramov criterion in divisor form). Strengthens
  the companion card's sufficient degree-∞ obstruction (recovered as the summed-over-orbits shadow). Localized
  `Λ`'s unique Source-A place to the single orbit `ℤ` of the Γ-multiplier `div(z)=[0]−[∞]` (`deg_ℤ=+1≠0`);
  every prime lane orbit-balanced (`q`-orbit analog). Weld localized as `{the one non-CC place}×{the CC
  places}`; seam/corank-`∞−1`/missing-Frobenius = the archimedean orbit-imbalance, vanishing over `F_q`
  (all-balanced). No runpod (exact divisor algebra). Library ticket filed.
- 2026-06-19 (Leaner) — added Lean anchors `orbitDegree_single_sub_single` and
  `eq_sum_single_sub_base_of_orbitDegree_zero` in `formal/GaloisForLFunctions/OrbitBalance.lean`. These
  formalize the finite augmentation-kernel core of the σ-orbit-balance proof: balanced point-masses have
  orbit degree zero, and every integer-valued finitely supported orbit divisor of degree zero decomposes as a
  finite sum of balanced point-masses against any chosen base point. Added the module to the root import and
  axiom audit; `cd formal && lake env lean GaloisForLFunctions/OrbitBalance.lean`, `cd formal && lake build`,
  and `bash scripts/check_axioms.sh` pass with 254 audited theorem outputs and no `sorry`. Card remains in
  `2-fully-proven`; the rational-function divisor/orbit layer, consecutive shift-telescoping, full CC
  equivalence, `q`-orbit analog, and Hölder/ADH import are not fully Lean-formalized.
- 2026-06-19 (Leaner) — extended `formal/GaloisForLFunctions/OrbitBalance.lean` with the orbit-degree
  algebra (`orbitDegree_zero`, `orbitDegree_single`, `orbitDegree_add`, `orbitDegree_sub`) and the
  consecutive-shift coboundary theorem `orbitDegree_intShiftCoboundary`. This proves the formal
  `im(Δ) ⊆ ker(deg)` half on the integer orbit: every finite sum of consecutive differences `[z-1]-[z]`
  has orbit degree zero. `cd formal && lake env lean GaloisForLFunctions/OrbitBalance.lean`,
  `cd formal && lake build`, and `bash scripts/check_axioms.sh` pass with 259 audited theorem outputs and no
  `sorry`. The reverse telescoping inclusion, rational divisor/orbit infrastructure, full CC equivalence,
  `q`-orbit analog, and Hölder/ADH import remain unformalized.
- 2026-06-19 (Leaner) — added `sum_intShiftTerm_right` to
  `formal/GaloisForLFunctions/OrbitBalance.lean`, proving the explicit right-path telescoping identity
  `n[base+k]-n[base] = Σ_{j<k} (−n)([base+j]-[base+j+1])` in the integer-orbit divisor model. This is a
  concrete reverse-telescoping fragment of `ker(deg) ⊆ im(Δ)`. `cd formal && lake env lean
  GaloisForLFunctions/OrbitBalance.lean`, `cd formal && lake build`, and `bash scripts/check_axioms.sh` pass
  with 260 audited theorem outputs and no `sorry`. The arbitrary divisor assembly, rational-function divisor
  layer, full CC equivalence, `q`-orbit analog, and Hölder/ADH import remain unformalized.
