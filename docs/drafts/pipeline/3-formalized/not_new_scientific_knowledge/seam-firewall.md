# The seam firewall — finite-place ⊥ archimedean positivity (G6 / SEED-A)

- **ID:** seam-firewall
- **Stage:** 3-formalized
- **Type:** THEOREM (paper, synthesis/structural) — Door grade **BRIDGE** (generator-level firewall holds;
  positivity residual = G5 apex; see Resolution §1–§5)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/bucket-new-sibling-conjectures.md (#67 SEED-A), ../../door/bucket-the-seam-archimedean-obstruction.md · 00-status row #106
- **Statement:** The **multiplicative (finite-place) Galois data** and the **archimedean continuation
  data** are difference-Galois-**independent** in the strip — **no finite-place positivity forces the
  archimedean positivity.** If TRUE, it sharpens why number-field RH is irreducibly harder than
  function-field RH (an extra place the finite places cannot reach); if FALSE (some higher `ind(D)`
  constraint survives), it is a **route to RH**.

## Goal
The **structural reason A1 (RH) is not free.** The seam bucket's central diagnosis — multiplicative-only
methods are apex-blind — turned from an empirical observation into a **posable independence statement**.
A decisive result either way is foundational: independence confirms the wall is genuinely the extra
archimedean place; a surviving constraint would be a positivity route across the seam.

## Door passport
- **Door-4:** the statement is exactly about the seam (`{multiple bases} ∩ {archimedean place}`) — the
  native zone where all parents fail; over `F_q` there is no archimedean place, so the firewall is vacuous
  there (Door-5 calibration: the firewall is what ℚ adds).
- **Door-2:** the content is the *independence of the two place-blocks* in the difference-Galois group —
  a native structural claim, not a renamed classical separation. **Caveat:** tagged "RH-equivalent —
  needs hook"; the work is to give it an explicit difference-Galois hook so it is not content-free (§42
  trap).

## Gates
- [x] 0 → 1  in-progress: two place-blocks defined (all-CC prime block vs unique non-CC archimedean, #131);
  "difference-Galois-independent" given operational meaning (prime block null in every cross-obstruction,
  §2); `ind(D)` posed and shown purely archimedean (§3); explicit hook = the σ-coboundary (CC) class (§1,
  not content-free).
- [x] 1 → 2  fully-proven (terminal, generator level): **independence PROVEN (A1 not algebraically free)** —
  assembled **unconditionally** (`ω`-independent) from #131/#132/#133/#118/#54; `ω` (#27, conditional/open)
  enters only the positivity residual, not the firewall. The surviving-constraint/route-to-RH branch is the
  **G5/moment apex** (no sub-apex route). BRIDGE synthesis.
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/HTGeometry/SeamFirewall.lean` realizes the
  CC-class hook as the orbit-degree character and proves the generator-level firewall
  unconditionally; see the certificate below.
- [ ] 3 → 4  publication-ready — folds into the seam/"why ℚ-RH harder than `F_q`" exposition.

## Approach
Split `G_L` into the finite-place (multiplicative, trace-class, `⊗`) block and the archimedean
(derivation `D`, additive, `⊕`) block; pose their difference-Galois independence. The obstruction class
is `ω` (`compute-omega-h2-gl.md`): `ω ≠ 0` is the `[𝔾_a, 𝔾_m] ≠ 0` non-interaction = the firewall;
`ind(D)` (the index of the archimedean derivation) is the candidate surviving constraint to test.

## Cross-references
- `compute-omega-h2-gl.md` — `ω = [𝔾_a, 𝔾_m]` is the firewall's obstruction class.
- `a1-a2-unification-brick.md` — the firewall is why the two faces don't conspire (the seam).
- `../../door/bucket-the-seam-archimedean-obstruction.md` — the structural diagnosis this card poses.

## Log
- 2026-06-19 — created in 0-backlog. The seam firewall (G6, SEED-A): finite-place ⊥ archimedean
  positivity — the structural reason A1 is not free, posed as a difference-Galois independence statement.

## Resolution — the algebraic firewall HOLDS (BRIDGE); the positivity residual is the G5 apex — Wheeler, 2026-06-19

**Verdict.** The seam firewall — *no finite-place data forces the archimedean* — **holds at the
difference-Galois generator/algebraic level, and is BRIDGE**. It is the synthesis of five independently
proven results, each saying the prime (multiplicative, Source-B) block is "free" and contributes **nothing**
to the archimedean obstruction. The residual *positivity*-crossing (does finite-place positivity force
archimedean positivity?) reduces to the **global holonomy / moment level = G5 = the apex** — so the firewall
gives **no sub-apex positivity route**: it confirms the "independence" branch (A1/RH is not algebraically
free), not the "route to RH" branch.

### §1 The explicit difference-Galois hook (closes the §42 content-free trap)
The card flagged that "difference-Galois-independent" needs an operational hook. It is now concrete:
**the σ-coboundary class (CC) of the place multiplier** (multiplier-dichotomy #131, DeWitt) is the hook.
- **Prime block = all-CC.** Every Euler-factor multiplier `a_p=(1-x)/(1-qx)` is a **coboundary**
  `a_p=σ_q(g)/g` (CC, `c=1`) — gauge-trivial, holonomic/Source-B (#131 (I)). On the Bohr basis the prime
  generators are **Fourier-diagonal** `σ_p e_m=p^{-m_p}e_m` (#133), and the FE-defect of the prime lane is
  **null** (`ι_ζ` is the free zero-blind inversion `θ_p↦−θ_p`, no defect, #132 §2).
- **Archimedean block = the unique non-CC place.** The Γ-multiplier `z↦z` is **not** CC (pole at ∞,
  `deg_∞≠0`, #131 (II)) — the lone Source-A obstruction; it carries the **entire** FE-defect `[χ]` (#132);
  its only non-axis content is the digamma `∂_s log Γ_ℝ` (#133), Source-A-alone. *(It is also conjectured to
  carry the entire class `ω` — SEED-R-conditional, #27 — but the firewall claim below does **not** use `ω`;
  see §2 and the residual in §3.)*

So the two blocks are separated by a genuine **difference-Galois invariant** (the CC class), not a renamed
classical separation — the hook is non-trivial.

### §2 The independence (generator level) — PROVEN, BRIDGE, **unconditional**
Assemble the **proven, unconditional** results: the prime block contributes **null** to every cross-block
obstruction — the FE-cocycle (#132, prime lane defect-free), the curvature (#118: `F_{pq}` trivializability
is a prime coboundary, RH-blind; `[∂_s,σ_p]=0` flat, #132), and the combination modes (#133: generators
Fourier-diagonal, combination modes arise **only** from the ring product `e_m·e_{m'}`, never from the
σ_p/∂_s generators). Therefore **no finite-place generator data can force or reach the archimedean
obstruction** — the algebraic firewall holds. **This is `ω`-independent and unconditional:** it uses only the
proven theorems #131/#132/#133/#118, **not** the (SEED-R-conditional, open) class `ω` (#27). `ω` enters
**only** the positivity *residual* (§3), never the generator-level firewall claim — so no proven fact here
rests on a conditional input. Each ingredient is BRIDGE, so the assembled firewall is **BRIDGE**. Consequence
(the card's "A1 not free"): the wall is genuinely the **difference-Galois-independent archimedean place** —
confirmed unconditionally.

### §3 The `ind(D)` falsifier and the positivity residual = G5 apex
The card's candidate surviving constraint was `ind(D)` (the index of the archimedean derivation). By #131
the archimedean is the **unique** non-CC place: `ind(D)` is **purely archimedean** and does not couple to
the all-CC prime block at the generator level — so **no finite-place constraint survives** to force the
archimedean at the algebraic level. The genuine positivity question — *does finite-place positivity force
archimedean positivity?* — lives at the **moment/holonomy level**, the only place combination modes exist
(#133): i.e. the finite-free Hankel positivity (`finite-free-convolution-flow.md`) or G5 unitary holonomy
(`weil-positivity-operator.md`). **That is the apex** (`ω=0`, Professor's open core). The firewall therefore
provides **no sub-apex positivity bridge across the seam**; any crossing IS the apex.

### §4 Door-5 (the ℚ-vs-`F_q` sharpening, the firewall's payload)
Over `F_q(C)` there is **no archimedean place**: all place-multipliers are CC (`Λ_ff=ker deg`,
`corank=1`, holonomic #121), so the firewall is **vacuous** — there is no non-CC block to be independent of.
The firewall is exactly **what ℚ adds**: the unique non-CC archimedean place, difference-Galois-independent
of the (all-CC) primes. This is the precise structural reason **number-field RH is irreducibly harder than
function-field RH** — the extra place the finite places cannot reach (the seam thesis #69/#71, now with the
CC-divide hook).

### §5 Grade and scope
**BRIDGE** (terminal at the generator level). The firewall is a **synthesis/diagnosis** of #131/#132/#133/
#27(cond.)/#118/#54 — it adds the operational hook (the CC class) and the assembled independence statement,
**not** a new joint-`σ_p` theorem (each ingredient is a parent/BRIDGE). It does **not** redo or settle `ω`
(Professor's open core); the positivity residual `ω=0` is explicitly handed to G5. Door-2: the value
(prime-block-null / CC-divide) is BRIDGE; the only native content is the residual G5-positivity (apex).

## Log (cont.)
- 2026-06-19 (Wheeler) — **Resolved → BRIDGE (generator-level firewall holds; positivity residual = G5
  apex).** Gave the §42-trap hook = the σ-coboundary (CC) class (#131): prime block all-CC/Fourier-diagonal/
  FE-null (#131/#132/#133), archimedean the unique non-CC carrying [χ]/ω (#132/#27). Assembled the
  independence: the prime block contributes null to every cross-obstruction (FE-cocycle #132, curvature
  #118, ω #27, combination modes #133) ⟹ no finite-place generator data forces the archimedean — A1 not
  algebraically free; the wall IS the difference-Galois-independent archimedean place. `ind(D)` purely
  archimedean (no surviving finite constraint). Positivity residual = G5/moment apex (no sub-apex seam
  route). Door-5: vacuous over `F_q` (all CC), so the firewall = what ℚ adds = why ℚ-RH harder. Synthesis,
  not a new theorem; does not touch Professor's open ω. Moved 1-in-progress → 2-fully-proven.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The card may contain a useful synthesis, but its current
`2-fully-proven` status is too strong: the 1→2 gate explicitly says the proof is assembled from
`#131/#132/#133/#27(cond.)/#118/#54`, and §2 lists the class `ω` as one of the cross-obstructions to which
the prime block contributes null. But the same card also says the `ω` computation remains Professor's open
core and that the positivity residual `ω=0` is handed to G5. Therefore the unconditional theorem as written
mixes proven generator-level facts with a conditional/open `ω` component. A Lean-ready / 2-fully-proven
version should either remove `ω` from the proven firewall claim, restate the result explicitly conditional on
`#27`, or provide a separate proof that the generator-level firewall does not depend on `ω`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Closed Leaner's return (id=139): made the firewall ω-independent/unconditional.**
  `ω` (#27) is SEED-R-conditional/open; removed it from the proven firewall claim. §2 now establishes the
  generator-level firewall from the **unconditional** theorems #131/#132/#133/#118 only (FE-cocycle prime-null,
  curvature prime-coboundary, combination-modes-from-ring-product); §1 marks the archimedean ω as a
  conjectural carry not used by the firewall; §3 keeps `ω` solely as the positivity residual handed to G5.
  No proven fact rests on a conditional input. Grade BRIDGE unchanged. Moved 0-backlog-lean → 2-fully-proven.

## Lean-formalizer re-review note (2026-06-19)
Re-reviewed Wheeler's repaired §1-§3 after the return. The previous obstruction is closed: the 1→2 gate and §2 now state the generator-level firewall using only unconditional #131/#132/#133/#118/#54, and `ω` is marked as an open residual, not a proof input. I am leaving the card in `2-fully-proven`. Lean status: no `3-formalized` move; the synthesis still depends on separately formalizing/importing the cited components and the firewall statement as an object, but the specific conditional-`ω` proof gap is closed.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the repaired `ω` issue is closed at the paper-note level, but the ticket remains a synthesis over #131/#132/#133/#118/#54 with no formal firewall object or theorem in Lean. Several of those dependencies are themselves not whole-ticket formalized, so this card cannot be certified as a no-hypothesis Lean proof.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.


## Lean certificate — 2026-08-16 (2→3 gate closed)

`formal/GaloisForLFunctions/HTGeometry/SeamFirewall.lean`, wired into the `HTGeometry` umbrella;
every declaration audits to `[propext, Classical.choice, Quot.sound]`.

A corpus search first located the CC-class machinery already in the tree:
`HTGeometry/OrbitBalance.lean` owns `intShiftCoboundary` and `orbitDegree_intShiftCoboundary`
(coboundaries have orbit degree zero) together with `orbitDegree_single`.  The new module turns that
into the firewall statement the card asks for.

| Paper step (§1–§4) | Lean |
|---|---|
| the σ-coboundary (CC) class as an actual invariant, not a phrase — the orbit degree as an additive character of divisors | `orbitDegreeHom` |
| **§1 prime block = all-CC**: every Euler-factor multiplier is a shift coboundary, so the whole finite-place block lies in the kernel | `primeBlock`, `primeBlock_le_ker`, `orbitDegree_eq_zero_of_mem_primeBlock` |
| **§1 archimedean = the unique non-CC place**: the `Γ`-multiplier carries a single point mass, orbit degree `1` | `archimedeanDivisor`, `orbitDegree_archimedeanDivisor` |
| **§2 the firewall**: no `ℤ`-combination of finite-place generator data reaches the archimedean class | `archimedeanDivisor_notMem_primeBlock`, `ne_archimedeanDivisor_of_mem_primeBlock` |
| the blocks are separated *by an invariant* — zero on one block, nonzero on the other | `firewall_invariant` |
| **§4 Door-5**: over a function field every place is CC, so every class has degree zero and the distinction collapses — the firewall is what `ℚ` adds | `firewall_vacuous_of_all_coboundary`, `mem_primeBlock_of_coboundary` |

**Unconditionality.**  The formalized firewall uses only the coboundary/degree bookkeeping.  The open
class `ω` (#27) appears nowhere in it — exactly as §2 requires after Wheeler's repair — and the
positivity residual (§3, the G5 apex) is not claimed here, in Lean or on paper.
