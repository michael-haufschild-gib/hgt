# Holonomicity is not closed under the border inverse limit (BRIDGE structural theorem; C7-native ⟺ C5★)

- **ID:** holonomicity-limit-nonclosure
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** arose from C6 §1 Theorem B (`../2-fully-proven/c6-specialization-functors.md`); couples to
  C7 (`../0-backlog/c7-autonomy-foundational-core.md`) and G3
  (`../2-fully-proven/G3-corank-dichotomy.md`); 00-status rows #20, #48, #119
- **Statement.** The finite-base border functors `{S_T : 𝓜 → 𝓓_T}_{T ⊂ P finite}` (C6 §1) **do not
  detect holonomicity**. Precisely, for a diagonal `M ∈ 𝓜` with `M = lim_T S_T(M)`:
  > **(Dichotomy)** `M` is holonomic ⟺ `corank(Λ_M) < ∞` ⟺ the corank sequence
  > `c_T := corank(Λ_{S_T M})` **stabilizes** along the prime tower (eventually constant on a cofinal
  > up-set), while **every** finite truncation `S_T(M)` is holonomic (`c_T ≤ |T| < ∞`).
  >
  > **(Autonomy corollary)** The comparison functor `𝓜 → lim_T 𝓓_T`, `M ↦ (S_T M)_T`, **does not
  > reflect holonomicity**: `M_ζ` has every `S_T(M_ζ)` holonomic yet `M_ζ` non-holonomic (G1). Hence the
  > holonomic structure of `𝓜` is **not** assembled from the borders — `𝓜 ≠ lim_T 𝓓_T` at the level of
  > the holonomic subcategory; the simultaneity of the `σ_p` is irreducible categorical content.

  **Door grade BRIDGE** (every load-bearing step is a parent or an already-BRIDGE result). **C7 verdict:**
  this closes only the *bridge-level* half of autonomy; **native autonomy ⟺ C5★** (see §7).

---

## §1 The inverse system (setup)

Notation as in C6 §0. `R = ℂ[x_p^{±1} : p ∈ P]`, `Φ_p = A_p σ_p`, flat. A **diagonal** `M` is determined
(up to the data G3 sees) by its multiplier tuple `g = g(M) = (g_p)_p` in the pro-torus
`𝕋 := (ℂ^×)^{(P)}` — the arithmetic monodromy point whose `⟨g⟩`-closure G3 measures. Its **relation
lattice** is
```
   Λ_M = { m ∈ ℤ^{(P)} : ∏_p g_p^{m_p} = 1 }  ⊂ ℤ^{(P)}   (finitely supported integer vectors).
```
For the arithmetic object `M_ζ`, `g_p = q_p = 1/p`, so `Λ_{M_ζ} = { m : ∑_p m_p log p = 0 } = {0}` by
ℚ-linear independence of `{log p}` (unique factorization; ledger `linearIndependent_log_primes`).

**The border functor on lattices.** `S_T` forgets `σ_q` (`q ∉ T`) and freezes `x_q ↦ c_q`; the multiplier
tuple of `S_T(M)` is `g_T = (g_p)_{p∈T} ∈ (ℂ^×)^T`. A relation supported on `T` is a relation of `g` iff
it is a relation of `g_T`, so
```
   Λ_{S_T M} = Λ_M ∩ ℤ^T,        c_T := corank(Λ_{S_T M}) = |T| − rank(Λ_M ∩ ℤ^T).
```
`corank` at any base = `dim` of the multiplier-closure (G3: `dim⟨g⟩-closure = corank(Λ)`); intrinsically
`corank(Λ_M) = rank( ℤ^{(P)} / Λ_M )` (the rank of the character lattice of the closure).

The transition maps `ℤ^T ↪ ℤ^{T'}` (`T ⊂ T'`) make `T ↦ Λ_M ∩ ℤ^T` a directed system with union `Λ_M`
(`ℤ^{(P)} = ⋃_T ℤ^T`, directed); `M = lim_T S_T(M)` is the corresponding limit of modules.

## §2 Lemma 1 — corank is monotone and passes to the limit as a sup `[PROVED HERE]`

**Claim.** `c_T` is non-decreasing in `T`, and `corank(Λ_M) = sup_T c_T`.

*Proof.* (Monotone) For `T ⊂ T'` with `|T'| − |T| = k`: the quotient `ℤ^{T'}/ℤ^T ≅ ℤ^k` has rank `k`, and
`Λ_M ∩ ℤ^T ⊆ Λ_M ∩ ℤ^{T'}`, so `0 ≤ rank(Λ_M∩ℤ^{T'}) − rank(Λ_M∩ℤ^T) ≤ k`. Hence
`c_{T'} − c_T = k − Δrank ∈ [0,k] ≥ 0`. (Limit) `ℤ^{(P)}/Λ_M = ⋃_T (ℤ^T + Λ_M)/Λ_M`, a directed union,
and rank of a directed union of free-abelian quotients is the sup of the ranks of the pieces:
`rank(ℤ^{(P)}/Λ_M) = sup_T rank(ℤ^T/(Λ_M∩ℤ^T)) = sup_T (|T|−rank(Λ_M∩ℤ^T)) = sup_T c_T`. ∎

**Corollary (stabilization = finiteness).** `corank(Λ_M) < ∞ ⟺ (c_T)` is eventually constant: if
`sup c_T = c^* < ∞` it is attained at some `T_0` (integer-valued, bounded, monotone), and by monotonicity
`c_T = c^*` for all `T ⊇ T_0`; conversely eventual constancy gives finite sup. ∎

## §3 Lemma 2 — every finite truncation is holonomic `[PROVED HERE]`

**Claim.** For every finite `T`, `S_T(M)` is holonomic.

*Proof.* `c_T = corank(Λ_{S_T M}) ≤ |T| < ∞`, so G3's `(⟸)` direction (corank `< ∞ ⟹` holonomic; the
diagonal of a `D`-finite/rational series over finitely many variables is `D`-finite, Lipshitz 1988 +
§49.2) applies. ∎ *(For `M_ζ` this is concrete: `S_T(M_ζ) = ∏_{p∈T}(1−x_p)^{-1}`, rational, holonomic —
C6 Thm B.)*

## §4 Theorem (the functorial dichotomy) `[PROVED HERE]`

`M` holonomic `⟺` `corank(Λ_M) < ∞` (G3, all bases) `⟺` `sup_T c_T < ∞` (§2) `⟺` `(c_T)` stabilizes
(§2 Cor). Combined with §3 (each `c_T < ∞`): **the holonomicity of the limit is governed entirely by
whether the corank growth halts** — every shadow is holonomic, and the only obstruction lives at the
limit. ∎

## §5 Corollary (autonomy / non-reconstruction) `[PROVED HERE]`

Holonomicity is a property in `𝓜` (for `M`) and in each `𝓓_T` (for `S_T M`). The comparison functor
`Φ : 𝓜 → lim_T 𝓓_T`, `M ↦ (S_T M)_T`, is well-defined (the `S_T` form a compatible cone). **Φ does not
reflect holonomicity:** take `M_ζ`. Each `S_T(M_ζ)` is holonomic (§3), so the image `(S_T M_ζ)_T` is
"holonomic at every stage," yet `M_ζ` is non-holonomic — `c_T = |T| ↗ ∞`, `Λ_{M_ζ} = {0}`,
`corank = ∞` (G1/§59). Therefore the holonomic subcategory of `𝓜` is **not** the limit of the holonomic
subcategories of the `𝓓_T`: `𝓜 ≠ lim_T 𝓓_T` as far as holonomic structure is concerned. The
finite-base borders cannot pose, let alone detect, the jump; **simultaneity of the `σ_p` is irreducible
categorical content**, not reconstructible from the one-direction-at-a-time shadows. ∎

## §6 Door grade — BRIDGE `[verdict]`

Strip the multi-`q` vocabulary and audit each load-bearing step:
- **Lemma 1** is pure abelian-group/lattice theory (`rank(ℤ^{(∞)}/Λ) = sup_T rank` of finite slices) —
  commutative algebra proves it.
- **Lemma 2 / §4** rest on **G3**, which is **BRIDGE** (its `(⟸)` is the Lipshitz import; its invariant
  `corank` is a torus-closure dimension — a renamed algebraic-group invariant, also failing **Door-3**).
- **§5's witness** is `M_ζ` non-holonomic = **G1/§59**, graded **BRIDGE** (Door-2: single-operator
  difference Galois + Kronecker–Weyl on `𝕋^∞` + unique factorization).

No step uses the `σ_p` **jointly and irreducibly**. ⟹ **BRIDGE**, not NATIVE — as the opening card
predicted. It is *not* a pure G3-reframing, though: the monotonicity/limit lemma (§2) and the categorical
non-reconstruction (§5) are content **about the functor family**, absent from the single-object G3
dichotomy. So it banks as a genuine **proved BRIDGE structural theorem**, not a §42-style relabel.

## §7 C7 verdict — bridge-level only; **native autonomy ⟺ C5★**

C7's test (charter): *a foundational core stands "without constant appeal to a parent."* The C7 card
sharpens this correctly: **the flagship structural theorem must itself survive Door-2, else the autonomy
is illusory** — a BRIDGE flagship merely re-derives what a parent already proves. This theorem's every
load-bearing step is a parent or a BRIDGE result (§6), so:

- ✅ It closes the **cheap half** of autonomy: from the field's own definitions (the `σ_p`-family, the
  relation lattice, the border functors) the category **provably exceeds the limit of its borders**
  (`𝓜 ≠ lim 𝓓_T`). The borders do not reconstruct the interior — a real, proven autonomy statement.
- ❌ It does **not** close C7: the proof leans on parents at every step, so the demonstrated autonomy is
  the "illusory" kind the C7 card warns against. A C7-closing flagship must use the `σ_p` jointly and
  irreducibly — i.e. survive Door-2.

**The structural finding (conjecture, pushed forward).** `C7-native ⟺ C5★`, mirroring the **proven**
`C3-native ⟺ C5★` (`../2-fully-proven/c3-gluing-invariants-bridge.md`). Every structural statement
provable from the definitions *alone* turns out BRIDGE (assembled from lattice theory + G1 + unique
factorization); the *native* residue of autonomy is exactly the irreducible joint-`σ_p` content of C5.
With C6 already MET-at-bridge / native-extension = C5★, the three open non-C5 criteria **collapse onto a
single theorem**:
```
   C3-native ⟺ C5★   (proven)
   C6-native ⟺ C5★   (proven: c6-specialization-functors §4)
   C7-native ⟺ C5★   (this card, conjectural)
```
⟹ **the proto-branch's entire remaining gap to branchhood is C5★.** Earning the one irreducible
joint-`σ_p` theorem closes C3, C6 (native), and C7 together. This sharpens "C5 is the keystone" into
"C5 is the *only* remaining lock."

## Gates
- [x] 0 → 1  in-progress: inverse system + functorial G3 restatement pinned; characterization sharpened;
  Door passport sketched; C7 coupling stated.
- [x] 1 → 2  fully-proven: dichotomy proven (§4, via the new monotonicity Lemma 1 + G3); the
  `𝓜 ≠ lim 𝓓_T` non-reconstruction proven (§5, comparison functor does not reflect holonomicity); Door
  grade decided (**BRIDGE**, §6); C7 fed with a definite verdict (bridge-level only; **C7-native ⟺ C5★**,
  §7). Not a G3-reframe (§2, §5 are new functor-family content) ⟹ banked, not failed.
- [ ] 2 → 3  formalized — Lean targets: Lemma 1 monotonicity `c_T ≤ c_{T'}` and
  `corank(Λ_M)=sup_T c_T` over the directed `ℤ^T`-system; the `M_ζ` witness slices
  (`finitePrimeLogAnnihilator_eq_singleton`, `linearIndependent_log_primes`, both ledgered). The new
  fragment is the directed-sup corank identity. Lean anchor **DONE** for the integer-valued stabilization
  corollary: `monotoneNat_eventually_constant_of_bddAbove` in
  `formal/GaloisForLFunctions/HolonomicityLimit.lean` proves that a monotone bounded natural-number
  sequence is eventually constant, matching §2's `sup c_T < ∞ ⟹ c_T` stabilizes step.
- [ ] 3 → 4  publication-ready — standalone note: the inverse system, the two lemmas, the dichotomy, the
  non-reconstruction corollary, the Door/C7 passport.

## Notes / risk
- **Duplication guard (discharged):** the dichotomy alone would be "G3 on a tower"; what makes this a
  result is the **functor-family** content — Lemma 1 (corank as a directed sup, monotone) and §5
  (`𝓜 ≠ lim 𝓓_T`, holonomicity not reflected by the comparison functor) — neither in G3. Had only the
  dichotomy survived, this would have been failed to `5-failed`.
- **C7 coupling outcome:** the card's two-way bet resolved to "C7 needs more than this" — and pinned
  *exactly* what more: a Door-2-surviving (C5★) flagship. The negative is itself the result.

## Log
- 2026-06-19 — created in 0-backlog (from C6 §1 Theorem B). Framed as the functorial/categorical autonomy
  statement, distinguished from single-object G3.
- 2026-06-19 — claimed by Professor; moved 0-backlog → 1-in-progress.
- 2026-06-19 — **fully proven; moved 1-in-progress → 2-fully-proven.** Proved the dichotomy (§4) via the
  new corank-monotonicity/directed-sup Lemma 1 (§2) + G3, and the non-reconstruction corollary
  `𝓜 ≠ lim 𝓓_T` (§5). Door grade **BRIDGE** (§6: every step parent/BRIDGE; no irreducible joint-`σ_p`
  use). C7 verdict (§7): closes bridge-level autonomy only; **native autonomy ⟺ C5★**, giving the
  three-criteria collapse `C3,C6,C7 native ⟺ C5★` (the remaining gap to branchhood is the single theorem
  C5★). Not a G3-reframe (Lemma 1 + §5 are new functor-family content) ⟹ banked to 2-fully-proven, not
  failed.
- 2026-06-19 (Leaner) — added Lean anchor for the §2 stabilization corollary:
  `monotoneNat_eventually_constant_of_bddAbove` in `formal/GaloisForLFunctions/HolonomicityLimit.lean`.
  It proves that a monotone bounded natural-number sequence is eventually constant, the integer-valued step
  used after the directed-sup corank identity. Added the module to the root import and axiom audit; `lake build`
  and `scripts/check_axioms.sh` pass with 248 audited theorem outputs and no `sorry`. Card remains in
  `2-fully-proven`; the directed-sup corank identity, G3 holonomicity implication, and comparison-functor
  non-reconstruction theorem are not fully formalized.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the Lean anchor proves only monotone bounded natural sequences eventually stabilize. The whole theorem needs the directed-sup corank identity, G3 holonomicity equivalence, G1 non-holonomic witness, and comparison-functor non-reconstruction statement. Those dependencies are not Lean-formalized.
