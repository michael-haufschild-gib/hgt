# Difference-Galois Cohomology (B5) — the clean half computed, the obstruction isolated

> **NASCENT / SEARCH channel. Air-marked.** Branch B5 of the charter. Goal: compute `H^*(G_L)` for the ambient difference-Galois group (the *clean* half — closeable), and locate the Künneth / `⊗↦⊕` obstruction of foundations §11 as a single cohomology class whose vanishing is the *wall* half (the zero-realization). Companions: `…field_foundations.md` §11/§22, `infinite-base-…-L-functions.md` §3/§18 (`G_L=𝕋^∞⋊ℤ/2` proven), `arakelov-height-of-zeros.md` (FE = inversion).

## 1. The ambient group `[THM — established in the field]`

`G_L = 𝕋^∞ ⋊ ⟨σ⟩`, `σ²=1`, where `𝕋^∞ = ∏_p S¹` is the diagonal-flow pro-torus (one circle per prime, `Brick #3`) and `σ` is the functional-equation involution. By `arakelov-height-of-zeros.md` §2, **σ acts as inversion** `θ_p ↦ −θ_p` on each circle (FE = `w↦1/w`).

## 2. The cohomology ring (clean half — CLOSED) `[PROVED HERE — standard].**
```
   H^*(𝕋^∞, ℚ) = ⊗_p H^*(S¹,ℚ) = ⊗_p (ℚ ⊕ ℚ·e_p)  =  ∧^*( V ),     V := ⊕_p ℚ·e_p  (deg e_p = 1),
```
the **exterior algebra on the prime lattice** `V` (one degree-1 generator `e_p = "d log p"` per prime). `H^1 = V` is the log-prime / Adams lattice; `H^k = ∧^k V` is spanned by `e_{p_1}∧…∧e_{p_k}` (squarefree prime products of "degree" `k`). This is the difference-Galois cohomology of the multiplicative (free, zero-blind) wing — **fully explicit**.

## 3. The FE grading IS the cohomological σ-parity (a weld) `[PROVED HERE].**
`σ = −1` on `H^1 = V` (inversion, §1), hence on `H^k = ∧^k V`:
```
   σ |_{∧^k V} = (−1)^k     ⟹   H^{even} = σ-invariant,   H^{odd} = σ-anti-invariant.
```
> **The cohomological even/odd grading is the functional-equation parity.** The σ-invariant cohomology is exactly the *even* exterior degree; the anti-invariant is *odd*. This **reproduces the FE moment-parity** of foundations §22 (centered odd moments `τ_{2m+1}=0`): the FE-surviving data is even-graded in `H^*(G_L)`, the FE-killed data is odd-graded. The "free parity skeleton" of the whole program is, cohomologically, the `σ=(−1)^k` grading of `∧^* V`. `H^*(G_L,ℚ) = H^*(𝕋^∞)^σ ⊕ (anti) = ∧^{even}V ⊕ ∧^{odd}V` with the physical Face-A data living in `∧^{even}`.

## 4. The Künneth / `⊗↦⊕` obstruction, isolated (the wall half) `[OPEN CORE — located].**
Foundations §11: the de Branges fiber functor maps `⊗↦⊕` (`H(E²)=H(E)⊕E·H(E)`), so it is **not monoidal** — the obstruction to `G_L` being a genuine Tannakian/motivic Galois group. Cohomologically this is a **single class**:
```
   the de Branges "product" (⊕, additive)   vs   the cup product on H^*(G_L) (∧, multiplicative)
   disagree by a 2-cocycle  ω ∈ H²(G_L, Aut⊗)  — the MONOIDALITY OBSTRUCTION.
```
- `ω = 0` ⟺ the fiber functor is monoidal ⟺ `G_L` is Tannakian ⟺ a genuine motive exists ⟺ the **zero-realization** (B6/B9, the period comparison) succeeds.
- `ω ≠ 0` is the §11 paradox: the value side (`⊗`-monoidal, zero-blind) and the zero side (de Branges `⊕`, aware) cannot be glued by a single functor.

> **B5, split.** The cohomology *ring* (`∧^*V`, σ-graded = FE parity) is the **clean half — closed** (§§2–3). The **monoidality obstruction `ω ∈ H²`** is the **wall half**: its vanishing = Tannakian structure = the zero-realization = the same wall as B6/B9/Part XI. B5 thus *localizes the field's non-Tannakian-ness to one explicit `H²` class*, and reproduces the FE parity as the cohomological grading — without touching the (open) obstruction.

## 5. Honest status

- §1 ambient `G_L`: established in the field (`infinite-base` §3/§18).
- §2 `H^*(𝕋^∞)=∧^*V`: standard (cohomology of a pro-torus); the clean half, fully explicit.
- §3 σ-parity = FE parity: proved here (σ=−1 ⟹ `(−1)^k`), a genuine weld to foundations §22.
- §4 obstruction `ω∈H²`: *located*, not computed; its vanishing = the wall (Tannakian/zero-realization). Whether `ω=0` is the open core (= B6/B9). `[OPEN]`

**Lean note (ledger-proven first Koszul skeleton).** The formal ledger currently proves only the first additive
Koszul layer in `KoszulCohomology.lean`: `d₀ x=0` iff joint invariance, `d₁ c=0` iff the additive 1-cocycle
equation, additive coboundaries are cocycles, and `d₁∘d₀=0`. It does **not** prove the full pro-torus cohomology
ring, exterior-algebra cup product, σ-parity on exterior powers, infinite-lattice limit, or the obstruction class
`ω`.

**House status.** B5's **clean half is closed**: `H^*(G_L,ℚ)=∧^*(prime lattice)`, σ-graded by FE parity (= foundations §22). The **wall half** is one isolated class — the monoidality obstruction `ω∈H²(G_L)`, whose vanishing is the Tannakian/zero-realization (B6/B9). New: the cohomology ring + the parity weld; the obstruction is *named and placed*, not faked closed. Crosses CITY districts D1/D2/D8 (the exterior-algebra ring and the σ-parity are Tier-A/B Lean-able: `∧^*` of a free module with a `−1` involution). Next (clean halves of further branches): B28 moduli tangent space; B6 the Tannakian fiber-functor obstruction = this `ω`.

**Ledger update — the σ-parity skeleton (§3) is now ledger-proven.** Formalized in `formal/GaloisForLFunctions/FunctionalEquationParity.lean` (`fe_odd_moment_vanish`), axiom-clean (`[propext, Classical.choice, Quot.sound]`, zero `sorry`): for any multiset `s` of complex numbers invariant under negation `x ↦ −x` (the FE symmetry centered on the critical line), every **odd** power sum vanishes, `Σ_{x∈s} x^{2m+1} = 0`. This is the cohomological grading `σ|_{∧ᵏV}=(−1)ᵏ` read on moments — the §3 weld to foundations §22 (centered odd moments `τ_{2m+1}=0`) — at ledger grade. Proof: the odd-power image is again negation-invariant (`Odd.neg_pow`), so its sum equals its own negation (`Multiset.sum_map_neg'`), hence `0` in characteristic zero (`add_self_eq_zero`). The exterior-algebra cup product and the monoidality obstruction `ω∈H²` (the wall) remain unformalized.

**Ledger update (cont.) — the literal functional equation.** `fe_centered_odd_moment_vanish` (same file) extends the σ-parity to the actual FE reflection `ρ ↦ 1 − ρ`: a zero multiset invariant under `ρ↦1−ρ` has vanishing **centered** odd moments `Σ_{ρ}(ρ−½)^{2m+1}=0` — foundations §22 `τ_{2m+1}=0` for the genuine functional equation (the shifted multiset `{ρ−½}` is negation-invariant, reducing to `fe_odd_moment_vanish`). Both the negation and the centered (critical-line) forms are now axiom-clean. (Current audit: 140 theorem surfaces.)

**Ledger update — the σ-parity at the EXTERIOR-POWER level (the genuine cohomology grading).** `ExteriorParity.lean`, axiom-clean: `exteriorPower_map_smul_id` (`∧ⁿ(c·id)=cⁿ·id` on `⋀ⁿM`, via `exteriorPower.map_apply_ιMulti` + `MultilinearMap.map_smul_univ` + `linearMap_ext`) and `exteriorPower_map_neg_id` (`∧ⁿ(−id)=(−1)ⁿ·id`). With `σ=−1` on the prime lattice `V=H¹` this is exactly the §3 cohomological grading `σ|_{∧ᵏV}=(−1)ᵏ` — now machine-checked at the exterior-algebra level, upgrading the moment-level `FunctionalEquationParity` (`τ_{2m+1}=0`) to the genuine `∧ᵏ` form. Still open/unformalized: the full `H^*(G_L)` ring with cup product, the infinite prime-lattice limit, and the monoidality obstruction `ω∈H²` (the wall). (Current audit: 140 theorem surfaces.)

---

## 6. The ω obstruction as Koszul homology in the prime-limit `[SPEC, novel frame — mines the e–h/Koszul weld]`

The B30↔B5 weld just established (`spectral-functoriality-operations-calculus.md` §9) — that the `e–h` duality `Σ_{i+j=k}(−1)ⁱeᵢhⱼ=0` **is** the `∧•`/`Sym•` Koszul exactness — suggests a new, low-prior reading of the monoidality obstruction `ω∈H²` (§4).

**The frame `[SPEC].** For a *finite* prime set, the Koszul complex of the prime lattice `V`,
```
   ⋯ → ∧ᵏV ⊗ Symᵐ⁻ᵏV → ∧ᵏ⁻¹V ⊗ Symᵐ⁻ᵏ⁺¹V → ⋯ ,
```
is **exact** (Koszul); its Euler relation is the e–h duality, which is finite, free, and now ledger-proven as `GaloisForLFunctions.eh_koszul_duality` (`EHKoszulDuality.lean`). The exterior wing `∧•V` (the cohomology ring `H^*(𝕋^∞)=∧^*V`, §2) and the symmetric wing `Sym•V` (the *coordinate ring* of the dual — the secular/moment side) are Koszul-dual; the Lean theorem proves the all-degree Euler/character identity, not the full complex exactness in the infinite-prime limit.

**The conjecture `[SPEC, the wall in Koszul language].** Pass to the infinite prime set. The claim is that **`ω = 0 ⟺ the ∞-prime Koszul complex stays acyclic`** (no homology condenses in the limit), and `ω ≠ 0` is precisely *Koszul homology appearing in the renormalized `∏_{p}→` limit*. Concretely:
```
   ω  =  the Koszul homology class of the prime lattice in the ∞-limit
       =  the failure of  ∧•V ⊗ Sym•V  to stay acyclic under  ∏_{p≤P} → ∏_p .
```
This identifies the B5 monoidality obstruction with a **homological** object (Koszul homology of the prime lattice), not just a 2-cocycle — and the e–h duality (acyclicity) is its *finite, free* shadow.

**Why this is the same wall `[honest].** The "no homology condenses in the `P→∞` limit" is the *same renormalization condition* as the ξ-outer program's "no singular-inner factor condenses" (`xi_outer_dilation_program`) and the prime-multiplier LP-limit (`speculative-proofs` Attack 5/§Synthesis): all three are "a free/exact finite structure must survive the infinite prime product." So the Koszul-homology frame is a **fourth language** for the renormalization wall (alongside singular-inner condensation, LP-survival, and the explicit-formula limit), now tied to the *cohomological* side (B5) via the e–h/Koszul duality. The finite Euler shadow (`Σ_{i+j=k}(-1)^i e_i h_j=0`) is now Tier-A ledgered; the ∞-limit homology (`ω`) and full acyclicity survival are the wall — open, not faked.

**House status (§6).** New frame `[SPEC]`: `ω` (B5 monoidality, §4) = Koszul homology of the prime lattice in the `∏_p` limit; its finite Euler shadow is the `∧•`/`Sym•` e–h duality, now ledger-proven in `EHKoszulDuality.lean`. This welds B5's `ω` to the renormalization wall in a *homological* language (a fourth tongue for the same stone). The full finite Koszul complex exactness and the ∞-limit (`ω≠0` ⟺ condensed Koszul homology) remain outside the current Lean theorem; the infinite wall is conjectured, air-marked, never relabeled proven.
