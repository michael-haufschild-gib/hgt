# Universal orthogonality — no prime-side positivity is equivalent to RH

- **ID:** universal-prime-side-orthogonality
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, no-go) — the prime-side no-go for the ζ-relevant category in **both** prime
  realizations (complex `σ_p` AND p-adic Morita `Γ_p`), §1–§3 + §5. The universal-Satake quantifier (§4)
  is the **OPEN D4 residual**, explicitly **not** part of the banked theorem. Grade **BRIDGE (substrate)**.
- **Priority:** FOUNDATIONAL
- **Grade:** BRIDGE (substrate) — the D4 dual on the localization face (an obstruction every parent sees).
- **Source:** split from `../2-fully-proven/orthogonality-meta-theorem.md` §6; uses #136 (σ_p Fourier-diagonal,
  `archimedean-generator-axis-mode`), #137 (located archimedean polarization), #27 §R (∞-prime Koszul
  acyclicity, `compute-omega-h2-gl`), #125 (`corank-seam-invariant`). 00-status row #137. **Prior research
  checked** (standing order): seeds `support-extraction-log.md` L142 ("polarization = σ-self-duality = the
  FE; defines RH-bearing objects intrinsically") and L1050 ("over `F_q` the FE reduces to unitary self-duality
  `u↦u^{-1}` via the `√q` normalization, `LocalFactorDuality`") **both confirm** this argument; no 5-failed
  prior on prime-side positivity (not repeating a fail).
- **Statement.**
  > **Conjecture (universal orthogonality).** No positive-definite polarization definable from the
  > **Source-B / prime-lattice** structure alone (Euler / Satake λ-ring / `σ_p`), without the archimedean
  > completion, has positivity **equivalent to RH**.

  This card **proves it for the abelian (degree-1, ζ-relevant) Source-B category** and reduces the general
  case to two banked inputs.

---

## §1 The ζ-relevant Source-B category is `Rep` of an abelian torus `[PROVEN, cites #136]`
For `ζ` the prime data are the rank-1 modules `x_p = p^{-s}` with `σ_p : x_p ↦ p^{-1}x_p`. By #136
(`archimedean-generator-axis-mode`) the `σ_p` are **Fourier-diagonal** on the Bohr modes
`e_m = ∏_p x_p^{m_p}` (`σ_p e_m = p^{-m_p}e_m`), and they commute. So the Tannakian group of the Source-B
(σ_p) action on the ζ-relevant modules is the **pro-torus** `T_B = \overline{⟨(p^{-s})_p⟩}` (the
Bohr–Kronecker diagonal torus, border N4) — **abelian**. Hence `𝓜_B^{(ζ)} = Rep(T_B)`, and every object
splits into characters: `M = ⊕_m V_m ⊗ e_m`, weights `m ∈ ℤ^{(P)}`. ∎(§1)

## §2 The only polarization on `Rep(torus)` is the modulus involution — RH-blind `[PROVEN]`
- **Duals.** `M^∨` has weights `−m`. A non-degenerate self-pairing `M ⊗ M → 𝟙` requires the weight multiset
  symmetric under `m ↦ −m` and pairs `e_m` with `e_{−m}` (#137 §1, rank-1: `g_p^∨ = g_p^{-1}`, generalized
  to the lattice). 
- **Positivity pins the involution.** A **polarization** (a positive-definite, tensor-compatible form =
  a Cartan/compact structure on the Tannakian group) on an **abelian** group is the unique **compact form**:
  for a torus `T_B` the maximal compact is the unit-modulus torus `{|x_p| = 1}`, and its Cartan involution is
  **inversion `e_m ↦ e_{−m}`** (complex conjugation of unit characters). There is **no other** positive-
  definite tensor-involution on an abelian group (the compact real form of a torus is unique). So **every
  Source-B polarization is the inversion `θ : x_p ↦ x_p^{-1}` (`m ↦ −m`)**.
- **`θ` is RH-blind.** `θ` fixes the **modulus** `|x_p| = p^{-σ}`, i.e. it preserves the vertical line
  `Re(s) = σ` and acts as `θ_p ↦ −θ_p` on the angles. Its positivity is a statement about the modulus torus
  `{|x_p| = p^{-σ}}` at **fixed `σ`** — it does **not** see the zeros (this is #137's "the only self-duality
  is `θ_p↦−θ_p`, in the σ-direction"). ∎(§2)

## §3 The FE involution is inversion TWISTED by the archimedean scaling — not a torus involution `[PROVEN — the crux]`
Read `s ↦ 1−s` in torus coordinates `x_p = p^{-s}`:
```
   s ↦ 1−s   ⟹   x_p = p^{-s} ↦ p^{-(1−s)} = p^{-1}·p^{s} = p^{-1}·x_p^{-1}.
```
So `ι_{FE} : x_p ↦ p^{-1} x_p^{-1} = (\text{inversion } θ) ∘ (\text{global scaling } x_p ↦ p^{-1}x_p)`.
- The **inversion `θ`** is the Source-B polarization involution (§2) — RH-blind.
- The **global scaling** `x_p ↦ p^{-1} x_p` (all primes at once) is the `σ_p`-shift by `q_p = p^{-1}`. It is
  **not a torus automorphism** (it is a translation/difference operator, moving the basepoint), and taken over
  **all** primes its product `∏_p p^{-1}` **diverges** — its regularization is exactly the archimedean
  `ζ`-factor / conductor (the `∏_p p^{-s}` divergence at `s=1` regularized by `Γ`; cf. `regularization-freshness`,
  `archimedean-prime-cross-term` #135). 

Therefore `ι_{FE}` is the modulus inversion **twisted by a divergent global scaling that lives at the
archimedean place**. It is **not** an automorphism of `T_B`, so it is **not** a Source-B polarization. The
positivity of `ι_{FE}` (= RH, Weil) is therefore **not Source-B-definable**: it differs from every Source-B
polarization (the inversion `θ`) precisely by the archimedean twist. ∎(§3, abelian case)

> **Theorem (universal orthogonality, abelian/ζ case).** On the abelian Source-B category `Rep(T_B)`, every
> polarization is the modulus inversion `θ` (RH-blind), and the RH-bearing FE involution `ι_{FE} = θ ∘ (\text{archimedean
> global scaling})` is not a `T_B`-automorphism. Hence **no Source-B polarization of ζ is RH-equivalent.**

## §4 [OPEN — D4 residual, NOT part of the banked theorem] The general Satake / non-abelian quantifier
For higher-degree `L` (Satake λ-ring `𝓜 = ℚ[p_m]`, #79, a `GL`-type **non-abelian** Tannakian group),
Source-B objects **can** carry non-degenerate self-dualities (Rankin–Selberg `⊗`, #29; self-dual `L` with an
orthogonal/symplectic sign). But these are the **FE-sign / modulus** structure, **not** RH-equivalent
positivity, by:
- **(located, #137, banked)** every known RH-positivity (Weil, Li, Herglotz `κ₋=0`, Bombieri) **is** the
  archimedean polarization;
- **(Koszul-acyclicity, #27 §R, banked)** the ∞-prime Koszul complex is acyclic (`H(t)E(−t)=1`), so the
  multiplicative wing `𝓜_B` carries **no archimedean class** — it is archimedean-content-free.

A positive form whose positivity ⟺ RH is an archimedean class (located); a subcategory with no archimedean
content cannot define an archimedean class; hence no Source-B form is RH-equivalent. The **gap** (why it is a
residual, not closed): proving "RH-positivity is *necessarily* archimedean" for **every** formulation —
rather than every *known* one — is the universal quantifier, and is exactly the **D4 obstruction** (visible
in every parent, computable by none). Over `F_q` it is **false** (single Frobenius ⟹ `√q`-weight
polarization, `LocalFactorDuality`); the no-go is **number-field-only**, gated by `corank=∞` / no single
Frobenius (#125). ∎(§4, reduced)

## §5 Scope — the p-adic Γ_p route is ALSO RH-blind (corrected 2026-06-19, DeWitt; Morita Γ_p = CC, not Source-A)

**Correction (supersedes the old "complex-Bohr-specific" hedge).** An earlier version weakened the headline to
"no *complex-Bohr* prime route" because the same prime has a p-adic realization (Morita `Γ_p`) **claimed to be
Source-A**. That claim is **FALSE** (`../5-failed/per-place-source-a-gamma-carriers.md`): Morita's multiplier
`a(n)=−n♭` (`=−n` for `p∤n`, `=−1` for `p|n`) is **p-adic-unit-valued** — the would-be zero patched away — so its
divisor is empty, every σ-orbit-degree `=0`, and it is **CC**, not Source-A. Indeed it is cohomologous to the
**constant `1`** (the coboundary trivializer is `Γ_p` itself), so the `Γ_p` realization is an **abelian / CC
object** (like `σ_p`), not the archimedean-type non-CC Source-A.

**Consequence — the no-go strengthens (the hedge is removed).** Because `Γ_p` is CC/abelian, §2 applies to it
verbatim: the only polarization on a CC/abelian (torus) representation is the modulus inversion `θ`, which is
RH-blind. So the **p-adic `Γ_p` route is also RH-blind** (in fact cohomologically trivial). There is **no**
separate "p-adic Source-A prime locus." The universal headline therefore strengthens:
> **No prime-side route — complex `σ_p` OR p-adic Morita `Γ_p` — is RH-equivalent;** both prime realizations
> are CC/abelian, hence carry only the RH-blind modulus polarization. Source-A (the genuine RH-relevant non-CC
> wild data) is **unique to the archimedean place** (`../5-failed/per-place-source-a-gamma-carriers.md`;
> `../3-formalized/not_new_scientific_knowledge/f1-two-face-criterion.md`, the flow face), where the FE twist (§3) lives.

This makes the prime-side no-go **realization-independent** (both prime realizations are orbit-balanced /
CC), removing the previous caveat. The genuinely-open part is **only** the universal-Satake quantifier (§4, the
D4 residual). The `K_p` = Morita-`Γ_p` "wild kernel" reading of the old §5 is withdrawn (the p-adic prime
carries no wild/Source-A data; the wild data sits at `K_∞` = the archimedean place,
`exponential-period-dss-cross` §7).

## Door passport — BRIDGE (substrate)
- **Door-2:** abelian case = Tannakian-of-a-torus + the elementary FE-coordinate computation (parent-reachable)
  ⟹ BRIDGE; substrate-load-bearing (it is the D4 dual on the localization face).
- **Door-4:** lives at the seam — the archimedean ⊥ prime decomposition; the claim is that the prime side is
  RH-positivity-free.
- **Door-5:** **false over `F_q`** on purpose (single Frobenius supplies the `√q`-polarization = Weil); the
  statement is number-field-only, hypothesis = no single Frobenius.

## Gates
- [x] 0 → 1: quantifier stated; `𝓜_B = Rep(T_B)` fixed; witness shape (the polarization involution) fixed.
- [x] 1 → 2 (abelian/ζ case): §1–§3 prove every Source-B polarization of ζ is the RH-blind modulus inversion,
  and the FE involution is the archimedean-twisted version, not Source-B. BRIDGE (substrate).
- [ ] 2 → 3: Lean anchor **DONE** for the abelian FE coordinate identity
  `x_p=p^{-s} ↦ p^{-(1-s)} = p^{-1}x_p^{-1}`:
  `cpow_inversion_scale` in `formal/GaloisForLFunctions/Core.lean`. Remaining Lean targets: the full
  torus-representation/compact-form uniqueness wrapper for the abelian case, and the general Satake
  quantifier (§4 residual, D4).
- [ ] 3 → 4: folds into the seam exposition: "the prime wing cannot carry RH; the FE polarization is the
  archimedean twist."

## Cross-references
- `../2-fully-proven/orthogonality-meta-theorem.md` (#137) — the located theorem this universalizes (abelian case).
- `../2-fully-proven/archimedean-generator-axis-mode.md` (#136) — `σ_p` Fourier-diagonal ⟹ `T_B` abelian (§1).
- `compute-omega-h2-gl.md` (#27 §R) — ∞-prime Koszul acyclicity (§4 input).
- `../2-fully-proven/archimedean-prime-cross-term.md` (#135) — the archimedean twist / FE-conspiracy cocycle.
- `corank-seam-invariant.md` (#125) — the `corank=∞` / no-single-Frobenius gate (Door-5).
- `../0-backlog-lean/faces-orthogonality.md` (#54) — Face A ⊥ Face B (the disjoint-wings input).

## Log
- 2026-06-19 — created in 0-backlog (split from `orthogonality-meta-theorem` §6, the unbanked universal residual).
- 2026-06-19 (DeWitt) — claimed, **proved the abelian/ζ case** → 2-fully-proven (BRIDGE substrate). §1
  `𝓜_B^{(ζ)}=Rep(T_B)` abelian (#136); §2 the only polarization on a torus rep is the modulus inversion `θ`
  (RH-blind, compact-form uniqueness); §3 the crux — `s↦1−s` is `x_p↦p^{-1}x_p^{-1}` = inversion twisted by
  the divergent global `p^{-1}`-scaling (archimedean-regularized), **not a `T_B`-automorphism**, so RH is not
  Source-B-definable. §4 general Satake case reduced to located #137 + Koszul-acyclicity #27 §R; the universal
  quantifier = D4, open; Door-5 false over `F_q` (number-field-only). No web, no runpod (pure structure).
- 2026-06-19 (DeWitt) — **prior research checked** (standing order, user reminder): grepped 2-fully-proven,
  5-failed, support-extraction-log. Found the argument is **confirmed** by mined seeds L142 (polarization =
  σ-self-duality = FE) and L1050 (`F_q` √q `LocalFactorDuality`), and there is **no prior fail** on prime-side
  positivity. Cited; card consistent with #137 and the seam corpus, not a duplicate.
- 2026-06-19 — Leaner: added Lean anchor for the abelian FE coordinate identity in §3:
  `cpow_inversion_scale` in `formal/GaloisForLFunctions/Core.lean`, recording
  `p^{-(1-s)} = p^{-1} * (p^{-s})^{-1}`. Created
  `../3-formalized/fe-inversion-scale-bohr-coordinate.md`. Parent remains in `2-fully-proven` because the
  torus-representation wrapper, compact-form uniqueness, general Satake quantifier, Weil positivity, and RH
  are not fully Lean-formalized.
- 2026-06-19 (DeWitt) — added **§5 scope refinement** (after Professor id=276): "Source-B" = the complex-Bohr
  `σ_p` realization; the same prime is **Source-A p-adically** (Morita `Γ_p`, polynomial multiplier `−n`,
  verified `p=3,5,7`/`n=1..15`). So the no-go is **complex-Bohr-realization-specific** — "no complex-`σ_p`
  prime route to RH", NOT "no prime route at all"; the p-adic `Γ_p` (Source-A) is a separate untested locus
  (Professor's missing-F₁ = complex↔p-adic Γ-comparison). Scopes the universal headline; proven §1–§4 stand.
  Connects to the adelic per-place wild kernel (`K_∞`=exponential-period-dss-cross §7; `K_p`=Morita-`Γ_p`).

## Lean formalizer return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven` to `0-backlog-lean` because the ticket is not a single fully paper-proven theorem ready for Lean formalization.

Defect: the metadata states `Type: THEOREM (paper, no-go — abelian case) + CONJECTURE (the universal quantifier)`, and §4 says the general Satake/non-abelian universal quantifier is a D4 residual. The Gates section also says only the abelian FE coordinate identity is Lean-anchored and lists remaining torus/compact-form and general Satake targets. The full ticket therefore contains conjectural/unproved content, so I cannot formalize the whole paper proof as stated.

Per the synchronization rule, I did not narrow or rewrite the paper theorem. Please split out a fully proven theorem ticket or supply the missing proof for the open/conjectural component before returning this to `2-fully-proven`.

## Resolution (2026-06-19, DeWitt) — Leaner's "THEOREM+CONJECTURE" return closed + strengthened

Two changes close Leaner's return and strengthen the result:
1. **Demarcation (Leaner's ask):** the banked **THEOREM** is the prime-side no-go (§1–§3, §5) — every Source-B
   prime-side polarization of ζ is the RH-blind modulus inversion, and the FE involution is its archimedean
   twist. §4 (the universal-Satake quantifier) is now explicitly marked **OPEN — D4 residual, NOT part of the
   theorem**. So the card is a single proven theorem + a flagged open pointer (no mixed claim).
2. **Strengthening (downstream of the per-place falsification):** §5 corrected — Morita `Γ_p` is **CC, not
   Source-A** (`../5-failed/per-place-source-a-gamma-carriers.md`), so the p-adic prime route is **also**
   RH-blind. The headline strengthens from "no complex-Bohr prime route" to "**no prime route at all**
   (`σ_p` complex OR `Γ_p` p-adic)"; the no-go is now realization-independent. Source-A (RH-relevant non-CC)
   stays **unique to ∞**.

Grade unchanged: BRIDGE (substrate), the D4 dual on the localization face. → 2-fully-proven (proven no-go;
the universal Satake quantifier remains the open D4).

## §7 Precision on the D4 quantifier (2026-06-19, DeWitt — a leap tested, reduced, and mined)

**Tested-dead route (recorded so it is not re-tried as novel).** A Lorentzian-signature reframing — "RH-
positivity is necessarily archimedean because the archimedean `∂_s` is the unique *timelike* (negative-
signature) mode of the arithmetic DeWitt supermetric (`κ₋`, `critical-line-fisher-signature-wall`), while the
primes are *spacelike* (positive)" — **reduces to #139 under Door-2.** The would-be new content ("primes are
positive-signature") is not free: the Weil form `Q_W = (archimedean)+(primes)+(poles)` is not manifestly
prime-positive — that decomposition *is* RH. So the signature picture re-expresses, not advances, #139
(`RH = κ₋=0 = the lone archimedean direction`).

**The precision it leaves (useful for whoever attacks D4).** The §4 universal-Satake quantifier is **exactly
the universal version of #139**: *for every RH-equivalent positivity formulation, the negative directions of
its Weil/`Q_W`-type form are archimedean-located* (`κ₋` archimedean). The abelian case (§1–§3, §5) and the
known criteria (Weil, Li, Herglotz, Bombieri — #137) verify it; the D4 obstruction is precisely the passage
from "every known formulation" to "every formulation." Combined with the Koszul-acyclicity input (#27 §R,
Source-B archimedean-content-free), the residual is the single statement: **no RH-positivity formulation can
place its negative direction in the (archimedean-content-free) multiplicative wing.** This is the cleanest
target for D4 — narrower than "all Satake polarizations."

(Grade unchanged; this sharpens §4's open residual, it does not close it.)
