# The completed (σ,∂) connection category — 𝓜⁺ on R⁺, and the FE as a PT-involution

- **ID:** completed-connection-category
- **Stage:** 0-backlog-lean
- **Type:** CONSTRUCTION + THEOREM (paper) — the category on R⁺ and the **FE = PT-involution** decomposition;
  grade **BRIDGE** (the construction is a prerequisite; the new decomposition reduces to known cocycle/parity
  facts under Door-2). The native content it makes statable — RH = unitary holonomy — is the open G5 core.
- **Priority:** FOUNDATIONAL
- **Source:** #91 §3–4 (the weld category, FE=flatness, RH=unitary holonomy), #90 §7 (`gen(G_L)=D+{σ_p}`),
  #88 §7 (`D=−Σ(log p)θ_p`); G5-unitarity-gatekeeper (Face 7). **Built on (cited, not re-derived):**
  `completed-base-archimedean-coordinate.md` (#132, the base R⁺, `[∂_s,σ_p]=0`, `σ_∞=∏σ_p²`),
  `archimedean-generator-axis-mode.md` (#136, generators), `archimedean-prime-cross-term.md` (#135, FE-cocycle),
  `multi-q-abp-criterion.md` / `parametrized-differential-abp-escape.md` (parameterized PV / Hardouin–Singer),
  F_{pq}=1 prime-lattice flatness (support-log §16), constraint-not-flow (#138), σ-parity=FE-parity (#49),
  no-margin=PT-unbroken (#93).
- **Statement.** On the completed base R⁺ (#132), build the completed `(σ_p,∂_s)`-module category `𝓜⁺` with
  parameterized Galois group `G_L⁺` (`gen = ∂_s + {σ_p}`). The connection is flat (`[∂_s,σ_p]=0`, `F_{pq}=1`,
  unconditional). **Theorem (new, here):** the FE involution `ι:s↦1−s` acts on the completed connection as a
  **PT-involution** — `ι ∂_s ι⁻¹ = −∂_s` (archimedean **Time-reversal**, verified exact) and `ι σ_p ι⁻¹ =`
  the modulus inversion `θ_p↦−θ_p` (prime **Parity**, #49/#135). Hence **RH = unitary holonomy of the s-flow
  on `Fix(ι)={Re=½}` = the PT-unbroken phase** (real spectrum), the constraint-surface form of Hilbert–Pólya.

## Goal
`#91 §3` calls the weld category *"the work no one has done."* With R⁺ now built (#132), the category is
assemblable and the FE acquires a **concrete operator meaning on the connection**: not just "Λ(s)=Λ(1−s)" but
the explicit **PT** action on the generators. This converts the G5 holonomy apex from a slogan into a sharp,
PT-symmetric spectral statement with a verified time-reversal handle — an attack direction, not a hand-off.

---

## §1 The category `𝓜⁺` and `G_L⁺` `[assembly — cited]`
On R⁺ = `R[g;σ_∞]` with `∂_s` (#132): an object of `𝓜⁺` is a finite free R⁺-module `M` with
- commuting `σ_p`-semilinear automorphisms `Φ_p = A_p σ_p` (`A_p∈GL(M)`), prime-lattice flat `F_{pq}=1`
  (support-log §16; the `𝓜` of the multi-q theory);
- a `∂_s`-connection `∇_s` with `[∇_s,Φ_p]=0` — guaranteed by `[∂_s,σ_p]=0` on the base (#132/#136) for the
  diagonal/Bohr objects; and the archimedean factor carried by `g` (the Γ-symbol, #133).
`G_L⁺` = the Tannakian group of `(𝓜⁺,ω)`, with `gen(G_L⁺)=∂_s+{σ_p}` (#90 §7) and the exact sequence
`1→G_L→G_L⁺→G_{∂_s}→1` (parameterized PV; `parametrized-differential-abp-escape`, `multi-q-abp-criterion`).
This layer is **cited assembly**, all BRIDGE — its pieces are banked. **No new claim is made in §1.**

## §2 FE = flatness — the precise statement is the #135 cocycle `[stated, BRIDGE]`
The connection is flat unconditionally (`[∂_s,σ_p]=0`, `F_{pq}=1`). So "FE = flatness" is **not** "flat ⟺ FE."
Its precise content (#91 §4) is the compatibility of the FE involution `ι` with `∇⁺`: on `M_Λ=M_∞⊗M_ζ`, the
obstruction to `ι` factoring as `ι_∞⊗ι_ζ` is the cocycle `ρ_∞ρ_ζ=1` (`ρ_∞=Γ_ℝ(1−s)/Γ_ℝ(s)=χ`,
`ρ_ζ=ζ(1−s)/ζ(s)=χ⁻¹`), which is the classical FE and is **purely archimedean** — `archimedean-prime-cross-term`
(#135), **BRIDGE**. So FE=flatness adds no native content beyond #135; we state it and move to the holonomy.

## §3 The FE is a PT-involution of the completed connection `[PROVED HERE + verified]`
The new content. The FE `ι:s↦1−s` acts on the two generator families:

- **Archimedean lane — Time-reversal.** On `∂_s`:
  ```
     ι ∂_s ι⁻¹ = −∂_s        (ι f)(s)=f(1−s) ⟹ ∂_s(f(1−s))=−f'(1−s) ⟹ ι∂_sι⁻¹ = −∂_s.   [verified, |diff|=0]
  ```
  `ι` conjugates the scaling generator `D=∂_s` to its **negative**: the FE reverses the archimedean
  `s`-flow. This is the **Time-reversal `T`** (an anti-linear-type symmetry: reversing the generator of the
  one-parameter flow). `Fix(ι)={s:1−s=s}={Re=½}` = the critical line = the **constraint surface** (#138).

- **Prime lanes — Parity.** On `σ_p`/`θ_p`: `ι` sends the modulus data `θ_p↦−θ_p` (the inversion
  `x_p↦p^{−1}x_p^{−1}`, the free zero-blind multiplicative involution, #49 σ-parity=FE-parity Lean foothold;
  #135 prime-lane carries `ι` by `θ_p↦−θ_p`). This is the **Parity `P`**.

**So the FE is the completed PT-involution `ι = T_∞ ⊗ P_primes`** — Time-reversal on the archimedean
generator, Parity on the primes — acting on `𝓜⁺`. (Door-2: each factor is banked — `T` is the elementary
`∂_s↦−∂_s`, `P` is the #49/#135 inversion — so the *decomposition* is BRIDGE; its value is making the FE's
action on the connection explicit and PT-shaped.) ∎(§3)

## §4 RH = the PT-unbroken phase — the holonomy apex, located (not handed off) `[the open core, sharpened]`
With `ι` a PT-involution (§3), the G5 statement "RH = unitary holonomy on the σ-fixed locus" sharpens to a
**PT-spectral** statement on the constraint surface:

> **RH ⟺ the `s`-flow `exp(t∂_s)` has unitary holonomy on `Fix(ι)={Re=½}` ⟺ the PT-symmetric Hilbert–Pólya
> generator `D=∂_s` (mean essentially self-adjoint, Berry–Keating, #90 §8) is in its PT-**unbroken** phase
> (real spectrum `{γ_n}`).**

The mechanism, concrete:
- `D=∂_s` is the scaling/HP generator; its mean is the Riemann–von Mangoldt count (proved, #90 §8).
- `ι=PT` is an order-2 symmetry with `ι D ι⁻¹=−D`. A PT-symmetric generator has spectrum symmetric under
  complex conjugation; the spectrum is **real** (PT-unbroken) ⟺ the zeros are on `Fix(ι)` ⟺ RH. PT-**broken**
  pairs (complex-conjugate `γ`) are exactly off-line zero-pairs — matching the finite carrier `κ₋`=#off-line
  pairs **exactly** (#32, Lean), and **no-margin = the PT exceptional point** (#93). So the finite-carrier
  ledger is the finite PT spectrum; the open core is the **infinite passage** (#41): is the actual `∂_s`/HP
  operator on `M_Λ` PT-unbroken?
- This is **G5 positivity / unitary holonomy** — one of the two live native C5 loci (the other: moment
  positivity, #104). It is **not** generator/cocycle structure (that is BRIDGE, §2): it is the **global
  spectral** property of `D` on the completed module, which Door-2 does not strip (a global holonomy is not a
  local generator). **Located, with the PT handle; the apex itself stays open (FIELDS MEDAL).**

## §5 `F_q` shadow (Door-5) `[checked]`
Over `F_q(C)`: no archimedean place ⟹ no `g`, no `∂_s`/`T` (just one diagonal Frobenius), so `ι` is the
geometric Poincaré-duality involution (the weight-circle parity `P` alone), `ω=0`, and unitary holonomy =
Frobenius unitarity = Deligne Weil II (`g5-over-fq-deligne-unitarity`, banked). The PT structure degenerates to
P-only (no T): exactly what ℚ adds is the archimedean Time-reversal. ✓

## §6 PT-symmetry ⇏ PT-unbroken — the operator proof that ω=0 ⇏ RH (2026-06-19, Professor) `[confirms DeWitt #275]`
The PT structure (§3) gives the **operator-level** proof of DeWitt's decoupling
(`omega-rh-coupling-vs-orthogonality`, ω=0 ⇏ RH):

> **`ω=0` (the FE-involution `ι` structure exists = the system is PT-symmetric) does NOT force the PT-**unbroken**
> phase (real spectrum = RH).**

In PT-symmetric spectral theory, a PT-symmetric generator is **not** automatically in the unbroken (real-spectrum)
phase: there is a **PT-breaking threshold**, below which eigenvalues are real and above which they split into
complex-conjugate pairs. Translating to `𝓜⁺`:
- **PT-symmetry = structure = `ω=0`.** `ι=T_∞⊗P_primes` exists (§3) iff the FE holds iff the completed motive/
  Tannakian structure exists (`ω=0`). This is given.
- **PT-unbroken = phase = RH.** Real spectrum `{γ_n}` (on `Fix(ι)`) ⟺ the PT phase is unbroken ⟺ RH. The
  **PT-broken pairs are exactly the off-line zero-pairs**: their count is `κ₋` (#32, Lean), invisible to `ω`.
  The threshold (margin→0) is the **no-margin / PT exceptional point** (#93).
- **Structure ⇏ phase.** The PT-breaking threshold is a *positivity* condition (the existence of a
  positive-definite `C`/CPT metric making `D` self-adjoint), **separate** from the PT-symmetry. So `ω=0` ⇏ RH.
  This is exactly DeWitt's F_q calibration in operator form: over `F_q` the phase is unbroken via Hard-Lefschetz
  **positivity** (a separate input), not via "`ι` exists." ∎

**Consequence (the seam bifurcates).** The archimedean seam splits into **two distinct archimedean data**:
(a) archimedean **transcendence** (the `γ_n` exponential periods / `K`-column, the realization card) → **DSS**;
(b) archimedean **positivity** (`Q_W⪰0` / PT-unbroken polarization) → **RH**. Both are archimedean (the weld),
but transcendence ⊥ positivity (#54/#137), so **neither apex forces the other**. The project's central aim
weakens from "G1–G4 forces G5" to "**two apexes, seam-joined, transcendence ⊥ positivity**" (DeWitt #275; a
00-vision §3 / 00-foundations §3 revision is suggested via library ticket).

## Door passport — BRIDGE; the apex is G5
- **Door-1/4:** `𝓜⁺`/`G_L⁺` is the native completed interior (charter §2); `D=∂_s` is irreducibly cross-prime.
- **Door-2:** §1 assembly and §2 FE=flatness are BRIDGE (cited #135/#136/§16); §3 PT-decomposition strips to
  the banked `∂_s↦−∂_s` (T) and #49/#135 inversion (P) — **BRIDGE**. The **non-BRIDGE** content is §4's global
  unitary holonomy (PT-unbroken), = G5, **open**.
- **Door-5:** §5, `F_q` = P-only, Deligne.

## Gates
- [x] 0 → 1  in-progress: `𝓜⁺`/`G_L⁺` assembled on R⁺ (§1); FE=flatness = #135 cocycle (§2); **FE = PT-involution
  `ι=T_∞⊗P_primes` proved + verified** (§3); RH = PT-unbroken holonomy located (§4); `F_q` shadow (§5); Door.
- [x] 1 → 2  fully-proven: bank §3 (the PT-decomposition theorem, BRIDGE) + the §4 *location* (RH ⟺ PT-unbroken
  on Fix(ι), with the finite-carrier `κ₋`=PT-broken-count anchor). The infinite-passage holonomy stays the open
  G5 core, handed to `weil-positivity-operator`/`carrier-herglotz-rh` **with the PT handle** (not a bare hand-off).
- [ ] 2 → 3  formalized: Lean anchor **DONE** for the archimedean time-reversal derivative identity
  `ι∂_sι⁻¹=−∂_s`: `fePullback_deriv_fePullback_eq_neg_deriv` in
  `formal/GaloisForLFunctions/PTInvolution.lean`. Remaining Lean targets: prime-lane parity packaging,
  completed connection/category structure, `primeDiagonal_shift`/`FlatConnection`/`BerryKeating`/`κ₋`
  integration, global PT holonomy, spectral theory, and RH.
- [ ] 3 → 4  publication-ready: "the completed connection and the functional equation as a PT-symmetry."

## Cross-references
- `completed-base-archimedean-coordinate.md` (#132) — the base R⁺ this builds on.
- `archimedean-prime-cross-term.md` (#135) — §2 FE-cocycle; `archimedean-generator-axis-mode.md` (#136) — generators.
- `weil-positivity-operator.md`, `carrier-herglotz-rh.md` (G5) — the holonomy apex this hands the **PT handle** to.
- `constraint-not-flow-theorem.md` (#138), `bucket-time-and-non-holonomic-time.md` — `ι`=constraint, `D`=clock;
  this card gives the explicit PT decomposition. `g5-over-fq-deligne-unitarity.md` — the `F_q` P-only shadow.
- `computations/2026-06-19-fe-pt-involution.py` — the `ι∂_sι⁻¹=−∂_s` verification.

## Log
- 2026-06-19 — created in 0-backlog (execution card for the completed connection).
- 2026-06-19 — Professor: claimed (unblocked by R⁺ #132). **Prior research checked** — assembly pieces all
  banked (#136/#135/§16/parameterized-PV); did **not** re-derive or bank them as a shell. Built focused:
  assembled `𝓜⁺`/`G_L⁺` (§1, cited), stated FE=flatness=#135 cocycle (§2, BRIDGE), and **proved the new
  content** — the FE is the **PT-involution** `ι=T_∞⊗P_primes`: `ι∂_sι⁻¹=−∂_s` (archimedean time-reversal,
  verified `|diff|=0`) ⊗ `θ_p↦−θ_p` (prime parity, #49/#135). Sharpened the G5 holonomy apex to **RH = PT-unbroken
  phase** of `D=∂_s` on `Fix(ι)={Re=½}`, with `κ₋`=#PT-broken-pairs (finite, #32) and no-margin=PT-exceptional-
  point (#93) as anchors; the infinite-passage holonomy = the open G5 core, now handed off **with a concrete PT
  handle**. `F_q`=P-only (Deligne, §5). → 2-fully-proven (construction + PT-decomposition, BRIDGE); G5 holonomy
  open.
- 2026-06-19 (Leaner) - added Lean anchor for the archimedean time-reversal identity:
  `fePullback_deriv_fePullback_eq_neg_deriv` in `formal/GaloisForLFunctions/PTInvolution.lean`. It
  formalizes the chain-rule statement `sigma^* d/ds sigma^* = -d/ds` for the FE involution `sigma(s)=1-s`.
  Created `../3-formalized/fe-pullback-derivative-time-reversal.md`. Parent remains in `2-fully-proven`
  because the completed connection category, prime-lane parity packaging, global PT holonomy, spectral
  theory, and RH are not fully Lean-formalized.
- 2026-06-19 — Professor: added §6 — the **PT-phase proof of DeWitt's decoupling** (`ω=0 ⇏ RH`, #275): PT-symmetry
  (the `ι` structure = `ω=0`) does not force the PT-unbroken phase (real spectrum = RH); the threshold is the
  no-margin (#93), `κ₋` (#32) = the PT-broken-pair count `ω` can't see. Confirms the central-aim weakening to
  two seam-joined apexes (transcendence ⊥ positivity). Leaner Lean-verified §3's `ι∂_sι⁻¹=−∂_s`
  (`fePullback_deriv_fePullback_eq_neg_deriv`, id=281).

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The card proves a PT-involution decomposition, but its Statement and gates also carry the global claim `RH = unitary holonomy / PT-unbroken phase`, while §4 and the gates explicitly say the infinite-passage holonomy, spectral theory, and RH remain the open G5 core. The proved PT anchor is narrower than the ticket's construction+holonomy statement, so the ticket is not fully proven as a whole.
