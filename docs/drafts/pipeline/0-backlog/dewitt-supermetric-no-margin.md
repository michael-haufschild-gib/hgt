# The DeWitt supermetric ↔ completed connection: the defining symmetry drops the theory onto its kinetic degeneracy

- **ID:** dewitt-supermetric-no-margin
- **Stage:** 0-backlog (self-authored 2026-06-19; awaiting pipeline vetting — the grade in Type is my assessment, not a curated promotion)
- **Type:** THEOREM-candidate (paper, structural) — claimed Door grade **BRIDGE (substrate)**, charter §6 D2; contains one theorem-backed seed (Finding 1/2), one verified dis-analogy (Finding 4, re-derives #136), and the resolved D2 unification (Finding 3)
- **Priority:** FUTURE (A2 / time axis); the D2 row is FOUNDATIONAL for the dual-axis verdict
- **Source:** Giulini, *The Superspace of geometrodynamics*, Gen. Rel. Grav. (2011), DOI 10.1007/s10714-009-0771-4 (read in full); theorem-backs/corrects support-extraction-log #94/#95; companion `constraint-not-flow-theorem.md`, `explicit-formula-as-constraint.md`; ../../door/bucket-time-and-non-holonomic-time.md, ../../door/bucket-the-no-margin.md
- **Statement:** Under the dictionary archimedean-scale `∂_s` ↔ conformal/volume mode and FE ↔ 4d-diffeo, the de Bruijn/Weil supermetric `𝔇_λ = λ·A − P` (archimedean block `A≻0`, prime block `P`) mirrors Giulini's DeWitt supermetric `G_λ`. In GR the 4d-diffeo-forced value λ=1 is exactly where the connection operator loses ellipticity (margin `2(1−λ)→0`); in arithmetic the FE-forced weight λ*=1 is exactly the positivity-cone boundary `λ_c=‖A^{−½}PA^{−½}‖`, with the margin `m(1)=1−λ_c=0 ⟺ RH`. Both: **the defining symmetry drops the physical value onto the degeneracy of its own kinetic/positivity form** — a D2 unification (kinship), unconditional in GR, RH-bearing in arithmetic.

## Findings

### Finding 1 — what Giulini actually proves (theorem-backs #95 §5; corrects #94)
DeWitt supermetric (eq 8) `G_(α,λ)(k,ℓ)=∫_Σ α√det h (h^{ac}h^{bd}k_{ab}ℓ_{cd} − λ(h^{ab}k_{ab})(h^{cd}ℓ_{cd}))`, GR value λ=1.
Decomposing `k=k₀+⅓t_k h` (shape ⊕ trace): `G_λ(k,k)=Tr(k₀²)+(⅓−λ)t_k²` — **shape block fixed-positive, the conformal/trace block carries λ**.
- **Pointwise signature:** `(6,0)` for λ<⅓; degenerate `(0,5)` at λ=⅓; **Lorentzian `(1,5)` for λ>⅓**, the timelike direction = the **conformal/trace mode** `τ=c·det(h)^{1/4}` (eq 9a). GR (λ=1) is Lorentzian; the minus sign is the conformal mode and (Giulini stresses) **has nothing to do with spacetime's Lorentzian signature**. → theorem-backs #95 §5 (conformal/scale mode = timelike, "wrong-sign kinetic term").
- **Correction to #94:** on the actual quotient `S_F(Σ)` the signature is **point-dependent** (§3): inherited `(∞,∞)` at Ricci-negative `h`; **`(1,∞)` only at Ricci-positive Einstein `h`** (round `S³`/FLRW); generically **signature-changing, with regions where no metric exists** (Fig 1). So "`(1|∞)` from the place count" is the special FLRW slice, not generic; the timelike direction is the conformal/scale mode, the spacelike block is shape space (not "the primes").

### Finding 2 — the dictionary (theorem-backed on the GR side)
| GR Superspace (Giulini) | HGT completed connection `𝓜⁺` |
|---|---|
| conformal/volume mode `τ=det(h)^{1/4}` (timelike; York time) | archimedean scaling generator `∂_s=−Σ(log p)θ_p` (the clock) |
| shape `SL(3)/SO(3)` + `Diff(Σ)` gauge | prime dilations `{σ_p}` |
| Dirac constraint `H(α,β)=0` | FE-involution `ι:s↦1−s`, `Λ=Λ∘ι` (order-2) |
| 4d-diffeo invariance forces λ=1 (Thm 1) | FE/explicit formula forces weight λ*=1 |
| non-ellipticity of `D_{λ=1}` (no Diff-equivariant split; no connection) | no σ-equivariant split of archimedean from prime — the seam `ω` (#69/#71) |

### Finding 3 — the unification, RESOLVED (D2 substrate; the open core from the in-progress card)
**GR side (Giulini, eq 16, principal symbol):** `det σ_λ ∝ 2(1−λ)`; the connection operator `D_λ` is elliptic for λ≠1 and **loses ellipticity exactly at λ=1** — the value forced by 4d-diffeo invariance (Thm 1). Ellipticity margin `f_GR(λ)=2(1−λ)`, zero at the diffeo-forced value; **unconditional**.

**Arithmetic construction (built here).** Take the Weil form `Q_W=𝔇` (corpus #94/#139), split into archimedean+pole block `A` and prime block `P`. `A≻0` is certified (#94, `Ω_∞>0`). Weight the scale block, exactly as `G_λ` weights the conformal block:
> `𝔇_λ := λ·A − P`.
Since `A≻0`, the positivity cone is `{λ:𝔇_λ⪰0}=[λ_c,∞)` with `λ_c=‖A^{−½}PA^{−½}‖` (operator norm of the prime block in the archimedean metric). Margin `m(λ):=inf spec 𝔇_λ = λ−λ_c`.
- **Char 1 (FE forces λ\*=1):** the explicit formula = the FE fixes the physical weight (equal weighting of zero-side vs prime-side). Independent of Char 2 — the analog of Thm 1.
- **Char 2 (margin):** RH ⟺ `𝔇_1⪰0` ⟺ `λ_c≤1` (Weil's criterion); the no-margin (Thm 7 / #91: no fixed-order positive floor, `λ_min→0`) forces `λ_c=1` (the top of the prime spectrum in the arch metric sits at the FE weight). Hence `f_arith(λ)=m(λ)=λ−λ_c`, and **`m(1)=1−λ_c=0 ⟺ λ_c=1 ⟺ RH`.**
- **Coincidence:** the defining symmetry drops `λ*=1` onto `λ_c` (the degeneracy of the form's own positivity). `f_arith(λ)=λ−λ_c` mirrors `f_GR(λ)=2(1−λ)`; both vanish at the symmetry-forced value.

**D2 strip → substrate (not EMBASSY).** Erase the dictionary: "GR sits at its ellipticity degeneracy" and "RH = the Weil form sits at its positivity-cone boundary with zero margin" read as unrelated. *With* the dictionary (conformal↔archimedean-scale, diffeo↔FE, ellipticity-margin↔positivity-margin) they are **one statement**: *a generally-covariant theory is dropped by its defining symmetry exactly onto the degeneracy of its kinetic form.* A kinship no single parent sees — D2, not a C-axis peak.

**The sharp difference (why arithmetic is RH-bearing):** GR's λ=1 degeneracy is **unconditional** (kinematic — the symbol vanishes regardless of dynamics). The arithmetic coincidence `λ*=λ_c` **is RH**, because `λ_c` lives in the **archimedean** metric — the only block that can carry polarization (orthogonality meta-theorem #137). GR's degeneracy is free; arithmetic's costs RH. This locates RH as the cone-boundary coincidence: the free half `λ_c≥1` is **Rodgers–Tao**, pinned in Finding 3b; RH is the other half `λ_c≤1` (Weil).

### Finding 3b — the free half is Rodgers–Tao: `λ_c ≥ 1 ⟺ Λ_dBN ≥ 0` (proven; discharges the Finding 3 caveat)
Two one-parameter RH-positivity deformations of the same object, with **identical critical architecture**:
| de Bruijn–Newman heat family `H_t=∫e^{tu²}Φ(u)e^{izu}du` | arch-weight family `𝔇_λ=λA−P` |
|---|---|
| critical time `Λ_dBN` (de Bruijn–Pólya: real-rooted for `t≥Λ`) | critical weight `λ_c=‖A^{−½}PA^{−½}‖` |
| physical `t=0` | physical `λ=1` |
| `RH ⟺ Λ≤0` | `RH ⟺ λ_c≤1` (Weil) |
| **`Λ≥0` (Rodgers–Tao 2020, free half)** | **`λ_c≥1` (transported, free half)** |
| `RH ⟺ Λ=0`; RH-margin `−Λ` | `RH ⟺ λ_c=1`; RH-margin `1−λ_c` |

Orientation: increasing `λ` (more archimedean weight) ↔ increasing `t` (more heat) — both RH-favorable — so the RH-margins identify, `(1−λ_c) ↔ (−Λ)`.

**Transport lemma (load-bearing):** *a uniform Weil margin forces `Λ<0`.* If `𝔇_1=A−P ⪰ ε>0`, the real-rootedness (Hermite–Biehler/Hankel) form `Q_t` of `H_t` satisfies `Q_0=A−P` and `Q_t=Q_0+t·∂_tQ+O(t²)` with `∂_tQ` bounded on band-limited test functions (the heat generator `−∂_{zz}` acts boundedly there); hence `Q_t ⪰ ε−|t|C ⪰ 0` for `t∈[−ε/C,0]`, so `H_t` is real-rooted down to `t=−ε/C` and `Λ≤−ε/C<0`. **Contrapositive:** `Λ≥0 ⟹` no uniform Weil margin `⟹ λ_c≥1`. Rodgers–Tao gives `Λ≥0` unconditionally, so **`λ_c≥1` is proven** (the Finding 3 "to verify" flag is discharged). The `Q_t` form is the **infinite version of the #104 finite-free Hankel carrier** (`t`=smoothing parameter); the tie is structural.

Net: `RH ⟺ λ_c=1` with `λ_c≥1` free — the exact mirror of `RH ⟺ Λ=0` with `Λ≥0` free, both unified with GR's `2(1−λ)→0` at λ=1.

### Finding 3c — constant-for-constant identity with the #104 finite-free carrier (exact, not analogy)
The structural tie flagged in Finding 3b is an **exact congruence-pencil identity**. Wheeler's carrier (`finite-free-convolution-flow.md`, #104) writes the degree-`d`, base-point-`t` Jensen–Hankel form as `H_d(t)=A_d^{1/2}(I+S_d(t))A_d^{1/2}` with `S_d(t)=A_d^{-1/2}δH_d(t)A_d^{-1/2}` (prime fluctuation in the archimedean metric), exact criterion **`RH ⟺ λ_min(S_d(t))≥−1 ∀d,t`** (Sylvester). My pencil factors identically: `𝔇_λ=λA−P=A^{1/2}(λI−A^{-1/2}PA^{-1/2})A^{1/2}`, so `λ_c=λ_max(A^{-1/2}PA^{-1/2})`.

| `dewitt-supermetric-no-margin` (this card) | `#104` finite-free carrier (Wheeler) |
|---|---|
| `A` (arch+pole block, `Ω_∞>0`) | `A_d` (archimedean Hankel, GORZ→Hermite, `≻0`) |
| `−P` (signed prime block of the Weil form) | `δH_d(t)` (mean-zero joint-prime Hankel) |
| `A^{-1/2}(−P)A^{-1/2}` | `S_d(t)=A_d^{-1/2}δH_d A_d^{-1/2}` |
| `λ_c=‖A^{-1/2}PA^{-1/2}‖` | `−inf_{d,t}λ_min(S_d(t))` |
| `𝔇_λ=λA−P` pencil; `λ_c` boundary | `λI+S_d` pencil (congruence = `λ=1` slice) |
| `RH ⟺ λ_c≤1` | `RH ⟺ inf_{d,t}λ_min(S_d)≥−1` |
| no-margin `λ_c=1` (Sylvester floor) | `det H_d=0` / `−1` Sylvester floor (19b) |
| `c_p∼p^{-1/2}`, `Σ_p p^{-1/2}(log p)^a=∞` | `c_p=p^{-1/2}`, same divergence (kernel §6) |

Identification: `δH_d↔−P`, `A_d↔A`, `S_d↔−A^{-1/2}PA^{-1/2}`, `λ_c=−inf_{d,t}λ_min(S_d(t))`. The `𝔇_λ`/dBN pencil is the **global (`d→∞`, all-`t`) limit** of the carrier's congruence pencil; the `−1` floor is the **same Sylvester-inertia floor** (one conjugate pair = one off-line zero = `det H_d=0`); the dBN heat-time and my `λ` are the **archimedean-dominance axis** orthogonal to `(d,t)`.

**Payoff — Rodgers–Tao discharges the lower half of Wheeler's no-margin wall.** Via `λ_c=−inf_{d,t}λ_min(S_d)`:
- **Rodgers–Tao (`Λ≥0`, Finding 3b) ⟹ `inf_{d,t}λ_min(S_d(t)) ≤ −1` — unconditionally.** This is exactly Wheeler's no-margin (`#104`: `sup_tρ_d→1`, `λ_d↓0`, "no uniform hyperbolicity margin"), now **proven** as the lower half — not conjectured.
- **RH is the remaining upper half: `inf_{d,t}λ_min(S_d(t)) ≥ −1`** (the floor is reached but never crossed).
- Together: **`RH ⟺ inf_{d,t}λ_min(S_d(t)) = −1` exactly.** The no-margin (the inf pinned to the Sylvester floor) is half-theorem (Rodgers–Tao), half-RH (the C5 crux). This sharpens `#104`'s open crux by removing the lower half via a known Annals theorem and gives it the DeWitt reading: `λ_min(S_d)≥−1` = the prime fluctuation, in the archimedean DeWitt-supermetric metric `A^{-1}`, never pushes a direction past the `−1` (timelike/null) Sylvester floor.

*(Caveat: the identification is the `d→∞`, `sup_t` limit; at finite `(d,t)` the carrier is the resolved truncation. `δH_d↔−P` / `A_d↔A` is exact in structure — arch Hankel vs prime Hankel — with the limit recovering the global `λ_c`.)*

### Finding 4 — structure-function dis-analogy (re-derives #136; sharpens A2)
GR's "why constraints" (§4.3): the deformation algebra closes with **structure functions** — `β'=[β₁,β₂]+σ(α₁grad_hα₂−α₂grad_hα₁)` (eq 23b) depends on the phase-space point `h`; non-closure-on-constants **forces** `H=0` and is the algebraic root of many-fingered time. HGT generators are by contrast **abelian/flat**: `σ_p x^m=p^{−m_p}x^m`, `∂_s x^m=−(m·ℓ)x^m` are simultaneously diagonal, so `[σ_p,σ_q]=[σ_p,∂_s]=0` (verified; = #133/#136). The "constraint not flow" headline matches but the *mechanism* differs: GR timelessness = non-abelian structure functions; HGT timelessness = order-2 FE + infinite simultaneity over a **flat generator algebra**. Confirms #136 and steers the WDW structure-function obstruction (if arithmetic) to the **moment/ring-product level** `e_m·e_{m'}=e_{m+m'}` — where C5 is already localized (#104).

### Finding 5 — rh-corp corroboration, sharpenings, and the honesty check (review of `docs/rh-corp/`, 3 subagents / 9 files, spot-checked)
The prior `rh-corp` corpus (the deep finite-free / no-margin / Hilbert–Pólya lineage) **corroborates the grade**, **elevates several findings to theorem-flavored arithmetic form**, and **corrects one framing assumption**.

**Elevations (arithmetic content the GR lens lacked):**
- **Finding 1/2 ↑ Hodge-index `(1,ρ−1)`.** The DeWitt Lorentzian `(1,∞)` supermetric (one conformal timelike direction) is the arithmetic **Hodge-index `(1,ρ−1)`**: the lone wrong-sign `ℓ` = gravitational conformal mode (Euclidean-gravity wrong-sign), Schur "project away `ℓ`" = Gibbons–Hawking–Perry rotation, **RH ⟺ exactly one wrong-sign mode**, `κ₋=p(Θ)−1` (theorist:1677, verbatim). "Conformal=timelike" is a Sylvester/Hodge-signature statement on the arithmetic side, not analogy.
- **Finding 3/3c ↑ `A` = regularizer of the integer index.** Completion `ζ→ξ` is *what makes the inertia finite*: "the prime form alone carries `κ=∞` (trivial zeros) ⟹ the archimedean Γ-factor is the REGULARIZER of the integer index" (theorist:1528, verbatim, pod-verified). Sharpens `A≻0` (#94) to: `A^{-1/2}(·)A^{-1/2}` is the regularization making `λ_c`/`κ₋` finite; prime-only is index-divergent (a sharper #137).
- **Finding 3b ↑ the free/RH asymmetry mechanism.** `Λ≥0` free vs `Λ≤0`=RH hard = **measured-vs-faithful**: dissipative/H-theorem half free (Rodgers–Tao), faithful integer `κ₋(0)=0` half = RH, "step function, no smooth law" (critic:2605). Exactly my lower/upper-half split, with the mechanism named.
- **Quantitative heart.** The no-margin's single heart = the **loglog divergence of `Σ_p p^{-2σ}` at `σ=½`** = the Hilbert–Schmidt / Fock(Shale–Bogoliubov) implementability edge by Mertens (critic:1392). Operator-theoretic form of my Finding 3c divergence.
- **Operator-algebra spine (A2).** The no-margin forces **type-III uniqueness-without-margin** ("dim→0 + gap→0 together"); type-I=gapped is foreclosed; the clock is the **Tomita modular flow** of a type-III₁ KMS state (critic:1735). Substantiates `constraint-not-flow` at the von Neumann level; ties dBN ↔ modular ↔ Connes-scaling clock.

**Honesty check — CONFIRMS the grade (reframes, not a C5 path).** rh-corp's critic independently adjudicated this whole lane as **RH-equivalent re-descriptions** — "≥8 names for the same wall," a five-frame meta-compression, and an explicit *honest kill* of the subleading-anomaly framing as "IN-CAGE (explicit-formula row), NOT new, NOT forwarded" (critic:1392); the Connes–Moscovici index for `κ₋` **is** the Weil explicit formula, so reading `κ₋` from the spectrum is circular (critic:2630). This is the **same verdict** as my BRIDGE(substrate): Findings 3/3b/3c are a D2 *kinship* (GR ↔ arithmetic, a cross-parent prediction), **not** a C5 path.

**Framing correction (honest).** rh-corp has **no Wheeler–DeWitt/supermetric material**: its lone "DeWitt" token is a *codename* for a Pfaffian/`(−1)^F` index (theorist:336, verbatim), not Bryce DeWitt. The WDW-supermetric bridge is **sourced solely from Giulini 2011 — genuinely new.** What it adds beyond rh-corp's arithmetic Hodge-index picture is the **GR-side unconditional degeneracy** (Giulini's `λ=1` ellipticity loss); this card is the bridge between them.

**Cautions inherited (for the 2→3 gate).** (i) **Conductor-matching:** the ζ-vs-fake `λ_c` separator can be a G2-tautology unless re-validated conductor-matched (critic:380). (ii) **Spectral pollution:** raw `λ_min(S_d)` is pollution-sensitive (Levitin–Shargorodsky); use a Spec₂/Davies–Plum-stable certificate `min_z(Re+|Im|)` (engineer). (iii) **Moment/HB blindness:** symmetric moments see only `{z_ρ²}`; off-line *ordering* (Hermite–Biehler) carries RH and is invisible to a bare Hankel (critic:570).

## Door / grade
BRIDGE (substrate). Each leg is parent-provable (Weil positivity; Rodgers–Tao `Λ≥0`; de Bruijn–Pólya monotonicity; the DeWitt symbol computation), so no C5. The new content is the **D2 unification** of GR canonical gravity and arithmetic under one structural law, with RH located as the cone-boundary coincidence and the **free half now anchored to a hard theorem (Rodgers–Tao), not a corpus conjecture**. Joins the D2 evidence rows (corank `F_q⟷ℚ`, orthogonality meta-theorem). Adds nothing to the NATIVE/C5 count.

## Gates
- [x] 0 → 1: dictionary + Findings 1/2/4.
- [x] 1 → 2: Finding 3 resolved — explicit family `𝔇_λ=λA−P`, margin `m(λ)=λ−λ_c`, `m(1)=0⟺RH`, GR mirror `2(1−λ)`, D2-strip done (substrate). No open dependency except RH itself (the apex, not a gap in the structural claim).
- [ ] 2 → 3: Lean anchor **DONE** for the finite congruence-pencil algebra in Finding 3c:
  `congruencePencil_factorization` and `congruencePencil_add_primeBlock` in
  `formal/GaloisForLFunctions/CongruencePencil.lean`. Remaining Lean targets, if wanted: the spectral
  `λ_c`/eigenvalue floor, the finite-to-infinite Hankel carrier limit, the Rodgers-Tao/de
  Bruijn-Newman transport, and the RH equivalence.
- [ ] 3 → 4: "Canonical gravity and arithmetic both sit at the kinetic degeneracy of their defining symmetry."

## Cross-references
- `constraint-not-flow-theorem.md` — proven WDW `ĤΨ=0` form; this card is its metric/geometric face.
- `archimedean-generator-axis-mode.md`, door #133/#136 — abelian/diagonal generators (Finding 4).
- `../../door/bucket-the-no-margin.md` #89–94, Thm 7 #91 — the no-margin = the cone boundary (Finding 3).
- `orthogonality-meta-theorem.md` #137 — why `λ_c` is archimedean ⟹ the coincidence is RH, not free.
- `finite-free-convolution-flow.md` / `weil-positivity-operator.md` (#104/#38) — the moment-level C5 target Finding 4 points to; `Q_t` (Finding 3b) is the infinite version of the #104 Hankel carrier with `t`=smoothing.
- Rodgers–Tao 2020 (`Λ_dBN≥0`, Newman's conjecture), de Bruijn–Pólya monotonicity, Hermite–Biehler/Hankel real-rootedness — imports anchoring Finding 3b.
- `theorem-m-with-margin-endpoint.md` — Theorem M (Haufschild, Lean-verified) is the **proven with-margin, sign-definite endpoint** of this `A_d`/`S_d` structure (`C_d=A_d`, atom `p=√(2/e)>½`); the two obstructions to RH-transfer (amplitude-vs-phase; margin `p→½`) are named there.
- support-extraction-log.md #94/#95 — the EMBASSY this card theorem-backs and corrects.

## Log
- 2026-06-19 — created in 1-in-progress from Giulini 2011 (read in full); Findings 1/2/4 settled, Finding 3 posed as open D2 core.
- 2026-06-19 — Finding 3 **resolved → D2 substrate**: built `𝔇_λ=λA−P`, `λ_c=‖A^{−½}PA^{−½}‖`, margin `m(λ)=λ−λ_c`, `m(1)=0⟺RH`, mirroring `f_GR=2(1−λ)`; D2-strip gives a kinship (defining symmetry → kinetic degeneracy), unconditional in GR, RH-bearing in arithmetic (because `λ_c` is archimedean, #137). Moved to 2-fully-proven.
- 2026-06-19 — **Finding 3b added**: the free half `λ_c≥1 ⟺ Λ_dBN≥0` proven via the transport lemma (uniform Weil margin ⟹ `Λ<0`, by de Bruijn–Pólya + first-order heat perturbation), so Rodgers–Tao `Λ≥0` pins `λ_c≥1`. The Finding 3 "to verify" caveat is discharged; the dBN heat family and the arch-weight family are one no-margin, `Q_t` = infinite #104 Hankel carrier. No web search; reasoning + paper + corpus only.
- 2026-06-19 — Leaner: added Lean anchor for Finding 3c's finite congruence-pencil algebra:
  `congruencePencil_factorization` and `congruencePencil_add_primeBlock` in
  `formal/GaloisForLFunctions/CongruencePencil.lean`. Created the exact split card
  `../3-formalized/finite-congruence-pencil-factorization.md`. Parent remains in `2-fully-proven` because
  the spectral `lambda_c` statement, finite-to-infinite Hankel carrier limit, Rodgers-Tao/de
  Bruijn-Newman transport, and RH equivalence are not Lean-formalized.
