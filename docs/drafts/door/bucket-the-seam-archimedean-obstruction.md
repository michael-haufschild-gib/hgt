# Bucket X3 — The seam / the archimedean obstruction

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** Both apex faces (RH and DSS) localize to **ONE archimedean seam** but split into
two axes: value/transcendence for DSS and polarization/positivity for RH. The seam is the
additive↔multiplicative divide = the period/non-period divide = the missing Frobenius at infinity (F₁).
**Work package this seeds.** Aim every apex attack at the **Γ-factor / `s=1`-Laurent (Stieltjes) data**,
not the integer ζ-values (which are structurally apex-blind); attack the **one explicit class `ω`**
(the seam's monoidality obstruction).

> **The structural payoff of this bucket:** it turns the parent project's empirical observation —
> "prime-side / multiplicative methods are RH-blind / circular" — into a **structural theorem**:
> multiplicative-only tools live on the wrong side of the seam and are *blind to both apex
> obstructions.* This is a grading rule for the whole corpus: a SEED on the multiplicative/prime side
> is structurally apex-blind; the live SEEDs are archimedean.

---

## The seam = the period / non-period divide (#74, #81, #83)
- #74: DSS = alg. independence of `{π} ∪ {ζ(odd)} ∪ {γ_n}`. The first two are **periods of `MTM(ℤ)`**
  (GPC-shaped, tooled); the **Stieltjes constants `γ_n` are conjecturally NOT periods**
  (exponential-period-like regularization constants). **DSS = GPC + (DSS-cross),** the cross-divide
  statement neither GPC nor the motivic Galois group sees. **G2's genuinely-open core is the Stieltjes
  side.** (→ [[G2-multi-q-siegel-shidlovsky]])
- #81 the seam = the completion `ξ = (Γ-factor) × ζ` glues period to non-period; each secular moment
  `P_k = ζ(k)[period] − a_{k−1}[non-period]` is literally a period+non-period sum glued at the seam.
- **#81 §2–4, corrected by #191/#54: BOTH apex faces meet at the SAME archimedean seam, but split into
  two distinct obstructions:**
  - **A2/DSS** = "is the non-period jet generic?" (the Stieltjes side, archimedean).
  - **A1/RH** = "is the archimedean-completed carrier type positive?" (`m_ξ` Herglotz / `κ₋=0`).
  - **The surviving unified bet:** the field needs a shared archimedean locus with **two inputs** — the
    Nesterenko/value-independence lower bound forcing DSS-cross [A2], and the Herglotz/FE-polarization
    input forcing `κ₋(m_ξ)=0` [A1]. The multiplicity estimate is the A2 rigidity, not a proof of A1.
    (→ [[bucket-A1-A2-unification-the-carrier]])
- **#81 prediction (the grading rule):** apex progress must engage the **Γ-factor / `s=1`-Laurent
  (Stieltjes) data, NOT the integer ζ-values.** Multiplicative-only tools (Euler product, prime sums,
  ζ-values) are **structurally blind** to both apex obstructions.
- #83 §5 the unified stone: *"the two places of `G_L` do not conspire — neither in SIGN (RH/A1) nor in
  ALGEBRA (DSS/A2)"* — the same archimedean non-conspiracy driving both.

## The missing Frobenius at infinity = F₁ (#88 §5, #85, #90, #98)
- #88 §5 the single missing brick over ℚ, named precisely: an **arithmetic cohomology with a Frobenius
  at the archimedean place (= F₁)** whose `H^1` Frobenius spectrum is the ζ-zeros. *The entire ℚ-frontier
  localizes to this one absence.* (the precise demand on [[G5-unitarity-gatekeeper]])
- #85 the missing Frobenius has **three names = one absence:** B24 (a spectral Galois group acting on
  the zeros) = B8 (missing Frobenius) = DSS (zeros transcendental ⟹ no Galois action). Over function
  fields the action exists (Frobenius = Weil); over ℚ `G_L` (on the primes) is the only surrogate,
  reaching the zeros only through the open carrier reconstruction.
- #90 the operator-level statement: **`D = x d/dx` is a derivation — additive (⊕), unbounded, NO trace,
  type III** ⟹ needs ζ-regularization; difference operators (finite places) are
  contracting/trace-class/multiplicative (⊗). **The de Branges `⊗↦⊕` obstruction (`ω≠0`) at operator
  level = "D is a derivation, not a Frobenius."** The **Γ-factor = ζ-regularized det of D = Kurokawa
  absolute zeta**. **`ω=0 ⟺ D is trace-class (F₁-regularized) ⟺ Hilbert–Pólya ⟺ RH`** — unifies 5
  programs (B5 monoidality, Deninger, B8 F₁, B35 q→1, B18 HP). (→ [[G4-multi-q-picard-vessiot-and-langlands-group]] for `ω`)
- #98 Attack 6: the four "missing structures" = ONE obstruction = **Connes type-III no-trace** (the
  `ℝ_{>0}^×` modular flow has no fixed points/trace); the trace defect = the Γ-factor = Kurokawa
  absolute zeta. Anchored in real absolute-zeta theory.
- **Moonshot attack routes (#203–#207):** five low-prior backlog cards now target the same `ω/F₁`
  knot: knot-at-infinity meridian, spinorial `√Frob`, hyperreal infinite prime, `2πi` log-monodromy
  (**test first** against `compute-omega §S`), and Type `III₁→III_λ` thermal Frobenius. They are not
  banked mechanisms; they are probes for how an archimedean Frobenius might be made explicit.

## The two transcendence towers don't interact — the seam in tower form (#80 SEED-U)
- The spectral/difference-Galois tower (`ζ→𝒵→…`) is **dead at level 2** (the superzeta has no Euler
  product, by the First Theorem); the additive/period/motivic tower is **alive**. **The two towers'
  non-interaction IS the seam:** `[𝔾_a, 𝔾_m] ≠ 0`. Ledger witness (`SuperzetaResolvent`): the superzeta
  is the **additive resolvent trace** `Σ_i(1−r_iX)^{−1}` (Σ, not ∏) — the seam itself is a Lean theorem.

## The shoreline localization — the wall is one term governed by Γ (#92 §5)
- §5 the prime sum (compact `𝕋^∞`, `|·|²` data) is **manifestly positive for free** (Sato–Tate/Ramanujan
  compactness, ledger `satake_trace_re_mem_Icc`); the **archimedean Γ-term is the SOLE obstruction to
  Weil positivity** — "the wall is the place at infinity," one specific term governed by one wild
  function Γ (`Γ(s+1)=sΓ(s)`, Hölder-wild).

## The regularization-freshness meta-principle (#74 SEED-S, #93)
- **SEED-S (#74):** zeta-regularization / Hadamard-finite-part is a **transcendence-CREATING
  operation** — it manufactures constants algebraically independent of the input's periods (`log 2π =
  −2ζ'(0)`, Glaisher `ζ'(−1)`). Candidate **G16 (regularization-freshness):** "the regularization
  constants attached to a hypertranscendental object are transcendentally fresh relative to its periods
  — this freshness is the field's irreducible new transcendence." *Explains structurally why the field
  is not a sub-case of period theory.* (→ [[bucket-new-sibling-conjectures]])
- #93 §3: the Stieltjes constants are the **rung ABOVE Baker** — a non-Kummer edge period sitting
  between solved `L(1,χ)` (Baker) and non-motivic `ζ(½)`; "is there a Baker for the Stieltjes
  constants?" is the seam's concrete G2 sub-target.

## Why DSS is hard — the A2/transcendence mechanism (#176/#178/#183/#196)
DSS is hard because the relevant values `{γ_n}` are **`∂_s`-derivative regularization constants** in the
wild kernel `K=ker(G^exp↠G_mot)`, beyond the reach of ordinary value-theory tools, and over ℚ there is
no single Frobenius to pin their values. The regular side has footholds (`{log p}`, `{ζ(odd)}`,
motivic periods); the exponential/Stieltjes side has none even at `γ_E`. Function-level information is
maximal but useless for values: Hölder/digamma hypertranscendence gives a huge differential Galois group,
not algebraic independence of constants. The p-adic per-place carriers `{Γ_v}` (#196/#197) give shadows,
but the required complex↔p-adic/F₁ synthesis is exactly the missing value-lift. This is the A2 companion
to #96's RH-hard mechanism: RH sits at a positivity forcing-degeneration point, while DSS sits at the
function/value gap in the wild kernel.

**Cohomological grading of the wild kernel (#198):** for the pro-unipotent Lie algebra of `K`,
`H₁(Lie K)` is the exponential-corank/generator count (one Stieltjes generator per Laurent order), while
`H₂(Lie K)=ω_mot` is the relation class. The moonshot reformulation is DSS-cross ⇔ `K` is free
pro-unipotent ⇔ `H₂(Lie K)=0`, with the value/regulator realization still the Fields-Medal wall.
**Hypertranscendence-axis synthesis (#208):** this is now the primary frame: function-level
hypertranscendence is mapped obstruction theory, while value-level hypertranscendence is the wild kernel
`K`; RH is the separate FE-polarization slice rather than a consequence of the transcendence axis.
Rung evidence for the graded-corank side is now recorded on #125: PSLQ finds no low-height relation at
rung 1 or at degree 2 over `𝓡`, supporting full graded corank through the first open algebraic rung while
leaving the all-degrees DSS / `K`-free apex completely open.

---

## The seam in one screen
| Multiplicative wing (FREE, zero-blind) | SEAM (the difficulty) | Archimedean wing (the frontier) |
|---|---|---|
| Euler product, primes, `σ_p` | `ξ = Γ-factor × ζ` | Γ-factor, pole at `s=1` |
| periods `{π, ζ(odd)}` (`MTM(ℤ)`) | each `P_k` = period − non-period | non-periods `{γ_n}`, log2π (Stieltjes) |
| trace-class / ⊗ / type II | `ω ≠ 0`? (`[𝔾_a,𝔾_m]`) | derivation `D` / ⊕ / type III, no trace |
| has Frobenius (over `F_q`) | the missing Frobenius = F₁ | needs an F₁-Frobenius at ∞ |
| compact, positive for free | `Z_n ≻ A_n`? | the sole obstruction to `Q_W⪰0` |

## Open core / the work package
**Two archimedean inputs at one seam:** a value-independence / regularization bound on the
`s=1`-Laurent / Γ-factor (Stieltjes) data for DSS-cross (A2), and a separate FE-polarization positivity
input forcing `κ₋(m_ξ)=0` (A1). Sub-targets: compute `ω`
([[G4-multi-q-picard-vessiot-and-langlands-group]]); a "Baker for the Stieltjes constants"
([[G2-multi-q-siegel-shidlovsky]]); the regularization-freshness conjecture G16
([[bucket-new-sibling-conjectures]]).

## Cross-references
- [[bucket-A1-A2-unification-the-carrier]] — both faces meet at one seam but split into two apexes.
- [[G2-multi-q-siegel-shidlovsky]], [[G5-unitarity-gatekeeper]] — the two faces the seam controls.
- [[bucket-function-field-proving-ground]] — over `F_q` there is NO archimedean place ⟹ no seam ⟹ all
  gatekeepers are theorems. The seam is exactly what ℚ adds.
- [[bucket-time-and-non-holonomic-time]] — the archimedean place `D` is the scaling clock; the **trace
  defect** (no trace / type III / `ω≠0`) = the **arrow of time**, and **corank ∞ = the WDW emergence of
  time** (over ℚ no single Frobenius = no global clock; over `F_q` corank 1 = a static universe). The
  `∞−1` seam gap = the missing *global clock*.
