# 03 — The Theorem Chain Toward RH (What Must Be Proven)

> **Scope.** The **theorem shapes that must be proved true** to arrive at a proof of RH — the
> Theorems A–L and the bridge theorems (§5), reconciled with the proven reductions and the "one wall,
> many names." A *map of the conditional structure*, not a proof and not a claim that any step is
> closed. Every node is register-tagged. No proof of RH.

---

## 0. The target, stated precisely

RH = the nontrivial zeros of `ζ` (equivalently the zeros of the completed `ξ` in the critical strip)
lie on `Re(s) = ½`. In the transport picture:

```
   RH  ⟺  supp μ_ξ ⊂ {Re s = ½},   μ_ξ = (1/2π) Δ log|ξ|  (the source measure on zeros)
       ⟺  (1/2πi) ∮_{∂R} (ξ'/ξ)(s) ds = 0  for every rectangle R strictly off the critical line.
```

So a proof must control the off-line contour charge of `d log ξ`. Everything below is organized as
*what forces that charge to vanish.*

---

## 1. The dream bridge theorem

`[CONJECTURE — the hard arrow]`

> **Transport-to-source bridge.** The completed transport features force source-measure confinement:
> ```
>   phase-weld cancellation + cross-lane association + Berry two-path equalization
>   + zero-shadow connectivity + survivor spines + reset-occupation centring
>   + observed-volume covariance + phase-space signed area + two-clock seam
>   ⟹  supp μ_ξ ⊂ {Re s = ½}.
> ```

This is "the dream theorem." **The hardest step is the arrow.** The experiments are statistical and
windowed; RH is all-scale and universal. A proof must upgrade *generic-window transport signatures* to
*all-scale off-seam source exclusion*. This upgrade is unproven and is where the real difficulty sits.

---

## 2. The concrete two-lemma bridge

A more realistic route splits the arrow into a *detection* lemma and a *confinement* lemma:

**Lemma 1 — off-line zero creates an off-seam transport defect.** `[CONJECTURE; locally PROVED]`
If `ρ = β + iγ`, `β ≠ ½`, the local pole model `ξ'/ξ(s) ~ m/(s−ρ) + g(s)` forces at least one off-seam
defect: an off-centre reset-occupation centre at `σ=β`; an off-line observed-volume anomaly; an off-line
phase-space signed-area defect; an off-line survivor spine; an off-line zero-shadow tear; an off-line
gate/tension seam; a nonzero contour charge; or a Berry imbalance that cannot be rerouted into
seam-relative phase. *The local pole model itself is `[PROVED]`* (self-verified):

```
   (log Ξ)''(t) = Σ_ρ (½+it−ρ)^{-2};   under RH < 0 everywhere (log|ξ(½+it)| concave);
   off-line FE-quartet ⟹ local convex window  2(a²−τ²)/(a²+τ²)² > 0,  |t−γ| < a,  a = |½−β|.
```

**Lemma 2 — completed transport forbids off-seam defects.** `[CONJECTURE — OPEN CORE]`
All nonextinct, source-carrying, coupled-lane, measure-covariant transport defects are confined to
`Re(s)=½`.

Then: `off-line zero ⟹ off-seam defect (L1) ⟹ contradiction (L2) ⟹ RH.` Lemma 2 is the genuine open
core; Lemma 1's local half is in hand, its *global/all-scale* half is not.

The RH-false contrapositive is the same statement:
```
   off-line zero  ⟺  off-seam source-carrying transport defect,
```
with "source-carrying" meaning nonzero logarithmic residue / source measure (a random off-seam artifact
does not count).

---

## 3. The Theorem ladder (A–L) — what each must become

The program is organized as theorem *shapes*, ordered by strength. They are the detectors Lemma 1 needs;
a proof requires upgrading each from a windowed statistic to a coordinate-invariant, all-scale statement.
Status tags reflect what is actually established.

| | Theorem shape | What must be proven | Status |
|---|---|---|---|
| **A** | far-left phase-weld: `Δ_P → log 2` for true, `Δ_{P_N} → 0` for finite | the clean-strip limit + finite collapse | `[CONJECTURE]`, strong numerics |
| **B** | transition-band transport metric `d_transport(P,P_N) ≥ c > 0` | a multi-feature metric separating true from finite/random | `[CONJECTURE]` |
| **C** | coupled low-reserve lane co-failure excess `≥ c > 0` | a new cross-σ invariant, positive for true only | `[OBSERVED]` |
| **D** | association-gate `λ₁(G_true) ≥ λ₁(G_finite)+c` | the non-product sigma-lane measure as a spectral gap | `[OBSERVED]` |
| **E** | **Berry two-path completion switch** | derive lane-magnitude equalization at `σ=½` from `ξ(s)=ξ(1−s)` | `[OBSERVED]` — *most promising* |
| **F** | observed-volume covariance `Cov(O,δV) > 0` (true) / `< 0` (controls) | a natural measure on the transport | `[OBSERVED]` |
| **G** | phase-space caustic `∫O dθ > c > 0` (true) / wrong sign (finite) | a signed action integral / symplectic lift | `[OBSERVED]` |
| **H** | phase-regulated dissolution exits | lawful (small phase-link) cancellation decay | `[OBSERVED]` |
| **I** | **reset-occupation centre recovers `β`** | `|1/(s−ρ)| = 1/√((σ−β)²+τ²)` ⟹ centre at `σ=β`; all centres `½` ⟹ RH | `[PROVED]` local model; `[CONJECTURE]` global |
| **J** | two-clock gate/tension covariance sign-crossing | finite-prime gate anti-timed with true tension in the strip | `[OBSERVED]` |
| **K** | context-fragility monotone `L_P(α) ↓` | native-context anchoring of the phase layer | `[OBSERVED]` |
| **L** | **right-strip collapse**: `σ>1 ⟹ P_N → P` | the mandatory sanity boundary (all separations vanish) | `[PROVED]` (Euler convergence) |

> The **theorem-ready** pieces to isolate first: **(E)** the Berry switch (derivable from the FE),
> **(I)** the reset-occupation local pole model (directly detects `β`), **(G)** the phase-space signed
> area (a candidate action integral), **(F)** observed-volume covariance (a natural measure), **(D)** the
> association operator as a continuum spectral kernel `K_q(σ,σ')`, and the canonical object `ω = d log ξ`.

---

## 4. The same target, named by its many equivalent apex forms

`[BRIDGE reductions PROVED; the apex itself OPEN]`

The genuine RH content is **one wall with many names**. These are the equivalent forms the completed
positivity theorem can take — proving *any* one (unconditionally, all-scale) is the apex:

1. **`κ₋ = 0`** — the faithful Krein–Langer / Sylvester index of the completed carrier `−Ξ'/Ξ` vanishes
   (`κ₋ = 2·#off-line zeros`; Lean-verified `multiPair_carrier_exact_neg_inertia`, `fe_quadruple_kappa_two`).
2. **`Q_W ⪰ 0`** — the explicit-formula quadratic form of signature `(1|∞)` is positive semidefinite;
   equivalently the single archimedean direction `V_arch = Re ψ` does not go negative.
3. **Positivity of the FE-polarization** — RH = positivity of the archimedean polarization (Weil); the
   prime structure carries no polarization.
4. **`m_ξ ∈ N₀`** (Herglotz / Krein–Langer), equivalently the *two-condition* faithful test
   `H = [m_{i+j}] ⪰ 0 ∧ H' = [m_{i+j+1}] ⪰ 0`.
5. **Uniform Laguerre–Turán / Hankel hierarchy** `det H_d ≥ 0 ∀ d, t` (Pólya–Jensen). The `d=2` leader
   (`log|ξ(½+it)|` concave) is classical; the **uniformity in `d`** is the open part.
6. **G5 unitary holonomy** — `ι` acts unitarily on the completed space (the `F_q` analogue is Deligne's
   Weil II).
7. **`Ω ≽ Π`** (M5 contraction) — `#neg(Q_W) = 0 ⟺ ‖P̃‖ ≤ 1 ⟺ Ω ≽ Π`, `P̃ = Ω^{-1/2}ΠΩ^{-1/2}`.

> **The seam-coordinate finite form, and what carries RH `[VERIFIED — comp81; no-roleplay-items §5–6]`.** In the
> reciprocal-seam chart these become `H^0_d = M_d(ν') ⪰ 0`, split `H^0_d = H^-_d + a_*v_*v_*^T`. The archimedean
> budget is `≈ a_*` (`s_d(arch only) ≈ 0.16`; the Γ-factor's pole+trivial-zero lattice `2|w|=4N+1` is the
> Connes–Consani–Moscovici prolate Hermite grading, `a_*` = the N=1 level), and matches their archimedean Sonin
> positivity *unconditionally*. The **RH content is the prime/finite-places demand** `a_c(d)` that eats the budget to
> `s_d→0⁺` — conjecturally the **semilocal** prolate positivity (arXiv:2310.18423). Watch the **integer `κ₋`**: the
> scalar `s_d=0` is only its rank-one shadow (a sign-fake has `κ₋=2` with `s_d>0`, comp81), so the apex is `κ₋=1
> from source` (the carrier) ∧ `s_d>0` — the index, not the scalar.

> **Crucial separation `[PROVED — BRIDGE]`:** `ω = 0` (realization / "a motive exists" / the DSS
> keystone) is a **different** apex from RH. **`ω = 0 ⇏ RH`** — already over `F_q` both hold for separate
> reasons. The aim "G1–G4 forces G5" is **false as stated** and must be weakened to **two apexes joined
> only at the archimedean seam**:
> - **DSS / value-arithmetic apex** — Schanuel-for-prime-logs (`{log p}` algebraically independent), the
>   realization/transcendence axis (`corank^{(T)} = ∞` for `T ≥ 2`).
> - **RH / positivity apex** — `κ₋ = 0` / `Q_W ⪰ 0`, the localization/positivity axis.

---

## 5. The dependency map (what must be proven, layered)

```
                       RH  ⟺  supp μ_ξ ⊂ {Re=½}  ⟺  off-line contour charge = 0
                                          ▲
        ┌─────────────────────────────────┴─────────────────────────────────┐
   Lemma 1 (detect): off-line zero ⟹ off-seam defect          Lemma 2 (confine): defects ⟹ seam
   local pole model PROVED (Thm I, §3 concavity)               OPEN CORE
   global/all-scale upgrade OPEN                                          │
        │                                                                  │
        └────────────► the apex positivity (one wall, §4 names) ◄──────────┘
                       κ₋=0 = Q_W⪰0 = FE-polarization⪰0 = m_ξ∈N₀
                       = det H_d≥0 ∀d,t (uniform-in-d) = Ω≽Π = G5 unitary
                                          ▲
                       distinct apex, joined only at the seam
                       DSS / Schanuel-for-prime-logs ({log p} alg. indep.)
                                          ▲
                       PROVEN FLOOR: corank=∞ ({log p} ℚ-LINEARLY indep, Baker)
                       OPEN: corank^{(T)}=∞ for T≥2 (begins at weight j=2)
```

**Proven floor (the BRIDGE layer, all `[PROVED]`):** the FE mirror law and order-2 constraint; the
critical line as `Fix(ι∘conj)`; the local pole model and `log|ξ|`-concavity; the corank `∞−1` seam invariant;
the linear floor `corank = ∞` (Baker); the Schur–Cohn / Bezoutian inertia bricks; the finite Laguerre
`d=2` leader.

**Open cores (the apex, all `[OPEN CORE]`/`[CONJECTURE]`):** Lemma 2 (global confinement); the
uniform-in-`d` Hankel hierarchy; Schanuel-for-prime-logs; and the bridge arrow of §1–§2 that links the
transport signatures to the source-measure confinement.

---

## 6. What a proof must additionally respect (the guardrails)

Any candidate theorem chain must survive the hardest checks, or it is `search`, not a proof:

- **Pass the surrogate ladder:** the refined statistics must *separate genuine hypertranscendent `Λ`
  from an FE-exact, correct-zeros analytic fake*. If a Davenport–Heilbronn-type surrogate reproduces
  them, the program reduces to "analytic continuation ≠ truncation," a known fact.
- **Be faithful, not measured:** use the integer index `κ₋`, not a density/variance — soft/second-moment
  methods are structurally RH-blind.
- **Cross the affine confinement:** flow/positivity/de-Bruijn/energy/Laguerre methods are affine-confined
  and *cannot reach the transverse seam* `[𝔾_a,𝔾_m]`; the apex needs constraint/transcendence-axis tools.
- **Not be RH-equivalent packaging:** ~10 reframes all reduced to Weil–Connes positivity / `Λ = 0`; a
  genuine step must *separate* the realization family's RH-axis, not restate it.

---

## 7. The faithful-index bridge package

This sharpens §4–§5 into a *constructive* obligation list. It reframes the apex from "name a positivity"
to "**source-build** the object and prove its index vanishes."

### B-min. The minimal required proof statement `[OPEN]`

> From the Euler product, `Γ`, the pole, and the functional equation **alone**, construct a source-built
> completed transport/polarization object whose faithful negative-square index is `κ₋`, prove `κ₋ = 0`,
> and show this index equals the off-line zero count.

Every word is load-bearing: **source-built** (no zero-feeding); **completed** (includes `Γ`);
**transport/polarization** (not scalar amplitude); **faithful** (not a measured trace); **index** (a
dust-proof integer); **equals off-line zero count** (connects to RH).

### Failure mode to avoid `[NO-GO]`

A theorem that only says "a familiar positivity criterion is equivalent to RH" is **not progress** — ~10
such routes reduce to the same wall. A bridge must either (i) construct the source object *before* reading
zeros, or (ii) produce a new canonical transport invariant that passes adversarial fake-family tests.

### The two live entrances `[CONJECTURE / STRATEGIC]`

Two coordinate presentations of the same missing archimedean-polarized object:
1. **Jacobi–Loewner–Krein–Hodge entrance (object-first).** Build, from Euler/PNT-scale source data, `Γ`,
   the pole, and the FE, a completed Jacobi/membrane object; prove it is a positive contraction
   (equivalently `κ₋ = 0`) and that its faithful index equals the off-line zero count.
2. **Jensen / Laguerre–Pólya entrance (scalar-polynomial-first).** Prove a uniform Jensen-polynomial /
   Pólya–Schur stability theorem for `ξ` beyond fixed-degree asymptotics — strong enough to place `ξ` in
   the Laguerre–Pólya class.

`[CONJECTURE]` These are likely the same object in two coordinates; the equivalence is itself open.

### The 5-form strengthened bridge package `[OPEN]`

A proof-grade bridge must supply all five theorems:
1. **Source-built object theorem** — construct the completed object without using zeros as input.
2. **Faithful index theorem** — prove the object's integer index equals the off-line zero count.
3. **Index-vanishing theorem** — prove the index is zero *from the source construction*.
4. **Fake-family separation theorem** — prove Davenport–Heilbronn-style / FE-exact / correct-zero
   surrogates fail at a *named* source gate.
5. **No-margin theorem** — prove the mechanism survives the zero-margin nature of RH (no hidden spectral
   gap, domination reserve, or finite cutoff is used to force the required sign).

The transport carrier of the mechanism view is compatible with this package **iff** its carrier can be
identified with the same faithful completed object; until then it is a parallel candidate, not a proof.

### The irreducible in one line, and the ranked proof shapes `[STRATEGIC — gpt/37]`

Stripped of scaffolding, the five-form package is one statement: **the completed explicit formula is a
one-sided Loewner domination theorem** — `−R^P ⪯ M_triv`, i.e.
`λ_max(M_triv^{−1/2}(−R^P)M_triv^{−1/2}) ≤ 1` for every `d`. The proof object is therefore a **source-built
factorization/contraction giving `I − K_d ⪰ 0` at zero margin** (the prime saturates the budget to `~24`
digits — no slack), not a "large-beats-small" estimate. It lives on a **three-stratum reciprocal divisor**:
pole `y=−4` (entireness) + trivial-zero chain (positive protector `μ_triv`) + nontrivial divisor (forced onto
`ℝ_{>0}`). Ranked routes: (1) one-sided Loewner / boundary-Weyl `K⪯I` as a compression of a single
**non-compact** completed-boundary operator; (2) Weil-form pullback `p↦h_p` (`Q_0[p]=Q_W[h_p]`); (3)
discriminant / Gram–Heine asymptotics, now requiring the exact cross-positive interval plus a summed
domination estimate; (4) direct Jacobi / Hankel-determinant (lowest
odds — intrinsically hard-edge ill-conditioned). The **fake-family separation theorem** (form 4 of the
package) acquires a concrete first test: the **reciprocal trivial-zero domination on Dirichlet `L`-functions**
— genuine Euler-product `L` should pass `K_d⪯I`, Davenport–Heilbronn should fail by `λ_max>1` (forward agenda
`research-topics.md` #38).

---

## 8. SOTA integration of the apex

- **APEX-B (positivity) is the Pólya–Jensen program; the live construction of the archimedean positivity
  is Connes–Consani.** `RH ⟺` uniform Jensen-polynomial hyperbolicity is **Pólya 1927**; the SOTA is
  **Griffin–Ono–Rolen–Zagier (2019)** — fixed-degree eventual hyperbolicity (`d ≤ 8`, density-1 for each
  `d`), with the *uniformity in `d`* still ⟺ RH and open. Separately, the **Connes–Consani 2014–2026**
  program is *actively constructing* the archimedean positivity this chain only *names*: the **arithmetic
  site** (2014), **Riemann–Roch for `\overline{Spec ℤ}`** (2022), **the Jacobian of `\overline{Spec ℤ}`**
  (2026), **zeta spectral triples**, and a **semilocal prolate-wave-operator spectral realization** of
  the low-lying zeros. *A serious bridge attempt should engage this line directly* — it is the strongest
  current handle on the source-built faithful-index object and on Conjecture E (the realization is
  archimedean/positivity).
- **APEX-A (value) is Schanuel-for-prime-logs, beyond current reach.** Baker gives the linear floor;
  algebraic independence of even `{log 2, log 3}` is open; Ax–Schanuel (Gao–Klingler 2023; elliptic
  variations 2025) is geometric/Hodge, not the arithmetic statement. *Role (scoped):* keep APEX-A as "why
  the native transcendence detector is hard," **not** a necessary RH route unless a theorem links it to
  the faithful positivity index.
- **Master Conjecture split:** the §4 apex names should be read as **Master 1** (transport face — name the
  cohomology group) + **Master 2** (faithful-index face — *source-build* the κ₋ object without
  zero-feeding) + an **identification theorem** between them (open). "`κ₋` is the holonomy" is a target to
  be *built*, not a definition to be *named*.
