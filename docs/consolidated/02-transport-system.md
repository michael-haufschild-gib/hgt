# 02 — The Completed ζ Object as a Constraint-Preserving Transport System (Not a Scalar Amplitude)

> **Scope.** A consolidation of the corpus's central structural claim — *"the completed zeta
> object is a constraint-preserving transport system, not a scalar amplitude object"* — and the
> mechanism that statement implies. This is the dynamic/mechanism companion to
> `01-landscape-and-geometry.md` (the static-geometry view). Sources: the light tower
> (`publications/hgt/docs/experiments/draft.md` §0–§4, §7), the synthesis
> (`publications/hgt/logs/synthesis.md` §1–§2, C2/C6), and the `2-fully-proven` / `3-formalized`
> cards. Register tags as the sources assign them. **No new mathematics.**

---

## 0. The thesis

```
   The completed zeta object is NOT a scalar-amplitude object.
   It is a completed logarithmic transport connection ω = d log ξ,
   equivalently  H(s) = ∂_s log Λ(s) = A(s) + P(s),
   A(s) = ∂_s log Γ∞(s)  (archimedean / dilation generator, "Source A"),
   P(s) = ζ'/ζ(s)         (prime / difference-base term, "Source B").
```

The object's meaningful structures are not peaks of `|ζ|` or `|ζ'/ζ|`, but phase-weld
cancellations, zero-shadow corridors, survivor spines, reset-occupation centres, two-clock seams,
observed-volume signs, phase-space caustic lifts, coupled low-reserve sheets, non-product
sigma-lane association, and Berry two-path interference (light tower §7). The hidden variable is
**lawful transport capacity** — *not how big the signal is, but whether it can keep carrying the
law* (light tower §1.3).

This thesis is the operational form of the founding principle **"the object is fixed by a
constraint, not propagated by a flow"** (the hgt charter; Hölder 1887: hypertranscendence = the
absence of a generative/algebraic-differential rule).

---

## 1. Why scalar observables fail (the empirical driver)

Across every experiment the same mistake recurs in different clothing (light tower §1.1):

```
   mean ≠ survival,   occupancy ≠ connectivity,   marginals ≠ joint association,
   residence time ≠ transition path,   amplitude ≠ phase weld,
   coordinate average ≠ observed-volume average,   lane balance ≠ Berry-relative phase.
```

> **Single-coordinate statistics destroy the constraint.** Finite Euler cutoffs can imitate a
> coordinate projection — be loud, have many events, match right-strip behaviour — but in the
> critical/left strip they repeatedly fail the *joint* constraint (light tower §1.1).

The consolidated empirical phenomenon `[OBSERVED]` (synthesis §1): in `σ ∈ [0.3, 0.5]` (fading
through `σ ≈ 0.7`), the *true* analytic continuation of the weld produces a persistent, structured,
**positive** phase-carrier defect `Δ = max(log|A|,log|P|) − log|A+P|` that **(a)** finite Euler
truncations never reproduce even as `N→∞` (amplitude grows, `Δ`-median stays `≈0`), **(b)**
amplitude-matched random-phase surrogates never reproduce, and **(c)** collapses to the
finite/right-strip value at `σ>1`. Everything else is substructure of this one fact.

---

## 2. The transport connection and its divisor-sensitivity

`[PROVED — argument principle]` (light tower §4.1)

The one-form `ω = d log ξ` transports logarithmic phase and amplitude along paths, and is
**divisor-sensitive**:

```
   (1/2πi) ∮_γ d log ξ = #zeros of ξ inside γ.
```

So `ω` is not merely a field of values — it is a **transport law that counts source charge**.
Zeros are the source charges / vortices; the source measure `μ_ξ = (1/2π) Δ log|ξ|` is supported
exactly on them (light tower §5.1). A *flow* would propagate values forward; this object instead
*constrains* them, and the constraint is what RH is about.

---

## 3. The constraint, named — there is no Hilbert–Pólya *flow*

`[PROVED — BRIDGE]` (`constraint-not-flow-theorem.md`)

The completed object is fixed by a **relation**, not a propagator:

> `Λ(s) = Λ(1−s)` — `Λ` is fixed by the involution `ι : s↦1−s`. `ι` is **order 2** (`ι²=id`,
> generates `ℤ/2`, *not* a one-parameter flow `ℝ`); it is **archimedean** (intertwined by `Γ`);
> its fixed locus is `Fix(ι) = {Re s = ½}`.

Three independent facts, one cause — *the object is constrained, not flowing*:

1. **(§1)** The flow Source B actually carries — the Kronecker flow on `𝕋^∞`, generator `∂_t` — has
   spectrum the **prime frequencies `{log p}`**, which is RH-blind (equidistribution), **not** the
   zeros. (Lean: `primeLogFrequency_eq_zero_iff`, `KroneckerFlow.lean`.)
2. **(§2)** Any operator with spectrum the zeros is a **self-adjointness = a positivity**, hence
   archimedean (orthogonality meta-theorem), not Source-B.
3. **(§3)** The governing symmetry is the order-2 reflection `ι`, not a flow.

> **Hilbert–Pólya re-posed:** stop seeking a *flow* (a self-adjoint Hamiltonian on a prime-built
> space). The correct object is the **constraint `ι`** on the archimedean-polarized completed
> space, and **RH ⟺ `ι` acts unitarily (preserves the polarization's positive form) ⟺ zeros real
> ⟺ on the line** (the G5 unitarity gatekeeper, here *derived* from the constraint principle).
> (Lean: `sigma_involutive`, `sigmaConj_fixed_iff_critical`.) Connes (1999) shows the zeros *are*
> an adelic spectrum — but only on an **archimedean-inclusive** space, confirming (2).

This is the WDW-superspace form (`ĤΨ=0`, a constraint, no `iℏ∂_t`): emergent time with no clock.

---

## 4. The transport mechanism — seven coupled components

The light tower (§4) names the mechanism's parts; each is a distinct experimental signature and,
where proven, a distinct structural fact:

| Component | What it is | Status / anchor |
|---|---|---|
| **4.1 A connection** | `ω = d log ξ` transports log-phase/amplitude; `∮ = #zeros` | `[PROVED]` argument principle |
| **4.2 A mirror seam** | the FE makes `Re=½` the fixed seam where two sides glue | `[PROVED]` `sigmaConj_fixed_iff_critical` |
| **4.3 An archimedean boundary operator** | `Γ∞` equalizes left/right and reroutes residual into phase | `[OBSERVED]`+`[PROVED]` cross-term cocycle (§6) |
| **4.4 A natural measure** | high values live on the perturbed observed-volume measure (`Cov(O,δV)>0` for true, `<0` for controls) | `[OBSERVED]` id761 |
| **4.5 A phase-space momentum** | amplitude coordinate `O` needs momentum `θ=arg P`; true lift has signed area `∫O dθ`, finite-prime is anti-symplectic | `[OBSERVED]` id762 |
| **4.6 A coupled-lane initial measure** | σ-lanes have a **non-product** joint measure (q70 association graph) | `[OBSERVED]` id771/772 |
| **4.7 A survival law** | states matter only if they survive / co-fail in linked ways (spines, low-reserve sheets) | `[OBSERVED]` id752/768 |

The mechanism is therefore **coupled-lane, measure-covariant, Berry-sensitive phase-space
transport** (light tower §4) — far richer than a scalar amplitude. The detailed experimental
evidence for 4.4–4.7 is in `06-experimental-findings.md`.

---

## 5. The transport *is* the holonomy of the affine weld connection

`[STRUCTURAL FACT + CONJECTURE]` (synthesis C2; `archimedean-generator-axis-mode.md`;
`additive-koszul-cocycle-skeleton`)

The weld lives on the affine `ax+b` group `𝔾_a ⋊ 𝔾_m` (`∂_s` = dilation, `M_p` =
translation-by-`log p`), with **universal curvature** `[∂_s, M_p] = −log p`. Decisively:

> The curvature is **object-independent** (the same `−log p` for every object). So
> hypertranscendence and any RH content live **in the holonomy, not the curvature** (synthesis §2).
> `[CONJECTURE C2]` *The weld phase carrier IS the holonomy / 1-cocycle of this flat-curvature
> (modulo universal) connection, and the Γ-completion is the additive boundary cocycle that
> trivializes the holonomy class exactly on the symmetry lane `σ=½`.*

The cocycle layer is partly formalized: with `τ_p = σ_p − 1`, the additive 1-cocycles are exactly
`τ_p a_q = τ_q a_p`, every coboundary is a cocycle (`d1∘d0=0`), and a constant-up-to-coboundary
multiplier `a = c·σ(g)/g` gauges to a constant (Lean: `additive-koszul-cocycle-skeleton`,
`cc-gauge-trivialization-identity`). The corpus's open core is whether the residual class — the
holonomy that survives — vanishes: `ω = 0 ∈ H²(G_L)` (see `03-theorems-toward-rh.md`).

This is also why **finite Euler is a wrong-transport projection**: every additive/axis-built Euler
object **decouples prime-by-prime** to `𝕋¹` (no small divisors, no resonances), so it lives on the
**flat affine orbit** and cannot carry the coupled holonomy. The flow group `𝔾_a⋊𝔾_m` is
order-preserving and *cannot reach the transverse seam* `[𝔾_a,𝔾_m]` — Hölder made mechanical
(`phase-cancellation-crux.md` §8). See `05-light-tower-challenges.md` for the consequence that
flow/positivity methods are affine-confined.

---

## 6. The archimedean boundary operator — Γ reroutes asymmetry into phase

`[PROVED — BRIDGE]` (`archimedean-prime-cross-term.md`; light tower §1.5, §4.3; Berry `id773`)

The Γ-factor is **not a smooth correction** — it acts as a boundary-condition operator for the
two-path seam geometry. The functional equation is exactly a **cocycle product relation**:

```
   ρ_∞(s)·ρ_ζ(s) = 1,   with the entire defect  χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s) = π^{s−1/2}·Γ((1−s)/2)/Γ(s/2)
   PURELY archimedean (no prime).   ι_ζ exists (prime inversion θ_p↦−θ_p, zero defect);
   ι_∞ does not  (∂_s log χ = logπ − ½ψ((1−s)/2) − ½ψ(s/2) ≠ 0);   [∂_s, σ_p] = 0.
```

So the weld **does not factor** as `ι_∞ ⊗ ι_ζ`: the obstruction is concentrated entirely in the
archimedean factor. Experimentally this is the **Berry two-path completion switch** (`id773`, light
tower Theorem E): completing `ζ'/ζ → ξ'/ξ` **exactly equalizes** the two `σ=½±δ` lane magnitudes at
`σ=½` (imbalance `→0`) and reroutes the residual into pure **relative phase**; off-centre, the
imbalance returns. *Γ-completion reroutes prime-side asymmetry into phase interference* (light tower
§4.3).

The same structure has an index reading (worklog-theorist): the weld `A + P` is *literally*
`Ω − Π` (the Maass–Selberg finite part `−(φ'/φ)(½+ir) = 2[(ξ'/ξ)(1+2ir) − (ξ'/ξ)(2ir)]`,
"structurally `Ω − Π`"), and the faithful index

```
   κ₋ = APS index:  bulk = Euler / finite places,  boundary η = archimedean,
   RH ⟺ Index = 0 ⟺ the archimedean η balances the prime bulk.
```

"The wild archimedean Γ-factor is the **regularizer of the integer index** — completion is what
makes `κ₋` exist as a finite integer" (worklog-theorist). This is the transport-system reading of
the explicit formula's signature-`(1|∞)` quadratic form `Q_W` (see `03-theorems-toward-rh.md`).

---

## 7. Transport, not amplitude — the faithful/measured distinction

`[PROVED — BRIDGE + Lean]` (`intrinsic-rh-locus-pure-polarized.md`, `kappa-minus-offline-pairs`)

The decisive reason the object is *transport* and not *amplitude*: the RH-bearing quantity is a
**faithful signed index** (a Krein–Langer / Sylvester inertia), not a magnitude or a density:

```
   κ₋ = #off-line zero-pairs (the FAITHFUL Krein–Langer index),   RH ⟺ κ₋ = 0,
   and a single off-line zero, FE-doubled, forces κ₋ = 2 exactly  (κ₋ = 2·#off-line zeros).
```

Lean-verified (axiom-clean): `kappa-minus-offline-pairs` / `multiPair_carrier_exact_neg_inertia`
(`κ₋(H) = #off-line conjugate pairs`, Sylvester) and `fe_quadruple_kappa_two` (one off-line zero
⟹ `κ₋ = 2`). The carrier is the **completed** `M = −Ξ'/Ξ` (the raw `−ζ'/ζ` has `κ = ∞` from trivial
zeros — only completion makes the index finite, worklog-theorist).

> **Why this is "transport" and not "amplitude":** a *measured* (density / type-III trace)
> positivity is **blind to density-zero off-line dust** and cannot decide RH; the **faithful**
> integer index can. Soft/variance/second-moment methods report the measured object and are
> structurally RH-blind (`erosion-threshold.md`; see `05-light-tower-challenges.md`). The transport
> picture is precisely the demand for the faithful, constraint-preserving carrier — not the loud
> scalar one.

---

## 8. The complete mechanism picture

```
   analytic continuation  =  coupled-lane, measure-covariant, Berry-sensitive
                             phase-space transport of d log ξ,
   constrained by the order-2 mirror ι (s↦1−s) with seam Fix(ι) = {Re=½},
   welded from the archimedean generator A and the prime term P,
   whose holonomy (not curvature) carries the hypertranscendence,
   whose Γ-completion is the boundary cocycle trivializing the holonomy on σ=½,
   and whose RH content is the FAITHFUL index κ₋ = 0 (not a measured amplitude).
```

Finite Euler cutoffs are legitimate in the right strip (`σ>1`) — that is why all separations
collapse there. In the critical/left strip they behave like a **projection of the wrong transport
object**: they can match amplitude, raw failure, some association, or event clocks, but not the
full coupled transport law (light tower §7).

---

## Source map

- Light tower: `publications/hgt/docs/experiments/draft.md` §0, §1.1, §1.3, §1.5, §4, §7.
- Synthesis: `publications/hgt/logs/synthesis.md` §1, §2 (C2, C6), §5.
- `2-fully-proven/`: `constraint-not-flow-theorem`, `archimedean-prime-cross-term`,
  `archimedean-generator-axis-mode`, `orthogonality-meta-theorem`, `intrinsic-rh-locus-pure-polarized`,
  `explicit-formula-as-constraint`, `phase-cancellation-crux`, `gamma-module-construction`.
- `3-formalized/`: `additive-koszul-cocycle-skeleton`, `cc-gauge-trivialization-identity`,
  `archimedean-gamma-shift-connection`, `archimedean-prime-mode-derivative`,
  `fe-constraint-critical-line-fixed-locus`, `kappa-minus-offline-pairs`, `fe-quadruple-kappa-two`,
  `finite-prime-log-flow-spectrum`.
- Worklogs: `docs/rh-corp/worklog-theorist.md` (carrier = `−Ξ'/Ξ`, `Ω−Π`, APS η-index, FE-doubling).

---

## Appendix — Minimal transport axioms for a future theorem (incorporated from the GPT consolidation pass)

`[CONJECTURE]` A theorem-level transport object — the kind that could carry the bridge of
`03-theorems-toward-rh.md` — should satisfy all of:

1. It is built from `ω = d log ξ` or an equivalent completed logarithmic connection.
2. It is invariant or stable under the FE reflection `s ↦ 1−s`.
3. It includes the archimedean `Γ` term as a **native** boundary/cofactor term (not a scalar
   normalization).
4. It has a **source-measure readout**: a contour integral, a divisor current, or `Δ log|ξ|`.
5. It distinguishes the **phase-space lift** from the amplitude projection (correct momentum
   `θ = arg P`, not just `|P|`).
6. It includes **cross-σ association**, not only lane marginals.
7. It **collapses to finite-Euler/product behaviour on `Re(s) > 1`** (the mandatory sanity
   boundary).
8. It **survives the adversarial FE-exact / correct-zero surrogate** to be called native HGT.

This is the constructive checklist behind §4 of this document: any candidate "carrier" object is
admissible as the transport invariant only if it meets all eight; axioms 4 and 8 are the ones the
current corpus has *not* yet discharged (see `05-light-tower-challenges.md` §0).
