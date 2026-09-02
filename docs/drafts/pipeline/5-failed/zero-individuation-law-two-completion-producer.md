# The individuation law: zeros are densities, not points — and the two-completion producer

- **ID:** ULF-IND-001
- **Stage:** 5-failed (producer B5 refuted on paper; bricks B1, B3 and the B5 no-go are Lean theorems)
- **Type:** CONJECTURE (universal law, frozen before proof search) + THEOREM (paper) bricks
- **Source:** learned from the two 2026-09-02 failures `ULF-PIO-001` (pole-plane index is
  Class I) and `ULF-SLC-001` (automorphic created positivity is Class II; zeros are scattering
  poles outside every `L²` Parseval identity), read against `rh-current-frontier-map.md`
  (six gates, two coupled problems), `stuck-route-obstruction-matrix.md` (W1–W11),
  `STATUS.md` F359–F378, MUST-115–117, and `LeeYangForcingThreshold.lean`.
- **Statement:** No arithmetic identity observes an individual nontrivial zero; every identity
  observes only the archimedean-smoothed *density* of the zero set, which is even under the
  functional-equation reflection of each pair. RH is an *individuation* statement (each zero sits
  on the symmetry axis of the density it contributes to) and can only be produced by comparing two
  inequivalent completions of the prime source, never by a positivity certificate.
- **Status:** [PRODUCER REFUTED 2026-09-02] [LAW DIAGNOSIS SURVIVES] [NOT RH] [LEAN: B1, B3, B5-no-go]

## 1. What the two failures actually proved (the compression)

Four facts, three of them proved this week, one packaged:

- **T1 (parity — new, paper-proved below).** Let `S ⊂ ℂ` be a zero set stable under
  `ρ ↦ 1−ρ̄` and `ρ ↦ ρ̄`, and let `φ` be any function on `ℂ`. Then
  `Σ_{ρ∈S} φ(ρ) = Σ_{pairs} [φ(ρ) + φ(1−ρ̄)]`, and for `ρ = ½+δ+iγ` the bracket is an *even*
  function of `δ`. Hence no share ledger `Σ_ρ φ(ρ)` with `φ` smooth is first-order sensitive to
  the off-line displacement `δ`. The only ways a ledger can reach first order are a
  half-plane cut (`(δ)₊`, Littlewood/Jensen — count direction, wall W5), an alignment
  singularity (`1/(σ−β)`, Class II), or amplification (`cosh(nδ)`, Class III). This is the
  reason Classes I–III of `ULF-SLC-001` are exhaustive.
- **T2 (crowd — ceilings C1–C4 + `SelbergLedgerCeiling`).** Every positivity certificate with a
  fixed kernel resolves off-line zeros only to the archimedean density
  `ν(t) = (1/2π) log(t/2π)`: exclusion width `≍ 1/ν(t)` (Class II), degree-`N` certificates see
  only heights `≲ e^{cN}` (Class III), fixed-point ledgers are `O(δ²/γ²)` (Class I). The
  `log t` in every ceiling *is* the Γ-factor's phase derivative.
- **T3 (Landau blindness — packaged).** A Dirichlet series with nonnegative coefficients has its
  convergence abscissa at a *real* singularity (Landau). The zeros are never real, and the pole
  of `ζ` sits to the right of every zero, so no nonnegative-coefficient object (in one or several
  variables) has an abscissa at `Θ = sup β`. Coefficient positivity cannot carry oriented zero
  data. (Corpus form: `NoSurrogateAnnihilator`, the C4 firewall.)
- **T4 (poles, not eigenvalues — `ULF-SLC-001` P3).** In every `GL(2)` spectral identity the
  zeros enter as poles of `φ(s) = ξ(2s−1)/ξ(2s)`; the created `L²` positivity (Maass forms,
  Petersson, Kuznetsov, Lax–Phillips dissipativity) lives on the complement of the resonance
  sector. Created positivity and zero location are disjoint by structure, not by weakness.

Together: **individual zeros are not observables of arithmetic.** What arithmetic observes is
`D_ε(t) = Σ_ρ K_ρ^{(ε)}(t)` (Poisson-smoothed, pair-even, mass `1` per zero independent of `δ`),
and every explicit formula, trace formula, Maass–Selberg relation and Weil form is an identity
for functionals of `D_ε`.

## 2. The universal statement (frozen truth-hunch)

> **Individuation law.** For an FE-symmetric arithmetic object `F` with archimedean density
> `ν_F`, every unconditional identity is a functional of the pair-even smoothed zero density
> and is therefore blind to the individual displacement `δ` at first order; the first-order
> oriented data of `F` are exactly (i) half-plane counts (`N(σ,T)`, Littlewood means,
> Cramér variance) and (ii) the archimedean phase `arg χ_F(σ+it)`, whose `σ`-derivative
> `−ν_F(t)` is the crowd. RH for `F` is the statement that the individual zeros coincide with
> the symmetry axis of the density they generate; it is *not* a positivity property of any
> fixed functional of the source. It is produced, when it is produced, by an exact comparison
> of two inequivalent completions of the same source (multiplicative: Euler product;
> additive: Hadamard product over zeros), with the archimedean phase as the only oriented
> term.

**Ontological reversal.** RH is a theorem about the archimedean place, not about the primes.
The primes supply pair-even data and the pole; the Γ-factor supplies the only first-order
oriented invariant. Over function fields `ν_F` is constant (finite genus), the crowd is a Betti
number, and the two-completion comparison is Weil's identity `trace = 2d₁d₂ − D·D` plus the
Hodge index theorem — one uniform-in-amplification identity, no certificate degree-by-degree.
Over `ℚ` the genus is infinite and the canonical class is `Γ`.

## 3. Shadow map (what the law compresses)

| shadow | how the law reads it |
|---|---|
| `ULF-PIO-001` refuted (`polePlane_index_blind`) | pole-plane index is a Class I ledger: even, `O(δ²)` |
| `ULF-SLC-001` retired (Selberg ledger `K_ρ`, mass ½+½, width `c/log γ`) | `D_ε` is pair-even; ceiling = `1/ν(t)` |
| corpus W1 "positivity must be created" / W2 multiplicative blindness | created positivity lives off the resonance sector (T4); multiplicative regularization sees leading data because zeros are second order (T1) |
| corpus W5 count direction, W6 Perron/Halász caps | the only first-order oriented ledgers are half-plane counts; their caps are the crowd |
| corpus ORIENT gate, F06 "FE transports, does not select" | orientation is exactly what pair-evenness erases; FE is the evenness |
| corpus `closed_forcing_data_not_decide_marginal` (Lee–Yang threshold) | density-level data cannot decide the marginal (individual) point — same statement in forcing-family language |
| de la Vallée Poussin, Selberg trace, Maass–Selberg, Weil on finite apertures (route O) | Class II with the Γ-phase as the `log t` |
| Polymath 15 `Λ ≤ 0.2` gives no zero-free strip | prediction P2 below: `Λ` is a Class II ledger through crowd drift |
| Griffin–Ono–Rolen–Zagier: Jensen `J^{d,n}` hyperbolic for `n ≥ N(d)`, never uniform in `d` | `d` is the crowd; uniformity in `d` would be individuation |
| Levinson–Conrey `κ < 1` | mollified half-plane count; cap = log-vs-square gap against the crowd |
| Lagarias–Suzuki (`a₀(y,s)`, truncation integrals `T ≥ 1`) and Rankin–Swinnerton-Dyer (`E_k` zeros on the arc): RH *proved* for approximants | two-term dominance with crowd `2`; their zeros are never `ξ`-zeros (B3) — positive instances of the law, not routes |
| Deligne (function fields): RH proved | finite crowd + one uniform identity — the unique positive instance with `ξ`-type zeros |

## 4. Risky consequences (parameter-free, falsifiable)

- **P1 (degree scaling).** For a degree-`d` Selberg-class element every fixed-kernel
  positivity certificate has exclusion width `≍ 1/(d log t)`; no method of that shape can beat
  `1/(d log t)` at all heights. *Falsifier:* a fixed-kernel certificate with width `≫ 1/log t`
  uniformly in `t` for `ζ`.
- **P2 (de Bruijn–Newman is Class II).** If `Λ ≤ ε` then every zero satisfies
  `|β−½| ≤ C ε log(|γ|+2)`. Mechanism: under the backward heat flow a conjugate pair at
  height `γ` and displacement `δ` is pulled to the real axis at rate `≤ 1/δ + C log γ`
  (partner term plus crowd term of the zero ODE `ż_j = 2Σ_{k≠j} 1/(z_j−z_k)`), so its collision
  time is `≥ δ/(C' log γ)`. Hence no upper bound `Λ ≤ ε` with `ε > 0` yields a zero-free strip;
  conversely the classical width `c/log γ` bounds the collision time of every hypothetical
  pair by `O(c)`, which is the order of magnitude Polymath obtained. *Target theorem B4.*
- **P3 (approximant blindness).** Any family `F_y → ξ` (in the sense that its zeros converge
  to `ξ`'s) for which RH is *provable uniformly* has zeros that are *not* `ξ`-zeros at every
  finite stage, and its dominance structure has bounded crowd. Checked instance B3: the
  Lagarias–Suzuki constant term never vanishes at `ρ/2`.
- **P4 (no positivity producer).** No card of the form "prove `Φ(source) ≥ 0` for one fixed
  `Φ`" can be a producer; every such card is Class I/II/III. This retro-predicts the shape of
  the 454 retired cards whose engine is a fixed positive functional and is the law's strongest
  exposure: a single fixed-functional producer refutes it.

## 5. What the law says a producer must be (the radical part)

Constraints forced by T1–T4: nonlinear in the zero measure; oriented through the archimedean
phase; an *identity*, uniform in amplification; crowd cancelling exactly. The one classical
identity with these properties is Littlewood's: for `T` fixed,

`M_T(σ) := (1/2π) ∫_{−T}^{T} log|ζ(σ+it)| dt = 2π Σ_{β>σ, |γ|<T} (β − σ) + O(log T)`,

a convex, piecewise-linear function of `σ` whose kinks are exactly the individual real parts
`β` — the *only* place in analytic number theory where individual zeros are read off an
integral of the source. Its multiplicative completion is exact: for `σ > 1` the Euler product
gives `M_T(σ) = O(1)` because `log ζ` has zero constant term. RH says the mean has no kink on
`(½, 1)`.

**Producer conjecture (two-completion comparison).** The vertical log-mean of the
*multiplicative* completion, continued from `σ > 1` through the strip by the Euler product's own
partial products, and the vertical log-mean of the *additive* completion (Hadamard) differ on
`½ < σ < 1` by an amount whose `σ`-derivative is the archimedean phase density alone; the
difference has no kink. Equivalently: the kink measure `M_T''` of the additive completion is
carried entirely by the point `σ = ½` plus the Γ-phase. This is MUST-117's "controlled nonsplit
comparison" with an explicit support cost: the cost is the Γ-phase, and off-line birth is
exactly a kink the multiplicative side cannot pay for (a kink at `β` costs `2π(β−σ)₊` per
zero, first order, uncapped, and Class III in `T`).

What is genuinely open, and what this card refuses to disguise: the multiplicative side is only
known on `σ > 1`; its continuation by partial Euler products on `½ < σ ≤ 1` converges to
`log ζ` exactly under RH (conditional convergence of `Σ_p p^{−s}` on `σ > Θ`). So the producer
is a *convergence-of-partial-Euler-products* statement whose mean-value version is weaker than
pointwise convergence. The law's bet is that the **mean** version — convergence of
`(1/T)∫ log|∏_{p≤X}(1−p^{−s})^{−1}| dt` to `M_T(σ)/T` with error `o(1)` uniformly for
`σ ≥ ½+η`, with rate governed by the crowd — is provable by a *second-moment* (pair-even,
crowd-capped) argument, because the mean is itself pair-even and needs no individuation; and
that individuation is then supplied by convexity of `M_T` in `σ` (a kink cannot hide in a mean
that is exactly linear on both sides). The kink is first-order and the mean is second-order:
that mismatch is the whole mechanism, and it is exactly what P4 forbids for fixed-functional
positivity while permitting here, since convexity is not positivity of a fixed functional but
subharmonicity of `log|ζ|`.

## 6. Bricks (paper first, then Lean after `formal_tools.py research`)

- **B1** parity theorem T1 (trivial; a two-line real-analysis lemma over `Finset` of pairs).
- **B2** Class II identification of Littlewood's mean: `M_T(σ) − M_T(σ') = 2π ∫_σ^{σ'} N(u,T)du`
  is in the corpus? — search `Littlewood`, `logIntegral`, `N(σ,T)` before building.
- **B3** Lagarias–Suzuki blindness: `a₀(y, ρ/2) = y^{1−ρ/2} ξ(2−ρ) ≠ 0` (uses only `ξ ≠ 0` on
  `Re > 1`). Elementary.
- **B4** the `Λ`-drift bound of P2: rate bound for the imaginary part of a nonreal zero of `H_t`.
  Needs the zero ODE with justified pairing (Rodgers–Tao / Polymath dynamics); paper first.
- **B5** the mean-value Euler-product comparison of §5, on `σ ≥ ½ + η` with the crowd rate:
  this is the producer target and is *not* to be attacked before B1–B4 and a corpus search of
  `RG` (Gaussian coordinate, "heat convolution propagates positivity"), `T1` (Selberg orders),
  and `D2` (pure-prime log-height defect, which is a pointwise version of the same difference).

## Gates
- [ ] 0 → 1  in-progress: B1, B3 proved on paper; B2/B4 corpus-searched; §5 stated with the
  exact error term the mean-value comparison needs.
- [ ] 1 → 2  fully-proven: B5 or its refutation with a typed independence witness.
- [ ] 2 → 3  formalized.
- [ ] 3 → 4  publication-ready.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-09-02 — created in 0-backlog after `ULF-SLC-001` was retired; law frozen before any
  proof search; corpus checked lane-deep for de Bruijn–Newman (owned as moonshots + Lee–Yang
  threshold), Lax–Phillips (closed), Selberg class/Kaczorowski–Perelli, de Branges, Levinson,
  zero-density, Sondow–Dumitrescu monotonicity (all owned); Lagarias–Suzuki and
  Rankin–Swinnerton-Dyer not previously engaged and entered only as positive instances.
- 2026-09-02 — B2 corpus search: Littlewood's zero count is already owned —
  `RHTower.Sieve.ZetaResidueUnitWeightedLittlewood.zetaLittlewoodZeroCountAbove` (multiplicity-
  weighted count of zeros with `Re ≥ σ` in the symmetric rectangle), the contour-shift identity
  `integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_sub_zeroSum`
  (`ZetaResidueUnitRectanglePeeling`), and the Ingham detector consumers. B2 must be stated as
  the `σ`-integral of that count, not rebuilt.

## Paper verdict on B5 (2026-09-02)

- **The multiplicative side does not exist in the strip.** The prime series `∑_p p^{−s}` diverges
  at every `s` with `Re s < 1`, RH or not: by the prime number theorem its partial sums are
  `X^{1−s}/((1−s) log X)(1+o(1))`, of modulus `X^{1−σ}/(|1−s| log X) → ∞`. The only convergent
  "Euler-side" object inside the strip is the Möbius series `∑ μ(n) n^{−s}`, and its convergence
  at a single point `s₀` already forces `ζ ≠ 0` on `Re s > Re s₀` (Cahen's lemma, corpus
  `tendstoLocallyUniformlyOn_dirichletPartialSum`, plus the identity theorem against
  `zetaEntire`). So the comparison assumes its conclusion.
- **The mean-value level is density-level.** With a smooth window `w` of length `T₀`, Green's
  identity on the strip `σ < x < σ'` gives the exact smooth Littlewood formula
  `∫ log|ζ(σ+it)| w(t) dt = −2π ∑_{β>σ} (β − σ) w(γ) + R_w(σ)` with `R_w = O(1)` uniformly in
  `T₀` (boundary terms at `σ' > 1` are an absolutely convergent prime series against `ŵ(log n)`,
  the interior ramp term is `O(1/T₀)`). Detecting one zero needs the window mean of `log|ζ|` to
  precision `O(1/T₀)`; pair-even second-moment inputs (zero-density) give `T₀^{−c}`. Convexity
  adds nothing: it is already the Green identity. The gap between `T₀^{−c}` and `T₀^{−1}` is
  the crowd, exactly as T2 predicts; the law diagnoses its own producer as capped.
- **Λ-drift (B4)** is unaffected but not attacked; it remains a paper prediction.

## No-go closure
- **Exact killing theorem/mechanism:** `RHTower.riemannZeta_ne_zero_of_moebius_convergesAt`
  (convergence of the Möbius series at one point ⇒ zero-free half-plane to its right) and
  `RHTower.re_le_abscissaOfConv_moebiusShift` (the abscissa of convergence of the Möbius series
  is ≥ `Re ρ` for every zero); module
  `GaloisForLFunctions.RHTower.MoebiusConvergenceZeroFree`. On paper: divergence of the prime
  series in `Re s < 1` and the density-level cap of the smooth Littlewood identity.
- **Strongest positive survivor:** the diagnosis T1–T4 of §1, three parts now Lean-certified:
  `GaloisForLFunctions.RHTower.pairLedger_even` / `deriv_pairLedger_zero` (pair parity, for every
  `φ`, no differentiability needed), `eisensteinConstantTerm_ne_zero_of_completedRiemannZeta_eq_zero`
  and `completedRiemannZeta_ne_zero_of_eisensteinConstantTerm_eq_zero` (Lagarias–Suzuki approximants
  never vanish at half-zeros of `Λ`), module `GaloisForLFunctions.RHTower.ZeroLedgerPairParity`;
  and the Möbius abscissa theorem above, unconditional. Paper-level survivor: the smooth-window
  Littlewood identity with `O(1)` remainder.
- **New insight:** a "two-completion comparison" cannot have two unconditional sides: inside the
  strip the multiplicative completion of `1/ζ` is the zero-free statement. Any surviving
  comparison must treat the multiplicative side as a regularized family with an explicitly
  computed regularization budget, which is the budget branch of the corpus's regularization
  trilemma (W1/W2), not an escape from it. MUST-118 is withdrawn in favour of MUST-119 (STATUS).
- **Status:** internal audit; both modules `lake build` green, axioms `propext, Classical.choice,
  Quot.sound`; wired into `GaloisForLFunctions.RHTower`.

## Log (continued)
- 2026-09-02 — B5 refuted on paper (multiplicative side is the conclusion; mean level is density
  level). B1, B3 and the B5 no-go formalized; card moved to 5-failed.
