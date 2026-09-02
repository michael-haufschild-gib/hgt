# The anchor law: zero-free regions are the reach of a nonvanishing anchor, and the line's own anchor is the inner band

- **ID:** ULF-ANC-001
- **Stage:** 5-failed (inner-band target B3 is circular; bricks B1 and the kernel no-go are Lean theorems)
- **Type:** CONJECTURE (universal law, frozen) + one new RH-adjacent target with a paper mechanism
- **Source:** the three 2026-09-02 failures (`ULF-PIO-001`, `ULF-SLC-001`, `ULF-IND-001`), read
  against `stuck-route-obstruction-matrix.md` W1–W11, STATUS F379–F380 / CANNOT-182–183 /
  MUST-119, the corpus Levinson lane (`LevinsonLinearOptimizationInterior`,
  `DifferentiatedBarbanVehovTwoFifthsScaleAsymptotics`), `XiLaguerrePolya.xi_laguerre_inequality_of_rh`,
  and `phase-cancellation-crux.md` (5-failed).
- **Statement:** Every unconditional zero-free statement about `ζ` is the *reach* of an *anchor* —
  an unconditional nonvanishing value — against the archimedean crowd. The strip has no
  unconditional interior anchor (convergent multiplicative anchors are the conclusion, Lean
  F380), the pole anchor saturates at width `(log log t)/log t` even under Lindelöf, and
  manufactured anchors (mollifiers of length `T^θ`) reach a proportion `1 − c/θ`. The only
  anchor located *on the line itself* is the on-line crowd, and it carves an **inner band**: the
  first Laguerre inequality of `Ξ` at height `γ` forbids off-line zeros with displacement
  `δ < c/log γ`.
- **Status:** [PRODUCER TARGET RETIRED 2026-09-02] [LAW DIAGNOSIS SURVIVES] [NOT RH] [LEAN: Laguerre identity, pair term, inner band, kernel no-go]

## 1. What the three failures say together

Each failure tried to *read* the zeros: from an index (even, Class I), from `L²` positivity
(zeros are scattering poles), from a mean of `log|ζ|` (density level). What all three lacked is
an **anchor**: a point or set where the object is unconditionally *nonzero* with quantified
strength, from which nonvanishing propagates by a growth or positivity bound. Reading the
classical results this way:

| anchor | strength | propagation input | reach |
|---|---|---|---|
| Euler product, `Re s > 1` | `|ζ(s)| ≥ ζ(2σ)/ζ(σ)` | none needed | the half-plane itself |
| pole at `s = 1` | residue `1` | `ζ'/ζ = O(log t)` (trivial growth) | de la Vallée Poussin `c/log t` |
| pole + Weyl-sum cancellation | `1` | Richert bound | Vinogradov–Korobov `(log t)^{−2/3}(log log t)^{−1/3}` |
| pole + Lindelöf | `1` | `t^ε` | Littlewood: `(log log t)/log t` — saturation |
| Bochner: `Φ > 0` | `ξ(σ) = ∫Φ cosh((σ−½)u) > 0` | none | the real axis only |
| Lagarias–Suzuki constant term | `T^{2σ−1} − |φ|²T^{1−2σ}` (Maass–Selberg) | none | zeros of `a₀`, never of `Λ` (Lean B3 of ULF-IND-001) |
| Levinson mollifier `ζM ≈ 1`, length `T^θ` | `1` | log-vs-square (Jensen's inequality) | proportion `κ(θ)` |
| Waldspurger square (GL(2) twists) | `|c(D)|²` | none | `L(½, f⊗χ_D) ≥ 0` at one point |

**Anchor law (frozen).** Reach `=` anchor strength ÷ crowd. The crowd at height `t` is the
archimedean density `ν(t) = (1/2π) log(t/2π)` (F379). Growth inputs cannot beat the crowd by more
than the Vinogradov exponent; no growth input reaches the interior of the strip from the pole
(Littlewood's `(log log t)/log t` under Lindelöf is the saturation). There is no unconditional
interior anchor: a convergent Möbius or prime series inside the strip *is* the zero-free
statement (`RHTower.riemannZeta_ne_zero_of_moebius_convergesAt`), and Landau blindness kills
coefficient-positive anchors (T3 of ULF-IND-001).

**Ontological reversal.** RH is not "the zeros are on the line"; it is "the line is an anchor
of infinite reach". The classical programme extends the *pole's* reach; the count-direction
programme *manufactures* anchors; nobody has an anchor on the line. The only unconditional
object located on the line is the on-line zero set itself, and that is where the new target
sits.

## 2. Risky consequences (checked where the literature allows)

- **P1 (mollifier reach).** A mollifier of length `T^θ` cancels the crowd only at scale
  `1/(θ log T)`, so the anchored proportion is `κ(θ) = 1 − c/θ + o(1/θ)` with `c` a shape
  constant of order `1/3`. Check against published values with the same linear mollifier shape:
  `κ(½) = 0.3474` gives `c = 0.326`; `κ(4/7) = 0.4088` gives `c = 0.338`. Consistent to 4%.
  Falsifier: any proportion formula approaching `1` faster than `1/θ`.
- **P2 (no interior anchor).** No unconditional theorem of the form "`ζ(s) ≠ 0` on a set of
  positive measure inside `½ < Re s < 1`" can be produced without a convergent multiplicative
  series there; hence all interior nonvanishing results are density statements. Falsifier: a
  positive-measure interior zero-free set proved from growth or positivity alone.
- **P3 (central twists).** `L(½, χ_D) ≥ 0` for all `D` stays open exactly because degree one
  has no Waldspurger square (the weight-`½` Eisenstein coefficient is `L` itself, not `|c|²`).
  Consistent with the literature.
- **P4 (inner band).** If `Ξ` satisfies the first Laguerre inequality `Ξ'(t)² ≥ Ξ(t)Ξ''(t)` on a
  neighbourhood of `t = γ`, then no off-line pair `γ ± iδ` (in the `t`-plane) has
  `δ² < 2 / Σ_{z real} (γ − z)^{−2}`; with the on-line spacing `2π/log γ` this is
  `δ ≥ c/log γ`. Proof: from the genus-one Hadamard product `Ξ(t) = Ξ(0)∏(1 − t²/z²)`,
  `Ξ'² − ΞΞ'' = Ξ² Σ_z (t − z)^{−2}` (sum over all zeros `z`, both signs); a conjugate pair
  contributes `2((t−γ)² − δ²)/((t−γ)² + δ²)²`, which is `−2/δ²` at `t = γ`; real zeros
  contribute positively. Hence the Laguerre inequality at `γ` forces the on-line zeros near `γ`
  to supply `≥ 2/δ²`, which bounds `δ` below by the local crowd. **This is the dual of de la
  Vallée Poussin:** the pole anchor clears the band `1 − c/log t < σ`, the line anchor clears the
  band `½ < σ < ½ + c/log t`. Both widths are the crowd, as the law requires.

## 3. The new target and its honest risk

**Target (inner band).** Prove the first Laguerre inequality for `Ξ` at every real `t`
unconditionally. Consequence: off-line zeros are confined to `c/log γ ≤ β − ½ ≤ ½ − c/log γ`.
This is strictly weaker than RH (it permits far-off-line zeros) and strictly stronger than every
known zero-free region in shape (it is the first statement clearing a band adjacent to the line).

**Risk, stated precisely.** For the de Bruijn–Newman deformation `Ξ_s` with `s < 0`, the
kernel `Φ e^{su²}` is still positive, even and log-concave, but `Ξ_s` has non-real pairs born
at collisions of close real zeros, which violate the Laguerre inequality near their birth point.
So the target cannot follow from positivity, evenness or log-concavity of the kernel alone; a
proof must use `s = 0` exactly, i.e. the arithmetic. The target shares RH's "barely true"
character (Rodgers–Tao) and is therefore not soft. Its value is diagnostic: it is the first
RH-adjacent statement whose anchor is on the line, and any proof of it would be the first
line-anchored mechanism.

**What would refute the law.** A zero-free region strictly inside the strip proved without an
interior convergent series; a proportion `κ(θ)` beating `1 − c/θ`; a Laguerre-inequality
counterexample for `Ξ` (which would refute RH).

## 4. Bricks
- **B1** (Lean, unconditional): the Laguerre identity for genus-one even real entire functions,
  `f'² − f f'' = f² Σ_z (t − z)^{−2}`, and its corollary: if `f'(γ)² ≥ f(γ)f''(γ)` and the
  real zeros contribute at most `C` at `γ`, then every non-real pair `γ ± iδ` has `δ² ≥ 2/C`.
  Search first: `XiHadamardFactorization`, `SuzukiZeroSumIdentity.hasSum_xiSupport_mult_inv_normSq`,
  `LaguerreInequality.laguerre_inequality_lp`.
- **B2** (paper): the spacing input `Σ_{z real} (γ − z)^{−2} ≪ (log γ)²` on average, and the
  precise inner-band constant.
- **B3** (paper): the Laguerre inequality of `Ξ` at all `t` — the target; attack only after B1
  and a corpus search of the Hankel/TCD real-rootedness no-goes.

## Gates
- [ ] 0 → 1: B1 formalized; B2 stated with constants; corpus search of TCD Hankel no-goes recorded.
- [ ] 1 → 2: B3 or its refutation with a typed witness.
- [ ] 2 → 3 / 3 → 4.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** —
- **Strongest positive survivor:** —
- **New insight:** —
- **Status:** —

## Log
- 2026-09-02 — created in 0-backlog from the three-failure synthesis; law frozen before proof
  search; Levinson-proportion check done against published values only (no computation).

## Paper proofs (2026-09-02)

**Identity.** `ΞC` has the unconditional Hadamard product `ΞC = ΞC(0)·∏_q E₁(z/a_q)` over the
multiplicity copies of its zeros (corpus). Its logarithmic derivative is the Mittag-Leffler sum
`∑_q ((z − a_q)⁻¹ + a_q⁻¹)` (corpus). On a disc of radius `d/2` around a non-zero `z` (with
`d = dist(z, zeros)`), the terms are bounded by a summable family (`2R/|a_q|²` for `|a_q| ≥ 2R`,
`2R/(d|a_q|/2)` for the finitely many others), so the sum may be differentiated termwise:
`(log ΞC)'' = −∑_q (z − a_q)⁻²`. With `(log f)'' = (f f'' − f'²)/f²` this gives
`ΞC'² − ΞC·ΞC'' = ΞC² ∑_q (z − a_q)⁻²`.

**Pair term.** At a real `γ`, a conjugate pair `a = γ ∓ δ i` contributes `(±δ i)⁻² = −1/δ²` each,
total `−2/δ²`; a real zero `a` contributes `(γ − a)⁻² > 0`. So if `ΞC'² ≥ ΞC·ΞC''` at `γ` and
`Ξ(γ) ≠ 0`, the remaining zeros must contribute at least `2/δ²`: the **inner band**
`δ ≥ (2/∑_{others}(γ − a)⁻²)^{1/2}`, of size `c/log γ` at typical spacing.

**Why B3 (the unconditional Laguerre inequality at every `t`) is circular.** The inequality at
`γ` holds iff `∑_{a real} (γ − a)⁻² ≥ 2/δ²` for every hypothetical pair at `γ`. Its only
possible anchor is therefore a *pointwise* lower bound on the on-line inverse-square sum near
every height, i.e. a pointwise density of *on-line* zeros. Unconditionally the corpus and the
literature supply on-line zeros only in proportion (Levinson–Conrey) and ordinates of *all*
zeros with gaps `≪ 1/log log t` (Littlewood); no unconditional input gives an on-line zero
within `o(1)` of an arbitrary height. So the "line anchor" is the on-line zero configuration
itself, which is the conclusion in the same way that the Möbius series was for ULF-IND-001.

**Why no kernel-positivity proof exists.** The kernel `Φ(u) = e^{−πu²}(cosh(ωu) + 6/5)`,
`ω² = 2π/5`, is positive, even and logarithmically concave, and its Fourier transform
`H(t) = e^{−πt²}(e^{1/10} cos(ωt) + 6/5)` has `H'² − H H'' = e^{−2πt₀²}(6/5 − A)(12π/5)(1 − A) < 0`
at `t₀ = π/ω`, `A = e^{1/10} ∈ (1, 6/5)`. Csordas–Norfolk–Varga-type arguments (positivity,
evenness, log-concavity of the theta kernel) therefore cannot prove the inequality for `Ξ`;
neither can the de Bruijn–Newman family, which preserves all three properties.

## No-go closure
- **Exact killing theorem/mechanism:** `GaloisForLFunctions.HTGeometry.laguerreTransform_laguerre_neg`
  together with `laguerreKernel_pos`, `laguerreKernel_even`, `laguerreKernel_logConcave`,
  `fourier_laguerreKernel` (module `HTGeometry.LaguerreKernelCounterexample`): the first Laguerre
  inequality is not a consequence of kernel positivity, evenness and log-concavity. On paper: the
  inner-band inequality's anchor is the pointwise on-line zero density, which is not an
  unconditional input.
- **Strongest positive survivor:** `RHTower.laguerre_XiC_eq_tsum_inv_sq` (the Laguerre identity
  for `ΞC` as an inverse-square sum over the multiplicity copies of its zeros, unconditional),
  `tsum_inv_sq_sub_xiSpectralPoint_pair` (the exact `−2/δ²` pair term),
  `laguerre_XiC_re_pair` and `two_div_sq_le_of_laguerre_nonneg` (the inner band as an
  implication), module `RHTower.XiLaguerreZeroSumIdentity`. Also the summability
  `summable_inv_sq_sub_xiSpectralPoint` at every non-zero point.
- **New insight:** the anchor law's diagnosis stands (every zero-free region is an anchor's reach
  against the crowd), but the only line anchor is the on-line zero set itself; a producer must
  manufacture its anchor (mollifiers, reach `1 − c/θ`) or find one that is neither multiplicative
  convergence nor on-line density. MUST-120 is withdrawn in favour of MUST-121 (STATUS).
- **Status:** internal audit; both modules `lake build` green, axioms
  `propext, Classical.choice, Quot.sound`; wired into `GaloisForLFunctions.RHTower` and
  `GaloisForLFunctions.HTGeometry`.

## Log (continued)
- 2026-09-02 — paper proofs written; B3 identified as circular; identity, pair term, inner band
  and kernel no-go formalized; card moved to 5-failed.
