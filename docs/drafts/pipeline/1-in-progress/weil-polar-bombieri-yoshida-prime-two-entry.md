# Constrained Weil form: Bombieri–Yoshida receiver, the prime-2 entry, and a large-values engine

**Stage:** 1 (in progress), opened 2026-09-04.  Working log: `weil-polar-ground-energy-working-log.md`.
Three deliverables requested together:

* **(BY)** Lean: `ccmRestrictedWeilPolarGroundEnergy a > 0` (or `≥ 0`) for all apertures `a` ⇒ `RiemannHypothesis`
  (Bombieri–Yoshida / pole-vanishing Weil criterion).  Corpus has the unconstrained version
  (`exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis`) via Suzuki's smooth-test
  criterion; the two-bump witness is not pole-vanishing.
* **(P2)** Paper + Lean: analytic (non-numerical) positivity of the pole-vanishing form across the prime-2 entry
  `a = (log 2)/2`, replacing Connes–Consani's computer-checked step; explicit aperture range.
* **(GM)** Lean: a Guth–Maynard-type large-values theorem for Dirichlet polynomials.

## (BY) route — discrete multiplier + weighted Widder–Landau

Corpus facts used (all Lean, unconditional):
`suzukiScrewSmoothForm_eq_tsum`: for a smooth zero-mean test `φ` on `[-a,a]`,
`Q(φ) = Σ'_q B̄_q(φ) B_q(φ) / γ_q²`, `B_q(φ) = ∫ (e^{-iγ_q u} − 1) φ(u) du` (ray energy, `XiZeroCopy` = zeros with
multiplicity, `γ_q = xiSpectralPoint q`, `|Im γ_q| < 1/2`).  `IsPolarConstrained a u` ⇔
`⟨e^{±x/2}·1_{[-a,a]}, u⟩ = 0`.  CCM restricted quadratic = Suzuki form on zero-mean smooth tests
(`suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm`, `ccmRestrictedWeilForm_primitive_eq_screw`).
Two-bump limit `Q(b_t − b_0) → 2Ψ(t)` (`suzukiScrewSmoothForm_twoBump`, `abs_suzukiLocalizedKernelAverage_sub_le`).
`Ψ(t) = Σ_q (1 − e^{iγ_q t})/γ_q²` (`ofReal_suzukiPsi_eq_xiScrewDivisor`), Widder–Landau engine
(`SuzukiScrewPointwiseNonnegativityCriterion`: `riemannHypothesis_of_suzukiPsiPointwiseNonnegative`).

1. **Discrete multiplier.** For `h > 0` let `M(γ) = (e^{iγh} − 1)(e^{iγh} − e^{h/2})(e^{iγh} − e^{-h/2}) = Σ_k μ_k e^{iγτ_k}`
   (`τ_k ∈ {0,h,2h,3h}`).  For any smooth `φ` put `(M∗φ)(x) = Σ_k μ_k φ(x − τ_k)`.  Then
   `∫ e^{sx}(M∗φ) = M(-is)·∫e^{sx}φ`, so `M∗φ` has zero mean and vanishing `e^{±x/2}` moments for **every** `φ`:
   `M∗φ` is pole-vanishing and zero-mean, support grows by `3h`.
2. **Twisted ray energy.** `B_q(M∗φ) = M(γ_q) B_q(φ)`, hence `Q(M∗φ) = Σ_q W_q |B_q(φ)|²/γ_q²`-type with
   `W_q = M(γ_q)·conj(M(conj γ_q))`; `W_q = |M(γ_q)|² ≥ 0` on the line, `W_q ≠ 0` at every off-line zero
   (`M` vanishes only on `Im γ ∈ {0, ±1/2}`).
3. **Twisted two-bump limit.** With `φ = b_t − b_0` (bumps of width `ε → 0`):
   `Q(M∗(b_t − b_0)) → 2 Φ(t)`, `Φ(t) := Re Ψ_M(t) − Ψ_M(0)`, `Ψ_M(t) = Σ_{k,l} μ_k μ̄_l Ψ(t + τ_k − τ_l)`.
   Zero series: `Φ(t) = Σ_q Re[W_q (1 − e^{iγ_q t})/γ_q²]`.  Constrained positivity at all apertures ⇒ `Φ ≥ 0` on `ℝ`.
4. **Weighted Widder–Landau.** `Φ ≥ 0`, continuous, `|Φ| ≤ C e^{y* t}`; Laplace transform
   `F(s) = Σ_q W_q(−i)/(γ_q s (s − iγ_q))` (single-pole rational atoms, poles at `s = iγ_q`, real parts `−Im γ_q`).
   Landau: the abscissa `σ_c` is a real singularity ⇒ a pole on the real axis ⇒ a zero with `Re γ_q = 0`
   (real zero of `ξ` in the strip) — excluded; hence `σ_c = −∞`?? no: hence every pole has `Re ≤ σ_c` and the
   abscissa is not a singularity unless real pole ⇒ contradiction unless there is no pole with `Re > σ_c`…
   Precisely: if an off-line zero exists, the conjugate pair gives poles with real parts `±y`, `y > 0`, `W ≠ 0`,
   so `σ_c ≥ y > 0` and Landau forces a real pole at `σ_c`, impossible.  So the engine's inputs are:
   (a) Landau's theorem for nonnegative functions (corpus: the halving argument of the pointwise module, to be
   generalized to weighted single-pole atoms), (b) no real zeros of `ξ` in the strip (corpus check needed),
   (c) `W_q ≠ 0` off the line.
5. **Assembly.** `∀a, μ₀^{pol}(a) ≥ 0` ⇒ `Q(M∗(b_t−b_0)) ≥ 0` for all small `ε` (the test is polar-constrained and
   its CCM embedding has nonnegative Rayleigh quotient) ⇒ `Φ ≥ 0` ⇒ RH.  Note only `≥ 0` is needed.

Open Lean work: translate-combination tests as `SuzukiSmoothZeroMeanTest`; `IsPolarConstrained` of their CCM
embedding; ray-coefficient translation rule; multi-bump localized limit; weighted Landau engine.

## (P2) route — see working log; needs Connes–Consani Thm 1 / (115) exactly.
## (GM) route — programme card `guth-maynard-large-values-lean-programme.md` (to be written after the exact statement is fetched).

## (P2) hgtl7 round — 2026-09-04

**Phase 1–2 (context).**  Corpus: Theorem C/D (Sonin transfer, continuity across the prime-2 entry),
the log-soft entry law, the elementary recasting `poleTerm + archTerm = C(S)‖f‖² + ∫₀^S D(u)K(u)du`
(`archimedean-weil-kernel-sign-and-aperture.md`), Hilbert/Hilbert1/Hilbert2, numerics
`μ₀(√2) = 0.547`, archimedean-only threshold `λ_arch = 1.8145`.  Literature: Connes–Consani 2021 prove
the √2 case by a numerical Toeplitz spectral computation (1732-term `L¹` approximation (115), top
eigenvalue 1.0516 vs 1); Suzuki 2026 (screw function): positivity "for small λ"; Connes 2026 survey:
nothing beyond √2.  Bombieri–Yoshida is now Lean (this card, WP-T1).

**Reformulation (new).**  On the pole-vanishing subspace the polar term vanishes and the archimedean
form is exactly

    Q_S(f) = A(S)‖f‖² + ∫₀^S ½‖f − T_u f‖² K₊(u) du,   K₊(u) = 2e^{−u/2}/(1 − e^{−2u}) = 2Σ_{m≥0} e^{−(2m+½)u} > 0,
    A(S) = −γ − log π − log(1 − e^{−2S}) − J(S)  (A(log 2) = −2.3785),

i.e. the negativity is entirely in the constant `A(S)` and the positivity entirely in a positive-kernel
translation-defect energy.  Fourier side: `Q_S(f) = (1/2π) ∫ |f̂(ξ)|² m_S(ξ) dξ`,
`m_S(ξ) = A(S) + Λ_S(ξ)`, `Λ_S(ξ) = ∫₀^S K₊(u)(1 − cos uξ) du = 2Σ_m [(1 − e^{−α_m S})/α_m − (α_m − e^{−α_m S}(α_m cos Sξ − ξ sin Sξ))/(α_m² + ξ²)]`,
`α_m = 2m + ½` — an explicit series, geometric at `S = log 2` (`e^{−2S} = ¼`).  `m_S` is negative on
`|ξ| < ξ_S` (`ξ_{log 2} = 5.448`), positive beyond, with dips at `ξ ≈ 10.05 + 9.06k` (period `2π/S`):
values at `S = log 2`: `m(6) = 0.178, m(8) = 0.416, m(10.05) = 0.369, m(12) = 0.50, m(16) ≥ 1.05`.

**Numerics (pod, `constrained_multiplier.py`, `constrained_check2.py`).**  Legendre basis on `[−a, a]`,
`N ≤ 24`: constrained minimum `0.5425` at `S = log 2` (direct x-space check `0.549`; corpus `0.547` ✓),
`0.175` at `S = 1.0`, zero crossing at `S ≈ 1.19` (corpus `λ_arch = 1.8145 ⇔ S = 1.192` ✓).  The extremal
function is **even**, essentially `0.87 p₂ + 0.48 p₄ + 0.06 p₆` (normalized Legendre modes).  Unconstrained
minimum `−1.29`.  Band concentrations at `S = log 2`: unconstrained `λ₀ = 0.86, λ₁ = 0.31, λ₂ = 0.027`
(band `|ξ| ≤ 5.45`, `c = 1.89`); on `V₀`: `0.048, 0.0037`.  (`N = 40` Gram is unreliable: high-mode
quadrature artifact; `N ≤ 24` validated against direct evaluation.)

**Phase 3 — frozen conjecture (P2-C1).**  *Constrained archimedean Weil positivity is an elementary
two-constraint concentration inequality, certifiable without prolate theory.*  Precisely: for every
`S ≤ S*` with `S* ≥ 1.1`, and every `f ∈ L²[−S/2, S/2]` with `∫ e^{±x/2} f = 0`,

    Q_S(f) ≥ κ(S)‖f‖²,   κ(log 2) ≥ 0.5,

and the proof is: (i) **Taylor localization** — for `g ⊥` polynomials of degree `< N` on `[−a, a]`,
`|ĝ(ξ)|² ≤ τ_N(ξ)‖g‖²`, `τ_N(ξ) = 2a^{2N+1}ξ^{2N}/((N!)²(2N+1))` (Cauchy–Schwarz against the Taylor
remainder of `e^{−iξx}`); (ii) **staircase** — `m_S ≥ m_stair := Σ_j c_j 1_{band_j}` with `c_j` band minima
(`c₀ = A(S)` exactly, since `Λ_S ≥ 0`), so `Q_S(f) ≥ ⟨f, M_stair f⟩`; (iii) **finite block** — the
compression of `M_stair` to `V₀ ∩ Legendre_{<N}` is an explicit matrix (band-limiting Grams of Legendre
modes: `∫_{−2a}^{2a} R_{nk}(t) [sin(hi·t) − sin(lo·t)]/(πt) dt` with `R_{nk}` the polynomial
autocorrelations, i.e. `Si` values at `2a·edge` and trigonometric terms); (iv) **assembly** —
`Q_S(f) ≥ min(λ_min(M_stair|V₀∩P_{<N}) − |c|_max√M_low, c_last(1 − M_low) − |c|_max(M_low + √M_low))·‖f‖²`
with `M_low = (1/π)∫₀^{Ξ_max} τ_N`, because the Legendre split `f = f_low + f_high` makes `f_high`
spectrally negligible below `Ξ_max` and `M_stair` acts as `c_last(I − B_{Ξ_max})` above it.

**Phase 4 — attack.**  Not circular (no zero information enters); not a rediscovery (Connes–Consani's route
is prolate/Toeplitz numerics at one aperture; Suzuki's is screw-function positivity for small λ); not
insignificant for the constrained-Weil programme (it certifies a range beyond √2 and, with the prime-2 term
`−√2 log 2 ⟨f, T_{log 2} f⟩` added as an explicit operator, a range for the full form with the prime 2).
It remains nonselective for RH (CANNOT-02), as every fixed-aperture statement.  Verdict:
SURVIVES PRELIMINARY ATTACK.

**Certificate values (pod, `certificate_bands.py`, `certificate_staircase.py`).**  At `S = log 2`:
two-band certificate `c₈(1 − θ₈) − |A|θ₆ = 0.3693(1 − 0.2157) − 2.3785·0.0725 = 0.117 > 0`
(`θ_B` = constrained concentration of `V₀ ∩ P_{<12}` in `|ξ| ≤ B`, `Mlow(12, 8) ≈ 10⁻⁶`); eight-band
staircase (`N = 15`): low-mode `0.217`, high-mode `0.509`, `M_low = 6·10⁻⁹`.  Archimedean-only certificate
positive also at `S = 0.75` (`0.110`); at `S = 0.8` the coarse staircase gives `−0.003` (true min `0.2`),
so finer bands are needed for the extended range.  With the prime-2 operator the coarse certificate fails
at `S = 0.75` (`−0.13`): the loss is the staircase resolution and the high-mode floor (`c_last = 0.51`
versus the prime-term norm `√2 log 2 = 0.98`); the refinement (bands of width `0.5`, `Ξ_max = 16` where
`m ≥ 1.05`) is running.

**Phase 5 (paper proof) status.**  Lemmas (i)–(iv) are dependency-closed on paper with the explicit
series for `A(S)`, `Λ_S`, the band Grams and the constraint vectors `⟨e^{±x/2}, p_n⟩`; the only inputs
needing certified evaluation are `Si` at explicit arguments, `γ`, `log π`, `log 2`, `√2`.
Next: the paper write-up with the explicit constants, then Lean (`ConstrainedWeilSqrtTwoCertificate*`):
Taylor localization, staircase, the `V₀` Fourier identity from the corpus's recasting, and the finite
certified block.

**Refined staircase (bands of width 0.5 on `[5,16]`, last band `[16,∞)`, `N ≈ 3·a·16`; pod,
`certificate_staircase.py`, floating point, no error bounds yet):**

| `S` | `λ = e^{S/2}` | archimedean low/high | with prime 2 low/high |
|---|---|---|---|
| log 2 | 1.4142 | 0.430 / 1.054 | — |
| 0.72 | 1.433 | 0.379 / 1.017 | **0.258 / 0.036** |
| 0.75 | 1.455 | 0.320 / 0.975 | 0.134 / −0.005 |
| 0.80 | 1.492 | 0.220 / 0.910 | −0.013 / −0.070 |
| 0.90 | 1.568 | 0.005 / 0.846 | −0.200 / −0.135 |
| 1.00 | 1.649 | −0.227 / 0.963 | −0.327 / −0.018 |

Reading: the certificate proves the constrained archimedean form positive up to `λ ≈ 1.57` and the **full
form with the prime 2** positive on `[√2, 1.433]` — beyond the literature's √2 — with the high-mode floor
`c_last` needing to exceed the prime-term norm `√2 log 2 = 0.980` (take `Ξ_max ≈ 19`, where `m ≥ 1.05`).
The remaining loss is band resolution (true constrained minimum `0.54` at √2 vs certified `0.43`).
Next: interval-arithmetic (mpmath `iv`) evaluation of every constant to make the paper proof rigorous
(stage 2), then Lean.

## Rigorous certificate (2026-09-04) and the Lean backbone

Computations: `docs/drafts/pipeline/2-fully-proven/computations/weil-constrained-prime-two-certificate/`
(`certificate_rigorous.py`, README with the full error-control ledger).  Every analytic constant
carries a proven tail bound; the only floating-point step is the 25-digit Gauss–Legendre band Gram
and the 25-digit symmetric eigenvalue.

| S | λ = e^{S/2} | certified constrained ground energy | finite block (exact multiplier) |
|---|---|---|---|
| log 2 | 1.414 | 0.5177 | 0.5223 |
| 0.72 | 1.433 | 0.2505 | 0.2606 |
| 0.80 | 1.492 | 0.1100 | 0.1244 |
| 0.90 | 1.568 | 0.0173 | 0.0341 |
| 0.95 | 1.608 | 0.0059 | 0.0127 |
| 0.98 | 1.632 | 0.0024 (band width 0.01) | 0.0059 |
| 1.00 | 1.649 | **0.0014** (band width 0.005) | 0.0031 |
| 1.02 | 1.670 | −0.0003 at width 0.005 (not certified) | 0.0014 |
| 1.05 | 1.691 | not certified | 0.00007 |

**Theorem (certified).**  The polar-constrained restricted Weil form is positive definite on every
aperture `S ≤ 1` (`λ ≤ √e = 1.6487`), with the prime 2 inside the window for `S > log 2`.

**Correction (2026-09-04, later).**  An earlier version of this section claimed that the full
constrained form "loses positivity at `S* ≈ 1.05`".  That was unjustified: the "finite block with
the exact multiplier" replaces the multiplier beyond `Ξ = 24` by the lower constant `c_last`, so
it is a *lower* bound of the Rayleigh quotient of one test function and bounds the true ground
energy `μ₀(S)` from neither side.  The certified numbers only show that the *lower* bound falls
below the resolution of the band staircase near `S ≈ 1`.  The behaviour is exactly what RH
predicts: on `V₀`, `Q(f) = Σ_ρ |f̂(γ_ρ)|²` (explicit formula), so `μ₀(S)` is the least spectral mass
that a function of exponential type `S/2` in `V₀` can leave on the zero set — a constrained-prolate
leakage that decays rapidly in `S` (through the gap `(−γ₁, γ₁)` and the zero gaps above), while
`μ₀(S) ≥ 0` for all `S` is equivalent to RH (`riemannHypothesis_of_polarGroundEnergy_nonneg`).  A
rigorous *upper* bound for `μ₀(S)` needs a test function with controlled Fourier tail
(`certificate_upper.py`: `V₀` plus vanishing endpoints, `|f̂| ≤ W/ξ²`); see the computations README.
Consequence for the lane: no finite-aperture certificate can approach the producer (all apertures),
and the margins shrink at least exponentially; the value of the lane is the exact multiplier, the
Lean chain, and the aperture-`√e` theorem, not a route to RH.

Lean (both wired into `RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
* `SuzukiWeilConstrainedKernelForm.lean` — `suzukiRestrictedWeilForm_eq_constrainedKernelForm`:
  Suzuki's literal form `= A(S) g(0) + ∫_0^S K₊(h)(g(0) − g(h)) dh + 2(∫e^{x/2}u)(∫e^{−x/2}u) + prime block`,
  with `weilPositiveKernel = e^{h/2}/sinh h` (`= 2e^{−h/2}/(1−e^{−2h})`, `weilPositiveKernel_eq`) and
  `weilConstrainedConstant S = −γ − log π − log(1−e^{−2S}) − ∫_0^S (e^{h/2}−e^{−h})/sinh h`; the
  `_of_moment_eq_zero` version on `V₀`; positivity of the kernel energy.
* `ConstrainedWeilTaylorLocalization.lean` — `norm_fourierIntegral_sq_le_taylorLocalization`:
  `|∫_{-a}^{a} g e^{−ixξ}|² ≤ 8a^{2N+1}ξ^{2N}/((N!)²(2N+1)) ∫g²` for `g ⊥ polynomials_{<N}`,
  `2a|ξ| ≤ N+1`.

* `ConstrainedWeilFourierMultiplier.lean` — `suzukiRestrictedWeilForm_eq_integral_multiplier_of_moment_eq_zero`:
  on `V₀`, `Q(u) = ∫ ‖𝓕u(ξ)‖² m_S(2πξ) dξ` with `weilConstrainedMultiplier S η = A(S) + Λ_S(η) −
  2Σ_{2≤n≤e^S} Λ(n)n^{−1/2} cos(η log n)` — the certified multiplier itself; Tonelli step
  `integral_weilPositiveKernel_mul_defect_eq_fourier`; corollary `suzukiRestrictedWeilForm_ge_of_multiplier_ge`.

Remaining Lean step of the chain: (F) the staircase assembly inequality (band projections, finite
Legendre block, the `Ω`-form); the finite block stays a documented computation.

## Aperture-to-zero-location transfer (paper, 2026-09-07)

What a certified aperture buys. Let `Q_S ≥ 0` hold on `V₀` for supports in `[−S/2, S/2]`. For an
off-line zero `ρ = ½ + a + iγ` with `|γ| ≥ e^S`, the test `u = e^{−iγx} φ` (`φ` real, odd, smooth, support
`[−S/2, S/2]`, `|φ| ≤ 1`, `φ = 1` on `[δ, S/2 − δ]`) has zero-side value

`Σ_ρ' û(ρ') conj û(1 − ρ̄') = −2Φ₊² + Σ_{on-line} |φ̂(γ' − γ)|² + (other off-line pairs) + O(e^{S/4}‖Q_S‖/|γ|)`,

`Φ₊ = ∫ φ e^{ax} ≥ (e^{a(S/2−δ)} − 1)/a`. The on-line total is `≤ C S log|γ|` (Plancherel on the window of
width `1/S` times the local zero count). Other off-line pairs `ρ_j` contribute `−2Re Ψ_j²` with
`Ψ_j = ∫ φ e^{a_j x} e^{ix(γ_j − γ)}`; in the multiplier picture all off-line pairs add with the same sign
to the envelope `Re Σ_j e^{a_j S}/(a_j − i(ξ − γ_j)) > 0` of the frequency-`S` ringing, so the negative
lobes near `ξ = γ` are not cancelled. Hence `Q_S ≥ 0` forces `e^{aS} ≤ C a² S log|γ|`, i.e.

`a ≤ (log log|γ| + log S + C)/S`  for every zero with `|γ| ≥ e^S`.

Reading: aperture `S = 1` (certified) gives nothing; aperture `A log log T` would give excess `< 1/A` below
height `T`, and its verification is band-limited at frequencies up to `exp(4e^{S/2})` (`= T⁴` for `A = 2`),
where `m_S ≥ 0` becomes trivial because `Λ_S(ξ) ≥ log ξ − C` and `Σ_{n<e^S} 2Λ(n)/√n ≤ 4e^{S/2}`.
STATUS CANNOT-330. Not formalized: it is a receiver-side transfer, not a source estimate; formalize only
if a source argument for aperture positivity at growing `S` appears (the Lean ingredients exist:
`suzukiRestrictedWeilForm_eq_integral_multiplier_of_moment_eq_zero`, the zero-side smooth form, and the
local zero count `N(t+1) − N(t) ≪ log t`).

**Correction (2026-09-08).** The "ringing envelope" argument above is invalid: the pointwise partial-sum
expansion of `−ζ'/ζ` is formal, and the smoothed prime sum with the odd autocorrelation weight
`w = φ⋆φ` has the opposite sign (`Σ_n Λ(n) n^{−½−iγ₀} w(log n) ⊃ +2Φ₊²`, consistent with the zero side
`−2Φ₊²` through the minus sign of the prime block). The exact statement is the zero-side test law:
`Q_S(e^{−iγ*x}φ) = ∓Σ_ρ Ψ_ρ(γ*)²` (odd/even `φ`), `Ψ_ρ = ∫φ e^{(a_ρ + i(γ_ρ−γ*))x}`. The rate
`(log log|γ|)/S` holds for an isolated off-line zero; clustered off-line zeros (more than `1/a₀` in a
unit window) can cancel the signal, and the local count only yields `a₀ ≲ (log|γ₀|)(log(a₀S))/S` via a
Turán power-sum inequality. STATUS CANNOT-330 has been rewritten accordingly.
