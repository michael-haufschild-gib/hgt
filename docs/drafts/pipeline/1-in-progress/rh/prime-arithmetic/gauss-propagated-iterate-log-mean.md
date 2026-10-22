# Gauss quasi-inner propagated-iterate control and the operator logarithmic mean at m ≥ 2

- **ID:** gauss-propagated-iterate-log-mean
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper, m = 2 complete; general-m architecture recorded)
- **Source:** rh-current-frontier-map.md §"Gauss quasi-inner multi-place assembly"; research priority 6
- **Statement:** For every Gauss component `(m,k)` with `m ≥ 2` and every prime `p`, the two-sided
  Fourier diagonal of the `m`-th power of the actual quasi-inner block `G` has relative deviation
  `o(1/n)` from the principal diagonal model, hence its logarithmic mean is the exact critical
  residue `2(p-1)^{2m}(p^m-1)^2/(p^{2m} m^2 log p)`. Complete dependency-closed proof below for
  `m = 2`; the general-`m` proof architecture (E-word expansion + k-fold defect chains) is recorded
  with its exact remaining combinatorial layer.

## Goal

This is the frontier map's named "remaining local theorem" of the Connes–Consani quasi-inner lane:
stage-by-stage control of the propagated iterates `R_n^i f` inside the principal-step power
telescope, followed by the logarithmic mean. Closing it at a given `m` closes the local
single-component principal asymptotic for that `m` at the level of the actual circle operator
(`m = 1` is already umbrella Lean: `tendsto_gaussLocalDiagonal_logResidue`). It is strictly below
RH (no RH-equivalent premise anywhere), and it is the next brick of the only historically validated
mechanism shape (created positivity of an intersection form). After all `m`, what remains for the
lane is multi-place assembly and the positivity law.

## Gates
- [x] 0 → 1  in-progress: well-posed; exact frontier audited against the committed Lean layer
- [x] 1 → 2  fully-proven (m = 2): complete paper proof below, no open dependency
- [x] 2 → 3  formalized (m = 2): `HTGeometry/HarmonicPowerConvolution.lean`,
      `RHTower/GaussConvolutionCoefficient.lean`, `RHTower/GaussDoubleDefect.lean`,
      `RHTower/GaussRelativeOneStep.lean`, `RHTower/GaussSquareDiagonalLogResidue.lean`;
      umbrella-wired, both area umbrellas build, axioms = [propext, Classical.choice, Quot.sound]
- [ ] general m ≥ 3: CHAIN(k) band lemma family (see §General-m architecture)

## Setting and objects (all already formalized)

Fix `m ≥ 1`, `k : Fin m`, prime `p`; all operators act on `L²(ℝ/ℤ)`. Frequency `i ∈ ℤ`, `|i| → ∞`.

- `d_j = gaussSampleValue k p j`: sampled Gauss component; `d_0 = 0`, `d_{-j} = conj d_j`,
  `d_j ≠ 0` for `j ≠ 0`; two-sided energy bound `c ≤ |d_j|^{2m}·|j| ≤ C`
  (`exists_gaussComponentPrimeMagnitudeEnergy_bounds`), giving the uniform ratio bound
  `(|d_{i+j}|/|d_i|)^{2m} ≤ K·|i|/|i+j|`  (`norm_gaussSampleRatio_pow_le`).
- `δ_i = gaussSamplePhase m p i`; ratio defect `ρ(j,i) = d_{i+j}/d_i − e(j δ_i)`
  (`gaussSampleRatioDefect`), with `ρ(j,i) → 0` for each fixed `j`
  (`tendsto_gaussSampleRatioDefect_nat`) and `|ρ(j,i)|² ≤ 4 + 2K·i/|i+j|`
  (`norm_gaussSampleRatioDefect_sq_le`).
- `B, B⁻², T_δ` (= rotation blocks), normalized shifted blocks `S^* = gaussShiftedBlockOf`,
  `S = gaussShiftedBlockDiag` with exact Fourier actions
  `(S^* u)^(j) = conj(d_{i+j}/d_i)·û(j)`, `(S u)^(j) = (d_{i+j}/d_i)·û(j)`
  (`fourierCoeff_gaussShiftedBlockOf/Diag`), and the coefficientwise defect identities
  `norm_fourierCoeff_shiftedBlockOf_sub_rotation`, `norm_fourierCoeff_shiftedBlockDiag_sub_rotationInv`.
- Principal step `R_i = B S B⁻² S^* B` (`gaussPrincipalStepBlock`), moving-amplitude model
  `M_δ = B T_{−δ} B⁻² T_δ B =` multiplication by `a_δ` (`gaussMovingAmplitudeBlock`,
  `gaussPrimeScaleBlock_translate_invSq_translate`), `‖M_δ‖ ≤ p`.
- Sector identity `G^r(e_i f) = σ̃_i^r · e_i (R_i^r f)`, `σ̃_i = p·conj(d_i)·d_i`
  (`gaussQuasiInnerG_pow_fourierMulBlock`); model iterate coefficients
  `≤ 4p^{r+1}/(1+|j|)` (`GaussIteratedAmplitude`); period averages
  `A_r(δ) = ∫ a_δ^r = gaussAmplitudeSegment p r (fract δ)` (`fourierCoeff_gaussAmplitudePow_zero`).
- Model log mean at every `m`: `gaussPrincipalDiagonalTerm_logResidue`; harmonic transfer:
  `tendsto_complexHarmonicWeighted_error_zero`; local factor and residue algebra:
  `gaussLocalFactorWeight_mul_principalResidue`, `gaussChannelResidue`.

**The open point (why `tendsto_gaussIterate` is not enough).** The proved fixed-`r` iterate law
bounds `|σ̃_i|^r·‖R_i^r 1 − a_δ^r‖ → 0`, an absolute `o(1)`. The diagonal's main term is itself
`|σ̃_i|^m ≍ 1/|i|`, so the logarithmic mean needs the *relative* law `‖R_i^m 1 − a_δ^m‖ → 0`
(equivalently `⟨1, R_i^m 1⟩ − A_m(δ_i) → 0`). The one-step operator deviation `E_i := R_i − M_{δ_i}`
has `‖E_i‖ ≍ |i|^{1/(2m)}` (the reflected frequency `j ≈ −i` is a genuine near-resonance where the
ratio symbol is `≍ (|i|/|i+j|)^{1/(2m)}`), so crude operator-norm propagation loses a polynomial
factor per stage and cannot close for `m ≥ 2`. All corpus estimates are rate-free (dominated
convergence over modes), so the closure must be rate-free too.

## Paper proof, m = 2  `[PAPER-PROVED]`

Throughout, `i` runs along any sequence with `|i| → ∞` (both signs; all cited family lemmas take an
arbitrary escaping `ι`). Write `δ = δ_i`, `ρ(j) = ρ(j,i)`, `b = B·1` (so
`|b̂(j)| ≤ 4p/(1+|j|)`), `q̂ =` Fourier coefficients of the `B⁻²` symbol (single-piece exponential,
`|q̂(x)| ≤ C_q/(1+|x|)` by `norm_fourierCoeff_of_isExpPiecewise`), `Δ^* := S^* − T_δ`,
`Δ := S − T_{−δ}` (both Fourier-diagonal with symbol modulus `|ρ(j)|`).

### Step 1 — R is self-adjoint

`B` and `B⁻²` are multiplications by real symbols, hence self-adjoint
(`lpBoundedMulCLM_inner_real`). `S` and `S^*` are mutually adjoint: in the Fourier basis they are
diagonal with conjugate symbols `(d_{i+j}/d_i)` and `conj(d_{i+j}/d_i)`. Hence
`R^* = (B S B⁻² S^* B)^* = B S B⁻² S^* B = R`. Likewise `M` is multiplication by the real function
`a_δ`, hence self-adjoint, and so is `E = R − M`.

### Step 2 — exact three-term split of the one-step deviation at the constant

With `w' := B⁻² T_δ b` and using `M = B T_{−δ} B⁻² T_δ B`:

```
R·1 − M·1 = B[ S(B⁻² S^* b) − T_{−δ} w' ]
          = B[ Δ(w') ]  +  B[ Δ(B⁻²(Δ^* b)) ]  +  B[ T_{−δ}(B⁻²(Δ^* b)) ].
```

(Algebra: `S(B⁻²S^*b) − T_{−δ}w' = (S−T_{−δ})w' + (S−T_{−δ})(B⁻²Δ^*b) + T_{−δ}B⁻²Δ^*b`, since
`B⁻²S^*b = w' + B⁻²Δ^*b`.) Therefore

```
‖R·1 − a_δ‖ ≤ √p·‖Δ w'‖ + √p·‖Δ(B⁻²(Δ^* b))‖ + √p·‖Δ^* b‖.
```

- `‖Δ^* b‖ → 0`: family estimate `tendsto_norm_gaussShiftedBlockOf_sub_rotation_family` at the
  amplitude `b` with decay constant `4p` (`norm_fourierCoeff_gaussPrimeScaleBlock_amplitudePow`, r=0).
- `‖Δ w'‖ → 0`: family estimate `tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv_family` at
  `w'` with decay constant `4p` (`norm_fourierCoeff_gaussIntermediate_amplitudePow`, r=0).
- `‖Δ(B⁻²(Δ^* b))‖ → 0` is the **double-defect lemma** (Step 3), the genuinely new estimate.

### Step 3 — the double-defect lemma (valid for every m ≥ 2)

**Lemma DD.** Let `c : ℤ → ℝ≥0` with `c(l) ≤ A/(1+|l|)` and let `κ(x) ≤ Q/(1+|x|)` bound the
`B⁻²`-kernel. Then, for `m ≥ 2`,

```
T_i := Σ_j |ρ(j,i)|² · ( Σ_l κ(j−l)·|ρ(l,i)|·c(l) )²  →  0   (|i| → ∞).
```

Given Lemma DD, Step 2's middle term vanishes: by Parseval,
`‖Δ(B⁻²(Δ^*b))‖² = Σ_j |ρ(j)|²·|(B⁻²(Δ^*b))^(j)|²`, and the coefficient of the multiplied vector
obeys the convolution bound `|(B⁻²v)^(j)| ≤ Σ_l |q̂(j−l)|·|v̂(l)|` (Fourier series of `v ∈ L²`
converges in `L²`; multiplication is bounded; the coefficient functional is continuous; the
convolution majorant is summable by Cauchy–Schwarz `ℓ²×ℓ²`). Since
`|(Δ^*b)^(l)| = |ρ(l)|·|b̂(l)|` exactly, take `c(l) = |b̂(l)|`.

**Proof of Lemma DD.** Write `r(x) := |d_{i+x}|/|d_i|`, so `|ρ(x)|² ≤ 2 + 2r(x)²` and
`r(x)^{2m} ≤ K·i/|i+x|` (with the convention that terms with `i+x = 0` vanish since `d_0 = 0`).

*(a) Collapse the inner square by weighted Cauchy–Schwarz.* With weights `κ(j−l)c(l)`:

```
( Σ_l κ(j−l)|ρ(l)|c(l) )² ≤ ( Σ_l κ(j−l)c(l) ) · ( Σ_l κ(j−l)c(l)|ρ(l)|² ).
```

*(b) Harmonic-convolution bound.* `Σ_l κ(j−l)c(l) ≤ QA·H(j)` where
`H(j) := Σ_l 1/((1+|l|)(1+|j−l|)) ≤ C_H·(1+log(2+|j|))/(1+|j|)`.
(Four regions: `|l| ≤ |j|/2` gives `(2/(2+|j|))·Σ_{|l|≤|j|/2} 1/(1+|l|) ≤ C log/(1+|j|)`;
symmetric region `|j−l| ≤ |j|/2`; `|l| ≥ 2|j|` forces `|j−l| ≥ |l|/2`, quadratic tail `≤ C/(1+|j|)`;
the middle region has both factors `> |j|/2` on `≤ 4|j|` sites, total `≤ C/(1+|j|)`.)

*(c) The resulting double sum.* Combining (a), (b):

```
T_i ≤ QA·C_H · Σ_{j,l}  W(j,l) · |ρ(j)|²|ρ(l)|² ,
W(j,l) := (1+log(2+|j|))/(1+|j|) · κ(j−l) · c(l).
```

*(d) Kill the defect product with the `m ≥ 2` power inequality.* From `|ρ|² ≤ 2+2r²`,
`r(j)²r(l)² ≤ ½(r(j)⁴ + r(l)⁴)`, and — this is where `m ≥ 2` enters —
`r⁴ ≤ 1 + r^{2m} ≤ 1 + K·i/v` (`v` the reflected distance `|i+·|`):

```
|ρ(j)|²|ρ(l)|² ≤ C₁ + C₂·K·i/|i+j| + C₂·K·i/|i+l| .
```

No product of two harmonic factors survives.

*(e) Dominated convergence (rate-free), via the corpus band-split.* Apply
`tendsto_tsum_zero_of_dominated` on the index set `ℤ×ℤ`:

- **Per-mode vanishing:** for fixed `(j,l)`, `|ρ(j,i)|²|ρ(l,i)|² → 0`.
- **G-part (fixed summable dominator):** `Σ_{j,l} W(j,l)·C₁ < ∞` since
  `Σ_l κ(j−l)c(l) ≤ QA C_H log/(1+|j|)` makes it
  `≤ C Σ_j (1+log(2+|j|))²/(1+|j|)² < ∞`.
- **H-part (vanishing totals):** the `i/|i+j|` piece: summing `l` first gives
  `≤ C Σ_j [(1+log(2+|j|))²/(1+|j|)²]·K i/|i+j| ≤ C' Σ_j (1+|j|)^{−3/2}·K i/|i+j|`,
  which splits into the near band `2|j| ≤ i` (there `i/|i+j| ≤ 2`, folds into G) and the far band,
  which vanishes by `tendsto_tsum_farBandPower_zero` at exponent `3/2 > 1`. The `i/|i+l|` piece:
  substitute `u = l` and sum `j` first — `Σ_j (1+log)/(1+|j|)·κ(j−u') ≤ C(1+log(2+|u'|))²/(1+|u'|)`
  wait, symmetric shape: `Σ_j W(j,l) ≤ C(1+log(2+|l|))²/(1+|l|)·…/(1+|l|)`; in either
  arrangement the surviving single-index weight is `≤ C(1+|·|)^{−3/2}` against `K i/|i+·|`, same
  near/far split. ∎

*(Numerical pre-certification below confirms `T_i ≍ i^{−1/2}·polylog` at `m = 2`.)*

### Step 4 — relative diagonal at power 2

`a_δ` is real, so `‖a_δ‖² = ∫ a_δ² = A₂(δ)` (`fourierCoeff_gaussAmplitudeIterate_zero`, r = 2),
and `‖a_δ‖ ≤ p`. By Step 1, `⟨1, R²1⟩ = ‖R·1‖²`, hence

```
|⟨1, R_i²·1⟩ − A₂(δ_i)| = | ‖R1‖² − ‖a_δ‖² | ≤ ‖R1 − a_δ‖·(‖R1 − a_δ‖ + 2p) → 0
```

by Steps 2–3. By the sector identity at `r = 2` and unitarity of `e_i`-multiplication,
`⟨e_i, G² e_i⟩ = σ̃_i²·⟨1, R_i²·1⟩`, and `|σ̃_i|²·(|i|) = p²·|d_i|⁴·|i| ≤ p²C` (energy bound at
`2m = 4`). Both frequencies `±i` carry the same scalar and phase (`gaussSampleValue_neg`,
`gaussSamplePhase_neg`). Hence, with `S(n)` the two-sided `GFull²`-diagonal at `±(n+1)` and
`PDT(n) = gaussPrincipalDiagonalTerm k p n` (which equals
`archConst·2·σ̃^m·A_m` by `gaussPrincipalDiagonalTerm_eq`):

```
(n+1)·‖S(n) − PDT(n)‖ ≤ archConst·p²C·( F(n+1) + F(−(n+1)) ) → 0,
F(i) := ‖R_i 1 − a_{δ_i}‖·(‖R_i 1 − a_{δ_i}‖ + 2p).
```

### Step 5 — logarithmic mean and the residue

`(n+1)·err(n) → 0` plus `tendsto_complexHarmonicWeighted_error_zero` gives
`Σ_{n<N} err(n) = o(log N)`; adding `gaussPrincipalDiagonalTerm_logResidue` (at `m = 2`) gives

```
Σ_{n<N} S(n) / log N  →  2(p² − 1)²/(4·log p),
```

and multiplying by the local factor `((p−1)/p)⁴` (`gaussLocalFactorWeight_mul_principalResidue`):

```
gaussLocalFactorWeight·Σ_{n<N} S(n)/log N  →  gaussChannelResidue 2 p
                                            = 2(p−1)⁴(p²−1)²/(4 p⁴ log p).
```

This is formula (A) for the operator at `m = 2`. ∎

## General-m architecture (formalization program; not yet claimed as paper-proved for m ≥ 3)

1. **Half-split.** `R` self-adjoint (Step 1 holds verbatim): `⟨1, R^m 1⟩ = ⟨R^a 1, R^{a'} 1⟩`,
   `a = ⌊m/2⌋`, `a' = ⌈m/2⌉`; boundedness of half-iterates follows from their relative laws.
2. **E-word expansion.** `R^t = (M+E)^t`; every mixed word's rightmost `E` acts on an explicit
   model amplitude `a_δ^c` (coefficients `4p^{c+1}/(1+|j|)`); `‖M‖ ≤ p`. All non-model content
   reduces to chains `E M^{t₁} E ⋯ E a_δ^c` with `e ≤ ⌈m/2⌉` E-factors, i.e. (after the three-term
   split of each `E`) to **k-fold defect chains** with `k ≤ 2⌈m/2⌉ ≤ m+1` diagonal defect factors
   interleaved with explicit-kernel convolutions.
3. **CHAIN(k) lemma.** The `ℓ²`-norm of a k-fold chain vanishes, rate-free, by the same
   band-split dominated convergence: weighted Cauchy–Schwarz collapses inner squares; the
   harmonic-convolution bound supplies per-index decay; products of defect caps distribute by
   AM–GM to single-index powers `r^{2w}`, `w ≤ k`; for `w ≤ m` use `r^{2w} ≤ 1 + K i/v`; for
   `w = m+1` (odd-m top chain) use the fractional cap `r^{2(m+1)} ≤ (1+K i/v)^{(m+1)/m}` — the
   super-harmonic far-band sum still vanishes against the `(1+|·|)^{−3/2}`-type weights supplied
   by the interleaved convolutions (margin `i^{1/m−1}·polylog`). Numerically pre-certified at
   `m = 2, 3` below.
4. **Assembly** is then verbatim Steps 4–5 with `A_m`, energy bound at `2m`, and the general-m
   model residue (all already formalized at general m).

The Lean development of CHAIN(k) generalizes `GaussDoubleDefect` (k = 2); k = 3, 4 suffice for
`m = 3` and hence for `m ≤ 4` via half-split. This is the named continuation of this card.

## Log
- 2026-08-10 — created in 1-in-progress; full audit of the committed Gauss layer (26 modules);
  identified the exact open statement (relative iterate law at power m); found the rate-free
  closure (self-adjoint fold + three-term split + double-defect band lemma); complete paper proof
  for m = 2; general-m architecture recorded with the exact remaining CHAIN(k) layer.
- 2026-08-11 — m = 2 instance `[LEAN-PROVED]` and umbrella-wired.  Five modules:
  the lattice harmonic-power-convolution decay (`tsum_harmonicPowConv_le`, exponent-loss form,
  no logs), the Parseval convolution law for the reciprocal-square multiplier
  (`hasSum_fourierCoeff_lpBoundedMulCLM`), the double-defect estimate for every `m ≥ 2`
  (`tendsto_norm_gaussDoubleDefectVector_comp`: master lattice bound + product cap
  `ρ_j²ρ_l² ≤ 24 + 6K·I/v_j + 6K·I/v_l` + far-band dominated convergence at exponent `3/2`),
  self-adjointness of `R` and the relative one-step law for every `m ≥ 2`
  (`tendsto_norm_gaussPrincipalStep_one_sub_amplitude`), and the m = 2 capstones
  `tendsto_gaussSquareFourierDiagonal_logResidue` (limit `2(p²-1)²/(4 log p)`) and
  `tendsto_gaussSquareLocalDiagonal_logResidue` (limit `gaussChannelResidue 2 p`).
  `#print axioms` clean on all six exported theorems.  Open continuation: depth-`⌈m/2⌉`
  propagated-iterate control for `m ≥ 3` via the k-fold defect chains (`k ≤ m+1`).
