# Gaussian-residue nonadmission in the unweighted Xi incidence completion

- **ID:** `deninger-meyer-gaussian-residue-incidence-nonadmission`
- **Stage:** 3-formalized result recorded with paper proof
- **Type:** SOURCE-TOPOLOGY OBSTRUCTION / POSITIVE SURVIVOR
- **Status:** `[LOCAL-RESEARCH] [PAPER PROOF COMPLETE] [LEAN-PROVED]`
- **Parent:** `../../../1-in-progress/deninger-meyer-gaussian-green-resolvent.md`
- **Publication context:**
  `../../../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`
- **Lean module:**
  `../../../../../formal/GaloisForLFunctions/RHTower/DeningerMeyerXiGaussianResidueNonadmission.lean`

## 1. Frontier theorem

Fix Gaussian centre `c = 2`. For every Xi divisor-multiplicity copy `q`, write `ρq` for its
underlying divisor point and define the forced completed singular residue

```text
R(q) = -2π A(ρq) / (χ₂(ρq) (ρq - 2)),
χ₂(s) = exp((s - 2)² / (4π)),
A(s) = s(s - 1) Γ_R(s) / 2.
```

Define its coefficient-faithful analytic normalizer

```text
W(q) = -χ₂(ρq) (ρq - 2) / (2π A(ρq)).
```

The new unconditional theorem is stronger than subsequential unboundedness:

> **Cofinal Gaussian-residue blow-up.** Along the cofinite filter on actual Xi
> divisor-multiplicity copies,
>
> ```text
> |W(q)| → 0,    |R(q)| → +∞,    and    W(q) R(q) = 1.
> ```
>
> Consequently `Σq |R(q)|²` is not summable. The raw source-faithful residue packet cannot lie in
> the ordinary unweighted ℓ² Xi-incidence completion.

No zero-location premise is used. Inputs are the unconditional open-strip theorem for Xi zeros,
the internally proved infinite and locally finite Xi divisor, Euler reflection, and the exact
Gaussian–Gamma residue formula.

## 2. Uniform reciprocal-Gamma estimate

Let `ρ = β + iγ`, with `0 < β < 1`, and put `z = ρ/2`. Then
`Re(1 - z) ∈ (1/2, 1)`. The integral representation gives

```text
|Γ(x + iy)| ≤ Γ(x)    for x > 0.
```

The real Gamma function is strictly decreasing on `(0,1]`, so

```text
|Γ(1 - z)| ≤ Γ(1/2) = √π.
```

Euler reflection and nonvanishing give

```text
|Γ(z)|⁻¹ = |Γ(1-z)| |sin(πz)| / π
          ≤ |sin(πz)| / √π.
```

From the exponential definition of complex sine,

```text
|sin u| ≤ exp(|u|).
```

Finally, the factor `π^(β/2)` in `Γ_R(ρ)⁻¹` is at most `√π`. The square-root constants cancel,
yielding the uniform strip estimate

```text
|Γ_R(ρ)|⁻¹ ≤ exp((π/2)|ρ|).                    (1)
```

This avoids Stirling asymptotics completely.

## 3. Centered Gaussian decay

Put `t = |ρ - 1/2|`. Exact complex-exponential modulus and

```text
(β - 2)² + (β - 1/2)² ≤ 17/4
```

give

```text
|χ₂(ρ)| ≤ exp((17/4 - t²)/(4π)).               (2)
```

For `t ≥ 4`, triangle inequalities give

```text
|ρ - 2| ≤ |ρ| |ρ - 1|.                         (3)
```

Indeed both denominator factors are at least `t - 1/2`, while the numerator is at most
`t + 3/2`, and `t + 3/2 ≤ (t - 1/2)²` for `t ≥ 4`.

Also `|ρ| ≤ t + 1/2`. Expanding `A` in `W` and combining (1)–(3) gives the explicit cofinal
majorant

```text
|W(q)| ≤ exp((17/4 - tq²)/(4π) + (π/2)(tq + 1/2)),
tq = |ρq - 1/2|.                                (4)
```

The exponent in (4) has negative quadratic leading term. More explicitly, once
`t ≥ 4π²`, its linear term is at most half of the negative quadratic magnitude, so (4) is bounded
by a positive constant times

```text
exp(-t²/(8π)) → 0.                              (5)
```

The spectral norms `tq` tend to infinity on the cofinite filter because every bounded spectral
ball contains only finitely many Xi divisor copies. Equations (4)–(5) therefore prove
`|W(q)| → 0` cofinally.

## 4. Cofinal residue blow-up and ℓ² nonadmission

Open-strip nonvanishing of `A`, nonvanishing of `χ₂`, and `ρ ≠ 2` give the exact identity

```text
W(q) R(q) = 1.                                  (6)
```

Thus `|R(q)| = |W(q)|⁻¹`. Since `|W(q)|` approaches zero through strictly positive values,
reciprocal continuity at the positive punctured neighbourhood of zero gives

```text
|R(q)| → +∞                                    (7)
```

on the cofinite filter. In particular the coordinate norms do not tend to zero. If
`Σq |R(q)|²` were summable, its nonnegative terms would tend cofinally to zero, hence so would
`|R(q)|`; (7) contradicts this. Therefore the raw packet is not in unweighted ℓ².

## 5. Exact positive survivor: forced two-factor rigging

Let `h : XiZeroCopy → ℂ` be any horizon grade and define the diagonal admission weight

```text
d(q) = h(q) W(q).
```

Equation (6) yields coefficientwise

```text
d(q) R(q) = h(q).                               (8)
```

Consequently

```text
Σq |d(q)R(q)|² < ∞    iff    Σq |h(q)|² < ∞.    (9)
```

Every diagonal source-faithful admission therefore has two logically independent factors:

1. `W`, forced by the actual Gaussian–Gamma source residue;
2. `h`, an independent square-summable source-horizon grade.

The analytic normalizer alone corresponds to `h = 1`. It leaves the constant packet, which is not
square-summable on the infinite Xi divisor. A second grade is unavoidable.

## 6. Hostile audit

### Ordinary meromorphic continuation

Burnol property-S theory and Fourier interpolation already assemble scalar principal parts. They do
not supply this source-residue normalization, resolved Green provenance, completed augmentation
conservativity, or Hermitian Gram calibration. Continuation alone is rediscovery, not frontier work.

### Reusing the completed Xi/incidence isometry

The existing Lean comparison pulls a Hilbert norm back through a coefficient identification. It is
an exact isometry after admission, but it cannot prove admission of the raw Möbius–Gaussian packet.
The theorem above proves that raw unweighted admission is false.

### Cancelling the Gaussian and stopping

`W R = 1` leaves the constant packet. Infinite Xi support makes it non-ℓ². Analytic normalization
and global grading are separate gates.

### Choosing arbitrary rapid decay

An arbitrary weight can force summability but destroys source provenance and does not determine
Hermitian normalization. Equation (8) isolates all remaining freedom as `h`; that grade must now be
constructed from the ordinary-prime/Gamma/co-Poisson source and tested for conservativity and Gram
order.

## 7. Novelty and formal status

- Generic scalar continuation: **REDISCOVERED / BRIDGE**.
- Exact Gaussian–Gamma residue: **LOCAL-RESEARCH, LEAN-PROVED parent**.
- Cofinal actual-divisor blow-up and unweighted ℓ² nonadmission: **LOCAL-RESEARCH, LEAN-PROVED**.
- Forced analytic/horizon-grade factorization: **LOCAL-RESEARCH, LEAN-PROVED**.

Headline Lean theorems:

- `tendsto_xiGaussianGammaResidueNormalizer_cofinite_zero`
- `tendsto_norm_xiGaussianGammaResiduePacket_cofinite_atTop`
- `not_summable_norm_sq_xiGaussianGammaResiduePacket`
- `summable_weighted_packet_iff_horizonGrade`

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 8. Updated Route-L frontier

The remaining topological problem is no longer “find some completion admitting the principal
parts.” It is:

> Construct the independent grade `h` from the ordinary-prime/Gamma/co-Poisson source; prove
> `h ∈ ℓ²`; prove the resulting `hW`-weighted incidence sector is conservative before codiagonal
> augmentation; and derive its Hermitian Gram domination.

This rules out the raw unweighted completed-incidence landing and identifies the exact missing
source datum rather than hiding it inside a chosen Hilbert norm.

## Lean status

`formal/GaloisForLFunctions/RHTower/DeningerMeyerGaussianResidueGrowth.lean`, axiom audit
`propext, Classical.choice, Quot.sound` for every declaration.  The exact residue formula `(1)` was
already in the corpus (`xi_mul_poissonGaussianSingularLift_residue_eq_explicit`); what is new here
is the growth estimate `(3)`.

**Section 2, the uniform Archimedean lower bound.**

- `norm_sin_le_exp_abs_im` — the elementary bound `‖sin w‖ ≤ exp |Im w|`, from the two exponentials
  in the sine.  This replaces `(7)` and needs no `sinh`/`cosh` identity.
- `exists_gamma_bound_Icc` — the constant `M` of `(5)`: the real `Γ` is continuous on `[1/2, 1]`,
  hence bounded there.
- `pi_le_norm_Gamma_half_mul` — the strip lower bound `(8)` in cleared form
  `π ≤ ‖Γ(ρ/2)‖ · M · exp(π|γ|/2)`.  Euler reflection turns the lower bound into an upper bound on
  the reflected line, which is the corpus's `norm_Gamma_le_Gamma_re` — the modulus of `Γ` on a
  vertical line is largest on the real axis.  No Stirling expansion, as the card says.
- `norm_archFactor_lower` — `(9)` assembled with the polynomial prefactor: the power of `π`
  contributes at least `π⁻¹` on the strip, giving `‖A(ρ)‖ ≥ γ²/(2M exp(π|γ|/2))`.

**Section 3, the Gaussian inverse growth and the estimate.**

- `norm_gaussianMellinCharacter` — the exact modulus `(10)` of the Gaussian character, for any
  centre.
- `exists_residue_growth` — **the theorem `(3)`**: there are `C, T₀ > 0` such that every strip point
  with `|γ| ≥ T₀` has `‖R(ρ)‖ ≥ C exp(γ²/(32π))`.  The witnesses are `C = (π/M) e^{-1/π}` and
  `T₀ = 8π²`, exactly `(16)` and the threshold of `(15)`.

**Sections 4 and 5.**
`formal/GaloisForLFunctions/RHTower/DeningerMeyerGaussianResidueNonadmission.lean`.

- `gaussianGreenResidue` — the residue `R(ρ)` as a named object.
- `exists_xiZero_im_gt` — **the Xi zero ordinates are unbounded.**  If they were bounded the zero set
  would lie in a compact disc, since the real parts are confined to the open unit strip, and would
  therefore be finite — contradicting infinitude.  Both inputs are corpus theorems:
  `xiZeroSet_infinite`, `xiZeroSet_mem_openUnitStrip`, and `xi_zeros_closedBall_finite`.
- `not_exists_bound_gaussianGreenResidue` — **the residue family is unbounded along the Xi zeros**,
  which is the theorem of section 4.  The growth estimate is evaluated at zeros of arbitrarily large
  ordinate.
- `not_forall_norm_le_of_gaussianGreenResidue` — no carrier whose coordinate evaluations are bounded
  by a single constant admits the packet.  This is the `ℓ²` nonadmission in the only form it needs:
  every `ℓ²` family is bounded coordinatewise by its norm.
- `gaussianResidueFlattening`, `gaussianResidueFlattening_mul_self` — **the exact positive survivor**
  of section 5: `W(ρ)R(ρ) = 1` on the off-centre open strip, so the obstruction determines the
  diagonal renormalisation rather than merely rejecting the packet.

The card is now formalized end to end.

### Log

- 2026-08-03 — Formalized the growth estimate `(3)` and its two inputs.  The Archimedean lower bound
  reuses the corpus's vertical-line modulus bound for `Γ` rather than rebuilding it, which is what
  makes the Stirling-free route work.
- 2026-08-03 — Formalized sections 4 and 5.  The Xi input needed for unboundedness was already in the
  corpus in exactly the two pieces the paper argument uses — infinitude of the zero set and
  finiteness of the zeros in a compact disc — so the escape-of-ordinates step is four lines.  With
  the growth estimate this gives unboundedness of the residue family, hence nonadmission in any
  carrier with norm-bounded coordinates; and the flattening factor inverts the residue pointwise on
  the off-centre strip.
