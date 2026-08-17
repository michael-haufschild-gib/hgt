# Logarithmic recurrence is the sharp polynomial-carrier wall for Suzuki orbit transport

- **ID:** `suzuki-log-recurrence-polynomial-carrier-trichotomy`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-log-recurrence-polynomial-carrier-trichotomy.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/SuzukiLatticeCarrierWeight.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiLatticeShellSummability.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPositionCommutatorGroup.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiPolynomialGroupEstimate.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiHatanoNelsonEllipse.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiApertureBorelCantelli.lean`

## Formal content

The card's §10 chain is closed unconditionally.

**Event summability `(8)`.**  `latticeL1 ν = ∑ᵢ |νᵢ|` and `polyWeight κ ν = (1 + |ν|₁)^{-κ}`.  Lean
proves the coordinatewise domination `1 + |νᵢ| ≤ 1 + |ν|₁`, hence
`(1 + |ν|₁)^{-p} ≤ ∏ᵢ (1 + |νᵢ|)^{-p/d}`, and that the product of one-dimensional `p/d`-series is
summable for `p > d` (`summable_prod_one_add_abs`, by induction over coordinates).  Therefore
`summable_polyDecay_fin : (d:ℝ) < p → Summable (fun ν : Fin d → ℤ => (1 + |ν|₁)^{-p})`, and with
the pointwise event bound `polyWeight_sq_mul_event_le`,

```text
summable_polyWeight_sq_event :
  d < 2κ − 2σQ → (∀ ν, τ ν ≤ Q log(2 + |ν|₁))
  → Summable (fun ν => polyWeight κ ν ^ 2 * exp (2 σ τ ν)).
```

No shell count is used.

**Bounded generator ratios `(14)`.**  `one_add_latticeL1_add_le` is the submultiplicativity
`1 + |ν + s|₁ ≤ (1 + |ν|₁)(1 + |s|₁)`; `polyWeight_ratio_le` and `polyWeight_ratio_le'` give the
two-sided bound `(1 + |s|₁)^κ`, uniform in `ν`.

**Iterated position commutator identity `(15)`.**  In a complete normed algebra, for `C = AX − XA`
with `AC = CA`, Lean proves `hasDerivAt_conj_position` (the conjugated coordinate has constant
velocity `C`), hence `conj_position_eq : e^{tA} X e^{-tA} = X + t C` and
`position_mul_exp : X e^{-tA} = e^{-tA} (X + tC)`.  Iterating,

```text
listProd_mul_exp : (l.map X).prod * exp (-t • A)
                     = exp (-t • A) * (l.map fun i => X i + t • C i).prod,
```

and `exists_time_polynomial` exhibits the shifted word as `∑_{k ≤ |l|} t^k • P k` with `P`
independent of `t`, which is the degree bound of `(15)`.

**Polynomial group estimate `(17)`.**  `wordProd` is the ordered coordinate word and
`posNorm X n v = ∑_{k ≤ n} ∑_{|w| = k} ‖X^w v‖` the position graph norm.  `DiffOp S X n` is the
inductive class of finite sums `∑ B · X^w` with `B` in a bounded symbol class `S` closed under
commutation with the coordinates and under products, `|w| ≤ n`.  Lean proves
`DiffOp.pos_mul`, `DiffOp.symbol_mul` and `DiffOp.exists_bound` (order-`n` operators are bounded by
`posNorm n`), then `exists_diffOp_expansion`: the shifted word expands as `∑ t^k • P k` with
`P k` of order at most `|l| − k`.  Hence

```text
exists_polynomial_word_bound :
  ∃ M ≥ 0, ∀ t v, ‖(l.map fun i => X i + t • C i).prod v‖
                    ≤ M (1 + ‖t‖)^{|l|} posNorm X |l| v,
```

with `M` uniform in `t`, and with an isometric intertwining evolution,

```text
exists_polynomial_group_bound :
  ∃ M ≥ 0, ∀ t U, (∀ i v, X i (U v) = U (X i v + t • C i v)) → (∀ v, ‖U v‖ = ‖v‖)
    → ∀ v, ‖(l.map X).prod (U v)‖ ≤ M (1 + ‖t‖)^{|l|} posNorm X |l| v.
```

No complex interpolation is used.

**Hatano–Nelson ellipse `(21)`–`(24)`.**  `hatanoNelsonSymbol κ θ = e^{κ + iθ} + e^{−κ − iθ}`;
`hatanoNelsonSymbol_eq` is the ellipse `2 cosh κ cos θ + 2i sinh κ sin θ`,
`hatanoNelsonSymbol_quarter` is `λ_κ(π/2) = 2i sinh κ`, and `hatanoNelsonSymbol_im_ne_zero` shows it
leaves the real axis for `κ > 0`.  `primeStepSymbol_im` is the weighted sine polynomial `(24)` of
the finite prime-power adjacency.

**Borel–Cantelli aperture theorem `(28)`.**  `badAperture ℓ q ν` is the window `(26)`;
`measure_badAperture_le` bounds its Lebesgue measure by `(2 + |ν|₁)^{-q}`,
`summable_badAperture_length` is `(27)` for `q > d`, and Borel–Cantelli gives
`ae_finite_badAperture`: almost every aperture meets only finitely many windows.  Hence

```text
ae_finite_logType :
  ∀ᵐ a, ∃ F : Finset (Fin d → ℤ), ∀ ν ∉ F, 0 < |2a − ℓ ν|
        → −log |2a − ℓ ν| ≤ q log (2 + |ν|₁).
```

Every declaration audits to `[propext, Classical.choice, Quot.sound]`.  No `sorry`, `axiom`,
numerical computation, or RH premise occurs.

## Open boundary

Formalization certifies the carrier chain, not the forward research of §7–§8.  `(29)` (an
all-aperture biweighted/closed-relation dichotomy) and `(30)` (`SUZUKI-BIWEIGHTED-EVANS-DICHOTOMY`)
remain open, as does the source-selected homogeneous cancellation.  The effective Matveev bound
behind `(5)` is Literature and is not part of the formalized chain.
