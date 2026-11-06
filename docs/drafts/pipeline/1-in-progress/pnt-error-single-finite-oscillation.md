# Single finite trigonometric oscillation of the Chebyshev prime error

- **ID:** pnt-error-single-finite-oscillation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.9 (tasks A31, B81, B82, F12)
- **Statement:** For every `β > 1/2`, `η > 0`, and nonzero finite trigonometric polynomial `T(u) = ∑_{j ∈ J} c_j e^{i γ_j u}` with distinct real frequencies `γ_j`, `ψ(x) - x ≠ x^β T(log x) + O(x^{β - η})` as `x → ∞`.

## Goal
Resolve §2.9 of `obstacles-summary.md`:
1. Establish the exact two-way equivalence (`A31`) between `¬ RHTower.AsymptoticAbscissaLaw` and the existence of `β > 1/2`, `η > 0`, and a nonzero finite trigonometric polynomial `T` such that `ψ(x) - x = x^β T(log x) + O(x^{β - η})` (valid across arbitrary zero multiplicities because `-ζ'/ζ` has only simple poles).
2. Decide whether the combined exact arithmetic constraints of `ℤ` (`ψ(x) = ∑_{n ≤ x} Λ(n)` integer-supported with jumps `≥ log 2`, `N(x) = ⌊x⌋` with exact sawtooth, Euler product `∏_p (1 - p^{-s})^{-1}`, and exact Riemann functional equation `ξ(1 - s) = ξ(s)`) refute `ψ(x) - x = x^β T(log x) + O(x^{β - η})`, thereby establishing `RHTower.AsymptoticAbscissaLaw` unconditionally.

## Gates
- [x] 0 → 1  in-progress: corpus & literature inventory complete; firewall models isolated
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean 4 formalization compiled clean with `lake --old env lean`, wired into umbrella

## Firewall constraints (proven countermodels that any valid proof must exclude)
1. **Continuous Beurling systems** (`overRegularZeta`, `BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean`): satisfy `ψ_B(x) - ρ x = x^β T(log x) + O(1)` and `N_B(x) - ρ x - C → 0`, violating discrete `ℕ`-support and exact Riemann FE.
2. **Discrete Beurling Euler products without FE** (`BeurlingOneOffZeroCountermodelsAndDefectTradeoff.lean`, Broucke–Debruyne–Vindas): satisfy positive Euler product with one-off off-line zero pair, violating integer norms and exact Riemann FE.
3. **Dirichlet series with exact FE and finite `ℕ`-prefix** (`functional-equation-is-blind-to-rh.md`, Davenport–Heilbronn): satisfy `s ↔ 1 - s` FE on `ℕ`-Dirichlet series with off-line zeros, violating Euler product (`Λ(n)` multiplicativity).
4. **Function-field zeta functions** (`𝔽_q[T]`): have periodic vertical zeros (`AAL` holds automatically by vertical periodicity `2πi / log q`), whereas over `ℤ` `log p` are `ℚ`-linearly independent.
5. **Symmetric rational zero relocation on `ξ`** (`SymmetricRationalZeroRelocationBohrObstruction.lean`, `zeroRelocation_destroys_vertical_bohr_and_LSeries`, `zeroRelocationFactor_two_mul_sub_one_eq_zero`): `completedRiemannZeta · zeroRelocationFactor ρ₀ γ₁ γ₂` preserves the exact `s ↔ 1 - s` functional equation, critical-line reality, and `1 + O(|t|^{-1})` vertical asymptotics while implanting `{ρ₀, conj ρ₀}`, yet strictly destroys vertical Bohr almost periodicity (and every summable `LSeries` representation) on every line `Re s = σ > 1` and vanishes at the half-shifted Eisenstein argument `2 s_* - 1` (`s_* = (1 + ρ₀)/2`, `Re s_* ∈ (3/4, 1)`).

## Equivalence, canonical rigidity, and prime-dilation characterizations (formalized)
- **Exact `A31` equivalence:** `¬ AsymptoticAbscissaLaw ↔ PrimeErrorIsFiniteOscillation` (`not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation` in `TheOneOffsAreFiniteOscillationsOfThePrimeError.lean`, `ThePrimeErrorExpansionLocatesZeros.lean`).
- **Canonical rigidity, sharp `Θ - Θ₂` threshold, sign changes, and parity transfer** (`PrimeErrorFiniteOscillationRigidityAndSignChanges.lean`): unconditional `1/2 ≤ σ₀` remainder floor (`half_le_of_oscillationError_bound`); pinning `β = Θ = zetaZeroAbscissa < 1` and global Fourier quantization `oscillationCoeff S c μ = -ord_{s = Θ + iμ}(ζ)/(Θ + iμ)` with `oscillationCoeff S c 0 = 0` (`oscillationCoeff_eq_neg_zeta_order_div`, `oscillationCoeff_zero_eq_zero`); uniqueness of `(β, T)` (`primeErrorFiniteOscillation_unique_abscissa_and_profile`); sharp secondary-abscissa ceiling `η ≤ Θ - Θ₂` (`eta_le_zetaZeroAbscissa_sub_secondAbscissa`) and converse for all `0 < η < Θ - Θ₂` (`exists_primeErrorFiniteOscillation_of_lt_gap`); bounded-logarithmic-gap bidirectional sign changes `± δ e^{Θ u}` (`exists_bounded_log_gap_sign_changes_of_primeErrorIsFiniteOscillation`); and exact alternating parity transfer `∑_{n ≤ x} (-1)^n Λ(n) = 2 (Nat.log 2 ⌊x⌋₊) log 2 - ψ(x)` (`sum_alternating_vonMangoldt_eq`, `alternating_vonMangoldt_finiteOscillation`).
- **Multiplicative dilation annihilation and two-prime equivalence** (`MultiplicativeDilationAnnihilationOfPrimeError.lean`): `dilationSetOp b β S` (`b > 1`, `β < 1`) annihilates `x^β T(log x)` identically (`dilationSetOp_rpow_mul_finiteOscillation_eq_zero`), scales `x` by `mainTermFactor b β S ≥ (1 - b^{β - 1})^{2|S|} > 0` (`mainTermFactor_ge_pos`), clears the `s = 1` Mellin pole without `t = 1` boundary error (`integral_Ioi_one_psi_div_mul_cpow`, `neg_dilationSymbol_mul_deriv_zetaResidueUnit_eq`), pins zeros in `{Re s > σ₀}` to `Re ρ = β` and `Im ρ ∈ (S ∪ -S) + (2π / log b)ℤ` (`re_eq_and_im_mem_periodic_of_dilation_bound`), and gives the exact two-prime (`p ≠ q`) characterization `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`.

## Approach
1. **Equivalence layer (`A31`):** Mellin continuation of `(ψ(x) - x) x^{-s-1}` vs. truncated Perron contour shift across the bilateral spectral-gap strip `(β₁, β_*)` (`not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`).
2. **Contradiction / rigidity search in `¬AAL` (`F12`):** Test interactions between (a) exact integer jump structure of `ψ(x)` and `N(x) = ⌊x⌋`, (b) Selberg / divisor convolutions and integer-supported atomic mass floors, (c) analytic continuation of `log((s - 1)ζ(s))` on `{Re s > β₁, Im s > T_*}` coupled to `{Re s < 1 - β₁, Im s > T_*}` via `ξ(1 - s) = ξ(s)` and to the Euler Dirichlet series on `Re s > 1`.

## Turán derivative route

- **Lean:** `not_asymptoticAbscissaLaw_has_high_jet_bounds` supplies the high zero-free region and Cauchy bounds for every derivative of the actual logarithmic derivative, from `¬AAL` alone.
- **Lean:** `scaled_norm_finitePoleJet_le_uniform_in_order` proves that the finite low-height pole contribution vanishes at distant centres, uniformly in the derivative order. `tendsto_finitePoleJet_at_unique_nearest` recovers a residue at a fixed centre with a unique nearest pole.
- **Lean:** `tendsto_logDeriv_jets_at_rightmost_zero` recovers the exact multiplicity of a rightmost zero of an entire function. Global peeling and compactness produce a zero-free cofactor on a disk larger than the tangent disk; Cauchy's estimate removes its normalized jets. Finiteness of the zero set is unnecessary.
- **Lean:** `not_asymptoticAbscissaLaw_has_prime_moment_limit` proves that for an actual rightmost zeta zero `ρ`, `s₀=ρ+d`, `Re s₀>1`, the corrected moments `d^(k+1)/k! · Σ Λ(n)(log n)^k n^(-s₀) − (d/(s₀−1))^(k+1)` tend to `−mρ < 0`. The only premise is `¬AAL`; multiplicity, factorization, and the analytic remainder are discharged for the actual zeta function. Axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- **Remaining:** force comparable prime-side jets at quantitatively controlled high ordinates, or prove an unconditional arithmetic theorem conflicting with this moment limit. Qualitative recurrence (`∀k ∃t`) does not supply the required relation between `k` and `t`.
- No contradiction to `¬AAL` established. The finite-oscillation question remains undecided here.

## Arithmetic bound target

The corrected von Mangoldt moment has a negative integer limit. A contradiction must bound this same corrected quantity, including its pole subtraction and normalization.

| Candidate input | Exact issue / retained target |
|---|---|
| Positivity of `Λ` | Absolute values restore the real-axis pole radius `σ−1`, smaller than the detection radius `σ−β`. They do not bound the corrected moment at the required scale. |
| Selberg / integer-counting convolution | Multiplication by `ζ` cancels the selected zero's logarithmic-derivative pole. The exact logarithmic commutator retains the prime kernel (`LogarithmicCommutatorsExposeThePrimeKernel`). |
| Quantitative phase recurrence | `horizontal_jet_gain_lt_half` proves `η log((η+1−β₁)/(η+1−β)) < β−β₁ < 1/2`. `tendsto_nat_mul_log_shift_ratio` proves the gap is the sharp envelope. Both audit with standard axioms. This compares candidate bounds, not actual return times. |
| Proper prime powers | `tendsto_normalized_higher_prime_power_jets` proves decay when `d<σ−1/2`. `not_asymptoticAbscissaLaw_has_prime_only_jet_limit` retains the exact nonzero limit for the corrected prime-only current. Both audited: standard three axioms only. |
| Fixed-height mean square | A diagonal estimate alone leaves the signed off-diagonal arithmetic term uncontrolled. Typical-height bounds permit bounded-height exceptional signals. |
| Bohr prime inequality | `sum_norm_prime_coeff_le` needs uniform boundedness on a whole strip. The high-height `log t` bound does not supply it. Prime-phase alignment still requires quantitative height control. |
| Short-interval variance | Gallagher's dictionary converts the desired second-moment bound to a prime variance bound; it does not prove that variance bound. |
| Integer shifts in `s` | For `ΔF(s)=F(s)−F(s+1)`, the prime kernel of `Δ^k F` is `(1−1/n)^k`. This replaces exponential integer scales by polynomial scales. A centered cancellation estimate is still missing; the pole and off-line contributions must both be retained. |
| Multiplicative bilinear splitting | The phase `(ab)^(-iτ)=a^(-iτ)b^(-iτ)` separates exactly. Splitting the convolution supplies no new oscillatory interaction; cancellation in the arithmetic coefficients remains necessary. |
| Prime-pair upper sieve | `RHTower.Sieve.sum_card_primePair_le` bounds unsigned pair counts by a main term proportional to `K Y` with two logarithmic savings and an explicit remainder. It does not bound the signed, factorially normalized correlation. |
| Integrable FE-defect rigidity | `beurlingSystem_rigidity_of_small_critical_line_defect` requires a countable positive Beurling spectrum and a small integrable uncompleted defect. No such spectral representation has been constructed for the rationally deflated zeta function. |

### Unit-shift moment and diagonal

At `s₀=ρ+1`, the pole correction is `ρ^(-k-1)`. The unconditional bound
`4≤|Im ρ|` makes it vanish. Thus `¬AAL` forces the **raw** limit

`M_k = (1/k!) Σ_n Λ(n)(log n)^k n^(-ρ-1) → −mρ`.

The arithmetic coefficient diagonal has the opposite behavior. For
`a_k(n)=d^(k+1)Λ(n)(log n)^k n^(-σ)/k!` and `0≤d<R<σ−1/2`,

`Σ_n a_k(n)^2 ≤ d²(d/R)^(2k) Σ_n Λ(n)^2 n^(-2(σ−R)) → 0`.

The final series converges by `Λ(n)≤log n`; exponential domination bounds the
factorial moment. At `σ=Re ρ+1`, `d=1` is admissible. This isolates distinct-integer
correlations as the remaining contribution to `|M_k|²`.
`tendsto_normalizedMangoldtTermDiagonal_zero` formalizes this unconditional diagonal
bound. `not_asymptoticAbscissaLaw_has_raw_prime_moment_limit` and
`not_asymptoticAbscissaLaw_has_nonzero_moment_and_vanishing_diagonal` prove the raw
limit and its coexistence with diagonal decay. All three audit with the standard
three axioms. `not_asymptoticAbscissaLaw_has_positive_offDiagonal_limit` proves the
explicit off-diagonal limit `mρ²`, with the same axiom audit. None of these
statements supplies off-diagonal cancellation.

### Sparse arithmetic correlations

For every square-summable complex sequence `a` and injective integer map `i`,
`|Σ_n a(n) conj(a(i(n)))| ≤ Σ_n |a(n)|²`. Thus additive shifts and integer
dilations obey the same bound. For the actual normalized von Mangoldt terms,
`1<R<Re s−1/2` and `0≤r<R²` give

`Σ_(1≤h≤floor(r^k)) |Σ_n a_k(n) conj(a_k(n+h))| → 0`.

The proof bounds this sum by `C (r/R²)^k`, with the convergent constant
`C=Σ Λ(n)² n^(-2(Re s−R))`.
`tendsto_normalizedMangoldtShortShiftCorrelations_zero` passed its final source
and axiom audits. `not_asymptoticAbscissaLaw_has_positive_limit_after_short_shifts`
proves that subtracting both orientations of these shifts from the off-diagonal
sum preserves the limit `mρ²`. Its final source check passed; both dependency
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
This controls exponentially many shifts, not the full off-diagonal sum.

### Real-pole calibration

At `s=2`, the same raw moments tend to `+1` while their diagonal tends to zero.
Indeed `(s−1)ζ(s)` is zero-free on `closedBall(2,3/2)` by the unconditional
ordinate bound `|Im ρ|≥4`; its normalized jets vanish. The pole at `1` contributes
exactly `1` at every order.
`mangoldt_at_two_has_nonzero_moment_and_vanishing_diagonal` passed its final source
and axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`. Thus a bound
deduced solely from diagonal decay cannot distinguish the proposed negative
zero residue from an actual nonzero moment of the same arithmetic sequence.

The low-height jet argument only needs an attained rightmost zero. A bound that
forces these moments to vanish at every ordinate would discard the finite-layer
information and impose a stronger zero-exclusion statement. Any gap-based
contradiction must use the high-height zero-free region quantitatively.
