# The step-packet matrices are the block matrices of the floor maps; the first two have a margin

- **ID:** agz-block-matrix (task A143 of `docs/reports/review-1111/obstacles-summary.md`)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** obstacles-summary (review-1111) §2.14, question 5 and order of work, first item;
  §2.1 A143
- **Statement:** Weil's form `𝔚_Q` on the step packets of the unit blocks `(a, a + 1]`,
  `a = R, …, R + J − 1`, is the quadratic form of
  `m(a, b) = d(a) + d(b) + δ_{ab} ϱ(a) − J(a, b) − Σ_{k ≤ Q} (Λ(k)/k)[⌊b/k⌋ = a]` (`a ≤ b`);
  `𝔚_4 ≥ (1/20) Σ σ_j²` on the three blocks of `(1, 4]` and `≥ (1/100) Σ σ_j²` on the six blocks
  of `(2, 8]`, `𝔚_7 ≥ (1/100) Σ σ_j²` on the six blocks of `(1, 7]`; the comb form of a divisor constant on the three blocks of `(B, 4B]` is
  `≥ (1/40) B Σ σ_j²` for `B ≥ 300000`, on the six blocks of `(B, 7B]` it is
  `≥ (1/200) B Σ σ_j²` for `B ≥ 3000000`.

## Gates
- [x] M1 the matrix as mixed second differences of window values
- [x] M2 closed form of the entries: degrees, density, jets, floor maps
- [x] M3 margin of `𝔚_4` at `R = 1`
- [x] M4 margin of `𝔚_7` at `R = 1`
- [x] M5 the comb at explicit block sizes
- [x] M6 the tower: refinement of step packets by translation; margins decrease along
  divisibility of `R`
- [x] M7 `𝔚_4` at `R = 2` (six blocks of `(2, 8]`): margin `1/100`
- [ ] M8 finer blocks (`R ≥ 3` for ratio four, `R ≥ 2` for ratio seven): not done

## Paper proof

Notation of the card `agz-step-packet-limit-matrices`: `𝔚_Q`, flat packets, step packets,
`w(a, b) = 𝔚_Q(flat packet of (a, b])` for integers `1 ≤ a ≤ b`, `w(a, a) = 0`.

**M1.** `stepPacket R J σ = Σ_j τ_j · flat(R, R + j)` with the nested coefficients
`τ_j = σ_{j−1} − σ_j` (`σ_{−1} = σ_J = 0`), and by the polar identity
`𝔚_Q = ½ Σ_{j,l} τ_j τ_l E(j, l)`, `E(j, l) = w(R, R+j) + w(R, R+l) − w(R+j, R+l)` (symmetric in
the window ends). Summation by parts in `j` and in `l`:
`Σ τ_j τ_l E(j, l) = Σ_{j,l<J} σ_j σ_l (E(j+1, l+1) − E(j+1, l) − E(j, l+1) + E(j, l))`. The terms
`w(R, ·)` cancel in the mixed difference, so
`𝔚_Q(step) = Σ σ_j σ_l m(j, l)`, `m(j, l) = ½(w(j, l+1) + w(j+1, l) − w(j, l) − w(j+1, l+1))`,
and `m(j, j) = w(j, j+1)`.

**M2.** For `a ≤ b`: `w(a, b) = 2(b−a)(log b − log a) − [(b−a)c + (b+a) log 2 + 2a log a
− (b+a) log(b+a) + (b−a) log(b−a)] − 2 Σ_{k≤Q} Λ(k)(b/k − a)⁺`, `c = γ + log 2π` (closed form of
the flat pairing; at `a = b` the bracket vanishes). Mixed second difference `Δ = ` value at
`(a, b+1) + (a+1, b) − (a, b) − (a+1, b+1)`, halved:
- pole term: `(b−a)(log b − log a) = b log b − b log a − a log b + a log a`; only the two middle
  terms survive: `½Δ = (log(a+1) − log a) + (log(b+1) − log b) = d(a) + d(b)`;
- the terms linear in `a`, `b` and `2a log a` have `Δ = 0`;
- with `G(n) = n log n`: `Δ[(b+a) log(b+a)] = −(G(s+2) − 2G(s+1) + G(s))`, `s = a + b`, and
  `Δ[(b−a) log(b−a)] = −(G(d+1) − 2G(d) + G(d−1))`, `d = b − a`; so the jets give
  `−½(D(a+b+1) + D(b−a))`, `D(n) = G(n+1) − 2G(n) + G(n−1)`;
- contacts: with `t = b − ka ∈ ℤ`, `Δ[(b/k − a)⁺] = ((t+1)⁺ − t⁺ − (t+1−k)⁺ + (t−k)⁺)/k
  = [0 ≤ t < k]/k = [⌊b/k⌋ = a]/k`; so the contacts give `−Σ_k (Λ(k)/k)[⌊b/k⌋ = a]`.
Diagonal: `w(a, a+1) = 2 d(a) − c − (2a+1) log 2 − 2a log a + (2a+1) log(2a+1)`
`= 2d(a) + (G(a+1) − G(a) − c) − ½ D(2a+1)`, using `log(2a+2) = log 2 + log(a+1)`,
`log 2a = log 2 + log a`; the contacts vanish since `(a+1)/k ≤ a` for `k ≥ 2`, `a ≥ 1`, and
`D(0) = 0`. `G(a+1) − G(a) − 1 = ∫_a^{a+1} log x dx`.

**M3.** `R = 1`, `Q = 4`. In `ℓ_p = log p`, `c = γ + log 2 + log π`:
`m(1,1) = −c − ℓ₂ + 3ℓ₃`, `m(2,2) = −c − 11ℓ₂ + 2ℓ₃ + 5ℓ₅`, `m(3,3) = −c − 3ℓ₂ − 8ℓ₃ + 7ℓ₇`,
`m(1,2) = ½(13ℓ₂ − ℓ₃ − 5ℓ₅)`, `m(2,3) = ½(12ℓ₂ + 12ℓ₃ − 5ℓ₅ − 7ℓ₇)`,
`m(1,3) = ½(−5ℓ₂ − (35/3)ℓ₃ + 10ℓ₅)`. Values: diagonal `0.18760, 0.20470, 0.33794`, off the
diagonal `−0.06744, −0.08372, −0.09425`. Cholesky from the last block of `M − 0.06`: pivots
`0.277938, 0.1194823, 0.0187678`, multipliers `−0.339105, −0.30123; −0.802088`. Least
eigenvalue near `0.069`.

**M4.** `R = 1`, `Q = 7`. Diagonal `0.18760, 0.20470, 0.33794, 0.47754, 0.60740, 0.72552`.
Off the diagonal, rows `1..5`: `(−0.06744, −0.09425, 0.12318, −0.18392, 0.18878)`,
`(−0.08372, −0.05126, 0.00865, 0.01141)`, `(−0.24499, 0.15271, −0.12472)`,
`(−0.33777, 0.07015)`, `(−0.39839)`. Contacts: `(1,2)`: `ℓ₂/2`; `(1,3)`: `ℓ₂/2 + ℓ₃/3`;
`(1,4)`: `ℓ₃/3 + ℓ₂/4`; `(1,5)`: `ℓ₃/3 + ℓ₂/4 + ℓ₅/5`; `(1,6)`: `ℓ₂/4 + ℓ₅/5`; `(2,4)`, `(2,5)`,
`(3,6)`: `ℓ₂/2`; `(2,6)`: `ℓ₃/3`. Row one is not diagonally dominant. Cholesky from the last
block of `M − 0.02`: pivots `0.7055232, 0.3624395, 0.205293, 0.1447595, 0.081137, 0.0349279`;
the last pivot is `0.0752` for `M` and `−0.0079` for `M − 0.03`, so the least eigenvalue is near
`0.028`.

**Certificate (M3, M4).** Logarithms: `log((1+y)/(1−y)) ≥ 2y + 2y³/3` and
`log x ≤ 2(x−1)/(x+1) + (x−1)³/(6x(x+1))` at `9/8`, `128/125`, `50/49`, `121/120`, `169/168`
give `ℓ₃, ℓ₅, ℓ₇, ℓ₁₁, ℓ₁₃` to `3·10⁻⁷`; `log π < 1.1447302` from `π < 3.141593`;
`γ < 0.577216` (corpus). Each entry is within `10⁻⁴` of a decimal table `q` (diagonal: not
below). If `|e_{jl} − q_{jl}| ≤ ε` off the diagonal and `q_{jj} ≤ e_{jj}`, then
`Σ σ_j σ_l e_{jl} ≥ Σ σ_j σ_l q_{jl} − εJ Σ σ_j²`
(`2σ_jσ_l d ≥ −ε(σ_j² + σ_l²)` for `|d| ≤ ε`). The form of `q` minus `(μ + εJ)` is the sum of the
squares of the Cholesky factors of `q − μ₁` (`μ₁ = 0.06`, resp. `0.02`) plus a remainder with
diagonal near `μ₁ − μ − εJ ≈ 0.0094` and entries of size `10⁻⁵`, which is diagonally dominant.

**M7.** `R = 2`, `Q = 4`, blocks `2, …, 7`. The entries with both blocks `≤ 6` are those of M4
(the contacts of `5` and `7` do not reach them); `m(7,7) = 0.83277`, `m(2,7) = 0.02203`
(contact `ℓ₃/3`), `m(3,7) = −0.09721` (contact `ℓ₂/2`), `m(4,7) = 0.14506`, `m(5,7) = 0.01573`,
`m(6,7) = −0.44121`. Cholesky from the last block of `M − 0.02`: pivots
`0.8127736, 0.4660141, 0.2609586, 0.205268, 0.1045294, 0.0670439`; the last pivot is `0.123` for
`M` and negative for `M − 0.035`: the least eigenvalue is near `0.03`. Certificate as in M3, M4,
with `log 15 = ℓ₃ + ℓ₅`, `log 16 = 4ℓ₂`. Comb: `42·E(8, 4, B) ≤ 1/200` for `B ≥ 3000000`
(tangent at `6.4·10⁷ = 2¹²5⁶`; needs `B ≥ 2682021`).

**M5.** Explicit block error (card `step-packet-matrices-explicit-block-error`):
`|comb/B − 𝔚_Q| ≤ 6(J+1) E(R+J, Q, B) Σσ²`, `E = (2X + 16(1 + log 2XB) + 2ψ(Q))/B`. With
`log x ≤ x/M + log M − 1` at `M = 8·10⁶` (`= 2⁹5⁶`): `24·E(4, 4, B) ≤ 1/40` for `B ≥ 300000`
(needs `B ≥ 260601`); at `M = 5.6·10⁷` (`= 2⁹5⁶7`): `42·E(7, 7, B) ≤ 1/200` for `B ≥ 3000000`
(needs `B ≥ 2707873`).

**M6.** `𝔚_Q(g)` depends on `g` through `h_g` and `d₁(g) d₂(g)`; under `g ↦ g(· − τ)` the
autocorrelation is unchanged and `d₁, d₂` pick up `e^{−τ/2}, e^{τ/2}`: `𝔚_Q` is translation
invariant. The flat packet of `(a, b]` translated by `log m` is `m^{−1/2}` times the flat packet
of `(ma, mb]`, and `(m(R+j), m(R+j+1)]` is the union of the `m` unit blocks above `m(R+j)`. So
the step packet of `σ` above `R`, translated by `log m`, is the step packet above `mR` of
`σ'_{mj+i} = σ_j/√m` (`i < m`), and `Σ σ'² = Σ σ²`.

## Lean

Folder `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/`.

| Step | Module | Declarations |
|---|---|---|
| M2 (pure) | `TheBlockMatrixOfTheDegreesTheJetsAndTheFloorMaps` | `blockMatrix`, `blockDegree`, `blockDensity`, `blockJet`, `floorContact`, `windowClosed`, `mixed_window_aux`, `max_mixed`, `windowClosed_mixed`, `windowClosed_succ`, `sum_sum_mul_ge_of_close` |
| M1, M2 | `TheMatrixOfAStepPacketIsTheMixedDifferenceOfItsWindows` | `sum_sum_nestedCoeff_eq`, `windowValue`, `blockEntry`, `packetForm_stepPacket_eq_sum_blockEntry`, `windowValue_eq_windowClosed`, `blockEntry_eq_blockMatrix`, `packetForm_stepPacket_eq_sum_blockMatrix` |
| M3, M4, M7 (pure) | `TheFirstBlockMatricesOfRatioFourAndSevenHaveAMargin` | `log_three_mem`, `log_five_mem`, `log_seven_mem`, `log_eleven_mem`, `log_thirteen_mem`, `log_pi_lt`, `floorContact_four`, `floorContact_seven`, `table4`, `table7`, `table4fine`, `table4_form_ge`, `table7_form_ge`, `table4fine_form_ge`, `sum_blockMatrix_four_ge`, `sum_blockMatrix_seven_ge`, `sum_blockMatrix_four_fine_ge` |
| M3–M5, M7 | `WeilsFormHasAMarginOnTheFirstStepPacketsOfRatioFourAndSeven` | `packetForm_stepPacket_ratioFour_ge`, `packetForm_stepPacket_ratioSeven_ge`, `packetForm_stepPacket_ratioFour_fine_ge`, `windowError_ratioFour_le`, `windowError_ratioSeven_le`, `windowError_ratioFour_fine_le`, `combForm_ratioFour_ge`, `combForm_ratioSeven_ge`, `combForm_ratioFour_fine_ge` |

| M6 | `TheStepPacketsOfAWindowFormATowerUnderRefinement` | `packetForm_translate`, `flatPacket_translate`, `sum_flatPacket_blocks`, `refineStep`, `sum_refineStep_sq`, `stepPacket_translate`, `packetForm_stepPacket_refine`, `sum_blockMatrix_refine`, `margin_of_refined_margin` |

## Open

- Finer blocks: each `R` is a finite statement in dimension `(Q−1)R`; by M6 the margins decrease
  along divisibility of `R`, to the bottom of Weil's form on a window of length `log Q`.
- An index theorem for the floor correspondences.

## Log
- 2026-11-11 — proved and formalized (M1–M5)
- 2026-11-12 — M6 (tower) and M7 (`R = 2`, ratio four) proved and formalized
- 2026-11-12 — M9–M16 proved and formalized

## The neutral part (M9, M10)

- [x] M9 the block matrix is the product of the charges, a potential and a Dirichlet form
- [x] M10 the neutral part is Lorentzian on the certified step packets
- [x] M11 a ground vector of the neutral part has one sign and is charged

**M9.** `N(a, b) = m(a, b) − d(a) − d(b)`. Off the diagonal `N = −(J + C) < 0`: `J > 0`
because the second difference of `n log n` is positive (strict convexity), `C ≥ 0`. For a
symmetric matrix, `Σσ_jσ_l N_{jl} = Σ_j σ_j² Σ_l N_{jl} − ½ Σ N_{jl}(σ_j − σ_l)²`; and
`Σσ_jσ_l(d_j + d_l) = 2(Σσ_j)(Σσ_j d_j)`. With `v` without zero entries the same identity
for `N_{jl}v_jv_l` and `σ_j/v_j` is the ground state representation. Since
`σ_jσ_l ≤ |σ_j||σ_l|` and `N_{jl} < 0` off the diagonal, the form of `N` does not increase
under the modulus. If `v > 0` and `Nv ≥ cv`, then on packets with `Σσ_j = 0` or
`Σσ_j d_j = 0` the form of `m` is at least `cΣσ_j²`.

**M10.** Where a charge vanishes the form of `N` is the form of `m`, so the margins M5–M7
hold for `N` there. `N(1, 1) = ϱ(1) − J(1, 1)` with `ϱ(1) = 2 log 2 − γ − log 2π < 0`
(`γ > ½`, `π > 3`) and `J(1, 1) ≥ 0`; `N(2, 2) < 0` likewise.

Lean: `…/WeilsFormOnStepPacketsIsTheChargesAPotentialAndADirichletForm.lean`
(`xLogXDiff_pos`, `neutralBlock`, `neutralBlock_neg`, `blockWeight_pos`,
`sum_sum_mul_eq_rowSum_sub_pairs`, `sum_sum_mul_eq_doob`,
`sum_blockMatrix_eq_charges_potential_dirichlet`, `sum_neutralBlock_abs_le`,
`sum_blockMatrix_ge_of_supersolution`);
`…/TheNeutralPartOfTheFirstBlockMatricesIsLorentzian.lean` (`sum_neutralBlock_four_ge`,
`sum_neutralBlock_seven_ge`, `sum_neutralBlock_four_fine_ge`, `neutralBlock_one_one_neg`,
`neutralBlock_two_two_neg`).

**M11.** For `σ` with `σ_{j₀} > 0 > σ_{l₀}`: termwise `|σ_j||σ_l| N_{jl} ≤ σ_jσ_l N_{jl}`
(`N_{jl} < 0` off the diagonal, equality on it), and strictly at `(j₀, l₀)`. So `|σ|` has the
same length and a strictly lower form: a minimiser among vectors of its length has entries of
one sign. Then `c₀ = Σσ_j` and `c₁ = Σσ_j d(R + j)` have that sign (`d > 0`), `c₀c₁ > 0`, and
the form of `m` exceeds the form of `N` by `2c₀c₁`.

Lean: `…/TheGroundVectorOfTheNeutralPartHasOneSignAndIsCharged.lean` (`blockDegree_pos`,
`sum_neutralBlock_abs_lt`, `neutral_minimizer_one_sign`, `charges_mul_pos_of_neutral_minimizer`,
`sum_neutralBlock_lt_sum_blockMatrix_of_minimizer`).

A supersolution cannot certify a window on which the neutral part has a negative square.

## The signature of the neutral part (M12–M16)

- [x] M12 margin `1/5000` on every window of ratio at most `103/50`, at every block size
- [x] M13 the neutral part is invariant under refinement; on the dyadic window it is negative
- [x] M14 the indices of the neutral part and of the block matrix differ by at most one; the
  neutral part has exactly one negative square on short windows, and on all windows under RH
- [x] M15 the neutral part is Weil's form of the zeros minus the poles; its index is one plus
  the number of zeros right of the line; RH iff at most one negative square on smooth tests
- [x] M16 finite scale: RH iff the neutral part of every window with `R ≤ J` has exactly one
  negative square

**M12.** Weil's form is `≥ (1/5000)‖f‖²` on `C²` tests supported in an interval of length
`181/250` (corpus: the ground energy of the aperture `181/500` is `≥ 1/5000`). Smoothing a
bounded packet of finite jump energy by bumps of integral one converges in Weil's form and in
mass and enlarges the support by twice the radius, so the bound holds for bounded packets of
support length `< 181/250`. A step packet on the blocks of `(R, R + J]` with `50J ≤ 53R` has
support length `log((R+J)/R) ≤ log 2 + log(103/100) < 0.6932 + 0.03 < 181/250`, and
`181/250 < log 3`, so `Q = 2` carries every contact. Its mass is `Σσ_j²`.

**M13.** Translation by `log m` maps the step packet of `σ` above `R` to that of
`σ'_{mj+i} = σ_j/√m` above `mR`. `Σσ' = √m Σσ`; `Σσ'_i d(mR + i) = (Σσ_j d(R+j))/√m`, since
the degrees of the `m` blocks above `m(R+j)` telescope to `log(m(R+j+1)) − log(m(R+j)) =
d(R+j)`. The product of the charges is invariant and the block matrix is (M6), so the neutral
part is. For `R = 1`, `J = 1`, `σ_0 = 1` and `m = R`: `Σ_{j,l<R} N(R+j, R+l)/R = N(1, 1) < 0`.

**M14.** On complex packets with `Σc_j = 0` the real and imaginary parts have first charge
zero, so the forms of `N` and `m` agree; two forms that agree on a hyperplane have indices
differing by at most one. If `m ≥ 0` on the window, `N` has at most one negative square. If
`R ≤ J`, the packet equal to one on the first `R` blocks is a negative vector (M13). `m ≥ 0`
holds on short windows (M12) and, under RH, on every window.

**M15.** `W_poles(f, g) = h_f(i/2) conj h_g(−i/2) + h_f(−i/2) conj h_g(i/2)` for the
configuration `{0, 1}` (`γ_0 = i/2`, `γ_1 = −i/2`); on a real packet it is
`2 ∫f e^{−u/2} · ∫f e^{u/2}`. So the form without the product of the charges is
`W_ζ − W_poles` on smooth packets, and the neutral block matrix on step packets (charges of a
step packet: `Σσ_j d(R+j)` and `Σσ_j`). Virtual index law: the largest number of negative
squares of `W_A − W_B` is the number of points right of the line with different
multiplicities plus the points on the line where `B` exceeds `A`. For `A` the zeros and
`B = {0, 1}`: the zeros right of the line and the point `1` (`0 < Re ρ < 1` for a zero; `0`
is left of the line). So the index is `1 + #{zeros right of the line}`, and it is `≤ 1` on
every family iff RH.

Lean: `…/TheBlockMatricesOfShortWindowsArePositiveAtEveryBlockSize.lean`
(`groundEnergy_mul_nested_mass_le_packetForm_of_log_lt`, `log_window_lt`,
`packetForm_stepPacket_ge_of_short`, `sum_blockMatrix_ge_of_short`,
`sum_neutralBlock_ge_of_short`);
`…/TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize.lean`
(`sum_refineStep`, `sum_refineStep_mul_blockDegree`, `sum_neutralBlock_refine`,
`sum_neutralBlock_dyadic`, `neutralWindow`, `blockWindow`,
`hermNegIndex_neutralWindow_le_blockWindow_add_one`, `one_le_hermNegIndex_neutralWindow`,
`hermNegIndex_neutralWindow_eq_one`, `hermNegIndex_neutralWindow_eq_one_of_riemannHypothesis`);
`…/TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles.lean` (`poleConfig`, `poleConfig_W`,
`poleConfig_W_ofReal`, `neutralForm`, `neutralForm_eq_re_sub`, `neutralForm_stepPacket`,
`virtualDefect_zeta_poleConfig`, `exists_le_negIndex_neutralGram_iff`,
`riemannHypothesis_iff_forall_negIndex_neutralGram_le_one`).

**M16.** Let `σ` be a step packet on the blocks of `(R, R + J]` with `m(σ) = N(σ) + 2c₀c₁ < 0`,
`c₁ = Σσ_j`, `c₀ = Σσ_j d(R+j)` (exists if RH fails). Put `ℓ = d(1)`, `n₁ = N(1, 1)`.

(a) *A block and a far window.* For a block `a ≥ 1` and `1 ≤ c ≤ d`:
`(1/M) Σ_{Mc ≤ l < Md} N(a, l) → −(d − c) d(a)`. For `a < l`, `N(a, l) = −J(a, l) − C(a, l)`.
Jets: the second difference of `n log n` is `≤ 2/n` (`log(1 + 1/n) ≤ 1/n`,
`log(1 − 1/n) ≤ −1/n`), so `J(a, l) ≤ 2/(l − a)` and the sum is `≤ 2M(d−c)/(Mc − a)`.
Contacts: `[⌊l/k⌋ = a]/k = φ_k(l+1) − φ_k(l)`, `φ_k(y) = (y/k − a)⁺ − (y/k − a − 1)⁺`, so the
sum telescopes to `G(Md) − G(Mc)`, `G(y) = S_a(y) − S_{a+1}(y)`,
`S_x(y) = Σ_k Λ(k)(y/k − x)⁺ = y L(y/x) − x ψ(y/x)`, `L(t) = Σ_{k ≤ t} Λ(k)/k`. With
`L(t) − log t → −γ` and `ψ(t)/t → 1`: `G(y)/y → log((a+1)/a)`.

(b) *Three vectors* on the blocks of `(1, 2M]`: `u₁` the refinement of `σ` by `L` (blocks above
`LR`), `u₂ = √L/M` on `M ≤ b < 2M`, `u₃ = 1/√L` on the block one. Exactly: `N(u₁,u₁) = N(σ)`
(M13), `N(u₂,u₂) = L n₁/M` (M13), `N(u₃,u₃) = n₁/L`. By (a), as `M → ∞`:
`N(u₁,u₂) → −√L Σ_i σ'_i d(LR + i) = −c₀` and `N(u₂,u₃) → −ℓ`; as `L → ∞`:
`N(u₁,u₃) = (1/L) Σ_j σ_j Σ_{L(R+j) ≤ l < L(R+j+1)} N(1, l) → −ℓ c₁`. The cutoff of the contacts
does not matter beyond the ratio of the blocks.

(c) `w₂ = u₂ + u₃`, `w₁ = u₁ − c₁u₂ − (c₀/ℓ)u₃`. In the limit `N(w₂,w₂) = −2ℓ`,
`N(w₁,w₂) = −c₀ − ℓc₁ + ℓc₁ + c₀ = 0`,
`N(w₁,w₁) = N(σ) + 2c₁c₀ + 2c₀c₁ − 2c₀c₁ = m(σ) < 0`. So for `L` and then `M` large the form is
negative definite on the plane of `w₁, w₂`: two negative squares on `(1, 2M]`. With M14 this
is the equivalence.

Lean: `…/TheNeutralPartOfABlockAndAFarWindowIsMinusTheProductOfTheirCharges.lean`
(`xLogXDiff_le`, `sum_Ico_blockJet_le`, `contactSum_eq`, `sum_Ico_floorContact`,
`tendsto_contactGap_div`, `tendsto_sum_Ico_neutralBlock_div`, `neutralBlock_eq_of_le`);
`…/TheRiemannHypothesisIsOneNegativeSquareOfTheNeutralPartOfEveryWindow.lean`
(`two_le_hermNegIndex_of_plane`, `tendsto_liftFar`, `tendsto_liftFirst`, `tendsto_farFirst`,
`exists_two_le_hermNegIndex_neutralWindow`,
`riemannHypothesis_iff_forall_hermNegIndex_neutralWindow_eq_one`).

Open: positivity of the block matrix on windows of ratio above `103/50` without RH.
