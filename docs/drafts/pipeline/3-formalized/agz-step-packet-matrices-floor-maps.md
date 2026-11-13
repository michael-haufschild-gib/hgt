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
  along divisibility of `R`, to the bottom of Weil's form on a window of length `log Q`, and by
  M21 by at most `C_Q²/(log R − E_Q − μ_R)` from `R` on.
- An index theorem for the floor correspondences.
- A positive trial vector with one sink (after the charge shift) on the windows of ratio two and
  four: with M25 it would count one bound state there without the zeros.

## Log
- 2026-11-11 — proved and formalized (M1–M5)
- 2026-11-12 — M6 (tower) and M7 (`R = 2`, ratio four) proved and formalized
- 2026-11-12 — M9–M24 proved and formalized
- 2026-11-12 — M25, M26, M27 proved and formalized
- 2026-11-12 — M28, M29 proved and formalized (B189 at ratio four: lowered models)
- 2026-11-13 — M30 proved and formalized (reweighted contacts: tower, second bound state at ratio three and four)
- 2026-11-13 — M31 proved and formalized (two-well and nodal criteria; RH as the Hodge index inequality on the positive cone)

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

## The signature of the neutral part (M12–M19)

- [x] M12 margin `1/5000` on every window of ratio at most `103/50`, at every block size
- [x] M13 the neutral part is invariant under refinement; on the dyadic window it is negative
- [x] M14 the indices of the neutral part and of the block matrix differ by at most one; the
  neutral part has exactly one negative square on short windows, and on all windows under RH
- [x] M15 the neutral part is Weil's form of the zeros minus the poles; its index is one plus
  the number of zeros right of the line; RH iff at most one negative square on smooth tests
- [x] M16 finite scale: RH iff the neutral part of every window with `R ≤ J` has exactly one
  negative square
- [x] M17 the pole adds one negative square: for every window there is a window `(1, 2M]` whose
  neutral part has one negative square more than the block matrix of the first
- [x] M18 index law at finite scale: block matrices `#{zeros right of the line}`, neutral part
  one more
- [x] M19 at every ratio the block matrices are nonnegative on thin step packets
- [x] M20 coercivity: `𝔚_Q ≥ (log R − E_Q) Σζ²` on the step packets of a refinement whose sums
  over the blocks above `R` vanish
- [x] M21 rate: a margin `μ` above `R` is a margin `μ − ε` on every refinement once
  `log R ≥ E_Q + C_Q²/ε + μ`
- [x] M22 index: at most `J` negative squares on every refinement once `log R ≥ E_Q`; at most
  `(Q − 1)⌈e^{E_Q}⌉` at every block size
- [x] M23 on a window `(R, R + J]` with `4J ≤ R` the block matrix is negative off the diagonal;
  its ground vector has one sign and is charged, at every block size
- [x] M24 gluing: two forms with one negative square each, coupled through minus the product of
  their charges, have one negative square together iff `αβ ≥ 1`, two iff `αβ < 1`
- [x] M25 a count of the bound states from the potential and the couplings: at most the sinks of
  a positive trial vector; with a charge dominated by the couplings, at most one more than the
  sinks of the shifted matrix; on a window, at most one more than the blocks with `V_j < −λJ`
- [x] M26 the potential of a window with `J ≤ R` in closed form; couplings `≥ 1/(2J)`; for
  `16J ≤ R` the potential is `≥ −½` and the count of M25 is one
- [x] M27 gluing of two adjacent windows: the union is two neutral parts coupled by the
  weights; it holds at most the bound states of the product model with potentials lowered by
  the excess of the couplings over the product of the charges
- [x] M28 at ratio four the product model does not count one bound state: for `H ≥ 64` and all
  charges below the couplings of `(2H, 4H]` and `(4H, 8H]` the lowered lower half has two
  negative squares
- [x] M29 the rank of the binding at ratio four: for every model coupling of rank `r` with
  `600(r + 1) ≤ H`, of any signs, and all weights, one of the two lowered halves has two
  negative squares
- [x] M30 reweighted contacts (criteria G3, G4 at every block size): the form with the contact
  of `k` weighted by `ω(k)` is a combination of Weil's forms of the cutoffs, so its block matrix
  and its neutral part form a tower; a weight of `2` in `[−4, 0]` (no primes, Liouville) gives
  two bound states on every window of ratio `≥ 3`; weights of `2`, `3` in `[−5/2, 19/40]` give
  two on every window of ratio `≥ 4`; the constant raised by `2/5` gives two at ratio four;
  Weil's form with weights of `2`, `3` both `≤ 7/12` or both `≥ 9/8` is negative on the halves
  of `(R, 4R]`
- [x] M31 the exact gluing law on the positive cone: a symmetric matrix with entries `≤ 0` off
  the diagonal has two negative squares iff two nonnegative vectors `x`, `y` without a common
  index have `N(x, x) < 0` and `N(x, y)² < N(x, x) N(y, y)`; with negative entries, iff an
  eigenvector with negative eigenvalue takes both signs. RH iff on every window with `R ≤ J`
  positive step packets without a common block satisfy `N(x, x) N(y, y) ≤ N(x, y)²`
  (`N(x, x) < 0`), iff every bound state of every such window has one sign

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
every family iff RH. On smooth tests `W_ζ − W_poles` is the archimedean-minus-prime energy of
the corpus (`markovEnergy`), and the criterion is its one-bound-state law
(`RHTower.riemannHypothesis_iff_not_exists_negDef_markovPlane`); the count of the squares and
the step-packet side (M12–M14, M16–M18) are what this card adds.

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
`poleConfig_W_ofReal`, `neutralForm`, `neutralForm_eq_re_sub`, `neutralForm_eq_markovEnergy`,
`neutralForm_stepPacket`,
`virtualDefect_poleConfig`, `exists_le_negIndex_sub_poleConfig_iff`, `exists_le_negIndex_neutralGram_iff`,
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

**M17.** For `x = (σ, t)`, `σ` on the blocks of `(R, R + J]`, put
`Φ(x) = u₁(σ) − c₁(σ)u₂ − (c₀(σ)/ℓ)u₃ + t(u₂ + u₃)` on the blocks of `(1, 2M]` (the vectors of
M16). `Φ` is linear: the refinement is linear in `σ`, and `c₁`, `c₀` are linear. By the Gram
identity of M16, `N(Φx)` is an explicit function of `x`, `L`, `M`, and for each `x` it tends
(first `M → ∞`, then `L → ∞`) to `m(σ) − 2ℓt²`, the form of `m ⊕ (−2ℓ)`. The Gram matrix `G`
of `N` on the frame `Φ(e_a)` is symmetric, so it is the polarization of `x ↦ N(Φx)`:
`G_{ab} = (q(e_a + e_b) − q(e_a) − q(e_b))/2`. Hence `G` converges entrywise to `m ⊕ (−2ℓ)`.
The negative index is lower semicontinuous for entrywise convergence to a Hermitian matrix,
`ind(m ⊕ (−2ℓ)) ≥ ind(m) + 1`, and a Gram matrix has at most the index of the form.

**M18.** Block matrices. Upper bound: the form of the block matrix on block values is the form
of the nested Gram matrix on the nested coefficients, and bounded packets have at most
`#{zeros right of the line}` negative squares. Attainment: the robust index of the comb counts
the zeros right of the line, and a robust negative direction of the comb survives the block
means as a negative step packet (both HodgeTheoryOfAFixedPart), a linear map into the block
values. Neutral part: `ind N ≤ ind m + 1` on one window (M14), and M17.

Lean: `…/ThePoleAddsOneNegativeSquareToTheBlockMatrixOfAWindow.lean` (`bilin`, `polar`,
`polar_bilin`, `tendsto_polar`, `hermNegIndex_gram_le`, `poleFrame`, `sum_poleFrame`,
`poleGram`, `bilin_poleGram_eq`, `poleLimit`, `tendsto_bilin_poleGram`, `tendsto_frameLimit`,
`exists_hermNegIndex_blockWindow_add_one_le`);
`…/TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine.lean`
(`hermNegIndex_blockWindow_le_rightZeros`, `exists_le_hermNegIndex_blockWindow`,
`exists_le_hermNegIndex_blockWindow_iff`, `exists_le_hermNegIndex_neutralWindow_iff`).

**M19.** At block size `B`, on the blocks of `(B, (N+1)B]`, a step function is thin of width
`c` if it vanishes off the blocks `nB + ρ`, `ρ < c`. Its packet, moved back by `log B`, is
supported in `⋃_{n ≤ N} (log n, log n + log(1 + c/B)]`: the block `nB + ρ` is
`(log(nB + ρ), log(nB + ρ + 1)]` and `(nB + c)/(nB) ≤ 1 + c/B`. Smoothing by a bump of radius
`r` and moving right by `r` gives a `C²` test supported in
`⋃ [log n, log n + log(1 + c/B) + 2r]`. Corpus (ArithmeticLorentzianGeometry): there are `N₀`
and `κ > 0` such that for `N ≥ N₀` Weil's form is nonnegative on every `C²` test supported
within `κ log(1 + 1/N)` to the right of the logarithms of the integers up to `N`. Weil's form
is invariant under translation and continuous under smoothing on bounded packets of finite jump
energy, so `𝔚_Q ≥ 0`, `Q ≥ N + 1`, on thin step packets with
`log(1 + c/B) < κ log(1 + 1/N)`. A window of smaller ratio `K + 1` is covered by the zero
extension to the ratio `max(N₀, K) + 1`; the form of a step packet does not depend on the
cutoff beyond the ratio of its window (both values are the limit of the forms of the smoothed
packets). So for every `K ≥ 1` there is `η > 0` with `𝔚_{K+1} ≥ 0` on the thin step packets of
`(B, (K+1)B]`, `log(1 + c/B) < η`; `K = 3` is `𝔚_4`.

Lean: `…/TheBlockMatricesOfEveryRatioAreNonnegativeOnThinStepPackets.lean` (`IsThinStep`,
`exists_abs_lt_of_mollify_ne_zero`, `thin_block_bounds`,
`exists_forall_packetForm_thin_stepPacket_nonneg`, `packetForm_stepPacket_eq_of_le`,
`exists_forall_packetForm_thin_stepPacket_nonneg_ratio`,
`exists_forall_sum_blockMatrix_thin_nonneg`).

**M20.** `E_Q = 3 + Q/4 + 2ψ(Q) + log 4π`, `C_Q = 12 + 2Q + 2ψ(Q)`. Window `(R, R + J]`,
`R + J ≤ QR`, refined by `m`: unit blocks of `(mR, mR + mJ]`. Let `ζ` on the fine blocks have
`Σ_{i<m} ζ_{mj+i} = 0` for every `j`. On the comb above `N = mRB` put `c_n = ζ(block of n)`,
blocks of `B` points. The coarse blocks have `mB = N/R` points, and the sum of `c` over a coarse
block is `B Σ_{i<m} ζ_{mj+i} = 0`. Corpus (HodgeTheoryOfAFixedPart): for divisors with vanishing
sums over blocks of `N/R` points, `d₂ = 0` and `D·D ≤ −(log(N/2π) − ρ) Σc_n²` with
`log(N/2π) − ρ ≥ log R − E_Q`. So `𝔚_comb(c) ≥ (log R − E_Q) B Σζ_i²`; divide by `B`; the comb
form per point of a block tends to `𝔚_Q` of the step packet (M2).

**M21.** With `τ` on the coarse blocks and `s_n = τ(coarse block of n)`: corpus,
`2|𝔚_comb(s, c)| ≤ C_Q (p Σs_n² + q Σc_n²)` for `pq = 1`, uniformly in the block size. So
`𝔚_comb(s + c) ≥ 𝔚_comb(s) − C_Q p Σs² + (log R − E_Q − C_Q q) Σc²`; divide by `B`, let
`B → ∞`: `𝔚_Q(τ' + ζ) ≥ 𝔚_Q(τ') − C_Q p Σ_i τ'_i² + (log R − E_Q − C_Q q) Σζ_i²`, `τ'_i = τ_{⌊i/m⌋}`.
With `τ'` the refinement `τ_{⌊i/m⌋}/√m` of a step function on the blocks above `R`:
`𝔚_Q(τ') = 𝔚_Q(τ)` and `Στ'² = Στ²` (M6). Every fine `σ` is `τ' + ζ` with
`τ_j = Σ_{i<m} σ_{mj+i}/√m`, and `Σσ² = Στ² + Σζ²`. Take `p = ε/C_Q`, `q = C_Q/ε`: if
`𝔚_Q(τ) ≥ μΣτ²` and `log R − E_Q − C_Q²/ε ≥ μ`, then `𝔚_Q(σ) ≥ (μ − ε)(Στ² + Σζ²)`. With M6:
the margins of the tower above `R` lie in `[μ_R − C_Q²/(log R − E_Q − μ_R), μ_R]`. For
`μ₀ > 0` and `log R ≥ E_Q + 2C_Q²/μ₀ + μ₀` the margin of every refinement is `≥ μ₀/2`.

**M22.** If `log R ≥ E_Q`, the block matrix of the refinement is nonnegative on the complex block
values with vanishing sums over the `J` coarse blocks (M20 for real and imaginary part): at most
`J` negative squares. Every window: refine `(R', R' + J']` by `R₀ = ⌈e^{E_Q}⌉` (the index does not
decrease), extend by zero to `R'·(Q − 1)R₀ ≥ R₀J'` fine blocks (a principal submatrix), and read
the fine blocks above `R'R₀` as the refinement by `R'` of the `(Q − 1)R₀` blocks above `R₀`.
For `Q = 4`: `ψ(4) = log 12`, `e^{E_4} = e⁴ · 144 · 4π ≤ 55 · 144 · 12.6 < 10⁵`, so `𝔚_4` has at
most `300000` negative squares at every block size.

Lean: `…/TheStepPacketMatricesOfARatioAreDecidedOnCoarseBlocks.lean` (`rowExcess`,
`IsCoarseNeutral`, `combForm_coarseNeutral_ge`, `combForm_coarse_add_ge`,
`packetForm_coarseNeutral_ge`, `packetForm_refineStep_add_ge`, `sum_sq_refine_add`,
`packetForm_refined_ge_of_margin`, `packetForm_refined_ge_half_of_margin`,
`hermNegIndex_blockWindow_refined_le`, `hermNegIndex_blockWindow_le_refined`,
`hermNegIndex_blockWindow_mono`, `hermNegIndex_blockWindow_le_uniform`,
`hermNegIndex_blockWindow_ratioFour_le`).

**M23.** `D(n)` the second difference of `n log n`, `d(n) = log(1 + 1/n)`. *`D(n) ≥ d(n)`:*
`D(n) − d(n) = n log((n+1)/n) − (n−1) log(n/(n−1))` for `n ≥ 2`, and
`log((n+1)/n) = log((1/n)·1 + ((n−1)/n)·(n/(n−1))) ≥ ((n−1)/n) log(n/(n−1))` by concavity;
`D(1) = 2 log 2 ≥ log 2`. *Entries:* for `R ≤ a < b < R + J`,
`m(a, b) = d(a) + d(b) − J(a, b) − C(a, b)`, `C ≥ 0`,
`J(a, b) = ½(D(a+b+1) + D(b−a)) ≥ ½ d(b−a) ≥ 1/(2(b−a+1)) ≥ 1/(2J)` and
`d(a) + d(b) ≤ 1/a + 1/b < 2/R ≤ 1/(2J)` when `4J ≤ R`. So `m(a, b) < 0`. *Ground vector:* for
a symmetric matrix that is negative off the diagonal, `|σ_j||σ_l| m_{jl} ≤ σ_jσ_l m_{jl}`
termwise, strictly at a pair of entries of opposite signs; so a minimiser among the vectors of
its length has one sign, and then `Σσ_j` and `Σσ_j d(R+j)` have that sign (`d > 0`).

**M24.** `A`, `B` real symmetric, `A ≥ 0` on `u·x = 0`, `B ≥ 0` on `v·y = 0`, `Aa = u`, `Bb = v`,
`α = u·a`, `β = v·b`. For `x₀ = cx − sa`: `A(x₀) = c²A(x) − 2cs(u·x) + s²α` (symmetry and
`Aa = u`), and `u·x₀ = c(u·x) − sα`. Glued form `G(x, y) = A(x) + B(y) − 2(u·x)(v·y)`.
*`αβ ≥ 1`, `β < 0`:* then `α < 0`. On the hyperplane `u·x = α t`, `t = v·y`: with
`x₀ = x − ta` and `y₀ = βy − tb` (both without charge),
`β²G = β²A(x₀) + B(y₀) + β(1 − αβ)t² ≥ 0`; so at most one negative square, and `G(a, 0) = α < 0`.
*`αβ < 1`, `α, β < 0`:* `G(sa, tb) = αs² − 2αβst + βt²` has the determinant `αβ(1 − αβ) > 0`
and `α < 0`: negative on a plane; and `G = A(x) + B(y) ≥ 0` where both charges vanish: exactly
two.

**M25.** `B` real symmetric with `B_ij ≤ 0` for `i ≠ j`, `v > 0`. Then
`Σ σ_iσ_j B_ij − Σ_i (σ_i²/v_i)(Bv)_i = ½ Σ_{i,j} (−B_ij) v_i v_j (σ_i/v_i − σ_j/v_j)² ≥ 0`
(the two orders of a pair add up to one square). So the form is `≥ 0` on the packets that vanish
at the sinks `{i : (Bv)_i < 0}`, and the negative squares are at most the sinks. *With a charge:*
if `B_ij + λ c_i c_j ≤ 0` off the diagonal, `B' = B + λ c ⊗ c` is of the same kind,
`B'v = Bv + λ (c·v) c`, and the forms of `B` and `B'` agree where `c·σ = 0`: at most one more
than the sinks of `B'`. *Windows:* `B = N` (neutral part), `v = c = 1`: `Nv = V`, `c·v = J`; the
hypothesis is `λ ≤ w_{jl}`. Lean:
`TheBoundStatesOfAWindowAreAtMostTheSinksOfAPositiveTrialVector` (`sum_div_mul_mulVec_le`,
`hermNegIndex_le_card_sinks`, `hermNegIndex_le_one_add_card_sinks`,
`hermNegIndex_neutralWindow_le_card_wells`,
`hermNegIndex_neutralWindow_le_one_add_card_deepWells`,
`hermNegIndex_neutralWindow_le_one_of_shallow`).

**M26.** `Δ(n) = (n+1) log(n+1) − n log n`, so `D(n) = Δ(n) − Δ(n−1)` for `n ≥ 1`, `Δ(0) = 0`,
`Σ_{d=0}^{k} D(d) = Δ(k)` and `Σ_{i<K} D(m+i+1) = Δ(m+K) − Δ(m)`. For `J ≤ R` and blocks
`a ≤ b` of the window, `b < 2a`, so `⌊b/k⌋ < a` for `k ≥ 2`: no contacts. Hence
`N(a,b) = δ_{ab} ϱ(a) − ½(D(a+b+1) + D(|b−a|))` and, with `ϱ(a) = Δ(a) − γ − log 2π`,

`V_j = Δ(R+j) − γ − log 2π − ½(Δ(2R+j+J) − Δ(2R+j)) − ½(Δ(j) + Δ(J−1−j))`

(the differences `|l − j|` run over `0..j` on one side and `1..J−1−j` on the other). Bounds:
`Δ(n) = log(n+1) + n log(1+1/n)` with `1 − 1/(n+1) ≤ n log(1+1/n) ≤ 1`. Couplings:
`w ≥ ½ D(|b−a|) ≥ ½·1/(|b−a|+1) ≥ 1/(2J)`. For `16J ≤ R`: `log(R+j+1) ≥ 4 log 2 + log J`,
`log(j+1), log(J−j) ≤ log J`, `Δ(2R+j+J) − Δ(2R+j) ≤ 1/32 + 1/33`, `γ < 2/3`, `log 2π < 2`, so
`V_j ≥ 4 log 2 − 1/17 − 2/3 − 2 − 1/64 − 1/66 − 1 + 1 > −½`, and `λJ = ½` with `λ = 1/(2J)`:
no sink, one bound state by M25. Lean:
`OnANarrowWindowThePotentialIsShallowAndTheCountOfBoundStatesIsOne` (`xLogXStep`,
`sum_range_succ_xLogXDiff`, `sum_range_xLogXDiff_add`, `blockPotential_eq_of_window`,
`inv_two_mul_le_blockWeight`, `blockPotential_add_half_nonneg_of_narrow`,
`hermNegIndex_neutralWindow_le_one_of_narrow_count`). Estimate, not proved: with the constant
trial vector the count should stop near `J ≈ R/4`, since in the middle
`V ≈ log(2R/J) − γ − log 2π`, against `λJ ≈ ½`. A trial vector with one sink on a window of
ratio two or four is not known.

**M27.** Forms `A`, `B`, couplings `K`, coupled form `G(x, y) = A(x) + B(y) − 2 Σ K_ij x_i y_j`.
For charges with `u_i v_j ≤ K_ij` put `F = K − u ⊗ v ≥ 0`. Then
`−2 Σ F_ij x_i y_j = Σ F_ij (x_i − y_j)² − Σ_i (F1)_i x_i² − Σ_j (Fᵀ1)_j y_j²`, so
`G(x, y) ≥ A'(x) + B'(y) − 2(u·x)(v·y)` with `A' = A − diag(F1)`, `B' = B − diag(Fᵀ1)`: the
product model (M24) of the forms with potentials lowered by the excess. A pointwise larger form
has at most as many negative squares. So `ind G ≤ ind glued(A', B', u, v)`; `≤ 1` under the
hypotheses of M24 for `A'`, `B'` with `αβ ≥ 1`; and with `u = v = 0`,
`ind G ≤ ind(A − diag(K1)) + ind(B − diag(Kᵀ1))`. For the windows `(R, R+J₁]`,
`(R+J₁, R+J₁+J₂]`: the neutral part of the union, reindexed by `Fin J₁ ⊕ Fin J₂`, is the
coupled form of the two neutral parts with `K_ij = w(R+i, R+J₁+j) > 0`. Lean:
`TwoCoupledWindowsHoldAtMostTheBoundStatesOfTheProductModelWithLoweredPotentials` (`coupled`,
`bilin_glued_le_coupled`, `hermNegIndex_coupled_le_glued`, `hermNegIndex_coupled_le_one`,
`hermNegIndex_coupled_le_add`, `neutralWindow_add_submatrix`,
`hermNegIndex_neutralWindow_add_le_glued`, `hermNegIndex_neutralWindow_add_le_add`).

**M28.** Halves `(2H, 4H]`, `(4H, 8H]`, `K_ij = w(2H+i, 4H+j) > 0`, `Q ≥ 2`, `H ≥ 64`.
(a) *A product of charges carries no contacts.* Let `K ≥ 0` have row sums `≤ ρ` and let each
`i` reserve a set `cont i` of columns, disjoint for different `i`. If `u_i v_j ≤ K_ij`, then for
every set `S` of rows `Σ_{i∈S} (K1 − u (v·1))_i ≥ Σ_{i∈S} Σ_{j∈cont i} K_ij − ρ`: with `P` the
sum of the positive parts of `v` and `p_i` its part on `cont i`, a positive `u_i` is `≤ ρ/P`
(sum `u_i v_j ≤ K_ij` over `v_j > 0`), so `u_i (v·1) ≤ Σ_{j∉cont i} K_ij + ρ p_i/P`, and
`Σ p_i ≤ P`. (b) The block `a` meets `2a`, `2a+1` with the weight `Λ(2)/2` each, so the
reserved couplings are `≥ log 2` per block; a row of `K` adds up to
`≤ ρ = ½ log(12H) + 1 + log 6`. (c) On the constant packets of the quarters `(2H, 3H]`,
`(3H, 4H]` the neutral part of `(2H, 4H]` is `−a₁H`, `−a₂H` with pairing `cH`:
`a₁ = c₀ − 5 log 5 + 9 log 2 ≈ 0.603`, `a₂ = c₀ − 7 log 7 + 7 log 2 + 6 log 3 ≈ 0.234`,
`c = (12 log 3 + 10 log 2 − 5 log 5 − 7 log 7)/2 ≈ −0.777`, `c₀ = γ + log 2π` (closed form of
the window values at multiples of `H`). Lowering by `H log 2 − ρ` on each quarter gives
diagonal values below `−1.02H`, `−0.65H`, whose product exceeds `c²H²`: the lowered lower half
is negative definite on a plane, so it has two negative squares, it is negative on a vector
without charge, and the product model has at least two negative squares. Lean:
`TheTwoHalvesOfAWindowOfRatioFourDoNotGlueThroughAProductOfCharges`
(`sum_contacts_sub_le_sum_excessLeft`, `two_le_hermNegIndex_of_two_vectors`,
`sum_neutralBlock_window`, `sum_neutralBlock_lower_quarter`, `sum_neutralBlock_upper_quarter`,
`sum_neutralBlock_cross_quarters`, `sum_range_blockWeight_le`, `log_two_div_two_le_blockWeight`,
`two_le_hermNegIndex_lowered_lower_half`, `exists_chargeless_negative_lowered_lower_half`,
`two_le_hermNegIndex_glued_lowered_ratio_four`).

**M29.** Same halves. For any model coupling `M` and weights `t_ij > 0`,
`2|K_ij − M_ij||x_i y_j| ≤ |K_ij − M_ij|(t_ij x_i² + y_j²/t_ij)`, so the coupled form is at least
the form coupled by `M` of `A − diag L`, `B − diag R`, `L_i = Σ_j |K − M|_ij t_ij`,
`R_j = Σ_i |K − M|_ij/t_ij`; a lowered model with one negative square would count one bound
state of the union (for `M = u ⊗ v ≤ K`, `t = 1` this is M27). **Claim:** if `M = Σ_{k<r} p_k ⊗ q_k`
and `600(r + 1) ≤ H`, then `A − diag L` or `B − diag R` has two negative squares, for all `t`.
Proof. Suppose both have at most one. (i) By M28(c) applied to `(2H, 4H]` and to `(4H, 8H]`
(quarters of size `2H`), with `X_q`, `Y_q` the sums of `L`, `R` over the quarter `q = 1, 2` of
the lower and of the upper half: `(a₁H + X₁)(a₂H + X₂) ≤ c²H²`,
`(2a₁H + Y₁)(2a₂H + Y₂) ≤ 4c²H²`. (ii) With `G_q = Σ |K − M|` over the lower quarter `q` times
the upper quarter `q`, Cauchy–Schwarz gives `G_q² ≤ X_q Y_q`. (iii) If `G₁², G₂² > 2e²`,
`e = 77H/200`, then `X_q + Y_q/2 > 2e`, `(a_q H + X_q)(a_q H + Y_q/2) ≥ (a_q H + e)²`, and the
product of the two criteria gives `(a₁H + e)(a₂H + e) ≤ c²H²`, false since
`0.9877 · 0.6189 > 0.7769²`. So `G_q ≤ (109/200)H` for one `q`. (iv) Between the lower quarter
`q` (blocks `a`) and the upper quarter `q` (blocks `b`, `a < b < 3a`, `b − a ≥ H`) the couplings
are the jets, `≤ 2/H`, plus `(log 2)/2` if `⌊b/2⌋ = a`. Summing columns over the two preimages
`2a'`, `2a'+1` turns `K` into `log 2 · 1 + (jets ≤ 4/H)` and `M` into a matrix `D` of rank `≤ r`.
(v) A matrix of rank `r` on `n` indices has `Σ_{ij} |D_ij − λδ_ij| ≥ λ(n − r)`: a set of rows
with `Σ_j |D_ij − λδ_ij| < λ` is diagonally dominant, hence independent, hence of size `≤ r`.
Applied on the `64` residue classes of the indices, where the jets add up to `≤ H/16 + 4`:
`log 2 · (H − 64r) ≤ G_q + H/16 + 4`. With (iii): `0.6931(H − 64r) ≤ 0.6075H + 4`, false for
`H ≥ 600(r + 1)`. ∎ So a coupling that carries the binding of the two halves at ratio four has
rank `≥ H/600 − 1`; the constant is not optimized. Lean:
`TheBindingOfTheTwoHalvesOfAWindowOfRatioFourHasRankProportionalToTheBlockSize`
(`loweringLeft`, `loweringRight`, `bilin_lowered_le_coupled`, `hermNegIndex_coupled_le_lowered`,
`hermNegIndex_neutralWindow_add_le_lowered`, `sq_sum_abs_le_lowering`,
`card_le_of_rank_of_diagonally_dominant`, `mul_card_sub_le_sum_abs_sub_diagonal`,
`mul_sub_le_sum_abs_on_residue_classes`, `mul_le_sq_of_hermNegIndex_lowered_le_one`,
`abs_blockWeight_pair_sub_le`, `log_two_mul_sub_le_quarter`, `lowerQuarterDepth`,
`upperQuarterDepth`, `quarterPairing`, `mul_le_sq_of_hermNegIndex_lowered_dyadic_le_one`,
`two_le_hermNegIndex_lowered_half_of_rank`, `two_le_hermNegIndex_lowered_model_of_rank`).

**M30.** For `ω : ℕ → ℝ` let `𝔚^ω_Q(g) = 𝔚_Q(g) + 2 Σ_{2≤k≤Q} (1 − ω(k)) (Λ(k)/√k) h_g(log k)`:
Weil's form with the contact of `k` weighted by `ω(k)` (`ω ≡ 1` true, `ω ≡ 0` no primes,
`ω(p^m) = (−1)^m` Liouville).
(a) `𝔚_{k−1}(g) − 𝔚_k(g) = 2 (Λ(k)/√k) h_g(log k)`. On a step packet, by M2 at the cutoffs
`k − 1` and `k`, this is `Σ σ_j σ_l Γ_k(R+j, R+l)` with `Γ_k(a, b) = Λ(k)/k` if
`⌊max(a,b)/k⌋ = min(a,b)` and `0` otherwise: the graph of the floor map of `k`. So `𝔚^ω_Q` on
step packets is the form of `M^ω = M_Q + Σ_k (1 − ω(k)) Γ_k`, with neutral part
`N^ω = N_Q + Σ_k (1 − ω(k)) Γ_k`; for `a < b`, `N^ω_{ab} = −jet(a, b) − Σ_k ω(k) Γ_k(a, b)`.
(b) Tower. `Γ_k = N_{k−1} − N_k`, and `N_Q`, `M_Q` are invariant under refinement at every
cutoff (M6, M9). So `Γ_k`, `N^ω`, `M^ω` are invariant under refinement.
(c) First blocks, `Q ≥ 3`. `N^ω_{11} = −D`, `D = γ + log 2π + 3 log 2 − 3 log 3`;
`N^ω_{22} + 2N^ω_{23} + N^ω_{33} = −2D` (the dyadic window `(2, 4]`; no floor map joins blocks
of ratio below two); `N^ω_{12} + N^ω_{13} = −(J + K_ω)` with
`J = jet(1,2) + jet(1,3) = 6 log 3 − 2 log 2 − (5/2) log 5` and
`K_ω = ω(2) log 2 + ω(3)(log 3)/3`: the floor map of `2` sends the blocks `2`, `3` to `1`, that
of `3` sends `3` to `1`, no other does. On `σ = (s, t, t)`:
`N^ω = −(D s² + 2(J + K_ω) s t + 2D t²)`, and by (b) the same on the packets with the values
`s/√R` on `(R, 2R]`, `t/√R` on `(2R, 4R]`. Two negative squares if `(J + K_ω)² < 2D²`.
Numbers: `D ∈ (1.195, 1.2)`, `J ∈ (1.1817, 1.1818)`, `log 2 + (log 3)/3 ∈ (1.0593, 1.0594)`.
True weights: `J + K = 2.241 > √2 D`; the form is positive on `(1, −1, −1)`:
`2(J + K) − 3D > 0`.
(d) Ratio three, `Q ≥ 2`. On `σ = (s, t)` on the blocks `1`, `2`:
`N^ω = −(D s² + 2(j₁₂ + ω(2)(log 2)/2) s t + D₂ t²)`,
`j₁₂ = (5 log 5 − 14 log 2 + 3 log 3)/2 ∈ (0.8194, 0.8195)`,
`D₂ = γ + log 2π + 9 log 2 − 5 log 5 > 0.6027`. For `ω(2) ∈ [−4, 0]`:
`|j₁₂ + ω(2)(log 2)/2| < 0.8195` and `0.8195² < 1.195 · 0.6027`. So `(R, 3R]` has two negative
squares, and so has every `(R, R + J]`, `J ≥ 2R` (principal submatrix). No other weight enters.
At the true weight `1.166² > D D₂`.
(e) Ratio four. `ω(2), ω(3) ∈ [−5/2, 19/40]`: `|J + K_ω| < 1.6855`, `1.6855² ≤ 2 · 1.195²`.
Constant raised by `δ` (density of every block lowered by `δ`): the refinement keeps `Σ σ²`,
so the form on the plane is `−((D + δ) s² + 2(J + K) s t + 2(D + δ) t²)`; for `δ ≥ 2/5`,
`2.2412² ≤ 2 · 1.595²`.
(f) Weil's form. Adding the charges `2(Σσ)(Σσ_j d_j) = 2 log 2 (s + 2t)(s + t)`:
`𝔚^ω = A s² + 2B s t + 2A t²`, `A = 2 log 2 − D ∈ (0.186, 0.1913)`, `B = 3 log 2 − J − K_ω`.
At `(s, t) = (−B, A)` the value is `A(2A² − B²)`, negative if `B² > 2A²`. Weights `≤ 7/12`:
`B > 0.2796`; weights `≥ 9/8`: `B < −0.2796`; and `2 · 0.1913² ≤ 0.2796²`. At the true weights
`B = −0.1617`, `B² < 2A²`. ∎ Lean:
`WeakenedOrTwistedContactsGiveASecondBoundStateOnWindowsOfRatioThreeAndFour` (`floorGraph`,
`blockMatrix_pred_sub`, `packetForm_pred_sub`, `contact_stepPacket_eq_sum_floorGraph`,
`sum_floorGraph_refine`, `reweightedNeutral`, `reweightedBlock`, `reweightedPacketForm`,
`reweightedPacketForm_eq`, `reweightedPacketForm_stepPacket`, `sum_reweightedNeutral_refine`,
`sum_reweightedBlock_refine`, `reweightedPacketForm_stepPacket_refine`,
`hermNegIndex_windowMatrix_mono`, `dyadicDepth`, `thirdDepth`, `halvesJet`, `halvesContact`,
`dyadicMargin`, `sum_reweightedNeutral_two_blocks`, `sum_reweightedNeutral_three_blocks`,
`bilin_reweightedNeutral_ratio_three`, `bilin_reweightedNeutral_halves`,
`two_le_hermNegIndex_reweighted_ratio_three`,
`two_le_hermNegIndex_reweighted_lowered_ratio_four`,
`two_le_hermNegIndex_reweighted_of_ratio_three`, `two_le_hermNegIndex_liouville`,
`two_le_hermNegIndex_weakened_contacts`, `two_le_hermNegIndex_raised_constant`,
`bilin_neutralWindow_halves_pos`, `reweightedPacketForm_halves`,
`exists_reweightedPacketForm_neg_of_sq_lt`, `exists_reweightedPacketForm_neg`).

**M31.** `G` real symmetric with `G_ij ≤ 0` for `i ≠ j`; `G(x, y) = Σ x_i y_j G_ij`.
(a) If `G(x, x) < 0` and `G(x, y)² < G(x, x) G(y, y)`, the binary form `G(sx + ty)` is negative
definite: two negative squares (no sign condition used).
(b) In an orthonormal eigenbasis `G(σ, σ) = Σ_i λ_i ⟨σ, ψ_i⟩²`, nonnegative on the vectors
orthogonal to the `ψ_i` with `λ_i < 0`; by the Pontryagin lemma the negative squares are at most
the negative eigenvalues. So two negative squares give orthonormal eigenvectors `u`, `v` with
eigenvalues `a, b < 0`.
(c) An eigenvector `ψ`, `Gψ = λψ`, `λ < 0`, with both signs: `p = ψ⁺`, `n = ψ⁻`, `ψ = p − n`,
`p_k n_k = 0`. Pairing the equation with `p` and `n`: `G(p, p) − c = λ|p|²`,
`c − G(n, n) = −λ|n|²`, `c = G(p, n) ≤ 0` (no common index). Then `G(p, p) < 0` and
`G(p, p) G(n, n) − c² = λc(|p|² + |n|²) + λ²|p|²|n|² > 0`.
(d) Otherwise `x = ±u ≥ 0`, `y = ±v ≥ 0` with `Σ x_k y_k = 0`, hence no common index;
`G(x, x) = a`, `G(y, y) = b`, `G(x, y) = b Σ x_k y_k = 0`, and `0 < ab`.
(e) If `G_ij < 0` for `i ≠ j`, case (d) does not occur: at `k₀` with `y_{k₀} > 0` one has
`x_{k₀} = 0`, so row `k₀` of `Gx = ax` reads `Σ_j G_{k₀j} x_j = 0`, while every term is `≤ 0` and
one is negative (`x ≠ 0`). With (c): two negative squares iff a bound state takes both signs.
(f) Windows. `N_ab < 0` off the diagonal (M9), at least one negative square for `R ≤ J` (M14),
RH iff exactly one (M16). For `x`, `y ≥ 0` without a common block `−N(x, y)` is the sum of the
jets and contacts between their blocks, weighted by `x_a y_b`, and
`N(x + y) = N(x) + N(y) + 2N(x, y)`. ∎ Lean:
`OneBoundStateIsTheHodgeIndexInequalityOnPositivePacketsWithoutCommonBlocks` (`bilin_swap`,
`bilin_comb`, `bilin_eigen`, `bilin_nonpos_of_disjoint`, `two_le_hermNegIndex_of_unbound_pair`,
`positiveWell`, `negativeWell`, `exists_unbound_wells_of_eigenvector`,
`exists_unbound_wells_of_two_eigenvectors`,
`exists_sign_changing_eigenvector_of_two_eigenvectors`, `dotProduct_mulVec_eq_sum_eigen`,
`hermNegIndex_le_card_neg_eigenvalues`, `exists_two_bound_states_of_two_le_hermNegIndex`,
`two_le_hermNegIndex_iff_exists_unbound_wells`, `hermNegIndex_le_one_iff_forall_wells_bound`,
`two_le_hermNegIndex_iff_exists_sign_changing_bound_state`, `neutralWindow_symm`,
`neutralWindow_neg_of_ne`, `bilin_neutralWindow_nonpos_of_disjoint`,
`two_le_hermNegIndex_neutralWindow_iff_exists_unbound_wells`,
`two_le_hermNegIndex_neutralWindow_iff_exists_sign_changing_bound_state`,
`hermNegIndex_neutralWindow_eq_one_iff_forall_wells_bound`,
`hermNegIndex_neutralWindow_eq_one_iff_forall_bound_state_one_sign`,
`riemannHypothesis_iff_forall_wells_bound`,
`riemannHypothesis_iff_forall_bound_state_one_sign`).

Lean: `…/TheGroundVectorOfTheBlockMatrixOfANarrowWindowHasOneSignAndIsCharged.lean`
(`blockDegree_le_xLogXDiff`, `blockMatrix_neg_of_narrow`, `sum_kernel_abs_lt`,
`kernel_minimizer_one_sign`, `blockMatrix_minimizer_one_sign`,
`charges_mul_pos_of_blockMatrix_minimizer`);
`…/TwoWindowsCoupledThroughTheirChargesHoldOneBoundStateIffTheirSusceptibilitiesMultiplyToAtLeastOne.lean`
(`chargeOf`, `bilin_sub_smul`, `glued`, `bilin_glued`, `glued_nonneg_of_charge_eq`,
`hermNegIndex_glued_eq_one`, `hermNegIndex_glued_eq_two`).

Open: positivity of the block matrix on windows of ratio above `103/50` on all step packets,
without RH; by M21 it is, with a margin, a statement about one matrix, at a scale `R` with
`log R ≥ E_Q + 2C_Q²/μ₀ + μ₀`. The constants `N₀`, `κ` of M19 are not explicit.
The ground vector of the block matrix on windows with `4J > R`: the matrix has entries of both
signs off the diagonal. The gluing of two actual windows: by M28, M29 no lowered model of rank
below `H/600` counts one bound state of a window of ratio four; open is an exact law in which
the contacts are kept (response matrices of full rank, or the refinement tower, where the
contacts of the floor map of `2` are `log 2` times the identity). By M30 the jets alone do not bind
the halves: without the contact of `2` there are two bound states from ratio three on, and on
the halves of `(R, 4R]` the form is nonnegative only for a common weight of `2`, `3` between
`7/12` and `9/8`. Open: the count one at the true weights on the windows of ratio three and
four at every block size, and the interval of admissible weights as the ratio grows (it
shrinks to the true weight if and only if RH holds and the weights are forced). By M31 the
exact law is the inequality `N(x, x) N(y, y) ≤ N(x, y)²` on positive packets without a common
block; open is to prove it beyond ratio `103/50` for one family of pairs that exhausts the cone
(the two parts of the second eigenvector: a bound on where its node lies).
