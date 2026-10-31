# SuccessorShellArithmetic (SSh)

Namespace `GaloisForLFunctions.SuccessorShellArithmetic`; umbrella `SuccessorShellArithmetic.lean`; 39 modules
(6 root, `TopBand/` 11, `Conductor/` 22). All results unconditional; RH appears only inside equivalences.

## 1. Motivation

The complete atomic Weil form `W_{N,c}` (atoms at `log n`, `n ≤ N`, width `w = c/N`) is a positivity family
built on the integers at square-root precision: its nonnegativity when `c⁴/log N → ∞` is RH
(`riemannHypothesis_iff_completeWeilEnergy_nonneg_of_growthTwo`). At fixed overlap it is solved: conductor
modes have nonnegative completed energies because the successor shells `n = km + h` repay the `−log c` of
the reference energy. The complete matrix is now positive uniformly for
`1≤c≤(log log N)^α`, every `0<α<1/16`, with logarithmic defect reserve.
The common-horizon proof still uses the preliminary cutoff from `D≤Cc¹⁶S`.
SSh studies the shell block itself: where it lives,
what its repayment is made of, what separate payment costs, and what joint signed payment with the pole
achieves.

## 2. Objects

Profile `φ` (`C²`, support `[0,1]`), `M = ∫φ²`, `q = (∫φ)²/M`, `G = ∫(atom)² = wM`, atom autocorrelation `β`.

| Object | Lean | Meaning |
|---|---|---|
| Shell lag / form | `shellLag`, `shellForm` | pairs `(m, n = km + h)`, `h ≠ 0`, weight `Λ(k)k^{−1/2}β(log k − log(n/m))` |
| Shift range | `shellRange`, `shellShifts` | `H = ⌊N(e^w − 1)⌋`; shifts `0 < |h| ≤ H` |
| Non-ratio form | `nonRatioForm` | `NR = Σ_h Sh_h` (ratio pairs `h = 0` excluded) |
| Pole vector, prime defect | `poleVector`, `poleDefect` | `b_n = n^{−1/2}`; `D = Σ Λ(t)(x_{mt} − x_m/√t)²` |
| Continuum completion | `continuumShellSum`, `continuumShellEnergy`, `continuumConductorEnergy` | shift sum replaced by `∫_0^c` |
| Lattice gain | `latticeGain` | actual minus continuum energy |
| Top band | `topBand` | `{n ≤ N : N e^w < 2n}`: partners never bases |
| Pole row | `shellPoleRow` | `R(n) = Σ_ℓ b_ℓ Λ_N(ℓ)β(log ℓ − log n)` |
| Top witness | `topWitness`, `topWitnessVector` | `b + η b 1_T` |
| Joint coefficients | `jointWitnessCoefficient`, `jointTopCoefficient`, `shellTopCoefficient` | linear coefficient of `2·Pole − NR` along a top-band perturbation |
| Weighted base row | `horizonDivisorCoefficient`, `shellCoefficientRow` | `Σ_{d|ℓ} Λ(d)a(ℓ/d)` with arbitrary bounded base `a` |
| Partner kernel | `shellPartnerKernel`, `shellWindowLower`, `shellWindowUpper` | row kernel of one base over its window |
| Divisor jet | `ramanujanLogDivisorJet`, `centeredRamanujanJet`, `ramanujanJetConductorWeight` | `J_m(n) = Σ_{d|(m,n)} μ(m/d)d log d`; `(J_m − Λ(m))/√φ(m)` |
| Power deformation | `ramanujanPowerDivisor` | `Σ_{d|(m,n)} μ(m/d)d^s` (value `c_m(n)` at 1, derivative `J_m(n)`) |
| Divisor-jet energy | `divisorJetEnergy`, `divisorJetGenerator` | `Σ_{k|m|M} Λ(m/k)φ(k)(f(m) − f(k))²` and its graph generator |
| Divisor packets | `divisorRamanujanPacket`, `divisorJetPacket` | `F = Σ f(m)c_m`, `JF = Σ f(m)J_m` |
| Source weights | `ramanujanAutocorrelationWeight`, `ramanujanProfileWeight`, `finiteSourceSmoothing` | `φ(k)^{−1}Σ a_i a_j c_k(|i−j|)` (profiled: × `autocorr φ(θ_j − θ_i)`) |
| Weighted energy | `weightedDivisorJetEnergy` | divisor-jet energy with weight `b(k)` on the lower conductor |
| Harmonic Gram | `Σ_(n≤N)u_m(n)u_l(n)/n`, `u_m=c_m/√φ(m)` | finite part `γδ_ml−I(m,l)/√(φ(m)φ(l))`, with torsion intersection `I` |
| Affine correlation | `Σ_(n<M)c_m(n)c_l(kn+h)` | `M c_l(h)` exactly when `m=l/gcd(l,k)`, zero otherwise |
| Prime finite part | `⟨v_m,N,P_N v_l,N⟩−δ_ml log N`, `v_m,N=u_m/√(n log N)` | `−I(m,l)/√(φ(m)φ(l))−δ_ml(log m+τ(m))` |
| Prime head and boundary | `primeConductorHeadPairing`, `primeConductorBoundaryFinitePart` | centered head limit `+I/√(φ(m)φ(l))−δ_ml(log m+τ(m))`; complementary boundary `−2I/√(φ(m)φ(l))` |
| Power head | `primePowerHeadCutoff θ N` | cutoff `⌊N^θ⌋`; leading coefficient `θ(2−θ)δ_ml log N`; mixed torsion coefficient `1−2θ` |
| Centered period head | `centeredPrimeConductorHead` | every cutoff has quadratic norm at most `6log Q+log4+4` on conductors through `Q` |
| Undilated prime packet | `2Σ_(k≤N)Λ(k)G(floor(N/k))/(k log N)` | finite part `−2T`, with error `C(1+log Q)²/log N` times coefficient mass |
| Twin shell | `twinShellForm` | shell weighted by `ω(k)(1 − ω(km)ω(km + h))` |

External: `nonRatioForm`, `atomDilate` (SSHA); `poleVector`, `poleDefect`, `completeWeilMatrix`,
`completedConductorEnergy`, `completeWeilAdjunctionEnergy` (RAPT); `ramanujanLogDivisorJet` (CACT);
`ramanujanLagCoefficient` (BVI); `tameDifferent` (AIT); `bumpCorr` (RHTower).

## 3. Language

- **Shift** `h`, **dilation** `k`, **base** `m` of a shell; **ratio block** = `h = 0`.
- **Repayment**: the shell symbol cancels the `−log c` of the reference energy on conductor modes.
- **Separate payment**: `NR ≤ G(εD + CS)`. **Joint payment**: shells with pole (and archimedean shells), signs kept.
- **Reserve exponents** `(θ, κ)`: `W ≥ δD − CS` with `δ ≍ c^{−θ}`, `C ≍ c^κ`; preliminary confinement exponent `θ + κ = 16`.
- **Adjunction value** `λ_d = log d + tameDifferent d`; **reduced lag modulus** `m/gcd(m, n)`.
- **Successor sign** `ω(ℓ)ω(ℓ + h)`; **disagreement** = −1.

## 4. Mechanisms

**A. Shell geometry**
1. A non-ratio pair of nonzero weight has `|n − km| ≤ min(n, km)(e^w − 1)`: unique bounded shift. `NR` is a
   finite sum of `2⌊c⌋` shells (large `N`), and shift `h` needs partner `n ≥ |h|N/(c e^{c/N})` (top band).
2. Continuum vs lattice: `∫_0^c F_c = c(∫φ)²/2` is exactly the pole charge; the lattice omits the cell
   `0 < h < 1`, which carries `M log c`. The repayment is the unit gap of `ℤ`.
3. Base collapse: on vectors equal to the pole vector on every base, shells reduce to pole rows; below overlap
   `N log 2` they are prime-free (`Λ_N(ℓ) = log ℓ`).

**B. Floors and witnesses**
4. Top band fits in a `log 2` window ⇒ Cauchy–Schwarz gives Gram ≥ `(|T|∫g)²/log 2`; shells read `≍ cq log N`
   per unit perturbation, defect costs `log N`. Quadratic in `η` ⇒ `C ≥ A⁺²/(2ε)`.
5. Pole rows are Laplace moments: `∫ e^{u/2}β = a₋a₊` (autocorrelation Laplace transform at ½) matches the pole
   moments, so shells and pole cancel on the witness up to first-order cell (Euler–Maclaurin) errors.

**C. Top-band calculus**
6. Product regrouping keeps arbitrary base coefficients; Abel summation on the partner variable with
   mean-zero periodic `ψ` before bounding divisor mass by `B log ℓ`.
7. Exact period means: mean of `c_m` is `[m = 1]`; mean of `J_m` is `Λ(m)`, which cancels the harmonic pole
   moment `−Λ(m)/√φ(m)` of a Ramanujan base.
8. Bilinearity of all coefficients ⇒ two-mode packets reduce to diagonal + both mixed orientations.

**D. Divisor-jet algebra**
9. `J_m = log m·c_m + Σ_{d|m} Λ(d)c_{m/d}` (Möbius / `Λ * ζ = log`), complete-period orthogonality of `c_m`.
10. Jordan-totient quotient `R_m(n,s)R_q(0,s) = μ(q)R_m(0,s)`, `q = m/gcd`; differentiate at `s = 1`.
11. Complementary-lag reciprocity `φ(k)c_d(M/k) = φ(d)c_k(M/d)` (equal reduced moduli) ⇒ reciprocal Ramanujan
    transform squares to `M` ⇒ eigenbasis of the divisor graph.
12. Signed source ⇒ Ramanujan lag Gram = `Σ_{primitive z}|Σ a_i z^i|² ≥ 0`; shifted orthogonality keeps the
    smoothed Gram diagonal; integrating over a profile translate keeps positivity.
13. Reciprocal inversion and the harmonic limit `Σ c_m(n)/n→−Λ(m)` identify the sharp Gram finite part
    with divisor-edge energy and torsion intersection. The two-sided large sieve and Abel summation
    give quadratic remainder `Q(Q−1)/(N+1)` times coefficient mass.
14. Affine Fourier resonance requires `z w^k=1`; the exact order of `w^k` is `l/gcd(l,k)`.
    This selects every mixed entry of the complete-period affine packet form.
15. The full prime-row residual vanishes in norm. Pairing it with a conductor mode and retaining the
    harmonic Gram finite part gives the exact prime finite part, including diagonal `−2log m`.
16. Period averaging of the completed upward correction gives the positive torsion head.
    Fixed-dilation harmonic averaging preserves it; subtracting from the full prime form leaves `−2I`.
    A summable correction majorant preserves the same centered limit at every exhausting cutoff.

**E. Gauge**
17. For completely multiplicative sign `ω`: `ω(k) − ω(m)ω(n) = ω(k)(1 − ω(km)ω(n))`, zero on ratio pairs.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| `NR = Σ_{0<|h|≤H} Sh_h`; exactly `2⌊c⌋` shells eventually; top-band support | `nonRatioForm_eq_sum_shellForm`, `eventually_shellRange_eq_floor`, `shellForm_eq_zero_of_vanish_on_top_band` | proved |
| Continuum shells = pole charge; continuum energy `log(1/(2πc)) + β/M → −∞`; gain `log(2πc) − β/M + o(1)` | `continuumShellSum_eq`, `tendsto_continuumShellEnergy_atBot`, `tendsto_latticeGain_sub_log` | proved |
| Every conductor: gain `log(2πc) − β/M − log m − τ(m) + γ + o(1)` | `tendsto_conductorLatticeGain_sub_log`, `conductorLatticeGain_ge` | proved |
| Fixed conductor packets positive along `c = (log N)^α`, `α < 1/19`; non-effective growing span | `eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth`, `exists_growing_packet_pos_of_lt_one_nineteenth` | proved |
| Separate payment floor `C ≥ A⁺²/(2ε)`, `A = cq/(4log 2) − ½`; order `c⁹` at reserve fraction `a c⁻⁷` | `le_of_nonRatioForm_payment`, `le_of_nonRatioForm_payment_at_reserve` | proved |
| Twin defect = Σ successor-disagreement shells; agreeing shifts invisible | `twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm`, `twinShellForm_eq_zero_of_agree` | proved |
| Joint witness coefficient `≤ K G(c + 1 + log N)`, `1 ≤ c ≤ N/4` (separate parts `≍ Gcq log N`) | `exists_abs_jointWitnessCoefficient_le_uniform_overlap` | proved |
| Nonpolar periodic perturbations: `≤ K BqU G(1 + log N)`; Ramanujan witness `K mφ(m)G(1 + log N)` | `exists_abs_jointTopCoefficient_le_uniform_overlap`, `exists_abs_ramanujan_jointTopCoefficient_le` | proved |
| Polar channel `≤ K m(√φ(m) + V_m)G(1 + log N)`; two-mode packet minus polar entry likewise | `exists_abs_ramanujan_polar_jointTopCoefficient_le`, `exists_abs_ramanujan_packet_sub_polar_le` | proved |
| Jet spectrum, envelope (attained at `m|n`), variance `≤ 2log²m`; full rows `O(mG/n)` | `ramanujanLogDivisorJet_eq_conductor_sum`, `abs_ramanujanLogDivisorJet_sub_mean_of_dvd`, `periodMean_centeredRamanujanJet_sq_le`, `abs_fullRamanujanShellRow_le` | proved |
| Jet = Ramanujan coefficient × adjunction gap `λ_m − λ_{m/gcd(m,n)}` | `ramanujanLogDivisorJet_eq_adjunction_gap` | proved |
| Divisor-jet energy: square completion, kernel = constants, ground packet = comb `f(1)M[M|n]` | `divisorJetEnergy_eq_period_pairing`, `divisorJetEnergy_eq_zero_iff`, `divisorRamanujanPacket_eq_comb_of_energy_zero` | proved |
| Exact adjunction spectrum `E = M⁻¹Σ_{d|M} φ(d)λ_d F(M/d)² = M⁻¹Σ_{n<M} λ_{M/gcd(M,n)}F(n)²` | `divisorJetEnergy_eq_adjunction_spectrum`, `divisorJetEnergy_eq_period_symbol` | proved |
| Smoothed packet–jet pairing has positive edge completion; adjunction lag kernel `c_m(h)(tameDiff m − λ_{m/gcd})` PSD (finite source, profiled, log mesh) | `weightedDivisorJetEnergy_eq_source_pairing`, `sum_adjunction_lag_charge_nonneg`, `logarithmic_profile_adjunction_charge_nonneg` | proved |
| Sharp harmonic finite part `(γ−log M)mass+E_M(f)` for divisor packets; exact mixed entries | `tendsto_divisorPacket_sq_harmonic_finitePart`, `tendsto_ramanujan_mul_harmonic_of_ne` | proved |
| Harmonic finite part = Euler scalar minus torsion intersection; absolute norm `≤ |γ|+4log Q+log4+4` | `tendsto_ramanujanPacket_harmonic_torsion`, `abs_harmonicGram_finitePart_le_log` | proved |
| Uniform quadratic tail `Q(Q−1)/(N+1)` times mass; logarithmic finite-horizon Gram budget | `abs_harmonicGram_quadratic_torsion_remainder`, `abs_harmonicGram_sub_log_mass_le` | proved |
| Every-horizon Gram remainder bounded by `min{Q(Q−1)/(N+1),6log Q+log4+5}` times mass | `abs_harmonicGram_torsion_remainder_le_log`, `abs_harmonicGram_torsion_remainder_le_min` | proved |
| Affine shell correlation selects `m=l/gcd(l,k)`; exact finite packet expansion | `sum_range_ramanujanLagCoefficient_mul_affine`, `sum_range_ramanujanPacket_mul_affine` | proved |
| Full prime finite part `−I/√(φ(m)φ(l))−δ_ml(log m+τ(m))`; exact packet polarization | `tendsto_primeConductorPairing_finitePart`, `tendsto_primeConductorPacket_finitePart` | proved |
| Exact prime head at the full horizon; complementary boundary limit `−2I/√(φ(m)φ(l))` | `primeConductorHeadPairing_horizon`, `tendsto_primeConductorBoundaryFinitePart` | proved |
| Prime logarithmic moment `Σ_(n≤N)Λ(n)log(n)/n=(log N)²/2+o(log N)` | `tendsto_primeHeadLogMoment_remainder` | proved |
| Every exhausting head retains the centered torsion correction `I/√(φ(m)φ(l))−δ_ml(log m+τ(m))` | `tendsto_primeConductorGrowingHead_correction` | proved |
| Power-head finite part `(1−2θ)I/√(φ(m)φ(l))−δ_ml[log m+τ(m)+2(1−θ)γ]`; square-root head diagonal | `tendsto_primeConductorPowerHead_finitePart`, `tendsto_primeConductorSqrtHead_finitePart` | proved |
| Scalar-identity centering retains `(1−θ²)B_ml`; bands between powers carry `2(β−α)B_ml` | `tendsto_primeConductorPowerHead_renormalized`, `tendsto_primeConductorPowerBand_finitePart` | proved |
| Exact dilation `φ(q)c_l(kn)=φ(l)c_q(n)`, `q=l/gcd(l,k)`; literal head is a sum of reduced-conductor Grams | `ramanujanLagCoefficient_dilate_reduced`, `primeConductorHeadPairing_eq_reducedGram` | proved |
| Centered head means: off-diagonal interval `[0,I/√(φ(m)φ(l))]`, diagonal interval `[−2τ(m),0]`; packet norm `≤6log Q+log4+4` uniformly in cutoff | `centeredPrimeConductorHead_offDiagonal_bounds`, `centeredPrimeConductorHead_diagonal_bounds`, `abs_centeredPrimeConductorHeadPacket_le_log` | proved |
| Exact prime-dilation square energy `sum Lambda(k)||E_k a||²/k = sum[log m+tau(m)]a_m²`; completed upward packet row | `hasSum_primeConductorDilationJump_sq`, `hasSum_normalizedRamanujanPacket_up` | proved |
| Undilated prime packet has finite part `−2T` and common error `C(1+log Q)²/log N`; exact harmonic divisor convolution | `primeHead_harmonic_convolution`, `abs_primeConductorUndilatedPacket_remainder`, `exists_abs_primeConductorUndilatedPacket_finitePart_le` | proved |
| Packet mass where `N/n<T` is at most `[1+log(2T)+2(6log Q+log4+5)]sum a_m²`; uniform two-range multiplier estimate | `harmonicConductorPacket_quotient_tail_le`, `sum_sq_packet_le_quotient_tail` | proved |
| Every increasing weight in `[0,1]` has packet Gram discrepancy at most `32(1+log Q)sum a_m²`; actual scalar prime residual squared norm at most `C(1+log Q)sum a_m²/log N`, for every `Q,N≥2` | `abs_harmonicPacket_monotone_weight_le`, `exists_scalarPrimeResidual_packet_sq_le` | proved |
| Reserve `W ≥ a c⁻⁷(D − C log(2c)S)`, uniformly for `1≤c≤(log log N)^α`, `0<α<1/16` | CACT `exists_completeWeil_logarithmic_defect_reserve_iteratedLog` | proved |

## 6. Tools

**Developed**
- Literal shell calculus: decomposition, count, support, top band; prime-free pole rows.
- Lattice/continuum comparison for every conductor.
- Witness method for payment floors (top-band perturbation, `log 2` window Cauchy–Schwarz).
- First-order cell comparison, Laplace-moment pole rows, periodic shell windows, Abel summation on partners.
- Uniform-in-overlap (`1 ≤ c ≤ N/4`) joint coefficient bounds for witness, periodic, Ramanujan and two-mode data.
- Divisor-jet algebra: conductor expansion, Plancherel, power deformation, reciprocity, finite adjunction spectrum.
- Positive source/profile autocorrelation weights and smoothed square completion.
- Exact harmonic finite parts and torsion identification; remainder bounded by a quadratic tail and a logarithmic plateau at every horizon.
- Exact affine conductor selection and full prime finite parts on every fixed finite packet.
- Exact fixed-head limits and their complementary torsion boundary.
- Exact power-cutoff and band finite parts, including square-root cancellation of mixed raw pairings.
- Exact reduced-conductor Gram decomposition of literal prime heads; uniform logarithmic period-mean head norm.
- Uniform undilated prime finite part on every conductor packet, including growing supports.
- Uniform packet mass on short quotient horizons and scalar prime-residual norm with logarithmic conductor loss.
- Common complete-conductor residual bounds on every logarithmic conductor range.

**To build**
- Identification of the divisor-jet completion with the complete Weil shell block (horizon boundary included).
- Joint payment ledger for shells + pole + archimedean shells with tracked `(θ, κ)`.
- Mean-square conductor costs in the upward prime residual (needs quantitative Mertens on short blocks).
- Control of the successor-variation form against `D`.

## 7. Open questions

1. Extend the uniform logarithmic reserve beyond `c≤(log log N)^α`, `α<1/16`.
2. Does the full agreement-shell block admit a sum-of-squares decomposition matching the divisor-jet completion?
3. PNT discrepancy `Σ_m f(m)[(1/m)Σf − Σ_k Λ(k)f(km)]` on the top band: size relative to `D`, `S`?
4. Successor-variation form `Σ_h Σ_ℓ y(ℓ)(x(ℓ+h) − x(ℓ))β`: which inequality with `D` holds; does it fail for Beurling systems?
5. Archimedean shells (`k = 1`): their signed interaction with prime shells and pole.
6. Operator control of the whole upward residual on growing conductor packets.
7. Twins: bound the twin defect via density of successor disagreements on the top band.

## 8. Traps

| Trap | Fact |
|---|---|
| Shells are an error term | They repay `log c` exactly on conductor modes; without them every nonpolar reference energy is negative past touching (`exists_overlap_all_nonpolar_reference_energies_negative`) |
| A continuum of shifts repays too | Continuum shells carry only the pole charge; continuum energy → −∞ |
| The repayment is prime arithmetic | On the pole vector the shells are prime-free; repayment is the unit gap of `ℤ` |
| Better Young constants remove `c¹⁶` | Every separate payment, even one-sided, costs `≥ A⁺²/(2ε)`, order `c⁹` at the reserve fraction |
| The floor witness is a negative direction | Jointly with the pole it costs only `O(G(c + 1 + log N))` |
| Repayment on conductor modes is repayment | Off the conductor span the signed structure is the open core |
| Positive packets at growing `c` are confinement | Packets are fixed (or non-effectively growing); confinement must reach every negative vector |
| Positive divisor-jet completion = positive shell form | Finite-coefficient positivity is not identified with the full Weil block |
| Twins differ by their primes | Only on shells where the gauge disagrees with its successor |
| Divisor jets are mean-zero | Period mean of `J_m` is `Λ(m)`; centering is needed before Plancherel |

## 9. Context

**Uses** (import counts): RenormalizedArithmeticPotentialTheory 17, RHTower 12, SignedArithmeticHodgeTheory 3,
HTGeometry 5, CriticalArithmeticCorrelationTheory 3, ArithmeticElectrostatics 1,
SpacingScaleHarmonicAnalysis 1, CompletedArithmeticForms 1,
BiScaleUncertainty 1, BezoutValuationIncidence 1, ArithmeticPositiveDuality 1, ArithmeticLorentzianGeometry 1,
ArithmeticIntersectionTheory 1.

**Used by**: none (umbrella only).

| Neighbour | Relation |
|---|---|
| RenormalizedArithmeticPotentialTheory | Completed conductor energies, shell repayment law, adjunction energy, pole-profile collapse |
| CriticalArithmeticCorrelationTheory | Polynomial reserve, residual horizon decay, downward prime row as the divisor jet |
| CompletedArithmeticForms | Growing packets (`1/40` there, `1/19` here) and the reserve being paid |
| SpacingScaleHarmonicAnalysis | Atom dilation, overlap identity, the non-ratio form and its bounded-overlap rows |
| ArithmeticGaugeTheory | General-kernel shell calculus and gauge charge (same object, other kernel) |
| BezoutValuationIncidence / ArithmeticIntersectionTheory | Ramanujan lag coefficients, tame different, torsion-orbit different |
| SignedArithmeticHodgeTheory | Uniform Ramanujan residual budget |
| ArithmeticPositiveDuality | Critical line as positivity threshold of the integer successor |
| BiScaleUncertainty | Shift-product integrals of compact profiles |

## 10. Big picture

The successor shells are where additive and multiplicative structure meet inside the Weil form, and the
programme shows that the fixed-overlap positivity is not a prime phenomenon but an integer one: the unit gap of
the shift lattice pays the logarithm, and a continuum of shifts would leave the form unboundedly negative. This
locates the discreteness that RH-strength positivity must use.

Growing-overlap positivity and logarithmic reserve hold on the stated iterated-logarithmic ranges.
Paying the shells by themselves is provably expensive, while joint payment with the pole retains cancellation. The
divisor-jet work exposes the finite algebra behind that cancellation as a positive divisor-graph energy with
explicit spectrum, positive even after arbitrary signed smoothing. The harmonic Gram finite part is exactly
this energy plus its scalar counterterm, equivalently Euler's scalar minus torsion intersection.
The full prime pairing retains the negative torsion intersection, with diagonal `−2log m` after removing
its logarithmic divergence. Complete-period affine correlations identify the precise conductor transitions.
The remaining gap is identification: proving
that the true complete Weil shell block is such a completion, including its horizon boundary, for vectors off
the conductor span at larger overlap. That joint signed estimate is the central missing input to wider confinement.
