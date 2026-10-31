# ArithmeticDefectRigidity (ADR)

Namespace `GaloisForLFunctions.ArithmeticDefectRigidity`; umbrella `ArithmeticDefectRigidity.lean`; 88 modules.
Everything is unconditional. Most statements are dichotomies `Admits dampedMobiusEnergy ε ∨ P`: the
receiver energy is bounded, or the escape property `P` holds.

## 1. Motivation

At damping `0 < ε < 1/2` the receiver energy `E_T = ‖Ψ‖²_T` of the centred damped Möbius prefix is bounded
for a cofinal family of dampings iff RH holds (receiver programme). ADR studies the escaping alternative:
what object carries divergent energy, which source relations survive normalization and limits, and whether
those relations pin the object to zeros of ζ. Outcome: escape states are cyclic Hilbert modules of the
critical Wiener algebra; power-like rows obeying the renormalized inversion law exist exactly at translated
zeros `ζ(s+ε) = 0`, with multiplicity.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Damping | `SubcriticalDamping` | `0 < ε < 1/2`; `α = 1−ε` |
| Receiver | `pmPowerDampedCenteredDivisorPrefix ε` (Ψ), `dampedMobiusEnergy` | centred prefix; `E_T = Σ_{n≤T} Ψ(n)²/(n(n+1))` |
| Forcing | `inversionDefect` (ρ), `forcingEnergy` | `ρ = Ψ + Σ_{j≥2} j^{−ε}Ψ(⌊n/j⌋)` (inversion law, ACCE) |
| Power / remainder | `forcingPower`, `forcingPowerCoefficient`, `forcingRemainder`, `forcingRemainderBudget` | `ρ = c_ε n^α + R`, `c_ε > 0`, `‖R‖_T ≤ B_ε` |
| Pole trace | `poleTraceDomain`, `poleTrace`, `actualPoleTrace` | `𝓛v = Σ v(n)(n^{−α}−(n+1)^{−α})/α` |
| Renormalized cofactor | `renormalizedCofactorOperator` (D̃), `renormalizedResidualOperator` | `D̃v = Σ_{j≥2} j^{−ε}v(⌊n/j⌋) − 𝓛(v)n^α`; residual `v + D̃v` |
| Inverse pole power | `inversePolePower`, `inversePoleVector` | `q_ε = Σ_{d≤n} μ(d)d^{−ε}⌊n/d⌋^α` |
| Dilation | `rowDilate`, `dil`, `dilOp` | `D_p v(n) = v(⌊n/p⌋)` |
| Cofactor sums | `totalCofactorSum`, `cTotalCofactorSum`, `etaCofactorSum` | `S_ε v = Σ_{j≤n} j^{−ε}v(⌊n/j⌋)`; `H_ε = S_ε − 2^α D₂S_ε` |
| Euler laws | `eulerLaw`, `cEulerLaw` | `w − p^s D_p w` |
| Energies | `pronicEnergy`, `cPronicEnergy`, `CAdmitted`, `Adm`, `EnergyBounded` | full-horizon pronic energy; admitted = `v(0)=0` + finite energy |
| Cofactor Gram | `cofactorGram`, `cofactorGramRadius` | `K_T(j,k) = ⟨D_jΨ,D_kΨ⟩_{T+1}/E_{T+1}`, `|K| ≤ 1/√(jk)` |
| Escape state | `ActualCofactorLimit` (`kernel`, `Hilbert`, `vector`, `dilation`, `wienerRepresentation`, `annihilator`, `moduleHull`) | subsequential Gram limit with its cyclic Wiener module |
| Power rows | `powerRow`, `powerLogRow`, `powerRowCofactorSum`, `powerPoleTrace`, `zetaLeibnizRow` | `Re(a n^s)`, `Σ c_k log^k n·n^s` |
| Row Mellin | `rowMellin` | `𝓜v(w) = Σ v(n)(n^{−w} − (n+1)^{−w})` |
| Diffuse coordinates | `receiverEnergyQuantile`, `CellWord`, `BoundedCellMultiplier` | energy quantiles, shift/dilation words, moving localizations |
| Countermodels | `whiteNoiseKernel`, `oddWhiteNoiseKernel`, `augmentationKernel`, `OriginStepModule.kernel`, `MixedOriginModule.kernel`, `dyadicGhost` | abstract Grams/rows passing partial laws |

## 3. Language

- **Admission / escape**: `Admits dampedMobiusEnergy ε` (bounded `E_T`) vs `E_T → ∞`; `admits_or_tendsto_atTop` (ACompT).
- **Forcing vs receiver normalization**: divide by `F_T` or by `E_T`; they never agree.
- **Renormalized inversion law** of a row `v`: `v + D̃v` has bounded energy ⇔ `S_ε v − c n^α` has bounded energy.
- **Tied exponent**: `z` with `2^z = 2^s`, `3^z = 3^t`. **Translated zero**: `ζ(s+ε) = 0`.
- **Hulls**: `moduleHull` (Bohr zeros of the annihilator) ⊆ AOT `obstructionHull` (zeros of the paid ideal).
- **Horizon order**: numeric order of horizons, `p ↦ p·K(p,p)` antitone; finer than multiplicative laws.

## 4. Mechanisms

**A. Scales.**
1. Forcing dominates: `F_T ≥ b_ε T^{1−2ε}`, `E_T ≤ C e^{−κσ(T)/270} F_T` (VK); `F/E → ∞`; no common scalar normalization.
2. Gram tangent: `F + G − 2Q = E` (`G = ‖D‖²`, `Q = ⟨ρ,D⟩`); `(FG−Q²)/F² → 0`: forcing-scale Grams erase the receiver.
3. Cofactor tail carries the forcing, for fixed `J` and for the moving window `⌊log(F/E)⌋`.

**B. Successors, words, forcing mass.**
4. `|Ψ(n+k) − Ψ(n)| ≤ k`; fixed shifts vanish on escape. Shift hierarchy: raw `k² = O(E)`, recentred `k = O(E)`,
   recentred `k^α = O(E)`, raw `k^{2α} = O(E)` all vanish; nonvanishing normalized shifts need `k²/E` unbounded.
5. Words cost `B(w)²` in energy; forcing mass `Σρ/(n(n+1)) = −ζ'/ζ(1+ε)` pays word work absolutely; horizon tails `≤ B(H+1)^{−ε}`.

**C. Paid renormalization.**
6. `‖R‖_T ≤ B_ε` at all `T`; `Ψ + D̃Ψ = R`; work `⟨Ψ,D̃Ψ⟩/E → −1` (antipodal), kept by energy quantiles and every bounded moving localization.
7. `𝓛(Ψ) = c_ε`; `𝓛(j^{−ε}D_j v) = 𝓛(v)/j`; `|[D̃,D_p]v| ≤ |𝓛v|` pointwise.
8. `v = floorTransform_μ(v + D̃v) + 𝓛(v)q_ε`; `𝓛(q_ε) = 1` (DLVP `M(x) ≪ x e^{−√log x/12}`); `ker(I + D̃) = ℝq_ε`.

**D. Euler factors on the log scale** (`g(u) = e^{−u/2}w(⌊e^u⌋)`, pronic energy = `∫g²`).
9. Law at `p` = one-prime law `g − e^{κ log p}g(·−log p) ∈ L²`; it fixes `g` modulo `L²` only up to `e^{κu}`×periodic ghost.
10. Two laws with incommensurable periods (`log 2`, `log 3`) leave `c e^{κu}`: periodic finite-energy functions vanish; two periods force a constant (ergodic irrational rotation). Twisted laws: eigenfunctions of irrational rotations are characters ⇒ tied exponent.
11. `H_ε = (I − 2^α D₂)S_ε` removes the pole exactly: `‖H_εΨ‖_T` bounded, symbol `(1−2^{α−s})ζ(s+ε)`; laws at 2 and 3 for `S_ε v` ⇔ renormalized inversion.

**E. Symbol calculus of D̃.**
12. Hyperbola at `√n`: `S_ε n^s = 𝓛_s n^α + ζ(s+ε)n^s + O(n^{(Re s−ε)/2})`; Cauchy estimates give log-power rows ↦ Leibniz matrix of `ζ^{(i)}(s+ε)`.
13. Rows `Re(b n^s)`, `Re s ≥ 1/2`, have infinite energy; top log-coefficient dominates; primes 2, 3 separate exponents (`2^a ≠ 3^b`), eliminations `D_p − p^{−s}` kill or are injective per block.
14. Mellin: `𝓜(S_ε v) = ζ(w+ε)𝓜v` (Re w > 2), `𝓜(n^s) = sζ(w−s+1) + E_s`, `𝓜r` holomorphic on `Re w > 1/2` for finite energy `r`; identity theorem + residue at `s` ⇒ `ζ(s+ε) = 0`.
15. Finite rank: Lagrange projectors in `D₂`, `D₃` split a row into joint eigen-components; `S_ε` commutes with dilation polynomials.

**F. Escape states.**
16. Compactness: one subsequence (along any cofinal horizon family) gives `K` with `K(1,1)=1`, PSD, `|K| ≤ 1/√(jk)`, packet contraction by `1/p`.
17. Module: cyclic `Hilbert L`, `‖dilation p‖ ≤ p^{−1/2}`, contractive `WienerAlgebraAt (1/2)` action; on escape paid ideal ⊆ annihilator ⇒ `∅ ≠ moduleHull ⊆ obstructionHull`; repairs and paid kernels vanish.
18. Annihilator quotient: finite (= dim = Σ joint character multiplicities) or exactly continuum.
19. Admission ⇒ unique kernel, `K(pj,pk) = K(j,k)/p`, faithful, full Bohr hull, infinite dim. Hence finite-dim or non-faithful ⇒ escape.
20. Horizon order: `p·K(p,p) = lim E(⌊T/p⌋)/E(T)` ∈ [0,1], antitone on packets and on `p‖D_p x‖²`; zero diagonal ⇒ `dim ≤ p−1` and escape; record-minimum horizons give a limit with `K(p,p) ≥ p^{2ε−2}`.
21. Contraction `K(pj,pk)/K(p,p)` is again actual; module = closed range of `D_p`, annihilator `I:δ_p`; compose multiplicatively; index drops by `dim ker D_p`.
22. Rank one: `K(j,k) = χ(j)χ(k)`, `χ` augmentation or `η(p)p^{−s}`, `s ≥ 1/2`, `η` multiplicative sign; finite-dim hull points are augmentation or radial `|ω(p)| = p^{−α'}`, limits of half-plane points `Re s ≥ 1/2`.
23. Kernel set: singleton or continuum (vanishing Gram steps fill intervals); non-uniqueness ⇒ escape. Hulls conjugation-symmetric; Möbius and Liouville modules unit-equivalent.
24. Origins: reset-origin shifts realize every `c > 0` with Gram `(K + c/max(j,k))/(1+c)` (faithful, continuum index); raw shifts add constant `c`, never an actual kernel.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Scale separation | `tendsto_forcingEnergy_div_receiver_atTop`, `no_common_scalar_normalization` | unconditional |
| Gram tangent | `gram_distance_div_receiverEnergy_eq_one`, `tendsto_forcingGramDefect_div_forcingEnergy_sq_zero` | unconditional |
| Paid remainder, antipodality | `pronicNorm_forcingRemainder_le`, `admits_or_renormalizedCofactorWork_is_antipodal` | unconditional; dichotomy |
| Pole trace, forcing mass | `actualPoleTrace_eq_forcingPowerCoefficient`, `forcingMassLimit_eq_logarithmicDerivative` | unconditional |
| Kernel line | `poleTrace_inversePoleVector`, `ker_renormalizedResidualOperator` | unconditional |
| Eta form paid | `exists_pronicNorm_etaCofactorSum_actual_le` | unconditional |
| Two Euler factors | `exists_pronicEnergy_sub_pole_ne_top`, `cofactor_two_euler_laws_iff`, `one_euler_factor_leaves_a_ghost` | unconditional |
| Two-pole expansion | `norm_powerRowCofactorSum_sub_le_rate`, `norm_logPowerCofactorSum_sub_le` | unconditional |
| Zero detector | `powerRow_renormalizedInversion_bounded_iff` | unconditional (`1/2 ≤ Re s < α`) |
| Index = zero multiplicity | `powerLogRows_global_renormalizedInversion_iff_order` | unconditional |
| Tied joint eigenrows | `exists_cPronicEnergy_sub_cpow_ne_top` | unconditional (`Re s ∈ (1/2,1]`) |
| Mellin residues | `riemannZeta_add_eq_zero_of_powerLike_solution` | unconditional |
| Rank-one escape ⇔ zero | `riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow` | unconditional (`1/2 < Re s < α`) |
| Finite-rank escape | `exists_finiteRank_zeroPower_decomposition`, `cPronicEnergy_ne_top_of_finiteRank_of_zeroFree` | unconditional |
| Common limit | `exists_cofactorGram_limit`, `exists_actualCofactorLimit_along_cofinal` | unconditional |
| Escape hull | `admits_or_moduleHull_subset_obstructionHull` | dichotomy |
| Faithfulness | `faithful_or_receiver_escapes`, `receiver_escapes_of_finiteDimensional` | dichotomy |
| Index dichotomy | `annihilator_quotient_finite_or_continuum`, `finite_joint_index_or_continuum` | unconditional |
| Horizon order | `contracted_energy_ratio_tendsto`, `scaled_diagonal_antitone`, `scaled_dilation_norm_sq_antitone` | unconditional |
| Positive record limit | `exists_actualCofactorLimit_kernel_diag_ge_rpow` | unconditional |
| Kernel family | `actualCofactorKernelSet_singleton_or_continuum` | unconditional |
| Rank one | `rankOneCharacter_eq_augmentation_or_signed_rpow` | unconditional |

## 6. Tools

**Developed.**
- Pronic calculus: `pronicPairing_packet_energy_eq`, `pronicNorm_sq_monotone`, `normalized_moving_gram_perturbation_tendsto_zero`, `pronicEnergy_ne_top_iff`.
- Mellin cells: `hasSum_dil_mul_mellinCell`, `hasSum_dil_mul_complexMellinCell`, `rowMellin_cpow_eq`, `differentiableOn_rowMellin`, `hasSum_cTotalCofactorSum_mul_cell`.
- Hyperbola / Abel: `sum_mul_partialSum_div_eq_hyperbola`, `sum_Ioc_mul_eq_abel`, `exists_abs_moebiusHarmonic_le`.
- Log-scale ergodic calculus: `ae_eq_zero_of_periodic`, `exists_ae_eq_const_of_two_periods`, `eigenfunction_of_irrational_rotation`, `exists_lintegral_sub_const_mul_cexp_ne_top`, `lintegral_logProfile_sq`.
- Prime separation: `exists_separating_prime`, `eq_of_two_three_cpow_eq`, `coeff_eq_zero_of_cAdmitted_sum`.
- Dilation polynomials: `aeval_dilOp_comm`, `cTotalCofactorSum_aeval`, `euler_mul_basis`, `adm_euler_component`.
- Module transport: `unitGramUnitary_intertwines`, `exists_actual_contracted_module`, `contractedKernelIsometry_wiener`.
- Extraction: `exists_actualCofactorLimit_along`, `admits_or_exists_record_horizons`, `exists_record_min_gt`, `pronicEnergy_eulerLaw_ne_top`.

**To build.**
- A source law forcing escape states (actual limits or receiver rows) to satisfy Euler laws at 2 and 3 with finite-energy error: the bridge from §4F to §4E.
- Dilation regularity `‖D_jΨ − D_{j+1}Ψ‖` at the energy scale (controls the eta tail, `alternatingPacket_le_of_tail`).
- Domain invariance and critical-norm bounds for D̃ on rows beyond the actual trace vector.
- A module invariant finer than the annihilator hull.

## 7. Open questions

1. Do actual escape modules carry joint approximate eigenvectors of `D₂`, `D₃` that lift to rows obeying the Euler laws? If yes, the finite-rank theorem plus a zero-free line excludes them.
2. Is `moduleHull = obstructionHull` on escape? Are rank-one signs/exponents tied to zeros at the Gram level (they are at row level)?
3. Is the record limit with all `K(p,p) > 0` infinite-dimensional? Is the kernel set a singleton (it is under admission)?
4. Critical line: the two-dilation and Mellin theorems need `Re s > 1/2`; the zero detector holds at `Re s = 1/2`. Extend the tied-exponent theorem to `Re s = 1/2`.
5. Joint extraction: one carrier keeping fixed covariances, quantile work and the moving cofactor tail without exchanging limit and infinite sum.
6. Moving successors that act nontrivially at the escape scale need `k²/E` unbounded; find their boundary cost.

## 8. Traps

| Trap | Fact |
|---|---|
| Gram + antipodal laws are not source laws | white noise satisfies all, with unique antipodal extension (`whiteNoise_has_unique_antipodal_extension`) |
| Multiplicative laws are not enough | odd white noise passes packet contraction; excluded only by horizon order (`actual_kernel_ne_oddWhiteNoise`) |
| Abstract laws admit non-Kronecker points | augmentation kernel passes everything; its point is no half-plane point (`augmentationBohrPoint_ne_halfPlanePoint`) |
| One Euler factor | dyadic ghost `n^α cos(2π log₂ n)` passes the law at 2 (`one_euler_factor_leaves_a_ghost`) |
| A nonzero module is not escape | admitted limits are faithful with full hull |
| Forcing normalization | erases the receiver: Gram determinant `/F² → 0` |
| Fixed cofactors | the tail carries all forcing; entrywise limits do not pass infinite cofactor sums |
| Finite-horizon symbols | cannot exclude cancellation by `S_ε r`, `r` of finite energy; Mellin residues can |
| Row vs state | rank-one/finite-rank theorems take Euler laws on a row as hypotheses; actual limits are not shown to satisfy them |
| Shifted origins | reset-origin Grams are shifted rows, not unshifted limits; raw constant boundary never actual (`unreset_boundary_ne_actual_kernel`) |
| Positive diagonals | do not force infinite dimension (rank-one limits have them); `RecordMinimaForceInfiniteCofactorLimits` proves positivity only |
| Power subtraction | not a bounded operator on arbitrary rows; generic domain invariance of D̃ unproved |
| Hygiene | several modules end with `#print axioms` lines |

## 9. Context

| Uses (imports) | Count | Used by | Count |
|---|---|---|---|
| HTGeometry | 26 | BiarithmeticGeometry | 3 |
| ArithmeticOrientationTheory | 17 | ArithmeticCorrespondencePositivity | 3 |
| ArithmeticContinuationAndCriticalEnergy | 10 | ArithmeticCorrelationGeometry | 3 |
| RHTower | 9 | ArithmeticCastelnuovoSeveri | 1 |
| TransHorizonIncidenceMechanics | 5 | MainTheorems | 1 |
| BezoutValuationIncidence | 4 | | |
| ArithmeticCompensationTheory | 3 | | |

| Neighbour | Interface |
|---|---|
| ArithmeticContinuationAndCriticalEnergy | receiver Ψ, inversion law, dilation blocks, pronic calculus |
| ArithmeticCompensationTheory | `admits_or_tendsto_atTop`, energy growth bound |
| BezoutValuationIncidence | VK zero-free saving, DLVP Mertens bound, pronic norms |
| TransHorizonIncidenceMechanics | Mellin cells, smooth-power expansion, critical Wiener kernels, partial ζ sums |
| ArithmeticOrientationTheory | Wiener algebra, paid ideal, obstruction/operator hulls, Bohr points |
| HTGeometry | kernel Hilbert spaces, normalized-budget lemmas, monotone characters, ζ meromorphy |
| RHTower | floor transforms, Möbius power weights, ξ order of zeros |
| ArithmeticCorrespondencePositivity | imports `TwoEulerFactorsDetermineThePoleTrace`, `TwoDilationEigenrowsArePowerRows`, `WienerCovariancesFollowTheCommonCofactorLimit` |
| ArithmeticCorrelationGeometry | imports `CommonCofactorLimitsExistAlongPrescribedHorizons`, `TheAdmittedCofactorKernelIsUnique`, `TheCofactorLimitCarriesACyclicDilationAction` |
| BiarithmeticGeometry | imports `TheForcingDominatesTheReceiver`, `PaidWienerKernelsAnnihilateTheCofactorLimit`, `TheClosedCofactorAnnihilatorHasNoCountableIndex` |
| ArithmeticCastelnuovoSeveri | imports `RecordMinimaForceInfiniteCofactorLimits` |

## 10. Big picture

ADR turns "the receiver energy might diverge" into a concrete object and asks what that object must look
like. The source keeps a lot: the forcing is paid by its own pole, the escaping energy is antipodal to its
cofactors, and every escape state is a cyclic module whose spectrum sits inside the obstruction hull. But
the same abstract constraints are satisfied by white noise and other countermodels, so geometry of Grams
alone never forces RH.

The decisive finding is a two-level picture. At the level of rows, the renormalized inversion law plus two
Euler factors (primes 2 and 3) is a zero detector: power-like solutions exist exactly at translated zeros of
ζ, counted with multiplicity, and vanish on zero-free lines. At the level of escape states, those Euler laws
are not yet derived. RH through this route reduces to one bridge: show that a divergent receiver produces a
row obeying Euler laws at two primes. Everything on either side of that bridge is proved.
