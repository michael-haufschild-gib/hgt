# Arithmetic Electrostatics (AES)

Namespace `GaloisForLFunctions.ArithmeticElectrostatics`; umbrella `ArithmeticElectrostatics.lean`; 30 modules.
Everything is unconditional; RH appears only inside proved equivalences.

## 1. Motivation

The zeros of ξ are the charges of the potential log|ξ|. Arithmetic computes several quantities of this potential: the
field at a charge (residues of (ζ'/ζ)²), its renormalized diagonal (ζ''/ζ, torsion discriminants), and Weil's pairing.
RH says the configuration is in transverse equilibrium: no zero feels a field across the critical line. AES turns this
into exact electrostatic laws (virial = energy, quantization, gap), measures what each law needs (an upper bound on the
field, a counterterm for the diagonal), proves the parts that are within reach (atomic-resolution stability, heat-flow
dissipation, large values at zero ordinates), and locates where they stop.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Field of a finite configuration | `fieldAt m z j` | E_j = Σ_{k≠j} m_k/(z_j − z_k) |
| Transverse / vertical energy | `transverseEnergy`, `verticalEnergy` | ½Σ m_j m_k (Re z_j − Re z_k)²/|z_j−z_k|² (resp. Im) |
| Reflection-closed configuration | `IsReflectionClosed` | z_{σj} = 1 − z̄_j, equal positive multiplicities |
| Divisor energy | `divisorTransverseEnergy`, `xiCopyTransverseEnergy` | ½Σ angularEnergy over ξ zeros, in [0,∞] |
| Window energy | `zeroWindow`, `windowEnergy` | Σ angularEnergy over |γ − T| ≤ H |
| Transverse field of a zero | `xiTransverseField`, `transverseForce` | field across the line at a zero copy |
| Damped source work | `xiDampedSourceWork`, `xiTaperedSourceWork`, `heightDamping`, `heightTaper` | Laurent-residue work of (ζ'/ζ)², damped R⁴/(R²+t²)², tapered |
| Reflected pair work | `reflectedEnergy`, `reflectedCross`, `reflectedWork` | pair + reflected partner in sum/difference coordinates |
| Selberg source | `selbergSource` | Λ₂ = Λ·log + Λ⋆Λ = μ⋆log² |
| Torsion orbit intersection | `orbitIntersection` (ArithmeticEffectivityTheory), `localCorrection` | I(m,n) = Σ log|ζ−η|; D = φ⋆Λ |
| Torsion pairing | `torsionPairing`, `selfMass`, `RenormalizesAt`, `RenormalizesWith` | Σ y_m y_n I(m,n) vs κΣφ(n)y_n² |
| Abel energy | `fullTorsionEnergy` | Σ −log|1 − rζη̄| over μ_A × μ_B |
| Atomic Weil prime form | `atomicWeilForm`, `weilPrimeKernel` (ArithmeticEffectivityTheory) | Σ x_m x_n Λ(n/m)(n/m)^{−1/2} on m ∣ n |
| Atomic test | `atomicTest`, `atomSpacing`, `atomicWidth`, `sharpAtomicWidth` | Σ x_n g(u − log n); δ_N = log(1+1/N) |
| Twisted kernel / prime sum | `twistedWeilPrimeKernel`, `twistedAtomicWeilForm`, `twistedPrimeSum` | sign-gauge twin ωΛ on atoms |
| Dirichlet polynomial tools | `coeffMass`, `primeCoeff`, `primeSupported`, `expSum`, `detector` | mass Σ|a_n|², prime polynomials, convolution powers |
| Heat depth energy | `heatGlobalVerticalEnergy`, `heatNonrealCopies` | Σ (Im z)² over nonreal zeros of the de Bruijn heat function |

## 3. Language

- **Equilibrium**: vanishing transverse field. **Stability**: positivity of the energy whose gradient is the field.
- **Virial law**: work of the field against a displacement = an energy.
- **Quantum**: an off-line zero and its partner contribute exactly m·m' to the transverse energy at every depth.
- **Counterterm**: self-energy per point added to make a diagonal-removed pairing positive; **Hecke compatible** if constant per point.
- **Arithmetic point**: z = 1 on the circle, orbit O_1; I(1,n) = Λ(n).
- **Atomic resolution**: tests concentrated at log n, n ≤ N, of width w below the spacing δ_N.
- **Sign twin / gauge**: completely multiplicative ω with ω(p) = ±1 replacing Λ by ωΛ.

## 4. Mechanisms

**A. Finite configurations**
1. Newton: Σ m_j E_j = 0. Stieltjes: Σ m_j z_j E_j = ((Σm)² − Σm²)/2. Transverse virial: Σ m_j(Re z_j − c)Re E_j = transverseEnergy for every c; transverse + vertical = ((Σm)² − Σm²)/2.
2. Reflection-closed: energy = 0 ⇔ all on ½ ⇔ all Re E_j = 0 ⇔ work ≤ 0. Partner segment is horizontal ⇒ quantum m_j m_{σj}; with m ≥ 1, critical ⇔ energy < 1. Maximum principle: rightmost charge has outward field, leftmost inward.

**B. The zero divisor**
3. 𝓔 = 0 ⇔ RH ⇔ 𝓔 < 1; #off-line ≤ 2𝓔; 𝓔 < ∞ ⇔ finitely many off-line zeros; at finite off-line index 𝓔 = Σ δ_j F_j (work), RH ⇔ work < 1.
4. Window: windowEnergy ≥ #off-line in window; an off-line zero forces ≥ 2; RH ⇔ every unit window has energy < 2.
5. Per zero: angular term ≤ 2/(1 + (γ−γ')²) ⇒ E(ρ) ≤ 16(C + log(|γ|+4)) (Lorentzian zero mass); energy is unconditionally logarithmic, the field is not bounded.
6. Source work: reflection pairing turns damped Laurent-residue work into a nonnegative pair kernel with summable majorant 16R⁴/((1+γ²)(1+γ'²)); tapers removed by dominated convergence; removing damping exhausts the full multiplicity-weighted transverse energy in [0,∞].
7. Hecke defect: 4L²M_f ≤ E_f(L) ≤ 8(cosh L − 1)M_f, E_f(L)/L² → 4M_f (M_f = Σ m δ²|f̂(ρ)|²).

**C. The field**
8. Counterterm identity F''/F = (F'/F)² + (F'/F)': self-term m² → m(m−1), residue 2mR(ρ) (R = field of the other zeros) unchanged.
9. Threshold: terminal witness field ≥ 1/(2δ) + cδ log γ ⇒ RH ⇔ field ≤ 1 at right zeros ⇔ field < √(2c log γ).
10. External field (Re s > 1): Re ξ'/ξ = Σ_ρ Re 1/(s−ρ) > 0 termwise; prime field + any finite Coulomb sum ≤ archimedean field; anti-alignment at zero ordinates: Σ Λ(n)n^{−σ}cos(γ log n) ≤ Re arch'/arch − m/(σ−β).
11. Large values at zero ordinates: unit-cell Sobolev + O(log) zeros per cell + Dirichlet mean value; prime polynomials have mass ≤ log X(log X + log4 + 4); powers F^k have mass ≤ k!S^k ⇒ aligned ordinates T^{1−1/C+o(1)} for X = (log T)^C.

**D. Renormalizing the diagonal**
12. Zero side: Λ₂ = Λ log + Λ⋆Λ ≥ 0, Λ₂(p^k) = (2k−1)log²p, L(Λ₂,s) = ζ''/ζ.
13. Circle: I(n,n) = φ(n)log n − (φ⋆Λ)(n) ≥ 0, D = φ·tame different, Leibniz on coprime orders ⇒ per-point additivity; tower p^a → p^{a+1} adds log p per point.
14. Counterterm rate: Schur with weights 1/n + Mertens ⇒ κ = 4 log N + O(1) suffices; a single prime orbit + Bertrand ⇒ κ ≥ ½log(N/2). The arithmetic point forces it: c(1) ≥ Σ Λ²/(cφ), κ² ≥ log2·(log N − C). Atomic Weil prime form has the same logarithmic rate (2log N + O(1) by Schur with n^{−1/2}; sharp log N + O(1) via RenormalizedArithmeticPotentialTheory).
15. Base: Abel energy T_r(A,B) = gcd·log(1/(1 − r^{lcm})) is PSD; power maps are similitudes T_r(At,Bt) = t·T_{r^t}(A,B); renormalized limit −gcd·log lcm; Fekete–Hadamard Σ_{i≠j} log|z_i−z_j| ≤ N log N attained by roots of unity.

**E. Stability at atomic resolution**
16. Below the spacing atoms are orthogonal, primeSum(atomicTest) = (∫g²)·atomicWeilForm, and disjoint shifts give Lévy gain e^{−1/2}log(δ_N/(2w)) per unit mass ⇒ Markov form M = arch − prime ≥ 0 for w ≤ atomicWidth N = N^{−O(1)} (sharp: δ_N N^{−e^{1/2}}).
17. With pole: Re W = M + 2C² − 2S²; Re W + 2S² ≥ 0 (rank-one counterterm); Re W ≥ 0 on nonnegative atomic tests.
18. Gauge: P_ω = diag(ω)P diag(ω), so every sign twin has the same spectral bounds and the same stability law; the twin's Markov form exceeds ζ's on nonnegative tests (two-atom test: by 2Λ(p)/√p·∫f²); M_ω(f_x) = M(f_{ωx}) + A(f⁺+f⁻) − A(f⁺−f⁻).
19. Coefficient gauge margin: ωΛ₂(p) = ω(p)log²p, margin 2log²p at a flipped prime, L-series margin ≥ 2log²p·p^{−σ}. Archimedean twists s ↦ ½ + λ(s−½) + iκ preserve transverse energy.

**F. Heat flow**
20. Real exterior zeros of an even order-one function do nonpositive vertical work (Im z·Im(f'/f − finite part) ≤ 0); passing to a simple zero gives Im a·Im(f''/f'(a) − 2Σ(a−r)⁻¹) ≤ 0; a conjugation-closed simple packet has drift ≤ −2·nonreal count.
21. Simple heat zeros have unique local branches with velocity f''/f'; nonreal zeros are confined to a fixed ball for t ≥ a > 0; the global depth energy is continuous through collisions and differentiates along branches.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Transverse virial; energy count | `sum_mul_re_fieldAt_eq_transverseEnergy`, `transverseEnergy_add_verticalEnergy` | proved |
| Equilibrium = critical line; one scalar; gap | `critical_iff_equilibrium`, `critical_iff_work_nonpos`, `critical_iff_transverseEnergy_lt_one` | proved |
| Divisor energy: RH ⇔ 𝓔 < 1; finite ⇔ finite off-line index; work = energy | `riemannHypothesis_iff_divisorTransverseEnergy_lt_one`, `divisorTransverseEnergy_lt_top_iff`, `divisorTransverseEnergy_eq_ofReal_work` | proved |
| RH ⇔ every unit window has energy < 2 | `riemannHypothesis_iff_windowEnergy_lt_two` | proved |
| Energy of a zero ≤ 16(C + log(|γ|+4)) | `angularEnergy_le_log`, `one_le_angularEnergy_le_log` | proved |
| Damped arithmetic source work exhausts the transverse energy | `xiTaperedSourceWork_eq_paired_tsum`, `xiTaperedSourceWork_tendsto`, `xiDampedSourceWork_tendsto_energy` | proved |
| Field thresholds (≤ 1; < √(2c log γ)) | `riemannHypothesis_iff_forall_transverseField_le_one`, `exists_riemannHypothesis_iff_transverseField_lt_sqrt_log` | proved |
| External field law; anti-alignment at zero ordinates | `re_LSeries_vonMangoldt_add_sum_le`, `re_LSeries_vonMangoldt_le_at_zero_ordinate` | proved |
| Large values; alignment law; power saving | `exists_card_largeValues_le`, `exists_card_aligned_le`, `exists_card_aligned_power_saving` | proved |
| Hecke defect = moment of inertia | `heckeDefect_le_moment`, `tendsto_heckeDefect_div_sq` | proved |
| Selberg source: Λ₂ ≥ 0, L(Λ₂) = ζ''/ζ; self-term/residue | `selbergSource_nonneg`, `LSeries_selbergSource`, `selfTerm_and_residue_of_analyticOrderAt` | proved |
| Torsion self-intersection, Leibniz, tower adjunction | `orbitIntersection_self_eq`, `orbitIntersection_self_mul_of_coprime`, `orbitIntersection_self_prime_pow_succ` | proved |
| Counterterm rate ∈ [½log(N/2), 4log N + O(1)]; arithmetic point | `torsionCounterterm_rate`, `le_counterterm_one`, `log_two_mul_le_sq_of_renormalizesAt` | proved |
| Atomic Weil prime form: upper and arithmetic-point lower bound | `atomicWeilForm_le`, `log_two_mul_le_sq_of_atomicWeilForm_le` | proved |
| Abel similitude; Fekete bound attained by torsion | `fullTorsionEnergy_eq`, `fullTorsionEnergy_mul`, `sum_sum_log_norm_sub_le`, `logEnergy_self_eq` | proved |
| Atomic stability law (Schur and sharp counterterm) | `markovEnergy_atomicTest_nonneg`, `markovEnergy_atomicTest_nonneg_sharp`, `archForm_poleTest_ge` | proved |
| Weil form on atomic tests | `re_W_add_sinh_sq_nonneg`, `re_W_atomicTest_nonneg_of_nonneg` | proved |
| Gauge invisibility; twin margin on the positive cone | `twistedWeilPrimeKernel_eq`, `twinMarkovEnergy_atomicTest_nonneg`, `twinMarkov_sub_markov_pairWeights`, `twinMarkov_atomicTest_eq` | proved |
| Coefficient gauge margin | `gaugeMargin_window`, `LSeries_gaugeMargin`, `eq_one_of_twisted_selbergSource_nonneg` | proved |
| Heat depth: E(b) + 2∫N ≤ E(a); antitone; E = 0 ⇔ all real | `heatGlobalVerticalEnergy_add_integral_count_le`, `antitoneOn_heatGlobalVerticalEnergy`, `heatGlobalVerticalEnergy_eq_zero_iff` | proved |

## 6. Tools

**Developed**
- Virial/symmetrization kit for ordered pairs (`sum_sum_erase_swap`, `two_mul_sum_sum_erase`).
- Reflected pair inequalities with damping and tapers (`reflectedCross_near`, `reflectedCross_far`, `heightDamping_taper_work_bound`).
- Laurent jet of F''/F and (F'/F)² at a zero of order m.
- Schur-test row bounds over Hecke towers (`sum_offDiag_row_le`, `sum_row_weilPrimeKernel_le`).
- Atomic test calculus: orthogonality, exact Hecke lag pairings, Lévy gain of disjoint shifts (`levyEnergy_ge_of_disjoint_shifts`, `primeSum_atomicTest`).
- Large-values machinery at zero ordinates: cell Sobolev, window mean value, convolution-power mass (`sum_normSq_pow_le`, `expSum_pow`).
- Heat-zero branch and packet-drift kit (`exists_simple_heat_zero_branch`, `heatGlobalPacket_drift_le`, `heatGlobalVerticalEnergy_hasDerivWithinAt_of_simple`).

**To build**
- An arithmetic upper bound for the transverse field at right zeros.
- Positivity at the spacing scale w ~ 1/N (cross kernel of overlapping shifts; prime cancellation).
- A calculus of overlapping atoms and non-ratio lags.
- A forcing law: depth δ ⇒ a short prime detector reaches V(δ) at the zero's ordinate.
- A finite initial value for the heat depth energy (or a per-zero quantum for it).

## 7. Open questions

1. Field law: field at right zeros below max(1, √(2c log γ)), or every unit window energy < 2 (both RH-equivalent); partial: finite total energy (finite off-line index).
2. Stability at the spacing w ~ 1/N, where the Lévy gain is bounded and the prime counterterm grows like log N: does a bounded-rank counterterm survive?
3. Matched renormalization: torsion counterterm vs zero-side Λ log through the explicit formula for ζ''/ζ.
4. Forcing law: combined with the power-saving alignment count it would give a zero-density estimate T^{1−1/C+o(1)} for deep zeros; the terminal reserve sits below the background ½log γ.
5. Does the heat depth energy have a finite limit as t → 0⁺, and does dissipation give a quantitative zero-free statement?

## 8. Traps

| Trap | Fact |
|---|---|
| Equilibrium can be derived variationally | ξ has no linear ODE; only virial identities hold on every configuration |
| A positive field at the deepest zero excludes it | It detects; exclusion needs an upper bound of size max(1, √(2c log γ)) |
| Transverse energy shrinks as zeros approach the line | Quantized: a full m·m' per pair at every depth |
| Field and energy are equally hard | Energy is O(log γ) per zero unconditionally; the field has no unconditional bound |
| Removing the diagonal keeps positivity | Needs a counterterm of size Θ(log N) |
| A bounded counterterm works away from one orbit | The arithmetic point alone forces divergence |
| Λ₂ ≥ 0 is form positivity | It is coefficient positivity; forms on signed tests do not inherit it |
| A coefficient gauge margin gives a spectral margin | On atoms the gauge is a diagonal of signs: identical spectra |
| On nonnegative tests ζ beats its twins | The twin's form is larger there by 2Λ(p)/√p per unit mass |
| The pole term is a nonnegative correction | Signature (1,1); −2S² is a rank-one counterterm |
| Archimedean self-energy cannot pay the prime form | It pays it below a power of the spacing, not at the spacing |
| Heat depth energy is a quantum-gapped RH criterion | It has no proved finite initial value and no per-zero quantum |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 28 (angular energy, transverse force/equilibrium, Lorentz zero mass, zero bands, Mertens, Dirichlet MVT, large values, de Bruijn heat, Markov form, pole term) |
| ArithmeticCorrespondencePositivity | 5 (fieldAt, outward field witness, source field, L(Λ⋆Λ) = (ζ'/ζ)², ξ reciprocal field) |
| HTGeometry | 4 (Fredholm/Hadamard, divided differences, log-derivative poles, forward comparison) |
| ArithmeticEffectivityTheory | 3 (orbit intersections, Hecke law, log energy of roots of unity) |
| RenormalizedArithmeticPotentialTheory, ConjugateDiagonalGeometry, ArithmeticIntersectionTheory | 1 each |

| Used by | Modules |
|---|---|
| RenormalizedArithmeticPotentialTheory | 4 (counterterm, anomaly, Mertens for characters, matched stability) |
| ArithmeticIndexDescent | 4 (index paid by transverse energy, source work, damping increments) |
| SpacingScaleHarmonicAnalysis | 3 (atomic family, spacing-scale stability, self-energy of an atom) |
| SelectiveMultiscaleArithmeticPositivity | 2 (gauge invisibility) |
| BezoutValuationIncidence, CriticalArithmeticCorrelationTheory, ArithmeticLorentzianGeometry, HilbertianExplicitFormulas, RHTower/Heat | 1 each |
| MainTheorems | umbrella |

| Neighbour | Relation |
|---|---|
| ArithmeticCorrespondencePositivity | supplies the field and Laurent residues; AES adds virial laws, thresholds, work = energy |
| ArithmeticEffectivityTheory / ArithmeticIntersectionTheory | torsion orbits and Hecke law; AES adds self-intersections, adjunction, counterterm rates |
| RenormalizedArithmeticPotentialTheory | sharp counterterm log N + O(1); continues the atomic stability law |
| SpacingScaleHarmonicAnalysis | takes the atomic stability law to the spacing scale |
| ArithmeticIndexDescent | uses transverse energy and reflected work to pay an index |
| RHTower/Heat | heat-zero dynamics; AES proves global depth dissipation |

## 10. Big picture

AES shows that RH has an exact electrostatic form: the zeros are in transverse equilibrium, and equilibrium is
quantized, so a single bounded quantity (energy below one quantum, window energy below two, field below a fixed
threshold) would decide it. Everything that can be computed is computed: energies are logarithmic per zero, source work
equals energy in the limit, and the explicit formula reads the field from the primes. What is missing is always the same
kind of statement: an upper bound for the field or a sign for the work, not a new identity.

The renormalization results say where positivity lives. Removing the diagonal costs a counterterm that grows like log N,
forced by the arithmetic point; the archimedean place pays it exactly while the tests are narrower than a power of the
atom spacing, and stops paying at the spacing itself. At that resolution the prime form cannot distinguish ζ from its
sign twins, so separation must come from archimedean interaction or from finer cancellation. The heat-flow dissipation
law is the one global monotone quantity proved; it lacks an initial value. The programme maps RH onto a definite missing
inequality at a definite scale.
