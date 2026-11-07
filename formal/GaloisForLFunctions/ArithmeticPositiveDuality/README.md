# ArithmeticPositiveDuality (APD)

Namespace `GaloisForLFunctions.ArithmeticPositiveDuality`; umbrella `ArithmeticPositiveDuality.lean`; 59 modules.
Every theorem is unconditional. RH enters only as one side of an `↔` (receivers) or as a proved consequence of a
hypothesis (`weil_extension_classification`).

## 1. Motivation

The explicit formula is a Poisson pair: the prime side is the characteristic function of a positive measure
unconditionally, the zero side is one exactly under RH. Everything forced about ζ so far has one shape:
positivity + an exact self-dual identity + an integer ⇒ rigidity. APD asks:

- what positivity plus self-duality plus integrality force (on measures, Beurling systems, PD functions on groups);
- which positive carriers (lattices, ℚ_{>0}, the affine group of ℚ, Meyer-source ideals) can hold Weil's
  correlation, and what extra structure (an arithmetic successor, a coupling) adds;
- how stable the forcing is when the functional equation holds only approximately.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Theta/Dirichlet transforms of a measure | `measureTheta`, `measureDirichlet`, `measureSeries`, `measureDual` | θ_ν(x) = ∫e^{−πu²x}dν, D_ν(s) = ∫u^{−s}dν, Laplace sides ∫t/(π(u²+t²))dν, ∫e^{−2πut}dν |
| Beurling measures | `mulConvPow`, `beurlingIntegerMeasure`, `riemannPrimeMeasure`; `RHTower.BeurlingSystem`, `beurlingSystemIntegerMeasure` | M = exp⋆P; Σ_{n≥2}(Λ(n)/log n)δ_n |
| Tent, self-dual pair | `tentAt`, `modTent`, `IsTentSelfDual`, `diracComb`, `dualLatticePair` | Λ = (1−|x|)⁺, 𝓕Λ = sinc²(πξ) vanishes exactly on ℤ∖{0} |
| Unit tent | `unitTent` | (1−|u−n|)⁺, partition of unity on ℤ |
| Certificate fibre | `fibreCoeff`, `channelFreq` | resonant modes mω of a nonnegative almost-periodic certificate |
| Sign character | `IsSignCharacter`, `extendByZero` | χ: H → {±1} on a subgroup, zero off H |
| PD functions | `IsPosDefOnLattice`, `IsPosDefOnGroup`, `PosDefFn`, `IsEvenPosDef` (MPG) | Gram Σc̄_aφ(x_a⁻¹x_b)c_b real ≥ 0 |
| Kronecker line | `kroneckerLine`, `archPoint` | t ↦ (γ_i t); x ↦ (x log p/2π)_p, the character u ↦ u^{ix} |
| Prime torus | `PrimeTorus`, `ratChar`, `valFinsupp`, `primeBox` | Π_p ℝ/ℤ, dual of ℚ_{>0}; valuation characters |
| Spline correlations | `splineCorr`, `twoPrimeCorr`, `ratCorr` | C(u) = W(B(·−u), B) for Weil's functional, cubic spline B |
| Curve trace sequence | `traceSeq` | τ(m) = Re Σβ_i^{|m|} |
| Prime measure | `primeMeasure` | ½ΣΛ(n)n^{−1−x}(δ_{log n} + δ_{−log n}) |
| Quantum budget | `quantumBudget` | b(η) = (√A + √(Gη))²/B |
| Affine group | `AffineGroupQ`, `dilation`, `translation`, `affSlope`, `affShift`, `posAffine`, `dilationRange` | x ↦ ax + b over ℚ |
| Induced function | `extendFromSubgroup` | PD on H extended by zero |
| Integer successor | `HasIntegerSuccessor`, `successorDensity` | φ(x ↦ x+b) = 1_ℤ(b); A_φ(q) = mass of qẐ |
| Arithmetic states | `haarState`, `heckeState`, `bcState`, `twistedHaar`, `heckeChar`, `commKernel`, `slopeWeight`, `jordan` | (nd)^{−s}1[db ∈ ℤ] for a = ±n/d; Bost–Connes state; Haar ⊗ character |
| Hecke extremal | `IsHeckeExtremal` | nd|φ(d_u)|² = 1 ∀u |
| Archimedean character | `archChar` | u^{iγ} |
| GNS | `PreGNS`, `GNSHilbert`, `gnsRep`, `gnsCyclic` | Hilbert space, unitary rep, cyclic vector of PD Φ |
| Eigenvectors, blind families | `IsArchEigen`, `IsBlindFamily`, `atomVec`, `remVec`, `atomAlpha` | π(d_u)v = u^{iγ}v; Gram α + (s−α)δ; atom projections e_γ |
| Extensions | `archExtension`, `realAffState`, `blindArchState`, `boxExtension` | affine PD functions with prescribed dilation part |
| Weil spectral measure | `weilWeight`, `weilMeasure` | ν_W = Σ_γ w_γδ_{−γ}, w_γ = μ_Λ{γ}|B̂(γ)|² |
| Meyer-source ideals | `meyerTraceBoundedIdeal` (ACS), `divisorOrderIdeal`, `orderJetSpan`, `poissonBoundary`, `criticalJetSpan`, `leftBlindIdeal`, `criticalJetReading` | sources by vanishing order at Xi zeros |
| Canonical-product tail | `xiTail` | ∏_{ρ∉F}E₁(z/z_ρ), z = (s−½)(−i) |
| Coupled trace | `coupledTrace`, `couplingMatrix`, `IsDivisorMultiplier`, `PointStable` | Σ_{a,b}tr(g_a, T_{ab}g_b); K_ρ(a,b) |
| Defect kernel | `RHTower.HamburgerStability.defectKernel`, `defectLaplace` | critical-line defect g of a functional equation |

## 3. Language

- **Positive side / spectral side**: the side positive by construction / the side whose positivity is the theorem.
- **Forcing**: an exact identity with a sum of nonnegative terms against a computable constant, then quantization.
- **Gap**: an interval around 0 with no mass. Gap and positivity on opposite sides of a self-dual pair give a lattice;
  on the same side only density.
- **Receiver**: an RH-equivalent reformulation; never an input to its own proof.
- **Successor**: the translation coordinate b ↦ φ(x ↦ x + b) of a PD function on Aff(ℚ). **Blind**: constant on b ≠ 0.
- **Archimedean / Kronecker-null**: spectral measure on ℚ_{>0} carried by / giving zero mass to the Kronecker line.
- **Atomic box**: the parameter set Π_x[0, ν{x}] of affine extensions of an atomic dilation correlation.
- **Isotropy vs blindness**: fibres at ρ, ρ* orthogonal for a coupling form vs Mellin values vanishing.

## 4. Mechanisms

**A. Positivity + self-duality rigidity**
1. Fejér tent pairing on vertical lines t = ε + iτ: series side O(√ε) (collar-blind), dual side → ∫sinc² dν, polar
   residues cancel ⇒ off-lattice mass zero.
2. Laplace transforms of the theta law; real-axis Fubini then identity theorem on Re t > 0.
3. Periodicity of the dual side ⇒ equal integer weights (HTGeometry Hamburger coefficient lemma).
4. Phragmén–Lindelöf twice (f, then f(s)(s+2)²): edge decay + finite order ⇒ strip decay.
5. Defect version: Laplace transform of the defect kernel has ‖J(t)‖ ≤ (3/2π)|t|^{−1/2}‖g‖₁; window (1−|s|)
   absorbs |t|^{−1/2}; Im β read from the theta law at x = 4.
6. Rounding: near-integer atoms + tent masses ⇒ counts; rounding multiplicative ⇒ primes map to primes.

**B. Quantization**
1. Integer PD with φ(0) = 1 ⇔ sign character (Gram splits over cosets).
2. Bohr projection onto a resonant fibre preserves nonnegativity; ℚ-independent channels split.
3. Budget arithmetic: an admissible integer order below 1 (even order below 2) is zero.

**C. Harmonic analysis on groups**
1. Fejér means on ℤ^ι + Prokhorov ⇒ Herglotz–Bochner; finite-rank stages + infinite-torus Fourier–Lévy ⇒ ℚ_{>0}.
2. log 2/log 3 ∉ ℚ ⇒ Kronecker line injective; two primes separate archimedean frequencies.
3. Induction from a subgroup: Gram forms split per coset; restriction–induction law.
4. GNS construction and completion; vector states are PD; PD closed under pointwise limits.

**D. Successor–dilation calculus**
1. Bi-invariance from φ(h) = φ(1) (three-point Gram); twisted dilation coefficients (1/d)ℤ-periodic (Bézout).
2. Hecke–Bessel Gram: nd·Σ|φ(x ↦ ux + b_i)|² ≤ 1 over classes mod (1/d)ℤ.
3. Two-scale null vector [x/m] − m⁻¹λ_mΣ[x + j/m] ⇒ multiplicativity of extremal dilation coefficients.
4. Monotone successor densities A(kq) ≤ A(q) ⇒ Mautner rigidity along u = (kq+1)/(kq) → 1.
5. Jordan totients: gcd^α = Σ J_α(d)1[d|a]1[d|b] ⇒ slope weights are PD multipliers.
6. Kakutani dichotomy for prime-Poisson products: Σp^{−2s} < ∞ ⇔ absolutely continuous to Haar.

**E. Affine spectral calculus**
1. Eigenvector covariance + block Cauchy–Schwarz ⇒ diagonal successor coefficient is one real constant.
2. Blind families: Cesàro means along injective sequences merge; their limit is an eigenvector ⇒ distinct
   frequencies and the continuous part never mix.
3. Two-prime box averages N⁻²Σ(2^a3^b)^{−iγ}π(2^a3^b)ξ converge to the projection e_γ; ‖e_γ‖² = ν{γ}.
4. Conjugation π(t_{rb}) = π_rπ(t_b)π_r⁻¹ transfers dilation continuity to the successor.
5. Real ax + b vector states on L²(0,∞): any nonzero L² wave has a nonconstant successor.

**F. Meyer source**
1. Canonical-product tails with half-Gaussian domination uniform in F; finite jet repair; Gaussian damping removed.
2. Point-supported pairing: S(g,h) = Σ m_σ ĝ(σ)conj ĥ(σ*); two-point packets reduce positivity to Re(α⟨x,y⟩_K) ≥ 0.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Positive measure on [1,∞) with Riemann's degree-one theta law is (−2Re α)Σδ_{k+1} | `measure_eq_of_measureTheta_relation`, `measure_eq_of_completed_functional_equation` | proved |
| Same from classical hypotheses: absolute convergence, completed FE, finite order (decay derived) | `measure_eq_of_completed_functional_equation_of_finiteOrder` | proved |
| Beurling selectivity: prime measure with theta law is `riemannPrimeMeasure` | `eq_riemannPrimeMeasure_of_beurling_theta_relation` | proved |
| Categorical rigidity: countable Beurling system with Riemann's FE ≅ ℤ, primes ↔ rational primes | `beurlingSystem_rigidity_of_completed_functional_equation` | proved |
| Signed self-dual coefficients: only the linear constraint Σa_n sinc²(λ_n) = 0 | `tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation` | proved |
| Quantitative Hamburger: off-lattice mass ≤ (6/π)‖g‖₁ | `integral_sinc_sq_le_of_critical_line_defect` | proved |
| Tent masses within (18/π + 4κ/π²)‖g‖₁ of 2Re β | `abs_integral_unitTent_sub_le_of_critical_line_defect` | proved |
| Approximate FE fixes integers and primes up to height ≍ ‖g‖₁^{−1/2} | `beurling_primes_of_critical_line_defect` | proved |
| Integrable FE defect, pole residue ≤1, and discrete atom masses ≥1 force the ordinary integer spectrum | `integer_spectrum_of_integrable_critical_line_defect` | proved |
| Positive integer atom masses and integrable FE defect: ordinary integer spectrum with residue 1, or residue ≥√2 | `pole_residue_gap_of_integrable_theta_defect` | proved |
| Countable Beurling system with integrable FE defect of norm ≤1/6400: exact integer spectrum and rational-prime rigidity | `beurlingSystem_rigidity_of_small_critical_line_defect` | proved |
| Poisson rigidity: positive self-dual with unit gap ⇔ comb; unit gap sharp; one-sided gap ⇒ density only | `tentSelfDual_iff_eq_smul_diracComb`, `exists_tentSelfDual_not_comb`, `measure_Icc_le_of_poissonPair` | proved |
| Integer PD functions are sign characters; isolation forces δ₀ ⇔ no 2-torsion | `intValued_posDef_iff_signCharacter`, `isolation_forces_dirac_iff` | proved |
| Fibre barrier 2cos(π/(K+2)); independent channels add nothing | `multiFrequency_purchase_le_fibre_fejer`, `independentChannel_purchase_le_fejer`, `twoChannel_joint_barrier_attained` | proved |
| Quantum budget: admissible ⇔ m ≤ b(η); b ≥ 1 (≥ 2) at η = ½ once L ≥ 2 (≥ 8) | `admissible_iff_le_quantumBudget`, `fejer_quantumBudget_half` | proved |
| Herglotz–Bochner on ℤ^ι and on ℚ_{>0} (prime torus) | `isPosDefOnLattice_iff`, `isPosDefOnGroup_posUnits_iff` | proved |
| Archimedean PD on ℚ_{>0} lives on the Kronecker line | `spectralMeasure_eq_map_archPoint` | proved |
| Kronecker decomposition f = f_arch + f_null, unique, f_arch maximal | `kronecker_decomposition`, `kronecker_decomposition_unique`, `archimedean_le_archPart` | proved |
| Positive duality of the explicit formula | `positive_duality_of_the_explicit_formula` | prime side proved; zero side ⇔ RH |
| Curves: RH ⇔ τ PD on ℤ ⇔ |τ| ≤ 2g ⇔ Hasse–Weil ⇔ Hodge index; golden datum fails | `curve_rh_tfae`, `not_isEvenPosDef_goldenDatum_traceSeq` | proved |
| Two-prime orbit: RH ⇔ twoPrimeCorr PD on ℤ² ⇔ torus measure | `riemannHypothesis_iff_exists_torusMeasure` | receiver |
| Restriction–induction; RH ⇔ ratCorr PD ⇔ affine PD extension | `exists_isPosDefOnGroup_extension_iff`, `riemannHypothesis_iff_exists_affine_posDef` | proved / receiver |
| Integer successor forces Hecke weight nd|φ(d_u)|² ≤ 1, attained by adelic Haar | `integer_successor_hecke_weight` | proved |
| Hecke state PD ⇔ s ≥ ½; spectrum Haar-AC ⇔ s > ½ (Kakutani wall) | `isPosDefOnGroup_heckeState_iff`, `heckeState_kakutani_wall` | proved |
| Bost–Connes temperature β forces exponent β/2 | `bc_successor_hecke_exponent` | proved |
| Hecke extremals = Haar twisted by unitary characters of ℚ^× | `heckeExtremal_iff` | proved |
| Mautner: ℤ-periodic successor + dilation continuous at 1 ⇒ constant successor | `translation_eq_of_continuousAt_dilation` | proved |
| Integer successor forces Kronecker-null dilation spectrum; dominates no archimedean PD | `integer_successor_kronecker_null`, `eq_zero_of_archimedean_le_integer_successor` | proved |
| Successor = blind constant + successor of the continuous dilation part | `successor_eq_blind_add_continuous`, `norm_successor_sub_le_nonatomic` | proved |
| Atomic dilation spectrum ⇒ blind successor; extensions = atomic box | `successor_blind_of_atomic`, `hasSum_affine_of_atomic`, `isPosDefOnGroup_boxExtension` | proved |
| Weil's correlation: extensions ⇒ RH and are exactly the box Π_γ[0, w_γ] | `weil_successor_blind`, `weil_extension_classification`, `weil_extension_exists` | proved |
| Nonzero absolutely continuous dilation part ⇒ visible (nonconstant) successor | `exists_nonblind_affine_extension_of_ac_part_ne_zero` | proved |
| Archimedean dilation part ⇒ successor continuous for the real topology | `tendsto_successor_of_continuousAt_dilation` | proved |
| Blind ideal closed (natural topology); closed in critical-jet topology ⇔ RH | `isClosed_meyerTraceBoundedIdeal`, `isClosed_criticalJet_iff` | proved |
| Spectral synthesis closure(E_k ⊔ R) = I_k; critical jets dense in source ⇔ RH | `closure_orderJetSpan_sup_poissonBoundary`, `closure_criticalJetSpan_sup_poissonBoundary_eq_univ_iff` | proved |
| Coupled positivity ⇒ isotropy at off-line pairs; one channel ⇒ half-blind | `coupled_isotropy`, `positive_ideal_halfBlind` | proved |
| Integer Euler norms, natural Dirichlet coefficients and linear counting coexist with exactly the zero pair 3/5 ± iγ on Re s > 1/2 away from 1 | `IntegerNormOneOff.exists_integer_norm_linear_count_one_off` | proved |
| Rational-prime Euler factors, multiplicative natural Dirichlet coefficients and positive linear counting coexist with exactly 3/5 ± iγ on Re s > 17/30 away from 1 | `RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off` | proved |
| Every finite xi-zero set with prescribed multiplicities has a nonnegative two-prime Dirichlet annihilator, constant coefficient 1, arbitrarily close to 1 uniformly on Re s ≥ 1 | `PositiveAnnihilator.exists_xi_zero_annihilator_with_multiplicities` | proved |
| Left-blind ideal is positive, strictly larger than the blind ideal unless RH | `meyerSourceTrace_nonneg_of_mem_leftBlindIdeal`, `meyerTraceBoundedIdeal_lt_leftBlindIdeal` | proved |

## 6. Tools

**Developed**
- Positive-measure theta/Laplace/Fejér machinery, with and without critical-line defect (`measureSeries_eq_of_theta_defect`).
- Phragmén–Lindelöf strip decay from finite order (`norm_le_of_edges_of_finiteOrder`).
- Group PD toolkit: induction, bi-invariance, Hermitian symmetry, limits, Jordan-totient multipliers.
- Herglotz–Bochner on ℤ^ι and the prime torus; Kronecker-line embedding; Kronecker decomposition.
- GNS spaces for any group (`GNSHilbert`, `inner_gnsCyclic_gnsRep`), weak measurability without separability
  (`measurable_inner_gnsRep`), real-scale extension of the dilation orbit (`exists_real_dilation_orbit`).
- Affine spectral calculus: eigenvector blindness, frequency non-mixing, atom projections, regularity transfer.
- Arithmetic states on Aff(ℚ): adelic Haar, Hecke, Bost–Connes, twisted Haar.
- Meyer-source synthesis via canonical-product tails; coupled trace and isotropy pairing.
- Rounding/tent counting for near-integer Beurling systems.

**To build**
- A positive structure whose integer counts intrinsic (zero-set) charge rather than inserted or pole charge.
- Successor visibility for singular continuous dilation spectra.
- Coupled scale positivity on carriers without point stability (Rankin–Selberg-type sources).
- Bochner–Schwartz theory for the Weil distribution beyond characteristic functions.
- Quantitative stability with signed or non-integrable defects.

## 7. Open questions

1. A third forcing instance inside the strip: exact identity on the Weil pair with a quantization step bounding
   intrinsic off-line charge.
2. Are singular continuous archimedean dilation spectra seen by some successor? (AC parts are, atoms are not.)
3. Which Kronecker-null spectra arise from arithmetic successors beyond Hecke and Bost–Connes; classification of
   successor-compatible dilation parts.
4. Higher degree analogues of the absolute small-defect rigidity theorem.
5. Positive crystalline measures beyond degree one.
6. Coupled positivity: which coupling matrices K_ρ arise from arithmetic operators, and whether any carrier
   forces K-isotropy to become blindness.
7. A self-dual base over Spec ℤ with nonnegative tensor-power traces (the 𝔽_q calibration has one).

## 8. Traps

| Trap | Fact |
|---|---|
| FE + positivity has many models | At degree one, discrete Beurling systems: only ζ |
| Hamburger needs strip decay as a hypothesis | Finite order suffices; decay follows by Phragmén–Lindelöf |
| Signed self-dual coefficients give rigidity | Only one linear constraint; positivity is essential |
| The FE is a self-duality of the Weil pair | On the Weil pair gap and positivity sit on the prime side: density only |
| Any gap gives a lattice | Only the unit gap; dual lattice pairs refute smaller gaps |
| Coupling channels buys more per zero | Fibre barrier; independent channels split |
| Rank-two positivity is progress | Two-prime Bochner problem is a receiver |
| A non-commutative carrier adds positivity | Affine positivity is induced from dilations |
| Prescribing the integer successor constrains Weil's correlation | It excludes it: Hecke decay, Kronecker-null spectrum, wrong regularity class |
| A Weil extension carries successor information | Only one blind parameter per critical zero |
| Closedness of the blind ideal is a critical property | Critical data make it dense |
| Positivity on a convolution ideal forces blindness | Forces isotropy/half-blindness; left-blind ideal is positive |
| Integer point counts force RH over 𝔽_q | Golden datum |
| Integer Euler norms and linear integer counting exclude a finite right zero layer | The rounded Beurling one-off has both; no Riemann functional equation is established |
| Rational-prime factors and ordinary multiplicativity exclude finite exceptional zeros | The prime-rounded one-off has both, with positive linear counting and exactly one prescribed pair on Re s > 17/30 |
| Positive finite deflating coefficients, arbitrarily close to the unit on Re s ≥ 1, exclude a finite zero layer | Every finite set of actual xi zeros admits such a two-prime annihilator |
| The adelic Haar state is "near" Weil's correlation | Its spectrum is Haar-singular and Kronecker-null |

## 9. Context

**Uses** (distinct modules imported)

| Programme | # | What |
|---|---|---|
| HTGeometry | 13 | Hamburger FE/theta defect, Bochner on ℝ, infinite-torus Fourier–Lévy, prime-Poisson screen, tail canonical products, AC autocorrelations |
| RHTower | 10 | Weil full cone (spectral measure, exposed point, sign rigidity), Deninger–Meyer source, Xi canonical product, Hamburger stability, Beurling systems |
| ArithmeticCastelnuovoSeveri | 5 | maximal blind ideal, Meyer radical, lambda ring, Frobenius span Hodge index, fake curves |
| MultiplicativePositivityGeometry | 4 | growth law, PD functions, zeta boundary divisor, arithmetic realization |
| ArithmeticOrientationGeometry | 1 | spline orbit decides the critical line |

**Used by**

| Programme | # | What |
|---|---|---|
| AdelicKreinGeometry | 5 | Hecke/Haar states, Mautner, Kakutani wall |
| ArithmeticCastelnuovoSeveri | 1 | measure Hamburger rigidity |
| StripBochnerWeilForcing | 1 | rigidity from the bare FE |
| MultiplicativePositivityGeometry | 1 | sign characters |
| BiarithmeticGeometry | 1 | Mautner phenomenon |
| ArithmeticCorrelationGeometry | 1 | Herglotz–Bochner on ℚ_{>0} |
| MainTheorems | 1 | umbrella |

| Neighbour | Relation |
|---|---|
| MultiplicativePositivityGeometry | height-side positivity; APD sharpens its barrier per fibre and quantizes its budget |
| ArithmeticCastelnuovoSeveri | owns the Meyer source and maximal blind ideal; APD adds topology, synthesis, coupled isotropy |
| ArithmeticOrientationGeometry | scale-side orientation; APD turns the two-prime orbit into a torus Bochner problem |
| StripBochnerWeilForcing | strip-side completed systems; consumes APD's FE rigidity |
| AdelicKreinGeometry | continues the affine/Hecke states into Krein index theory |
| BiarithmeticGeometry, SignedSuccessorArithmetic | successor and affine action; APD supplies Mautner rigidity |

## 10. Big picture

APD shows that positivity is a strong forcing engine exactly where it is paired with self-duality on the opposite
side and an integer: it recovers the integers, the primes and ζ itself from Riemann's functional equation, and does so
stably. But on Weil's own pair the gap and the positivity sit on the same (prime) side, so the same engine produces
only density statements and receivers. Every positive carrier tried — lattices, the prime torus, the affine group,
convolution ideals, coupled channels — either reduces to the dilation Gram (adding nothing) or, when given genuine
arithmetic structure, becomes incompatible with Weil's correlation.

The affine programme makes this precise: arithmetic successors live on the Kronecker-null, Haar-singular part of the
prime torus, Weil's correlation lives on one archimedean line, and the two never meet. The critical line appears as
a positivity threshold (Hecke s ≥ ½, Bost–Connes β = 1, Kakutani wall) of arithmetic states, not of Weil's
correlation. For the RH research this says: positivity of a carrier is not the missing ingredient; the missing
ingredient is a quantized identity that counts the zero set's own charge, and none of the positive structures built
here can supply it.
