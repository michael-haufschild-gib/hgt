# ULF-OISM-1 — Lean certification record

Card: `infinite-orbit-defect-induction-essentialization-information-amplification-and-selection-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules (all new)

| Module | Card sections |
|---|---|
| `GaloisForLFunctions.HTGeometry.OrbitInductionEssentialization` | §2, §3, §4, §9 (Prediction 9.1), §10 (item 6) |
| `GaloisForLFunctions.HTGeometry.OrbitInductionInformation` | §5, §6, §7 |
| `GaloisForLFunctions.RHTower.OrbitReciprocalTimeBand` | §9 (Theorem 9.2) |

The two `HTGeometry` modules are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`, which `GaloisForLFunctions.HTGeometry`
imports; the `RHTower` module is imported by `GaloisForLFunctions.RHTower`.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(OI.2)`–`(OI.4)` orbit induction | `orbitBlock` (`D_i = V_i D U_i⁻¹`), `norm_orbitBlock`, `orbitInduction` on `lp (fun _ : I => H) 2 →L[ℂ] lp (fun _ : I => K) 2`, `orbitInduction_apply`, `orbitInduction_single` |
| **Theorem 2.1 (1)**, `(OI.5)` | `norm_orbitInduction_le`, `norm_orbitInduction` (`‖Ind D‖ = ‖D‖`) |
| **Theorem 2.1 (2)**, `(OI.6)` | `orbitInduction_eq_zero_iff`, `mem_ker_orbitBlock_iff`, `mem_ker_orbitBlock_orthogonal_iff`, `coeFn_mem_ker_orthogonal`, `mem_ker_orbitInduction_orthogonal_single` |
| **Theorem 2.1 (3)(4)**, `(OI.7)` | `le_norm_orbitInduction_of_le_norm`, `hasTransverseLowerBound_orbitInduction_iff`, `isClosed_range_orbitInduction_iff` |
| **Theorem 2.1 (5)** adjoint side | `adjoint_orbitInduction` (the adjoint of an induction is the induction of the adjoint with `U`, `V` exchanged) |
| **Corollary 2.2 (1)** | `orbitInduction_injective_iff`, `exists_lower_bound_orbitInduction_iff` |
| **Corollary 2.2 (2)** | `orbitInduction_surjective_iff` (built from `exists_nonlinearRightInverse_of_surjective`, with the `Memℓp` estimate for the assembled preimage) |
| **Corollary 2.2 (3)** | `orbitInduction_bijective_iff` |
| **Theorem 3.1**, `(OI.8)`, `(OI.9)` | `rectEssentialNorm`, `norm_le_norm_sub_of_isCompactOperator`, `rectEssentialNorm_orbitInduction`, `isCompactOperator_orbitInduction_iff`; escape sequence `orbitEscape`, `norm_orbitEscape`, `weaklyNull_orbitEscape`, `norm_orbitInduction_orbitEscape` |
| **Corollary 3.2**, `(OI.11)` | the same pair: `rectEssentialNorm_orbitInduction` is `‖q_glob(Ind D)‖ = ‖D‖` while every `q_loc(D_i)` vanishes when `D` is compact |
| **Corollary 4.1**, `(OI.12)` | `orthonormal_orbitEscape`, `orthonormal_lp_single_const`, `not_finiteDimensional_of_orthonormal`, `not_finiteDimensional_ker_orbitInduction`, `not_finiteDimensional_range_orbitInduction` |
| **Theorem 4.2**, `(OI.G1)`–`(OI.G3)` | `gram_orbitInduction` (`Ind(D)* Ind(D) = Ind_{U,U}(D*D)`, the output unitaries vanish), `rectEssentialNorm_gram_orbitInduction` (`= ‖D‖²`) |
| `(OI.13)`–`(OI.15)` packets | `orbitPacket`, `splitPacketLaw` (corpus), `isProbabilityMeasure_splitPacketLaw` |
| **Theorem 5.1**, `(OI.16)`–`(OI.18)` | `klDiv_orbitPacket` (`= n · D(P‖Q)`), `klDiv_orbitPacket_recovery`, `formationJeffreys_orbitPacket` |
| **Corollary 5.2**, `(OI.19)` | `eq_zero_of_forall_nat_mul_le`, `bounded_cofinal_work_iff` |
| `(OI.20)`, `(OI.21)` | `lpTwist` (a `LinearIsometryEquiv` on the Hilbert sum permuting orbit coordinates and applying the local involution), `lpTwist_apply`, `lpTwist_involutive`, `memℓp_twist` |
| **Theorem 6.1**, `(OI.22)` | `lpTwist_orbitInduction` |
| **Theorem 7.1**, `(OI.23)` | `orbit_selection_certificate` |
| **Prediction 9.1**, `(OI.25)` | `shellResidual_essentialNorm` |
| **Theorem 9.2 (1)**, `(OI.26)` | `timeBand`, `isCompactOperator_timeBand`, `timeBand_ne_zero` (with `bandProbe`, `indicatorCutoff_bandProbe`, `integrable_bandProbe`, `fourierIntegral_bandProbe_zero`, `continuous_fourierIntegral_bandProbe`) |
| **Theorem 9.2 (2)**, `(OI.27)` | `timeBand_mul_dilationCLM` |
| **Theorem 9.2 (3)** | `timeBand_aperture_product`, `timeBand_rapidity_shift` |
| **Theorem 9.2 (4)** | `fourierUnitary_indicatorCutoff_symm`, `fourierUnitary_timeBand_conj`, `adjoint_timeBand` |
| **Theorem 9.2 (5)**, `(OI.28)`, `(OI.29)` | `rapidityOrbit`, `orbitBlock_timeBand`, `rectEssentialNorm_allRapidity` |
| §10 item 6 | `rectEssentialNorm_orbitInduction_smul` |

§1 is motivation, §8 the fusion table, §11 the mechanism laws, §12 the closure; none carries a
further theorem.  §10 items 1–5 and 7 are scope remarks recording which hypotheses of the theorems
above are load-bearing (infinite orbit, homogeneous amplitude, independence in §5, no RH content);
they are the negations of hypotheses actually used, not separate claims.

## Design notes

* **`rectEssentialNorm` is new.**  The corpus's `RHTower.essentialNorm` treats endomorphisms only,
  but `Ind_I(D)` genuinely maps `ℓ²(I;H) → ℓ²(I;K)`.  The rectangular essential norm and its
  basic calculus (`rectEssentialNorm_le`, `le_rectEssentialNorm`, `rectEssentialNorm_le_norm`,
  `rectEssentialNorm_eq_zero_of_isCompactOperator`) are developed here.
* **`(OI.7)` is proved through the transverse lower bound, not through `γ` directly.**  Membership
  of `ξ` in `(ker Ind D)ᗮ` is pushed to each coordinate by testing against `lp.single 2 i v` for
  `v ∈ ker D_i` (this is `coeFn_mem_ker_orthogonal`); the converse pushes a single coordinate back
  the same way.  Closed range then follows from the corpus's
  `ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range`.
* **The essentialization is a weak-null argument, executed on `lp.single` vectors.**
  `orbitEscape U x n = lp.single 2 (natEmbedding I n) (U_{f n} x)` is orthonormal (hence weakly
  null by summability of `∑ ‖z i‖²` along an injection), is mapped by `Ind D` to a vector of norm
  exactly `‖D x‖`, and is annihilated in the limit by every compact operator.  This gives
  `‖D x‖ ≤ ‖Ind D − C‖` for every unit `x` and every compact `C`.
* **Corollary 2.2 (2) is constructive.**  Surjectivity of `Ind D` from surjectivity of `D` uses the
  Banach open-mapping `NonlinearRightInverse`; its uniform bound is exactly what makes the
  assembled preimage square-summable.
* **Theorem 9.2 reuses the corpus's Sonin `L²(ℝ)` model.**  `fourierUnitary`, `dilation`,
  `indicatorCutoff`, `fourierCutoff`, the dilation covariances `indicatorCutoff_mul_dilationCLM`
  and `fourierCutoff_mul_dilationCLM`, and the time–band compactness
  `isCompactOperator_fourierCutoff_indicatorCutoff_central` are all corpus assets; what is new
  here is the time–band operator's **nontriviality** (through the continuity of the transform of
  the aperture indicator and its value `2a` at the origin), the aperture invariants, the Fourier
  exchange, and the identification of the all-rapidity blocks with `orbitBlock`, which lets the
  abstract `(OI.9)` deliver `(OI.29)`.

## Verification

* All three modules elaborate with 0 errors and 0 warnings and build.
* `#print axioms` over every public declaration of the three modules reports only `propext`,
  `Classical.choice`, `Quot.sound`.
* 82 declarations in total.
