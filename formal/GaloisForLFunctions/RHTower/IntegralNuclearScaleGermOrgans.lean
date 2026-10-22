import GaloisForLFunctions.RHTower.PhysicalPluckerThetaLift
import GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona
import GaloisForLFunctions.RHTower.PoissonScaleHistoryFrame
import GaloisForLFunctions.RHTower.BurnolCoPoissonTopConormalPluckerJuliaCayleyLanding
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature
import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMorseResolventOperatorLift

/-!
# The boundary-scale germ of the physical Plücker density and its four organs

For the normalized physical-overlap Plücker density `T` (positive, compact, injective, trace one,
`-ind C = Tr T = 1`), the scale germs `𝔢_T(c) = [ε ↦ E_ε(cT)]` of the boundary-history corona obey

* **(INBSG.9)** `‖𝔢_T(c) - 𝔢_T(d)‖ = |√c - √d|/(√c + √d)`;
* **(INBSG.15)** `‖𝔢_T(t²) - 𝔢_T(u²)‖² + P(t,u) = 1` with the literal Poisson overlap
  `P(t,u) = 4tu/(t+u)²`;
* **(INBSG.16)–(INBSG.17)** with `C = κ(A²,1) = (A-1)/(A+1)` and `G = P(A,1) = 1 - C²`: the Burnol
  holonomy `A - A⁻¹ = 4C/G`, the Gamma-six curvature `2(cosh log A - 1) = 4C²/G`, the visibility
  `√G = sech(½ log A)` and the rapidity `artanh C = ½ log A`; on actual Xi fibres these are the
  corpus Burnol and Gamma-six organs;
* **(INBSG.18)** `C = tanh(a log p/2) = (pᵃ-1)/(pᵃ+1)`; reflection `a ↦ -a` reverses `C` and fixes
  `G` and the curvature;
* **(INBSG.19)** with a spectral gap at zero (in particular for finite rank or on a
  finite-dimensional carrier) the contrast vanishes;
* **(INBSG.20)–(INBSG.21)** `𝔢_T(pᵃ) = 𝔢_T(p⁻ᵃ)` iff `a = 0`.
-/

open Filter Topology Real
open scoped InnerProductSpace
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

/-- The scale germ `𝔢_T(c)` of the normalized physical Plücker density. -/
def pluckerScaleGerm {c : ℝ} (hc : 0 < c) : BoundaryCorona GammaSewnCriticalPhysicalPluckerHilbert :=
  scaleGerm normalizedPhysicalPluckerOperator normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_isCompact hc

/-- **(INBSG.9).**  `‖𝔢_T(c) - 𝔢_T(d)‖ = |√c - √d|/(√c + √d)`. -/
theorem norm_pluckerScaleGerm_sub {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ‖pluckerScaleGerm hc - pluckerScaleGerm hd‖ = |germContrast c d| :=
  norm_scaleGerm_sub normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_isCompact normalizedPhysicalPluckerOperator_injective
    not_finiteDimensional_pluckerHilbert hc hd

/-- **(INBSG.15).**  Open nuclear scale memory squared plus closed Poisson overlap is one. -/
theorem norm_sq_pluckerScaleGerm_add_poisson {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ‖pluckerScaleGerm (pow_pos ht 2) - pluckerScaleGerm (pow_pos hu 2)‖ ^ 2 +
      poissonScaleHistoryGram t u = 1 := by
  rw [norm_pluckerScaleGerm_sub, sq_abs, poissonScaleHistoryGram_eq ht hu, germContrast,
    Real.sqrt_sq ht.le, Real.sqrt_sq hu.le]
  have htu : 0 < t + u := add_pos ht hu
  field_simp
  ring

/-- The oriented contrast at `c = A²`, `d = 1`. -/
theorem germContrast_sq_one {A : ℝ} (hA : 0 < A) : germContrast (A ^ 2) 1 = (A - 1) / (A + 1) := by
  rw [germContrast, Real.sqrt_sq hA.le, Real.sqrt_one]

theorem poissonScaleHistoryGram_one {A : ℝ} (hA : 0 < A) :
    poissonScaleHistoryGram A 1 = 1 - germContrast (A ^ 2) 1 ^ 2 := by
  rw [poissonScaleHistoryGram_eq hA one_pos, germContrast_sq_one hA]
  have : 0 < A + 1 := by linarith
  field_simp
  ring

/-- **(INBSG.17), four organs.**  Burnol holonomy, Gamma-six curvature, Poisson visibility and
rapidity are rational functions of the oriented germ coordinate. -/
theorem germContrast_four_organs {A : ℝ} (hA : 0 < A) :
    A - A⁻¹ = 4 * germContrast (A ^ 2) 1 / (1 - germContrast (A ^ 2) 1 ^ 2) ∧
      2 * (Real.cosh (Real.log A) - 1) =
        4 * germContrast (A ^ 2) 1 ^ 2 / (1 - germContrast (A ^ 2) 1 ^ 2) ∧
      Real.sqrt (poissonScaleHistoryGram A 1) = (Real.cosh (Real.log A / 2))⁻¹ ∧
      Real.artanh (germContrast (A ^ 2) 1) = Real.log A / 2 := by
  rw [germContrast_sq_one hA]
  have hA1 : 0 < A + 1 := by linarith
  have hG : 1 - ((A - 1) / (A + 1)) ^ 2 = 4 * A / (A + 1) ^ 2 := by
    field_simp
    ring
  have hcosh : Real.cosh (Real.log A) = (A + A⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_log hA, Real.exp_neg, Real.exp_log hA]
  have hsq : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA.le
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hG]
    field_simp
    ring
  · rw [hG, hcosh]
    field_simp
    ring
  · have hcosh2 : Real.cosh (Real.log A / 2) = (A + 1) / (2 * Real.sqrt A) := by
      rw [show Real.log A / 2 = Real.log (Real.sqrt A) by rw [Real.log_sqrt hA.le], Real.cosh_eq,
        Real.exp_log hsA, Real.exp_neg, Real.exp_log hsA]
      field_simp
      rw [Real.sq_sqrt hA.le]
    rw [poissonScaleHistoryGram_eq hA one_pos, hcosh2, inv_div,
      show 4 * A * 1 / (A + 1) ^ 2 = (2 * Real.sqrt A / (A + 1)) ^ 2 by
        rw [div_pow, mul_pow, sq (Real.sqrt A), hsq]; ring,
      Real.sqrt_sq (by positivity)]
  · have h := artanh_germContrast (pow_pos hA 2) one_pos
    rw [germContrast_sq_one hA, Real.log_one, sub_zero, Real.log_pow] at h
    rw [h]
    push_cast
    ring

/-- **(INBSG.18).**  At `A = pᵃ` the oriented coordinate is `tanh(a log p/2) = (pᵃ-1)/(pᵃ+1)`. -/
theorem germContrast_prime_rpow (p : Nat.Primes) (a : ℝ) :
    germContrast (((p : ℝ) ^ a) ^ 2) 1 = Real.tanh (a * Real.log (p : ℝ) / 2) ∧
      germContrast (((p : ℝ) ^ a) ^ 2) 1 = ((p : ℝ) ^ a - 1) / ((p : ℝ) ^ a + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hA : 0 < (p : ℝ) ^ a := Real.rpow_pos_of_pos hp a
  refine ⟨?_, germContrast_sq_one hA⟩
  rw [germContrast_sq_one hA, Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hexp : Real.exp (a * Real.log (p : ℝ) / 2) * Real.exp (a * Real.log (p : ℝ) / 2) =
      (p : ℝ) ^ a := by
    rw [← Real.exp_add, show a * Real.log (p : ℝ) / 2 + a * Real.log (p : ℝ) / 2 =
      Real.log (p : ℝ) * a by ring, Real.rpow_def_of_pos hp]
  have he := Real.exp_pos (a * Real.log (p : ℝ) / 2)
  rw [Real.exp_neg, ← hexp]
  field_simp

/-- On an actual right-half Xi fibre the germ coordinate is the corpus Burnol–Cayley coordinate. -/
theorem germContrast_eq_burnolXiPrimeCayleyCoordinate (q : XiZeroCopy) (p : Nat.Primes) :
    germContrast (((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1) ^ 2) 1 =
      burnolXiPrimeCayleyCoordinate q p := by
  rw [burnolXiPrimeCayleyCoordinate_eq_character_ratio, (germContrast_prime_rpow p _).2]

/-- **(INBSG.17), Burnol organ.**  On an actual right-half Xi fibre the corpus normalized Burnol
holonomy is `4C/G` in the germ coordinate. -/
theorem burnolCoPoissonNormalizedHolonomy_eq_germ (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : Nat.Primes) :
    burnolCoPoissonNormalizedHolonomy (w := (q.1 : ℂ)) (r := (p : ℝ))
        hq (xi_divisor_support_re_mem_open_unit q.1).2 ha (by exact_mod_cast p.2.one_lt) =
      4 * germContrast (((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1) ^ 2) 1 /
        (1 - germContrast (((p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1) ^ 2) 1 ^ 2) := by
  rw [burnolCoPoissonNormalizedHolonomy_eq_four_mul_cayley_div_one_sub_sq q hq ha ha1 p,
    germContrast_eq_burnolXiPrimeCayleyCoordinate]

/-- **(INBSG.17), Gamma-six organ.**  The corpus paired Gamma-six curvature at `log A` is `4C²/G`. -/
theorem sourceHorizontalGammaSixCurvature_eq_germ {A : ℝ} (hA : 0 < A) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (Real.log A) =
      4 * germContrast (A ^ 2) 1 ^ 2 / (1 - germContrast (A ^ 2) 1 ^ 2) := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  exact (germContrast_four_organs hA).2.1

/-- **(INBSG.18), reflection.**  `a ↦ -a` reverses the germ coordinate, fixes the visibility and
leaves the curvature even. -/
theorem germContrast_prime_reflection (p : Nat.Primes) (a : ℝ) :
    germContrast (((p : ℝ) ^ (-a)) ^ 2) 1 = -germContrast (((p : ℝ) ^ a) ^ 2) 1 ∧
      poissonScaleHistoryGram ((p : ℝ) ^ (-a)) 1 = poissonScaleHistoryGram ((p : ℝ) ^ a) 1 ∧
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (Real.log ((p : ℝ) ^ (-a))) =
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature (Real.log ((p : ℝ) ^ a)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hA : 0 < (p : ℝ) ^ a := Real.rpow_pos_of_pos hp a
  have hB : 0 < (p : ℝ) ^ (-a) := Real.rpow_pos_of_pos hp (-a)
  have hinv : (p : ℝ) ^ (-a) = ((p : ℝ) ^ a)⁻¹ := Real.rpow_neg hp.le a
  refine ⟨?_, ?_, ?_⟩
  · rw [germContrast_sq_one hB, germContrast_sq_one hA, hinv]
    field_simp
    ring
  · rw [poissonScaleHistoryGram_eq hB one_pos, poissonScaleHistoryGram_eq hA one_pos, hinv]
    field_simp
    ring
  · rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq, hinv, Real.log_inv, Real.cosh_neg]

/-- **(INBSG.20)–(INBSG.21).**  The direct and reflected prime scales define the same germ iff
`a = 0`. -/
theorem pluckerScaleGerm_prime_eq_iff (p : Nat.Primes) (a : ℝ) :
    pluckerScaleGerm (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < p) a) =
        pluckerScaleGerm (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos : (0 : ℝ) < p) (-a)) ↔
      a = 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hkey := norm_pluckerScaleGerm_sub (Real.rpow_pos_of_pos hp a) (Real.rpow_pos_of_pos hp (-a))
  have hiff := germContrast_eq_zero_iff (Real.rpow_pos_of_pos hp a).le
    (Real.rpow_pos_of_pos hp (-a)).le (by positivity)
  constructor
  · intro h
    rw [h, sub_self, norm_zero, eq_comm, abs_eq_zero, hiff, Real.rpow_right_inj hp hp1.ne'] at hkey
    linarith
  · rintro rfl
    simp only [neg_zero]

/-! ## (INBSG.19): gapped carriers carry no contrast -/

/-- A set of nonnegative reals whose nonzero part is finite has a gap at zero. -/
theorem exists_gap_of_finite_nonzero {s : Set ℝ} (hnn : ∀ x ∈ s, 0 ≤ x)
    (hfin : {x ∈ s | x ≠ 0}.Finite) : ∃ δ > 0, s ⊆ {0} ∪ Set.Ici δ := by
  set F := hfin.toFinset
  by_cases hF : F.Nonempty
  · have hmin := F.min'_mem hF
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hmin
    refine ⟨F.min' hF, lt_of_le_of_ne (hnn _ hmin.1) (Ne.symm hmin.2), fun x hx => ?_⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr (F.min'_le x (by simp [F, hx, hx0]))
  · refine ⟨1, one_pos, fun x hx => Or.inl ?_⟩
    by_contra hx0
    have hx0' : x ≠ 0 := hx0
    exact hF ⟨x, by simp [F, hx, hx0']⟩

/-- On a finite-dimensional carrier every positive operator has a spectral gap at zero. -/
theorem exists_spectral_gap_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {S : E →L[ℂ] E} (hS : S.IsPositive) :
    ∃ δ > 0, spectrum ℝ S ⊆ {0} ∪ Set.Ici δ := by
  have hfin : (spectrum ℝ S).Finite := by
    have hC : (spectrum ℂ S).Finite := by
      have h := Module.End.finite_spectrum ((Module.End.toContinuousLinearMap E).symm S)
      rwa [AlgEquiv.spectrum_eq] at h
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hC.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  exact exists_gap_of_finite_nonzero (fun x hx => (spectrum_subset_Icc_of_isPositive hS hx).1)
    (hfin.subset fun x hx => hx.1)

/-- A positive operator of finite rank has a spectral gap at zero: its nonzero spectral values are
eigenvalues with linearly independent eigenvectors in the finite-dimensional range. -/
theorem exists_spectral_gap_of_hasRankLE {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {S : H →L[ℂ] H} (hS : S.IsPositive) {n : ℕ}
    (hr : HasRankLE S n) : ∃ δ > 0, spectrum ℝ S ⊆ {0} ∪ Set.Ici δ := by
  obtain ⟨V, hV, hVn, hSV⟩ := hr
  have hcpt : IsCompactOperator S :=
    (memSchattenClass_of_hasRankLE one_pos ⟨V, hV, hVn, hSV⟩).isCompactOperator one_pos
  set N := {x ∈ spectrum ℝ S | x ≠ 0}
  have hNfin : N.Finite := by
    have hv : ∀ x : N, ∃ v : H, v ≠ 0 ∧ S v = ((x : ℝ) : ℂ) • v := fun x =>
      exists_eigenvector_of_mem_spectrum_real hcpt x.2.1 x.2.2
    choose v hv0 hvS using hv
    have hx0 : ∀ x : N, ((x : ℝ) : ℂ) ≠ 0 := fun x => by exact_mod_cast x.2.2
    have hvV : ∀ x : N, v x ∈ V := fun x => by
      have : v x = ((x : ℝ) : ℂ)⁻¹ • S (v x) := by
        rw [hvS, smul_smul, inv_mul_cancel₀ (hx0 x), one_smul]
      rw [this]
      exact V.smul_mem _ (hSV _)
    have hli : LinearIndependent ℂ v :=
      Module.End.eigenvectors_linearIndependent' (S : H →ₗ[ℂ] H) (fun x : N => ((x : ℝ) : ℂ))
        (fun a b hab => Subtype.ext (Complex.ofReal_injective hab)) v
        (fun x => ⟨Module.End.mem_eigenspace_iff.2 (hvS x), hv0 x⟩)
    have hliV : LinearIndependent ℂ (fun x : N => (⟨v x, hvV x⟩ : V)) :=
      LinearIndependent.of_comp V.subtype hli
    haveI := hliV.finite
    exact Set.toFinite N
  exact exists_gap_of_finite_nonzero (fun x hx => (spectrum_subset_Icc_of_isPositive hS hx).1) hNfin

/-- **(INBSG.19), finite packets.**  A positive finite-rank source carries no nuclear scale
memory: the boundary transfers at two scales merge as `ε → 0⁺`. -/
theorem tendsto_norm_scaledTransfer_sub_of_hasRankLE {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {S : H →L[ℂ] H} (hS : S.IsPositive) {n : ℕ}
    (hr : HasRankLE S n) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Tendsto (fun ε => ‖positiveBoundaryTransfer (c • S) ε - positiveBoundaryTransfer (d • S) ε‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_spectral_gap_of_hasRankLE hS hr
  exact tendsto_norm_scaledTransfer_sub_of_gap hS hc hd hδ hgap

/-- **(INBSG.19), finite-dimensional carriers.**  On a finite-dimensional carrier the boundary
transfers at two scales merge as `ε → 0⁺`: no nuclear scale memory survives. -/
theorem tendsto_norm_scaledTransfer_sub_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {S : E →L[ℂ] E} (hS : S.IsPositive)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    Tendsto (fun ε => ‖positiveBoundaryTransfer (c • S) ε - positiveBoundaryTransfer (d • S) ε‖)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_spectral_gap_of_finiteDimensional hS
  exact tendsto_norm_scaledTransfer_sub_of_gap hS hc hd hδ hgap

end RHTower.HedenmalmThetaSource
