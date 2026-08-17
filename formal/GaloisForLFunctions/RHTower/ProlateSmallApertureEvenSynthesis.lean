import GaloisForLFunctions.RHTower.ProlateSmallApertureGramBridge

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Reflection parity of physical monomials. -/
theorem complexUnitBandReflection_physicalComplexMonomialL2 (j : ℕ) :
    complexUnitBandReflection (physicalComplexMonomialL2 j) =
      ((((-1 : ℝ) ^ j : ℝ) : ℂ) • physicalComplexMonomialL2 j) := by
  apply Lp.ext
  have hmono := (physicalComplexMonomialL2_coeFn j).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [complexUnitBandReflection_ae (physicalComplexMonomialL2 j),
    hmono, physicalComplexMonomialL2_coeFn j,
    Lp.coeFn_smul ((((-1 : ℝ) ^ j : ℝ) : ℂ))
      (physicalComplexMonomialL2 j)] with x href hneg hx hsmul
  have hneg' :
      (physicalComplexMonomialL2 j : UnitPhysicalInterval → ℂ)
          (unitIntervalNeg x) =
        ((((unitIntervalNeg x : UnitPhysicalInterval) : ℝ) ^ j : ℝ) : ℂ) := by
    simpa only [Function.comp_apply] using hneg
  rw [href, hneg', hsmul, Pi.smul_apply, hx]
  simp only [unitIntervalNeg, smul_eq_mul]
  push_cast
  rw [neg_pow]

/-- Odd physical moments vanish on the actual complex even carrier. -/
theorem inner_physicalComplexMonomialL2_even_eq_zero
    {j : ℕ} (hj : Odd j) (f : complexUnitBandEvenSubspace) :
    inner ℂ (physicalComplexMonomialL2 j) (f : ComplexUnitIntervalL2) = 0 := by
  have hinner := complexUnitBandReflectionIsometry.inner_map_map
    (physicalComplexMonomialL2 j) (f : ComplexUnitIntervalL2)
  change inner ℂ (complexUnitBandReflection (physicalComplexMonomialL2 j))
      (complexUnitBandReflection (f : ComplexUnitIntervalL2)) = _ at hinner
  rw [complexUnitBandReflection_physicalComplexMonomialL2,
    (mem_complexUnitBandEvenSubspace_iff _).mp f.2, inner_smul_left] at hinner
  have hsign : ((-1 : ℝ) ^ j : ℝ) = -1 := Odd.neg_one_pow hj
  rw [hsign] at hinner
  have hneg : -inner ℂ (physicalComplexMonomialL2 j)
      (f : ComplexUnitIntervalL2) =
      inner ℂ (physicalComplexMonomialL2 j)
        (f : ComplexUnitIntervalL2) := by
    simpa using hinner
  let z := inner ℂ (physicalComplexMonomialL2 j)
    (f : ComplexUnitIntervalL2)
  have htwo : (2 : ℂ) * z = 0 := by
    calc
      (2 : ℂ) * z = z + z := by ring
      _ = z + (-z) := congrArg (z + ·) hneg.symm
      _ = 0 := add_neg_cancel z
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Operator-valued Taylor coefficient of the undeflated aperture synthesis. -/
noncomputable def apertureMomentPowerSynthesisCoeff (j : ℕ) :
    UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 :=
  apertureMomentSynthesisMap
    (apertureMomentFieldToL2 (apertureMomentFieldCoeff 0 j))

theorem apertureMomentPowerSynthesisCoeff_apply (j : ℕ)
    (f : UnitPhysicalScalarL2) :
    apertureMomentPowerSynthesisCoeff j f =
      inner ℂ (physicalComplexMonomialL2 j) f •
        fourierGroundVector 1 (apertureMomentResidual 0) j := by
  rw [apertureMomentPowerSynthesisCoeff, apertureMomentSynthesisMap_apply,
    l2Synthesis_apply]
  let q : UnitApertureL2 :=
    fourierGroundVector 1 (apertureMomentResidual 0) j
  have hfield :
      (apertureMomentFieldToL2 (apertureMomentFieldCoeff 0 j) :
          UnitPhysicalInterval → UnitApertureL2) =ᵐ[volume]
        fun x => (((x : ℝ) ^ j : ℝ) : ℂ) • q := by
    have h := ContinuousMap.coeFn_toLp
      (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure UnitPhysicalInterval))
      (apertureMomentFieldCoeff 0 j)
    simpa [apertureMomentFieldToL2, apertureMomentFieldCoeff, q] using h
  calc
    (∫ x, f x •
        (apertureMomentFieldToL2 (apertureMomentFieldCoeff 0 j)) x
          ∂(volume : Measure UnitPhysicalInterval)) =
        ∫ x, (f x * (((x : ℝ) ^ j : ℝ) : ℂ)) • q
          ∂(volume : Measure UnitPhysicalInterval) := by
      apply integral_congr_ae
      filter_upwards [hfield] with x hx
      rw [hx, smul_smul]
    _ = (∫ x, f x * (((x : ℝ) ^ j : ℝ) : ℂ)
          ∂(volume : Measure UnitPhysicalInterval)) • q := by
      rw [integral_smul_const]
    _ = inner ℂ (physicalComplexMonomialL2 j) f • q := by
      congr 1
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [physicalComplexMonomialL2_coeFn j] with x hx
      rw [hx]
      simp [RCLike.inner_apply, mul_comm]

/-- Real scalar multiplication on rectangular aperture operators agrees with
complex multiplication by the embedded real scalar. -/
theorem ofReal_smul_apertureMomentOperator (r : ℝ)
    (T : UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2) :
    (r : ℂ) • T = r • T := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (r : ℂ) (T f), Lp.coeFn_smul r (T f)]
    with x hx hy
  rw [smul_apply, smul_apply, hx, hy, Pi.smul_apply, Pi.smul_apply]
  exact Complex.real_smul.symm

theorem hasSum_apertureMomentFourierSynthesis_coeff (c : ℝ) :
    HasSum (fun j : ℕ => ((c : ℂ) ^ j •
      apertureMomentPowerSynthesisCoeff j))
      (apertureMomentFourierSynthesis 0 c) := by
  have hfield := (hasSum_apertureMomentFourierField 0 c).mapL
    apertureMomentFieldToL2
  have hsynth := hfield.mapL apertureMomentSynthesisMap
  refine hsynth.congr_fun (fun j => ?_)
  rw [apertureMomentFieldToL2.map_smul_of_tower,
    apertureMomentSynthesisMap.map_smul_of_tower]
  change (c : ℂ) ^ j • apertureMomentPowerSynthesisCoeff j =
    c ^ j • apertureMomentPowerSynthesisCoeff j
  simpa only [Complex.ofReal_pow] using
    ofReal_smul_apertureMomentOperator (c ^ j)
      (apertureMomentPowerSynthesisCoeff j)

/-- Continuous restriction of rectangular operators to the actual even
physical carrier. -/
def restrictApertureMomentSynthesisCLM :
    (UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2) →L[ℂ]
      (complexUnitBandEvenSubspace →L[ℂ] UnitApertureL2) :=
  ContinuousLinearMap.flip
    (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
    (σ₁₃ := RingHom.id ℂ) (σ₂₃ := RingHom.id ℂ)
    (E := UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2)
    (F := complexUnitBandEvenSubspace →L[ℂ] UnitPhysicalScalarL2)
    (G := complexUnitBandEvenSubspace →L[ℂ] UnitApertureL2)
    (ContinuousLinearMap.compL ℂ complexUnitBandEvenSubspace
      UnitPhysicalScalarL2 UnitApertureL2)
    complexUnitBandEvenSubspace.subtypeL

/-- Taylor coefficient after restriction to the actual even carrier. -/
noncomputable def evenApertureMomentPowerSynthesisCoeff (j : ℕ) :
    complexUnitBandEvenSubspace →L[ℂ] UnitApertureL2 :=
  apertureMomentPowerSynthesisCoeff j ∘L
    complexUnitBandEvenSubspace.subtypeL

theorem evenApertureMomentPowerSynthesisCoeff_odd_eq_zero
    {j : ℕ} (hj : Odd j) :
    evenApertureMomentPowerSynthesisCoeff j = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [evenApertureMomentPowerSynthesisCoeff,
    ContinuousLinearMap.comp_apply, apertureMomentPowerSynthesisCoeff_apply]
  change inner ℂ (physicalComplexMonomialL2 j)
      (f : ComplexUnitIntervalL2) •
      fourierGroundVector 1 (apertureMomentResidual 0) j = 0
  rw [inner_physicalComplexMonomialL2_even_eq_zero hj, zero_smul]

theorem hasSum_complexEvenApertureMomentSynthesis_coeff (c : ℝ) :
    HasSum (fun j : ℕ => ((c : ℂ) ^ j •
      evenApertureMomentPowerSynthesisCoeff j))
      (complexEvenApertureMomentSynthesis c) := by
  have h := restrictApertureMomentSynthesisCLM.hasSum
    (hasSum_apertureMomentFourierSynthesis_coeff c)
  simpa [restrictApertureMomentSynthesisCLM,
    evenApertureMomentPowerSynthesisCoeff,
    complexEvenApertureMomentSynthesis] using h

theorem summable_norm_apertureMomentPowerSynthesisCoeff :
    Summable (fun j : ℕ => ‖apertureMomentPowerSynthesisCoeff j‖) := by
  let C : ℝ := ‖apertureMomentSynthesisMap‖ * ‖apertureMomentFieldToL2‖
  have hmajor : ∀ j : ℕ, ‖apertureMomentPowerSynthesisCoeff j‖ ≤
      C * ‖apertureMomentFieldCoeff 0 j‖ := by
    intro j
    calc
      ‖apertureMomentPowerSynthesisCoeff j‖ ≤
          ‖apertureMomentSynthesisMap‖ *
            ‖apertureMomentFieldToL2 (apertureMomentFieldCoeff 0 j)‖ :=
        apertureMomentSynthesisMap.le_opNorm _
      _ ≤ ‖apertureMomentSynthesisMap‖ *
          (‖apertureMomentFieldToL2‖ *
            ‖apertureMomentFieldCoeff 0 j‖) := by
        gcongr
        exact apertureMomentFieldToL2.le_opNorm _
      _ = C * ‖apertureMomentFieldCoeff 0 j‖ := by
        dsimp [C]
        ring
  exact Summable.of_nonneg_of_le
    (fun j => norm_nonneg (apertureMomentPowerSynthesisCoeff j))
    hmajor ((summable_norm_apertureMomentFieldCoeff 0).mul_left C)

theorem summable_norm_evenApertureMomentPowerSynthesisCoeff :
    Summable (fun j : ℕ => ‖evenApertureMomentPowerSynthesisCoeff j‖) := by
  let C : ℝ := ‖complexUnitBandEvenSubspace.subtypeL‖
  have hmajor : ∀ j : ℕ, ‖evenApertureMomentPowerSynthesisCoeff j‖ ≤
      C * ‖apertureMomentPowerSynthesisCoeff j‖ := by
    intro j
    calc
      ‖evenApertureMomentPowerSynthesisCoeff j‖ ≤
          ‖apertureMomentPowerSynthesisCoeff j‖ * C := by
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ = C * ‖apertureMomentPowerSynthesisCoeff j‖ := by ring
  exact Summable.of_nonneg_of_le
    (fun j => norm_nonneg (evenApertureMomentPowerSynthesisCoeff j))
    hmajor (summable_norm_apertureMomentPowerSynthesisCoeff.mul_left C)

/-- Taylor truncation through degree `2n-1` on the even carrier. -/
noncomputable def complexEvenApertureMomentTaylorHead (n : ℕ) (c : ℝ) :
    complexUnitBandEvenSubspace →L[ℂ] UnitApertureL2 :=
  ∑ j ∈ Finset.range (2 * n),
    ((c : ℂ) ^ j • evenApertureMomentPowerSynthesisCoeff j)

theorem hasRectRankLE_complexEvenApertureMomentTaylorHead
    (n : ℕ) (c : ℝ) :
    HasRectRankLE (complexEvenApertureMomentTaylorHead n c) n := by
  classical
  let q : Fin n → UnitApertureL2 := fun i =>
    fourierGroundVector 1 (apertureMomentResidual 0) (2 * (i : ℕ))
  let V : Submodule ℂ UnitApertureL2 := Submodule.span ℂ (Set.range q)
  have hdim : Module.finrank ℂ V ≤ n := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range q)) ≤ n
    refine (finrank_span_le_card (R := ℂ) (Set.range q)).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  refine ⟨V, FiniteDimensional.span_of_finite ℂ (Set.finite_range q), hdim, ?_⟩
  intro f
  rw [complexEvenApertureMomentTaylorHead,
    sum_apply]
  exact Submodule.sum_mem V fun j hj => by
    simp only [Finset.mem_range] at hj
    by_cases heven : Even j
    · obtain ⟨k, rfl⟩ := heven
      have hk : k < n := by omega
      rw [smul_apply,
        evenApertureMomentPowerSynthesisCoeff,
        ContinuousLinearMap.comp_apply,
        apertureMomentPowerSynthesisCoeff_apply]
      have hq : fourierGroundVector 1 (apertureMomentResidual 0) (k + k) ∈ V :=
        Submodule.subset_span ⟨⟨k, hk⟩, by simp [q, two_mul]⟩
      exact V.smul_mem _ (V.smul_mem _ hq)
    · have hodd : Odd j := Nat.not_even_iff_odd.mp heven
      rw [evenApertureMomentPowerSynthesisCoeff_odd_eq_zero hodd,
        smul_zero, zero_apply]
      exact V.zero_mem

/-- An absolutely summable complex vector power series has a uniform shifted
tail on the closed unit disc. -/
theorem norm_tsum_shifted_complexPower_smul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℕ → E) (hu : Summable fun j => ‖u j‖) (r : ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖∑' j : ℕ, z ^ (j + r) • u (j + r)‖ ≤
      ‖z‖ ^ r * ∑' j : ℕ, ‖u j‖ := by
  have huShift : Summable (fun j : ℕ => ‖u (j + r)‖) := by
    exact (summable_nat_add_iff (f := fun j : ℕ => ‖u j‖) r).mpr hu
  have hterm : ∀ j : ℕ,
      ‖z ^ (j + r) • u (j + r)‖ ≤ ‖z‖ ^ r * ‖u (j + r)‖ := by
    intro j
    have hpow : ‖z‖ ^ j ≤ 1 :=
      (pow_le_one₀ (norm_nonneg z) hz : ‖z‖ ^ j ≤ 1)
    calc
      ‖z ^ (j + r) • u (j + r)‖ =
          ‖z‖ ^ j * ‖z‖ ^ r * ‖u (j + r)‖ := by
            rw [norm_smul, norm_pow, pow_add]
      _ ≤ 1 * ‖z‖ ^ r * ‖u (j + r)‖ := by gcongr
      _ = ‖z‖ ^ r * ‖u (j + r)‖ := by ring
  have hnorm : Summable (fun j : ℕ => ‖z ^ (j + r) • u (j + r)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      hterm (huShift.mul_left (‖z‖ ^ r))
  have hshiftle : (∑' j : ℕ, ‖u (j + r)‖) ≤ ∑' j : ℕ, ‖u j‖ := by
    have hs := hu.sum_add_tsum_nat_add r
    have hhead : 0 ≤ ∑ j ∈ Finset.range r, ‖u j‖ := by positivity
    linarith
  calc
    ‖∑' j : ℕ, z ^ (j + r) • u (j + r)‖ ≤
        ∑' j : ℕ, ‖z ^ (j + r) • u (j + r)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, ‖z‖ ^ r * ‖u (j + r)‖ :=
      hnorm.tsum_le_tsum hterm (huShift.mul_left (‖z‖ ^ r))
    _ = ‖z‖ ^ r * ∑' j : ℕ, ‖u (j + r)‖ := tsum_mul_left
    _ ≤ ‖z‖ ^ r * ∑' j : ℕ, ‖u j‖ :=
      mul_le_mul_of_nonneg_left hshiftle (pow_nonneg (norm_nonneg z) r)

set_option maxHeartbeats 2000000 in
/-- Uniform even Taylor-tail estimate: rank `n` removes every power below
`2n`, because odd coefficients vanish on the even carrier. -/
theorem norm_complexEvenApertureMomentSynthesis_sub_taylorHead_le
    (n : ℕ) {c : ℝ} (hc : |c| ≤ 1) :
    ‖complexEvenApertureMomentSynthesis c -
        complexEvenApertureMomentTaylorHead n c‖ ≤
      |c| ^ (2 * n) *
        ∑' j : ℕ, ‖evenApertureMomentPowerSynthesisCoeff j‖ := by
  have hsum := hasSum_complexEvenApertureMomentSynthesis_coeff c
  have hsplit := hsum.summable.sum_add_tsum_nat_add (2 * n)
  rw [hsum.tsum_eq] at hsplit
  have hdecomp :
      complexEvenApertureMomentTaylorHead n c +
          ∑' j : ℕ, (c : ℂ) ^ (j + 2 * n) •
            evenApertureMomentPowerSynthesisCoeff (j + 2 * n) =
        complexEvenApertureMomentSynthesis c := by
    simpa [complexEvenApertureMomentTaylorHead, Nat.add_comm]
      using hsplit
  have hdiff :
      complexEvenApertureMomentSynthesis c -
          complexEvenApertureMomentTaylorHead n c =
        ∑' j : ℕ, (c : ℂ) ^ (j + 2 * n) •
          evenApertureMomentPowerSynthesisCoeff (j + 2 * n) := by
    rw [← hdecomp]
    abel
  rw [hdiff]
  simpa [Complex.norm_real, Real.norm_eq_abs] using
    norm_tsum_shifted_complexPower_smul_le
      evenApertureMomentPowerSynthesisCoeff
      summable_norm_evenApertureMomentPowerSynthesisCoeff (2 * n)
      (z := (c : ℂ)) (by simpa [Complex.norm_real, Real.norm_eq_abs] using hc)

/-- The `n`th rectangular singular rung of the actual even synthesis has
upper order `|c|^(2n)`. -/
theorem exists_pos_eventually_rectApproxNumber_complexEven_upper (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
        rectApproxNumber (complexEvenApertureMomentSynthesis c) n ≤
          D * |c| ^ (2 * n) := by
  let M : ℝ := ∑' j : ℕ, ‖evenApertureMomentPowerSynthesisCoeff j‖
  let D : ℝ := M + 1
  have hM : 0 ≤ M := by
    dsimp [M]
    exact tsum_nonneg fun j =>
      norm_nonneg (evenApertureMomentPowerSynthesisCoeff j)
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  have hsmallNhd : ∀ᶠ c : ℝ in nhds (0 : ℝ), |c| ≤ 1 := by
    filter_upwards
      [(Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
      with c hc
    simpa [Real.dist_eq] using hc
  filter_upwards [hsmallNhd.filter_mono nhdsWithin_le_nhds] with c hc
  calc
    rectApproxNumber (complexEvenApertureMomentSynthesis c) n ≤
        ‖complexEvenApertureMomentSynthesis c -
          complexEvenApertureMomentTaylorHead n c‖ :=
      rectApproxNumber_le _ _ _
        (hasRectRankLE_complexEvenApertureMomentTaylorHead n c)
    _ ≤ M * |c| ^ (2 * n) := by
      rw [mul_comm]
      simpa [M] using
        norm_complexEvenApertureMomentSynthesis_sub_taylorHead_le n hc
    _ ≤ D * |c| ^ (2 * n) := by
      gcongr
      dsimp [D]
      linarith

/-- The degree-`2i` physical monomial as a vector of the actual even carrier. -/
noncomputable def physicalComplexEvenMonomialL2 (i : ℕ) :
    complexUnitBandEvenSubspace :=
  ⟨physicalComplexMonomialL2 (2 * i), by
    rw [mem_complexUnitBandEvenSubspace_iff,
      complexUnitBandReflection_physicalComplexMonomialL2]
    simp⟩

theorem linearIndependent_physicalComplexEvenMonomialL2 :
    LinearIndependent ℂ physicalComplexEvenMonomialL2 := by
  apply LinearIndependent.of_comp complexUnitBandEvenSubspace.subtype
  have h := linearIndependent_physicalComplexMonomialL2.comp
    (fun i : ℕ => 2 * i) (by intro i j hij; dsimp at hij; omega)
  simpa [Function.comp_def, physicalComplexEvenMonomialL2] using h

/-- Span of the first `k` even physical monomials inside the actual even
prolate carrier. -/
def physicalEvenMomentSpan (k : ℕ) :
    Submodule ℂ complexUnitBandEvenSubspace :=
  Submodule.span ℂ
    (Set.range fun i : Fin k => physicalComplexEvenMonomialL2 (i : ℕ))

noncomputable instance physicalEvenMomentSpan_finiteDimensional (k : ℕ) :
    FiniteDimensional ℂ (physicalEvenMomentSpan k) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem finrank_physicalEvenMomentSpan (k : ℕ) :
    Module.finrank ℂ (physicalEvenMomentSpan k) = k := by
  rw [physicalEvenMomentSpan]
  change Module.finrank ℂ (Submodule.span ℂ
    (Set.range (physicalComplexEvenMonomialL2 ∘ fun i : Fin k => (i : ℕ)))) = k
  rw [finrank_span_eq_card
    (linearIndependent_physicalComplexEvenMonomialL2.comp
      (fun i : Fin k => (i : ℕ)) (fun i j h => Fin.ext h)), Fintype.card_fin]

/-- Joint leading jet of the first `n+1` even moment rungs. -/
noncomputable def leadingEvenMomentJet (n : ℕ) :
    physicalEvenMomentSpan (n + 1) →ₗ[ℂ]
      (Fin (n + 1) → UnitApertureL2) where
  toFun f i := apertureMomentLeadingSynthesis (2 * (i : ℕ))
    ((f : complexUnitBandEvenSubspace) : ComplexUnitIntervalL2)
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

theorem leadingEvenMomentJet_injective (n : ℕ) :
    Function.Injective (leadingEvenMomentJet n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have hmoment : ∀ i : Fin (n + 1),
      inner ℂ (physicalComplexEvenMonomialL2 (i : ℕ))
        (f : complexUnitBandEvenSubspace) = 0 := by
    intro i
    have hi := congrFun hf i
    change apertureMomentLeadingSynthesis (2 * (i : ℕ))
      ((f : complexUnitBandEvenSubspace) : ComplexUnitIntervalL2) = 0 at hi
    rw [apertureMomentLeadingSynthesis_apply] at hi
    have hscalar : inner ℂ (physicalComplexMonomialL2 (2 * (i : ℕ)))
        ((f : complexUnitBandEvenSubspace) : ComplexUnitIntervalL2) = 0 :=
      (smul_eq_zero.mp hi).resolve_right
        (fourierGroundVector_apertureMomentResidual_ne_zero (2 * (i : ℕ)))
    exact hscalar
  have hself : inner ℂ (f : complexUnitBandEvenSubspace)
      (f : complexUnitBandEvenSubspace) = 0 := by
    refine Submodule.span_induction
      (p := fun g _ => inner ℂ g
        (f : complexUnitBandEvenSubspace) = 0)
      ?_ (by simp) ?_ ?_ f.property
    · rintro g ⟨i, rfl⟩
      exact hmoment i
    · intro x y hx hy hix hiy
      rw [inner_add_left, hix, hiy, add_zero]
    · intro c x hx hix
      rw [inner_smul_left, hix, mul_zero]
  apply Subtype.ext
  exact inner_self_eq_zero.mp hself

/-- Matching lower power law for every rectangular rung of the actual even
moment synthesis. -/
theorem exists_pos_eventually_rectApproxNumber_complexEven_lower (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
        C * |c| ^ (2 * n) ≤
          rectApproxNumber (complexEvenApertureMomentSynthesis c) n := by
  classical
  obtain ⟨K, hKpos, hanti⟩ :=
    @LinearMap.exists_antilipschitzWith
      ℂ inferInstance
      (physicalEvenMomentSpan (n + 1)) inferInstance
      (physicalEvenMomentSpan (n + 1)).normedSpace
      (Fin (n + 1) → UnitApertureL2) inferInstance Pi.normedSpace
      inferInstance (physicalEvenMomentSpan_finiteDimensional (n + 1))
      (leadingEvenMomentJet n)
      (LinearMap.ker_eq_bot.mpr (leadingEvenMomentJet_injective n))
  let C : ℝ := (K : ℝ)⁻¹ / 2
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  have hcloseEach : ∀ i : Fin (n + 1),
      ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
        ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c -
          apertureMomentLeadingSynthesis (2 * (i : ℕ))‖ < C := by
    intro i
    have hzero := (tendsto_iff_norm_sub_tendsto_zero).mp
      (tendsto_normalizedApertureMomentSynthesis (2 * (i : ℕ)))
    exact hzero.eventually_lt_const hCpos
  have hclose : ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
      ∀ i : Fin (n + 1),
        ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c -
          apertureMomentLeadingSynthesis (2 * (i : ℕ))‖ < C :=
    Filter.eventually_all.mpr hcloseEach
  have hsmallNhd : ∀ᶠ c : ℝ in nhds (0 : ℝ), |c| < 1 := by
    filter_upwards
      [(Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
      with c hc
    simpa [Real.dist_eq] using hc
  have hsmall : ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, |c| < 1 :=
    hsmallNhd.filter_mono nhdsWithin_le_nhds
  filter_upwards [hclose, hsmall, self_mem_nhdsWithin]
    with c hcclose hcsmall hc0
  have hcne : c ≠ 0 := by simpa using hc0
  refine le_rectApproxNumber_of_subspace
    (physicalEvenMomentSpan (n + 1)) ?_ ?_
  · rw [finrank_physicalEvenMomentSpan]
  · intro w hw
    let wf : physicalEvenMomentSpan (n + 1) := ⟨w, hw⟩
    have hjet : (K : ℝ)⁻¹ * ‖w‖ ≤ ‖leadingEvenMomentJet n wf‖ := by
      calc
        (K : ℝ)⁻¹ * ‖w‖ = (K : ℝ)⁻¹ * dist wf 0 := by
          rw [dist_zero_right]
          rfl
        _ ≤ dist (leadingEvenMomentJet n wf)
            (leadingEvenMomentJet n 0) := hanti.mul_le_dist wf 0
        _ = ‖leadingEvenMomentJet n wf‖ := by
          rw [LinearMap.map_zero, dist_zero_right]
    obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (leadingEvenMomentJet n wf)).1
    have hlead : (K : ℝ)⁻¹ * ‖w‖ ≤
        ‖apertureMomentLeadingSynthesis (2 * (i : ℕ))
          (w : ComplexUnitIntervalL2)‖ := by
      calc
        (K : ℝ)⁻¹ * ‖w‖ ≤ ‖leadingEvenMomentJet n wf‖ := hjet
        _ = ‖leadingEvenMomentJet n wf i‖ := hi.symm
        _ = ‖apertureMomentLeadingSynthesis (2 * (i : ℕ))
            (w : ComplexUnitIntervalL2)‖ := rfl
    have hdiff :
        ‖apertureMomentLeadingSynthesis (2 * (i : ℕ))
            (w : ComplexUnitIntervalL2) -
          normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
            (w : ComplexUnitIntervalL2)‖ ≤ C * ‖w‖ := by
      calc
        _ = ‖(normalizedApertureMomentSynthesis (2 * (i : ℕ)) c -
              apertureMomentLeadingSynthesis (2 * (i : ℕ)))
            (w : ComplexUnitIntervalL2)‖ := by
          rw [sub_apply, norm_sub_rev]
        _ ≤ ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c -
              apertureMomentLeadingSynthesis (2 * (i : ℕ))‖ * ‖w‖ :=
          (normalizedApertureMomentSynthesis (2 * (i : ℕ)) c -
            apertureMomentLeadingSynthesis (2 * (i : ℕ))).le_opNorm _
        _ ≤ C * ‖w‖ :=
          mul_le_mul_of_nonneg_right (hcclose i).le (norm_nonneg w)
    have htri :
        ‖apertureMomentLeadingSynthesis (2 * (i : ℕ))
            (w : ComplexUnitIntervalL2)‖ ≤
          ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
            (w : ComplexUnitIntervalL2)‖ + C * ‖w‖ := by
      calc
        _ = ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
              (w : ComplexUnitIntervalL2) +
            (apertureMomentLeadingSynthesis (2 * (i : ℕ))
                (w : ComplexUnitIntervalL2) -
              normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
                (w : ComplexUnitIntervalL2))‖ := by
          congr 1
          abel
        _ ≤ ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
              (w : ComplexUnitIntervalL2)‖ +
            ‖apertureMomentLeadingSynthesis (2 * (i : ℕ))
                (w : ComplexUnitIntervalL2) -
              normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
                (w : ComplexUnitIntervalL2)‖ := norm_add_le _ _
        _ ≤ ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
              (w : ComplexUnitIntervalL2)‖ + C * ‖w‖ :=
          add_le_add le_rfl hdiff
    have hnormalized : C * ‖w‖ ≤
        ‖normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
          (w : ComplexUnitIntervalL2)‖ := by
      have hcomb := hlead.trans htri
      dsimp [C] at hcomb ⊢
      linarith
    have hrescale :
        apertureMomentFourierSynthesis (2 * (i : ℕ)) c
            (w : ComplexUnitIntervalL2) =
          (c ^ (2 * (i : ℕ))) •
            normalizedApertureMomentSynthesis (2 * (i : ℕ)) c
              (w : ComplexUnitIntervalL2) := by
      change apertureMomentFourierSynthesis (2 * (i : ℕ)) c
          (w : ComplexUnitIntervalL2) =
        (c ^ (2 * (i : ℕ))) •
          (((c ^ (2 * (i : ℕ)))⁻¹ •
            apertureMomentFourierSynthesis (2 * (i : ℕ)) c)
              (w : ComplexUnitIntervalL2))
      rw [smul_apply, smul_smul,
        mul_inv_cancel₀ (pow_ne_zero _ hcne), one_smul]
    have hdeflated : C * |c| ^ (2 * (i : ℕ)) * ‖w‖ ≤
        ‖apertureMomentFourierSynthesis (2 * (i : ℕ)) c
          (w : ComplexUnitIntervalL2)‖ := by
      rw [hrescale, norm_smul, Real.norm_eq_abs, abs_pow]
      have hmul := mul_le_mul_of_nonneg_left hnormalized
        (pow_nonneg (abs_nonneg c) (2 * (i : ℕ)))
      nlinarith
    have hcontract :
        ‖apertureMomentResidual (2 * (i : ℕ))
          (apertureMomentFourierSynthesis 0 c
            (w : ComplexUnitIntervalL2))‖ ≤
        ‖apertureMomentFourierSynthesis 0 c
          (w : ComplexUnitIntervalL2)‖ := by
      rw [apertureMomentResidual_apply,
        ← (apertureMomentSpan (2 * (i : ℕ))).starProjection_orthogonal_val]
      exact (apertureMomentSpan (2 * (i : ℕ))).orthogonal
        |>.norm_starProjection_apply_le _
    have hfull : C * |c| ^ (2 * (i : ℕ)) * ‖w‖ ≤
        ‖apertureMomentFourierSynthesis 0 c
          (w : ComplexUnitIntervalL2)‖ := by
      apply hdeflated.trans
      rw [apertureMomentFourierSynthesis_eq_residual_comp,
        ContinuousLinearMap.comp_apply]
      exact hcontract
    have hpow : |c| ^ (2 * n) ≤ |c| ^ (2 * (i : ℕ)) :=
      pow_le_pow_of_le_one (abs_nonneg c) hcsmall.le (by omega)
    change C * |c| ^ (2 * n) * ‖w‖ ≤
      ‖apertureMomentFourierSynthesis 0 c
        (w : ComplexUnitIntervalL2)‖
    calc
      C * |c| ^ (2 * n) * ‖w‖ ≤
          C * |c| ^ (2 * (i : ℕ)) * ‖w‖ := by gcongr
      _ ≤ ‖apertureMomentFourierSynthesis 0 c
          (w : ComplexUnitIntervalL2)‖ := hfull

/-- Two-sided small-aperture power law for every singular rung of the actual
even synthesis. -/
theorem exists_pos_eventually_rectApproxNumber_complexEven_twoSided (n : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
        C * |c| ^ (2 * n) ≤
            rectApproxNumber (complexEvenApertureMomentSynthesis c) n ∧
          rectApproxNumber (complexEvenApertureMomentSynthesis c) n ≤
            D * |c| ^ (2 * n) := by
  obtain ⟨C, hC, hlower⟩ :=
    exists_pos_eventually_rectApproxNumber_complexEven_lower n
  obtain ⟨D, hD, hupper⟩ :=
    exists_pos_eventually_rectApproxNumber_complexEven_upper n
  refine ⟨C, D, hC, hD, ?_⟩
  filter_upwards [hlower, hupper] with c hcLower hcUpper
  exact ⟨hcLower, hcUpper⟩


end GaloisForLFunctions.RHTower
