import GaloisForLFunctions.WindowTowerOfSpecZ.TheEvenWeilFormHasAFloorAtAperture1881Over5000
import GaloisForLFunctions.WindowTowerOfSpecZ.TheOddWeilFormHasAFloorAtAperture1881Over5000
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheBlockMatricesOfShortWindowsArePositiveAtEveryBlockSize

/-!
# A positive Weil floor on the first overlap window

The even and odd floors combine by orthogonal parity splitting. Complexification
and smooth approximation transfer the same floor to the closed Weil form and to
every step packet of a window of ratio at most `53/25`.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Finset Zeta23
open _root_.RHTower
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory ArithmeticPositivityTheory SquareRootThreshold
open SpacingScaleHarmonicAnalysis AbsoluteGeometryOfSpecZ

private theorem supported_of_vanish {F : ℝ → ℝ} {a : ℝ}
    (hs : ∀ x, a < |x| → F x = 0) : tsupport F ⊆ Icc (-a) a := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  exact abs_le.mp (le_of_not_gt fun h => hx (hs x h))

/-- Every real test in the first overlap window has the floor `1/50000`. -/
theorem fullZeroForm_ge_at_aperture_1881_over_5000 {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (hs : ∀ x, (1881 / 5000 : ℝ) < |x| → F x = 0) :
    (1 / 50000 : ℝ) * (∫ x, F x ^ 2) ≤ fullZeroForm F := by
  have hse : tsupport (evenPartReal F) ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000) := by
    apply supported_of_vanish
    intro x hx
    simp only [evenPartReal, hs x hx, hs (-x) (by rwa [abs_neg]), add_zero, zero_div]
  have hso : tsupport (oddPartReal F) ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000) := by
    apply supported_of_vanish
    intro x hx
    simp only [oddPartReal, hs x hx, hs (-x) (by rwa [abs_neg]), sub_self, zero_div]
  have he := weilQuad_ge_even_at_aperture_1881_over_5000
    (contDiff_evenPartReal hF) hse (evenPartReal_neg F)
  have ho := weilQuad_ge_odd_at_aperture_1881_over_5000
    (contDiff_oddPartReal hF) hso (oddPartReal_neg F)
  rw [← fullZeroForm_eq_re_weilFullFunctional (contDiff_evenPartReal hF).continuous
    (hasCompactSupport_evenPartReal hcs)] at he
  rw [← fullZeroForm_eq_re_weilFullFunctional (contDiff_oddPartReal hF).continuous
    (hasCompactSupport_oddPartReal hcs)] at ho
  have hn : 0 ≤ ∫ x, oddPartReal F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  rw [fullZeroForm_eq_even_add_odd hF hcs, integral_sq_eq_even_add_odd hF.continuous hcs]
  linarith only [he, ho, hn]

/-- The same floor holds for complex tests, with no parity condition. -/
theorem zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000 {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f)
    (hs : tsupport f ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000)) :
    (1 / 50000 : ℝ) * (∫ x, ‖f x‖ ^ 2) ≤ (zetaZeroConfig.W f f).re :=
  zetaZeroConfig_re_W_ge_of_window
    (fun _ hF hcs hs => fullZeroForm_ge_at_aperture_1881_over_5000 hF hcs hs) hf hs

/-- The closed Weil form retains the first overlap floor at every smaller aperture. -/
theorem one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000
    {A : SuzukiPositiveAperture} (hA : A.1 ≤ (1881 / 5000 : ℝ)) :
    (1 / 50000 : ℝ) ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, hu, rfl⟩
  have hnorm : ‖suzukiWeilIntervalFormEmbedding A u.toCCMFormVector‖ =
      ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ := by
    change ‖suzukiPhysicalToApertureCLM A (ccmArchimedeanFormToAperture A u.toCCMFormVector)‖ = _
    exact (suzukiApertureL2Equiv A).symm.norm_map _
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, ‖u x‖ ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [hnorm, norm_sq_ccmArchimedeanFormToAperture_toCCMFormVector]
  have hpos : 0 < suzukiWeilIntervalFormMass A u.toCCMFormVector :=
    pow_pos (norm_pos_iff.mpr hu) 2
  unfold suzukiWeilIntervalFormRayleigh
  rw [le_div_iff₀ hpos, ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil, hmass]
  have hs : tsupport (u : ℝ → ℂ) ⊆ Icc (-(1881 / 5000 : ℝ)) (1881 / 5000) :=
    u.tsupport_subset.trans fun x hx =>
      ⟨by linarith only [hx.1, hA], by linarith only [hx.2, hA]⟩
  exact zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000
    (u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) hs

private theorem log_first_overlap_ratio_lt : Real.log (53 / 25 : ℝ) < (1881 / 2500 : ℝ) := by
  have hsq : (53 / 50 : ℝ) ≤ (1287 / 1250 : ℝ) ^ 2 := by norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 53 / 50) hsq
  rw [Real.log_pow] at hl
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1287 / 1250)
  rw [show (53 / 25 : ℝ) = 2 * (53 / 50) by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  linarith only [hl, hu, Real.log_two_lt_d9]

/-- Step packets of every window of ratio at most `53/25` have the same positive floor. -/
theorem packetForm_stepPacket_ge_of_first_overlap {R J Q : ℕ}
    (hR : 1 ≤ R) (hJ : 25 * J ≤ 28 * R) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    (1 / 50000 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
  let A : SuzukiPositiveAperture := ⟨1881 / 5000, by norm_num⟩
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hJR : ((R + J : ℕ) : ℝ) ≤ (53 / 25) * R := by
    have hJ' : (25 : ℝ) * J ≤ 28 * R := by exact_mod_cast hJ
    push_cast
    linarith only [hJ']
  have hRJp : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < R + J by omega)
  have hlog := Real.log_le_log hRJp hJR
  rw [Real.log_mul (by norm_num) hRp.ne'] at hlog
  have hlen : Real.log ((R + J : ℕ) : ℝ) - Real.log R < 1881 / 2500 := by
    linarith only [hlog, log_first_overlap_ratio_lt]
  have hlogQ : Real.log ((R + J : ℕ) : ℝ) - Real.log R < Real.log ((Q : ℝ) + 1) := by
    have hQ' : (3 : ℝ) ≤ (Q : ℝ) + 1 := by exact_mod_cast (show 3 ≤ Q + 1 by omega)
    have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hQ'
    linarith only [hlen, h3, Real.log_three_gt_d9]
  have hμ : (1 / 50000 : ℝ) ≤ ccmRestrictedWeilGroundEnergy A :=
    one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000 le_rfl
  have hfloor : ccmRestrictedWeilGroundEnergy A * ∑ j ∈ range J, σ j ^ 2 ≤
      packetForm Q (stepPacket R J σ) := by
    rw [← packetAutocorr_stepPacket_zero hR J σ]
    simp only [stepPacket_eq_nested hR J σ]
    exact groundEnergy_mul_nested_mass_le_packetForm_of_log_lt hR (nested_bounds R J)
      (nestedCoeff J σ) (by dsimp [A]; linarith only [hlen]) hlogQ
  exact (mul_le_mul_of_nonneg_right hμ (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans hfloor

/-- Every block matrix of a window of ratio at most `53/25` is uniformly positive definite. -/
theorem sum_blockMatrix_ge_of_first_overlap {R J Q : ℕ}
    (hR : 1 ≤ R) (hJ : 25 * J ≤ 28 * R) (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    (1 / 50000 : ℝ) * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  rw [← packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ]
  exact packetForm_stepPacket_ge_of_first_overlap hR hJ hQ σ

#print axioms fullZeroForm_ge_at_aperture_1881_over_5000
#print axioms zetaZeroConfig_re_W_ge_at_aperture_1881_over_5000
#print axioms one_div_50000_le_groundEnergy_of_aperture_le_1881_over_5000
#print axioms packetForm_stepPacket_ge_of_first_overlap
#print axioms sum_blockMatrix_ge_of_first_overlap

end GaloisForLFunctions.WindowTowerOfSpecZ
