import GaloisForLFunctions.RHTower.ProlateSectorLeakageFloor

/-!
# The sector ground vector realizes the secular root

The secular ground coordinates `v_j = ℓ_j/(d_j − μ₀)` are square-summable, so synthesising them
against the phase-normalized prolate family of a sector produces an honest vector of the even
carrier.  That vector lies in the sector, is annihilated by the integral functional, and its
leakage form is exactly `μ₀‖f‖²`.  Together with the sector Rayleigh floor this identifies `μ₀`
as the lowest constrained leakage eigenvalue of the sector, in the operator's own terms.
-/

noncomputable section

open Filter Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-! ### Synthesis of an `ℓ²` coefficient sequence along a sector -/

/-- The ambient coefficient sequence: sector coefficients carried by their phase along the sector,
and zero off it. -/
def sectorAmbient (a : ℝ) (σ : ℕ → ℕ) (X : ℕ → ℂ) : ℕ → ℂ :=
  Function.extend σ (fun j : ℕ => X j * signedModePhase a (σ j)) 0

theorem sectorAmbient_apply {a : ℝ} {σ : ℕ → ℕ} (hσ : Function.Injective σ) (X : ℕ → ℂ) (j : ℕ) :
    sectorAmbient a σ X (σ j) = X j * signedModePhase a (σ j) :=
  hσ.extend_apply _ _ j

theorem sectorAmbient_eq_zero (a : ℝ) (σ : ℕ → ℕ) (X : ℕ → ℂ) {n : ℕ} (hn : n ∉ Set.range σ) :
    sectorAmbient a σ X n = 0 := by
  rw [sectorAmbient, Function.extend_apply' _ _ _ (by simpa [Set.range] using hn)]
  rfl

theorem norm_sectorAmbient {a : ℝ} {σ : ℕ → ℕ} (hσ : Function.Injective σ) (X : ℕ → ℂ) (j : ℕ) :
    ‖sectorAmbient a σ X (σ j)‖ ^ 2 = ‖X j‖ ^ 2 := by
  rw [sectorAmbient_apply hσ, norm_mul, norm_signedModePhase, mul_one]

/-- Square-summability of a complex sequence puts it in `ℓ²`. -/
theorem memℓp_two_of_norm_sq_summable {f : ℕ → ℂ} (hf : Summable fun j => ‖f j‖ ^ 2) :
    Memℓp f 2 := by
  apply memℓp_gen
  refine hf.congr fun i => ?_
  rw [show ((2 : ENNReal)).toReal = ((2 : ℕ) : ℝ) by simp, Real.rpow_natCast]

theorem memℓp_sectorAmbient {a : ℝ} {σ : ℕ → ℕ} (hσ : Function.Injective σ) {X : ℕ → ℂ}
    (hX : Summable fun j : ℕ => ‖X j‖ ^ 2) : Memℓp (sectorAmbient a σ X) 2 := by
  refine memℓp_two_of_norm_sq_summable ?_
  refine (hσ.summable_iff (f := fun n : ℕ => ‖sectorAmbient a σ X n‖ ^ 2) ?_).mp ?_
  · intro n hn
    rw [sectorAmbient_eq_zero a σ X hn, norm_zero]
    norm_num
  · exact hX.congr fun j => (norm_sectorAmbient hσ X j).symm

theorem subtypeL_signedNatBasis {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (Submodule.subtypeL (evenTimeLimitedSubspace a)) ((signedNatBasis a ha) n)
      = evenProlateSignedMode a n := by
  rw [signedNatBasis_apply, Submodule.subtypeL_apply]
  rfl

theorem subtypeL_smul_signedNatBasis {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ) (X : ℕ → ℂ) (j : ℕ) :
    (Submodule.subtypeL (evenTimeLimitedSubspace a))
        (sectorAmbient a σ X (σ j) • (signedNatBasis a ha) (σ j))
      = X j • sectorMode a σ j := by
  rw [Submodule.subtypeL_apply, Submodule.coe_smul, sectorAmbient_apply hσ]
  have hb : ((signedNatBasis a ha (σ j) : evenTimeLimitedSubspace a) : evenSubspace)
      = evenProlateSignedMode a (σ j) := by
    rw [signedNatBasis_apply]
    rfl
  rw [hb, sectorMode, phasedSignedMode, smul_smul]

/-- **Synthesis along a sector.**  Every square-summable coefficient sequence sums, against the
phase-normalized prolate family of the sector, to an honest vector of the even carrier. -/
theorem exists_hasSum_sector {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    {X : ℕ → ℂ} (hX : Summable fun j : ℕ => ‖X j‖ ^ 2) :
    ∃ f : evenSubspace, HasSum (fun j : ℕ => X j • sectorMode a σ j) f := by
  have hmem : Memℓp (sectorAmbient a σ X) 2 := memℓp_sectorAmbient hσ hX
  set Z : lp (fun _ : ℕ => ℂ) 2 := ⟨sectorAmbient a σ X, hmem⟩ with hZdef
  have hZn : ∀ n : ℕ, Z n = sectorAmbient a σ X n := fun _ => rfl
  have hsum0 : HasSum (fun n : ℕ => Z n • (signedNatBasis a ha) n)
      ((signedNatBasis a ha).repr.symm Z) :=
    (signedNatBasis a ha).hasSum_repr_symm Z
  have hres0 : HasSum ((fun n : ℕ => Z n • (signedNatBasis a ha) n) ∘ σ)
      ((signedNatBasis a ha).repr.symm Z) := by
    refine (Function.Injective.hasSum_iff
      (f := fun n : ℕ => Z n • (signedNatBasis a ha) n) hσ ?_).mpr hsum0
    intro n hn
    rw [hZn n, sectorAmbient_eq_zero a σ X hn, zero_smul]
  have hres : HasSum (fun j : ℕ => Z (σ j) • (signedNatBasis a ha) (σ j))
      ((signedNatBasis a ha).repr.symm Z) := hres0
  have hcoe := hres.mapL (Submodule.subtypeL (evenTimeLimitedSubspace a))
  have hfun : (fun j : ℕ => (Submodule.subtypeL (evenTimeLimitedSubspace a))
        (Z (σ j) • (signedNatBasis a ha) (σ j)))
      = fun j : ℕ => X j • sectorMode a σ j := by
    funext j
    rw [hZn (σ j)]
    exact subtypeL_smul_signedNatBasis ha hσ X j
  rw [hfun] at hcoe
  exact ⟨_, hcoe⟩

/-- **Parseval for a synthesised difference.** -/
theorem hasSum_norm_sub_sq_of_hasSum {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ) {X Y : ℕ → ℂ} {f g : evenSubspace}
    (hf : HasSum (fun j : ℕ => X j • sectorMode a σ j) f)
    (hg : HasSum (fun j : ℕ => Y j • sectorMode a σ j) g) :
    HasSum (fun j : ℕ => ‖X j - Y j‖ ^ 2) (‖f - g‖ ^ 2) := by
  have h := hf.sub hg
  have heq : (fun j : ℕ => X j • sectorMode a σ j - Y j • sectorMode a σ j)
      = fun j : ℕ => (X j - Y j) • sectorMode a σ j := by
    funext j
    rw [sub_smul]
  rw [heq] at h
  exact hasSum_norm_sq_of_hasSum_smul (orthonormal_sectorMode ha hσ) h

/-! ### The secular ground coordinates -/

/-- The secular ground coordinates of a sector. -/
def sectorGroundCoeff (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : ℝ :=
  secularVector (sectorLeakage a σ) (sectorCoord a σ)
    (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ)) j

/-- The ground coordinates are square-summable. -/
theorem summable_sectorGroundCoeff_sq {a : ℝ} {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0) :
    Summable fun j : ℕ => sectorGroundCoeff a σ j ^ 2 := by
  have hsumL := summable_sectorCoord_sq a hσ
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsumL hℓ0 hℓ1
  exact (summable_nat_add_iff
      (f := fun j => sectorGroundCoeff a σ j ^ 2) 2).mp
    (summable_secularVector_sq_tail hd2 hsumL (by linarith [hrmem.2]))

/-- The secular ground coordinates synthesise an honest vector of the sector. -/
theorem exists_hasSum_sectorGround {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0) :
    ∃ f : evenSubspace,
      HasSum (fun j : ℕ => ((sectorGroundCoeff a σ j : ℝ) : ℂ) • sectorMode a σ j) f := by
  refine exists_hasSum_sector ha hσ ?_
  refine (summable_sectorGroundCoeff_sq hσ h01 h12 hd2 hℓ0 hℓ1).congr fun j => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **The sector ground vector realizes the secular root.**  A vector of the sector synthesised
from the secular ground coordinates is nonzero, is annihilated by the integral functional, and its
leakage form is exactly the secular ground root times its squared norm. -/
theorem sectorGround_properties {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {f : evenSubspace}
    (hcoe : HasSum (fun j : ℕ => ((sectorGroundCoeff a σ j : ℝ) : ℂ) • sectorMode a σ j) f) :
    f ≠ 0 ∧
      inner ℂ (evenCentralIndicator a) f = 0 ∧
      (inner ℂ (evenProlateLeakage a f) f : ℂ).re
        = infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ) * ‖f‖ ^ 2 := by
  classical
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  set v : ℕ → ℝ := sectorGroundCoeff a σ with hvdef
  have hsumL : Summable fun j : ℕ => L j ^ 2 := summable_sectorCoord_sq a hσ
  have hsv : Summable fun j : ℕ => v j ^ 2 :=
    summable_sectorGroundCoeff_sq hσ h01 h12 hd2 hℓ0 hℓ1
  have hvon := orthonormal_sectorMode ha hσ
  have hnormfun : (fun j : ℕ => ‖((v j : ℝ) : ℂ)‖ ^ 2) = fun j : ℕ => v j ^ 2 := by
    funext j
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hns : HasSum (fun j : ℕ => v j ^ 2) (‖f‖ ^ 2) := by
    have h := hasSum_norm_sq_of_hasSum_smul hvon hcoe
    rwa [hnormfun] at h
  have hv0 : v 0 ≠ 0 := by
    obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsumL hℓ0 hℓ1
    have hne : D 0 - infiniteSecularRoot D L ≠ 0 := by
      have := hrmem.1
      linarith
    rw [hvdef, sectorGroundCoeff, secularVector]
    exact div_ne_zero hℓ0 hne
  have hfne : f ≠ 0 := by
    intro hzero
    have hle : v 0 ^ 2 ≤ ‖f‖ ^ 2 := le_hasSum hns 0 fun j _ => sq_nonneg _
    rw [hzero, norm_zero] at hle
    have hpos : (0 : ℝ) < v 0 ^ 2 := by positivity
    nlinarith [hle]
  have hcon : inner ℂ (evenCentralIndicator a) f = 0 := by
    have h := hasSum_constraint_of_hasSum_smul (inner_evenCentralIndicator_sectorMode a σ) hcoe
    have hreal : Summable fun j : ℕ => L j * v j := summable_mul_of_sq_summable hsumL hsv
    have hzero : (∑' j : ℕ, L j * v j) = 0 := secularVector_constraint h01 h12 hd2 hsumL hℓ0 hℓ1
    have hrs : HasSum (fun j : ℕ => L j * v j) 0 := by
      rw [← hzero]
      exact hreal.hasSum
    have h2 : HasSum (fun j : ℕ => (((L j * v j : ℝ)) : ℂ)) ((0 : ℝ) : ℂ) :=
      (Complex.hasSum_ofReal (f := fun j : ℕ => L j * v j) (x := 0)).mpr hrs
    have hcsfun : (fun j : ℕ => (((L j * v j : ℝ)) : ℂ))
        = fun j : ℕ => ((v j : ℝ) : ℂ) * ((L j : ℝ) : ℂ) := by
      funext j
      push_cast
      ring
    rw [hcsfun] at h2
    have huniq := h.unique h2
    simpa using huniq
  have hls : HasSum (fun j : ℕ => D j * v j ^ 2)
      ((inner ℂ (evenProlateLeakage a f) f : ℂ).re) := by
    have h := hasSum_leakage_of_hasSum_smul hvon (evenProlateLeakage_apply_sectorMode a σ) hcoe
    have hfun2 : (fun j : ℕ => D j * ‖((v j : ℝ) : ℂ)‖ ^ 2) = fun j : ℕ => D j * v j ^ 2 := by
      funext j
      rw [show ‖((v j : ℝ) : ℂ)‖ ^ 2 = v j ^ 2 from congrFun hnormfun j]
    rwa [hfun2] at h
  have hray : (∑' j : ℕ, D j * v j * v j)
      = infiniteSecularRoot D L * ∑' j : ℕ, v j * v j :=
    tsum_mul_secularVector_sq_eq h01 h12 hd2 hsumL hℓ0 hℓ1
  rw [tsum_congr (fun j : ℕ => by ring : ∀ j : ℕ, D j * v j * v j = D j * v j ^ 2),
    tsum_congr (fun j : ℕ => by ring : ∀ j : ℕ, v j * v j = v j ^ 2),
    hls.tsum_eq, hns.tsum_eq] at hray
  exact ⟨hfne, hcon, hray⟩

end RHTower

end
