import GaloisForLFunctions.RHTower.SelbergMaassCharacterProjection

/-!
# Every original residue-frequency channel and its actual inversion transfer

The literal Maass coefficient vector is the finite-period Bochner integral of the original
source vector. Every continuous linear source readout therefore commutes with its Fourier
coefficient. The complete upper-character family filters precisely the residue class of the
integer index. Physical Parseval identifies upper and lower channel mass with the original
coefficient energy and the actual finite Fourier–inversion–Fourier transfer, respectively.
No truncation, averaging bound, or source/coupling identification is supplied as a premise.
-/

open Complex Set UpperHalfPlane MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterFourier
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassSourceCurrents
open SelbergMaassMean SelbergMaassFourier SelbergMaassUnipotentFourier
open SelbergMaassCharacterProjection SelbergMaassUnipotentBlocks
open _root_.RHTower
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Original component regularity gives continuity of the complete source vector in its actual chart. -/
theorem sourceVector_continuousOn :
    ContinuousOn (fun z : ℂ => sourceVector N f (ofComplex z)) {z : ℂ | 0 < z.im} := by
  change ContinuousOn (fun z => WithLp.toLp 2 (fun q => field N f q z)) _
  exact (PiLp.continuous_toLp 2 (fun _ : Deck N => ℂ)).comp_continuousOn
    (continuousOn_pi.mpr (fun q => (quotientForm N f q).2.2.1.1.continuousOn))

/-- Every positive-height slice of the complete original source is continuous. -/
theorem sourceSlice_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => sourceVector N f (ofComplex (point x y))) := by
  change Continuous (fun x => WithLp.toLp 2 (fun q => field N f q (point x y)))
  exact (PiLp.continuous_toLp 2 (fun _ : Deck N => ℂ)).comp
    (continuous_pi (fun q => slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy))

/-- The literal Fourier-kernel-weighted source vector is genuinely continuous on each slice. -/
theorem sourceKernel_continuous (n : ℤ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => deningerFourierKernel (N+1 : ℕ) n x •
      sourceVector N f (ofComplex (point x y))) := by
  have hk : Continuous (deningerFourierKernel (N+1 : ℕ) n) :=
    continuous_iff_continuousAt.mpr
      (fun x => (deningerFourierKernel_hasDerivAt (N+1 : ℕ) n x).continuousAt)
  exact hk.smul (sourceSlice_continuous N f hy)

/-- The existing original coefficient vector is exactly its vector-valued normalized Fourier integral. -/
theorem coefficientVector_eq_integral (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficientVector N f n y = (1 / ((N+1 : ℕ) : ℂ)) •
      ∫ x in (0 : ℝ)..(N+1 : ℕ), deningerFourierKernel (N+1 : ℕ) n x •
        sourceVector N f (ofComplex (point x y)) := by
  ext q
  have hi := (EuclideanSpace.proj q : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ).intervalIntegral_comp_comm (μ := volume)
    ((sourceKernel_continuous N f n hy).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
    deningerFourierKernel (N+1 : ℕ) n x * field N f q (point x y)) =
    (∫ x in (0 : ℝ)..(N+1 : ℕ), deningerFourierKernel (N+1 : ℕ) n x •
      sourceVector N f (ofComplex (point x y))) q at hi
  change (1 / ((N+1 : ℕ) : ℂ)) *
    (∫ x in (0 : ℝ)..(N+1 : ℕ), deningerFourierKernel (N+1 : ℕ) n x * field N f q (point x y)) =
    (1 / ((N+1 : ℕ) : ℂ)) *
    (∫ x in (0 : ℝ)..(N+1 : ℕ), deningerFourierKernel (N+1 : ℕ) n x •
      sourceVector N f (ofComplex (point x y))) q
  rw [hi]

/-- Every continuous linear readout commutes with the original Maass coefficient integral. -/
theorem coefficient_readout (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (fun z => L (sourceVector N f (ofComplex z))) y =
      L (coefficientVector N f n y) := by
  rw [coefficientVector_eq_integral N f n hy,map_smul]
  unfold coefficient deningerFourierCoeff
  change (1 / ((N+1 : ℕ) : ℂ)) *
      (∫ x in (0 : ℝ)..(N+1 : ℕ),
        deningerFourierKernel (N+1 : ℕ) n x * L (sourceVector N f (ofComplex (point x y)))) =
    (1 / ((N+1 : ℕ) : ℂ)) *
      L (∫ x in (0 : ℝ)..(N+1 : ℕ), deningerFourierKernel (N+1 : ℕ) n x •
        sourceVector N f (ofComplex (point x y)))
  congr 1
  have h := L.intervalIntegral_comp_comm (μ := volume)
    ((sourceKernel_continuous N f n hy).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  simpa only [map_smul,smul_eq_mul] using h

/-- The actual source field selected by one full block-character projector. -/
def characterField (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (q : Deck N) (z : ℂ) : ℂ :=
  characterProjection N p r (sourceVector N f (ofComplex z)) q

/-- Every projected source field is continuous, including zero fields. -/
theorem characterField_continuousOn (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (q : Deck N) :
    ContinuousOn (characterField N f p r q) {z : ℂ | 0 < z.im} :=
  (((EuclideanSpace.proj q : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ).comp
    (characterProjection N p r).toContinuousLinearMap).continuous).comp_continuousOn
      (sourceVector_continuousOn N f)

/-- The coefficient of a projected original field is its projected literal coefficient vector. -/
theorem coefficient_characterField (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (q : Deck N) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (characterField N f p r q) y =
      characterProjection N p r (coefficientVector N f n y) q :=
  coefficient_readout N f
    ((EuclideanSpace.proj q : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ).comp
      (characterProjection N p r).toContinuousLinearMap) n hy

/-- Each original Fourier vector belongs to precisely its index residue channel. -/
theorem upperProjection_coefficientVector (r : ZMod (N+1)) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    characterProjection N (upperBlock N) r (coefficientVector N f n y) =
      if (n : ZMod (N+1))=r then coefficientVector N f n y else 0 := by
  have hv : characterProjection N (upperBlock N) (n : ZMod (N+1))
      (coefficientVector N f n y)=coefficientVector N f n y :=
    (connes_characterProjector_fixed_iff (blockAction_mul N (upperBlock N))
      (residueCharacter_mul N (n : ZMod (N+1)))
      (residueCharacter_unit N (n : ZMod (N+1))) (coefficientVector N f n y)).mpr
        (fun j => coefficientVector_upperBlock N f j n hy)
  have h := characterProjection_pair N (upperBlock N) r (n : ZMod (N+1))
    (coefficientVector N f n y)
  rw [hv] at h
  simpa only [eq_comm] using h

/-- Every original upper-character field keeps exactly one residue class of Fourier indices. -/
theorem coefficient_upperCharacter (r : ZMod (N+1)) (q : Deck N)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (characterField N f (upperBlock N) r q) y =
      if (n : ZMod (N+1))=r then maassCoefficient N (quotientForm N f q) n y else 0 := by
  rw [coefficient_characterField N f (upperBlock N) r q n hy,
    upperProjection_coefficientVector N f r n hy]
  split_ifs <;> rfl

/-- Physical Parseval for one literal original residue-channel coordinate. -/
theorem upperCharacter_mass_hasSum (r : ZMod (N+1)) (q : Deck N) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => if (n : ZMod (N+1))=r then
      normSq (maassCoefficient N (quotientForm N f q) n y) else 0)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        normSq (characterField N f (upperBlock N) r q (point x y))) := by
  have h := SelbergMaassParseval.coefficient_mass_hasSum (N+1 : ℕ) (by positivity)
    (characterField_continuousOn N f (upperBlock N) r q) hy
  simp_rw [coefficient_upperCharacter N f r q _ hy] at h
  simpa only [apply_ite normSq,map_zero] using h

/-- The full actual character energy is the sum of every projected coordinate mass. -/
theorem characterProjection_norm_sq_eq (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) (z : ℍ) :
    ‖characterProjection N p r (sourceVector N f z)‖^2 =
      ∑ q : Deck N, normSq (characterField N f p r q (z : ℂ)) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm,characterField,ofComplex_apply]

/-- Physical Parseval for any original block-character source, retaining all frequencies. -/
theorem character_mass_hasSum (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖characterProjection N p r (coefficientVector N f n y)‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖characterProjection N p r (sourceVector N f (ofComplex (point x y)))‖^2) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => SelbergMaassParseval.coefficient_mass_hasSum (N+1 : ℕ) (by positivity)
      (characterField_continuousOn N f p r q) hy)
  simp_rw [coefficient_characterField N f p r _ _ hy] at h
  have hv (v : EuclideanSpace ℂ (Deck N)) :
      (∑ q : Deck N, normSq (characterProjection N p r v q)) =
      ‖characterProjection N p r v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
  simp_rw [hv] at h
  rw [← Finset.mul_sum] at h
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (characterField_continuousOn N f p r q) hy)).intervalIntegrable
        (0 : ℝ) (N+1 : ℕ))
  simp only [Function.comp_def] at hi
  rw [← hi] at h
  have he (x : ℝ) :
      (∑ q : Deck N, normSq (characterField N f p r q (point x y))) =
      ‖characterProjection N p r (sourceVector N f (ofComplex (point x y)))‖^2 := by
    rw [characterProjection_norm_sq_eq,SelbergMaassUnipotentPaths.coe_ofComplex_point x hy]
  simp_rw [he] at h
  exact h

/-- The actual full upper-channel mass is precisely its original residue-class Fourier energy. -/
theorem upperCharacter_energy_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => if (n : ZMod (N+1))=r then ‖coefficientVector N f n y‖^2 else 0)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖characterProjection N (upperBlock N) r
          (sourceVector N f (ofComplex (point x y)))‖^2) := by
  have h := character_mass_hasSum N f (upperBlock N) r hy
  simp_rw [upperProjection_coefficientVector N f r _ hy] at h
  simpa only [apply_ite (fun v => ‖v‖^2),norm_zero,zero_pow (show (2 : ℕ)≠0 from Nat.succ_ne_zero 1)] using h

open GaloisForLFunctions.HTGeometry ModularGroup

/-- The actual finite inversion transfer from upper residue s to upper residue r. -/
def inversionTransfer (N : ℕ) (r s : ZMod (N+1)) :
    EuclideanSpace ℂ (Deck N) →ₗ[ℂ] EuclideanSpace ℂ (Deck N) :=
  (characterProjection N (upperBlock N) r).comp
    ((finiteRegularUnitary (QuotientGroup.mk (S⁻¹) : Deck N)).toLinearEquiv.toLinearMap.comp
      (characterProjection N (upperBlock N) s))

/-- Each transfer column preserves all energy of its input character component. -/
theorem inversionTransfer_energy_sum (N : ℕ) (s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    (∑ r : ZMod (N+1), ‖inversionTransfer N r s v‖^2)=
      ‖characterProjection N (upperBlock N) s v‖^2 := by
  unfold inversionTransfer
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [sum_characterProjection_norm_sq]
  change ‖finiteRegularUnitary (QuotientGroup.mk (S⁻¹) : Deck N)
    (characterProjection N (upperBlock N) s v)‖^2 = _
  rw [LinearIsometryEquiv.norm_map]

/-- The actual source coefficient already lies in its residue eigenspace. -/
theorem inversionTransfer_coefficientVector (r : ZMod (N+1)) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    inversionTransfer N r (n : ZMod (N+1)) (coefficientVector N f n y) =
      characterProjection N (upperBlock N) r
        (finiteRegularUnitary (QuotientGroup.mk (S⁻¹) : Deck N) (coefficientVector N f n y)) := by
  unfold inversionTransfer
  simp only [LinearMap.comp_apply]
  rw [upperProjection_coefficientVector N f (n : ZMod (N+1)) n hy,if_pos rfl]
  rfl

/-- Exact physical lower-channel mass in terms of the actual finite inversion coupling. -/
theorem lowerCharacter_transfer_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ =>
      ‖inversionTransfer N (-r) (n : ZMod (N+1)) (coefficientVector N f n y)‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖characterProjection N (lowerBlock N) r
          (sourceVector N f (ofComplex (point x y)))‖^2) := by
  have h := character_mass_hasSum N f (lowerBlock N) r hy
  have he (n : ℤ) :
      ‖characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^2 =
      ‖inversionTransfer N (-r) (n : ZMod (N+1)) (coefficientVector N f n y)‖^2 := by
    rw [characterProjection_lower_conjugate,LinearIsometryEquiv.norm_map,
      inversionTransfer_coefficientVector N f (-r) n hy]
  simp_rw [he] at h
  exact h

/-- Inversion redistributes every original Fourier mode without losing any of its energy. -/
theorem coefficient_inversion_energy_sum (n : ℤ) {y : ℝ} (hy : 0 < y) :
    (∑ r : ZMod (N+1),
      ‖inversionTransfer N r (n : ZMod (N+1)) (coefficientVector N f n y)‖^2)=
      ‖coefficientVector N f n y‖^2 := by
  rw [inversionTransfer_energy_sum,upperProjection_coefficientVector N f (n : ZMod (N+1)) n hy,
    if_pos rfl]

/-- Literal finite Fourier–inversion–Fourier kernel on every original deck coordinate. -/
theorem inversionTransfer_coord (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) (q : Deck N) :
    inversionTransfer N r s v q = (((N+1 : ℕ) : ℂ)⁻¹)^2 *
      ∑ a : Multiplicative (ZMod (N+1)), ∑ b : Multiplicative (ZMod (N+1)),
        (starRingEnd ℂ) (residueCharacter N r a) *
          (starRingEnd ℂ) (residueCharacter N s b) *
            v (((q*upperBlock N a)*QuotientGroup.mk (S⁻¹))*upperBlock N b) := by
  unfold inversionTransfer
  change characterProjection N (upperBlock N) r
    (finiteRegularUnitary (QuotientGroup.mk (S⁻¹) : Deck N)
      (characterProjection N (upperBlock N) s v)) q= _
  rw [characterProjection_coord]
  simp only [finiteRegularUnitary_apply]
  simp_rw [characterProjection_coord,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterFourier
