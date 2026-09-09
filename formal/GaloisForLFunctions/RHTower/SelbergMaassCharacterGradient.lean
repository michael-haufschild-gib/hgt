import GaloisForLFunctions.RHTower.SelbergMaassInversionPhaseEnergy

/-!
# Actual character phases and the complete original Maass gradient

Original C² regularity and periodicity pass to every continuous linear source readout.
Exact horizontal and vertical Parseval identify the character phase losses with the
physical missing-channel derivatives. The actual coefficient height vector retains
its original upper residue eigenspace. Both derivative energies split exactly into
retained and missing character fields; the complete phase sum recovers both together.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCharacterGradient
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionGram
open SelbergMaassInversionPhaseEnergy SelbergMaassMean SelbergMaassFourier
open SelbergMaassSourceCurrents SelbergMaassUnipotentFourier
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The complete original source vector retains its actual two real chart derivatives. -/
theorem sourceVector_contDiffOn :
    ContDiffOn ℝ 2 (fun z : ℂ => sourceVector N f (ofComplex z)) {z : ℂ | 0 < z.im} := by
  apply (contDiffOn_piLp 2).mpr
  intro q
  exact (quotientForm N f q).2.2.1.1

/-- Every continuous linear observation retains the original source chart regularity. -/
theorem readout_contDiffOn (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ) :
    ContDiffOn ℝ 2 (fun z : ℂ => L (sourceVector N f (ofComplex z))) {z : ℂ | 0 < z.im} :=
  (L.restrictScalars ℝ).contDiff.comp_contDiffOn (sourceVector_contDiffOn N f)

/-- Actual linear observations retain the full original horizontal period. -/
theorem readout_periodic (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    L (sourceVector N f (ofComplex (point (x+(N+1 : ℕ)) y)))=
      L (sourceVector N f (ofComplex (point x y))) := by
  congr 1
  ext q
  exact maass_periodic N (quotientForm N f q) x hy

/-- The exact horizontal gradient of any actual linear source observation has its weighted Parseval sum. -/
theorem readout_horizontal_hasSum (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^2 * normSq (L (coefficientVector N f n y)))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        normSq (directional 1 (fun z => L (sourceVector N f (ofComplex z))) (point x y))) := by
  have hf := readout_contDiffOn N f L
  have hd := directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)
  have hs := SelbergMaassParseval.coefficient_mass_hasSum (N+1 : ℕ) (by positivity)
    hd.continuousOn hy
  apply hs.congr_fun
  intro n
  rw [SelbergMaassParseval.coefficient_horizontal (N+1 : ℕ) (by positivity) n
    (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy (fun x => readout_periodic N f L x hy),
    coefficient_readout N f L n hy]
  simp [Complex.normSq_mul,Complex.normSq_ofReal,Complex.normSq_I,pow_two]

/-- The literal missing lower-character source field, including every deck component. -/
def complementField (r : ZMod (N+1)) (q : Deck N) (z : ℂ) : ℂ :=
  sourceVector N f (ofComplex z) q-characterProjection N (lowerBlock N) r (sourceVector N f (ofComplex z)) q

/-- The missing field is an actual continuous linear observation of the original source. -/
def complementReadout (N : ℕ) (r : ZMod (N+1)) (q : Deck N) : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ :=
  (EuclideanSpace.proj q).comp
    ((ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Deck N)))-
      (characterProjection N (lowerBlock N) r).toContinuousLinearMap)

/-- The actual complement readout has exactly the stated coordinate difference. -/
theorem complementReadout_apply (N : ℕ) (r : ZMod (N+1)) (q : Deck N)
    (v : EuclideanSpace ℂ (Deck N)) :
    complementReadout N r q v=v q-characterProjection N (lowerBlock N) r v q := rfl

/-- Exact weighted Fourier loss equals the physical horizontal energy of the original missing channel. -/
theorem complement_horizontal_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^2 *
      ‖coefficientVector N f n y-
        characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional 1 (complementField N f r q) (point x y))) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => readout_horizontal_hasSum N f (complementReadout N r q) hy)
  have hn (n : ℤ) :
      (∑ q : Deck N, signedFrequency (N+1 : ℕ) n^2 *
        normSq (complementReadout N r q (coefficientVector N f n y)))=
          signedFrequency (N+1 : ℕ) n^2 *
            ‖coefficientVector N f n y-
              characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^2 := by
    rw [← Finset.mul_sum,EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm,complementReadout_apply]
    rfl
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum _ (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
    normSq (directional 1 (complementField N f r q) (point x y))) at h
  have hd (q : Deck N) := directional_contDiffOn
    (readout_contDiffOn N f (complementReadout N r q)) (m := 1) le_rfl (1 : ℂ)
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (hd q).continuousOn hy)).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ∑ q : Deck N, normSq (directional 1 (complementField N f r q) (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional 1 (complementField N f r q) (point x y)) at hi
  rw [← hi] at h
  exact h

/-- Exact horizontal derivative Parseval for each actual original character field. -/
theorem character_horizontal_hasSum (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^2 *
      ‖characterProjection N p r (coefficientVector N f n y)‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional 1 (characterField N f p r q) (point x y))) := by
  let L (q : Deck N) : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ :=
    (EuclideanSpace.proj q).comp (characterProjection N p r).toContinuousLinearMap
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => readout_horizontal_hasSum N f (L q) hy)
  have hn (n : ℤ) :
      (∑ q : Deck N, signedFrequency (N+1 : ℕ) n^2 * normSq (L q (coefficientVector N f n y)))=
        signedFrequency (N+1 : ℕ) n^2 * ‖characterProjection N p r (coefficientVector N f n y)‖^2 := by
    rw [← Finset.mul_sum,EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
    rfl
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum _ (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
    normSq (directional 1 (characterField N f p r q) (point x y))) at h
  have hd (q : Deck N) := directional_contDiffOn (readout_contDiffOn N f (L q))
    (m := 1) le_rfl (1 : ℂ)
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (hd q).continuousOn hy)).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ∑ q : Deck N, normSq (directional 1 (characterField N f p r q) (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional 1 (characterField N f p r q) (point x y)) at hi
  rw [← hi] at h
  exact h

/-- Complete physical horizontal gradient splits exactly into the missing and retained character energies. -/
theorem horizontal_energy_split (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N, normSq (directional 1 (field N f q) (point x y)))=
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N,
      normSq (directional 1 (complementField N f r q) (point x y)))+
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N,
      normSq (directional 1 (characterField N f (lowerBlock N) r q) (point x y))) := by
  have h := (complement_horizontal_hasSum N f r hy).add
    (character_horizontal_hasSum N f (lowerBlock N) r hy)
  have he (n : ℤ) :
      signedFrequency (N+1 : ℕ) n^2 *
        ‖coefficientVector N f n y-characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^2+
      signedFrequency (N+1 : ℕ) n^2 * ‖characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^2=
      signedFrequency (N+1 : ℕ) n^2 * ‖coefficientVector N f n y‖^2 := by
    rw [characterProjection_loss]
    ring
  simp_rw [he] at h
  have hEq := h.unique (coefficientVector_horizontal_hasSum N f hy)
  rw [← mul_add] at hEq
  have hN : ((N+1 : ℕ) : ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  exact (mul_left_cancel₀ (inv_ne_zero hN) hEq).symm

/-- Frequency-weighted original lower phase displacement is precisely its physical missing-channel gradient. -/
theorem source_phase_horizontal_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^2 *
      ((((N+1 : ℕ) : ℝ)⁻¹/2) *
        (∑ b : ZMod (N+1), ‖coefficientVector N f n y-
          blockMotion N (lowerBlock N) r b (coefficientVector N f n y)‖^2)))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional 1 (complementField N f r q) (point x y))) := by
  simp_rw [block_displacement_energy]
  exact complement_horizontal_hasSum N f r hy

/-- The full arithmetic three-factor phase energy retains exactly the same physical horizontal derivative. -/
theorem source_triple_horizontal_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^2 *
      (((((N+1 : ℕ) : ℝ)⁻¹)^3/2) *
        (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
          ‖coefficientVector N f n y-
            tripleMotion N (-r) (n : ZMod (N+1)) a b c (coefficientVector N f n y)‖^2)))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional 1 (complementField N f r q) (point x y))) := by
  simp_rw [coefficient_triple_energy_eq_block N f (-r) _ hy,neg_neg]
  exact source_phase_horizontal_hasSum N f r hy

/-- The literal vector of original coefficient height derivatives. -/
def coefficientHeightVector (n : ℤ) (y : ℝ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q => deriv (maassCoefficient N (quotientForm N f q) n) y)

/-- Original coefficient differentiation produces precisely the stated height vector. -/
theorem coefficientVector_hasDerivAt (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (coefficientVector N f n) (coefficientHeightVector N f n y) y := by
  have h : HasDerivAt (fun t : ℝ => fun q : Deck N => maassCoefficient N (quotientForm N f q) n t)
      (fun q : Deck N => deriv (maassCoefficient N (quotientForm N f q) n) y) y :=
    hasDerivAt_pi.mpr (fun q => maassCoefficient_hasDerivAt N (quotientForm N f q) n hy)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Deck N => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y h

/-- Differentiation retains the exact original upper residue eigenspace. -/
theorem coefficientHeight_upperProjection (n : ℤ) {y : ℝ} (hy : 0 < y) :
    characterProjection N (upperBlock N) (n : ZMod (N+1)) (coefficientHeightVector N f n y)=
      coefficientHeightVector N f n y := by
  have h := coefficientVector_hasDerivAt N f n hy
  have hp := ((characterProjection N (upperBlock N) (n : ZMod (N+1))).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y h
  change HasDerivAt (fun t => characterProjection N (upperBlock N) (n : ZMod (N+1)) (coefficientVector N f n t))
    (characterProjection N (upperBlock N) (n : ZMod (N+1)) (coefficientHeightVector N f n y)) y at hp
  have he : (fun t => characterProjection N (upperBlock N) (n : ZMod (N+1)) (coefficientVector N f n t))
      =ᶠ[nhds y] coefficientVector N f n := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    rw [upperProjection_coefficientVector N f (n : ZMod (N+1)) n ht,if_pos rfl]
  have hd := he.deriv_eq
  rw [hp.deriv,h.deriv] at hd
  exact hd

/-- The source readout's vertical coefficient is the readout of the actual height vector. -/
theorem coefficient_readout_vertical (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (N+1 : ℕ) n (directional Complex.I (fun z => L (sourceVector N f (ofComplex z)))) y=
      L (coefficientHeightVector N f n y) := by
  have hf := readout_contDiffOn N f L
  have hc := coefficient_hasDerivAt (N+1 : ℕ) (by positivity) n
    (hf.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy
  have hL := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y (coefficientVector_hasDerivAt N f n hy)
  change HasDerivAt (fun t => L (coefficientVector N f n t)) (L (coefficientHeightVector N f n y)) y at hL
  have he : coefficient (N+1 : ℕ) n (fun z => L (sourceVector N f (ofComplex z)))
      =ᶠ[nhds y] (fun t => L (coefficientVector N f n t)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact coefficient_readout N f L n ht
  have hd := he.deriv_eq
  rw [hc.deriv,hL.deriv] at hd
  exact hd

/-- Exact vertical derivative Parseval for every actual linear observation of the original source. -/
theorem readout_vertical_hasSum (L : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => normSq (L (coefficientHeightVector N f n y)))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        normSq (directional Complex.I (fun z => L (sourceVector N f (ofComplex z))) (point x y))) := by
  have hd := directional_contDiffOn (readout_contDiffOn N f L) (m := 1) le_rfl Complex.I
  have h := SelbergMaassParseval.coefficient_mass_hasSum (N+1 : ℕ) (by positivity) hd.continuousOn hy
  simp_rw [coefficient_readout_vertical N f L _ hy] at h
  exact h

/-- Actual coefficient height losses have exactly the physical missing-channel vertical energy. -/
theorem complement_vertical_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖coefficientHeightVector N f n y-
      characterProjection N (lowerBlock N) r (coefficientHeightVector N f n y)‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional Complex.I (complementField N f r q) (point x y))) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => readout_vertical_hasSum N f (complementReadout N r q) hy)
  have hn (n : ℤ) : (∑ q : Deck N, normSq (complementReadout N r q (coefficientHeightVector N f n y)))=
      ‖coefficientHeightVector N f n y-characterProjection N (lowerBlock N) r (coefficientHeightVector N f n y)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm,complementReadout_apply]
    rfl
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum _ (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
    normSq (directional Complex.I (complementField N f r q) (point x y))) at h
  have hd (q : Deck N) := directional_contDiffOn
    (readout_contDiffOn N f (complementReadout N r q)) (m := 1) le_rfl Complex.I
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (hd q).continuousOn hy)).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ∑ q : Deck N, normSq (directional Complex.I (complementField N f r q) (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional Complex.I (complementField N f r q) (point x y)) at hi
  rw [← hi] at h
  exact h

/-- Each retained original character field has its exact physical vertical-energy sum. -/
theorem character_vertical_hasSum (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖characterProjection N p r (coefficientHeightVector N f n y)‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional Complex.I (characterField N f p r q) (point x y))) := by
  let L (q : Deck N) : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ :=
    (EuclideanSpace.proj q).comp (characterProjection N p r).toContinuousLinearMap
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => readout_vertical_hasSum N f (L q) hy)
  have hn (n : ℤ) : (∑ q : Deck N, normSq (L q (coefficientHeightVector N f n y)))=
      ‖characterProjection N p r (coefficientHeightVector N f n y)‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
    rfl
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum _ (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
    normSq (directional Complex.I (characterField N f p r q) (point x y))) at h
  have hd (q : Deck N) := directional_contDiffOn (readout_contDiffOn N f (L q))
    (m := 1) le_rfl Complex.I
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (hd q).continuousOn hy)).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ∑ q : Deck N, normSq (directional Complex.I (characterField N f p r q) (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional Complex.I (characterField N f p r q) (point x y)) at hi
  rw [← hi] at h
  exact h

/-- Complete original source vertical Parseval, with its actual coefficient height vector. -/
theorem coefficientVector_vertical_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖coefficientHeightVector N f n y‖^2)
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional Complex.I (field N f q) (point x y))) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => readout_vertical_hasSum N f (EuclideanSpace.proj q) hy)
  have hn (n : ℤ) : (∑ q : Deck N, normSq (coefficientHeightVector N f n y q))=
      ‖coefficientHeightVector N f n y‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Complex.sq_norm]
  change HasSum (fun n : ℤ => ∑ q : Deck N, normSq (coefficientHeightVector N f n y q)) _ at h
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum _ (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
    normSq (directional Complex.I (field N f q) (point x y))) at h
  have hd (q : Deck N) := directional_contDiffOn (quotientForm N f q).2.2.1.1
    (m := 1) le_rfl Complex.I
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (hd q).continuousOn hy)).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ∑ q : Deck N, normSq (directional Complex.I (field N f q) (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional Complex.I (field N f q) (point x y)) at hi
  rw [← hi] at h
  exact h

/-- Complete physical vertical gradient retains exactly both complementary character energies. -/
theorem vertical_energy_split (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N, normSq (directional Complex.I (field N f q) (point x y)))=
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N,
      normSq (directional Complex.I (complementField N f r q) (point x y)))+
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N,
      normSq (directional Complex.I (characterField N f (lowerBlock N) r q) (point x y))) := by
  have h := (complement_vertical_hasSum N f r hy).add
    (character_vertical_hasSum N f (lowerBlock N) r hy)
  have he (n : ℤ) :
      ‖coefficientHeightVector N f n y-characterProjection N (lowerBlock N) r (coefficientHeightVector N f n y)‖^2+
      ‖characterProjection N (lowerBlock N) r (coefficientHeightVector N f n y)‖^2=
      ‖coefficientHeightVector N f n y‖^2 := by
    rw [characterProjection_loss]
    ring
  simp_rw [he] at h
  have hEq := h.unique (coefficientVector_vertical_hasSum N f hy)
  rw [← mul_add] at hEq
  have hN : ((N+1 : ℕ) : ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  exact (mul_left_cancel₀ (inv_ne_zero hN) hEq).symm

/-- Actual height derivatives have the same single-block reduction of the complete arithmetic triple energy. -/
theorem coefficientHeight_triple_energy_eq_block (r : ZMod (N+1)) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    ((((N+1 : ℕ) : ℝ)⁻¹)^3/2) *
      (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
        ‖coefficientHeightVector N f n y-
          tripleMotion N r (n : ZMod (N+1)) a b c (coefficientHeightVector N f n y)‖^2)=
    (((N+1 : ℕ) : ℝ)⁻¹/2) *
      (∑ b : ZMod (N+1), ‖coefficientHeightVector N f n y-
        blockMotion N (lowerBlock N) (-r) b (coefficientHeightVector N f n y)‖^2) := by
  rw [triple_displacement_energy,transfer_loss_decomposition,
    coefficientHeight_upperProjection N f n hy,sub_self,norm_zero,block_displacement_energy]
  simp

/-- The complete original phase energy, including height derivatives, equals the full missing-channel physical gradient. -/
theorem source_full_gradient_phase_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ =>
      signedFrequency (N+1 : ℕ) n^2 * ((((N+1 : ℕ) : ℝ)⁻¹/2) *
        (∑ b : ZMod (N+1), ‖coefficientVector N f n y-
          blockMotion N (lowerBlock N) r b (coefficientVector N f n y)‖^2))+
      (((N+1 : ℕ) : ℝ)⁻¹/2) *
        (∑ b : ZMod (N+1), ‖coefficientHeightVector N f n y-
          blockMotion N (lowerBlock N) r b (coefficientHeightVector N f n y)‖^2))
      (((N+1 : ℕ) : ℝ)⁻¹ *
        ((∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N,
          normSq (directional 1 (complementField N f r q) (point x y)))+
         (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N,
          normSq (directional Complex.I (complementField N f r q) (point x y))))) := by
  simp_rw [block_displacement_energy]
  rw [mul_add]
  exact (complement_horizontal_hasSum N f r hy).add (complement_vertical_hasSum N f r hy)

end
end GaloisForLFunctions.RHTower.SelbergMaassCharacterGradient
