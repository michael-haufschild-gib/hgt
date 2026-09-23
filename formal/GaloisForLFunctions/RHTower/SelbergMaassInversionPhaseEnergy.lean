import GaloisForLFunctions.RHTower.SelbergMaassInversionGram

/-!
# Exact arithmetic phase energy of original Maass inversion

The complete phased three-factor motion average has precisely the inversion-transfer
norm loss. Orthogonal upper and lower character losses split it exactly, and the
original Fourier eigenspace constraint reduces it to one lower-block displacement
average. Full source Parseval identifies the convergent physical missing-channel
mass. Actual horizontal gradient controls the complete frequency-weighted phase loss.
-/

open Complex Set UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassInversionPhaseEnergy
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassUnipotentBlocks
open SelbergMaassCharacterProjection SelbergMaassCharacterFourier SelbergMaassInversionGram
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- The original arithmetic phase multiplying its actual three-block deck motion. -/
def tripleMotion (N : ℕ) (r s a b c : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) : EuclideanSpace ℂ (Deck N) :=
  tripleWeight N r s a b c • finiteRegularUnitary (deckTriple N a b c) v

/-- Every original phase-weighted word preserves the complete deck norm. -/
theorem tripleMotion_norm (N : ℕ) (r s a b c : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) : ‖tripleMotion N r s a b c v‖=‖v‖ := by
  rw [tripleMotion,norm_smul,tripleWeight_norm,one_mul,LinearIsometryEquiv.norm_map]

/-- The actual Gram operator is the complete average of original phased motions. -/
theorem transferGram_eq_average (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    transferGram N r s v=(((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) •
      ∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
        tripleMotion N r s a b c v := by
  ext q
  rw [transferGram_coord]
  change _=(((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ) *
    (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
      tripleMotion N r s a b c v).ofLp q
  simp only [WithLp.ofLp_sum,Finset.sum_apply,tripleMotion]
  rfl

/-- The normalized phase correlations are exactly the original transfer energy. -/
theorem transfer_inner_average (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    (((N+1 : ℕ) : ℝ)⁻¹)^(3 : ℕ) *
      (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
        (inner ℂ (tripleMotion N r s a b c v) v).re)=‖inversionTransfer N r s v‖^(2 : ℕ) := by
  rw [← transferGram_inner,transferGram_eq_average]
  have hc : (((N+1 : ℕ) : ℂ)⁻¹)^(3 : ℕ)=
      ((((N+1 : ℕ) : ℝ)⁻¹)^(3 : ℕ) : ℝ) := by push_cast; rfl
  rw [hc,inner_smul_left]
  simp only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,sum_inner,Complex.re_sum]

/-- The full phase-displacement energy equals the actual inversion-transfer loss. -/
theorem triple_displacement_energy (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ((((N+1 : ℕ) : ℝ)⁻¹)^(3 : ℕ)/2) *
      (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
        ‖v-tripleMotion N r s a b c v‖^(2 : ℕ)) =
      ‖v‖^(2 : ℕ)-‖inversionTransfer N r s v‖^(2 : ℕ) := by
  have ht (a b c : ZMod (N+1)) : ‖v-tripleMotion N r s a b c v‖^(2 : ℕ)=
      2*‖v‖^(2 : ℕ)-2*(inner ℂ (tripleMotion N r s a b c v) v).re := by
    rw [norm_sub_rev,norm_sub_sq (𝕜 := ℂ),tripleMotion_norm]
    change ‖v‖^(2 : ℕ)-2*(inner ℂ (tripleMotion N r s a b c v) v).re+‖v‖^(2 : ℕ)=_
    ring
  simp_rw [ht,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have h := transfer_inner_average N r s v
  have hN : ((N+1 : ℕ) : ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  rw [← h]
  field_simp

/-- Every original character projector has its exact orthogonal loss splitting. -/
theorem characterProjection_loss (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ‖v-characterProjection N p r v‖^(2 : ℕ)=‖v‖^(2 : ℕ)-‖characterProjection N p r v‖^(2 : ℕ) := by
  rw [norm_sub_rev,norm_sub_sq (𝕜 := ℂ),characterProjection_inner_left]
  rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  ring

/-- The lower projected input has exactly the inversion-transfer norm. -/
theorem lowerProjection_transfer_norm (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ‖characterProjection N (lowerBlock N) (-r) (characterProjection N (upperBlock N) s v)‖=
      ‖inversionTransfer N r s v‖ := by
  rw [characterProjection_lower_conjugate,neg_neg,LinearIsometryEquiv.norm_map]
  rfl

/-- The actual inversion loss retains both successive orthogonal character losses. -/
theorem transfer_loss_decomposition (N : ℕ) (r s : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ‖v‖^(2 : ℕ)-‖inversionTransfer N r s v‖^(2 : ℕ)=
      ‖v-characterProjection N (upperBlock N) s v‖^(2 : ℕ)+
      ‖characterProjection N (upperBlock N) s v-
        characterProjection N (lowerBlock N) (-r) (characterProjection N (upperBlock N) s v)‖^(2 : ℕ) := by
  rw [characterProjection_loss,characterProjection_loss,lowerProjection_transfer_norm]
  ring

/-- Summing the diagonal inversion losses leaves at least `N` full deck energies.
The upper-character decomposition is exact; the second lower-character loss is nonnegative. -/
theorem diagonal_transfer_loss_sum_lower (N : ℕ) (v : EuclideanSpace ℂ (Deck N)) :
    (N : ℝ)*‖v‖^(2 : ℕ) ≤
      ∑ r : ZMod (N+1), (‖v‖^(2 : ℕ)-‖inversionTransfer N r r v‖^(2 : ℕ)) := by
  have hpoint (r : ZMod (N+1)) :
      ‖v-characterProjection N (upperBlock N) r v‖^(2 : ℕ) ≤
        ‖v‖^(2 : ℕ)-‖inversionTransfer N r r v‖^(2 : ℕ) := by
    rw [transfer_loss_decomposition]
    exact le_add_of_nonneg_right (sq_nonneg _)
  calc
    (N : ℝ)*‖v‖^(2 : ℕ) = ∑ r : ZMod (N+1), ‖v-characterProjection N (upperBlock N) r v‖^(2 : ℕ) := by
      simp_rw [characterProjection_loss]
      rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        sum_characterProjection_norm_sq, ZMod.card]
      push_cast
      ring
    _ ≤ ∑ r : ZMod (N+1), (‖v‖^(2 : ℕ)-‖inversionTransfer N r r v‖^(2 : ℕ)) :=
      Finset.sum_le_sum (fun r _ => hpoint r)

/-- The original character phase multiplying one actual block motion. -/
def blockMotion (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r b : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) : EuclideanSpace ℂ (Deck N) :=
  ZMod.stdAddChar (-(r*b)) • finiteRegularUnitary (p (Multiplicative.ofAdd b)) v

/-- Every actual character-twisted block motion preserves the full deck norm. -/
theorem blockMotion_norm (N : ℕ) (p : Multiplicative (ZMod (N+1)) →* Deck N)
    (r b : ZMod (N+1)) (v : EuclideanSpace ℂ (Deck N)) :
    ‖blockMotion N p r b v‖=‖v‖ := by
  have hp : ‖ZMod.stdAddChar (-(r*b))‖=1 := by
    rw [ZMod.stdAddChar_apply]
    exact (ZMod.toCircle (-(r*b))).norm_coe
  rw [blockMotion,norm_smul,hp,one_mul,LinearIsometryEquiv.norm_map]

/-- The actual character projector is the average of its twisted block motions. -/
theorem characterProjection_eq_average (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    characterProjection N p r v=((N+1 : ℕ) : ℂ)⁻¹ •
      ∑ b : ZMod (N+1), blockMotion N p r b v := by
  ext q
  rw [projection_coord_add]
  change _=((N+1 : ℕ) : ℂ)⁻¹ *
    (∑ b : ZMod (N+1), blockMotion N p r b v).ofLp q
  simp only [WithLp.ofLp_sum,Finset.sum_apply,blockMotion]
  simp_rw [← AddChar.inv_apply_eq_conj,← AddChar.map_neg_eq_inv]
  rfl

/-- Original block correlations recover the exact projected source norm. -/
theorem block_inner_average (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    ((N+1 : ℕ) : ℝ)⁻¹ *
      (∑ b : ZMod (N+1), (inner ℂ (blockMotion N p r b v) v).re)=
        ‖characterProjection N p r v‖^(2 : ℕ) := by
  have he : (inner ℂ (characterProjection N p r v) v).re=
      ‖characterProjection N p r v‖^(2 : ℕ) := by
    rw [characterProjection_inner_left]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  rw [← he,characterProjection_eq_average]
  have hc : ((N+1 : ℕ) : ℂ)⁻¹=((((N+1 : ℕ) : ℝ)⁻¹) : ℝ) := by push_cast; rfl
  rw [hc,inner_smul_left]
  simp only [Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,sum_inner,Complex.re_sum]

/-- Exact twisted displacement energy of each original block-character projector. -/
theorem block_displacement_energy (N : ℕ)
    (p : Multiplicative (ZMod (N+1)) →* Deck N) (r : ZMod (N+1))
    (v : EuclideanSpace ℂ (Deck N)) :
    (((N+1 : ℕ) : ℝ)⁻¹/2) *
      (∑ b : ZMod (N+1), ‖v-blockMotion N p r b v‖^(2 : ℕ))=
        ‖v-characterProjection N p r v‖^(2 : ℕ) := by
  rw [characterProjection_loss]
  have ht (b : ZMod (N+1)) : ‖v-blockMotion N p r b v‖^(2 : ℕ)=
      2*‖v‖^(2 : ℕ)-2*(inner ℂ (blockMotion N p r b v) v).re := by
    rw [norm_sub_rev,norm_sub_sq (𝕜 := ℂ),blockMotion_norm]
    change ‖v‖^(2 : ℕ)-2*(inner ℂ (blockMotion N p r b v) v).re+‖v‖^(2 : ℕ)=_
    ring
  simp_rw [ht,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  rw [← block_inner_average N p r v]
  have hN : ((N+1 : ℕ) : ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero N
  field_simp

open SelbergMaassMean SelbergMaassUnipotentFourier MeasureTheory
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Every actual Fourier coefficient loses exactly its lower-character complement. -/
theorem coefficient_transfer_loss (r : ZMod (N+1)) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖coefficientVector N f n y‖^(2 : ℕ)-
      ‖inversionTransfer N r (n : ZMod (N+1)) (coefficientVector N f n y)‖^(2 : ℕ)=
        ‖coefficientVector N f n y-
          characterProjection N (lowerBlock N) (-r) (coefficientVector N f n y)‖^(2 : ℕ) := by
  rw [transfer_loss_decomposition,
    upperProjection_coefficientVector N f (n : ZMod (N+1)) n hy,if_pos rfl,sub_self,norm_zero]
  simp

/-- On actual Fourier coefficients the full triple energy collapses to one lower-block average. -/
theorem coefficient_triple_energy_eq_block (r : ZMod (N+1)) (n : ℤ)
    {y : ℝ} (hy : 0 < y) :
    ((((N+1 : ℕ) : ℝ)⁻¹)^(3 : ℕ)/2) *
      (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
        ‖coefficientVector N f n y-
          tripleMotion N r (n : ZMod (N+1)) a b c (coefficientVector N f n y)‖^(2 : ℕ))=
    (((N+1 : ℕ) : ℝ)⁻¹/2) *
      (∑ b : ZMod (N+1), ‖coefficientVector N f n y-
        blockMotion N (lowerBlock N) (-r) b (coefficientVector N f n y)‖^(2 : ℕ)) := by
  rw [triple_displacement_energy,coefficient_transfer_loss N f r n hy,block_displacement_energy]

open SelbergMaassFourier SelbergMaassSourceCurrents

/-- Parseval for the literal complete original Fourier source vector. -/
theorem coefficientVector_mass_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖coefficientVector N f n y‖^(2 : ℕ))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖sourceVector N f (ofComplex (point x y))‖^(2 : ℕ)) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => SelbergMaassParseval.maass_mass_hasSum N (quotientForm N f q) hy)
  have hn (n : ℤ) :
      (∑ q : Deck N, normSq (maassCoefficient N (quotientForm N f q) n y))=
        ‖coefficientVector N f n y‖^(2 : ℕ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [coefficientVector,WithLp.ofLp_toLp,Complex.sq_norm]
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum (fun n : ℤ => ‖coefficientVector N f n y‖^(2 : ℕ))
    (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (field N f q (point x y))) at h
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy)).intervalIntegrable
        (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ), ∑ q : Deck N, normSq (field N f q (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ), normSq (field N f q (point x y)) at hi
  rw [← hi] at h
  have he (x : ℝ) :
      (∑ q : Deck N, normSq (field N f q (point x y)))=
        ‖sourceVector N f (ofComplex (point x y))‖^(2 : ℕ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [sourceVector,field,WithLp.ofLp_toLp,Complex.sq_norm,Function.comp_def]
  simp_rw [he] at h
  exact h

/-- Complete original coefficient loss has exactly the physical slice mass difference. -/
theorem coefficient_transfer_loss_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ =>
      ‖coefficientVector N f n y-
        characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^(2 : ℕ))
      (((N+1 : ℕ) : ℝ)⁻¹ *
        ((∫ x in (0 : ℝ)..(N+1 : ℕ), ‖sourceVector N f (ofComplex (point x y))‖^(2 : ℕ))-
         (∫ x in (0 : ℝ)..(N+1 : ℕ),
           ‖characterProjection N (lowerBlock N) r (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ)))) := by
  have h := (coefficientVector_mass_hasSum N f hy).sub
    (character_mass_hasSum N f (lowerBlock N) r hy)
  simp_rw [← characterProjection_loss] at h
  rw [← mul_sub] at h
  exact h

/-- The full original arithmetic phase displacement sum converges to physical missing channel mass. -/
theorem source_triple_displacement_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ =>
      ((((N+1 : ℕ) : ℝ)⁻¹)^(3 : ℕ)/2) *
        (∑ a : ZMod (N+1), ∑ b : ZMod (N+1), ∑ c : ZMod (N+1),
          ‖coefficientVector N f n y-
            tripleMotion N (-r) (n : ZMod (N+1)) a b c (coefficientVector N f n y)‖^(2 : ℕ)))
      (((N+1 : ℕ) : ℝ)⁻¹ *
        ((∫ x in (0 : ℝ)..(N+1 : ℕ), ‖sourceVector N f (ofComplex (point x y))‖^(2 : ℕ))-
         (∫ x in (0 : ℝ)..(N+1 : ℕ),
           ‖characterProjection N (lowerBlock N) r (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ)))) := by
  simp_rw [triple_displacement_energy,coefficient_transfer_loss N f (-r) _ hy,neg_neg]
  exact coefficient_transfer_loss_hasSum N f r hy

/-- Horizontal gradient Parseval for the actual complete original coefficient vector. -/
theorem coefficientVector_horizontal_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^(2 : ℕ) * ‖coefficientVector N f n y‖^(2 : ℕ))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional 1 (field N f q) (point x y))) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => SelbergMaassParseval.maass_horizontal_hasSum N (quotientForm N f q) hy)
  have hn (n : ℤ) :
      (∑ q : Deck N, signedFrequency (N+1 : ℕ) n^(2 : ℕ) *
        normSq (maassCoefficient N (quotientForm N f q) n y))=
          signedFrequency (N+1 : ℕ) n^(2 : ℕ) * ‖coefficientVector N f n y‖^(2 : ℕ) := by
    rw [← Finset.mul_sum,EuclideanSpace.norm_sq_eq]
    simp only [coefficientVector,WithLp.ofLp_toLp,Complex.sq_norm]
  simp_rw [hn] at h
  rw [← Finset.mul_sum] at h
  change HasSum (fun n : ℤ => signedFrequency (N+1 : ℕ) n^(2 : ℕ) * ‖coefficientVector N f n y‖^(2 : ℕ))
    (((N+1 : ℕ) : ℝ)⁻¹ * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional 1 (field N f q) (point x y))) at h
  have hd (q : Deck N) := directional_contDiffOn (quotientForm N f q).2.2.1.1
    (m := 1) le_rfl (1 : ℂ)
  have hi := intervalIntegral.integral_finsetSum (μ := volume)
    (s := (Finset.univ : Finset (Deck N)))
    (fun q _ => (Complex.continuous_normSq.comp
      (slice_continuous (hd q).continuousOn hy)).intervalIntegrable (0 : ℝ) (N+1 : ℕ))
  change (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ∑ q : Deck N, normSq (directional 1 (field N f q) (point x y)))=
    ∑ q : Deck N, ∫ x in (0 : ℝ)..(N+1 : ℕ),
      normSq (directional 1 (field N f q) (point x y)) at hi
  rw [← hi] at h
  exact h

/-- Original phase loss is bounded by the complete coefficient energy. -/
theorem coefficient_transfer_loss_le (r : ZMod (N+1)) (n : ℤ) (y : ℝ) :
    ‖coefficientVector N f n y-
      characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^(2 : ℕ) ≤
        ‖coefficientVector N f n y‖^(2 : ℕ) := by
  rw [characterProjection_loss]
  exact sub_le_self _ (sq_nonneg _)

/-- The frequency-weighted actual phase loss has a convergent full integer sum. -/
theorem weighted_phase_loss_summable (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℤ => signedFrequency (N+1 : ℕ) n^(2 : ℕ) *
      ‖coefficientVector N f n y-
        characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^(2 : ℕ)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _
    (coefficientVector_horizontal_hasSum N f hy).summable
  intro n
  exact mul_le_mul_of_nonneg_left (coefficient_transfer_loss_le N f r n y) (sq_nonneg _)

/-- Actual horizontal gradient bounds the complete frequency-weighted arithmetic phase loss. -/
theorem weighted_phase_loss_le_horizontal (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, signedFrequency (N+1 : ℕ) n^(2 : ℕ) *
      ‖coefficientVector N f n y-
        characterProjection N (lowerBlock N) r (coefficientVector N f n y)‖^(2 : ℕ)) ≤
      ((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ∑ q : Deck N, normSq (directional 1 (field N f q) (point x y)) := by
  have h := coefficientVector_horizontal_hasSum N f hy
  rw [← h.tsum_eq]
  exact (weighted_phase_loss_summable N f r hy).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (coefficient_transfer_loss_le N f r n y) (sq_nonneg _))
    h.summable

/-- The exact physical source mass difference is the integral of its character complement. -/
theorem source_complement_mass_eq (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ‖sourceVector N f (ofComplex (point x y))-
        characterProjection N (lowerBlock N) r (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ))=
    (∫ x in (0 : ℝ)..(N+1 : ℕ), ‖sourceVector N f (ofComplex (point x y))‖^(2 : ℕ))-
    (∫ x in (0 : ℝ)..(N+1 : ℕ),
      ‖characterProjection N (lowerBlock N) r (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ)) := by
  simp_rw [characterProjection_loss]
  apply intervalIntegral.integral_sub
  · exact ((sourceSlice_continuous N f hy).norm.pow 2).intervalIntegrable _ _
  · exact (((characterProjection N (lowerBlock N) r).toContinuousLinearMap.continuous.comp
      (sourceSlice_continuous N f hy)).norm.pow 2).intervalIntegrable _ _

/-- The complete original lower-character phase sum is exactly its physical complement mass. -/
theorem source_block_displacement_hasSum (r : ZMod (N+1)) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => (((N+1 : ℕ) : ℝ)⁻¹/2) *
      (∑ b : ZMod (N+1), ‖coefficientVector N f n y-
        blockMotion N (lowerBlock N) r b (coefficientVector N f n y)‖^(2 : ℕ)))
      (((N+1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N+1 : ℕ),
        ‖sourceVector N f (ofComplex (point x y))-
          characterProjection N (lowerBlock N) r (sourceVector N f (ofComplex (point x y)))‖^(2 : ℕ)) := by
  simp_rw [block_displacement_energy]
  rw [source_complement_mass_eq N f r hy]
  exact coefficient_transfer_loss_hasSum N f r hy

end
end GaloisForLFunctions.RHTower.SelbergMaassInversionPhaseEnergy
