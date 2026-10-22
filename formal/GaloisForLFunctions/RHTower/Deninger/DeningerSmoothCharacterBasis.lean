import GaloisForLFunctions.RHTower.Deninger.DeningerFourierCharacter
import GaloisForLFunctions.RHTower.Deninger.DeningerSmoothPeriodicNuclear

/-!
# The characters as basis vectors of the smooth periodic test space

A character is smooth and periodic, and its coefficient sequence is a standard basis vector of the
Köthe space.  The coefficient map is therefore an isometry of the seminorm quotients carrying the
characters to the basis vectors, and since an isometry reflects convergence, a smooth periodic
function is the sum of its coefficients against the characters in every coefficient seminorm.

* `deningerCharacterMem` : the characters as elements of the smooth periodic space.
* `deningerSmoothCoeff_character` : their coefficient sequences are the basis vectors.
* `deningerHasSum_of_isometry` : an isometry reflects convergence.
* `deningerSmooth_hasSum` : **a smooth periodic function is the sum of its coefficients.**
-/

namespace RHTower

open Complex

section IsometryHasSum

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **An isometry reflects convergence of series.** -/
theorem deningerHasSum_of_isometry (J : X →L[𝕜] Y) (hJ : ∀ x, ‖J x‖ = ‖x‖) {ι : Type*}
    {f : ι → X} {a : X} (h : HasSum (fun i => J (f i)) (J a)) : HasSum f a := by
  have hiso : Isometry J := AddMonoidHomClass.isometry_of_norm _ hJ
  rw [HasSum] at h ⊢
  refine (hiso.isEmbedding.tendsto_nhds_iff).mpr ?_
  simpa [map_sum, Function.comp_def] using h

end IsometryHasSum

section CharacterBasis

variable {T : ℝ} [Fact (0 < T)]

theorem deningerCharacter_periodic' (n : ℤ) : Function.Periodic (deningerCharacter T n) T := by
  intro x
  have hT : (T : ℂ) ≠ 0 := by
    have := (Fact.out : (0 : ℝ) < T)
    exact_mod_cast this.ne'
  rw [deningerCharacter_apply, deningerCharacter_apply]
  have hsplit : 2 * Real.pi * Complex.I * n * ((x + T : ℝ) : ℂ) / T
      = 2 * Real.pi * Complex.I * n * (x : ℂ) / T + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [Fact (0 < T)] in
theorem deningerCharacter_contDiff (n : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (deningerCharacter T n) := by
  have hfun : deningerCharacter T n
      = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * (x : ℂ) / T) :=
    funext (deningerCharacter_apply n)
  rw [hfun]
  refine Complex.contDiff_exp.comp ?_
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _

/-- **The characters as elements of the smooth periodic test space.** -/
noncomputable def deningerCharacterMem (n : ℤ) : DeningerSmoothPeriodic T :=
  ⟨deningerCharacter T n, deningerCharacter_contDiff n, deningerCharacter_periodic' n⟩

@[simp]
theorem deningerCharacterMem_coe (n : ℤ) :
    ((deningerCharacterMem (T := T) n : DeningerSmoothPeriodic T) : ℝ → ℂ)
      = deningerCharacter T n := rfl

/-- **The coefficient sequence of a character is a standard basis vector.** -/
theorem deningerSmoothCoeff_character (hT : 0 < T) (n : ℤ) :
    deningerSmoothCoeff hT (deningerCharacterMem n)
      = deningerKotheDelta (𝕜 := ℂ) deningerFourierWeights n := by
  refine Subtype.ext (funext fun m => ?_)
  show deningerFourierCoeff T (deningerCharacter T n) m = _
  rw [deningerFourierCoeff_character hT n m]
  show _ = (Pi.single n 1 : ℤ → ℂ) m
  by_cases hm : m = n
  · subst hm
    simp
  · simp [hm]

end CharacterBasis

section SmoothNuclearDirect

variable {T : ℝ} [Fact (0 < T)]

omit [Fact (0 < T)] in
theorem deningerSmoothSeminorm_kothe (hT : 0 < T) (k : ℕ) (f : DeningerSmoothPeriodic T) :
    deningerSmoothSeminorm hT k f
      = deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k (deningerSmoothCoeff hT f) := rfl

/-- The map of seminorm quotients induced by the coefficient map. -/
noncomputable def deningerSmoothToKothe (hT : 0 < T) (k : ℕ) :
    DeningerSeminormSpace (deningerSmoothSeminorm hT k) →L[ℂ]
      DeningerSeminormSpace (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k) :=
  LinearMap.mkContinuous
    (Submodule.liftQ (deningerSeminormKer (deningerSmoothSeminorm hT k))
      ((deningerSeminormMk (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k)).comp
        (deningerSmoothCoeff hT)) (by
        intro f hf
        have hzero : deningerSmoothSeminorm hT k f = 0 := hf
        have hnorm : ‖deningerSeminormMk (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k)
            (deningerSmoothCoeff hT f)‖ = 0 := by
          rw [deningerSeminormMk_norm, ← deningerSmoothSeminorm_kothe hT k f, hzero]
        exact norm_eq_zero.mp hnorm))
    1 (by
      rintro ⟨f⟩
      show ‖deningerSeminormMk (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k)
          (deningerSmoothCoeff hT f)‖ ≤ 1 * ‖deningerSeminormMk (deningerSmoothSeminorm hT k) f‖
      rw [one_mul, deningerSeminormMk_norm, deningerSeminormMk_norm,
        deningerSmoothSeminorm_kothe hT k f])

omit [Fact (0 < T)] in
@[simp]
theorem deningerSmoothToKothe_mk (hT : 0 < T) (k : ℕ) (f : DeningerSmoothPeriodic T) :
    deningerSmoothToKothe hT k (deningerSeminormMk (deningerSmoothSeminorm hT k) f)
      = deningerSeminormMk (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k)
        (deningerSmoothCoeff hT f) := rfl

omit [Fact (0 < T)] in
theorem deningerSmoothToKothe_norm (hT : 0 < T) (k : ℕ)
    (x : DeningerSeminormSpace (deningerSmoothSeminorm hT k)) :
    ‖deningerSmoothToKothe hT k x‖ = ‖x‖ := by
  obtain ⟨f, rfl⟩ := deningerSeminormMk_surjective (deningerSmoothSeminorm hT k) x
  rw [deningerSmoothToKothe_mk, deningerSeminormMk_norm, deningerSeminormMk_norm,
    deningerSmoothSeminorm_kothe hT k f]

/-- **A smooth periodic function is the sum of its coefficients against the characters**, in every
coefficient seminorm. -/
theorem deningerSmooth_hasSum (hT : 0 < T) (k : ℕ) (f : DeningerSmoothPeriodic T) :
    HasSum (fun n : ℤ => deningerFourierCoeff T (f : ℝ → ℂ) n •
        deningerSeminormMk (deningerSmoothSeminorm hT k) (deningerCharacterMem n))
      (deningerSeminormMk (deningerSmoothSeminorm hT k) f) := by
  refine deningerHasSum_of_isometry (deningerSmoothToKothe hT k)
    (deningerSmoothToKothe_norm hT k) ?_
  have hkothe := deningerKothe_hasSum (𝕜 := ℂ) deningerFourierWeights k
    (deningerSmoothCoeff hT f)
  have hfun : (fun n : ℤ => deningerSmoothToKothe hT k
        (deningerFourierCoeff T (f : ℝ → ℂ) n •
          deningerSeminormMk (deningerSmoothSeminorm hT k) (deningerCharacterMem n)))
      = fun n : ℤ =>
        ((deningerSmoothCoeff hT f : DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n •
          deningerSeminormMk (deningerKotheSeminorm (𝕜 := ℂ) deningerFourierWeights k)
            (deningerKotheDelta (𝕜 := ℂ) deningerFourierWeights n) := by
    funext n
    rw [map_smul, deningerSmoothToKothe_mk, deningerSmoothCoeff_character hT n]
    rfl
  rw [hfun, deningerSmoothToKothe_mk]
  exact hkothe

/-- **The smooth periodic test space is nuclear**, with the characters as basis vectors and the
coefficients as functionals. -/
theorem deningerSmoothPeriodic_isNuclearSpace (hT : 0 < T) :
    DeningerIsNuclearSpace (deningerSmoothSeminorm hT) := by
  intro k
  obtain ⟨m, hkm, hsum⟩ := deningerFourierWeights_isNuclear k
  have hdom : ∀ f : DeningerSmoothPeriodic T,
      deningerSmoothSeminorm hT k f ≤ 1 * deningerSmoothSeminorm hT m f := by
    intro f
    rw [one_mul, deningerSmoothSeminorm_kothe hT k f, deningerSmoothSeminorm_kothe hT m f]
    exact deningerKotheSeminorm_le (𝕜 := ℂ) deningerFourierWeights hkm _
  refine ⟨m, 1, hdom, ?_⟩
  refine ⟨ℤ, fun n => (deningerKotheCoeff (𝕜 := ℂ) deningerFourierWeights m n).comp
      (deningerSmoothToKothe hT m),
    fun n => deningerSeminormMk (deningerSmoothSeminorm hT k) (deningerCharacterMem n), ?_, ?_⟩
  · refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun n => ?_) hsum
    have hvec : ‖deningerSeminormMk (deningerSmoothSeminorm hT k) (deningerCharacterMem n)‖
        = deningerFourierWeights.w k n := by
      rw [deningerSeminormMk_norm, deningerSmoothSeminorm_kothe hT k,
        deningerSmoothCoeff_character hT n,
        deningerKotheSeminorm_delta (𝕜 := ℂ) deningerFourierWeights k n]
    have hfun : ‖(deningerKotheCoeff (𝕜 := ℂ) deningerFourierWeights m n).comp
        (deningerSmoothToKothe hT m)‖ ≤ (deningerFourierWeights.w m n)⁻¹ := by
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      have h1 := deningerKotheCoeff_norm_le (𝕜 := ℂ) deningerFourierWeights m n
      have h2 : ‖deningerSmoothToKothe hT m‖ ≤ 1 :=
        LinearMap.mkContinuous_norm_le _ zero_le_one _
      calc ‖deningerKotheCoeff (𝕜 := ℂ) deningerFourierWeights m n‖ * ‖deningerSmoothToKothe hT m‖
          ≤ (deningerFourierWeights.w m n)⁻¹ * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _)
              (inv_nonneg.mpr (deningerFourierWeights.pos m n).le)
        _ = (deningerFourierWeights.w m n)⁻¹ := by ring
    rw [hvec]
    calc ‖(deningerKotheCoeff (𝕜 := ℂ) deningerFourierWeights m n).comp
          (deningerSmoothToKothe hT m)‖ * deningerFourierWeights.w k n
        ≤ (deningerFourierWeights.w m n)⁻¹ * deningerFourierWeights.w k n :=
          mul_le_mul_of_nonneg_right hfun (deningerFourierWeights.pos k n).le
      _ = deningerFourierWeights.w k n / deningerFourierWeights.w m n := by
          rw [inv_mul_eq_div, div_eq_div_iff (deningerFourierWeights.pos m n).ne'
            (deningerFourierWeights.pos m n).ne']
  · intro x
    obtain ⟨f, rfl⟩ := deningerSeminormMk_surjective (deningerSmoothSeminorm hT m) x
    exact deningerSmooth_hasSum hT k f

/-- **Every subspace of the smooth periodic test space is nuclear**, the compactly supported
smooth functions of a suspension factor in particular. -/
theorem deningerSmoothSubspace_isNuclearSpaceC (hT : 0 < T)
    (F : Submodule ℂ (DeningerSmoothPeriodic T)) :
    DeningerIsNuclearSpaceC
      (fun k : ℕ => deningerRestrictSeminorm F (deningerSmoothSeminorm hT k)) :=
  deningerIsNuclearSpaceC_subspace _ F (deningerSmoothPeriodic_isNuclearSpace hT)

end SmoothNuclearDirect

end RHTower
