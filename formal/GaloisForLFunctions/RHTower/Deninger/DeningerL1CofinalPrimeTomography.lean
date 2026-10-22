import GaloisForLFunctions.RHTower.Deninger.DeningerDampedCompleteXiPacket
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# Original cofinal-prime tomography on all integrable sources

All original circle coefficients along unbounded positive periods determine an
integrable source almost everywhere. The proof uses every integer harmonic:
`floor(w * L) / L` tends to each real frequency `w`, and the Fourier transform of
an integrable source is continuous. L1 Fourier uniqueness then determines the
source. No exponential Schwartz decay or entire continuation is required.

For an actual integrable translation primitive, the original translation phase
is one at every lattice harmonic. Consequently, common original Green admission
over any infinite set of primes is equivalent to the source being zero almost
everywhere. The positive result is full injectivity of the original circle
observations, including equality only almost everywhere on each original cell.
A singular or nonintegrable primitive requires a separate domain comparison;
none is identified here with the fixed degree-six physical reader.
-/

open MeasureTheory Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Every real frequency is approached by harmonics of unbounded positive periods. -/
theorem deningerCofinalLattice_frequency_tendsto
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (ht : Tendsto L atTop atTop) (w : ℝ) :
    Tendsto (fun n => (⌊w*L n⌋ : ℝ)/L n) atTop (𝓝 w) := by
  have hb (n : ℕ) : 0 ≤ w-(⌊w*L n⌋ : ℝ)/L n ∧
      w-(⌊w*L n⌋ : ℝ)/L n ≤ 1/L n := by
    constructor
    · rw [sub_nonneg,div_le_iff₀ (hL n)]
      exact Int.floor_le _
    · apply (le_div_iff₀ (hL n)).mpr
      rw [sub_mul,div_mul_cancel₀ _ (hL n).ne']
      linarith [Int.lt_floor_add_one (w*L n)]
  have he : Tendsto (fun n => w-(⌊w*L n⌋ : ℝ)/L n) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2)
      (tendsto_const_nhds.div_atTop ht)
  simpa only [sub_sub_cancel,sub_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => w) atTop (𝓝 w)).sub he

/-- Complete lattice readings determine any continuous scalar response. -/
theorem deningerCofinalLattice_continuous_ext
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (ht : Tendsto L atTop atTop)
    {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G)
    (he : ∀ n (m : ℤ), F ((m : ℝ)/L n) = G ((m : ℝ)/L n)) : F = G := by
  funext w
  have hseq := deningerCofinalLattice_frequency_tendsto L hL ht w
  apply tendsto_nhds_unique ((hF.tendsto w).comp hseq)
  have htG := (hG.tendsto w).comp hseq
  exact htG.congr (fun n => (he n ⌊w*L n⌋).symm)

/-- All original circle coefficients at cofinal periods determine an L1 source. -/
theorem deningerL1CofinalCircle_coefficients_injective
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (ht : Tendsto L atTop atTop)
    (he : ∀ n (m : ℤ),
      fourierCoeffOn (hL n) (l1PeriodizationAtScale f (L n)) m =
      fourierCoeffOn (hL n) (l1PeriodizationAtScale g (L n)) m) : f =ᵐ[volume] g := by
  apply HTGeometry.ae_eq_of_fourierIntegral_eq hf hg
  have hF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hG : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have h := deningerCofinalLattice_continuous_ext L hL ht hF hG (fun n m => by
    have h := he n m
    rw [fourierCoeffOn_l1PeriodizationAtScale hf (hL n),
      fourierCoeffOn_l1PeriodizationAtScale hg (hL n)] at h
    have h' := (smul_right_injective ℂ (one_div_ne_zero (hL n).ne')).eq_iff.mp h
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h')
  exact fun w => congrFun h w

/-- Original circles over any infinite set of primes determine an integrable source. -/
theorem deningerL1PrimeCircle_coefficients_injective
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {Q : Set ℕ} (hQ : Q.Infinite) (hprime : ∀ p ∈ Q, p.Prime)
    (he : ∀ p (hp : p ∈ Q) (m : ℤ),
      fourierCoeffOn (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast (hprime p hp).one_lt))
        (l1PeriodizationAtScale f (Real.log p)) m =
      fourierCoeffOn (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast (hprime p hp).one_lt))
        (l1PeriodizationAtScale g (Real.log p)) m) : f =ᵐ[volume] g := by
  let e := Set.Infinite.natEmbedding Q hQ
  let p : ℕ → ℕ := fun n => (e n).val
  have hmem : ∀ n, p n ∈ Q := fun n => (e n).property
  have hinj : Function.Injective p := fun i j h => e.injective (Subtype.ext h)
  have hp : Tendsto p atTop atTop := by
    have h := hinj.tendsto_cofinite
    rwa [Nat.cofinite_eq_atTop] at h
  exact deningerL1CofinalCircle_coefficients_injective hf hg
    (fun n => Real.log (p n))
    (fun n => Real.log_pos (by exact_mod_cast (hprime _ (hmem n)).one_lt))
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hp))
    (fun n m => he _ (hmem n) m)

/-- Almost-everywhere equality on the original cells already determines the source. -/
theorem deningerL1PrimeCircle_periodizations_injective
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {Q : Set ℕ} (hQ : Q.Infinite) (hprime : ∀ p ∈ Q, p.Prime)
    (he : ∀ p ∈ Q, l1PeriodizationAtScale f (Real.log p) =ᵐ[volume.restrict (Set.Ioc 0 (Real.log p))]
      l1PeriodizationAtScale g (Real.log p)) : f =ᵐ[volume] g := by
  apply deningerL1PrimeCircle_coefficients_injective hf hg hQ hprime
  intro p hp m
  exact congrFun (fourierCoeffOn_congr_ae _ (he p hp)) m

/-- An actual integrable translation primitive kills every lattice Fourier sample. -/
theorem deningerL1OriginalGreen_fourier_lattice_zero
    {f g : ℝ → ℂ} (hg : Integrable g) {L : ℝ} (hL : L ≠ 0)
    (he : f =ᵐ[volume] (fun x => g x-g (x+L))) (m : ℤ) :
    𝓕 f ((m : ℝ)/L) = 0 := by
  have hphase : (Real.fourierChar (L*((m : ℝ)/L)) : ℂ) = 1 := by
    rw [show L*((m : ℝ)/L)=(m : ℝ) by field_simp,Real.fourierChar_apply]
    convert Complex.exp_int_mul_two_pi_mul_I m using 1
    congr 1
    push_cast
    ring
  have htranslate : 𝓕 (fun x => g (x+L)) ((m : ℝ)/L) = 𝓕 g ((m : ℝ)/L) := by
    have h := congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) g L) ((m : ℝ)/L)
    have h' : 𝓕 (fun x => g (x+L)) ((m : ℝ)/L) =
        (Real.fourierChar (L*((m : ℝ)/L)) : ℂ)*𝓕 g ((m : ℝ)/L) := by
      simpa [Real.fourier_eq,Fourier.fourierIntegral_def,Circle.smul_def,
        Function.comp_apply,mul_comm] using h
    simpa only [hphase,one_mul] using h'
  rw [Real.fourier_congr_ae he]
  calc
    _ = 𝓕 g ((m : ℝ)/L)-𝓕 (fun x => g (x+L)) ((m : ℝ)/L) := by
      rw [Real.fourier_eq,Real.fourier_eq,Real.fourier_eq]
      simp only [smul_sub]
      exact integral_sub
        ((Real.fourierIntegral_convergent_iff _).mpr hg)
        ((Real.fourierIntegral_convergent_iff _).mpr (hg.comp_add_right L))
    _ = 0 := by rw [htranslate,sub_self]

/-- No nonzero integrable source lies in all original Green ranges at cofinal periods. -/
theorem deningerL1CofinalOriginalGreen_eq_zero
    {f : ℝ → ℂ} (hf : Integrable f)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (ht : Tendsto L atTop atTop)
    (hgreen : ∀ n, ∃ g : ℝ → ℂ, Integrable g ∧
      f =ᵐ[volume] (fun x => g x-g (x+L n))) : f =ᵐ[volume] 0 := by
  apply HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hf
  have hF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have h := deningerCofinalLattice_continuous_ext L hL ht hF continuous_const (fun n m => by
    obtain ⟨g,hg,he⟩ := hgreen n
    exact deningerL1OriginalGreen_fourier_lattice_zero hg (hL n).ne' he m)
  exact fun w => congrFun h w

/-- Exact common-domain classification over every infinite set of original primes. -/
theorem deningerL1PrimeOriginalGreen_iff_zero
    {f : ℝ → ℂ} (hf : Integrable f) {Q : Set ℕ}
    (hQ : Q.Infinite) (hprime : ∀ p ∈ Q, p.Prime) :
    (∀ p ∈ Q, ∃ g : ℝ → ℂ, Integrable g ∧
      f =ᵐ[volume] (fun x => g x-g (x+Real.log p))) ↔ f =ᵐ[volume] 0 := by
  constructor
  · intro hgreen
    let e := Set.Infinite.natEmbedding Q hQ
    let p : ℕ → ℕ := fun n => (e n).val
    have hmem : ∀ n, p n ∈ Q := fun n => (e n).property
    have hinj : Function.Injective p := fun i j h => e.injective (Subtype.ext h)
    have hp : Tendsto p atTop atTop := by
      have h := hinj.tendsto_cofinite
      rwa [Nat.cofinite_eq_atTop] at h
    exact deningerL1CofinalOriginalGreen_eq_zero hf
      (fun n => Real.log (p n))
      (fun n => Real.log_pos (by exact_mod_cast (hprime _ (hmem n)).one_lt))
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hp))
      (fun n => hgreen _ (hmem n))
  · intro hf p hp
    refine ⟨0,integrable_zero ℝ ℂ volume,?_⟩
    filter_upwards [hf] with x hx
    simpa using hx

end RHTower
