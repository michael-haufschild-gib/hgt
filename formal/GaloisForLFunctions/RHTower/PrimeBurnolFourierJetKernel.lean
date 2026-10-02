import GaloisForLFunctions.RHTower.PrimeBurnolFourierPair
import GaloisForLFunctions.RHTower.PrimeBurnolConfluentMomentGram
import GaloisForLFunctions.RHTower.SoninDilationContinuity
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.HTGeometry.MaximalRealL2Multiplication

/-!
# Literal Fourier–radial-jet collision exclusion

Position square is taken on its actual maximal physical L2 domain. Exact dilation covariance,
Fourier inversion of dilations, and positive position energy exclude its Fourier commutator
kernel. Consequently retaining both f+F g and M f+F M g gives an injective source map.
Every literal prime-depth column is admitted, and its M image is precisely the even radial jet
of order two. The proof works on full physical L2, hence also on the even source carrier.

This does not assert graph-closure injectivity, prime-depth graph-core density, Gamma–Xi
identification, a Hardy-index comparison, or the TG sub-unit bound.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace LinearPMap
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Literal position square on its maximal physical L2 domain. -/
def burnolSquarePosition : SoninL2 →ₗ.[ℂ] SoninL2 :=
  maximalRealL2Mul volume (fun x : ℝ => x^2)

private theorem square_position_ae (f : burnolSquarePosition.domain) :
    (burnolSquarePosition f : ℝ → ℂ) =ᵐ[volume] fun x => (x^2 : ℝ) * (f : SoninL2) x :=
  maximalRealL2Mul_apply_ae volume (fun x : ℝ => x^2) f

private theorem square_dilation_ae (r : ℝ) (hr : 0 < r) (f : burnolSquarePosition.domain) :
    (fun x : ℝ => (x^2 : ℝ) * (dilation r hr (f : SoninL2)) x) =ᵐ[volume]
      fun x => (r : ℂ)⁻¹^2 * (dilation r hr (burnolSquarePosition f)) x := by
  have hcomp := (square_position_ae f).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [dilation_ae r hr (f : SoninL2),
    dilation_ae r hr (burnolSquarePosition f), hcomp] with x hf hm hfx
  rw [hf, hm]
  change (burnolSquarePosition f) (r*x) = (((r*x)^2 : ℝ) : ℂ) * (f : SoninL2) (r*x) at hfx
  rw [hfx]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp

private theorem square_dilation_mem (r : ℝ) (hr : 0 < r) (f : burnolSquarePosition.domain) :
    dilation r hr (f : SoninL2) ∈ burnolSquarePosition.domain := by
  change MemLp (fun x : ℝ => (x^2 : ℝ) * (dilation r hr (f : SoninL2)) x) 2 volume
  exact (memLp_congr_ae (square_dilation_ae r hr f)).mpr
    ((Lp.memLp (dilation r hr (burnolSquarePosition f))).const_mul _)

private def squareDilation (r : ℝ) (hr : 0 < r) (f : burnolSquarePosition.domain) :
    burnolSquarePosition.domain := ⟨dilation r hr (f : SoninL2), square_dilation_mem r hr f⟩

private theorem square_dilation (r : ℝ) (hr : 0 < r) (f : burnolSquarePosition.domain) :
    burnolSquarePosition (squareDilation r hr f) =
      (r : ℂ)⁻¹^2 • dilation r hr (burnolSquarePosition f) := by
  apply Lp.ext
  have h := (square_position_ae (squareDilation r hr f)).trans (square_dilation_ae r hr f)
  filter_upwards [h, Lp.coeFn_smul ((r : ℂ)⁻¹^2)
    (dilation r hr (burnolSquarePosition f))] with x hx hs
  rw [hx, hs]
  rfl

private theorem square_inner_dilation (r : ℝ) (hr : 0 < r)
    (f g : burnolSquarePosition.domain) :
    ⟪burnolSquarePosition f, dilation r hr (g : SoninL2)⟫_ℂ =
      (r : ℂ)⁻¹^2 * ⟪(f : SoninL2), dilation r hr (burnolSquarePosition g)⟫_ℂ := by
  have h := maximalRealL2Mul_formalSelfAdjoint volume (fun x : ℝ => x^2)
    f (squareDilation r hr g)
  change ⟪burnolSquarePosition f, dilation r hr (g : SoninL2)⟫_ℂ =
    ⟪(f : SoninL2), burnolSquarePosition (squareDilation r hr g)⟫_ℂ at h
  rw [h, square_dilation, inner_smul_right]

private theorem square_energy (f : burnolSquarePosition.domain) :
    (⟪(f : SoninL2), burnolSquarePosition f⟫_ℂ).re =
      ∫ x : ℝ, x^2 * ‖(f : SoninL2) x‖^2 := by
  rw [L2.inner_def]
  change RCLike.re (∫ x : ℝ, ⟪(f : SoninL2) x, (burnolSquarePosition f) x⟫_ℂ) = _
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (f : SoninL2)
    (burnolSquarePosition f))]
  apply integral_congr_ae
  filter_upwards [square_position_ae f] with x hx
  rw [hx]
  change (⟪(f : SoninL2) x, ((x^2 : ℝ) : ℂ) • (f : SoninL2) x⟫_ℂ).re = _
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change x^2 * RCLike.re ⟪(f : SoninL2) x, (f : SoninL2) x⟫_ℂ = _
  rw [inner_self_eq_norm_sq]

private theorem square_energy_integrable (f : burnolSquarePosition.domain) :
    Integrable (fun x : ℝ => x^2 * ‖(f : SoninL2) x‖^2) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (f : SoninL2) (burnolSquarePosition f)).re.congr
  filter_upwards [square_position_ae f] with x hx
  rw [hx]
  change (⟪(f : SoninL2) x, ((x^2 : ℝ) : ℂ) • (f : SoninL2) x⟫_ℂ).re = _
  rw [inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change x^2 * RCLike.re ⟪(f : SoninL2) x, (f : SoninL2) x⟫_ℂ = _
  rw [inner_self_eq_norm_sq]

private theorem square_energy_zero (f : burnolSquarePosition.domain)
    (he : ⟪(f : SoninL2), burnolSquarePosition f⟫_ℂ = 0) : (f : SoninL2) = 0 := by
  have hint : (∫ x : ℝ, x^2 * ‖(f : SoninL2) x‖^2) = 0 := by
    rw [← square_energy, he, Complex.zero_re]
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun x : ℝ => mul_nonneg (sq_nonneg x) (sq_nonneg _)) (square_energy_integrable f)).mp hint
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  apply Lp.ext
  filter_upwards [hae, hne, Lp.coeFn_zero ℂ 2 volume] with x hx hn hz
  rw [hz]
  apply norm_eq_zero.mp
  apply (sq_eq_zero_iff).mp
  exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ hn)

private theorem rayDilate_one_eq (f : SoninL2) : rayDilate 1 f = f := by
  rw [rayDilate_of_pos zero_lt_one]
  apply Lp.ext
  filter_upwards [dilation_ae 1 zero_lt_one f] with x hx
  simpa using hx

/-- Maximal-domain Fourier commutation with position square has zero kernel. -/
private theorem square_fourier_kernel (f g : burnolSquarePosition.domain)
    (hg : (g : SoninL2) = fourierUnitary (f : SoninL2))
    (hM : burnolSquarePosition g = fourierUnitary (burnolSquarePosition f)) :
    (f : SoninL2) = 0 := by
  have hzero (r : ℝ) (hr : 1 < r) :
      ⟪(f : SoninL2), rayDilate r (burnolSquarePosition f)⟫_ℂ = 0 := by
    have hr0 := zero_lt_one.trans hr
    have hfirst := square_inner_dilation r hr0 f f
    have hsecond : ⟪burnolSquarePosition f, dilation r hr0 (f : SoninL2)⟫_ℂ =
        (r : ℂ)^2 * ⟪(f : SoninL2), dilation r hr0 (burnolSquarePosition f)⟫_ℂ := by
      calc
        _ = ⟪fourierUnitary (burnolSquarePosition f),
              fourierUnitary (dilation r hr0 (f : SoninL2))⟫_ℂ :=
          (fourierUnitary.inner_map_map _ _).symm
        _ = ⟪burnolSquarePosition g,
              dilation r⁻¹ (inv_pos.mpr hr0) (g : SoninL2)⟫_ℂ := by
          rw [← hM, fourierUnitary_dilation, ← hg]
        _ = (r : ℂ)^2 * ⟪(g : SoninL2),
              dilation r⁻¹ (inv_pos.mpr hr0) (burnolSquarePosition g)⟫_ℂ := by
          rw [square_inner_dilation, Complex.ofReal_inv, inv_inv]
        _ = (r : ℂ)^2 * ⟪(f : SoninL2), dilation r hr0 (burnolSquarePosition f)⟫_ℂ := by
          rw [hg, hM, ← fourierUnitary_dilation, fourierUnitary.inner_map_map]
    have hfactor : ((r : ℂ)⁻¹^2 - (r : ℂ)^2) *
        ⟪(f : SoninL2), dilation r hr0 (burnolSquarePosition f)⟫_ℂ = 0 := by
      rw [sub_mul, ← hfirst, ← hsecond, sub_self]
    have hcoef : (r : ℂ)⁻¹^2 - (r : ℂ)^2 ≠ 0 := by
      have hinv : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
      have hri : 0 < r⁻¹ := inv_pos.mpr hr0
      have hreal : r⁻¹^2 - r^2 ≠ 0 := by nlinarith
      exact_mod_cast hreal
    rw [rayDilate_of_pos hr0]
    exact (mul_eq_zero.mp hfactor).resolve_left hcoef
  have hc : ContinuousAt (fun r : ℝ =>
      ⟪(f : SoninL2), rayDilate r (burnolSquarePosition f)⟫_ℂ) 1 :=
    continuousAt_const.inner ((continuousOn_rayDilate (burnolSquarePosition f) 1
      (by change (0 : ℝ) < 1; exact zero_lt_one)).continuousAt (Ioi_mem_nhds zero_lt_one))
  have hlim : Tendsto (fun r : ℝ => ⟪(f : SoninL2), rayDilate r (burnolSquarePosition f)⟫_ℂ)
      (𝓝[>] 1) (𝓝 ⟪(f : SoninL2), burnolSquarePosition f⟫_ℂ) := by
    simpa only [rayDilate_one_eq] using hc.continuousWithinAt.tendsto
  have hzlim : Tendsto (fun r : ℝ => ⟪(f : SoninL2), rayDilate r (burnolSquarePosition f)⟫_ℂ)
      (𝓝[>] 1) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hzero r hr).symm
  exact square_energy_zero f (tendsto_nhds_unique hlim hzlim)

/-- Keep the actual radial-square jet as a second physical Fourier output. -/
def primeBurnolFourierJetSynthesis :
    (burnolSquarePosition.domain × burnolSquarePosition.domain) →ₗ[ℂ] (SoninL2 × SoninL2) where
  toFun z := ((z.1 : SoninL2) + fourierUnitary (z.2 : SoninL2),
    burnolSquarePosition.toFun z.1 + fourierUnitary (burnolSquarePosition.toFun z.2))
  map_add' z w := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add] <;> abel
  map_smul' c z := by
    apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
      RingHom.id_apply, smul_add]

/-- The retained literal jet removes every Fourier synthesis collision on this maximal domain. -/
theorem primeBurnolFourierJetSynthesis_injective :
    Function.Injective primeBurnolFourierJetSynthesis := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨f, g⟩ h
  have h1 : (f : SoninL2) + fourierUnitary (g : SoninL2) = 0 := congrArg Prod.fst h
  have h2 : burnolSquarePosition.toFun f + fourierUnitary (burnolSquarePosition.toFun g) = 0 :=
    congrArg Prod.snd h
  have hgF : fourierUnitary (g : SoninL2) = -(f : SoninL2) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using h1
  let gF : burnolSquarePosition.domain :=
    ⟨fourierUnitary (g : SoninL2), hgF ▸ burnolSquarePosition.domain.neg_mem f.property⟩
  have hgF' : gF = -f := Subtype.ext hgF
  have hM : burnolSquarePosition.toFun gF = fourierUnitary (burnolSquarePosition.toFun g) := by
    rw [hgF', map_neg]
    rw [eq_neg_of_add_eq_zero_left h2, neg_neg]
  have hg0 := square_fourier_kernel g gF rfl hM
  have hf0 : (f : SoninL2) = 0 := by simpa only [hg0, map_zero, add_zero] using h1
  exact Prod.ext (Subtype.ext hf0) (Subtype.ext hg0)

private theorem integrable_even_of_halfLine {f : ℝ → ℝ}
    (he : ∀ x, f (-x) = f x) (hi : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hl : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, he, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hi

private theorem memLp_even_radialJet (pe : Nat.Primes × ℕ) (m : ℕ) :
    MemLp (fun x : ℝ => primeBurnolRadialJet pe m |x|) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    ((continuous_primeBurnolRadialJet pe m).comp continuous_abs).aestronglyMeasurable).mpr
  apply integrable_even_of_halfLine (by intro x; simp only [Function.comp_apply, abs_neg])
  have hi : IntegrableOn (fun x => ‖primeBurnolRadialJet pe m x‖^2) (Ioi 0) :=
    (memLp_two_iff_integrable_sq_norm
    (continuous_primeBurnolRadialJet pe m).aestronglyMeasurable.restrict).mp
      (memLp_primeBurnolRadialJet pe m)
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [Function.comp_apply, abs_of_pos (show 0 < x from hx)]

/-- The retained physical observable is exactly the literal radial jet of order two. -/
theorem square_primeBurnolEvenFeature (pe : Nat.Primes × ℕ) (x : ℝ) :
    ((x^2 : ℝ) : ℂ) * primeBurnolEvenFeature pe x = primeBurnolRadialJet pe 2 |x| := by
  rw [← sq_abs x]
  simp only [primeBurnolEvenFeature, primeBurnolWindowFeature, primeBurnolComplexExponent,
    Complex.ofReal_zero, mul_zero, add_zero, primeBurnolRadialJet, Nat.reduceAdd,
    Complex.ofReal_pow]
  ring_nf

/-- Every literal prime-depth column belongs to the actual maximal position-square domain. -/
theorem primeBurnolEvenFeatureLp_mem_squarePosition (pe : Nat.Primes × ℕ) :
    primeBurnolEvenFeatureLp pe ∈ burnolSquarePosition.domain := by
  change MemLp (fun x : ℝ => ((x^2 : ℝ) : ℂ) * primeBurnolEvenFeatureLp pe x) 2 volume
  apply (memLp_congr_ae _).mpr (memLp_even_radialJet pe 2)
  filter_upwards [primeBurnolEvenFeatureLp_coeFn pe] with x hx
  rw [hx, square_primeBurnolEvenFeature]

def primeBurnolSquareColumn (pe : Nat.Primes × ℕ) : burnolSquarePosition.domain :=
  ⟨primeBurnolEvenFeatureLp pe, primeBurnolEvenFeatureLp_mem_squarePosition pe⟩

theorem burnolSquarePosition_primeBurnolSquareColumn (pe : Nat.Primes × ℕ) :
    (burnolSquarePosition (primeBurnolSquareColumn pe) : ℝ → ℂ) =ᵐ[volume]
      fun x => primeBurnolRadialJet pe 2 |x| := by
  filter_upwards [square_position_ae (primeBurnolSquareColumn pe),
    primeBurnolEvenFeatureLp_coeFn pe] with x hx hf
  change (burnolSquarePosition (primeBurnolSquareColumn pe)) x =
    ((x^2 : ℝ) : ℂ) * primeBurnolEvenFeatureLp pe x at hx
  rw [hx, hf, square_primeBurnolEvenFeature]
end RHTower
