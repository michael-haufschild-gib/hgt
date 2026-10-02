import GaloisForLFunctions.RHTower.SoninBandCodimensionTwo
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.L2FourierUncertainty

/-!
# Exact support recovery for the Sonin dilation source

For a bounded sum of physical and Fourier forbidden bands, `D_r = U_r + U_(r^-1)`
has an exact inverse-support law: its image belongs to the radius-`c` forbidden
sum precisely when its input belongs to the radius-`c/r` sum. Fourier uncertainty
separates the two polarizations. Finite dilation descent recovers each support.

Consequently `Q_c D_r` is injective on any lost Sonin layer inside `K_a` when
`c ≤ r*a`. This is an actual source rigidity theorem; no spectral, Xi, or RH
premise enters its proof.
-/

noncomputable section
namespace RHTower
open scoped InnerProductSpace
open MeasureTheory

private theorem mem_physical_iff_cutoff {a : ℝ} {f : SoninL2} :
    f ∈ centralPhysicalForbidden a ↔
      indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = f := by
  rw [indicatorCutoff_eq_physicalForbidden_starProjection,
    Submodule.starProjection_eq_self_iff]
  rfl

private theorem mem_fourier_iff_physical {a : ℝ} {f : SoninL2} :
    f ∈ centralFourierForbidden a ↔ fourierUnitary f ∈ centralPhysicalForbidden a :=
  mem_fourierForbidden_iff (centralInterval a) (measurableSet_centralInterval a) f

/-- Exact transport of the physical forbidden band by normalized dilation. -/
theorem dilation_mem_centralPhysicalForbidden {a r : ℝ} (hr : 0 < r) {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden a) :
    dilation r hr f ∈ centralPhysicalForbidden (a / r) := by
  rw [mem_physical_iff_cutoff, indicatorCutoff_dilation,
    show r * (a / r) = a by field_simp]
  rw [(mem_physical_iff_cutoff.mp hf)]

private theorem physical_support_descent {c t r : ℝ} (hr : 1 < r) {f : SoninL2}
    (hct : c ≤ r * t) (hf : f ∈ centralPhysicalForbidden (r * (r * t)))
    (hD : dilationSum r hr f ∈ centralPhysicalForbidden c) :
    f ∈ centralPhysicalForbidden t := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hU : dilation r hr0 f ∈ centralPhysicalForbidden (r * t) := by
    simpa only [mul_div_cancel_left₀ _ hr0.ne'] using dilation_mem_centralPhysicalForbidden hr0 hf
  have hV : dilation r⁻¹ (inv_pos.mpr hr0) f ∈ centralPhysicalForbidden (r * t) := by
    have h := (centralPhysicalForbidden (r * t)).sub_mem
      (centralPhysicalForbidden_mono hct hD) hU
    simpa only [dilationSum_apply, add_sub_cancel_left] using h
  have h := dilation_mem_centralPhysicalForbidden hr0 hV
  simpa only [dilation_dilation_inv, mul_div_cancel_left₀ _ hr0.ne'] using h

/-- Bounded support of a symmetric dilation sum recovers its input support exactly. -/
theorem mem_centralPhysicalForbidden_of_dilationSum {b c r : ℝ}
    (hc : 0 < c) (hr : 1 < r) {f : SoninL2}
    (hf : f ∈ centralPhysicalForbidden b)
    (hD : dilationSum r hr f ∈ centralPhysicalForbidden c) :
    f ∈ centralPhysicalForbidden (c / r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hrr : 1 < r * r := by nlinarith
  have hd : 0 < c / r := div_pos hc hr0
  have hiter : ∀ n : ℕ,
      f ∈ centralPhysicalForbidden ((r * r) ^ n * (c / r)) →
      f ∈ centralPhysicalForbidden (c / r) := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_mul, imp_self]
    | succ n ih =>
      intro hn
      apply ih
      apply physical_support_descent hr (f := f) (c := c)
      · have hp : 1 ≤ (r * r) ^ n := one_le_pow₀ hrr.le
        calc c = r * (c / r) := by field_simp
             _ ≤ r * ((r * r) ^ n * (c / r)) :=
               mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hd.le hp) hr0.le
      · have heq : (r * r) ^ (n + 1) * (c / r) =
            r * (r * ((r * r) ^ n * (c / r))) := by rw [pow_succ]; ring
        exact heq ▸ hn
      · exact hD
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / (c / r)) hrr
  apply hiter n
  exact centralPhysicalForbidden_mono ((div_lt_iff₀ hd).mp hn).le hf

/-- Fourier transform commutes with the symmetric normalized dilation source. -/
theorem fourierUnitary_dilationSum (r : ℝ) (hr : 1 < r) (f : SoninL2) :
    fourierUnitary (dilationSum r hr f) = dilationSum r hr (fourierUnitary f) := by
  simp only [dilationSum_apply, map_add, fourierUnitary_dilation, inv_inv]
  exact add_comm _ _

/-- The same exact support recovery holds for the Fourier forbidden band. -/
theorem mem_centralFourierForbidden_of_dilationSum {b c r : ℝ}
    (hc : 0 < c) (hr : 1 < r) {f : SoninL2}
    (hf : f ∈ centralFourierForbidden b)
    (hD : dilationSum r hr f ∈ centralFourierForbidden c) :
    f ∈ centralFourierForbidden (c / r) := by
  rw [mem_fourier_iff_physical] at hf hD ⊢
  rw [fourierUnitary_dilationSum] at hD
  exact mem_centralPhysicalForbidden_of_dilationSum hc hr hf hD

/-- Symmetric dilation transports a physical band into the outer radius. -/
theorem dilationSum_mem_centralPhysicalForbidden {b r : ℝ} (hb : 0 ≤ b) (hr : 1 < r)
    {f : SoninL2} (hf : f ∈ centralPhysicalForbidden b) :
    dilationSum r hr f ∈ centralPhysicalForbidden (r * b) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hscale : b / r ≤ r * b := by
    apply (div_le_iff₀ hr0).mpr
    nlinarith [mul_nonneg hb (show 0 ≤ r * r - 1 by nlinarith)]
  rw [dilationSum_apply]
  apply (centralPhysicalForbidden (r * b)).add_mem
  · exact centralPhysicalForbidden_mono hscale (dilation_mem_centralPhysicalForbidden hr0 hf)
  · simpa only [div_inv_eq_mul, mul_comm] using
      dilation_mem_centralPhysicalForbidden (inv_pos.mpr hr0) hf

/-- Symmetric dilation transports a Fourier band into the outer radius. -/
theorem dilationSum_mem_centralFourierForbidden {b r : ℝ} (hb : 0 ≤ b) (hr : 1 < r)
    {f : SoninL2} (hf : f ∈ centralFourierForbidden b) :
    dilationSum r hr f ∈ centralFourierForbidden (r * b) := by
  rw [mem_fourier_iff_physical, fourierUnitary_dilationSum]
  exact dilationSum_mem_centralPhysicalForbidden hb hr (mem_fourier_iff_physical.mp hf)

/-- The physical and Fourier bounded forbidden bands intersect only at zero. -/
theorem eq_zero_of_mem_centralPhysicalForbidden_of_mem_centralFourierForbidden {a b : ℝ} {f : SoninL2}
    (hA : f ∈ centralPhysicalForbidden a) (hF : f ∈ centralFourierForbidden b) :
    f = 0 := by
  apply l2_fourier_uncertainty f
  · exact (mem_physicalForbidden_iff _ _ f).mp hA
  · exact (mem_physicalForbidden_iff _ _ (fourierUnitary f)).mp
      (mem_fourier_iff_physical.mp hF)

/-- Exact inverse support for a bounded physical-plus-Fourier source.
The two polarizations cannot hide a dilation tail by canceling each other. -/
theorem dilationSum_mem_forbiddenSum_iff {b c r : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hr : 1 < r) {v : SoninL2}
    (hv : v ∈ centralPhysicalForbidden b ⊔ centralFourierForbidden b) :
    dilationSum r hr v ∈ centralPhysicalForbidden c ⊔ centralFourierForbidden c ↔
      v ∈ centralPhysicalForbidden (c / r) ⊔ centralFourierForbidden (c / r) := by
  constructor
  · intro hD
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨h, hh, k, hk, heq⟩ := Submodule.mem_sup.mp hD
    have hsum : dilationSum r hr f + dilationSum r hr g = h + k := by
      simpa only [map_add] using heq.symm
    have hsep : dilationSum r hr f - h = k - dilationSum r hr g := by
      calc
        _ = (dilationSum r hr f + dilationSum r hr g) -
            (h + dilationSum r hr g) := by abel
        _ = (h + k) - (h + dilationSum r hr g) := by rw [hsum]
        _ = _ := by abel
    have hz : dilationSum r hr f - h = 0 := by
      apply eq_zero_of_mem_centralPhysicalForbidden_of_mem_centralFourierForbidden (a := max (r * b) c) (b := max (r * b) c)
      · exact (centralPhysicalForbidden _).sub_mem
          (centralPhysicalForbidden_mono (le_max_left _ _) (dilationSum_mem_centralPhysicalForbidden hb.le hr hf))
          (centralPhysicalForbidden_mono (le_max_right _ _) hh)
      · rw [hsep]
        exact (centralFourierForbidden _).sub_mem
          (centralFourierForbidden_mono (le_max_right _ _) hk)
          (centralFourierForbidden_mono (le_max_left _ _) (dilationSum_mem_centralFourierForbidden hb.le hr hg))
    have hDf : dilationSum r hr f = h := sub_eq_zero.mp hz
    have hDg : dilationSum r hr g = k := by
      rw [hDf] at hsum
      exact add_left_cancel hsum
    exact Submodule.mem_sup.mpr ⟨f,
      mem_centralPhysicalForbidden_of_dilationSum hc hr hf (hDf.symm ▸ hh),
      g, mem_centralFourierForbidden_of_dilationSum hc hr hg (hDg.symm ▸ hk), rfl⟩
  · intro hv'
    obtain ⟨f, hf, g, hg, rfl⟩ := Submodule.mem_sup.mp hv'
    have hr0 : 0 < r := zero_lt_one.trans hr
    have hrc : r * (c / r) = c := by field_simp
    rw [map_add]
    exact Submodule.mem_sup.mpr ⟨dilationSum r hr f,
      hrc ▸ dilationSum_mem_centralPhysicalForbidden (div_pos hc hr0).le hr hf,
      dilationSum r hr g, hrc ▸ dilationSum_mem_centralFourierForbidden (div_pos hc hr0).le hr hg, rfl⟩

/-- On any bounded forbidden source, compression after dilation detects exactly
membership in the smaller forbidden source at radius `c/r`. -/
theorem centralSoninProjection_dilationSum_eq_zero_iff {b c r : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hr : 1 < r) {v : SoninL2}
    (hv : centralSoninProjection b v = 0) :
    centralSoninProjection c (dilationSum r hr v) = 0 ↔
      centralSoninProjection (c / r) v = 0 := by
  have hzero (t : ℝ) (ht : 0 < t) (w : SoninL2) :
      centralSoninProjection t w = 0 ↔
        w ∈ centralPhysicalForbidden t ⊔ centralFourierForbidden t := by
    rw [centralSoninProjection, Submodule.starProjection_apply_eq_zero_iff,
      orthogonal_centralSoninCarrier ht]
  rw [hzero c hc, hzero (c / r) (div_pos hc (zero_lt_one.trans hr))]
  exact dilationSum_mem_forbiddenSum_iff hb hc hr ((hzero b hb v).mp hv)

/-- No lost-layer vector has a vanishing retained dilation channel in the crossing chamber. -/
theorem eq_zero_of_centralSoninProjection_dilationSum_eq_zero
    {a b c r : ℝ} (hb : 0 < b) (hc : 0 < c) (hr : 1 < r) (hca : c ≤ r * a)
    {v : SoninL2} (hva : v ∈ centralSoninCarrier a)
    (hvb : centralSoninProjection b v = 0)
    (hvD : centralSoninProjection c (dilationSum r hr v) = 0) : v = 0 := by
  have hsmall := (centralSoninProjection_dilationSum_eq_zero_iff hb hc hr hvb).mp hvD
  rw [centralSoninProjection, Submodule.starProjection_apply_eq_zero_iff,
    orthogonal_centralSoninCarrier (div_pos hc (zero_lt_one.trans hr))] at hsmall
  have hle : c / r ≤ a := (div_le_iff₀ (zero_lt_one.trans hr)).mpr (by simpa [mul_comm] using hca)
  have hsum : v ∈ centralPhysicalForbidden a ⊔ centralFourierForbidden a :=
    sup_le_sup (centralPhysicalForbidden_mono hle) (centralFourierForbidden_mono hle) hsmall
  have horth : v ∈ (centralPhysicalForbidden a ⊔ centralFourierForbidden a)ᗮ := by
    rwa [centralSoninCarrier_eq_orthogonal_sup] at hva
  exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ _).mp horth v hsum)

end RHTower
