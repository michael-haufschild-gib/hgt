import GaloisForLFunctions.RHTower.SoninCouplingLayerOrthogonality

/-!
# The coupling is a compression of the dilation sum inside one Sonin space

The dilation sum moves the Sonin space at aperture `a` into the Sonin space at aperture `a / r`, so
in the crossing chamber both aperture layers of the successive-layer coupling and the whole image of
the dilation sum sit inside the single Sonin space at aperture `b / r`.

The coupling is therefore the compression of the dilation sum to that one space, cut between two of
its orthogonal layers.  Its vanishing is exactly the statement that the compressed dilation has no
off-diagonal block between those layers.

Note the aperture tower is *not* dilation covariant: the physical and Fourier constraints scale
oppositely, so `U_r` carries the symmetric Sonin space at `a` into an asymmetric one and only the
inclusion into the Sonin space at `a / r` survives.  That inclusion is what the compression form
rests on.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The dilation sum carries the even Sonin carrier at aperture `a` into the one at `a / r`. -/
theorem evenDilationSum_mem_evenCentralSoninCarrier_inv_mul
    {a r : ℝ} (ha : 0 ≤ a) (hr : 1 < r) {f : evenSubspace}
    (hf : f ∈ evenCentralSoninCarrier a) :
    evenDilationSum r hr f ∈ evenCentralSoninCarrier (r⁻¹ * a) := by
  change ((evenDilationSum r hr f : evenSubspace) : SoninL2) ∈
    centralSoninCarrier (r⁻¹ * a)
  rw [coe_evenDilationSum_apply]
  exact dilationSum_mem_centralSoninCarrier_inv_mul ha hr hf

/-- **Aperture-tower absorption.**  Everything the dilation sum produces from the Sonin space at
`a` is already fixed by the Sonin projection at `a / r`. -/
theorem evenCentralSoninProjection_mul_evenDilationSum_mul_evenCentralSoninProjection
    {a r : ℝ} (ha : 0 ≤ a) (hr : 1 < r) :
    evenCentralSoninProjection (r⁻¹ * a) * (evenDilationSum r hr *
        evenCentralSoninProjection a) =
      evenDilationSum r hr * evenCentralSoninProjection a := by
  apply ContinuousLinearMap.ext
  intro f
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    evenCentralSoninProjection_eq_starProjection (r⁻¹ * a)]
  refine (evenCentralSoninCarrier (r⁻¹ * a)).starProjection_eq_self_iff.mpr ?_
  refine evenDilationSum_mem_evenCentralSoninCarrier_inv_mul ha hr ?_
  rw [evenCentralSoninProjection_eq_starProjection]
  exact (evenCentralSoninCarrier a).starProjection_apply_mem f

/-- The image of a whole aperture layer under the dilation sum lands in the Sonin space at the
smaller of the two shrunk apertures. -/
theorem evenCentralSoninProjection_mul_evenDilationSum_mul_evenSoninApertureLayer
    {b c r : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    evenCentralSoninProjection (r⁻¹ * b) * (evenDilationSum r hr *
        evenSoninApertureLayer b c) =
      evenDilationSum r hr * evenSoninApertureLayer b c := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr0
  have hc : (0 : ℝ) ≤ c := hb.trans hbc
  have hshrink : r⁻¹ * b ≤ r⁻¹ * c := by
    exact mul_le_mul_of_nonneg_left hbc hrinv.le
  have habs_b := evenCentralSoninProjection_mul_evenDilationSum_mul_evenCentralSoninProjection
    hb hr
  have habs_c := evenCentralSoninProjection_mul_evenDilationSum_mul_evenCentralSoninProjection
    hc hr
  have hnest := (evenCentralSoninProjection_mul_of_le hshrink).2
  have habs_c' : evenCentralSoninProjection (r⁻¹ * b) * (evenDilationSum r hr *
      evenCentralSoninProjection c) =
      evenDilationSum r hr * evenCentralSoninProjection c := by
    calc evenCentralSoninProjection (r⁻¹ * b) *
          (evenDilationSum r hr * evenCentralSoninProjection c)
        = evenCentralSoninProjection (r⁻¹ * b) *
            (evenCentralSoninProjection (r⁻¹ * c) *
              (evenDilationSum r hr * evenCentralSoninProjection c)) := by
          rw [habs_c]
      _ = (evenCentralSoninProjection (r⁻¹ * b) *
            evenCentralSoninProjection (r⁻¹ * c)) *
            (evenDilationSum r hr * evenCentralSoninProjection c) := by
          rw [mul_assoc]
      _ = evenCentralSoninProjection (r⁻¹ * c) *
            (evenDilationSum r hr * evenCentralSoninProjection c) := by rw [hnest]
      _ = evenDilationSum r hr * evenCentralSoninProjection c := habs_c
  unfold evenSoninApertureLayer
  rw [mul_sub, mul_sub, habs_b, habs_c']

/-- The compression of the dilation sum to the Sonin space at aperture `b / r`. -/
def evenSoninCompressedDilation (b r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninProjection (r⁻¹ * b) * evenDilationSum r hr *
    evenCentralSoninProjection (r⁻¹ * b)

/-- The compressed dilation is self-adjoint. -/
theorem adjoint_evenSoninCompressedDilation (b r : ℝ) (hr : 1 < r) :
    ContinuousLinearMap.adjoint (evenSoninCompressedDilation b r hr) =
      evenSoninCompressedDilation b r hr := by
  unfold evenSoninCompressedDilation
  change ContinuousLinearMap.adjoint
      ((evenCentralSoninProjection (r⁻¹ * b) ∘L evenDilationSum r hr) ∘L
        evenCentralSoninProjection (r⁻¹ * b)) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_evenCentralSoninProjection, adjoint_evenDilationSum]
  exact (mul_assoc _ _ _).symm

/-- **Compression form of the successive-layer coupling.**  In the crossing chamber the coupling is
the compressed dilation cut between the two aperture layers. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_compression
    {a b c r : ℝ} (hb : 0 ≤ b) (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r)
    (hba : r⁻¹ * b ≤ a) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr =
      evenSoninApertureLayer a b * evenSoninCompressedDilation b r hr *
        evenSoninApertureLayer b c := by
  have hbrb : r⁻¹ * b ≤ b := hba.trans hab
  have hbrc : r⁻¹ * b ≤ c := hbrb.trans hbc
  have hlow : evenSoninApertureLayer a b *
      evenCentralSoninProjection (r⁻¹ * b) = evenSoninApertureLayer a b := by
    unfold evenSoninApertureLayer
    rw [sub_mul, (evenCentralSoninProjection_mul_of_le hba).1,
      (evenCentralSoninProjection_mul_of_le hbrb).1]
  have hpush := evenCentralSoninProjection_mul_evenDilationSum_mul_evenSoninApertureLayer
    hb hbc hr
  have hhigh : evenCentralSoninProjection (r⁻¹ * b) * evenSoninApertureLayer b c =
      evenSoninApertureLayer b c := by
    unfold evenSoninApertureLayer
    rw [mul_sub, (evenCentralSoninProjection_mul_of_le hbrb).2,
      (evenCentralSoninProjection_mul_of_le hbrc).2]
  unfold evenSoninApertureSuccessiveLayerTransition evenSoninCompressedDilation
  calc evenSoninApertureLayer a b * evenDilationSum r hr * evenSoninApertureLayer b c
      = (evenSoninApertureLayer a b * evenCentralSoninProjection (r⁻¹ * b)) *
          evenDilationSum r hr *
          (evenCentralSoninProjection (r⁻¹ * b) * evenSoninApertureLayer b c) := by
        rw [hlow, hhigh]
    _ = evenSoninApertureLayer a b *
          (evenCentralSoninProjection (r⁻¹ * b) * evenDilationSum r hr *
            evenCentralSoninProjection (r⁻¹ * b)) *
          evenSoninApertureLayer b c := by
        simp only [mul_assoc]

/-- **The coupling question is a commutation question.**  It vanishes exactly when the compressed
dilation has no matrix element between the two layers. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_compression_orthogonal
    {a b c r : ℝ} (hb : 0 ≤ b) (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r)
    (hba : r⁻¹ * b ≤ a) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 ↔
      evenSoninApertureLayer a b * evenSoninCompressedDilation b r hr *
        evenSoninApertureLayer b c = 0 := by
  rw [evenSoninApertureSuccessiveLayerTransition_eq_compression hb hab hbc hr hba]

end RHTower
