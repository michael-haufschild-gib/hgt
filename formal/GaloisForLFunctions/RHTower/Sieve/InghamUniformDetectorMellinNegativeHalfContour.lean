import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfLeftEdge
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinContourResidue

open Complex Filter Metric Set Finset Topology MeasureTheory Asymptotics intervalIntegral

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Entire Mellin analyticity removes the old positive-left-edge restriction from the exact
residue rectangle. -/
theorem routeTNormalizedZetaRegularMellinBoundary_eq_neg_zeroPacket_univ
    {N H c d T : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hcd : c < d) (hT : 0 < T)
    (hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((d : ℂ) + (y : ℝ) * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * I) ≠ 0) :
    routeTNormalizedZetaRegularMellinBoundary N H c d T =
      -routeTNormalizedZetaRegularMellinZeroPacket N H c d T := by
  have hrect := rectIntegral_mul_zetaLogDerivReg_eq_neg_closedRectangleZeroSum
    (g := routeTNormalizedSmoothWindowMellin N H)
    (z₁ := (c : ℂ) + ((-T : ℝ) : ℂ) * I)
    (z₂ := (d : ℂ) + ((T : ℝ) : ℂ) * I)
    isOpen_univ (analyticOnNhd_routeTNormalizedSmoothWindowMellin_univ hN hH)
    (by simp) (by simpa using hcd) (by simp; linarith)
    (by simpa using hbot) (by simpa using htop)
    (by simpa using hright) (by simpa using hleft)
  simp [rectIntegral, routeTNormalizedZetaRegularMellinBoundary,
    routeTNormalizedZetaRegularMellinZeroPacket, smul_eq_mul, mul_comm] at hrect ⊢
  linear_combination hrect

/-- The fixed line `Re s = -1/2` contains no residue-unit zero. -/
theorem zetaResidueUnit_ne_zero_negative_half (t : ℝ) :
    zetaResidueUnit ((-1 / 2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let s : ℂ := (-1 / 2 : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [s] at hre
    norm_num at hre
  have hz0 : riemannZeta s ≠ 0 := by
    apply RHTower.riemannZeta_ne_zero_of_re_lt_zero (by dsimp only [s]; norm_num)
    intro n htriv
    have hre := congrArg Complex.re htriv
    have hsRe : s.re = -1 / 2 := by simp [s]
    have hrRe : (-(2 * ((n : ℂ) + 1))).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hsRe, hrRe] at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (zetaResidueUnit_ne_zero_iff hs1).2 hz0

/-- The fixed Euler line `Re s = 2` contains no residue-unit zero. -/
theorem zetaResidueUnit_ne_zero_two (t : ℝ) :
    zetaResidueUnit ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  let s : ℂ := (2 : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [s] at hre
    norm_num at hre
  apply (zetaResidueUnit_ne_zero_iff hs1).2
  apply riemannZeta_ne_zero_of_one_le_re
  dsimp only [s]
  norm_num

private theorem exists_routeT_Ioo_not_mem_finset
    {a b : ℝ} (hab : a < b) (F : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ F := by
  have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  have hdiff : (Set.Ioo a b \ (F : Set ℝ)).Infinite := hinf.sdiff F.finite_toSet
  obtain ⟨x, hxI, hxF⟩ := hdiff.nonempty
  exact ⟨x, hxI, by simpa using hxF⟩

/-- At every large natural scale one can keep the canonical vertical edges and select only a
nearby height so the complete rectangle boundary avoids residue-unit zeros. -/
theorem exists_routeT_negativeHalf_two_zeroFreeBoundary_height
    {X : ℕ} (hX : 4 ≤ X) :
    ∃ T ∈ Set.Ioo ((X : ℝ) - 3) ((X : ℝ) - 2),
      (∀ x ∈ uIcc (-1 / 2 : ℝ) 2,
        zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ uIcc (-1 / 2 : ℝ) 2,
        zetaResidueUnit ((x : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) ∧
      (∀ y ∈ uIcc (-T) T,
        zetaResidueUnit ((2 : ℂ) + (y : ℝ) * I) ≠ 0) ∧
      ∀ y ∈ uIcc (-T) T,
        zetaResidueUnit ((-1 / 2 : ℂ) + (y : ℝ) * I) ≠ 0 := by
  classical
  let R : ℝ := (X : ℝ) - 2
  let z₁ : ℂ := (-1 / 2 : ℂ) + ((-R : ℝ) : ℂ) * I
  let z₂ : ℂ := (2 : ℂ) + ((R : ℝ) : ℂ) * I
  let Z : Finset ℂ := zetaResidueUnitClosedRectangleZeros z₁ z₂
  let F : Finset ℝ := Z.image (fun z => |z.im|)
  have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hR : 0 < R := by dsimp only [R]; linarith
  obtain ⟨T, hTI, hTavoid⟩ := exists_routeT_Ioo_not_mem_finset
    (by linarith : (X : ℝ) - 3 < (X : ℝ) - 2) F
  have hT : 0 < T := by linarith [hTI.1, hXR]
  have hhorizontal (eps : ℝ) (heps : eps = -1 ∨ eps = 1) :
      ∀ x ∈ uIcc (-1 / 2 : ℝ) 2,
        zetaResidueUnit ((x : ℂ) + ((eps * T : ℝ) : ℂ) * I) ≠ 0 := by
    intro x hx hzero
    have hxI : -1 / 2 ≤ x ∧ x ≤ 2 := by
      simpa [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] using hx
    let w : ℂ := (x : ℂ) + ((eps * T : ℝ) : ℂ) * I
    have hwK : w ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
      apply Complex.mem_reProdIm.mpr
      constructor
      · simpa [w, z₁, z₂, uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] using hxI
      · have him : -R ≤ eps * T ∧ eps * T ≤ R := by
          rcases heps with rfl | rfl <;> constructor <;> linarith [hTI.2]
        simpa [w, z₁, z₂, uIcc_of_le (by linarith : -R ≤ R)] using him
    have hwZ : w ∈ Z :=
      mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨hwK, hzero⟩
    apply hTavoid
    rw [show F = Z.image (fun z => |z.im|) from rfl, Finset.mem_image]
    refine ⟨w, hwZ, ?_⟩
    dsimp only [w]
    rcases heps with rfl | rfl <;> simp [abs_of_pos hT]
  refine ⟨T, hTI, ?_, ?_, ?_, ?_⟩
  · simpa only [neg_one_mul] using hhorizontal (-1) (Or.inl rfl)
  · simpa only [one_mul] using hhorizontal 1 (Or.inr rfl)
  · intro y hy
    exact zetaResidueUnit_ne_zero_two y
  · intro y hy
    exact zetaResidueUnit_ne_zero_negative_half y

/-- Canonical selected rectangle: exact complete zero packet, fixed negative and Euler edges. -/
theorem exists_routeT_negativeHalf_two_boundary_eq_neg_zeroPacket
    {X : ℕ} (hX : 4 ≤ X) :
    ∃ T ∈ Set.Ioo ((X : ℝ) - 3) ((X : ℝ) - 2),
      routeTNormalizedZetaRegularMellinBoundary
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (-1 / 2) 2 T =
        -routeTNormalizedZetaRegularMellinZeroPacket
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinBufferedPhysicalWidth X) (-1 / 2) 2 T := by
  obtain ⟨T, hTI, hbot, htop, hright, hleft⟩ :=
    exists_routeT_negativeHalf_two_zeroFreeBoundary_height hX
  have hX1 : 1 ≤ X := by omega
  refine ⟨T, hTI, ?_⟩
  exact routeTNormalizedZetaRegularMellinBoundary_eq_neg_zeroPacket_univ
    (inghamRouteTMellinPhysicalCenter_pos hX1)
    (inghamRouteTMellinBufferedPhysicalWidth_pos hX1)
    (by norm_num) (by linarith [hTI.1, show (4 : ℝ) ≤ X by exact_mod_cast hX])
    hbot htop hright (by simpa using hleft)

end

end RHTower.Sieve
