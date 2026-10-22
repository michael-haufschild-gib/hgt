import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniCircleDirac

/-!
# Kernel growth under Connes--Consani circle compression

The proof of Connes--Consani `propDpert1` says that compression by a rank-`k` projection increases
Dirac nullity by `k`.  Finite-rank compression does not imply this.  The exact kernel criterion in
`FiniteSmoothCompression` shows that extra zero modes are governed by the interaction space

`{q ∈ ran(1-P) | D₀ q ∈ ran P}`.

This file gives a source-native circle counterexample at every positive length.  For the rank-one
packet spanned by `e₁+e₋₁`, the independent vector `e₁-e₋₁` becomes a compressed zero mode even
though it is outside the packet and is not an original Dirac zero mode.  Thus the exact-rank step
used in `propDpert1` is false; any valid asymptotic theorem must control this interaction space.
-/

open Module Topology
open scoped InnerProductSpace

namespace RHTower

open HilbertSchmidt GaloisForLFunctions.HTGeometry

noncomputable section

/-- Symmetric frequency pair spanning the rank-one packet. -/
def ccmSymmetricPair (L : CCMCircleLength) : (ccmCircleDirac (L : ℝ)).domain :=
  ⟨lpBasis ℤ (1 : ℤ) + lpBasis ℤ (-1 : ℤ),
    (ccmCircleDirac (L : ℝ)).domain.add_mem
      (lpBasis_mem_maximalRealDiagonalDomain _ (1 : ℤ))
      (lpBasis_mem_maximalRealDiagonalDomain _ (-1 : ℤ))⟩

def ccmSymmetricPairPacket (L : CCMCircleLength) : CCMCircleSmoothPacket L 1 :=
  fun _ => ccmSymmetricPair L

/-- Antisymmetric partner, orthogonal to the packet but coupled into it by the Dirac operator. -/
def ccmAntisymmetricPair (L : CCMCircleLength) : (ccmCircleDirac (L : ℝ)).domain :=
  ⟨lpBasis ℤ (1 : ℤ) - lpBasis ℤ (-1 : ℤ),
    (ccmCircleDirac (L : ℝ)).domain.sub_mem
      (lpBasis_mem_maximalRealDiagonalDomain _ (1 : ℤ))
      (lpBasis_mem_maximalRealDiagonalDomain _ (-1 : ℤ))⟩

theorem inner_ccmAntisymmetricPair_ccmSymmetricPair (L : CCMCircleLength) :
    inner ℂ (ccmAntisymmetricPair L : DiagonalL2 ℤ)
      (ccmSymmetricPair L : DiagonalL2 ℤ) = 0 := by
  change inner ℂ (lpBasis ℤ (1 : ℤ) - lpBasis ℤ (-1 : ℤ))
    (lpBasis ℤ (1 : ℤ) + lpBasis ℤ (-1 : ℤ)) = 0
  rw [inner_sub_left, inner_add_right, inner_add_right]
  have hpn : inner ℂ (lpBasis ℤ (1 : ℤ)) (lpBasis ℤ (-1 : ℤ)) = 0 :=
    (lpBasis ℤ).orthonormal.inner_eq_zero (by norm_num)
  have hnp : inner ℂ (lpBasis ℤ (-1 : ℤ)) (lpBasis ℤ (1 : ℤ)) = 0 :=
    (lpBasis ℤ).orthonormal.inner_eq_zero (by norm_num)
  rw [hpn, hnp]
  simp [(lpBasis ℤ).orthonormal.norm_eq_one]

theorem ccmAntisymmetricPair_mem_packet_orthogonal (L : CCMCircleLength) :
    (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∈
      (smoothPacketSpan (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  refine Submodule.span_induction (p := fun z _ =>
    inner ℂ (ccmAntisymmetricPair L : DiagonalL2 ℤ) z = 0) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨i, rfl⟩
    exact inner_ccmAntisymmetricPair_ccmSymmetricPair L
  · simp
  · intro x z _ _ hx hz
    rw [inner_add_right, hx, hz, add_zero]
  · intro c x _ hx
    rw [inner_smul_right, hx, mul_zero]

theorem ccmSymmetricPairProjection_antisymmetric_eq_zero (L : CCMCircleLength) :
    ccmConnesConsaniProjection L (ccmSymmetricPairPacket L)
      (ccmAntisymmetricPair L : DiagonalL2 ℤ) = 0 := by
  let V := smoothPacketSpan (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L)
  letI : V.HasOrthogonalProjection := by
    dsimp only [V]
    rw [smoothPacketSpan]
    exact RHTower.hasOrthogonalProjection_span (𝕜 := ℂ)
      (fun i => ((ccmSymmetricPairPacket L) i : DiagonalL2 ℤ))
  change V.starProjection (ccmAntisymmetricPair L : DiagonalL2 ℤ) = 0
  rw [Submodule.starProjection_apply_eq_zero_iff]
  exact ccmAntisymmetricPair_mem_packet_orthogonal L

theorem ccmCircleDirac_antisymmetric_eq_frequency_smul_symmetric
    (L : CCMCircleLength) :
    ccmCircleDirac (L : ℝ) (ccmAntisymmetricPair L) =
      (ccmCircleFrequency (L : ℝ) 1 : ℂ) •
        (ccmSymmetricPair L : DiagonalL2 ℤ) := by
  let ep : (ccmCircleDirac (L : ℝ)).domain :=
    ⟨lpBasis ℤ (1 : ℤ), lpBasis_mem_maximalRealDiagonalDomain _ (1 : ℤ)⟩
  let en : (ccmCircleDirac (L : ℝ)).domain :=
    ⟨lpBasis ℤ (-1 : ℤ), lpBasis_mem_maximalRealDiagonalDomain _ (-1 : ℤ)⟩
  have hanti : ccmAntisymmetricPair L = ep - en := Subtype.ext rfl
  have hmap : ccmCircleDirac (L : ℝ) (ep - en) =
      ccmCircleDirac (L : ℝ) ep - ccmCircleDirac (L : ℝ) en :=
    (ccmCircleDirac (L : ℝ)).toFun.map_sub ep en
  have hep : ccmCircleDirac (L : ℝ) ep =
      (ccmCircleFrequency (L : ℝ) 1 : ℂ) • lpBasis ℤ (1 : ℤ) := by
    simpa [ccmCircleDirac, ep] using
      (deningerPhaseGenerator_apply_basis (ccmCircleFrequency (L : ℝ)) (1 : ℤ))
  have hen : ccmCircleDirac (L : ℝ) en =
      (ccmCircleFrequency (L : ℝ) (-1) : ℂ) • lpBasis ℤ (-1 : ℤ) := by
    simpa [ccmCircleDirac, en] using
      (deningerPhaseGenerator_apply_basis (ccmCircleFrequency (L : ℝ)) (-1 : ℤ))
  rw [hanti, hmap, hep, hen]
  change (ccmCircleFrequency (L : ℝ) 1 : ℂ) • lpBasis ℤ (1 : ℤ) -
      (ccmCircleFrequency (L : ℝ) (-1) : ℂ) • lpBasis ℤ (-1 : ℤ) = _
  have hneg : ccmCircleFrequency (L : ℝ) (-1) = -ccmCircleFrequency (L : ℝ) 1 := by
    simp only [ccmCircleFrequency, Int.cast_neg, Int.cast_one]
    ring
  rw [hneg, Complex.ofReal_neg, neg_smul, sub_neg_eq_add]
  change (ccmCircleFrequency (L : ℝ) 1 : ℂ) • lpBasis ℤ (1 : ℤ) +
    (ccmCircleFrequency (L : ℝ) 1 : ℂ) • lpBasis ℤ (-1 : ℤ) =
    (ccmCircleFrequency (L : ℝ) 1 : ℂ) •
      (lpBasis ℤ (1 : ℤ) + lpBasis ℤ (-1 : ℤ))
  rw [smul_add]

theorem ccmCompressedDirac_antisymmetric_eq_zero (L : CCMCircleLength) :
    ccmConnesConsaniCompressedDirac L (ccmSymmetricPairPacket L)
      ⟨(ccmAntisymmetricPair L : DiagonalL2 ℤ), by
        change (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∈
          (ccmCircleDirac (L : ℝ)).domain
        exact (ccmAntisymmetricPair L).property⟩ = 0 := by
  change smoothPacketCompressedOperator (ccmCircleDirac (L : ℝ))
    (ccmSymmetricPairPacket L) _ = 0
  rw [smoothPacketCompressedOperator_apply_eq_zero_iff
    (ccmCircleDirac (L : ℝ)) (ccmCircleDirac_isSelfAdjoint (L : ℝ))]
  have hPzero := ccmSymmetricPairProjection_antisymmetric_eq_zero L
  have hQ : (1 - ccmConnesConsaniProjection L (ccmSymmetricPairPacket L))
      (ccmAntisymmetricPair L : DiagonalL2 ℤ) =
      (ccmAntisymmetricPair L : DiagonalL2 ℤ) := by
    change (ccmAntisymmetricPair L : DiagonalL2 ℤ) -
      ccmConnesConsaniProjection L (ccmSymmetricPairPacket L)
        (ccmAntisymmetricPair L : DiagonalL2 ℤ) = _
    rw [hPzero, sub_zero]
  let qarg : (ccmCircleDirac (L : ℝ)).domain :=
    ⟨(1 - ccmConnesConsaniProjection L (ccmSymmetricPairPacket L))
      (ccmAntisymmetricPair L : DiagonalL2 ℤ), by
        change (ccmAntisymmetricPair L : DiagonalL2 ℤ) -
          ccmConnesConsaniProjection L (ccmSymmetricPairPacket L)
            (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∈ (ccmCircleDirac (L : ℝ)).domain
        rw [hPzero, sub_zero]
        exact (ccmAntisymmetricPair L).property⟩
  change ccmCircleDirac (L : ℝ) qarg ∈
    smoothPacketSpan (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L)
  have hsubtype : qarg = ccmAntisymmetricPair L := Subtype.ext hQ
  rw [hsubtype, ccmCircleDirac_antisymmetric_eq_frequency_smul_symmetric]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨(0 : Fin 1), rfl⟩

theorem ccmAntisymmetricPair_ne_zero (L : CCMCircleLength) :
    (ccmAntisymmetricPair L : DiagonalL2 ℤ) ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : DiagonalL2 ℤ => z (1 : ℤ)) h
  change (lpBasis ℤ (1 : ℤ) - lpBasis ℤ (-1 : ℤ)) (1 : ℤ) = 0 at hcoord
  simp [lpBasis_apply, lp.single_apply] at hcoord

theorem ccmAntisymmetricPair_not_mem_packetSpan (L : CCMCircleLength) :
    (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∉
      smoothPacketSpan (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L) := by
  intro hmem
  have hortho := (Submodule.mem_orthogonal'
    (smoothPacketSpan (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L))
    (ccmAntisymmetricPair L : DiagonalL2 ℤ)).mp
      (ccmAntisymmetricPair_mem_packet_orthogonal L)
      (ccmAntisymmetricPair L : DiagonalL2 ℤ) hmem
  exact ccmAntisymmetricPair_ne_zero L (inner_self_eq_zero.mp hortho)

theorem ccmCircleDirac_antisymmetric_ne_zero (L : CCMCircleLength) :
    ccmCircleDirac (L : ℝ) (ccmAntisymmetricPair L) ≠ 0 := by
  rw [ccmCircleDirac_antisymmetric_eq_frequency_smul_symmetric]
  apply smul_ne_zero
  · exact_mod_cast (ne_of_gt (show 0 < ccmCircleFrequency (L : ℝ) 1 by
      rw [ccmCircleFrequency]
      norm_num
      exact div_pos (mul_pos zero_lt_two Real.pi_pos) L.property))
  · intro h
    have hcoord := congrArg (fun z : DiagonalL2 ℤ => z (1 : ℤ)) h
    change (lpBasis ℤ (1 : ℤ) + lpBasis ℤ (-1 : ℤ)) (1 : ℤ) = 0 at hcoord
    simp [lpBasis_apply, lp.single_apply] at hcoord

/-- **Concrete failure of the source nullity heuristic.**  A one-dimensional smooth packet has
an additional compressed zero mode which is neither in the packet nor in the original Dirac
kernel. -/
theorem connesConsani_propDpert1_exactRankCounterexample (L : CCMCircleLength) :
    ccmConnesConsaniCompressedDirac L (ccmSymmetricPairPacket L)
        ⟨(ccmAntisymmetricPair L : DiagonalL2 ℤ), by
          change (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∈
            (ccmCircleDirac (L : ℝ)).domain
          exact (ccmAntisymmetricPair L).property⟩ = 0 ∧
      (ccmAntisymmetricPair L : DiagonalL2 ℤ) ∉
        smoothPacketSpan (ccmCircleDirac (L : ℝ)) (ccmSymmetricPairPacket L) ∧
      ccmCircleDirac (L : ℝ) (ccmAntisymmetricPair L) ≠ 0 :=
  ⟨ccmCompressedDirac_antisymmetric_eq_zero L,
    ccmAntisymmetricPair_not_mem_packetSpan L,
    ccmCircleDirac_antisymmetric_ne_zero L⟩

end

end RHTower
