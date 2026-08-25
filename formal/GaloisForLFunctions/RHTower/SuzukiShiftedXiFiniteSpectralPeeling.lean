import GaloisForLFunctions.RHTower.SuzukiShiftedXiCrossingChannelPeeling
import GaloisForLFunctions.RHTower.SuzukiShiftedXiStrongContinuity
import GaloisForLFunctions.RHTower.SuzukiShiftedXiLeakageRankIndex
import GaloisForLFunctions.RHTower.SuzukiShiftedXiLeakageRH
import GaloisForLFunctions.RHTower.XiShiftEulerProductBridge
import GaloisForLFunctions.HTGeometry.FiniteChannelGramSpectralPeeling

open Complex Filter Topology
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem finiteBlaschke_toMultiplier_isometry (B : FiniteBlaschke) :
    HardyMultiplierIsometry B.toMultiplier :=
  norm_hardyMul_blaschke B

def xiShiftPersistentOrthonormalBasis (B₀ : FiniteBlaschke) :
    OrthonormalBasis (Fin (Module.finrank ℂ (finiteBlaschkeModelSpace B₀))) ℂ
      (finiteBlaschkeModelSpace B₀) :=
  stdOrthonormalBasis ℂ (finiteBlaschkeModelSpace B₀)

def xiShiftPersistentFrame (B₀ : FiniteBlaschke) :
    Fin (Module.finrank ℂ (finiteBlaschkeModelSpace B₀)) → HardyDisk :=
  fun j => (xiShiftPersistentOrthonormalBasis B₀ j : HardyDisk)

def xiShiftCrossingOrthonormalBasis
    {ι : Type*} {omega : ι → ℝ} (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke) (i : ι) :
    OrthonormalBasis (Fin P.multiplicity) ℂ
      (hardyMultiplierFiniteCrossingChannel B₀.toMultiplier
        ((P.toBoundaryPacket homega).divisor i)) :=
    (stdOrthonormalBasis ℂ
    (hardyMultiplierFiniteCrossingChannel B₀.toMultiplier
      ((P.toBoundaryPacket homega).divisor i))).reindex
    (finCongr (P.finrank_crossingChannel_eq_multiplicity homega
      (fun _ => B₀.toMultiplier) (fun _ => finiteBlaschke_toMultiplier_isometry B₀) i))

def xiShiftCrossingFrame
    {ι : Type*} {omega : ι → ℝ} (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (i : ι) : Fin P.multiplicity → HardyDisk :=
  fun j => (xiShiftCrossingOrthonormalBasis homega P B₀ i j : HardyDisk)

theorem norm_xiShiftPersistentFrame (B₀ : FiniteBlaschke)
    (j : Fin (Module.finrank ℂ (finiteBlaschkeModelSpace B₀))) :
    ‖xiShiftPersistentFrame B₀ j‖ = 1 := by
  exact (xiShiftPersistentOrthonormalBasis B₀).orthonormal.norm_eq_one j

theorem norm_xiShiftCrossingFrame
    {ι : Type*} {omega : ι → ℝ} (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (i : ι) (j : Fin P.multiplicity) :
    ‖xiShiftCrossingFrame homega P B₀ i j‖ = 1 := by
  exact (xiShiftCrossingOrthonormalBasis homega P B₀ i).orthonormal.norm_eq_one j

theorem inner_xiShiftCrossingFrame
    {ι : Type*} {omega : ι → ℝ} (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (i : ι) (j k : Fin P.multiplicity) :
    inner ℂ (xiShiftCrossingFrame homega P B₀ i j)
        (xiShiftCrossingFrame homega P B₀ i k) =
      (1 : Matrix (Fin P.multiplicity) (Fin P.multiplicity) ℂ) j k := by
  simpa [xiShiftCrossingFrame, Matrix.one_apply] using
    (orthonormal_iff_ite.mp
      (xiShiftCrossingOrthonormalBasis homega P B₀ i).orthonormal j k)

theorem xiShiftCrossingFrame_mem
    {ι : Type*} {omega : ι → ℝ} (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (i : ι) (j : Fin P.multiplicity) :
    xiShiftCrossingFrame homega P B₀ i j ∈
      hardyMultiplierFiniteCrossingChannel B₀.toMultiplier
        ((P.toBoundaryPacket homega).divisor i) :=
  (xiShiftCrossingOrthonormalBasis homega P B₀ i j).property

theorem xiShiftPersistentFrame_mem_crossing_orthogonal
    {ι : Type*} {omega : ι → ℝ} (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (i : ι) (j : Fin (Module.finrank ℂ (finiteBlaschkeModelSpace B₀))) :
    xiShiftPersistentFrame B₀ j ∈
      (hardyMultiplierFiniteCrossingChannel B₀.toMultiplier
        ((P.toBoundaryPacket homega).divisor i))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have hp : xiShiftPersistentFrame B₀ j ∈
      hardyMultiplierModelSpace B₀.toMultiplier :=
    (xiShiftPersistentOrthonormalBasis B₀ j).property
  have hz' : z ∈ hardyMultiplierModelSpace
      ((P.toBoundaryPacket homega).divisor i).toMultiplier := hz
  have hzero := hardyMultiplierModelSpace_inner_transported_eq_zero
    B₀.toMultiplier ((P.toBoundaryPacket homega).divisor i).toMultiplier
    ⟨xiShiftPersistentFrame B₀ j, hp⟩ ⟨z, hz'⟩
  have hz0 : inner ℂ (xiShiftPersistentFrame B₀ j)
      ((hardyMul B₀.toMultiplier) z) = 0 := by
    simpa using hzero
  rw [← inner_conj_symm]
  change (starRingEnd ℂ)
    (inner ℂ (xiShiftPersistentFrame B₀ j) ((hardyMul B₀.toMultiplier) z)) = 0
  rw [hz0, map_zero]

/-- Literal shifted-Xi theorem C: the complete finite Gram matrix converges to the persistent
block plus one unit channel for every crossing multiplicity. -/
theorem tendsto_actualXiFiniteLeakageSplitGram
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : ∀ i, 0 < omega i) (homega₀ : 0 ≤ omega₀)
    (hlim : Tendsto omega l (𝓝 omega₀))
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (hfactor : ∀ i,
      B₀.toMultiplier.mul ((P.toBoundaryPacket homega).divisor i).toMultiplier =
        xiShiftPoleBlaschkeMultiplier (homega i).le)
    (hP : P.Tame homega l) :
    Tendsto (fun i => finiteLeakageSplitGram
        (hardyMultiplierLeakageCore
          (xiShiftInfiniteSchurNumerator (homega i).le)
          (xiShiftPoleBlaschkeMultiplier (homega i).le))
        (xiShiftPersistentFrame B₀) (xiShiftCrossingFrame homega P B₀ i)) l
      (𝓝 (finiteBlockSum
        (xiShiftInfiniteLeakageGram homega₀ (xiShiftPersistentFrame B₀))
        (1 : Matrix (Fin P.multiplicity) (Fin P.multiplicity) ℂ))) := by
  let S := fun i => hardyMultiplierFiniteCrossingChannel B₀.toMultiplier
    ((P.toBoundaryPacket homega).divisor i)
  let F : ι → Type := fun i =>
    hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier (homega i).le)
  let L : ∀ i, HardyDisk →L[ℂ] F i := fun i =>
    hardyMultiplierLeakageCore
      (xiShiftInfiniteSchurNumerator (homega i).le)
      (xiShiftPoleBlaschkeMultiplier (homega i).le)
  change Tendsto (fun i => finiteHermitianBlock
      (finiteLeakagePersistentGram (L i) (xiShiftPersistentFrame B₀))
      (finiteLeakageCrossGram (L i) (xiShiftPersistentFrame B₀)
        (xiShiftCrossingFrame homega P B₀ i))
      (finiteLeakageCrossingGram (L i) (xiShiftCrossingFrame homega P B₀ i))) l _
  apply tendsto_finiteHermitianBlock_peeling
  · change Tendsto (fun i =>
        xiShiftInfiniteLeakageGram (homega i).le (xiShiftPersistentFrame B₀)) l
      (𝓝 (xiShiftInfiniteLeakageGram homega₀ (xiShiftPersistentFrame B₀)))
    exact tendsto_xiShiftInfiniteLeakageGram hlim (fun i => (homega i).le)
      homega₀ (xiShiftPersistentFrame B₀)
  · apply tendsto_finiteLeakageCrossGram_zero_of_channelOffDiagonal_pi
      (E := HardyDisk) F S L
      (xiShiftPersistentFrame B₀) (xiShiftCrossingFrame homega P B₀)
    · exact xiShiftPersistentFrame_mem_crossing_orthogonal homega P B₀
    · exact norm_xiShiftPersistentFrame B₀
    · exact xiShiftCrossingFrame_mem homega P B₀
    · exact norm_xiShiftCrossingFrame homega P B₀
    · simpa [S, L, F] using
        P.tendsto_norm_actualXiCrossingOffDiagonalGram_zero homega
          (fun _ => B₀.toMultiplier) (fun _ => finiteBlaschke_toMultiplier_isometry B₀)
          hfactor hP
  · apply tendsto_finiteLeakageCrossingGram_one_of_channelDefect_pi
      (E := HardyDisk) F S L
      (xiShiftCrossingFrame homega P B₀)
    · exact xiShiftCrossingFrame_mem homega P B₀
    · exact norm_xiShiftCrossingFrame homega P B₀
    · exact inner_xiShiftCrossingFrame homega P B₀
    · simpa [S, L, F] using
        P.tendsto_norm_actualXiCrossingGramDefect_zero homega
          (fun _ => B₀.toMultiplier) (fun _ => finiteBlaschke_toMultiplier_isometry B₀)
          hfactor hP

/-- Shifted-Xi theorem C `(14)`: exact squared Hilbert--Schmidt trace jump. -/
theorem tendsto_trace_actualXiFiniteLeakageSplitGram
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : ∀ i, 0 < omega i) (homega₀ : 0 ≤ omega₀)
    (hlim : Tendsto omega l (𝓝 omega₀))
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (hfactor : ∀ i,
      B₀.toMultiplier.mul ((P.toBoundaryPacket homega).divisor i).toMultiplier =
        xiShiftPoleBlaschkeMultiplier (homega i).le)
    (hP : P.Tame homega l) :
    Tendsto (fun i =>
        (finiteLeakageSplitGram
          (hardyMultiplierLeakageCore
            (xiShiftInfiniteSchurNumerator (homega i).le)
            (xiShiftPoleBlaschkeMultiplier (homega i).le))
          (xiShiftPersistentFrame B₀) (xiShiftCrossingFrame homega P B₀ i)).trace -
        (xiShiftInfiniteLeakageGram homega₀ (xiShiftPersistentFrame B₀)).trace) l
      (𝓝 P.multiplicity) := by
  exact tendsto_trace_finiteGram_peeling _
    (xiShiftInfiniteLeakageGram homega₀ (xiShiftPersistentFrame B₀))
    (tendsto_actualXiFiniteLeakageSplitGram homega homega₀ hlim P B₀ hfactor hP)

/-- Shifted-Xi theorem C `(13)`: exact spectral multiset at the peeling limit. -/
theorem roots_charpoly_actualXiFiniteLeakagePeelingLimit
    {n m : ℕ} {omega₀ : ℝ} (homega₀ : 0 ≤ omega₀)
    (v : Fin n → HardyDisk) :
    (finiteBlockSum (xiShiftInfiniteLeakageGram homega₀ v)
        (1 : Matrix (Fin m) (Fin m) ℂ)).charpoly.roots =
      (xiShiftInfiniteLeakageGram homega₀ v).charpoly.roots +
        Multiset.replicate m 1 :=
  roots_charpoly_finiteBlockSum_one _

/-- Shifted-Xi theorem C `(13)`: sorted eigenvalues of the literal finite Gram converge to those
of the persistent block plus `m` unit channels. -/
theorem tendsto_sortedSpectrum_actualXiFiniteLeakageSplitGram
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : ∀ i, 0 < omega i) (homega₀ : 0 ≤ omega₀)
    (hlim : Tendsto omega l (𝓝 omega₀))
    (P : XiShiftCrossingPacket omega) (B₀ : FiniteBlaschke)
    (hfactor : ∀ i,
      B₀.toMultiplier.mul ((P.toBoundaryPacket homega).divisor i).toMultiplier =
        xiShiftPoleBlaschkeMultiplier (homega i).le)
    (hP : P.Tame homega l) :
    let G := fun i => finiteLeakageSplitGram
      (hardyMultiplierLeakageCore
        (xiShiftInfiniteSchurNumerator (homega i).le)
        (xiShiftPoleBlaschkeMultiplier (homega i).le))
      (xiShiftPersistentFrame B₀) (xiShiftCrossingFrame homega P B₀ i)
    let G₀ := finiteBlockSum
      (xiShiftInfiniteLeakageGram homega₀ (xiShiftPersistentFrame B₀))
      (1 : Matrix (Fin P.multiplicity) (Fin P.multiplicity) ℂ)
    let hG : ∀ i, (G i).IsHermitian := fun i =>
      finiteLeakageSplitGram_isHermitian _ _ _
    let hG₀ : G₀.IsHermitian := finiteBlockSum_isHermitian
      (finiteLeakagePersistentGram_isHermitian
        (xiShiftInfiniteLeakageCore homega₀) (xiShiftPersistentFrame B₀))
      Matrix.isHermitian_one
    Tendsto (fun i => sortedTuple (hG i).eigenvalues) l
      (𝓝 (sortedTuple hG₀.eigenvalues)) := by
  dsimp only
  apply tendsto_sortedSpectrum_of_tendsto_hermitian
  · exact tendsto_actualXiFiniteLeakageSplitGram
      homega homega₀ hlim P B₀ hfactor hP

end

end RHTower
