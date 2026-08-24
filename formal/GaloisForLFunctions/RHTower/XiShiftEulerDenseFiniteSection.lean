import GaloisForLFunctions.RHTower.XiShiftEulerRegionIndex
import GaloisForLFunctions.HTGeometry.KernelNestedFiniteSectionInertia

/-!
# Dense Euler-region finite sections of the shifted-Xi Pick kernel

Every dense sequence in the Euler sampling half-plane retains the complete nonexceptional
shifted-Xi negative index.  Its nested Pick matrices have monotone negative inertia; in the finite
divisor case the inertia stabilizes at the exact strict-right Xi divisor-copy count, and in the
infinite case it tends to infinity.  The matrix inertia is literally the number of strictly
negative eigenvalues, counted with multiplicity.
-/

open Complex Set Topology Filter Matrix
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The nested Euler-region shifted-Xi Pick matrix along a fixed sampling sequence. -/
def eulerXiShiftPickFiniteSectionMatrix (omega : ℝ)
    (z : ℕ → xiShiftEulerUpperSet omega) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  kernelFiniteSectionMatrix
    (fun u v : xiShiftEulerUpperSet omega => eulerXiShiftPick omega u.1 v.1) z N

/-- Negative inertia of the nested Euler-region shifted-Xi Pick matrix. -/
def eulerXiShiftPickFiniteSectionNegIndex (omega : ℝ)
    (z : ℕ → xiShiftEulerUpperSet omega) (N : ℕ) : ℕ :=
  kernelFiniteSectionNegIndex
    (fun u v : xiShiftEulerUpperSet omega => eulerXiShiftPick omega u.1 v.1) z N

/-- Supremum of all nested Euler-region Pick inertias. -/
def eulerXiShiftPickFiniteSectionNegIndexSup (omega : ℝ)
    (z : ℕ → xiShiftEulerUpperSet omega) : WithTop ℕ :=
  kernelFiniteSectionNegIndexSup
    (fun u v : xiShiftEulerUpperSet omega => eulerXiShiftPick omega u.1 v.1) z

/-- The literal Euler shifted-Xi Pick kernel is Hermitian. -/
theorem star_eulerXiShiftPick_swap (omega : ℝ) (u v : ℂ) :
    (starRingEnd ℂ) (eulerXiShiftPick omega u v) =
      eulerXiShiftPick omega v u := by
  rw [eulerXiShiftPick_eq_upperHalfPlaneSchurKernel,
    eulerXiShiftPick_eq_upperHalfPlaneSchurKernel]
  simp [upperHalfPlaneSchurKernel, Complex.conj_I]
  have hden : v - (starRingEnd ℂ) u = -((starRingEnd ℂ) u - v) := by ring
  rw [hden, div_neg]
  ring

/-- Finite-section negative inertia is exactly the number of strictly negative eigenvalues. -/
theorem eulerXiShiftPickFiniteSectionNegIndex_eq_card_neg_eigenvalues
    (omega : ℝ) (z : ℕ → xiShiftEulerUpperSet omega) (N : ℕ) :
    eulerXiShiftPickFiniteSectionNegIndex omega z N =
      ({i | (kernelFiniteSectionMatrix_isHermitian
        (fun u v : xiShiftEulerUpperSet omega => by
          exact star_eulerXiShiftPick_swap omega u.1 v.1) z N).eigenvalues i < 0} :
        Finset (Fin N)).card := by
  exact kernelFiniteSectionNegIndex_eq_card_neg_eigenvalues
    (fun u v : xiShiftEulerUpperSet omega => star_eulerXiShiftPick_swap omega u.1 v.1) z N

/-- Exact dense finite-section form of the Euler-region shifted-Xi index theorem. In the finite
branch the nested inertia stabilizes at, tends to, and has supremum equal to the strict-right Xi
divisor-copy count. In the infinite branch it tends to infinity and has supremum `⊤`. -/
theorem eulerXiShiftPick_denseFiniteSection_limit_classification
    {omega : ℝ} (homega : 0 < omega) (hnon : SuzukiShiftNonexceptional omega)
    (z : ℕ → xiShiftEulerUpperSet omega) (hz : DenseRange z) :
    (Finite (XiShiftRightZeroCopy omega) ∧
      Filter.Tendsto (eulerXiShiftPickFiniteSectionNegIndex omega z)
        Filter.atTop (nhds (Nat.card (XiShiftRightZeroCopy omega))) ∧
      (∀ᶠ N in Filter.atTop,
        eulerXiShiftPickFiniteSectionNegIndex omega z N =
          Nat.card (XiShiftRightZeroCopy omega)) ∧
      eulerXiShiftPickFiniteSectionNegIndexSup omega z =
        (Nat.card (XiShiftRightZeroCopy omega) : WithTop ℕ) ∧
      ∀ N, eulerXiShiftPickFiniteSectionNegIndex omega z N ≤
        Nat.card (XiShiftRightZeroCopy omega)) ∨
    (Infinite (XiShiftRightZeroCopy omega) ∧
      Filter.Tendsto (eulerXiShiftPickFiniteSectionNegIndex omega z)
        Filter.atTop Filter.atTop ∧
      eulerXiShiftPickFiniteSectionNegIndexSup omega z = ⊤) := by
  let D : Set ℂ := Set.range fun n => (z n).1
  let zd : ℕ → D := fun n => ⟨(z n).1, ⟨n, rfl⟩⟩
  have hzd : Function.Surjective zd := by
    intro w
    obtain ⟨n, hn⟩ := w.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  obtain ⟨p, hpU, hfreq⟩ := denseRange_subtype_range_accumulates
    (isOpen_xiShiftEulerUpperSet omega) (xiShiftEulerUpperSet_nonempty omega) z hz
  have hsub : D ⊆ upperHalfPlaneSet := by
    rintro w ⟨n, rfl⟩
    exact xiShiftEulerUpperSet_subset_upperHalfPlane homega (z n).2
  have hregular : ∀ w ∈ D, suzukiCanonicalE omega w ≠ 0 := by
    rintro w ⟨n, rfl⟩
    exact suzukiCanonicalE_ne_zero_of_mem_xiShiftEulerUpperSet homega (z n).1 (z n).2
  have hpUpper : p ∈ upperHalfPlaneSet :=
    xiShiftEulerUpperSet_subset_upperHalfPlane homega hpU
  let K := fun u v : D => eulerXiShiftPick omega u.1 v.1
  have hclass :
      (Finite (XiShiftRightZeroCopy omega) ∧
        HasFiniteKernelNegativeDimension K (Nat.card (XiShiftRightZeroCopy omega)) ∧
        ∀ r, HasFiniteKernelNegativeDimension K r →
          r ≤ Nat.card (XiShiftRightZeroCopy omega)) ∨
      (Infinite (XiShiftRightZeroCopy omega) ∧
        ∀ r, HasFiniteKernelNegativeDimension K r) := by
    have h := xiShiftRegularUpperKernel_accumulationSet_negativeIndex_classification
      homega hnon D hsub hregular p hpUpper hfreq
    simpa only [K, eulerXiShiftPick_eq_upperHalfPlaneSchurKernel] using h
  have hsection (N : ℕ) :
      kernelFiniteSectionNegIndex K zd N =
        eulerXiShiftPickFiniteSectionNegIndex omega z N := by
    rfl
  have hsectionFun : kernelFiniteSectionNegIndex K zd =
      eulerXiShiftPickFiniteSectionNegIndex omega z := funext hsection
  rcases hclass with hfinite | hinfinite
  · left
    refine ⟨hfinite.1, ?_, ?_, ?_, ?_⟩
    · have h := tendsto_kernelFiniteSectionNegIndex_of_surjective
        K zd hzd hfinite.2.1 hfinite.2.2
      rw [hsectionFun] at h
      exact h
    · have h := eventually_kernelFiniteSectionNegIndex_eq_of_surjective
        K zd hzd hfinite.2.1 hfinite.2.2
      filter_upwards [h] with N hN
      simpa only [hsection] using hN
    · have h := kernelFiniteSectionNegIndexSup_eq_of_surjective
        K zd hzd hfinite.2.1 hfinite.2.2
      simpa [kernelFiniteSectionNegIndexSup, eulerXiShiftPickFiniteSectionNegIndexSup,
        eulerXiShiftPickFiniteSectionNegIndex, hsectionFun] using h
    · intro N
      rw [← hsection]
      exact kernelFiniteSectionNegIndex_le_of_global_bound hfinite.2.2 zd N
  · right
    refine ⟨hinfinite.1, ?_, ?_⟩
    · have h := tendsto_kernelFiniteSectionNegIndex_atTop_of_surjective
        K zd hzd hinfinite.2
      rw [hsectionFun] at h
      exact h
    · have h := kernelFiniteSectionNegIndexSup_eq_top_of_surjective
        K zd hzd hinfinite.2
      simpa [kernelFiniteSectionNegIndexSup, eulerXiShiftPickFiniteSectionNegIndexSup,
        eulerXiShiftPickFiniteSectionNegIndex, hsectionFun] using h

/-- Pick matrix formed from an arbitrary finite packet of Euler-region sample points. -/
def eulerXiShiftPickSampleMatrix (omega : ℝ) {N : ℕ}
    (w : Fin N → xiShiftEulerUpperSet omega) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => eulerXiShiftPick omega (w j).1 (w i).1

theorem eulerXiShiftPickSampleMatrix_isHermitian
    (omega : ℝ) {N : ℕ} (w : Fin N → xiShiftEulerUpperSet omega) :
    (eulerXiShiftPickSampleMatrix omega w).IsHermitian := by
  ext i j
  simp [eulerXiShiftPickSampleMatrix, star_eulerXiShiftPick_swap]

/-- Exact arbitrary-finite-matrix form of the shifted zero-count law. -/
theorem eulerXiShiftPick_arbitrarySample_inertia_le_iff
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) (m : ℕ) :
    (Finite (XiShiftRightZeroCopy omega) ∧
        Nat.card (XiShiftRightZeroCopy omega) ≤ m) ↔
      ∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
        hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ m := by
  let K := fun z w : xiShiftEulerUpperSet omega =>
    eulerXiShiftPick omega z.1 w.1
  rw [show (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
      hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ m) ↔
      ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ m by
    simpa only [K, eulerXiShiftPickSampleMatrix] using
      (finite_sample_negIndex_le_iff_global_bound K m)]
  have hclass := eulerXiShiftPick_negativeIndex_classification homega hnon
  change (Finite (XiShiftRightZeroCopy omega) ∧
      Nat.card (XiShiftRightZeroCopy omega) ≤ m) ↔
    ∀ r, HasFiniteKernelNegativeDimension K r → r ≤ m
  constructor
  · rintro ⟨hfinite, hcard⟩
    rcases hclass with hfin | hinf
    · intro r hr
      exact (hfin.2.2 r hr).trans hcard
    · letI : Finite (XiShiftRightZeroCopy omega) := hfinite
      letI : Infinite (XiShiftRightZeroCopy omega) := hinf.1
      exact (not_finite (XiShiftRightZeroCopy omega)).elim
  · intro hbound
    rcases hclass with hfin | hinf
    · exact ⟨hfin.1, hbound _ hfin.2.1⟩
    · have hbad := hbound (m + 1) (hinf.2 (m + 1))
      omega

/-- Zero-free shifted half-strip is equivalent to positive semidefiniteness of every arbitrary
finite Euler-region Pick matrix. -/
theorem eulerXiShiftPick_noZero_iff_everySample_posSemidef
    {omega : ℝ} (homega : 0 < omega)
    (hnon : SuzukiShiftNonexceptional omega) :
    IsEmpty (XiShiftRightZeroCopy omega) ↔
      ∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
        (eulerXiShiftPickSampleMatrix omega w).PosSemidef := by
  have hpsd :
      (∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
          (eulerXiShiftPickSampleMatrix omega w).PosSemidef) ↔
        ∀ (N : ℕ) (w : Fin N → xiShiftEulerUpperSet omega),
          hermNegIndex (eulerXiShiftPickSampleMatrix omega w) ≤ 0 := by
    constructor
    · intro h N w
      rw [Nat.le_zero]
      exact (hermNegIndex_eq_zero_iff_posSemidef
        (eulerXiShiftPickSampleMatrix_isHermitian omega w)).mpr (h N w)
    · intro h N w
      apply (hermNegIndex_eq_zero_iff_posSemidef
        (eulerXiShiftPickSampleMatrix_isHermitian omega w)).mp
      exact Nat.eq_zero_of_le_zero (h N w)
  rw [hpsd, ← eulerXiShiftPick_arbitrarySample_inertia_le_iff homega hnon 0]
  constructor
  · intro hempty
    letI : IsEmpty (XiShiftRightZeroCopy omega) := hempty
    refine ⟨inferInstance, ?_⟩
    rw [Nat.le_zero, Nat.card_eq_zero]
    exact Or.inl hempty
  · rintro ⟨hfinite, hcard⟩
    rw [Nat.le_zero] at hcard
    rw [Nat.card_eq_zero] at hcard
    exact hcard.resolve_right (fun hinfinite => by
      letI : Finite (XiShiftRightZeroCopy omega) := hfinite
      letI : Infinite (XiShiftRightZeroCopy omega) := hinfinite
      exact not_finite (XiShiftRightZeroCopy omega))

end

end RHTower
