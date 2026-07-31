import GaloisForLFunctions.HTGeometry.ProjectiveHorizonJetFrame

/-!
# The moving-frame invariants of a covector span

The jet frame of a span absorbs the observer group, and what is left over is invariant.  Two
families come out of this.

The frame coordinates of a jet column are horizon observables: an observer multiplies both the
frame and the column by the same unimodular block, and the block cancels in the coordinates.  For a
direction outside the span, the jet coordinate with its span component removed by the frame is also
a horizon observable: an observer changes the row by a combination of span rows, and the frame
equation says the correction removes exactly that combination.

Together with the jet determinant these are the coordinates in which the horizon field of a span of
any rank becomes visible.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Expansion of a matrix-vector product as a sum. -/
theorem mulVec_apply_eq_sum {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]
    (M : Matrix ι ι R) (v : ι → R) (m : ι) : M.mulVec v m = ∑ q, M m q * v q := by
  rw [Matrix.mulVec]
  rfl

/-! ## The observer block in the jet field -/

/-- The unimodular block through which an observer of a span acts on the jets of that span. -/
def observerBlock (t : Finset n) (g : SpecialLinearGroup n K) :
    Matrix ↥t ↥t (HomogeneousJetField n K) :=
  (blockRestrict t g).map (algebraMap K (HomogeneousJetField n K))

theorem det_observerBlock {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) :
    (observerBlock t g).det = 1 := by
  rw [observerBlock, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_blockRestrict hg, map_one]

/-- An observer moves a jet column of the span by its block. -/
theorem linearJetAction_jetColumn {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) (l : ℕ) (m : ↥t) :
    g • jetColumn (K := K) t l m =
      (observerBlock t (g⁻¹ : SpecialLinearGroup n K)).mulVec (jetColumn t l) m := by
  rw [mulVec_apply_eq_sum]
  exact linearJetAction_freeCoordinate_of_mem hg m l

/-- An observer moves the jet frame of the span by its block. -/
theorem linearJetAction_jetFrame {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) (m c : ↥t) :
    g • jetFrame (K := K) t m c =
      (observerBlock t (g⁻¹ : SpecialLinearGroup n K) * jetFrame t :
        Matrix ↥t ↥t (HomogeneousJetField n K)) m c := by
  rw [Matrix.mul_apply]
  exact linearJetAction_freeCoordinate_of_mem hg m (jetOrder t c)

/-! ## The frame coordinates are horizon observables -/

/-- **Invariance of the frame coordinates.**  An observer of a span multiplies both the jet frame
and every jet column by the same unimodular block, so the frame coordinates are unchanged. -/
theorem frameCoord_invariant {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) (l : ℕ) :
    (fun c => g • frameCoord (K := K) t l c) = frameCoord t l := by
  have hBdet : IsUnit (observerBlock t (g⁻¹ : SpecialLinearGroup n K)).det := by
    rw [det_observerBlock (inv_mem hg)]
    exact isUnit_one
  refine frameCoord_unique ?_
  have hcancel : (observerBlock t (g⁻¹ : SpecialLinearGroup n K)).mulVec
        ((jetFrame (K := K) t).mulVec (fun c => g • frameCoord (K := K) t l c)) =
      (observerBlock t (g⁻¹ : SpecialLinearGroup n K)).mulVec (jetColumn t l) := by
    funext m
    rw [Matrix.mulVec_mulVec, mulVec_apply_eq_sum,
      Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => by
        rw [← linearJetAction_jetFrame hg m c]]
    have hsum : ∑ c : ↥t, (g • jetFrame (K := K) t m c) * (g • frameCoord (K := K) t l c) =
        g • ∑ c : ↥t, jetFrame (K := K) t m c * frameCoord (K := K) t l c := by
      rw [linearJetAction_apply, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [linearJetAction_apply, ← map_mul]
    rw [hsum, ← mulVec_apply_eq_sum, jetFrame_mulVec_frameCoord,
      linearJetAction_jetColumn hg l m]
  have hstep := congrArg
    (fun w => (observerBlock t (g⁻¹ : SpecialLinearGroup n K))⁻¹.mulVec w) hcancel
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet,
    Matrix.one_mul, Matrix.one_mulVec] at hstep
  exact hstep

theorem frameCoord_mem_horizonField (t : Finset n) (l : ℕ) (c : ↥t) :
    frameCoord (K := K) t l c ∈ horizonField (K := K) (↑t : Set n) := by
  rw [mem_horizonField_iff']
  intro g hg
  exact congrFun (frameCoord_invariant hg l) c

/-! ## The normalised transverse jets -/

/-- An observer of a span changes a jet coordinate outside the span by a combination of the jet
coordinates of the span. -/
theorem linearJetAction_freeCoordinate_notMem {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) {x : n} (hx : x ∉ t) (l : ℕ) :
    g • freeCoordinate K (n × ℕ) (x, l) =
      freeCoordinate K (n × ℕ) (x, l) +
        ∑ m : ↥t, algebraMap K (HomogeneousJetField n K)
            (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) x (m : n)) *
          freeCoordinate K (n × ℕ) ((m : n), l) := by
  classical
  have hginv : (g⁻¹ : SpecialLinearGroup n K) ∈
      chartSubsetStabilizer (K := K) (↑t : Set n) := inv_mem hg
  rw [linearJetAction_freeCoordinate,
    ← Finset.sum_add_sum_compl t fun m => algebraMap K (HomogeneousJetField n K)
      (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) x m) *
        freeCoordinate K (n × ℕ) (m, l),
    add_comm]
  congr 1
  · rw [Finset.sum_eq_single x]
    · rw [hginv x (by simpa using hx) x, Matrix.one_apply_eq, map_one, one_mul]
    · intro m hm hmx
      rw [hginv m (by simpa using (Finset.mem_compl.1 hm)) x,
        Matrix.one_apply_ne (Ne.symm hmx), map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_compl.2 hx) hcon
  · exact (Finset.sum_coe_sort t _).symm

/-- The jet coordinate of a direction outside a span, with its span component removed by the frame
of the span. -/
def transverseNormal (t : Finset n) (x : n) (l : ℕ) : HomogeneousJetField n K :=
  freeCoordinate K (n × ℕ) (x, l) -
    ∑ c : ↥t, frameCoord t l c * freeCoordinate K (n × ℕ) (x, jetOrder t c)

/-- **Invariance of the normalised transverse jets.**  The correction removes exactly the
combination of span rows that an observer adds. -/
theorem transverseNormal_invariant {t : Finset n} {g : SpecialLinearGroup n K}
    (hg : g ∈ chartSubsetStabilizer (K := K) (↑t : Set n)) {x : n} (hx : x ∉ t) (l : ℕ) :
    g • transverseNormal (K := K) t x l = transverseNormal t x l := by
  classical
  set a : ↥t → HomogeneousJetField n K := fun m =>
    algebraMap K (HomogeneousJetField n K)
      (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) x (m : n)) with ha
  have hring : ∀ u v : HomogeneousJetField n K, g • (u - v) = g • u - g • v := by
    intro u v
    rw [linearJetAction_apply, map_sub]
    rfl
  have hsmulsum : ∀ F : ↥t → HomogeneousJetField n K,
      g • (∑ c : ↥t, F c) = ∑ c : ↥t, g • F c := by
    intro F
    rw [linearJetAction_apply, map_sum]
    rfl
  have hmul : ∀ u v : HomogeneousJetField n K, g • (u * v) = (g • u) * (g • v) := by
    intro u v
    rw [linearJetAction_apply, map_mul]
    rfl
  have hfc : ∀ c : ↥t, g • frameCoord (K := K) t l c = frameCoord t l c :=
    fun c => congrFun (frameCoord_invariant hg l) c
  have hxact : ∀ j : ℕ, g • freeCoordinate K (n × ℕ) (x, j) =
      freeCoordinate K (n × ℕ) (x, j) +
        ∑ m : ↥t, a m * freeCoordinate K (n × ℕ) ((m : n), j) :=
    fun j => linearJetAction_freeCoordinate_notMem hg hx j
  have hkey : ∀ m : ↥t, ∑ c : ↥t, frameCoord (K := K) t l c *
      freeCoordinate K (n × ℕ) ((m : n), jetOrder t c) =
      freeCoordinate K (n × ℕ) ((m : n), l) := by
    intro m
    have h := congrFun (jetFrame_mulVec_frameCoord (K := K) t l) m
    rw [mulVec_apply_eq_sum] at h
    simp only [jetFrame, jetArray, jetColumn, Matrix.of_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hswap : ∑ c : ↥t, frameCoord (K := K) t l c *
        (∑ m : ↥t, a m * freeCoordinate K (n × ℕ) ((m : n), jetOrder t c)) =
      ∑ m : ↥t, a m * freeCoordinate K (n × ℕ) ((m : n), l) := by
    have hstep : ∀ c : ↥t, frameCoord (K := K) t l c *
        (∑ m : ↥t, a m * freeCoordinate K (n × ℕ) ((m : n), jetOrder t c)) =
        ∑ m : ↥t, a m * (frameCoord (K := K) t l c *
          freeCoordinate K (n × ℕ) ((m : n), jetOrder t c)) := by
      intro c
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => hstep c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, hkey m]
  rw [transverseNormal, hring, hsmulsum]
  simp only [hmul, hfc, hxact]
  rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) =>
      mul_add (frameCoord (K := K) t l c) _ _,
    Finset.sum_add_distrib, hswap]
  ring

theorem transverseNormal_mem_horizonField {t : Finset n} {x : n} (hx : x ∉ t) (l : ℕ) :
    transverseNormal (K := K) t x l ∈ horizonField (K := K) (↑t : Set n) := by
  rw [mem_horizonField_iff']
  intro g hg
  exact transverseNormal_invariant hg hx l

end

end GaloisForLFunctions.HTGeometry
