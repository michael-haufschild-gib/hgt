import GaloisForLFunctions.HTGeometry.DifferentialPointedCollisionIncidenceMatroid
import GaloisForLFunctions.HTGeometry.LinearSystemDescent
import GaloisForLFunctions.HilbertMetric.UnisolventEvaluation
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Linear and base-field bridges for pointed collision incidence

Pointed collision incidence matrices have entries in the prime field.  Their represented matroid
is therefore independent of the chosen characteristic-zero coefficient field.  This file also
identifies full-ground independence with ordinary row independence and proves that pairwise
differences of any linearly independent occupied-label family represent exactly this matroid.

These are the coefficient-field and linear-algebra connectors needed to transport differential
collision laws to literal complex evaluation and Hilbert geometry.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- **Characteristic-zero pointed-incidence universality.** Collapsing repeated labels and the
distinguished loop label commutes with every characteristic-zero coefficient-field change. -/
theorem pointedCollisionIncidenceMatroid_charZero_eq
    {C D V E Frame : Type} [Field C] [Field D] [CharZero C] [CharZero D]
    [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    pointedCollisionIncidenceMatroid (C := C) frame loopFrame tail head =
      pointedCollisionIncidenceMatroid (C := D) frame loopFrame tail head := by
  apply Matroid.ext_indep
  · simp
  · intro I _hI
    rw [pointedCollisionIncidenceMatroid_indep_iff,
      pointedCollisionIncidenceMatroid_indep_iff]
    have hC :
        (fun e : I ↦ pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head e) =
          fun e : I ↦ algebraMap ℚ C ∘
            pointedCollisionIncidenceMatrix
              (C := ℚ) frame loopFrame tail head e := by
      funext e q
      simp only [pointedCollisionIncidenceMatrix, Function.comp_apply, map_sub]
      congr <;> split_ifs <;> simp_all
    have hD :
        (fun e : I ↦ pointedCollisionIncidenceMatrix
          (C := D) frame loopFrame tail head e) =
          fun e : I ↦ algebraMap ℚ D ∘
            pointedCollisionIncidenceMatrix
              (C := ℚ) frame loopFrame tail head e := by
      funext e q
      simp only [pointedCollisionIncidenceMatrix, Function.comp_apply, map_sub]
      congr <;> split_ifs <;> simp_all
    rw [hC, hD, linearIndependent_algebraMap_comp_iff,
      linearIndependent_algebraMap_comp_iff]

/-- Injective relabelling identifies the occupied nonloop collision supports. -/
noncomputable def pointedCollisionIncidenceSupportEquivOfInjective
    {V Frame Target : Type} [Fintype V] [DecidableEq Frame] [DecidableEq Target]
    (frame : V → Frame) (loopFrame : Frame) (embed : Frame → Target)
    (hinj : Function.Injective embed) :
    pointedCollisionIncidenceSupport frame loopFrame ≃
      pointedCollisionIncidenceSupport (embed ∘ frame) (embed loopFrame) :=
  Equiv.ofBijective
    (fun q => ⟨embed q, by
      have hq := Finset.mem_erase.mp q.property
      refine Finset.mem_erase.mpr ⟨fun h => hq.1 (hinj h), ?_⟩
      obtain ⟨v, _hv, hvq⟩ := Finset.mem_image.mp hq.2
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, by
        simp only [Function.comp_apply]
        rw [hvq]⟩⟩)
    ⟨by
      intro q r hqr
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val hqr,
    by
      intro q
      have hq := Finset.mem_erase.mp q.property
      obtain ⟨v, _hv, hvq⟩ := Finset.mem_image.mp hq.2
      have hvne : frame v ≠ loopFrame := by
        intro hvloop
        apply hq.1
        rw [← hvq, Function.comp_apply, hvloop]
      let r : pointedCollisionIncidenceSupport frame loopFrame :=
        ⟨frame v, Finset.mem_erase.mpr ⟨hvne, Finset.mem_image.mpr
          ⟨v, Finset.mem_univ v, rfl⟩⟩⟩
      refine ⟨r, ?_⟩
      apply Subtype.ext
      exact hvq⟩

/-- Injective relabelling carries every collision-incidence row through the canonical coordinate
reindexing. -/
theorem pointedCollisionIncidenceMatrix_comp_injective_reindex
    {C V E Frame Target : Type} [Field C] [Fintype V]
    [DecidableEq Frame] [DecidableEq Target]
    (frame : V → Frame) (loopFrame : Frame) (embed : Frame → Target)
    (hinj : Function.Injective embed) (tail head : E → V) (edge : E) :
    let e := pointedCollisionIncidenceSupportEquivOfInjective
      frame loopFrame embed hinj
    LinearEquiv.piCongrLeft' C
        (fun _ : pointedCollisionIncidenceSupport frame loopFrame ↦ C) e
        (pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head edge) =
      pointedCollisionIncidenceMatrix
        (C := C) (embed ∘ frame) (embed loopFrame) tail head edge := by
  dsimp only
  let e := pointedCollisionIncidenceSupportEquivOfInjective
    frame loopFrame embed hinj
  funext q
  rw [LinearEquiv.piCongrLeft'_apply]
  have heq := congrArg Subtype.val (e.apply_symm_apply q)
  change embed
      ((e.symm q : pointedCollisionIncidenceSupport frame loopFrame) : Frame) =
    (q : Target) at heq
  have hhead :
      frame (head edge) =
          ((e.symm q : pointedCollisionIncidenceSupport frame loopFrame) : Frame) ↔
        embed (frame (head edge)) = (q : Target) := by
    constructor
    · intro h
      rw [h, heq]
    · intro h
      exact hinj (h.trans heq.symm)
  have htail :
      frame (tail edge) =
          ((e.symm q : pointedCollisionIncidenceSupport frame loopFrame) : Frame) ↔
        embed (frame (tail edge)) = (q : Target) := by
    constructor
    · intro h
      rw [h, heq]
    · intro h
      exact hinj (h.trans heq.symm)
  simp only [pointedCollisionIncidenceMatrix, Function.comp_apply]
  rw [if_congr hhead rfl rfl, if_congr htail rfl rfl]
  rfl

/-- **Injective label-reparametrization law.** Pointed collision incidence depends only on label
equality and the distinguished loop class, not on the chosen injective coordinates for labels. -/
theorem pointedCollisionIncidenceMatroid_comp_injective_eq
    {C V E Frame Target : Type} [Field C] [Fintype V] [Fintype E]
    [DecidableEq E] [DecidableEq Frame] [DecidableEq Target]
    (frame : V → Frame) (loopFrame : Frame) (embed : Frame → Target)
    (hinj : Function.Injective embed) (tail head : E → V) :
    pointedCollisionIncidenceMatroid
        (C := C) (embed ∘ frame) (embed loopFrame) tail head =
      pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head := by
  apply Matroid.ext_indep
  · simp
  · intro I _hI
    rw [pointedCollisionIncidenceMatroid, pointedCollisionIncidenceMatroid,
      linearFamilyMatroid_indep_iff, linearFamilyMatroid_indep_iff]
    let e := pointedCollisionIncidenceSupportEquivOfInjective
      frame loopFrame embed hinj
    let T := LinearEquiv.piCongrLeft' C
      (fun _ : pointedCollisionIncidenceSupport frame loopFrame ↦ C) e
    have hrow (edge : E) :
        T (pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head edge) =
          pointedCollisionIncidenceMatrix
            (C := C) (embed ∘ frame) (embed loopFrame) tail head edge :=
      pointedCollisionIncidenceMatrix_comp_injective_reindex
        frame loopFrame embed hinj tail head edge
    constructor
    · intro hnew
      have hmap := hnew.map' T.symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr T.symm.injective)
      convert! hmap using 1
      funext i
      change pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head i =
        T.symm (pointedCollisionIncidenceMatrix
          (C := C) (embed ∘ frame) (embed loopFrame) tail head i)
      rw [← hrow i]
      exact (T.symm_apply_apply _).symm
    · intro hold
      have hmap := hold.map' T.toLinearMap
        (LinearMap.ker_eq_bot.mpr T.injective)
      convert! hmap using 1
      funext i
      exact (hrow i).symm

/-- Linear forms in a linearly independent finite coordinate family are independent exactly when
their coefficient rows are independent. -/
theorem linearIndependent_matrixLinearForms_iff_rowIndependent
    {C K m n : Type*} [Field C] [CommRing K] [Algebra C K]
    [Fintype m] [Fintype n]
    (M : Matrix m n C) (x : n → K) (hx : LinearIndependent C x) :
    LinearIndependent C (matrixLinearForms M x) ↔
      LinearIndependent C M.row := by
  let L : (n → C) →ₗ[C] K := Fintype.linearCombination C x
  have hcomp : (L ∘ M.row) = matrixLinearForms M x := by
    funext i
    simp [L, matrixLinearForms, Fintype.linearCombination_apply, Algebra.smul_def]
  constructor
  · intro hout
    apply LinearIndependent.of_comp L
    simpa only [hcomp] using hout
  · intro hrows
    have hL : Function.Injective L := hx.fintypeLinearCombination_injective
    have hmap := hrows.map' L (LinearMap.ker_eq_bot.mpr hL)
    simpa only [hcomp] using hmap

/-- Full-ground independence of the pointed collision incidence matroid is exactly linear
independence of its complete incidence-row family. -/
theorem pointedCollisionIncidenceMatroid_univ_indep_iff_linearIndependent
    {C V E Frame : Type} [Field C] [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep Set.univ ↔
      LinearIndependent C
        (pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head) := by
  constructor
  · intro hind
    have hsub := (pointedCollisionIncidenceMatroid_indep_iff
      frame loopFrame tail head Set.univ).1 hind
    exact hsub.comp
      (fun e : E => ⟨e, Set.mem_univ e⟩)
      (fun _ _ hij => congrArg Subtype.val hij)
  · intro hlin
    apply (pointedCollisionIncidenceMatroid_indep_iff
      frame loopFrame tail head Set.univ).2
    exact hlin.comp (fun e : (Set.univ : Set E) => e.1) Subtype.val_injective

/-- One collision-incidence row in the canonical finite real Euclidean coordinate space. -/
noncomputable def pointedCollisionIncidenceEuclideanRow
    {V E Frame : Type} [Fintype V] [Fintype E] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) (e : E) :
    EuclideanSpace ℝ (pointedCollisionIncidenceSupport frame loopFrame) :=
  WithLp.toLp 2
    (pointedCollisionIncidenceMatrix
      (C := ℝ) frame loopFrame tail head e)

/-- The occupied-label coordinate corresponding to one leaf of an injectively labelled rooted
star. -/
def pointedCollisionIncidenceRootedStarCoordinate
    {E Frame : Type} [Fintype E] [DecidableEq Frame]
    (frame : Option E → Frame) (hframe : Function.Injective frame) (i : E) :
    pointedCollisionIncidenceSupport frame (frame none) :=
  ⟨frame (some i), by
    simp [pointedCollisionIncidenceSupport, hframe.eq_iff]⟩

/-- Every canonical incidence row of an injectively labelled rooted star is the corresponding
standard Euclidean basis vector. -/
theorem pointedCollisionIncidenceEuclideanRow_rootedStar_eq_single
    {E Frame : Type} [Fintype E] [DecidableEq Frame]
    (frame : Option E → Frame) (hframe : Function.Injective frame) (i : E) :
    pointedCollisionIncidenceEuclideanRow
        frame (frame none) (fun _ : E => none) some i =
      EuclideanSpace.single
        (pointedCollisionIncidenceRootedStarCoordinate frame hframe i) 1 := by
  apply WithLp.ofLp_injective 2
  funext q
  have hqroot : frame none ≠ (q : Frame) :=
    (Finset.mem_erase.mp q.property).1.symm
  have hhead :
      frame (some i) = (q : Frame) ↔
        q = pointedCollisionIncidenceRootedStarCoordinate frame hframe i := by
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      exact (congrArg Subtype.val h).symm
  simp [pointedCollisionIncidenceEuclideanRow,
    pointedCollisionIncidenceMatrix, hqroot, hhead]

/-- Evaluation of a rooted-star incidence row at its canonical leaf coordinate is the Kronecker
delta. -/
@[simp]
theorem pointedCollisionIncidenceMatrix_rootedStarCoordinate_apply
    {E Frame : Type} [Fintype E] [DecidableEq E] [DecidableEq Frame]
    (frame : Option E → Frame) (hframe : Function.Injective frame)
    (r i : E) :
    pointedCollisionIncidenceMatrix
        (C := ℝ) frame (frame none) (fun _ : E => none) some r
        (pointedCollisionIncidenceRootedStarCoordinate frame hframe i) =
      if r = i then 1 else 0 := by
  simp [pointedCollisionIncidenceMatrix,
    pointedCollisionIncidenceRootedStarCoordinate, hframe.eq_iff]

/-- Injective relabelling carries every canonical Euclidean incidence row through an isometry,
not merely through an abstract linear coordinate equivalence. -/
theorem pointedCollisionIncidenceEuclideanRow_comp_injective_reindex
    {V E Frame Target : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq Target]
    (frame : V → Frame) (loopFrame : Frame) (embed : Frame → Target)
    (hinj : Function.Injective embed) (tail head : E → V) (edge : E) :
    let e := pointedCollisionIncidenceSupportEquivOfInjective
      frame loopFrame embed hinj
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
        (pointedCollisionIncidenceEuclideanRow
          frame loopFrame tail head edge) =
      pointedCollisionIncidenceEuclideanRow
        (embed ∘ frame) (embed loopFrame) tail head edge := by
  dsimp only
  apply WithLp.ofLp_injective 2
  exact pointedCollisionIncidenceMatrix_comp_injective_reindex
    frame loopFrame embed hinj tail head edge

/-- Passing incidence rows through the canonical finite `L²` model preserves and reflects linear
independence. -/
theorem linearIndependent_pointedCollisionIncidenceEuclideanRow_iff
    {V E Frame : Type} [Fintype V] [Fintype E] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    LinearIndependent ℝ
        (pointedCollisionIncidenceEuclideanRow frame loopFrame tail head) ↔
      LinearIndependent ℝ
        (pointedCollisionIncidenceMatrix
          (C := ℝ) frame loopFrame tail head) := by
  let L := WithLp.linearEquiv 2 ℝ
    (pointedCollisionIncidenceSupport frame loopFrame → ℝ)
  constructor
  · intro hrow
    have hmap := hrow.map' L.toLinearMap
      (LinearMap.ker_eq_bot.mpr L.injective)
    simpa [pointedCollisionIncidenceEuclideanRow, L] using! hmap
  · intro hmatrix
    have hmap := hmatrix.map' L.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr L.symm.injective)
    simpa [pointedCollisionIncidenceEuclideanRow, L] using! hmap

/-- Collision kernel for two endpoints: it is one exactly when their labels agree away from the
distinguished loop label. -/
def pointedCollisionIncidenceEndpointKernel
    {V Frame : Type} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (v w : V) : ℝ :=
  ∑ q : pointedCollisionIncidenceSupport frame loopFrame,
    (if frame v = (q : Frame) then 1 else 0) *
      (if frame w = (q : Frame) then 1 else 0)

/-- Closed form of the endpoint-collision kernel. -/
@[simp]
theorem pointedCollisionIncidenceEndpointKernel_eq
    {V Frame : Type} [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (v w : V) :
    pointedCollisionIncidenceEndpointKernel frame loopFrame v w =
      if frame v = frame w ∧ frame v ≠ loopFrame then 1 else 0 := by
  by_cases hv : frame v = loopFrame
  · rw [if_neg (fun h => h.2 hv)]
    simp only [pointedCollisionIncidenceEndpointKernel]
    apply Finset.sum_eq_zero
    intro q _hq
    have hqloop : loopFrame ≠ (q : Frame) :=
      (Finset.mem_erase.mp q.property).1.symm
    simp [hv, hqloop]
  by_cases hvw : frame v = frame w
  · rw [if_pos ⟨hvw, hv⟩]
    let qv : pointedCollisionIncidenceSupport frame loopFrame :=
      ⟨frame v, by simp [pointedCollisionIncidenceSupport, hv]⟩
    rw [pointedCollisionIncidenceEndpointKernel, Fintype.sum_eq_single qv]
    · simp [qv, hvw]
    · intro q hq
      have hqv : frame v ≠ (q : Frame) := by
        intro h
        apply hq
        exact Subtype.ext h.symm
      have hwq : frame w ≠ (q : Frame) := by
        intro h
        exact hqv (hvw.trans h)
      simp [hqv, hwq]
  · rw [if_neg]
    · simp only [pointedCollisionIncidenceEndpointKernel]
      apply Finset.sum_eq_zero
      intro q _hq
      by_cases hvq : frame v = (q : Frame)
      · have hwq : frame w ≠ (q : Frame) := by
          intro hwq
          exact hvw (hvq.trans hwq.symm)
        simp [hvq, hwq]
      · simp [hvq]
    · exact fun h => hvw h.1

/-- Canonical real Hilbert Gram of the complete collision-quotient incidence-row family. Unlike
unisolvent reconstruction, this matrix uses every occupied nonloop label as a fixed coordinate
and involves no chosen sampling packet. -/
noncomputable def pointedCollisionIncidenceGram
    {V E Frame : Type} [Fintype V] [Fintype E] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    Matrix E E ℝ :=
  Matrix.gram ℝ
    (pointedCollisionIncidenceEuclideanRow frame loopFrame tail head)

/-- Every canonical pointed-incidence Gram is positive semidefinite, without any collision,
acyclicity, or reconstruction hypothesis. -/
theorem pointedCollisionIncidenceGram_posSemidef
    {V E Frame : Type} [Fintype V] [Fintype E] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceGram frame loopFrame tail head).PosSemidef := by
  rw [pointedCollisionIncidenceGram]
  exact Matrix.posSemidef_gram ℝ _

/-- Canonical pointed-incidence volume is always nonnegative. -/
theorem pointedCollisionIncidenceGram_det_nonneg
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    0 ≤ (pointedCollisionIncidenceGram frame loopFrame tail head).det :=
  (pointedCollisionIncidenceGram_posSemidef
    frame loopFrame tail head).det_nonneg

/-- **Exact incidence-Gram entry law.** Every metric entry is the signed four-endpoint collision
kernel. This removes the hidden Euclidean coordinate sum and makes the canonical metric purely
combinatorial. -/
theorem pointedCollisionIncidenceGram_apply
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame)
    (tail head : E → V) (e f : E) :
    pointedCollisionIncidenceGram frame loopFrame tail head e f =
      pointedCollisionIncidenceEndpointKernel
          frame loopFrame (head e) (head f) -
        pointedCollisionIncidenceEndpointKernel
          frame loopFrame (head e) (tail f) -
        pointedCollisionIncidenceEndpointKernel
          frame loopFrame (tail e) (head f) +
        pointedCollisionIncidenceEndpointKernel
          frame loopFrame (tail e) (tail f) := by
  rw [pointedCollisionIncidenceGram, Matrix.gram_apply]
  simp only [pointedCollisionIncidenceEuclideanRow,
    EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, pointedCollisionIncidenceMatrix,
    pointedCollisionIncidenceEndpointKernel, star_trivial]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- **Edge-energy trichotomy.** A collision-loop edge has zero canonical energy, a nonloop edge
incident to the distinguished loop has unit energy, and an edge between two distinct nonloop
labels has energy two. -/
theorem pointedCollisionIncidenceGram_apply_self
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame)
    (tail head : E → V) (e : E) :
    pointedCollisionIncidenceGram frame loopFrame tail head e e =
      if frame (head e) = frame (tail e) then 0
      else if frame (head e) = loopFrame ∨ frame (tail e) = loopFrame
      then 1 else 2 := by
  rw [pointedCollisionIncidenceGram_apply]
  simp only [pointedCollisionIncidenceEndpointKernel_eq]
  by_cases heq : frame (head e) = frame (tail e)
  · simp [heq]
  have heq' : frame (tail e) ≠ frame (head e) := fun h => heq h.symm
  by_cases hhead : frame (head e) = loopFrame
  · simp [hhead, eq_comm]
  by_cases htail : frame (tail e) = loopFrame
  · simp [hhead, htail]
  · norm_num [heq, heq', hhead, htail]

/-- A canonical incidence row has zero Hilbert energy exactly when its endpoint labels collide. -/
theorem pointedCollisionIncidenceGram_apply_self_eq_zero_iff
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame)
    (tail head : E → V) (e : E) :
    pointedCollisionIncidenceGram frame loopFrame tail head e e = 0 ↔
      frame (head e) = frame (tail e) := by
  rw [pointedCollisionIncidenceGram_apply_self]
  by_cases heq : frame (head e) = frame (tail e)
  · simp [heq]
  by_cases hloop :
      frame (head e) = loopFrame ∨ frame (tail e) = loopFrame
  · simp [heq, hloop]
  · norm_num [heq, hloop]

/-- Strict positivity of one canonical incidence-row norm needs no global independence
hypothesis: it is exactly endpoint-label separation. -/
theorem pointedCollisionIncidenceGram_apply_self_pos_iff
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame)
    (tail head : E → V) (e : E) :
    0 < pointedCollisionIncidenceGram frame loopFrame tail head e e ↔
      frame (head e) ≠ frame (tail e) := by
  rw [pointedCollisionIncidenceGram_apply_self]
  by_cases heq : frame (head e) = frame (tail e)
  · simp [heq]
  by_cases hloop :
      frame (head e) = loopFrame ∨ frame (tail e) = loopFrame
  · simp [heq, hloop]
  · norm_num [heq, hloop]

/-- **Rooted-star unit-metric law.** The canonical Hilbert incidence metric of every injectively
labelled rooted star is literally the identity matrix. This strengthens independence and positive
definiteness to an exact orthonormal-coordinate description. -/
theorem pointedCollisionIncidenceGram_rootedStar_eq_one_of_injective
    {E Frame : Type} [Fintype E] [DecidableEq E] [DecidableEq Frame]
    (frame : Option E → Frame) (hframe : Function.Injective frame) :
    pointedCollisionIncidenceGram
        frame (frame none) (fun _ : E => none) some =
      (1 : Matrix E E ℝ) := by
  ext i j
  rw [pointedCollisionIncidenceGram, Matrix.gram_apply,
    pointedCollisionIncidenceEuclideanRow_rootedStar_eq_single frame hframe,
    pointedCollisionIncidenceEuclideanRow_rootedStar_eq_single frame hframe,
    EuclideanSpace.inner_single_left]
  simp [Matrix.one_apply, pointedCollisionIncidenceRootedStarCoordinate,
    hframe.eq_iff]

/-- **Exact canonical metric invariance.** Every injective relabelling preserves the complete
incidence Gram entry-for-entry. Thus the canonical Hilbert metric depends only on pointed label
equality, rather than on the ambient label type or chosen coordinates. -/
theorem pointedCollisionIncidenceGram_comp_injective_eq
    {V E Frame Target : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq Target]
    (frame : V → Frame) (loopFrame : Frame) (embed : Frame → Target)
    (hinj : Function.Injective embed) (tail head : E → V) :
    pointedCollisionIncidenceGram
        (embed ∘ frame) (embed loopFrame) tail head =
      pointedCollisionIncidenceGram frame loopFrame tail head := by
  ext i j
  rw [pointedCollisionIncidenceGram, pointedCollisionIncidenceGram,
    Matrix.gram_apply, Matrix.gram_apply]
  let e := pointedCollisionIncidenceSupportEquivOfInjective
    frame loopFrame embed hinj
  let T := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  rw [← pointedCollisionIncidenceEuclideanRow_comp_injective_reindex
      frame loopFrame embed hinj tail head i,
    ← pointedCollisionIncidenceEuclideanRow_comp_injective_reindex
      frame loopFrame embed hinj tail head j]
  exact T.inner_map_map _ _

/-- **Canonical incidence Gram law.** Positive definiteness of the fixed real incidence Gram is
exactly full pointed-incidence independence over every characteristic-zero coefficient field. -/
theorem pointedCollisionIncidenceGram_posDef_iff_univ_indep
    {C V E Frame : Type} [Field C] [CharZero C]
    [Fintype V] [Fintype E] [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceGram frame loopFrame tail head).PosDef ↔
      (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep Set.univ := by
  calc
    _ ↔ LinearIndependent ℝ
        (pointedCollisionIncidenceMatrix
          (C := ℝ) frame loopFrame tail head) := by
      rw [pointedCollisionIncidenceGram,
        Matrix.posDef_gram_iff_linearIndependent,
        linearIndependent_pointedCollisionIncidenceEuclideanRow_iff]
    _ ↔ (pointedCollisionIncidenceMatroid
          (C := ℝ) frame loopFrame tail head).Indep Set.univ :=
      (pointedCollisionIncidenceMatroid_univ_indep_iff_linearIndependent
        frame loopFrame tail head).symm
    _ ↔ _ := by
      rw [pointedCollisionIncidenceMatroid_charZero_eq
        (C := ℝ) (D := C) frame loopFrame tail head]

/-- Positive volume of the canonical incidence Gram is the same exact characteristic-zero
matroid phase; no separate positivity hypothesis is required. -/
theorem pointedCollisionIncidenceGram_det_pos_iff_univ_indep
    {C V E Frame : Type} [Field C] [CharZero C]
    [Fintype V] [Fintype E] [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    0 < (pointedCollisionIncidenceGram frame loopFrame tail head).det ↔
      (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep Set.univ := by
  calc
    _ ↔ (pointedCollisionIncidenceGram frame loopFrame tail head).PosDef := by
      constructor
      · intro hdet
        rw [pointedCollisionIncidenceGram] at hdet ⊢
        exact (Matrix.posSemidef_gram ℝ _).posDef_iff_det_ne_zero.mpr
          (ne_of_gt hdet)
      · exact Matrix.PosDef.det_pos
    _ ↔ _ :=
      pointedCollisionIncidenceGram_posDef_iff_univ_indep
        (C := C) frame loopFrame tail head

/-- **Canonical singular-phase law.** The incidence Gram has zero volume exactly when the full
pointed collision-incidence family is dependent. Nonnegativity is unconditional, so failure of
strict positivity closes to literal determinant zero. -/
theorem pointedCollisionIncidenceGram_det_eq_zero_iff_not_univ_indep
    {C V E Frame : Type} [Field C] [CharZero C]
    [Fintype V] [Fintype E] [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceGram frame loopFrame tail head).det = 0 ↔
      ¬(pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep Set.univ := by
  constructor
  · intro hzero hindep
    have hpos :=
      (pointedCollisionIncidenceGram_det_pos_iff_univ_indep
        (C := C) frame loopFrame tail head).2 hindep
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos).elim
  · intro hnotIndep
    have hnonneg :=
      pointedCollisionIncidenceGram_det_nonneg frame loopFrame tail head
    have hnotPos :
        ¬0 < (pointedCollisionIncidenceGram
          frame loopFrame tail head).det := by
      intro hpos
      exact hnotIndep
        ((pointedCollisionIncidenceGram_det_pos_iff_univ_indep
          (C := C) frame loopFrame tail head).1 hpos)
    exact le_antisymm (le_of_not_gt hnotPos) hnonneg

/-- Distinct occupied-label coordinates and real dual weights that isolate every incidence row
and recover every real edge coefficient vector. -/
def PointedCollisionIncidenceCoordinateReconstruction
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) : Prop :=
  ∃ (nodes : E → pointedCollisionIncidenceSupport frame loopFrame)
      (dual : E → E → ℝ),
    Function.Injective nodes ∧
    (∀ q r, ∑ i, dual q i *
      pointedCollisionIncidenceMatrix
        (C := ℝ) frame loopFrame tail head r (nodes i) =
        if q = r then 1 else 0) ∧
    ∀ (a : E → ℝ) q,
      ∑ i, dual q i *
        (∑ r, a r * pointedCollisionIncidenceMatrix
          (C := ℝ) frame loopFrame tail head r (nodes i)) = a q

/-- **Canonical rooted-star reconstruction.** Injective rooted-star labels discharge the
existential unisolvent interface with the canonical occupied leaf coordinates and identity dual
weights. No basis selection or abstract inverse is needed. -/
theorem pointedCollisionIncidenceCoordinateReconstruction_rootedStar_of_injective
    {E Frame : Type} [Fintype E] [DecidableEq E] [DecidableEq Frame]
    (frame : Option E → Frame) (hframe : Function.Injective frame) :
    PointedCollisionIncidenceCoordinateReconstruction
      frame (frame none) (fun _ : E => none) some := by
  refine ⟨
    pointedCollisionIncidenceRootedStarCoordinate frame hframe,
    (fun q i => if q = i then 1 else 0), ?_, ?_, ?_⟩
  · intro i j hij
    apply Option.some.inj
    apply hframe
    exact congrArg Subtype.val hij
  · intro q r
    simp
  · intro a q
    simp

/-- **Pointed-incidence unisolvent reconstruction law.** Full collision-incidence independence
is equivalent to a square packet of distinct occupied-label coordinates with exact real dual
isolation and coefficient recovery. No coordinate packet or dual certificate is assumed. -/
theorem pointedCollisionIncidenceMatroid_univ_indep_iff_coordinateReconstruction
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceMatroid
        (C := ℝ) frame loopFrame tail head).Indep Set.univ ↔
      PointedCollisionIncidenceCoordinateReconstruction
        frame loopFrame tail head := by
  constructor
  · intro hind
    have hlinear :=
      (pointedCollisionIncidenceMatroid_univ_indep_iff_linearIndependent
        frame loopFrame tail head).1 hind
    exact GaloisForLFunctions.HilbertMetric.exists_injective_nodes_dual_reconstruction
      (pointedCollisionIncidenceMatrix
        (C := ℝ) frame loopFrame tail head) hlinear
  · rintro ⟨nodes, dual, _hnodes, _hdelta, hrecovery⟩
    apply (pointedCollisionIncidenceMatroid_univ_indep_iff_linearIndependent
      frame loopFrame tail head).2
    rw [Fintype.linearIndependent_iff]
    intro a ha q
    rw [← hrecovery a q]
    apply Finset.sum_eq_zero
    intro i _hi
    have hai := congrFun ha (nodes i)
    have hinner :
        ∑ r, a r * pointedCollisionIncidenceMatrix
          (C := ℝ) frame loopFrame tail head r (nodes i) = 0 := by
      simpa [Finset.sum_apply, Pi.smul_apply] using hai
    rw [hinner, mul_zero]

/-- Fixed canonical incidence-Gram positivity and existential unisolvent coordinate recovery are
equivalent manifestations of the same Hilbert phase. -/
theorem pointedCollisionIncidenceGram_posDef_iff_coordinateReconstruction
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    (pointedCollisionIncidenceGram frame loopFrame tail head).PosDef ↔
      PointedCollisionIncidenceCoordinateReconstruction
        frame loopFrame tail head := by
  calc
    _ ↔ (pointedCollisionIncidenceMatroid
          (C := ℝ) frame loopFrame tail head).Indep Set.univ :=
      pointedCollisionIncidenceGram_posDef_iff_univ_indep
        (C := ℝ) frame loopFrame tail head
    _ ↔ _ :=
      pointedCollisionIncidenceMatroid_univ_indep_iff_coordinateReconstruction
        frame loopFrame tail head

/-- Exact coordinate reconstruction is equivalent to absence of a nonzero real circulation in
the complete collision-quotient incidence family. -/
theorem pointedCollisionIncidenceCoordinateReconstruction_iff_no_nonzeroCirculation
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    PointedCollisionIncidenceCoordinateReconstruction frame loopFrame tail head ↔
      ∀ weight : E → ℝ,
        IsPointedCollisionIncidenceCirculation
            frame loopFrame tail head id weight →
          ∀ e, weight e = 0 := by
  rw [← pointedCollisionIncidenceMatroid_univ_indep_iff_coordinateReconstruction,
    pointedCollisionIncidenceMatroid_univ_indep_iff_linearIndependent,
    Fintype.linearIndependent_iff]
  simp only [IsPointedCollisionIncidenceCirculation, funext_iff, Pi.zero_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id_eq]

/-- **Unisolvent/Kirchhoff duality.** Distinct occupied-label coordinates with exact dual
recovery exist exactly when every real flow conserved at every vertex of the collapsed pointed
quotient is zero. This discharges both the coordinate certificate and the missing loop equation. -/
theorem pointedCollisionIncidenceCoordinateReconstruction_iff_vertexConservation
    {V E Frame : Type} [Fintype V] [Fintype E]
    [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V) :
    PointedCollisionIncidenceCoordinateReconstruction frame loopFrame tail head ↔
      ∀ weight : E → ℝ,
        (∀ q : pointedCollisionIncidenceVertex frame loopFrame,
          (∑ e, if pointedCollisionIncidenceVertexOf frame loopFrame
              (head e) = q then weight e else 0) =
            ∑ e, if pointedCollisionIncidenceVertexOf frame loopFrame
              (tail e) = q then weight e else 0) →
          ∀ e, weight e = 0 := by
  constructor
  · intro hrec weight hconservation
    apply (pointedCollisionIncidenceCoordinateReconstruction_iff_no_nonzeroCirculation
      frame loopFrame tail head).1 hrec weight
    apply (isPointedCollisionIncidenceCirculation_iff_vertex_conservation
      frame loopFrame tail head id weight).2
    simpa using! hconservation
  · intro hconservation
    apply (pointedCollisionIncidenceCoordinateReconstruction_iff_no_nonzeroCirculation
      frame loopFrame tail head).2
    intro weight hcirculation
    apply hconservation weight
    have hvertex :=
      (isPointedCollisionIncidenceCirculation_iff_vertex_conservation
        frame loopFrame tail head id weight).1 hcirculation
    simpa using! hvertex

/-- Collision-quotient incidence linear forms remain literal endpoint-label differences when the
target is only a commutative coefficient algebra, including function rings. -/
theorem matrixLinearForms_pointedCollisionIncidenceMatrix_commRing
    {C K V E Frame : Type} [Field C] [CommRing K] [Algebra C K]
    [Fintype V] [DecidableEq Frame]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (x : Frame → K) (hx : x loopFrame = 0) :
    matrixLinearForms
        (pointedCollisionIncidenceMatrix (C := C) frame loopFrame tail head)
        (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q) =
      fun e ↦ x (frame (head e)) - x (frame (tail e)) := by
  funext e
  have hsum (v0 : V) :
      ∑ q : pointedCollisionIncidenceSupport frame loopFrame,
        algebraMap C K (if frame v0 = (q : Frame) then 1 else 0) * x q =
          x (frame v0) := by
    by_cases hv0 : frame v0 = loopFrame
    · rw [hv0, hx]
      apply Finset.sum_eq_zero
      intro q _
      have hq : (q : Frame) ≠ loopFrame :=
        (Finset.mem_erase.mp q.property).1
      simp [hq.symm]
    · let q' : pointedCollisionIncidenceSupport frame loopFrame :=
        ⟨frame v0, by simp [pointedCollisionIncidenceSupport, hv0]⟩
      calc
        (∑ q : pointedCollisionIncidenceSupport frame loopFrame,
            algebraMap C K (if frame v0 = (q : Frame) then 1 else 0) * x q) =
            algebraMap C K (if frame v0 = (q' : Frame) then 1 else 0) * x q' := by
          apply Fintype.sum_eq_single q'
          intro q hq
          have hne : frame v0 ≠ (q : Frame) := by
            intro h
            exact hq (Subtype.ext h.symm)
          simp [hne]
        _ = x (frame v0) := by simp [q']
  simp only [matrixLinearForms, pointedCollisionIncidenceMatrix, map_sub,
    sub_mul, Finset.sum_sub_distrib]
  rw [hsum, hsum]

/-- **Linear pointed-collision incidence law.** Pairwise differences of a labelled family whose
occupied nonloop label values are linearly independent represent the complete collision-quotient
incidence matroid, with repeated and loop labels requiring no extra hypotheses. -/
theorem linearIndependent_gradedPairwiseDifferences_iff_pointedCollisionIncidence
    {C K V E Frame : Type} [Field C] [CommRing K] [Algebra C K]
    [Fintype V] [Fintype E] [DecidableEq Frame] [DecidableEq E]
    (frame : V → Frame) (loopFrame : Frame) (tail head : E → V)
    (x : Frame → K) (hx0 : x loopFrame = 0)
    (hx : LinearIndependent C
      (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q)) :
    LinearIndependent C
        (fun e ↦ x (frame (head e)) - x (frame (tail e))) ↔
      (pointedCollisionIncidenceMatroid
        (C := C) frame loopFrame tail head).Indep Set.univ := by
  rw [← matrixLinearForms_pointedCollisionIncidenceMatrix_commRing
    (C := C) frame loopFrame tail head x hx0]
  calc
    LinearIndependent C
        (matrixLinearForms
          (pointedCollisionIncidenceMatrix
            (C := C) frame loopFrame tail head)
          (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q)) ↔
      LinearIndependent C
        (pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head) :=
      linearIndependent_matrixLinearForms_iff_rowIndependent
        (pointedCollisionIncidenceMatrix
          (C := C) frame loopFrame tail head)
        (fun q : pointedCollisionIncidenceSupport frame loopFrame ↦ x q) hx
    _ ↔ _ :=
      (pointedCollisionIncidenceMatroid_univ_indep_iff_linearIndependent
        frame loopFrame tail head).symm

end GaloisForLFunctions.HTGeometry
