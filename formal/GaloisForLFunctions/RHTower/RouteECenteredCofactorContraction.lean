import GaloisForLFunctions.RHTower.RouteEFinitePhysicalCodiagonalGaugeCollapse
import GaloisForLFunctions.HTGeometry.FiniteDiagonalOperator

/-!
# Route E centered-cofactor contraction

The finite Route E codiagonal decomposition leaves one concrete interface: a physical sharp
cofactor must become a source-predeclared contraction before the Fisher one-corner estimate can
be used. This module closes that interface for every finite probability law and every real
cofactor in `[0, 1]`.

The source has coordinate `sqrt w_s`. Subtracting the physical cofactor mean keeps every
coordinate multiplier in `[-1, 1]`, hence gives a canonical diagonal contraction. Its pairing
with the weighted marker source is exactly the centered codiagonal score.

This is not an endpoint estimate: identifying an actual Ramaré sharp cofactor with a Fisher
one-corner reporter, and transporting it through the zero/one-large-prime recurrence seam,
remain arithmetic obligations.
-/

open Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Square-root coordinate realization of a finite physical mass law. -/
def routeEFiniteCodiagonalSource (w : Ω → ℝ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 fun s => (Real.sqrt (w s) : ℂ)

/-- Weighted marker vector whose Hermitian pairing retains the marker phase. -/
def routeEFiniteCodiagonalMarker (w : Ω → ℝ) (d : Ω → ℂ) : EuclideanSpace ℂ Ω :=
  WithLp.toLp 2 fun s => d s * (Real.sqrt (w s) : ℂ)

/-- Canonical source-defined multiplier for a real physical cofactor after centering. -/
def routeEFiniteCenteredCofactorContraction
    (w G : Ω → ℝ) : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω :=
  euclideanDiagOp fun s => routeEFiniteCenteredCofactor w (fun t => (G t : ℂ)) s

omit [DecidableEq Ω] in
/-- A normalized nonnegative physical mass law gives a unit square-root source. -/
theorem routeEFiniteCodiagonalSource_norm_sq
    (w : Ω → ℝ) (hw : ∑ s, w s = 1) (hw0 : ∀ s, 0 ≤ w s) :
    ‖routeEFiniteCodiagonalSource w‖ ^ 2 = 1 := by
  rw [routeEFiniteCodiagonalSource, PiLp.norm_sq_eq_of_L2]
  calc
    (∑ i, ‖((Real.sqrt (w i) : ℂ))‖ ^ 2) = ∑ i, w i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (hw0 i)]
    _ = 1 := hw

omit [DecidableEq Ω] in
private theorem routeEFinite_realDiagonal_source_marker_pairing
    (w : Ω → ℝ) (A : Ω → ℝ) (d : Ω → ℂ) (hw0 : ∀ s, 0 ≤ w s) :
    inner ℂ (euclideanDiagOp (fun s => (A s : ℂ)) (routeEFiniteCodiagonalSource w))
      (routeEFiniteCodiagonalMarker w d) =
      ∑ s, (w s : ℂ) * (A s : ℂ) * d s := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [diagOp_apply]
  simp only [routeEFiniteCodiagonalSource, routeEFiniteCodiagonalMarker,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have hsqrt : (Real.sqrt (w s) : ℂ) * (Real.sqrt (w s) : ℂ) = (w s : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (hw0 s)
  calc
    d s * (Real.sqrt (w s) : ℂ) * ((A s : ℂ) * (Real.sqrt (w s) : ℂ)) =
        ((Real.sqrt (w s) : ℂ) * (Real.sqrt (w s) : ℂ)) * (A s : ℂ) * d s := by ring
    _ = (w s : ℂ) * (A s : ℂ) * d s := by rw [hsqrt]

omit [DecidableEq Ω] in
private theorem routeEFinite_centeredCofactor_abs_le_one
    (w G : Ω → ℝ) (hw0 : ∀ s, 0 ≤ w s) (hw : ∑ s, w s = 1)
    (hG0 : ∀ s, 0 ≤ G s) (hG1 : ∀ s, G s ≤ 1) (s : Ω) :
    ‖routeEFiniteCenteredCofactor w (fun t => (G t : ℂ)) s‖ ≤ 1 := by
  have hmean0 : 0 ≤ ∑ t, w t * G t := by
    exact Finset.sum_nonneg fun t _ => mul_nonneg (hw0 t) (hG0 t)
  have hmean1 : (∑ t, w t * G t) ≤ 1 := by
    calc
      (∑ t, w t * G t) ≤ ∑ t, w t * 1 := by
        apply Finset.sum_le_sum
        intro t _ht
        exact mul_le_mul_of_nonneg_left (hG1 t) (hw0 t)
      _ = 1 := by simpa using hw
  have hmeanC : (∑ t, (w t : ℂ) * (G t : ℂ)) =
      ((∑ t, w t * G t : ℝ) : ℂ) := by
    calc
      (∑ t, (w t : ℂ) * (G t : ℂ)) = ∑ t, ((w t * G t : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro t _ht
        push_cast
        ring
      _ = ((∑ t, w t * G t : ℝ) : ℂ) := by rw [Complex.ofReal_sum]
  unfold routeEFiniteCenteredCofactor routeEFiniteCodiagonalMean
  rw [hmeanC, ← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hG0 s, hmean1], by linarith [hG1 s, hmean0]⟩

omit [DecidableEq Ω] in
/-- A centered `[0,1]` cofactor is a canonical norm-`≤ 1` source contraction. -/
theorem norm_routeEFiniteCenteredCofactorContraction_le_one
    (w G : Ω → ℝ) (hw0 : ∀ s, 0 ≤ w s) (hw : ∑ s, w s = 1)
    (hG0 : ∀ s, 0 ≤ G s) (hG1 : ∀ s, G s ≤ 1) :
    ‖routeEFiniteCenteredCofactorContraction w G‖ ≤ 1 := by
  have huniv : (Finset.univ : Finset Ω).Nonempty := by
    by_contra h
    have hempty : (Finset.univ : Finset Ω) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    rw [hempty] at hw
    norm_num at hw
  letI : Nonempty Ω := ⟨huniv.choose⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hmax : diagMax (fun s => routeEFiniteCenteredCofactor w (fun t => (G t : ℂ)) s) ≤ 1 := by
    exact Finset.sup'_le Finset.univ_nonempty _ (fun s _ =>
      routeEFinite_centeredCofactor_abs_le_one w G hw0 hw hG0 hG1 s)
  calc
    ‖routeEFiniteCenteredCofactorContraction w G x‖ ≤
        diagMax (fun s => routeEFiniteCenteredCofactor w (fun t => (G t : ℂ)) s) * ‖x‖ :=
      norm_diagOp_le _ x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hmax (norm_nonneg _)

omit [DecidableEq Ω] in
/-- The canonical contraction paired with the marker source is exactly the centered physical
codiagonal score. -/
theorem routeEFiniteCenteredCofactorContraction_score
    (w G : Ω → ℝ) (d : Ω → ℂ) (hw0 : ∀ s, 0 ≤ w s) :
    inner ℂ (routeEFiniteCenteredCofactorContraction w G (routeEFiniteCodiagonalSource w))
      (routeEFiniteCodiagonalMarker w d) =
      routeEFiniteCodiagonalScore w (routeEFiniteCenteredCofactor w (fun t => (G t : ℂ))) d := by
  have hmeanC : (∑ t, (w t : ℂ) * (G t : ℂ)) =
      ((∑ t, w t * G t : ℝ) : ℂ) := by
    calc
      (∑ t, (w t : ℂ) * (G t : ℂ)) = ∑ t, ((w t * G t : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro t _ht
        push_cast
        ring
      _ = ((∑ t, w t * G t : ℝ) : ℂ) := by rw [Complex.ofReal_sum]
  have hsymbol :
      (fun s => routeEFiniteCenteredCofactor w (fun t => (G t : ℂ)) s) =
        fun s => ((G s - ∑ t, w t * G t : ℝ) : ℂ) := by
    funext s
    unfold routeEFiniteCenteredCofactor routeEFiniteCodiagonalMean
    rw [hmeanC]
    exact (Complex.ofReal_sub _ _).symm
  rw [routeEFiniteCenteredCofactorContraction, hsymbol,
    routeEFinite_realDiagonal_source_marker_pairing w (fun s => G s - ∑ t, w t * G t) d hw0]
  unfold routeEFiniteCodiagonalScore routeEFiniteCenteredCofactor routeEFiniteCodiagonalMean
  rw [hmeanC]
  apply Finset.sum_congr rfl
  intro s _hs
  push_cast
  ring

omit [DecidableEq Ω] in
/-- The centered cofactor contraction is an explicit certificate, not an existential choice. -/
theorem routeEFiniteCenteredCofactorContraction_certificate
    (w G : Ω → ℝ) (d : Ω → ℂ) (hw0 : ∀ s, 0 ≤ w s) (hw : ∑ s, w s = 1)
    (hG0 : ∀ s, 0 ≤ G s) (hG1 : ∀ s, G s ≤ 1) :
    ‖routeEFiniteCenteredCofactorContraction w G‖ ≤ 1 ∧
      inner ℂ (routeEFiniteCenteredCofactorContraction w G (routeEFiniteCodiagonalSource w))
        (routeEFiniteCodiagonalMarker w d) =
        routeEFiniteCodiagonalScore w
          (routeEFiniteCenteredCofactor w (fun t => (G t : ℂ))) d := by
  exact ⟨norm_routeEFiniteCenteredCofactorContraction_le_one w G hw0 hw hG0 hG1,
    routeEFiniteCenteredCofactorContraction_score w G d hw0⟩

end RHTower
