import GaloisForLFunctions.HTGeometry.ComplexOpenUnitBallLoop
import GaloisForLFunctions.HTGeometry.ComplexUnitsGeneratorPath
import GaloisForLFunctions.HTGeometry.CriticalSourceAnalyticProjectionCoordinates
import GaloisForLFunctions.HTGeometry.CriticalSourceMeridianAssignments
import GaloisForLFunctions.HTGeometry.TopologicalGroupTranslatedLoop

namespace GaloisForLFunctions.HTGeometry

open Path MvPolynomial

noncomputable section

set_option maxHeartbeats 1000000

noncomputable def criticalMeridianScale : ℂ :=
  Classical.choose
    (exists_scale_mul_complexUnitsPath_norm_lt_one complexUnitsFundamentalGeneratorPath)

theorem criticalMeridianScale_ne_zero : criticalMeridianScale ≠ 0 :=
  (Classical.choose_spec
    (exists_scale_mul_complexUnitsPath_norm_lt_one
      complexUnitsFundamentalGeneratorPath)).1

theorem criticalMeridianScale_norm_lt_one (t : unitInterval) :
    ‖criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ)‖ < 1 :=
  (Classical.choose_spec
    (exists_scale_mul_complexUnitsPath_norm_lt_one
      complexUnitsFundamentalGeneratorPath)).2 t

noncomputable def criticalMeridianScaleUnit : Units ℂ :=
  Units.mk0 criticalMeridianScale criticalMeridianScale_ne_zero

def criticalMeridianScaledGeneratorPath :
    Path criticalMeridianScaleUnit criticalMeridianScaleUnit :=
  translatedLoopPath criticalMeridianScaleUnit complexUnitsFundamentalGeneratorPath

def criticalMeridianUnitBallBase : ComplexOpenUnitBall :=
  ⟨criticalMeridianScale, by
    have h := criticalMeridianScale_norm_lt_one (0 : unitInterval)
    simpa [Metric.mem_ball, dist_zero_right] using h⟩

def criticalMeridianUnitBallPath :
    Path criticalMeridianUnitBallBase criticalMeridianUnitBallBase where
  toFun t := ⟨criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ), by
    simpa [Metric.mem_ball, dist_zero_right] using criticalMeridianScale_norm_lt_one t⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop
  source' := by
    apply Subtype.ext
    simp [criticalMeridianUnitBallBase]
  target' := by
    apply Subtype.ext
    simp [criticalMeridianUnitBallBase]

variable (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

def criticalFirstMeridianAwayBase :
    {v : Fin (m + n) → ℂ //
      MvPolynomial.eval v (criticalSourceChartPoly ℂ m n) ≠ 0} :=
  ⟨criticalFirstMeridianRaw criticalMeridianScale,
    criticalFirstMeridianRaw_chartPoly_ne_zero criticalMeridianScale_ne_zero
      (by simpa using criticalMeridianScale_norm_lt_one (0 : unitInterval))⟩

def criticalSecondMeridianAwayBase :
    {v : Fin (m + n) → ℂ //
      MvPolynomial.eval v (criticalSourceChartPoly ℂ m n) ≠ 0} :=
  ⟨criticalSecondMeridianRaw criticalMeridianScale,
    criticalSecondMeridianRaw_chartPoly_ne_zero criticalMeridianScale_ne_zero
      (by simpa using criticalMeridianScale_norm_lt_one (0 : unitInterval))⟩

def criticalFirstMeridianAwayPath :
    Path (criticalFirstMeridianAwayBase m n) (criticalFirstMeridianAwayBase m n) where
  toFun t :=
    ⟨criticalFirstMeridianRaw
        (criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ)),
      criticalFirstMeridianRaw_chartPoly_ne_zero
        (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
        (criticalMeridianScale_norm_lt_one t)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_criticalFirstMeridianRaw.comp (by fun_prop)
  source' := by
    apply Subtype.ext
    funext i
    simp [criticalFirstMeridianAwayBase]
  target' := by
    apply Subtype.ext
    funext i
    simp [criticalFirstMeridianAwayBase]

def criticalSecondMeridianAwayPath :
    Path (criticalSecondMeridianAwayBase m n) (criticalSecondMeridianAwayBase m n) where
  toFun t :=
    ⟨criticalSecondMeridianRaw
        (criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ)),
      criticalSecondMeridianRaw_chartPoly_ne_zero
        (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
        (criticalMeridianScale_norm_lt_one t)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_criticalSecondMeridianRaw.comp (by fun_prop)
  source' := by
    apply Subtype.ext
    funext i
    simp [criticalSecondMeridianAwayBase]
  target' := by
    apply Subtype.ext
    funext i
    simp [criticalSecondMeridianAwayBase]

def criticalFirstSourceLocalMeridian :
    Path
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianAwayBase m n).2)
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianAwayBase m n).2) :=
  (criticalFirstMeridianAwayPath m n).map
    (AlgSpec.continuous_awayAlgPoint (criticalSourceChartPoly ℂ m n))

def criticalSecondSourceLocalMeridian :
    Path
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalSecondMeridianAwayBase m n).2)
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalSecondMeridianAwayBase m n).2) :=
  (criticalSecondMeridianAwayPath m n).map
    (AlgSpec.continuous_awayAlgPoint (criticalSourceChartPoly ℂ m n))

def criticalFirstProjectedMeridian :
    Path
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalFirstMeridianAwayBase m n).2))
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalFirstMeridianAwayBase m n).2)) :=
  (criticalFirstSourceLocalMeridian m n).map
    (criticalSourceAnalyticProjectionContinuousMap
      (m := m) (n := n)).continuous

def criticalSecondProjectedMeridian :
    Path
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalSecondMeridianAwayBase m n).2))
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalSecondMeridianAwayBase m n).2)) :=
  (criticalSecondSourceLocalMeridian m n).map
    (criticalSourceAnalyticProjectionContinuousMap
      (m := m) (n := n)).continuous

theorem criticalFirstProjectedMeridian_base_first :
    (criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianAwayBase m n).2)).1 =
      criticalMeridianScaleUnit := by
  apply Units.ext
  rw [criticalSourceAnalyticProjection_awayAlgPoint_first_val]
  exact criticalFirstMeridianRaw_marked (m := m) (n := n) criticalMeridianScale

theorem criticalSecondProjectedMeridian_base_second :
    (criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalSecondMeridianAwayBase m n).2)).2.1 =
      criticalMeridianScaleUnit := by
  apply Units.ext
  rw [criticalSourceAnalyticProjection_awayAlgPoint_second_val]
  · exact criticalSecondMeridianRaw_reciprocal
      (m := m) (n := n) criticalMeridianScale
  · exact criticalSecondMeridianRaw_zero
      (m := m) (n := n) criticalMeridianScale

theorem criticalFirstProjectedMeridian_first :
    (criticalFirstProjectedMeridian m n).map ContinuousMap.fst.continuous =
      criticalMeridianScaledGeneratorPath.cast
        (criticalFirstProjectedMeridian_base_first m n)
        (criticalFirstProjectedMeridian_base_first m n) := by
  apply Path.ext
  funext t
  apply Units.ext
  change
    ((criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianRaw_chartPoly_ne_zero
          (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
          (criticalMeridianScale_norm_lt_one t)))).1 : ℂ) = _
  rw [criticalSourceAnalyticProjection_awayAlgPoint_first_val]
  exact criticalFirstMeridianRaw_marked (m := m) (n := n)
    (criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ))

theorem criticalSecondProjectedMeridian_second :
    ((criticalSecondProjectedMeridian m n).map ContinuousMap.snd.continuous).map
        ContinuousMap.fst.continuous =
      criticalMeridianScaledGeneratorPath.cast
        (criticalSecondProjectedMeridian_base_second m n)
        (criticalSecondProjectedMeridian_base_second m n) := by
  apply Path.ext
  funext t
  apply Units.ext
  change
    ((criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalSecondMeridianRaw_chartPoly_ne_zero
          (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
          (criticalMeridianScale_norm_lt_one t)))).2.1 : ℂ) = _
  rw [criticalSourceAnalyticProjection_awayAlgPoint_second_val]
  · exact criticalSecondMeridianRaw_reciprocal (m := m) (n := n)
      (criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ))
  · exact criticalSecondMeridianRaw_zero (m := m) (n := n)
      (criticalMeridianScale * (complexUnitsFundamentalGeneratorPath t : ℂ))

private theorem pathQuotient_mk_eq_refl_of_eq_cast
    {X : Type*} [TopologicalSpace X] {x y : X}
    (hxy : x = y) {p : Path x x} {q : Path y y}
    (hp : p = q.cast hxy hxy)
    (hq : Path.Homotopic.Quotient.mk q =
      Path.Homotopic.Quotient.mk (Path.refl y)) :
    Path.Homotopic.Quotient.mk p =
      Path.Homotopic.Quotient.mk (Path.refl x) := by
  subst y
  simpa using hp ▸ hq

@[simp] theorem complexOpenUnitBallSubtractionMap_coe
    (c : ℂ) (hc : ‖c‖ = 1) (z : ComplexOpenUnitBall) :
    ((complexOpenUnitBallSubtractionMap c hc z : Units ℂ) : ℂ) = c - z.1 := by
  have h := (unitsHomeomorphNeZero (G₀ := ℂ)).apply_symm_apply
    (⟨c - z.1, by
      intro hzero
      have heq : c = z.1 := sub_eq_zero.mp hzero
      have hzdist : dist z.1 0 < 1 := z.2
      have hz : ‖z.1‖ < 1 := by
        simpa [dist_zero_right] using hzdist
      rw [← heq, hc] at hz
      exact (lt_self_iff_false 1).mp hz⟩ : {w : ℂ // w ≠ 0})
  exact congrArg Subtype.val h

theorem criticalFirstProjectedMeridian_base_second_of_eq (h : n = m) :
    ContinuousMap.fst (ContinuousMap.snd
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalFirstMeridianAwayBase m n).2))) =
      complexOpenUnitBallSubtractionMap ((-1 : ℂ) ^ m) (by simp)
        criticalMeridianUnitBallBase := by
  subst n
  apply Units.ext
  change
    ((criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m m)
        (criticalFirstMeridianAwayBase m m).2)).2.1 : ℂ) = _
  rw [criticalSourceAnalyticProjection_awayAlgPoint_second_val]
  · change MvPolynomial.eval
      (criticalFirstMeridianRaw (m := m) (n := m) criticalMeridianScale)
        (criticalReciprocalNumerator ℂ (m + m) m) = _
    rw [criticalFirstMeridianRaw_reciprocal]
    simp [criticalMeridianUnitBallBase]
  · exact criticalFirstMeridianRaw_zero (m := m) (n := m) criticalMeridianScale

theorem criticalSecondProjectedMeridian_base_first_of_eq (h : n = m) :
    ContinuousMap.fst
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalSecondMeridianAwayBase m n).2)) =
      complexOpenUnitBallSubtractionMap ((-1 : ℂ) ^ m) (by simp)
        criticalMeridianUnitBallBase := by
  subst n
  apply Units.ext
  change
    ((criticalSourceAnalyticProjection
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m m)
        (criticalSecondMeridianAwayBase m m).2)).1 : ℂ) = _
  rw [criticalSourceAnalyticProjection_awayAlgPoint_first_val]
  change criticalSecondMeridianRaw (m := m) (n := m) criticalMeridianScale
    criticalRawMarkedIndex = _
  rw [criticalSecondMeridianRaw_marked]
  simp [criticalMeridianUnitBallBase]

theorem criticalFirstProjectedMeridian_second_mk_eq_refl :
    Path.Homotopic.Quotient.mk
        (((criticalFirstProjectedMeridian m n).map
          ContinuousMap.snd.continuous).map ContinuousMap.fst.continuous) =
      Path.Homotopic.Quotient.mk
        (Path.refl
          (ContinuousMap.fst (ContinuousMap.snd
            (criticalSourceAnalyticProjection
              (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
                (criticalFirstMeridianAwayBase m n).2))))) := by
  by_cases hnm : n = m
  · subst n
    let f := complexOpenUnitBallSubtractionMap ((-1 : ℂ) ^ m) (by simp)
    let q := criticalMeridianUnitBallPath.map f.continuous
    let hbase := criticalFirstProjectedMeridian_base_second_of_eq
      (m := m) (n := m) rfl
    apply pathQuotient_mk_eq_refl_of_eq_cast hbase (q := q)
    · apply Path.ext
      funext t
      apply Units.ext
      change
        ((criticalSourceAnalyticProjection
          (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m m)
            (criticalFirstMeridianRaw_chartPoly_ne_zero
              (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
              (criticalMeridianScale_norm_lt_one t)))).2.1 : ℂ) = _
      rw [criticalSourceAnalyticProjection_awayAlgPoint_second_val]
      · rw [criticalFirstMeridianRaw_reciprocal]
        have hqval : ((q.cast hbase hbase t : Units ℂ) : ℂ) =
            (-1 : ℂ) ^ m - criticalMeridianScale *
              (complexUnitsFundamentalGeneratorPath t : ℂ) := by
          change ((f (criticalMeridianUnitBallPath t) : Units ℂ) : ℂ) = _
          simp [f, criticalMeridianUnitBallPath]
        rw [hqval]
        simp
      · exact criticalFirstMeridianRaw_zero (m := m) (n := m)
          (criticalMeridianScale *
            (complexUnitsFundamentalGeneratorPath t : ℂ))
    · exact complexOpenUnitBallSubtractionLoop_mk_eq_refl
        ((-1 : ℂ) ^ m) (by simp) criticalMeridianUnitBallPath
  · apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    apply Units.ext
    change
      ((criticalSourceAnalyticProjection
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalFirstMeridianRaw_chartPoly_ne_zero
            (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
            (criticalMeridianScale_norm_lt_one t)))).2.1 : ℂ) =
        ((criticalSourceAnalyticProjection
          (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
            (criticalFirstMeridianAwayBase m n).2)).2.1 : ℂ)
    rw [criticalSourceAnalyticProjection_awayAlgPoint_second_val,
      criticalSourceAnalyticProjection_awayAlgPoint_second_val]
    · change MvPolynomial.eval
          (criticalFirstMeridianRaw (m := m) (n := n)
            (criticalMeridianScale *
              (complexUnitsFundamentalGeneratorPath t : ℂ)))
          (criticalReciprocalNumerator ℂ (m + n) n) =
        MvPolynomial.eval
          (criticalFirstMeridianRaw (m := m) (n := n) criticalMeridianScale)
          (criticalReciprocalNumerator ℂ (m + n) n)
      rw [criticalFirstMeridianRaw_reciprocal,
        criticalFirstMeridianRaw_reciprocal]
      simp [hnm]
    · exact criticalFirstMeridianRaw_zero (m := m) (n := n)
        criticalMeridianScale
    · exact criticalFirstMeridianRaw_zero (m := m) (n := n)
        (criticalMeridianScale *
          (complexUnitsFundamentalGeneratorPath t : ℂ))

theorem criticalSecondProjectedMeridian_first_mk_eq_refl :
    Path.Homotopic.Quotient.mk
        ((criticalSecondProjectedMeridian m n).map
          ContinuousMap.fst.continuous) =
      Path.Homotopic.Quotient.mk
        (Path.refl
          (ContinuousMap.fst
            (criticalSourceAnalyticProjection
              (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
                (criticalSecondMeridianAwayBase m n).2)))) := by
  by_cases hnm : n = m
  · subst n
    let f := complexOpenUnitBallSubtractionMap ((-1 : ℂ) ^ m) (by simp)
    let q := criticalMeridianUnitBallPath.map f.continuous
    let hbase := criticalSecondProjectedMeridian_base_first_of_eq
      (m := m) (n := m) rfl
    apply pathQuotient_mk_eq_refl_of_eq_cast hbase (q := q)
    · apply Path.ext
      funext t
      apply Units.ext
      change
        ((criticalSourceAnalyticProjection
          (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m m)
            (criticalSecondMeridianRaw_chartPoly_ne_zero
              (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
            (criticalMeridianScale_norm_lt_one t)))).1 : ℂ) = _
      rw [criticalSourceAnalyticProjection_awayAlgPoint_first_val]
      have hqval : ((q.cast hbase hbase t : Units ℂ) : ℂ) =
          (-1 : ℂ) ^ m - criticalMeridianScale *
            (complexUnitsFundamentalGeneratorPath t : ℂ) := by
        change ((f (criticalMeridianUnitBallPath t) : Units ℂ) : ℂ) = _
        simp [f, criticalMeridianUnitBallPath]
      rw [hqval]
      rw [show (⟨m, by
          have hm : 0 < m := Fact.out
          omega⟩ : Fin (m + m)) =
          criticalRawMarkedIndex (m := m) (n := m) by
        apply Fin.ext
        rfl]
      rw [criticalSecondMeridianRaw_marked]
      simp
    · exact complexOpenUnitBallSubtractionLoop_mk_eq_refl
        ((-1 : ℂ) ^ m) (by simp) criticalMeridianUnitBallPath
  · apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    apply Units.ext
    change
      ((criticalSourceAnalyticProjection
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalSecondMeridianRaw_chartPoly_ne_zero
            (mul_ne_zero criticalMeridianScale_ne_zero (Units.ne_zero _))
            (criticalMeridianScale_norm_lt_one t)))).1 : ℂ) =
        ((criticalSourceAnalyticProjection
          (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
            (criticalSecondMeridianAwayBase m n).2)).1 : ℂ)
    rw [criticalSourceAnalyticProjection_awayAlgPoint_first_val,
      criticalSourceAnalyticProjection_awayAlgPoint_first_val]
    change criticalSecondMeridianRaw (m := m) (n := n)
        (criticalMeridianScale *
          (complexUnitsFundamentalGeneratorPath t : ℂ)) criticalRawMarkedIndex =
      criticalSecondMeridianRaw (m := m) (n := n) criticalMeridianScale
        criticalRawMarkedIndex
    rw [criticalSecondMeridianRaw_marked, criticalSecondMeridianRaw_marked]
    simp [hnm]

private theorem conjugate_cast_translatedLoopPath_mk
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {u v : G} (huv : v = u) (alpha : Path 1 v) (g : Path 1 1) :
    Path.Homotopic.Quotient.mk
        (alpha.trans (((translatedLoopPath u g).cast huv huv).trans alpha.symm)) =
      Path.Homotopic.Quotient.mk g := by
  subst u
  simpa using conjugate_translatedLoopPath_mk alpha g

private theorem conjugate_null_loop_mk
    {X : Type*} [TopologicalSpace X] {x y : X}
    (alpha : Path x y) (p : Path y y)
    (hp : Path.Homotopic.Quotient.mk p =
      Path.Homotopic.Quotient.mk (Path.refl y)) :
    Path.Homotopic.Quotient.mk (alpha.trans (p.trans alpha.symm)) =
      Path.Homotopic.Quotient.mk (Path.refl x) := by
  change (Path.Homotopic.Quotient.mk alpha).trans
      ((Path.Homotopic.Quotient.mk p).trans
        (Path.Homotopic.Quotient.mk alpha.symm)) = _
  rw [hp]
  simp

private theorem pathQuotient_trans_left_cancel
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path.Homotopic.Quotient x y)
    {q r : Path.Homotopic.Quotient y z}
    (h : p.trans q = p.trans r) : q = r := by
  have h' := congrArg (fun s ↦ p.symm.trans s) h
  simpa [← Path.Homotopic.Quotient.trans_assoc] using h'

private theorem pathQuotient_symm_trans
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) :
    (p.trans q).symm = q.symm.trans p.symm := by
  apply pathQuotient_trans_left_cancel (p.trans q)
  rw [Path.Homotopic.Quotient.trans_symm]
  symm
  calc
    (p.trans q).trans (q.symm.trans p.symm) =
        p.trans (q.trans (q.symm.trans p.symm)) :=
          Path.Homotopic.Quotient.trans_assoc p q _
    _ =
        p.trans ((q.trans q.symm).trans p.symm) := by
          rw [Path.Homotopic.Quotient.trans_assoc]
    _ = p.trans ((Path.Homotopic.Quotient.refl y).trans p.symm) := by
      rw [Path.Homotopic.Quotient.trans_symm]
    _ = p.trans p.symm := by simp
    _ = Path.Homotopic.Quotient.refl x :=
      Path.Homotopic.Quotient.trans_symm p

private theorem conjugate_two_paths_cast_translatedLoopPath_mk
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {u v w : G} (huv : v = u) (alpha : Path 1 w) (eta : Path w v)
    (g : Path 1 1) :
    Path.Homotopic.Quotient.mk
        (alpha.trans
          (eta.trans
            (((translatedLoopPath u g).cast huv huv).trans
              (eta.symm.trans alpha.symm)))) =
      Path.Homotopic.Quotient.mk g := by
  have h := conjugate_cast_translatedLoopPath_mk huv (alpha.trans eta) g
  change ((Path.Homotopic.Quotient.mk alpha).trans
      (Path.Homotopic.Quotient.mk eta)).trans
        ((Path.Homotopic.Quotient.mk
          ((translatedLoopPath u g).cast huv huv)).trans
          ((Path.Homotopic.Quotient.mk alpha).trans
            (Path.Homotopic.Quotient.mk eta)).symm) =
      Path.Homotopic.Quotient.mk g at h
  rw [pathQuotient_symm_trans] at h
  change (Path.Homotopic.Quotient.mk alpha).trans
      ((Path.Homotopic.Quotient.mk eta).trans
        ((Path.Homotopic.Quotient.mk
          ((translatedLoopPath u g).cast huv huv)).trans
          ((Path.Homotopic.Quotient.mk eta).symm.trans
            (Path.Homotopic.Quotient.mk alpha).symm))) =
    Path.Homotopic.Quotient.mk g
  simpa only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.mk_cast] using h

def criticalSourceMeridianConnector :
    Path
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianAwayBase m n).2)
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalSecondMeridianAwayBase m n).2) := by
  letI : PathConnectedSpace (AlgSpec (criticalSourceChartRing ℂ m n)) :=
    pathConnectedSpace_algSpec_criticalSourceChartRing m n
  exact PathConnectedSpace.somePath _ _

def criticalChartMeridianConnector :
    Path (1 : ComplexTorusAffineChart (n + m - 2))
      (criticalSourceAnalyticProjectionContinuousMap (m := m) (n := n)
        (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
          (criticalFirstMeridianAwayBase m n).2)) := by
  letI : PathConnectedSpace
      (Multiplicative (Fin (n + m - 2) → ℂ)) :=
    inferInstanceAs (PathConnectedSpace (Fin (n + m - 2) → ℂ))
  letI : PathConnectedSpace (ComplexTorusAffineChart (n + m - 2)) :=
    inferInstance
  exact PathConnectedSpace.somePath _ _

def criticalFirstGlobalProjectedMeridian :
    Path (1 : ComplexTorusAffineChart (n + m - 2)) 1 :=
  (criticalChartMeridianConnector m n).trans
    ((criticalFirstProjectedMeridian m n).trans
      (criticalChartMeridianConnector m n).symm)

def criticalSecondGlobalProjectedMeridian :
    Path (1 : ComplexTorusAffineChart (n + m - 2)) 1 :=
  let etaProjected := (criticalSourceMeridianConnector m n).map
    (criticalSourceAnalyticProjectionContinuousMap
      (m := m) (n := n)).continuous
  (criticalChartMeridianConnector m n).trans
    (etaProjected.trans
      ((criticalSecondProjectedMeridian m n).trans
        (etaProjected.symm.trans (criticalChartMeridianConnector m n).symm)))

@[simp] private theorem torusChart_fst_one (k : ℕ) :
    ContinuousMap.fst (1 : ComplexTorusAffineChart k) = (1 : Units ℂ) := rfl

@[simp] private theorem torusChart_snd_fst_one (k : ℕ) :
    ContinuousMap.fst (ContinuousMap.snd
      (1 : ComplexTorusAffineChart k)) = (1 : Units ℂ) := rfl

theorem criticalFirstGlobalProjectedMeridian_mk :
    Path.Homotopic.Quotient.mk (criticalFirstGlobalProjectedMeridian m n) =
      torusChartFirstFundamentalGenerator (n + m - 2) := by
  apply torusChart_mk_eq_firstGenerator_of_coordinate_mk
  · rw [show (criticalFirstGlobalProjectedMeridian m n).map
        ContinuousMap.fst.continuous =
      ((criticalChartMeridianConnector m n).map
          ContinuousMap.fst.continuous).trans
        (((criticalFirstProjectedMeridian m n).map
            ContinuousMap.fst.continuous).trans
          ((criticalChartMeridianConnector m n).map
            ContinuousMap.fst.continuous).symm) by
        simp only [criticalFirstGlobalProjectedMeridian, Path.map_trans,
          ← Path.map_symm]]
    rw [criticalFirstProjectedMeridian_first]
    have h := conjugate_cast_translatedLoopPath_mk
      (criticalFirstProjectedMeridian_base_first m n)
      ((criticalChartMeridianConnector m n).map ContinuousMap.fst.continuous)
      complexUnitsFundamentalGeneratorPath
    rw [complexUnitsFundamentalGeneratorPath_mk] at h
    rw [show criticalMeridianScaledGeneratorPath =
      translatedLoopPath criticalMeridianScaleUnit
        complexUnitsFundamentalGeneratorPath by rfl]
    convert h using 1
    case e'_1 => simp
    case e'_2 => rfl
    case e'_3 => rfl
  · rw [show ((criticalFirstGlobalProjectedMeridian m n).map
          ContinuousMap.snd.continuous).map ContinuousMap.fst.continuous =
      (((criticalChartMeridianConnector m n).map
          ContinuousMap.snd.continuous).map
          ContinuousMap.fst.continuous).trans
        ((((criticalFirstProjectedMeridian m n).map
            ContinuousMap.snd.continuous).map
            ContinuousMap.fst.continuous).trans
          (((criticalChartMeridianConnector m n).map
            ContinuousMap.snd.continuous).map
            ContinuousMap.fst.continuous).symm) by
        simp only [criticalFirstGlobalProjectedMeridian, Path.map_trans,
          ← Path.map_symm]]
    have h := conjugate_null_loop_mk
      (((criticalChartMeridianConnector m n).map
        ContinuousMap.snd.continuous).map ContinuousMap.fst.continuous)
      (((criticalFirstProjectedMeridian m n).map
        ContinuousMap.snd.continuous).map ContinuousMap.fst.continuous)
      (criticalFirstProjectedMeridian_second_mk_eq_refl m n)
    simpa using h

theorem criticalSecondGlobalProjectedMeridian_mk :
    Path.Homotopic.Quotient.mk (criticalSecondGlobalProjectedMeridian m n) =
      torusChartSecondFundamentalGenerator (n + m - 2) := by
  let etaProjected := (criticalSourceMeridianConnector m n).map
    (criticalSourceAnalyticProjectionContinuousMap
      (m := m) (n := n)).continuous
  let gamma := (criticalChartMeridianConnector m n).trans etaProjected
  apply torusChart_mk_eq_secondGenerator_of_coordinate_mk
  · have h := conjugate_null_loop_mk
      (gamma.map ContinuousMap.fst.continuous)
      ((criticalSecondProjectedMeridian m n).map
        ContinuousMap.fst.continuous)
      (criticalSecondProjectedMeridian_first_mk_eq_refl m n)
    simpa [criticalSecondGlobalProjectedMeridian, etaProjected, gamma,
      Path.map_trans, ← Path.map_symm] using h
  · let alphaSecond := ((criticalChartMeridianConnector m n).map
      ContinuousMap.snd.continuous).map ContinuousMap.fst.continuous
    let etaSecond := (etaProjected.map ContinuousMap.snd.continuous).map
      ContinuousMap.fst.continuous
    rw [show ((criticalSecondGlobalProjectedMeridian m n).map
          ContinuousMap.snd.continuous).map ContinuousMap.fst.continuous =
      alphaSecond.trans
        (etaSecond.trans
          ((((criticalSecondProjectedMeridian m n).map
              ContinuousMap.snd.continuous).map
              ContinuousMap.fst.continuous).trans
            (etaSecond.symm.trans alphaSecond.symm))) by
        simp only [criticalSecondGlobalProjectedMeridian, etaProjected,
          alphaSecond, etaSecond, Path.map_trans, ← Path.map_symm]]
    rw [criticalSecondProjectedMeridian_second]
    rw [show criticalMeridianScaledGeneratorPath =
      translatedLoopPath criticalMeridianScaleUnit
        complexUnitsFundamentalGeneratorPath by rfl]
    have h := conjugate_two_paths_cast_translatedLoopPath_mk
      (criticalSecondProjectedMeridian_base_second m n)
      alphaSecond etaSecond complexUnitsFundamentalGeneratorPath
    rw [complexUnitsFundamentalGeneratorPath_mk] at h
    convert h using 1
    case e'_1 => simp
    case e'_2 => rfl
    case e'_3 => rfl

def criticalSecondSourceMeridian :
    Path
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianAwayBase m n).2)
      (AlgSpec.awayAlgPoint (criticalSourceChartPoly ℂ m n)
        (criticalFirstMeridianAwayBase m n).2) :=
  (criticalSourceMeridianConnector m n).trans
    ((criticalSecondSourceLocalMeridian m n).trans
      (criticalSourceMeridianConnector m n).symm)

theorem criticalFirstSourceMeridian_conjugate_mk :
    (Path.Homotopic.Quotient.mk (criticalChartMeridianConnector m n)).trans
        (((Path.Homotopic.Quotient.mk
          (criticalFirstSourceLocalMeridian m n)).map
            (criticalSourceAnalyticProjectionContinuousMap
              (m := m) (n := n))).trans
          (Path.Homotopic.Quotient.mk
            (criticalChartMeridianConnector m n)).symm) =
      torusChartFirstFundamentalGenerator (n + m - 2) := by
  rw [← Path.Homotopic.Quotient.mk_map]
  change (Path.Homotopic.Quotient.mk
      (criticalChartMeridianConnector m n)).trans
        ((Path.Homotopic.Quotient.mk
          ((criticalFirstSourceLocalMeridian m n).map
            (criticalSourceAnalyticProjectionContinuousMap
              (m := m) (n := n)).continuous)).trans
          (Path.Homotopic.Quotient.mk
            (criticalChartMeridianConnector m n)).symm) =
      torusChartFirstFundamentalGenerator (n + m - 2)
  have h := criticalFirstGlobalProjectedMeridian_mk m n
  change (Path.Homotopic.Quotient.mk
      (criticalChartMeridianConnector m n)).trans
        ((Path.Homotopic.Quotient.mk
          (criticalFirstProjectedMeridian m n)).trans
          (Path.Homotopic.Quotient.mk
            (criticalChartMeridianConnector m n).symm)) =
      torusChartFirstFundamentalGenerator (n + m - 2) at h
  rw [Path.Homotopic.Quotient.mk_symm
    (criticalChartMeridianConnector m n)] at h
  exact h

theorem criticalSecondSourceMeridian_conjugate_mk :
    (Path.Homotopic.Quotient.mk (criticalChartMeridianConnector m n)).trans
        (((Path.Homotopic.Quotient.mk
          (criticalSecondSourceMeridian m n)).map
            (criticalSourceAnalyticProjectionContinuousMap
              (m := m) (n := n))).trans
          (Path.Homotopic.Quotient.mk
            (criticalChartMeridianConnector m n)).symm) =
      torusChartSecondFundamentalGenerator (n + m - 2) := by
  rw [← Path.Homotopic.Quotient.mk_map]
  rw [criticalSecondSourceMeridian, Path.map_trans, Path.map_trans,
    ← Path.map_symm]
  rw [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  have h := criticalSecondGlobalProjectedMeridian_mk m n
  rw [criticalSecondGlobalProjectedMeridian,
    Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_symm] at h
  rw [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_assoc]
  exact h

end
end GaloisForLFunctions.HTGeometry
