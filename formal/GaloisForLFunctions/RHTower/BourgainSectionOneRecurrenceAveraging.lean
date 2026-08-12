/-
# Exact averaging transfer for Bourgain's Section-1 recurrence

This module formalizes the passage from products of local `L⁶` masses on
coarse cubes to the two independently translated averages in Bourgain's
equation (1.20).  Exact grid partition and Tonelli remove the apparent
`H⁸` cube count; only the fixed enlargement from radius `R` to `2R`
remains.
-/
import GaloisForLFunctions.RHTower.BourgainSectionOneRecurrenceGeometry

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Centered four-dimensional sup-norm cube. -/
def bourgainCenteredNormCube (R : ℝ) : Set BourgainPhaseSpace :=
  {x | ‖x‖ ≤ R}

/-- Unnormalized average of a nonnegative function over a translated
centered cube. -/
def bourgainTranslateAverage
    (R : ℝ) (f : BourgainPhaseSpace → ENNReal)
    (x : BourgainPhaseSpace) : ENNReal :=
  ∫⁻ y in bourgainCenteredNormCube R, f (x + y)

theorem measurableSet_bourgainCenteredNormCube (R : ℝ) :
    MeasurableSet (bourgainCenteredNormCube R) := by
  unfold bourgainCenteredNormCube
  exact measurableSet_Iic.preimage continuous_norm.measurable

theorem measurable_bourgainTranslateAverage
    {R : ℝ} {f : BourgainPhaseSpace → ENNReal}
    (hf : Measurable f) :
    Measurable (bourgainTranslateAverage R f) := by
  unfold bourgainTranslateAverage
  have hjoint : Measurable fun p :
      BourgainPhaseSpace × BourgainPhaseSpace => f (p.1 + p.2) :=
    hf.comp (measurable_fst.add measurable_snd)
  exact
    (hjoint.lintegral_prod_right :
      Measurable fun x : BourgainPhaseSpace =>
        ∫⁻ y in bourgainCenteredNormCube R, f (x + y))

/-- Two points of one radius-`R` cube differ by at most `2R`. -/
theorem bourgainTranslatedNormCube_subset_translate_twoRadius
    {R : ℝ}
    {c x : BourgainPhaseSpace}
    (hx : x ∈ bourgainTranslatedNormCube c R) :
    bourgainTranslatedNormCube c R ⊆
      bourgainTranslatedNormCube x (2 * R) := by
  intro z hz
  rw [mem_bourgainTranslatedNormCube_iff] at hx hz ⊢
  calc
    ‖z - x‖ ≤ ‖z - c‖ + ‖x - c‖ := by
      have hidentity : z - x = (z - c) - (x - c) := by
        module
      rw [hidentity]
      exact norm_sub_le _ _
    _ ≤ R + R := add_le_add hz hx
    _ = 2 * R := by ring

/-- Every local mass is bounded by the radius-`2R` translate average around
each point of its own cube. -/
theorem setLIntegral_bourgainTranslatedNormCube_le_translateAverage
    {R : ℝ}
    (f : BourgainPhaseSpace → ENNReal)
    {c x : BourgainPhaseSpace}
    (hx : x ∈ bourgainTranslatedNormCube c R) :
    (∫⁻ z in bourgainTranslatedNormCube c R, f z) ≤
      bourgainTranslateAverage (2 * R) f x := by
  calc
    (∫⁻ z in bourgainTranslatedNormCube c R, f z) ≤
        ∫⁻ z in bourgainTranslatedNormCube x (2 * R), f z :=
      lintegral_mono_set
        (bourgainTranslatedNormCube_subset_translate_twoRadius hx)
    _ = ∫⁻ y in bourgainCenteredNormCube (2 * R), f (y + x) := by
      exact setLIntegral_bourgainTranslatedNormCube x (2 * R) f
    _ = bourgainTranslateAverage (2 * R) f x := by
      apply setLIntegral_congr_fun
        (measurableSet_bourgainCenteredNormCube (2 * R))
      intro y hy
      change f (y + x) = f (x + y)
      rw [add_comm]

/-- Exact local-to-global averaging inequality over the recurrence grid.
The volume factor on the left is the anchor-point average that removes the
cube count after summation. -/
theorem volume_mul_sum_coarseGrid_localMassProduct_le_translateAverage
    (J H : ℕ) (hJ : 0 < J) (hH : 0 < H)
    {f g : BourgainPhaseSpace → ENNReal}
    (hf : Measurable f) (hg : Measurable g) :
    let R := bourgainSectionOneCoarsePhysicalRadius J
    let V := ENNReal.ofReal ((2 * R) ^ (4 : ℕ))
    V *
        ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          (∫⁻ z in bourgainTranslatedNormCube
              (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, f z) *
            (∫⁻ z in bourgainTranslatedNormCube
              (bourgainGridCenter (H ^ (2 : ℕ)) R k) R, g z) ≤
      ∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H),
        bourgainTranslateAverage (2 * R) f x *
          bourgainTranslateAverage (2 * R) g x := by
  dsimp only
  let R := bourgainSectionOneCoarsePhysicalRadius J
  let V := ENNReal.ofReal ((2 * R) ^ (4 : ℕ))
  let U : (Fin 4 → Fin (H ^ (2 : ℕ))) → Set BourgainPhaseSpace :=
    fun k => bourgainTranslatedNormCube
      (bourgainGridCenter (H ^ (2 : ℕ)) R k) R
  let F : BourgainPhaseSpace → ENNReal :=
    bourgainTranslateAverage (2 * R) f
  let G : BourgainPhaseSpace → ENNReal :=
    bourgainTranslateAverage (2 * R) g
  have hR : 0 < R := by
    dsimp [R]
    unfold bourgainSectionOneCoarsePhysicalRadius
    positivity
  have hV (k : Fin 4 → Fin (H ^ (2 : ℕ))) :
      volume (U k) = V := by
    simpa [U, V, R] using
      volume_bourgainSectionOne_coarsePhysicalCube J
        (bourgainGridCenter (H ^ (2 : ℕ)) R k)
  have hFGmeas : Measurable fun x => F x * G x :=
    (measurable_bourgainTranslateAverage hf).mul
      (measurable_bourgainTranslateAverage hg)
  have hterm (k : Fin 4 → Fin (H ^ (2 : ℕ))) :
      V * ((∫⁻ z in U k, f z) * (∫⁻ z in U k, g z)) ≤
        ∫⁻ x in U k, F x * G x := by
    calc
      V * ((∫⁻ z in U k, f z) * (∫⁻ z in U k, g z)) =
          ((∫⁻ z in U k, f z) * (∫⁻ z in U k, g z)) *
            volume (U k) := by rw [hV]; ring
      _ = ∫⁻ _x in U k,
          ((∫⁻ z in U k, f z) * (∫⁻ z in U k, g z)) := by
        exact (setLIntegral_const (U k) _).symm
      _ ≤ ∫⁻ x in U k, F x * G x := by
        apply setLIntegral_mono hFGmeas
        intro x hx
        exact mul_le_mul
          (setLIntegral_bourgainTranslatedNormCube_le_translateAverage
            f hx)
          (setLIntegral_bourgainTranslatedNormCube_le_translateAverage
            g hx) (by positivity) (by positivity)
  calc
    V *
        ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          (∫⁻ z in U k, f z) * (∫⁻ z in U k, g z) =
        ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
          V * ((∫⁻ z in U k, f z) * (∫⁻ z in U k, g z)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ k : Fin 4 → Fin (H ^ (2 : ℕ)),
        ∫⁻ x in U k, F x * G x := by
      exact Finset.sum_le_sum fun k hk => hterm k
    _ = ∫⁻ x in bourgainSectionOnePhaseBall
          (bourgainSectionOneBlockDenominator J H), F x * G x := by
      simpa [U] using
        sum_setLIntegral_bourgainSectionOne_coarseGrid_eq_finePhaseBall
          J H hJ hH (fun x => F x * G x)
    _ = _ := by rfl

/-- Tonelli form of the two independent translate averages. -/
theorem setLIntegral_translateAverage_mul_eq_independent_translates
    {A : Set BourgainPhaseSpace} (hA : MeasurableSet A)
    {R : ℝ} {f g : BourgainPhaseSpace → ENNReal}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x in A,
      bourgainTranslateAverage R f x *
        bourgainTranslateAverage R g x) =
      ∫⁻ y₁ in bourgainCenteredNormCube R,
        ∫⁻ y₂ in bourgainCenteredNormCube R,
          ∫⁻ x in A, f (x + y₁) * g (x + y₂) := by
  let B := bourgainCenteredNormCube R
  have hB : MeasurableSet B :=
    measurableSet_bourgainCenteredNormCube R
  have hfactor (x : BourgainPhaseSpace) :
      bourgainTranslateAverage R f x *
          bourgainTranslateAverage R g x =
        ∫⁻ y₁ in B, ∫⁻ y₂ in B,
          f (x + y₁) * g (x + y₂) := by
    unfold bourgainTranslateAverage
    dsimp only [B]
    calc
      (∫⁻ y₁ in B, f (x + y₁)) *
          (∫⁻ y₂ in B, g (x + y₂)) =
        ∫⁻ y₁ in B,
          f (x + y₁) * (∫⁻ y₂ in B, g (x + y₂)) := by
        symm
        exact lintegral_mul_const _
          (hf.comp (measurable_const.add measurable_id))
      _ = ∫⁻ y₁ in B, ∫⁻ y₂ in B,
          f (x + y₁) * g (x + y₂) := by
        apply setLIntegral_congr_fun hB
        intro y₁ hy₁
        symm
        exact lintegral_const_mul _
          (hg.comp (measurable_const.add measurable_id))
  rw [setLIntegral_congr_fun hA (fun x hx => hfactor x)]
  have hthree : Measurable fun p :
      (BourgainPhaseSpace × BourgainPhaseSpace) × BourgainPhaseSpace =>
        f (p.1.1 + p.1.2) * g (p.1.1 + p.2) := by
    exact
      (hf.comp ((measurable_fst.comp measurable_fst).add
        (measurable_snd.comp measurable_fst))).mul
      (hg.comp ((measurable_fst.comp measurable_fst).add measurable_snd))
  have hxy : Measurable fun p : BourgainPhaseSpace × BourgainPhaseSpace =>
      ∫⁻ y₂ in B, f (p.1 + p.2) * g (p.1 + y₂) :=
    hthree.lintegral_prod_right
  rw [lintegral_lintegral_swap hxy.aemeasurable]
  apply setLIntegral_congr_fun hB
  intro y₁ hy₁
  have hxz : Measurable fun p : BourgainPhaseSpace × BourgainPhaseSpace =>
      f (p.1 + y₁) * g (p.1 + p.2) :=
    (hf.comp (measurable_fst.add measurable_const)).mul
      (hg.comp (measurable_fst.add measurable_snd))
  exact lintegral_lintegral_swap hxz.aemeasurable

end

end RHTower
