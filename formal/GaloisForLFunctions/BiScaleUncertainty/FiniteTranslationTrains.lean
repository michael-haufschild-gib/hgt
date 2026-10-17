import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridDistanceClassification
import GaloisForLFunctions.BiScaleUncertainty.AbstractBiScaleSystemAndSchurKreinCoupling

/-!
# Finite translated sources and extremal-pair isolation

The full finite-source correlation expansion yields local diagonal preservation and
an exact endpoint-pair identity near the full span of a separated common-seed train.
Interior difference collisions and arbitrary real coefficient signs are allowed.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def finiteTranslateSource {ι : Type*} (f : ℝ → ℝ) (s : Finset ι) (c t : ι → ℝ)
    (u : ℝ) : ℝ := ∑ i ∈ s, c i * f (u - t i)

theorem contDiff_finiteTranslateSource {ι : Type*} {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hf : ContDiff ℝ r f) (s : Finset ι) (c t : ι → ℝ) :
    ContDiff ℝ r (finiteTranslateSource f s c t) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_finiteTranslateSource {ι : Type*} {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (s : Finset ι) (c t : ι → ℝ) :
    HasCompactSupport (finiteTranslateSource f s c t) := by
  classical
  apply hasCompactSupport_finset_sum
  intro i _
  exact (hfc.comp_homeomorph (Homeomorph.subRight (t i))).mul_left

theorem autocorr_finiteTranslateSource {ι : Type*} {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (s : Finset ι) (c t : ι → ℝ) (x : ℝ) :
    autocorr (finiteTranslateSource f s c t) x =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * autocorr f (x + t i - t j) := by
  let F := fun i j u => c i * c j * (f (u + -t i) * f (u + (x - t j)))
  have hi (i j : ι) : Integrable (F i j) :=
    (integrable_shift_mul_shift hf hfc (-t i) (x - t j)).const_mul _
  have he : (fun u => finiteTranslateSource f s c t u * finiteTranslateSource f s c t (u + x)) =
      fun u => ∑ i ∈ s, ∑ j ∈ s, F i j u := by
    funext u
    simp only [finiteTranslateSource, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [F]
    rw [show u - t i = u + -t i by ring, show u + x - t j = u + (x - t j) by ring]
    ring
  change (∫ u, finiteTranslateSource f s c t u * finiteTranslateSource f s c t (u + x)) = _
  rw [he, integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum s (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [F]
  rw [integral_const_mul, integral_shift_mul_shift]
  congr 2
  ring

def copyTrain (f : ℝ → ℝ) {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) : ℝ → ℝ :=
  finiteTranslateSource f Finset.univ c (fun i => (i.val : ℝ) * S)

def copyTrainMass {m : ℕ} (c : Fin (m + 1) → ℝ) : ℝ := ∑ i, c i ^ 2

theorem contDiff_copyTrain {f : ℝ → ℝ} {r : WithTop ℕ∞} (hf : ContDiff ℝ r f)
    {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) : ContDiff ℝ r (copyTrain f c S) :=
  contDiff_finiteTranslateSource hf _ _ _

theorem hasCompactSupport_copyTrain {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    {m : ℕ} (c : Fin (m + 1) → ℝ) (S : ℝ) : HasCompactSupport (copyTrain f c S) :=
  hasCompactSupport_finiteTranslateSource hfc _ _ _

theorem autocorr_copyTrain {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {m : ℕ} (c : Fin (m + 1) → ℝ) (S x : ℝ) :
    autocorr (copyTrain f c S) x =
      ∑ i, ∑ j, c i * c j * autocorr f (x + (i.val : ℝ) * S - (j.val : ℝ) * S) :=
  autocorr_finiteTranslateSource hf hfc _ _ _ _

theorem copyTrainMass_pos {m : ℕ} {c : Fin (m + 1) → ℝ} (hc : c 0 ≠ 0) :
    0 < copyTrainMass c := by
  have hp : 0 < c 0 ^ 2 := by positivity
  have h := Finset.single_le_sum (s := Finset.univ) (f := fun i => c i ^ 2)
    (fun i _ => sq_nonneg (c i)) (by simp : (0 : Fin (m + 1)) ∈ Finset.univ)
  exact hp.trans_le h

/-- Every short correlation is exactly the diagonal coefficient mass times the seed correlation. -/
theorem autocorr_copyTrain_local {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {m : ℕ} (c : Fin (m + 1) → ℝ) {D S x : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S) (hx : |x| ≤ 1) :
    autocorr (copyTrain f c S) x = copyTrainMass c * autocorr f x := by
  have hS0 : 0 < S := by linarith
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hz (i j : Fin (m + 1)) (hij : i ≠ j) :
      autocorr f (x + (i.val : ℝ) * S - (j.val : ℝ) * S) = 0 := by
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · have hb : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
      have hm := mul_le_mul_of_nonneg_right hb hS0.le
      apply hsupp
      exact lt_of_lt_of_le (by nlinarith : D < -(x + (i.val : ℝ) * S - (j.val : ℝ) * S)) (neg_le_abs _)
    · have hb : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast (show j.val + 1 ≤ i.val by omega)
      have hm := mul_le_mul_of_nonneg_right hb hS0.le
      apply hsupp
      exact lt_of_lt_of_le (by nlinarith : D < x + (i.val : ℝ) * S - (j.val : ℝ) * S) (le_abs_self _)
  rw [autocorr_copyTrain hf hfc, copyTrainMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = c i * c i * autocorr f (x + (i.val : ℝ) * S - (i.val : ℝ) * S) := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [hz i j (Ne.symm hj), mul_zero]
      · simp
    _ = _ := by rw [add_sub_cancel_right]; ring

/-- Near the full span, only the endpoint pair survives, irrespective of interior interference. -/
theorem autocorr_copyTrain_extremal {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {m : ℕ} (c : Fin (m + 1) → ℝ) {D S x : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ y, D < |y| → autocorr f y = 0) (hS : D + 1 < S)
    (hx : |x - (m : ℝ) * S| ≤ 1) :
    autocorr (copyTrain f c S) x = c 0 * c (Fin.last m) * autocorr f (x - (m : ℝ) * S) := by
  have hS0 : 0 < S := by linarith
  have hxlo := (abs_le.mp hx).1
  have hz (i j : Fin (m + 1)) (hp : i ≠ 0 ∨ j ≠ Fin.last m) :
      autocorr f (x + (i.val : ℝ) * S - (j.val : ℝ) * S) = 0 := by
    have hnat : j.val + 1 ≤ m + i.val := by
      have hj := j.is_lt
      rcases hp with hi | hjm
      · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        omega
      · have hjv : j.val ≠ m := fun h => hjm (Fin.ext h)
        omega
    have hb : (j.val : ℝ) + 1 ≤ (m : ℝ) + (i.val : ℝ) := by exact_mod_cast hnat
    have hm := mul_le_mul_of_nonneg_right hb hS0.le
    apply hsupp
    exact lt_of_lt_of_le (by nlinarith : D < x + (i.val : ℝ) * S - (j.val : ℝ) * S) (le_abs_self _)
  rw [autocorr_copyTrain hf hfc]
  calc
    _ = ∑ j : Fin (m + 1), c 0 * c j * autocorr f (x + ((0 : Fin (m + 1)).val : ℝ) * S - (j.val : ℝ) * S) := by
      apply Finset.sum_eq_single 0
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro j _
        rw [hz i j (Or.inl hi), mul_zero]
      · simp
    _ = c 0 * c (Fin.last m) *
        autocorr f (x + ((0 : Fin (m + 1)).val : ℝ) * S - ((Fin.last m).val : ℝ) * S) := by
      apply Finset.sum_eq_single (Fin.last m)
      · intro j _ hj
        rw [hz 0 j (Or.inr hj), mul_zero]
      · simp
    _ = _ := by simp

end

end GaloisForLFunctions.BiScaleUncertainty
