/-
# Gaussian majorant for Bourgain's first-spacing count

The double large sieve counts pairs of six-fold moment vectors that are close
at four reciprocal coordinate scales.  A positive Gaussian turns that sharp
near-pair count into a smooth spacing energy.  This is the positivity step
behind the standard Fourier-majorant argument, proved here with an explicit
constant.
-/
import GaloisForLFunctions.RHTower.BourgainSixfoldCloud

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Squared distance after applying the four spacing scales. -/
def bourgainScaledSqDist
    (X u v : BourgainPhaseSpace) : ℝ :=
  ∑ j : Fin 4, (X j * (u j - v j)) ^ (2 : ℕ)

/-- Positive Gaussian energy of the six-fold moment cloud. -/
def bourgainGaussianSpacingEnergy
    (H : ℕ) (X : BourgainPhaseSpace) : ℝ :=
  ∑ h : Fin 6 → Fin H, ∑ h' : Fin 6 → Fin H,
    Real.exp (-Real.pi *
      bourgainScaledSqDist X
        (bourgainSixfoldMoment h) (bourgainSixfoldMoment h'))

theorem bourgainScaledSqDist_nonneg
    (X u v : BourgainPhaseSpace) :
    0 ≤ bourgainScaledSqDist X u v := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem bourgainGaussianSpacingEnergy_nonneg
    (H : ℕ) (X : BourgainPhaseSpace) :
    0 ≤ bourgainGaussianSpacingEnergy H X := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Real.exp_nonneg _

/-- A coordinatewise near pair has scaled squared distance at most one. -/
theorem bourgainScaledSqDist_le_one_of_nearPair
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) {h h' : Fin 6 → Fin H}
    (hnear : BourgainNearPair X h h') :
    bourgainScaledSqDist X
      (bourgainSixfoldMoment h) (bourgainSixfoldMoment h') ≤ 1 := by
  have hcoord (j : Fin 4) :
      (X j * (bourgainSixfoldMoment h j -
        bourgainSixfoldMoment h' j)) ^ (2 : ℕ) ≤ 1 / 4 := by
    let d : ℝ :=
      bourgainSixfoldMoment h j - bourgainSixfoldMoment h' j
    have habs :
        |X j * d| < 1 / 2 := by
      calc
        |X j * d| = X j * |d| := by
          rw [abs_mul, abs_of_pos (hX j)]
        _ < X j * (1 / (2 * X j)) :=
          mul_lt_mul_of_pos_left (hnear j) (hX j)
        _ = 1 / 2 := by
          field_simp [(hX j).ne']
    have habs_nonneg : 0 ≤ |X j * d| := abs_nonneg _
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hsq :
        |X j * d| ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ habs_nonneg hhalf 2 habs.le
    simpa [d, sq_abs] using hsq
  calc
    bourgainScaledSqDist X
        (bourgainSixfoldMoment h) (bourgainSixfoldMoment h') ≤
      ∑ _j : Fin 4, (1 / 4 : ℝ) :=
        Finset.sum_le_sum fun j _ => hcoord j
    _ = 1 := by norm_num

/-- Explicit Gaussian majorant for the first-spacing count:

`#near pairs ≤ e^π · Σ exp(-π‖X(y-y')‖²)`.

The proof uses only positivity and the fact that every near pair has scaled
squared distance at most one. -/
theorem bourgainFirstSpacingCount_le_gaussianEnergy
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) :
    (bourgainFirstSpacingCount H X : ℝ) ≤
      Real.exp Real.pi * bourgainGaussianSpacingEnergy H X := by
  classical
  let U : Finset (Fin 6 → Fin H) := Finset.univ
  let P : Finset ((Fin 6 → Fin H) × (Fin 6 → Fin H)) := U.product U
  have hterm
      (p : (Fin 6 → Fin H) × (Fin 6 → Fin H)) (hp : p ∈ P) :
      (if BourgainNearPair X p.1 p.2 then (1 : ℝ) else 0) ≤
        Real.exp Real.pi *
          Real.exp (-Real.pi *
            bourgainScaledSqDist X
              (bourgainSixfoldMoment p.1)
              (bourgainSixfoldMoment p.2)) := by
    split_ifs with hnear
    · rw [← Real.exp_add]
      have hdist := bourgainScaledSqDist_le_one_of_nearPair hX hnear
      have hexp :
          (0 : ℝ) ≤ Real.pi +
            -Real.pi *
              bourgainScaledSqDist X
                (bourgainSixfoldMoment p.1)
                (bourgainSixfoldMoment p.2) := by
        nlinarith [Real.pi_pos]
      simpa using (Real.exp_le_exp.mpr hexp :
        Real.exp 0 ≤ Real.exp
          (Real.pi +
            -Real.pi *
              bourgainScaledSqDist X
                (bourgainSixfoldMoment p.1)
                (bourgainSixfoldMoment p.2)))
    · positivity
  calc
    (bourgainFirstSpacingCount H X : ℝ) =
        ∑ p ∈ P,
          if BourgainNearPair X p.1 p.2 then (1 : ℝ) else 0 := by
      simp [bourgainFirstSpacingCount, P, U, Finset.sum_boole]
    _ ≤ ∑ p ∈ P,
        Real.exp Real.pi *
          Real.exp (-Real.pi *
            bourgainScaledSqDist X
              (bourgainSixfoldMoment p.1)
              (bourgainSixfoldMoment p.2)) :=
      Finset.sum_le_sum hterm
    _ = Real.exp Real.pi * bourgainGaussianSpacingEnergy H X := by
      simp only [P, U, Finset.sum_product, bourgainGaussianSpacingEnergy,
        Finset.mul_sum]

end

end RHTower
