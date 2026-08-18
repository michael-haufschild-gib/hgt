import Mathlib

/-!
# A complex jet as a real Euclidean point

A jet of `n` complex numbers is a point of a real Euclidean space of dimension `2n`, by splitting
each coordinate into its real and imaginary parts.  The map is continuous and injective, which is
all a dimension bound needs: an injective chart into `ℂ^n` is an injective chart into `ℝ^(2n)`, and
the frequency-rank bound reads the real dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- Split a complex jet into its real and imaginary coordinates. -/
noncomputable def complexJetToEuclidean (n : ℕ) (v : Fin n → ℂ) :
    EuclideanSpace ℝ (Fin (n * 2)) :=
  (EuclideanSpace.equiv (Fin (n * 2)) ℝ).symm fun i =>
    if (finProdFinEquiv.symm i).2 = 0 then (v (finProdFinEquiv.symm i).1).re
    else (v (finProdFinEquiv.symm i).1).im

@[simp]
theorem complexJetToEuclidean_apply (n : ℕ) (v : Fin n → ℂ) (i : Fin (n * 2)) :
    complexJetToEuclidean n v i =
      if (finProdFinEquiv.symm i).2 = 0 then (v (finProdFinEquiv.symm i).1).re
      else (v (finProdFinEquiv.symm i).1).im := rfl

theorem continuous_complexJetToEuclidean (n : ℕ) :
    Continuous (complexJetToEuclidean n) := by
  refine (EuclideanSpace.equiv (Fin (n * 2)) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  by_cases h : (finProdFinEquiv.symm i).2 = 0
  · simp only [if_pos h]
    exact Complex.continuous_re.comp (continuous_apply _)
  · simp only [if_neg h]
    exact Complex.continuous_im.comp (continuous_apply _)

theorem injective_complexJetToEuclidean (n : ℕ) :
    Function.Injective (complexJetToEuclidean n) := by
  intro v w hvw
  funext j
  have hre := congrArg (fun z : EuclideanSpace ℝ (Fin (n * 2)) =>
    z (finProdFinEquiv (j, (0 : Fin 2)))) hvw
  have him := congrArg (fun z : EuclideanSpace ℝ (Fin (n * 2)) =>
    z (finProdFinEquiv (j, (1 : Fin 2)))) hvw
  simp only [complexJetToEuclidean_apply, Equiv.symm_apply_apply] at hre him
  norm_num at hre him
  exact Complex.ext hre him

/-- **A chart into `ℂ^n` is a chart into `ℝ^(2n)`.**  Composing an injective continuous jet chart
with the real-coordinate splitting keeps both properties. -/
theorem injOn_complexJetToEuclidean_comp {X : Type*} {n : ℕ} {E : X → Fin n → ℂ} {F : Set X}
    (hE : Set.InjOn E F) : Set.InjOn (fun x => complexJetToEuclidean n (E x)) F :=
  fun _ ha _ hb hab => hE ha hb (injective_complexJetToEuclidean n hab)

theorem continuousOn_complexJetToEuclidean_comp {X : Type*} [TopologicalSpace X] {n : ℕ}
    {E : X → Fin n → ℂ} {F : Set X} (hE : ContinuousOn E F) :
    ContinuousOn (fun x => complexJetToEuclidean n (E x)) F :=
  (continuous_complexJetToEuclidean n).comp_continuousOn hE

end GaloisForLFunctions.HTGeometry
