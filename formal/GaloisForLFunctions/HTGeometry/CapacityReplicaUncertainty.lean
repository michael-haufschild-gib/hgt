import GaloisForLFunctions.HTGeometry.SpectralResolventKernel

/-!
# The capacity--replica uncertainty law and the capacity-normalized accessibility law

A weighted `L²` structure on a finite state space carries an orthonormal observer family, and the
projection of the first-entrance reporter onto that family has coefficients given by the exact
charge--mode transfer.  Each coefficient is the capacity times a source pairing over `1 − aλ`, and
the source pairings have total square mass at most the sector dimension because the reproducing
kernel of a homogeneous sector is bounded by that dimension.  So the captured square mass is at
most `cap² K/(1−a)²`, while the reporter's own square mass is at least the target mass, which is at
least the capacity.  Dividing gives the uncertainty ratio, and Bessel's best-approximation identity
turns it into a lower bound on the relative error of every observer-sector approximation.

Normalizing the reporter by `(1−a)/cap` produces the accessibility amplification: a non-negative
density of unit mean whose value on the target is `(1−a)/cap`, whose observer projection differs
from one by at most `K−1`, whose logarithm is sandwiched by the robust word complexity, and whose
super-level sets obey Markov's inequality.  Reweighting `π` by it gives the accessibility
likelihood, whose target mass lies in `[1−a, 1]` and whose relative entropy against `π` is at least
`(1−a)log(1/q) − log 2`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Weighted

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The `π`-weighted inner product of two observables. -/
def piInner (pi f g : X → ℝ) : ℝ := ∑ x, pi x * (f x * g x)

/-- The `π`-weighted square mass of an observable. -/
def piNormSq (pi f : X → ℝ) : ℝ := piInner pi f f

theorem piNormSq_nonneg (pi f : X → ℝ) (hpi : ∀ x, 0 ≤ pi x) : 0 ≤ piNormSq pi f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hpi x) (mul_self_nonneg (f x))

/-- An orthonormal observer family. -/
def IsPiOrthonormal {K : ℕ} (pi : X → ℝ) (phi : Fin K → X → ℝ) : Prop :=
  ∀ i j, piInner pi (phi i) (phi j) = if i = j then 1 else 0

/-- The observer-sector projection of an observable. -/
def piProjection {K : ℕ} (pi : X → ℝ) (phi : Fin K → X → ℝ) (f : X → ℝ) : X → ℝ :=
  fun x => ∑ j, piInner pi f (phi j) * phi j x

theorem piNormSq_piProjection {K : ℕ} (pi : X → ℝ) (phi : Fin K → X → ℝ)
    (horth : IsPiOrthonormal pi phi) (f : X → ℝ) :
    piNormSq pi (piProjection pi phi f) = ∑ j, (piInner pi f (phi j)) ^ 2 := by
  classical
  set b : Fin K → ℝ := fun j => piInner pi f (phi j) with hb
  have hLHS : piNormSq pi (piProjection pi phi f)
      = ∑ x : X, pi x * ((∑ i, b i * phi i x) * ∑ j, b j * phi j x) := rfl
  have hstep : ∀ x : X, pi x * ((∑ i, b i * phi i x) * ∑ j, b j * phi j x)
      = ∑ i, ∑ j, b i * b j * (pi x * (phi i x * phi j x)) := by
    intro x
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hLHS, Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin K, (∑ x : X, b i * b j * (pi x * (phi i x * phi j x)))
      = if i = j then (b i) ^ 2 else 0 := by
    intro j
    have hfold : (∑ x : X, b i * b j * (pi x * (phi i x * phi j x)))
        = b i * b j * piInner pi (phi i) (phi j) := by
      rw [← Finset.mul_sum]
      rfl
    rw [hfold, horth i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, mul_one, hij, sq]
    · rw [if_neg hij, if_neg hij, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => hinner j,
    Finset.sum_ite_eq Finset.univ i (fun _ => (b i) ^ 2)]
  simp only [Finset.mem_univ, if_true, hb]

end Weighted

section UncertaintyLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The source pairings of a homogeneous sector have total square mass at most its dimension.** -/
theorem sum_sq_source_pairing_le {K : ℕ} (phi : Fin K → X → ℝ) (rho : X → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hker : ∀ x y, |∑ j, phi j x * phi j y| ≤ (K : ℝ)) :
    (∑ j, (∑ x, rho x * phi j x) ^ 2) ≤ (K : ℝ) := by
  classical
  have hexp : (∑ j, (∑ x, rho x * phi j x) ^ 2)
      = ∑ x, ∑ y, rho x * rho y * (∑ j, phi j x * phi j y) := by
    have hstep : ∀ j : Fin K, (∑ x, rho x * phi j x) ^ 2
        = ∑ x, ∑ y, rho x * rho y * (phi j x * phi j y) := by
      intro j
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
  rw [hexp]
  have hbound : ∀ x y : X, rho x * rho y * (∑ j, phi j x * phi j y)
      ≤ rho x * rho y * (K : ℝ) := by
    intro x y
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hrho x) (hrho y))
    exact le_trans (le_abs_self _) (hker x y)
  calc (∑ x, ∑ y, rho x * rho y * (∑ j, phi j x * phi j y))
      ≤ ∑ x, ∑ y, rho x * rho y * (K : ℝ) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hbound x y
    _ = (K : ℝ) := by
        have hdouble : (∑ x : X, ∑ y : X, rho x * rho y * (K : ℝ))
            = (∑ x : X, ∑ y : X, rho x * rho y) * (K : ℝ) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
        have hone : (∑ x : X, ∑ y : X, rho x * rho y) = 1 := by
          have hrow : ∀ x : X, (∑ y : X, rho x * rho y) = rho x := by
            intro x
            rw [← Finset.mul_sum, hrhosum, mul_one]
          rw [Finset.sum_congr rfl fun x _ => hrow x, hrhosum]
        rw [hdouble, hone, one_mul]

/-- **`(11g)`.**  The captured square mass of the reporter is at most `cap²K/(1−a)²`. -/
theorem sum_sq_transfer_le {K : ℕ} (cap a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (coeff lam mu : Fin K → ℝ) (hlam : ∀ j, |lam j| ≤ 1)
    (hcoeff : ∀ j, coeff j = cap / (1 - a * lam j) * mu j)
    (hmu : (∑ j, (mu j) ^ 2) ≤ (K : ℝ)) :
    (∑ j, (coeff j) ^ 2) ≤ cap ^ 2 * (K : ℝ) / (1 - a) ^ 2 := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hstep : ∀ j : Fin K, (coeff j) ^ 2 ≤ cap ^ 2 / (1 - a) ^ 2 * (mu j) ^ 2 := by
    intro j
    have hlow : 1 - a ≤ 1 - a * lam j := by
      have h1 : a * lam j ≤ a := by
        have := (abs_le.mp (hlam j)).2
        nlinarith [ha]
      linarith
    have hpos : (0 : ℝ) < 1 - a * lam j := lt_of_lt_of_le hden hlow
    rw [hcoeff j, mul_pow, div_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg (mu j))
    refine div_le_div_of_nonneg_left (sq_nonneg cap) (by positivity) ?_
    exact pow_le_pow_left₀ hden.le hlow 2
  calc (∑ j, (coeff j) ^ 2) ≤ ∑ j, cap ^ 2 / (1 - a) ^ 2 * (mu j) ^ 2 :=
        Finset.sum_le_sum fun j _ => hstep j
    _ = cap ^ 2 / (1 - a) ^ 2 * ∑ j, (mu j) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ cap ^ 2 / (1 - a) ^ 2 * (K : ℝ) := by
        refine mul_le_mul_of_nonneg_left hmu (by positivity)
    _ = cap ^ 2 * (K : ℝ) / (1 - a) ^ 2 := by ring

/-- **`(11h)`.**  The reporter's square mass is at least the target mass. -/
theorem measure_le_piNormSq (pi h : X → ℝ) (A : Finset X) (hpi : ∀ x, 0 ≤ pi x)
    (hA : ∀ x ∈ A, h x = 1) :
    (∑ x ∈ A, pi x) ≤ piNormSq pi h := by
  classical
  have hsub : (∑ x ∈ A, pi x) = ∑ x ∈ A, pi x * (h x * h x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hA x hx]
    ring
  rw [hsub, piNormSq, piInner]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    fun x _ _ => mul_nonneg (hpi x) (mul_self_nonneg (h x))

/-- **`(11j)`.**  Bessel's identity: the projection is the best sector approximation, so the
relative error of every sector element is at least one minus the capture ratio. -/
theorem one_sub_le_relative_error {K : ℕ} (pi : X → ℝ) (phi : Fin K → X → ℝ)
    (horth : IsPiOrthonormal pi phi) (h : X → ℝ)
    (c : Fin K → ℝ) {ratio : ℝ}
    (hcap : piNormSq pi (piProjection pi phi h) ≤ ratio * piNormSq pi h) :
    (1 - ratio) * piNormSq pi h ≤ piNormSq pi (fun x => h x - ∑ j, c j * phi j x) := by
  classical
  have hstep : ∀ x : X, pi x * ((h x - ∑ j, c j * phi j x) * (h x - ∑ j, c j * phi j x))
      = pi x * (h x * h x) - 2 * ∑ j, c j * (pi x * (h x * phi j x))
        + ∑ i, ∑ j, c i * c j * (pi x * (phi i x * phi j x)) := by
    intro x
    have h1 : (∑ j, c j * phi j x) * (∑ j, c j * phi j x)
        = ∑ i, ∑ j, c i * c j * (phi i x * phi j x) := by
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h3 : pi x * ∑ i, ∑ j, c i * c j * (phi i x * phi j x)
        = ∑ i, ∑ j, c i * c j * (pi x * (phi i x * phi j x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h4 : pi x * (h x * ∑ j, c j * phi j x) = ∑ j, c j * (pi x * (h x * phi j x)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc pi x * ((h x - ∑ j, c j * phi j x) * (h x - ∑ j, c j * phi j x))
        = pi x * (h x * h x) - 2 * (pi x * (h x * ∑ j, c j * phi j x))
          + pi x * ((∑ j, c j * phi j x) * (∑ j, c j * phi j x)) := by ring
      _ = pi x * (h x * h x) - 2 * ∑ j, c j * (pi x * (h x * phi j x))
          + ∑ i, ∑ j, c i * c j * (pi x * (phi i x * phi j x)) := by rw [h1, h3, h4]
  have hlin : (∑ x : X, 2 * ∑ j, c j * (pi x * (h x * phi j x)))
      = 2 * ∑ j, c j * piInner pi h (phi j) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    rfl
  have hquad : (∑ x : X, ∑ i, ∑ j, c i * c j * (pi x * (phi i x * phi j x)))
      = ∑ i, (c i) ^ 2 := by
    have hinner : ∀ i j : Fin K, (∑ x : X, c i * c j * (pi x * (phi i x * phi j x)))
        = c i * c j * piInner pi (phi i) (phi j) := by
      intro i j
      rw [← Finset.mul_sum]
      rfl
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    have hstep2 : ∀ j : Fin K, (∑ x : X, c i * c j * (pi x * (phi i x * phi j x)))
        = if i = j then (c i) ^ 2 else 0 := by
      intro j
      rw [hinner i j, horth i j]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij, mul_one, hij, sq]
      · rw [if_neg hij, if_neg hij, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => hstep2 j,
      Finset.sum_ite_eq Finset.univ i (fun _ => (c i) ^ 2)]
    simp
  have hkey : piNormSq pi (fun x => h x - ∑ j, c j * phi j x)
      = piNormSq pi h - 2 * (∑ j, c j * piInner pi h (phi j)) + ∑ j, (c j) ^ 2 := by
    have hLHS : piNormSq pi (fun x => h x - ∑ j, c j * phi j x)
        = ∑ x : X, pi x * ((h x - ∑ j, c j * phi j x) * (h x - ∑ j, c j * phi j x)) := rfl
    have hRHS1 : piNormSq pi h = ∑ x : X, pi x * (h x * h x) := rfl
    rw [hLHS, Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hlin, hquad, hRHS1]
  have hproj : piNormSq pi (piProjection pi phi h) = ∑ j, (piInner pi h (phi j)) ^ 2 :=
    piNormSq_piProjection pi phi horth h
  have hsq : (∑ j, (piInner pi h (phi j)) ^ 2) ≤ ratio * piNormSq pi h := by
    rw [← hproj]
    exact hcap
  have hres : 0 ≤ ∑ j, (c j - piInner pi h (phi j)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsquare : piNormSq pi h - 2 * (∑ j, c j * piInner pi h (phi j)) + ∑ j, (c j) ^ 2
      = (piNormSq pi h - ∑ j, (piInner pi h (phi j)) ^ 2)
        + ∑ j, (c j - piInner pi h (phi j)) ^ 2 := by
    have hsum : (∑ j, (c j - piInner pi h (phi j)) ^ 2)
        = ∑ j, (c j) ^ 2 - 2 * (∑ j, c j * piInner pi h (phi j))
          + ∑ j, (piInner pi h (phi j)) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum]
    ring
  rw [hkey, hsquare]
  linarith

end UncertaintyLaw

end

end GaloisForLFunctions.HTGeometry
