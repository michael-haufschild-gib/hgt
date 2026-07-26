/-
# Perturbation stability of scaled near-pair energy

Gaussian localization reduces a finite Fourier moment to a coordinatewise
near-pair energy.  Unlike pointwise subtraction of exponential sums, this
energy is stable under bounded frequency perturbations without an additive
coefficient-`ℓ¹` error: one only shrinks the spacing scale.
-/
import GaloisForLFunctions.RHTower.BourgainGaussianClustering

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Scale shrink required when each point moves by at most `δ` in every
scaled coordinate. -/
def bourgainPerturbedSpacingScale
    (δ : ℝ) (X : BourgainPhaseSpace) : BourgainPhaseSpace :=
  fun j => X j / (1 + 4 * δ)

theorem bourgainPerturbedSpacingScale_pos
    {δ : ℝ} (hδ : 0 ≤ δ) {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) :
    ∀ j, 0 < bourgainPerturbedSpacingScale δ X j := by
  intro j
  unfold bourgainPerturbedSpacingScale
  apply div_pos (hX j)
  linarith

/-- A scaled near pair remains near after perturbing both endpoints and
shrinking the spacing scale by `1+4δ`. -/
theorem bourgainScaledNear_of_perturbed
    {δ : ℝ} (hδ : 0 ≤ δ) {X p q p' q' : BourgainPhaseSpace}
    (hp : ∀ j, |X j * (p j - q j)| ≤ δ)
    (hp' : ∀ j, |X j * (p' j - q' j)| ≤ δ)
    (hnear : BourgainScaledNear X p p') :
    BourgainScaledNear
      (bourgainPerturbedSpacingScale δ X) q q' := by
  intro j
  have hden : 0 < 1 + 4 * δ := by positivity
  have hdecomp :
      X j * (q j - q' j) =
        -(X j * (p j - q j)) +
          X j * (p j - p' j) +
          X j * (p' j - q' j) := by
    ring
  have hbound :
      |X j * (q j - q' j)| < 1 / 2 + 2 * δ := by
    rw [hdecomp]
    calc
      |-(X j * (p j - q j)) +
            X j * (p j - p' j) +
            X j * (p' j - q' j)|
          ≤ |X j * (p j - q j)| +
              |X j * (p j - p' j)| +
              |X j * (p' j - q' j)| := by
            simpa only [abs_neg] using
              abs_add_three
                (-(X j * (p j - q j)))
                (X j * (p j - p' j))
                (X j * (p' j - q' j))
      _ < δ + 1 / 2 + δ := by
        exact add_lt_add_of_lt_of_le
          (add_lt_add_of_le_of_lt (hp j) (hnear j))
          (hp' j)
      _ = 1 / 2 + 2 * δ := by ring
  unfold bourgainPerturbedSpacingScale
  have hrewrite :
      (X j / (1 + 4 * δ)) * (q j - q' j) =
        (X j * (q j - q' j)) / (1 + 4 * δ) := by
    ring
  rw [hrewrite, abs_div, abs_of_pos hden]
  apply (div_lt_iff₀ hden).2
  calc
    |X j * (q j - q' j)| < 1 / 2 + 2 * δ := hbound
    _ = (1 / 2) * (1 + 4 * δ) := by ring

/-- Pointwise perturbation stability for a finite family of frequencies. -/
theorem bourgainScaledNear_family_of_perturbed
    {ι : Type*} {δ : ℝ} (hδ : 0 ≤ δ)
    {X : BourgainPhaseSpace}
    {p q : ι → BourgainPhaseSpace}
    (hperturb :
      ∀ i j, |X j * (p i j - q i j)| ≤ δ)
    {i k : ι}
    (hnear : BourgainScaledNear X (p i) (p k)) :
    BourgainScaledNear
      (bourgainPerturbedSpacingScale δ X) (q i) (q k) :=
  bourgainScaledNear_of_perturbed hδ
    (hperturb i) (hperturb k) hnear

/-- Weighted near-pair energy is monotone under bounded frequency
perturbation after the explicit scale shrink. -/
theorem bourgainWeightedScaledNearEnergy_perturbation_le
    {ι : Type*} [Fintype ι]
    {δ : ℝ} (hδ : 0 ≤ δ)
    (X : BourgainPhaseSpace)
    (p q : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hperturb :
      ∀ i j, |X j * (p i j - q i j)| ≤ δ) :
    bourgainWeightedScaledNearEnergy X p a ≤
      bourgainWeightedScaledNearEnergy
        (bourgainPerturbedSpacingScale δ X) q a := by
  classical
  unfold bourgainWeightedScaledNearEnergy
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro k hk
  by_cases hnear : BourgainScaledNear X (p i) (p k)
  · have hnear' :=
      bourgainScaledNear_family_of_perturbed
        hδ hperturb hnear
    simp [hnear, hnear']
  · simp only [hnear, if_false]
    split_ifs
    · exact mul_nonneg (ha i) (ha k)
    · exact le_rfl

end

end RHTower
