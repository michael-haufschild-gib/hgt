/-
# Double large sieve for Bourgain's six-fold moment cloud

The abstract double large sieve is specialized here to the phase-aligned
sixth powers from equation (3.7).  Weighted spacing energies are bounded by
literal sharp pair counts.  The resulting theorem controls the twelfth power
of the sample sum by the first- and second-spacing counts.
-/
import GaloisForLFunctions.RHTower.BourgainDoubleLargeSieve
import GaloisForLFunctions.RHTower.BourgainSixthPowerPolarization

open scoped BigOperators

namespace RHTower

noncomputable section

noncomputable def bourgainScaledNearCount
    {ι : Type*} [Fintype ι]
    (X : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace) : ℕ := by
  classical
  exact (((Finset.univ : Finset ι).product
    (Finset.univ : Finset ι)).filter
      fun q => BourgainScaledNear X (p q.1) (p q.2)).card

theorem bourgainWeightedScaledNearEnergy_le_count
    {ι : Type*} [Fintype ι]
    (X : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    bourgainWeightedScaledNearEnergy X p a ≤
      (bourgainScaledNearCount X p : ℝ) := by
  classical
  let U : Finset ι := Finset.univ
  let P : Finset (ι × ι) := U.product U
  calc
    bourgainWeightedScaledNearEnergy X p a =
        ∑ q ∈ P,
          if BourgainScaledNear X (p q.1) (p q.2)
          then a q.1 * a q.2 else 0 := by
      unfold bourgainWeightedScaledNearEnergy P U
      simpa using
        (Finset.sum_product (Finset.univ : Finset ι)
          (Finset.univ : Finset ι)
          (fun q =>
            if BourgainScaledNear X (p q.1) (p q.2)
            then a q.1 * a q.2 else 0)).symm
    _ ≤ ∑ q ∈ P,
          if BourgainScaledNear X (p q.1) (p q.2)
          then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · calc
          a q.1 * a q.2 ≤ 1 * a q.2 :=
            mul_le_mul_of_nonneg_right (ha1 q.1) (ha0 q.2)
          _ ≤ 1 * 1 :=
            mul_le_mul_of_nonneg_left (ha1 q.2) (by norm_num)
          _ = 1 := by norm_num
      · exact le_rfl
    _ = (bourgainScaledNearCount X p : ℝ) := by
      simp [bourgainScaledNearCount, P, U, Finset.sum_boole]

theorem norm_bourgainSixfoldWeight_le_one
    {H : ℕ} {α : Fin H → ℂ}
    (hα : ∀ h, ‖α h‖ ≤ 1)
    (u : Fin 6 → Fin H) :
    ‖bourgainSixfoldWeight α u‖ ≤ 1 := by
  unfold bourgainSixfoldWeight
  rw [norm_prod]
  calc
    (∏ j : Fin 6, ‖α (u j)‖) ≤ ∏ _j : Fin 6, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact hα (u j)
    _ = 1 := by simp

theorem bourgainPolarizedSixfoldSampleSum_eq_bilinear
    {ι : Type*} [Fintype ι]
    (H : ℕ) (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace) :
    bourgainPolarizedSixfoldSampleSum H α x =
      bourgainBilinearForm x bourgainSixfoldMoment
        (fun i => bourgainSixthPowerPolarizer
          (bourgainShortCurveSum H α (x i)))
        (bourgainSixfoldWeight α) := by
  unfold bourgainPolarizedSixfoldSampleSum bourgainBilinearForm
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro h hh
  ring

theorem bourgainScaledNearCount_sixfold_eq_firstSpacingCount
    {H : ℕ} {X : BourgainPhaseSpace}
    (hX : ∀ j, 0 < X j) :
    bourgainScaledNearCount X
        (bourgainSixfoldMoment : (Fin 6 → Fin H) → BourgainPhaseSpace) =
      bourgainFirstSpacingCount H X := by
  classical
  unfold bourgainScaledNearCount bourgainFirstSpacingCount
  congr 1
  apply Finset.filter_congr
  intro q hq
  exact bourgainScaledNear_sixfold_iff hX q.1 q.2

/-- Double-large-sieve specialization of Bourgain's equation (3.7). -/
theorem bourgainDoubleLargeSieve_shortCurveSum
    {ι : Type*} [Fintype ι]
    {H : ℕ} {X Y : BourgainPhaseSpace}
    (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace)
    (hX : ∀ j, 0 < X j) (hY : ∀ j, 0 < Y j)
    (hx : ∀ q j, |x q j| ≤ X j)
    (hmoment : ∀ (h : Fin 6 → Fin H) (j : Fin 4),
      |bourgainSixfoldMoment h j| ≤ Y j)
    (hα : ∀ h, ‖α h‖ ≤ 1) :
    (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^ (12 : ℕ) ≤
      (Fintype.card ι : ℝ) ^ (10 : ℕ) *
        (((Real.exp (4 * Real.pi) * 331776) *
          (∏ j : Fin 4,
            (Real.pi ^ (2 : ℕ) * (1 + X j * Y j)))) *
        ((bourgainScaledNearCount Y x : ℝ) *
          (bourgainFirstSpacingCount H X : ℝ))) := by
  let A : ι → ℂ := fun i =>
    bourgainSixthPowerPolarizer
      (bourgainShortCurveSum H α (x i))
  let B : (Fin 6 → Fin H) → ℂ := bourgainSixfoldWeight α
  let C : ℝ := (Real.exp (4 * Real.pi) * 331776) *
    (∏ j : Fin 4,
      (Real.pi ^ (2 : ℕ) * (1 + X j * Y j)))
  let E₁ : ℝ :=
    bourgainWeightedScaledNearEnergy Y x (fun i => ‖A i‖)
  let E₂ : ℝ :=
    bourgainWeightedScaledNearEnergy X bourgainSixfoldMoment
      (fun h => ‖B h‖)
  have hpol :=
    sum_norm_bourgainShortCurveSum_pow_six_le_cloud H α x
  have hsum0 :
      0 ≤ ∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖ :=
    Finset.sum_nonneg fun i hi => norm_nonneg _
  have hsquare :
      (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^ (12 : ℕ) ≤
        (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          ‖bourgainPolarizedSixfoldSampleSum H α x‖ ^ (2 : ℕ) := by
    have hp :=
      pow_le_pow_left₀
        (pow_nonneg hsum0 6) hpol 2
    calc
      (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^ (12 : ℕ) =
          ((∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^
            (6 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ (((Fintype.card ι : ℝ) ^ (5 : ℕ)) *
          ‖bourgainPolarizedSixfoldSampleSum H α x‖) ^ (2 : ℕ) := hp
      _ = (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          ‖bourgainPolarizedSixfoldSampleSum H α x‖ ^ (2 : ℕ) := by ring
  have hdls :
      ‖bourgainPolarizedSixfoldSampleSum H α x‖ ^ (2 : ℕ) ≤
        C * (E₁ * E₂) := by
    rw [bourgainPolarizedSixfoldSampleSum_eq_bilinear]
    exact bourgainDoubleLargeSieve_standardScale
      x bourgainSixfoldMoment A B hX hY hx hmoment
  have hE₁ :
      E₁ ≤ (bourgainScaledNearCount Y x : ℝ) := by
    exact bourgainWeightedScaledNearEnergy_le_count Y x
      (fun i => ‖A i‖)
      (fun i => norm_nonneg _)
      (fun i => norm_bourgainSixthPowerPolarizer_le_one _)
  have hE₂ :
      E₂ ≤ (bourgainFirstSpacingCount H X : ℝ) := by
    have hcount :=
      bourgainWeightedScaledNearEnergy_le_count X
        (bourgainSixfoldMoment :
          (Fin 6 → Fin H) → BourgainPhaseSpace)
        (fun h => ‖B h‖)
        (fun h => norm_nonneg _)
        (fun h => norm_bourgainSixfoldWeight_le_one hα h)
    rw [bourgainScaledNearCount_sixfold_eq_firstSpacingCount hX] at hcount
    exact hcount
  have hE₂0 : 0 ≤ E₂ :=
    bourgainWeightedScaledNearEnergy_nonneg X bourgainSixfoldMoment
      (fun h => ‖B h‖) (fun h => norm_nonneg _)
  have hcount1 :
      0 ≤ (bourgainScaledNearCount Y x : ℝ) := by positivity
  have hC0 : 0 ≤ C := by
    unfold C
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_pos _).le (by norm_num)
    · exact Finset.prod_nonneg fun j hj =>
        mul_nonneg (sq_nonneg _) (by
          have hxy : 0 ≤ X j * Y j :=
            mul_nonneg (hX j).le (hY j).le
          linarith)
  calc
    (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^ (12 : ℕ) ≤
        (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          ‖bourgainPolarizedSixfoldSampleSum H α x‖ ^ (2 : ℕ) :=
      hsquare
    _ ≤ (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          (C * (E₁ * E₂)) := by
      exact mul_le_mul_of_nonneg_left hdls (by positivity)
    _ ≤ (Fintype.card ι : ℝ) ^ (10 : ℕ) *
          (C * ((bourgainScaledNearCount Y x : ℝ) *
            (bourgainFirstSpacingCount H X : ℝ))) := by
      have hprod :
          E₁ * E₂ ≤ (bourgainScaledNearCount Y x : ℝ) *
            (bourgainFirstSpacingCount H X : ℝ) :=
        mul_le_mul hE₁ hE₂ hE₂0 hcount1
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hprod hC0) (by positivity)
    _ = _ := rfl

end

end RHTower
