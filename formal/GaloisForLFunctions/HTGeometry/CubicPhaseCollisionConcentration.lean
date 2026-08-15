import GaloisForLFunctions.HTGeometry.CubicPhaseCollisionMoments

/-!
# Basis-uniform concentration of the cubic phase seed collision

The first two moments of the collision of a cubic eighth-root phase seed with an orthonormal family
equal the continuous ones, so the continuous mean and variance bounds hold verbatim: the mean is at
most twice the family size and the variance at most ninety-six times it, before the squared-dimension
normalization of the seed.  Chebyshev's inequality in the uniform finite model then bounds the
fraction of seeds whose collision exceeds the mean bound.
-/

open Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {J : Type*} [Fintype J] [DecidableEq J]

section RealTransfer

theorem average_finCollision (e : J → (ι → Bool) → ℂ) :
    ((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finCollision e c =
      ∫ x in torusBox (ι → Bool), ∑ j, ‖phaseAmp e j x‖ ^ 4 := by
  have h := average_finQuarticSum e
  have hL : ((cubicSeedCount ι : ℂ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finQuarticSum e c =
      ((((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finCollision e c : ℝ) : ℂ) := by
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun c _ => finQuarticSum_eq_ofReal e c
  have hR : (∫ x in torusBox (ι → Bool), quarticSum e x) =
      (((∫ x in torusBox (ι → Bool), ∑ j, ‖phaseAmp e j x‖ ^ 4 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => quarticSum_eq_ofReal e x)
  rw [hL, hR] at h
  exact_mod_cast h

theorem average_finCollision_sq (e : J → (ι → Bool) → ℂ) :
    ((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, (finCollision e c) ^ 2 =
      ∫ x in torusBox (ι → Bool), (∑ j, ‖phaseAmp e j x‖ ^ 4) ^ 2 := by
  have h := average_finQuarticSum_sq e
  have hL : ((cubicSeedCount ι : ℂ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, (finQuarticSum e c) ^ 2 =
      ((((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8,
        (finCollision e c) ^ 2 : ℝ) : ℂ) := by
    have hstep : ∀ c : MonLe ι 3 → ZMod 8,
        (finQuarticSum e c) ^ 2 = (((finCollision e c ^ 2 : ℝ)) : ℂ) := by
      intro c
      rw [finQuarticSum_eq_ofReal]
      push_cast
      ring
    simp only [hstep]
    push_cast
    ring
  have hR : (∫ x in torusBox (ι → Bool), (quarticSum e x) ^ 2) =
      (((∫ x in torusBox (ι → Bool), (∑ j, ‖phaseAmp e j x‖ ^ 4) ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (quarticSum e x) ^ 2 = (((∑ j, ‖phaseAmp e j x‖ ^ 4) ^ 2 : ℝ) : ℂ)
    rw [quarticSum_eq_ofReal]
    push_cast
    ring
  rw [hL, hR] at h
  exact_mod_cast h

end RealTransfer

section Bounds

/-- **The continuous mean collision of the unit-weight seed.** -/
theorem integral_box_collision_le (e : J → (ι → Bool) → ℂ)
    (he : ∀ j, (∑ a, ‖e j a‖ ^ 2) ≤ 1) :
    (∫ x in torusBox (ι → Bool), ∑ j, ‖phaseAmp e j x‖ ^ 4) ≤ 2 * (Fintype.card J : ℝ) := by
  classical
  rw [integral_finsetSum _ fun j _ => integrableOn_box_normPow_phaseAmp e j 4]
  have hterm : ∀ j : J,
      (∫ x in torusBox (ι → Bool), ‖phaseAmp e j x‖ ^ 4) ≤ 2 := by
    intro j
    have hpt : ∀ x : (ι → Bool) → ℝ, ‖phaseAmp e j x‖ ^ 4 =
        finitePureStateFidelity (torusReplicaPhaseOrbit (fun _ => (1 : ℝ)) x) (e j) ^ 2 := by
      intro x
      rw [← normSq_phaseAmp, ← pow_mul]
    simp only [hpt]
    have hbound := integral_box_fidelity_pow_le (p := fun _ : ι → Bool => (1 : ℝ))
      (fun _ => zero_le_one) (τ := 1) (fun _ => le_rfl) zero_le_one (he j) 2
    refine le_trans hbound (le_of_eq ?_)
    norm_num [Nat.factorial]
  calc (∑ j : J, ∫ x in torusBox (ι → Bool), ‖phaseAmp e j x‖ ^ 4)
      ≤ ∑ _j : J, (2 : ℝ) := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * (Fintype.card J : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

/-- **Mean collision of the cubic phase seed.** -/
theorem average_finCollision_le (e : J → (ι → Bool) → ℂ)
    (he : ∀ j, (∑ a, ‖e j a‖ ^ 2) ≤ 1) :
    ((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finCollision e c ≤
      2 * (Fintype.card J : ℝ) := by
  rw [average_finCollision]
  exact integral_box_collision_le e he

/-- **Variance of the collision of the cubic phase seed.** -/
theorem variance_finCollision_le (e : J → (ι → Bool) → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) :
    ((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, (finCollision e c) ^ 2 -
        (((cubicSeedCount ι : ℝ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finCollision e c) ^ 2 ≤
      96 * (Fintype.card J : ℝ) := by
  rw [average_finCollision, average_finCollision_sq]
  exact integral_box_variance_collision_le e horth

end Bounds

section Chebyshev

/-- **Chebyshev concentration of the cubic phase seed collision.**  The fraction of cubic seeds
whose collision exceeds the mean bound by `t` is at most `96 |J| / t²`. -/
theorem card_filter_finCollision_gt_le (e : J → (ι → Bool) → ℂ)
    (he : ∀ j, (∑ a, ‖e j a‖ ^ 2) ≤ 1)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0)
    {t : ℝ} (ht : 0 < t) :
    ((Finset.univ.filter fun c : MonLe ι 3 → ZMod 8 =>
        2 * (Fintype.card J : ℝ) + t < finCollision e c).card : ℝ) /
        (cubicSeedCount ι : ℝ) ≤ 96 * (Fintype.card J : ℝ) / t ^ 2 := by
  classical
  set N : ℝ := (cubicSeedCount ι : ℝ) with hN
  have hNpos : 0 < N := cubicSeedCount_pos
  set μ : ℝ := N⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finCollision e c with hμ
  set A : ℝ := N⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, (finCollision e c) ^ 2 with hA
  set S : Finset (MonLe ι 3 → ZMod 8) :=
    Finset.univ.filter fun c => 2 * (Fintype.card J : ℝ) + t < finCollision e c with hS
  have hmean : μ ≤ 2 * (Fintype.card J : ℝ) := average_finCollision_le e he
  have hvar : A - μ ^ 2 ≤ 96 * (Fintype.card J : ℝ) := variance_finCollision_le e horth
  have hcardN : ((Fintype.card (MonLe ι 3 → ZMod 8) : ℕ) : ℝ) = N := by
    rw [hN, cubicSeedCount]
  have hsumeq : (∑ c : MonLe ι 3 → ZMod 8, finCollision e c) = N * μ := by
    rw [hμ, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
  have hsumsq : (∑ c : MonLe ι 3 → ZMod 8, (finCollision e c) ^ 2) = N * A := by
    rw [hA, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
  have hexpand : (∑ c : MonLe ι 3 → ZMod 8, (finCollision e c - μ) ^ 2) =
      (∑ c : MonLe ι 3 → ZMod 8, (finCollision e c) ^ 2) -
        2 * μ * (∑ c : MonLe ι 3 → ZMod 8, finCollision e c) + N * μ ^ 2 := by
    have h1 : ∀ c : MonLe ι 3 → ZMod 8, (finCollision e c - μ) ^ 2 =
        (finCollision e c) ^ 2 - 2 * μ * finCollision e c + μ ^ 2 := by
      intro c
      ring
    simp only [h1]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hcardN]
  have hkey : (∑ c : MonLe ι 3 → ZMod 8, (finCollision e c - μ) ^ 2) ≤
      N * (96 * (Fintype.card J : ℝ)) := by
    rw [hexpand, hsumeq, hsumsq]
    have hmul := mul_le_mul_of_nonneg_left hvar (le_of_lt hNpos)
    nlinarith [hmul]
  have hlow : (S.card : ℝ) * t ^ 2 ≤
      ∑ c : MonLe ι 3 → ZMod 8, (finCollision e c - μ) ^ 2 := by
    have hsub : ∑ _c ∈ S, t ^ 2 ≤ ∑ c ∈ S, (finCollision e c - μ) ^ 2 := by
      refine Finset.sum_le_sum fun c hc => ?_
      rw [hS, Finset.mem_filter] at hc
      have hgt : t < finCollision e c - μ := by linarith [hc.2, hmean]
      nlinarith [ht.le, hgt]
    have hall : ∑ c ∈ S, (finCollision e c - μ) ^ 2 ≤
        ∑ c : MonLe ι 3 → ZMod 8, (finCollision e c - μ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun c _ _ => by positivity)
    calc (S.card : ℝ) * t ^ 2 = ∑ _c ∈ S, t ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ S, (finCollision e c - μ) ^ 2 := hsub
      _ ≤ _ := hall
  have htsq : 0 < t ^ 2 := by positivity
  rw [div_le_div_iff₀ hNpos htsq]
  nlinarith [hlow, hkey]

end Chebyshev

end GaloisForLFunctions.HTGeometry
