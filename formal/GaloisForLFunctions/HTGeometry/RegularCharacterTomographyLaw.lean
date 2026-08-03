import GaloisForLFunctions.RHTower.BohrCoefficientUniqueness

/-!
# Regular character tomography

An absolutely summable character packet can vanish identically only by
cancellation inside each observed-frequency fibre.  Thus every nonzero atom
has a distinct mate in the same observed grade.  An injective resolving
coordinate upgrades this to equality of full source grades; a noninjective
coordinate can create a zero only through an explicit collision of distinct
source grades.

For injectively resolved distinct grades, character tomography is exact:
the response vanishes identically if and only if every source coefficient
vanishes.
-/

open Complex MeasureTheory intervalIntegral Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An absolutely summable character packet can vanish identically only if
the coefficient sum in every observed-frequency fibre vanishes. -/
theorem regularCharacter_fiberSum_eq_zero
    (freq : ℕ → ℝ) (c : ℕ → ℂ)
    (hsum : Summable (fun n => ‖c n‖))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * Complex.exp ((freq n : ℂ) * Complex.I * (y : ℂ)) = 0)
    (m : ℕ) :
    (∑' n : ℕ, if freq n = freq m then c n else 0) = 0 := by
  have havg := RHTower.char_avg_tendsto hsum (fun n => freq n - freq m)
  have hzero : Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0 : ℝ)..T,
      ∑' n : ℕ, c n *
        Complex.exp (((freq n - freq m : ℝ) : ℂ) * Complex.I * (y : ℂ)))
      atTop (𝓝 0) := by
    have hInt : ∀ y : ℝ, (∑' n : ℕ, c n *
        Complex.exp (((freq n - freq m : ℝ) : ℂ) * Complex.I * (y : ℂ))) = 0 := by
      intro y
      have hterm : ∀ n : ℕ,
          c n * Complex.exp (((freq n - freq m : ℝ) : ℂ) * Complex.I * (y : ℂ))
            = Complex.exp (((-freq m : ℝ) : ℂ) * Complex.I * (y : ℂ)) *
              (c n * Complex.exp ((freq n : ℂ) * Complex.I * (y : ℂ))) := by
        intro n
        rw [show (((freq n - freq m : ℝ) : ℂ) * Complex.I * (y : ℂ)) =
            (freq n : ℂ) * Complex.I * (y : ℂ) +
              ((-freq m : ℝ) : ℂ) * Complex.I * (y : ℂ) by push_cast; ring,
          Complex.exp_add]
        ring
      rw [tsum_congr hterm, tsum_mul_left, hvan y, mul_zero]
    have hfun : (fun T : ℝ => (↑T)⁻¹ * ∫ y in (0 : ℝ)..T,
        ∑' n : ℕ, c n *
          Complex.exp (((freq n - freq m : ℝ) : ℂ) * Complex.I * (y : ℂ))) =
        fun _ : ℝ => (0 : ℂ) := by
      funext T
      rw [show (fun y : ℝ => ∑' n : ℕ, c n *
          Complex.exp (((freq n - freq m : ℝ) : ℂ) * Complex.I * (y : ℂ))) =
          fun _ => (0 : ℂ) from funext hInt,
        intervalIntegral.integral_zero, mul_zero]
    rw [hfun]
    exact tendsto_const_nhds
  have hdiag :
      (∑' n : ℕ, if freq n - freq m = 0 then c n else 0) = 0 :=
    tendsto_nhds_unique havg hzero
  simpa only [sub_eq_zero] using hdiag

/-- Every nonzero atom of a vanishing regular character packet has a
distinct nonzero mate in the same observed-frequency fibre. -/
theorem exists_sameObservedGrade_mate_of_regularCharacter_eq_zero
    (freq : ℕ → ℝ) (c : ℕ → ℂ)
    (hsum : Summable (fun n => ‖c n‖))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * Complex.exp ((freq n : ℂ) * Complex.I * (y : ℂ)) = 0)
    {m : ℕ} (hcm : c m ≠ 0) :
    ∃ n : ℕ, n ≠ m ∧ freq n = freq m ∧ c n ≠ 0 := by
  have hfiber := regularCharacter_fiberSum_eq_zero freq c hsum hvan m
  by_contra hmate
  have hpt : ∀ n : ℕ, (if freq n = freq m then c n else 0) =
      if n = m then c m else 0 := by
    intro n
    by_cases hnm : n = m
    · subst n
      simp
    · by_cases hfreq : freq n = freq m
      · have hcn : c n = 0 := by
          by_contra hcn
          exact hmate ⟨n, hnm, hfreq, hcn⟩
        simp [hnm, hfreq, hcn]
      · simp [hnm, hfreq]
  have hcollapse :
      (∑' n : ℕ, if freq n = freq m then c n else 0) = c m := by
    rw [tsum_congr hpt, tsum_eq_single m (fun n hn => if_neg hn), if_pos rfl]
  rw [hcollapse] at hfiber
  exact hcm hfiber

/-- If the resolving coordinate is injective, a vanishing regular packet
must cancel in the full source grade, not merely after observation. -/
theorem exists_sameGrade_mate_of_regularCharacter_eq_zero
    {Γ : Type*} (grade : ℕ → Γ) (resolve : Γ → ℝ)
    (hresolve : Function.Injective resolve) (c : ℕ → ℂ)
    (hsum : Summable (fun n => ‖c n‖))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * Complex.exp ((resolve (grade n) : ℂ) * Complex.I * (y : ℂ)) = 0)
    {m : ℕ} (hcm : c m ≠ 0) :
    ∃ n : ℕ, n ≠ m ∧ grade n = grade m ∧ c n ≠ 0 := by
  obtain ⟨n, hnm, hfreq, hcn⟩ :=
    exists_sameObservedGrade_mate_of_regularCharacter_eq_zero
      (resolve ∘ grade) c hsum hvan hcm
  exact ⟨n, hnm, hresolve hfreq, hcn⟩

/-- If full source grades are distinct, any vanishing produced after a
nonfaithful resolving coordinate exhibits an explicit collision of distinct
source grades. -/
theorem exists_gradeCollision_of_regularCharacter_eq_zero
    {Γ : Type*} (grade : ℕ → Γ) (hgrade : Function.Injective grade)
    (resolve : Γ → ℝ) (c : ℕ → ℂ)
    (hsum : Summable (fun n => ‖c n‖))
    (hvan : ∀ y : ℝ, ∑' n : ℕ,
      c n * Complex.exp ((resolve (grade n) : ℂ) * Complex.I * (y : ℂ)) = 0)
    {m : ℕ} (hcm : c m ≠ 0) :
    ∃ n : ℕ, n ≠ m ∧ grade n ≠ grade m ∧
      resolve (grade n) = resolve (grade m) ∧ c n ≠ 0 := by
  obtain ⟨n, hnm, hfreq, hcn⟩ :=
    exists_sameObservedGrade_mate_of_regularCharacter_eq_zero
      (resolve ∘ grade) c hsum hvan hcm
  exact ⟨n, hnm, fun h => hnm (hgrade h), hfreq, hcn⟩

/-- A regular character packet with distinct fully resolved grades cannot
vanish if it has any nonzero coefficient. -/
theorem exists_regularCharacterResponse_ne_zero_of_injective
    {Γ : Type*} (grade : ℕ → Γ) (hgrade : Function.Injective grade)
    (resolve : Γ → ℝ) (hresolve : Function.Injective resolve)
    (c : ℕ → ℂ) (hsum : Summable (fun n => ‖c n‖))
    {m : ℕ} (hcm : c m ≠ 0) :
    ∃ y : ℝ, (∑' n : ℕ,
      c n * Complex.exp ((resolve (grade n) : ℂ) * Complex.I * (y : ℂ))) ≠ 0 := by
  by_contra hnone
  have hvan : ∀ y : ℝ, (∑' n : ℕ,
      c n * Complex.exp ((resolve (grade n) : ℂ) * Complex.I * (y : ℂ))) = 0 := by
    intro y
    simpa only [not_ne_iff] using (not_exists.mp hnone y)
  obtain ⟨n, hnm, hsame, _⟩ :=
    exists_sameGrade_mate_of_regularCharacter_eq_zero
      grade resolve hresolve c hsum hvan hcm
  exact hnm (hgrade hsame)

/-- Exact regular-tomography law for separated grades: an absolutely
summable character packet vanishes identically exactly when every source
coefficient vanishes. -/
theorem regularCharacter_response_eq_zero_iff_of_injective
    (freq : ℕ → ℝ) (hfreq : Function.Injective freq)
    (c : ℕ → ℂ) (hsum : Summable (fun n => ‖c n‖)) :
    (∀ y : ℝ, ∑' n : ℕ,
      c n * Complex.exp ((freq n : ℂ) * Complex.I * (y : ℂ)) = 0) ↔
      ∀ n : ℕ, c n = 0 := by
  constructor
  · intro hvan m
    have hfiber := regularCharacter_fiberSum_eq_zero freq c hsum hvan m
    have hpt : ∀ n : ℕ, (if freq n = freq m then c n else 0) =
        if n = m then c m else 0 := by
      intro n
      by_cases hnm : n = m
      · subst n
        simp
      · have hne : freq n ≠ freq m := fun h => hnm (hfreq h)
        simp [hnm, hne]
    have hcollapse :
        (∑' n : ℕ, if freq n = freq m then c n else 0) = c m := by
      rw [tsum_congr hpt, tsum_eq_single m (fun n hn => if_neg hn), if_pos rfl]
    rwa [hcollapse] at hfiber
  · intro hc y
    simp_rw [hc, zero_mul]
    exact tsum_zero

end

end GaloisForLFunctions.HTGeometry
