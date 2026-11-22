import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedVariance.Residues
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedContinuation.InfinitePoles

/-!
# Sharp boundary for probability-preserving centered poles

The real variance pole fixes the largest right half-plane on which
every centered pole is an isometric binary split. Its residue relative
to the real primary residue also recovers the squared radix.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance

open BalancedContinuation BalancedShift

theorem analytic_off_lattices (t : ExceptionalTime) (j : ℕ)
    (s : {z : ℂ // -(7/2) < z.re ∧ ∀ k, z ≠ point t j k ∧ z ≠ second t j k}) :
    AnalyticAt ℂ (continued t j) s.val := by
  have h₀ := scale_off t j _ fun k => (s.property.2 k).1
  have h₂ := scale_off t j (s.val+2) fun k hk => (s.property.2 k).2 ((eq_sub_iff_add_eq).mpr hk)
  exact (fullNum_analytic t j ⟨_,s.property.1⟩).div (scale_analytic t j _) (mul_ne_zero h₀ h₂)

/-- Each surviving primary clock frequency produces precisely two simple poles in this region. -/
theorem pole_locus (t : ExceptionalTime) (j : ℕ) (s : Region) :
    meromorphicOrderAt (continued t j) s.val < 0 ↔ ∃ k : ℤ,
      meromorphicOrderAt (continuation t j) (point t j k) = (-1:ℤ) ∧
      (s.val = point t j k ∨ s.val = second t j k) := by
  constructor
  · intro hp
    by_cases h : ∃ k, s.val = point t j k ∨ s.val = second t j k
    · obtain ⟨k,hk|hk⟩ := h
      · exact ⟨k,(primary_data t j k).2.1.mp (hk ▸ hp),Or.inl hk⟩
      · exact ⟨k,(secondary_data t j k).2.1.mp (hk ▸ hp),Or.inr hk⟩
    · push Not at h
      exact (hp.not_ge (analytic_off_lattices t j ⟨s.val,s.property,h⟩).meromorphicOrderAt_nonneg).elim
  · rintro ⟨k,hk,he|he⟩
    · rw [he]; exact (primary_data t j k).2.1.mpr hk
    · rw [he]; exact (secondary_data t j k).2.1.mpr hk

theorem no_cubic_poles (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // z.re = -(5/2)}) :
    AnalyticAt ℂ (continued t j) s.val := by
  apply analytic_off_lattices t j ⟨s.val,by rw [s.property]; norm_num,?_⟩
  intro k
  constructor
  · intro h; have hr : s.val.re = 1/2 := congrArg Complex.re h; linarith only [hr,s.property]
  · intro h; have hr := congrArg Complex.re h; rw [second_re] at hr; linarith only [hr,s.property]

private theorem real_second (t : ExceptionalTime) (j : ℕ) : second t j 0 = -(3/2:ℂ) := by
  apply Complex.ext <;> norm_num [second,clockPoint,Complex.sub_re,Complex.sub_im]

private theorem real_primary (t : ExceptionalTime) (j : ℕ) : point t j 0 = 1/2 := by
  apply Complex.ext <;> norm_num [clockPoint]

theorem real_variance_pole (t : ExceptionalTime) (j : ℕ) :
    meromorphicOrderAt (continued t j) (-(3/2:ℂ)) = (-1:ℤ) ∧
      HTGeometry.laurentCoeff (continued t j) (-(3/2:ℂ)) (-1) =
        -HTGeometry.laurentCoeff (continued t j) (1/2) (-1)/(32*((base t j:ℂ)+1)) := by
  have hp := (secondary_data t j 0).2.2.mpr (first_clock_poles t j ⟨0,Or.inl rfl⟩)
  have hr := (secondary_data t j 0).1
  have h₀ := (primary_data t j 0).1
  rw [real_second] at hp hr
  rw [← h₀,real_primary,multiplier] at hr
  refine ⟨hp,hr.trans ?_⟩
  have hB : (base t j:ℂ)+1 ≠ 0 := base_add_one_ne t j
  field_simp [hB]
  ring

/-- A pair of real Laurent coefficients determines the square of the radix. -/
theorem recover_base (t : ExceptionalTime) (j : ℕ) :
    -HTGeometry.laurentCoeff (continued t j) (1/2) (-1) /
      (32*HTGeometry.laurentCoeff (continued t j) (-(3/2:ℂ)) (-1)) = (base t j:ℂ)+1 := by
  have h := (primary_data t j 0).1
  rw [clock_residue,real_primary] at h
  have hn := (clock_pole_iff t j 0).mp (first_clock_poles t j ⟨0,Or.inl rfl⟩)
  rw [real_primary] at hn
  have h₀ : HTGeometry.laurentCoeff (continued t j) (1/2) (-1) ≠ 0 := by
    rw [h]
    exact div_ne_zero hn (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (logRadix t j).property.ne'))
  have hB : (base t j:ℂ)+1 ≠ 0 := base_add_one_ne t j
  rw [(real_variance_pole t j).2]
  field_simp [h₀,hB]

/-- Exactly the open half-planes starting at or above −3/2 have only isometric poles. -/
theorem all_poles_isometric_iff (t : ExceptionalTime) (j : ℕ) (σ : ℝ) :
    (∀ s : {z : ℂ // -(7/2) < z.re ∧ σ < z.re ∧ meromorphicOrderAt (continued t j) z < 0},
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x) ↔ -(3/2) ≤ σ := by
  constructor
  · intro hall
    by_contra! hs
    let u := second t j 0
    have hr : u.re = -(3/2) := second_re t j 0
    have hp := (secondary_data t j 0).2.1.mpr (first_clock_poles t j ⟨0,Or.inl rfl⟩)
    have h := (split_isometric_iff u).mp (hall ⟨u,by rw [hr]; norm_num,hr ▸ hs,hp⟩)
    linarith only [hr,h]
  · rintro hσ ⟨z,hz,hσz,hp⟩
    obtain ⟨k,_,hk|hk⟩ := (pole_locus t j ⟨z,hz⟩).mp hp
    · exact (split_isometric_iff _).mpr (congrArg Complex.re hk)
    · have h := (congrArg Complex.re hk).trans (second_re t j k)
      linarith only [h,hσ,hσz]

/-- Arbitrarily high positive and negative harmonics survive on the variance line. -/
theorem unbounded_variance_pairs (t : ExceptionalTime) (j K : ℕ) :
    ∃ k : ℕ, K < k ∧ meromorphicOrderAt (continued t j) (second t j (k:ℤ)) = (-1:ℤ) ∧
      meromorphicOrderAt (continued t j) (second t j (-(k:ℤ))) = (-1:ℤ) := by
  obtain ⟨k,hk,hp,hn⟩ := unbounded_pole_pairs t j K
  exact ⟨k,hk,(secondary_data t j _).2.2.mpr hp,(secondary_data t j _).2.2.mpr hn⟩

#print axioms pole_locus
#print axioms no_cubic_poles
#print axioms real_variance_pole
#print axioms recover_base
#print axioms all_poles_isometric_iff
#print axioms unbounded_variance_pairs

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedVariance
