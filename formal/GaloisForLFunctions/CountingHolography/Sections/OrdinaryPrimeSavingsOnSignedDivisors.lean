import GaloisForLFunctions.CountingHolography.Sections.EffectiveSectionsAtSeparatedConductors

/-!
# Ordinary prime savings on signed divisors

The one-sided cost of the omitted prime powers on a signed divisor is bounded
by the effective cost on its absolute coefficients. On a pole-balanced divisor the archimedean debit also has a uniform
quadratic bound on the original mesh.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology AbsoluteGeometryOfSpecZ ArithmeticFunction BiScaleUncertainty.ChebyshevGauge

private theorem abs_sample_le {N : ℕ} (a : Fin N → ℤ) (r j : ℕ) :
    |degreeSample (packet a) r j| ≤ degreeSample (packet (fun i => |a i|)) r j := by
  unfold degreeSample packet splineSource
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul,Int.cast_abs,abs_of_nonneg (cubicSpline_nonneg _)]

private theorem contact_le_abs_divisor {N : ℕ} (a : Fin N → ℤ) (L r k : ℕ) :
    contactMultiplicity (packet a) L r k ≤ contactMultiplicity (packet (fun i => |a i|)) L r k := by
  unfold contactMultiplicity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine sum_le_sum fun j _ => div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine (le_abs_self _).trans ?_
  rw [abs_mul]
  exact mul_le_mul (abs_sample_le a r j) (abs_sample_le a r (j*k)) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_sample_le a r j))

private theorem log_full_modulus {N : ℕ} (a : Fin N → ℤ) :
    Real.log (contactModulus a) = ∑ k ∈ Icc 2 (3*windowEnd N),
      (⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) k⌋₊ : ℝ)*vonMangoldt k := by
  unfold contactModulus
  push_cast
  rw [Real.log_prod (fun k _ => (pow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℝ) < _) _).ne')]
  simp only [Real.log_pow,log_contactBase]

/-- The upper comparison of the full signed logarithmic generator with its
ordinary-prime part costs only squared total variation, at every horizon. -/
theorem signed_proper_power_upper : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    Real.log (generator a : ℝ) - Real.log (ordinaryPrimeGenerator a : ℝ) ≤ C*(resolution a : ℝ)^2 := by
  obtain ⟨C,h⟩ := effective_modulus_difference_bound
  refine ⟨|C|,abs_nonneg _,fun N a => ?_⟩
  let b := fun i => |a i|
  let S := Icc 2 (3*windowEnd N)
  let x (v : Fin N → ℤ) := contactMultiplicity (packet v) (3*windowEnd N) (resolution v)
  have hr : resolution b = resolution a := by
    have he : (resolution b : ℝ) = resolution a := by
      rw [← coefficientVariation_eq_resolution b, ← coefficientVariation_eq_resolution a]
      simp only [b,Int.cast_abs,abs_abs]
    exact_mod_cast he
  have hsplit (w : ℕ → ℝ) : (∑ k ∈ S, w k) - (∑ k ∈ S.filter Nat.Prime, w k) =
      ∑ k ∈ S.filter (fun k => ¬ k.Prime), w k :=
    sub_eq_iff_eq_add.mpr ((sum_filter_add_sum_filter_not S Nat.Prime w).symm.trans (add_comm _ _))
  have h₁ : Real.log (generator a : ℝ) - Real.log (ordinaryPrimeGenerator a : ℝ) =
      ∑ k ∈ S.filter (fun k => ¬ k.Prime), (⌊x a k⌋ : ℝ)*vonMangoldt k := by
    rw [generator,log_contactGenerator,log_ordinaryPrimeGenerator]
    exact hsplit _
  have h₂ : Real.log (contactModulus b) - Real.log (ordinaryPrimeModulus b) =
      ∑ k ∈ S.filter (fun k => ¬ k.Prime), (⌊x b k⌋₊ : ℝ)*vonMangoldt k := by
    rw [log_full_modulus,log_ordinaryPrimeModulus]
    exact hsplit _
  have hc := (h N b (fun i => abs_nonneg _)).2
  simp only [b,Int.cast_abs,coefficientVariation_eq_resolution] at hc
  rw [h₁]
  calc _ ≤ ∑ k ∈ S.filter (fun k => ¬ k.Prime), (⌊x b k⌋₊ : ℝ)*vonMangoldt k := by
          refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ vonMangoldt_nonneg
          have hx : x a k ≤ x b k := by
            unfold x
            rw [hr]
            exact contact_le_abs_divisor a _ _ _
          have hw : ⌊x a k⌋ ≤ (⌊x b k⌋₊ : ℤ) := by
            refine (Int.floor_le_floor hx).trans ?_
            rw [← Int.floor_toNat]
            omega
          exact_mod_cast hw
       _ ≤ _ := (h₂.ge.trans hc).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))

/-- On a positive-pole-balanced divisor every ordinary-prime logarithmic saving
beyond a uniform quadratic cost is available to the original section lattice. -/
theorem pole_balanced_ordinary_section_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    positivePoleDegree a = 0 → Real.log (generator a : ℝ)-radius a ≤
      Real.log (ordinaryPrimeGenerator a : ℝ) + C*(resolution a : ℝ)^2 := by
  obtain ⟨A,hA,hord⟩ := signed_proper_power_upper
  obtain ⟨J,hJ,hjet⟩ := uniform_finite_jet_debit
  obtain ⟨P,hP,hpole⟩ := pole_balanced_linear_error
  refine ⟨A+J+P,by positivity,fun N a ha => ?_⟩
  have hr : (resolution a : ℝ) ≤ (resolution a : ℝ)^2 := by
    rcases Nat.eq_zero_or_pos (resolution a) with h | h
    · simp [h]
    · have h1 : (1:ℝ) ≤ resolution a := by exact_mod_cast h
      linarith only [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) (resolution a))]
  have hjet' : -jetRadius a ≤ J*(resolution a : ℝ)^2 := by
    rcases Nat.eq_zero_or_pos (resolution a) with h | h
    · simp [jetRadius,h,degreeForm,degreePairing]
    · simpa only [jetRadius,neg_neg,coefficientVariation_eq_resolution] using hjet N a (3*windowEnd N) _ h
  linarith only [hord N a, hjet', (abs_le.mp (hpole N a ha)).1, mul_le_mul_of_nonneg_left hr hP]

#print axioms signed_proper_power_upper
#print axioms pole_balanced_ordinary_section_bound

end GaloisForLFunctions.CountingHolography.Sections
