import GaloisForLFunctions.CountingHolography.Sections.TheDiagonalOrdinaryFloorLoss

/-!
# Sections at linear multiplicity on arbitrarily late square conductors

The nonnegative signed degree bounds the continuous prime contact from
above on a cofinal set of conductors. On those same conductors the
quadratic floor saving pays the full original height at every positive
multiplicity up to a fixed positive multiple of the conductor index.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticScatteringHolography SquareRootThreshold

/-- On arbitrarily late conductors both the ordinary and full section
heights have a fixed quadratic saving for every multiplicity, against a
single quadratic allowance in the multiplicity. The eventual tail at
each such conductor already fits the original radius. -/
theorem cofinal_square_height_with_quadratic_saving :
    ∃ A γ : ℝ, 1 ≤ A ∧ 0 < γ ∧ ∃ᶠ n : ℕ in atTop,
      (∀ m : ℕ, 0 < m → let a := m • successorSquareTriple n
        max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a)
          ≤ A*(m:ℝ)^2-γ*(n:ℝ)^2) ∧
      (∀ᶠ m : ℕ in atTop, let a := m • successorSquareTriple n
        Real.log (generator a : ℝ) < radius a) := by
  obtain ⟨c,hc,hfloor⟩ := all_multiplicities_through_diagonal_ordinary_floor_loss (K := 1) le_rfl
  obtain ⟨C,hC,hmesh⟩ := successorSquare_floor_corrected_mesh_error
  obtain ⟨D,hD,hcontact⟩ := successorSquare_contact_degree
  obtain ⟨J,hJ,hjet⟩ := pole_balanced_ordinary_section_bound
  let γ := min (c/2) (1/2:ℝ)
  have hγ : 0 < γ := lt_min (half_pos hc) (by norm_num)
  have hγc : 2*γ ≤ c := by linarith only [min_le_left (c/2) (1/2:ℝ)]
  have hγ₁ : 2*γ ≤ 1 := by linarith only [min_le_right (c/2) (1/2:ℝ)]
  refine ⟨D+16*J+1,γ,by linarith only [hD,hJ],hγ,?_⟩
  have hlate := (hfloor.and (eventually_ge_atTop ⌈C/γ⌉₊)).and (eventually_ge_atTop 1)
  apply (frequently_successorSquare_sections.and_eventually hlate).mono
  rintro n ⟨⟨htail,hlimit⟩,⟨hf,hnC⟩,hn₁⟩
  refine ⟨fun m hm => ?_,htail⟩
  let d := successorSquareTriple n
  let a := m • d
  have hq : 0 ≤ integerProbe _ d := ge_of_tendsto hlimit (Eventually.of_forall (fun m =>
    div_nonneg (Nat.cast_nonneg (α := ℝ) _) (sq_nonneg (m:ℝ))))
  have hP : ordinaryPrimeContact d ≤ D := by linarith only [(abs_le.mp (hcontact hn₁)).2,hq]
  have hC' : C ≤ (n:ℝ)*γ := (div_le_iff₀ hγ).mp ((Nat.le_ceil _).trans (by exact_mod_cast hnC))
  have hbal : positivePoleDegree a = 0 := by
    change (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i : ℝ)+1)*(((m • d) i : ℤ) : ℝ)) = 0
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]
    simp_rw [mul_left_comm _ (m:ℝ)]
    rw [← mul_sum,show (∑ i : Fin ((2*n+1)^2+1), Real.sqrt ((i : ℝ)+1)*(d i:ℝ))=0 from positivePoleDegree_successorSquareTriple hn₁,mul_zero]
  have hsize : (resolution a : ℝ) ≤ (m:ℝ)*4 := by
    change (resolution (m • d) : ℝ) ≤ _
    rw [resolution_smul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (coefficientVariation_eq_resolution d ▸ successorSquareTriple_mass n) (Nat.cast_nonneg _)
  have hJ' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hsize 2) hJ
  have hjet' := hjet _ a hbal
  have hcost := (abs_le.mp (hmesh hn₁ m)).2
  change Real.log (ordinaryPrimeGenerator a : ℝ)+ordinaryFloorLoss a-(m:ℝ)^2*ordinaryPrimeContact d ≤ C*n at hcost
  have hcomp : 2*γ*(n:ℝ)^2 ≤ ordinaryFloorLoss a+(m:ℝ)^2 := by
    by_cases hmn : m ≤ n
    · have hfit : (m:ℝ) ≤ 1*squareUpperRoot n := by
        unfold squareUpperRoot
        linarith only [(show (m:ℝ) ≤ n from Nat.cast_le.mpr hmn),Nat.cast_nonneg (α := ℝ) n]
      have hfloor' : c*(n:ℝ)^2 ≤ ordinaryFloorLoss a := hf hm hfit
      linarith only [hfloor',mul_le_mul_of_nonneg_right hγc (sq_nonneg (n:ℝ)),sq_nonneg (m:ℝ)]
    · have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_le.mpr (le_of_lt (lt_of_not_ge hmn))) 2
      linarith only [hsq,(ordinaryFloorLoss_bounds a).1,mul_le_mul_of_nonneg_right hγ₁ (sq_nonneg (n:ℝ))]
  have hcharge := mul_le_mul_of_nonneg_left hP (sq_nonneg (m:ℝ))
  have hlinear := mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg (α := ℝ) n)
  change max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) ≤ _
  apply max_le
  · linarith only [hcomp,hcost,hcharge,hlinear,mul_nonneg hJ (sq_nonneg (m:ℝ))]
  · linarith only [hcomp,hcost,hcharge,hlinear,hjet',hJ']

/-- Every prescribed multiplicity up to a fixed positive multiple of n
admits exponentially many original sections, simultaneously on arbitrarily
late conductors that also have a tail of exact original-radius fits. -/
theorem cofinal_all_square_sections_at_linear_multiplicities :
    ∃ K γ : ℝ, 1 ≤ K ∧ 0 < γ ∧ ∃ᶠ n : ℕ in atTop,
      (∀ {m : ℕ}, 0 < m → K*(m:ℝ) ≤ n → let a := m • successorSquareTriple n
        Real.log (ordinaryPrimeGenerator a : ℝ) ≤ -(γ*(n:ℝ)^2) ∧
        Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a ∧
        2*⌊Real.exp (γ*(n:ℝ)^2)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card) ∧
      (∀ᶠ m : ℕ in atTop, let a := m • successorSquareTriple n
        Real.log (generator a : ℝ) < radius a) := by
  obtain ⟨A,c,hA,hc,h⟩ := cofinal_square_height_with_quadratic_saving
  let K := 1+2*A/c
  have hK : 1 ≤ K := le_add_of_nonneg_right (div_nonneg (by linarith only [hA]) hc.le)
  have hKc : 2*A ≤ K*c := (div_le_iff₀ hc).mp (le_add_of_nonneg_left zero_le_one)
  refine ⟨K,c/2,hK,half_pos hc,h.mono ?_⟩
  rintro n ⟨hn,htail⟩
  refine ⟨fun {m} hm hs => ?_,htail⟩
  let a := m • successorSquareTriple n
  have hm₀ := Nat.cast_nonneg (α := ℝ) m
  have hn₀ := Nat.cast_nonneg (α := ℝ) n
  have hmn : (m:ℝ) ≤ n := (le_mul_of_one_le_left hm₀ hK).trans hs
  have hEm : 2*A*(m:ℝ) ≤ c*n := by
    linarith only [mul_le_mul_of_nonneg_right hKc hm₀,mul_le_mul_of_nonneg_left hs hc.le]
  have h₂ := mul_le_mul hEm hmn hm₀ (mul_nonneg hc.le hn₀)
  have hfit : max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) ≤
      -((c/2)*(n:ℝ)^2) := by linarith only [hn m hm,h₂]
  obtain ⟨ho,hfull⟩ := max_le_iff.mp hfit
  refine ⟨ho,by linarith only [hfull],?_⟩
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have he := Real.exp_le_exp.mpr (show (c/2)*(n:ℝ)^2 ≤ radius a-Real.log (generator a : ℝ) by linarith only [hfull])
  rw [Real.exp_sub,Real.exp_log hpos] at he
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.floor_mono he)) 1

#print axioms cofinal_square_height_with_quadratic_saving
#print axioms cofinal_all_square_sections_at_linear_multiplicities

end GaloisForLFunctions.CountingHolography.Sections
