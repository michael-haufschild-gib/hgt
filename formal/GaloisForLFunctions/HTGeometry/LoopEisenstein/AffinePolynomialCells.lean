import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveTranslationPolynomialCells

/-!
# Finite polynomial representatives for affine monomial cells

The two Iwahori Gauss orders isolate the root expanded by each monomial.
Truncation at its conjugation threshold leaves a finite polynomial head;
the remaining root parameters satisfy the Iwahori valuation conditions.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section

private theorem upper_reflection_factor {L : Type*} [Field L]
    (a v : Lˣ) (p t l : L) :
    sl2Upper (p + (v : L)^2 * t) * sl2Diagonal a * sl2Lower l * sl2WeylLower v⁻¹ =
      sl2Upper p * sl2WeylLower v⁻¹ *
        (sl2Lower (-t) * sl2Diagonal a⁻¹ * sl2Upper (-((v : L)^2 * l))) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, sl2Lower, sl2Diagonal, sl2WeylLower,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val] <;>
    field_simp [a.ne_zero, v.ne_zero] <;> ring

private theorem lower_translation_factor {L : Type*} [Field L]
    (a v : Lˣ) (p t u : L) :
    sl2Lower (p + (v : L)^2 * t) * sl2Diagonal a * sl2Upper u * sl2Diagonal v⁻¹ =
      sl2Lower p * sl2Diagonal v⁻¹ *
        (sl2Lower t * sl2Diagonal a * sl2Upper ((v : L)^2 * u)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, sl2Lower, sl2Diagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val] <;>
    field_simp [a.ne_zero, v.ne_zero] <;> ring

private theorem lower_reflection_factor {L : Type*} [Field L]
    (a v : Lˣ) (p t u : L) :
    sl2Lower (p + (v : L)^2 * t) * sl2Diagonal a * sl2Upper u * sl2WeylLower v =
      sl2Lower p * sl2WeylLower v *
        (sl2Upper (-t) * sl2Diagonal a⁻¹ * sl2Lower (-((v : L)^2 * u))) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, sl2Lower, sl2Diagonal, sl2WeylLower,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val] <;>
    field_simp [a.ne_zero, v.ne_zero] <;> ring

variable (F : Type*) [Field F]

private theorem exists_upper_head (n : ℕ) (u : PowerSeries F) :
    ∃ p : Polynomial F, ∃ t : PowerSeries F,
      p.degree < n ∧ u = (p : PowerSeries F) + PowerSeries.X^n*t := by
  refine ⟨PowerSeries.trunc n u, PowerSeries.mk (fun i => PowerSeries.coeff (i+n) u),
    PowerSeries.degree_trunc_lt u n, ?_⟩
  exact (PowerSeries.eq_X_pow_mul_shift_add_trunc n u).trans (add_comm _ _)

private theorem exists_lower_head (n : ℕ) (l : PowerSeries F)
    (hl : PowerSeries.constantCoeff l = 0) :
    ∃ p : Polynomial F, ∃ t : PowerSeries F,
      p.degree < n ∧ l = PowerSeries.X * (p : PowerSeries F) + PowerSeries.X^(n+1)*t := by
  obtain ⟨r, hr⟩ := PowerSeries.X_dvd_iff.mpr hl
  obtain ⟨p,t,hp,he⟩ := exists_upper_head F n r
  refine ⟨p,t,hp,?_⟩
  rw [hr,he,mul_add,pow_succ]
  ring

private theorem monomial_square_series (n : ℕ) (t : PowerSeries F) :
    (((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F)^2) *
        (t : LaurentSeries F) =
      ((PowerSeries.X^(2*n)*t : PowerSeries F) : LaurentSeries F) := by
  rw [map_mul,map_pow,HahnSeries.ofPowerSeries_X,Units.val_pow_eq_pow_val,←pow_mul]
  change (HahnSeries.single (1:ℤ) (1:F))^(n*2) * (t:LaurentSeries F) = _
  rw [Nat.mul_comm n 2]

private theorem monomial_square_X_series (n : ℕ) (t : PowerSeries F) :
    (((laurentXUnit F ^ n : (LaurentSeries F)ˣ) : LaurentSeries F)^2) *
        ((PowerSeries.X*t : PowerSeries F) : LaurentSeries F) =
      ((PowerSeries.X^(2*n+1)*t : PowerSeries F) : LaurentSeries F) := by
  rw [monomial_square_series,pow_succ,mul_assoc]

private theorem upper_series_mem (u : PowerSeries F) :
    sl2Upper (u : LaurentSeries F) ∈ laurentIwahori F :=
  sl2Upper_mem_laurentIwahori F (valuation_powerSeries_le_one F u)

private theorem lower_series_mem (l : PowerSeries F) (hl : PowerSeries.constantCoeff l = 0) :
    sl2Lower (l : LaurentSeries F) ∈ laurentIwahori F :=
  sl2Lower_mem_laurentIwahori F ((valuation_powerSeries_lt_one_iff F l).mpr hl)

private theorem diagonal_inverse_mem (a : (PowerSeries F)ˣ) :
    sl2Diagonal ((powerSeriesLaurentUnit F a)⁻¹) ∈ laurentIwahori F := by
  simpa only [map_inv] using sl2Diagonal_powerSeriesUnit_mem_laurentIwahori F a⁻¹

private theorem exists_laurent_upper_gauss (g : SL2 (LaurentSeries F))
    (hg : g ∈ laurentIwahori F) :
    ∃ u : PowerSeries F, ∃ a : (PowerSeries F)ˣ, ∃ l : PowerSeries F,
      PowerSeries.constantCoeff l = 0 ∧
        g = sl2Upper (u:LaurentSeries F) * sl2Diagonal (powerSeriesLaurentUnit F a) *
          sl2Lower (l:LaurentSeries F) := by
  obtain ⟨g₀,hg₀,rfl⟩ := hg
  obtain ⟨u,a,l,hl,he⟩ := exists_iwahori_upper_diagonal_lower F ⟨g₀,hg₀⟩
  refine ⟨u,a,l,hl,?_⟩
  change FiniteRingSl2.upper u * powerSeriesDiagonal F a * FiniteRingSl2.lower l = g₀ at he
  have hm := congrArg (powerSeriesSL2Map F) he
  rw [map_mul,map_mul,powerSeriesSL2Map_upper,powerSeriesSL2Map_diagonal,
    powerSeriesSL2Map_lower] at hm
  exact hm.symm

private theorem exists_laurent_lower_gauss (g : SL2 (LaurentSeries F))
    (hg : g ∈ laurentIwahori F) :
    ∃ l : PowerSeries F, ∃ a : (PowerSeries F)ˣ, ∃ u : PowerSeries F,
      PowerSeries.constantCoeff l = 0 ∧
        g = sl2Lower (l:LaurentSeries F) * sl2Diagonal (powerSeriesLaurentUnit F a) *
          sl2Upper (u:LaurentSeries F) := by
  obtain ⟨g₀,hg₀,rfl⟩ := hg
  obtain ⟨c,hc⟩ : ∃ c : IwahoriCoordinates F, c.toMatrix F = ⟨g₀,hg₀⟩ :=
    ⟨iwahoriCoordinates F ⟨g₀,hg₀⟩,iwahoriCoordinates_toMatrix F ⟨g₀,hg₀⟩⟩
  rcases c with ⟨l,hl,a,u⟩
  have he := congrArg (Subtype.val : iwahoriMatrices F → PowerSeriesSL2 F) hc
  change FiniteRingSl2.lower l * powerSeriesDiagonal F a * FiniteRingSl2.upper u = g₀ at he
  refine ⟨l,a,u,hl,?_⟩
  have hm := congrArg (powerSeriesSL2Map F) he
  rw [map_mul,map_mul,powerSeriesSL2Map_lower,powerSeriesSL2Map_diagonal,
    powerSeriesSL2Map_upper] at hm
  exact hm.symm

/-- A negative translation has a finite strictly-positive lower polynomial head. -/
theorem exists_lower_polynomial_translation_cell (n : ℕ) (g : SL2 (LaurentSeries F))
    (hg : g ∈ laurentIwahori F) :
    ∃ p : Polynomial F, p.degree < 2*n ∧ ∃ j ∈ laurentIwahori F,
      g * sl2Diagonal ((laurentXUnit F ^ n)⁻¹) =
        sl2Lower ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F) *
          sl2Diagonal ((laurentXUnit F ^ n)⁻¹) * j := by
  obtain ⟨l,a,u,hl,hg⟩ := exists_laurent_lower_gauss F g hg
  obtain ⟨p,t,hp,hlp⟩ := exists_lower_head F (2*n) l hl
  have hlt : PowerSeries.constantCoeff (PowerSeries.X*t) = 0 := by
    rw [map_mul,PowerSeries.constantCoeff_X,zero_mul]
  let j := sl2Lower ((PowerSeries.X*t:PowerSeries F):LaurentSeries F) *
    sl2Diagonal (powerSeriesLaurentUnit F a) *
      sl2Upper ((PowerSeries.X^(2*n)*u:PowerSeries F):LaurentSeries F)
  have hj : j ∈ laurentIwahori F :=
    (laurentIwahori F).mul_mem ((laurentIwahori F).mul_mem (lower_series_mem F _ hlt)
      (sl2Diagonal_powerSeriesUnit_mem_laurentIwahori F a)) (upper_series_mem F _)
  have hlc : (l:LaurentSeries F) =
      ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F) +
        (((laurentXUnit F ^ n:(LaurentSeries F)ˣ):LaurentSeries F)^2) *
          ((PowerSeries.X*t:PowerSeries F):LaurentSeries F) := by
    rw [monomial_square_X_series,←map_add]
    exact congrArg (HahnSeries.ofPowerSeries ℤ F) hlp
  refine ⟨p,hp,j,hj,?_⟩
  have ht : sl2Lower ((PowerSeries.X*t:PowerSeries F):LaurentSeries F) *
      sl2Diagonal (powerSeriesLaurentUnit F a) *
        sl2Upper ((((laurentXUnit F ^ n:(LaurentSeries F)ˣ):LaurentSeries F)^2) *
          (u:LaurentSeries F)) = j := by
    dsimp only [j]
    rw [monomial_square_series]
  calc
    _ = (sl2Lower (l:LaurentSeries F) * sl2Diagonal (powerSeriesLaurentUnit F a) *
        sl2Upper (u:LaurentSeries F)) * sl2Diagonal ((laurentXUnit F ^ n)⁻¹) :=
      congrArg (fun z : SL2 (LaurentSeries F) => z * sl2Diagonal ((laurentXUnit F ^ n)⁻¹)) hg
    _ = _ := (congrArg (fun z : LaurentSeries F => sl2Lower z *
      sl2Diagonal (powerSeriesLaurentUnit F a) * sl2Upper (u:LaurentSeries F) *
        sl2Diagonal ((laurentXUnit F ^ n)⁻¹)) hlc).trans
      ((lower_translation_factor (powerSeriesLaurentUnit F a) (laurentXUnit F ^ n)
        ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F)
        ((PowerSeries.X*t:PowerSeries F):LaurentSeries F) (u:LaurentSeries F)).trans
        (congrArg (fun z : SL2 (LaurentSeries F) =>
          sl2Lower ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F) *
            sl2Diagonal ((laurentXUnit F ^ n)⁻¹) * z) ht))

/-- The upper reflection cell has the head degrees `0,…,2n`. -/
theorem exists_upper_polynomial_reflection_cell (n : ℕ) (g : SL2 (LaurentSeries F))
    (hg : g ∈ laurentIwahori F) :
    ∃ p : Polynomial F, p.degree < 2*n+1 ∧ ∃ j ∈ laurentIwahori F,
      g * sl2WeylLower ((laurentXUnit F ^ n)⁻¹) =
        sl2Upper ((p:PowerSeries F):LaurentSeries F) *
          sl2WeylLower ((laurentXUnit F ^ n)⁻¹) * j := by
  obtain ⟨u,a,l,hl,hg⟩ := exists_laurent_upper_gauss F g hg
  obtain ⟨p,t,hp,hu⟩ := exists_upper_head F (2*n+1) u
  have hlt : PowerSeries.constantCoeff (-(PowerSeries.X*t)) = 0 := by
    rw [map_neg,map_mul,PowerSeries.constantCoeff_X,zero_mul,neg_zero]
  let j := sl2Lower ((-(PowerSeries.X*t):PowerSeries F):LaurentSeries F) *
    sl2Diagonal ((powerSeriesLaurentUnit F a)⁻¹) *
      sl2Upper ((-(PowerSeries.X^(2*n)*l):PowerSeries F):LaurentSeries F)
  have hj : j ∈ laurentIwahori F :=
    (laurentIwahori F).mul_mem ((laurentIwahori F).mul_mem (lower_series_mem F _ hlt)
      (diagonal_inverse_mem F a)) (upper_series_mem F _)
  have huc : (u:LaurentSeries F) = ((p:PowerSeries F):LaurentSeries F) +
      (((laurentXUnit F ^ n:(LaurentSeries F)ˣ):LaurentSeries F)^2) *
        ((PowerSeries.X*t:PowerSeries F):LaurentSeries F) := by
    rw [monomial_square_X_series,←map_add]
    exact congrArg (HahnSeries.ofPowerSeries ℤ F) hu
  refine ⟨p,hp,j,hj,?_⟩
  have ht : sl2Lower (-((PowerSeries.X*t:PowerSeries F):LaurentSeries F)) *
      sl2Diagonal ((powerSeriesLaurentUnit F a)⁻¹) *
        sl2Upper (-((((laurentXUnit F ^ n:(LaurentSeries F)ˣ):LaurentSeries F)^2) *
          (l:LaurentSeries F))) = j := by
    dsimp only [j]
    rw [monomial_square_series, map_neg, map_neg]
  calc
    _ = (sl2Upper (u:LaurentSeries F) * sl2Diagonal (powerSeriesLaurentUnit F a) *
        sl2Lower (l:LaurentSeries F)) * sl2WeylLower ((laurentXUnit F ^ n)⁻¹) :=
      congrArg (fun z : SL2 (LaurentSeries F) => z * sl2WeylLower ((laurentXUnit F ^ n)⁻¹)) hg
    _ = _ := (congrArg (fun z : LaurentSeries F => sl2Upper z *
      sl2Diagonal (powerSeriesLaurentUnit F a) * sl2Lower (l:LaurentSeries F) *
        sl2WeylLower ((laurentXUnit F ^ n)⁻¹)) huc).trans
      ((upper_reflection_factor (powerSeriesLaurentUnit F a) (laurentXUnit F ^ n)
        ((p:PowerSeries F):LaurentSeries F)
        ((PowerSeries.X*t:PowerSeries F):LaurentSeries F) (l:LaurentSeries F)).trans
        (congrArg (fun z : SL2 (LaurentSeries F) =>
          sl2Upper ((p:PowerSeries F):LaurentSeries F) *
            sl2WeylLower ((laurentXUnit F ^ n)⁻¹) * z) ht))

/-- The lower reflection cell has the head degrees `1,…,2n+1`. -/
theorem exists_lower_polynomial_reflection_cell (n : ℕ) (g : SL2 (LaurentSeries F))
    (hg : g ∈ laurentIwahori F) :
    ∃ p : Polynomial F, p.degree < 2*n+1 ∧ ∃ j ∈ laurentIwahori F,
      g * sl2WeylLower (laurentXUnit F ^ (n+1)) =
        sl2Lower ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F) *
          sl2WeylLower (laurentXUnit F ^ (n+1)) * j := by
  obtain ⟨l,a,u,hl,hg⟩ := exists_laurent_lower_gauss F g hg
  obtain ⟨p,t,hp,hlp⟩ := exists_lower_head F (2*n+1) l hl
  have hn : 2*n+1+1 = 2*(n+1) := by omega
  rw [hn] at hlp
  have hlu : PowerSeries.constantCoeff (-(PowerSeries.X^(2*(n+1))*u)) = 0 := by
    rw [map_neg,map_mul,map_pow,PowerSeries.constantCoeff_X,zero_pow (by omega),zero_mul,neg_zero]
  let j := sl2Upper ((-t:PowerSeries F):LaurentSeries F) *
    sl2Diagonal ((powerSeriesLaurentUnit F a)⁻¹) *
      sl2Lower ((-(PowerSeries.X^(2*(n+1))*u):PowerSeries F):LaurentSeries F)
  have hj : j ∈ laurentIwahori F :=
    (laurentIwahori F).mul_mem ((laurentIwahori F).mul_mem (upper_series_mem F _)
      (diagonal_inverse_mem F a)) (lower_series_mem F _ hlu)
  have hlc : (l:LaurentSeries F) =
      ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F) +
        (((laurentXUnit F ^ (n+1):(LaurentSeries F)ˣ):LaurentSeries F)^2) * (t:LaurentSeries F) := by
    rw [monomial_square_series,←map_add]
    exact congrArg (HahnSeries.ofPowerSeries ℤ F) hlp
  refine ⟨p,hp,j,hj,?_⟩
  have ht : sl2Upper (-(t:LaurentSeries F)) *
      sl2Diagonal ((powerSeriesLaurentUnit F a)⁻¹) *
        sl2Lower (-((((laurentXUnit F ^ (n+1):(LaurentSeries F)ˣ):LaurentSeries F)^2) *
          (u:LaurentSeries F))) = j := by
    dsimp only [j]
    rw [monomial_square_series, map_neg, map_neg]
  calc
    _ = (sl2Lower (l:LaurentSeries F) * sl2Diagonal (powerSeriesLaurentUnit F a) *
        sl2Upper (u:LaurentSeries F)) * sl2WeylLower (laurentXUnit F ^ (n+1)) :=
      congrArg (fun z : SL2 (LaurentSeries F) => z * sl2WeylLower (laurentXUnit F ^ (n+1))) hg
    _ = _ := (congrArg (fun z : LaurentSeries F => sl2Lower z *
      sl2Diagonal (powerSeriesLaurentUnit F a) * sl2Upper (u:LaurentSeries F) *
        sl2WeylLower (laurentXUnit F ^ (n+1))) hlc).trans
      ((lower_reflection_factor (powerSeriesLaurentUnit F a) (laurentXUnit F ^ (n+1))
        ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F)
        (t:LaurentSeries F) (u:LaurentSeries F)).trans
        (congrArg (fun z : SL2 (LaurentSeries F) =>
          sl2Lower ((PowerSeries.X*(p:PowerSeries F):PowerSeries F):LaurentSeries F) *
            sl2WeylLower (laurentXUnit F ^ (n+1)) * z) ht))

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_lower_polynomial_translation_cell
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_upper_polynomial_reflection_cell
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.exists_lower_polynomial_reflection_cell
