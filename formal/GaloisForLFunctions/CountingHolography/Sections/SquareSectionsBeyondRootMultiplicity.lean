import GaloisForLFunctions.CountingHolography.Sections.PrimeFloorLossAcrossMultiplicities
import GaloisForLFunctions.CountingHolography.Sections.TheCostsBeforeOrdinaryPrimeRounding

/-!
# Original sections beyond square-root multiplicity

The continuous prime contact has growth controlled by the zero width. A
quadratic saving from the signed floors then pays both quadrature and the
archimedean cost on a whole range of multiplicity scales.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography SquareRootThreshold

/-- Before the ordinary floors, the excess above the original radius is at
most the signed degree bound plus the global mesh error. -/
private theorem square_radius_comparison : ∃ E : ℝ, 1 ≤ E ∧ ∀ {n m : ℕ}, 0 < n → 0 < m →
    let a := m • successorSquareTriple n
    let g := ((n:ℝ)+1)^zetaZeroWidth
    Real.log (generator a : ℝ)-radius a+ordinaryFloorLoss a ≤ E*((m*g)^2+n*m) := by
  obtain ⟨E,hE,h⟩ := square_cost_before_ordinary_floors
  exact ⟨E,hE,fun hn hm => (add_le_add (le_max_right _ _) le_rfl).trans (h hn hm)⟩

/-- Every multiplicity scale up to a fixed multiple of (n+1)^(1-w), where
w is the actual zero width, contains a multiplicity with exponentially many
sections of the original lattice. -/
theorem square_sections_at_width_scales : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ {M : ℕ}, 0 < M → K*(M:ℝ) ≤ ((n:ℝ)+1)^(1-zetaZeroWidth) →
      ∃ m ∈ Icc M (3*M), let a := m • successorSquareTriple n
        Real.log (generator a : ℝ)+(n:ℝ)^2/4608 ≤ radius a ∧
        2*⌊Real.exp ((n:ℝ)^2/4608)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨K,hK,hfloor⟩ := successorSquare_exists_floor_loss
  obtain ⟨E,hE,hcomp⟩ := square_radius_comparison
  let D := K+100000*E
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [hE,hK]
  refine ⟨2*D,by linarith only [hD],?_⟩
  filter_upwards [hfloor,eventually_ge_atTop 1] with n hn hn1
  intro M hM hscale
  let g := ((n:ℝ)+1)^zetaZeroWidth
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hX : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hg : 1 ≤ g := Real.one_le_rpow hX zetaZeroWidth_nonneg
  have hg₀ := zero_le_one.trans hg
  have hprod : ((n:ℝ)+1)^(1-zetaZeroWidth)*g=(n:ℝ)+1 := by
    unfold g
    rw [← Real.rpow_add (zero_lt_one.trans_le hX),sub_add_cancel,Real.rpow_one]
  have hb := mul_le_mul_of_nonneg_right hscale hg₀
  rw [hprod] at hb
  have hDM : D*((M:ℝ)*g) ≤ n := by linarith only [hb,hn']
  have hMK : K*(M:ℝ) ≤ n := by
    have hKD : K ≤ D := by unfold D; linarith only [hE]
    have hm' := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α := ℝ) M)
    linarith only [hDM,mul_le_mul_of_nonneg_right hKD (Nat.cast_nonneg (α := ℝ) M),
      mul_le_mul_of_nonneg_left hm' (zero_le_one.trans hD)]
  obtain ⟨m,hm,hloss⟩ := hn hM hMK
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hm
  let a := m • successorSquareTriple n
  have hm₀ : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have ht : (m:ℝ) ≤ 3*M := by exact_mod_cast hhi
  have hmg := mul_le_mul_of_nonneg_right ht hg₀
  have hMg := mul_nonneg (Nat.cast_nonneg (α := ℝ) M) hg₀
  have hmax : (m:ℝ)*g ≤ 3*n := by
    linarith only [hmg,hDM,mul_le_mul_of_nonneg_right hD hMg]
  have hEm : 100000*E*((m:ℝ)*g) ≤ 3*n := by
    have hED : 100000*E ≤ D := by unfold D; linarith only [hK]
    linarith only [hDM,mul_le_mul_of_nonneg_right hED hMg,
      mul_le_mul_of_nonneg_left hmg (by linarith only [hE] : 0 ≤ 100000*E)]
  have hquad := mul_le_mul hEm hmax (mul_nonneg hm₀ hg₀)
    (by linarith only [hn'] : 0 ≤ 3*(n:ℝ))
  have hlin : 100000*E*(m:ℝ) ≤ 3*n := by
    linarith only [hEm,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hm₀)
      (by linarith only [hE] : 0 ≤ 100000*E)]
  have hc := hcomp hn1 (hM.trans_le hlo)
  change Real.log (generator a : ℝ)-radius a+ordinaryFloorLoss a ≤ E*(((m:ℝ)*g)^2+(n:ℝ)*m) at hc
  have hfit : Real.log (generator a : ℝ)+(n:ℝ)^2/4608 ≤ radius a := by
    linarith only [hc,hloss,hquad,mul_le_mul_of_nonneg_right hlin (Nat.cast_nonneg (α := ℝ) n),sq_nonneg (n:ℝ)]
  refine ⟨m,hm,hfit,?_⟩
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have hexp := Real.exp_le_exp.mpr (show (n:ℝ)^2/4608 ≤ radius a-Real.log (generator a : ℝ) by linarith only [hfit])
  rw [Real.exp_sub,Real.exp_log hpos] at hexp
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.floor_mono hexp)) 1

/-- In particular every scale up to a fixed multiple of n^(5/8) contains
an original section lattice with exponentially many sections. -/
theorem square_sections_through_five_eighths : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop,
    ∀ {M : ℕ}, 0 < M → K*(M:ℝ) ≤ ((n:ℝ)+1)^(5/8:ℝ) →
      ∃ m ∈ Icc M (3*M), let a := m • successorSquareTriple n
        Real.log (generator a : ℝ)+(n:ℝ)^2/4608 ≤ radius a ∧
        2*⌊Real.exp ((n:ℝ)^2/4608)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨K,hK,h⟩ := square_sections_at_width_scales
  refine ⟨K,hK,?_⟩
  filter_upwards [h] with n hn
  intro M hM ht
  exact hn hM (ht.trans (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n))
    (by linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths])))

#print axioms square_sections_at_width_scales
#print axioms square_sections_through_five_eighths

end GaloisForLFunctions.CountingHolography.Sections
