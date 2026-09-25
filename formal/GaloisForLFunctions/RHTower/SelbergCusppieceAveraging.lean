import GaloisForLFunctions.RHTower.SelbergCellCosetShift

open MeasureTheory UpperHalfPlane ModularGroup Set
open scoped MatrixGroups Pointwise

/-!
# Averaging the `N` width-one cusp pieces of the `Γ(N)` cell into one period

The cosets `Γ̄(N)\PSL(2,ℤ)` are finite (`finite_cosets`). For a weight `w` invariant under the right `T`-shift,
`N Σ_c w_c f_c = Σ_c w_c Σ_{j<N} f(cT^j)` (`avg_sum`: each shift permutes the cosets). For `Γ(N)`-invariant `F`,
`F(R_{cT^j} w) = F(R_c(w + j))` (`F_out_iterate`), so the `N` shifted width-one horizontal integrals
`∫_{-1/2}^{1/2} F(R_{cT^j}(x + iy)) dx` add up to one period `∫_0^N F(R_c(x + iy)) dx` (`sum_shift_integral`).
-/

namespace GaloisForLFunctions.RHTower.SelbergCusppieceAveraging
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace
  GaloisForLFunctions.RHTower.SelbergCellCosetShift
open CongruenceSubgroup

variable (N : ℕ) [NeZero N]

theorem finite_cosets : Finite (Cosets N) := by
  have hd := Subgroup.index_map_dvd (Gamma N) (f := QuotientGroup.mk' modularActionKernel)
    (QuotientGroup.mk'_surjective _)
  have hne : (gammaBar N).index ≠ 0 := by
    intro h0
    have : (Gamma N).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    exact this (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))
  haveI : (gammaBar N).FiniteIndex := ⟨hne⟩
  exact Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (gammaBar N)).symm

noncomputable instance fintypeCosets : Fintype (Cosets N) :=
  haveI := finite_cosets N; Fintype.ofFinite _

omit [NeZero N] in
theorem iterate_sh_eq (j : ℕ) : ⇑((shEquiv N) ^ j) = (sh N)^[j] := by
  rw [Equiv.Perm.coe_pow]; rfl

/-- **Averaging over the `T`-shift**: for a shift-invariant weight `w`,
`N Σ_c w_c f_c = Σ_c w_c Σ_{j<N} f(cT^j)`. -/
theorem avg_sum (f w : Cosets N → ℂ) (hw : ∀ c, w (sh N c) = w c) :
    (N : ℂ) * ∑ c, w c * f c = ∑ c, w c * ∑ j ∈ Finset.range N, f ((sh N)^[j] c) := by
  have hwj : ∀ j c, w ((sh N)^[j] c) = w c := by
    intro j
    induction j with
    | zero => intro c; rfl
    | succ j ih => intro c; rw [Function.iterate_succ_apply', hw, ih]
  have hj : ∀ j, ∑ c, w c * f ((sh N)^[j] c) = ∑ c, w c * f c := by
    intro j
    have := Equiv.sum_comp ((shEquiv N) ^ j) (fun c => w c * f c)
    rw [iterate_sh_eq] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro c _
    rw [hwj]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hj]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]

omit [NeZero N] in
/-- `F(R_{cT^j} w) = F(R_c(w + j))` for `Γ(N)`-invariant `F`. -/
theorem F_out_iterate {F : ℍ → ℂ} (hF : ∀ (γ : Gamma N) z, F ((γ : SL(2, ℤ)) • z) = F z) (j : ℕ)
    (c : Cosets N) (w : ℍ) :
    F ((Quotient.out ((sh N)^[j] c) : PSL2Z) • w) = F ((Quotient.out c : PSL2Z) • ((T ^ (j : ℤ)) • w)) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, F_out_sh N hF, ← mul_smul]
    congr 3
    rw [show ((j + 1 : ℕ) : ℤ) = 1 + j by push_cast; ring, zpow_add, zpow_one]

/-- The point `x + iy`. -/
def pt (x y : ℝ) (hy : 0 < y) : ℍ := ⟨(x : ℂ) + (y : ℂ) * Complex.I, by simpa using hy⟩

theorem T_zpow_pt (x y : ℝ) (hy : 0 < y) (j : ℤ) : (T ^ j) • pt x y hy = pt (x + j) y hy := by
  rw [modular_T_zpow_smul]
  ext
  simp [pt, UpperHalfPlane.coe_vadd]
  ring

omit [NeZero N] in
/-- **The `N` shifted width-one pieces make a full period.** -/
theorem sum_shift_integral {F : ℍ → ℂ} (hF : ∀ (γ : Gamma N) z, F ((γ : SL(2, ℤ)) • z) = F z) (c : Cosets N)
    {y : ℝ} (hy : 0 < y)
    (hint : IntervalIntegrable (fun x => F ((Quotient.out c : PSL2Z) • pt x y hy)) volume (-1 / 2) (N - 1 / 2)) :
    ∑ j ∈ Finset.range N, ∫ x in (-1 / 2 : ℝ)..(1 / 2), F ((Quotient.out ((sh N)^[j] c) : PSL2Z) • pt x y hy) =
      ∫ x in (0 : ℝ)..N, F ((Quotient.out c : PSL2Z) • pt x y hy) := by
  set G : ℝ → ℂ := fun x => F ((Quotient.out c : PSL2Z) • pt x y hy)
  have hG : ∀ j : ℕ, (fun x => F ((Quotient.out ((sh N)^[j] c) : PSL2Z) • pt x y hy)) = fun x => G (x + j) := by
    intro j; funext x
    rw [F_out_iterate N hF, T_zpow_pt]
    simp [G]
  have hper : Function.Periodic G N := by
    intro x
    simp only [G]
    have e : pt (x + N) y hy = T ^ (N : ℤ) • pt x y hy := by rw [T_zpow_pt]; simp
    rw [e]
    exact F_out_periodic N hF c (pt x y hy)
  simp_rw [hG, intervalIntegral.integral_comp_add_right]
  have e : ∀ j ∈ Finset.range N, ∫ x in (-1 / 2 + (j : ℝ))..(1 / 2 + j), G x =
      ∫ x in ((fun k : ℕ => (k : ℝ) - 1 / 2) j)..((fun k : ℕ => (k : ℝ) - 1 / 2) (j + 1)), G x := by
    intro j _; congr 1 <;> push_cast <;> ring
  rw [Finset.sum_congr rfl e, intervalIntegral.sum_integral_adjacent_intervals]
  · simp only [Nat.cast_zero, zero_sub]
    have := hper.intervalIntegral_add_eq (-(1 / 2)) 0
    rw [show (-(1 / 2) : ℝ) + N = (N : ℝ) - 1 / 2 by ring, zero_add] at this
    exact this
  · intro k hk
    refine hint.mono_set ?_
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    rw [Set.uIcc_of_le (show (-1 / 2 : ℝ) ≤ N - 1 / 2 by linarith),
      Set.uIcc_of_le (show (k : ℝ) - 1 / 2 ≤ ((k + 1 : ℕ) : ℝ) - 1 / 2 by push_cast; linarith)]
    intro x hx
    constructor
    · have := hx.1; linarith
    · have := hx.2; push_cast at this; linarith

end GaloisForLFunctions.RHTower.SelbergCusppieceAveraging
