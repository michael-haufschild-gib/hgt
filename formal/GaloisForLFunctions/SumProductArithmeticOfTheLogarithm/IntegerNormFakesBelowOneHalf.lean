import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakesAboveOneHalf
import GaloisForLFunctions.RHTower.BeurlingDeletionRegion
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.ZetaSubconvexStripBound
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator

/-!
# Sub-`1/2` Integer-Norm Beurling Fakes, Quasi-RH Calibration, and Complete Synthesis

This module completes the solution of the integer-norm Beurling fake remainder problem
(Question B182) below the critical exponent `1/2` and synthesizes the unconditional theory:

1. **Deletion-set bridge (`isIntegerNormFakeAt_keptPrimeSystem_of_deletionData`).**
   For any square-root discrepancy prime deletion datum `D : DeletionData α` with `1/2 < α < 1`,
   if `ζ` is nonvanishing on `{Re z > Θ}` with `Θ < 3/2 - α`, the Perron numerator
   `D.perronNum` holomorphically continues `(s - 1) ζ_{ℙ \ D.S}(s)` across `{Re s > 1/2}` and
   vanishes at the real point `s = α ∈ (1/2, 1)` where `ζ(α) ≠ 0`.  Nonemptiness of `D.S` (hence
   `NotNormEquivPrimes (keptPrimeSystem D.S)`) follows automatically from the finite-omission
   obstruction `no_fake_zero_of_finite_missing_primes`.

2. **Sub-`1/2` integer-norm fakes from any zero-free half-plane
   (`exists_integerNormFakeAt_lt_half_of_zeroFree`).**
   If `ζ` has no zeros on `{Re z > Θ}` for some `Θ ∈ [1/2, 1)`, combining the three-circles
   subpolynomial lower bound on `ζ(s + 1 - α)` (`exists_zeta_lower_bound_subpolynomial_of_zeroFree`),
   the unconditional Weyl-interpolated subconvex bound for `ζ(s + 1 - α)`
   (`exists_norm_riemannZeta_le_subconvex`), and the dyadic sawtooth-hyperbola decomposition of
   `D.count` produces a prime-deletion Beurling fake `keptPrimeSystem S` with explicit sub-`1/2`
   remainder exponent `β = 1/2 - (1 - max Θ (3/4)) / 64 < 1/2`.

3. **Sharp `RiemannHypothesis` calibration (`exists_integerNormFakeAt_of_riemannHypothesis`).**
   Under `RiemannHypothesis`, integer-norm prime-deletion fakes exist at every remainder exponent
   `β > 1/3`, so `sInf integerNormFakeExponents ≤ 1/3`.

4. **Unconditional ZFC frontier dichotomy and master synthesis (`integerNormFake_complete_solution`).**
   Unconditionally, `zetaZeroAbscissa = 1 ↔ zetaAsymptoticAbscissa = 1`, and either
   `zetaZeroAbscissa = 1` (which forces `zetaAsymptoticAbscissa = 1` and `AsymptoticAbscissaLaw`),
   or `zetaZeroAbscissa < 1` and sub-`1/2` integer-norm Beurling fakes exist (`sInf < 1/2`).
-/

open Complex Finset Filter Topology Real
open RHTower RHTower.BeurlingDeletion
open GaloisForLFunctions.HTGeometry.TestFunctionPerron GaloisForLFunctions.HTGeometry.SmoothedSawtooth
open GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-! ## 1. Bridging `DeletionData` to `keptPrimeSystem` and `IsIntegerNormFakeAt` -/

theorem sFreeR_eq_sFreeInd {α : ℝ} (D : DeletionData α) (n : ℕ) :
    (sFreeR D.S n : ℂ) = D.sFreeInd n := by
  classical
  unfold sFreeR DeletionData.sFreeInd SFree DeletionData.sFree
  split_ifs <;> simp

theorem countBall_keptPrimeSystem_eq_count {α : ℝ} (D : DeletionData α) {X : ℝ} (hX : 0 ≤ X) :
    ((keptPrimeSystem D.S).countBall X : ℂ) = D.count X := by
  rw [← Complex.ofReal_natCast, countBall_keptPrimeSystem D.S hX, Complex.ofReal_sum,
    DeletionData.count]
  exact Finset.sum_congr rfl fun n _ => sFreeR_eq_sFreeInd D n

theorem perronNum_eq_sub_one_mul_zetaSeriesC {α : ℝ} (D : DeletionData α) (hα0 : 0 < α)
    (hα : α < 1) {s : ℂ} (hs : 1 < s.re) :
    D.perronNum s = (s - 1) * (keptPrimeSystem D.S).zetaSeriesC s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h] at hs; simp at hs
  have hdiv := D.perronNum_div_eq_LSeries hα0 hα hs
  have hcongr : LSeries D.sFreeInd s = LSeries (fun n => (sFreeR D.S n : ℂ)) s :=
    LSeries_congr (fun {n} _ => (sFreeR_eq_sFreeInd D n).symm) s
  rw [zetaSeriesC_keptPrimeSystem D.S hs, ← hcongr, ← hdiv, mul_div_cancel₀ _ hs1]

theorem differentiableOn_perronNum_of_zeroFree {α Θ : ℝ} (D : DeletionData α)
    (hα1 : 1 / 2 < α) (hα : α < 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (hΘα : Θ < 3 / 2 - α) :
    DifferentiableOn ℂ D.perronNum {s : ℂ | 1 / 2 < s.re} := by
  have hα0 : 0 < α := by linarith
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  intro s hs
  have hs_re : 1 / 2 < s.re := hs
  have hsα2 : α / 2 < s.re := by linarith
  have hE : DifferentiableAt ℂ D.eFactor s :=
    (D.differentiableOn_eFactor hα0 hα).differentiableAt (hU.mem_nhds hsα2)
  have hw : Θ < (s + ((1 - α : ℝ) : ℂ)).re := by simp; linarith
  have hzu_ne : zetaResidueUnit (s + ((1 - α : ℝ) : ℂ)) ≠ 0 :=
    zetaResidueUnit_ne_zero_of_zeroFree hzf hw
  have hz' : DifferentiableAt ℂ (fun z : ℂ => zetaResidueUnit (z + ((1 - α : ℝ) : ℂ))) s :=
    (analyticAt_zetaResidueUnit _).differentiableAt.comp s (differentiableAt_id.add_const _)
  have hQ : DifferentiableAt ℂ (DeletionData.qFactor α) s :=
    (differentiableAt_id.sub_const _).div hz' hzu_ne
  exact (((analyticAt_zetaResidueUnit s).differentiableAt.mul hE).mul hQ).differentiableWithinAt

theorem perronNum_self_eq_zero {α : ℝ} (D : DeletionData α) :
    D.perronNum (α : ℂ) = 0 := by
  unfold DeletionData.perronNum DeletionData.qFactor
  rw [sub_self, zero_div, mul_zero]

/-- Any `DeletionData α` (`1/2 < α < 1`) whose shifted denominator `ζ_u(s + 1 - α)` is nonvanishing
on `{Re s > 1/2}` (via a zero-free half-plane `{Re z > Θ}` with `Θ < 3/2 - α`) and whose counting
function `D.count` satisfies a linear asymptotic with remainder `O(X^β)` (`β < 1`) yields an
integer-norm Beurling fake `keptPrimeSystem D.S` at exponent `β`. -/
theorem isIntegerNormFakeAt_keptPrimeSystem_of_deletionData {α Θ β C : ℝ} {z : ℂ}
    (D : DeletionData α) (hα1 : 1 / 2 < α) (hα : α < 1)
    (hzf : ∀ w : ℂ, Θ < w.re → riemannZeta w ≠ 0) (hΘα : Θ < 3 / 2 - α)
    (hβ1 : β < 1)
    (hcnt : ∀ X : ℝ, 1 ≤ X → ‖D.count X - z * X‖ ≤ C * X ^ β) :
    IsIntegerNormFakeAt (keptPrimeSystem D.S) β := by
  set A : ℝ := z.re
  set C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hreal_cnt : ∀ X : ℝ, 1 ≤ X →
      |((keptPrimeSystem D.S).countBall X : ℝ) - A * X| ≤ C' * X ^ β := by
    intro X hX
    have hX0 : 0 ≤ X := by linarith
    have hre_eq : ((keptPrimeSystem D.S).countBall X : ℝ) - A * X =
        (D.count X - z * X).re := by
      rw [← countBall_keptPrimeSystem_eq_count D hX0]
      simp [A]
    calc |((keptPrimeSystem D.S).countBall X : ℝ) - A * X|
        = |(D.count X - z * X).re| := by rw [hre_eq]
      _ ≤ ‖D.count X - z * X‖ := Complex.abs_re_le_norm _
      _ ≤ C * X ^ β := hcnt X hX
      _ ≤ C' * X ^ β := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hA0 : 0 ≤ A := by
    by_contra hneg
    push Not at hneg
    have hlim : Tendsto (fun X : ℝ => A + C' * X ^ (β - 1)) atTop (𝓝 A) := by
      have h0 : Tendsto (fun X : ℝ => X ^ (β - 1)) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := 1 - β) (by linarith)
        simpa [neg_sub] using this
      simpa using tendsto_const_nhds.add (h0.const_mul C')
    have hev : ∀ᶠ X : ℝ in atTop, A + C' * X ^ (β - 1) < 0 :=
      hlim.eventually (Iio_mem_nhds hneg)
    obtain ⟨X, hlt, hX1⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
    have hX0 : 0 < X := by linarith
    have hprod_lt : (A + C' * X ^ (β - 1)) * X < 0 :=
      mul_neg_of_neg_of_pos hlt hX0
    have hpow_eq : X ^ (β - 1) * X = X ^ β := by
      rw [← Real.rpow_add_one hX0.ne', sub_add_cancel]
    have hlin_lt : A * X + C' * X ^ β < 0 := by
      calc A * X + C' * X ^ β = (A + C' * X ^ (β - 1)) * X := by
            rw [add_mul, mul_assoc, hpow_eq]
        _ < 0 := hprod_lt
    have hball_le : ((keptPrimeSystem D.S).countBall X : ℝ) ≤ A * X + C' * X ^ β := by
      have habs := (abs_le.mp (hreal_cnt X hX1)).2
      linarith
    have hball_nn : (0 : ℝ) ≤ ((keptPrimeSystem D.S).countBall X : ℝ) := Nat.cast_nonneg _
    linarith
  have hGd : DifferentiableOn ℂ D.perronNum {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_perronNum_of_zeroFree D hα1 hα hzf hΘα
  have hGeq : ∀ s : ℂ, 1 < s.re →
      D.perronNum s = (s - 1) * (keptPrimeSystem D.S).zetaSeriesC s :=
    fun s hs => perronNum_eq_sub_one_mul_zetaSeriesC D (by linarith) hα hs
  have hρ_re : 1 / 2 < ((α : ℂ)).re := by simpa using hα1
  have hρ_ne1 : (α : ℂ) ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    simp at this
    linarith
  have hG0 : D.perronNum (α : ℂ) = 0 := perronNum_self_eq_zero D
  have hζ_ne : riemannZeta (α : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_abs_im_lt_four (by simpa using (show 0 < α by linarith))
      (by simpa using hα) (by simp)
  have hS_ne : D.S.Nonempty := by
    by_contra hS_emp
    have hS_eq : D.S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_emp
    have hFin : {p : ℕ | p.Prime ∧
        ∀ l : (keptPrimeSystem D.S).Label, (keptPrimeSystem D.S).labelNorm l ≠ p}.Finite := by
      refine Set.finite_empty.subset ?_
      rintro p ⟨hpP, hall⟩
      have hp_not : p ∉ D.S := by simp [hS_eq]
      exact hall ⟨p, hpP, hp_not⟩ rfl
    have hiff := no_fake_zero_of_finite_missing_primes (hasIntegerNorms_keptPrimeSystem D.S)
      (isDiscrete_keptPrimeSystem D.S) (hasLinearCounting_keptPrimeSystem D.S) hFin hGd hGeq
      hρ_re hρ_ne1
    exact hζ_ne (hiff.mp hG0)
  obtain ⟨p₀, hp₀⟩ := hS_ne
  exact ⟨hasIntegerNorms_keptPrimeSystem D.S, isDiscrete_keptPrimeSystem D.S,
    notNormEquivPrimes_keptPrimeSystem (D.prime p₀ hp₀) hp₀,
    ⟨A, C', hA0, hreal_cnt⟩,
    D.perronNum, hGd, hGeq, (α : ℂ), hρ_re, hρ_ne1, hG0, hζ_ne⟩

/-! ## 2. Sub-`1/2` integer-norm fakes from a zero-free half-plane `Re z > Θ` (`Θ < 1`) -/

private theorem differentiableOn_eFactor_mul_qFactor_of_zeroFree {α Θ a₀ : ℝ}
    (D : DeletionData α) (hα0 : 0 < α) (hα : α < 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    (ha₀ : α / 2 < a₀) (hΘa : Θ < a₀ + (1 - α)) :
    DifferentiableOn ℂ (fun s => D.eFactor s * DeletionData.qFactor α s) {s : ℂ | a₀ < s.re} := by
  have hU : IsOpen {s : ℂ | α / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  intro s hs
  have hs_re : a₀ < s.re := hs
  have hsα2 : α / 2 < s.re := lt_trans ha₀ hs_re
  have hE : DifferentiableAt ℂ D.eFactor s :=
    (D.differentiableOn_eFactor hα0 hα).differentiableAt (hU.mem_nhds hsα2)
  have hw : Θ < (s + ((1 - α : ℝ) : ℂ)).re := by simp; linarith
  have hzu_ne : zetaResidueUnit (s + ((1 - α : ℝ) : ℂ)) ≠ 0 :=
    zetaResidueUnit_ne_zero_of_zeroFree hzf hw
  have hz' : DifferentiableAt ℂ (fun z : ℂ => zetaResidueUnit (z + ((1 - α : ℝ) : ℂ))) s :=
    (analyticAt_zetaResidueUnit _).differentiableAt.comp s (differentiableAt_id.add_const _)
  have hQ : DifferentiableAt ℂ (DeletionData.qFactor α) s :=
    (differentiableAt_id.sub_const _).div hz' hzu_ne
  exact (hE.mul hQ).differentiableWithinAt

private theorem exists_norm_eFactor_mul_qFactor_le_of_zeroFree {α Θ' δ σ₀ τ : ℝ}
    (D : DeletionData α) (hα0 : 0 < α) (hα : α < 1)
    (hΘ' : 1 / 2 ≤ Θ') (hΘ'1 : Θ' ≤ 1)
    (hzf' : ∀ z : ℂ, Θ' < z.re → riemannZeta z ≠ 0)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hσ₀ : α / 2 < σ₀) (hshift : Θ' + δ ≤ σ₀ + (1 - α))
    (hτ : 0 < τ) :
    ∃ c_eq : ℝ, 0 < c_eq ∧ ∀ s : ℂ, σ₀ ≤ s.re → 6 ≤ |s.im| →
      ‖D.eFactor s * DeletionData.qFactor α s‖ ≤ c_eq * (|s.im| + 3) ^ (2 * τ) := by
  obtain ⟨c₁, hc₁, hE⟩ := D.exists_norm_eFactor_le hα0 hα (δ := σ₀ - α / 2) (by linarith) hτ
  obtain ⟨κ, hκ0, hζ⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree hΘ' hΘ'1 hzf' hδ hδ1 hτ
  refine ⟨c₁ * κ⁻¹, by positivity, fun s hs ht => ?_⟩
  have hsα : s ≠ (α : ℂ) := by
    intro h
    rw [h] at ht
    simp at ht
    linarith
  have hw_re : Θ' + δ ≤ (s + ((1 - α : ℝ) : ℂ)).re := by simp; linarith
  have hw_im : 6 ≤ |(s + ((1 - α : ℝ) : ℂ)).im| := by simpa using ht
  have hlow := hζ (s + ((1 - α : ℝ) : ℂ)) hw_re hw_im
  have him_eq : |(s + ((1 - α : ℝ) : ℂ)).im| = |s.im| := by simp
  rw [him_eq] at hlow
  have hu_pos : 0 < 2 + |s.im| := by positivity
  have hζ_pos : 0 < ‖riemannZeta (s + ((1 - α : ℝ) : ℂ))‖ :=
    lt_of_lt_of_le (by positivity) hlow
  have hQ_le : ‖DeletionData.qFactor α s‖ ≤ κ⁻¹ * (|s.im| + 3) ^ τ := by
    rw [DeletionData.qFactor_eq hsα, norm_inv]
    calc (‖riemannZeta (s + ((1 - α : ℝ) : ℂ))‖)⁻¹
        ≤ (κ * (2 + |s.im|) ^ (-τ))⁻¹ := (inv_le_inv₀ hζ_pos (by positivity)).mpr hlow
      _ = κ⁻¹ * (2 + |s.im|) ^ τ := by rw [mul_inv, Real.rpow_neg hu_pos.le, inv_inv]
      _ ≤ κ⁻¹ * (|s.im| + 3) ^ τ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hu_pos.le (by linarith) hτ.le) (by positivity)
  have hE_le : ‖D.eFactor s‖ ≤ c₁ * (|s.im| + 3) ^ τ := by
    have h1 := hE s (by linarith)
    exact h1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hτ.le) hc₁.le)
  rw [norm_mul]
  calc ‖D.eFactor s‖ * ‖DeletionData.qFactor α s‖
      ≤ (c₁ * (|s.im| + 3) ^ τ) * (κ⁻¹ * (|s.im| + 3) ^ τ) :=
        mul_le_mul hE_le hQ_le (norm_nonneg _) (by positivity)
    _ = c₁ * κ⁻¹ * ((|s.im| + 3) ^ τ * (|s.im| + 3) ^ τ) := by ring
    _ = c₁ * κ⁻¹ * (|s.im| + 3) ^ (2 * τ) := by
        rw [← Real.rpow_add (by positivity), show τ + τ = 2 * τ by ring]

private theorem exists_mobS_bounds_of_zeroFree {α a₀ σ₀ τ ε θ_M c_eq : ℝ}
    (D : DeletionData α) (hα0 : 0 < α) (hα : α < 1)
    (haσ : a₀ < σ₀) (hσ₀0 : 0 < σ₀) (hσ₀1 : σ₀ < 1)
    (hτ0 : 0 < τ) (h2τ1 : 2 * τ < 1) (h2τε : 2 * τ ≤ ε) (hε1 : ε < 1)
    (hθ_exp : (2 * τ + σ₀) / (1 + 2 * τ) + τ ≤ θ_M)
    (hDiff : DifferentiableOn ℂ (fun s => D.eFactor s * DeletionData.qFactor α s)
      {s : ℂ | a₀ < s.re})
    (hEQ : ∀ s : ℂ, σ₀ ≤ s.re → 6 ≤ |s.im| →
      ‖D.eFactor s * DeletionData.qFactor α s‖ ≤ c_eq * (|s.im| + 3) ^ (2 * τ)) :
    ∃ (CM K₁ CA : ℝ), 0 ≤ CM ∧ 0 ≤ K₁ ∧ 0 ≤ CA ∧
      (∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ CM * Y ^ θ_M) ∧
      (∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
        ‖∑' n, D.mobS n * g (n / M)‖ ≤ K₁ * M ^ σ₀ * DeletionData.lineMass g σ₀ ε) ∧
      (∀ M : ℝ, 1 ≤ M → ‖D.mainSum M - D.mobSum‖ ≤ CA * M ^ (σ₀ - 1)) := by
  have hcont : ∀ s : ℂ, a₀ < s.re →
      ContinuousAt (fun s => D.eFactor s * DeletionData.qFactor α s) s := fun s hs =>
    (hDiff.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).continuousAt
  obtain ⟨K_st, hK_st⟩ := DeletionData.exists_strip_bound
    (G := fun s => D.eFactor s * DeletionData.qFactor α s)
    (σ₀ := σ₀) (σ₁ := 3 / 2) (fun s h1 _ _ => hcont s (lt_of_lt_of_le haσ h1))
    (by positivity : (0 : ℝ) ≤ 2 * τ) (T := 6) (fun s h1 _ h3 => hEQ s h1 h3)
  have hlinecont : Continuous fun t : ℝ =>
      ‖D.eFactor ((σ₀ : ℂ) + t * I) * DeletionData.qFactor α ((σ₀ : ℂ) + t * I)‖ :=
    (continuous_iff_continuousAt.mpr fun t => (hcont _ (by simp [haσ])).comp (by fun_prop)).norm
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_line hlinecont (by positivity : (0 : ℝ) ≤ 2 * τ)
    (K := K_st) (T := 1) fun t ht => by
      have h := hK_st ((σ₀ : ℂ) + t * I) (by simp) (by simp; linarith) (by simpa using ht)
      simpa using h
  -- (1) Partial sums of `D.mobS` via smoothed Perron.
  have hH : DifferentiableOn ℂ (fun s => (s - 1) * (D.eFactor s * DeletionData.qFactor α s))
      {s : ℂ | a₀ < s.re} :=
    (differentiableOn_id.sub_const 1).mul hDiff
  have hdiv : ∀ s : ℂ, s ≠ 1 → (s - 1) * (D.eFactor s * DeletionData.qFactor α s) / (s - 1) =
      D.eFactor s * DeletionData.qFactor α s := fun s hs => by
    field_simp [sub_ne_zero.mpr hs]
  obtain ⟨C_raw, hC_raw⟩ := GaloisForLFunctions.HTGeometry.SmoothedPerron.exists_norm_sum_sub_le
    D.mobS D.mobS_zero D.norm_mobS_le (a := a₀) (σ₀ := σ₀) haσ hσ₀0 hσ₀1 hH
    (fun s hs => by
      rw [hdiv s (fun h => by rw [h] at hs; simp at hs), D.LSeries_mobS_eq hα0 hα hs])
    (K := K_st) (T₀ := 1) (κ₁ := 2 * τ) (by linarith)
    (fun s h1 h2 h3 => by
      have hs1 : s ≠ 1 := fun h => by rw [h] at h3; norm_num at h3
      rw [hdiv s hs1]; exact hK_st s h1 h2 h3)
    (K₀ := K₀) (θ := 2 * τ) (by positivity) h2τ1
    (fun t => by
      have hs1 : (σ₀ : ℂ) + t * I ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      rw [hdiv _ hs1]; exact hK₀ t)
    (κ := τ) hτ0
  set CM : ℝ := max C_raw 0
  have hCM0 : 0 ≤ CM := le_max_right _ _
  have hCM : ∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ CM * Y ^ θ_M := by
    intro Y hY
    have h := hC_raw Y hY
    have hH1 : (1 - 1) * (D.eFactor 1 * DeletionData.qFactor α 1) = 0 := by ring
    rw [hH1, zero_mul, sub_zero] at h
    calc ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖
        ≤ C_raw * Y ^ ((2 * τ + σ₀) / (1 + 2 * τ) + τ) := h
      _ ≤ CM * Y ^ ((2 * τ + σ₀) / (1 + 2 * τ) + τ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ CM * Y ^ θ_M :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY hθ_exp) hCM0
  -- (2) Smooth sums of `D.mobS` at `(σ₀, ε)` via `TestFunctionPerron.norm_tsum_sub_residue_le`.
  have hK_st_ge0 : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
      ‖D.eFactor s * DeletionData.qFactor α s‖ ≤ max K_st 0 * |s.im| ^ ε := by
    intro s h1 h2 h3
    calc ‖D.eFactor s * DeletionData.qFactor α s‖
        ≤ K_st * |s.im| ^ (2 * τ) := hK_st s h1 h2 h3
      _ ≤ max K_st 0 * |s.im| ^ (2 * τ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max K_st 0 * |s.im| ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h3 h2τε) (le_max_right _ _)
  have hK₀_ε : ∀ t : ℝ,
      ‖D.eFactor ((σ₀ : ℂ) + t * I) * DeletionData.qFactor α ((σ₀ : ℂ) + t * I)‖ ≤
        K₀ * (|t| + 1) ^ ε := by
    intro t
    have ht1 : 1 ≤ |t| + 1 := by linarith [abs_nonneg t]
    exact (hK₀ t).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht1 h2τε) hK₀0)
  set K₁ : ℝ := K₀ / (2 * π)
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₁ : ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.mobS n * g (n / M)‖ ≤ K₁ * M ^ σ₀ * DeletionData.lineMass g σ₀ ε := by
    intro g a b hg M hM
    have h := norm_tsum_sub_residue_le hg D.mobS D.mobS_zero D.norm_mobS_le (A := 0) (ρ := 1)
      (G₀ := fun s => D.eFactor s * DeletionData.qFactor α s) (a₀ := a₀) (σ₀ := σ₀) haσ
      (by simp; linarith) (by norm_num) hDiff
      (fun s hs => by rw [zero_div, zero_add, D.LSeries_mobS_eq hα0 hα hs])
      (by linarith : 0 ≤ ε) hε1 (K := max K_st 0)
      (fun s h1 h2 h3 => by rw [zero_div, zero_add]; exact hK_st_ge0 s h1 h2 h3)
      (K₀ := K₀) (fun t => by rw [zero_div, zero_add]; exact hK₀_ε t) hM
    rw [zero_mul, zero_mul, sub_zero] at h
    calc _ ≤ _ := h
      _ = K₁ * M ^ σ₀ * DeletionData.lineMass g σ₀ ε := by
          unfold DeletionData.lineMass; dsimp [K₁]; ring
  -- (3) Telescoping `D.mainSum M - D.mobSum`.
  obtain ⟨L₃, hL₃⟩ : ∃ L₃ : ℝ, L₃ = DeletionData.lineMass bumpDivC σ₀ ε := ⟨_, rfl⟩
  have hL₃0 : 0 ≤ L₃ := hL₃ ▸ MeasureTheory.integral_nonneg fun _ => by positivity
  set r : ℝ := (2 : ℝ) ^ (σ₀ - 1) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set CA : ℝ := K₁ * L₃ / (1 - r)
  have hCA0 : 0 ≤ CA := by have := sub_pos.mpr hr1; positivity
  have hCA : ∀ M : ℝ, 1 ≤ M → ‖D.mainSum M - D.mobSum‖ ≤ CA * M ^ (σ₀ - 1) := by
    intro M hM
    have hM0 : 0 < M := by linarith
    have hstep : ∀ j : ℕ, ‖D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M)‖ ≤
        K₁ * L₃ * M ^ (σ₀ - 1) * r ^ j := by
      intro j
      have hMj : 0 < 2 ^ j * M := by positivity
      rw [show (2 : ℝ) ^ (j + 1) * M = 2 * (2 ^ j * M) by ring, D.mainSum_two_mul_sub hMj,
        norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMj]
      have h := hK₁ bumpDivC 1 4 isTest_bumpDivC (2 ^ j * M) hMj
      rw [← hL₃] at h
      calc (2 ^ j * M)⁻¹ * ‖∑' m : ℕ, D.mobS m * bumpDivC (m / (2 ^ j * M))‖
          ≤ (2 ^ j * M)⁻¹ * (K₁ * (2 ^ j * M) ^ σ₀ * L₃) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = K₁ * L₃ * (2 ^ j * M) ^ (σ₀ - 1) := by
            rw [Real.rpow_sub hMj, Real.rpow_one]; field_simp
        _ = K₁ * L₃ * M ^ (σ₀ - 1) * r ^ j := by
            rw [Real.mul_rpow (by positivity) hM0.le, hr, ← Real.rpow_natCast,
              ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
            ring_nf
    have hpartial : ∀ J : ℕ, ‖D.mainSum M - D.mainSum (2 ^ J * M)‖ ≤
        K₁ * L₃ * M ^ (σ₀ - 1) / (1 - r) := by
      intro J
      have htel : D.mainSum M - D.mainSum (2 ^ J * M) =
          -∑ j ∈ Finset.range J, (D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M)) := by
        rw [Finset.sum_range_sub (fun j => D.mainSum (2 ^ j * M))]; simp
      rw [htel, norm_neg]
      have hgeom : ∑ j ∈ Finset.range J, r ^ j ≤ 1 / (1 - r) := by
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0.le hr1
        rwa [pow_zero, ← Finset.range_eq_Ico] at this
      have hK_nn : 0 ≤ K₁ * L₃ * M ^ (σ₀ - 1) := by positivity
      calc ‖∑ j ∈ Finset.range J, (D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M))‖
          ≤ ∑ j ∈ Finset.range J, ‖D.mainSum (2 ^ (j + 1) * M) - D.mainSum (2 ^ j * M)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range J, K₁ * L₃ * M ^ (σ₀ - 1) * r ^ j :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = K₁ * L₃ * M ^ (σ₀ - 1) * ∑ j ∈ Finset.range J, r ^ j := by rw [Finset.mul_sum]
        _ ≤ K₁ * L₃ * M ^ (σ₀ - 1) * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hK_nn
        _ = K₁ * L₃ * M ^ (σ₀ - 1) / (1 - r) := by ring
    have hlim : Tendsto (fun J : ℕ => ‖D.mainSum M - D.mainSum (2 ^ J * M)‖) atTop
        (𝓝 ‖D.mainSum M - D.mobSum‖) :=
      (tendsto_const_nhds.sub (D.tendsto_mainSum hα0 hα M hM0)).norm
    calc ‖D.mainSum M - D.mobSum‖ ≤ K₁ * L₃ * M ^ (σ₀ - 1) / (1 - r) :=
          le_of_tendsto' hlim hpartial
      _ = CA * M ^ (σ₀ - 1) := by dsimp [CA]; ring
  exact ⟨CM, K₁, CA, hCM0, hK₁0, hCA0, hCM, hK₁, hCA⟩

private theorem exists_norm_riemannZeta_shift_le_subconvex {c : ℝ} (hc0 : 0 < c) (hc_le : c ≤ 1 / 32) :
    ∃ C_ζ : ℝ, 0 < C_ζ ∧
      ∀ s : ℂ, 1 / 2 - c ≤ s.re → 8 ≤ |s.im| →
        ‖riemannZeta (s + ((1 - (1 / 2 + c / 8) : ℝ) : ℂ))‖ ≤
          C_ζ * (|s.im| + 3) ^ (7 * c / 16) := by
  obtain ⟨C_sub, hC_sub, hsub⟩ :=
    exists_norm_riemannZeta_le_subconvex (η := c / 8) (by positivity) (by linarith)
  refine ⟨max C_sub (1 + 8 / c), lt_of_lt_of_le hC_sub (le_max_left _ _), fun s hs_re hs_im => ?_⟩
  set w : ℂ := s + ((1 - (1 / 2 + c / 8) : ℝ) : ℂ)
  have hw_re : 1 - 9 * c / 8 ≤ w.re := by simp [w]; linarith
  have hw_half : 1 / 2 ≤ w.re := by linarith
  have hw_im : w.im = s.im := by simp [w]
  have ht1 : 1 ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
  rcases le_or_gt w.re (1 + c / 8) with hw_hi | hw_gt
  · have hexp_le : (1 / 6 + c / 8) * (1 + c / 8 - w.re) / (1 / 2 + c / 8) ≤ 7 * c / 16 := by
      rw [div_le_iff₀ (by linarith)]
      have h1 : 1 / 6 + c / 8 ≤ 131 / 768 := by linarith
      have h2 : 1 + c / 8 - w.re ≤ 5 * c / 4 := by linarith
      calc (1 / 6 + c / 8) * (1 + c / 8 - w.re)
          ≤ (131 / 768) * (5 * c / 4) := mul_le_mul h1 h2 (by linarith) (by norm_num)
        _ ≤ 7 * c / 16 * (1 / 2) := by linarith
        _ ≤ 7 * c / 16 * (1 / 2 + c / 8) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hnorm_w : ‖riemannZeta w‖ ≤
        C_sub * |s.im| ^ ((1 / 6 + c / 8) * (1 + c / 8 - w.re) / (1 / 2 + c / 8)) := by
      rcases le_or_gt 0 s.im with him0 | him_neg
      · have hw_eq : ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + (s.im : ℂ) * I)‖ := by
          congr 2
          conv_lhs => rw [← Complex.re_add_im w]
          rw [hw_im]
        rw [abs_of_nonneg him0] at hs_im ⊢
        rw [hw_eq]
        exact hsub w.re s.im hw_half hw_hi hs_im
      · have hw_eq : ‖riemannZeta w‖ = ‖riemannZeta ((w.re : ℂ) + ((-s.im : ℝ) : ℂ) * I)‖ := by
          have hw_conj : w = starRingEnd ℂ ((w.re : ℂ) + ((-s.im : ℝ) : ℂ) * I) := by
            apply Complex.ext <;> simp [hw_im]
          conv_lhs => rw [hw_conj, riemannZeta_conj, Complex.norm_conj]
        rw [abs_of_neg him_neg] at hs_im ⊢
        rw [hw_eq]
        exact hsub w.re (-s.im) hw_half hw_hi hs_im
    have hs1 : 1 ≤ |s.im| := by linarith
    calc ‖riemannZeta w‖
        ≤ C_sub * |s.im| ^ ((1 / 6 + c / 8) * (1 + c / 8 - w.re) / (1 / 2 + c / 8)) := hnorm_w
      _ ≤ C_sub * |s.im| ^ (7 * c / 16) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hexp_le) hC_sub.le
      _ ≤ C_sub * (|s.im| + 3) ^ (7 * c / 16) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by positivity)) hC_sub.le
      _ ≤ max C_sub (1 + 8 / c) * (|s.im| + 3) ^ (7 * c / 16) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have htriv := RHTower.Sieve.norm_riemannZeta_le (s := w) (by linarith)
    have hdiv_le : 1 / (w.re - 1) ≤ 8 / c := by
      rw [div_le_div_iff₀ (by linarith) hc0]
      linarith
    have hpow1 : 1 ≤ (|s.im| + 3) ^ (7 * c / 16) := Real.one_le_rpow ht1 (by positivity)
    calc ‖riemannZeta w‖ ≤ 1 + 1 / (w.re - 1) := htriv
      _ ≤ 1 + 8 / c := by linarith
      _ ≤ max C_sub (1 + 8 / c) := le_max_right _ _
      _ ≤ max C_sub (1 + 8 / c) * (|s.im| + 3) ^ (7 * c / 16) :=
          le_mul_of_one_le_right (by positivity) hpow1

private theorem exists_norm_tsum_lamS_sub_le_subconvex {c : ℝ} (hc0 : 0 < c) (hc_le : c ≤ 1 / 32)
    (D : DeletionData (1 / 2 + c / 8)) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧
      ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
        ‖∑' n, D.lamS n * g (n / M) -
            D.lamNum ((1 / 2 + c / 8 : ℝ) : ℂ) * mellin g ((1 / 2 + c / 8 : ℝ) : ℂ) *
              (M : ℂ) ^ ((1 / 2 + c / 8 : ℝ) : ℂ)‖ ≤
          K₂ * M ^ (1 / 2 - c) * DeletionData.lineMass g (1 / 2 - c) (c / 2) := by
  let α : ℝ := 1 / 2 + c / 8
  let σ₀ : ℝ := 1 / 2 - c
  let ε : ℝ := c / 2
  have hα0 : 0 < α := by dsimp [α]; linarith
  have hα : α < 1 := by dsimp [α]; linarith
  have hα2_σ₀ : α / 2 < σ₀ := by dsimp [α, σ₀]; linarith
  obtain ⟨c_exp, hc_exp, hE⟩ := D.exists_norm_exp_corr_le hα0 hα
    (δ := σ₀ - α / 2) (by linarith) (κ := c / 16) (by positivity)
  obtain ⟨C_ζ, hC_ζ, hζ⟩ := exists_norm_riemannZeta_shift_le_subconvex hc0 hc_le
  have hL_tail : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 3 / 2 → 8 ≤ |s.im| →
      ‖D.lamNum α / (s - (α : ℂ)) + dslope D.lamNum (α : ℂ) s‖ ≤
        (C_ζ * c_exp) * (|s.im| + 3) ^ ε := by
    intro s hs1 _ hs_im
    have hsα : s ≠ (α : ℂ) := by
      intro h; rw [h] at hs_im; simp at hs_im; linarith
    rw [D.residue_add_dslope_eq hsα, D.lamNum_div_eq hsα, norm_mul]
    have hE' : ‖Complex.exp (D.corr s + D.rem₁ s - DeletionData.rem₂ α s)‖ ≤
        c_exp * (|s.im| + 3) ^ (c / 16) := by
      refine (hE s (by dsimp only [σ₀, α] at hs1 ⊢; linarith)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)) hc_exp.le
    calc ‖riemannZeta (s + ((1 - α : ℝ) : ℂ))‖ *
          ‖Complex.exp (D.corr s + D.rem₁ s - DeletionData.rem₂ α s)‖
        ≤ (C_ζ * (|s.im| + 3) ^ (7 * c / 16)) * (c_exp * (|s.im| + 3) ^ (c / 16)) :=
          mul_le_mul (hζ s hs1 hs_im) hE' (norm_nonneg _) (by positivity)
      _ = (C_ζ * c_exp) * ((|s.im| + 3) ^ (7 * c / 16) * (|s.im| + 3) ^ (c / 16)) := by ring
      _ = (C_ζ * c_exp) * (|s.im| + 3) ^ ε := by
          rw [← Real.rpow_add (by positivity)]
          congr 2; dsimp [ε]; ring
  have hcont : ∀ s : ℂ, α / 2 < s.re → s ≠ (α : ℂ) →
      ContinuousAt (fun s => D.lamNum α / (s - (α : ℂ)) + dslope D.lamNum (α : ℂ) s) s := by
    intro s hs hsα
    have h1 : ContinuousAt (fun s : ℂ => D.lamNum α / (s - (α : ℂ))) s :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hsα)
    exact h1.add ((D.differentiableOn_dslope_lamNum hα0 hα).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).continuousAt
  have hne : ∀ s : ℂ, 1 ≤ |s.im| → s ≠ (α : ℂ) := fun s hs h => by
    rw [h] at hs; simp at hs; linarith
  obtain ⟨K_st, hK_st⟩ := DeletionData.exists_strip_bound
    (G := fun s => D.lamNum α / (s - (α : ℂ)) + dslope D.lamNum (α : ℂ) s)
    (σ₀ := σ₀) (σ₁ := 3 / 2)
    (fun s h1 _ h3 => hcont s (lt_of_lt_of_le hα2_σ₀ h1) (hne s h3))
    (by positivity : (0 : ℝ) ≤ ε) (T := 8) hL_tail
  have hlinecont : Continuous fun t : ℝ =>
      ‖D.lamNum α / ((σ₀ : ℂ) + t * I - (α : ℂ)) + dslope D.lamNum (α : ℂ) ((σ₀ : ℂ) + t * I)‖ := by
    refine (continuous_iff_continuousAt.mpr fun t => ?_).norm
    have hs : ((σ₀ : ℂ) + t * I) ≠ (α : ℂ) := fun h => by
      have := congrArg Complex.re h; simp at this; dsimp [σ₀, α] at this; linarith
    exact (hcont _ (by simp [hα2_σ₀]) hs).comp (f := fun t : ℝ => (σ₀ : ℂ) + t * I) (by fun_prop)
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_bound_line hlinecont (by positivity : (0 : ℝ) ≤ ε)
    (K := K_st) (T := 1) fun t ht => by
      have h := hK_st ((σ₀ : ℂ) + t * I) (by simp) (by simp; dsimp [σ₀]; linarith) (by simpa using ht)
      simpa using h
  refine ⟨K₀ / (2 * π), by positivity, fun g a b hg M hM => ?_⟩
  have h := norm_tsum_sub_residue_le hg D.lamS D.lamS_zero D.norm_lamS_le (A := D.lamNum α)
    (ρ := (α : ℂ)) (G₀ := dslope D.lamNum (α : ℂ)) (a₀ := α / 2) (σ₀ := σ₀) hα2_σ₀
    (by simp; dsimp [σ₀, α]; linarith) (by simp; dsimp [α]; linarith)
    (D.differentiableOn_dslope_lamNum hα0 hα)
    (fun s hs => D.LSeries_lamS_eq_residue hα0 hα hs)
    (by positivity : 0 ≤ ε) (by dsimp [ε]; linarith) (K := K_st)
    (fun s h1 h2 h3 => hK_st s h1 h2 h3) (K₀ := K₀) hK₀ hM
  calc _ ≤ _ := h
    _ = K₀ / (2 * π) * M ^ σ₀ * DeletionData.lineMass g σ₀ ε := by
        dsimp [σ₀, ε]; unfold DeletionData.lineMass; ring

private theorem exists_norm_block_le_of_smooth {α σ₀ ε K₁ K₂ : ℝ} (D : DeletionData α)
    (hσ₀0 : 0 ≤ σ₀) (hσα : σ₀ ≤ α) (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.mobS n * g (n / M)‖ ≤ K₁ * M ^ σ₀ * DeletionData.lineMass g σ₀ ε)
    (hK₂ : ∀ (g : ℝ → ℂ) (a b : ℝ), IsTest g a b → ∀ M : ℝ, 0 < M →
      ‖∑' n, D.lamS n * g (n / M) - D.lamNum α * mellin g (α : ℂ) * (M : ℂ) ^ (α : ℂ)‖ ≤
        K₂ * M ^ σ₀ * DeletionData.lineMass g σ₀ ε) :
    ∃ KB : ℝ, 0 ≤ KB ∧ ∀ M x Δ : ℝ, 1 ≤ M → M ≤ x → 0 < Δ → Δ ≤ 1 →
      ‖∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊,
          D.mobS m * BeurlingDeletion.bumpC (m / M) * (saw (x / m) : ℂ)‖ ≤
        KB * (M ^ σ₀ * (x / M) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε)) +
          Δ ^ (1 - ε) * M ^ α) := by
  obtain ⟨CF, hCF0, hCF⟩ := exists_integral_twist_le isTest_bumpC (σ := σ₀) (κ := ε)
    hσ₀0 hε.le (by linarith)
  obtain ⟨Cr, hCr0, hCr⟩ := exists_norm_mellin_twist_le isTest_bumpC α
  obtain ⟨A0, hA0, hdec⟩ := exists_saw_decomposition
  have hZs : Summable fun h : ℤ => |(h : ℝ)| ^ (-(1 + ε)) := summable_abs_int_rpow (by linarith)
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = zetaAbs (1 + ε) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := hZ ▸ zetaAbs_nonneg _
  set L := ‖D.lamNum α‖
  have hL0 : 0 ≤ L := norm_nonneg _
  set c₁ : ℝ := (A0 * K₁ * CF * 2 ^ (1 / 2 + ε) + A0 * K₂ * CF * 2 ^ (1 / 2 + ε)) * Z
  set c₂ : ℝ := A0 * L * Cr * Z
  set c₃ : ℝ := A0 * (L * Cr + K₂ * CF)
  refine ⟨c₁ + c₂ + c₃, by positivity, ?_⟩
  intro M x Δ hM hMx hΔ hΔ1
  have hM0 : 0 < M := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hy1 : 1 ≤ x / M := by rw [le_div_iff₀ hM0]; linarith
  obtain ⟨a, k, haS, hkS, ha, hk, hmain⟩ := hdec Δ hΔ
  have hβ : ∀ m, ‖D.mobS m * BeurlingDeletion.bumpC (m / M)‖ ≤ D.lamR m * bump (m / M) := fun m => by
    rw [norm_mul, BeurlingDeletion.bumpC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (bump_nonneg _)]
    exact mul_le_mul_of_nonneg_right (D.norm_mobS_le_lamR m) (bump_nonneg _)
  have key := hmain (Finset.Icc 1 ⌊4 * M⌋₊) (fun m : ℕ => x / m)
    (fun m => D.mobS m * BeurlingDeletion.bumpC (m / M)) (fun m => D.lamR m * bump (m / M)) hβ
  have hlamc : ∀ m : ℕ,
      ((D.lamR m * bump (m / M) : ℝ) : ℂ) = D.lamS m * BeurlingDeletion.bumpC (m / M) := by
    intro m; simp [DeletionData.lamS, BeurlingDeletion.bumpC]
  set X₁ : ℝ := M ^ σ₀ * (x / M) ^ (1 / 2 + ε) * Δ ^ (-(1 / 2 + 2 * ε))
  set X₂ : ℝ := Δ ^ (1 - ε) * M ^ α
  set G₀ : ℝ := A0 * Δ * (L * Cr * M ^ α + K₂ * M ^ σ₀ * CF)
  set B₁ : ℝ := A0 * K₁ * CF * 2 ^ (1 / 2 + ε) * X₁
  set B₂ : ℝ := A0 * L * Cr * M ^ α * Δ ^ (1 - ε) + A0 * K₂ * CF * 2 ^ (1 / 2 + ε) * X₁
  have hT1 : ∀ h : ℤ, ‖a h‖ * ‖∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊,
      (fun m => D.mobS m * BeurlingDeletion.bumpC (m / M)) i *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle)‖ ≤
      B₁ * |(h : ℝ)| ^ (-(1 + ε)) := by
    intro h
    rw [DeletionData.sum_mul_fourier_eq_tsum _ D.mobS_zero M x hM0 h]
    refine (DeletionData.smooth_term_le hA0 hK₁0 hCF0 hΔ hy1 (by positivity) hε hε4 (ha h)
      (norm_nonneg _) (D.norm_tsum_mobS_twist_le hK₁0 hK₁ hCF hM0 hx0 h)).trans (le_of_eq ?_)
    dsimp [B₁, X₁]; ring
  have hT2 : ∀ h : ℤ, ‖k h‖ * ‖∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊,
      (((fun m => D.lamR m * bump (m / M)) i : ℝ) : ℂ) *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle)‖ ≤
      B₂ * |(h : ℝ)| ^ (-(1 + ε)) + (if h = 0 then G₀ else 0) := by
    intro h
    have e : ∑ i ∈ Finset.Icc 1 ⌊4 * M⌋₊, (((fun m => D.lamR m * bump (m / M)) i : ℝ) : ℂ) *
        fourier h (((fun m : ℕ => x / m) i : ℝ) : UnitAddCircle) =
        ∑' n, D.lamS n * twist BeurlingDeletion.bumpC (h * x / M) (n / M) := by
      rw [← DeletionData.sum_mul_fourier_eq_tsum _ D.lamS_zero M x hM0 h]
      exact Finset.sum_congr rfl fun m _ => by simp only [hlamc]
    rw [e]
    refine (DeletionData.majorant_term_le hA0 hL0 hCr0 hK₂0 hCF0 hΔ hy1 (by positivity)
      (by positivity) hε hε4 (hk h) (norm_nonneg _)
      (D.norm_tsum_lamS_twist_le hK₂0 hK₂ hCF hCr hM0 hx0 h)).trans (le_of_eq ?_)
    dsimp [B₂, X₁, G₀, L]; ring
  have hS1 := summable_mul_norm_sum (Finset.Icc 1 ⌊4 * M⌋₊)
    (fun m => D.mobS m * BeurlingDeletion.bumpC (m / M)) (fun m : ℕ => x / m) haS
  have hS2 := summable_mul_norm_sum (Finset.Icc 1 ⌊4 * M⌋₊)
    (fun m => ((D.lamR m * bump (m / M) : ℝ) : ℂ)) (fun m : ℕ => x / m) hkS
  have hfin : Summable fun h : ℤ => (if h = 0 then G₀ else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun b hb => by
      rw [Finset.mem_singleton] at hb; simp [hb]
  have hsum1 := hS1.tsum_le_tsum hT1 (hZs.mul_left B₁)
  rw [tsum_mul_left, ← zetaAbs, ← hZ] at hsum1
  have hsum2 := hS2.tsum_le_tsum hT2 ((hZs.mul_left B₂).add hfin)
  rw [(hZs.mul_left _).tsum_add hfin, tsum_mul_left, tsum_ite_eq, ← zetaAbs, ← hZ] at hsum2
  have hMσ : M ^ σ₀ ≤ M ^ α := Real.rpow_le_rpow_of_exponent_le hM hσα
  have hΔε : Δ ≤ Δ ^ (1 - ε) := by
    calc Δ = Δ ^ (1 : ℝ) := (Real.rpow_one Δ).symm
      _ ≤ Δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hΔ hΔ1 (by linarith)
  have hG₀le : G₀ ≤ c₃ * X₂ := by
    have h1 : L * Cr * M ^ α + K₂ * M ^ σ₀ * CF ≤ (L * Cr + K₂ * CF) * M ^ α := by
      have : K₂ * M ^ σ₀ * CF ≤ K₂ * M ^ α * CF :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMσ hK₂0) hCF0
      nlinarith
    have h2 : 0 ≤ L * Cr * M ^ α + K₂ * M ^ σ₀ * CF := by positivity
    calc G₀ = A0 * Δ * (L * Cr * M ^ α + K₂ * M ^ σ₀ * CF) := rfl
      _ ≤ A0 * Δ ^ (1 - ε) * ((L * Cr + K₂ * CF) * M ^ α) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔε hA0) h1 h2 (by positivity)
      _ = c₃ * X₂ := by dsimp [c₃, X₂]; ring
  have hX₁0 : 0 ≤ X₁ := by positivity
  have hX₂0 : 0 ≤ X₂ := by positivity
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  have hfinal : B₁ * Z + (B₂ * Z + G₀) ≤ (c₁ + c₂ + c₃) * (X₁ + X₂) := by
    have e1 : B₁ * Z + B₂ * Z = c₁ * X₁ + c₂ * X₂ := by dsimp [B₁, B₂, c₁, c₂, X₂]; ring
    have e2 : (c₁ + c₂ + c₃) * (X₁ + X₂) = c₁ * X₁ + c₂ * X₂ + c₃ * X₂ +
        (c₁ * X₂ + c₂ * X₁ + c₃ * X₁) := by ring
    have h1 := mul_nonneg hc₁0 hX₂0
    have h2 := mul_nonneg hc₂0 hX₁0
    have h3 := mul_nonneg hc₃0 hX₁0
    linarith
  calc _ ≤ _ := key
    _ ≤ B₁ * Z + (B₂ * Z + G₀) := add_le_add hsum1 hsum2
    _ ≤ _ := hfinal

private theorem dyadic_scale_sub_half {c X : ℝ} (hc0 : 0 < c) (hc_le : c ≤ 1 / 32) (hX : 1 ≤ X) :
    X ^ (1 - c / 4) ≤ 2 ^ ⌈Real.logb 2 (X ^ (1 - c / 4) / X ^ (15 / 16 : ℝ))⌉₊ * X ^ (15 / 16 : ℝ) ∧
      (2 : ℝ) ^ ⌈Real.logb 2 (X ^ (1 - c / 4) / X ^ (15 / 16 : ℝ))⌉₊ * X ^ (15 / 16 : ℝ) ≤
        2 * X ^ (1 - c / 4) ∧
      (⌈Real.logb 2 (X ^ (1 - c / 4) / X ^ (15 / 16 : ℝ))⌉₊ : ℝ) ≤
        Real.log X / Real.log 2 + 1 := by
  have hX0 : 0 < X := by linarith
  set M₁ := X ^ (15 / 16 : ℝ)
  set K_hi := X ^ (1 - c / 4)
  have hM₁0 : 0 < M₁ := Real.rpow_pos_of_pos hX0 _
  set ρ := K_hi / M₁
  have hρeq : ρ = X ^ (1 - c / 4 - 15 / 16) :=
    (Real.rpow_sub hX0 (1 - c / 4) (15 / 16)).symm
  have hρ1 : 1 ≤ ρ := by rw [hρeq]; exact Real.one_le_rpow hX (by linarith)
  have hρX : ρ ≤ X := by
    rw [hρeq]
    calc X ^ (1 - c / 4 - 15 / 16) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
      _ = X := Real.rpow_one X
  have hρ0 : 0 < ρ := by linarith
  set b := Real.logb 2 ρ
  have hb0 : 0 ≤ b := Real.logb_nonneg (by norm_num) hρ1
  set J := ⌈b⌉₊
  have hJb : b ≤ J := Nat.le_ceil b
  have hJb' : (J : ℝ) < b + 1 := Nat.ceil_lt_add_one hb0
  have h2b : (2 : ℝ) ^ b = ρ := Real.rpow_logb (by norm_num) (by norm_num) hρ0
  have hJlow : ρ ≤ (2 : ℝ) ^ J := by
    rw [← h2b, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hJb
  have hJup : (2 : ℝ) ^ J ≤ 2 * ρ := by
    rw [← h2b, ← Real.rpow_natCast, show (2 : ℝ) * 2 ^ b = 2 ^ (b + 1) by
      rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hJb'.le
  refine ⟨?_, ?_, ?_⟩
  · calc K_hi = ρ * M₁ := by dsimp [ρ]; field_simp
      _ ≤ 2 ^ J * M₁ := mul_le_mul_of_nonneg_right hJlow hM₁0.le
  · calc (2 : ℝ) ^ J * M₁ ≤ 2 * ρ * M₁ := mul_le_mul_of_nonneg_right hJup hM₁0.le
      _ = 2 * K_hi := by dsimp [ρ]; field_simp
  · have hbX : b ≤ Real.log X / Real.log 2 := by
      dsimp only [b]
      rw [Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
      exact Real.log_le_log hρ0 hρX
    linarith

private theorem norm_count_sub_mobSum_le_sub_half {c CM CA KB E_sm : ℝ}
    (hc0 : 0 < c) (hc_le : c ≤ 1 / 32)
    (D : DeletionData (1 / 2 + c / 8))
    (hCM0 : 0 ≤ CM) (hCA0 : 0 ≤ CA) (hKB0 : 0 ≤ KB)
    (hE_sm : E_sm = Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(1 / 2 + c / 4))) n))
    (hCM : ∀ Y : ℝ, 1 ≤ Y → ‖∑ n ∈ Finset.Iic ⌊Y⌋₊, D.mobS n‖ ≤ CM * Y ^ (1 / 2 - 3 * c / 4))
    (hCA : ∀ M : ℝ, 1 ≤ M → ‖D.mainSum M - D.mobSum‖ ≤ CA * M ^ ((1 / 2 - c) - 1))
    (hKB : ∀ M x Δ : ℝ, 1 ≤ M → M ≤ x → 0 < Δ → Δ ≤ 1 →
      ‖∑ m ∈ Finset.Icc 1 ⌊4 * M⌋₊,
          D.mobS m * BeurlingDeletion.bumpC (m / M) * (saw (x / m) : ℂ)‖ ≤
        KB * (M ^ (1 / 2 - c) * (x / M) ^ (1 / 2 + c / 2) * Δ ^ (-(1 / 2 + 2 * (c / 2))) +
          Δ ^ (1 - c / 2) * M ^ (1 / 2 + c / 8)))
    {X : ℝ} (hX : (8 : ℝ) ^ (4 / c) ≤ X) :
    ‖D.count X - D.mobSum * X‖ ≤
      (CA + 2 * CM + E_sm + 3 * KB * (1 / (2 * (c / 16) * Real.log 2) + 1) +
        2 * CM / (1 - (1 / 2 - 3 * c / 4))) * X ^ (1 / 2 - c / 8) := by
  have hE_sm0 : 0 ≤ E_sm := hE_sm ▸ (Real.exp_pos _).le
  have h8_ge1 : (1 : ℝ) ≤ (8 : ℝ) ^ (4 / c) := Real.one_le_rpow (by norm_num) (by positivity)
  have hX1 : 1 ≤ X := le_trans h8_ge1 hX
  have hX0 : 0 < X := by linarith
  have hc_sq : c * c ≤ (1 / 32) * c := mul_le_mul_of_nonneg_right hc_le hc0.le
  have hα0 : 0 < 1 / 2 + c / 8 := by linarith
  have hα : 1 / 2 + c / 8 < 1 := by linarith
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = X ^ (15 / 16 : ℝ) := ⟨_, rfl⟩
  obtain ⟨K_hi, hK_hi⟩ : ∃ K_hi : ℝ, K_hi = X ^ (1 - c / 4) := ⟨_, rfl⟩
  have hM₁1 : 1 ≤ M₁ := hM₁ ▸ Real.one_le_rpow hX1 (by norm_num)
  have hM₁0 : 0 < M₁ := by linarith
  have hK1 : 1 ≤ K_hi := hK_hi ▸ Real.one_le_rpow hX1 (by linarith)
  have hK0 : 0 < K_hi := by linarith
  obtain ⟨hlo_raw, hhi_raw, hJ_log_raw⟩ := dyadic_scale_sub_half hc0 hc_le hX1
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌈Real.logb 2 (K_hi / M₁)⌉₊ := ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℝ, M₂ = 2 ^ J * M₁ := ⟨_, rfl⟩
  have hJ_raw : J = ⌈Real.logb 2 (X ^ (1 - c / 4) / X ^ (15 / 16 : ℝ))⌉₊ := by
    rw [hJ, hK_hi, hM₁]
  have hlo : K_hi ≤ M₂ := by rw [hK_hi, hM₂, hJ_raw, hM₁]; exact hlo_raw
  have hhi : M₂ ≤ 2 * K_hi := by rw [hK_hi, hM₂, hJ_raw, hM₁]; exact hhi_raw
  have hJ_log : (J : ℝ) ≤ Real.log X / Real.log 2 + 1 := by rw [hJ_raw]; exact hJ_log_raw
  have hM₂1 : 1 ≤ M₂ := le_trans hK1 hlo
  have hM₂0 : 0 < M₂ := by linarith
  have h8_K : 8 * K_hi ≤ X := by
    have hpow8 : (8 : ℝ) ≤ X ^ (c / 4) := by
      calc (8 : ℝ) = ((8 : ℝ) ^ (4 / c)) ^ (c / 4) := by
            rw [← Real.rpow_mul (by norm_num),
              show 4 / c * (c / 4) = 1 by field_simp, Real.rpow_one]
        _ ≤ X ^ (c / 4) := Real.rpow_le_rpow (by positivity) hX (by positivity)
    calc 8 * K_hi = 8 * X ^ (1 - c / 4) := by rw [hK_hi]
      _ ≤ X ^ (c / 4) * X ^ (1 - c / 4) :=
          mul_le_mul_of_nonneg_right hpow8 (by positivity)
      _ = X := by rw [← Real.rpow_add hX0, show c / 4 + (1 - c / 4) = 1 by ring, Real.rpow_one]
  have hN : 2 * (2 ^ J * M₁) ≤ (⌊X⌋₊ : ℝ) := by
    rw [← hM₂]
    have hfl := Nat.lt_floor_add_one X
    linarith
  rw [D.count_decomposition hα0 hα hX0.le hM₁0 J hN, ← hM₂]
  obtain ⟨S₂, hS₂⟩ : ∃ S₂ : ℂ, S₂ = ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₂) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨Sm, hSm⟩ : ∃ Sm : ℂ,
      Sm = ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, D.mobS m * (cut (m / M₁) : ℂ) * (saw (X / m) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨Bl, hBl⟩ : ∃ Bl : ℂ, Bl = ∑ j ∈ Finset.range J, ∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
      D.mobS m * BeurlingDeletion.bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨Hy, hHy⟩ : ∃ Hy : ℂ, Hy = ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, ∑ m ∈ Finset.Ioc 0 (⌊X⌋₊ / j),
      D.mobS m * (((1 - cut (m / M₂)) : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  rw [← hS₂, ← hSm, ← hBl, ← hHy]
  have e : (X : ℂ) * D.mainSum M₂ - 1 / 2 * S₂ - Sm - Bl + Hy - D.mobSum * X =
      (X : ℂ) * (D.mainSum M₂ - D.mobSum) - 1 / 2 * S₂ - Sm - Bl + Hy := by ring
  rw [e]
  -- (a) Main term remainder.
  have ha : ‖(X : ℂ) * (D.mainSum M₂ - D.mobSum)‖ ≤ CA * X ^ (1 / 2 - c / 8) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    have hM₂_pow : X * M₂ ^ ((1 / 2 - c) - 1) ≤ X ^ (1 / 2 - c / 8) := by
      calc X * M₂ ^ ((1 / 2 - c) - 1)
          ≤ X * K_hi ^ ((1 / 2 - c) - 1) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hK0 hlo (by linarith)) hX0.le
        _ = X ^ (1 + (1 - c / 4) * ((1 / 2 - c) - 1)) := by
            rw [hK_hi, ← Real.rpow_mul hX0.le, Real.rpow_add hX0, Real.rpow_one]
        _ ≤ X ^ (1 / 2 - c / 8) := by
            refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
            have hexp : 1 + (1 - c / 4) * ((1 / 2 - c) - 1) =
                1 / 2 - 7 * c / 8 + (1 / 4) * (c * c) := by ring
            rw [hexp]; linarith [hc_sq]
    calc X * ‖D.mainSum M₂ - D.mobSum‖
        ≤ X * (CA * M₂ ^ ((1 / 2 - c) - 1)) := mul_le_mul_of_nonneg_left (hCA M₂ hM₂1) hX0.le
      _ = CA * (X * M₂ ^ ((1 / 2 - c) - 1)) := by ring
      _ ≤ CA * X ^ (1 / 2 - c / 8) := mul_le_mul_of_nonneg_left hM₂_pow hCA0
  -- (b) Smoothly cut Möbius sum.
  have hb : ‖1 / 2 * S₂‖ ≤ 2 * CM * X ^ (1 / 2 - c / 8) := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := D.norm_sum_mobS_cut_le (θ := 1 / 2 - 3 * c / 4) (M₂ := M₂) hCM0 (by linarith)
      hCM hX1 hM₂0
    rw [← hS₂] at h
    have hθ_le : X ^ (1 / 2 - 3 * c / 4) ≤ X ^ (1 / 2 - c / 8) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have hCM_X : 0 ≤ CM * X ^ (1 / 2 - c / 8) := by positivity
    calc 1 / 2 * ‖S₂‖ ≤ 1 / 2 * (3 * CM * X ^ (1 / 2 - 3 * c / 4)) := by gcongr
      _ ≤ 1 / 2 * (3 * CM * X ^ (1 / 2 - c / 8)) := by gcongr
      _ ≤ 2 * CM * X ^ (1 / 2 - c / 8) := by linarith
  -- (c) Small range via Rankin.
  have hc_piece : ‖Sm‖ ≤ E_sm * X ^ (1 / 2 - c / 8) := by
    have h := D.norm_small_le hα0 hα (σ := 1 / 2 + c / 4) (by linarith)
      (X := X) (M₁ := M₁) (by linarith)
    rw [← hSm, ← hE_sm] at h
    have h2M₁ : (2 * M₁) ^ (1 / 2 + c / 4) ≤ 2 * X ^ (1 / 2 - c / 8) := by
      rw [Real.mul_rpow (by norm_num) hM₁0.le]
      have h2_le : (2 : ℝ) ^ (1 / 2 + c / 4) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 2 + c / 4) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have hM_le : M₁ ^ (1 / 2 + c / 4) ≤ X ^ (1 / 2 - c / 8) := by
        rw [hM₁, ← Real.rpow_mul hX0.le]
        exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      exact mul_le_mul h2_le hM_le (by positivity) (by norm_num)
    calc ‖Sm‖ ≤ 1 / 2 * ((2 * M₁) ^ (1 / 2 + c / 4) * E_sm) := h
      _ ≤ 1 / 2 * ((2 * X ^ (1 / 2 - c / 8)) * E_sm) := by gcongr
      _ = E_sm * X ^ (1 / 2 - c / 8) := by ring
  -- (d) Dyadic sawtooth blocks.
  have hd : ‖Bl‖ ≤ 3 * KB * (1 / (2 * (c / 16) * Real.log 2) + 1) * X ^ (1 / 2 - c / 8) := by
    obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℝ, Δ = X ^ (-3 * c / 5) := ⟨_, rfl⟩
    have hΔ0 : 0 < Δ := hΔ ▸ Real.rpow_pos_of_pos hX0 _
    have hΔ1 : Δ ≤ 1 := hΔ ▸ Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
    have hblock : ∀ j ∈ Finset.range J, ‖∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
        D.mobS m * BeurlingDeletion.bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ)‖ ≤
        KB * (3 * X ^ (1 / 2 - c / 4)) := by
      intro j hj
      have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
      obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 ^ j * M₁ := ⟨_, rfl⟩
      have hu_lo : M₁ ≤ u := hu ▸ le_mul_of_one_le_left hM₁0.le (one_le_pow₀ (by norm_num))
      have hu_hi : u ≤ 2 * K_hi := by
        have hu_M₂ : u ≤ M₂ := by
          rw [hu, hM₂]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) (by omega)) hM₁0.le
        exact le_trans hu_M₂ hhi
      have hu1 : 1 ≤ u := le_trans hM₁1 hu_lo
      have hu0 : 0 < u := by linarith
      have huX : u ≤ X := by linarith
      have hT1_le : u ^ (1 / 2 - c) * (X / u) ^ (1 / 2 + c / 2) * Δ ^ (-(1 / 2 + 2 * (c / 2))) ≤
          X ^ (1 / 2 - c / 4) := by
        have hrew : u ^ (1 / 2 - c) * (X / u) ^ (1 / 2 + c / 2) =
            u ^ (-3 * c / 2) * X ^ (1 / 2 + c / 2) := by
          rw [Real.div_rpow hX0.le hu0.le, div_eq_mul_inv, ← Real.rpow_neg hu0.le,
            mul_comm (X ^ (1 / 2 + c / 2)), ← mul_assoc, ← Real.rpow_add hu0]
          congr 2; ring
        have hu_pow : u ^ (-3 * c / 2) ≤ X ^ ((15 / 16 : ℝ) * (-3 * c / 2)) := by
          calc u ^ (-3 * c / 2) ≤ M₁ ^ (-3 * c / 2) :=
                Real.rpow_le_rpow_of_nonpos hM₁0 hu_lo (by linarith)
            _ = X ^ ((15 / 16 : ℝ) * (-3 * c / 2)) := by
                rw [hM₁, ← Real.rpow_mul hX0.le]
        have hΔ_pow : Δ ^ (-(1 / 2 + 2 * (c / 2))) =
            X ^ ((-3 * c / 5) * -(1 / 2 + 2 * (c / 2))) := by
          rw [hΔ, ← Real.rpow_mul hX0.le]
        rw [hrew, hΔ_pow]
        calc u ^ (-3 * c / 2) * X ^ (1 / 2 + c / 2) *
              X ^ ((-3 * c / 5) * -(1 / 2 + 2 * (c / 2)))
            ≤ X ^ ((15 / 16 : ℝ) * (-3 * c / 2)) * X ^ (1 / 2 + c / 2) *
                X ^ ((-3 * c / 5) * -(1 / 2 + 2 * (c / 2))) := by gcongr
          _ = X ^ ((15 / 16 : ℝ) * (-3 * c / 2) + (1 / 2 + c / 2) +
                (-3 * c / 5) * -(1 / 2 + 2 * (c / 2))) := by
              rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
          _ ≤ X ^ (1 / 2 - c / 4) := by
              refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
              have hexp : (15 / 16 : ℝ) * (-3 * c / 2) + (1 / 2 + c / 2) +
                  (-3 * c / 5) * -(1 / 2 + 2 * (c / 2)) =
                  1 / 2 - 97 * c / 160 + (3 / 5) * (c * c) := by ring
              rw [hexp]; linarith [hc_sq]
      have hT2_le : Δ ^ (1 - c / 2) * u ^ (1 / 2 + c / 8) ≤ 2 * X ^ (1 / 2 - c / 4) := by
        have h2α : (2 : ℝ) ^ (1 / 2 + c / 8) ≤ 2 := by
          calc (2 : ℝ) ^ (1 / 2 + c / 8) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hα.le
            _ = 2 := Real.rpow_one 2
        have hu_α : u ^ (1 / 2 + c / 8) ≤ 2 * X ^ ((1 - c / 4) * (1 / 2 + c / 8)) := by
          calc u ^ (1 / 2 + c / 8) ≤ (2 * K_hi) ^ (1 / 2 + c / 8) :=
                Real.rpow_le_rpow hu0.le hu_hi hα0.le
            _ = (2 : ℝ) ^ (1 / 2 + c / 8) * K_hi ^ (1 / 2 + c / 8) :=
                Real.mul_rpow (by norm_num) hK0.le
            _ ≤ 2 * K_hi ^ (1 / 2 + c / 8) := mul_le_mul_of_nonneg_right h2α (by positivity)
            _ = 2 * X ^ ((1 - c / 4) * (1 / 2 + c / 8)) := by
                rw [hK_hi, ← Real.rpow_mul hX0.le]
        have hΔ_pow : Δ ^ (1 - c / 2) = X ^ ((-3 * c / 5) * (1 - c / 2)) := by
          rw [hΔ, ← Real.rpow_mul hX0.le]
        rw [hΔ_pow]
        calc X ^ ((-3 * c / 5) * (1 - c / 2)) * u ^ (1 / 2 + c / 8)
            ≤ X ^ ((-3 * c / 5) * (1 - c / 2)) *
                (2 * X ^ ((1 - c / 4) * (1 / 2 + c / 8))) :=
              mul_le_mul_of_nonneg_left hu_α (by positivity)
          _ = 2 * (X ^ ((-3 * c / 5) * (1 - c / 2)) *
                X ^ ((1 - c / 4) * (1 / 2 + c / 8))) := by ring
          _ = 2 * X ^ ((-3 * c / 5) * (1 - c / 2) + (1 - c / 4) * (1 / 2 + c / 8)) := by
              rw [← Real.rpow_add hX0]
          _ ≤ 2 * X ^ (1 / 2 - c / 4) := by
              refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX1 ?_) (by norm_num)
              have hexp : (-3 * c / 5) * (1 - c / 2) + (1 - c / 4) * (1 / 2 + c / 8) =
                  1 / 2 - 3 * c / 5 + (43 / 160) * (c * c) := by ring
              rw [hexp]; linarith [hc_sq]
      rw [← hu]
      exact (hKB u X Δ hu1 huX hΔ0 hΔ1).trans
        (mul_le_mul_of_nonneg_left (by linarith) hKB0)
    have hJb := nat_le_rpow_of_le_log hX1 (ε := c / 16) (by positivity) hJ_log
    have hx_add : X ^ (1 / 2 - c / 4) * X ^ (2 * (c / 16)) = X ^ (1 / 2 - c / 8) := by
      rw [← Real.rpow_add hX0]; congr 1; ring
    rw [hBl]
    calc ‖∑ j ∈ Finset.range J, ∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
            D.mobS m * BeurlingDeletion.bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ)‖
        ≤ ∑ j ∈ Finset.range J, ‖∑ m ∈ Finset.Icc 1 ⌊4 * (2 ^ j * M₁)⌋₊,
            D.mobS m * BeurlingDeletion.bumpC (m / (2 ^ j * M₁)) * (saw (X / m) : ℂ)‖ :=
              norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range J, KB * (3 * X ^ (1 / 2 - c / 4)) := Finset.sum_le_sum hblock
      _ = (J : ℝ) * (KB * (3 * X ^ (1 / 2 - c / 4))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((1 / (2 * (c / 16) * Real.log 2) + 1) * X ^ (2 * (c / 16))) *
            (KB * (3 * X ^ (1 / 2 - c / 4))) :=
          mul_le_mul_of_nonneg_right hJb (by positivity)
      _ = 3 * KB * (1 / (2 * (c / 16) * Real.log 2) + 1) *
            (X ^ (1 / 2 - c / 4) * X ^ (2 * (c / 16))) := by ring
      _ = 3 * KB * (1 / (2 * (c / 16) * Real.log 2) + 1) * X ^ (1 / 2 - c / 8) := by rw [hx_add]
  -- (e) Hyperbola remainder.
  have he : ‖Hy‖ ≤ 2 * CM / (1 - (1 / 2 - 3 * c / 4)) * X ^ (1 / 2 - c / 8) := by
    have h := D.norm_hyperbola_le (θ := 1 / 2 - 3 * c / 4) (M₂ := M₂) hCM0 (by linarith)
      (by linarith) hCM hX1 hM₂1
    rw [← hHy] at h
    have hprod_le : X ^ (1 / 2 - 3 * c / 4) * (X / M₂) ^ (1 - (1 / 2 - 3 * c / 4)) ≤
        X ^ (1 / 2 - c / 8) := by
      have hdiv_eq : X / K_hi = X ^ (c / 4) := by
        rw [hK_hi, ← Real.rpow_one_sub' hX0.le (by linarith)]
        congr 1; ring
      calc X ^ (1 / 2 - 3 * c / 4) * (X / M₂) ^ (1 - (1 / 2 - 3 * c / 4))
          ≤ X ^ (1 / 2 - 3 * c / 4) * (X / K_hi) ^ (1 - (1 / 2 - 3 * c / 4)) := by gcongr
        _ = X ^ ((1 / 2 - 3 * c / 4) + (c / 4) * (1 - (1 / 2 - 3 * c / 4))) := by
            rw [hdiv_eq, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
        _ ≤ X ^ (1 / 2 - c / 8) := by
            refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
            have hexp : (1 / 2 - 3 * c / 4) + (c / 4) * (1 - (1 / 2 - 3 * c / 4)) =
                1 / 2 - 5 * c / 8 + (3 / 16) * (c * c) := by ring
            rw [hexp]; linarith [hc_sq]
    calc ‖Hy‖ ≤ 2 * CM / (1 - (1 / 2 - 3 * c / 4)) *
            X ^ (1 / 2 - 3 * c / 4) * (X / M₂) ^ (1 - (1 / 2 - 3 * c / 4)) := h
      _ = 2 * CM / (1 - (1 / 2 - 3 * c / 4)) *
            (X ^ (1 / 2 - 3 * c / 4) * (X / M₂) ^ (1 - (1 / 2 - 3 * c / 4))) := by ring
      _ ≤ 2 * CM / (1 - (1 / 2 - 3 * c / 4)) * X ^ (1 / 2 - c / 8) :=
          mul_le_mul_of_nonneg_left hprod_le (div_nonneg (by positivity) (by linarith))
  calc ‖(X : ℂ) * (D.mainSum M₂ - D.mobSum) - 1 / 2 * S₂ - Sm - Bl + Hy‖
      ≤ ‖(X : ℂ) * (D.mainSum M₂ - D.mobSum)‖ + ‖1 / 2 * S₂‖ + ‖Sm‖ + ‖Bl‖ + ‖Hy‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
        exact norm_sub_le _ _
    _ ≤ CA * X ^ (1 / 2 - c / 8) + 2 * CM * X ^ (1 / 2 - c / 8) +
        E_sm * X ^ (1 / 2 - c / 8) +
        3 * KB * (1 / (2 * (c / 16) * Real.log 2) + 1) * X ^ (1 / 2 - c / 8) +
        2 * CM / (1 - (1 / 2 - 3 * c / 4)) * X ^ (1 / 2 - c / 8) := by gcongr
    _ = _ := by ring

/-- **Sub-`1/2` integer-norm Beurling fake from any zero-free half-plane `Re z > Θ` (`Θ < 1`).**
If `1/2 ≤ Θ < 1` and `ζ` has no zeros with `Re z > Θ`, then there exists a prime set `S` such that
`keptPrimeSystem S` is an integer-norm Beurling fake at the explicit sub-`1/2` remainder exponent
`1/2 - (1 - max Θ (3/4)) / 64 < 1/2`. -/
theorem exists_integerNormFakeAt_lt_half_of_zeroFree {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) :
    ∃ S : Set ℕ,
      IsIntegerNormFakeAt (keptPrimeSystem S) (1 / 2 - (1 - max Θ (3 / 4)) / 64) ∧
      1 / 2 - (1 - max Θ (3 / 4)) / 64 < 1 / 2 := by
  set Θ' : ℝ := max Θ (3 / 4)
  have hΘ'_ge : 3 / 4 ≤ Θ' := le_max_right _ _
  have hΘ'_lt1 : Θ' < 1 := max_lt hΘ1 (by norm_num)
  have hzf' : ∀ z : ℂ, Θ' < z.re → riemannZeta z ≠ 0 :=
    fun z hz => hzf z (lt_of_le_of_lt (le_max_left _ _) hz)
  set c : ℝ := (1 - Θ') / 8
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hc_le : c ≤ 1 / 32 := by dsimp [c]; linarith
  have hΘ'_eq : Θ' = 1 - 8 * c := by dsimp [c]; ring
  set α : ℝ := 1 / 2 + c / 8
  set σ₀ : ℝ := 1 / 2 - c
  set a₀ : ℝ := 1 / 2 - 2 * c
  set τ : ℝ := c / 16
  set ε : ℝ := c / 2
  set θ_M : ℝ := 1 / 2 - 3 * c / 4
  set β : ℝ := 1 / 2 - c / 8
  have hα1 : 1 / 2 < α := by dsimp [α]; linarith
  have hα : α < 1 := by dsimp [α]; linarith
  have hα0 : 0 < α := by linarith
  obtain ⟨D⟩ := exists_deletionData hα0 hα
  have hDiff := differentiableOn_eFactor_mul_qFactor_of_zeroFree D hα0 hα hzf'
    (a₀ := a₀) (by dsimp [α, a₀]; linarith) (by rw [hΘ'_eq]; dsimp [a₀, α]; linarith)
  obtain ⟨c_eq, _, hEQ⟩ := exists_norm_eFactor_mul_qFactor_le_of_zeroFree D hα0 hα
    (by linarith : 1 / 2 ≤ Θ') hΘ'_lt1.le hzf' (δ := c) hc0 (by linarith)
    (σ₀ := σ₀) (by dsimp [α, σ₀]; linarith) (by rw [hΘ'_eq]; dsimp [σ₀, α]; linarith)
    (τ := τ) (by dsimp [τ]; positivity)
  have hσ₀_pos : 0 < σ₀ := by dsimp [σ₀]; linarith
  have hτ_pos : 0 < τ := by dsimp [τ]; positivity
  have hθ_exp : (2 * τ + σ₀) / (1 + 2 * τ) + τ ≤ θ_M := by
    have hdiv_le : (2 * τ + σ₀) / (1 + 2 * τ) ≤ 2 * τ + σ₀ := by
      rw [div_le_iff₀ (by linarith)]
      have hpos : 0 ≤ 2 * τ * (2 * τ + σ₀) := by positivity
      linarith
    dsimp [τ, σ₀, θ_M] at hdiv_le ⊢
    linarith
  obtain ⟨CM, K₁, CA, hCM0, hK₁0, hCA0, hCM, hK₁, hCA⟩ :=
    exists_mobS_bounds_of_zeroFree (ε := ε) (θ_M := θ_M) D hα0 hα (by dsimp [a₀, σ₀]; linarith)
      hσ₀_pos (by dsimp [σ₀]; linarith) hτ_pos (by dsimp [τ]; linarith)
      (by dsimp [τ, ε]; linarith) (by dsimp [ε]; linarith) hθ_exp hDiff hEQ
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_tsum_lamS_sub_le_subconvex hc0 hc_le D
  obtain ⟨KB, hKB0, hKB⟩ := exists_norm_block_le_of_smooth D
    (by dsimp [σ₀]; linarith) (by dsimp [σ₀, α]; linarith)
    (by dsimp [ε]; positivity) (by dsimp [ε]; linarith)
    hK₁0 hK₂0 hK₁ hK₂
  obtain ⟨E_sm, hE_sm⟩ : ∃ E_sm : ℝ,
      E_sm = Real.exp (∑' n : ℕ, D.S.indicator (fun n => (n : ℝ) ^ (-(1 / 2 + c / 4))) n) :=
    ⟨_, rfl⟩
  have hE_sm0 : 0 ≤ E_sm := hE_sm ▸ (Real.exp_pos _).le
  set C₁ : ℝ := CA + 2 * CM + E_sm + 3 * KB * (1 / (2 * (c / 16) * Real.log 2) + 1) +
    2 * CM / (1 - θ_M)
  have hC₁0 : 0 ≤ C₁ := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden : 0 < 1 - θ_M := by dsimp [θ_M]; linarith
    positivity
  set X₀ : ℝ := (8 : ℝ) ^ (4 / c)
  obtain ⟨M_mob, hM_mob⟩ : ∃ M_mob : ℝ, M_mob = ‖D.mobSum‖ := ⟨_, rfl⟩
  have hM_mob0 : 0 ≤ M_mob := hM_mob ▸ norm_nonneg _
  set C_tot : ℝ := max C₁ ((2 + M_mob) * X₀)
  have hcnt_all : ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.mobSum * X‖ ≤ C_tot * X ^ β := by
    intro X hX1
    have hX0 : 0 < X := by linarith
    by_cases hXX : X₀ ≤ X
    · calc ‖D.count X - D.mobSum * X‖
          ≤ C₁ * X ^ β :=
            norm_count_sub_mobSum_le_sub_half hc0 hc_le D hCM0 hCA0 hKB0 hE_sm hCM hCA hKB hXX
        _ ≤ C_tot * X ^ β := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · push Not at hXX
      have hpow1 : 1 ≤ X ^ β := Real.one_le_rpow hX1 (by dsimp [β]; linarith)
      have hterm2 : ‖D.mobSum * (X : ℂ)‖ = M_mob * X := by
        rw [norm_mul, ← hM_mob, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
      calc ‖D.count X - D.mobSum * X‖
          ≤ ‖D.count X‖ + ‖D.mobSum * (X : ℂ)‖ := norm_sub_le _ _
        _ ≤ (X + 1) + M_mob * X := add_le_add (D.norm_count_le X hX0.le) (le_of_eq hterm2)
        _ ≤ (2 + M_mob) * X₀ := by nlinarith
        _ ≤ C_tot := le_max_right _ _
        _ ≤ C_tot * X ^ β := le_mul_of_one_le_right (le_trans hC₁0 (le_max_left _ _)) hpow1
  have hΘ_shift : Θ < 3 / 2 - α := by
    have hle : Θ ≤ Θ' := le_max_left _ _
    rw [hΘ'_eq] at hle
    dsimp [α]
    linarith
  have hfake : IsIntegerNormFakeAt (keptPrimeSystem D.S) β :=
    isIntegerNormFakeAt_keptPrimeSystem_of_deletionData D hα1 hα hzf hΘ_shift
      (by dsimp [β]; linarith) hcnt_all
  have hβ_eq : β = 1 / 2 - (1 - max Θ (3 / 4)) / 64 := by dsimp [β, c, Θ']; ring
  rw [hβ_eq] at hfake
  exact ⟨D.S, hfake, by rw [← hβ_eq]; dsimp [β]; linarith⟩

theorem csInf_integerNormFakeExponents_lt_half_of_zeroFree {Θ : ℝ}
    (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) :
    sInf integerNormFakeExponents ≤ 1 / 2 - (1 - max Θ (3 / 4)) / 64 ∧
      sInf integerNormFakeExponents < 1 / 2 := by
  obtain ⟨S, hf, hlt⟩ := exists_integerNormFakeAt_lt_half_of_zeroFree hΘ hΘ1 hzf
  have hle := csInf_le bddBelow_integerNormFakeExponents ⟨keptPrimeSystem S, hf⟩
  exact ⟨hle, lt_of_le_of_lt hle hlt⟩

/-! ## 3. Conditional `RiemannHypothesis` calibration (`β > 1/3`) -/

/-- Under `RiemannHypothesis`, prime-deletion Beurling fakes exist for every remainder exponent
`β > 1/3`. -/
theorem exists_integerNormFakeAt_of_riemannHypothesis (hRH : RiemannHypothesis)
    {β : ℝ} (hβ : 1 / 3 < β) :
    ∃ S : Set ℕ, IsIntegerNormFakeAt (keptPrimeSystem S) β := by
  set β' : ℝ := min β (1 / 2)
  have hβ' : 1 / 3 < β' := lt_min hβ (by norm_num)
  have hβ'1 : β' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set δ : ℝ := β' - 1 / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  set α : ℝ := 1 / 2 + min (δ / 2) (1 / 8)
  have hα1 : 1 / 2 < α := by
    dsimp [α]
    have : 0 < min (δ / 2) (1 / 8) := lt_min (by linarith) (by norm_num)
    linarith
  have hα : α < 1 := by
    dsimp [α]
    have : min (δ / 2) (1 / 8) ≤ 1 / 8 := min_le_right _ _
    linarith
  have hsaw_lt : 3 * α / (α + 4) < β' := by
    rw [div_lt_iff₀ (by linarith)]
    have hα_sub : α - 1 / 2 ≤ δ / 2 := by
      simp only [α, add_sub_cancel_left]
      exact min_le_left (δ / 2) (1 / 8)
    have hlin : 3 * α < (1 / 3 + δ) * (α + 4) := by
      have h9 : 8 * (α - 1 / 2) ≤ 4 * δ := by linarith
      have h27 : 9 / 2 < α + 4 := by linarith
      nlinarith
    simpa [δ] using hlin
  set η : ℝ := β' - 3 * α / (α + 4)
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨D⟩ := exists_deletionData (α := α) (by linarith) hα
  obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le_saw hRH hα1 hα hη
  have hexp_eq : 3 * α / (α + 4) + η = β' := by dsimp [η]; ring
  have hcnt : ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ β' := by
    intro X hX; rw [← hexp_eq]; exact hC X hX
  have hzf : ∀ z : ℂ, 1 / 2 < z.re → riemannZeta z ≠ 0 := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; exact riemannZeta_ne_zero_of_one_le_re le_rfl
    · exact RHTower.WeilSpectral.riemannZeta_ne_zero_of_half_lt hRH hz hz1
  have hfake' : IsIntegerNormFakeAt (keptPrimeSystem D.S) β' :=
    isIntegerNormFakeAt_keptPrimeSystem_of_deletionData D hα1 hα hzf (by linarith) hβ'1 hcnt
  exact ⟨D.S, hfake'.mono (min_le_left β (1 / 2))⟩

theorem csInf_integerNormFakeExponents_le_one_third_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    sInf integerNormFakeExponents ≤ 1 / 3 := by
  by_contra hgt
  push Not at hgt
  set mid : ℝ := (1 / 3 + min (sInf integerNormFakeExponents) 1) / 2
  have hmid_gt : 1 / 3 < mid := by
    dsimp [mid]
    have : 1 / 3 < min (sInf integerNormFakeExponents) 1 := lt_min hgt (by norm_num)
    linarith
  have hmid_lt : mid < sInf integerNormFakeExponents := by
    dsimp [mid]
    have h1 : min (sInf integerNormFakeExponents) 1 ≤ sInf integerNormFakeExponents :=
      min_le_left _ _
    have h2 : 1 / 3 < min (sInf integerNormFakeExponents) 1 := lt_min hgt (by norm_num)
    linarith
  obtain ⟨S, hf⟩ := exists_integerNormFakeAt_of_riemannHypothesis hRH hmid_gt
  exact not_le_of_gt hmid_lt (csInf_le bddBelow_integerNormFakeExponents ⟨keptPrimeSystem S, hf⟩)

/-! ## 4. Unconditional ZFC frontier dichotomy and complete solution of Question B182 -/

/-- Because `ζ` has no zeros on `Re s ≥ 1` (`riemannZeta_ne_zero_of_one_le_re`), any finite upper
layer `{q : XiZeroCopy | σ < Re q}` (`σ < 1`) has supremum strictly below `1`.  Consequently,
`zetaZeroAbscissa < 1` is unconditionally equivalent to `zetaAsymptoticAbscissa < 1`. -/
theorem zetaZeroAbscissa_lt_one_iff_zetaAsymptoticAbscissa_lt_one :
    zetaZeroAbscissa < 1 ↔ zetaAsymptoticAbscissa < 1 := by
  constructor
  · exact lt_of_le_of_lt zetaAsymptoticAbscissa_le_zetaZeroAbscissa
  · intro hlt
    set σ : ℝ := (zetaAsymptoticAbscissa + 1) / 2
    have hσ_gt : zetaAsymptoticAbscissa < σ := by dsimp [σ]; linarith
    have hσ_lt1 : σ < 1 := by dsimp [σ]; linarith
    have hσ_half : 1 / 2 ≤ σ := by
      dsimp [σ]; linarith [half_le_zetaAsymptoticAbscissa]
    obtain ⟨σ₀, hσ₀_mem, hσ₀_lt⟩ := exists_lt_of_csInf_lt zetaAsymptoticAbscissaSet_nonempty hσ_gt
    have hσ_mem : σ ∈ zetaAsymptoticAbscissaSet :=
      zetaAsymptoticAbscissaSet_mono hσ₀_mem hσ₀_lt.le
    have hfin : {q : XiZeroCopy | σ < (q.1 : ℂ).re}.Finite := hσ_mem.2
    classical
    set F : Finset XiZeroCopy := hfin.toFinset
    by_cases hF : F.Nonempty
    · set M : ℝ := (F.image fun q : XiZeroCopy => (q.1 : ℂ).re).max' (hF.image _)
      have hM_mem : M ∈ F.image fun q : XiZeroCopy => (q.1 : ℂ).re := Finset.max'_mem _ _
      obtain ⟨q₀, _, hq₀_eq⟩ := Finset.mem_image.mp hM_mem
      have hM_lt1 : M < 1 := by
        rw [← hq₀_eq]
        exact (_root_.RHTower.xi_divisor_support_re_mem_open_unit q₀.1).2
      have hle : zetaZeroAbscissa ≤ max σ M := by
        refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le
          (le_trans hσ_half (le_max_left _ _)) fun q => ?_
        rcases le_or_gt (q.1 : ℂ).re σ with hq_le | hq_gt
        · exact le_trans hq_le (le_max_left _ _)
        · have hqF : q ∈ F := (Set.Finite.mem_toFinset hfin).mpr hq_gt
          have hqM : (q.1 : ℂ).re ≤ M :=
            Finset.le_max' _ _ (Finset.mem_image_of_mem (fun q : XiZeroCopy => (q.1 : ℂ).re) hqF)
          exact le_trans hqM (le_max_right _ _)
      exact lt_of_le_of_lt hle (max_lt hσ_lt1 hM_lt1)
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      have hle : zetaZeroAbscissa ≤ σ := by
        refine zetaZeroAbscissa_le_of_forall_xiZeroCopy_re_le hσ_half fun q => ?_
        by_contra hgt
        push Not at hgt
        have hqF : q ∈ F := (Set.Finite.mem_toFinset hfin).mpr hgt
        rw [hF] at hqF
        exact absurd hqF (Finset.notMem_empty q)
      exact lt_of_le_of_lt hle hσ_lt1

theorem zetaZeroAbscissa_eq_one_iff_zetaAsymptoticAbscissa_eq_one :
    zetaZeroAbscissa = 1 ↔ zetaAsymptoticAbscissa = 1 := by
  constructor
  · intro h1
    by_contra hne
    have hlt : zetaAsymptoticAbscissa < 1 := lt_of_le_of_ne zetaAsymptoticAbscissa_le_one hne
    exact (zetaZeroAbscissa_lt_one_iff_zetaAsymptoticAbscissa_lt_one.mpr hlt).ne h1
  · intro h1
    exact le_antisymm zetaZeroAbscissa_le_one
      (h1 ▸ zetaAsymptoticAbscissa_le_zetaZeroAbscissa)

/-- **Unconditional ZFC frontier dichotomy for sub-`1/2` integer-norm Beurling fakes.**
Either `zetaZeroAbscissa = 1` (in which case `zetaAsymptoticAbscissa = 1`, infinitely many zeros
of `ζ` accumulate at `Re s = 1`, and `AsymptoticAbscissaLaw` holds unconditionally), or
`zetaZeroAbscissa < 1` and there exists a prime-deletion Beurling fake `keptPrimeSystem S` at the
explicit sub-`1/2` remainder exponent `1/2 - (1 - max zetaZeroAbscissa (3/4)) / 64 < 1/2`. -/
theorem zetaZeroAbscissa_eq_one_or_exists_integerNormFakeAt_lt_half :
    (zetaZeroAbscissa = 1 ∧ zetaAsymptoticAbscissa = 1 ∧ RHTower.AsymptoticAbscissaLaw) ∨
      (zetaZeroAbscissa < 1 ∧
        ∃ S : Set ℕ,
          IsIntegerNormFakeAt (keptPrimeSystem S)
            (1 / 2 - (1 - max zetaZeroAbscissa (3 / 4)) / 64) ∧
          1 / 2 - (1 - max zetaZeroAbscissa (3 / 4)) / 64 < 1 / 2) := by
  rcases eq_or_lt_of_le zetaZeroAbscissa_le_one with h1 | hlt
  · have ha1 : zetaAsymptoticAbscissa = 1 :=
      zetaZeroAbscissa_eq_one_iff_zetaAsymptoticAbscissa_eq_one.mp h1
    have hAAL : RHTower.AsymptoticAbscissaLaw :=
      asymptoticAbscissaLaw_iff_zetaAsymptoticAbscissa_eq_zetaZeroAbscissa.mpr (ha1.trans h1.symm)
    exact Or.inl ⟨h1, ha1, hAAL⟩
  · exact Or.inr ⟨hlt, exists_integerNormFakeAt_lt_half_of_zeroFree half_le_zetaZeroAbscissa hlt
      (fun _ hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz)⟩

theorem asymptoticAbscissaLaw_or_exists_integerNormFakeAt_lt_half :
    RHTower.AsymptoticAbscissaLaw ∨
      ∃ β < (1 / 2 : ℝ), ∃ B : BeurlingSystem, IsIntegerNormFakeAt B β := by
  rcases zetaZeroAbscissa_eq_one_or_exists_integerNormFakeAt_lt_half with
    ⟨_, _, hAAL⟩ | ⟨_, S, hf, hlt⟩
  · exact Or.inl hAAL
  · exact Or.inr ⟨_, hlt, keptPrimeSystem S, hf⟩

theorem exists_integerNormFakeAt_lt_half_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ β < (1 / 2 : ℝ), ∃ B : BeurlingSystem, IsIntegerNormFakeAt B β := by
  rcases asymptoticAbscissaLaw_or_exists_integerNormFakeAt_lt_half with hAAL | hex
  · exact absurd hAAL hnot
  · exact hex

/-- **Complete unconditional solution to Question B182 (the integer-norm Beurling fake remainder
spectrum).**
1. **Existence for `β < 1`:** Every exponent `β > 1/2` belongs unconditionally to
   `integerNormFakeExponents` (`Set.Ioi (1/2) ⊆ integerNormFakeExponents`), realized by
   prime-deletion systems `keptPrimeSystem S` whose analytic continuation vanishes at both a real
   point and an off-real point in `{Re s > 1/2}` where `ζ` is nonzero.
2. **Lower bound, critical-threshold localization, and structural obstructions:**
   Every `β ∈ integerNormFakeExponents` satisfies `0 ≤ β`, so unconditionally
   `sInf integerNormFakeExponents ∈ [0, 1/2]`; every fake at exponent `β ≤ 1/2` has strictly
   positive density `A > 0` and omits infinitely many rational primes; and no unit-density
   (`A = 1`) sub-logarithmic integer-norm fake exists (`|N_B(x) - x| = o(log x)` is impossible).
3. **Sub-`1/2` characterization and ZFC frontier dichotomy:**
   Any zero-free half-plane `{Re z > Θ}` (`1/2 ≤ Θ < 1`) for `ζ` produces a sub-`1/2`
   prime-deletion fake (`β < 1/2`), reaching every `β > 1/3` under `RiemannHypothesis`; and
   unconditionally in ZFC, either `zetaZeroAbscissa = 1` (with `zetaAsymptoticAbscissa = 1` and
   `AsymptoticAbscissaLaw`) or sub-`1/2` integer-norm Beurling fakes exist (`sInf < 1/2`). -/
theorem integerNormFake_complete_solution :
    (Set.Ioi (1 / 2 : ℝ) ⊆ integerNormFakeExponents) ∧
    (∀ β > (1 / 2 : ℝ), ∃ (S : Set ℕ) (G : ℂ → ℂ) (ρ₀ ρ₁ : ℂ),
      IsIntegerNormFakeAt (keptPrimeSystem S) β ∧
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * (keptPrimeSystem S).zetaSeriesC s) ∧
      1 / 2 < ρ₀.re ∧ ρ₀.im = 0 ∧ ρ₀ ≠ 1 ∧ G ρ₀ = 0 ∧ riemannZeta ρ₀ ≠ 0 ∧
      1 / 2 < ρ₁.re ∧ ρ₁.im ≠ 0 ∧ G ρ₁ = 0 ∧ riemannZeta ρ₁ ≠ 0) ∧
    (∀ β ∈ integerNormFakeExponents, 0 ≤ β) ∧
    (sInf integerNormFakeExponents ∈ Set.Icc (0 : ℝ) (1 / 2)) ∧
    (∀ (B : BeurlingSystem) (β : ℝ), β ≤ 1 / 2 → IsIntegerNormFakeAt B β →
      (∃ A C : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
      {p : ℕ | p.Prime ∧ ∀ l : B.Label, B.labelNorm l ≠ p}.Infinite) ∧
    (RiemannHypothesis → Set.Ioi (1 / 3 : ℝ) ⊆ integerNormFakeExponents ∧
      sInf integerNormFakeExponents ≤ 1 / 3) ∧
    ((zetaZeroAbscissa = 1 ∧ zetaAsymptoticAbscissa = 1 ∧ RHTower.AsymptoticAbscissaLaw) ∨
      (zetaZeroAbscissa < 1 ∧ ∃ β < (1 / 2 : ℝ), β ∈ integerNormFakeExponents ∧
        sInf integerNormFakeExponents < 1 / 2)) := by
  refine ⟨Ioi_half_subset_integerNormFakeExponents,
    fun _ hβ => exists_keptPrimeSystem_fake_above_half hβ,
    fun _ ⟨_, hf⟩ => nonneg_of_integerNormFakeAt hf,
    csInf_integerNormFakeExponents_mem_Icc,
    fun B β hβ hf =>
      let ⟨_, _, _, ⟨A, C, _, hC⟩, _⟩ := hf
      ⟨⟨A, C, pos_density_of_integerNormFakeAt_le_half hf hβ hC, hC⟩,
        infinite_missing_primes_of_integerNormFakeAt (by linarith) hf⟩,
    fun hRH => ⟨fun _ hβ => let ⟨S, hf⟩ := exists_integerNormFakeAt_of_riemannHypothesis hRH hβ
      ⟨keptPrimeSystem S, hf⟩,
      csInf_integerNormFakeExponents_le_one_third_of_riemannHypothesis hRH⟩,
    ?_⟩
  rcases zetaZeroAbscissa_eq_one_or_exists_integerNormFakeAt_lt_half with h1 | ⟨hlt, S, hf, hβ_lt⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hlt, _, hβ_lt, ⟨keptPrimeSystem S, hf⟩, ?_⟩
    exact lt_of_le_of_lt (csInf_le bddBelow_integerNormFakeExponents ⟨keptPrimeSystem S, hf⟩) hβ_lt

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
