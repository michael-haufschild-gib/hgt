import GaloisForLFunctions.RHTower.KuznetsovRowKloosterman

/-!
# The geometric side of the large sieve for `Γ₀(Q)` at the cusp `∞`

For the cusp vector `1_H` of `Γ₀(Q)` (`Q ∣ N+1`) and integral frequencies `m, n ≥ 1`,

`geomRow(1, K; m, n; 1_H, 1_H) = 4|H| [m = n] (4πm)⁻¹ ∫g_K
   + 2|H| Σ_{c ≠ 0, Q ∣ c} S(m, n; |c|) c^{−2} Ψ_1(4π√(mn)/|c|)`

(`geomRow_gamma0`), with `Ψ_1(X) = 2 ∫ 𝒢_K(w) tanh w sin(X cosh w) dw` (`gaussKernel_one`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry RHTower.Sieve KuznetsovGauss

noncomputable section

variable {N : ℕ}

theorem norm_rowExp (m n : ℤ) (p : gammaSet 1 1 0) : ‖rowExp m n p‖ = 1 := by
  rw [rowExp, show 2 * Real.pi * Complex.I * (((m : ℝ) * (p.1 1 : ℂ) + (n : ℝ) *
      (gammaSetMatrix p 0 0 : ℂ)) / (p.1 0 : ℂ)) =
      ((2 * Real.pi * (((m : ℝ) * (p.1 1 : ℝ) + (n : ℝ) * (gammaSetMatrix p 0 0 : ℝ)) /
        (p.1 0 : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem rowSq_eq (r : ReducedRow) : rowSq r = ((rowModulus r : ℤ) : ℝ) ^ 2 := rfl

open Classical in
/-- The modulus weight `Φ(c) = [Q ∣ c] c^{−2} Ψ_1(4π√(mn)/|c|)`. -/
def gamma0Weight (Q : ℕ) (K m n : ℝ) (c : ℤ) : ℂ :=
  (if ((c : ℤ) : ZMod Q) = 0 then 1 else 0) * ((((c : ℝ) ^ 2) ^ (-(1 : ℝ)) : ℝ) : ℂ) *
    gaussKernel 1 K (4 * Real.pi * Real.sqrt (m * n / (c : ℝ) ^ 2))

theorem norm_gamma0Weight_le (Q : ℕ) {K m n : ℝ} (hK : 0 < K) {c : ℤ} (hc : c ≠ 0) :
    ‖gamma0Weight Q K m n c‖ ≤ (Real.pi * (4 * Real.pi * Real.sqrt (m * n)) * gaussSinhMass K) *
      (((c : ℝ) ^ 2) ^ (-(3 / 2 : ℝ))) := by
  classical
  have hq : (0 : ℝ) < (c : ℝ) ^ 2 := by have : (c : ℝ) ≠ 0 := by exact_mod_cast hc
                                        positivity
  have hX : 0 ≤ 4 * Real.pi * Real.sqrt (m * n / (c : ℝ) ^ 2) := by positivity
  have h2 := norm_gaussKernel_le le_rfl hK hX
  have h4 : Real.sqrt (m * n / (c : ℝ) ^ 2) = Real.sqrt (m * n) * ((c : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' _ hq.le, Real.sqrt_eq_rpow ((c : ℝ) ^ 2), Real.rpow_neg hq.le, div_eq_mul_inv]
  have h5 : ((c : ℝ) ^ 2) ^ (-(1 : ℝ)) * ((c : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) =
      ((c : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hq]; norm_num
  have hind : ‖(if ((c : ℤ) : ZMod Q) = 0 then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> simp
  rw [gamma0Weight, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖(if ((c : ℤ) : ZMod Q) = 0 then (1 : ℂ) else 0)‖ * ((c : ℝ) ^ 2) ^ (-(1 : ℝ)) *
        ‖gaussKernel 1 K (4 * Real.pi * Real.sqrt (m * n / (c : ℝ) ^ 2))‖
      ≤ 1 * ((c : ℝ) ^ 2) ^ (-(1 : ℝ)) *
        (Real.pi * (4 * Real.pi * Real.sqrt (m * n / (c : ℝ) ^ 2)) * gaussSinhMass K) := by
        gcongr
    _ = _ := by rw [h4, ← h5]; ring

theorem summable_rowExp_mul_gamma0Weight (Q : ℕ) {K : ℝ} (hK : 0 < K) (m n : ℕ) :
    Summable fun r : ReducedRow => rowExp m n r.1 * gamma0Weight Q K m n (rowModulus r) := by
  refine ((summable_reducedRow_rpow (τ := 3 / 2) (by norm_num)).mul_left
    (Real.pi * (4 * Real.pi * Real.sqrt ((m : ℝ) * n)) * gaussSinhMass K)).of_norm_bounded ?_
  intro r
  rw [norm_mul, norm_rowExp, one_mul]
  exact norm_gamma0Weight_le Q hK (rowModulus_ne_zero r)

open Classical in
/-- **The Γ₀(Q) geometric row at the cusp `∞`.** -/
theorem geomRow_gamma0 {Q : ℕ} (hQ : Q ∣ N + 1) {K : ℝ} (hK : 0 < K) (m n : ℕ) (hm : 0 < m) :
    geomRow 1 K m n (gamma0Vec N Q) (gamma0Vec N Q) =
      (if m = n then 4 * (Fintype.card (gamma0Deck N Q) : ℂ) *
        ((4 * Real.pi * m : ℝ) : ℂ)⁻¹ * (gaussMass K : ℂ) else 0) +
      2 * (Fintype.card (gamma0Deck N Q) : ℂ) *
        ∑' c : ℤ, intKloosterman m n c * gamma0Weight Q K m n c := by
  rw [geomRow]
  congr 1
  · rw [diagPlus]
    by_cases h : m = n
    · subst h
      rw [if_pos rfl, if_pos rfl, inner_gamma0Vec_add_neg_one hQ,
        show ((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) - 1 = 1 by push_cast; ring, Complex.cpow_one,
        Complex.Gamma_one]
      have : ((4 * Real.pi * m : ℝ) : ℂ) ≠ 0 := by
        have : (0 : ℝ) < m := by exact_mod_cast hm
        exact_mod_cast (by positivity : (0 : ℝ) < 4 * Real.pi * m).ne'
      field_simp
      ring
    · rw [if_neg (by exact_mod_cast h), if_neg h]; ring
  · rw [mul_assoc]
    congr 1
    rw [← tsum_rowExp_mul m n _ (summable_rowExp_mul_gamma0Weight Q hK m n), ← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [rowWeightPlus_gamma0Vec hQ, gamma0Weight, rowSq_eq]
    have hex : cexp (2 * Real.pi * Complex.I * (((((m : ℕ) : ℝ) : ℂ) * (r.1.1 1 : ℂ) +
        (((n : ℕ) : ℝ) : ℂ) * (gammaSetMatrix r.1 0 0 : ℂ)) / (r.1.1 0 : ℂ))) =
        rowExp m n r.1 := by
      rw [rowExp]; push_cast; rfl
    rw [hex]
    have hif : (if ((r.1.1 0 : ℤ) : ZMod Q) = 0 then (1 : ℂ) else 0) =
        (if ((rowModulus r : ℤ) : ZMod Q) = 0 then (1 : ℂ) else 0) := rfl
    rw [hif]
    ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
