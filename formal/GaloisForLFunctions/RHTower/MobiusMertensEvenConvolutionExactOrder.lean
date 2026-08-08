import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionOrderLowerEdge
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.HTGeometry.LogOrderLimsupLower

/-!
# The exact even additive-convolution order law

Littlewood's bound `M(N) = O(N^(Θ+ε))` at the zeta zero abscissa caps every even additive Mertens
convolution: `‖C_k(N)‖ ≤ C^{2k} (N+1)^{2k(1+Θ+ε)-1}` (`norm_mobiusMertensEvenConvolution_le_of_subpower`),
hence `Λ_k ≤ 2k(1+Θ)-1` (`mertensEvenConvolutionOrder_le`).  Together with the one-sided lower edge
this gives the exact affine law

`Λ_k = 2k(1+Θ) - 1`      (`mertensEvenConvolutionOrder_eq`)

for every `k ≥ 1`, and its Riemann-hypothesis form `RH ↔ Λ_k = 3k - 1`
(`riemannHypothesis_iff_mertensEvenConvolutionOrder_eq`).
-/

open Complex Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-! ### From a Mertens subpower bound to the even convolution -/

theorem norm_mobiusAdditiveTriangleSecondCesaro_le_of_subpower {θ C : ℝ}
    (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ θ) (N : ℕ) :
    ‖mobiusAdditiveTriangleSecondCesaro N‖ ≤ C ^ 2 * ((N : ℝ) + 1) ^ (2 * θ + 1) := by
  set X : ℝ := (N : ℝ) + 1 with hXdef
  have hX0 : 0 < X := by rw [hXdef]; positivity
  rw [mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution]
  have hstep : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
      ‖mobiusMertensPartialSum ab.1 * mobiusMertensPartialSum ab.2‖ ≤ C ^ 2 * X ^ (2 * θ) := by
    intro ab hab
    have habSum : ab.1 + ab.2 = N := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have haBase : (ab.1 : ℝ) + 1 ≤ X := by
      rw [hXdef]
      have : (ab.1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ab.1 ≤ N)
      linarith
    have hbBase : (ab.2 : ℝ) + 1 ≤ X := by
      rw [hXdef]
      have : (ab.2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ab.2 ≤ N)
      linarith
    have haPow : ((ab.1 : ℝ) + 1) ^ θ ≤ X ^ θ := Real.rpow_le_rpow (by positivity) haBase hθ
    have hbPow : ((ab.2 : ℝ) + 1) ^ θ ≤ X ^ θ := Real.rpow_le_rpow (by positivity) hbBase hθ
    rw [norm_mul]
    calc
      ‖mobiusMertensPartialSum ab.1‖ * ‖mobiusMertensPartialSum ab.2‖
          ≤ (C * ((ab.1 : ℝ) + 1) ^ θ) * (C * ((ab.2 : ℝ) + 1) ^ θ) :=
            mul_le_mul (hM ab.1) (hM ab.2) (norm_nonneg _)
              (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
      _ ≤ (C * X ^ θ) * (C * X ^ θ) := by gcongr
      _ = C ^ 2 * (X ^ θ * X ^ θ) := by ring
      _ = C ^ 2 * X ^ (2 * θ) := by
          rw [← Real.rpow_add hX0]
          congr 2
          ring
  refine le_trans (le_trans (norm_sum_le _ _) (Finset.sum_le_sum hstep)) ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have hcast : ((N + 1 : ℕ) : ℝ) = X := by rw [hXdef]; push_cast; ring
  rw [hcast]
  have hsplit : X ^ (2 * θ + 1) = X ^ (2 * θ) * X := by
    rw [Real.rpow_add hX0, Real.rpow_one]
  rw [hsplit]
  ring_nf
  exact le_of_eq (by ring)

theorem norm_mobiusMertensEvenConvolution_le_of_subpower {θ C : ℝ}
    (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hM : ∀ N : ℕ, ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ θ) (j N : ℕ) :
    ‖mobiusMertensEvenConvolution (j + 1) N‖
      ≤ (C ^ 2) ^ (j + 1) * ((N : ℝ) + 1) ^ (2 * ((j : ℝ) + 1) * (1 + θ) - 1) := by
  have h := norm_additiveConvolutionPower_succ_le mobiusAdditiveTriangleSecondCesaro
    (A := C ^ 2) (α := 2 * θ + 1) (by positivity) (by linarith)
    (fun M => norm_mobiusAdditiveTriangleSecondCesaro_le_of_subpower hθ hC hM M) j N
  have hexp : ((j + 1 : ℕ) : ℝ) * (2 * θ + 1) + (j : ℝ)
      = 2 * ((j : ℝ) + 1) * (1 + θ) - 1 := by push_cast; ring
  rwa [hexp] at h

/-! ### The upper edge and the exact law -/

/-- **The upper edge `(E10)`.**  `Λ_k ≤ 2k(1+Θ) - 1`. -/
theorem mertensEvenConvolutionOrder_le (j : ℕ) :
    mertensEvenConvolutionOrder (j + 1) ≤ 2 * ((j : ℝ) + 1) * (1 + zetaZeroAbscissa) - 1 := by
  refine le_of_forall_pos_le_add fun dlt hdlt => ?_
  set c : ℝ := 2 * ((j : ℝ) + 1) with hc
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨C, hC, hbound⟩ := mobiusMertens_subpower_zetaZeroAbscissa (dlt / c) (by positivity)
  set A : ℝ := max C 1 with hAdef
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hA0 : (0 : ℝ) < A := by linarith
  have hbound' : ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ A * ((N : ℝ) + 1) ^ (zetaZeroAbscissa + dlt / c) := by
    intro N
    refine (hbound N).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _)
  have hΘ := half_le_zetaZeroAbscissa
  have hθ0 : (0 : ℝ) ≤ zetaZeroAbscissa + dlt / c := by positivity
  have hdeg : 0 ≤ 2 * ((j : ℝ) + 1) * (1 + (zetaZeroAbscissa + dlt / c)) - 1 := by
    nlinarith
  refine le_trans (GaloisForLFunctions.HTGeometry.limsup_log_one_add_div_log_le_rpow
    (C := (A ^ 2) ^ (j + 1))
    (d := 2 * ((j : ℝ) + 1) * (1 + (zetaZeroAbscissa + dlt / c)) - 1)
    (by positivity) hdeg (fun N => le_max_right _ _) (fun N => ?_)) ?_
  · refine max_le ?_ (by positivity)
    exact (Complex.re_le_norm _).trans
      (norm_mobiusMertensEvenConvolution_le_of_subpower hθ0 hA0.le hbound' j N)
  · have hcancel : c * (dlt / c) = dlt := by field_simp
    rw [hc] at hcancel ⊢
    nlinarith [hcancel]

/-- **The exact affine order law `(E3)`.**  `Λ_k = 2k(1 + Θ) - 1`. -/
theorem mertensEvenConvolutionOrder_eq (j : ℕ) :
    mertensEvenConvolutionOrder (j + 1) = 2 * ((j : ℝ) + 1) * (1 + zetaZeroAbscissa) - 1 :=
  le_antisymm (mertensEvenConvolutionOrder_le j) (le_mertensEvenConvolutionOrder j)

/-! ### The Riemann-hypothesis form -/

theorem zetaZeroAbscissa_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) :
    zetaZeroAbscissa = 1 / 2 := by
  refine le_antisymm (csSup_le zetaZeroReSet_nonempty fun x hx => ?_) half_le_zetaZeroAbscissa
  obtain ⟨ρ, hzero, rfl⟩ := hx
  by_cases htriv : ∃ n : ℕ, ρ = -2 * (n + 1)
  · obtain ⟨n, rfl⟩ := htriv
    have hre : ((-2 * ((n : ℂ) + 1)) : ℂ).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re]
    rw [hre]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · by_cases hone : ρ = 1
    · rw [hone] at hzero
      exact absurd hzero (riemannZeta_ne_zero_of_one_le_re (by simp))
    · exact le_of_eq (hRH ρ hzero htriv hone)

theorem riemannHypothesis_of_zetaZeroAbscissa_eq_half (h : zetaZeroAbscissa = 1 / 2) :
    RiemannHypothesis := by
  intro ρ hzero htriv _
  have htriv' : ∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1)) := by
    intro n hn
    exact htriv ⟨n, by linear_combination hn⟩
  have hupper : ρ.re ≤ 1 / 2 := by
    rw [← h]
    exact re_le_zetaZeroAbscissa hzero
  have hlt1 : ρ.re < 1 := by linarith
  have hpos : 0 < ρ.re := riemannZeta_zero_re_pos hzero htriv'
  have hrefl := riemannZeta_one_sub_eq_zero_of_mem_openStrip hzero hpos hlt1
  have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by simp
  have hle := re_le_zetaZeroAbscissa hrefl
  rw [hre, h] at hle
  linarith

/-- **The Riemann-hypothesis form `(E4)`.**  For one, hence every, `k ≥ 1`, RH is equivalent to the
even additive Mertens convolution order being exactly `3k - 1`. -/
theorem riemannHypothesis_iff_mertensEvenConvolutionOrder_eq (j : ℕ) :
    RiemannHypothesis ↔ mertensEvenConvolutionOrder (j + 1) = 3 * ((j : ℝ) + 1) - 1 := by
  have hjR : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  constructor
  · intro hRH
    rw [mertensEvenConvolutionOrder_eq j, zetaZeroAbscissa_eq_half_of_riemannHypothesis hRH]
    ring
  · intro hval
    refine riemannHypothesis_of_zetaZeroAbscissa_eq_half ?_
    have heq := mertensEvenConvolutionOrder_eq j
    rw [hval] at heq
    have hc : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by linarith
    nlinarith [heq]

end

end RHTower
