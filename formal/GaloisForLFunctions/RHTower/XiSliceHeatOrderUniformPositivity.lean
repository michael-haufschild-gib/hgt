import GaloisForLFunctions.RHTower.XiSliceHeatThresholdVerificationHeight

/-!
# All-height heated slice positivity at every order above `C/λ`

**Theorem** (`exists_xiSliceHeatTransfer_pos_order_ge_inv_heat`).  There is an absolute `C > 0` such
that for every heat `0 < λ ≤ 1`, every height `t` and every order `2n` with `n ≥ C/λ`,

  `T_{2n}(λ, 0, t) > 0`,

where `T_m(λ, 0, t)` is the `m`-th Taylor coefficient of `e^{(λ/2)∂_x²}[ξ(½+x+it) ξ(½−x+it)]` at
`x = 0`.  So at arbitrarily small heat, all-height coefficient positivity holds for every order
beyond `C/λ`, uniformly in the height: the RH content of the heated slice at heat `λ` lies in the
finite order range `n < C/λ` (and, by the effective Ki–Kim–Lee bound, at heights `|t| < e^{100/λ}`).

Proof.  Fix `λ`, `t ≥ 0` (even orders are even in the height, `xiSliceHeatTransfer_neg_height`).
* If `t ≥ t₀` and `λ ≥ 100/log t`, every even order is positive (effective slice Ki–Kim–Lee,
  `exists_xiSliceHeatTransfer_pos_heat_over_log`).
* Otherwise `½ log t ≤ max(½ log t₀, 50/λ) ≤ C/λ ≤ n`, so every unheated coefficient `c_{2m}(t)` with
  `m ≥ n` is positive (sharp window `m ≥ max(K, ½ log t)`, `exists_xiSliceCoeff_pos_above_quarter_log`),
  and the heat series `T_{2n} = Σ_k w_k c_{2n+2k}`, `w_0 = 1`, `w_k ≥ 0`, is positive.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-- **Order-uniform all-height positivity at arbitrarily small heat.** -/
theorem exists_xiSliceHeatTransfer_pos_order_ge_inv_heat :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ t : ℝ, ∀ n : ℕ, C / lam ≤ n →
      0 < xiSliceHeatTransfer lam 0 t (2 * n) := by
  obtain ⟨t₀, ht₀, hkkl⟩ := exists_xiSliceHeatTransfer_pos_heat_over_log
  obtain ⟨K, hK⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  set C := max (max K (Real.log t₀ / 2)) 50 with hCdef
  have hC50 : 50 ≤ C := le_max_right _ _
  have hCK : K ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hClog : Real.log t₀ / 2 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C, by linarith, fun lam hlam hlam1 t n hn => ?_⟩
  have hCle : C ≤ C / lam := by
    rw [le_div_iff₀ hlam]; nlinarith
  wlog ht : 0 ≤ t generalizing t
  · have h := this (-t) (by linarith)
    rwa [xiSliceHeatTransfer_neg_height hlam] at h
  by_cases hbig : t₀ ≤ t ∧ 100 / Real.log t ≤ lam
  · exact hkkl t (by rw [abs_of_nonneg ht]; exact hbig.1) lam
      (by rw [abs_of_nonneg ht]; exact hbig.2) n
  -- below the Ki–Kim–Lee range every order `≥ 2n` is in the sharp positivity window
  have hlogn : (1 / 4 + 1 / 4 : ℝ) * Real.log t ≤ n := by
    rcases not_and_or.mp hbig with hsmall | hheat
    · have hlog : Real.log t ≤ Real.log t₀ := by
        rcases ht.eq_or_lt with h0 | hpos
        · rw [← h0, Real.log_zero]; exact Real.log_nonneg (by linarith)
        · exact Real.log_le_log hpos (by linarith)
      linarith
    · push Not at hheat
      have ht1 : 1 < t := by
        by_contra h1
        push Not at h1
        have : Real.log t ≤ 0 := Real.log_nonpos ht h1
        have : 100 / Real.log t ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) this
        linarith
      have hlogpos : 0 < Real.log t := Real.log_pos ht1
      have hlt : Real.log t < 100 / lam := by
        rw [lt_div_iff₀ hlogpos] at hheat
        rw [lt_div_iff₀ hlam]; linarith
      have h50 : 50 / lam ≤ C / lam := div_le_div_of_nonneg_right hC50 hlam.le
      have : (1 / 4 + 1 / 4 : ℝ) * Real.log t < 50 / lam := by
        have e : (50 : ℝ) / lam = (1 / 2) * (100 / lam) := by ring
        rw [e]; linarith
      linarith
  have hcoef : ∀ k : ℕ, 0 < xiSliceCoeff t (2 * n + 2 * k) := by
    intro k
    rw [show 2 * n + 2 * k = 2 * (n + k) by ring]
    refine hK t ht (n + k) (max_le ?_ ?_)
    · have : (n : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast Nat.le_add_right n k
      linarith
    · have : (n : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast Nat.le_add_right n k
      linarith
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam.le 0 t (2 * n)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ ((((lam / 2) ^ k / k.factorial *
      ((2 * n + 2 * k).factorial / (2 * n).factorial) : ℝ) : ℂ) *
        xiSliceCoeff t (2 * n + 2 * k)) := fun k =>
    mul_nonneg (Complex.zero_le_real.mpr (by positivity)) (hcoef k).le
  have h0 : 0 < ((((lam / 2) ^ 0 / (0 : ℕ).factorial *
      ((2 * n + 2 * 0).factorial / (2 * n).factorial) : ℝ) : ℂ) *
        xiSliceCoeff t (2 * n + 2 * 0)) := by
    have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    simpa [hfac] using hcoef 0
  exact lt_of_lt_of_le h0 (le_hasSum hT 0 fun j _ => hterm j)

end

end RHTower.DeBruijn
