import GaloisForLFunctions.RHTower.WeilWorkExposingRayLogLocalMass

/-!
# Absolute Dirichlet convergence from actual critical polar separators

The square-root local absolute mass bound is summed over dyadic intervals.
The half-plane of absolute convergence is derived from the actual source
inequality, with no coefficient-growth assumption in the public theorem.
-/

open MeasureTheory Filter Topology Finset
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilOneSided WeilMeanSquare

private theorem summable_of_sqrt_log_mass {b : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 2 N, |b n|) ≤ C*Real.sqrt N*(1+Real.log N))
    {p : ℝ} (hp : 1/2 < p) :
    Summable fun n : ℕ => |b n| / (n : ℝ)^p := by
  let r : ℝ := (2 : ℝ)^(1/2-p)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let v : ℕ → ℝ := fun j => 2*C*r^j*(1+((j : ℝ)+1)*Real.log 2)
  have hvs : Summable v := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖r‖ < 1 by rw [Real.norm_eq_abs,abs_of_nonneg hr0]; exact hr1)).mul_left
      (2*C*Real.log 2)
    have h2 := (summable_geometric_of_lt_one hr0 hr1).mul_left (2*C*(1+Real.log 2))
    refine (h1.add h2).congr fun j => ?_
    simp only [v,pow_one]
    ring
  have hv0 : ∀ j, 0 ≤ v j := fun j => by
    dsimp [v]
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  let f : ℕ → ℝ := fun n => |b n|/(n : ℝ)^p
  have hf0 : ∀ n, 0 ≤ f n := fun n => by dsimp [f]; positivity
  have hblock : ∀ j : ℕ, ∑ n ∈ Finset.Ioc (2^j) (2^(j+1)), f n ≤ v j := by
    intro j
    let N : ℕ := 2^j
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h2N : 2^(j+1)=2*N := by dsimp [N]; rw [pow_succ,mul_comm]
    have hlog : Real.log (2*N : ℕ)=((j : ℝ)+1)*Real.log 2 := by
      rw [← h2N,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      push_cast
      ring
    have hlog0 : 0 ≤ 1+Real.log (2*N : ℕ) := by rw [hlog]; positivity
    have hsqrt : Real.sqrt (2*N : ℕ) ≤ 2*Real.sqrt N := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (2*N : ℕ) by positivity)
      have hsqN := Real.sq_sqrt hN0.le
      have hn := Real.sqrt_nonneg (N : ℝ)
      push_cast at hsq
      rw [Nat.cast_mul,Nat.cast_ofNat]
      nlinarith
    have habs : (∑ n ∈ Finset.Ioc N (2*N), |b n|) ≤
        2*C*Real.sqrt N*(1+Real.log (2*N : ℕ)) := by
      have hsub : (∑ n ∈ Finset.Ioc N (2*N), |b n|) ≤
          ∑ n ∈ Finset.Icc 2 (2*N), |b n| :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro n hn; obtain ⟨hn1,hn2⟩ := Finset.mem_Ioc.mp hn
              exact Finset.mem_Icc.mpr ⟨by omega,hn2⟩)
          (fun n _ _ => abs_nonneg (b n))
      have hbound := hmass (2*N) (by omega)
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsqrt hC) hlog0
      nlinarith only [hsub,hbound,hmul]
    have hNpow : ∀ n ∈ Finset.Ioc N (2*N), f n ≤ |b n|/(N : ℝ)^p := by
      intro n hn
      dsimp [f]
      refine div_le_div_of_nonneg_left (abs_nonneg _) (Real.rpow_pos_of_pos hN0 _) ?_
      exact Real.rpow_le_rpow hN0.le (by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le)
        (by linarith)
    have hratio : Real.sqrt N/(N : ℝ)^p=r^j := by
      have eN : (N : ℝ)=(2 : ℝ)^(j : ℝ) := by
        dsimp [N]
        rw [Nat.cast_pow,Nat.cast_ofNat,Real.rpow_natCast]
      rw [Real.sqrt_eq_rpow,eN,← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num),← Real.rpow_sub (by norm_num)]
      dsimp [r]
      rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [h2N]
    calc
      _ ≤ ∑ n ∈ Finset.Ioc N (2*N), |b n|/(N : ℝ)^p := Finset.sum_le_sum hNpow
      _ = (∑ n ∈ Finset.Ioc N (2*N), |b n|)/(N : ℝ)^p := by rw [Finset.sum_div]
      _ ≤ (2*C*Real.sqrt N*(1+Real.log (2*N : ℕ)))/(N : ℝ)^p :=
        div_le_div_of_nonneg_right habs (Real.rpow_nonneg hN0.le _)
      _ = v j := by
        rw [hlog]
        have he : 2*C*Real.sqrt N*(1+((j : ℝ)+1)*Real.log 2)/(N : ℝ)^p =
            2*C*(Real.sqrt N/(N : ℝ)^p)*(1+((j : ℝ)+1)*Real.log 2) := by ring
        rw [he,hratio]
  have hdyad : ∀ J : ℕ, ∑ n ∈ Finset.Ioc 1 (2^J), f n ≤ ∑ j ∈ Finset.range J, v j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive f Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)),Finset.sum_range_succ]
      exact add_le_add ih (hblock J)
  refine summable_of_sum_range_le (c := f 0+f 1+∑' j,v j) hf0 fun T => ?_
  have hT : T ≤ 2^T := Nat.lt_two_pow_self.le
  calc
    _ ≤ ∑ n ∈ Finset.range (2^T+1), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun n _ _ => hf0 n)
    _ = f 0+f 1+∑ n ∈ Finset.Ioc 1 (2^T), f n :=
      sum_range_succ_eq_Ioc f (2^T) Nat.one_le_two_pow
    _ ≤ f 0+f 1+∑' j,v j := by
      have hh := (hdyad T).trans (hvs.sum_le_tsum _ fun j _ => hv0 j)
      linarith

/-- Every actual logarithmic polar separator has an absolutely convergent
coefficient Dirichlet series throughout Re(s)>1/2. -/
theorem summable_critical_separator_coefficients
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 (by norm_num : (0 : ℝ) ≤ 1) le_rfl f))
    {p : ℝ} (hp : 1/2 < p) : Summable fun n : ℕ => |b n|/(n : ℝ)^p := by
  obtain ⟨C,hC,hmass⟩ := exists_sqrt_log_mass_of_polar_bound
    (by norm_num : (0 : ℝ) ≤ 1) le_rfl h
  simp only [Real.rpow_one] at hmass
  exact summable_of_sqrt_log_mass hC hmass hp

end RHTower.ExposingRayTransfer
