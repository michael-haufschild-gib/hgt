import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSigma

/-!
# Short logarithmic prefixes with an explicit derivative-order budget

The classical corpus derivative test is reused unchanged. Keeping the actual
short length exposes the two quantities `4^k * lambda` and `H^2 * lambda`.
An exponential budget bounds every prefix uniformly, with the dependence on
`2^k` explicit for the growing-order many-node certificate. Signed Abel
weights cost their literal finite total variation.
-/

open Complex Real Finset
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem short_power_identity {H lam : ℝ} (hH : 0 < H) (hlam : 0 < lam)
    (D : ℝ) :
    H^(1-4/D)*lam^(-(2/D)) = H*(H^2*lam)^(-(2/D)) := by
  rw [Real.mul_rpow (sq_nonneg H) hlam.le,
    ← Real.rpow_natCast H 2, ← Real.rpow_mul hH.le]
  norm_num only [Nat.cast_ofNat]
  have he : (2:ℝ)*(-(2/D)) = -(4/D) := by ring
  rw [he, sub_eq_add_neg, Real.rpow_add hH, Real.rpow_one]
  ring

/-- A quantitative short-prefix bound with every derivative-order loss visible. -/
theorem joint_short_phase_prefix (t : ℝ) (ht : 0 < t) (k n m : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) (hnm : n < m) (hm : m ≤ 2*n+1)
    (U : ℝ) (hU : 0 ≤ U)
    (hsmall : (4:ℝ)^k*(t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k)
      ≤ Real.exp (-U))
    (hlarge : Real.exp U ≤ ((m-n:ℕ):ℝ)^2*
      (t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k)) :
    ∀ r, n ≤ r → r ≤ m →
      ‖∑ j ∈ Finset.Ico n r, (j:ℂ)^(-(Complex.I*(t:ℂ)))‖ ≤
        512*((m-n:ℕ):ℝ)*Real.exp (-U/(2:ℝ)^k) := by
  let lam : ℝ := t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k
  let H : ℝ := ((m-n:ℕ):ℝ)
  let D : ℝ := (2:ℝ)^k
  have hH : 0 < H := by dsimp [H]; exact_mod_cast Nat.sub_pos_of_lt hnm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hf0 : (0:ℝ) < (Nat.factorial (k-1):ℝ) := by
    exact_mod_cast Nat.factorial_pos (k-1)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hD : 4 ≤ D := by
    calc (4:ℝ) = 2^2 := by norm_num
         _ ≤ D := pow_le_pow_right₀ one_le_two hk
  have hD0 : 0 < D := by linarith
  have hD2 : 0 < D-2 := by linarith
  have h4 : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have hsmall' : (4:ℝ)^k*lam ≤ Real.exp (-U) := hsmall
  have hlarge' : Real.exp U ≤ H^2*lam := hlarge
  have hlam1 : lam ≤ 1 := by
    have he : Real.exp (-U) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have hfirst : ((4:ℝ)^k*lam)^(1/(D-2)) ≤ Real.exp (-U/D) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (4:ℝ)^k*lam)
      hsmall' (show 0 ≤ (1:ℝ)/(D-2) from div_nonneg zero_le_one hD2.le)
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have hfrac : 1/D ≤ 1/(D-2) :=
      (div_le_div_iff₀ hD0 hD2).mpr (by linarith)
    have hh := mul_le_mul_of_nonpos_left hfrac (show -U ≤ 0 by linarith)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hh
  have hsecond : (H^2*lam)^(-(2/D)) ≤ Real.exp (-U/D) := by
    have h := Real.rpow_le_rpow_of_nonpos (Real.exp_pos U) hlarge'
      (neg_nonpos.mpr (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hD0.le))
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    have hnonneg : 0 ≤ U/D := div_nonneg hU hD0.le
    calc U * -(2 / D) = -2 * (U/D) := by ring
         _ ≤ -(U/D) := by linarith
         _ = -U/D := by ring
  intro r hnr hrm
  have hp := Sieve.phase_prefix_bound t ht k n m hk hn hnm.le hm hlam1 r hnr hrm
  change _ ≤ 256*(H*((4:ℝ)^k*lam)^(1/(D-2))+
    H^(1-4/D)*lam^(-(2/D))) at hp
  rw [short_power_identity hH hlam] at hp
  have h1 := mul_le_mul_of_nonneg_left hfirst hH.le
  have h2 := mul_le_mul_of_nonneg_left hsecond hH.le
  change _ ≤ 512*H*Real.exp (-U/D)
  linarith

/-- Signed weights require only their literal finite variation, with no monotonicity premise. -/
theorem joint_short_phase_weighted (t : ℝ) (ht : 0 < t) (k n m : ℕ)
    (hk : 2 ≤ k) (hn : 1 ≤ n) (hnm : n < m) (hm : m ≤ 2*n+1)
    (U : ℝ) (hU : 0 ≤ U)
    (hsmall : (4:ℝ)^k*(t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k)
      ≤ Real.exp (-U))
    (hlarge : Real.exp U ≤ ((m-n:ℕ):ℝ)^2*
      (t/(2*Real.pi)*(Nat.factorial (k-1):ℝ)/(2*(n:ℝ))^k))
    (w : ℕ → ℝ) :
    ‖∑ j ∈ Finset.Ico n m, (w j:ℂ)*(j:ℂ)^(-(Complex.I*(t:ℂ)))‖ ≤
      512*((m-n:ℕ):ℝ)*Real.exp (-U/(2:ℝ)^k)*
        ((∑ j ∈ Finset.Ico n m, |w j-w (j+1)|)+|w m|) := by
  let a : ℕ → ℂ := fun j => (j:ℂ)^(-(Complex.I*(t:ℂ)))
  let P : ℝ := 512*((m-n:ℕ):ℝ)*Real.exp (-U/(2:ℝ)^k)
  have hP := joint_short_phase_prefix t ht k n m hk hn hnm hm U hU hsmall hlarge
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico n m) :
      ‖((w j-w (j+1):ℝ):ℂ)*(∑ v ∈ Finset.Ico n (j+1), a v)‖ ≤
        |w j-w (j+1)| * P := by
    rw [Finset.mem_Ico] at hj
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hP (j+1) (by omega) (by omega)) (abs_nonneg _)
  have hend : ‖(w m:ℂ)*(∑ v ∈ Finset.Ico n m, a v)‖ ≤ |w m| * P := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hP m hnm.le le_rfl) (abs_nonneg _)
  change ‖∑ j ∈ Finset.Ico n m, (w j:ℂ)*a j‖ ≤ P*_
  rw [Sieve.sum_weight_mul_eq_abel a w n m hnm.le]
  calc
    _ ≤ ‖∑ j ∈ Finset.Ico n m,
        ((w j-w (j+1):ℝ):ℂ)*(∑ v ∈ Finset.Ico n (j+1), a v)‖+
        ‖(w m:ℂ)*(∑ v ∈ Finset.Ico n m, a v)‖ := norm_add_le _ _
    _ ≤ (∑ j ∈ Finset.Ico n m, |w j-w (j+1)| * P)+|w m| * P :=
      add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) hend
    _ = _ := by rw [← Finset.sum_mul]; ring

end RHTower.WeilWorkPBAP
