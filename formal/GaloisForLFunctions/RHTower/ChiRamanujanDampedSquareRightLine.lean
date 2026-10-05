import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareAxis
import GaloisForLFunctions.RHTower.Sieve.PSeriesTailAboveCutoff

/-!
# Uniform damping-squared control of the original BAG square series

The complete finite prime product gives `Dε(n) ≤ ε log n` for every `n>1`.
A summable logarithmic-square majorant then bounds the entire original
Dirichlet line by `24 ε² / b³`, uniformly in its imaginary part.
Subtracting the n=1 term and dividing by ε² preserves this control even
when damping tends to zero arbitrarily fast. No integer or prime-power
terms are discarded.
-/

noncomputable section
open Real Set Filter Complex
open scoped BigOperators Topology
namespace RHTower.BAGTrace

/-- The complete divisor coefficient retains one damping factor for every n>1. -/
theorem pmPowerDampedDivisorCoeff_le_damping_log {ε : ℝ} (hε : 0 ≤ ε)
    {n : ℕ} (hn : 1 < n) : pmPowerDampedDivisorCoeff ε n ≤ ε*Real.log n := by
  obtain ⟨p,hp,hpn⟩ := Nat.exists_prime_and_dvd hn.ne'
  have hn0 : n ≠ 0 := by omega
  have hpm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpn,hn0⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpp : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hple : (p : ℝ) ≤ n := by exact_mod_cast Nat.le_of_dvd (by omega : 0 < n) hpn
  rw [pmPowerDampedDivisorCoeff_eq_prod ε hn0]
  calc
    (∏ q ∈ n.primeFactors, (1-(q : ℝ)^(-ε))) ≤ 1-(p : ℝ)^(-ε) := by
      have h := Finset.prod_le_prod_of_subset_of_le_one
        (f := fun q : ℕ => 1-(q : ℝ)^(-ε))
        (Finset.singleton_subset_iff.mpr hpm)
        (fun q hq => sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le) (neg_nonpos.mpr hε)))
        (fun q _ _ => by linarith [Real.rpow_nonneg (Nat.cast_nonneg q) (-ε)])
      simpa using h
    _ ≤ ε*Real.log p := by
      rw [Real.rpow_def_of_pos hp0]
      have h := Real.add_one_le_exp (Real.log p*(-ε))
      nlinarith
    _ ≤ ε*Real.log n := mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hple) hε

private theorem log_sq_le_rpow {b : ℝ} (hb : 0 < b) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x)^2 ≤ (8/b^2)*x^(b/2) := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_nonneg hx
  have hz : 0 ≤ b*Real.log x/2 := by positivity
  have hh := Real.pow_div_factorial_le_exp (b*Real.log x/2) hz 2
  norm_num at hh
  rw [Real.rpow_def_of_pos hx0]
  have he : b*Real.log x/2 = Real.log x*(b/2) := by ring
  rw [he] at hh
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos hb)]
  nlinarith

private theorem tsum_rpow_bound {c : ℝ} (hc : 1 < c) :
    (∑' n : ℕ, (n : ℝ)^(-c)) ≤ c/(c-1) := by
  apply Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  intro N
  have hsub : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_insert,Finset.mem_Icc]
    omega
  calc
    (∑ n ∈ Finset.range N,(n : ℝ)^(-c)) ≤
      ∑ n ∈ insert 0 (Finset.Icc 1 N),(n : ℝ)^(-c) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = ∑ n ∈ Finset.Icc 1 N,(n : ℝ)^(-c) := by
      rw [Finset.sum_insert (by simp)]
      simp [Real.zero_rpow (by linarith : -c ≠ 0)]
    _ ≤ c/(c-1) := by
      simpa using Sieve.sum_rpow_neg_tail_le hc (R := 1) (N := N) (by omega)

private theorem square_log_term_bound {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (Real.log n)^2*(n : ℝ)^(-(1+b)) ≤ (8/b^2)*(n : ℝ)^(-(1+b/2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero,Real.log_zero,pow_two,zero_mul]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ ((8/b^2)*(n : ℝ)^(b/2))*(n : ℝ)^(-(1+b)) := by
      gcongr
      exact log_sq_le_rpow hb hn1
    _ = _ := by
      rw [mul_assoc,← Real.rpow_add hn0]
      congr 2
      ring

/-- A uniform logarithmic-square majorant for the original Dirichlet line. -/
theorem summable_dampedSquare_log_majorant {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => (Real.log n)^2*(n : ℝ)^(-(1+b))) := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(1+b/2))) :=
    (Real.summable_nat_rpow.mpr (by linarith))
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (square_log_term_bound hb) (hs.mul_left (8/b^2))

/-- The bound is polynomial in the line's distance from one and independent of damping. -/
theorem tsum_dampedSquare_log_majorant_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    (∑' n : ℕ, (Real.log n)^2*(n : ℝ)^(-(1+b))) ≤ 24/b^3 := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-(1+b/2))) :=
    (Real.summable_nat_rpow.mpr (by linarith))
  have hc : 1 < 1+b/2 := by linarith
  calc
    _ ≤ ∑' n : ℕ,(8/b^2)*(n : ℝ)^(-(1+b/2)) :=
      (summable_dampedSquare_log_majorant hb).tsum_le_tsum
        (square_log_term_bound hb) (hs.mul_left (8/b^2))
    _ = (8/b^2)*(∑' n : ℕ,(n : ℝ)^(-(1+b/2))) := tsum_mul_left
    _ ≤ (8/b^2)*((1+b/2)/(1+b/2-1)) :=
      mul_le_mul_of_nonneg_left (tsum_rpow_bound hc) (by positivity)
    _ ≤ 24/b^3 := by
      rw [show 1+b/2-1 = b/2 by ring]
      have he : (8/b^2)*((1+b/2)/(b/2)) = (16+8*b)/b^3 := by
        field_simp
        ring
      rw [he,div_le_div_iff_of_pos_right (pow_pos hb 3)]
      linarith

/-- The complete original right-line source has a damping-squared bound, uniformly in height. -/
theorem norm_dampedSquareDirichlet_sub_one_le {ε b : ℝ} (hε : 0 ≤ ε)
    (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    ‖dampedSquareDirichlet ε ((1+b : ℝ)+t*I)-1‖ ≤ 24*ε^2/b^3 := by
  let s : ℂ := (1+b : ℝ)+t*I
  let f : ℕ → ℂ := fun n => (pmPowerDampedDivisorCoeff ε n : ℂ)^2*(n : ℂ)^(-s)
  let a : ℕ → ℝ := fun n => (Real.log n)^2*(n : ℝ)^(-(1+b))
  have hs : 1 < s.re := by dsimp [s]; simp; linarith
  have hf : Summable f := summable_dampedSquareDirichlet hε hs
  have ha : Summable a := summable_dampedSquare_log_majorant hb
  have hfshift : Summable (fun n : ℕ => f (n+2)) :=
    (summable_nat_add_iff 2).mpr hf
  have hashift : Summable (fun n : ℕ => a (n+2)) :=
    (summable_nat_add_iff 2).mpr ha
  have hfeq : dampedSquareDirichlet ε s-1 = ∑' n : ℕ, f (n+2) := by
    have h := hf.sum_add_tsum_nat_add 2
    have hh : (∑ n ∈ Finset.range 2,f n) = 1 := by
      simp [Finset.sum_range_succ,f,pmPowerDampedDivisorCoeff_zero,pmPowerDampedDivisorCoeff_one]
    rw [hh] at h
    change 1+(∑' n : ℕ, f (n+2)) = dampedSquareDirichlet ε s at h
    linear_combination -h
  have haeq : (∑' n : ℕ,a (n+2)) = ∑' n : ℕ,a n := by
    have h := ha.sum_add_tsum_nat_add 2
    simpa [Finset.sum_range_succ,a] using h
  have hterm : ∀ n : ℕ, ‖f (n+2)‖ ≤ ε^2*a (n+2) := by
    intro n
    have hn : 1 < n+2 := by omega
    have hn0 : 0 < n+2 := by omega
    have hd0 := pmPowerDampedDivisorCoeff_nonneg hε (n+2)
    have hd := pmPowerDampedDivisorCoeff_le_damping_log hε hn
    have hd2 : pmPowerDampedDivisorCoeff ε (n+2)^2 ≤ ε^2*(Real.log (n+2))^2 := by
      simpa only [mul_pow,Nat.cast_add,Nat.cast_ofNat] using pow_le_pow_left₀ hd0 hd 2
    dsimp only [f,a]
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hd0,
      Complex.norm_natCast_cpow_of_pos hn0]
    have he : (-s).re = -(1+b) := by simp [s]
    rw [he]
    simpa only [Nat.cast_add,Nat.cast_ofNat,mul_assoc] using
      mul_le_mul_of_nonneg_right hd2 (Real.rpow_nonneg (Nat.cast_nonneg (n+2)) (-(1+b)))
  change ‖dampedSquareDirichlet ε s-1‖ ≤ _
  rw [hfeq]
  calc ‖∑' n : ℕ,f (n+2)‖ ≤ ∑' n : ℕ,‖f (n+2)‖ := norm_tsum_le_tsum_norm hfshift.norm
    _ ≤ ∑' n : ℕ,ε^2*a (n+2) :=
      hfshift.norm.tsum_le_tsum hterm (hashift.mul_left (ε^2))
    _ = ε^2*(∑' n : ℕ,a (n+2)) := tsum_mul_left
    _ = ε^2*(∑' n : ℕ,a n) := by rw [haeq]
    _ ≤ ε^2*(24/b^3) := mul_le_mul_of_nonneg_left
      (tsum_dampedSquare_log_majorant_le hb hb1) (sq_nonneg ε)
    _ = 24*ε^2/b^3 := by ring

/-- Division by damping squared is harmless on the entire original line, even as ε→0. -/
theorem norm_dampedSquareDirichlet_normalized_le {ε b : ℝ} (hε : 0 < ε)
    (hb : 0 < b) (hb1 : b ≤ 1) (t : ℝ) :
    ‖(dampedSquareDirichlet ε ((1+b : ℝ)+t*I)-1)/(ε : ℂ)^2‖ ≤ 24/b^3 := by
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hε.le,
    div_le_iff₀ (sq_pos_of_pos hε)]
  calc
    _ ≤ 24*ε^2/b^3 := norm_dampedSquareDirichlet_sub_one_le hε.le hb hb1 t
    _ = _ := by ring

end RHTower.BAGTrace
