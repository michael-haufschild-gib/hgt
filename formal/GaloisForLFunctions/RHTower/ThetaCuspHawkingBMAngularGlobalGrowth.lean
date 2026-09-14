import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularCuspBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries

/-! Global power control of the literal Fourier--Bessel family at every positive height. -/
open Set Filter Topology MeasureTheory Complex Real
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMAngularSeries
noncomputable section
set_option autoImplicit false

private theorem power_exp_bound (x : ℝ) (hx : 0≤x) (n : ℕ) :
    x^n*Real.exp (-x)≤(n.factorial:ℝ) := by
  have h := (div_le_iff₀ (show 0<(n.factorial:ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp x hx n)
  calc
    _ ≤ (Real.exp x*(n.factorial:ℝ))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = _ := by rw [mul_right_comm,← Real.exp_add]; simp

private theorem kernel_power_bound (nu : ℂ) (n : ℕ) {x t : ℝ} (hx : 0<x) (ht : 0≤t) :
    x^n*‖besselOrderKernel x nu t‖≤
      ((n.factorial:ℝ)*2^n)*Real.exp ((‖nu‖-(n:ℝ))*t) := by
  have hc : 0<Real.cosh t := Real.cosh_pos t
  have hP := power_exp_bound (x*Real.cosh t) (mul_pos hx hc).le n
  have hbase : x^n*Real.exp (-x*Real.cosh t)≤(n.factorial:ℝ)/(Real.cosh t)^n := by
    apply (le_div_iff₀ (pow_pos hc n)).mpr
    simpa only [mul_pow,neg_mul,mul_assoc,mul_left_comm,mul_comm] using hP
  have hcosh : Real.exp t/2≤Real.cosh t := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-t)]
  have hden : (n.factorial:ℝ)/(Real.cosh t)^n≤
      (n.factorial:ℝ)*2^n*Real.exp (-(n:ℝ)*t) := by
    calc
      _ ≤ (n.factorial:ℝ)/(Real.exp t/2)^n := by gcongr
      _ = _ := by
        rw [div_pow,← Real.exp_nat_mul,show -(n:ℝ)*t = -((n:ℝ)*t) by ring,Real.exp_neg]
        field_simp
  have he : ‖Complex.exp (-(x:ℂ)*Complex.cosh (t:ℂ))‖=Real.exp (-x*Real.cosh t) := by
    rw [Complex.norm_exp]
    simp [← Complex.ofReal_cosh]
  have hn : ‖nu*(t:ℂ)‖=‖nu‖*t := by simp [abs_of_nonneg ht]
  calc
    _ ≤ x^n*(Real.exp (-x*Real.cosh t)*Real.exp (‖nu‖*t)) := by
      rw [besselOrderKernel,norm_mul,he]
      gcongr
      simpa only [hn] using norm_complex_cosh_le_exp_norm (nu*(t:ℂ))
    _ = (x^n*Real.exp (-x*Real.cosh t))*Real.exp (‖nu‖*t) := by ring
    _ ≤ ((n.factorial:ℝ)*2^n*Real.exp (-(n:ℝ)*t))*Real.exp (‖nu‖*t) :=
      mul_le_mul_of_nonneg_right (hbase.trans hden) (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring

/-- Every integer power above the complex order bounds the actual Bessel integral globally. -/
theorem bessel_global_power_bound (nu : ℂ) (n : ℕ) (hn : ‖nu‖<(n:ℝ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 0<x → x^n*‖modifiedBesselKOrder x nu‖≤C := by
  let B : ℝ→ℝ := fun t => ((n.factorial:ℝ)*2^n)*Real.exp ((‖nu‖-(n:ℝ))*t)
  have hB : IntegrableOn B (Ioi (0:ℝ)) :=
    (integrableOn_exp_mul_Ioi (sub_neg.mpr hn) 0).const_mul _
  refine ⟨∫ t in Ioi (0:ℝ),B t,integral_nonneg (fun _ => by dsimp [B]; positivity),?_⟩
  intro x hx
  have h : ‖∫ t in Ioi (0:ℝ),(x^n:ℝ) • besselOrderKernel x nu t‖≤
      ∫ t in Ioi (0:ℝ),B t := by
    apply norm_integral_le_of_norm_le hB
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hx.le n)] using
      kernel_power_bound nu n hx ht.le
  rw [integral_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hx.le n)] at h
  exact h

private theorem coefficient_power_bound (u : ℂ) (d N : ℕ) :
    ‖coefficient u d N‖≤((N:ℝ)+1)^(3*|u.re|+1+d) := by
  have hn : 0<(N:ℝ)+1 := by positivity
  rw [coefficient,norm_mul,norm_pow,Complex.norm_natCast]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ((N:ℝ)+1)^(3*|u.re|+1)*((N:ℝ)+1)^d := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using
        d4BM_norm_completedEisensteinWhittakerCoefficient_le u ⟨N+1,by omega⟩
    _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_add hn]

/-- A global bound in logarithmic height for every member of the full signed derivative family. -/
theorem value_global_log_growth (u nu : ℂ) (a : ℝ) (d : ℕ) (negative : Bool) :
    ∃ C B : ℝ, 0≤C ∧ 0≤B ∧ ∀ x k : ℝ,
      ‖value u nu a d negative ![x,Real.exp k]‖≤C*Real.exp (B*|k|) := by
  let r : ℝ := 3*|u.re|+1+d
  obtain ⟨n,hn⟩ := exists_nat_gt (max ‖nu‖ (r+2))
  have hnu : ‖nu‖<(n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hr : r-(n:ℝ) < -1 := by have := lt_of_le_of_lt (le_max_right _ _) hn; linarith
  obtain ⟨C,hC,hK⟩ := bessel_global_power_bound nu n hnu
  let M : ℕ→ℝ := fun N => ((N:ℝ)+1)^(r-(n:ℝ))
  have hM : Summable M := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hr)
    simpa only [M,Nat.cast_add,Nat.cast_one] using h
  let A : ℝ := ∑' N, M N
  have hA : 0≤A := tsum_nonneg (fun N => Real.rpow_nonneg (by positivity) _)
  refine ⟨C*A,|a-(n:ℝ)|,mul_nonneg hC hA,abs_nonneg _,?_⟩
  intro x k
  have hy : 0<Real.exp k := Real.exp_pos _
  have hT (N : ℕ) : ‖term u nu a d negative N ![x,Real.exp k]‖≤
      (C*Real.exp ((a-(n:ℝ))*k))*M N := by
    let m : ℝ := (N:ℝ)+1
    have hm : 0 < m := by dsimp [m]; positivity
    have harg : 0<2*Real.pi*m*Real.exp k := by positivity
    have hKn : ‖modifiedBesselKOrder (2*Real.pi*m*Real.exp k) nu‖≤
        C/(2*Real.pi*m*Real.exp k)^n := by
      apply (le_div_iff₀ (pow_pos harg n)).mpr
      simpa only [mul_comm] using hK (2*Real.pi*m*Real.exp k) harg
    have hKm : ‖modifiedBesselKOrder (2*Real.pi*m*Real.exp k) nu‖≤C/(m*Real.exp k)^n := by
      apply hKn.trans
      apply div_le_div_of_nonneg_left hC (pow_pos (mul_pos hm hy) n)
      apply pow_le_pow_left₀ (mul_pos hm hy).le
      have hp : 1≤2*Real.pi := by linarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_right hp (mul_pos hm hy).le]
    have he : m^r*(Real.exp k)^a*(C/(m*Real.exp k)^n)=
        (C*Real.exp ((a-(n:ℝ))*k))*M N := by
      calc
        _ = C*(m^r/m^n)*((Real.exp k)^a/(Real.exp k)^n) := by
          rw [mul_pow]
          field_simp
        _ = _ := by
          rw [← Real.rpow_natCast m n,← Real.rpow_natCast (Real.exp k) n,
            ← Real.rpow_sub hm,← Real.rpow_sub hy,← Real.exp_mul]
          dsimp only [M,m]
          rw [mul_comm k (a-(n:ℝ))]
          ring
    rw [term,norm_mul,norm_mul,norm_mul,d4BM_norm_completedEisensteinFourierPhase,
      mul_one,Complex.norm_real,Real.norm_eq_abs]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    change ‖coefficient u d N‖ * |(Real.exp k)^a| *
      ‖modifiedBesselKOrder (2*Real.pi*m*Real.exp k) nu‖ ≤ _
    rw [abs_of_nonneg (Real.rpow_nonneg hy.le a)]
    calc
      _ ≤ m^r*(Real.exp k)^a*(C/(m*Real.exp k)^n) := by
        gcongr
        · exact coefficient_power_bound u d N
      _ = _ := he
  have hnorm := (term_summable u nu a d negative ![x,Real.exp k] hy).norm
  have hsum := Summable.tsum_le_tsum hT hnorm (hM.mul_left _)
  calc
    _ ≤ ∑' N, ‖term u nu a d negative N ![x,Real.exp k]‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ (C*Real.exp ((a-(n:ℝ))*k))*A := by simpa only [tsum_mul_left,A] using hsum
    _ ≤ (C*A)*Real.exp (|a-(n:ℝ)| * |k|) := by
      rw [mul_right_comm]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (mul_nonneg hC hA)
      exact (le_abs_self _).trans_eq (abs_mul _ _)

end
end RHTower.D4BMAngularSeries
