import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularCuspBounds
import Mathlib.Analysis.Complex.SummableUniformlyOn

/-!
Entire spectral dependence of the full scalar Fourier–Bessel tail, proved using a locally uniform summable majorant for the original infinite series.
-/

open Complex Real Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMAngularSeries
noncomputable section

/-- Each literal arithmetic Fourier coefficient is entire in the spectral parameter. -/
theorem whittakerCoefficient_differentiable (n : D4BMPositiveIndex) :
    Differentiable ℂ (fun u => d4BMCompletedEisensteinWhittakerCoefficient u n) := by
  intro u
  unfold d4BMCompletedEisensteinWhittakerCoefficient
  refine (differentiableAt_id.const_cpow (.inl (by exact_mod_cast n.2.ne'))).mul ?_
  apply DifferentiableAt.fun_sum
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) n.2
  exact (differentiableAt_id.const_mul (-2)).const_cpow (.inl (by exact_mod_cast hd0.ne'))

private theorem spectralTerm_differentiable (negative : Bool) (N : ℕ)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    Differentiable ℂ (fun u => term u u (1/2) 0 negative N z) := by
  have hc := whittakerCoefficient_differentiable ⟨N+1,by omega⟩
  have hK := differentiable_modifiedBesselKOrder
    (by positivity : 0 < 2*Real.pi*((N:ℝ)+1)*z 1)
  simpa only [term,coefficient,pow_zero,mul_one] using!
    ((hc.mul_const (d4BMCompletedEisensteinFourierPhase negative N (z 0))).mul_const
      (Real.rpow (z 1) (1/2) : ℂ)).mul hK

/-- A locally uniform spectral majorant for every actual signed Fourier mode. -/
theorem spectralTerm_majorant (negative : Bool) (z : Fin 2 → ℝ) (hz : 0 < z 1)
    (R : ℝ) (hR : 0 < R) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ N u, u ∈ Metric.ball (0:ℂ) R →
      ‖term u u (1/2) 0 negative N z‖ ≤ M N := by
  let r := 3*R+1
  let D := Real.exp (R^(2 : ℕ)/(2*z 1))*Real.sqrt (2*Real.pi/z 1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let M := fun N : ℕ => ((z 1)^(1/2:ℝ)*D)*
    (((N:ℝ)+1)^r * Real.exp (-((N:ℝ)*z 1)))
  refine ⟨M, (summable_natSucc_rpow_exp_neg_and_tsum_le hr hz).1.mul_left _, ?_⟩
  intro N u hu
  have hun : ‖u‖ ≤ R := (by simpa only [Metric.mem_ball,dist_zero_right] using hu : ‖u‖ < R).le
  have hN : (1:ℝ) ≤ (N:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hcoef : ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N+1,by omega⟩‖ ≤
      ((N:ℝ)+1)^r := by
    calc
      _ ≤ ((N+1:ℕ):ℝ)^(3*|u.re|+1) := d4BM_norm_completedEisensteinWhittakerCoefficient_le _ _
      _ ≤ _ := by
        simp only [Nat.cast_add,Nat.cast_one]
        apply Real.rpow_le_rpow_of_exponent_le hN
        dsimp [r]
        linarith [(Complex.abs_re_le_norm u).trans hun]
  have hBC : besselBound u (z 1) ≤ D := by
    dsimp [besselBound,D]
    gcongr
  have hK : ‖modifiedBesselKOrder (2*Real.pi*((N:ℝ)+1)*z 1) u‖ ≤
      D*Real.exp (-((N:ℝ)*z 1)) := by
    calc
      _ ≤ besselBound u (z 1)*Real.exp (-(((N:ℝ)+1)*z 1)) :=
        bessel_local_bound u (z 1) hz N (z 1) le_rfl
      _ ≤ _ := by
        apply mul_le_mul hBC
        · apply Real.exp_le_exp.mpr
          linarith
        · positivity
        · exact hD
  simp only [term,coefficient,pow_zero,mul_one,norm_mul,
    d4BM_norm_completedEisensteinFourierPhase]
  rw [Complex.norm_real,Real.norm_eq_abs,Real.rpow_eq_pow,
    abs_of_nonneg (Real.rpow_nonneg hz.le (1/2))]
  calc
    _ ≤ ((N:ℝ)+1)^r * (z 1)^(1/2:ℝ) *
        (D*Real.exp (-((N:ℝ)*z 1))) := by gcongr
    _ = _ := by dsimp [M]; ring

/-- The complete infinite signed scalar tail is entire in the spectral parameter. -/
theorem scalarValue_spectral_differentiable (negative : Bool)
    (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    Differentiable ℂ (fun u => value u u (1/2) 0 negative z) := by
  intro u0
  let R : ℝ := ‖u0‖+1
  obtain ⟨M,hM,hb⟩ := spectralTerm_majorant negative z hz R (by dsimp [R]; positivity)
  have ht := (tendstoUniformlyOn_tsum hM hb).tendstoLocallyUniformlyOn
  have hd := ht.differentiableOn (Filter.Eventually.of_forall fun t =>
    (fun u _ => (DifferentiableAt.fun_sum fun n _ => spectralTerm_differentiable negative n z hz u).differentiableWithinAt))
    Metric.isOpen_ball
  apply hd.differentiableAt
  apply Metric.isOpen_ball.mem_nhds
  simp [Metric.mem_ball,R]

end
end RHTower.D4BMAngularSeries
