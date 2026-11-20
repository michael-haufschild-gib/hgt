import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheCriticalLogarithmicPowerOfTheMoebiusDiagonal
import GaloisForLFunctions.RHTower.SteinhausModel
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fractional integration of critical-line Möbius jets

On the nonconstant Dirichlet modes the horizontal translation semigroup
has positive frequencies log n. The Gamma integral for the Riesz potential
used by Qiu and Roberto cancels a fractional
number of derivatives. Steinhaus orthogonality reduces the exact second
moment of every filtered jet to a squarefree logarithmic diagonal.
The boundedness threshold in the polynomial length is α > k + 1/2.
-/

noncomputable section
open Finset MeasureTheory Set ArithmeticFunction
open RHTower.SteinhausModel
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def amplitude (n : ℕ) : ℝ := (moebius n:ℤ)/Real.sqrt n

/-- Centered random Möbius polynomial based at the critical line. -/
def centeredRandomMoebius (N : ℕ) (ω : Omega) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 N, ((amplitude n:ℂ)*X n ω)*Complex.exp (-(Real.log n:ℂ)*s)

/-- Riesz potential of the kth derivative, evaluated at the critical line. -/
def moebiusJetPotential (N k : ℕ) (α : ℝ) (ω : Omega) : ℂ :=
  (∫ t : ℝ in Ioi 0, ((t^(α-1):ℝ):ℂ)*iteratedDeriv k (centeredRandomMoebius N ω) t) /
    (Real.Gamma α:ℂ)

/-- Fourier amplitude after horizontal differentiation and fractional integration. -/
def moebiusJetAmplitude (k : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  amplitude n*(-Real.log n)^k*(Real.log n)^(-α)

private theorem gamma_mode_integrable {α L : ℝ} (hα : 0 < α) (hL : 0 < L) :
    IntegrableOn (fun t : ℝ => t^(α-1)*Real.exp (-(L*t))) (Ioi 0) := by
  simpa only [Real.rpow_one,neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=α-1) (b:=L)
      (by linarith only [hα]) le_rfl hL)

/-- Exact multiplier of the fractional integral on all nonconstant modes.
The restriction to n ≥ 2 removes the stationary mode. -/
theorem moebiusJetPotential_fourier (N k : ℕ) {α : ℝ} (hα : 0 < α) (ω : Omega) :
    moebiusJetPotential N k α ω =
      ∑ n ∈ Finset.Icc 2 N, (moebiusJetAmplitude k α n:ℂ)*X n ω := by
  let c (n : ℕ) : ℂ := ((amplitude n:ℂ)*X n ω)*(-(Real.log n:ℂ))^k
  let g (n : ℕ) (t : ℝ) := t^(α-1)*Real.exp (-(Real.log n*t))
  have hl {n : ℕ} (hn : n ∈ Finset.Icc 2 N) : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
  have hi (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      IntegrableOn (fun t : ℝ => c n*(g n t:ℂ)) (Ioi 0) :=
    (Complex.ofRealCLM.integrable_comp (gamma_mode_integrable hα (hl hn))).const_mul _
  have hjet (t : ℝ) : ((t^(α-1):ℝ):ℂ)*iteratedDeriv k (centeredRandomMoebius N ω) t =
      ∑ n ∈ Finset.Icc 2 N, c n*(g n t:ℂ) := by
    rw [centeredRandomMoebius,iteratedDeriv_fun_sum (fun i hi => by fun_prop),mul_sum]
    apply sum_congr rfl
    intro n _
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_cexp_const_mul]
    simp only [g,c,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,neg_mul]
    ring
  have hΓ : (Real.Gamma α:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos hα).ne'
  rw [moebiusJetPotential]
  simp_rw [hjet]
  rw [integral_finsetSum _ hi,sum_div]
  apply sum_congr rfl
  intro n hn
  rw [integral_const_mul,integral_complex_ofReal,show (∫ t in Ioi 0, g n t) = _ from
    Real.integral_rpow_mul_exp_neg_mul_Ioi hα (hl hn),one_div,Real.inv_rpow (hl hn).le,
    ←Real.rpow_neg (hl hn).le]
  simp only [c,moebiusJetAmplitude,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg]
  field_simp [hΓ]
  <;> ring

/-- The logarithmic power left on each nonconstant mode after filtering. -/
theorem moebiusJetAmplitude_sq (k : ℕ) (α : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    moebiusJetAmplitude k α n ^ 2 =
      ((moebius n:ℤ):ℝ)^2/(n:ℝ)*(Real.log n)^(2*((k:ℝ)-α)) := by
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n from hn))
  have hsq : ((-Real.log n)^k)^2 = (Real.log n)^(2*(k:ℝ)) := by
    calc _ = ((Real.log n)^k)^2 := by rw [←sq_abs ((-Real.log n)^k),abs_pow,abs_neg,abs_of_pos hL]
         _ = (Real.log n)^((k:ℝ)*2) := by
           rw [Real.rpow_mul hL.le,Real.rpow_natCast,Real.rpow_two]
         _ = _ := by rw [mul_comm]
  rw [moebiusJetAmplitude,mul_pow,mul_pow,amplitude,div_pow,Real.sq_sqrt (Nat.cast_nonneg _),hsq,
    ←Real.rpow_mul_natCast hL.le, mul_assoc,←Real.rpow_add hL]
  congr 2
  push_cast
  ring

/-- Exact model second moment of every horizontally integrated derivative,
including the endpoint and cutoffs below the first nonconstant term. -/
theorem moebiusJetPotential_second_moment (N k : ℕ) {α : ℝ} (hα : 0 < α) :
    (∫ ω, ‖moebiusJetPotential N k α ω‖^2 ∂steinhausMeasure) =
      ∑ n ∈ Finset.Icc 2 N, ((moebius n:ℤ):ℝ)^2/(n:ℝ)*(Real.log n)^(2*((k:ℝ)-α)) := by
  simp_rw [moebiusJetPotential_fourier N k hα]
  rw [integral_normSq_dpoly _ _ (fun n hn => by have := (Finset.mem_Icc.mp hn).1; omega)]
  exact sum_congr rfl fun n hn => moebiusJetAmplitude_sq k α (Finset.mem_Icc.mp hn).1

/-- The least amount of fractional integration that bounds the kth random
Möbius jet is k + 1/2, with divergence at equality. -/
theorem uniform_random_jet_second_moment_iff (k : ℕ) {α : ℝ} (hα : 0 < α) :
    (∃ C : ℝ, ∀ N : ℕ, (∫ ω, ‖moebiusJetPotential N k α ω‖^2 ∂steinhausMeasure) ≤ C) ↔
      (k:ℝ)+1/2 < α := by
  let f (n : ℕ) := ((moebius n:ℤ):ℝ)^2/(n:ℝ)*(Real.log n)^(2*((k:ℝ)-α))
  have hf (n : ℕ) : 0 ≤ f n := by
    apply mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    apply Real.rpow_nonneg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.log_nonneg (by exact_mod_cast hn)
  have he : Summable f ↔ (k:ℝ)+1/2 < α := by
    have hh := squarefree_logarithmic_diagonal_iff (2*(α-(k:ℝ)))
    rw [show -(2*(α-(k:ℝ)))=2*((k:ℝ)-α) by ring] at hh
    exact hh.trans ⟨fun h => by linarith only [h],fun h => by linarith only [h]⟩
  simp_rw [moebiusJetPotential_second_moment _ _ hα]
  change (∃ C : ℝ, ∀ N, (∑ n ∈ Finset.Icc 2 N, f n) ≤ C) ↔ _
  rw [←he]
  constructor
  · rintro ⟨C,hC⟩
    apply summable_of_sum_range_le hf (c:=f 0+f 1+C)
    intro K
    have hsub : range K ⊆ insert 0 (insert 1 (Finset.Icc 2 K)) := by
      intro n hn
      simp only [mem_insert,Finset.mem_Icc,mem_range] at *
      omega
    have h := sum_le_sum_of_subset_of_nonneg (f:=f) hsub (fun n _ _ => hf n)
    simp only [sum_insert (by simp : 0 ∉ insert 1 (Finset.Icc 2 K)),
      sum_insert (by simp : 1 ∉ Finset.Icc 2 K)] at h
    linarith only [h,hC K]
  · intro hs
    exact ⟨_,fun N => hs.sum_le_tsum _ (fun n _ => hf n)⟩

#print axioms moebiusJetPotential_fourier
#print axioms moebiusJetPotential_second_moment
#print axioms uniform_random_jet_second_moment_iff

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
