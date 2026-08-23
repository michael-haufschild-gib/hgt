import GaloisForLFunctions.HTGeometry.GammaBellSubstitution
import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading
import GaloisForLFunctions.RHTower.PeriodWeightFiltration
import GaloisForLFunctions.RHTower.FriableMomentPolygammaJet
import GaloisForLFunctions.HTGeometry.LogDerivBellTransfer
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# The rational Bell polynomials and weighted evaluation

The universal Bell recursion has rational (indeed integer) coefficients, and evaluating a
weight-homogeneous rational polynomial on a jet whose `i`-th coordinate lies in the weight-`(i+1)`
layer of the period filtration lands in the layer of the polynomial's weight.
-/

open MvPolynomial GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The universal Bell recursion over `ℚ`. -/
def bellCoreQ : (k : ℕ) → MvPolynomial (Fin k) ℚ
  | 0 => 1
  | k + 1 =>
      X 0 * rename Fin.castSucc (bellCoreQ k)
        + ∑ j : Fin k, rename Fin.castSucc (pderiv j (bellCoreQ k)) * X j.succ

theorem bellCoreQ_zero : bellCoreQ 0 = 1 := rfl

theorem bellCoreQ_succ (k : ℕ) :
    bellCoreQ (k + 1)
      = X 0 * rename Fin.castSucc (bellCoreQ k)
        + ∑ j : Fin k, rename Fin.castSucc (pderiv j (bellCoreQ k)) * X j.succ := rfl

/-- The universal Bell polynomials have rational coefficients. -/
theorem map_bellCoreQ (k : ℕ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (bellCoreQ k) = bellCore k := by
  induction k with
  | zero =>
    rw [bellCoreQ_zero, bellCore_zero, map_one]
  | succ k ih =>
    rw [bellCoreQ_succ, bellCore_succ, map_add, map_mul, MvPolynomial.map_X,
      MvPolynomial.map_rename, ih, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPolynomial.map_X, MvPolynomial.map_rename, ← MvPolynomial.pderiv_map, ih]

/-! ## Weighted evaluation into the period filtration -/

theorem pow_mem_periodFilt {S : Finset ℕ} {a : ℕ} {x : ℂ} (hx : x ∈ periodFilt S a) (k : ℕ) :
    x ^ k ∈ periodFilt S (a * k) := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.mul_zero]
    exact one_mem_periodFilt S 0
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact periodFilt_mul ih hx

theorem prod_pow_mem_periodFilt {n : ℕ} {S : Finset ℕ} {x : Fin n → ℂ}
    (hx : ∀ i : Fin n, x i ∈ periodFilt S ((i : ℕ) + 1)) (m : Fin n → ℕ) (s : Finset (Fin n)) :
    (∏ i ∈ s, (x i) ^ (m i)) ∈ periodFilt S (∑ i ∈ s, ((i : ℕ) + 1) * m i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact one_mem_periodFilt S 0
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact periodFilt_mul (pow_mem_periodFilt (hx i) (m i)) ih

theorem weight_eq_sum {n : ℕ} (m : Fin n →₀ ℕ) :
    Finsupp.weight (fun i : Fin n => (i : ℕ) + 1) m = ∑ i : Fin n, ((i : ℕ) + 1) * m i := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  · intro i
    simp

/-- **Weighted evaluation lands in the matching layer.** -/
theorem eval_mem_periodFilt {n d : ℕ} {S : Finset ℕ} {B : MvPolynomial (Fin n) ℚ}
    (hB : B.IsWeightedHomogeneous (fun i : Fin n => (i : ℕ) + 1) d)
    {x : Fin n → ℂ} (hx : ∀ i : Fin n, x i ∈ periodFilt S ((i : ℕ) + 1)) :
    MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) B) ∈ periodFilt S d := by
  classical
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq']
  refine Submodule.sum_mem _ fun m hm => ?_
  have hcoeff : MvPolynomial.coeff m B ≠ 0 := by
    simpa using (MvPolynomial.mem_support_iff).mp hm
  have hweight : Finsupp.weight (fun i : Fin n => (i : ℕ) + 1) m = d := hB hcoeff
  have hprod : (∏ i : Fin n, (x i) ^ (m i)) ∈ periodFilt S d := by
    have h := prod_pow_mem_periodFilt hx (fun i => m i) Finset.univ
    rwa [← weight_eq_sum m, hweight] at h
  have hsmul := (periodFilt S d).smul_mem (MvPolynomial.coeff m B) hprod
  rwa [Rat.smul_def] at hsmul

theorem isWeightedHomogeneous_bellCoreQ (k : ℕ) :
    (bellCoreQ k).IsWeightedHomogeneous (fun i : Fin k => (i : ℕ) + 1) k := by
  intro m hm
  have hmap : MvPolynomial.coeff m (bellCore k) ≠ 0 := by
    rw [← map_bellCoreQ k, MvPolynomial.coeff_map]
    intro h
    exact hm ((map_eq_zero_iff (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).mp h)
  exact bellCore_isWeightedHomogeneous k hmap

/-! ## The digamma jet lies in the period filtration -/

theorem iteratedDeriv_digamma_mem_periodFilt (S : Finset ℕ) (i j : ℕ) :
    iteratedDeriv i Complex.digamma ((j : ℂ) + 1) ∈ periodFilt S (i + 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [iteratedDeriv_zero, digamma_natSucc]
    refine Submodule.sub_mem _ ?_ ?_
    · exact periodFilt_mono S (Nat.zero_le 1) (ratCast_mem_periodFilt S 0 _)
    · exact eulerMascheroni_mem_periodFilt S
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [iteratedDeriv_digamma_natSucc_succ]
    have hzeta : riemannZeta (((m + 2 : ℕ) : ℕ) : ℂ) ∈ periodFilt S (m + 2) :=
      riemannZeta_mem_periodFilt S (by omega)
    have hrat : ((harmonicQ (m + 1) j : ℚ) : ℂ) ∈ periodFilt S (m + 2) :=
      periodFilt_mono S (Nat.zero_le _) (ratCast_mem_periodFilt S 0 _)
    have hsub := Submodule.sub_mem (periodFilt S (m + 2)) hzeta hrat
    have hcoeff : ((((-1 : ℚ) ^ (m + 2) * ((m + 1).factorial : ℚ) : ℚ)) : ℂ)
        = (-1 : ℂ) ^ (m + 2) * ((m + 1).factorial : ℂ) := by
      push_cast
      ring
    have hsmul := (periodFilt S (m + 2)).smul_mem
      ((-1 : ℚ) ^ (m + 2) * ((m + 1).factorial : ℚ)) hsub
    rw [Rat.smul_def, hcoeff] at hsmul
    rw [show m + 1 + 1 = m + 2 from rfl]
    exact hsmul

/-! ## The Gamma jet lies in the period filtration -/

/-- **The normalized Gamma jet at a positive integer lands in the weight-`t` period layer.** -/
theorem gammaJet_mem_periodFilt (S : Finset ℕ) (t j : ℕ) :
    iteratedDeriv t Complex.Gamma ((j : ℂ) + 1) / (j.factorial : ℂ) ∈ periodFilt S t := by
  have hΩ : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfan : ∀ z ∈ {z : ℂ | 0 < z.re}, AnalyticAt ℂ Complex.Gamma z := fun z hz =>
    HTGeometry.analyticAt_Gamma_of_re_pos hz
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.Gamma z ≠ 0 := by
    intro z hz
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have hzre : (0 : ℝ) < z.re := hz
    rw [hm] at hzre
    simp only [Complex.neg_re, Complex.natCast_re] at hzre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hmem : ((j : ℂ) + 1) ∈ {z : ℂ | 0 < z.re} := by
    show (0 : ℝ) < ((j : ℂ) + 1).re
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    positivity
  have hbell := iteratedDeriv_eq_bellCore_generic hΩ hfan hne t hmem
  have hfac : Complex.Gamma ((j : ℂ) + 1) = (j.factorial : ℂ) :=
    Complex.Gamma_nat_eq_factorial j
  have hfacne : ((j.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [hbell, hfac, mul_comm, mul_div_assoc, div_self hfacne, mul_one, ← map_bellCoreQ t]
  exact eval_mem_periodFilt (isWeightedHomogeneous_bellCoreQ t)
    (fun i => iteratedDeriv_digamma_mem_periodFilt S (i : ℕ) j)

end

end RHTower
