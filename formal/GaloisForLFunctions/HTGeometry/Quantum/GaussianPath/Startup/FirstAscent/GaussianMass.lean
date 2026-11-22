import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CoordinateLaw
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Chebyshev

/-! # Absolute mass of small sets of Gaussian path coefficients -/
open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section

private theorem integrable_quarter_square :
    Integrable (fun x : ℝ => exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul (√(2*π))⁻¹
  apply h.congr
  filter_upwards with x
  simp only [toReal_gaussianPDF,smul_eq_mul,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

private theorem exponential_mass :
    ∃ B : ℝ, 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∑ l : PathLabel n, exp ((pathPauliDisorderShell ω n l)^2/4) ≤ B*((n+2:ℕ):ℝ) := by
  let f (x : ℝ) := exp (x^2/4)
  let b := (∫ x, f x ∂gaussianReal 0 1)+1
  have hb : 0<b := add_pos_of_nonneg_of_pos (integral_nonneg fun _ => (exp_pos _).le) zero_lt_one
  have hl (d : PathPauliDirections) := LocalPatches.coordinate_strong_law (gaussianReal 0 1) d f
    (by dsimp [f]; fun_prop) integrable_quarter_square
  refine ⟨(Fintype.card PathPauliDirections:ℝ)*b,mul_pos (by positivity) hb,?_⟩
  filter_upwards [ae_all_iff.mpr hl] with ω hω
  have hu (d) := (hω d).eventually_lt_const (lt_add_one (∫ x, f x ∂gaussianReal 0 1))
  filter_upwards [(tendsto_add_atTop_nat 2).eventually (Filter.eventually_all.mpr hu)] with n hn
  let N := n+2
  have hN : 0<(N:ℝ) := by dsimp [N]; positivity
  have per (d : PathPauliDirections) : (∑ i ∈ Finset.range N, f (ω (i,d))) ≤ b*N :=
    ((div_lt_iff₀ hN).mp (hn d)).le
  calc
    _ ≤ ∑ d : PathPauliDirections, ∑ i ∈ Finset.range N, f (ω (i,d)) := by
      simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
      change (∑ i : Fin N, ∑ a : Fin 3, f (ω (i.val,.inl a)))+
        (∑ e : Fin (n+1), ∑ a : Fin 3, ∑ b : Fin 3, f (ω (e.val,.inr (a,b)))) ≤ _
      apply add_le_add
      · rw [Finset.sum_comm]
        exact le_of_eq (Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun i => f (ω (i,.inl a))) N)
      · rw [Fin.sum_univ_eq_sum_range (fun i => ∑ a : Fin 3, ∑ b : Fin 3, f (ω (i,.inr (a,b))))]
        apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (show n+1≤N by omega))
          (fun i _ _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => (exp_pos _).le)).trans_eq
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ ≤ ∑ _d : PathPauliDirections, b*N := Finset.sum_le_sum (fun d _ => per d)
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]

/-- On one Gaussian draw all coefficient subsets of all sufficiently long
prefixes obey the squared order-statistic bound 4k² log(BN/k). -/
theorem gaussian_subset_mass :
    ∃ B : ℝ, 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ L : Finset (PathLabel n), L.Nonempty →
        (∑ l ∈ L, |pathPauliDisorderShell ω n l|)^2 ≤
          4*(L.card:ℝ)^2*log (B*((n+2:ℕ):ℝ)/L.card) := by
  obtain ⟨B,hB,hω⟩ := exponential_mass
  refine ⟨B,hB,?_⟩
  filter_upwards [hω] with ω hh
  filter_upwards [hh] with n hn
  intro L hL
  let u := pathPauliDisorderShell ω n
  let k : ℝ := L.card
  have hk : 0<k := by dsimp [k]; exact_mod_cast Finset.card_pos.mpr hL
  have hw : ∑ _i ∈ L, k⁻¹ = 1 := by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_inv_cancel₀ hk.ne'
  have hj := convexOn_exp.map_sum_le (t := L) (w := fun _ => k⁻¹)
    (p := fun l => (u l)^2/4) (fun _ _ => inv_nonneg.mpr hk.le) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul,←Finset.mul_sum,←Finset.sum_div] at hj
  have hsub := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
    (fun l _ _ => (exp_pos ((u l)^2/4)).le)).trans hn
  have he : exp (((∑ l ∈ L, (u l)^2)/4)/k) ≤ B*((n+2:ℕ):ℝ)/k := by
    simpa only [div_eq_inv_mul] using
      hj.trans (mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hk.le))
  have hlog := Real.log_le_log (exp_pos _) he
  rw [Real.log_exp] at hlog
  have hsq := sq_sum_le_card_mul_sum_sq (s := L) (f := fun l => |u l|)
  simp only [sq_abs] at hsq
  have hl := (div_le_iff₀ hk).mp hlog
  apply hsq.trans
  change k*(∑ l ∈ L, (u l)^2) ≤ _
  nlinarith only [mul_le_mul_of_nonneg_left hl hk.le]

#print axioms gaussian_subset_mass
end
end GaloisForLFunctions.HTGeometry.FirstAscent
