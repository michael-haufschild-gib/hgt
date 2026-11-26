import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.DateTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.PhysicalWindow
import Mathlib.Analysis.PSeries

/-! # A superlinear window excluding circuits of subextensive size -/

open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private def gridDate (n j : ℕ) : ℝ := j/((n+2:ℕ):ℝ)^2

private def gridFailure (n : ℕ) (a T τ : ℝ) (E : Set PathPauliDisorder) : Set PathPauliDisorder :=
  ⋃ j : Fin ((n+2)^4+1), if gridDate n j∈Icc a T then
    ((fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹'
      affordableDraw n ⌊τ*((n+2:ℕ):ℝ)⌋₊ (5/16) (gridDate n j)) ∩ E else ∅

private theorem grid_mass (n : ℕ) (a T τ : ℝ) (E : Set PathPauliDisorder)
    (h : ∀ t∈Icc a T, pathPauliDisorderLaw.real (((fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹'
      affordableDraw n ⌊τ*((n+2:ℕ):ℝ)⌋₊ (5/16) t) ∩ E)≤1/((n+2:ℕ):ℝ)^6) :
    pathPauliDisorderLaw.real (gridFailure n a T τ E)≤2/((n+2:ℕ):ℝ)^2 := by
  let K : ℝ := (n+2:ℕ)
  have hK : 1≤K := by dsimp only [K]; exact_mod_cast (show 1≤n+2 by omega)
  have hK' := zero_lt_one.trans_le hK
  unfold gridFailure
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _j : Fin ((n+2)^4+1), 1/K^6 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hd
      · exact h _ hd
      · rw [measureReal_empty]; positivity
    _ = (K^4+1)*(1/K^6) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one,Nat.cast_pow,K]
    _ ≤ 2/K^2 := by
      rw [mul_one_div,div_le_div_iff₀ (pow_pos hK' 6) (sq_pos_of_pos hK')]
      have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ hK (n:=4)) (sq_nonneg K)
      nlinarith only [hh]

/-- At all real dates through a constant times the sixty-fifth power
of the sixty-fourth root of K the original chain needs more than
cK two-qubit gates, starting at a deterministic constant date. -/
theorem gaussian_superlinear_window :
    ∃ τ>0, ∃ a>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let q : ℝ := sizeRoot (n+2)
      ∀ t∈Icc a (δ*q^65), ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → τ*K<(s:ℝ) := by
  obtain ⟨τ,hτ,a,ha,δ,hδ,E,hE,hp⟩ := gaussian_superlinear_date_tail
  obtain ⟨B,hB,hH⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  let T (n : ℕ) := δ*(sizeRoot (n+2):ℝ)^65
  let bad (n : ℕ) := gridFailure n a (T n) τ (E n)
  have hs : Summable fun n => pathPauliDisorderLaw.real (bad n) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left 2
    apply h.of_norm_bounded_eventually_nat
    filter_upwards [hp,eventually_gt_atTop 0] with n hn hn'
    rw [Real.norm_of_nonneg measureReal_nonneg]
    apply (grid_mass n a (T n) τ (E n) hn).trans
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (Nat.cast_pos.mpr hn'))
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega : n≤n+2)) 2)
  have hg : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉bad n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
  have hl : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  refine ⟨τ,hτ,a+1,by positivity,δ,hδ.1,?_⟩
  filter_upwards [hg,hH,hE] with ω hg hH hE
  filter_upwards [hg,hH,hE,hl.eventually (eventually_ge_atTop (16*B))] with n hg hH hE hB'
  intro K q t ht s hf
  have hK : 1≤K := by dsimp only [K]; exact_mod_cast (show 1≤n+2 by omega)
  have hK' := zero_lt_one.trans_le hK
  have hK₂ := sq_pos_of_pos hK'
  obtain ⟨hq,hqlo,_⟩ := root_bounds (by omega : 0<n+2)
  have hqn : sizeRoot (n+2)≤n+2 := (Nat.le_pow (by decide : 0<64)).trans hqlo
  have htop : T n≤K^2 := by
    have hpoly : q^65≤K^2 := by
      rw [show (65:ℕ)=64+1 by decide,pow_succ,pow_two]
      exact mul_le_mul (by exact_mod_cast hqlo) (by exact_mod_cast hqn) (Nat.cast_nonneg _) hK'.le
    exact (mul_le_of_le_one_left (pow_nonneg (Nat.cast_nonneg _) _) hδ.2).trans hpoly
  let j := ⌊t*K^2⌋₊
  have ht' : 0≤t := (by linarith only [ha] : 0≤a+1).trans ht.1
  have hfl : (j:ℝ)≤t*K^2 := Nat.floor_le (mul_nonneg ht' hK₂.le)
  have hj : j<(n+2)^4+1 := by
    apply Nat.lt_succ_of_le
    apply Nat.cast_le.mp (α:=ℝ)
    rw [Nat.cast_pow]
    exact hfl.trans ((mul_le_mul_of_nonneg_right (ht.2.trans htop) hK₂.le).trans_eq (by ring))
  let y := gridDate n j
  have hyt : y≤t := (div_le_iff₀ hK₂).mpr hfl
  have hty : t-y≤1/K^2 := by
    have hh := Nat.lt_floor_add_one (t*K^2)
    change t-(j:ℝ)/K^2≤1/K^2
    rw [sub_le_iff_le_add,←add_div,le_div_iff₀ hK₂]
    linarith only [hh]
  have hy : y∈Icc a (T n) := ⟨by
    have hh := one_div_le_one_div_of_le zero_lt_one (one_le_pow₀ hK (n:=2))
    rw [one_div_one] at hh
    linarith only [hh,ht.1,hty],hyt.trans ht.2⟩
  by_contra! hc
  obtain ⟨z,hz,C,hC,he⟩ := hf
  apply hg
  change ω∈gridFailure n a (T n) τ (E n)
  unfold gridFailure
  apply mem_iUnion.mpr
  refine ⟨⟨j,hj⟩,?_⟩
  rw [if_pos hy]
  refine ⟨⟨z,hz,C,hC.trans (Nat.le_floor hc),?_⟩,hE⟩
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) _).trans
  have hdiff := norm_unitaryEvolution_time_sub_le (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)) y t
  rw [abs_of_nonpos (sub_nonpos.mpr hyt)] at hdiff
  have hdate : -(y-t)≤1/K^2 := by linarith only [hty]
  have hevol := hdiff.trans (mul_le_mul hH hdate (by linarith only [hyt]) (mul_nonneg hB.le hK'.le))
  have htol : B*K*(1/K^2)≤1/16 := by
    rw [mul_one_div,div_le_iff₀ hK₂]
    nlinarith only [mul_le_mul_of_nonneg_right hB' hK'.le]
  linarith only [hevol.trans htol,he]

#print axioms gaussian_superlinear_window
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
