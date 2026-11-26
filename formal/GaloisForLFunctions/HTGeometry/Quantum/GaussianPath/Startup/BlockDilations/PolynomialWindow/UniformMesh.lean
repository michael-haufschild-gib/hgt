import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid
import Mathlib.Analysis.PSeries

/-! # Frozen circuit exclusion at every date through a polynomial horizon -/

open MeasureTheory Real Filter Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private def mesh (n : ℕ) : ℝ := 1/((n+2:ℕ):ℝ)^2
private def gridSize (n : ℕ) := plateauGridCount ((n+2:ℕ):ℝ) (mesh n)
private def date (n : ℕ) (a T : ℝ) (j : Fin (gridSize n)) :=
  min T (plateauGridPoint a (mesh n) j.val)

private theorem grid_size (n : ℕ) : gridSize n=(n+2)^3+1 := by
  unfold gridSize plateauGridCount mesh
  have h : ((n+2:ℕ):ℝ)/(1/((n+2:ℕ):ℝ)^2)=(((n+2)^3:ℕ):ℝ) := by
    rw [Nat.cast_pow]; field_simp; ring
  rw [h,Nat.ceil_natCast]

private def badGrid (n : ℕ) (a T τ u v : ℝ) : Set PathPauliDisorder :=
  let K : ℝ := (n+2:ℕ)
  if a≤T then ⋃ j : Fin (gridSize n), (fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹'
    (affordableDraw n ⌊τ*K⌋₊ (5/16) (date n a T j) ∩ globalBounds n (u*K) (v*K))
  else ∅

private theorem grid_bound (n : ℕ) (a T τ u v : ℝ) :
    let K : ℝ := (n+2:ℕ)
    (∀ t∈Icc a T, pathPauliDisorderLaw.real ((fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹'
      (affordableDraw n ⌊τ*K⌋₊ (5/16) t ∩ globalBounds n (u*K) (v*K)))≤2/K^6) →
    pathPauliDisorderLaw.real (badGrid n a T τ u v) ≤ 4/K^3 := by
  intro K ht
  have hK : 1≤K := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hKp := zero_lt_one.trans_le hK
  by_cases ha : a≤T
  · rw [badGrid,if_pos ha]
    apply (measureReal_iUnion_fintype_le _).trans
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => ht (date n a T j)
      ⟨le_min ha (plateauGridPoint_le a (by unfold mesh; positivity) _),min_le_left ..⟩)
    rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,grid_size,nsmul_eq_mul,Nat.cast_add,
      Nat.cast_one,Nat.cast_pow] at h
    apply h.trans
    change (K^3+1)*(2/K^6)≤4/K^3
    have he : K^6=(K^3)^2 := by ring
    rw [he]
    field_simp
    nlinarith only [one_le_pow₀ hK (n:=3),
      mul_nonneg (show 0≤K^3-1 from sub_nonneg.mpr (one_le_pow₀ hK)) (pow_nonneg hKp.le 3)]
  · simp only [badGrid,if_neg ha,measureReal_empty]
    positivity

private theorem excludes_grid {n : ℕ} {a T τ u v C : ℝ} {ω : PathPauliDisorder}
    (hC : 0<C) (hK : 16*C≤((n+2:ℕ):ℝ)) (hT : T≤a+((n+2:ℕ):ℝ))
    (hH : ‖pathHamiltonian (pathPauliDisorderShell ω n)‖≤C*(n+2:ℕ))
    (hg : (fun l => pathPauliDisorderShell ω n l)∈globalBounds n (u*(n+2:ℕ)) (v*(n+2:ℕ)))
    (hw : ω∉badGrid n a T τ u v) {t : ℝ} (ht : t∈Icc a T) {s : ℕ}
    (hfit : HasProjectiveCircuitApproximation (n+2) (1/4) s
      (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)) :
    τ*(n+2:ℕ)<(s:ℝ) := by
  let K : ℝ := (n+2:ℕ)
  have hKp : 0<K := by dsimp only [K]; positivity
  have hm : 0<mesh n := by unfold mesh; positivity
  obtain ⟨j,hj⟩ := exists_plateauGrid_near hm a (show t∈Icc a (a+K) from ⟨ht.1,ht.2.trans hT⟩)
  let d := date n a T j
  have hd : |d-t|≤mesh n := by
    rw [abs_le] at hj ⊢
    dsimp only [d,date]
    rcases le_total T (plateauGridPoint a (mesh n) j.val) with h|h
    · rw [min_eq_left h]; constructor <;> linarith only [hj.1,hj.2,ht.2,h,hm]
    · rw [min_eq_right h]; constructor <;> linarith only [hj.1,hj.2]
  have hdU := (norm_unitaryEvolution_time_sub_le (isSelfAdjoint_pathHamiltonian
    (pathPauliDisorderShell ω n)) d t).trans
    (mul_le_mul hH hd (abs_nonneg _) (mul_nonneg hC.le hKp.le))
  have htol : C*K*mesh n≤1/16 := by
    change C*K*(1/K^2)≤1/16
    rw [mul_one_div,div_le_iff₀ (sq_pos_of_pos hKp)]
    nlinarith only [mul_le_mul_of_nonneg_right hK hKp.le]
  by_contra! hs
  have hs' : s≤⌊τ*K⌋₊ := Nat.le_floor hs
  obtain ⟨z,hz,F,hF,he⟩ := hfit
  apply hw
  rw [badGrid,if_pos (ht.1.trans ht.2)]
  refine mem_iUnion.mpr ⟨j,⟨⟨z,hz,F,hF.trans hs',?_⟩,hg⟩⟩
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) _).trans
  linarith only [hdU.trans htol,he]

/-- On almost every single draw, every sufficiently large prefix has
extensive gate cost simultaneously throughout the stated date window. -/
theorem gaussian_polynomial_gate_floor :
    ∃ τ>0, ∃ a>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ t∈Icc a (δ*K/(log K)^2), ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → τ*K<(s:ℝ) := by
  obtain ⟨u,v,hu,hv,hglobal⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨τ,hτ,a,ha,δ,hδ,hdate⟩ := gaussian_packet_date_tail hu hv
  let T (n : ℕ) := δ*((n+2:ℕ):ℝ)/(log ((n+2:ℕ):ℝ))^2
  let E (n : ℕ) := badGrid n a (T n) τ u v
  have hs : Summable fun n => pathPauliDisorderLaw.real (E n) := by
    have hp := (Real.summable_one_div_nat_pow.mpr (by decide : 1<3)).mul_left 4
    apply hp.of_norm_bounded_eventually_nat
    filter_upwards [hdate,eventually_gt_atTop 0] with n hn hn₀
    rw [Real.norm_of_nonneg measureReal_nonneg]
    apply (grid_bound n a (T n) τ u v hn).trans
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (pow_pos (Nat.cast_pos.mpr hn₀) 3)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega : n≤n+2)) _)
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉E n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
  obtain ⟨C,hC,hnorm⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  have htop : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hl := (tendsto_log_atTop.comp htop).eventually (eventually_ge_atTop (max 1 δ))
  refine ⟨τ,hτ,a,ha,δ,hδ,?_⟩
  filter_upwards [hglobal,hgood,hnorm] with ω hω hw hH
  filter_upwards [hω,hw,hH,htop.eventually (eventually_ge_atTop (16*C)),hl] with n hg he hH hK hl
  let K : ℝ := (n+2:ℕ)
  have hKp : 0<K := by dsimp only [K]; positivity
  have hl₁ : 1≤log K := (le_max_left ..).trans hl
  have hlog : δ≤(log K)^2 := ((le_max_right ..).trans hl).trans (by nlinarith only [hl₁,
    mul_nonneg (sub_nonneg.mpr hl₁) (zero_lt_one.trans_le hl₁).le])
  have hT : T n≤a+K := by
    apply le_trans (b:=K) _ (le_add_of_nonneg_left ha.le)
    apply (div_le_iff₀ (sq_pos_of_pos (zero_lt_one.trans_le hl₁))).mpr
    exact (mul_le_mul_of_nonneg_right hlog hKp.le).trans_eq (mul_comm ..)
  intro t ht s hf
  apply excludes_grid hC hK hT hH _ he ht hf
  refine ⟨hg.1,?_⟩
  rw [←total_energy]
  exact hg.2

#print axioms gaussian_polynomial_gate_floor
end
end GaloisForLFunctions.HTGeometry.BlockDilations
