import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.ExponentialFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # Pathwise Choi overlap exclusion on a whole positive time interval -/
open MeasureTheory Set Filter Matrix GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private theorem overlap_change {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U V W : Matrix ι ι ℂ) (hW : W∈unitary _) :
    ‖inner ℂ (choiVector U) (choiVector W)‖-‖inner ℂ (choiVector V) (choiVector W)‖ ≤ ‖U-V‖ := by
  have h := norm_sub_norm_le (inner ℂ (choiVector U) (choiVector W)) (inner ℂ (choiVector V) (choiVector W))
  rw [←inner_sub_left] at h
  have hh := h.trans (norm_inner_le_norm _ _)
  rw [norm_choiVector_eq_one Fintype.card_pos (Unitary.mem_iff.mp hW).1,mul_one] at hh
  have hs : choiVector U-choiVector V=choiVector (U-V) := by
    ext p
    simp [choiVector]
    ring
  rw [hs] at hh
  exact hh.trans (norm_choiVector_le_l2_opNorm _)

private def grid (a T : ℝ) (n j : ℕ) := min T (a+j/(n:ℝ)^2)

private theorem near_grid {a T t : ℝ} (ht : t∈Icc a T) {n : ℕ} (hn : 0<(n:ℝ)) (hw : T-a<n) :
    ∃ j : Fin (n^3), |t-grid a T n j.val|≤1/(n:ℝ)^2 := by
  let x := (t-a)*(n:ℝ)^2
  have hx : 0≤x := mul_nonneg (sub_nonneg.mpr ht.1) (sq_nonneg _)
  have hn₂ := sq_pos_of_pos hn
  have hfloor := Nat.floor_le hx
  have hj : (⌊x⌋₊:ℝ)<(n:ℝ)^3 := by
    apply hfloor.trans_lt
    have hh := mul_lt_mul_of_pos_right ((sub_le_sub_right ht.2 a).trans_lt hw) hn₂
    simpa only [x,pow_succ (n:ℝ) 2,mul_comm ((n:ℝ)^2) (n:ℝ)] using hh
  refine ⟨⟨⌊x⌋₊,by exact_mod_cast hj⟩,?_⟩
  have hlo := (div_le_iff₀ hn₂).mpr (show (⌊x⌋₊:ℝ)≤(t-a)*(n:ℝ)^2 from hfloor)
  have hhi := Nat.lt_floor_add_one x
  rw [grid,min_eq_right (by linarith only [hlo,ht.2]),abs_of_nonneg (by linarith only [hlo])]
  apply (le_div_iff₀ hn₂).mpr
  calc (t-(a+(⌊x⌋₊:ℝ)/(n:ℝ)^2))*(n:ℝ)^2 = x-⌊x⌋₊ := by
         dsimp only [x]
         field_simp [hn.ne']
         ring
       _ ≤ 1 := by linarith only [hhi]

/-- Failure at at least one date of an inverse-square mesh. -/
def gridOverlap (a T η κ : ℝ) (n : ℕ) : Set PathPauliDisorder :=
  ⋃ j : Fin (n^3), cutOverlapEvent n (grid a T n j.val) η κ

/-- A prescribed-date bound transfers to the whole mesh at the cost of
its cardinality, including when the horizon depends on prefix length. -/
theorem grid_overlap_le {n : ℕ} {a T η κ b : ℝ} (hT : a ≤ T)
    (h : ∀ t ∈ Icc a T, pathPauliDisorderLaw.real (cutOverlapEvent n t η κ) ≤ b) :
    pathPauliDisorderLaw.real (gridOverlap a T η κ n) ≤ (n:ℝ)^3*b := by
  unfold gridOverlap
  apply (measureReal_iUnion_fintype_le _).trans
  have hgrid (j : Fin (n^3)) : grid a T n j.val∈Icc a T :=
    ⟨le_min hT (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))),min_le_left ..⟩
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => h _ (hgrid j))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]

/-- Summing the prescribed-date tail costs at most the mesh cardinality. -/
theorem grid_overlap_tail {a T η κ : ℝ} (ha : 0 < a) (hT : a ≤ T) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ A > 0, ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      pathPauliDisorderLaw.real (gridOverlap a T η κ n) ≤ A*(n:ℝ)^3*Real.exp (-c*n) := by
  obtain ⟨A,hA,c,hc,h⟩ := gaussian_cut_overlap_tail (T:=T) ha hη hκ
  refine ⟨A,hA,c,hc,?_⟩
  filter_upwards [h] with n hn
  apply (grid_overlap_le hT hn).trans_eq
  ring

/-- The Hamiltonian speed bound transfers every overlap obstruction
from the mesh to the entire time interval. -/
theorem exclude_from_grid {a T C κ η : ℝ} {n : ℕ} {ω : PathPauliDisorder}
    (hC : 0 < C) (hκ : 0 < κ) (hn₂ : 2 ≤ n)
    (hlarge : max (T-a) (4*C/κ) < (n:ℝ))
    (hnH : ‖pathHamiltonian (pathPauliDisorderShell ω n)‖ ≤ C*(n+2:ℕ))
    (hn : ω ∉ gridOverlap a T η (κ/2) n) :
    ∀ t ∈ Icc a T, ω ∉ cutOverlapEvent n t η κ := by
  intro t ht hs
  have hnpos : 0<(n:ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨j,hj⟩ := near_grid ht hnpos ((le_max_left ..).trans_lt hlarge)
  let u := grid a T n j.val
  have hb : ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-
      unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) u‖ ≤ κ/2 := by
    apply (norm_unitaryEvolution_time_sub_le (isSelfAdjoint_pathHamiltonian _) t u).trans
    apply (mul_le_mul hnH hj (abs_nonneg _) (mul_nonneg hC.le (Nat.cast_nonneg _))).trans
    have hK := (div_lt_iff₀ hκ).mp ((le_max_right ..).trans_lt hlarge)
    have hN : (n:ℝ)+2≤2*n := by exact_mod_cast (show n+2≤2*n by omega)
    have h := mul_le_mul_of_nonneg_left hN hC.le
    rw [Nat.cast_add,Nat.cast_ofNat,mul_one_div,div_le_iff₀ (sq_pos_of_pos hnpos)]
    nlinarith only [h,mul_le_mul_of_nonneg_right hK.le hnpos.le]
  obtain ⟨C',c',hcut,hfit⟩ := hs
  apply hn (mem_iUnion.mpr ⟨j,C',c',hcut,?_⟩)
  have h := (overlap_change _ _ C'.eval.val C'.eval.property).trans hb
  change κ/2 ≤ ‖inner ℂ (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) u))
    (choiVector C'.eval.val)‖
  linarith only [h,hfit]

/-- Almost surely along the same Gaussian prefixes, every circuit with
a dense gate-respecting cut has small overlap at every date of the
compact interval, including dates chosen after observing the path. -/
theorem gaussian_uniform_cut_overlap {a T η κ : ℝ} (ha : 0<a) (hη : 0<η) (hκ : 0<κ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T,
      ω∉cutOverlapEvent n t η κ := by
  by_cases hT : a≤T
  · obtain ⟨A,_,c,hc,htail⟩ := grid_overlap_tail ha hT hη (half_pos hκ)
    let B (n : ℕ) := gridOverlap a T η (κ/2) n
    have hs : Summable fun n => pathPauliDisorderLaw.real (B n) := by
      apply ((Real.summable_pow_mul_exp_neg_nat_mul 3 hc).mul_left A).of_norm_bounded_eventually_nat
      filter_upwards [htail] with n hn
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact hn.trans_eq (mul_assoc ..)
    have hB : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉B n := by
      apply ae_eventually_notMem
      simpa only [ofReal_measureReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
    obtain ⟨C,hC,hbound⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
    obtain ⟨n₀,hn₀⟩ := exists_nat_gt (max (T-a) (4*C/κ))
    filter_upwards [hB,hbound] with ω hω hnorm
    filter_upwards [hω,hnorm,eventually_ge_atTop n₀,eventually_ge_atTop 2] with n hn hnH hnn hn₂
    exact exclude_from_grid hC hκ hn₂ (hn₀.trans_le (Nat.cast_le.mpr hnn)) hnH hn
  · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ _ ht => (hT (ht.1.trans ht.2)).elim

#print axioms gaussian_uniform_cut_overlap
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
