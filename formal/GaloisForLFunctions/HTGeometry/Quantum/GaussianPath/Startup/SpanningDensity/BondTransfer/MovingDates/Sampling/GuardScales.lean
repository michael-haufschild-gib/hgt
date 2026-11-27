import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.Summability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SeamDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BondMinimum

/-! # Simultaneous weak seams for variable strip lengths and thresholds -/
open MeasureTheory Filter Real Finset Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open FixedHorizon BlockDilations.AdaptiveCuts
noncomputable section

private theorem absent_strip_bound (s L : ℕ) {γ : ℝ} (hγ : 0<γ) (h₁ : γ≤1) :
    pathPauliDisorderLaw.real (absentStrip γ L s)≤exp (-(L:ℝ)*(2*gaussianDensityFloor*γ)^9) := by
  obtain ⟨q,_,hq,hm⟩ := gaussian_weak_strip_mass hγ
  have h := buffer_miss_bound L hγ.le h₁
  rw [buffer_miss_mass,←hq,sub_sub_cancel] at h
  exact (hm L (fun i => s+i.val) (fun i k he => Fin.ext (Nat.add_left_cancel he))).le.trans h

/-- If the expected weak-bond count in each strip grows at least
linearly in j, polynomially many locations are all covered eventually. -/
theorem gaussian_covered_strips (L : ℕ→ℕ) (g : ℕ→ℝ) {c : ℝ} (hc : 0<c)
    (hm : ∀ᶠ j : ℕ in atTop, 0<g j ∧ g j≤1 ∧ c*j≤(L j:ℝ)*(2*gaussianDensityFloor*g j)^9) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop,
      ∀ n : ℕ, n+1≤4*(2*j)^256 → missedBonds n (L j) (g j) ω=∅ := by
  classical
  let M (j : ℕ) := 8*(2*j)^256
  let E (j : ℕ) := ⋃ s : Fin (M j), absentStrip (g j) (L j) s.val
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hrare : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ω∉E j := by
    apply avoid_exponential_windows pathPauliDisorderLaw E 256 (8*2^256) hc
    filter_upwards [hm] with j hj
    have hb (s : Fin (M j)) := (absent_strip_bound s.val (L j) hj.1 hj.2.1).trans
      (exp_le_exp.mpr (show -(L j:ℝ)*(2*gaussianDensityFloor*g j)^9≤ -c*j by linarith only [hj.2.2]))
    apply (measureReal_iUnion_fintype_le _).trans ((sum_le_sum fun i _ => hb i).trans_eq _)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,M,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow]
    ring
  filter_upwards [hrare] with ω hw
  filter_upwards [hw,eventually_gt_atTop (0:ℕ)] with j hgood hj
  intro n hn
  have hlim : 4*(2*j)^256<M j := by
    have hp : 0<(2*j)^256 := pow_pos (Nat.mul_pos (by decide) hj) _
    dsimp only [M]
    omega
  have hstrip (s : ℕ) (hs : s<M j) : ω∉absentStrip (g j) (L j) s :=
    fun h => hgood (mem_iUnion.mpr ⟨(⟨s,hs⟩ : Fin (M j)),h⟩)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have h := (mem_filter.mp he).2
  have hl := e.isLt
  rcases h with h|h
  · exact hstrip (e.val-L j) (by omega) h
  · exact hstrip (e.val+1) (by omega) h

/-- At central threshold j⁻¹¹ the bracketing strips of length j¹⁰⁰
all contain a bond of strength at most j⁻¹¹/1024. -/
theorem gaussian_eighth_power_seams :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      n+1≤4*(2*j)^256 → missedBonds n (j^100) ((1/(j:ℝ))^11/1024) ω=∅ := by
  let c := (2*gaussianDensityFloor/1024)^9
  apply gaussian_covered_strips _ _ (c:=c) (pow_pos (div_pos (mul_pos zero_lt_two gaussianDensityFloor_pos) (by norm_num)) _)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
  have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have h₁ : 1/(j:ℝ)≤1 := (div_le_one hJ).mpr (by exact_mod_cast hj)
  have hp := pow_le_one₀ (one_div_pos.mpr hJ).le h₁ (n:=11)
  refine ⟨by positivity,by linarith only [hp],?_⟩
  apply le_of_eq
  dsimp only [c]
  rw [Nat.cast_pow]
  field_simp [hJ.ne']

#print axioms gaussian_eighth_power_seams
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
