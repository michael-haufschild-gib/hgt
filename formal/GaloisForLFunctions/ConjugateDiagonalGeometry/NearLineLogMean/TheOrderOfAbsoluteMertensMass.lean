import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.EveryMertensSectionPaysForEachZetaZero
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent

/-!
# The ordinary growth order of the absolute Mertens mass

In every upper half-octave one terminal cost is controlled by the
accumulated reciprocal mass. Each zeta zero therefore supplies a
power lower bound at all sufficiently large cutoffs, including when
all nontrivial zeros lie on the critical line.
-/

noncomputable section
open Finset Filter
open scoped Topology
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

theorem mertens_abel_mass_eq (N : ℕ) :
    mertensAbelMass N = ∑ k ∈ Icc 1 N, ‖mobiusMertensPartialSum k‖ / (k:ℝ) := by
  induction N with
  | zero => simp [mertensAbelMass]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega)]
    change (∑ j ∈ range (N+1), _) = _
    rw [sum_range_succ,←ih,Nat.cast_succ]
    rfl

theorem mertens_abel_mass_mono : Monotone mertensAbelMass :=
  fun _ _ h => sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h)
    fun _ _ _ => div_nonneg (norm_nonneg _) (by positivity)

/-- An upper-half cutoff has full Abel cost at most three times the
accumulated mass of the given section. -/
theorem upper_half_mertens_abel_selection {N : ℕ} (hN : 1≤N) :
    ∃ k ∈ Ioc (N/2) N, mertensAbelCost k ≤ 3*mertensAbelMass N := by
  let S := Ico (N/2) N
  let f := fun j : ℕ => ‖mobiusMertensPartialSum (j+1)‖/((j:ℝ)+1)
  have hf (j : ℕ) : 0 ≤ f j := div_nonneg (norm_nonneg _) (by positivity)
  have hs : S ⊆ range N := fun j hj => mem_range.mpr (mem_Ico.mp hj).2
  have small : ∑ j ∈ S,f j ≤ mertensAbelMass N :=
    sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => hf j)
  have hc : (N:ℝ) ≤ 2*(S.card:ℝ) := by
    dsimp only [S]; rw [Nat.card_Ico]
    exact_mod_cast (show N ≤ 2*(N-N/2) by omega)
  have hsum : ∑ j ∈ S,(N:ℝ)*f j ≤ ∑ _j ∈ S, 2*mertensAbelMass N := by
    rw [←mul_sum,sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_left small (Nat.cast_nonneg N)).trans
      ((mul_le_mul_of_nonneg_right hc (mertens_abel_mass_nonneg N)).trans_eq (by ring))
  have ne : S.Nonempty := ⟨N/2,mem_Ico.mpr ⟨le_rfl,by omega⟩⟩
  obtain ⟨j,hj,hcheap⟩ := exists_le_of_sum_le ne hsum
  obtain ⟨hl,hu⟩ := mem_Ico.mp hj
  refine ⟨j+1,mem_Ioc.mpr ⟨by omega,hu⟩,?_⟩
  have hcost := mul_le_mul_of_nonneg_right (by exact_mod_cast hu : (j:ℝ)+1 ≤ N) (hf j)
  have hcancel : ((j:ℝ)+1)*f j = ‖mobiusMertensPartialSum (j+1)‖ := by
    dsimp only [f]; field_simp
  rw [hcancel] at hcost
  dsimp only [mertensAbelCost]
  linarith only [hcheap,hcost,mertens_abel_mass_mono hu]

/-- The reciprocal mass through every sufficiently large cutoff exceeds
any fixed multiple of each strictly subcritical power. -/
theorem eventually_large_mertens_abel_mass {b : ℝ} (hb : 0 ≤ b) (h : b < zetaZeroAbscissa)
    (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C*((N:ℝ)+1)^b < mertensAbelMass N := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_large_mertens_abel_cost hb h (3*|C|*3^b))
  filter_upwards [eventually_ge_atTop (2*K+1)] with N hN
  obtain ⟨k,hk,hcost⟩ := upper_half_mertens_abel_selection (N:=N) (by omega)
  have hhalf := (mem_Ioc.mp hk).1
  have hp := hK k (by omega)
  have hx : (N:ℝ)+1 ≤ 3*k := by exact_mod_cast (show N+1≤3*k by omega)
  have hscale := Real.rpow_le_rpow (by positivity : 0 ≤ (N:ℝ)+1) hx hb
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (Nat.cast_nonneg k)] at hscale
  have hC := mul_le_mul (le_abs_self C) hscale (Real.rpow_nonneg (by positivity) _) (abs_nonneg C)
  linarith only [hC,hp,hcost]

/-- Littlewood's bound gives the matching upper exponent without a
logarithmic loss in passing from prefixes to their reciprocal mass. -/
theorem supercritical_mertens_abel_mass {a : ℝ} (ha : zetaZeroAbscissa < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N, mertensAbelMass N ≤ C*((N:ℝ)+1)^a := by
  have ha0 : 0<a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) half_le_zetaZeroAbscissa |>.trans ha
  obtain ⟨A,hA,hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
  rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa)=a by ring] at hM
  refine ⟨A*2^a*(1+1/a),by positivity,fun N => ?_⟩
  have hrow (j : ℕ) : ‖mobiusMertensPartialSum (j+1)‖/((j:ℝ)+1) ≤
      (A*2^a)*((j:ℝ)+1)^(a-1) := by
    have hp : 0 < (j:ℝ)+1 := by positivity
    have h := hM (j+1)
    rw [Nat.cast_add_one] at h
    have hc := Real.rpow_le_rpow (by positivity : 0≤(j:ℝ)+1+1)
      (by linarith only [Nat.cast_nonneg (α:=ℝ) j] : (j:ℝ)+1+1 ≤ 2*((j:ℝ)+1)) ha0.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hp.le] at hc
    apply (div_le_iff₀ hp).mpr
    rw [Real.rpow_sub hp,Real.rpow_one]
    exact (h.trans (mul_le_mul_of_nonneg_left hc hA)).trans_eq (by field_simp)
  have hsum := sum_le_sum (s:=range N) (fun j _ => hrow j)
  rw [←mul_sum] at hsum
  exact hsum.trans ((mul_le_mul_of_nonneg_left (ArithmeticGaugeTheory.sum_rpow_sub_one_le ha0 N)
    (mul_nonneg hA (by positivity))).trans_eq (by ring))

/-- The ordinary logarithmic order of the reciprocal Mertens mass is Θ. -/
theorem mertens_abel_mass_log_order :
    Tendsto (fun N : ℕ => Real.log (1+mertensAbelMass N)/Real.log ((N:ℝ)+1))
      atTop (𝓝 zetaZeroAbscissa) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    let c := (max 0 b+zetaZeroAbscissa)/2
    have hθ : 0<zetaZeroAbscissa := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
    have hm : max 0 b < zetaZeroAbscissa := max_lt hθ hb
    have hbc : b<c := by dsimp only [c]; linarith only [le_max_right 0 b,hm]
    have hc0 : 0 ≤ c := by dsimp only [c]; linarith only [le_max_left 0 b,hθ]
    have hc : c < zetaZeroAbscissa := by dsimp only [c]; linarith only [hm]
    filter_upwards [eventually_large_mertens_abel_mass hc0 hc 1,eventually_ge_atTop 1] with N hn hN
    have hX : 1<(N:ℝ)+1 := by linarith only [(Nat.one_le_cast (α:=ℝ)).mpr hN]
    rw [one_mul] at hn
    have hl := Real.log_lt_log (Real.rpow_pos_of_pos (zero_lt_one.trans hX) c)
      (hn.trans (lt_add_of_pos_left _ zero_lt_one))
    rw [Real.log_rpow (zero_lt_one.trans hX)] at hl
    exact hbc.trans ((lt_div_iff₀ (Real.log_pos hX)).mpr hl)
  · intro b hb
    obtain ⟨a,ha,hab⟩ := exists_between hb
    obtain ⟨C,hC,hbound⟩ := supercritical_mertens_abel_mass ha
    have ha0 : 0≤a := by linarith only [half_le_zetaZeroAbscissa,ha]
    have hX : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hab)).comp hX).eventually_gt_atTop (1+C),
      eventually_ge_atTop 1] with N hn hN
    have hx : 1<(N:ℝ)+1 := by linarith only [(Nat.one_le_cast (α:=ℝ)).mpr hN]
    have hp := zero_lt_one.trans hx
    have hw := Real.one_le_rpow hx.le ha0
    have hs := mul_lt_mul_of_pos_right hn (Real.rpow_pos_of_pos hp a)
    change (1+C)*((N:ℝ)+1)^a < ((N:ℝ)+1)^(b-a)*((N:ℝ)+1)^a at hs
    rw [←Real.rpow_add hp,sub_add_cancel] at hs
    have hle : 1+mertensAbelMass N < ((N:ℝ)+1)^b := by linarith only [hw,hs,hbound N]
    have hl := Real.log_lt_log (by linarith only [mertens_abel_mass_nonneg N] : 0<1+mertensAbelMass N) hle
    rw [Real.log_rpow hp] at hl
    exact (div_lt_iff₀ (Real.log_pos hx)).mpr hl

#print axioms upper_half_mertens_abel_selection
#print axioms eventually_large_mertens_abel_mass
#print axioms mertens_abel_mass_log_order
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
