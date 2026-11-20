import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheVirialGapOfComplementaryFactors
import GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound

/-!
# The minimum critical virial energy of integer factors

The smaller consecutive-factor cost increases with the smaller factor.
The logarithm bound 2(r−1)/(r+1) ≤ log r controls its derivative.
The least nonzero oriented and paired costs are both attained at {1,2}.
-/

noncomputable section
open Filter Set
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def adjacentLogCost (x : ℝ) : ℝ := x*(x+1)*(Real.log (x+1)-Real.log x)^2

private theorem adjacent_log_cost_deriv {x : ℝ} (hx : 0<x) :
    HasDerivAt adjacentLogCost
      ((Real.log (x+1)-Real.log x)*((2*x+1)*(Real.log (x+1)-Real.log x)-2)) x := by
  have xp := add_pos hx zero_lt_one
  have plus := (hasDerivAt_id x).add_const 1
  let L := Real.log (x+1)-Real.log x
  have logs : HasDerivAt (fun y : ℝ => Real.log (y+1)-Real.log y) (1/(x+1)-1/x) x :=
    (plus.log xp.ne').sub ((hasDerivAt_id x).log hx.ne')
  have square : HasDerivAt (fun y : ℝ => (Real.log (y+1)-Real.log y)^2)
      (2*L*(1/(x+1)-1/x)) x := by simpa [L] using! logs.fun_pow 2
  have pair : HasDerivAt (fun y : ℝ => y*(y+1)) ((x+1)+x) x := by
    simpa using! (hasDerivAt_id x).fun_mul plus
  have raw := pair.fun_mul square
  change HasDerivAt adjacentLogCost (((x+1)+x)*L^2+x*(x+1)*(2*L*(1/(x+1)-1/x))) x at raw
  have coefficient : ((x+1)+x)*L^2+x*(x+1)*(2*L*(1/(x+1)-1/x))=L*((2*x+1)*L-2) := by
    field_simp [hx.ne',xp.ne'] <;> ring
  rwa [coefficient] at raw

private theorem adjacent_log_cost_mono : MonotoneOn adjacentLogCost (Set.Ici 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (1:ℝ))
  · intro x hx
    exact (adjacent_log_cost_deriv (zero_lt_one.trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (adjacent_log_cost_deriv (zero_lt_one.trans_le (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    have pos : 0<x := zero_lt_one.trans_le (interior_subset hx : x∈Set.Ici (1:ℝ))
    have xp := add_pos pos zero_lt_one
    have ratio : 1≤(x+1)/x := (one_le_div pos).mpr (by linarith)
    have logpos := Real.log_nonneg ratio
    have lower := GaloisForLFunctions.HTGeometry.two_mul_sub_one_div_add_one_le_log ratio
    have reduce : 2*((x+1)/x-1)/((x+1)/x+1)=2/(2*x+1) := by
      have plus := add_pos (div_pos xp pos) zero_lt_one
      field_simp [pos.ne',plus.ne',(by linarith : 2*x+1≠0)]
      ring
    rw [reduce,Real.log_div xp.ne' pos.ne'] at lower
    rw [Real.log_div xp.ne' pos.ne'] at logpos
    rw [(adjacent_log_cost_deriv pos).deriv]
    apply mul_nonneg logpos
    have bound := (div_le_iff₀ (by linarith : 0<2*x+1)).mp lower
    linarith only [bound]

private theorem ordered_log_cost_floor {a b : ℕ} (ha : 0<a) (less : a<b) :
    2*Real.log 2^2≤((a:ℝ)*b)*Real.log ((b:ℝ)/a)^2 := by
  have ap : 0<(a:ℝ) := Nat.cast_pos.mpr ha
  have bp : 0<(b:ℝ) := Nat.cast_pos.mpr (ha.trans less)
  have one : (1:ℝ)≤a := Nat.one_le_cast.mpr ha
  have next : (a:ℝ)+1≤b := by exact_mod_cast Nat.succ_le_of_lt less
  have apos := add_pos ap zero_lt_one
  have near := adjacent_log_cost_mono (mem_Ici.mpr (le_refl (1:ℝ))) (mem_Ici.mpr one) one
  have gap := Real.log_le_log apos next
  have logpos := Real.log_le_log ap (by linarith : (a:ℝ)≤a+1)
  rw [adjacentLogCost,adjacentLogCost,Real.log_one,sub_zero,one_mul,show (1:ℝ)+1=2 by norm_num] at near
  rw [Real.log_div bp.ne' ap.ne']
  exact near.trans (mul_le_mul (mul_le_mul_of_nonneg_left next ap.le)
    (pow_le_pow_left₀ (sub_nonneg.mpr logpos) (sub_le_sub_right gap _) 2) (sq_nonneg _) (mul_pos ap bp).le)

private theorem factor_log_cost_floor {d e : ℕ} (hd : 0<d) (he : 0<e) (neq : d≠e) :
    2*Real.log 2^2≤((d:ℝ)*e)*Real.log ((d:ℝ)/e)^2 := by
  rcases lt_or_gt_of_ne neq with h|h
  · rw [show (d:ℝ)/e=((e:ℝ)/d)⁻¹ by rw [inv_div],Real.log_inv,neg_sq]
    exact ordered_log_cost_floor hd h
  · rw [mul_comm (d:ℝ) e]
    exact ordered_log_cost_floor he h

/-- Among all distinct positive factor pairs, the minimum oriented
critical energy is 2(log 2)². The pair (1,2) attains it. -/
theorem sharp_factor_virial_floor (c : ℝ) :
    (∀ d e : ℕ, 0<d → 0<e → d≠e → c ≤ scaledFactorVirial d e) ↔ c≤2*Real.log 2^2 := by
  constructor
  · intro all
    have bound := all 1 2 (by norm_num) (by norm_num) (by norm_num)
    rw [factor_virial_identity (d:=1) (e:=2) (by norm_num) (by norm_num) (by norm_num)] at bound
    simpa [factorFrequency,Real.log_div] using bound
  · intro cap d e hd he neq
    have hk : 1<d*e := by
      rcases lt_or_gt_of_ne neq with h|h
      · exact (show 1<e by omega).trans_le (Nat.le_mul_of_pos_left e hd)
      · exact (show 1<d by omega).trans_le (Nat.le_mul_of_pos_right d he)
    have kp : 1≤(d:ℝ)*e := by exact_mod_cast hk.le
    have freq : 0≤factorFrequency d e :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg d)) (Real.log_nonneg kp)
    rw [factor_virial_identity hd he hk,mul_assoc]
    exact (cap.trans (factor_log_cost_floor hd he neq)).trans (le_mul_of_one_le_left
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)) (le_add_of_nonneg_right freq))

/-- The minimum sum over both orientations is 16(log 2)², attained by {1,2}. -/
theorem sharp_paired_factor_virial_floor (c : ℝ) :
    (∀ d e : ℕ, 0<d → 0<e → d≠e → c ≤ scaledFactorVirial d e+scaledFactorVirial e d) ↔ c≤16*Real.log 2^2 := by
  constructor
  · intro all
    have bound := all 1 2 (by norm_num) (by norm_num) (by norm_num)
    rw [paired_factor_virial_identity (d:=1) (e:=2) (by norm_num) (by norm_num) (by norm_num)] at bound
    norm_num at bound ⊢
    exact bound
  · intro cap d e hd he neq
    have hk : 1<d*e := by
      rcases lt_or_gt_of_ne neq with h|h
      · exact (show 1<e by omega).trans_le (Nat.le_mul_of_pos_left e hd)
      · exact (show 1<d by omega).trans_le (Nat.le_mul_of_pos_right d he)
    rw [paired_factor_virial_identity hd he hk]
    have cost := factor_log_cost_floor hd he neq
    rw [Real.log_div (Nat.cast_pos.mpr hd).ne' (Nat.cast_pos.mpr he).ne'] at cost
    linarith only [cost,cap]

/-- The multiplicative cofactor strip is exactly a strict sublevel of the
sum of the two critical energies. -/
theorem paired_factor_virial_strip {d e b : ℕ} (hd : 0<d) (he : 0<e) (hb : 1<b) (hk : 1<d*e) :
    (d<b*e ∧ e<b*d) ↔ scaledFactorVirial d e+scaledFactorVirial e d<8*((d:ℝ)*e)*Real.log b^2 := by
  have dp : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have ep : 0<(e:ℝ) := Nat.cast_pos.mpr he
  have B : 1<(b:ℝ) := Nat.one_lt_cast.mpr hb
  have bp := zero_lt_one.trans B
  rw [paired_factor_virial_identity hd he hk,mul_lt_mul_iff_right₀ (mul_pos (by norm_num) (mul_pos dp ep)),
    sq_lt_sq,abs_of_pos (Real.log_pos B),abs_lt]
  have left : d<b*e ↔ Real.log d<Real.log b+Real.log e := by
    rw [←Real.log_mul bp.ne' ep.ne',Real.log_lt_log_iff dp (mul_pos bp ep)]
    exact_mod_cast Iff.rfl
  have right : e<b*d ↔ Real.log e<Real.log b+Real.log d := by
    rw [←Real.log_mul bp.ne' dp.ne',Real.log_lt_log_iff ep (mul_pos bp dp)]
    exact_mod_cast Iff.rfl
  rw [left,right]
  constructor <;> rintro ⟨u,v⟩ <;> constructor <;> linarith only [u,v]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
