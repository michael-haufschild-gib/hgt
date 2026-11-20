import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFractionalProbeOfTheCorrectedCompositePrice
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The least absolute atom mass of the corrected fractional probe

The smooth square and cube payments telescope. Each is positive and
their combined cost per integer is at most five. Once log(2n)>10,
retaining any proper-power atom strictly increases absolute mass.
A factorial center attains the exact minimum. Even that minimum is of
square-root size, although signed fractional readings detect quarter powers.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def correctedCompositeVariation (m n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (2*n) (4*n), |correctedCompositeAtom m k|

private theorem payment_bounds {k : ℕ} (hk : 0<k) : 0≤compositeRootPayment k ∧ compositeRootPayment k≤5 := by
  have hstep : ((k-1:ℕ):ℝ)+1=k := by rw [Nat.cast_sub hk,Nat.cast_one,sub_add_cancel]
  have root {a : ℝ} (ha : 0≤a) (ha' : a≤1) :
      0≤(k:ℝ)^a-((k-1:ℕ):ℝ)^a ∧ (k:ℝ)^a-((k-1:ℕ):ℝ)^a≤1 := by
    have hu := Real.rpow_add_le_add_rpow (Nat.cast_nonneg (α:=ℝ) (k-1)) zero_le_one ha ha'
    rw [hstep,Real.one_rpow] at hu
    exact ⟨sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.sub_le _ _)) ha),
      by linarith only [hu]⟩
  have hs := root (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  have hc := root (by norm_num : (0:ℝ)≤1/3) (by norm_num)
  unfold compositeRootPayment
  constructor <;> linarith only [hs.1,hs.2,hc.1,hc.2]

private theorem atom_extrema (m : ℕ) {k : ℕ} (hk : 0<k) (hl : 10<Real.log k) :
    compositeRootPayment k≤|correctedCompositeAtom m k| ∧
    |correctedCompositeAtom m k|≤|correctedCompositeAtom 1 k| ∧
    (compositeRootPayment k=|correctedCompositeAtom m k| ↔ purePowerLog m k=0) := by
  obtain ⟨hp,hu⟩ := payment_bounds hk
  have hsurplus : compositeRootPayment k<Real.log k-compositeRootPayment k := by linarith only [hu,hl]
  have log_ne : Real.log (k:ℝ)≠0 := (lt_trans (by norm_num : (0:ℝ)<10) hl).ne'
  have paid : |Real.log (k:ℝ)-compositeRootPayment k|=Real.log k-compositeRootPayment k :=
    abs_of_nonneg (hp.trans hsurplus.le)
  have empty : |(0:ℝ)-compositeRootPayment k|=compositeRootPayment k := by rw [zero_sub,abs_neg,abs_of_nonneg hp]
  by_cases h : ¬k.Prime ∧ k.primeFactors.card=1
  · by_cases hc : m.Coprime k
    · simp only [correctedCompositeAtom,purePowerLog,if_pos (And.intro hc h),if_pos (And.intro (Nat.coprime_one_left k) h),
        paid,hsurplus.le,le_refl,hsurplus.ne,log_ne,iff_self,true_and,and_self]
    · have hn : ¬(m.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun hit => hc hit.1
      simp only [correctedCompositeAtom,purePowerLog,if_neg hn,if_pos (And.intro (Nat.coprime_one_left k) h),
        empty,paid,hsurplus.le,le_refl,iff_self,true_and,and_self]
  · have hn (c : ℕ) : ¬(c.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun hit => h hit.2
    simp [correctedCompositeAtom,purePowerLog,hn,empty,hp]

private theorem factorial_omits_octave {n k : ℕ} (hn : 0<n) (hk : k∈Ioc (2*n) (4*n)) :
    purePowerLog (4*n).factorial k=0 := by
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hk
  have hk₁ : 1<k := by omega
  have hd := Nat.dvd_factorial (by omega : 0<k) hu
  unfold purePowerLog
  apply if_neg
  rintro ⟨hc,_⟩
  have he := Nat.dvd_gcd hd (dvd_refl k)
  rw [show (4*n).factorial.gcd k=1 from hc] at he
  exact hk₁.ne' (Nat.eq_one_of_dvd_one he)

/-- The factorial center attains the lower envelope exactly. It has no
proper-power atoms throughout the octave, so only the smooth increments remain. -/
theorem factorial_variation_is_the_root_payment {n : ℕ} (hn : 0<n) :
    correctedCompositeVariation (4*n).factorial n =
      2*(((4*n:ℕ):ℝ)^(1/2:ℝ)-((2*n:ℕ):ℝ)^(1/2:ℝ)) +
        3*(((4*n:ℕ):ℝ)^(1/3:ℝ)-((2*n:ℕ):ℝ)^(1/3:ℝ)) := by
  unfold correctedCompositeVariation
  calc _ = ∑ k ∈ Ioc (2*n) (4*n), compositeRootPayment k := by
         apply sum_congr rfl
         intro k hk
         have h := (mem_Ioc.mp hk).1
         rw [correctedCompositeAtom,factorial_omits_octave hn hk,zero_sub,abs_neg,abs_of_nonneg (payment_bounds (by omega : 0<k)).1]
       _ = _ := by
         simp only [compositeRootPayment,sum_add_distrib,←mul_sum]
         rw [_root_.RHTower.DeletionResidueMartingale.sum_Ioc_sub_eq (fun k : ℕ => (k:ℝ)^(1/2:ℝ)) (by omega : 2*n≤4*n),
           _root_.RHTower.DeletionResidueMartingale.sum_Ioc_sub_eq (fun k : ℕ => (k:ℝ)^(1/3:ℝ)) (by omega : 2*n≤4*n)]

/-- The exact range endpoints of absolute mass, with a classification of
all minimizing centers. Every surviving proper power strictly raises the mass. -/
theorem absolute_composite_mass_extrema (m : ℕ) {n : ℕ} (hn : 0<n) (hlog : 10<Real.log ((2*n:ℕ):ℝ)) :
    correctedCompositeVariation (4*n).factorial n ≤ correctedCompositeVariation m n ∧
    correctedCompositeVariation m n ≤ correctedCompositeVariation 1 n ∧
    (correctedCompositeVariation (4*n).factorial n = correctedCompositeVariation m n ↔
      ∀ k ∈ Ioc (2*n) (4*n), purePowerLog m k=0) := by
  have he {k : ℕ} (hk : k∈Ioc (2*n) (4*n)) := atom_extrema m
    ((Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1) (hlog.trans_le
      (Real.log_le_log (Nat.cast_pos.mpr (by omega : 0<2*n)) (Nat.cast_le.mpr (mem_Ioc.mp hk).1.le)))
  have hf {k : ℕ} (hk : k∈Ioc (2*n) (4*n)) :
      |correctedCompositeAtom (4*n).factorial k|=compositeRootPayment k := by
    rw [correctedCompositeAtom,factorial_omits_octave hn hk,zero_sub,abs_neg,
      abs_of_nonneg (payment_bounds ((Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1)).1]
  have lower (k : ℕ) (hk : k∈Ioc (2*n) (4*n)) : |correctedCompositeAtom (4*n).factorial k|≤|correctedCompositeAtom m k| :=
    (hf hk).le.trans (he hk).1
  refine ⟨sum_le_sum lower,sum_le_sum fun k hk => (he hk).2.1,?_⟩
  unfold correctedCompositeVariation
  rw [sum_eq_sum_iff_of_le lower]
  exact forall_congr' fun k => forall_congr' fun hk => by rw [hf hk]; exact (he hk).2.2

/-- Even the least unsigned cost grows at the square-root scale. This
uniform bound applies before any signed cancellation of the kernel readings. -/
theorem square_root_floor_for_absolute_composite_mass (m : ℕ) {n : ℕ} (hn : 0<n) (hlog : 10<Real.log ((2*n:ℕ):ℝ)) :
    2*(2-Real.sqrt 2)*Real.sqrt n ≤ correctedCompositeVariation m n := by
  apply le_trans _ (absolute_composite_mass_extrema m hn hlog).1
  rw [factorial_variation_is_the_root_payment hn]
  have hc := Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) (2*n)) (Nat.cast_le.mpr (by omega : 2*n≤4*n)) (by norm_num : (0:ℝ)≤1/3)
  simp only [←Real.sqrt_eq_rpow,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2),show Real.sqrt 4=2 by norm_num] at hc ⊢
  linarith only [hc]

/-- The coefficient of the square-root floor is sharp. The remaining
term for the minimizing center is exactly a constant times the cube root. -/
theorem normalized_factorial_composite_variation :
    Tendsto (fun n : ℕ => correctedCompositeVariation (4*n).factorial n / Real.sqrt n)
      atTop (𝓝 (2*(2-Real.sqrt 2))) := by
  let C := 3*((4:ℝ)^(1/3:ℝ)-(2:ℝ)^(1/3:ℝ))
  have h := (((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul C).const_add (2*(2-Real.sqrt 2))
  rw [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hx := (Nat.cast_pos (α:=ℝ)).mpr hn
  have hs := Real.sqrt_pos.mpr hx
  rw [factorial_variation_is_the_root_payment hn]
  change 2*(2-Real.sqrt 2)+C*(n:ℝ)^(-(1/6:ℝ))=_
  apply (eq_div_iff hs.ne').mpr
  have hp : (n:ℝ)^(-(1/6:ℝ))*Real.sqrt n=(n:ℝ)^(1/3:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hx]
    norm_num
  rw [add_mul,mul_assoc C, hp]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0:ℝ)≤4) hx.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx.le,←Real.sqrt_eq_rpow,
    show Real.sqrt 4=2 by norm_num,C]
  ring

/-- Allowing the coprimality center to depend arbitrarily on the octave
cannot yield a sub-square-root majorant after taking absolute atom masses. -/
theorem every_subhalf_absolute_atom_bound_fails (m : ℕ → ℕ) {t : ℝ} (ht : t<1/2) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A*(n:ℝ)^t < correctedCompositeVariation (m n) n := by
  let c := 2*(2-Real.sqrt 2)
  have hc : 0<c := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)<4)
    rw [show Real.sqrt 4=2 by norm_num] at h
    dsimp only [c]
    linarith only [h]
  have hr := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hratio := ((tendsto_rpow_neg_atTop (sub_pos.mpr ht)).comp hr).const_mul A
  rw [mul_zero] at hratio
  have hl := Real.tendsto_log_atTop.comp (hr.const_mul_atTop (by norm_num : (0:ℝ)<2))
  filter_upwards [hratio.eventually_lt_const hc,hl.eventually_gt_atTop 10,eventually_gt_atTop (0:ℕ)] with n hpay hlog hn
  have hx := (Nat.cast_pos (α:=ℝ)).mpr hn
  have h := mul_lt_mul_of_pos_right hpay (Real.sqrt_pos.mpr hx)
  change A*(n:ℝ)^(-(1/2-t))*Real.sqrt n < c*Real.sqrt n at h
  rw [Real.sqrt_eq_rpow,mul_assoc,←Real.rpow_add hx,show -(1/2-t)+1/2=t by ring,←Real.sqrt_eq_rpow] at h
  exact h.trans_le (square_root_floor_for_absolute_composite_mass (m n) hn
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hlog))

#print axioms factorial_variation_is_the_root_payment
#print axioms absolute_composite_mass_extrema
#print axioms square_root_floor_for_absolute_composite_mass
#print axioms normalized_factorial_composite_variation
#print axioms every_subhalf_absolute_atom_bound_fails

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
