import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheLowerCountingOrderOfMertensExcursions

/-!
# Ordinary order of every positive Mertens moment

The upper order of an unweighted positive moment follows from
Littlewood. For the lower order, each subcritical excursion contributes
its index to a positive power. Packing the indices towards zero still
leaves a power of their cardinality. This also works below moment one,
where convexity is unavailable.
-/

noncomputable section
open Filter Finset
open scoped Topology
open _root_.RHTower GaloisForLFunctions.ArithmeticPowerMass
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Unweighted absolute p-th moment of the Mertens prefixes through N. -/
def mertensMoment (p : ℝ) (N : ℕ) :=
  ∑ k ∈ range (N+1), ‖mobiusMertensPartialSum k‖^p

theorem mertens_moment_nonneg (p : ℝ) (N : ℕ) : 0 ≤ mertensMoment p N :=
  sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

/-- Cardinality alone forces moment mass. No restriction p ≥ 1 enters. -/
theorem mertens_moment_from_population {p b : ℝ} (hp : 0<p) (hb : 0≤b) (N : ℕ) :
    ((mertensExcursions b 1 N).card:ℝ)^(1+p*b) ≤ 2^(1+p*b)*mertensMoment p N := by
  let E := mertensExcursions b 1 N
  have h := cardinal_power_le_mass E (mul_nonneg hp.le hb)
  have small (k : ℕ) (hk : k∈E) : ((k:ℝ)+1)^(p*b) ≤ ‖mobiusMertensPartialSum k‖^p := by
    have hlarge := (mem_filter.mp hk).2
    change 1*((k:ℝ)+1)^b < |shiftedMertensReal k| at hlarge
    rw [one_mul,←norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at hlarge
    rw [mul_comm p b,Real.rpow_mul (by positivity : 0≤(k:ℝ)+1)]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hlarge.le hp.le
  have hbnd : (∑ k ∈ E, ((k:ℝ)+1)^(p*b)) ≤ mertensMoment p N :=
    (sum_le_sum small).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun k _ _ => Real.rpow_nonneg (norm_nonneg _) _))
  exact h.trans (mul_le_mul_of_nonneg_left hbnd (by positivity))

/-- Above 1+pΘ every power bounds the moment uniformly. -/
theorem supercritical_mertens_moment {p c : ℝ} (hp : 0<p) (hc : 1+p*zetaZeroAbscissa<c) :
    ∃ B : ℝ, 0≤B ∧ ∀ N, mertensMoment p N ≤ B*((N:ℝ)+1)^c := by
  let a := (c-1)/p
  have ha : zetaZeroAbscissa<a := (lt_div_iff₀ hp).mpr (by linarith only [hc])
  have ha0 : 0≤a := by linarith only [ha,half_le_zetaZeroAbscissa]
  obtain ⟨A,hA,hh⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
  rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa)=a by ring] at hh
  refine ⟨A^p,Real.rpow_nonneg hA _,fun N => ?_⟩
  let X := (N:ℝ)+1
  have xp : 0<X := by dsimp only [X]; positivity
  have hrow (k : ℕ) (hk : k∈range (N+1)) : ‖mobiusMertensPartialSum k‖^p ≤ A^p*X^(a*p) := by
    rw [Real.rpow_mul xp.le,←Real.mul_rpow hA (Real.rpow_nonneg xp.le _)]
    have hkn := Nat.lt_succ_iff.mp (mem_range.mp hk)
    exact Real.rpow_le_rpow (norm_nonneg _) ((hh k).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (add_le_add_right (Nat.cast_le.mpr hkn) 1) ha0) hA)) hp.le
  have h := sum_le_sum hrow
  rw [sum_const,card_range,nsmul_eq_mul,Nat.cast_succ] at h
  have he : 1+a*p=c := by dsimp only [a]; field_simp; ring
  apply h.trans_eq
  change X*(A^p*X^(a*p)) = A^p*X^c
  rw [←he,Real.rpow_add xp,Real.rpow_one]; ring

/-- Below 1+pΘ the moment at every sufficiently large cutoff exceeds
every fixed multiple of the proposed power. -/
theorem eventually_large_mertens_moment {p c : ℝ} (hp : 0<p) (hc : c<1+p*zetaZeroAbscissa)
    (K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K*((N:ℝ)+1)^c < mertensMoment p N := by
  have hθ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  have hfrac : (c-1)/p < zetaZeroAbscissa := (div_lt_iff₀ hp).mpr (by linarith only [hc])
  obtain ⟨b,hb,hbθ⟩ := exists_between (max_lt hθ hfrac)
  have hb0 := (le_max_left 0 ((c-1)/p)).trans_lt hb
  let q := 1+p*b
  have hq : 0<q := add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hp.le hb0.le)
  have hcq : c<q := by
    have h := (div_lt_iff₀ hp).mp ((le_max_right 0 _).trans_lt hb)
    dsimp only [q]; linarith only [h]
  obtain ⟨d,hd,hd1⟩ := exists_between ((div_lt_one hq).mpr hcq)
  have hedge := (div_lt_iff₀ hq).mp hd
  have hX : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [all_cutoffs_many_mertens_excursions hbθ hd1 1 1,
    ((tendsto_rpow_atTop (sub_pos.mpr hedge)).comp hX).eventually_gt_atTop (2^q*|K|)] with N hpop hlarge
  let X := (N:ℝ)+1
  have xp : 0<X := by dsimp only [X]; positivity
  rw [one_mul] at hpop
  have hf := Real.rpow_le_rpow (Real.rpow_nonneg xp.le d) hpop.le hq.le
  rw [←Real.rpow_mul xp.le] at hf
  have hm := hf.trans (mertens_moment_from_population hp hb0.le N)
  have hh := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos xp c)
  change (2^q*|K|)*X^c < X^(d*q-c)*X^c at hh
  rw [←Real.rpow_add xp,sub_add_cancel] at hh
  have hp2 : 0<(2:ℝ)^q := by positivity
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg xp.le c))
  apply (mul_lt_mul_iff_right₀ hp2).mp
  change 2^q*(|K|*X^c) < 2^q*mertensMoment p N
  linarith only [hh,hm]

/-- The ordinary logarithmic limit through all integer cutoffs, for each
real moment order p > 0, equals 1+pΘ. -/
theorem all_positive_mertens_moment_orders {p : ℝ} (hp : 0<p) :
    Tendsto (fun N : ℕ => Real.log (1+mertensMoment p N)/Real.log ((N:ℝ)+1)) atTop
      (𝓝 (1+p*zetaZeroAbscissa)) := by
  have hθ : 0≤zetaZeroAbscissa := (by norm_num : (0:ℝ)≤1/2).trans half_le_zetaZeroAbscissa
  apply log_order_of_power_envelope (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hp.le hθ))
    (mertens_moment_nonneg p)
  · intro b _ hb; simpa only [one_mul] using eventually_large_mertens_moment hp hb 1
  · exact fun h => supercritical_mertens_moment hp h

#print axioms mertens_moment_from_population
#print axioms eventually_large_mertens_moment
#print axioms all_positive_mertens_moment_orders
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
