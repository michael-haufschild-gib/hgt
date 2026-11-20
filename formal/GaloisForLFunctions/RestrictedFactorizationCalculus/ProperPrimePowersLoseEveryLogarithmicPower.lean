import GaloisForLFunctions.RestrictedFactorizationCalculus.LogarithmicSavingsThroughoutTheRoughInterior
import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeOnlyQuotientRowsOfTheRoughInterior

/-!
# Absolute cancellation cost of the proper prime powers

The rough prefix at a quotient satisfies two bounds: uniform logarithmic
saving at the external scale and the trivial length bound at the quotient
itself. Geometric interpolation transfers the saving to any input with a
bounded absolute Dirichlet sum at an exponent below one. Proper prime
powers satisfy that condition above one half.
-/
noncomputable section
open Filter Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Topology Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev F (y m : ℕ) := coprimeMoebiusSum (primorial y) m

/-- A logarithmically small bound at the ambient scale and a length
bound at the quotient imply a weighted uniform bound at each site. -/
private theorem interpolate {U X L q C s : ℝ} {A m : ℕ}
    (hu : 0 ≤ U) (hx : 0 < X) (hl : 1 ≤ L) (hq : 0 < q) (hc : 1 ≤ C)
    (hs : 0 ≤ s) (hs1 : s < 1) (hm : (A:ℝ) ≤ (m:ℝ)*(1-s))
    (small : U*L^m ≤ C*X) (length : U*q ≤ X) :
    U*L^A ≤ C*X*q^(-s) := by
  have hlp := zero_lt_one.trans_le hl
  have hsp := sub_pos.mpr hs1
  have hlower : L^A ≤ (L^m)^(1-s) := by
    rw [←Real.rpow_natCast L A,←Real.rpow_natCast L m,←Real.rpow_mul hlp.le]
    exact Real.rpow_le_rpow_of_exponent_le hl hm
  have hu1 := Real.rpow_le_rpow (mul_nonneg hu (pow_nonneg hlp.le m)) small hsp.le
  have hu2 := Real.rpow_le_rpow (mul_nonneg hu hq.le) length hs
  have hprod := mul_le_mul hu1 hu2 (Real.rpow_nonneg (mul_nonneg hu hq.le) _)
    (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hc) hx.le) _)
  rw [Real.mul_rpow hu (pow_nonneg hlp.le m),Real.mul_rpow hu hq.le,
    Real.mul_rpow (zero_le_one.trans hc) hx.le] at hprod
  have hU : U^(1-s)*U^s=U := by
    rw [←Real.rpow_add' hu (by linarith : (1-s)+s≠0),sub_add_cancel,Real.rpow_one]
  have hX : X^(1-s)*X^s=X := by rw [←Real.rpow_add hx,sub_add_cancel,Real.rpow_one]
  have hh : (U*(L^m)^(1-s))*q^s ≤ C^(1-s)*X := by
    calc _ = ((U^(1-s)*U^s)*(L^m)^(1-s))*q^s := by rw [hU]
         _ = (U^(1-s)*(L^m)^(1-s))*(U^s*q^s) := by ring
         _ ≤ _ := hprod
         _ = _ := by rw [mul_assoc,hX]
  have hc' : C^(1-s) ≤ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hc (show 1-s ≤ 1 by linarith)
  rw [Real.rpow_neg hq.le,←div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mpr
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlower hu) (Real.rpow_nonneg hq.le _)).trans
    (hh.trans (mul_le_mul_of_nonneg_right hc' hx.le))

/-- The absolute mass of every arithmetic input inherits all logarithmic
savings after normalization by its finite weighted Dirichlet norm. -/
theorem absolute_interior_via_dirichlet_mass {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ y ≤ logSquareCutoff X, ∀ T : ℕ, ∀ w : ℕ → ℝ,
      (∑ q∈Icc 1 X,|w q*interiorKernel y X T q|)*Real.log X^A ≤
        C*(X:ℝ)*(∑ q∈Icc 1 X,|w q| * (q:ℝ)^(-s)) := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((A:ℝ)/(1-s))
  have hsize := ((div_lt_iff₀ (sub_pos.mpr hs1)).mp hm).le
  obtain ⟨B,hB,hbound⟩ := uniform_log_savings_for_rough_prefixes m
  let C := max 1 B
  have hC : 1 ≤ C := le_max_left .. 
  have c0 := zero_le_one.trans hC
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hbound,(Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1,eventually_ge_atTop 1]
    with X cap hL hX
  intro y hy T w
  let L := Real.log (X:ℝ)
  have l0 : 0 ≤ L := zero_le_one.trans hL
  have x0 : 0 < (X:ℝ) := Nat.cast_pos.mpr hX
  have single (t q : ℕ) (ht : t ≤ X) (hq : 0 < q) :
      |F y (t/q)| * L^A ≤ C*(X:ℝ)*(q:ℝ)^(-s) := by
    apply interpolate (abs_nonneg _) x0 hL (Nat.cast_pos.mpr hq) hC hs hs1 hsize
    · exact (cap y hy _ ((Nat.div_le_self ..).trans ht)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 B) x0.le)
    · have hlen := mul_le_mul_of_nonneg_right (abs_coprimeMoebiusSum_le (primorial y) (t/q))
        (Nat.cast_nonneg (α:=ℝ) q)
      apply hlen.trans
      exact_mod_cast (Nat.div_mul_le_self t q).trans ht
  rw [sum_mul,mul_sum]
  apply sum_le_sum
  intro q hq
  have qp := (mem_Icc.mp hq).1
  have htri := mul_le_mul_of_nonneg_right (abs_sub (F y (X/q)) (F y (min X T/q))) (pow_nonneg l0 A)
  rw [add_mul] at htri
  have htotal := htri.trans (add_le_add (single X q le_rfl qp) (single (min X T) q (min_le_left X T) qp))
  rw [abs_mul,mul_assoc]
  exact (mul_le_mul_of_nonneg_left htotal (abs_nonneg _)).trans_eq (by ring)

/-- The absolute budget on all nonprime Mangoldt sites is negligible by
every logarithmic power, uniformly in both the prime wall and the removed head. -/
theorem absolute_proper_prime_power_saving (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ y ≤ logSquareCutoff X, ∀ T : ℕ,
      (∑ q∈(Icc 1 X).filter (fun q => ¬q.Prime),vonMangoldt q*|interiorKernel y X T q|)*
        Real.log X^A ≤ C*(X:ℝ) := by
  obtain ⟨C,hC,h⟩ := absolute_interior_via_dirichlet_mass (by norm_num : (0:ℝ) ≤ 3/4)
    (by norm_num : (3/4:ℝ) < 1) A
  refine ⟨144*C,by positivity,?_⟩
  filter_upwards [h] with X hx
  intro y hy T
  let w := fun q : ℕ => if ¬q.Prime then vonMangoldt q else 0
  have hrow := hx y hy T w
  have hb := _root_.RHTower.sum_nonprime_vonMangoldt_rpow_le (by norm_num : (0:ℝ) < 1/4)
    (by norm_num : (1/4:ℝ) ≤ 1) X
  norm_num at hb
  have hleft : (∑ q∈Icc 1 X,|w q*interiorKernel y X T q|)=
      ∑ q∈(Icc 1 X).filter (fun q => ¬q.Prime),vonMangoldt q*|interiorKernel y X T q| := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hq : q.Prime <;> simp [w,hq,abs_mul,abs_of_nonneg (vonMangoldt_nonneg (n:=q))]
  have hright : (∑ q∈Icc 1 X,|w q| * (q:ℝ)^(-(3/4:ℝ)))=
      ∑ q∈(Icc 1 X).filter (fun q => ¬q.Prime),vonMangoldt q*(q:ℝ)^(-(3/4:ℝ)) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q _
    by_cases hq : q.Prime <;> simp [w,hq,abs_of_nonneg (vonMangoldt_nonneg (n:=q))]
  rw [hleft,hright] at hrow
  apply hrow.trans ((mul_le_mul_of_nonneg_left hb (mul_nonneg hC (Nat.cast_nonneg _))).trans_eq ?_)
  ring

end GaloisForLFunctions.RestrictedFactorizationCalculus
