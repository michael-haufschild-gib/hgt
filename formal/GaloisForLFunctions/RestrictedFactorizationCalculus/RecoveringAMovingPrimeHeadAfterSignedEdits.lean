import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola

/-!
# Recovering the Möbius prefix after edits to a moving prime reading

At the current wall every edit away from the unit uses a strictly smaller
cofactor. Logarithmic partial summation leaves room to absorb their weighted
mass. A second finite Euler product restores the unrestricted prefix.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev rowPrefix (y n : ℕ) := coprimeMoebiusSum (primorial y) n

/-- Absolute mass of the edits to a genuine Mangoldt reading at a given exponent. -/
def primeHeadEditMass (s : ℝ) (y n : ℕ) (a : ArithmeticFunction ℝ) :=
  ∑ q ∈ Icc 1 n,|a q-roughMangoldtWeight y q|*(q:ℝ)^(-s)

private theorem edit_price_on_smaller_rows {s H : ℝ} (sp : 0<s) (hH : 0 ≤ H)
    {n : ℕ} (np : 0<n) (y : ℕ) (a : ArithmeticFunction ℝ) (unit : a 1=roughMangoldtWeight y 1)
    (rows : ∀ k,k<n → |rowPrefix y k| ≤ H*(k:ℝ)^s) :
    |quotientReading (roughFloorCoefficient y a) n-
      quotientReading (roughFloorCoefficient y (roughMangoldtWeight y)) n| ≤
      H*(n:ℝ)^s*primeHeadEditMass s y n a := by
  rw [coefficient_head_as_quotient_sum,coefficient_head_as_quotient_sum,←sum_sub_distrib,primeHeadEditMass,mul_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro q hq
  rw [←sub_mul,abs_mul]
  by_cases one : q=1
  · simp [one,unit]
  have qp := (mem_Icc.mp hq).1
  have q1 : 1<q := by omega
  have qpos : 0<(q:ℝ) := Nat.cast_pos.mpr qp
  have floor : ((n/q:ℕ):ℝ) ≤ (n:ℝ)/q :=
    (le_div_iff₀ qpos).mpr (by exact_mod_cast Nat.div_mul_le_self n q)
  have smaller := (rows (n/q) (Nat.div_lt_self np q1)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) floor sp.le) hH)
  rw [Real.div_rpow (Nat.cast_nonneg _) qpos.le] at smaller
  apply (mul_le_mul_of_nonneg_left smaller (abs_nonneg _)).trans_eq
  rw [Real.rpow_neg qpos.le]; ring

/-- The logarithmic variation at exponent s uses only strictly earlier rows. -/
private theorem log_price_on_smaller_rows {s H : ℝ} (hs : 1/2 ≤ s) (hH : 0 ≤ H)
    {n : ℕ} (np : 0<n) (y : ℕ) (rows : ∀ k,k<n → |rowPrefix y k| ≤ H*(k:ℝ)^s) :
    |rowPrefix y n*Real.log n-roughLogarithmicHead y n| ≤ 2*H*(n:ℝ)^s := by
  let h := s-1/2
  have hp : 0 ≤ h := sub_nonneg.mpr hs
  have n0 : 0<(n:ℝ) := Nat.cast_pos.mpr np
  have e : h+1/2=s := by dsimp only [h]; ring
  have pp (k : ℕ) (kp : 0<k) : (k:ℝ)^h*Real.sqrt k=(k:ℝ)^s := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add (Nat.cast_pos.mpr kp),e]
  have budget := critical_variation_of_the_frozen_logarithmic_row y n
    (mul_nonneg hH (Real.rpow_nonneg n0.le h)) (fun k kn => by
      rcases Nat.eq_zero_or_pos k with rfl | kp
      · simp [rowPrefix,coprimeMoebiusSum]
      have smaller := rows k kn
      rw [←pp k kp] at smaller
      have growth := Real.rpow_le_rpow (Nat.cast_nonneg k) (Nat.cast_le.mpr kn.le) hp
      exact smaller.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right growth (Real.sqrt_nonneg _)) hH).trans_eq (mul_assoc ..).symm))
  have exactLog : weightedFrozenPrefix (fun k => Real.log k) y n=roughLogarithmicHead y n :=
    sum_congr rfl (fun k hk => congrArg (fun u : ℝ => u*Real.log k)
      (primorial_indicator_eq_deleted_mobius y k (mem_Icc.mp hk).1))
  rw [exactLog] at budget
  exact budget.trans_eq (by rw [←pp n np]; ring)

/-- A strict fraction of the endpoint logarithm can be spent on changes
to the prime weights at every observation. The resulting sequence of
heads recovers the full prefix with two finite Euler factors. -/
theorem recover_the_prefix_from_a_perturbed_prime_head {s δ : ℝ} (hs : 1/2 ≤ s) (dp : 0<δ)
    (b : ℕ → ℕ) (inc : Monotone b) (a : ℕ → ArithmeticFunction ℝ)
    (active : ∀ᶠ n : ℕ in atTop,0<b n ∧ a n 1=roughMangoldtWeight (b n) 1 ∧
      primeHeadEditMass s (b n) n (a n) ≤ (1-δ)*Real.log n)
    {B : ℝ} (bp : 0 ≤ B)
    (reading : ∀ᶠ n : ℕ in atTop,|quotientReading (roughFloorCoefficient (b n) (a n)) n| ≤ B*(n:ℝ)^s) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ n,|coprimeMoebiusSum 1 n| ≤ C*(deletionPrice s (b n))^2*(n:ℝ)^s := by
  have sp := (by norm_num : (0:ℝ)<1/2).trans_le hs
  have top := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,late⟩ := eventually_atTop.mp (active.and (reading.and (top.eventually_ge_atTop (3/δ))))
  let C := max (N:ℝ) B
  have c0 : 0 ≤ C := (Nat.cast_nonneg N).trans (le_max_left ..)
  have allRows (n y : ℕ) (high : b n ≤ y) : |rowPrefix y n| ≤ C*deletionPrice s y*(n:ℝ)^s := by
    apply induction_above_a_moving_prime_cutoff b inc (fun _ => C) (fun _ _ _ => le_rfl)
      (fun _ => c0) sp _ n y high
    intro t tp ih
    let Y := b t
    let H := C*deletionPrice s Y
    let Z := H*(t:ℝ)^s
    have e1 := deletionPrice_one_le sp Y
    have h0 : 0 ≤ H := mul_nonneg c0 (zero_le_one.trans e1)
    have hc : C ≤ H := le_mul_of_one_le_right c0 e1
    have power : 1 ≤ (t:ℝ)^s := Real.one_le_rpow (Nat.one_le_cast.mpr tp) sp.le
    have z0 : 0 ≤ Z := mul_nonneg h0 (Real.rpow_nonneg (Nat.cast_nonneg t) _)
    by_cases early : t<N
    · exact (abs_coprimeMoebiusSum_le _ _).trans (((Nat.cast_le.mpr early.le).trans (le_max_left _ B)).trans
        (hc.trans (le_mul_of_one_le_right h0 power)))
    obtain ⟨⟨yp,unit,mass⟩,seen,logsize⟩ := late t (le_of_not_gt early)
    have edit := edit_price_on_smaller_rows sp h0 tp Y (a t) unit ih
    have variation := log_price_on_smaller_rows hs h0 tp Y ih
    have full := (rough_action_as_a_coefficient_prefix Y t (roughMangoldtWeight Y)).symm.trans (full_rough_reading yp t)
    rw [full,sub_neg_eq_add] at edit
    have editCost := edit.trans (mul_le_mul_of_nonneg_left mass z0)
    have observation := seen.trans (mul_le_mul_of_nonneg_right ((le_max_right _ B).trans hc)
      (Real.rpow_nonneg (Nat.cast_nonneg t) _))
    let M := rowPrefix Y t
    let L := Real.log (t:ℝ)
    let V := roughLogarithmicHead Y t
    let R := quotientReading (roughFloorCoefficient Y (a t)) t
    have identity : M*L=(M*L-V)+(R+V)-R := by ring
    have tri := (abs_sub ((M*L-V)+(R+V)) R).trans
      (add_le_add_right (abs_add_le (M*L-V) (R+V)) _)
    rw [←identity] at tri
    have Lp : 0<L := (div_pos (by norm_num) dp).trans_le logsize
    rw [abs_mul,abs_of_pos Lp] at tri
    have room := mul_le_mul_of_nonneg_left ((div_le_iff₀ dp).mp logsize) z0
    change |M*L-V| ≤ 2*H*(t:ℝ)^s at variation
    change |R+V| ≤ Z*((1-δ)*L) at editCost
    change |R| ≤ Z at observation
    change |M| ≤ Z
    apply le_of_mul_le_mul_right _ Lp
    dsimp only [Z] at *
    linarith only [tri,variation,editCost,observation,room]
  refine ⟨C,c0,fun n => ?_⟩
  let Y := b n
  have h := restore_full_row_from_prime_cutoff sp n Y
    (mul_nonneg c0 (zero_le_one.trans (deletionPrice_one_le sp Y))) (fun k kn => allRows k Y (inc kn))
  change |rowPrefix 0 n| ≤ _ at h
  rw [show rowPrefix 0 n=coprimeMoebiusSum 1 n by simp [rowPrefix]] at h
  exact h.trans_eq (by dsimp only [Y]; ring)

/-- Keeping the ordinary primes bounds the perturbation mass independently
of the height and sieve, even when each proper-power sign is chosen anew. -/
theorem mass_of_all_signed_proper_power_edits {s : ℝ} (hs : 1/2<s) (upper : s ≤ 1)
    (y n : ℕ) (a : ArithmeticFunction ℝ) (dom : ∀ q,|a q| ≤ vonMangoldt q)
    (fix : ∀ p,p.Prime → a p=roughMangoldtWeight y p) :
    primeHeadEditMass s y n a ≤ 2*(36/(s-1/2)) := by
  have cap := RHTower.sum_nonprime_vonMangoldt_rpow_le (sub_pos.mpr hs)
    (by linarith only [upper] : s-1/2 ≤ 1) n
  rw [show (1:ℝ)/2+(s-1/2)=s by ring] at cap
  apply le_trans _ (mul_le_mul_of_nonneg_left cap (by norm_num : (0:ℝ) ≤ 2))
  rw [primeHeadEditMass,mul_sum,sum_filter]
  apply sum_le_sum
  intro q _
  by_cases hp : q.Prime
  · simp [fix q hp,hp]
  · simp only [hp,not_false_eq_true,if_true]
    have diff := (abs_sub (a q) (roughMangoldtWeight y q)).trans ((add_le_add (dom q) (mangoldt_dominated y q)).trans_eq (two_mul _).symm)
    exact (mul_le_mul_of_nonneg_right diff (Real.rpow_nonneg (Nat.cast_nonneg q) _)).trans_eq (by ring)

#print axioms recover_the_prefix_from_a_perturbed_prime_head
#print axioms mass_of_all_signed_proper_power_edits
end GaloisForLFunctions.RestrictedFactorizationCalculus
