import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola

/-!
# The exact height of a removable prime head

Pricing only the last full Mangoldt head already determines which heights
admit a uniform price for every genuine prime reading and all intermediate
heads. The inverse samples every integer at an observation with precisely
that terminal head, then restores the moving sieve by divisor inversion.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Signed full Mangoldt head at the final quotient index floor(X^α). -/
def terminalMangoldtHead (α : ℝ) (X : ℕ) :=
  quotientReading (roughFloorCoefficient (logSquareCutoff X) (roughMangoldtWeight (logSquareCutoff X)))
    ⌊(X:ℝ)^α⌋₊

private def observation (α : ℝ) (n : ℕ) := ⌈(n:ℝ)^(1/α)⌉₊

private theorem observation_mono {α : ℝ} (ap : 0<α) : Monotone (observation α) :=
  fun _ _ h => Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr h) (one_div_pos.mpr ap).le)

/-- Sampling the inverse power never skips an integer head when α ≤ 1. -/
private theorem inverse_observation {α : ℝ} (ap : 0<α) (small : α ≤ 1) {n : ℕ} (np : 1 ≤ n) :
    n ≤ observation α n ∧ ⌊((observation α n:ℕ):ℝ)^α⌋₊=n ∧
    ∀ s : ℝ,0 ≤ s → ((observation α n:ℕ):ℝ)^(α*s) ≤ (2:ℝ)^(α*s)*(n:ℝ)^s := by
  let d := 1/α
  let X := observation α n
  have n1 : (1:ℝ) ≤ n := Nat.one_le_cast.mpr np
  have n0 := zero_lt_one.trans_le n1
  have d1 : 1 ≤ d := (le_div_iff₀ ap).mpr (by simpa only [one_mul] using small)
  have na := Real.rpow_nonneg n0.le d
  have low : (n:ℝ)^d ≤ X := Nat.le_ceil _
  have hi : (X:ℝ)<(n:ℝ)^d+1 := Nat.ceil_lt_add_one na
  have inv : d*α=1 := div_mul_cancel₀ 1 ap.ne'
  have original (x : ℝ) (nn : 0 ≤ x) : (x^d)^α=x := by rw [←Real.rpow_mul nn,inv,Real.rpow_one]
  have positivePow : 1 ≤ (n:ℝ)^d := Real.one_le_rpow n1 (zero_le_one.trans d1)
  have jump : (n:ℝ)^d+1 ≤ ((n:ℝ)+1)^d := by
    have split (x : ℝ) (p : 0<x) : x^d=x*x^(d-1) := by
      calc _ = x^(1+(d-1)) := by rw [show 1+(d-1)=d by ring]
           _ = _ := by rw [Real.rpow_add p,Real.rpow_one]
    rw [split _ n0,split _ (by positivity)]
    have mono := Real.rpow_le_rpow n0.le (by linarith : (n:ℝ) ≤ n+1) (sub_nonneg.mpr d1)
    have one := Real.one_le_rpow n1 (sub_nonneg.mpr d1)
    linarith only [mul_le_mul_of_nonneg_left mono n0.le,one,mono]
  have early := (show (n:ℝ) ≤ (n:ℝ)^d by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le n1 d1).trans low
  refine ⟨Nat.cast_le.mp early,(Nat.floor_eq_iff (Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ⟨?_,?_⟩,?_⟩
  · exact (original _ n0.le).symm.le.trans (Real.rpow_le_rpow na low ap.le)
  · exact (Real.rpow_lt_rpow (Nat.cast_nonneg X) (hi.trans_le jump) ap).trans_eq (original _ (by positivity))
  · intro s sp
    have size : (X:ℝ) ≤ 2*(n:ℝ)^d := by linarith only [hi,positivePow]
    apply (Real.rpow_le_rpow (Nat.cast_nonneg X) size (mul_nonneg ap.le sp)).trans_eq
    rw [Real.mul_rpow (by norm_num) na,←Real.rpow_mul n0.le,←mul_assoc,inv,one_mul]

private theorem observation_tendsto {α : ℝ} (ap : 0<α) (sm : α ≤ 1) :
    Tendsto (observation α) atTop atTop :=
  tendsto_atTop_mono (show ∀ n : ℕ,n ≤ observation α n by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | np
    · exact Nat.zero_le _
    · exact (inverse_observation ap sm np).1) tendsto_id

private def positiveLog (n : ℕ) := Real.log (max (2:ℝ) n)

private theorem complete_the_unit_weight {t : ℕ} (tp : 1 ≤ t) (y : ℕ) :
    weightedFrozenPrefix positiveLog y t=roughLogarithmicHead y t+Real.log 2 := by
  have each (n : ℕ) (hn : n ∈ Icc 1 t) :
      coprimeMoebiusIndicator (primorial y) n*positiveLog n=
        RoughReading.row y n*Real.log n+(if n=1 then Real.log 2 else 0) := by
    by_cases unit : n=1
    · simp [unit,positiveLog,coprimeMoebiusIndicator]
    rw [primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1,if_neg unit,add_zero,
      positiveLog,max_eq_right (show (2:ℝ) ≤ n by exact_mod_cast (show 2 ≤ n by have := (mem_Icc.mp hn).1; omega))]
  rw [weightedFrozenPrefix,roughLogarithmicHead,sum_congr rfl each,sum_add_distrib]
  simp [tp]

private theorem recover_the_strip_from_the_terminal_heads {α β : ℝ} (ap : 0<α) (sm : α ≤ 1) (critical : 1/2 ≤ β)
    (heads : ∀ ε : ℝ,0<ε → PrefixPower (α*(β+ε)) (terminalMangoldtHead α)) :
    RHTower.zetaZeroAbscissa ≤ β := by
  by_contra! tooNarrow
  let η := (RHTower.zetaZeroAbscissa-β)/3
  have ep : 0<η := div_pos (sub_pos.mpr tooNarrow) (by norm_num)
  let s := β+η
  have strict : 1/2<s := critical.trans_lt (lt_add_of_pos_right _ ep)
  have sp := (by norm_num : (0:ℝ)<1/2).trans strict
  let Y := fun n => logSquareCutoff (observation α n)
  have ym : Monotone Y := logSquareCutoff_mono.comp (observation_mono ap)
  have yt := logSquareCutoff_tendsto_atTop.comp (observation_tendsto ap sm)
  obtain ⟨C,c0,bound⟩ := heads η ep
  let diag := fun n => weightedFrozenPrefix positiveLog (Y n) n
  have diagPower : PrefixPower s diag := by
    apply prefixPower_of_eventual (C := C*(2:ℝ)^(α*s)+Real.log 2) (by simp [diag,weightedFrozenPrefix]) sp
    filter_upwards [yt.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with n high np
    let X := observation α n
    have sample := inverse_observation ap sm np
    have exactHead : terminalMangoldtHead α X= -roughLogarithmicHead (Y n) n := by
      rw [terminalMangoldtHead,sample.2.1,←rough_action_as_a_coefficient_prefix,full_rough_reading high]
    have cost := bound X
    rw [exactHead,abs_neg] at cost
    have price := cost.trans (mul_le_mul_of_nonneg_left (sample.2.2 s sp.le) c0)
    have one := Real.one_le_rpow (Nat.one_le_cast.mpr np) sp.le
    have term := mul_le_mul_of_nonneg_left one (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    change |weightedFrozenPrefix positiveLog (Y n) n| ≤ _
    rw [complete_the_unit_weight np]
    change |roughLogarithmicHead (Y n) n+Real.log 2| ≤ (C*2^(α*s)+Real.log 2)*(n:ℝ)^s
    change |roughLogarithmicHead (Y n) n| ≤ C*(2^(α*s)*(n:ℝ)^s) at price
    have tri := abs_add_le (roughLogarithmicHead (Y n) n) (Real.log 2)
    rw [abs_of_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))] at tri
    linarith only [price,term,tri]
  obtain ⟨A,a0,adiag⟩ := diagPower
  have v0 : 0<positiveLog 1 := by norm_num [positiveLog,Real.log_pos]
  have mono : Monotone positiveLog := fun _ _ h => Real.log_le_log
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (le_max_left ..)) (max_le_max_left _ (Nat.cast_le.mpr h))
  let D := A/positiveLog 1
  have dp : 0 ≤ D := div_nonneg a0 v0.le
  have read (n : ℕ) : |diag n| ≤ D*positiveLog 1*(n:ℝ)^s := by
    rw [show D*positiveLog 1=A from div_mul_cancel₀ _ v0.ne']; exact adiag n
  have full : PrefixPower (s+η) (coprimeMoebiusSum 1) := by
    apply prefixPower_of_eventual (C := D*(2:ℝ)^(α*η)) (by simp [coprimeMoebiusSum]) (add_pos sp ep)
    filter_upwards [(observation_tendsto ap sm) (log_square_deletion_cost strict (mul_pos ap ep)),eventually_ge_atTop (1:ℕ)] with n paid np
    let X := observation α n
    let E := deletionPrice s (Y n)
    have cheap : E^2 ≤ (X:ℝ)^(α*η) :=
      (le_mul_of_one_le_left (sq_nonneg E) (by have := Nat.cast_nonneg (α := ℝ) (Y n); linarith : 1 ≤ (Y n:ℝ)+1)).trans paid
    have restored := full_prefix_from_one_weighted_reading Y ym positiveLog mono v0 sp dp read n
    have product := cheap.trans ((inverse_observation ap sm np).2.2 η ep.le)
    have both := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left product dp) (Real.rpow_nonneg (Nat.cast_nonneg n) s)
    rw [Real.rpow_add (Nat.cast_pos.mpr np)]
    exact restored.trans (both.trans_eq (by ring))
  obtain ⟨K,k0,estimate⟩ := full
  have width := zetaZeroAbscissa_le_of_moebius_power_bound k0 (add_pos sp ep).le
    (fun n _ => by simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using estimate n)
  dsimp only [s,η] at width
  linarith only [width,tooNarrow]

/-- A uniform exponent for the signed costs of every lower head and every
Mangoldt-dominated weight that agrees with the surviving ordinary primes. -/
def uniformPrimeHeadPower (α u : ℝ) : Prop :=
  ∃ K : ℝ,0 ≤ K ∧ ∀ᶠ X : ℕ in atTop,∀ T : ℕ,(T:ℝ) ≤ (X:ℝ)^α →
    ∀ a : ArithmeticFunction ℝ,(∀ q,|a q| ≤ vonMangoldt q) →
    (∀ p,p.Prime → a p=roughMangoldtWeight (logSquareCutoff X) p) →
    |roughCofactorReading (logSquareCutoff X) X (quotientReading a)-
      roughInteriorReading a (logSquareCutoff X) X T| ≤ K*(X:ℝ)^u

private theorem terminal_price_of_all_lower_heads {α u : ℝ} (ap : 0<α) (sm : α ≤ 1) (up : 0<u)
    (uniform : uniformPrimeHeadPower α u) : PrefixPower u (terminalMangoldtHead α) := by
  obtain ⟨K,_,budget⟩ := uniform
  apply prefixPower_of_eventual (C := K) (by simp [terminalMangoldtHead,Real.zero_rpow ap.ne',quotientReading]) up
  filter_upwards [budget,eventually_ge_atTop (1:ℕ)] with X paid xp
  let T := ⌊(X:ℝ)^α⌋₊
  let y := logSquareCutoff X
  have size : (T:ℝ) ≤ (X:ℝ)^α := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have below : T ≤ X := Nat.cast_le.mp (size.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr xp) sm))
  have cut := paid T size (roughMangoldtWeight y) (mangoldt_dominated y) (fun _ _ => rfl)
  rw [rough_head_and_interior,add_sub_cancel_left,min_eq_right below] at cut
  exact cut

/-- Above the square-root line the signed price of just the terminal
Mangoldt head has exponent α times the ordinary zero abscissa. -/
theorem terminal_mangoldt_head_detects_the_strip {α β : ℝ} (ap : 0<α) (sm : α ≤ 1) (critical : 1/2 ≤ β) :
    (∀ ε : ℝ,0<ε → PrefixPower (α*(β+ε)) (terminalMangoldtHead α)) ↔ RHTower.zetaZeroAbscissa ≤ β := by
  refine ⟨recover_the_strip_from_the_terminal_heads ap sm critical,?_⟩
  intro strip ε ep
  have u0 := mul_pos ap ((by norm_num : (0:ℝ)<1/2).trans_le (critical.trans (le_add_of_nonneg_right ep.le)))
  apply terminal_price_of_all_lower_heads ap sm u0
  exact shrinking_the_cofactor_range_for_prime_readings ap
    (mul_lt_mul_of_pos_left (strip.trans_lt (lt_add_of_pos_right β ep)) ap)

/-- The half-plus price for all heads through X^α is equivalent to
α times the zero abscissa being at most one half, including equality.
Necessity uses only the full Mangoldt weight at each terminal height. -/
theorem sharp_square_root_height_for_all_prime_readings {α : ℝ} (ap : 0<α) (sm : α ≤ 1) :
    (∀ ε : ℝ,0<ε → uniformPrimeHeadPower α (1/2+ε)) ↔ α*RHTower.zetaZeroAbscissa ≤ 1/2 := by
  refine ⟨?_,fun h ε ep => shrinking_the_cofactor_range_for_prime_readings ap (h.trans_lt (lt_add_of_pos_right _ ep))⟩
  intro prices
  let β := (1/2:ℝ)/α
  have value : α*β=1/2 := by dsimp only [β]; field_simp
  have critical : 1/2 ≤ β := (le_div_iff₀ ap).mpr (by linarith only [sm])
  have strips := recover_the_strip_from_the_terminal_heads ap sm critical (fun ε ep => by
    let u := α*(β+ε)
    have scale : u=1/2+α*ε := by dsimp only [u]; rw [mul_add,value]
    have up : 0<u := by rw [scale]; positivity
    apply terminal_price_of_all_lower_heads ap sm up
    rw [scale]
    exact prices _ (mul_pos ap ep))
  exact (mul_le_mul_of_nonneg_left strips ap.le).trans_eq value

#print axioms sharp_square_root_height_for_all_prime_readings
#print axioms terminal_mangoldt_head_detects_the_strip
end GaloisForLFunctions.RestrictedFactorizationCalculus
