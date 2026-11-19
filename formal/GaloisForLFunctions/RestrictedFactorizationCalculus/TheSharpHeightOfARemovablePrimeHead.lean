import GaloisForLFunctions.RestrictedFactorizationCalculus.RecoveringAMovingPrimeHeadAfterSignedEdits

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

/-- Signed terminal head of a prime reading chosen at the current observation. -/
def terminalPrimeHead (α : ℝ) (a : ℕ → ArithmeticFunction ℝ) (X : ℕ) :=
  quotientReading (roughFloorCoefficient (logSquareCutoff X) (a X)) ⌊(X:ℝ)^α⌋₊

/-- The terminal head of the full surviving Mangoldt weight. -/
abbrev terminalMangoldtHead (α : ℝ) :=
  terminalPrimeHead α (fun X => roughMangoldtWeight (logSquareCutoff X))

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

private theorem recover_the_strip_from_the_terminal_heads {α β : ℝ} (ap : 0<α) (sm : α ≤ 1) (critical : 1/2 ≤ β)
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ X q,|a X q| ≤ vonMangoldt q)
    (fix : ∀ X p,p.Prime → a X p=roughMangoldtWeight (logSquareCutoff X) p)
    (heads : ∀ ε : ℝ,0<ε → PrefixPower (α*(β+ε)) (terminalPrimeHead α a)) :
    RHTower.zetaZeroAbscissa ≤ β := by
  by_contra! tooNarrow
  let η := (RHTower.zetaZeroAbscissa-β)/3
  have ep : 0<η := div_pos (sub_pos.mpr tooNarrow) (by norm_num)
  let s := β+η
  have strict : 1/2<s := critical.trans_lt (lt_add_of_pos_right _ ep)
  have sp := (by norm_num : (0:ℝ)<1/2).trans strict
  have small : s ≤ 1 := by
    have strip := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths
    dsimp only [s,η]; linarith only [strip,tooNarrow]
  let Y := fun n => logSquareCutoff (observation α n)
  let w := fun n => a (observation α n)
  have ym : Monotone Y := logSquareCutoff_mono.comp (observation_mono ap)
  have yt := logSquareCutoff_tendsto_atTop.comp (observation_tendsto ap sm)
  obtain ⟨C,c0,bound⟩ := heads η ep
  have reading : ∀ᶠ n : ℕ in atTop,|quotientReading (roughFloorCoefficient (Y n) (w n)) n| ≤
      (C*(2:ℝ)^(α*s))*(n:ℝ)^s := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n np
    let X := observation α n
    have sample := inverse_observation ap sm np
    have paid := bound X
    change |quotientReading (roughFloorCoefficient (Y n) (w n)) ⌊(X:ℝ)^α⌋₊| ≤ C*(X:ℝ)^(α*s) at paid
    rw [sample.2.1] at paid
    exact paid.trans ((mul_le_mul_of_nonneg_left (sample.2.2 s sp.le) c0).trans_eq (mul_assoc ..).symm)
  let P := 2*(36/(s-1/2))
  have logtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have active : ∀ᶠ n : ℕ in atTop,0<Y n ∧ w n 1=roughMangoldtWeight (Y n) 1 ∧
      primeHeadEditMass s (Y n) n (w n) ≤ (1-(1/2:ℝ))*Real.log n := by
    filter_upwards [yt.eventually_ge_atTop 1,logtop.eventually_ge_atTop (2*P)] with n high large
    have unit (f : ArithmeticFunction ℝ) (h : |f 1| ≤ vonMangoldt 1) : f 1=0 :=
      abs_eq_zero.mp (le_antisymm (by simpa using h) (abs_nonneg _))
    have same : w n 1=roughMangoldtWeight (Y n) 1 :=
      (unit _ (dom (observation α n) 1)).trans (unit _ (mangoldt_dominated (Y n) 1)).symm
    have cheap := mass_of_all_signed_proper_power_edits strict small (Y n) n (w n)
      (dom (observation α n)) (fix (observation α n))
    exact ⟨high,same,cheap.trans (by change P ≤ _; linarith only [large])⟩
  obtain ⟨A,a0,restore⟩ := recover_the_prefix_from_a_perturbed_prime_head strict.le
    (by norm_num : (0:ℝ)<1/2) Y ym w active (mul_nonneg c0 (by positivity)) reading
  have full : PrefixPower (s+η) (coprimeMoebiusSum 1) := by
    apply prefixPower_of_eventual (C := A*(2:ℝ)^(α*η)) (by simp [coprimeMoebiusSum]) (add_pos sp ep)
    filter_upwards [(observation_tendsto ap sm) (log_square_deletion_cost strict (mul_pos ap ep)),eventually_ge_atTop (1:ℕ)] with n paid np
    let X := observation α n
    let E := deletionPrice s (Y n)
    have cheap : E^2 ≤ (X:ℝ)^(α*η) :=
      (le_mul_of_one_le_left (sq_nonneg E) (by have := Nat.cast_nonneg (α := ℝ) (Y n); linarith : 1 ≤ (Y n:ℝ)+1)).trans paid
    have product := cheap.trans ((inverse_observation ap sm np).2.2 η ep.le)
    have both := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left product a0) (Real.rpow_nonneg (Nat.cast_nonneg n) s)
    rw [Real.rpow_add (Nat.cast_pos.mpr np)]
    exact (restore n).trans (both.trans_eq (by ring))
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
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ X q,|a X q| ≤ vonMangoldt q)
    (fix : ∀ X p,p.Prime → a X p=roughMangoldtWeight (logSquareCutoff X) p)
    (uniform : uniformPrimeHeadPower α u) : PrefixPower u (terminalPrimeHead α a) := by
  obtain ⟨K,_,budget⟩ := uniform
  apply prefixPower_of_eventual (C := K) (by simp [terminalPrimeHead,Real.zero_rpow ap.ne',quotientReading]) up
  filter_upwards [budget,eventually_ge_atTop (1:ℕ)] with X paid xp
  let T := ⌊(X:ℝ)^α⌋₊
  let y := logSquareCutoff X
  have size : (T:ℝ) ≤ (X:ℝ)^α := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have below : T ≤ X := Nat.cast_le.mp (size.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr xp) sm))
  have cut := paid T size (a X) (dom X) (fix X)
  rw [rough_head_and_interior,add_sub_cancel_left,min_eq_right below] at cut
  exact cut

/-- Each single prime reading, including independently chosen signed proper
powers at every observation, detects the zero abscissa in its terminal head. -/
theorem one_perturbed_terminal_head_detects_the_strip {α β : ℝ} (ap : 0<α) (sm : α ≤ 1) (critical : 1/2 ≤ β)
    (a : ℕ → ArithmeticFunction ℝ) (dom : ∀ X q,|a X q| ≤ vonMangoldt q)
    (fix : ∀ X p,p.Prime → a X p=roughMangoldtWeight (logSquareCutoff X) p) :
    (∀ ε : ℝ,0<ε → PrefixPower (α*(β+ε)) (terminalPrimeHead α a)) ↔ RHTower.zetaZeroAbscissa ≤ β := by
  refine ⟨recover_the_strip_from_the_terminal_heads ap sm critical a dom fix,?_⟩
  intro strip ε ep
  have u0 := mul_pos ap ((by norm_num : (0:ℝ)<1/2).trans_le (critical.trans (le_add_of_nonneg_right ep.le)))
  apply terminal_price_of_all_lower_heads ap sm u0 a dom fix
  exact shrinking_the_cofactor_range_for_prime_readings ap
    (mul_lt_mul_of_pos_left (strip.trans_lt (lt_add_of_pos_right β ep)) ap)

/-- The full surviving Mangoldt reading at terminal heights alone detects the strip. -/
theorem terminal_mangoldt_head_detects_the_strip {α β : ℝ} (ap : 0<α) (sm : α ≤ 1) (critical : 1/2 ≤ β) :
    (∀ ε : ℝ,0<ε → PrefixPower (α*(β+ε)) (terminalMangoldtHead α)) ↔ RHTower.zetaZeroAbscissa ≤ β :=
  one_perturbed_terminal_head_detects_the_strip ap sm critical _ (fun X => mangoldt_dominated (logSquareCutoff X)) (fun _ _ _ => rfl)

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
  have strips := (terminal_mangoldt_head_detects_the_strip ap sm critical).mp (fun ε ep => by
    let u := α*(β+ε)
    have scale : u=1/2+α*ε := by dsimp only [u]; rw [mul_add,value]
    have up : 0<u := by rw [scale]; positivity
    apply terminal_price_of_all_lower_heads ap sm up _ (fun X => mangoldt_dominated (logSquareCutoff X)) (fun _ _ _ => rfl)
    rw [scale]
    exact prices _ (mul_pos ap ep))
  exact (mul_le_mul_of_nonneg_left strips ap.le).trans_eq value

#print axioms sharp_square_root_height_for_all_prime_readings
#print axioms one_perturbed_terminal_head_detects_the_strip
#print axioms terminal_mangoldt_head_detects_the_strip
end GaloisForLFunctions.RestrictedFactorizationCalculus
