import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePowerThresholdOfWeightedInteriorPerturbations
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Detecting the zero abscissa in intervals of nearly full power width

The first quotient coefficient is the increment of a frozen rough Möbius
prefix. Comparing this increment to the increment of x^s gives a telescoping
bound at each prime wall. A logarithmic loss in interval length costs no
power in the resulting zero-abscissa test.
-/
noncomputable section
open Finset Filter RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Topology Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev F (y t : ℕ) := coprimeMoebiusSum (primorial y) t
private abbrev wall := logSquareCutoff

/-- A lower bound on the width of a sampling interval, up to every positive
power loss. A gap of n/(log n)^A has width exponent one. -/
def intervalWidthExponent (T : ℕ → ℕ) (κ : ℝ) : Prop :=
  ∀ η : ℝ,0 < η → ∀ᶠ n : ℕ in atTop,
    (n:ℝ)^(κ-η) ≤ (n:ℝ)-(T n:ℝ)

private theorem power_increment {x t s : ℝ} (xp : 0 < x) (t0 : 0 ≤ t) (tx : t ≤ x) (hs : 1/2 ≤ s) :
    (x-t)*x^(s-1) ≤ 2*(x^s-t^s) := by
  let z := t/x
  have z0 : 0 ≤ z := div_nonneg t0 xp.le
  have z1 : z ≤ 1 := (div_le_one xp).mpr tx
  have root : z^s ≤ Real.sqrt z := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge_of_imp z0 z1 hs (fun _ s0 => by linarith only [s0,hs])
  have ratio : 1-z ≤ 2*(1-z^s) := by
    nlinarith only [root,Real.sq_sqrt z0,sq_nonneg (1-Real.sqrt z)]
  have multiply : x^s*z^s=t^s := by
    rw [←Real.mul_rpow xp.le z0,show x*z=t by
      dsimp only [z]
      field_simp [xp.ne']]
  calc
    _ = x^s*(1-z) := by
      rw [Real.rpow_sub xp,Real.rpow_one];dsimp only [z];field_simp [xp.ne']
    _ ≤ x^s*(2*(1-z^s)) := mul_le_mul_of_nonneg_left ratio (Real.rpow_nonneg xp.le _)
    _ = _ := by linarith only [multiply]

/-- An eventual bound by increments of x^s at a monotonically growing
prime wall gives a bound for every complete prefix at every higher wall. -/
theorem recover_frozen_rows_from_power_increments (b T : ℕ → ℕ) (mono : Monotone b)
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (inc : ∀ᶠ n : ℕ in atTop,T n < n ∧
      |interiorKernel (b n) n (T n) 1| ≤ C*((n:ℝ)^s-(T n:ℝ)^s)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ n y : ℕ,b n ≤ y →
      |F y n| ≤ B*deletionPrice s y*(n:ℝ)^s := by
  obtain ⟨N,after⟩ := eventually_atTop.mp inc
  let S := ∑ n∈range N,|F (b n) n|
  have S0 : 0 ≤ S := sum_nonneg (fun _ _ => abs_nonneg _)
  let B := C+S
  have B0 : 0 ≤ B := add_nonneg hC S0
  refine ⟨B,B0,?_⟩
  refine induction_above_a_moving_prime_cutoff b mono (fun _ => B) (fun _ _ _ => le_rfl) (fun _ => B0) hs ?_
  intro n np previous
  have price := deletionPrice_one_le hs (b n)
  have big := le_mul_of_one_le_right B0 price
  have x1 : 1 ≤ (n:ℝ) := Nat.one_le_cast.mpr np
  have npow : 1 ≤ (n:ℝ)^s := Real.one_le_rpow x1 hs.le
  rcases lt_or_ge n N with early|late
  · have era : |F (b n) n| ≤ S :=
      single_le_sum (fun i _ => abs_nonneg (F (b i) i)) (mem_range.mpr early)
    exact era.trans ((le_add_of_nonneg_left hC).trans (big.trans
      (le_mul_of_one_le_right (B0.trans big) npow)))
  · obtain ⟨short,delta⟩ := after n late
    have old := previous (T n) short
    have range : 0 ≤ (n:ℝ)^s-(T n:ℝ)^s :=
      sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr short.le) hs.le)
    have bd : C ≤ B*deletionPrice s (b n) := (le_add_of_nonneg_right S0).trans big
    have gain := delta.trans (mul_le_mul_of_nonneg_right bd range)
    have tri := abs_add_le (interiorKernel (b n) n (T n) 1) (F (b n) (T n))
    have eq : interiorKernel (b n) n (T n) 1+F (b n) (T n)=F (b n) n := by
      simp only [interiorKernel,min_eq_right short.le,Nat.div_one,sub_add_cancel]
    rw [eq] at tri
    exact tri.trans ((add_le_add gain old).trans_eq (by ring))

private theorem cheap_square {s η : ℝ} (hs : 1/2 < s) (ep : 0 < η) :
    ∀ᶠ n : ℕ in atTop, (deletionPrice s (wall n))^2 ≤ (n:ℝ)^η := by
  filter_upwards [log_square_deletion_cost hs ep] with n cost
  exact (le_mul_of_one_le_left (sq_nonneg _)
    (le_add_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) (wall n)))).trans cost

/-- A width exponent κ costs at most 1−κ in recovering the zeta
abscissa from one signed increment. The prime wall is the actual
log-square sieve. No regularity of the lower endpoints is required. -/
theorem abscissa_from_first_site_and_interval_width {κ β : ℝ} (κ1 : κ ≤ 1) (hb : 1/2 ≤ β)
    (T : ℕ → ℕ) (width : intervalWidthExponent T κ)
    (obs : ∀ η : ℝ,0 < η → ∃ C : ℝ,∀ᶠ n : ℕ in atTop,
      |interiorKernel (wall n) n (T n) 1| ≤ C*(n:ℝ)^(β+η)) :
    _root_.RHTower.zetaZeroAbscissa ≤ β+(1-κ) := by
  have bound := sub_nonneg.mpr κ1
  apply abscissa_from_frozen_rows (hb.trans (le_add_of_nonneg_right bound))
    wall logSquareCutoff_mono (fun _ hs _ he => cheap_square hs he)
  intro ε ep
  let η := ε/4
  let s := β+(1-κ)+2*η
  have ηp : 0 < η := div_pos ep (by norm_num)
  have half : 1/2 < s := by dsimp only [s];linarith only [hb,bound,ηp]
  have sp := (by norm_num : (0:ℝ)<1/2).trans half
  obtain ⟨C,hC⟩ := obs η ηp
  have inc : ∀ᶠ n : ℕ in atTop, T n < n ∧ |interiorKernel (wall n) n (T n) 1| ≤
      (2*|C|)*((n:ℝ)^s-(T n:ℝ)^s) := by
    filter_upwards [hC,width η ηp,eventually_ge_atTop (1:ℕ)] with n read length np
    have xp : 0 < (n:ℝ) := Nat.cast_pos.mpr np
    have diff := (Real.rpow_pos_of_pos xp (κ-η)).trans_le length
    have less : T n < n := by exact_mod_cast (sub_pos.mp diff)
    have factor := mul_le_mul_of_nonneg_right length (Real.rpow_nonneg xp.le (s-1))
    rw [←Real.rpow_add xp,show κ-η+(s-1)=β+η by dsimp only [s];ring] at factor
    have frac := factor.trans (power_increment xp (Nat.cast_nonneg (T n)) (Nat.cast_le.mpr less.le) half.le)
    exact ⟨less,read.trans ((mul_le_mul (le_abs_self C) frac
      (Real.rpow_nonneg xp.le _) (abs_nonneg C)).trans_eq (by ring))⟩
  obtain ⟨B,hB,frozen⟩ := recover_frozen_rows_from_power_increments wall T logSquareCutoff_mono
    sp (by positivity) inc
  refine ⟨B,?_⟩
  filter_upwards [cheap_square half (show 0 < 2*η by positivity),eventually_ge_atTop (1:ℕ)] with n price np
  have one := deletionPrice_one_le sp (wall n)
  have sq : deletionPrice s (wall n) ≤ (deletionPrice s (wall n))^2 := by
    simpa only [pow_two] using le_mul_of_one_le_right (zero_le_one.trans one) one
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sq.trans price) hB)
    (Real.rpow_nonneg (Nat.cast_nonneg n) s)
  apply (frozen n (wall n) le_rfl).trans (ht.trans_eq ?_)
  rw [mul_assoc,←Real.rpow_add (Nat.cast_pos.mpr np),show 2*η+s=β+(1-κ)+ε by dsimp only [s,η];ring]

/-- Nearly full power width preserves the entire zero-abscissa test at a
single quotient coordinate, even when the head is asymptotic to n. -/
theorem first_site_on_nearly_full_power_intervals {β : ℝ} (hb : 1/2 ≤ β) (T : ℕ → ℕ)
    (width : intervalWidthExponent T 1) :
    (∀ ε : ℝ,0 < ε → ∃ C : ℝ,∀ᶠ n : ℕ in atTop,
      |interiorKernel (wall n) n (T n) 1| ≤ C*(n:ℝ)^(β+ε)) ↔
        _root_.RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro obs
    simpa only [sub_self,add_zero] using abscissa_from_first_site_and_interval_width (le_refl 1) hb T width obs
  · intro strip ε ep
    obtain ⟨C,_,top⟩ := upper_weighted_sites_all_heads ((by norm_num : (0:ℝ) ≤ 1/2).trans hb) strip ep
    refine ⟨C,?_⟩
    filter_upwards [top,eventually_ge_atTop (1:ℕ)] with n cap np
    simpa only [Nat.cast_one,Real.one_rpow,one_mul] using cap (T n) 1 (mem_Icc.mpr ⟨le_rfl,np⟩)

/-- The lower endpoint obtained by retaining a terminal interval of
length rounded up from n/(log n)^r. -/
def inverseLogIntervalHead (r n : ℕ) : ℕ := n-⌈(n:ℝ)/(Real.log n)^r⌉₊

/-- Every inverse-logarithmic fraction of the observation has width exponent one. -/
theorem inverse_log_window_has_full_width_exponent (r : ℕ) :
    intervalWidthExponent (inverseLogIntervalHead r) 1 := by
  intro η ep
  have grows := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (_root_.RHTower.burnolEventually_log_pow_le_rpow ep r),grows.eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℕ)] with n bound large np
  let P := (Real.log n)^r
  have P1 : 1 ≤ P := one_le_pow₀ large
  have Pp := zero_lt_one.trans_le P1
  have xp : 0 < (n:ℝ) := Nat.cast_pos.mpr np
  have ce : ⌈(n:ℝ)/P⌉₊ ≤ n := Nat.ceil_le.mpr (div_le_self xp.le P1)
  change (n:ℝ)^(1-η) ≤ (n:ℝ)-((n-⌈(n:ℝ)/P⌉₊:ℕ):ℝ)
  rw [Nat.cast_sub ce,sub_sub_cancel,Real.rpow_sub xp,Real.rpow_one]
  exact (div_le_div_of_nonneg_left xp.le Pp bound).trans (Nat.le_ceil _)

/-- Each individual inverse-logarithmic terminal interval gives the
same exponent criterion as the complete Möbius prefix. -/
theorem first_site_in_each_inverse_log_window (r : ℕ) {β : ℝ} (hb : 1/2 ≤ β) :
    (∀ ε : ℝ,0 < ε → ∃ C : ℝ,∀ᶠ n : ℕ in atTop,
      |interiorKernel (wall n) n (inverseLogIntervalHead r n) 1| ≤ C*(n:ℝ)^(β+ε)) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ β :=
  first_site_on_nearly_full_power_intervals hb _ (inverse_log_window_has_full_width_exponent r)

end GaloisForLFunctions.RestrictedFactorizationCalculus
