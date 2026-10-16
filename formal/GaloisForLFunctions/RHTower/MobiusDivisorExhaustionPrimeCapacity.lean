import GaloisForLFunctions.RHTower.MobiusDivisorMandatoryScalarBlock
import GaloisForLFunctions.RHTower.MobiusDivisorPositivePrimeSupply
import GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType

/-!
# Fixed prime capacity for paid exhaustion

The complete child source is sublinear relative to the number of available
signed helpers. One clock factor therefore suffices for an entire inherited
history; its choice does not depend on a subsequently processed core.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower
namespace PaidExhaustion
open GaloisForLFunctions.HTGeometry

def completeSource (M : ℕ) : ℝ := ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d

def singletonSource (M p : ℕ) : ℝ :=
  -Real.sqrt p * ((1-divisorPrimeClipWeight M p)*completeSource (M/p) +
    divisorPrimeClipWeight M p*completeSource (M/p+1))

lemma selectionPrimes_mono {a b : ℕ} (hab : a ≤ b) :
    mobiusDivisorSelectionPrimes a ⊆ mobiusDivisorSelectionPrimes b := by
  intro p hp
  obtain ⟨hp, hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hp).trans_le hab), hprime⟩

lemma singleton_eq_source (M : ℕ) (P : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hpP : p ∉ P) (hcore : mobiusDivisorSelectionPrimes (M/p+1) ⊆ P) :
    mobiusDivisorSelectionFibre M P {p} = singletonSource M p := by
  rw [show ({p} : Finset ℕ) = insert p ∅ by rfl,
    mobiusDivisorSelectionFibre_prime_interpolation hp M P ∅ hpP (by simp)]
  unfold mobiusDivisorInterpolatedFibre singletonSource completeSource
  rw [mobiusDivisorSelectionFibre_of_all_source_primes_processed (M/p) P ∅
      ((selectionPrimes_mono (Nat.le_succ _)).trans hcore),
    mobiusDivisorSelectionFibre_of_all_source_primes_processed (M/p+1) P ∅ hcore]
  simp

lemma singletonSource_mul (A r : ℕ) (hr : 0 < r) :
    singletonSource (A*r) r = -Real.sqrt r * completeSource A := by
  simp [singletonSource, divisorPrimeClipWeight, Nat.mul_div_cancel A hr]

/-- A fixed-width prime window dominates any smaller fixed counting budget. -/
lemma eventually_window_capacity (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b)
    (hwidth : 8*c ≤ b-a) :
    ∀ᶠ r : ℕ in atTop, c * Nat.primeCounting r ≤ (primesInIoc (a*r) (b*r)).card := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hratio : (1 : ℝ) < (b:ℝ)/a := (one_lt_div haR).mpr (by exact_mod_cast hab)
  have hc := ((tendsto_natCast_atTop_atTop : Tendsto (fun r : ℕ => (r:ℝ)) atTop atTop).
    const_mul_atTop haR).eventually (eventually_primeCount_window_ge hratio)
  have hp := tendsto_primeCounting_nat_ratio.eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2))
  have hl := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun r : ℕ => (r:ℝ)) atTop atTop)).eventually_ge_atTop
      (Real.log a)
  filter_upwards [hc, hp, hl, eventually_ge_atTop (2:ℕ)] with r hcount hprime hlog hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlr : 0 < Real.log (r:ℝ) := Real.log_pos (by exact_mod_cast hr)
  have hlar : 0 < Real.log ((a:ℝ)*r) := Real.log_pos (by
    have ha1 : (1:ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
    have hr1 : (1:ℝ) < r := by exact_mod_cast hr
    nlinarith)
  have habr : a*r ≤ b*r := Nat.mul_le_mul_right r hab.le
  have harg : (b:ℝ)/a*((a:ℝ)*r) = ((b*r:ℕ):ℝ) := by push_cast; field_simp
  rw [harg, show (a:ℝ)*r = ((a*r:ℕ):ℝ) by push_cast; rfl,
    Nat.floor_natCast, Nat.floor_natCast, ← card_primesInIoc habr] at hcount
  have hlow : ((b:ℝ)-a)*r ≤
      2*((primesInIoc (a*r) (b*r)).card:ℝ)*Real.log ((a:ℝ)*r) := by
    have hc' := (le_div_iff₀ hlar).mp (show
      (((b:ℝ)-a)/2*r)/Real.log ((a:ℝ)*r) ≤
        ((primesInIoc (a*r) (b*r)).card:ℝ) by
      convert hcount using 1 <;> push_cast <;> field_simp <;> ring)
    linarith only [hc']
  have hlog2 : Real.log ((a:ℝ)*r) ≤ 2*Real.log (r:ℝ) := by
    rw [Real.log_mul haR.ne' hrR.ne']
    linarith only [hlog]
  have hlow' : ((b:ℝ)-a)*r ≤
      4*((primesInIoc (a*r) (b*r)).card:ℝ)*Real.log (r:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog2
      (show 0 ≤ 2*((primesInIoc (a*r) (b*r)).card:ℝ) by positivity)
    linarith only [hlow, hh]
  have hpi : (Nat.primeCounting r:ℝ)*Real.log r ≤ 2*r := by
    have ht := (div_lt_iff₀ (div_pos hrR hlr)).mp hprime
    have ht' := (lt_div_iff₀ hlr).mp (show (Nat.primeCounting r:ℝ) < 2*r/Real.log r by
      simpa only [mul_div_assoc] using ht)
    exact ht'.le
  have hw : 8*(c:ℝ) ≤ (b:ℝ)-a := by
    have hh : 8*c+a ≤ b := by omega
    exact_mod_cast (show (8*c+a:ℕ) ≤ b from hh)
  have hcpi := mul_le_mul_of_nonneg_left hpi (show 0 ≤ 4*(c:ℝ) by positivity)
  have hwr := mul_le_mul_of_nonneg_right hw hrR.le
  have hfinal : (c:ℝ)*(Nat.primeCounting r:ℝ) ≤ (primesInIoc (a*r) (b*r)).card := by
    nlinarith only [hlow', hcpi, hwr, hlr]
  exact_mod_cast hfinal

private lemma source_normalized :
    Tendsto (fun M : ℕ => completeSource M / ((M:ℝ)*Real.sqrt M)) atTop (𝓝 0) := by
  have hi := tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop))
  have h := tendsto_sum_mobiusDivisorDilationChannel_log_normalized.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with M hM
  have hl : Real.log (M:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hM))
  change completeSource M * Real.log M / ((M:ℝ)*Real.sqrt M) *
    ((1:ℝ)/Real.log M) = _
  field_simp

/-- One fixed scale pays the mandatory singleton using fewer helpers than
the linear width of either source window. -/
lemma exists_source_scale (C : ℕ) (hC : 0 < C) (a : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, 1 ≤ n ∧ |completeSource (C*n)| ≤ (n:ℝ)*a*Real.sqrt n := by
  have hC' : (0:ℝ) < C := by exact_mod_cast hC
  have hclock : Tendsto (fun n : ℕ => C*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith) tendsto_id
  have ht := ((source_normalized.comp hclock).abs).const_mul ((C:ℝ)*Real.sqrt C)
  simp only [abs_zero, mul_zero] at ht
  obtain ⟨n, hn, hs⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (ht.eventually (eventually_lt_nhds ha))).exists
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have he : (C:ℝ)*Real.sqrt C *
      |completeSource (C*n) / ((C*n:ℕ)*Real.sqrt (C*n:ℕ))| =
      |completeSource (C*n)| / ((n:ℝ)*Real.sqrt n) := by
    rw [abs_div, abs_of_pos (by positivity), Nat.cast_mul,
      Real.sqrt_mul hC'.le]
    field_simp
  rw [he] at hs
  refine ⟨n, hn, ?_⟩
  have hh := (div_lt_iff₀ (mul_pos hn' hsqrt)).mp hs
  nlinarith only [hh]

end PaidExhaustion
end RHTower
