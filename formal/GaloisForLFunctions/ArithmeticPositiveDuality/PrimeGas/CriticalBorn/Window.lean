import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.CutoffMass

/-! # Mass carried by a short multiplicative interval below the harmonic exponent -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Real Filter Finset
open scoped Topology

def window (c x : ℝ) := primes (cutoff x) \ primes (cutoff (c*x))

def windowMass (a c x : ℝ) := ∑ p ∈ window c x, (p : ℝ)^(a-1)

theorem mem_window {c x : ℝ} (hx : 2 ≤ x) (hcx : 2 ≤ c*x) {p : ℕ} :
    p ∈ window c x ↔ p.Prime ∧ c*x < p ∧ (p : ℝ) ≤ x := by
  constructor
  · intro h
    obtain ⟨upper,lower⟩ := Finset.mem_sdiff.mp (show p ∈ primes (cutoff x) \ primes (cutoff (c*x)) from h)
    obtain ⟨hp,hpx⟩ := (mem_cutoff hx).mp upper
    exact ⟨hp,lt_of_not_ge (fun he => lower ((mem_cutoff hcx).mpr ⟨hp,he⟩)),hpx⟩
  · rintro ⟨hp,hlo,hhi⟩
    exact Finset.mem_sdiff.mpr ⟨(mem_cutoff hx).mpr ⟨hp,hhi⟩,
      fun h => hlo.not_ge ((mem_cutoff hcx).mp h).2⟩

theorem cutoff_mono {x y : ℝ} (h : x ≤ y) : primes (cutoff x) ⊆ primes (cutoff y) := by
  intro p hp
  have hxy := Nat.floor_mono h
  obtain ⟨h₁,h₂⟩ := Nat.mem_primesBelow.mp hp
  apply Nat.mem_primesBelow.mpr
  exact ⟨by unfold cutoff at *; omega,h₂⟩

theorem powerMass_mono (a : ℝ) : Monotone (powerMass a) := by
  intro x y h
  exact sum_le_sum_of_subset_of_nonneg (cutoff_mono h) (fun p _ _ => rpow_nonneg (Nat.cast_nonneg p) _)

theorem windowMass_sub {c x : ℝ} (h : c*x ≤ x) (a : ℝ) :
    windowMass a c x = powerMass a x - powerMass a (c*x) :=
  sum_sdiff_eq_sub (cutoff_mono h)

private theorem compare_power {b a z y : ℝ} (hz : 0 < z) (hy : z ≤ y) (hab : b ≤ a) :
    y^(b-1)*z^(a-b) ≤ y^(a-1) := by
  rw [show a-1=(b-1)+(a-b) by ring, rpow_add (hz.trans_le hy)]
  exact mul_le_mul_of_nonneg_left (rpow_le_rpow hz.le hy (sub_nonneg.mpr hab))
    (rpow_nonneg (hz.le.trans hy) _)

private theorem reference_share {b c : ℝ} (hb : 0 < b) (hb' : b < 1) (hc : 0 < c)
    (hc' : c < 1) : ∀ᶠ x : ℝ in atTop,
      ((1-c^b)/2)*powerMass b x ≤ windowMass b c x := by
  have frac := powerMass_ratio hb hb' hc
  have hi : c^b < 1 := Real.rpow_lt_one hc.le hc' hb
  have ev := frac.eventually_lt_const (show c^b < (1+c^b)/2 by linarith)
  filter_upwards [ev,eventually_ge_atTop (2:ℝ)] with x hh hx
  have bound := (div_lt_iff₀ (powerMass_pos b x)).mp hh
  rw [windowMass_sub (mul_le_of_le_one_left (by linarith only [hx]) hc'.le)]
  linarith only [bound]

/-- At every subcritical exponent a fixed fractional interval next to
the cutoff eventually carries a positive fraction of the entire packet. -/
theorem positive_window_share {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hc' : c < 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop, d*powerMass a x ≤ windowMass a c x := by
  let b := min (a/2) (1/2)
  have hb : 0 < b := lt_min (by linarith only [ha]) (by norm_num)
  have hb' : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hab : b ≤ a := (min_le_left _ _).trans (by linarith only [ha])
  let f := (1-c^b)/2
  have hf : 0 < f := div_pos (sub_pos.mpr (rpow_lt_one hc.le hc' hb)) (by norm_num)
  refine ⟨c^(a-b)*f,mul_pos (rpow_pos_of_pos hc _) hf,?_⟩
  have hcX := _root_.RHTower.tendsto_const_mul_atTop_of_pos hc
  filter_upwards [reference_share hb hb' hc hc',eventually_ge_atTop (2:ℝ),
    hcX.eventually_ge_atTop 2] with x href hx hcx
  have xp : 0 < x := by linarith only [hx]
  have upper : powerMass a x ≤ powerMass b x*x^(a-b) := by
    rw [powerMass,powerMass,sum_mul]
    apply sum_le_sum
    intro p hp
    obtain ⟨hprime,hle⟩ := (mem_cutoff hx).mp hp
    have pp := (Nat.cast_pos.mpr hprime.pos : 0 < (p:ℝ))
    rw [show a-1=(b-1)+(a-b) by ring,rpow_add pp]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow pp.le hle (sub_nonneg.mpr hab))
      (rpow_nonneg pp.le _)
  have lower : windowMass b c x*(c*x)^(a-b) ≤ windowMass a c x := by
    rw [windowMass,windowMass,sum_mul]
    apply sum_le_sum
    intro p hp
    exact compare_power (mul_pos hc xp) ((mem_window hx hcx).mp hp).2.1.le hab
  calc
    c^(a-b)*f*powerMass a x ≤ c^(a-b)*f*(powerMass b x*x^(a-b)) :=
      mul_le_mul_of_nonneg_left upper (mul_nonneg (rpow_nonneg hc.le _) hf.le)
    _ = (f*powerMass b x)*(c*x)^(a-b) := by rw [mul_rpow hc.le xp.le]; ring
    _ ≤ windowMass b c x*(c*x)^(a-b) :=
      mul_le_mul_of_nonneg_right href (rpow_nonneg (mul_nonneg hc.le xp.le) _)
    _ ≤ _ := lower

#print axioms mem_window
#print axioms cutoff_mono
#print axioms powerMass_mono
#print axioms windowMass_sub
#print axioms positive_window_share

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
