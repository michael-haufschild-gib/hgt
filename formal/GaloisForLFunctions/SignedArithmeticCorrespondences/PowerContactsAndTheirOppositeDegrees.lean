import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.PoleMomentsFromSeparatedGraphContacts

/-!
# Contacts on the power graphs

Restrict the directed intersection to contacts whose ratio is a perfect d-th power.
Taking its d-th root rescales both profiles and tilts them in opposite directions.
The resulting identity determines the exact separation exponent and both limiting degrees.
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open _root_.RHTower

namespace GaloisForLFunctions.SignedArithmeticCorrespondences

/-- Directed intersection of two profiles separated by the logarithmic displacement s. -/
def contact (w : ℕ → ℝ) (f g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * w n / Real.sqrt n) * ∫ u : ℝ, f u * g (u + (Real.log n - s))

theorem contact_eq_smoothPrimePair (f g : ℝ → ℝ) (s : ℝ) :
    contact (fun n => Λ n) f g s = LogCells.smoothPrimePair f (fun v => g (v - s)) := by
  simp only [contact, LogCells.smoothPrimePair, add_sub_assoc]

open Classical in
/-- A prime-power contact survives exactly when its conductor ratio is a d-th power. -/
def powerWeight (d n : ℕ) : ℝ := if ∃ m : ℕ, m ^ d = n then Λ n else 0

/-- Pull a graph profile back along multiplication by d in log coordinates, with tilt a. -/
def pullProfile (d a : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := f (d * u) * Real.exp (a * u)

private theorem integral_scale {d : ℝ} (hd : 0 < d) (f : ℝ → ℝ) :
    (∫ u : ℝ, f (d*u)) = d⁻¹ * ∫ u : ℝ, f u := by
  simpa only [abs_of_pos (inv_pos.mpr hd), smul_eq_mul] using Measure.integral_comp_mul_left f d

private theorem pull_lag {d : ℝ} (hd : 0 < d) (a : ℝ) (f g : ℝ → ℝ) (z : ℝ) :
    (∫ u : ℝ, pullProfile d a f u * pullProfile d (-a) g (u+z)) =
      (Real.exp (-a*z) * d⁻¹) * ∫ u : ℝ, f u * g (u+d*z) := by
  have h (u : ℝ) : pullProfile d a f u * pullProfile d (-a) g (u+z) =
      Real.exp (-a*z) * (f (d*u) * g (d*u+d*z)) := by
    unfold pullProfile
    rw [mul_add, mul_mul_mul_comm, ← Real.exp_add]
    rw [show a*u + -a*(u+z) = -a*z by ring, mul_comm]
  simp only [h, integral_const_mul]
  rw [integral_scale hd (fun u => f u * g (u+d*z)), mul_assoc]

private theorem pull_moment {d : ℝ} (hd : 0 < d) (a b : ℝ) (f : ℝ → ℝ) :
    ccmRealExponentialMoment b (pullProfile d a f) =
      d⁻¹ * ccmRealExponentialMoment ((a+b)/d) f := by
  have h (u : ℝ) : ccmRealExponentialTilt b (pullProfile d a f) u =
      ccmRealExponentialTilt ((a+b)/d) f (d*u) := by
    simp only [ccmRealExponentialTilt, pullProfile, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simpa only [ccmRealExponentialMoment, h] using
    integral_scale hd (ccmRealExponentialTilt ((a+b)/d) f)

private theorem sqrt_nat_exp {n : ℕ} (hn : n ≠ 0) :
    Real.sqrt n = Real.exp (Real.log n / 2) := by
  rw [Real.exp_half, Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]

/-- Exact descent from a perfect-power contact to a full von Mangoldt contact.
The opposite tilts absorb the change in the square-root metric. -/
theorem power_contact_descent (d : ℕ+) (f g : ℝ → ℝ) (s : ℝ) :
    let r : ℝ := (d : ℕ)
    let a := (r-1)/2
    contact (powerWeight d) f g (r*s) =
      r * Real.exp (-a*s) * contact (fun n => Λ n) (pullProfile r a f) (pullProfile r (-a) g) s := by
  classical
  dsimp only
  let r : ℝ := (d : ℕ)
  let a := (r-1)/2
  have hr : 0 < r := Nat.cast_pos.mpr d.pos
  let term (n : ℕ) := (2 * powerWeight d n / Real.sqrt n) *
    ∫ u : ℝ, f u * g (u + (Real.log n - r*s))
  have hinj : Function.Injective (fun k : ℕ => k ^ (d : ℕ)) :=
    fun i j h => (pow_left_inj₀ (Nat.zero_le i) (Nat.zero_le j) d.pos.ne').mp h
  have hre : (∑' k : ℕ, term (k ^ (d : ℕ))) = ∑' n : ℕ, term n := by
    apply hinj.tsum_eq
    intro n hn
    by_contra hout
    exact hn (by simp [term, powerWeight, show ¬ ∃ k : ℕ, k ^ (d : ℕ) = n from hout])
  change (∑' n : ℕ, term n) = r * Real.exp (-a*s) * _
  rw [← hre, contact, ← tsum_mul_left]
  apply tsum_congr
  intro k
  have hw : powerWeight d (k ^ (d : ℕ)) = Λ k := by
    rw [powerWeight, if_pos ⟨k,rfl⟩, ArithmeticFunction.vonMangoldt_apply_pow d.pos.ne']
  dsimp only [term]
  rw [hw, pull_lag hr]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hp : k ^ (d : ℕ) ≠ 0 := pow_ne_zero _ hk
  rw [sqrt_nat_exp hp, sqrt_nat_exp hk, Nat.cast_pow, Real.log_pow]
  change 2 * Λ k / Real.exp (r * Real.log k / 2) * _ = _
  rw [← mul_sub]
  have he : Real.exp (-a*s) * Real.exp (-a*(Real.log k - s)) /
      Real.exp (Real.log k/2) = (Real.exp (r*Real.log k/2))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_neg]
    congr 1
    dsimp only [a]
    ring
  simp only [div_eq_mul_inv] at he ⊢
  rw [← he]
  field_simp [hr.ne']
  <;> ring

private theorem pull_compact {d : ℝ} (hd : 0 < d) (a : ℝ) {f : ℝ → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (pullProfile d a f) :=
  (hf.comp_homeomorph (Homeomorph.mulLeft₀ d hd.ne')).mul_right

private theorem pull_smooth (d a : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (pullProfile d a f) :=
  (hf.comp (contDiff_const.mul contDiff_id)).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

/-- The d-th power contacts at separation t have size exp((1/d−1/2)t).
Their normalized limit factors through moments at the two opposite degrees. -/
theorem tendsto_power_contact (d : ℕ+) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    let r : ℝ := (d : ℕ)
    let b := 1/r - 1/2
    Tendsto (fun t : ℝ => Real.exp (-b*t) * contact (powerWeight d) f g t) atTop
      (𝓝 ((2/r) * ccmRealExponentialMoment (-b) f * ccmRealExponentialMoment b g)) := by
  dsimp only
  let r : ℝ := (d : ℕ)
  let a := (r-1)/2
  let b := 1/r-1/2
  have hr : 0 < r := Nat.cast_pos.mpr d.pos
  have h := (tendsto_separated_graph_pair (pull_smooth r a hf) (pull_smooth r (-a) hg)
    (pull_compact hr a hfc) (pull_compact hr (-a) hgc)).2
  have ht : Tendsto (fun t : ℝ => Real.exp (t / r)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const hr)
  have hlim := (h.comp ht).const_mul r
  rw [pull_moment hr, pull_moment hr] at hlim
  have h1 : (-a + 1/2)/r = b := by dsimp [a,b]; field_simp; ring
  have h2 : (a + -(1/2))/r = -b := by dsimp [a,b]; field_simp; ring
  rw [h1,h2] at hlim
  change Tendsto _ _ (𝓝 ((2/r) * ccmRealExponentialMoment (-b) f * ccmRealExponentialMoment b g))
  convert hlim using 1
  · funext t
    simp only [Function.comp_apply, Real.log_exp, ← contact_eq_smoothPrimePair, ← Real.exp_half]
    have hr' : r*(t/r) = t := by field_simp
    have he := power_contact_descent d f g (t/r)
    change contact (powerWeight d) f g (r*(t/r)) =
      r * Real.exp (-a*(t/r)) * _ at he
    rw [hr'] at he
    rw [he]
    change Real.exp (-b*t) * (r * Real.exp (-a*(t/r)) * _) = _
    have hex : Real.exp (-b*t) * Real.exp (-a*(t/r)) = (Real.exp (t/r/2))⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]
      congr 1
      dsimp [a,b]
      field_simp
      ring
    rw [div_eq_mul_inv _ (Real.exp _), ← hex]
    ring
  · congr 1
    field_simp
    ring

#print axioms power_contact_descent
#print axioms tendsto_power_contact

end GaloisForLFunctions.SignedArithmeticCorrespondences
