import GaloisForLFunctions.BiScaleUncertainty.AffineFourierCorrelation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Complete affine data and divisor-coordinate sign components

The Fourier coefficients of a literal finite divisor signal are its truncated
multiples coordinates. Affine observations recover precisely products on the
divisibility relation. Their exact remaining ambiguity is one sign on each
component of the nonzero divisibility graph. Explicit profiles at the
incomparable modes three and five exhibit this ambiguity at every cutoff.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.AffineSieve
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩


/-- Complex multiples coordinates of a finite divisor weight. -/
def coordinate (N : ℕ) (c : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, if q ∣ d then c d / (d : ℂ) else 0

/-- The actual weighted divisibility response on the factorial residue period. -/
def residueSignal (N : ℕ) (c : ℕ → ℂ) (k : ZMod N.factorial) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, c d * divisorIndicator d k

/-- Reduction to the period preserves the literal integer divisor response. -/
theorem residueSignal_natCast (N : ℕ) (c : ℕ → ℂ) (k : ℕ) :
    residueSignal N c (k : ZMod N.factorial) =
      ∑ d ∈ Finset.Icc 1 N, if d ∣ k then c d else 0 := by
  unfold residueSignal
  apply Finset.sum_congr rfl
  intro d hd
  rw [divisorIndicator_natCast (Nat.dvd_factorial (Finset.mem_Icc.mp hd).1
    (Finset.mem_Icc.mp hd).2)]
  split_ifs <;> simp

/-- A frequency of additive order q reads exactly the q-th multiples coordinate. -/
theorem dft_residueSignal (N : ℕ) (c : ℕ → ℂ) (r : ZMod N.factorial) :
    ZMod.dft (residueSignal N c) r =
      (N.factorial : ℂ) * coordinate N c (addOrderOf r) := by
  rw [ZMod.dft_apply]
  simp only [residueSignal, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, c d * ZMod.dft (divisorIndicator d) r := by
      apply Finset.sum_congr rfl
      intro d _
      rw [ZMod.dft_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [smul_eq_mul]
      ring
    _ = _ := by
      rw [coordinate, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
      have hd0 : (d : ℂ) ≠ 0 := by
        exact_mod_cast (show d ≠ 0 by have := (Finset.mem_Icc.mp hd).1; omega)
      rw [dft_divisorIndicator hdP]
      by_cases hr : addOrderOf r ∣ d
      · rw [if_pos hr, if_pos hr, Nat.cast_div hdP hd0]
        ring
      · rw [if_neg hr, if_neg hr]
        ring

/-- Dilation couples a coordinate to its exact divisor partner q/gcd(q,a). -/
theorem dft_affine_signal (N : ℕ) (c : ℕ → ℂ) (a : ℕ) (r : ZMod N.factorial) :
    ZMod.dft (correlation (residueSignal N c) (a : ZMod N.factorial)) r =
      (N.factorial : ℂ) * coordinate N c (addOrderOf r) *
        coordinate N c (addOrderOf r / Nat.gcd (addOrderOf r) a) := by
  rw [dft_correlation, dft_residueSignal, dft_residueSignal]
  have hr : addOrderOf (-((a : ZMod N.factorial)*r)) =
      addOrderOf r / Nat.gcd (addOrderOf r) a := by
    rw [addOrderOf_neg]
    simpa only [nsmul_eq_mul] using (addOrderOf_nsmul (n := a) r)
  rw [hr]
  have hP : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp

private theorem coordinate_eq_zero_above (N : ℕ) (c : ℕ → ℂ) {q : ℕ} (hq : N < q) :
    coordinate N c q = 0 := by
  unfold coordinate
  apply Finset.sum_eq_zero
  intro d hd
  apply if_neg
  intro hqd
  have hpos : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have := Nat.le_of_dvd hpos hqd
  have := (Finset.mem_Icc.mp hd).2
  omega

private theorem order_frequency {N q : ℕ} (hq : q ∈ Finset.Icc 1 N) :
    addOrderOf ((N.factorial / q : ℕ) : ZMod N.factorial) = q := by
  have hd := Nat.dvd_factorial (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
  rw [ZMod.addOrderOf_coe _ (Nat.factorial_ne_zero N),
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd), Nat.div_div_self hd (Nat.factorial_ne_zero N)]

/-- Equality of all coordinate products at comparable positive divisor modes. -/
def ComparableProducts (N : ℕ) (y z : ℕ → ℂ) : Prop :=
  ∀ q ∈ Finset.Icc 1 N, ∀ d ∈ q.divisors, y q * y d = z q * z d

/-- Equality of every natural dilation and translation observation. -/
def AllDataEqual (N : ℕ) (c e : ℕ → ℂ) : Prop :=
  ∀ a b : ℕ, correlation (residueSignal N c) (a : ZMod N.factorial) b =
    correlation (residueSignal N e) (a : ZMod N.factorial) b

/-- Equality on slopes one through the cutoff and one complete translation period. -/
def FiniteDataEqual (N : ℕ) (c e : ℕ → ℂ) : Prop :=
  ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.range N.factorial,
    correlation (residueSignal N c) (a : ZMod N.factorial) b =
      correlation (residueSignal N e) (a : ZMod N.factorial) b

private theorem comparableProducts_of_finiteData (N : ℕ) (c e : ℕ → ℂ)
    (h : FiniteDataEqual N c e) : ComparableProducts N (coordinate N c) (coordinate N e) := by
  intro q hq d hd
  have hqpos : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
  have hdq := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have ha : q/d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
    ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
      (Nat.div_le_self q d).trans (Finset.mem_Icc.mp hq).2⟩
  have heq : correlation (residueSignal N c) ((q/d : ℕ) : ZMod N.factorial) =
      correlation (residueSignal N e) ((q/d : ℕ) : ZMod N.factorial) := by
    funext b
    simpa only [ZMod.natCast_zmod_val] using h (q/d) ha b.val (Finset.mem_range.mpr b.val_lt)
  have hf := congrFun (congrArg (ZMod.dft (N := N.factorial) (E := ℂ)) heq)
    ((N.factorial/q : ℕ) : ZMod N.factorial)
  rw [dft_affine_signal, dft_affine_signal, order_frequency hq,
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdq), Nat.div_div_self hdq hqpos.ne'] at hf
  have hP : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  exact mul_left_cancel₀ hP (by simpa only [mul_assoc] using hf)

private theorem allData_of_comparableProducts (N : ℕ) (c e : ℕ → ℂ)
    (h : ComparableProducts N (coordinate N c) (coordinate N e)) : AllDataEqual N c e := by
  intro a b
  have heq : correlation (residueSignal N c) (a : ZMod N.factorial) =
      correlation (residueSignal N e) (a : ZMod N.factorial) := by
    apply ZMod.dft.injective
    funext r
    rw [dft_affine_signal, dft_affine_signal]
    by_cases hq : addOrderOf r ≤ N
    · have hpos := addOrderOf_pos r
      have hqd : addOrderOf r / Nat.gcd (addOrderOf r) a ∈ (addOrderOf r).divisors :=
        Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _), hpos.ne'⟩
      have hp := h (addOrderOf r) (Finset.mem_Icc.mpr ⟨hpos, hq⟩) _ hqd
      simpa only [mul_assoc] using congrArg ((N.factorial : ℂ)*·) hp
    · rw [coordinate_eq_zero_above N c (Nat.lt_of_not_ge hq),
        coordinate_eq_zero_above N e (Nat.lt_of_not_ge hq)]
      simp
  exact congrFun heq (b : ZMod N.factorial)

/-- The finite observation family is complete and reads precisely comparable products. -/
theorem allData_iff_finiteData_iff_comparableProducts (N : ℕ) (c e : ℕ → ℂ) :
    (AllDataEqual N c e ↔ FiniteDataEqual N c e) ∧
    (FiniteDataEqual N c e ↔ ComparableProducts N (coordinate N c) (coordinate N e)) := by
  have hfin : AllDataEqual N c e → FiniteDataEqual N c e := fun h a _ b _ => h a b
  have hprod := comparableProducts_of_finiteData N c e
  have hall := allData_of_comparableProducts N c e
  exact ⟨⟨hfin, fun h => hall (hprod h)⟩, ⟨hprod, fun h => hfin (hall h)⟩⟩

/-- A sign is constant across every nonzero divisibility edge, hence each component. -/
def SignComponents (N : ℕ) (y : ℕ → ℂ) (ε : ℕ → Bool) : Prop :=
  ∀ q ∈ Finset.Icc 1 N, ∀ d ∈ q.divisors,
    y q ≠ 0 → y d ≠ 0 → ε q = ε d

private theorem edge_sign {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (p q : Bool)
    (h : u*v = (if p then u else -u) * (if q then v else -v)) : p = q := by
  cases p <;> cases q
  · rfl
  · exfalso
    have hz : (2 : ℂ)*(u*v) = 0 := by
      calc
        _ = u*v - (-u)*v := by ring
        _ = 0 := sub_eq_zero.mpr h
    exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (mul_ne_zero hu hv)) hz
  · exfalso
    have hz : (2 : ℂ)*(u*v) = 0 := by
      calc
        _ = u*v - u*(-v) := by ring
        _ = 0 := sub_eq_zero.mpr h
    exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (mul_ne_zero hu hv)) hz
  · rfl

/-- Comparable products determine exactly the componentwise signs of a profile. -/
theorem comparableProducts_iff_signComponents (N : ℕ) (y z : ℕ → ℂ) :
    ComparableProducts N y z ↔ ∃ ε : ℕ → Bool,
      (∀ q ∈ Finset.Icc 1 N, z q = if ε q then y q else -y q) ∧ SignComponents N y ε := by
  classical
  constructor
  · intro h
    let ε : ℕ → Bool := fun q => if z q = y q then true else false
    have hp (q : ℕ) (hq : q ∈ Finset.Icc 1 N) : z q = if ε q then y q else -y q := by
      have hq0 : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
      have hs := h q hq q (Nat.mem_divisors.mpr ⟨dvd_refl q, hq0⟩)
      have he := mul_self_eq_mul_self_iff.mp hs.symm
      by_cases hz : z q = y q
      · simp [ε, hz]
      · simp [ε, he.resolve_left hz]
    refine ⟨ε, hp, ?_⟩
    intro q hq d hd hyq hyd
    have hdN : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hq).1; omega)
          (Nat.dvd_of_mem_divisors hd)).trans (Finset.mem_Icc.mp hq).2⟩
    have he := h q hq d hd
    rw [hp q hq, hp d hdN] at he
    exact edge_sign hyq hyd _ _ he
  · rintro ⟨ε, hp, hc⟩ q hq d hd
    have hdN : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (by have := (Finset.mem_Icc.mp hq).1; omega)
          (Nat.dvd_of_mem_divisors hd)).trans (Finset.mem_Icc.mp hq).2⟩
    rw [hp q hq, hp d hdN]
    by_cases hyq : y q = 0
    · simp [hyq]
    by_cases hyd : y d = 0
    · simp [hyd]
    rw [hc q hq d hd hyq hyd]
    cases hε : ε d <;> simp

/-- Exact phase classification for the full affine observation family. -/
theorem allData_iff_signComponents (N : ℕ) (c e : ℕ → ℂ) :
    AllDataEqual N c e ↔ ∃ ε : ℕ → Bool,
      (∀ q ∈ Finset.Icc 1 N,
        coordinate N e q = if ε q then coordinate N c q else -coordinate N c q) ∧
      SignComponents N (coordinate N c) ε := by
  rw [(allData_iff_finiteData_iff_comparableProducts N c e).1,
    (allData_iff_finiteData_iff_comparableProducts N c e).2,
    comparableProducts_iff_signComponents]

private def pointWeight (t : ℕ) (w : ℂ) (d : ℕ) : ℂ := if d = t then w else 0

private theorem coordinate_pointWeight (N t : ℕ) (ht : t ∈ Finset.Icc 1 N) (w : ℂ) (q : ℕ) :
    coordinate N (pointWeight t w) q = if q ∣ t then w / (t : ℂ) else 0 := by
  unfold coordinate pointWeight
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, if d = t then (if q ∣ t then w/(t : ℂ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = t
      · subst d; simp
      · simp [hd]
    _ = _ := by simp [ht]

private theorem coordinate_add (N : ℕ) (c e : ℕ → ℂ) (q : ℕ) :
    coordinate N (c+e) q = coordinate N c q + coordinate N e q := by
  unfold coordinate
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : q ∣ d <;> simp [hd, add_div]

/-- An explicit finite weight with independent coordinates at modes three and five. -/
def primePairWeight (t : ℂ) : ℕ → ℂ :=
  pointWeight 1 (-(1+t)) + pointWeight 3 3 + pointWeight 5 (5*t)

/-- The displayed weight realizes its two-mode profile at every sufficient cutoff. -/
theorem coordinate_primePairWeight (N : ℕ) (t : ℂ) (q : ℕ) :
    coordinate (N+5) (primePairWeight t) q = if q = 3 then 1 else if q = 5 then t else 0 := by
  rw [primePairWeight, coordinate_add, coordinate_add,
    coordinate_pointWeight _ 1 (by simp), coordinate_pointWeight _ 3 (by simp),
    coordinate_pointWeight _ 5 (by simp)]
  have hp3 : Nat.Prime 3 := by decide
  have hp5 : Nat.Prime 5 := by decide
  by_cases hq1 : q = 1
  · subst q; norm_num
  by_cases hq3 : q = 3
  · subst q; norm_num
  by_cases hq5 : q = 5
  · subst q; norm_num
  simp [Nat.dvd_one, Nat.dvd_prime hp3, Nat.dvd_prime hp5, hq1, hq3, hq5]

/-- Flipping only the mode-five sign preserves every affine quadratic observation. -/
theorem primePairWeight_allDataEqual (N : ℕ) :
    AllDataEqual (N+5) (primePairWeight 1) (primePairWeight (-1)) := by
  apply allData_of_comparableProducts
  intro q _ d hd
  simp only [coordinate_primePairWeight]
  by_cases hq3 : q = 3
  · subst q
    have hd' := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (Nat.dvd_of_mem_divisors hd)
    rcases hd' with rfl | rfl <;> norm_num
  by_cases hq5 : q = 5
  · subst q
    have hd' := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (Nat.dvd_of_mem_divisors hd)
    rcases hd' with rfl | rfl <;> norm_num
  simp [hq3, hq5]

/-- The two signs change the actual coefficient at the trivial divisor. -/
theorem primePairWeight_one (t : ℂ) : primePairWeight t 1 = -(1+t) := by
  simp [primePairWeight, pointWeight]

private theorem residueSignal_pointWeight (N t : ℕ) (ht : t ∈ Finset.Icc 1 N)
    (w : ℂ) (k : ℕ) :
    residueSignal N (pointWeight t w) (k : ZMod N.factorial) = if t ∣ k then w else 0 := by
  rw [residueSignal_natCast]
  unfold pointWeight
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, if d = t then (if t ∣ k then w else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d = t
      · subst d; simp
      · simp [hd]
    _ = _ := by simp [ht]

private theorem residueSignal_add (N : ℕ) (c e : ℕ → ℂ) (k : ZMod N.factorial) :
    residueSignal N (c+e) k = residueSignal N c k + residueSignal N e k := by
  simp only [residueSignal, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Literal pointwise values of the explicit indistinguishable weight family. -/
theorem residueSignal_primePairWeight (N : ℕ) (t : ℂ) (k : ℕ) :
    residueSignal (N+5) (primePairWeight t) (k : ZMod (N+5).factorial) =
      -(1+t) + (if 3 ∣ k then 3 else 0) + (if 5 ∣ k then 5*t else 0) := by
  rw [primePairWeight, residueSignal_add, residueSignal_add,
    residueSignal_pointWeight _ 1 (by simp), residueSignal_pointWeight _ 3 (by simp),
    residueSignal_pointWeight _ 5 (by simp)]
  simp

end GaloisForLFunctions.BiScaleUncertainty.AffineSieve
