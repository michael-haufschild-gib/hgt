import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import GaloisForLFunctions.BiScaleUncertainty.DivisorSieveAffineSpectrum
import GaloisForLFunctions.RHTower.Sieve.PeriodicDFTSupport
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Gcd transport, additive orbit projection and exact sieve periods

Translation-orbit averaging sends normalized divisor mass at `d` to `gcd(d,h)`.
This explicit coefficient transport is the Selberg-orthogonal projection onto
signals fixed by the additive stride `h`. Its composition law is the gcd law.
The exact additive periods are the multiples of the lcm of active raw divisors:
signed cancellation does not create a shorter period.

The Fourier transform is used only on the internal factorial cycle of the actual
signal. No external averaging family or asymptotic cancellation is assumed.
-/

open Finset GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-- Push normalized coefficient mass along `d ↦ gcd(d,h)`, with zero extension. -/
def sieveGcdProjection (N h : ℕ) (c : ℕ → ℝ) (e : ℕ) : ℝ :=
  if e ∈ Finset.Icc 1 N then
    (e : ℝ) * ∑ d ∈ Finset.Icc 1 N, if Nat.gcd d h = e then c d / (d : ℝ) else 0
  else 0

private theorem gcd_projection_outside (N h : ℕ) (c : ℕ → ℝ) (e : ℕ)
    (he : e ∉ Finset.Icc 1 N) : sieveGcdProjection N h c e = 0 := by
  simp only [sieveGcdProjection, if_neg he]

private theorem gcd_projection_support (N h : ℕ) (c : ℕ → ℝ) (e : ℕ)
    (he : ¬ e ∣ h) : sieveGcdProjection N h c e = 0 := by
  unfold sieveGcdProjection
  split_ifs
  · have hz : (∑ d ∈ Finset.Icc 1 N,
        if Nat.gcd d h = e then c d / (d : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d _
      have hne : Nat.gcd d h ≠ e := by
        intro hd
        apply he
        rw [← hd]
        exact Nat.gcd_dvd_right d h
      exact if_neg hne
    rw [hz, mul_zero]
  · rfl

/-- Exact transport identity against every real test function on the divisor labels. -/
theorem sieveGcdProjection_transport (N h : ℕ) (c F : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 1 N, sieveGcdProjection N h c e / (e : ℝ) * F e) =
      ∑ d ∈ Finset.Icc 1 N, c d / (d : ℝ) * F (Nat.gcd d h) := by
  classical
  calc
    _ = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
        if Nat.gcd d h = e then c d / (d : ℝ) * F e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      have he0 : (e : ℝ) ≠ 0 := by
        exact_mod_cast (by have := (Finset.mem_Icc.mp he).1; omega : e ≠ 0)
      rw [sieveGcdProjection, if_pos he, mul_div_cancel_left₀ _ he0, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hg : Nat.gcd d h ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
        ⟨Nat.gcd_pos_of_pos_left h hdpos,
          (Nat.gcd_le_left h hdpos).trans (Finset.mem_Icc.mp hd).2⟩
      rw [Finset.sum_eq_single (Nat.gcd d h)]
      · simp
      · intro e _ he
        exact if_neg (Ne.symm he)
      · intro hn
        exact False.elim (hn hg)

/-- Gcd transport retains precisely the multiples coordinates resonant with the stride. -/
theorem selbergMultiplesCoord_gcdProjection (N h q : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (sieveGcdProjection N h c) q =
      if q ∣ h then selbergMultiplesCoord N c q else 0 := by
  have hleft : selbergMultiplesCoord N (sieveGcdProjection N h c) q =
      ∑ e ∈ Finset.Icc 1 N, sieveGcdProjection N h c e / (e : ℝ) *
        (if q ∣ e then 1 else 0) := by
    rw [selbergMultiplesCoord, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  rw [hleft, sieveGcdProjection_transport]
  by_cases hh : q ∣ h
  · rw [if_pos hh, selbergMultiplesCoord, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : q ∣ d <;> simp [Nat.dvd_gcd_iff, hh, hd]
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro d _
    simp [Nat.dvd_gcd_iff, hh]

/-- Every orbit projection preserves the exact harmonic mean, including the empty level. -/
theorem finiteHarmonicSum_gcdProjection (N h : ℕ) (c : ℕ → ℝ) :
    finiteHarmonicSum N (sieveGcdProjection N h c) = finiteHarmonicSum N c := by
  simpa [selbergMultiplesCoord, finiteHarmonicSum] using
    selbergMultiplesCoord_gcdProjection N h 1 c

private theorem gcd_coefficients_eq (N : ℕ) (c b : ℕ → ℝ)
    (hy : ∀ q ∈ Finset.Icc 1 N, selbergMultiplesCoord N c q = selbergMultiplesCoord N b q) :
    ∀ d ∈ Finset.Icc 1 N, c d = b d := by
  have hz := (selbergMultiplesCoord_tail_zero_iff N 0 (fun d => c d - b d)).mp
    (fun q hq => by rw [selbergMultiplesCoord_sub, hy q hq, sub_self])
  intro d hd
  exact sub_eq_zero.mp (hz d hd)

/-- Composing two additive orbit projections is projection onto their gcd stride. -/
theorem sieveGcdProjection_comp (N h k : ℕ) (c : ℕ → ℝ) :
    sieveGcdProjection N h (sieveGcdProjection N k c) =
      sieveGcdProjection N (Nat.gcd h k) c := by
  have heq := gcd_coefficients_eq N
    (sieveGcdProjection N h (sieveGcdProjection N k c))
    (sieveGcdProjection N (Nat.gcd h k) c) (fun q _ => by
      rw [selbergMultiplesCoord_gcdProjection, selbergMultiplesCoord_gcdProjection,
        selbergMultiplesCoord_gcdProjection]
      by_cases hh : q ∣ h <;> by_cases hk : q ∣ k <;> simp [Nat.dvd_gcd_iff, hh, hk])
  funext d
  by_cases hd : d ∈ Finset.Icc 1 N
  · exact heq d hd
  · rw [gcd_projection_outside N h _ d hd, gcd_projection_outside N _ c d hd]

/-- Every arithmetic orbit projection is idempotent as a complete weight function. -/
theorem sieveGcdProjection_idempotent (N h : ℕ) (c : ℕ → ℝ) :
    sieveGcdProjection N h (sieveGcdProjection N h c) = sieveGcdProjection N h c := by
  rw [sieveGcdProjection_comp, Nat.gcd_self]

/-- Zero stride keeps exactly the coefficients inside the finite level. -/
theorem sieveGcdProjection_zero_stride (N : ℕ) (c : ℕ → ℝ) (d : ℕ) :
    sieveGcdProjection N 0 c d = if d ∈ Finset.Icc 1 N then c d else 0 := by
  by_cases hd : d ∈ Finset.Icc 1 N
  · have hd0 : (d : ℝ) ≠ 0 := by
      exact_mod_cast (by have := (Finset.mem_Icc.mp hd).1; omega : d ≠ 0)
    simp [sieveGcdProjection, hd, Nat.gcd_zero_right]
    field_simp
  · simp [sieveGcdProjection, hd]

/-- Unit stride retains only the constant harmonic mode. -/
theorem sieveGcdProjection_one_stride (N : ℕ) (c : ℕ → ℝ) (d : ℕ) :
    sieveGcdProjection N 1 c d = if d = 1 then finiteHarmonicSum N c else 0 := by
  cases N with
  | zero => simp [sieveGcdProjection, finiteHarmonicSum]
  | succ N =>
    by_cases hd : d = 1
    · subst d
      simp [sieveGcdProjection, finiteHarmonicSum]
    · simp [sieveGcdProjection, hd, Ne.symm hd]

private theorem gcd_periodic_of_support (N h : ℕ) (c : ℕ → ℝ)
    (hc : ∀ d ∈ Finset.Icc 1 N, c d ≠ 0 → d ∣ h) :
    Function.Periodic (sieveSeq N c) h := by
  intro k
  simp only [sieveSeq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hz : c d = 0
  · simp [hz]
  · have hdh := hc d hd hz
    simp only [← Nat.dvd_add_iff_left hdh]

/-- The transported weight always gives a literal signal fixed by the stride. -/
theorem sieveGcdProjection_periodic (N h : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (sieveSeq N (sieveGcdProjection N h c)) h := by
  apply gcd_periodic_of_support
  intro d _ hd
  by_contra hnot
  exact hd (gcd_projection_support N h c d hnot)

private theorem gcd_complex_coordinate (N q : ℕ) (c : ℕ → ℝ) :
    AffineSieve.coordinate N (fun d => (c d : ℂ)) q =
      (selbergMultiplesCoord N c q : ℂ) := by
  rw [AffineSieve.coordinate, selbergMultiplesCoord, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

private theorem gcd_complex_signal (N k : ℕ) (c : ℕ → ℝ) :
    AffineSieve.residueSignal N (fun d => (c d : ℂ)) (k : ZMod N.factorial) =
      (sieveSeq N c k : ℂ) := by
  rw [AffineSieve.residueSignal_natCast, sieveSeq, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

private theorem gcd_signal_dft (N : ℕ) (c : ℕ → ℝ) (r : ZMod N.factorial) :
    ZMod.dft (AffineSieve.residueSignal N (fun d => (c d : ℂ))) r =
      (N.factorial : ℂ) * (selbergMultiplesCoord N c (addOrderOf r) : ℂ) := by
  rw [AffineSieve.dft_residueSignal, gcd_complex_coordinate]

private theorem gcd_frequency_order (N q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
    addOrderOf ((N.factorial / q : ℕ) : ZMod N.factorial) = q := by
  have hd := Nat.dvd_factorial (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
  rw [ZMod.addOrderOf_coe _ (Nat.factorial_ne_zero N),
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd), Nat.div_div_self hd (Nat.factorial_ne_zero N)]

private theorem gcd_periodic_coordinates (N h : ℕ) (c : ℕ → ℝ)
    (hc : Function.Periodic (sieveSeq N c) h) (q : ℕ) (hq : q ∈ Finset.Icc 1 N)
    (hqh : ¬ q ∣ h) : selbergMultiplesCoord N c q = 0 := by
  let f := AffineSieve.residueSignal N (fun d => (c d : ℂ))
  have hp : ∀ x : ZMod N.factorial, f (x + (h : ZMod N.factorial)) = f x := by
    intro x
    calc
      _ = f ((x.val + h : ℕ) : ZMod N.factorial) := by congr 1; simp
      _ = (sieveSeq N c (x.val + h) : ℂ) := gcd_complex_signal N _ c
      _ = (sieveSeq N c x.val : ℂ) := by rw [hc]
      _ = f x := by simpa only [ZMod.natCast_zmod_val] using (gcd_complex_signal N x.val c).symm
  let r : ZMod N.factorial := ((N.factorial / q : ℕ) : ZMod N.factorial)
  have horder : addOrderOf r = q := gcd_frequency_order N q hq
  have hhr : (h : ZMod N.factorial) * r ≠ 0 := by
    intro hz
    have hh : addOrderOf r ∣ h := addOrderOf_dvd_iff_nsmul_eq_zero.mpr
      (by simpa only [nsmul_eq_mul] using hz)
    exact hqh (horder ▸ hh)
  have hphase : ZMod.stdAddChar (-((h : ZMod N.factorial) * r)) ≠ 1 := by
    intro hz
    have hz' : -((h : ZMod N.factorial) * r) = 0 :=
      ZMod.injective_stdAddChar (by simpa using hz)
    exact hhr (by simpa using hz')
  have hz := dft_eq_zero_of_periodic_nontrivial_phase f (h : ZMod N.factorial) r hp hphase
  change ZMod.dft (AffineSieve.residueSignal N (fun d => (c d : ℂ))) r = 0 at hz
  rw [gcd_signal_dft, horder] at hz
  have hP : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hy := (mul_eq_zero.mp hz).resolve_left hP
  exact Complex.ofReal_injective (by simpa using hy)

/-- Complete additive stabilizer: every active raw divisor must divide the period. -/
theorem sieveSeq_periodic_iff_active_divisors (N h : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (sieveSeq N c) h ↔
      ∀ d ∈ Finset.Icc 1 N, c d ≠ 0 → d ∣ h := by
  constructor
  · intro hp
    have heq := gcd_coefficients_eq N c (sieveGcdProjection N h c) (fun q hq => by
      rw [selbergMultiplesCoord_gcdProjection]
      by_cases hh : q ∣ h
      · simp [hh]
      · rw [if_neg hh, gcd_periodic_coordinates N h c hp q hq hh])
    intro d hd hc
    by_contra hnot
    exact hc ((heq d hd).trans (gcd_projection_support N h c d hnot))
  · exact gcd_periodic_of_support N h c

/-- The exact positive generator of the additive period set. -/
def sieveLeastPeriod (N : ℕ) (c : ℕ → ℝ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun d => c d ≠ 0)).lcm id

/-- All periods, including zero, are precisely the multiples of the active-divisor lcm. -/
theorem sieveSeq_periodic_iff_leastPeriod_dvd (N h : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (sieveSeq N c) h ↔ sieveLeastPeriod N c ∣ h := by
  rw [sieveSeq_periodic_iff_active_divisors, sieveLeastPeriod, Finset.lcm_dvd_iff]
  simp only [Finset.mem_filter, id_eq, and_imp]

/-- The period generator is positive even for empty support and is the least positive period. -/
theorem sieveLeastPeriod_isLeast (N : ℕ) (c : ℕ → ℝ) :
    IsLeast {h : ℕ | 0 < h ∧ Function.Periodic (sieveSeq N c) h} (sieveLeastPeriod N c) := by
  have hne : sieveLeastPeriod N c ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro d hd
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    change d ≠ 0
    omega
  refine ⟨⟨by omega, (sieveSeq_periodic_iff_leastPeriod_dvd N _ c).mpr (dvd_refl _)⟩, ?_⟩
  intro h hh
  exact Nat.le_of_dvd hh.1 ((sieveSeq_periodic_iff_leastPeriod_dvd N h c).mp hh.2)


/-- A weight is fixed inside its level exactly when its signal is stride-periodic. -/
theorem sieveGcdProjection_eq_zero_stride_iff (N h : ℕ) (c : ℕ → ℝ) :
    sieveGcdProjection N h c = sieveGcdProjection N 0 c ↔
      Function.Periodic (sieveSeq N c) h := by
  constructor
  · intro heq
    apply (sieveSeq_periodic_iff_active_divisors N h c).mpr
    intro d hd hc
    by_contra hn
    have hh := congrFun heq d
    rw [gcd_projection_support N h c d hn, sieveGcdProjection_zero_stride,
      if_pos hd] at hh
    exact hc hh.symm
  · intro hp
    have heq := gcd_coefficients_eq N (sieveGcdProjection N h c)
      (sieveGcdProjection N 0 c) (fun q hq => by
        simp only [selbergMultiplesCoord_gcdProjection, dvd_zero, if_true]
        by_cases hh : q ∣ h
        · simp [hh]
        · rw [if_neg hh, gcd_periodic_coordinates N h c hp q hq hh])
    funext d
    by_cases hd : d ∈ Finset.Icc 1 N
    · exact heq d hd
    · rw [gcd_projection_outside N h c d hd, gcd_projection_outside N 0 c d hd]

private def gcd_cycleAverage {P : ℕ} [NeZero P]
    (h : ZMod P) (f : ZMod P → ℂ) (x : ZMod P) : ℂ :=
  (P : ℂ)⁻¹ * ∑ j : ZMod P, f (x + j * h)

private theorem gcd_cycleAverage_periodic {P : ℕ} [NeZero P]
    (h : ZMod P) (f : ZMod P → ℂ) (x : ZMod P) :
    gcd_cycleAverage h f (x + h) = gcd_cycleAverage h f x := by
  unfold gcd_cycleAverage
  congr 1
  refine Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun j => ?_)
  change f (x + h + j * h) = f (x + (j + 1) * h)
  congr 1
  ring

private theorem gcd_cycleAverage_dft_resonant {P : ℕ} [NeZero P]
    (h r : ZMod P) (f : ZMod P → ℂ) (hr : h * r = 0) :
    ZMod.dft (gcd_cycleAverage h f) r = ZMod.dft f r := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, gcd_cycleAverage]
  calc
    _ = (P : ℂ)⁻¹ * ∑ x : ZMod P, ∑ j : ZMod P,
        ZMod.stdAddChar (-(x * r)) * f (x + j * h) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (P : ℂ)⁻¹ * ∑ j : ZMod P, ∑ x : ZMod P,
        ZMod.stdAddChar (-(x * r)) * f (x + j * h) := by rw [Finset.sum_comm]
    _ = (P : ℂ)⁻¹ * ∑ _j : ZMod P, ZMod.dft f r := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ZMod.dft_apply]
      simp only [smul_eq_mul]
      refine Fintype.sum_equiv (Equiv.addRight (j * h)) _ _ (fun x => ?_)
      change ZMod.stdAddChar (-(x * r)) * f (x + j * h) =
        ZMod.stdAddChar (-((x + j * h) * r)) * f (x + j * h)
      simp only [add_mul, mul_assoc, hr, mul_zero, add_zero]
    _ = ZMod.dft f r := by
      have hP : (P : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne P)
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hP, one_mul]

private theorem gcd_cycleAverage_dft {P : ℕ} [NeZero P]
    (h r : ZMod P) (f : ZMod P → ℂ) :
    ZMod.dft (gcd_cycleAverage h f) r = if h * r = 0 then ZMod.dft f r else 0 := by
  by_cases hr : h * r = 0
  · rw [if_pos hr]
    exact gcd_cycleAverage_dft_resonant h r f hr
  · rw [if_neg hr]
    apply dft_eq_zero_of_periodic_nontrivial_phase _ h r (gcd_cycleAverage_periodic h f)
    intro hz
    have hz' : -(h * r) = 0 := ZMod.injective_stdAddChar (by simpa using hz)
    exact hr (by simpa using hz')

/-- The gcd coefficient transport is the literal average along the actual additive orbit. -/
theorem sieveSeq_gcdProjection_eq_orbitAverage (N h k : ℕ) (c : ℕ → ℝ) :
    sieveSeq N (sieveGcdProjection N h c) k =
      (∑ j ∈ Finset.range N.factorial, sieveSeq N c (k + j * h)) / (N.factorial : ℝ) := by
  let f := AffineSieve.residueSignal N (fun d => (c d : ℂ))
  have heq : AffineSieve.residueSignal N (fun d => (sieveGcdProjection N h c d : ℂ)) =
      gcd_cycleAverage (h : ZMod N.factorial) f := by
    apply ZMod.dft.injective
    funext r
    have hres : (h : ZMod N.factorial) * r = 0 ↔ addOrderOf r ∣ h := by
      rw [addOrderOf_dvd_iff_nsmul_eq_zero]
      simp only [nsmul_eq_mul]
    change ZMod.dft (AffineSieve.residueSignal N
      (fun d => (sieveGcdProjection N h c d : ℂ))) r =
        ZMod.dft (gcd_cycleAverage (h : ZMod N.factorial) f) r
    rw [gcd_signal_dft, gcd_cycleAverage_dft]
    change (N.factorial : ℂ) * (selbergMultiplesCoord N (sieveGcdProjection N h c)
      (addOrderOf r) : ℂ) = if (h : ZMod N.factorial) * r = 0 then
        ZMod.dft (AffineSieve.residueSignal N (fun d => (c d : ℂ))) r else 0
    rw [gcd_signal_dft, selbergMultiplesCoord_gcdProjection]
    by_cases hh : addOrderOf r ∣ h
    · simp [hh, hres.mpr hh]
    · have hn : (h : ZMod N.factorial) * r ≠ 0 := fun hz => hh (hres.mp hz)
      simp [hh, hn]
  have hsum : (∑ j : ZMod N.factorial, f ((k : ZMod N.factorial) + j * h)) =
      ∑ j ∈ Finset.range N.factorial, (sieveSeq N c (k + j * h) : ℂ) := by
    calc
      _ = ∑ j : ZMod N.factorial, (sieveSeq N c (k + j.val * h) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        calc
          _ = f ((k + j.val * h : ℕ) : ZMod N.factorial) := by congr 1; simp
          _ = _ := gcd_complex_signal N _ c
      _ = _ := AffineSieve.sum_zmod_val (fun j => (sieveSeq N c (k + j * h) : ℂ))
  apply Complex.ofReal_injective
  push_cast
  rw [← gcd_complex_signal, heq]
  change (N.factorial : ℂ)⁻¹ * (∑ j : ZMod N.factorial,
    f ((k : ZMod N.factorial) + j * h)) = _
  rw [hsum]
  ring

private theorem gcd_selberg_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c = 0 ↔ ∀ d ∈ Finset.Icc 1 N, c d = 0 := by
  have hphi : ∀ q ∈ Finset.Icc 1 N, 0 < (Nat.totient q : ℝ) := by
    intro q hq
    exact_mod_cast (Nat.totient_pos.mpr (Finset.mem_Icc.mp hq).1)
  unfold selbergTotientDiagonalForm
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun q hq => mul_nonneg (hphi q hq).le (sq_nonneg _))]
  constructor
  · intro hz
    apply (selbergMultiplesCoord_tail_zero_iff N 0 c).mp
    intro q hq
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (hz q hq)).resolve_left (hphi q hq).ne')
  · intro hc q hq
    have hy := (selbergMultiplesCoord_tail_zero_iff N 0 c).mpr hc q hq
    rw [hy, zero_pow (by omega), mul_zero]

/-- Exact Pythagoras for approximation by every arithmetic orbit projection. -/
theorem sieveGcdProjection_pythagoras (N h : ℕ) (c b : ℕ → ℝ) :
    selbergTotientDiagonalForm N (fun d => c d - sieveGcdProjection N h b d) =
      selbergTotientDiagonalForm N (fun d => c d - sieveGcdProjection N h c d) +
      selbergTotientDiagonalForm N
        (fun d => sieveGcdProjection N h c d - sieveGcdProjection N h b d) := by
  unfold selbergTotientDiagonalForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [selbergMultiplesCoord_sub, selbergMultiplesCoord_gcdProjection]
  by_cases hh : q ∣ h <;> simp [hh]

/-- Unique Selberg best approximation among all stride-periodic projected weights. -/
theorem sieveGcdProjection_bestApproximation (N h : ℕ) (c b : ℕ → ℝ) :
    selbergTotientDiagonalForm N (fun d => c d - sieveGcdProjection N h c d) ≤
      selbergTotientDiagonalForm N (fun d => c d - sieveGcdProjection N h b d) ∧
    (selbergTotientDiagonalForm N (fun d => c d - sieveGcdProjection N h c d) =
      selbergTotientDiagonalForm N (fun d => c d - sieveGcdProjection N h b d) ↔
        sieveGcdProjection N h c = sieveGcdProjection N h b) := by
  have hp := sieveGcdProjection_pythagoras N h c b
  have hn := selbergTotientDiagonalForm_nonneg N
    (fun d => sieveGcdProjection N h c d - sieveGcdProjection N h b d)
  have hz : selbergTotientDiagonalForm N
      (fun d => sieveGcdProjection N h c d - sieveGcdProjection N h b d) = 0 ↔
        sieveGcdProjection N h c = sieveGcdProjection N h b := by
    rw [gcd_selberg_zero_iff]
    constructor
    · intro hd
      funext d
      by_cases hdI : d ∈ Finset.Icc 1 N
      · exact sub_eq_zero.mp (hd d hdI)
      · rw [gcd_projection_outside N h c d hdI, gcd_projection_outside N h b d hdI]
    · intro heq d _
      rw [heq, sub_self]
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    apply hz.mp
    linarith
  · intro heq
    have := hz.mpr heq
    linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
