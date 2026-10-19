import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery
import GaloisForLFunctions.BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods

/-!
# Exact half-period shifts and affine anchors

A translate of a divisor sieve remains a divisor sieve precisely when twice
the shift is an actual period. The translated weights are twice the existing
gcd projection minus the original weights. Every translated moment is then
preserved. Labelled affine moments are preserved exactly when all comparable
coordinate products crossing the resonant divisor set vanish.
-/

open scoped BigOperators
open Finset ZMod
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.HalfPeriod
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Reflection across the divisor signals fixed by translation through h. -/
def reflection (N h : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  2 * sieveGcdProjection N h c d - c d

/-- Reflection keeps the resonant coordinates and reverses the others. -/
theorem coordinate_reflection (N h q : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (reflection N h c) q =
      if q ∣ h then selbergMultiplesCoord N c q else -selbergMultiplesCoord N c q := by
  calc
    _ = 2 * selbergMultiplesCoord N (sieveGcdProjection N h c) q -
        selbergMultiplesCoord N c q := by
      simp only [reflection, selbergMultiplesCoord, sub_div, mul_div_assoc,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [selbergMultiplesCoord_gcdProjection]
      split_ifs <;> ring

private abbrev signal (N : ℕ) (c : ℕ → ℝ) : ZMod N.factorial → ℂ :=
  residueSignal N (fun d => (c d : ℂ))

private theorem signal_even (N : ℕ) (c : ℕ → ℝ) : Function.Even (signal N c) := by
  apply ZMod.dft_even_iff.mp
  intro r
  simp only [signal, dft_residueSignal, addOrderOf_neg]

private theorem signal_periodic (N h : ℕ) (c : ℕ → ℝ)
    (hp : Function.Periodic (sieveSeq N c) h) :
    ∀ x : ZMod N.factorial, signal N c (x + h) = signal N c x := by
  intro x
  have hx : x + (h : ZMod N.factorial) = ((x.val + h : ℕ) : ZMod N.factorial) := by simp
  rw [hx, signal, residueSignal_sieveSeq, hp]
  simpa only [signal, ZMod.natCast_zmod_val] using
    (residueSignal_sieveSeq N c x.val).symm

private theorem dft_right_translation {P : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (t r : ZMod P) :
    ZMod.dft (fun x => f (x + t)) r = ZMod.stdAddChar (t * r) * ZMod.dft f r := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ (fun x => ?_)
  change ZMod.stdAddChar (-(x*r)) * f (x+t) =
    ZMod.stdAddChar (t*r) * (ZMod.stdAddChar (-((x+t)*r)) * f (x+t))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

private theorem phase_eq_one_iff {P : ℕ} [NeZero P] (x : ZMod P) :
    ZMod.stdAddChar x = 1 ↔ x = 0 := by
  constructor
  · intro hx
    exact ZMod.injective_stdAddChar (by simpa using hx)
  · rintro rfl
    simp

private theorem signal_reflection (N h : ℕ) (c : ℕ → ℝ)
    (hp : Function.Periodic (sieveSeq N c) (2*h)) :
    signal N (reflection N h c) = fun x => signal N c (x + h) := by
  apply ZMod.dft.injective
  funext r
  have hr (t : ℕ) : (t : ZMod N.factorial) * r = 0 ↔ addOrderOf r ∣ t := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simp only [nsmul_eq_mul]
  have href : ZMod.dft (signal N (reflection N h c)) r =
      if addOrderOf r ∣ h then ZMod.dft (signal N c) r
      else -ZMod.dft (signal N c) r := by
    simp only [signal, dft_residueSignal, coordinate_ofReal, coordinate_reflection]
    split_ifs <;> simp
  rw [href, dft_right_translation]
  by_cases hh : addOrderOf r ∣ h
  · rw [if_pos hh, (hr h).mpr hh]
    simp
  · rw [if_neg hh]
    by_cases htwo : addOrderOf r ∣ 2*h
    · have hz : (h : ZMod N.factorial) * r + (h : ZMod N.factorial) * r = 0 := by
        calc
          _ = ((2*h : ℕ) : ZMod N.factorial) * r := by push_cast; ring
          _ = 0 := (hr (2*h)).mpr htwo
      have hs : ZMod.stdAddChar ((h : ZMod N.factorial)*r) *
          ZMod.stdAddChar ((h : ZMod N.factorial)*r) = 1 := by
        rw [← AddChar.map_add_eq_mul, hz]
        simp
      have hn : ZMod.stdAddChar ((h : ZMod N.factorial)*r) ≠ 1 :=
        fun hx => hh ((hr h).mp ((phase_eq_one_iff _).mp hx))
      rw [(mul_self_eq_one_iff.mp hs).resolve_left hn]
      ring
    · have hz : ZMod.dft (signal N c) r = 0 := by
        apply RHTower.Sieve.dft_eq_zero_of_periodic_nontrivial_phase _
          ((2*h : ℕ) : ZMod N.factorial) r (signal_periodic N (2*h) c hp)
        intro hx
        have hz := (phase_eq_one_iff _).mp hx
        exact htwo ((hr (2*h)).mp (by simpa using hz))
      rw [hz]
      simp

/-- A literal half-period shift is an actual reflected divisor sieve. -/
theorem sieveSeq_reflection (N h k : ℕ) (c : ℕ → ℝ)
    (hp : Function.Periodic (sieveSeq N c) (2*h)) :
    sieveSeq N (reflection N h c) k = sieveSeq N c (k+h) := by
  apply Complex.ofReal_injective
  rw [← residueSignal_sieveSeq, ← residueSignal_sieveSeq]
  have hs := congrFun (signal_reflection N h c hp) (k : ZMod N.factorial)
  simpa only [signal, Nat.cast_add] using hs

/-- A shifted divisor sieve is again a divisor sieve exactly when twice the shift is a period. -/
theorem shift_representable_iff (N h : ℕ) (c : ℕ → ℝ) :
    (∃ b : ℕ → ℝ, ∀ k, sieveSeq N b k = sieveSeq N c (k+h)) ↔
      Function.Periodic (sieveSeq N c) (2*h) := by
  constructor
  · rintro ⟨b, hb⟩
    have hs (x : ZMod N.factorial) : signal N b x = signal N c (x+h) := by
      have hx : x + (h : ZMod N.factorial) = ((x.val+h : ℕ) : ZMod N.factorial) := by simp
      change residueSignal N (fun d => (b d : ℂ)) x =
        residueSignal N (fun d => (c d : ℂ)) (x+h)
      rw [hx, residueSignal_sieveSeq]
      have hbx := residueSignal_sieveSeq N b x.val
      rw [ZMod.natCast_zmod_val, hb] at hbx
      exact hbx
    have hp (x : ZMod N.factorial) : signal N c (x + ((2*h : ℕ) : ZMod N.factorial)) = signal N c x := by
      calc
        _ = signal N c ((x+h)+h) := by congr 1; push_cast; ring
        _ = signal N b (x+h) := (hs _).symm
        _ = signal N b (-(x+h)) := (signal_even N b _).symm
        _ = signal N c (-(x+h)+h) := hs _
        _ = signal N c (-x) := by congr 1; ring
        _ = signal N c x := signal_even N c x
    intro k
    apply Complex.ofReal_injective
    rw [← residueSignal_sieveSeq, ← residueSignal_sieveSeq]
    simpa only [signal, Nat.cast_add] using hp (k : ZMod N.factorial)
  · intro hp
    exact ⟨reflection N h c, fun k => sieveSeq_reflection N h k c hp⟩

/-- The exact representability condition is divisibility of every active raw divisor into twice the shift. -/
theorem shift_representable_iff_active_divisors (N h : ℕ) (c : ℕ → ℝ) :
    (∃ b : ℕ → ℝ, ∀ k, sieveSeq N b k = sieveSeq N c (k+h)) ↔
      ∀ d ∈ Finset.Icc 1 N, c d ≠ 0 → d ∣ 2*h := by
  exact (shift_representable_iff N h c).trans
    (sieveSeq_periodic_iff_active_divisors N (2*h) c)

/-- Every translated moment is unchanged by the actual half-period reflection. -/
theorem translatedMoment_reflection (N h : ℕ) (c : ℕ → ℝ)
    (hp : Function.Periodic (sieveSeq N c) (2*h)) {m : ℕ} (v : Fin m → ℕ) :
    translatedMoment N (reflection N h c) v = translatedMoment N c v := by
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq, translatedMoment_complex_eq]
  change translationMoment (signal N (reflection N h c)) (fun i => (v i : ZMod N.factorial)) =
    translationMoment (signal N c) (fun i => (v i : ZMod N.factorial))
  rw [signal_reflection N h c hp]
  unfold translationMoment
  apply congrArg (fun z : ℂ => (N.factorial : ℂ)⁻¹ * z)
  refine Fintype.sum_equiv (Equiv.addRight (h : ZMod N.factorial)) _ _ (fun x => ?_)
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (signal N c) (by
    change x + (v i : ZMod N.factorial) + (h : ZMod N.factorial) =
      (x + h) + (v i : ZMod N.factorial)
    ring)

/-- Labelled affine data preserve a reflection exactly when every crossing divisor product vanishes. -/
theorem affineMoment_reflection_iff (N h : ℕ) (c : ℕ → ℝ) :
    (∀ a b, affineMoment N c a b = affineMoment N (reflection N h c) a b) ↔
      ∀ q ∈ Finset.Icc 1 N, ∀ d ∈ q.divisors, ¬q ∣ h → d ∣ h →
        selbergMultiplesCoord N c q * selbergMultiplesCoord N c d = 0 := by
  rw [affineMoment_eq_iff_comparable]
  constructor
  · intro hdata q hq d hd hqnot hdyes
    have he := hdata q hq d hd
    rw [coordinate_reflection, coordinate_reflection, if_neg hqnot, if_pos hdyes] at he
    linarith
  · intro hzero q hq d hd
    rw [coordinate_reflection, coordinate_reflection]
    by_cases hqyes : q ∣ h
    · have hdyes := (Nat.dvd_of_mem_divisors hd).trans hqyes
      simp [hqyes, hdyes]
    · by_cases hdyes : d ∣ h
      · simp only [if_neg hqyes, if_pos hdyes, neg_mul]
        rw [hzero q hq d hd hqyes hdyes, neg_zero]
      · simp [hqyes, hdyes]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.HalfPeriod
