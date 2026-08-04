import GaloisForLFunctions.RHTower.CCMRationalAdelicPureTensorHaarRadialTrace
import GaloisForLFunctions.RHTower.DeningerCapInversion

/-!
# Unit-invariant Möbius--Poisson compression

Normalized profinite-unit Haar averaging makes every finite residue weight
constant on `(ZMod N)ˣ`-orbits.  Möbius inversion then replaces that finite
orbit datum by divisor dilations of one even Schwartz source.  This file
proves the exact analytic compression law:

`bilateral periodic trace = physical zero mode + one Meyer positive sum`.

No formal power series, finite truncation, or exchange of two infinite sums
is used.  The only infinite reindexing is multiplication on positive
integers, after absolute summability has already been proved.
-/

noncomputable section

open scoped Classical BigOperators SchwartzMap FourierTransform

namespace GaloisForLFunctions.RHTower

/-- The finite weight on `Fin N` associated with a function on `ZMod N`. -/
def ccmRationalZModFinWeight
    (N : ℕ) [NeZero N] (g : ZMod N → ℂ) : Fin N → ℂ :=
  ccmRationalPeriodicResidueWeight N (fun n : ℤ => g (n : ZMod N))

theorem ccmRationalZMod_intCast_periodic
    (N : ℕ) [NeZero N] (g : ZMod N → ℂ) :
    Function.Periodic (fun n : ℤ => g (n : ZMod N)) (N : ℤ) := by
  intro n
  change g ((n + (N : ℤ) : ℤ) : ZMod N) = g (n : ZMod N)
  rw [Int.cast_add]
  simp

theorem ccmRationalZModFinWeight_residue
    (N : ℕ) [NeZero N] (g : ZMod N → ℂ) (n : ℤ) :
    ccmRationalZModFinWeight N g
        (ccmRationalPeriodicResidue N n) = g (n : ZMod N) := by
  exact (ccmRationalPeriodic_eq_residueWeight N _
    (ccmRationalZMod_intCast_periodic N g) n).symm

/-- Reflection symmetrization of an archimedean Schwartz source. -/
def ccmRationalSchwartzEvenization
    (f : CCMRationalArchimedeanSchwartz) :
    CCMRationalArchimedeanSchwartz :=
  f + RHTower.deningerReflect f

@[simp]
theorem ccmRationalSchwartzEvenization_apply
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalSchwartzEvenization f x = f x + f (-x) := by
  rfl

theorem ccmRationalSchwartzEvenization_even
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalSchwartzEvenization f (-x) =
      ccmRationalSchwartzEvenization f x := by
  simp only [ccmRationalSchwartzEvenization_apply, neg_neg]
  abel

/-- Natural dilation, with the zero scale sent to zero.  Divisors of a
nonzero modulus always select the nonzero branch. -/
def ccmRationalNaturalDilation
    (f : CCMRationalArchimedeanSchwartz) (d : ℕ) :
    CCMRationalArchimedeanSchwartz :=
  if hd : d = 0 then 0 else
    ccmRationalArchimedeanDilation f (d : ℝ) (by exact_mod_cast hd)

@[simp]
theorem ccmRationalNaturalDilation_apply_of_ne_zero
    (f : CCMRationalArchimedeanSchwartz) {d : ℕ} (hd : d ≠ 0) (x : ℝ) :
    ccmRationalNaturalDilation f d x = f ((d : ℝ) * x) := by
  simp [ccmRationalNaturalDilation, hd,
    ccmRationalArchimedeanDilation_apply]

/-- The single Schwartz source produced by unit-orbit Möbius compression. -/
def ccmRationalUnitInvariantMobiusSource
    (N : ℕ) (g : ZMod N → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    CCMRationalArchimedeanSchwartz :=
  ∑ d ∈ N.divisors,
    ccmRationalZModMobiusDivisorCoefficient N g d •
      ccmRationalNaturalDilation
        (ccmRationalSchwartzEvenization f) d

theorem ccmRationalUnitInvariantMobiusSource_apply
    {N : ℕ} (hN : N ≠ 0) (g : ZMod N → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalUnitInvariantMobiusSource N g f x =
      ∑ d ∈ N.divisors,
        ccmRationalZModMobiusDivisorCoefficient N g d *
          (f ((d : ℝ) * x) + f (-((d : ℝ) * x))) := by
  change RHTower.deningerSchwartzEval x (∑ d ∈ N.divisors,
      ccmRationalZModMobiusDivisorCoefficient N g d •
        ccmRationalNaturalDilation
          (ccmRationalSchwartzEvenization f) d) = _
  rw [map_sum (RHTower.deningerSchwartzEval x)]
  simp only [map_smul, RHTower.deningerSchwartzEval_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  change ccmRationalZModMobiusDivisorCoefficient N g d *
      ccmRationalNaturalDilation
        (ccmRationalSchwartzEvenization f) d x = _
  rw [ccmRationalNaturalDilation_apply_of_ne_zero _ hd0,
    ccmRationalSchwartzEvenization_apply]

theorem ccmRationalUnitInvariantMobiusSource_even
    {N : ℕ} (hN : N ≠ 0) (g : ZMod N → ℂ)
    (f : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    ccmRationalUnitInvariantMobiusSource N g f (-x) =
      ccmRationalUnitInvariantMobiusSource N g f x := by
  simp_rw [ccmRationalUnitInvariantMobiusSource_apply hN]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Physical endpoint of the compressed source.  The factor two records the
positive/negative pairing. -/
theorem ccmRationalUnitInvariantMobiusSource_zero
    {N : ℕ} (hN : N ≠ 0) (g : ZMod N → ℂ)
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalUnitInvariantMobiusSource N g f 0 =
      2 * (g 0 * f 0) := by
  rw [ccmRationalUnitInvariantMobiusSource_apply hN]
  simp only [mul_zero, neg_zero]
  rw [← Finset.sum_mul]
  have hmob := ccmRationalZMod_sum_mobiusDivisorCoefficient
    N g (n := N) (Nat.pos_of_ne_zero hN)
  rw [hmob]
  have hcast : (N : ZMod N) = 0 := by simp
  rw [hcast]
  ring

/-- A positive integer is divisible by `d ∣ N` exactly when its canonical
residue representative modulo `N` is divisible by `d`. -/
theorem ccmRational_dvd_zmodVal_natCast_iff
    {N d n : ℕ} (hdN : d ∣ N) :
    d ∣ (n : ZMod N).val ↔ d ∣ n := by
  rw [ZMod.val_natCast, Nat.dvd_mod_iff hdN]

/-- Möbius reconstruction written over the fixed divisor set of `N`, rather
than the residue-dependent divisor set of a gcd. -/
theorem CCMRationalZModUnitInvariant.eq_sum_divisors_indicator_pnat
    {N : ℕ} (hN : N ≠ 0) {g : ZMod N → ℂ}
    (hg : CCMRationalZModUnitInvariant N g) (n : ℕ+) :
    g ((n : ℕ) : ZMod N) =
      ∑ d ∈ N.divisors,
        if d ∣ (n : ℕ) then
          ccmRationalZModMobiusDivisorCoefficient N g d else 0 := by
  rw [hg.eq_sum_mobiusDivisorCoefficient hN ((n : ℕ) : ZMod N)]
  have hfin : (((n : ℕ) : ZMod N).val.gcd N).divisors =
      N.divisors.filter (fun d => d ∣ (n : ℕ)) := by
    ext d
    rw [ccmRational_mem_gcd_divisors_iff hN,
      Finset.mem_filter]
    constructor
    · rintro ⟨hdr, hdN⟩
      exact ⟨Nat.mem_divisors.mpr ⟨hdN, hN⟩,
        (ccmRational_dvd_zmodVal_natCast_iff hdN).mp hdr⟩
    · rintro ⟨hdmem, hdn⟩
      have hdN := (Nat.mem_divisors.mp hdmem).1
      exact ⟨(ccmRational_dvd_zmodVal_natCast_iff hdN).mpr hdn, hdN⟩
  rw [hfin, Finset.sum_filter]

/-- Multiplication by a positive integer identifies positive integers with
the positive multiples of that integer. -/
def ccmRationalPNatMulEquivDvd (m : ℕ+) :
    ℕ+ ≃ {n : ℕ+ // m ∣ n} where
  toFun k := ⟨m * k, dvd_mul_right m k⟩
  invFun n := PNat.divExact n.1 m
  left_inv k := by
    apply mul_left_cancel (a := m)
    exact PNat.mul_div_exact (dvd_mul_right m k)
  right_inv n := by
    apply Subtype.ext
    exact PNat.mul_div_exact n.2

/-- Meyer's natural-index sum is exactly the positive-integer sum. -/
theorem deningerMeyerSum_eq_tsum_pnat
    (f : CCMRationalArchimedeanSchwartz) (a : ℝ) :
    RHTower.deningerMeyerSum f a =
      ∑' n : ℕ+, f ((n : ℝ) * a) := by
  rw [RHTower.deningerMeyerSum]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => f ((n : ℝ) * a))).symm

private theorem ccmRationalPNat_cast_injective :
    Function.Injective (fun n : ℕ+ => (n : ℤ)) := by
  intro m n h
  apply Subtype.ext
  exact Int.ofNat.inj h

private theorem ccmRationalPNat_negCast_injective :
    Function.Injective (fun n : ℕ+ => -(n : ℤ)) := by
  intro m n h
  apply ccmRationalPNat_cast_injective
  exact neg_injective h

private theorem ccmRational_tsum_pnat_indicator_dvd_eq_dilation
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0)
    (c : ℂ) (d : ℕ) (hd : d ≠ 0) :
    (∑' n : ℕ+,
      if d ∣ (n : ℕ) then
        c * f ((n : ℝ) * a) else 0) =
      c * RHTower.deningerMeyerSum
        (ccmRationalNaturalDilation f d) a := by
  let m : ℕ+ := ⟨d, Nat.pos_of_ne_zero hd⟩
  have hsumm : Summable (fun n : ℕ+ => f ((n : ℝ) * a)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => f ((n : ℝ) * a))).2 (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          RHTower.deningerMeyerPositiveSum_summable f ha)
  have hdiv (n : ℕ+) : m ∣ n ↔ d ∣ (n : ℕ) := by
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨(k : ℕ), rfl⟩
    · rintro ⟨k, hk⟩
      have hkpos : 0 < k := by
        by_contra hk0
        have : k = 0 := Nat.eq_zero_of_not_pos hk0
        subst k
        simp at hk
      exact ⟨⟨k, hkpos⟩, Subtype.ext hk⟩
  calc
    (∑' n : ℕ+,
        if d ∣ (n : ℕ) then c * f ((n : ℝ) * a) else 0) =
        ∑' n : ℕ+, {n : ℕ+ | m ∣ n}.indicator
          (fun n : ℕ+ => c * f ((n : ℝ) * a)) n := by
      apply tsum_congr
      intro n
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      simp only [hdiv n]
    _ = ∑' n : ↑({n : ℕ+ | m ∣ n} : Set ℕ+),
          c * f ((n.1 : ℝ) * a) := by
      rw [← tsum_subtype]
    _ = ∑' n : {n : ℕ+ // m ∣ n},
          c * f ((n.1 : ℝ) * a) := by
      rfl
    _ = ∑' k : ℕ+,
          c * f ((((m * k : ℕ+) : ℝ)) * a) := by
      exact (ccmRationalPNatMulEquivDvd m).tsum_eq
        (fun n : {n : ℕ+ // m ∣ n} =>
          c * f ((n.1 : ℝ) * a)) |>.symm
    _ = c * ∑' k : ℕ+,
          ccmRationalNaturalDilation f d ((k : ℝ) * a) := by
      rw [tsum_mul_left]
      apply congrArg (fun z : ℂ => c * z)
      apply tsum_congr
      intro k
      rw [ccmRationalNaturalDilation_apply_of_ne_zero f hd]
      congr 1
      have hmk : (((m * k : ℕ+) : ℝ)) =
          (d : ℝ) * (k : ℝ) := by
        push_cast
        rfl
      rw [hmk]
      ring
    _ = c * RHTower.deningerMeyerSum
          (ccmRationalNaturalDilation f d) a := by
      rw [deningerMeyerSum_eq_tsum_pnat]

/-- **Unit-orbit Möbius--Poisson compression law.**  Every unit-invariant
periodic weighted bilateral Schwartz trace is a physical zero mode plus one
Meyer boundary. -/
theorem ccmRationalPeriodicWeightedTrace_eq_zero_add_mobiusMeyerSum
    {N : ℕ} [NeZero N] {g : ZMod N → ℂ}
    (hg : CCMRationalZModUnitInvariant N g)
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    ccmRationalPeriodicWeightedTrace N
        (ccmRationalZModFinWeight N g) f a =
      g 0 * f 0 + RHTower.deningerMeyerSum
        (ccmRationalUnitInvariantMobiusSource N g f) a := by
  have hN : N ≠ 0 := NeZero.ne N
  let w := ccmRationalZModFinWeight N g
  let F : ℤ → ℂ := fun n =>
    w (ccmRationalPeriodicResidue N n) * f (a * (n : ℝ))
  have hF : Summable F :=
    ccmRationalPeriodicWeightedTrace_summable N w f ha
  have hpos : Summable (fun n : ℕ+ => F (n : ℤ)) :=
    hF.comp_injective ccmRationalPNat_cast_injective
  have hneg : Summable (fun n : ℕ+ => F (-(n : ℤ))) :=
    hF.comp_injective ccmRationalPNat_negCast_injective
  have hevenSumm : Summable (fun n : ℕ+ =>
      ccmRationalSchwartzEvenization f ((n : ℝ) * a)) := by
    exact (summable_pnat_iff_summable_succ
      (f := fun n : ℕ =>
        ccmRationalSchwartzEvenization f ((n : ℝ) * a))).2 (by
          simpa only [Nat.cast_add, Nat.cast_one] using
            RHTower.deningerMeyerPositiveSum_summable
              (ccmRationalSchwartzEvenization f) ha)
  have htermSumm (d : ℕ) : Summable (fun n : ℕ+ =>
      if d ∣ (n : ℕ) then
        ccmRationalZModMobiusDivisorCoefficient N g d *
          ccmRationalSchwartzEvenization f ((n : ℝ) * a)
      else 0) := by
    refine ((hevenSumm.mul_left
      (ccmRationalZModMobiusDivisorCoefficient N g d)).indicator
        {n : ℕ+ | d ∣ (n : ℕ)}).congr ?_
    intro n
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [ccmRationalPeriodicWeightedTrace]
  change (∑' n : ℤ, F n) = _
  rw [tsum_int_eq_zero_add_tsum_pnat hF]
  have hzero : F 0 = g 0 * f 0 := by
    simp [F, w, ccmRationalZModFinWeight_residue]
  rw [hzero, add_assoc, ← hpos.tsum_add hneg]
  congr 1
  calc
    (∑' n : ℕ+, (F (n : ℤ) + F (-(n : ℤ)))) =
        ∑' n : ℕ+,
          g ((n : ℕ) : ZMod N) *
            ccmRationalSchwartzEvenization f ((n : ℝ) * a) := by
      apply tsum_congr
      intro n
      have hunit := hg (-1 : (ZMod N)ˣ) ((n : ℕ) : ZMod N)
      have hnegWeight : g (-((n : ℕ) : ZMod N)) =
          g ((n : ℕ) : ZMod N) := by
        simpa using hunit
      simp only [F, w, ccmRationalZModFinWeight_residue,
        Int.cast_natCast, Int.cast_neg,
        ccmRationalSchwartzEvenization_apply]
      rw [hnegWeight]
      congr 1
      push_cast
      ring
    _ = ∑' n : ℕ+, ∑ d ∈ N.divisors,
          if d ∣ (n : ℕ) then
            ccmRationalZModMobiusDivisorCoefficient N g d *
              ccmRationalSchwartzEvenization f ((n : ℝ) * a)
          else 0 := by
      apply tsum_congr
      intro n
      rw [hg.eq_sum_divisors_indicator_pnat hN n,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp_all
    _ = ∑ d ∈ N.divisors, ∑' n : ℕ+,
          if d ∣ (n : ℕ) then
            ccmRationalZModMobiusDivisorCoefficient N g d *
              ccmRationalSchwartzEvenization f ((n : ℝ) * a)
          else 0 := by
      exact Summable.tsum_finsetSum (fun d hd => htermSumm d)
    _ = ∑ d ∈ N.divisors,
          ccmRationalZModMobiusDivisorCoefficient N g d *
            RHTower.deningerMeyerSum
              (ccmRationalNaturalDilation
                (ccmRationalSchwartzEvenization f) d) a := by
      apply Finset.sum_congr rfl
      intro d hd
      exact ccmRational_tsum_pnat_indicator_dvd_eq_dilation
        (ccmRationalSchwartzEvenization f) ha _ d
          (Nat.pos_of_mem_divisors hd).ne'
    _ = RHTower.deningerMeyerSum
        (ccmRationalUnitInvariantMobiusSource N g f) a := by
      change (∑ d ∈ N.divisors,
          ccmRationalZModMobiusDivisorCoefficient N g d *
            RHTower.deningerMeyerPositiveSumLM a ha
              (ccmRationalNaturalDilation
              (ccmRationalSchwartzEvenization f) d)) =
        RHTower.deningerMeyerPositiveSumLM a ha
          (ccmRationalUnitInvariantMobiusSource N g f)
      rw [ccmRationalUnitInvariantMobiusSource]
      rw [map_sum (RHTower.deningerMeyerPositiveSumLM a ha)]
      simp only [map_smul, smul_eq_mul]

/-- Haar-radial pure tensors satisfy the compression law with the literal
averaged packet weight. -/
theorem ccmRationalAdelicPureTensorProfiniteHaarLogTrace_eq_mobiusMeyer
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (P : CCMRationalFiniteBruhatHaarRadialPacket phi) :
    ccmRationalAdelicPureTensorProfiniteHaarLogTrace f phi =
      fun t => P.averageWeight 0 *
          (ccmRationalPositiveDenominatorDilation
            f P.denominator P.denominator_pos) 0 +
        RHTower.deningerMeyerSum
          (ccmRationalUnitInvariantMobiusSource P.period P.averageWeight
            (ccmRationalPositiveDenominatorDilation
              f P.denominator P.denominator_pos))
          (Real.exp t) := by
  letI : NeZero P.period := P.period_neZero
  rw [ccmRationalAdelicPureTensorProfiniteHaarLogTrace_eq f phi P]
  funext t
  change ccmRationalPeriodicWeightedTrace P.period P.averageFinWeight
      (ccmRationalPositiveDenominatorDilation
        f P.denominator P.denominator_pos) (Real.exp t) = _
  have hw : P.averageFinWeight =
      ccmRationalZModFinWeight P.period P.averageWeight := rfl
  rw [hw]
  exact ccmRationalPeriodicWeightedTrace_eq_zero_add_mobiusMeyerSum
    P.averageWeight_unitInvariant _ (Real.exp_ne_zero t)

end GaloisForLFunctions.RHTower
