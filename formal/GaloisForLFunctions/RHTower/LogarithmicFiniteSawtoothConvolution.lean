import GaloisForLFunctions.RHTower.LogarithmicFiniteEntryProfile
import GaloisForLFunctions.RHTower.LogarithmicSawtoothEntryCorrelation

/-!
# Finite signed convolution on the square-root rectangle

The reciprocal-correlation matrix factors as one integral of two finite
causal profiles. Coefficients are arbitrary signed reals. Specializing
to Möbius coefficients preserves the actual short inverse and every
arrival-time cutoff.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

theorem logarithmicFiniteEntryProfile_sawtooth_eq_sum (w : ℕ → ℝ) (U : ℕ) (t : ℝ) :
    logarithmicFiniteEntryProfile w U logarithmicCenteredSawtooth t =
      ∑ n ∈ Finset.Icc 1 U, w n * logarithmicSawtoothEntry (Real.log n) t := by
  unfold logarithmicFiniteEntryProfile
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ t <;> simp [logarithmicSawtoothEntry, hn]

private theorem profile_pair_expansion (w v : ℕ → ℝ) (U : ℕ) (T s : ℝ) :
    logarithmicFiniteEntryProfile w U logarithmicCenteredSawtooth s *
      logarithmicFiniteEntryProfile v U logarithmicCenteredSawtooth (T - s) =
        ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U, w a * v b *
          (logarithmicSawtoothEntry (Real.log a) s *
            logarithmicSawtoothEntry (Real.log b) (T - s)) := by
  simp only [logarithmicFiniteEntryProfile_sawtooth_eq_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem intervalIntegrable_logarithmicFiniteEntryProfile_pair
    (w v : ℕ → ℝ) (U : ℕ) (T a b : ℝ) :
    IntervalIntegrable (fun s =>
      logarithmicFiniteEntryProfile w U logarithmicCenteredSawtooth s *
        logarithmicFiniteEntryProfile v U logarithmicCenteredSawtooth (T - s)) volume a b := by
  have hi (m n : ℕ) : IntervalIntegrable (fun s => w m * v n *
      (logarithmicSawtoothEntry (Real.log m) s *
        logarithmicSawtoothEntry (Real.log n) (T - s))) volume a b :=
    (intervalIntegrable_logarithmicSawtoothEntry_pair (Real.log m) (Real.log n) T a b).const_mul _
  have hs := IntervalIntegrable.sum (s := Finset.Icc 1 U)
    (fun m _ => IntervalIntegrable.sum (s := Finset.Icc 1 U) (fun n _ => hi m n))
  apply hs.congr
  intro s _
  simpa only [Finset.sum_apply] using (profile_pair_expansion w v U T s).symm

theorem integral_logarithmicFiniteEntryProfile_pair
    (w v : ℕ → ℝ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T,
      logarithmicFiniteEntryProfile w ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth s *
        logarithmicFiniteEntryProfile v ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth (T - s)) =
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
          w a * v b * logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ)) := by
  let U := ⌊Real.exp (T / 2)⌋₊
  let term := fun (a b : ℕ) (s : ℝ) => w a * v b *
    (logarithmicSawtoothEntry (Real.log a) s * logarithmicSawtoothEntry (Real.log b) (T - s))
  have hi (a b : ℕ) : IntervalIntegrable (term a b) volume 0 T :=
    (intervalIntegrable_logarithmicSawtoothEntry_pair (Real.log a) (Real.log b) T 0 T).const_mul _
  have hirow (a : ℕ) : IntervalIntegrable
      (fun s => ∑ b ∈ Finset.Icc 1 U, term a b s) volume 0 T := by
    apply (IntervalIntegrable.sum (s := Finset.Icc 1 U) (fun b _ => hi a b)).congr
    intro s _
    simp only [Finset.sum_apply]
  have hpoint (s : ℝ) :
      logarithmicFiniteEntryProfile w U logarithmicCenteredSawtooth s *
        logarithmicFiniteEntryProfile v U logarithmicCenteredSawtooth (T - s) =
          ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U, term a b s :=
    profile_pair_expansion w v U T s
  change (∫ s in (0 : ℝ)..T,
    logarithmicFiniteEntryProfile w U logarithmicCenteredSawtooth s *
      logarithmicFiniteEntryProfile v U logarithmicCenteredSawtooth (T - s)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun a _ => hirow a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [intervalIntegral.integral_finsetSum (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b hb
  have hap : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hbp : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  have ha0 : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp ha).1)
  have hb0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hb).1)
  have haT : Real.log a ≤ T / 2 := (Real.log_le_iff_le_exp hap).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp ha).2)
  have hbT : Real.log b ≤ T / 2 := (Real.log_le_iff_le_exp hbp).mpr
    ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hb).2)
  dsimp only [term]
  rw [intervalIntegral.integral_const_mul,
    integral_logarithmicSawtoothEntry_pair ha0 hb0 (by linarith only [haT, hbT]),
    Nat.cast_mul, Real.log_mul hap.ne' hbp.ne', sub_add_eq_sub_sub]

theorem logarithmicShortMobiusInverse_reciprocalCorrelation_square (T : ℝ) :
    (∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
      ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ))) =
      ∫ s in (0 : ℝ)..T,
        logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth s *
          logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth (T - s) := by
  simp_rw [logarithmicShortMobiusInverse_eq_finiteEntryProfile]
  exact (integral_logarithmicFiniteEntryProfile_pair _ _ T).symm

end RHTower
