import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasOneEulerConstant
import GaloisForLFunctions.HTGeometry.LogHarmonicFinitePart

/-!
# The quadratic logarithmic divergence of a finite sieve

Deleting primes changes the density of the logarithmic harmonic sum, but creates
no term proportional to `log N`. The shift of the decimated logarithm cancels
the logarithm of the deleted prime in each summand.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry

/-- The logarithmic harmonic sum over the units of a finite prime sieve. -/
def sievedLogarithmicHarmonic (Q : Finset Nat.Primes) (N : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => Nat.Coprime n (sievePrimorial Q)),
    Real.log n / (n : ℝ)

/-- Prime deletion shifts both the harmonic weight and its logarithm. -/
theorem sievedLogarithmicHarmonic_insert
    {p : Nat.Primes} {Q : Finset Nat.Primes} (hp : p ∉ Q) (N : ℕ) :
    sievedLogarithmicHarmonic (insert p Q) N = sievedLogarithmicHarmonic Q N -
      (sievedLogarithmicHarmonic Q (N / (p : ℕ)) +
        Real.log (p : ℕ) * sievedHarmonic Q (N / (p : ℕ))) / (p : ℕ) := by
  classical
  let f : ℕ → ℝ := fun n =>
    if Nat.Coprime n (sievePrimorial Q) then Real.log n / (n : ℝ) else 0
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) (fun n => (p : ℕ) ∣ n) f
  have hcop : Nat.Coprime (p : ℕ) (sievePrimorial Q) := coprime_sievePrimorial hp
  have hmult : ∑ n ∈ (Icc 1 N).filter (fun n => (p : ℕ) ∣ n), f n =
      (sievedLogarithmicHarmonic Q (N / (p : ℕ)) +
        Real.log (p : ℕ) * sievedHarmonic Q (N / (p : ℕ))) / (p : ℕ) := by
    rw [multiples_Icc p.2.pos,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left p.2.pos h,
      sievedLogarithmicHarmonic, sievedHarmonic, sum_filter, sum_filter,
      mul_sum, ← sum_add_distrib, sum_div]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      have hnpos : 0 < n := (mem_Icc.mp hn).1
      exact_mod_cast hnpos.ne'
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    change (if Nat.Coprime ((p : ℕ) * n) (sievePrimorial Q) then
      Real.log (((p : ℕ) * n : ℕ) : ℝ) / (((p : ℕ) * n : ℕ) : ℝ) else 0) =
        ((if Nat.Coprime n (sievePrimorial Q) then Real.log n / (n : ℝ) else 0) +
          Real.log (p : ℕ) * (if Nat.Coprime n (sievePrimorial Q) then 1 / (n : ℝ) else 0)) /
            (p : ℕ)
    by_cases hunit : Nat.Coprime n (sievePrimorial Q)
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hcop, hunit⟩)]
      simp only [if_pos hunit, Nat.cast_mul, Real.log_mul hp0 hn0]
      ring
    · rw [if_neg (fun h => hunit (Nat.coprime_mul_iff_left.mp h).2)]
      simp only [if_neg hunit]
      ring
  have hfree : ∑ n ∈ (Icc 1 N).filter (fun n => ¬ (p : ℕ) ∣ n), f n =
      sievedLogarithmicHarmonic (insert p Q) N := by
    rw [sum_filter, sievedLogarithmicHarmonic, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [coprime_sievePrimorial_insert_iff hp, f]
    split_ifs <;> simp_all
  have hfull : ∑ n ∈ Icc 1 N, f n = sievedLogarithmicHarmonic Q N := by
    rw [sievedLogarithmicHarmonic, sum_filter]
  rw [hmult, hfree, hfull] at hsplit
  linarith only [hsplit]

private theorem tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Decimation by a fixed positive integer preserves logarithmic scale. -/
theorem tendsto_decimated_log_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => Real.log ((N / d : ℕ) : ℝ) / Real.log N) atTop (𝓝 1) := by
  have hzero := (tendsto_log_natDiv_sub_log hd).div_atTop tendsto_log_nat_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  field_simp
  ring

/-- A remainder negligible compared with the logarithm stays negligible after
fixed integer decimation. -/
theorem tendsto_decimated_log_error {f : ℕ → ℝ}
    (hf : Tendsto (fun N : ℕ => f N / Real.log N) atTop (𝓝 0))
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => f (N / d) / Real.log N) atTop (𝓝 0) := by
  have h := (hf.comp (tendsto_natDiv_atTop hd)).mul (tendsto_decimated_log_ratio hd)
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [(tendsto_natDiv_atTop hd).eventually (eventually_ge_atTop 2)] with N hN
  have hlog : Real.log ((N / d : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  dsimp only [Function.comp]
  field_simp

private theorem tendsto_decimated_log_square_error {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ =>
      (Real.log N ^ 2 - Real.log ((N / d : ℕ) : ℝ) ^ 2 -
        2 * Real.log d * Real.log ((N / d : ℕ) : ℝ)) / Real.log N) atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun N => Real.log ((N / d : ℕ) : ℝ) - Real.log N + Real.log d
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_log_natDiv_sub_log hd).add_const (Real.log d)
    simpa only [neg_add_cancel] using h
  have hsmall := ((tendsto_const_nhds (x := Real.log d ^ 2)).sub (hr.pow 2)).div_atTop
    tendsto_log_nat_atTop
  have h := hsmall.sub (hr.const_mul 2)
  simp only [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  dsimp only [r]
  field_simp
  ring

/-- A finite prime sieve has quadratic logarithmic divergence and no linear
logarithmic term in its logarithm-weighted harmonic sum. -/
theorem tendsto_sievedLogarithmicHarmonic_sub_div_log (Q : Finset Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (2 * sievedLogarithmicHarmonic Q N - sieveDensity Q * Real.log N ^ 2) / Real.log N)
      atTop (𝓝 0) := by
  classical
  induction Q using Finset.induction with
  | empty =>
      have h := (tendsto_logarithmicHarmonic_sub.div_atTop tendsto_log_nat_atTop).const_mul 2
      rw [mul_zero] at h
      refine h.congr fun N => ?_
      have hsum : sievedLogarithmicHarmonic ∅ N = logarithmicHarmonic N := by
        simp [sievedLogarithmicHarmonic, logarithmicHarmonic]
      rw [hsum, sieveDensity_empty]
      ring
  | insert p Q hp ih =>
      have hdec := tendsto_decimated_log_error ih p.2.pos
      have hH := ((tendsto_sievedHarmonic_sub_sieveEuler Q).comp
        (tendsto_natDiv_atTop p.2.pos)).div_atTop tendsto_log_nat_atTop
      have hquad := tendsto_decimated_log_square_error p.2.pos
      have h := ((ih.sub (hdec.div_const ((p : ℕ) : ℝ))).sub
        (hH.const_mul (2 * Real.log (p : ℕ) / (p : ℕ)))).add
          (hquad.const_mul (sieveDensity Q / (p : ℕ)))
      simp only [zero_div, mul_zero, sub_zero, add_zero] at h
      refine h.congr fun N => ?_
      rw [sievedLogarithmicHarmonic_insert hp, sieveDensity_insert hp]
      dsimp only [Function.comp]
      ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
