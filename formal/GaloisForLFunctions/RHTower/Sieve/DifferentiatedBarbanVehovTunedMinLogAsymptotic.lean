import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogGram
import GaloisForLFunctions.RHTower.Sieve.SelbergLogPowerGeneralAsymptotic
import GaloisForLFunctions.RHTower.RegularizedDivisorHarmonicLimit
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedFortyNineError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovFortyNineScaleAsymptotics

/-!
# Tuned minimum-log asymptotic and the T1 one-eighth law

An exact ordinary Abel transform converts the reciprocal-tuned minimum-log Gram remainder
into three one-variable Selberg profile channels.  A floor-stable real-cutoff Graham law and
dominated convergence evaluate those channels, proving the normalized remainder limit `7/12`.
Consequently, at the `49/100` reciprocal schedule, the actual included long detector carries
exactly one eighth of the full long-energy asymptotic.
-/

open ArithmeticFunction Finset Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

def selbergOriginalLogCutoffMonomial
    (i j M : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    selbergOriginalCoeff p.1 p.2 *
      (max (u - Real.log p.1) 0) ^ i *
        (max (u - Real.log p.2) 0) ^ j

theorem selbergOriginalLogCutoffMonomial_comm
    (i j M : ℕ) (u : ℝ) :
    selbergOriginalLogCutoffMonomial i j M u =
      selbergOriginalLogCutoffMonomial j i M u := by
  rw [selbergOriginalLogCutoffMonomial, selbergOriginalLogCutoffMonomial,
    Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [show selbergOriginalCoeff n m = selbergOriginalCoeff m n by
    rw [selbergOriginalCoeff, selbergOriginalCoeff, Nat.gcd_comm]
    ring]
  ring

theorem mul_max_eq_sq_add (x c : ℝ) :
    (x + c) * max x 0 = (max x 0) ^ 2 + c * max x 0 := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx]
    ring
  · rw [max_eq_left hx]
    ring

theorem selbergOriginalTunedMinLogRemainder_eq_integral_pairFeature
    {M : ℕ} (hM : 0 < M) :
    selbergOriginalTunedMinLogRemainder M =
      ∫ t in (0 : ℝ)..Real.log M,
        ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          selbergOriginalCoeff p.1 p.2 *
            (linearCutoffFeature (Real.log ((M : ℝ) / (p.1 : ℝ))) t *
              linearCutoffFeature (Real.log ((M : ℝ) / (p.2 : ℝ))) t) := by
  let S : Finset ℕ := Finset.Icc 1 M
  let H : ℝ := Real.log M
  let A : ℕ → ℝ := fun m => Real.log ((M : ℝ) / (m : ℝ))
  have hpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
  have hle : ∀ m ∈ S, m ≤ M := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).2
  have hA0 : ∀ m ∈ S, 0 ≤ A m := by
    intro m hm
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hpos m hm
    apply Real.log_nonneg
    rw [le_div_iff₀ hmR]
    norm_num
    exact_mod_cast hle m hm
  have hAH : ∀ m ∈ S, A m ≤ H := by
    intro m hm
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpos m hm
    have hmR : (0 : ℝ) < (m : ℝ) := by positivity
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hratio : (M : ℝ) / (m : ℝ) ≤ (M : ℝ) := by
      rw [div_le_iff₀ hmR]
      nlinarith
    exact Real.log_le_log (by positivity) hratio
  rw [selbergOriginalTunedMinLogRemainder_eq_kernel]
  have hterm : ∀ p ∈ S ×ˢ S,
      selbergOriginalCoeff p.1 p.2 *
          (A p.1 * A p.2 *
            (min (A p.1) (A p.2) * A p.1 * A p.2 -
              min (A p.1) (A p.2) ^ 2 / 2 * (A p.1 + A p.2) +
                min (A p.1) (A p.2) ^ 3 / 3)) =
        ∫ t in (0 : ℝ)..H,
          selbergOriginalCoeff p.1 p.2 *
            (linearCutoffFeature (A p.1) t * linearCutoffFeature (A p.2) t) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [← integral_linearCutoffFeature_mul (hA0 p.1 hp1) (hA0 p.2 hp2)
      (hAH p.1 hp1) (hAH p.2 hp2)]
    rw [intervalIntegral.integral_const_mul]
  change (∑ p ∈ S ×ˢ S,
      selbergOriginalCoeff p.1 p.2 *
        (A p.1 * A p.2 *
          (min (A p.1) (A p.2) * A p.1 * A p.2 -
            min (A p.1) (A p.2) ^ 2 / 2 * (A p.1 + A p.2) +
              min (A p.1) (A p.2) ^ 3 / 3))) = _
  rw [Finset.sum_congr rfl hterm]
  have hintegrable : ∀ p ∈ S ×ˢ S, IntervalIntegrable
      (fun t : ℝ => selbergOriginalCoeff p.1 p.2 *
        (linearCutoffFeature (A p.1) t * linearCutoffFeature (A p.2) t))
      volume 0 H := by
    intro p hp
    exact (continuous_const.mul ((continuous_linearCutoffFeature (A p.1)).mul
      (continuous_linearCutoffFeature (A p.2)))).intervalIntegrable 0 H
  rw [← intervalIntegral.integral_finsetSum hintegrable]

theorem linearCutoffFeature_log_sub
    {M m : ℕ} (hM : 0 < M) (hm : 0 < m) (u : ℝ) :
    linearCutoffFeature (Real.log ((M : ℝ) / (m : ℝ)))
        (Real.log M - u) =
      (max (u - Real.log m) 0) ^ 2 +
        (Real.log M - u) * max (u - Real.log m) 0 := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [linearCutoffFeature, Real.log_div hMR hmR]
  have harg : Real.log (M : ℝ) - Real.log (m : ℝ) -
      (Real.log (M : ℝ) - u) = u - Real.log (m : ℝ) := by ring
  rw [harg]
  convert mul_max_eq_sq_add (u - Real.log (m : ℝ)) (Real.log (M : ℝ) - u) using 1 <;> ring

theorem selbergOriginalTunedMinLogRemainder_eq_ordinaryAbel
    {M : ℕ} (hM : 0 < M) :
    selbergOriginalTunedMinLogRemainder M =
      ∫ u in (0 : ℝ)..Real.log M,
        selbergOriginalLogCutoffMonomial 2 2 M u +
          2 * (Real.log M - u) * selbergOriginalLogCutoffMonomial 1 2 M u +
            (Real.log M - u) ^ 2 * selbergOriginalLogCutoffMonomial 1 1 M u := by
  rw [selbergOriginalTunedMinLogRemainder_eq_integral_pairFeature hM]
  let H : ℝ := Real.log M
  let F : ℝ → ℝ := fun t =>
    ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      selbergOriginalCoeff p.1 p.2 *
        (linearCutoffFeature (Real.log ((M : ℝ) / (p.1 : ℝ))) t *
          linearCutoffFeature (Real.log ((M : ℝ) / (p.2 : ℝ))) t)
  have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := H) F H
  have hsub' : (∫ x in (0 : ℝ)..H, F (H - x)) = ∫ x in (0 : ℝ)..H, F x := by
    simpa using hsub
  change (∫ t in (0 : ℝ)..H, F t) = _
  rw [← hsub']
  apply intervalIntegral.integral_congr
  intro u hu
  simp only [F]
  have hp : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      linearCutoffFeature (Real.log ((M : ℝ) / (p.1 : ℝ))) (H - u) =
          (max (u - Real.log p.1) 0) ^ 2 +
            (H - u) * max (u - Real.log p.1) 0 ∧
      linearCutoffFeature (Real.log ((M : ℝ) / (p.2 : ℝ))) (H - u) =
          (max (u - Real.log p.2) 0) ^ 2 +
            (H - u) * max (u - Real.log p.2) 0 := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact ⟨linearCutoffFeature_log_sub hM (Finset.mem_Icc.mp hp1).1 u,
      linearCutoffFeature_log_sub hM (Finset.mem_Icc.mp hp2).1 u⟩
  rw [Finset.sum_congr rfl fun p hpmem => by rw [(hp p hpmem).1, (hp p hpmem).2]]
  calc
    (∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        selbergOriginalCoeff p.1 p.2 *
          (((max (u - Real.log p.1) 0) ^ 2 +
              (H - u) * max (u - Real.log p.1) 0) *
            ((max (u - Real.log p.2) 0) ^ 2 +
              (H - u) * max (u - Real.log p.2) 0))) =
        selbergOriginalLogCutoffMonomial 2 2 M u +
          (H - u) * selbergOriginalLogCutoffMonomial 2 1 M u +
          (H - u) * selbergOriginalLogCutoffMonomial 1 2 M u +
          (H - u) ^ 2 * selbergOriginalLogCutoffMonomial 1 1 M u := by
      simp only [selbergOriginalLogCutoffMonomial, pow_one]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hpmem
      ring
    _ = selbergOriginalLogCutoffMonomial 2 2 M u +
          2 * (Real.log M - u) * selbergOriginalLogCutoffMonomial 1 2 M u +
            (Real.log M - u) ^ 2 * selbergOriginalLogCutoffMonomial 1 1 M u := by
      rw [selbergOriginalLogCutoffMonomial_comm 2 1 M u]
      dsimp [H]
      ring

/-- Absolute mass of the original gcd coefficient on the square `[1,N]^2`. -/
def selbergOriginalCoeffAbsMass (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    |selbergOriginalCoeff p.1 p.2|

/-- Original Selberg log-monomial with a real cutoff and natural-floor support. -/
def selbergOriginalLogMonomialReal (i j : ℕ) (Y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊Y⌋₊) ×ˢ (Finset.Icc 1 ⌊Y⌋₊),
    selbergOriginalCoeff p.1 p.2 *
      Real.log (Y / (p.1 : ℝ)) ^ i * Real.log (Y / (p.2 : ℝ)) ^ j

@[simp] theorem selbergOriginalLogMonomialReal_natCast (i j N : ℕ) :
    selbergOriginalLogMonomialReal i j (N : ℝ) =
      selbergOriginalLogMonomial i j N := by
  simp only [selbergOriginalLogMonomialReal, selbergOriginalLogMonomial,
    Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private theorem abs_pow_mul_pow_sub_le_t1
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    {x x₀ y y₀ R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hx : |x| ≤ R) (hx₀ : |x₀| ≤ R)
    (hy : |y| ≤ R) (hy₀ : |y₀| ≤ R)
    (hdx : |x - x₀| ≤ δ) (hdy : |y - y₀| ≤ δ) :
    |x ^ i * y ^ j - x₀ ^ i * y₀ ^ j| ≤
      ((i + j : ℕ) : ℝ) * R ^ (i + j - 1) * δ := by
  have hpowx := GaloisForLFunctions.RHTower.Matveev.abs_pow_sub_pow_le hx hx₀ i
  have hpowy := GaloisForLFunctions.RHTower.Matveev.abs_pow_sub_pow_le hy hy₀ j
  have hpowx' : |x ^ i - x₀ ^ i| ≤ (i : ℝ) * R ^ (i - 1) * δ :=
    hpowx.trans (mul_le_mul_of_nonneg_left hdx (by positivity))
  have hpowy' : |y ^ j - y₀ ^ j| ≤ (j : ℝ) * R ^ (j - 1) * δ :=
    hpowy.trans (mul_le_mul_of_nonneg_left hdy (by positivity))
  calc
    |x ^ i * y ^ j - x₀ ^ i * y₀ ^ j| =
        |(x ^ i - x₀ ^ i) * y ^ j + x₀ ^ i * (y ^ j - y₀ ^ j)| := by
      congr 1
      ring
    _ ≤ |(x ^ i - x₀ ^ i) * y ^ j| +
        |x₀ ^ i * (y ^ j - y₀ ^ j)| := abs_add_le _ _
    _ = |x ^ i - x₀ ^ i| * |y| ^ j +
        |x₀| ^ i * |y ^ j - y₀ ^ j| := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow]
    _ ≤ ((i : ℝ) * R ^ (i - 1) * δ) * R ^ j +
        R ^ i * ((j : ℝ) * R ^ (j - 1) * δ) := by
      gcongr
    _ = ((i : ℝ) * δ) * (R ^ (i - 1) * R ^ j) +
        ((j : ℝ) * δ) * (R ^ i * R ^ (j - 1)) := by ring
    _ = ((i + j : ℕ) : ℝ) * R ^ (i + j - 1) * δ := by
      rw [← pow_add, ← pow_add,
        show i - 1 + j = i + j - 1 by omega,
        show i + (j - 1) = i + j - 1 by omega]
      push_cast
      ring

private theorem harmonic_cast_mono_t1 {a b : ℕ} (hab : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  rw [RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum,
    RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hab⟩
  · intro n hn hna
    positivity

private theorem abs_selbergOriginalCoeff_le_reciprocalGcd
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    |selbergOriginalCoeff m n| ≤
      (Nat.gcd m n : ℝ) * (m : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
  have hmu_m : |((moebius m : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))
  have hmu_n : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [selbergOriginalCoeff, abs_mul, abs_mul, abs_div, abs_div,
    abs_of_pos hmR, abs_of_pos hnR,
    abs_of_nonneg (show (0 : ℝ) ≤ (Nat.gcd m n : ℝ) by positivity)]
  calc
    (|((moebius m : ℤ) : ℝ)| / (m : ℝ)) *
        (|((moebius n : ℤ) : ℝ)| / (n : ℝ)) * (Nat.gcd m n : ℝ) ≤
      (1 / (m : ℝ)) * (1 / (n : ℝ)) * (Nat.gcd m n : ℝ) := by
        gcongr
    _ = (Nat.gcd m n : ℝ) * (m : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
      simp only [one_div]
      ring

/-- The endpoint-shift majorant: absolute gcd-coefficient mass grows at most cubically in the
harmonic number.  This is the rate needed to transfer the ordinary Selberg asymptotics from
integer cutoffs to real cutoffs. -/
theorem selbergOriginalCoeffAbsMass_le_harmonic_cube (N : ℕ) :
    selbergOriginalCoeffAbsMass N ≤ (harmonic N : ℝ) ^ 3 := by
  classical
  let S : Finset ℕ := Finset.Icc 1 N
  let f : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  have hpos : ∀ d ∈ S, 0 < d := fun d hd => (Finset.mem_Icc.mp hd).1
  have hle : ∀ d ∈ S, d ≤ N := fun d hd => (Finset.mem_Icc.mp hd).2
  have hgauss := sum_gcd_mul_weight_eq_sum_totient_mul_sq f hpos hle
  calc
    selbergOriginalCoeffAbsMass N ≤
        ∑ p ∈ S ×ˢ S, (Nat.gcd p.1 p.2 : ℝ) * f p.1 * f p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      exact abs_selbergOriginalCoeff_le_reciprocalGcd
        (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
    _ = ∑ g ∈ Finset.Icc 1 N, (Nat.totient g : ℝ) *
          (∑ d ∈ S.filter (fun d => g ∣ d), f d) ^ 2 := hgauss
    _ ≤ ∑ g ∈ Finset.Icc 1 N, (g : ℝ)⁻¹ * (harmonic N : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro g hg
      have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
      have hgN : g ≤ N := (Finset.mem_Icc.mp hg).2
      have hgR : (0 : ℝ) < (g : ℝ) := by positivity
      have hsum : (∑ d ∈ S.filter (fun d => g ∣ d), f d) =
          (g : ℝ)⁻¹ * (harmonic (N / g) : ℝ) := by
        simpa only [S, f] using
          RHTower.RegularizedDivisorHarmonic.sum_inv_multiples_eq_harmonic N g hg1
      rw [hsum]
      have hharm : (harmonic (N / g) : ℝ) ≤ (harmonic N : ℝ) :=
        harmonic_cast_mono_t1 (Nat.div_le_self N g)
      have hharm0 : (0 : ℝ) ≤ (harmonic (N / g) : ℝ) := by
        rw [RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
        positivity
      have hHN0 : (0 : ℝ) ≤ (harmonic N : ℝ) := by
        rw [RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
        positivity
      calc
        (Nat.totient g : ℝ) * ((g : ℝ)⁻¹ * (harmonic (N / g) : ℝ)) ^ 2 ≤
            (g : ℝ) * ((g : ℝ)⁻¹ * (harmonic N : ℝ)) ^ 2 := by
          gcongr
          · exact_mod_cast Nat.totient_le g
        _ = (g : ℝ)⁻¹ * (harmonic N : ℝ) ^ 2 := by
          field_simp [hgR.ne']
          <;> ring
    _ = (harmonic N : ℝ) ^ 3 := by
      rw [← Finset.sum_mul]
      change (∑ g ∈ Finset.Icc 1 N, (g : ℝ)⁻¹) * (harmonic N : ℝ) ^ 2 = _
      rw [← RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
      ring

/-- Quantitative real-to-floor transfer for every positive original Selberg log-monomial. -/
theorem abs_selbergOriginalLogMonomialReal_sub_floor_le
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) {Y : ℝ} (hY : 2 ≤ Y) :
    |selbergOriginalLogMonomialReal i j Y -
        selbergOriginalLogMonomial i j ⌊Y⌋₊| ≤
      ((i + j : ℕ) : ℝ) * Real.log Y ^ (i + j - 1) *
        Real.log (Y / (⌊Y⌋₊ : ℝ)) * selbergOriginalCoeffAbsMass ⌊Y⌋₊ := by
  classical
  let N : ℕ := ⌊Y⌋₊
  let δ : ℝ := Real.log (Y / (N : ℝ))
  let R : ℝ := Real.log Y
  have hYpos : 0 < Y := by linarith
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hR : 0 ≤ R := Real.log_nonneg (by linarith)
  have hδ : 0 ≤ δ := by
    exact Real.log_nonneg ((one_le_div hNR).mpr hNle)
  let K : ℝ := ((i + j : ℕ) : ℝ) * R ^ (i + j - 1) * δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hterm : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      |selbergOriginalCoeff p.1 p.2 *
          Real.log (Y / (p.1 : ℝ)) ^ i * Real.log (Y / (p.2 : ℝ)) ^ j -
        selbergOriginalCoeff p.1 p.2 *
          (Real.log ((N : ℝ) / (p.1 : ℝ)) ^ i *
            Real.log ((N : ℝ) / (p.2 : ℝ)) ^ j)| ≤
        |selbergOriginalCoeff p.1 p.2| * K := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have hlogData : ∀ d ∈ Finset.Icc 1 N,
        |Real.log (Y / (d : ℝ))| ≤ R ∧
        |Real.log ((N : ℝ) / (d : ℝ))| ≤ R ∧
        |Real.log (Y / (d : ℝ)) - Real.log ((N : ℝ) / (d : ℝ))| ≤ δ := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hdY : (d : ℝ) ≤ Y := (by exact_mod_cast hdN : (d : ℝ) ≤ (N : ℝ)).trans hNle
      have hx0 : 0 ≤ Real.log (Y / (d : ℝ)) :=
        Real.log_nonneg ((one_le_div hdR).mpr hdY)
      have hy0 : 0 ≤ Real.log ((N : ℝ) / (d : ℝ)) :=
        Real.log_nonneg ((one_le_div hdR).mpr (by exact_mod_cast hdN))
      have hratioY : Y / (d : ℝ) ≤ Y := by
        rw [div_le_iff₀ hdR]
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
        nlinarith
      have hratioN : (N : ℝ) / (d : ℝ) ≤ Y := by
        rw [div_le_iff₀ hdR]
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
        nlinarith
      have hxR : Real.log (Y / (d : ℝ)) ≤ R :=
        Real.log_le_log (by positivity) hratioY
      have hyR : Real.log ((N : ℝ) / (d : ℝ)) ≤ R :=
        Real.log_le_log (by positivity) hratioN
      have hdiff : Real.log (Y / (d : ℝ)) -
          Real.log ((N : ℝ) / (d : ℝ)) = δ := by
        dsimp [δ]
        rw [Real.log_div hYpos.ne' hdR.ne', Real.log_div hNR.ne' hdR.ne',
          Real.log_div hYpos.ne' hNR.ne']
        ring
      rw [abs_of_nonneg hx0, abs_of_nonneg hy0, hdiff, abs_of_nonneg hδ]
      exact ⟨hxR, hyR, le_rfl⟩
    have hpow := abs_pow_mul_pow_sub_le_t1 hi hj hR hδ
      (hlogData p.1 hp1).1 (hlogData p.1 hp1).2.1
      (hlogData p.2 hp2).1 (hlogData p.2 hp2).2.1
      (hlogData p.1 hp1).2.2 (hlogData p.2 hp2).2.2
    dsimp [K]
    calc
      |selbergOriginalCoeff p.1 p.2 *
          Real.log (Y / (p.1 : ℝ)) ^ i * Real.log (Y / (p.2 : ℝ)) ^ j -
        selbergOriginalCoeff p.1 p.2 *
          (Real.log ((N : ℝ) / (p.1 : ℝ)) ^ i *
            Real.log ((N : ℝ) / (p.2 : ℝ)) ^ j)| =
          |selbergOriginalCoeff p.1 p.2| *
            |Real.log (Y / (p.1 : ℝ)) ^ i * Real.log (Y / (p.2 : ℝ)) ^ j -
              Real.log ((N : ℝ) / (p.1 : ℝ)) ^ i *
                Real.log ((N : ℝ) / (p.2 : ℝ)) ^ j| := by
            rw [← abs_mul]
            congr 1
            ring
      _ ≤ |selbergOriginalCoeff p.1 p.2| *
          (((i + j : ℕ) : ℝ) * R ^ (i + j - 1) * δ) :=
        mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
  rw [selbergOriginalLogMonomialReal, selbergOriginalLogMonomial,
    show ⌊Y⌋₊ = N from rfl, ← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        (selbergOriginalCoeff p.1 p.2 *
            Real.log (Y / (p.1 : ℝ)) ^ i * Real.log (Y / (p.2 : ℝ)) ^ j -
          selbergOriginalCoeff p.1 p.2 *
            (Real.log ((N : ℝ) / (p.1 : ℝ)) ^ i *
              Real.log ((N : ℝ) / (p.2 : ℝ)) ^ j))| ≤
        ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          |selbergOriginalCoeff p.1 p.2 *
              Real.log (Y / (p.1 : ℝ)) ^ i * Real.log (Y / (p.2 : ℝ)) ^ j -
            selbergOriginalCoeff p.1 p.2 *
              (Real.log ((N : ℝ) / (p.1 : ℝ)) ^ i *
                Real.log ((N : ℝ) / (p.2 : ℝ)) ^ j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
          |selbergOriginalCoeff p.1 p.2| * K := Finset.sum_le_sum hterm
    _ = K * selbergOriginalCoeffAbsMass N := by
      rw [← Finset.sum_mul]
      dsimp [selbergOriginalCoeffAbsMass]
      ring
    _ = ((i + j : ℕ) : ℝ) * Real.log Y ^ (i + j - 1) *
        Real.log (Y / (⌊Y⌋₊ : ℝ)) * selbergOriginalCoeffAbsMass ⌊Y⌋₊ := by
      rfl

/-- The harmonic-cubic endpoint mass is still killed by the exponentially small floor
displacement.  Hence every positive real-cutoff monomial has the same normalization as its
integer-floor counterpart. -/
theorem tendsto_selbergOriginalLogMonomialReal_sub_floor_div_log_pow_zero
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Tendsto (fun Y : ℝ =>
      (selbergOriginalLogMonomialReal i j Y -
        selbergOriginalLogMonomial i j ⌊Y⌋₊) /
          Real.log Y ^ (i + j - 1)) atTop (𝓝 0) := by
  let C : ℝ := ((i + j : ℕ) : ℝ)
  have hgap0 := tendsto_log_div_natFloor_mul_log_pow_zero 0
  have hgap1 := tendsto_log_div_natFloor_mul_log_pow_zero 1
  have hgap2 := tendsto_log_div_natFloor_mul_log_pow_zero 2
  have hgap3 := tendsto_log_div_natFloor_mul_log_pow_zero 3
  have hpoly : Tendsto (fun Y : ℝ =>
      C * Real.log (Y / (⌊Y⌋₊ : ℝ)) * (1 + Real.log Y) ^ 3)
      atTop (𝓝 0) := by
    have hsum := hgap0.add ((hgap1.const_mul 3).add
      ((hgap2.const_mul 3).add hgap3))
    have hscaled := hsum.const_mul C
    simpa only [zero_add, mul_zero] using hscaled.congr'
      (Eventually.of_forall fun Y => by ring)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun Y => norm_nonneg _) ?_
    (by simpa only [norm_zero] using hpoly.norm)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  let N : ℕ := ⌊Y⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNle : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  have hdelta : 0 ≤ Real.log (Y / (N : ℝ)) :=
    Real.log_nonneg ((one_le_div hNR).mpr hNle)
  have hmass := selbergOriginalCoeffAbsMass_le_harmonic_cube N
  have hharm : (harmonic N : ℝ) ≤ 1 + Real.log Y := by
    calc
      (harmonic N : ℝ) = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) :=
        (sum_Icc_one_div_eq_harmonic N).symm
      _ ≤ 1 + Real.log N := sum_Icc_one_div_le_one_add_log N
      _ ≤ 1 + Real.log Y := by
        linarith [Real.log_le_log hNR hNle]
  have hharm0 : (0 : ℝ) ≤ (harmonic N : ℝ) := by
    rw [RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
    positivity
  have hlogOne : 0 ≤ 1 + Real.log Y := by linarith
  have hmass' : selbergOriginalCoeffAbsMass N ≤ (1 + Real.log Y) ^ 3 :=
    hmass.trans (by gcongr)
  have hbound := abs_selbergOriginalLogMonomialReal_sub_floor_le hi hj hY
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hlog (i + j - 1))]
  calc
    |selbergOriginalLogMonomialReal i j Y -
        selbergOriginalLogMonomial i j ⌊Y⌋₊| /
          Real.log Y ^ (i + j - 1) ≤
      (C * Real.log Y ^ (i + j - 1) *
        Real.log (Y / (N : ℝ)) * selbergOriginalCoeffAbsMass N) /
          Real.log Y ^ (i + j - 1) := by
        exact div_le_div_of_nonneg_right (by simpa [C, N] using hbound)
          (pow_pos hlog (i + j - 1)).le
    _ = C * Real.log (Y / (N : ℝ)) * selbergOriginalCoeffAbsMass N := by
      field_simp [hlog.ne']
    _ ≤ C * Real.log (Y / (N : ℝ)) * (1 + Real.log Y) ^ 3 := by
      exact mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ ≤ ‖C * Real.log (Y / (⌊Y⌋₊ : ℝ)) * (1 + Real.log Y) ^ 3‖ := by
      rw [show N = ⌊Y⌋₊ from rfl]
      rw [Real.norm_eq_abs]
      exact le_abs_self _

/-- Graham's ordinary Selberg law survives every real cutoff. -/
theorem tendsto_selbergOriginalLogMonomialReal_div_log_pow
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Tendsto (fun Y : ℝ =>
      selbergOriginalLogMonomialReal i j Y /
        Real.log Y ^ (i + j - 1)) atTop
      (𝓝 (((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1))) := by
  let p : ℕ := i + j - 1
  let c : ℝ := ((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1)
  have hfloor : Tendsto (fun Y : ℝ => ⌊Y⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hinteger : Tendsto (fun Y : ℝ =>
      selbergOriginalLogMonomial i j ⌊Y⌋₊ /
        Real.log (⌊Y⌋₊ : ℝ) ^ p) atTop (𝓝 c) := by
    have hcomp :=
      (tendsto_selbergOriginalLogMonomial_div_log_pow hi hj).comp hfloor
    have hcomp' : Tendsto (fun Y : ℝ =>
        selbergOriginalLogMonomial i j ⌊Y⌋₊ /
          Real.log (⌊Y⌋₊ : ℝ) ^ (i + j - 1)) atTop
        (𝓝 (((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1))) :=
      hcomp.congr' (Eventually.of_forall fun Y => by rfl)
    simpa only [p, c] using hcomp'
  have hscale : Tendsto (fun Y : ℝ =>
      (Real.log (⌊Y⌋₊ : ℝ) / Real.log Y) ^ p) atTop (𝓝 1) := by
    simpa only [one_pow] using tendsto_log_natFloor_div_log_one.pow p
  have hmain : Tendsto (fun Y : ℝ =>
      selbergOriginalLogMonomial i j ⌊Y⌋₊ / Real.log Y ^ p)
      atTop (𝓝 c) := by
    have hprod := hinteger.mul hscale
    simpa only [mul_one] using hprod.congr' (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
      have hlogY : Real.log Y ≠ 0 := (Real.log_pos (by linarith)).ne'
      have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
      have hlogN : Real.log (⌊Y⌋₊ : ℝ) ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hfloor2)).ne'
      rw [div_pow]
      field_simp [hlogY, hlogN])
  have herr :=
    tendsto_selbergOriginalLogMonomialReal_sub_floor_div_log_pow_zero hi hj
  have hadd := hmain.add herr
  rw [add_zero] at hadd
  simpa only [p, c] using hadd.congr' (Eventually.of_forall fun Y => by ring)

/-- Logarithmic-ray form of the real-cutoff Selberg law. -/
theorem tendsto_selbergOriginalLogMonomialReal_exp_div_pow
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Tendsto (fun u : ℝ =>
      selbergOriginalLogMonomialReal i j (Real.exp u) /
        u ^ (i + j - 1)) atTop
      (𝓝 (((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1))) := by
  have hcomp := (tendsto_selbergOriginalLogMonomialReal_div_log_pow hi hj).comp
    Real.tendsto_exp_atTop
  exact hcomp.congr' (Eventually.of_forall fun u => by
    simp only [Function.comp_apply, Real.log_exp])

/-- On every logarithmic layer below the ambient cutoff, the finite max-profile is exactly the
universal real-cutoff Selberg monomial. -/
theorem selbergOriginalLogCutoffMonomial_eq_real_exp
    {i j M : ℕ} (hi : 0 < i) (hj : 0 < j) (hM : 0 < M)
    {u : ℝ} (hu0 : 0 ≤ u) (huM : u ≤ Real.log M) :
    selbergOriginalLogCutoffMonomial i j M u =
      selbergOriginalLogMonomialReal i j (Real.exp u) := by
  classical
  let N : ℕ := ⌊Real.exp u⌋₊
  let S : Finset (ℕ × ℕ) := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  let T : Finset (ℕ × ℕ) := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hexpM : Real.exp u ≤ (M : ℝ) := by
    calc
      Real.exp u ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr huM
      _ = (M : ℝ) := Real.exp_log hMposR
  have hNM : N ≤ M := by
    exact_mod_cast (Nat.floor_le (Real.exp_pos u).le).trans hexpM
  have hsubset : T ⊆ S := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp1).1,
        (Finset.mem_Icc.mp hp1).2.trans hNM⟩,
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp2).1,
        (Finset.mem_Icc.mp hp2).2.trans hNM⟩⟩
  have hzero : ∀ p ∈ S, p ∉ T →
      selbergOriginalCoeff p.1 p.2 *
        (max (u - Real.log p.1) 0) ^ i *
          (max (u - Real.log p.2) 0) ^ j = 0 := by
    intro p hpS hpT
    obtain ⟨hp1S, hp2S⟩ := Finset.mem_product.mp hpS
    have hnot : ¬ (p.1 ≤ N ∧ p.2 ≤ N) := by
      intro hboth
      apply hpT
      exact Finset.mem_product.mpr ⟨
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp1S).1, hboth.1⟩,
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp2S).1, hboth.2⟩⟩
    rcases not_and_or.mp hnot with hp1 | hp2
    · have hNp : N + 1 ≤ p.1 := by omega
      have hexplt : Real.exp u < (p.1 : ℝ) := by
        calc
          Real.exp u < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp u)
          _ ≤ (p.1 : ℝ) := by exact_mod_cast hNp
      have hlog : u - Real.log p.1 ≤ 0 := by
        rw [sub_nonpos, ← Real.log_exp u]
        exact Real.log_le_log (Real.exp_pos u) hexplt.le
      simp [max_eq_right hlog, hi.ne']
    · have hNp : N + 1 ≤ p.2 := by omega
      have hexplt : Real.exp u < (p.2 : ℝ) := by
        calc
          Real.exp u < (N : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp u)
          _ ≤ (p.2 : ℝ) := by exact_mod_cast hNp
      have hlog : u - Real.log p.2 ≤ 0 := by
        rw [sub_nonpos, ← Real.log_exp u]
        exact Real.log_le_log (Real.exp_pos u) hexplt.le
      simp [max_eq_right hlog, hj.ne']
  rw [selbergOriginalLogCutoffMonomial, selbergOriginalLogMonomialReal,
    show ⌊Real.exp u⌋₊ = N from rfl]
  change (∑ p ∈ S, selbergOriginalCoeff p.1 p.2 *
      (max (u - Real.log p.1) 0) ^ i *
        (max (u - Real.log p.2) 0) ^ j) = _
  rw [← Finset.sum_subset hsubset hzero]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hlogData : ∀ d ∈ Finset.Icc 1 N,
      max (u - Real.log d) 0 = Real.log (Real.exp u / (d : ℝ)) := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdexp : (d : ℝ) ≤ Real.exp u :=
      (by exact_mod_cast hdN : (d : ℝ) ≤ (N : ℝ)).trans
        (Nat.floor_le (Real.exp_pos u).le)
    have hnonneg : 0 ≤ u - Real.log d := by
      rw [sub_nonneg, ← Real.log_exp u]
      exact Real.log_le_log hdR hdexp
    rw [max_eq_left hnonneg, Real.log_div (Real.exp_pos u).ne' hdR.ne',
      Real.log_exp]
  rw [hlogData p.1 hp1, hlogData p.2 hp2]

/-- Global polynomial envelope for the continuous logarithmic profile.  It is deliberately crude
but independent of every ambient cutoff, which is exactly what dominated convergence needs. -/
theorem abs_selbergOriginalLogMonomialReal_exp_le
    (i j : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |selbergOriginalLogMonomialReal i j (Real.exp u)| ≤
      (1 + u) ^ (i + j + 3) := by
  classical
  let N : ℕ := ⌊Real.exp u⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using Real.one_le_exp hu)
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hNexp : (N : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hlogN : Real.log N ≤ u := by
    rw [← Real.log_exp u]
    exact Real.log_le_log hNR hNexp
  have huOne : 0 ≤ 1 + u := by linarith
  have hharm : (harmonic N : ℝ) ≤ 1 + u := by
    calc
      (harmonic N : ℝ) = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) :=
        (sum_Icc_one_div_eq_harmonic N).symm
      _ ≤ 1 + Real.log N := sum_Icc_one_div_le_one_add_log N
      _ ≤ 1 + u := by linarith
  have hharm0 : (0 : ℝ) ≤ (harmonic N : ℝ) := by
    rw [RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum]
    positivity
  have hmass : selbergOriginalCoeffAbsMass N ≤ (1 + u) ^ 3 :=
    (selbergOriginalCoeffAbsMass_le_harmonic_cube N).trans (by gcongr)
  have hterm : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      |selbergOriginalCoeff p.1 p.2 *
        Real.log (Real.exp u / (p.1 : ℝ)) ^ i *
          Real.log (Real.exp u / (p.2 : ℝ)) ^ j| ≤
        |selbergOriginalCoeff p.1 p.2| * u ^ (i + j) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have hlog : ∀ d ∈ Finset.Icc 1 N,
        0 ≤ Real.log (Real.exp u / (d : ℝ)) ∧
          Real.log (Real.exp u / (d : ℝ)) ≤ u := by
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hdexp : (d : ℝ) ≤ Real.exp u :=
        (by exact_mod_cast hdN : (d : ℝ) ≤ (N : ℝ)).trans hNexp
      have hratio : (1 : ℝ) ≤ Real.exp u / (d : ℝ) :=
        (one_le_div hdR).mpr hdexp
      have hratio_le : Real.exp u / (d : ℝ) ≤ Real.exp u := by
        rw [div_le_iff₀ hdR]
        have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
        nlinarith [Real.exp_pos u]
      exact ⟨Real.log_nonneg hratio,
        by simpa only [Real.log_exp] using
          Real.log_le_log (by positivity) hratio_le⟩
    rw [abs_mul, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (hlog p.1 hp1).1, abs_of_nonneg (hlog p.2 hp2).1]
    have hxpow : Real.log (Real.exp u / (p.1 : ℝ)) ^ i ≤ u ^ i :=
      pow_le_pow_left₀ (hlog p.1 hp1).1 (hlog p.1 hp1).2 i
    have hypow : Real.log (Real.exp u / (p.2 : ℝ)) ^ j ≤ u ^ j :=
      pow_le_pow_left₀ (hlog p.2 hp2).1 (hlog p.2 hp2).2 j
    calc
      |selbergOriginalCoeff p.1 p.2| *
          Real.log (Real.exp u / (p.1 : ℝ)) ^ i *
            Real.log (Real.exp u / (p.2 : ℝ)) ^ j =
        |selbergOriginalCoeff p.1 p.2| *
          (Real.log (Real.exp u / (p.1 : ℝ)) ^ i *
            Real.log (Real.exp u / (p.2 : ℝ)) ^ j) := by ring
      _ ≤ |selbergOriginalCoeff p.1 p.2| * (u ^ i * u ^ j) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hxpow hypow (pow_nonneg (hlog p.2 hp2).1 j)
            (pow_nonneg hu i)) (abs_nonneg _)
      _ = |selbergOriginalCoeff p.1 p.2| * u ^ (i + j) := by rw [pow_add]
  rw [selbergOriginalLogMonomialReal, show ⌊Real.exp u⌋₊ = N from rfl]
  calc
    |∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        selbergOriginalCoeff p.1 p.2 *
          Real.log (Real.exp u / (p.1 : ℝ)) ^ i *
            Real.log (Real.exp u / (p.2 : ℝ)) ^ j| ≤
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        |selbergOriginalCoeff p.1 p.2 *
          Real.log (Real.exp u / (p.1 : ℝ)) ^ i *
            Real.log (Real.exp u / (p.2 : ℝ)) ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        |selbergOriginalCoeff p.1 p.2| * u ^ (i + j) :=
      Finset.sum_le_sum hterm
    _ = selbergOriginalCoeffAbsMass N * u ^ (i + j) := by
      rw [← Finset.sum_mul]
      rfl
    _ ≤ (1 + u) ^ 3 * (1 + u) ^ (i + j) := by
      exact mul_le_mul hmass (by gcongr; linarith)
        (pow_nonneg hu (i + j)) (pow_nonneg huOne 3)
    _ = (1 + u) ^ (i + j + 3) := by
      rw [← pow_add]
      congr 1
      omega

/-- Although defined with a moving natural floor, the logarithmic profile is continuous on every
compact positive interval: each entering coefficient vanishes to positive order at its endpoint. -/
theorem continuousOn_selbergOriginalLogMonomialReal_exp
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) {H : ℝ} (hH : 0 ≤ H) :
    ContinuousOn (fun u : ℝ =>
      selbergOriginalLogMonomialReal i j (Real.exp u)) (Set.Icc 0 H) := by
  let M : ℕ := ⌊Real.exp H⌋₊ + 1
  have hM : 0 < M := by dsimp [M]; omega
  have hcont : Continuous (fun u : ℝ =>
      selbergOriginalLogCutoffMonomial i j M u) := by
    simp only [selbergOriginalLogCutoffMonomial]
    fun_prop
  refine hcont.continuousOn.congr ?_
  intro u hu
  have hu0 : 0 ≤ u := hu.1
  have huexp : Real.exp u ≤ Real.exp H := Real.exp_le_exp.mpr hu.2
  have hexpM : Real.exp H < (M : ℝ) := by
    dsimp [M]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.exp H)
  have huM : u ≤ Real.log M := by
    rw [← Real.log_exp u]
    exact Real.log_le_log (Real.exp_pos u) (huexp.trans hexpM.le)
  exact (selbergOriginalLogCutoffMonomial_eq_real_exp hi hj hM hu0 huM).symm

/-- Dimensionless beta-convolution law for every positive Selberg log-monomial.  The proof uses
the new floor-transfer theorem, removable floor jumps, and a cutoff-independent majorant. -/
theorem tendsto_integral_selbergOriginalLogMonomialReal_exp_scaled
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (q : ℕ) :
    let p := i + j - 1
    let c := ((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1)
    Tendsto (fun H : ℝ =>
      ∫ x in (0 : ℝ)..1,
        (1 - x) ^ q *
          (selbergOriginalLogMonomialReal i j (Real.exp (H * x)) / H ^ p))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, (1 - x) ^ q * (c * x ^ p))) := by
  dsimp only
  let p : ℕ := i + j - 1
  let c : ℝ := ((i : ℝ) * (j : ℝ)) / ((i : ℝ) + (j : ℝ) - 1)
  let F : ℝ → ℝ := fun u => selbergOriginalLogMonomialReal i j (Real.exp u)
  have hp : 0 < p := by dsimp [p]; omega
  have hratio : Tendsto (fun u : ℝ => F u / u ^ p) atTop (𝓝 c) := by
    simpa only [F, p, c] using
      tendsto_selbergOriginalLogMonomialReal_exp_div_pow hi hj
  obtain ⟨A₀, hA₀⟩ := (Metric.tendsto_atTop.mp hratio) 1 (by norm_num)
  let A : ℝ := max A₀ 1
  let K : ℝ := |c| + 1
  let C : ℝ := (1 + A) ^ (i + j + 3)
  let B : ℝ := max K C
  have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hB0 : 0 ≤ B := le_trans hK0 (le_max_left _ _)
  have htail : ∀ u : ℝ, A ≤ u → |F u / u ^ p| ≤ K := by
    intro u hu
    have hdist := hA₀ u ((le_max_left A₀ 1).trans hu)
    rw [Real.dist_eq] at hdist
    dsimp [K]
    calc
      |F u / u ^ p| = |(F u / u ^ p - c) + c| := by congr 1 <;> ring
      _ ≤ |F u / u ^ p - c| + |c| := abs_add_le _ _
      _ ≤ |c| + 1 := by linarith
  let G : ℝ → ℝ → ℝ := fun H x =>
    (1 - x) ^ q * (F (H * x) / H ^ p)
  let g : ℝ → ℝ := fun x => (1 - x) ^ q * (c * x ^ p)
  have hmeas : ∀ᶠ H : ℝ in atTop,
      AEStronglyMeasurable (G H) (volume.restrict (Set.uIoc 0 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    have hH0 : 0 ≤ H := by linarith
    have hprofile := continuousOn_selbergOriginalLogMonomialReal_exp hi hj hH0
    have hmap : Set.MapsTo (fun x : ℝ => H * x) (Set.Icc 0 1) (Set.Icc 0 H) := by
      intro x hx
      exact ⟨mul_nonneg hH0 hx.1, mul_le_of_le_one_right hH0 hx.2⟩
    have hcomp : ContinuousOn (fun x : ℝ => F (H * x)) (Set.Icc 0 1) := by
      have hpcont : ContinuousOn F (Set.Icc 0 H) := by
        simpa only [F] using hprofile
      exact hpcont.comp (continuous_const.mul continuous_id).continuousOn hmap
    have hGcont : ContinuousOn (G H) (Set.Icc 0 1) := by
      dsimp only [G]
      have hw : Continuous (fun x : ℝ => (1 - x) ^ q) := by fun_prop
      have hquot : ContinuousOn (fun x : ℝ => F (H * x) / H ^ p)
          (Set.Icc 0 1) := by
        have hm := hcomp.mul
          (continuous_const : Continuous (fun _ : ℝ => (H ^ p)⁻¹)).continuousOn
        convert hm using 1
        funext x
        simp only [Pi.mul_apply, div_eq_mul_inv]
      exact hw.continuousOn.mul hquot
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hGcont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᶠ H : ℝ in atTop, ∀ᵐ x : ℝ ∂volume,
      x ∈ Set.uIoc (0 : ℝ) 1 → ‖G H x‖ ≤ B := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
    filter_upwards [] with x
    intro hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 ≤ x := hx.1.le
    have hx1 : x ≤ 1 := hx.2
    have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
    have hu0 : 0 ≤ H * x := mul_nonneg hHpos.le hx0
    have hweight0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hweight : |(1 - x) ^ q| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg hweight0]
      exact pow_le_one₀ hweight0 (by linarith)
    have hcore : |F (H * x) / H ^ p| ≤ B := by
      by_cases htailCase : A ≤ H * x
      · have hxpos : 0 < x := by
          by_contra hxz
          have : x = 0 := le_antisymm (le_of_not_gt hxz) hx0
          rw [this, mul_zero] at htailCase
          linarith
        have hratioBound := htail (H * x) htailCase
        have heq : F (H * x) / H ^ p =
            (F (H * x) / (H * x) ^ p) * x ^ p := by
          field_simp [hHpos.ne', hxpos.ne']
          <;> ring
        rw [heq, abs_mul]
        calc
          |F (H * x) / (H * x) ^ p| * |x ^ p| ≤ K * 1 := by
            rw [abs_pow, abs_of_nonneg hx0]
            exact mul_le_mul hratioBound (pow_le_one₀ hx0 hx1)
              (pow_nonneg hx0 p) hK0
          _ ≤ B := by simpa only [mul_one, B] using le_max_left K C
      · have huA : H * x ≤ A := le_of_not_ge htailCase
        have hprofileBound := abs_selbergOriginalLogMonomialReal_exp_le i j hu0
        have hFA : |F (H * x)| ≤ C := by
          dsimp [F, C]
          exact hprofileBound.trans (pow_le_pow_left₀
            (by linarith : 0 ≤ 1 + H * x) (by linarith : 1 + H * x ≤ 1 + A)
            (i + j + 3))
        rw [abs_div, abs_of_pos (pow_pos hHpos p)]
        calc
          |F (H * x)| / H ^ p ≤ C / H ^ p :=
            div_le_div_of_nonneg_right hFA (pow_pos hHpos p).le
          _ ≤ C := by
            have hpow1 : (1 : ℝ) ≤ H ^ p := by exact one_le_pow₀ (by linarith)
            exact (div_le_iff₀ (pow_pos hHpos p)).2 (by nlinarith [hC0])
          _ ≤ B := le_max_right K C
    dsimp only [G]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |(1 - x) ^ q| * |F (H * x) / H ^ p| ≤ 1 * B :=
        mul_le_mul hweight hcore (abs_nonneg _) (by norm_num)
      _ = B := one_mul B
  have hlim : ∀ᵐ x : ℝ ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Tendsto (fun H : ℝ => G H x) atTop (𝓝 (g x)) := by
    filter_upwards [] with x
    intro hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hxpos : 0 < x := hx.1
    have hx0 : 0 ≤ x := hxpos.le
    have hxscale : Tendsto (fun H : ℝ => H * x) atTop atTop :=
      tendsto_id.atTop_mul_const hxpos
    have hratioX := hratio.comp hxscale
    have hscaled := hratioX.mul_const (x ^ p)
    have hcore : Tendsto (fun H : ℝ => F (H * x) / H ^ p)
        atTop (𝓝 (c * x ^ p)) := by
      refine hscaled.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
      have heq : F (H * x) / H ^ p =
          (F (H * x) / (H * x) ^ p) * x ^ p := by
        field_simp [hH.ne', hxpos.ne']
        <;> ring
      exact heq.symm
    have hweighted := hcore.const_mul ((1 - x) ^ q)
    simpa only [G, g] using hweighted
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => B) hmeas hbound (continuous_const.intervalIntegrable 0 1) hlim
  simpa only [G, g, F, p, c] using hDCT

private theorem integral_beta_three_zero_four_thirds :
    (∫ x in (0 : ℝ)..1, (1 - x) ^ 0 * ((4 / 3 : ℝ) * x ^ 3)) = 1 / 3 := by
  norm_num [integral_pow]

private theorem integral_beta_two_one_one :
    (∫ x in (0 : ℝ)..1, (1 - x) ^ 1 * ((1 : ℝ) * x ^ 2)) = 1 / 12 := by
  have hfun : (fun x : ℝ => (1 - x) ^ 1 * ((1 : ℝ) * x ^ 2)) =
      fun x => x ^ 2 - x ^ 3 := by funext x; ring
  rw [hfun, intervalIntegral.integral_sub]
  · norm_num [integral_pow]
  · exact (by fun_prop : Continuous (fun x : ℝ => x ^ 2)).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous (fun x : ℝ => x ^ 3)).intervalIntegrable 0 1

private theorem integral_beta_one_two_one :
    (∫ x in (0 : ℝ)..1, (1 - x) ^ 2 * ((1 : ℝ) * x ^ 1)) = 1 / 12 := by
  have hfun : (fun x : ℝ => (1 - x) ^ 2 * ((1 : ℝ) * x ^ 1)) =
      fun x => x - 2 * x ^ 2 + x ^ 3 := by funext x; ring
  rw [hfun, intervalIntegral.integral_add, intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop

theorem tendsto_integral_selbergOriginalLogMonomialReal_exp_two_two_scaled :
    Tendsto (fun H : ℝ =>
      ∫ x in (0 : ℝ)..1,
        (1 - x) ^ 0 *
          (selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3))
      atTop (𝓝 (1 / 3 : ℝ)) := by
  have h := tendsto_integral_selbergOriginalLogMonomialReal_exp_scaled
    (i := 2) (j := 2) (by norm_num) (by norm_num) 0
  norm_num at h
  simpa using h

theorem tendsto_integral_selbergOriginalLogMonomialReal_exp_one_two_scaled :
    Tendsto (fun H : ℝ =>
      ∫ x in (0 : ℝ)..1,
        (1 - x) ^ 1 *
          (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2))
      atTop (𝓝 (1 / 12 : ℝ)) := by
  have h := tendsto_integral_selbergOriginalLogMonomialReal_exp_scaled
    (i := 1) (j := 2) (by norm_num) (by norm_num) 1
  norm_num at h
  have hval : (∫ x in (0 : ℝ)..1, (1 - x) * x ^ 2) = 1 / 12 := by
    simpa using integral_beta_two_one_one
  rw [hval] at h
  simpa using h

theorem tendsto_integral_selbergOriginalLogMonomialReal_exp_one_one_scaled :
    Tendsto (fun H : ℝ =>
      ∫ x in (0 : ℝ)..1,
        (1 - x) ^ 2 *
          (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H ^ 1))
      atTop (𝓝 (1 / 12 : ℝ)) := by
  have h := tendsto_integral_selbergOriginalLogMonomialReal_exp_scaled
    (i := 1) (j := 1) (by norm_num) (by norm_num) 2
  norm_num at h
  have hval : (∫ x in (0 : ℝ)..1, (1 - x) ^ 2 * x) = 1 / 12 := by
    simpa using integral_beta_one_two_one
  rw [hval] at h
  simpa using h

/-- The three scaled Abel channels sum to the new coefficient `7/12`. -/
theorem tendsto_selbergOriginalTunedMinLogAbelScaled :
    Tendsto (fun H : ℝ =>
      (∫ x in (0 : ℝ)..1,
        selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3) +
      2 * (∫ x in (0 : ℝ)..1,
        (1 - x) *
          (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2)) +
      (∫ x in (0 : ℝ)..1,
        (1 - x) ^ 2 *
          (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H)))
      atTop (𝓝 (7 / 12 : ℝ)) := by
  have h22 := tendsto_integral_selbergOriginalLogMonomialReal_exp_two_two_scaled
  have h12 := tendsto_integral_selbergOriginalLogMonomialReal_exp_one_two_scaled
  have h11 := tendsto_integral_selbergOriginalLogMonomialReal_exp_one_one_scaled
  have hsum := h22.add ((h12.const_mul 2).add h11)
  norm_num at hsum ⊢
  simpa [mul_assoc, add_assoc] using hsum

/-- Single-integral form of the scaled `7/12` law. -/
theorem tendsto_integral_selbergOriginalTunedMinLogAbelScaled :
    Tendsto (fun H : ℝ =>
      ∫ x in (0 : ℝ)..1,
        selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3 +
          2 * (1 - x) *
            (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2) +
          (1 - x) ^ 2 *
            (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H))
      atTop (𝓝 (7 / 12 : ℝ)) := by
  refine tendsto_selbergOriginalTunedMinLogAbelScaled.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  have hH0 : 0 ≤ H := by linarith
  have hmap : Set.MapsTo (fun x : ℝ => H * x) (Set.Icc 0 1) (Set.Icc 0 H) := by
    intro x hx
    exact ⟨mul_nonneg hH0 hx.1, mul_le_of_le_one_right hH0 hx.2⟩
  have hc (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
      ContinuousOn (fun x : ℝ =>
        selbergOriginalLogMonomialReal i j (Real.exp (H * x))) (Set.Icc 0 1) :=
    (continuousOn_selbergOriginalLogMonomialReal_exp hi hj hH0).comp
      (continuous_const.mul continuous_id).continuousOn hmap
  have hquot (i j k : ℕ) (hi : 0 < i) (hj : 0 < j) :
      ContinuousOn (fun x : ℝ =>
        selbergOriginalLogMonomialReal i j (Real.exp (H * x)) / H ^ k)
        (Set.Icc 0 1) := by
    have hm := (hc i j hi hj).mul
      (continuous_const : Continuous (fun _ : ℝ => (H ^ k)⁻¹)).continuousOn
    convert hm using 1
    funext x
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hc22 : ContinuousOn (fun x : ℝ =>
      selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3)
      (Set.Icc 0 1) := hquot 2 2 3 (by norm_num) (by norm_num)
  have hc12 : ContinuousOn (fun x : ℝ =>
      (1 - x) *
        (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2))
      (Set.Icc 0 1) := by
    exact (continuous_const.sub continuous_id).continuousOn.mul
      (hquot 1 2 2 (by norm_num) (by norm_num))
  have hc11 : ContinuousOn (fun x : ℝ =>
      (1 - x) ^ 2 *
        (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H))
      (Set.Icc 0 1) := by
    have hbase : Continuous (fun x : ℝ => (1 - x) ^ 2) := by fun_prop
    convert hbase.continuousOn.mul (hquot 1 1 1 (by norm_num) (by norm_num)) using 1
    funext x
    simp only [Pi.mul_apply, pow_one]
  have hi22 : IntervalIntegrable (fun x : ℝ =>
      selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc22
  have hi12 : IntervalIntegrable (fun x : ℝ =>
      (1 - x) *
        (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc12
  have hi11 : IntervalIntegrable (fun x : ℝ =>
      (1 - x) ^ 2 *
        (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc11
  symm
  have hfun : (fun x : ℝ =>
      selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3 +
        2 * (1 - x) *
          (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2) +
        (1 - x) ^ 2 *
          (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H)) =
      fun x =>
        selbergOriginalLogMonomialReal 2 2 (Real.exp (H * x)) / H ^ 3 +
          2 * ((1 - x) *
            (selbergOriginalLogMonomialReal 1 2 (Real.exp (H * x)) / H ^ 2)) +
          (1 - x) ^ 2 *
            (selbergOriginalLogMonomialReal 1 1 (Real.exp (H * x)) / H) := by
    funext x
    ring
  rw [hfun]
  rw [intervalIntegral.integral_add (hi22.add (hi12.const_mul 2)) hi11,
    intervalIntegral.integral_add hi22 (hi12.const_mul 2),
    intervalIntegral.integral_const_mul]

/-- Exact dimensionless rescaling of the literal tuned minimum-log remainder. -/
theorem selbergOriginalTunedMinLogRemainder_div_log_four_eq_AbelScaled
    {M : ℕ} (hM : 2 ≤ M) :
    selbergOriginalTunedMinLogRemainder M / Real.log M ^ 4 =
      ∫ x in (0 : ℝ)..1,
        selbergOriginalLogMonomialReal 2 2
            (Real.exp (Real.log M * x)) / Real.log M ^ 3 +
          2 * (1 - x) *
            (selbergOriginalLogMonomialReal 1 2
              (Real.exp (Real.log M * x)) / Real.log M ^ 2) +
          (1 - x) ^ 2 *
            (selbergOriginalLogMonomialReal 1 1
              (Real.exp (Real.log M * x)) / Real.log M) := by
  let H : ℝ := Real.log M
  let A : ℝ → ℝ := fun u =>
    selbergOriginalLogCutoffMonomial 2 2 M u +
      2 * (H - u) * selbergOriginalLogCutoffMonomial 1 2 M u +
        (H - u) ^ 2 * selbergOriginalLogCutoffMonomial 1 1 M u
  have hMpos : 0 < M := by omega
  have hH : 0 < H := Real.log_pos (by exact_mod_cast hM)
  have hcutoff (i j : ℕ) : Continuous (fun u : ℝ =>
      selbergOriginalLogCutoffMonomial i j M u) := by
    simp only [selbergOriginalLogCutoffMonomial]
    fun_prop
  have hAcont : Continuous A := by
    dsimp only [A]
    have hlin : Continuous (fun u : ℝ => H - u) := continuous_const.sub continuous_id
    have h2 : Continuous (fun u : ℝ =>
        2 * (H - u) * selbergOriginalLogCutoffMonomial 1 2 M u) :=
      (hlin.const_mul 2).mul (hcutoff 1 2)
    have h3 : Continuous (fun u : ℝ =>
        (H - u) ^ 2 * selbergOriginalLogCutoffMonomial 1 1 M u) :=
      (hlin.pow 2).mul (hcutoff 1 1)
    exact ((hcutoff 2 2).add h2).add h3
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => H * x) (f' := fun _ : ℝ => H) (g := A)
    (fun x hx => hasDerivAt_const_mul H)
    continuous_const.continuousOn hAcont
  have hsub' : (∫ x in (0 : ℝ)..1, A (H * x) * H) =
      ∫ u in (0 : ℝ)..H, A u := by
    simpa only [Function.comp_apply, mul_zero, mul_one] using hsub
  rw [selbergOriginalTunedMinLogRemainder_eq_ordinaryAbel hMpos]
  change (∫ u in (0 : ℝ)..H, A u) / H ^ 4 = _
  rw [← hsub']
  rw [div_eq_mul_inv, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hu0 : 0 ≤ H * x := mul_nonneg hH.le hx0
  have huH : H * x ≤ H := mul_le_of_le_one_right hH.le hx1
  have h22 := selbergOriginalLogCutoffMonomial_eq_real_exp
    (i := 2) (j := 2) (M := M) (by norm_num) (by norm_num) hMpos hu0 huH
  have h12 := selbergOriginalLogCutoffMonomial_eq_real_exp
    (i := 1) (j := 2) (M := M) (by norm_num) (by norm_num) hMpos hu0 huH
  have h11 := selbergOriginalLogCutoffMonomial_eq_real_exp
    (i := 1) (j := 1) (M := M) (by norm_num) (by norm_num) hMpos hu0 huH
  dsimp only [A]
  rw [h22, h12, h11]
  dsimp only [H]
  field_simp [hH.ne']

/-- **Exact leading law of the tuned minimum-log remainder.** -/
theorem tendsto_selbergOriginalTunedMinLogRemainder_div_log_four_seven_twelfths :
    Tendsto (fun M : ℕ =>
      selbergOriginalTunedMinLogRemainder M / Real.log M ^ 4)
      atTop (𝓝 (7 / 12 : ℝ)) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcomp := tendsto_integral_selbergOriginalTunedMinLogAbelScaled.comp hlog
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  exact (selbergOriginalTunedMinLogRemainder_div_log_four_eq_AbelScaled hM).symm

/-- Reciprocal detector tuning collapses the whole ordinary included sector to five normalized
Graham monomials with a common factor `ρ²`. -/
theorem selbergOriginalIncludedOrdinaryEnergy_normalized_eq
    {rho : ℝ} (hrho : rho ≠ 0) {M : ℕ} (hM : 2 ≤ M) :
    selbergOriginalIncludedOrdinaryEnergy
        (rho / Real.log M) (Real.log M / rho) M / Real.log M ^ 2 =
      rho ^ 2 *
        ((1 / 3 : ℝ) *
            (selbergOriginalLogMonomial 1 1 M / Real.log M) -
          selbergOriginalLogMonomial 1 2 M / Real.log M ^ 2 +
          (1 / 3 : ℝ) *
            (selbergOriginalLogMonomial 1 4 M / Real.log M ^ 4) -
          selbergOriginalLogMonomial 2 3 M / Real.log M ^ 4 +
          selbergOriginalLogMonomial 2 2 M / Real.log M ^ 3) := by
  have hlog : Real.log M ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  unfold selbergOriginalIncludedOrdinaryEnergy
  field_simp [hlog, hrho]
  ring

/-- Universal ordinary-sector law at reciprocal tuning: its normalized limit is `-ρ²/2`. -/
theorem tendsto_selbergOriginalIncludedOrdinaryEnergy_normalized_of_rho
    (rho : ℝ) (hrho : rho ≠ 0) :
    Tendsto (fun M : ℕ =>
      selbergOriginalIncludedOrdinaryEnergy
        (rho / Real.log M) (Real.log M / rho) M / Real.log M ^ 2)
      atTop (𝓝 (-(rho ^ 2) / 2)) := by
  have h11 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have h12 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 2) (by norm_num) (by norm_num)
  have h14 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 4) (by norm_num) (by norm_num)
  have h23 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 3) (by norm_num) (by norm_num)
  have h22 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 2) (by norm_num) (by norm_num)
  norm_num at h11 h12 h14 h23 h22
  have hcomb0 := (((h11.const_mul (1 / 3 : ℝ)).sub h12).add
    (h14.const_mul (1 / 3 : ℝ))).sub h23
  have hcomb := hcomb0.add h22
  have hscaled := hcomb.const_mul (rho ^ 2)
  norm_num at hscaled
  have hscaled' : Tendsto (fun M : ℕ =>
      rho ^ 2 *
        ((1 / 3 : ℝ) * (selbergOriginalLogMonomial 1 1 M / Real.log M) -
          selbergOriginalLogMonomial 1 2 M / Real.log M ^ 2 +
          (1 / 3 : ℝ) * (selbergOriginalLogMonomial 1 4 M / Real.log M ^ 4) -
          selbergOriginalLogMonomial 2 3 M / Real.log M ^ 4 +
          selbergOriginalLogMonomial 2 2 M / Real.log M ^ 3))
      atTop (𝓝 (-(rho ^ 2) / 2)) := by
    convert hscaled using 1 <;> ring
  refine hscaled'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  exact (selbergOriginalIncludedOrdinaryEnergy_normalized_eq hrho hM).symm

/-- Reciprocal-tuned included polynomial main has the exact limit `ρ²/12`: the ordinary
`-ρ²/2` channel and the new Gram contribution `7ρ²/12` leave one twelfth. -/
theorem tendsto_barbanVehovIncludedLongEnergyPolynomialMain_tuned_rho
    (rho : ℝ) (hrho : rho ≠ 0) :
    Tendsto (fun M : ℕ =>
      barbanVehovIncludedLongEnergyPolynomialMain
        (rho / Real.log M) (Real.log M / rho) M)
      atTop (𝓝 (rho ^ 2 / 12)) := by
  have hord := tendsto_selbergOriginalIncludedOrdinaryEnergy_normalized_of_rho rho hrho
  have hrem :=
    tendsto_selbergOriginalTunedMinLogRemainder_div_log_four_seven_twelfths
  have hsum := hord.add (hrem.const_mul (rho ^ 2))
  have hsum' : Tendsto (fun M : ℕ =>
      selbergOriginalIncludedOrdinaryEnergy
          (rho / Real.log M) (Real.log M / rho) M / Real.log M ^ 2 +
        rho ^ 2 *
          (selbergOriginalTunedMinLogRemainder M / Real.log M ^ 4))
      atTop (𝓝 (rho ^ 2 / 12)) := by
    convert hsum using 1 <;> ring
  refine hsum'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlog : Real.log M ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  have htune : (rho / Real.log M) * (Real.log M / rho) = 1 := by
    field_simp [hlog, hrho]
  rw [barbanVehovIncludedLongEnergyPolynomialMain_eq_ordinary_add_tunedRemainder
    (Nat.zero_lt_of_lt (by omega : 1 < M)) htune]
  field_simp [hlog]

private theorem tendsto_nat_pow_fortyNine_atTop_t1 :
    Tendsto (fun N : ℕ => N ^ 49) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN
  have hBN : B ≤ N := (Nat.le_max_left B 1).trans hN
  have hN1 : 1 ≤ N := (Nat.le_max_right B 1).trans hN
  exact hBN.trans (by
    calc
      N ≤ N * N ^ 48 := Nat.le_mul_of_pos_right N (pow_pos hN1 48)
      _ = N ^ 49 := by ring)

/-- Schedule specialization of the included polynomial main at reciprocal tuning. -/
theorem tendsto_barbanVehovIncludedLongEnergyPolynomialMain_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      barbanVehovIncludedLongEnergyPolynomialMain
        ((49 / 100 : ℝ) / (49 * Real.log N))
        (100 * Real.log N) (N ^ 49))
      atTop (𝓝 ((49 / 100 : ℝ) ^ 2 / 12)) := by
  have hbase := tendsto_barbanVehovIncludedLongEnergyPolynomialMain_tuned_rho
    (49 / 100 : ℝ) (by norm_num)
  have hcomp := hbase.comp tendsto_nat_pow_fortyNine_atTop_t1
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [Function.comp_apply]
  rw [show (((N ^ 49 : ℕ) : ℝ)) = (N : ℝ) ^ 49 by norm_num,
    Real.log_pow]
  congr 2
  norm_num
  ring

private theorem tendsto_const_div_nat_sq_t1 (c : ℝ) :
    Tendsto (fun N : ℕ => c / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => c / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmul := hc.mul hone
  rw [zero_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [hNR]

/-- **Actual included long-detector energy at reciprocal tuning.**  Its exact limit is one eighth
of the full long-energy limit. -/
theorem tendsto_levinsonCriticalDetectorLongEnergy_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      levinsonCriticalDetectorLongEnergy
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      atTop (𝓝 ((1 / 12 : ℝ) * (49 / 100 : ℝ) ^ 2)) := by
  let rho : ℝ := 49 / 100
  let P : ℕ → ℝ := fun N =>
    barbanVehovIncludedLongEnergyPolynomialMain
      (rho / (49 * Real.log N)) (100 * Real.log N) (N ^ 49)
  have hP : Tendsto P atTop (𝓝 ((1 / 12 : ℝ) * rho ^ 2)) := by
    convert
      tendsto_barbanVehovIncludedLongEnergyPolynomialMain_fortyNine_reciprocal using 1 <;>
      simp only [P, rho] <;> ring
  have habs : Tendsto (fun N : ℕ =>
      |levinsonCriticalDetectorLongEnergy
          (rho / (49 * Real.log N)) (N ^ 100) (N ^ 49) - P N|)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_
      (tendsto_const_div_nat_sq_t1 (barbanVehovIncludedFortyNineErrorConstant rho))
    filter_upwards [eventually_ge_atTop 8] with N hN
    simpa only [P] using
      abs_levinsonCriticalDetectorLongEnergy_fortyNine_sub_polynomialMain_le rho hN
  have herr : Tendsto (fun N : ℕ =>
      levinsonCriticalDetectorLongEnergy
          (rho / (49 * Real.log N)) (N ^ 100) (N ^ 49) - P N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs, norm_zero] using habs
  have hsum := herr.add hP
  simpa only [rho, P, zero_add] using hsum.congr'
    (Eventually.of_forall fun N => by ring)

/-- **Full long-detector energy at reciprocal tuning.**  This is the exact full-energy
comparison value needed to measure how much of the product range survives the detector cut. -/
theorem tendsto_levinsonCriticalDetectorFullLongEnergy_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      levinsonCriticalDetectorFullLongEnergy
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      atTop (𝓝 ((2 / 3 : ℝ) * (49 / 100 : ℝ) ^ 2)) := by
  convert tendsto_levinsonCriticalDetectorFullLongEnergy_fortyNine
    (49 / 100 : ℝ) using 1 <;> ring

/-- **One-eighth cancellation law for the actual long detector.**  At the reciprocal
`49/100` schedule, the included long detector is asymptotically exactly one eighth of the
full long detector.  Thus the omitted product range carries the other seven eighths; it cannot
be discarded as a lower-order tail. -/
theorem tendsto_levinsonCriticalDetectorLongEnergy_sub_oneEighth_full_fortyNine :
    Tendsto (fun N : ℕ =>
      levinsonCriticalDetectorLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) -
        (1 / 8 : ℝ) * levinsonCriticalDetectorFullLongEnergy
          ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      atTop (𝓝 0) := by
  have h :=
    tendsto_levinsonCriticalDetectorLongEnergy_fortyNine_reciprocal.sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 8 : ℝ))
          atTop (𝓝 (1 / 8 : ℝ))).mul
        tendsto_levinsonCriticalDetectorFullLongEnergy_fortyNine_reciprocal)
  convert h using 1 <;> ring

end

end RHTower.Sieve
