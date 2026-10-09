import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticHarmonicPositive
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticEulerPolydisk

/-!
# Full source positivity forces absolute prime summability

The positive ordinary source normalization controls every finite product
of first-coefficient gains. Local harmonic factors have a quadratic tail;
the logarithm comparison bounds all finite large-prime sums uniformly.
Removing the finite head gives absolute square-root-weighted prime
summability, with every analytic input derived from the actual source.
-/

open ArithmeticFunction Complex Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- The local harmonic factor in its ordinary geometric-series form. -/
theorem localEulerValue_eq_geometric (f : ArithmeticFunction ℝ) (p : ℕ) :
    localEulerValue f p = ∑' k : ℕ, f (p ^ k) * ((p : ℝ)⁻¹) ^ k := by
  unfold localEulerValue
  apply tsum_congr
  intro k
  rw [Nat.cast_pow, div_eq_mul_inv, inv_pow]

theorem localEulerValue_pos {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {p : ℕ} (hp : p.Prime) : 0 < localEulerValue f p := by
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hb 2 Nat.prime_two 1 le_rfl)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hqhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    exact (inv_le_comm₀ hp0 (by norm_num)).mpr (by simpa using hp2)
  have hq1 : (p : ℝ)⁻¹ < 1 := by linarith
  have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  have hscale : θ * (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) ≤ θ := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hqhalf hθ0]
  have hl := real_localEuler_lower (a := fun k => f (p ^ k)) (by simp [hf.map_one])
    (hb p hp) hq0 hq1
  rw [localEulerValue_eq_geometric]
  linarith

/-- Isolating the first coefficient leaves a uniformly quadratic local tail. -/
theorem real_localEuler_upper_first {a : ℕ → ℝ} (ha : ∀ k, |a k| ≤ 1)
    (ha0 : a 0 = 1) {q : ℝ} (hq0 : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (∑' k : ℕ, a k * q ^ k) ≤ 1 + |a 1| * q + 2 * q ^ 2 := by
  have hq1 : q < 1 := by linarith
  have hs := summable_real_bounded_geometric ha hq0 hq1
  have ht := abs_real_bounded_geometric_le (fun k => ha (k + 2)) hq0 hq1
  have he : (∑' k : ℕ, a k * q ^ k) =
      1 + a 1 * q + q ^ 2 * ∑' k : ℕ, a (k + 2) * q ^ k := by
    rw [← hs.sum_add_tsum_nat_add 2]
    norm_num [Finset.sum_range_succ, ha0]
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [pow_add]
    ring
  have htail : (∑' k : ℕ, a (k + 2) * q ^ k) ≤ 2 := by
    apply (le_abs_self _).trans (ht.trans _)
    apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
    linarith
  rw [he]
  have hfirst := mul_le_mul_of_nonneg_right (le_abs_self (a 1)) hq0
  have htail' := mul_le_mul_of_nonneg_left htail (sq_nonneg q)
  linarith

theorem log_one_add_lower_quadratic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by positivity
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hpos)
  have hi : (1 + x)⁻¹ ≤ 1 - (x - x ^ 2) := by
    rw [← one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx (sq_nonneg x)]
  linarith

/-- A local first-coefficient gain dominates the harmonic factor at large primes. -/
theorem log_first_gain_sub_log_factor {u q A : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 16)
    (hA0 : 0 < A) (hA : A ≤ 1 + u * q ^ 2 + 2 * q ^ 4) :
    u * q / 8 - 2 * q ^ 4 ≤ Real.log (1 + u * q / 4) - Real.log A := by
  have hlow := log_one_add_lower_quadratic (div_nonneg (mul_nonneg hu0 hq0) (by norm_num : (0 : ℝ) ≤ 4))
  have hupp := Real.log_le_sub_one_of_pos hA0
  have huq : u * q ≤ q := by nlinarith
  have hsmall : q + u * q / 16 ≤ 1 / 8 := by linarith
  have hprod := mul_nonneg (mul_nonneg hu0 hq0) (sub_nonneg.mpr hsmall)
  nlinarith


theorem primeRadius_le_sixteenth {p : ℕ} (hp : 256 ≤ p) : primeRadius p ≤ 1 / 16 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hs : (p : ℝ)⁻¹ ≤ 1 / 256 := by
    apply (inv_le_comm₀ hp0 (by norm_num : (0 : ℝ) < 1 / 256)).mpr
    norm_num
    exact_mod_cast hp
  rw [← primeRadius_sq] at hs
  nlinarith [primeRadius_nonneg p]

/-- The local comparison sums without a loss depending on the prime cutoff. -/
theorem sum_first_gain_le_of_product_bound {ι : Type*} [Fintype ι]
    (u q A : ι → ℝ) {K : ℝ} (hK : 0 < K)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1 / 16)
    (hA0 : ∀ i, 0 < A i) (hA : ∀ i, A i ≤ 1 + u i * q i ^ 2 + 2 * q i ^ 4)
    (hprod : (∏ i, (1 + u i * q i / 4)) ≤ K * ∏ i, A i) :
    (∑ i, u i * q i) ≤ 8 * Real.log K + 16 * ∑ i, q i ^ 4 := by
  have hg (i : ι) : 0 < 1 + u i * q i / 4 := by
    have := hu0 i
    have := hq0 i
    positivity
  have hl := Real.log_le_log (Finset.prod_pos (fun i _ => hg i)) hprod
  rw [Real.log_mul hK.ne' (Finset.prod_pos (fun i _ => hA0 i)).ne',
    Real.log_prod (fun i _ => (hg i).ne'), Real.log_prod (fun i _ => (hA0 i).ne')] at hl
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    log_first_gain_sub_log_factor (hu0 i) (hu1 i) (hq0 i) (hq1 i) (hA0 i) (hA i))
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum] at hs
  linarith

/-- Every unit complex phase is the first character of an additive-circle point. -/
theorem exists_fourier_one_eq {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ x : UnitAddCircle, fourier 1 x = z := by
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle one_ne_zero).surjective
    (⟨z, mem_sphere_zero_iff_norm.mpr hz⟩ : Circle)
  refine ⟨x, ?_⟩
  rw [fourier_one, ← AddCircle.homeomorphCircle_apply one_ne_zero, hx]

/-- The actual source bounds every finite product of prime coefficient gains. -/
theorem exists_source_prime_gain_bound {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime),
      (∏ p ∈ P, (1 + |f p| * primeRadius p / 4)) ≤
        (2 / H) * ∏ p ∈ P, localEulerValue f p := by
  classical
  obtain ⟨H, _, hHpos, hHle, hbound⟩ :=
    exists_positive_finiteEuler_bound_of_strict_multiplicative_source hf hθ hb hW hs
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hb 2 Nat.prime_two 1 le_rfl)
  have hglobal (n : ℕ) : |f n| ≤ 1 := by
    simpa [primeAttenuation] using abs_le_primeAttenuation hf hθ0 hθ.le hb ∅ (by simp) n
  refine ⟨H, hHpos, hHle, ?_⟩
  intro P hP
  let A := ∏ p ∈ P, localEulerValue f p
  have hA : 0 < A := Finset.prod_pos (fun p hp => localEulerValue_pos hf hθ hb (hP p hp))
  have hc (z : P → ℂ) (hz : ∀ p, ‖z p‖ = 1) :
      (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
        ((primeRadius p : ℂ) * z p)).re ≤ A / H := by
    choose x hx using fun p => exists_fourier_one_eq (hz p)
    have h := hbound P hP x
    simp_rw [hx] at h
    have hdiv : (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
        ((primeRadius p : ℂ) * z p)).re ≤ 1 / (H / A) :=
      (le_div_iff₀ (div_pos hHpos hA)).mpr (by simpa only [mul_comm, A] using h)
    simpa only [one_div, inv_div] using hdiv
  have hg := prod_one_add_first_coefficient_le
    (fun (p : P) k => (f ((p : ℕ) ^ k) : ℂ)) (fun p : P => primeRadius p)
    (fun p k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hglobal ((p : ℕ) ^ k))
    (fun p => by simp [hf.map_one]) (fun p => primeRadius_nonneg p)
    (fun p => primeRadius_lt_one (hP p p.2)) hc
  simp only [pow_one, Complex.norm_real, Real.norm_eq_abs] at hg
  rw [Finset.prod_coe_sort (s := P) (f := fun p : ℕ => 1 + |f p| * primeRadius p / 4)] at hg
  calc
    _ ≤ 2 * (A / H) - 1 := hg
    _ ≤ (2 / H) * A := by nlinarith [show 2 * (A / H) = (2 / H) * A by ring]

theorem localEulerValue_le_first_quadratic {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {p : ℕ} (hp : p.Prime) :
    localEulerValue f p ≤ 1 + |f p| * primeRadius p ^ 2 + 2 * primeRadius p ^ 4 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    apply (inv_le_comm₀ hp0 (by norm_num : (0 : ℝ) < 1 / 2)).mpr
    norm_num
    exact_mod_cast hp.two_le
  have h := real_localEuler_upper_first (fun k => hb (p ^ k)) (by simp [hf.map_one])
    (inv_nonneg.mpr hp0.le) hhalf
  have hfour : primeRadius p ^ 4 = ((p : ℝ)⁻¹) ^ 2 := by
    rw [show primeRadius p ^ 4 = (primeRadius p ^ 2) ^ 2 by ring, primeRadius_sq]
  simpa only [← localEulerValue_eq_geometric, pow_one, hfour, primeRadius_sq] using h

theorem sum_primeRadius_four_le (P : Finset ℕ) :
    ∑ p ∈ P, primeRadius p ^ 4 ≤ invSquareTailConst := by
  have he (p : ℕ) : primeRadius p ^ 4 = 1 / (p : ℝ) ^ (2 : ℝ) := by
    rw [show primeRadius p ^ 4 = (primeRadius p ^ 2) ^ 2 by ring, primeRadius_sq,
      inv_pow, Real.rpow_two, one_div]
  simp_rw [he]
  exact sum_inv_rpow_two_le P

/-- A single source normalization bounds every finite large-prime gain sum. -/
theorem exists_uniform_large_prime_gain_bound {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    ∃ K : ℝ, ∀ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime ∧ 256 ≤ p),
      (∑ p ∈ P, |f p| * primeRadius p) ≤ K := by
  obtain ⟨H, hHpos, _, hprod⟩ := exists_source_prime_gain_bound hf hθ hb hW hs
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hb 2 Nat.prime_two 1 le_rfl)
  have hglobal (n : ℕ) : |f n| ≤ 1 := by
    simpa [primeAttenuation] using abs_le_primeAttenuation hf hθ0 hθ.le hb ∅ (by simp) n
  refine ⟨8 * Real.log (2 / H) + 16 * invSquareTailConst, ?_⟩
  intro P hP
  have h := sum_first_gain_le_of_product_bound
    (fun p : P => |f p|) (fun p : P => primeRadius p) (fun p : P => localEulerValue f p)
    (div_pos (by norm_num : (0 : ℝ) < 2) hHpos) (fun p => abs_nonneg _) (fun p => hglobal p)
    (fun p => primeRadius_nonneg p) (fun p => primeRadius_le_sixteenth (hP p p.2).2)
    (fun p => localEulerValue_pos hf hθ hb (hP p p.2).1)
    (fun p => localEulerValue_le_first_quadratic hf hglobal (hP p p.2).1)
    (by
      rw [Finset.prod_coe_sort (s := P) (f := fun p : ℕ => 1 + |f p| * primeRadius p / 4),
        Finset.prod_coe_sort (s := P) (f := fun p : ℕ => localEulerValue f p)]
      exact hprod P (fun p hp => (hP p hp).1))
  rw [Finset.sum_coe_sort (s := P) (f := fun p : ℕ => |f p| * primeRadius p),
    Finset.sum_coe_sort (s := P) (f := fun p : ℕ => primeRadius p ^ 4)] at h
  exact h.trans (by nlinarith [sum_primeRadius_four_le P])

/-- The source inequality forces absolute square-root-weighted prime summability. -/
theorem summable_prime_gain_of_strict_multiplicative_source {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    Summable (fun p : Nat.Primes => |f p| * primeRadius p) := by
  obtain ⟨K, hK⟩ := exists_uniform_large_prime_gain_bound hf hθ hb hW hs
  have hcut : Summable (fun n : ℕ =>
      if n.Prime ∧ 256 ≤ n then |f n| * primeRadius n else 0) := by
    apply summable_of_sum_le (c := K)
    · intro n
      change 0 ≤ if n.Prime ∧ 256 ≤ n then |f n| * primeRadius n else 0
      split_ifs
      · exact mul_nonneg (abs_nonneg _) (primeRadius_nonneg n)
      · exact le_rfl
    · intro P
      simpa only [Finset.sum_filter] using hK (P.filter (fun n => n.Prime ∧ 256 ≤ n))
        (fun n hn => (Finset.mem_filter.mp hn).2)
  have hprime : Summable (fun n : ℕ => if n.Prime then |f n| * primeRadius n else 0) := by
    apply hcut.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 256] with n hn
    by_cases hp : n.Prime <;> simp [hp, hn]
  exact (hprime.subtype Nat.Prime).congr (fun p => if_pos p.property)

end RHTower.WeilSingularArithmetic
