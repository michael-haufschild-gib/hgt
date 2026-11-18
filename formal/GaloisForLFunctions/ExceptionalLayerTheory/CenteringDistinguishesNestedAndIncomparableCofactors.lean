import GaloisForLFunctions.ExceptionalLayerTheory.CoincidentProductsOfOrdinaryPrimeWeights
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw

/-!
# Centering distinguishes nested and incomparable cofactor pairs

For two incomparable cofactors the common product above their least
common multiple has two coprime complementary dilations greater than one.
Their centred covariance differs from the count of all such products by
an explicit nonpositive logarithmic correction. A nested pair can
instead reproduce the entire ordinary prime error.
-/

noncomputable section

open Finset ArithmeticFunction Filter

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Logarithmic mass of the positive powers of the least prime factor of
`a` through `X`, retained only when `a` is on this prime-power sequence. -/
def dilationPrimeMass (a X : ℕ) : ℝ :=
  if IsPrimePow a then Real.log ((a.minFac ^ Nat.log a.minFac X : ℕ) : ℝ) else 0

private theorem exists_minFac_pow_iff {a : ℕ} (ha : 2 ≤ a) :
    (∃ i : ℕ, a = a.minFac ^ i) ↔ IsPrimePow a := by
  constructor
  · rintro ⟨i, hi⟩
    have hi0 : i ≠ 0 := fun h => by simp [h] at hi; omega
    exact (isPrimePow_nat_iff _).mpr ⟨a.minFac, i, Nat.minFac_prime (by omega), Nat.pos_of_ne_zero hi0, hi.symm⟩
  · intro h
    exact ⟨_, h.minFac_pow_factorization_eq.symm⟩

/-- A nontrivial dilation samples only prime powers on one prime ray. -/
theorem sum_dilated_mangoldt_tail {a X : ℕ} (ha : 2 ≤ a) (hX : 1 ≤ X) :
    ∑ k ∈ Icc 2 X, vonMangoldt (a*k) = dilationPrimeMass a X := by
  classical
  let p := a.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have he (k : ℕ) (hk : k ∈ Icc 2 X) :
      vonMangoldt (a*k) * vonMangoldt k = Real.log p * vonMangoldt (a*k) := by
    by_cases hz : vonMangoldt (a*k) = 0
    · simp only [hz, zero_mul, mul_zero]
    obtain ⟨j, _, hj⟩ := RHTower.GaussZeroSum.eq_minFac_pow_of_dvd ha (dvd_mul_right a k)
      (vonMangoldt_ne_zero_iff.mp hz)
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp
      (show k ∣ p ^ j by rw [← hj]; exact dvd_mul_left k a)
    have hi0 : i ≠ 0 := fun h => by
      have := (mem_Icc.mp hk).1
      simp [h] at hi
      omega
    have hΛ : vonMangoldt k = Real.log p := by
      rw [hi, vonMangoldt_apply_pow hi0, vonMangoldt_apply_prime hp]
    rw [hΛ, mul_comm]
  have h := sum_dilated_mangoldt_product ha 1 hX
  simp only [one_mul] at h
  rw [sum_congr rfl he, ← mul_sum] at h
  have hone : ∃ j : ℕ, 1 = a.minFac ^ j := ⟨0, by simp⟩
  simp only [hone, and_true, exists_minFac_pow_iff ha] at h
  apply mul_left_cancel₀ hlog
  rw [h]
  unfold dilationPrimeMass
  split_ifs <;> simp [p]

private theorem primeMass_bounds {a X : ℕ} (ha : 2 ≤ a) (hX : 1 ≤ X) :
    0 ≤ dilationPrimeMass a X ∧ dilationPrimeMass a X ≤ Real.log X := by
  have hp : a.minFac.Prime := Nat.minFac_prime (by omega)
  unfold dilationPrimeMass
  split_ifs
  · have hpos : 0 < a.minFac ^ Nat.log a.minFac X := pow_pos hp.pos _
    exact ⟨Real.log_natCast_nonneg _, Real.log_le_log (by exact_mod_cast hpos)
      (by exact_mod_cast Nat.pow_log_le_self a.minFac (by omega : X ≠ 0))⟩
  · exact ⟨le_rfl, Real.log_natCast_nonneg _⟩

private theorem product_zero_of_coprime_dilations {a b k : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : a.Coprime b) (hk : 2 ≤ k) : vonMangoldt (a*k) * vonMangoldt (b*k) = 0 := by
  by_contra h
  obtain ⟨_, ⟨j, hj⟩, _⟩ := prime_powers_of_dilated_mangoldt_product ha hk h
  have hj0 : j ≠ 0 := fun h => by simp [h] at hj; omega
  have hpa : a.minFac ∣ a := Nat.minFac_dvd a
  have hpb : a.minFac ∣ b := hj ▸ dvd_pow_self _ hj0
  have hdiv := Nat.dvd_gcd hpa hpb
  rw [hc.gcd_eq_one] at hdiv
  exact (Nat.minFac_prime (by omega : a ≠ 1)).not_dvd_one hdiv

/-- The covariance above the first common product of two coprime nonunit
dilations equals the number of rows minus two explicit prime-power masses. -/
theorem centered_coprime_dilation_sum {a b X : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : a.Coprime b) (hX : 1 ≤ X) :
    ∑ k ∈ Icc 2 X, (vonMangoldt (a*k) - 1) * (vonMangoldt (b*k) - 1) =
      ((Icc 2 X).card : ℝ) - dilationPrimeMass a X - dilationPrimeMass b X := by
  have he (k : ℕ) (hk : k ∈ Icc 2 X) :
      (vonMangoldt (a*k) - 1) * (vonMangoldt (b*k) - 1) =
        1 - vonMangoldt (a*k) - vonMangoldt (b*k) := by
    linear_combination product_zero_of_coprime_dilations ha hb hc (mem_Icc.mp hk).1
  rw [sum_congr rfl he, sum_sub_distrib, sum_sub_distrib,
    sum_dilated_mangoldt_tail ha hX, sum_dilated_mangoldt_tail hb hX]
  simp

/-- Uniform signed error after subtracting the number of shared products. -/
theorem centered_coprime_dilation_bounds {a b X : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : a.Coprime b) (hX : 1 ≤ X) :
    let E := (∑ k ∈ Icc 2 X, (vonMangoldt (a*k) - 1) * (vonMangoldt (b*k) - 1)) -
      ((Icc 2 X).card : ℝ)
    E ∈ Set.Icc (-(2 * Real.log X)) 0 := by
  dsimp only
  rw [centered_coprime_dilation_sum ha hb hc hX]
  obtain ⟨ha0, hau⟩ := primeMass_bounds ha hX
  obtain ⟨hb0, hbu⟩ := primeMass_bounds hb hX
  constructor <;> linarith only [ha0, hau, hb0, hbu]

/-- A nested pair with non-prime-power ratio reproduces the ordinary prime
error exactly after centering both complementary factors. -/
theorem centered_nested_dilation_eq_prime_error {a : ℕ} (ha : 2 ≤ a) (hc : ¬ IsPrimePow a) (X : ℕ) :
    ∑ k ∈ Icc 1 X, (vonMangoldt (a*k) - 1) * (vonMangoldt k - 1) = (X : ℝ) - Chebyshev.psi X := by
  have hz (k : ℕ) : vonMangoldt (a*k) = 0 := by
    by_contra h
    obtain ⟨j, _, hj⟩ := RHTower.GaussZeroSum.eq_minFac_pow_of_dvd ha (dvd_mul_right a k)
      (vonMangoldt_ne_zero_iff.mp h)
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow (Nat.minFac_prime (by omega : a ≠ 1))).mp
      (show a ∣ a.minFac ^ j by rw [← hj]; exact dvd_mul_right a k)
    exact hc ((exists_minFac_pow_iff ha).mp ⟨i, hi⟩)
  simp_rw [hz, zero_sub, neg_one_mul, neg_sub, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
  unfold Chebyshev.psi
  rw [Nat.floor_natCast]
  rfl

private theorem no_dvd_in_octave {V d e : ℕ} (hd : V < d) (he : 0 < e) (hhi : e ≤ 2 * V)
    (hne : d ≠ e) : ¬ d ∣ e := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := fun h => by simp [h] at hk; omega
  have hk1 : k ≠ 1 := fun h => by simp [h] at hk; exact hne hk.symm
  have hmul := Nat.mul_le_mul_left d (show 2 ≤ k by omega)
  omega

private theorem two_le_reduced_of_not_dvd {d e : ℕ} (hd : 0 < d) (hnot : ¬ d ∣ e) :
    2 ≤ d / d.gcd e := by
  let g := d.gcd e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hgd : g ∣ d := Nat.gcd_dvd_left d e
  have hge : g ∣ e := Nat.gcd_dvd_right d e
  change 2 ≤ d / g
  by_contra! h
  have hq : d/g = 1 := le_antisymm (by omega)
    ((Nat.one_le_div_iff hg).mpr (Nat.le_of_dvd hd hgd))
  have hmul := Nat.div_mul_cancel hgd
  rw [hq, one_mul] at hmul
  exact hnot (hmul ▸ hge)

private theorem lcm_product_div {d : ℕ} (hd : 0 < d) (e k : ℕ) :
    d.lcm e * k / d = (e / d.gcd e) * k := by
  have hq : (d.lcm e) / d = e / d.gcd e := by
    apply Nat.div_eq_of_eq_mul_left hd
    apply Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left e hd)
    calc
      _ = d * e := (mul_comm _ _).trans (Nat.gcd_mul_lcm d e)
      _ = d * (e / d.gcd e * d.gcd e) := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
      _ = _ := by ac_rfl
  rw [Nat.mul_comm (d.lcm e) k, Nat.mul_div_assoc k (Nat.dvd_lcm_left d e), hq, Nat.mul_comm]

private theorem octave_reduced_pair {V d e : ℕ} (hd : V < d) (hD : d ≤ 2*V)
    (he : V < e) (hE : e ≤ 2*V) (hne : d ≠ e) :
    2 ≤ e / d.gcd e ∧ 2 ≤ d / d.gcd e ∧ (e / d.gcd e).Coprime (d / d.gcd e) := by
  have hd0 : 0 < d := by omega
  have he0 : 0 < e := by omega
  have ha := two_le_reduced_of_not_dvd he0 (no_dvd_in_octave he hd0 hD hne.symm)
  rw [Nat.gcd_comm e d] at ha
  exact ⟨ha, two_le_reduced_of_not_dvd hd0 (no_dvd_in_octave hd he0 hE hne),
    (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left e hd0)).symm⟩

/-- Within one octave two distinct prime-weight columns can meet only at
the least common multiple of their cofactors. -/
theorem first_octave_prime_overlap_eq_zero {V d e n : ℕ} (hd : V < d) (hD : d ≤ 2*V)
    (he : V < e) (hE : e ≤ 2*V) (hne : d ≠ e) (hdn : d ∣ n) (hen : e ∣ n)
    (hn : d.lcm e < n) : vonMangoldt (n/d) * vonMangoldt (n/e) = 0 := by
  obtain ⟨a, b, hc⟩ := octave_reduced_pair hd hD he hE hne
  obtain ⟨k, rfl⟩ := Nat.lcm_dvd_iff.mpr ⟨hdn, hen⟩
  have hk : 2 ≤ k := by
    by_contra! h
    have hh := Nat.mul_le_mul_left (d.lcm e) (show k ≤ 1 by omega)
    rw [Nat.mul_one] at hh
    omega
  have hright : d.lcm e * k / e = (d / d.gcd e) * k := by
    rw [Nat.lcm_comm d e, lcm_product_div (by omega : 0 < e) d k, Nat.gcd_comm e d]
  rw [lcm_product_div (by omega : 0 < d) e k, hright]
  exact product_zero_of_coprime_dilations a b hc hk

/-- Past the product of the two largest possible cofactors, the square of
the actual weighted prime sum is pointwise diagonal. The subset may also
restrict the long prime head. -/
theorem first_octave_prime_sum_sq {V n : ℕ} (hn : 4 * V ^ 2 < n) (S : Finset ℕ)
    (hS : S ⊆ (Ioc V (2*V)).filter (· ∣ n)) (w : ℕ → ℝ) :
    (∑ d ∈ S, w d * vonMangoldt (n/d)) ^ 2 =
      ∑ d ∈ S, (w d) ^ 2 * (vonMangoldt (n/d)) ^ 2 := by
  rw [sq, sum_mul]
  refine sum_congr rfl fun d hd => ?_
  rw [mul_sum, sum_eq_single_of_mem d hd]
  · ring
  · intro e he hne
    obtain ⟨hdv, hdn⟩ := mem_filter.mp (hS hd)
    obtain ⟨hev, hen⟩ := mem_filter.mp (hS he)
    obtain ⟨hdlo, hdhi⟩ := mem_Ioc.mp hdv
    obtain ⟨helo, hehi⟩ := mem_Ioc.mp hev
    have hprod : d.lcm e ≤ 4 * V ^ 2 := calc
      _ ≤ d*e := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega))
        (Nat.lcm_dvd (dvd_mul_right d e) (dvd_mul_left e d))
      _ ≤ (2*V)*(2*V) := Nat.mul_le_mul hdhi hehi
      _ = _ := by ring
    have hz := first_octave_prime_overlap_eq_zero hdlo hdhi helo hehi hne.symm hdn hen (hprod.trans_lt hn)
    linear_combination w d * w e * hz

/-- Taking absolute values of the cofactor weights leaves the absolute prime
coefficient unchanged past the product horizon. Cancellation in a longer
signed count must then occur between different integers. -/
theorem first_octave_abs_prime_sum {V n : ℕ} (hn : 4 * V ^ 2 < n) (S : Finset ℕ)
    (hS : S ⊆ (Ioc V (2*V)).filter (· ∣ n)) (w : ℕ → ℝ) :
    |∑ d ∈ S, w d * vonMangoldt (n/d)| = ∑ d ∈ S, |w d| * vonMangoldt (n/d) := by
  apply (sq_eq_sq₀ (abs_nonneg _) (sum_nonneg fun d _ =>
    mul_nonneg (abs_nonneg (w d)) vonMangoldt_nonneg)).mp
  rw [sq_abs, first_octave_prime_sum_sq hn S hS w,
    first_octave_prime_sum_sq hn S hS (fun d => |w d|)]
  simp only [sq_abs]

/-- For distinct cofactors anywhere in one octave, the centred correlation
above their least common multiple lies between the row count and that count
minus `2 log X`. Here `k` indexes multiples of the common product. -/
theorem centered_first_octave_overlap_bounds {V d e X : ℕ} (hd : V < d) (hD : d ≤ 2*V)
    (he : V < e) (hE : e ≤ 2*V) (hne : d ≠ e) (hX : 1 ≤ X) :
    let L := d.lcm e
    let E := (∑ k ∈ Icc 2 X, (vonMangoldt (L*k/d) - 1) * (vonMangoldt (L*k/e) - 1)) -
      ((Icc 2 X).card : ℝ)
    E ∈ Set.Icc (-(2 * Real.log X)) 0 := by
  have hd0 : 0 < d := by omega
  have he0 : 0 < e := by omega
  obtain ⟨ha, hb, hc⟩ := octave_reduced_pair hd hD he hE hne
  have heq (k : ℕ) : d.lcm e * k / e = (d / d.gcd e) * k := by
    rw [Nat.lcm_comm d e, lcm_product_div he0 d k, Nat.gcd_comm e d]
  dsimp only
  simp_rw [lcm_product_div hd0 e, heq]
  exact centered_coprime_dilation_bounds ha hb hc hX

/-- At the fixed nested ratio six the centred correlation has negative
excursions beyond every nonnegative exponent below the zero abscissa. -/
theorem sixfold_centered_overlap_has_prime_excursions {b : ℝ} (hb : 0 ≤ b)
    (hΘ : b < RHTower.zeroReSup) (B : ℕ) :
    ∃ N ≥ B, (∑ k ∈ Icc 1 N, (vonMangoldt (6*k) - 1) * (vonMangoldt k - 1)) < -((N : ℝ) ^ b) := by
  have h6 : ¬ IsPrimePow 6 := by
    intro h
    obtain ⟨p, _, hu⟩ := isPrimePow_iff_unique_prime_dvd.mp h
    have h₂ := hu 2 ⟨Nat.prime_two, ⟨3, rfl⟩⟩
    have h₃ := hu 3 ⟨Nat.prime_three, ⟨2, rfl⟩⟩
    omega
  obtain ⟨x, hx, hψ⟩ := frequently_atTop.mp
    (RHTower.frequently_rpow_lt_chebyshevPsi_sub hΘ) (max (B : ℝ) 1)
  have hx0 : 0 ≤ x := zero_le_one.trans ((le_max_right _ _).trans hx)
  refine ⟨⌊x⌋₊, Nat.le_floor ((le_max_left _ _).trans hx), ?_⟩
  rw [centered_nested_dilation_eq_prime_error (by norm_num : 2 ≤ 6) h6, ← Chebyshev.psi_eq_psi_coe_floor x]
  have hfloor := Nat.floor_le hx0
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg ⌊x⌋₊) hfloor hb
  linarith only [hfloor, hpow, hψ]

#print axioms first_octave_abs_prime_sum
#print axioms centered_first_octave_overlap_bounds
#print axioms sixfold_centered_overlap_has_prime_excursions

end GaloisForLFunctions.ExceptionalLayerTheory
