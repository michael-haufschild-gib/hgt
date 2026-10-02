import GaloisForLFunctions.RHTower.SoninCutoffMonomialDilation
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import GaloisForLFunctions.RHTower.SoninPrimeSquareOverlapSummability
import GaloisForLFunctions.RHTower.CoherentGramSummability

noncomputable section
namespace RHTower

/-- The retained prime-square coefficient is the original unsquared Euler coefficient. -/
theorem soninLogPrimePowerCoefficient_primeSquare (p : Nat.Primes) :
    soninLogPrimePowerCoefficient (p, 0) = ((1 / (2 * (p : ℝ)) : ℝ) : ℂ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [soninLogPrimePowerCoefficient]
  have henergy : soninPrimePowerTailEnergy (p, 0) = ((p : ℝ)⁻¹)^2 := rfl
  rw [henergy, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  congr 1
  simp only [Nat.cast_zero, zero_add]
  field_simp

private theorem weighted_primeSquare_overlap_of_le
    (a : ℝ) (n : ℕ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) :
    ‖inner ℂ
      (((1 / (2 * p) : ℝ) : ℂ) • dilation (p^2) (sq_pos_of_pos hp) (soninCutoffMonomial a n))
      (((1 / (2 * q) : ℝ) : ℂ) • dilation (q^2) (sq_pos_of_pos hq) (soninCutoffMonomial a n))‖ ≤
        ‖soninCutoffMonomial a n‖^2 / (4 * q^2) := by
  have hover := norm_inner_dilation_soninCutoffMonomial_le a n (p^2) (q^2)
    (sq_pos_of_pos hp) (sq_pos_of_pos hq) (pow_le_pow_left₀ hp.le hpq 2)
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hp, abs_of_pos hq] at hover
  calc
    _ = (1 / (2 * p)) * (1 / (2 * q)) *
        ‖inner ℂ (dilation (p^2) (sq_pos_of_pos hp) (soninCutoffMonomial a n))
          (dilation (q^2) (sq_pos_of_pos hq) (soninCutoffMonomial a n))‖ := by
      rw [inner_smul_left, inner_smul_right]
      simp only [Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 1 / (2 * p)),
        abs_of_pos (by positivity : 0 < 1 / (2 * q))]
      ring
    _ ≤ (1 / (2 * p)) * (1 / (2 * q)) *
        ((p / q) * ‖soninCutoffMonomial a n‖^2) :=
      mul_le_mul_of_nonneg_left hover (by positivity)
    _ = _ := by field_simp; ring

/-- Inverting both scales reverses their coherent overlap. -/
theorem inner_inverse_dilations (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (f : SoninL2) :
    inner ℂ (dilation r⁻¹ (inv_pos.mpr hr) f) (dilation s⁻¹ (inv_pos.mpr hs) f) =
      inner ℂ (dilation s hs f) (dilation r hr f) := by
  calc
    _ = inner ℂ
        (dilation (r*s) (mul_pos hr hs) (dilation r⁻¹ (inv_pos.mpr hr) f))
        (dilation (r*s) (mul_pos hr hs) (dilation s⁻¹ (inv_pos.mpr hs) f)) :=
      ((dilation (r*s) (mul_pos hr hs)).inner_map_map _ _).symm
    _ = _ := by
      rw [dilation_comp_apply, dilation_comp_apply]
      have hleft : r * s * r⁻¹ = s := by field_simp
      have hright : r * s * s⁻¹ = r := by field_simp
      simp only [hleft, hright]

private theorem weighted_primeSquare_overlap
    (a : ℝ) (n : ℕ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ‖inner ℂ
      (((1 / (2 * p) : ℝ) : ℂ) • dilation (p^2) (sq_pos_of_pos hp) (soninCutoffMonomial a n))
      (((1 / (2 * q) : ℝ) : ℂ) • dilation (q^2) (sq_pos_of_pos hq) (soninCutoffMonomial a n))‖ ≤
        ‖soninCutoffMonomial a n‖^2 / (4 * (max p q)^2) := by
  rcases le_total p q with h | h
  · simpa only [max_eq_right h] using weighted_primeSquare_overlap_of_le a n p q hp hq h
  · rw [norm_inner_symm (𝕜 := ℂ)]
    simpa only [max_eq_left h] using weighted_primeSquare_overlap_of_le a n q p hq hp h

private theorem weighted_primeSquare_inverse_overlap
    (a : ℝ) (n : ℕ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    ‖inner ℂ
      (((1 / (2 * p) : ℝ) : ℂ) • dilation (p^2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hp)) (soninCutoffMonomial a n))
      (((1 / (2 * q) : ℝ) : ℂ) • dilation (q^2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hq)) (soninCutoffMonomial a n))‖ ≤
        ‖soninCutoffMonomial a n‖^2 / (4 * (max p q)^2) := by
  have h := weighted_primeSquare_overlap a n p q hp hq
  rw [inner_smul_left, inner_smul_right] at h ⊢
  simp only [Complex.conj_ofReal, norm_mul] at h ⊢
  rw [inner_inverse_dilations, norm_inner_symm (𝕜 := ℂ)]
  exact h

/-- Original unsquared prime-square modes converge on every actual time-band
output monomial, over the directed system of all finite prime sets. -/
theorem summable_soninPrimeSquareWeightedDilationSum_monomial (a : ℝ) (n : ℕ) :
    Summable (fun p : Nat.Primes => soninLogPrimePowerCoefficient (p, 0) •
      dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))
        (soninCutoffMonomial a n)) := by
  have hmajor : Summable (fun pq : Nat.Primes × Nat.Primes =>
      ‖soninCutoffMonomial a n‖^2 /
        (4 * ((max (pq.1 : ℕ) (pq.2 : ℕ) : ℕ) : ℝ)^2)) := by
    apply (summable_prime_pair_max_inv_sq.mul_left (‖soninCutoffMonomial a n‖^2 / 4)).congr
    intro pq
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hp (p : Nat.Primes) : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hin : Summable (fun p : Nat.Primes =>
      ((1 / (2 * (p : ℝ)) : ℝ) : ℂ) •
        dilation ((p : ℝ)^2) (sq_pos_of_pos (hp p)) (soninCutoffMonomial a n)) := by
    apply summable_of_summable_norm_inner
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
    intro pq
    simpa only [Nat.cast_max] using weighted_primeSquare_overlap a n
      (pq.1 : ℝ) (pq.2 : ℝ) (hp pq.1) (hp pq.2)
  have hout : Summable (fun p : Nat.Primes =>
      ((1 / (2 * (p : ℝ)) : ℝ) : ℂ) •
        dilation ((p : ℝ)^2)⁻¹ (inv_pos.mpr (sq_pos_of_pos (hp p))) (soninCutoffMonomial a n)) := by
    apply summable_of_summable_norm_inner
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
    intro pq
    simpa only [Nat.cast_max] using weighted_primeSquare_inverse_overlap a n
      (pq.1 : ℝ) (pq.2 : ℝ) (hp pq.1) (hp pq.2)
  apply (hin.add hout).congr
  intro p
  rw [soninLogPrimePowerCoefficient_primeSquare, dilationSum_apply, smul_add]
  rfl

/-- One finite prime exclusion controls every degree of the original time-band
output. This is the uniform tail estimate required by the nuclear expansion. -/
theorem soninPrimeSquareWeightedDilationSum_monomial_uniform_tail (a : ℝ) :
    ∀ ε > 0, ∃ s : Finset Nat.Primes, ∀ t : Finset Nat.Primes, Disjoint t s →
      ∀ n : ℕ,
        ‖∑ p ∈ t, soninLogPrimePowerCoefficient (p, 0) •
          dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))
            (soninCutoffMonomial a n)‖ ≤ ε * ‖soninCutoffMonomial a n‖ := by
  classical
  let κ : Nat.Primes × Nat.Primes → ℝ := fun pq =>
    1 / (4 * ((max (pq.1 : ℕ) (pq.2 : ℕ) : ℕ) : ℝ)^2)
  have hk : Summable κ := by
    apply (summable_prime_pair_max_inv_sq.mul_left (1 / 4)).congr
    intro pq
    dsimp [κ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hk ((ε/2)^2) (by positivity)
  refine ⟨s.image Prod.fst, fun t ht n => ?_⟩
  have hdis : Disjoint (t ×ˢ t) s := by
    apply Finset.disjoint_left.mpr
    intro ij hij hsij
    exact Finset.disjoint_left.mp ht (Finset.mem_product.mp hij).1
      (Finset.mem_image_of_mem Prod.fst hsij)
  have htail := hs (t ×ˢ t) hdis
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (by intro pq _; dsimp [κ]; positivity))] at htail
  have hleg (u : Nat.Primes → SoninL2)
      (hu : ∀ pq : Nat.Primes × Nat.Primes,
        ‖inner ℂ (u pq.1) (u pq.2)‖ ≤ ‖soninCutoffMonomial a n‖^2 * κ pq) :
      ‖∑ p ∈ t, u p‖ ≤ (ε / 2) * ‖soninCutoffMonomial a n‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      _ ≤ ∑ pq ∈ t ×ˢ t, ‖inner ℂ (u pq.1) (u pq.2)‖ :=
        norm_sum_sq_le_sum_norm_inner u t
      _ ≤ ∑ pq ∈ t ×ˢ t, ‖soninCutoffMonomial a n‖^2 * κ pq :=
        Finset.sum_le_sum (fun pq _ => hu pq)
      _ = ‖soninCutoffMonomial a n‖^2 * ∑ pq ∈ t ×ˢ t, κ pq :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ ‖soninCutoffMonomial a n‖^2 * (ε / 2)^2 :=
        mul_le_mul_of_nonneg_left htail.le (sq_nonneg _)
      _ = _ := by ring
  have hp (p : Nat.Primes) : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  let u : Nat.Primes → SoninL2 := fun p =>
    ((1 / (2 * (p : ℝ)) : ℝ) : ℂ) •
      dilation ((p : ℝ)^2) (sq_pos_of_pos (hp p)) (soninCutoffMonomial a n)
  let v : Nat.Primes → SoninL2 := fun p =>
    ((1 / (2 * (p : ℝ)) : ℝ) : ℂ) •
      dilation ((p : ℝ)^2)⁻¹ (inv_pos.mpr (sq_pos_of_pos (hp p))) (soninCutoffMonomial a n)
  have hu : ‖∑ p ∈ t, u p‖ ≤ (ε/2)*‖soninCutoffMonomial a n‖ := by
    apply hleg u
    intro pq
    simpa only [u, κ, Nat.cast_max, div_eq_mul_inv, one_mul] using
      weighted_primeSquare_overlap a n (pq.1 : ℝ) (pq.2 : ℝ) (hp pq.1) (hp pq.2)
  have hv : ‖∑ p ∈ t, v p‖ ≤ (ε/2)*‖soninCutoffMonomial a n‖ := by
    apply hleg v
    intro pq
    simpa only [v, κ, Nat.cast_max, div_eq_mul_inv, one_mul] using
      weighted_primeSquare_inverse_overlap a n (pq.1 : ℝ) (pq.2 : ℝ) (hp pq.1) (hp pq.2)
  have heq (p : Nat.Primes) : soninLogPrimePowerCoefficient (p, 0) •
      dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))
        (soninCutoffMonomial a n) = u p + v p := by
    rw [soninLogPrimePowerCoefficient_primeSquare, dilationSum_apply, smul_add]
    rfl
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  calc
    _ ≤ ‖∑ p ∈ t, u p‖ + ‖∑ p ∈ t, v p‖ := norm_add_le _ _
    _ ≤ (ε/2)*‖soninCutoffMonomial a n‖ + (ε/2)*‖soninCutoffMonomial a n‖ := add_le_add hu hv
    _ = _ := by ring
end RHTower


