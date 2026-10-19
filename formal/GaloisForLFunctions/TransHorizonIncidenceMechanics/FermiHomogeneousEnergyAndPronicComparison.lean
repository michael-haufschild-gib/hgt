import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPronicRayWeightAndTailControl

/-!
# Homogeneous comparison for the native physical Fermi trace

Both actual reciprocal-pronic energies lie between one half and one times
these reciprocal-square forms. The comparison preserves the odd observation
and the omitted first dyadic difference. Summability comes from the existing
physical ray decomposition, before any infinite Gram expansion is used.

This is an ingredient for the odd-prime capacity classification on dyadic
antichains, not the classification itself.
-/

open RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem homogeneous_comparison {ι : Type*} (f g : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i / 2 ≤ g i ∧ g i ≤ f i)
    (hg : Summable g) :
    Summable f ∧ (∑' i, f i) / 2 ≤ ∑' i, g i ∧ (∑' i, g i) ≤ ∑' i, f i := by
  have ha : Summable f := Summable.of_nonneg_of_le hf0
    (fun i => by linarith [(hfg i).1]) (hg.mul_left 2)
  have hh := ha.tsum_le_tsum (fun i => show f i ≤ 2 * g i by
    linarith [(hfg i).1]) (hg.mul_left 2)
  rw [hg.tsum_mul_left 2] at hh
  exact ⟨ha, by linarith, hg.tsum_le_tsum (fun i => (hfg i).2) ha⟩

private theorem half_weight (k b : ℕ) (hb : 0 < b) :
    (1 / (b : ℝ)^2) / 2 ≤ fermiDyadicPronicWeight k b ∧
      fermiDyadicPronicWeight k b ≤ 1 / (b : ℝ)^2 := by
  have hp : (1 : ℝ) ≤ 2^k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hh : (1 / (b : ℝ)^2) / 2 ≤
      (2 : ℝ)^k / (((2 : ℝ)^k + 1) * (b : ℝ)^2) := by
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg (b : ℝ))]
  exact ⟨hh.trans (fermiDyadicPronicWeight_bounds k b hb).1,
    (fermiDyadicPronicWeight_bounds k b hb).2⟩

private theorem weighted_square_bounds (x : ℝ) (k b : ℕ) (hb : 0 < b) :
    (x^2 / (b : ℝ)^2) / 2 ≤ x^2 * fermiDyadicPronicWeight k b ∧
      x^2 * fermiDyadicPronicWeight k b ≤ x^2 / (b : ℝ)^2 := by
  obtain ⟨hl, hu⟩ := half_weight k b hb
  constructor
  · calc
      _ = x^2 * ((1 / (b : ℝ)^2) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (sq_nonneg x)
  · calc
      _ ≤ x^2 * (1 / (b : ℝ)^2) := mul_le_mul_of_nonneg_left hu (sq_nonneg x)
      _ = _ := by ring

private theorem odd_homogeneous_comparison (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun m : ℕ => (sieveSeq N c (2*m+1))^2 / ((2*m+1 : ℕ) : ℝ)^2) ∧
      (∑' m : ℕ, (sieveSeq N c (2*m+1))^2 / ((2*m+1 : ℕ) : ℝ)^2) / 2 ≤
        ∑' m : ℕ, (sieveSeq N c (2*m+1))^2 / (pronicSeq (2*m+1) : ℝ) ∧
      (∑' m : ℕ, (sieveSeq N c (2*m+1))^2 / (pronicSeq (2*m+1) : ℝ)) ≤
        ∑' m : ℕ, (sieveSeq N c (2*m+1))^2 / ((2*m+1 : ℕ) : ℝ)^2 := by
  apply homogeneous_comparison
  · intro m; positivity
  · intro m
    simpa [fermiDyadicPronicWeight, div_eq_mul_inv] using
      weighted_square_bounds (sieveSeq N c (2*m+1)) 0 (2*m+1) (by omega)
  · apply Summable.of_nonneg_of_le (fun m => by positivity) ?_
      (sieve_fermi_pronic_summable N c).1
    intro m
    simp only [sievePairedPronicEnergy, Finset.sum_singleton]
    exact le_add_of_nonneg_right (by positivity)

private theorem sieve_homogeneous_comparison (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ =>
      (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 /
        ((2*p.2+1 : ℕ) : ℝ)^2) ∧
      (∑' p : ℕ × ℕ, (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 /
        ((2*p.2+1 : ℕ) : ℝ)^2) / 2 ≤
      (∑' p : ℕ × ℕ, (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 *
        fermiDyadicPronicWeight (p.1+1) (2*p.2+1)) ∧
      (∑' p : ℕ × ℕ, (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 *
        fermiDyadicPronicWeight (p.1+1) (2*p.2+1)) ≤
      ∑' p : ℕ × ℕ, (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 /
        ((2*p.2+1 : ℕ) : ℝ)^2 := by
  exact homogeneous_comparison _ _ (fun p => by positivity)
    (fun p => weighted_square_bounds _ _ _ (by omega))
    (sieve_fermi_dyadic_pronic_summable N c).1

private theorem jump_homogeneous_comparison (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun p : ℕ × ℕ =>
      (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 /
        ((2*p.2+1 : ℕ) : ℝ)^2) ∧
      (∑' p : ℕ × ℕ, (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 /
        ((2*p.2+1 : ℕ) : ℝ)^2) / 2 ≤
      (∑' p : ℕ × ℕ, (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 *
        fermiDyadicPronicWeight (p.1+2) (2*p.2+1)) ∧
      (∑' p : ℕ × ℕ, (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 *
        fermiDyadicPronicWeight (p.1+2) (2*p.2+1)) ≤
      ∑' p : ℕ × ℕ, (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 /
        ((2*p.2+1 : ℕ) : ℝ)^2 := by
  exact homogeneous_comparison _ _ (fun p => by positivity)
    (fun p => weighted_square_bounds _ _ _ (by omega))
    (sieve_fermi_dyadic_pronic_summable N c).2

/-- Sieve energy with reciprocal-square weights, in native odd-ray coordinates. -/
def sieveHomogeneousEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑' m : ℕ, (sieveSeq N c (2*m+1))^2 / ((2*m+1 : ℕ) : ℝ)^2) +
    ∑' p : ℕ × ℕ, (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 /
      ((2*p.2+1 : ℕ) : ℝ)^2

/-- Selected Fermi energy with reciprocal-square weights on the actual observation schedule. -/
def fermiSelectedHomogeneousEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  (∑' m : ℕ, (sieveSeq N c (2*m+1))^2 / ((2*m+1 : ℕ) : ℝ)^2) +
    ∑' p : ℕ × ℕ, (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 /
      ((2*p.2+1 : ℕ) : ℝ)^2

/-- All homogeneous odd readings and both complete ray arrays are summable. -/
theorem sieve_fermi_homogeneous_summable (N : ℕ) (c : ℕ → ℝ) :
    Summable (fun m : ℕ => (sieveSeq N c (2*m+1))^2 / ((2*m+1 : ℕ) : ℝ)^2) ∧
      Summable (fun p : ℕ × ℕ =>
        (fermiNormalizedDyadicSieve N c (2*p.2+1) (p.1+1))^2 /
          ((2*p.2+1 : ℕ) : ℝ)^2) ∧
      Summable (fun p : ℕ × ℕ =>
        (fermiNormalizedDyadicJump N c (2*p.2+1) (p.1+1))^2 /
          ((2*p.2+1 : ℕ) : ℝ)^2) :=
  ⟨(odd_homogeneous_comparison N c).1, (sieve_homogeneous_comparison N c).1,
    (jump_homogeneous_comparison N c).1⟩

/-- Reciprocal-pronic sieve energy and its homogeneous form differ by at most a factor two. -/
theorem sieveHomogeneousEnergy_pronic_bounds (N : ℕ) (c : ℕ → ℝ) :
    sieveHomogeneousEnergy N c / 2 ≤ sieveTotalPronicEnergy N c ∧
      sieveTotalPronicEnergy N c ≤ sieveHomogeneousEnergy N c := by
  have ho := (odd_homogeneous_comparison N c).2
  have hr := (sieve_homogeneous_comparison N c).2
  have hp := (sieve_fermi_dyadic_pronic_summable N c).1.tsum_prod
  rw [sieveTotalPronicEnergy_dyadic_rays, ← hp]
  unfold sieveHomogeneousEnergy
  constructor <;> linarith [ho.1, ho.2, hr.1, hr.2]

/-- The same factor-two comparison holds for the literal selected Fermi observations. -/
theorem fermiSelectedHomogeneousEnergy_pronic_bounds (N : ℕ) (c : ℕ → ℝ) :
    fermiSelectedHomogeneousEnergy N c / 2 ≤ fermiSelectedTotalPronicEnergy N c ∧
      fermiSelectedTotalPronicEnergy N c ≤ fermiSelectedHomogeneousEnergy N c := by
  have ho := (odd_homogeneous_comparison N c).2
  have hr := (jump_homogeneous_comparison N c).2
  have hp := (sieve_fermi_dyadic_pronic_summable N c).2.tsum_prod
  rw [fermiSelectedTotalPronicEnergy_dyadic_rays, ← hp]
  unfold fermiSelectedHomogeneousEnergy
  constructor <;> linarith [ho.1, ho.2, hr.1, hr.2]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
