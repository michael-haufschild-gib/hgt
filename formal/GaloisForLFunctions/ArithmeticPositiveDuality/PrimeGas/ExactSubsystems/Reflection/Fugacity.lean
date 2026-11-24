import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Grading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.ExactFactors

/-! # Independent complex fugacities in finite windows of an exact gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

/-- The product of single-prime fugacities, one for each occupied quantum. -/
def occupationWeight (u : ℕ → ℂ) (n : ℕ) : ℂ := n.factorization.prod (fun p k => u p^k)

theorem occupationWeight_mul (u : ℕ → ℂ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    occupationWeight u (m*n) = occupationWeight u m*occupationWeight u n := by
  rw [occupationWeight,Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index (fun _ _ => pow_zero _) (fun _ _ _ _ => pow_add _ _ _)

private theorem weight_one (u : ℕ → ℂ) : occupationWeight u 1 = 1 := by simp [occupationWeight]

private theorem weight_coprime (u : ℕ → ℂ) {m n : ℕ} (h : m.Coprime n) :
    occupationWeight u (m*n) = occupationWeight u m*occupationWeight u n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using h
    simp only [hn,weight_one,mul_one]
  by_cases hn : n = 0
  · subst n
    have hm' : m = 1 := by simpa using h
    simp only [hm',weight_one,one_mul]
  exact occupationWeight_mul u hm hn

private theorem weight_prime_power (u : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    occupationWeight u (p^k) = u p^k := by
  rw [occupationWeight,hp.factorization_pow]
  exact Finsupp.prod_single_index (h := fun p k => u p^k) (pow_zero _)

/-- The window partition with independently adjustable prime fugacities. -/
def fugacityTrace {ι : Type*} (P : Finset ℕ) (a : ι → ℕ+) (u : ℕ → ℂ) :=
  ∑' i : WindowState P a, occupationWeight u (a i.val).val

/-- The exact product persists on the full open polydisk of prime fugacities. -/
theorem fugacity_window_product {ι κ : Type*} (P : Finset ℕ) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (u : ℕ → ℂ) (hu : ∀ p, p.Prime → ‖u p‖ < 1) :
    fugacityTrace P a u * fugacityTrace P b u = ∏ p ∈ P with Nat.Prime p, (1-u p)⁻¹ := by
  obtain ⟨_,hs⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := occupationWeight u) (weight_one u) (weight_coprime u)
    (fun {p} hp => by
      simp only [weight_prime_power u hp,norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hu p hp)) P
  let e := Equiv.ofBijective (windowProduct P a b) (windowProduct_bijective P h)
  have hr := (e.hasSum_iff (f := fun n : Nat.factoredNumbers P => occupationWeight u n.val)).mpr hs
  have ht := hr.congr_fun (g := fun v : WindowState P a × WindowState P b =>
    occupationWeight u (a v.1.val).val*occupationWeight u (b v.2.val).val)
    (fun v => (occupationWeight_mul u (a v.1.val).ne_zero (b v.2.val).ne_zero).symm)
  calc
    _ = ∑' v : WindowState P a × WindowState P b, occupationWeight u (a v.1.val).val*occupationWeight u (b v.2.val).val := by
      rw [ht.summable.tsum_prod]
      simp only [fugacityTrace,tsum_mul_left,tsum_mul_right]
    _ = _ := ht.tsum_eq.trans (Finset.prod_congr rfl (fun p hp => by
      have hprime := (Finset.mem_filter.mp hp).2
      simp only [weight_prime_power u hprime,tsum_geometric_of_norm_lt_one (hu p hprime)]))

/-- Every exact finite factor is zero-free when the prime fugacities vary independently inside the disk. -/
theorem finite_fugacity_ne_zero {ι κ : Type*} [Fintype ι] {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (u : ℕ → ℂ) (hu : ∀ p, p.Prime → ‖u p‖ < 1) :
    (∑ i, occupationWeight u (a i).val) ≠ 0 := by
  classical
  let P := Finset.univ.biUnion fun i => (a i).val.primeFactors
  have hmem (i : ι) : (a i).val ∈ Nat.factoredNumbers P :=
    Nat.mem_factoredNumbers_of_primeFactors_subset (a i).ne_zero
      (fun _ hp => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hp⟩)
  let e : WindowState P a ≃ ι := Equiv.subtypeUnivEquiv hmem
  have hf : fugacityTrace P a u = ∑ i, occupationWeight u (a i).val :=
    (e.tsum_eq (fun i => occupationWeight u (a i).val)).trans (tsum_fintype _)
  have hprod : (∏ p ∈ P with Nat.Prime p, (1-u p)⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    apply inv_ne_zero
    apply sub_ne_zero.mpr
    intro he
    have hl := hu p (Finset.mem_filter.mp hp).2
    rw [← he,norm_one] at hl
    exact hl.false
  exact hf ▸ (mul_ne_zero_iff.mp ((fugacity_window_product P h u hu).trans_ne hprod)).1

private theorem grade_weight (t n : ℕ) (z : ℂ) :
    occupationWeight (fun p => z^(t^p)) n = z^(grade t n) := by
  rw [grade,Polynomial.eval_eq_sum]
  change (∏ p ∈ n.factorization.support, (z^(t^p))^(n.factorization p)) =
    z^(∑ p ∈ n.factorization.support, n.factorization p*t^p)
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul,Nat.mul_comm]

/-- Every positive integer grading has a disk-free finite partition. -/
theorem graded_partition_ne_zero {ι κ : Type*} [Fintype ι] {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (t : ℕ+) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑ i, z^(grade t.val (a i).val)) ≠ 0 := by
  have hu (p : ℕ) (_ : p.Prime) : ‖z^(t.val^p)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hz (pow_pos t.pos _).ne'
  simpa only [grade_weight] using finite_fugacity_ne_zero h (fun p => z^(t.val^p)) hu

#print axioms occupationWeight_mul
#print axioms fugacity_window_product
#print axioms finite_fugacity_ne_zero
#print axioms graded_partition_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
