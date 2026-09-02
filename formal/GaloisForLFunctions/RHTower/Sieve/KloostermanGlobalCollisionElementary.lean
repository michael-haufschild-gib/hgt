import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionGram

/-!
# Elementary envelope for global Kloosterman collision energy

The exact collision normal form admits an unconditional baseline estimate without any spectral
input. A complete single-modulus response is bounded pointwise by its full transform energy,
while the other factor in each ordered modulus pair uses its normalized global-period L2
receiver. Finite Cauchy--Schwarz across the erased diagonal then produces the exact ordered-pair
cost `#Q * (#Q - 1)`.

Every modulus weight and source-residue energy remains visible, giving a future collective
Kuznetsov estimate an exact no-premise baseline to improve.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem normSq_finset_sum_le_card_mul_sum_normSq
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℂ) :
    Complex.normSq (∑ i ∈ S, a i) ≤
      (S.card : ℝ) * ∑ i ∈ S, Complex.normSq (a i) := by
  rw [← Complex.sq_norm]
  have htri : ‖∑ i ∈ S, a i‖ ≤ ∑ i ∈ S, ‖a i‖ := norm_sum_le _ _
  have hsum0 : 0 ≤ ∑ i ∈ S, ‖a i‖ := by positivity
  calc
    ‖∑ i ∈ S, a i‖ ^ 2 ≤ (∑ i ∈ S, ‖a i‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ S, a i)]
    _ ≤ (S.card : ℝ) * ∑ i ∈ S, Complex.normSq (a i) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq S
        (fun _ => (1 : ℝ)) (fun i => ‖a i‖)
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
        Complex.sq_norm, Nat.cast_ofNat, mul_one] using h

private theorem normSq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := by
  change Complex.normSq ((starRingEnd ℂ) z) = Complex.normSq z
  exact Complex.normSq_conj z

/-- Exact number of ordered unequal pairs from a finite set. -/
theorem card_sigma_erase_eq_card_mul_pred
    {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (S.sigma fun i => S.erase i).card = S.card * (S.card - 1) := by
  rw [Finset.card_sigma]
  calc
    (∑ i ∈ S, #(S.erase i)) = ∑ i ∈ S, (S.card - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.card_erase_of_mem hi
    _ = S.card * (S.card - 1) := by simp

/-- A complete single-modulus response is pointwise bounded by the full sharp transform energy. -/
theorem normSq_kloostermanGlobalModulusTimeResponse_le
    (q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (n : ℕ) :
    Complex.normSq (kloostermanGlobalModulusTimeResponse q B b n) ≤
      ((q + 1 : ℕ) : ℝ) ^ 2 *
        ∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z) := by
  rw [kloostermanGlobalModulusTimeResponse_eq_kloostermanTransform]
  have hsingle :
      Complex.normSq
          (kloostermanTransform (q + 1)
            (kloostermanSourceResidue (q + 1) B b)
            (-(n : ZMod (q + 1)))) ≤
        ∑ z : ZMod (q + 1),
          Complex.normSq
            (kloostermanTransform (q + 1)
              (kloostermanSourceResidue (q + 1) B b) z) := by
    exact Finset.single_le_sum
      (fun z _ => Complex.normSq_nonneg
        (kloostermanTransform (q + 1)
          (kloostermanSourceResidue (q + 1) B b) z))
      (Finset.mem_univ (-(n : ZMod (q + 1))))
  exact hsingle.trans
    (sum_normSq_kloostermanTransform_le (q + 1)
      (kloostermanSourceResidue (q + 1) B b))

/-- Elementary cross-modulus response product bound: one response is charged pointwise and the
other by its exact normalized global-period `L²` receiver. -/
theorem average_normSq_kloostermanGlobalModulusTimeResponse_mul_le
    (Q : Finset ℕ) (q r : ℕ) (hr : r ∈ Q)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) ≤
      ((q + 1 : ℕ) : ℝ) ^ 2 *
        ((r + 1 : ℕ) : ℝ) *
        (∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
        ∑ z : ZMod (r + 1),
          Complex.normSq (kloostermanSourceResidue (r + 1) B b z) := by
  let Eq : ℝ := ∑ z : ZMod (q + 1),
    Complex.normSq (kloostermanSourceResidue (q + 1) B b z)
  let Er : ℝ := ∑ z : ZMod (r + 1),
    Complex.normSq (kloostermanSourceResidue (r + 1) B b z)
  let Cq : ℝ := ((q + 1 : ℕ) : ℝ) ^ 2 * Eq
  have hEq : 0 ≤ Eq := by
    dsimp only [Eq]
    exact Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _
  have hCq : 0 ≤ Cq := by
    exact mul_nonneg (sq_nonneg _) hEq
  have hpoint : ∀ k : ZMod (kloostermanGlobalPeriod Q),
      Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
          Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) ≤
        Cq * Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) := by
    intro k
    exact mul_le_mul_of_nonneg_right
      (normSq_kloostermanGlobalModulusTimeResponse_le q B b k.val)
      (Complex.normSq_nonneg _)
  have hsum :
      (∑ k : ZMod (kloostermanGlobalPeriod Q),
        Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
          Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val)) ≤
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Cq * Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) :=
    Finset.sum_le_sum fun k _ => hpoint k
  have havg := average_normSq_kloostermanGlobalModulusTimeResponse_le Q r hr B b
  calc
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
            Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) ≤
      (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Cq * Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Cq * ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ Cq * (((r + 1 : ℕ) : ℝ) * Er) := by
      exact mul_le_mul_of_nonneg_left havg hCq
    _ = ((q + 1 : ℕ) : ℝ) ^ 2 *
        ((r + 1 : ℕ) : ℝ) *
        (∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
        ∑ z : ZMod (r + 1),
          Complex.normSq (kloostermanSourceResidue (r + 1) B b z) := by
      dsimp only [Cq, Eq, Er]
      ring

/-- Unconditional elementary envelope for the exact signed global collision energy.  Its explicit
ordered-pair cardinality is the finite Cauchy cost; improving this scale is the collective
cross-modulus fourth-moment problem. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_elementary
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      ((Q.card * (Q.card - 1) : ℕ) : ℝ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (w q) * Complex.normSq (w r) *
            (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              (∑ z : ZMod (q + 1),
                Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
              ∑ z : ZMod (r + 1),
                Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) := by
  classical
  rw [kloostermanGlobalFrequencyCollisionEnergy_eq_average_timeTransform]
  simp_rw [kloostermanGlobalCollisionTimeTransform_eq_modulusResponseGram]
  simp_rw [Complex.sq_norm]
  let S := Q.sigma fun q => Q.erase q
  let c : ZMod (kloostermanGlobalPeriod Q) → (Σ _ : ℕ, ℕ) → ℂ := fun k p =>
    star (w p.1 * kloostermanGlobalModulusTimeResponse p.1 B b k.val) *
      (w p.2 * kloostermanGlobalModulusTimeResponse p.2 B b k.val)
  have hpoint : ∀ k : ZMod (kloostermanGlobalPeriod Q),
      Complex.normSq (∑ p ∈ S, c k p) ≤
        (S.card : ℝ) * ∑ p ∈ S, Complex.normSq (c k p) :=
    fun k => normSq_finset_sum_le_card_mul_sum_normSq S (c k)
  have hsum :
      (∑ k : ZMod (kloostermanGlobalPeriod Q),
        Complex.normSq (∑ p ∈ S, c k p)) ≤
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          (S.card : ℝ) * ∑ p ∈ S, Complex.normSq (c k p) :=
    Finset.sum_le_sum fun k _ => hpoint k
  calc
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq
            (∑ q ∈ Q, ∑ r ∈ Q.erase q,
              star (w q * kloostermanGlobalModulusTimeResponse q B b k.val) *
                (w r * kloostermanGlobalModulusTimeResponse r B b k.val)) =
      (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (∑ p ∈ S, c k p) := by
      apply congrArg (fun x : ℝ => (kloostermanGlobalPeriod Q : ℝ)⁻¹ * x)
      apply Fintype.sum_congr
      intro k
      congr 1
      exact Finset.sum_sigma' Q (fun q => Q.erase q)
        (fun q r =>
          star (w q * kloostermanGlobalModulusTimeResponse q B b k.val) *
            (w r * kloostermanGlobalModulusTimeResponse r B b k.val))
    _ ≤ (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          (S.card : ℝ) * ∑ p ∈ S, Complex.normSq (c k p) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (S.card : ℝ) *
        ∑ p ∈ S,
          ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
            ∑ k : ZMod (kloostermanGlobalPeriod Q), Complex.normSq (c k p)) := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [← Finset.mul_sum]
      ring
    _ ≤ (S.card : ℝ) *
        ∑ p ∈ S,
          Complex.normSq (w p.1) * Complex.normSq (w p.2) *
            (((p.1 + 1 : ℕ) : ℝ) ^ 2 * ((p.2 + 1 : ℕ) : ℝ) *
              (∑ z : ZMod (p.1 + 1),
                Complex.normSq (kloostermanSourceResidue (p.1 + 1) B b z)) *
              ∑ z : ZMod (p.2 + 1),
                Complex.normSq (kloostermanSourceResidue (p.2 + 1) B b z)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro p hp
        rcases p with ⟨q, r⟩
        have hr : r ∈ Q.erase q := (Finset.mem_sigma.mp hp).2
        have hpair := average_normSq_kloostermanGlobalModulusTimeResponse_mul_le
          Q q r (Finset.mem_of_mem_erase hr) B b
        dsimp only [c]
        simp only [Complex.normSq_mul, normSq_star]
        calc
          (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
              ∑ k : ZMod (kloostermanGlobalPeriod Q),
                (Complex.normSq (w q) *
                    Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val)) *
                  (Complex.normSq (w r) *
                    Complex.normSq (kloostermanGlobalModulusTimeResponse r B b k.val)) =
            (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
              ∑ k : ZMod (kloostermanGlobalPeriod Q),
                (Complex.normSq (w q) * Complex.normSq (w r)) *
                  (Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
                    Complex.normSq
                      (kloostermanGlobalModulusTimeResponse r B b k.val)) := by
            apply congrArg (fun x : ℝ => (kloostermanGlobalPeriod Q : ℝ)⁻¹ * x)
            apply Fintype.sum_congr
            intro k
            ring
          _ =
            Complex.normSq (w q) * Complex.normSq (w r) *
              ((kloostermanGlobalPeriod Q : ℝ)⁻¹ *
                ∑ k : ZMod (kloostermanGlobalPeriod Q),
                  Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) *
                    Complex.normSq
                      (kloostermanGlobalModulusTimeResponse r B b k.val)) := by
            rw [← Finset.mul_sum]
            ring
          _ ≤ Complex.normSq (w q) * Complex.normSq (w r) *
              (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
                (∑ z : ZMod (q + 1),
                  Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
                ∑ z : ZMod (r + 1),
                  Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) :=
            mul_le_mul_of_nonneg_left hpair
              (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      · positivity
    _ = ((Q.card * (Q.card - 1) : ℕ) : ℝ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          Complex.normSq (w q) * Complex.normSq (w r) *
            (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              (∑ z : ZMod (q + 1),
                Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
              ∑ z : ZMod (r + 1),
                Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) := by
      dsimp only [S]
      rw [card_sigma_erase_eq_card_mul_pred]
      congr 1
      exact (Finset.sum_sigma' Q (fun q => Q.erase q)
        (fun q r =>
          Complex.normSq (w q) * Complex.normSq (w r) *
            (((q + 1 : ℕ) : ℝ) ^ 2 * ((r + 1 : ℕ) : ℝ) *
              (∑ z : ZMod (q + 1),
                Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
              ∑ z : ZMod (r + 1),
                Complex.normSq (kloostermanSourceResidue (r + 1) B b z)))).symm

end

end RHTower.Sieve
