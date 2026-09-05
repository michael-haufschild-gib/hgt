import GaloisForLFunctions.HTGeometry.ArithmeticSecondOrderObstruction

/-!
# Arithmetic interaction reconstructed from integer scale response

For an exact Leibniz law `f` and a second-order lift `g` with bilinear source `B`,
the normalized discrepancy between multiplication and repeated addition obeys

`q^(-k) • (g(m*q^k) - m • g(q^k)) = g(m) + (k/q) • B(f(m),f(q))`.

The discrepancy is an exact finite sum of additive carries. Its increment reconstructs
the interaction, retaining its vector value. Consequently bounded returns at arbitrarily
sparse integer power scales are equivalent to zero interaction. Bounds and return schedules
may depend on the pair of integer inputs; no bound on `f`, completeness, finite dimension,
integrality, positivity, or phase choice is required.

These are laws of the stated arithmetic deformation class. They do not construct a
deformation associated with an actual Xi zero or establish its bounded returns.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplying the input versus adding the same number of copies of its response. -/
def arithmeticReplicationDefect (g : ℕ → F) (m n : ℕ) : F :=
  g (m * n) - (m : ℝ) • g n

/-- The discrepancy is exactly the sum of the individual additive carries, with no
discarded endpoint or limiting convention. -/
theorem arithmeticReplicationDefect_eq_sum (g : ℕ → F) (h0 : g 0 = 0) (m n : ℕ) :
    arithmeticReplicationDefect g m n =
      ∑ j ∈ Finset.range m, (g (j * n + n) - g (j * n) - g n) := by
  induction m with
  | zero => simp [arithmeticReplicationDefect, h0]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [arithmeticReplicationDefect, Nat.add_mul, one_mul,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

/-- The replication discrepancy per unit input mass, on literal integer power scales. -/
noncomputable def arithmeticPowerResponse (g : ℕ → F) (m q k : ℕ) : F :=
  ((q : ℝ) ^ k)⁻¹ • arithmeticReplicationDefect g m (q ^ k)

/-- The first-order law gives an exact response on every integer power, including depth zero. -/
theorem IsArithmeticLeibniz.normalized_power {f : ℕ → E}
    (hf : IsArithmeticLeibniz f) {q : ℕ} (hq : 0 < q) (k : ℕ) :
    ((q : ℝ) ^ k)⁻¹ • f (q ^ k) = ((k : ℝ) / q) • f q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  cases k with
  | zero => simp [hf.map_one]
  | succ k =>
    rw [hf.map_pow_succ]
    simp only [smul_smul]
    congr 1
    push_cast
    field_simp
    rw [pow_succ]

/-- Both source operations determine the whole scale trajectory, not just an estimate. -/
theorem arithmeticPowerResponse_eq_affine
    {f : ℕ → E} {g : ℕ → F} (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + B (f m) (f n))
    (m : ℕ) {q : ℕ} (hq : 0 < q) (k : ℕ) :
    arithmeticPowerResponse g m q k = g m + ((k : ℝ) / q) • B (f m) (f q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hsplit : arithmeticReplicationDefect g m (q ^ k) =
      ((q : ℝ) ^ k) • g m + B (f m) (f (q ^ k)) := by
    rw [arithmeticReplicationDefect, hg]
    simp only [Nat.cast_pow]
    abel
  rw [arithmeticPowerResponse, hsplit, smul_add, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero k hq0), one_smul]
  congr 1
  rw [← map_smul, hf.normalized_power hq, map_smul]

/-- A single increment of the same source response reconstructs its bilinear interaction. -/
theorem arithmeticInteraction_eq_response_increment
    {f : ℕ → E} {g : ℕ → F} (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + B (f m) (f n))
    (m : ℕ) {q : ℕ} (hq : 0 < q) (k : ℕ) :
    (q : ℝ) • (arithmeticPowerResponse g m q (k + 1) -
      arithmeticPowerResponse g m q k) = B (f m) (f q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  rw [arithmeticPowerResponse_eq_affine B hf hg m hq,
    arithmeticPowerResponse_eq_affine B hf hg m hq]
  rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul]
  have hc : (q : ℝ) * (((k + 1 : ℕ) : ℝ) / q - (k : ℝ) / q) = 1 := by
    push_cast
    field_simp
    ring
  rw [hc, one_smul]

private theorem affine_cofinal_bounded_iff (a v : F) :
    (∃ C : ℝ, ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ ‖a + (k : ℝ) • v‖ ≤ C) ↔ v = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hv
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    obtain ⟨K, hK⟩ := exists_nat_gt ((C + ‖a‖) / ‖v‖)
    obtain ⟨k, hKk, hk⟩ := hC K
    have hkr : (K : ℝ) ≤ k := by exact_mod_cast hKk
    have hlarge : C + ‖a‖ < (k : ℝ) * ‖v‖ := by
      apply (div_lt_iff₀ hvnorm).mp
      exact hK.trans_le hkr
    have hnorm : (k : ℝ) * ‖v‖ ≤ ‖a + (k : ℝ) • v‖ + ‖a‖ := by
      have h := norm_sub_le (a + (k : ℝ) • v) a
      simpa only [add_sub_cancel_left, norm_smul, Real.norm_natCast] using h
    linarith
  · intro hv
    refine ⟨‖a‖, fun K => ⟨K, le_rfl, ?_⟩⟩
    simp [hv]

/-- A cofinal sequence of bounded returns suffices; neither a uniform-in-scale bound nor
an estimate on the first-order law is required. The bound and return sequence may depend
on both integer inputs. -/
theorem arithmeticPowerResponse_boundedReturns_iff
    {f : ℕ → E} {g : ℕ → F} (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + B (f m) (f n))
    (m : ℕ) {q : ℕ} (hq : 0 < q) :
    (∃ C : ℝ, ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ ‖arithmeticPowerResponse g m q k‖ ≤ C) ↔
      B (f m) (f q) = 0 := by
  have hq0 : (q : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.ne_of_gt hq)
  have heq (k : ℕ) : arithmeticPowerResponse g m q k =
      g m + (k : ℝ) • ((q : ℝ)⁻¹ • B (f m) (f q)) := by
    rw [arithmeticPowerResponse_eq_affine B hf hg m hq, smul_smul, div_eq_mul_inv]
  simp_rw [heq]
  rw [affine_cofinal_bounded_iff, smul_eq_zero]
  simp [hq0]

/-- Complete classification for one exact arithmetic lift: cofinal bounded returns on
each integer power ray are equivalent to vanishing of all its bilinear interactions. -/
theorem arithmeticSecondOrder_cofinalReturns_iff
    {f : ℕ → E} {g : ℕ → F} (B : E →ₗ[ℝ] E →ₗ[ℝ] F)
    (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + B (f m) (f n)) :
    (∀ m q : ℕ, 0 < q → ∃ C : ℝ, ∀ K : ℕ,
      ∃ k : ℕ, K ≤ k ∧ ‖arithmeticPowerResponse g m q k‖ ≤ C) ↔
      ∀ m n, B (f m) (f n) = 0 := by
  constructor
  · intro h m n
    by_cases hn : n = 0
    · simp [hn, hf.map_zero]
    · exact (arithmeticPowerResponse_boundedReturns_iff B hf hg m (Nat.pos_of_ne_zero hn)).mp
        (h m n (Nat.pos_of_ne_zero hn))
  · intro h m q hq
    exact (arithmeticPowerResponse_boundedReturns_iff B hf hg m hq).mpr (h m q)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [IsReduced A]

/-- For multiplication in a reduced algebra, sparse returns of the exact second-order
response already force the tangent to vanish. No bound on that tangent is imposed. -/
theorem arithmeticSecondOrder_cofinalReturns_iff_tangent_zero
    {f g : ℕ → A} (hf : IsArithmeticLeibniz f)
    (hg : ∀ m n, g (m * n) = (m : ℝ) • g n + (n : ℝ) • g m + f m * f n) :
    (∀ m q : ℕ, 0 < q → ∃ C : ℝ, ∀ K : ℕ,
      ∃ k : ℕ, K ≤ k ∧ ‖arithmeticPowerResponse g m q k‖ ≤ C) ↔ f = 0 := by
  rw [arithmeticSecondOrder_cofinalReturns_iff (LinearMap.mul ℝ A) hf hg]
  constructor
  · intro h
    funext n
    exact eq_zero_of_pow_eq_zero (n := 2) (by simpa [pow_two] using h n n)
  · intro h m n
    simp [h]

end GaloisForLFunctions.HTGeometry

