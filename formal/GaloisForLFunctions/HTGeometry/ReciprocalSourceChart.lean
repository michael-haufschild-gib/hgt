import GaloisForLFunctions.HTGeometry.TriangularPolynomialAutomorphism
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The reciprocal source chart: squaring and inversion of unit jets are automorphisms

On the unit-jet chart `Z = 1 + ∑_{q=1}^{M} z_q t^q`, the coefficients of `Z²` are
`h_q = 2 z_q + (a polynomial in z_1, …, z_{q-1})` (`(12)`), so `z ↦ h` is a triangular
automorphism of `K[z_1, …, z_M]` in characteristic zero.  Likewise the coefficients of `Z⁻¹`
are `w_q = -z_q + (a polynomial in z_1, …, z_{q-1})`, so reciprocal inversion is an automorphism of
the unit-jet chart (in particular birational).

* `HTGeometry.unitJet`, `HTGeometry.coeff_unitJet`.
* `HTGeometry.jetSqCoeff`, `HTGeometry.jetSqCoeff_succ_sub_mem` : `(12)`.
* `HTGeometry.jetSqEquiv` : `h ↦ coefficients of Z²` as a `K`-algebra automorphism.
* `HTGeometry.recipCoeff`, `HTGeometry.unitJet_mul_recip_coeff`, `HTGeometry.recipEquiv`.
-/

namespace HTGeometry

open MvPolynomial

variable (K : Type*) [Field K] (M : ℕ)

/-- The unit jet `Z = 1 + ∑_{i<M} z_i t^{i+1}`. -/
noncomputable def unitJet : Polynomial (MvPolynomial (Fin M) K) :=
  1 + ∑ i : Fin M, Polynomial.C (X i) * Polynomial.X ^ ((i : ℕ) + 1)

variable {K M}

theorem coeff_unitJet (a : ℕ) :
    (unitJet K M).coeff a = if a = 0 then 1 else if h : a - 1 < M then X ⟨a - 1, h⟩ else 0 := by
  rw [unitJet, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [if_neg ha, zero_add, if_neg ha]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨a - 1, h⟩]
      · rw [if_pos (by simp only; omega)]
      · intro b _ hb
        rw [if_neg]
        intro hab
        exact hb (Fin.ext (by simp only; omega))
      · simp
    · refine Finset.sum_eq_zero fun b _ => if_neg ?_
      intro hab
      have := b.isLt
      omega

theorem coeff_unitJet_mem {q : Fin M} {a : ℕ} (ha : a ≤ q) : (unitJet K M).coeff a ∈ lowerVars q := by
  rw [coeff_unitJet]
  split_ifs with h0 h
  · exact Subalgebra.one_mem _
  · exact Algebra.subset_adjoin ⟨⟨a - 1, h⟩, by rw [Set.mem_setOf_eq, Fin.lt_def]; simp only; omega,
      rfl⟩
  · exact Subalgebra.zero_mem _

variable (K M) in
/-- **The coefficients of `Z²`.** -/
noncomputable def jetSqCoeff (q : ℕ) : MvPolynomial (Fin M) K := ((unitJet K M) ^ 2).coeff q

/-- **`(12)`: `h_q = 2 z_q + (a polynomial in z_1, …, z_{q-1})`.** -/
theorem jetSqCoeff_succ_sub_mem (q : Fin M) :
    jetSqCoeff K M ((q : ℕ) + 1) - C 2 * X q ∈ lowerVars (K := K) q := by
  set c := fun a => (unitJet K M).coeff a
  have hc0 : c 0 = 1 := by simp [c, coeff_unitJet]
  have hcq : c ((q : ℕ) + 1) = X q := by
    simp only [c, coeff_unitJet, Nat.add_sub_cancel, dif_pos q.isLt]
    rw [if_neg (Nat.succ_ne_zero _)]
  have hsum : jetSqCoeff K M ((q : ℕ) + 1) = ∑ k ∈ Finset.range ((q : ℕ) + 2), c k * c ((q : ℕ) + 1 - k) := by
    rw [jetSqCoeff, pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => c i * c j)]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_zero, Nat.sub_self, hc0, hcq,
    mul_one, one_mul]
  have hmid : ∑ k ∈ Finset.range (q : ℕ), c (k + 1) * c ((q : ℕ) + 1 - (k + 1)) ∈ lowerVars (K := K) q :=
    Subalgebra.sum_mem _ fun k hk => by
      rw [Finset.mem_range] at hk
      exact Subalgebra.mul_mem _ (coeff_unitJet_mem (by omega)) (coeff_unitJet_mem (by omega))
  convert hmid using 1
  rw [map_ofNat]
  ring

variable (K M) in
/-- The squaring map `h_q ↦ [t^{q}] Z²` on `K[h_1, …, h_M]`. -/
noncomputable def jetSqMap : MvPolynomial (Fin M) K →ₐ[K] MvPolynomial (Fin M) K :=
  aeval fun q : Fin M => jetSqCoeff K M ((q : ℕ) + 1)

variable (K M) in
/-- **The squaring map is an automorphism** in characteristic zero. -/
noncomputable def jetSqEquiv [CharZero K] : MvPolynomial (Fin M) K ≃ₐ[K] MvPolynomial (Fin M) K :=
  triangularEquiv (jetSqMap K M) (fun _ => 2) (fun _ => two_ne_zero) fun q => by
    rw [jetSqMap, aeval_X]
    exact jetSqCoeff_succ_sub_mem q

theorem jetSqEquiv_X [CharZero K] (q : Fin M) : jetSqEquiv K M (X q) = jetSqCoeff K M ((q : ℕ) + 1) := by
  change jetSqMap K M (X q) = _
  rw [jetSqMap, aeval_X]

/-! ## Reciprocal inversion -/

theorem adjoin_lt_mono {b c : ℕ} (h : b ≤ c) :
    Algebra.adjoin K ((X : Fin M → MvPolynomial (Fin M) K) '' {i : Fin M | (i : ℕ) < b})
      ≤ Algebra.adjoin K ((X : Fin M → MvPolynomial (Fin M) K) '' {i : Fin M | (i : ℕ) < c}) :=
  Algebra.adjoin_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem adjoin_lt_le_lowerVars {b : ℕ} {q : Fin M} (h : b ≤ q) :
    Algebra.adjoin K ((X : Fin M → MvPolynomial (Fin M) K) '' {i : Fin M | (i : ℕ) < b})
      ≤ lowerVars (K := K) q :=
  Algebra.adjoin_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

variable (K M) in
/-- **The coefficients of `Z⁻¹`** (the inverse of the unit jet as a power series). -/
noncomputable def recipCoeff (q : ℕ) : MvPolynomial (Fin M) K :=
  PowerSeries.coeff q (PowerSeries.invOfUnit (unitJet K M : PowerSeries (MvPolynomial (Fin M) K)) 1)

/-- **`Z · Z⁻¹ = 1`**: the recursion `w_{n+1} = -∑_{k ≤ n} z_{k+1} w_{n-k}`. -/
theorem recipCoeff_succ (n : ℕ) :
    recipCoeff K M (n + 1)
      = -∑ k ∈ Finset.range (n + 1), (unitJet K M).coeff (k + 1) * recipCoeff K M (n - k) := by
  have h := congrArg (PowerSeries.coeff (n + 1))
    (PowerSeries.mul_invOfUnit (unitJet K M : PowerSeries (MvPolynomial (Fin M) K)) 1 (by
      rw [Polynomial.constantCoeff_coe, coeff_unitJet, if_pos rfl, Units.val_one]))
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i
      (unitJet K M : PowerSeries (MvPolynomial (Fin M) K)) * PowerSeries.coeff j _),
    Finset.sum_range_succ'] at h
  have h0 : PowerSeries.coeff 0 (unitJet K M : PowerSeries (MvPolynomial (Fin M) K)) = 1 := by
    rw [Polynomial.coeff_coe, coeff_unitJet, if_pos rfl]
  rw [h0, one_mul, Nat.sub_zero] at h
  rw [eq_neg_iff_add_eq_zero, add_comm]
  refine Eq.trans ?_ h
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_coe, recipCoeff, Nat.add_sub_add_right]

theorem recipCoeff_mem (b : ℕ) :
    recipCoeff K M b ∈ Algebra.adjoin K ((X : Fin M → MvPolynomial (Fin M) K) '' {i : Fin M | (i : ℕ) < b}) := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    rcases b with _ | n
    · rw [recipCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
      exact Subalgebra.one_mem _
    · rw [recipCoeff_succ]
      refine Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun k hk => Subalgebra.mul_mem _ ?_ ?_)
      · rw [Finset.mem_range] at hk
        rw [coeff_unitJet, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
        split_ifs with h
        · exact Algebra.subset_adjoin ⟨⟨k, h⟩, show k < n + 1 from hk, rfl⟩
        · exact Subalgebra.zero_mem _
      · rw [Finset.mem_range] at hk
        exact adjoin_lt_mono (by omega) (ih (n - k) (by omega))

/-- **Reciprocal inversion is triangular**: `w_q = -z_q + (a polynomial in z_1, …, z_{q-1})`. -/
theorem recipCoeff_succ_add_mem (q : Fin M) :
    recipCoeff K M ((q : ℕ) + 1) - C (-1) * X q ∈ lowerVars (K := K) q := by
  rw [recipCoeff_succ, Finset.sum_range_succ, Nat.sub_self]
  have hw0 : recipCoeff K M 0 = 1 := by
    rw [recipCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  rw [hw0, mul_one, coeff_unitJet, if_neg (Nat.succ_ne_zero _), Nat.add_sub_cancel, dif_pos q.isLt]
  have hrest : ∑ k ∈ Finset.range (q : ℕ), (unitJet K M).coeff (k + 1) * recipCoeff K M (q - k)
      ∈ lowerVars (K := K) q :=
    Subalgebra.sum_mem _ fun k hk => by
      rw [Finset.mem_range] at hk
      exact Subalgebra.mul_mem _ (coeff_unitJet_mem (by omega))
        (adjoin_lt_le_lowerVars (by omega) (recipCoeff_mem _))
  convert Subalgebra.neg_mem _ hrest using 1
  rw [map_neg, map_one]
  ring

variable (K M) in
/-- The inversion map `w_q ↦ [t^q] Z⁻¹` on `K[w_1, …, w_M]`. -/
noncomputable def recipMap : MvPolynomial (Fin M) K →ₐ[K] MvPolynomial (Fin M) K :=
  aeval fun q : Fin M => recipCoeff K M ((q : ℕ) + 1)

variable (K M) in
/-- **Reciprocal inversion is an automorphism of the unit-jet chart** (in particular birational). -/
noncomputable def recipEquiv : MvPolynomial (Fin M) K ≃ₐ[K] MvPolynomial (Fin M) K :=
  triangularEquiv (recipMap K M) (fun _ => -1) (fun _ => neg_ne_zero.mpr one_ne_zero) fun q => by
    rw [recipMap, aeval_X]
    exact recipCoeff_succ_add_mem q

end HTGeometry
