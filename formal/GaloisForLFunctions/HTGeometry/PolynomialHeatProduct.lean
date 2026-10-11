import GaloisForLFunctions.HTGeometry.PolynomialHeatFlow

/-!
# The polynomial heat operator and products

For a real polynomial `p` and `s ∈ ℝ` let `e^{sD²} p = Σ_k s^k/k! · p^{(2k)}` (`forwardPolyHeat`; a finite
sum).

**Product identity** (`forwardPolyHeat_mul`).

  `e^{sD²}(p q) = Σ_k (2s)^k/k! · (e^{sD²}p)^{(k)} · (e^{sD²}q)^{(k)}`   (`heatPair`).

Proof by induction on `q`: both sides are additive in `q`, agree on constants, and obey the same
rule under `q ↦ X q`, because `e^{sD²}(X r) = X e^{sD²}r + 2s D e^{sD²}r`
(`forwardPolyHeat_X_mul`), `heatPair P (X Q) = X heatPair P Q + 2s heatPair (DP) Q`
(`heatPair_X_mul_right`) and `D heatPair P Q = heatPair (DP) Q + heatPair P (DQ)`
(`derivative_heatPair`).

**Positivity closure** (`coeffNonneg_forwardPolyHeat_mul`).  For `s ≥ 0`: if `e^{sD²}p` and `e^{sD²}q`
have nonnegative coefficients, so does `e^{sD²}(pq)`, since derivatives and products of polynomials
with nonnegative coefficients have nonnegative coefficients.  The set of polynomials made
coefficient-positive by a given forward heat is closed under multiplication.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `Σ_{k<N} f k = Σ_{k<n} f k` when `f` vanishes from `n` on. -/
theorem sum_range_eq_of_vanish_from {M : Type*} [AddCommMonoid M] {f : ℕ → M} {n N : ℕ}
    (hnN : n ≤ N) (hf : ∀ k, n ≤ k → f k = 0) : ∑ k ∈ range N, f k = ∑ k ∈ range n, f k := by
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hnN) fun k _ hk => ?_
  exact hf k (by simpa using hk)

theorem iterate_derivative_add_poly (k : ℕ) (p q : ℝ[X]) :
    derivative^[k] (p + q) = derivative^[k] p + derivative^[k] q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply, derivative_add, ih]

theorem iterate_derivative_X_mul_poly (n : ℕ) (p : ℝ[X]) :
    derivative^[n + 1] (X * p) = X * derivative^[n + 1] p + C ((n : ℝ) + 1) * derivative^[n] p := by
  induction n with
  | zero =>
    simp only [Function.iterate_one, derivative_mul, derivative_X, one_mul, Function.iterate_zero,
      id_eq, Nat.cast_zero, zero_add, map_one]
    ring
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivative_add, derivative_mul, derivative_X,
      derivative_C_mul, ← Function.iterate_succ_apply' derivative (n + 1),
      ← Function.iterate_succ_apply' derivative n]
    push_cast
    rw [show C ((n : ℝ) + 1 + 1) = C ((n : ℝ) + 1) + 1 by rw [map_add, map_one]]
    ring

/-- The polynomial heat operator `e^{sD²} p = Σ_k s^k/k! · p^{(2k)}`. -/
def forwardPolyHeat (s : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree + 1), C (s ^ k / k.factorial) * derivative^[2 * k] p

/-- The forward heat is the backward heat `polyHeat` at negative time. -/
theorem forwardPolyHeat_eq_polyHeat (s : ℝ) (p : ℝ[X]) : forwardPolyHeat s p = polyHeat (-s) p := by
  unfold forwardPolyHeat polyHeat
  simp only [neg_neg]

theorem forwardPolyHeat_eq_sum {s : ℝ} {p : ℝ[X]} {N : ℕ} (hN : p.natDegree < 2 * N) :
    forwardPolyHeat s p = ∑ k ∈ range N, C (s ^ k / k.factorial) * derivative^[2 * k] p := by
  have hv : ∀ k, p.natDegree / 2 + 1 ≤ k →
      C (s ^ k / k.factorial) * derivative^[2 * k] p = 0 := by
    intro k hk
    rw [iterate_derivative_eq_zero (by omega), mul_zero]
  unfold forwardPolyHeat
  rw [sum_range_eq_of_vanish_from (N := p.natDegree + 1) (by omega) hv,
    sum_range_eq_of_vanish_from (N := N) (by omega) hv]

theorem forwardPolyHeat_add (s : ℝ) (p q : ℝ[X]) :
    forwardPolyHeat s (p + q) = forwardPolyHeat s p + forwardPolyHeat s q := by
  have hpq := natDegree_add_le p q
  rw [forwardPolyHeat_eq_sum (N := p.natDegree + q.natDegree + 1) (by omega),
    forwardPolyHeat_eq_sum (N := p.natDegree + q.natDegree + 1) (p := p) (by omega),
    forwardPolyHeat_eq_sum (N := p.natDegree + q.natDegree + 1) (p := q) (by omega),
    ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_add_poly, mul_add]

theorem forwardPolyHeat_C_mul (s c : ℝ) (p : ℝ[X]) : forwardPolyHeat s (C c * p) = C c * forwardPolyHeat s p := by
  have h := natDegree_C_mul_le c p
  rw [forwardPolyHeat_eq_sum (N := p.natDegree + 1) (by omega),
    forwardPolyHeat_eq_sum (N := p.natDegree + 1) (p := p) (by omega), mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_C_mul]
  ring

theorem forwardPolyHeat_C (s c : ℝ) : forwardPolyHeat s (C c) = C c := by
  unfold forwardPolyHeat
  simp

theorem derivative_forwardPolyHeat (s : ℝ) (p : ℝ[X]) :
    derivative (forwardPolyHeat s p) = forwardPolyHeat s (derivative p) := by
  have h := natDegree_derivative_le p
  rw [forwardPolyHeat_eq_sum (N := p.natDegree + 1) (p := p) (by omega),
    forwardPolyHeat_eq_sum (N := p.natDegree + 1) (p := derivative p) (by omega), derivative_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul, ← Function.iterate_succ_apply' derivative, Function.iterate_succ_apply]

/-- **Commutation with `X`.**  `e^{sD²}(X p) = X e^{sD²}p + 2s D e^{sD²}p`. -/
theorem forwardPolyHeat_X_mul (s : ℝ) (p : ℝ[X]) :
    forwardPolyHeat s (X * p) = X * forwardPolyHeat s p + C (2 * s) * derivative (forwardPolyHeat s p) := by
  have hX : (X * p).natDegree ≤ p.natDegree + 1 := by
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [natDegree_X_mul hp]
  set N := p.natDegree + 1 with hN
  rw [forwardPolyHeat_eq_sum (N := N + 1) (p := X * p) (by omega), derivative_forwardPolyHeat,
    forwardPolyHeat_eq_sum (N := N + 1) (p := p) (by omega),
    forwardPolyHeat_eq_sum (N := N) (p := derivative p) (by have := natDegree_derivative_le p; omega),
    mul_sum, mul_sum]
  have hL := Finset.sum_range_succ' (fun k => C (s ^ k / k.factorial) * derivative^[2 * k] (X * p)) N
  have hR := Finset.sum_range_succ' (fun k => X * (C (s ^ k / k.factorial) * derivative^[2 * k] p)) N
  rw [hL, hR]
  have hstep : ∀ j ∈ range N, C (s ^ (j + 1) / (j + 1).factorial) * derivative^[2 * (j + 1)] (X * p) =
      X * (C (s ^ (j + 1) / (j + 1).factorial) * derivative^[2 * (j + 1)] p) +
        C (2 * s) * (C (s ^ j / j.factorial) * derivative^[2 * j] (derivative p)) := by
    intro j _
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, iterate_derivative_X_mul_poly,
      show derivative^[2 * j] (derivative p) = derivative^[2 * j + 1] p from
        (Function.iterate_succ_apply derivative (2 * j) p).symm]
    have hf : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    have hc : C (s ^ (j + 1) / (j + 1).factorial) * C (((2 * j + 1 : ℕ) : ℝ) + 1) =
        C (2 * s) * C (s ^ j / j.factorial) := by
      rw [← map_mul, ← map_mul, hf]
      congr 1
      push_cast
      field_simp
      ring
    calc C (s ^ (j + 1) / (j + 1).factorial) * (X * derivative^[2 * j + 1 + 1] p +
          C (((2 * j + 1 : ℕ) : ℝ) + 1) * derivative^[2 * j + 1] p)
        = X * (C (s ^ (j + 1) / (j + 1).factorial) * derivative^[2 * j + 1 + 1] p) +
            (C (s ^ (j + 1) / (j + 1).factorial) * C (((2 * j + 1 : ℕ) : ℝ) + 1)) *
              derivative^[2 * j + 1] p := by ring
      _ = _ := by rw [hc]; ring
  rw [sum_congr rfl hstep, sum_add_distrib]
  simp only [Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, map_one, one_mul,
    mul_zero, Function.iterate_zero, id_eq]
  ring

/-- `heatPair s P Q = Σ_k (2s)^k/k! · P^{(k)} Q^{(k)}`. -/
def heatPair (s : ℝ) (P Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (P.natDegree + 1), C ((2 * s) ^ k / k.factorial) *
    (derivative^[k] P * derivative^[k] Q)

theorem heatPair_eq_sum {s : ℝ} {P Q : ℝ[X]} {N : ℕ} (hN : P.natDegree < N) :
    heatPair s P Q = ∑ k ∈ range N, C ((2 * s) ^ k / k.factorial) *
      (derivative^[k] P * derivative^[k] Q) := by
  have hv : ∀ k, P.natDegree + 1 ≤ k →
      C ((2 * s) ^ k / k.factorial) * (derivative^[k] P * derivative^[k] Q) = 0 := by
    intro k hk
    rw [iterate_derivative_eq_zero (by omega), zero_mul, mul_zero]
  unfold heatPair
  rw [sum_range_eq_of_vanish_from (N := N) (by omega) hv]

theorem heatPair_add_right (s : ℝ) (P Q₁ Q₂ : ℝ[X]) :
    heatPair s P (Q₁ + Q₂) = heatPair s P Q₁ + heatPair s P Q₂ := by
  unfold heatPair
  rw [← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_add_poly]
  ring

theorem heatPair_C_right (s : ℝ) (P : ℝ[X]) (c : ℝ) : heatPair s P (C c) = P * C c := by
  unfold heatPair
  rw [sum_range_succ', sum_eq_zero fun k _ => by
    rw [iterate_derivative_C (Nat.succ_pos k), mul_zero, mul_zero]]
  simp

theorem derivative_heatPair (s : ℝ) (P Q : ℝ[X]) :
    derivative (heatPair s P Q) = heatPair s (derivative P) Q + heatPair s P (derivative Q) := by
  have h := natDegree_derivative_le P
  rw [heatPair_eq_sum (N := P.natDegree + 1) (P := P) (by omega),
    heatPair_eq_sum (N := P.natDegree + 1) (P := derivative P) (by omega),
    heatPair_eq_sum (N := P.natDegree + 1) (P := P) (Q := derivative Q) (by omega),
    derivative_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul, derivative_mul, ← Function.iterate_succ_apply' derivative k P,
    ← Function.iterate_succ_apply' derivative k Q, Function.iterate_succ_apply,
    Function.iterate_succ_apply]
  ring

/-- `heatPair P (X Q) = X heatPair P Q + 2s heatPair (DP) Q`. -/
theorem heatPair_X_mul_right (s : ℝ) (P Q : ℝ[X]) :
    heatPair s P (X * Q) = X * heatPair s P Q + C (2 * s) * heatPair s (derivative P) Q := by
  have h := natDegree_derivative_le P
  set N := P.natDegree + 1 with hN
  rw [heatPair_eq_sum (N := N) (P := P) (Q := X * Q) (by omega),
    heatPair_eq_sum (N := N) (P := P) (Q := Q) (by omega),
    heatPair_eq_sum (N := N) (P := derivative P) (Q := Q) (by omega)]
  have hz1 : derivative^[N] (derivative P) = 0 := iterate_derivative_eq_zero (by omega)
  have hz2 : derivative^[N] P = 0 := iterate_derivative_eq_zero (by omega)
  have hext : ∑ k ∈ range N, C ((2 * s) ^ k / k.factorial) *
        (derivative^[k] (derivative P) * derivative^[k] Q) =
      ∑ k ∈ range (N + 1), C ((2 * s) ^ k / k.factorial) *
        (derivative^[k] (derivative P) * derivative^[k] Q) := by
    rw [Finset.sum_range_succ (n := N), hz1, zero_mul, mul_zero, add_zero]
  have hext2 : ∑ k ∈ range N, C ((2 * s) ^ k / k.factorial) *
        (derivative^[k] P * derivative^[k] (X * Q)) =
      ∑ k ∈ range (N + 1), C ((2 * s) ^ k / k.factorial) *
        (derivative^[k] P * derivative^[k] (X * Q)) := by
    rw [Finset.sum_range_succ (n := N), hz2, zero_mul, mul_zero, add_zero]
  have hext3 : ∑ k ∈ range N, C ((2 * s) ^ k / k.factorial) *
        (derivative^[k] P * derivative^[k] Q) =
      ∑ k ∈ range (N + 1), C ((2 * s) ^ k / k.factorial) *
        (derivative^[k] P * derivative^[k] Q) := by
    rw [Finset.sum_range_succ (n := N), hz2, zero_mul, mul_zero, add_zero]
  rw [hext2, hext3]
  have hL := Finset.sum_range_succ' (fun k => C ((2 * s) ^ k / k.factorial) *
    (derivative^[k] P * derivative^[k] (X * Q))) N
  have hR := Finset.sum_range_succ' (fun k => C ((2 * s) ^ k / k.factorial) *
    (derivative^[k] P * derivative^[k] Q)) N
  rw [hL, hR, mul_add, mul_sum, mul_sum]
  have hstep : ∀ j ∈ range N, C ((2 * s) ^ (j + 1) / (j + 1).factorial) *
      (derivative^[j + 1] P * derivative^[j + 1] (X * Q)) =
      X * (C ((2 * s) ^ (j + 1) / (j + 1).factorial) *
        (derivative^[j + 1] P * derivative^[j + 1] Q)) +
      C (2 * s) * (C ((2 * s) ^ j / j.factorial) *
        (derivative^[j] (derivative P) * derivative^[j] Q)) := by
    intro j _
    rw [iterate_derivative_X_mul_poly, ← Function.iterate_succ_apply derivative j P]
    have hf : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    have hc : C ((2 * s) ^ (j + 1) / (j + 1).factorial) * C ((j : ℝ) + 1) =
        C (2 * s) * C ((2 * s) ^ j / j.factorial) := by
      rw [← map_mul, ← map_mul, hf]
      congr 1
      field_simp
      ring
    calc C ((2 * s) ^ (j + 1) / (j + 1).factorial) *
          (derivative^[j + 1] P * (X * derivative^[j + 1] Q + C ((j : ℝ) + 1) * derivative^[j] Q))
        = X * (C ((2 * s) ^ (j + 1) / (j + 1).factorial) *
            (derivative^[j + 1] P * derivative^[j + 1] Q)) +
          (C ((2 * s) ^ (j + 1) / (j + 1).factorial) * C ((j : ℝ) + 1)) *
            (derivative^[j + 1] P * derivative^[j] Q) := by ring
      _ = _ := by rw [hc]; ring
  rw [sum_congr rfl hstep, sum_add_distrib]
  simp only [Nat.factorial_zero, pow_zero, Nat.cast_one, div_one, map_one, one_mul,
    Function.iterate_zero, id_eq]
  ring

/-- **The heat of a product.**
`e^{sD²}(p q) = Σ_k (2s)^k/k! · (e^{sD²}p)^{(k)} · (e^{sD²}q)^{(k)}`. -/
theorem forwardPolyHeat_mul (s : ℝ) (p q : ℝ[X]) :
    forwardPolyHeat s (p * q) = heatPair s (forwardPolyHeat s p) (forwardPolyHeat s q) := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [forwardPolyHeat_C, heatPair_C_right, mul_comm, forwardPolyHeat_C_mul, mul_comm]
  | add q₁ q₂ h₁ h₂ =>
    rw [mul_add, forwardPolyHeat_add, forwardPolyHeat_add, h₁, h₂, heatPair_add_right]
  | monomial n a ih =>
    have e : C a * X ^ (n + 1) = X * (C a * X ^ n) := by ring
    rw [e, show p * (X * (C a * X ^ n)) = X * (p * (C a * X ^ n)) by ring, forwardPolyHeat_X_mul,
      forwardPolyHeat_X_mul s (C a * X ^ n), ih, derivative_heatPair, heatPair_add_right,
      heatPair_X_mul_right]
    have : heatPair s (forwardPolyHeat s p) (C (2 * s) * derivative (forwardPolyHeat s (C a * X ^ n))) =
        C (2 * s) * heatPair s (forwardPolyHeat s p) (derivative (forwardPolyHeat s (C a * X ^ n))) := by
      unfold heatPair
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [iterate_derivative_C_mul]
      ring
    rw [this]
    ring

/-- Polynomials with nonnegative coefficients. -/
def CoeffNonneg (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n

theorem CoeffNonneg.add {p q : ℝ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p + q) := fun n => by rw [coeff_add]; exact add_nonneg (hp n) (hq n)

theorem CoeffNonneg.mul {p q : ℝ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p * q) := fun n => by
  rw [coeff_mul]
  exact sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)

theorem CoeffNonneg.C_mul {p : ℝ[X]} (hp : CoeffNonneg p) {c : ℝ} (hc : 0 ≤ c) :
    CoeffNonneg (C c * p) := fun n => by rw [coeff_C_mul]; exact mul_nonneg hc (hp n)

theorem CoeffNonneg.derivative {p : ℝ[X]} (hp : CoeffNonneg p) : CoeffNonneg (derivative p) :=
  fun n => by rw [coeff_derivative]; exact mul_nonneg (hp _) (by positivity)

theorem CoeffNonneg.iterate_derivative {p : ℝ[X]} (hp : CoeffNonneg p) (k : ℕ) :
    CoeffNonneg ((⇑Polynomial.derivative)^[k] p) := by
  induction k with
  | zero => exact hp
  | succ k ih => rw [Function.iterate_succ_apply']; exact CoeffNonneg.derivative ih

theorem CoeffNonneg.sum {ι : Type*} (S : Finset ι) {f : ι → ℝ[X]} (hf : ∀ i ∈ S, CoeffNonneg (f i)) :
    CoeffNonneg (∑ i ∈ S, f i) := fun n => by
  rw [finsetSum_coeff]
  exact sum_nonneg fun i hi => hf i hi n

/-- **Positivity closure under products.**  For `s ≥ 0`, if `e^{sD²}p` and `e^{sD²}q` have
nonnegative coefficients then so does `e^{sD²}(p q)`. -/
theorem coeffNonneg_forwardPolyHeat_mul {s : ℝ} (hs : 0 ≤ s) {p q : ℝ[X]}
    (hp : CoeffNonneg (forwardPolyHeat s p)) (hq : CoeffNonneg (forwardPolyHeat s q)) :
    CoeffNonneg (forwardPolyHeat s (p * q)) := by
  rw [forwardPolyHeat_mul]
  unfold heatPair
  exact CoeffNonneg.sum _ fun k _ =>
    CoeffNonneg.C_mul (CoeffNonneg.mul (CoeffNonneg.iterate_derivative hp k)
      (CoeffNonneg.iterate_derivative hq k)) (by positivity)

/-- Finite products. -/
theorem coeffNonneg_forwardPolyHeat_prod {s : ℝ} (hs : 0 ≤ s) {ι : Type*} (S : Finset ι) {f : ι → ℝ[X]}
    (hf : ∀ i ∈ S, CoeffNonneg (forwardPolyHeat s (f i))) :
    CoeffNonneg (forwardPolyHeat s (∏ i ∈ S, f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [prod_empty, ← C_1, forwardPolyHeat_C]
    intro n; rw [coeff_C]; split_ifs <;> norm_num
  | insert a S ha ih =>
    rw [prod_insert ha]
    exact coeffNonneg_forwardPolyHeat_mul hs (hf a (mem_insert_self a S))
      (ih fun i hi => hf i (mem_insert_of_mem hi))

end

end GaloisForLFunctions.HTGeometry
