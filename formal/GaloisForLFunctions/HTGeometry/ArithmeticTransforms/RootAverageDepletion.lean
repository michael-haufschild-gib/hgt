import GaloisForLFunctions.HTGeometry.RootOfUnityPacketFilter
import GaloisForLFunctions.HTGeometry.RootBlockMomentSelection

/-!+# Unit restriction in the polynomial Amice transform

Mori, arXiv:1910.09992, Theorem 2.11, restricts a measure to the units
by subtracting the average of its transforms under
`T ↦ ζ T + ζ - 1`. For finite atomic distributions on the nonnegative
integers, their Amice transforms are polynomials in `1 + T`.

The existing root-of-unity packet filter proves the exact restriction
formula: the average keeps precisely the atoms whose indices are
divisible by the averaging order. Its complement is idempotent and
commutes with every other such restriction. At prime order this is
restriction to the units; at composite order it deletes multiples.
-/

namespace GaloisForLFunctions.HTGeometry.ArithmeticTransforms

open Polynomial Finset

noncomputable section

/-- Root averaging keeps exponents divisible by the positive order `q`. -/
def rootAverage (q : ℕ+) (P : ℂ[X]) : ℂ[X] :=
  ((q : ℕ) : ℂ)⁻¹ • ∑ j ∈ range (q : ℕ), P.comp (C (unitRoot q ^ j) * X)

/-- Coefficientwise form of the root-of-unity averaging projector. -/
theorem coeff_rootAverage (q : ℕ+) (P : ℂ[X]) (k : ℕ) :
    (rootAverage q P).coeff k = if (q : ℕ) ∣ k then P.coeff k else 0 := by
  have hq : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  simp only [rootAverage, coeff_smul, smul_eq_mul, finsetSum_coeff,
    comp_C_mul_X_coeff, ← pow_mul, ← Finset.mul_sum]
  rw [_root_.HTGeometry.sum_primitiveRoot_pow_mul (unitRoot_isPrimitiveRoot q.pos.ne')]
  split_ifs <;> simp [hq, mul_comm]

/-- Delete atoms divisible by the averaging order. -/
def deplete (q : ℕ+) (P : ℂ[X]) : ℂ[X] := P - rootAverage q P

@[simp] theorem coeff_deplete (q : ℕ+) (P : ℂ[X]) (k : ℕ) :
    (deplete q P).coeff k = if (q : ℕ) ∣ k then 0 else P.coeff k := by
  rw [deplete, coeff_sub, coeff_rootAverage]
  split_ifs <;> simp

theorem rootAverage_idempotent (q : ℕ+) (P : ℂ[X]) :
    rootAverage q (rootAverage q P) = rootAverage q P := by
  ext k
  simp only [coeff_rootAverage]
  split_ifs <;> rfl

theorem deplete_idempotent (q : ℕ+) (P : ℂ[X]) : deplete q (deplete q P) = deplete q P := by
  ext k
  simp only [coeff_deplete]
  split_ifs <;> rfl

/-- Restrictions away from different divisors commute. -/
theorem deplete_comm (p q : ℕ+) (P : ℂ[X]) :
    deplete p (deplete q P) = deplete q (deplete p P) := by
  ext k
  simp only [coeff_deplete]
  split_ifs <;> rfl

/-- An exact characterization of the deleted subspace. -/
theorem deplete_eq_zero_iff (q : ℕ+) (P : ℂ[X]) :
    deplete q P = 0 ↔ ∀ k, ¬ (q : ℕ) ∣ k → P.coeff k = 0 := by
  constructor
  · intro h k hk
    have := congrArg (fun Q : ℂ[X] => Q.coeff k) h
    simpa only [coeff_deplete, if_neg hk, coeff_zero] using this
  · intro h
    ext k
    by_cases hk : (q : ℕ) ∣ k <;> simp [hk, h]

theorem rootAverage_sum {ι : Type*} (q : ℕ+) (s : Finset ι) (F : ι → ℂ[X]) :
    rootAverage q (∑ i ∈ s, F i) = ∑ i ∈ s, rootAverage q (F i) := by
  ext k
  simp only [coeff_rootAverage, finsetSum_coeff]
  by_cases h : (q : ℕ) ∣ k <;> simp [h]

theorem rootAverage_monomial (q : ℕ+) (k : ℕ) (a : ℂ) :
    rootAverage q (monomial k a) = if (q : ℕ) ∣ k then monomial k a else 0 := by
  ext j
  by_cases hj : k = j
  · subst j
    by_cases hd : (q : ℕ) ∣ k <;> simp [coeff_rootAverage, hd]
  · by_cases hd : (q : ℕ) ∣ k <;> simp [coeff_rootAverage, hd, coeff_monomial, hj]

/-- The polynomial `U` operator retains divisible indices and divides their exponents by `q`. -/
def atkinU (q : ℕ+) (P : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ P.support, if (q : ℕ) ∣ k then monomial (k / q) (P.coeff k) else 0

/-- The polynomial `V` operator multiplies every exponent by `q`. -/
def atkinV (q : ℕ+) (P : ℂ[X]) : ℂ[X] := P.comp (X ^ (q : ℕ))

/-- Root averaging is exactly `V U`, with no analytic or modular-form assumptions. -/
theorem atkinV_atkinU (q : ℕ+) (P : ℂ[X]) :
    atkinV q (atkinU q P) = rootAverage q P := by
  have hsum := congrArg (rootAverage q) (Polynomial.sum_monomial_eq P)
  rw [Polynomial.sum_def, rootAverage_sum] at hsum
  rw [← hsum]
  simp only [atkinV, atkinU, Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [rootAverage_monomial]
  by_cases hk : (q : ℕ) ∣ k
  · simp only [if_pos hk, monomial_comp, ← pow_mul]
    rw [Nat.mul_div_cancel' hk, C_mul_X_pow_eq_monomial]
  · simp [hk]

/-- The algebraic depletion operator is `1 - V U`. -/
theorem deplete_eq_one_sub_VU (q : ℕ+) (P : ℂ[X]) :
    deplete q P = P - atkinV q (atkinU q P) := by
  rw [atkinV_atkinU]
  rfl

theorem coeff_atkinU (q : ℕ+) (P : ℂ[X]) (k : ℕ) :
    (atkinU q P).coeff k = P.coeff ((q : ℕ) * k) := by
  calc
    (atkinU q P).coeff k = (atkinV q (atkinU q P)).coeff ((q : ℕ) * k) :=
      (Polynomial.coeff_expand_mul' q.pos (atkinU q P) k).symm
    _ = P.coeff ((q : ℕ) * k) := by
      rw [atkinV_atkinU, coeff_rootAverage, if_pos (dvd_mul_right _ _)]

/-- Downsampling is a left inverse to exponent dilation. -/
theorem atkinU_atkinV (q : ℕ+) (P : ℂ[X]) : atkinU q (atkinV q P) = P := by
  ext k
  rw [coeff_atkinU]
  exact Polynomial.coeff_expand_mul' q.pos P k

/-- The deleted subspace consists exactly of polynomials in `X^q`. -/
theorem deplete_eq_zero_iff_range_atkinV (q : ℕ+) (P : ℂ[X]) :
    deplete q P = 0 ↔ ∃ Q, atkinV q Q = P := by
  rw [deplete, sub_eq_zero]
  constructor
  · intro h
    exact ⟨atkinU q P, (atkinV_atkinU q P).trans h.symm⟩
  · rintro ⟨Q, rfl⟩
    rw [← atkinV_atkinU q (atkinV q Q), atkinU_atkinV]

theorem deplete_monomial (q : ℕ+) (k : ℕ) (a : ℂ) :
    deplete q (monomial k a) = if (q : ℕ) ∣ k then 0 else monomial k a := by
  rw [deplete, rootAverage_monomial]
  split_ifs <;> simp

/-- The polynomial Amice transform of an atomic distribution encoded by `P`. -/
def amice (P : ℂ[X]) : ℂ[X] := P.comp (X + 1)

/-- Affine root-average complement; at prime order this restricts to the units. -/
def amiceUnitPart (q : ℕ+) (F : ℂ[X]) : ℂ[X] :=
  F - ((q : ℕ) : ℂ)⁻¹ • ∑ j ∈ range (q : ℕ),
    F.comp (C (unitRoot q ^ j) * X + C (unitRoot q ^ j - 1))

/-- Mori's averaging formula is literal atom restriction after the Amice change of coordinate. -/
theorem amiceUnitPart_amice (q : ℕ+) (P : ℂ[X]) :
    amiceUnitPart q (amice P) = amice (deplete q P) := by
  simp only [amiceUnitPart, amice, deplete, sub_comp, rootAverage, smul_comp, Polynomial.sum_comp,
    comp_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [add_comp, X_comp, one_comp, mul_comp, C_comp]
  rw [map_sub, map_one]
  ring

/-- Every polynomial is the Amice transform of a unique atomic coefficient polynomial. -/
theorem amice_injective : Function.Injective amice := by
  intro P Q h
  have := congrArg (fun F : ℂ[X] => F.comp (X - 1)) h
  simpa [amice, comp_assoc] using this

theorem amice_surjective : Function.Surjective amice := by
  intro F
  refine ⟨F.comp (X - 1), ?_⟩
  simp [amice, comp_assoc]

/-- Affine root depletion is idempotent on all polynomial Amice transforms. -/
theorem amiceUnitPart_idempotent (q : ℕ+) (F : ℂ[X]) :
    amiceUnitPart q (amiceUnitPart q F) = amiceUnitPart q F := by
  obtain ⟨P, rfl⟩ := amice_surjective F
  rw [amiceUnitPart_amice, amiceUnitPart_amice, deplete_idempotent]

/-- Successive restrictions commute in the Serre–Tate coordinate as well. -/
theorem amiceUnitPart_comm (p q : ℕ+) (F : ℂ[X]) :
    amiceUnitPart p (amiceUnitPart q F) = amiceUnitPart q (amiceUnitPart p F) := by
  obtain ⟨P, rfl⟩ := amice_surjective F
  simp only [amiceUnitPart_amice, deplete_comm p q]

/-- At prime order, precisely the atoms prime to `p` survive the Amice unit restriction. -/
theorem amiceUnitPart_prime_atom (p : Nat.Primes) (k : ℕ) (a : ℂ) :
    amiceUnitPart ⟨p.val, p.property.pos⟩ (C a * (X + 1) ^ k) =
      if Nat.Coprime p.val k then C a * (X + 1) ^ k else 0 := by
  have hm : amice (monomial k a) = C a * (X + 1) ^ k := monomial_comp k
  rw [← hm, amiceUnitPart_amice, deplete_monomial, p.property.coprime_iff_not_dvd]
  by_cases hd : p.val ∣ k <;> simp [hd, amice]

/-- The logarithmic derivative reads atom indices in the ordinary polynomial coordinate. -/
def eulerPolynomial (P : ℂ[X]) : ℂ[X] := X * P.derivative

theorem coeff_eulerPolynomial (P : ℂ[X]) (k : ℕ) :
    (eulerPolynomial P).coeff k = P.coeff k * k := by
  cases k with
  | zero => simp [eulerPolynomial]
  | succ k => simp [eulerPolynomial, coeff_X_mul, coeff_derivative]

/-- Every iterate multiplies an atom by the corresponding power of its index. -/
theorem coeff_eulerPolynomial_iterate (r : ℕ) (P : ℂ[X]) (k : ℕ) :
    ((eulerPolynomial^[r]) P).coeff k = P.coeff k * (k : ℂ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', coeff_eulerPolynomial, ih, pow_succ, mul_assoc]

theorem deplete_eulerPolynomial (q : ℕ+) (P : ℂ[X]) :
    deplete q (eulerPolynomial P) = eulerPolynomial (deplete q P) := by
  ext k
  simp only [coeff_deplete, coeff_eulerPolynomial]
  by_cases hd : (q : ℕ) ∣ k <;> simp [hd]

/-- The moment derivative in the Amice coordinate. -/
def amiceTheta (F : ℂ[X]) : ℂ[X] := (X + 1) * F.derivative

theorem amiceTheta_amice (P : ℂ[X]) : amiceTheta (amice P) = amice (eulerPolynomial P) := by
  simp [amiceTheta, amice, eulerPolynomial, derivative_comp, mul_comp]

/-- Restricting atoms to the units commutes with taking moment derivatives. -/
theorem amiceUnitPart_theta (q : ℕ+) (F : ℂ[X]) :
    amiceUnitPart q (amiceTheta F) = amiceTheta (amiceUnitPart q F) := by
  obtain ⟨P, rfl⟩ := amice_surjective F
  rw [amiceTheta_amice, amiceUnitPart_amice, amiceUnitPart_amice, amiceTheta_amice,
    deplete_eulerPolynomial]

end

end GaloisForLFunctions.HTGeometry.ArithmeticTransforms

#print axioms GaloisForLFunctions.HTGeometry.ArithmeticTransforms.amiceUnitPart_amice
#print axioms GaloisForLFunctions.HTGeometry.ArithmeticTransforms.amiceUnitPart_idempotent
#print axioms GaloisForLFunctions.HTGeometry.ArithmeticTransforms.atkinU_atkinV
#print axioms GaloisForLFunctions.HTGeometry.ArithmeticTransforms.amiceUnitPart_prime_atom
#print axioms GaloisForLFunctions.HTGeometry.ArithmeticTransforms.amiceUnitPart_theta
