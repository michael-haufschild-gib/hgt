import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma23I

/-!
# Convolution operators for the finite Matomäki--Teräväinen iteration

Lemma 2.3(ii) repeatedly adjoins one prime from a prescribed adic block to the coefficient
sequence.  Arithmetic-function convolution is the literal operation on those coefficients.  This
file identifies its evaluations with the source's divisor sums and boundary coefficient.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- A coefficient sequence, extended by zero at the forbidden arithmetic-function index `0`. -/
def mtCoefficientAF (α : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else α n, by simp⟩

@[simp] theorem mtCoefficientAF_apply_of_pos (α : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mtCoefficientAF α n = α n := by
  simp [mtCoefficientAF, hn.ne']

/-- Complex-valued sifting indicator as an arithmetic function. -/
def mtRhoAF (z : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => (rho n z : ℂ), by simp [rho]⟩

@[simp] theorem mtRhoAF_apply (z n : ℕ) : mtRhoAF z n = (rho n z : ℂ) := rfl

/-- Truncated Legendre kernel, again zeroed only at index `0`. -/
def mtTruncLegendreAF (z D : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (truncLegendre n z D : ℂ), by simp⟩

@[simp] theorem mtTruncLegendreAF_apply_of_pos (z D : ℕ) {n : ℕ} (hn : 0 < n) :
    mtTruncLegendreAF z D n = (truncLegendre n z D : ℂ) := by
  simp [mtTruncLegendreAF, hn.ne']

/-- Indicator of one finite prime block, viewed as a Dirichlet-convolution factor. -/
def mtPrimeBlockAF (S : Finset ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else if n ∈ S then 1 else 0, by simp⟩

@[simp] theorem mtPrimeBlockAF_apply_of_pos (S : Finset ℕ) {n : ℕ} (hn : 0 < n) :
    mtPrimeBlockAF S n = if n ∈ S then 1 else 0 := by
  simp [mtPrimeBlockAF, hn.ne']

/-- Boundary kernel with the source's prime-dependent sifting level. -/
def mtBoundaryKernel (S : Finset ℕ) (level : ℕ → ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
      ∑ q ∈ S, if q ∣ n then (rho (n / q) (level q) : ℂ) else 0,
    by simp⟩

@[simp] theorem mtBoundaryKernel_apply_of_pos
    (S : Finset ℕ) (level : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    mtBoundaryKernel S level n =
      ∑ q ∈ S, if q ∣ n then (rho (n / q) (level q) : ℂ) else 0 := by
  simp [mtBoundaryKernel, hn.ne']

/-- Re-extending an arithmetic function's coefficients changes nothing. -/
@[simp] theorem mtCoefficientAF_coe (a : ArithmeticFunction ℂ) :
    mtCoefficientAF (fun n => a n) = a := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtCoefficientAF]
  · simp [mtCoefficientAF, hn]

/-- Evaluation commutes with a finite sum of arithmetic functions. -/
theorem arithmeticFunction_finset_sum_apply
    {ι : Type*} (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (n : ℕ) :
    (∑ i ∈ S, F i) n = ∑ i ∈ S, F i n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, ih]

/-- Literal divisor sum against a sifting level. -/
def mtDivisorSiftSum (α : ℕ → ℂ) (z n : ℕ) : ℂ :=
  ∑ m ∈ n.divisors, α m * (rho (n / m) z : ℂ)

/-- Literal divisor sum against the truncated Legendre kernel. -/
def mtDivisorTruncSum (α : ℕ → ℂ) (z D n : ℕ) : ℂ :=
  ∑ m ∈ n.divisors, α m * (truncLegendre (n / m) z D : ℂ)

/-- A sifted divisor sum is exactly one Dirichlet-convolution coefficient. -/
theorem mtDivisorSiftSum_eq_mul_apply (α : ℕ → ℂ) (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtDivisorSiftSum α z n = (mtCoefficientAF α * mtRhoAF z) n := by
  rw [ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtCoefficientAF α x.1 * mtRhoAF z x.2) =
      ∑ m ∈ n.divisors, mtCoefficientAF α m * mtRhoAF z (n / m) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun m q => mtCoefficientAF α m * mtRhoAF z q)]
  unfold mtDivisorSiftSum
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
  have hqPos : 0 < n / m :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm)) hmPos
  simp [mtCoefficientAF_apply_of_pos α hmPos, mtRhoAF_apply]

/-- The finite Legendre main term is the matching convolution coefficient. -/
theorem mtDivisorTruncSum_eq_mul_apply
    (α : ℕ → ℂ) (z D : ℕ) {n : ℕ} (hn : 0 < n) :
    mtDivisorTruncSum α z D n = (mtCoefficientAF α * mtTruncLegendreAF z D) n := by
  rw [ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtCoefficientAF α x.1 * mtTruncLegendreAF z D x.2) =
      ∑ m ∈ n.divisors,
        mtCoefficientAF α m * mtTruncLegendreAF z D (n / m) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun m q => mtCoefficientAF α m * mtTruncLegendreAF z D q)]
  unfold mtDivisorTruncSum
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
  have hqPos : 0 < n / m :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm)) hmPos
  simp [mtCoefficientAF_apply_of_pos α hmPos,
    mtTruncLegendreAF_apply_of_pos z D hqPos]

/-- Adjoining one prime block to the coefficients is exactly the source boundary sum. -/
theorem mtC2BoundaryCoefficient_const_eq_mul_apply
    (α : ℕ → ℂ) (S : Finset ℕ) (z : ℕ) {n : ℕ} (hn : 0 < n) :
    mtC2BoundaryCoefficient α S (fun _ => z) n =
      ((mtCoefficientAF α * mtPrimeBlockAF S) * mtRhoAF z) n := by
  rw [mul_assoc, ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtCoefficientAF α x.1 * (mtPrimeBlockAF S * mtRhoAF z) x.2) =
      ∑ m ∈ n.divisors,
        mtCoefficientAF α m * (mtPrimeBlockAF S * mtRhoAF z) (n / m) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun m q => mtCoefficientAF α m * (mtPrimeBlockAF S * mtRhoAF z) q)]
  unfold mtC2BoundaryCoefficient
  rw [← sum_divisors_indicator_eq_sum_finset_dvd hn S
    (fun q => ∑ m ∈ (n / q).divisors,
      α m * (rho ((n / q) / m) z : ℂ))]
  have hswap := sum_divisors_quotient_swap hn
    (fun m q => if q ∈ S then α m * (rho (n / (m * q)) z : ℂ) else 0)
  have hreindex :
      (∑ q ∈ n.divisors, if q ∈ S then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) z : ℂ) else 0) =
        ∑ m ∈ n.divisors, ∑ q ∈ (n / m).divisors,
          if q ∈ S then α m * (rho ((n / m) / q) z : ℂ) else 0 := by
    calc
      (∑ q ∈ n.divisors, if q ∈ S then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) z : ℂ) else 0) =
        ∑ q ∈ n.divisors, ∑ m ∈ (n / q).divisors,
          if q ∈ S then α m * (rho ((n / q) / m) z : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            split_ifs <;> simp
      _ = ∑ m ∈ n.divisors, ∑ q ∈ (n / m).divisors,
          if q ∈ S then α m * (rho ((n / m) / q) z : ℂ) else 0 := by
            simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using hswap.symm
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
  have hnmPos : 0 < n / m :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm)) hmPos
  rw [ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ (n / m).divisorsAntidiagonal,
      mtPrimeBlockAF S x.1 * mtRhoAF z x.2) =
      ∑ q ∈ (n / m).divisors,
        mtPrimeBlockAF S q * mtRhoAF z ((n / m) / q) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n / m)
      (fun q k => mtPrimeBlockAF S q * mtRhoAF z k)]
  simp only [mtCoefficientAF_apply_of_pos α hmPos]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqPos : 0 < q := Nat.pos_of_mem_divisors hq
  rw [mtPrimeBlockAF_apply_of_pos S hqPos, mtRhoAF_apply]
  split_ifs <;> ring

/-- One constant-level block operator is its varying-level boundary kernel specialization. -/
theorem mtPrimeBlockAF_mul_mtRhoAF_eq_boundaryKernel_const
    (S : Finset ℕ) (z : ℕ) :
    mtPrimeBlockAF S * mtRhoAF z = mtBoundaryKernel S (fun _ => z) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [ArithmeticFunction.mul_apply]
    rw [show (∑ x ∈ n.divisorsAntidiagonal,
        mtPrimeBlockAF S x.1 * mtRhoAF z x.2) =
        ∑ q ∈ n.divisors, mtPrimeBlockAF S q * mtRhoAF z (n / q) by
      exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
        (fun q k => mtPrimeBlockAF S q * mtRhoAF z k)]
    rw [mtBoundaryKernel_apply_of_pos S (fun _ => z) hnPos]
    have hswap := sum_divisors_indicator_eq_sum_finset_dvd hnPos S
      (fun q => (rho (n / q) z : ℂ))
    calc
      (∑ q ∈ n.divisors, mtPrimeBlockAF S q * mtRhoAF z (n / q)) =
          ∑ q ∈ n.divisors,
            if q ∈ S then (rho (n / q) z : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqPos : 0 < q := Nat.pos_of_mem_divisors hq
        rw [mtPrimeBlockAF_apply_of_pos S hqPos, mtRhoAF_apply]
        split_ifs <;> ring
      _ = ∑ q ∈ S, if q ∣ n then (rho (n / q) z : ℂ) else 0 := hswap

/-- Pairwise-disjoint constant-level blocks assemble to the varying-level boundary kernel of
their union. -/
theorem sum_primeBlock_mul_rho_eq_boundaryKernel_biUnion
    {ι : Type*} (I : Finset ι) (block : ι → Finset ℕ)
    (cutoff : ι → ℕ) (S : Finset ℕ) (lower : ℕ → ℕ)
    (hdisj : (↑I : Set ι).PairwiseDisjoint block)
    (hunion : I.biUnion block = S)
    (hlower : ∀ i ∈ I, ∀ q ∈ block i, lower q = cutoff i) :
    (∑ i ∈ I, mtPrimeBlockAF (block i) * mtRhoAF (cutoff i)) =
      mtBoundaryKernel S lower := by
  classical
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [arithmeticFunction_finset_sum_apply]
    calc
      (∑ i ∈ I, (mtPrimeBlockAF (block i) * mtRhoAF (cutoff i)) n) =
          ∑ i ∈ I, mtBoundaryKernel (block i) (fun _ => cutoff i) n := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mtPrimeBlockAF_mul_mtRhoAF_eq_boundaryKernel_const]
      _ = ∑ i ∈ I, ∑ q ∈ block i,
          if q ∣ n then (rho (n / q) (lower q) : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mtBoundaryKernel_apply_of_pos (block i) (fun _ => cutoff i) hnPos]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hlower i hi q hq]
      _ = ∑ q ∈ I.biUnion block,
          if q ∣ n then (rho (n / q) (lower q) : ℂ) else 0 := by
        symm
        exact Finset.sum_biUnion hdisj
      _ = mtBoundaryKernel S lower n := by
        rw [hunion, mtBoundaryKernel_apply_of_pos S lower hnPos]

/-- The varying-level source boundary is convolution by `mtBoundaryKernel`. -/
theorem mtC2BoundaryCoefficient_eq_mul_boundaryKernel_apply
    (α : ℕ → ℂ) (S : Finset ℕ) (level : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    mtC2BoundaryCoefficient α S level n =
      (mtCoefficientAF α * mtBoundaryKernel S level) n := by
  rw [ArithmeticFunction.mul_apply]
  rw [show (∑ x ∈ n.divisorsAntidiagonal,
      mtCoefficientAF α x.1 * mtBoundaryKernel S level x.2) =
      ∑ m ∈ n.divisors,
        mtCoefficientAF α m * mtBoundaryKernel S level (n / m) by
    exact Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun m k => mtCoefficientAF α m * mtBoundaryKernel S level k)]
  unfold mtC2BoundaryCoefficient
  rw [← sum_divisors_indicator_eq_sum_finset_dvd hn S
    (fun q => ∑ m ∈ (n / q).divisors,
      α m * (rho ((n / q) / m) (level q) : ℂ))]
  have hswap := sum_divisors_quotient_swap hn
    (fun m q => if q ∈ S then
      α m * (rho (n / (m * q)) (level q) : ℂ) else 0)
  have hreindex :
      (∑ q ∈ n.divisors, if q ∈ S then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0) =
        ∑ m ∈ n.divisors, ∑ q ∈ (n / m).divisors,
          if q ∈ S then
            α m * (rho ((n / m) / q) (level q) : ℂ) else 0 := by
    calc
      (∑ q ∈ n.divisors, if q ∈ S then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0) =
        ∑ q ∈ n.divisors, ∑ m ∈ (n / q).divisors,
          if q ∈ S then
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro q hq
            split_ifs <;> simp
      _ = ∑ m ∈ n.divisors, ∑ q ∈ (n / m).divisors,
          if q ∈ S then
            α m * (rho ((n / m) / q) (level q) : ℂ) else 0 := by
            simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using hswap.symm
  rw [hreindex]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := Nat.pos_of_mem_divisors hm
  have hnmPos : 0 < n / m :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm)) hmPos
  rw [mtCoefficientAF_apply_of_pos α hmPos,
    mtBoundaryKernel_apply_of_pos S level hnmPos, Finset.mul_sum]
  simpa only [mul_ite, mul_zero] using
    (sum_divisors_indicator_eq_sum_finset_dvd hnmPos S
      (fun q => α m * (rho ((n / m) / q) (level q) : ℂ)))

end

end RHTower.Sieve
