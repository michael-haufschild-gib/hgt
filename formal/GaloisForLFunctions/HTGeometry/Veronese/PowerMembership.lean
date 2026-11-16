import GaloisForLFunctions.HTGeometry.Veronese.BoundedDecomposition
import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# All powers of the squarefree Veronese ideal

The `k`th power of the squarefree degree-`r` ideal contains a monomial
exactly when its exponents, capped at `k`, have sum at least `k * r`.
Lin–Zhang's integral decomposition lemma supplies the squarefree factors.
This extends the support-width criterion to the entire ideal filtration.
-/

namespace GaloisForLFunctions.VeroneseIdeal

open Finset MvPolynomial

noncomputable section

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Width of an exponent vector when each coordinate can fill at most `k` rows. -/
def cappedDegree (k : ℕ) (d : ι →₀ ℕ) : ℕ := ∑ i, min (d i) k

/-- Every nonzero coefficient has enough capped degree for `k` squarefree degree-`r` factors. -/
def CappedWide (k r : ℕ) (P : MvPolynomial ι R) : Prop :=
  ∀ d, coeff d P ≠ 0 → k * r ≤ cappedDegree k d

omit [DecidableEq ι] in
theorem cappedDegree_one (d : ι →₀ ℕ) : cappedDegree 1 d = d.support.card := by
  unfold cappedDegree
  calc
    (∑ i, min (d i) 1) = ∑ i ∈ d.support, min (d i) 1 := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hz : d i = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hi
      rw [hz]
      rfl
    _ = d.support.card := by
      rw [card_eq_sum_ones]
      apply sum_congr rfl
      intro i hi
      have := Finsupp.mem_support_iff.mp hi
      omega

omit [DecidableEq ι] in
private theorem cappedDegree_mono_right (k : ℕ) (a b : ι →₀ ℕ) :
    cappedDegree k b ≤ cappedDegree k (a + b) := by
  apply sum_le_sum
  intro i _
  simp only [Finsupp.add_apply]
  omega

/-- The capped support condition is an ideal condition. -/
def cappedWidthIdeal (k r : ℕ) : Ideal (MvPolynomial ι R) where
  carrier := {P | CappedWide k r P}
  zero_mem' := by intro d hd; exact (hd (by simp)).elim
  add_mem' := by
    intro P Q hP hQ d hd
    rw [coeff_add] at hd
    by_cases h : coeff d P = 0
    · exact hQ d (by simpa [h] using hd)
    · exact hP d h
  smul_mem' := by
    intro P Q hQ d hd
    change coeff d (P * Q) ≠ 0 at hd
    rw [coeff_mul] at hd
    obtain ⟨⟨a, b⟩, hab, hne⟩ := exists_ne_zero_of_sum_ne_zero hd
    have hb : coeff b Q ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hab' : a + b = d := mem_antidiagonal.mp hab
    exact (hQ b hb).trans (hab' ▸ cappedDegree_mono_right k a b)

private theorem cappedWide_mul (k r : ℕ) (P Q : MvPolynomial ι R)
    (hP : CappedWide k r P) (hQ : MonoWide r Q) : CappedWide (k + 1) r (P * Q) := by
  intro d hd
  rw [coeff_mul] at hd
  obtain ⟨⟨a, b⟩, hab, hne⟩ := exists_ne_zero_of_sum_ne_zero hd
  have ha : coeff a P ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have hb : coeff b Q ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hab' : a + b = d := mem_antidiagonal.mp hab
  have hcap : cappedDegree k a + cappedDegree 1 b ≤ cappedDegree (k + 1) d := by
    rw [cappedDegree, cappedDegree, ← sum_add_distrib, ← hab']
    apply sum_le_sum
    intro i _
    simp only [Finsupp.add_apply]
    omega
  rw [cappedDegree_one] at hcap
  have hp := hP a ha
  have hq := hQ b hb
  simpa only [Nat.add_mul, Nat.one_mul] using (add_le_add hp hq).trans hcap

/-- Every coefficient in an ideal power satisfies the capped degree bound. -/
theorem veroneseIdeal_pow_le_cappedWidthIdeal (k r : ℕ) :
    veroneseIdeal R ι r ^ k ≤ cappedWidthIdeal k r := by
  induction k with
  | zero =>
      intro P _ d _
      simp [cappedDegree]
  | succ k ih =>
      rw [pow_succ]
      apply Ideal.mul_le.mpr
      intro P hP Q hQ
      exact cappedWide_mul k r P Q (ih hP) (monoWide_of_mem_ideal hQ)

/-- A monomial written using all finitely many coordinates. -/
def vectorMonomial (a : ι → ℕ) : MvPolynomial ι R := ∏ i, X i ^ a i

private theorem squarefree_vector_mem (r : ℕ) (a : ι → ℕ)
    (ha : ∀ i, a i ≤ 1) (hs : (∑ i, a i) = r) :
    vectorMonomial (R := R) a ∈ veroneseIdeal R ι r := by
  let S : Finset ι := univ.filter fun i => a i = 1
  have hcard : S.card = r := by
    rw [show S.card = ∑ i, if a i = 1 then 1 else 0 by
      rw [card_eq_sum_ones, show S = univ.filter (fun i => a i = 1) from rfl, sum_filter]]
    convert hs using 1
    apply sum_congr rfl
    intro i _
    have := ha i
    split_ifs <;> omega
  have hprod : vectorMonomial (R := R) a = ∏ i ∈ S, X i := by
    rw [vectorMonomial, show S = univ.filter (fun i => a i = 1) from rfl, prod_filter]
    apply prod_congr rfl
    intro i _
    by_cases hi : a i = 1
    · rw [if_pos hi, hi, pow_one]
    · have hz : a i = 0 := by have := ha i; omega
      simp only [hz, pow_zero, zero_ne_one, if_false]
  rw [hprod]
  exact Ideal.subset_span ⟨S, hcard, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem fin_prod_mem_pow (I : Ideal (MvPolynomial ι R)) (k : ℕ)
    (f : Fin k → MvPolynomial ι R) (hf : ∀ j, f j ∈ I) :
    (∏ j, f j) ∈ I ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.prod_univ_succ, pow_succ']
      exact Ideal.mul_mem_mul (hf 0) (ih (fun j => f j.succ) (fun j => hf j.succ))

private theorem bounded_vector_mem_pow (k r : ℕ) (a : ι → ℕ)
    (ha : ∀ i, a i ≤ k) (hs : (∑ i, a i) = k * r) :
    vectorMonomial (R := R) a ∈ veroneseIdeal R ι r ^ k := by
  obtain ⟨β, hβs, hβb, hβα⟩ :=
    (bounded_degree_decomposition_iff k r (fun _ : ι => 1) a).mp
      ⟨hs, by simpa using ha⟩
  have hfactor : vectorMonomial (R := R) a =
      ∏ j, vectorMonomial (R := R) (β j) := by
    unfold vectorMonomial
    calc
      (∏ i, (X i : MvPolynomial ι R) ^ a i) = ∏ i, ∏ j, X i ^ β j i := by
        apply prod_congr rfl
        intro i _
        rw [prod_pow_eq_pow_sum, hβα]
      _ = _ := prod_comm
  rw [hfactor]
  exact fin_prod_mem_pow _ k _ (fun j => squarefree_vector_mem r (β j) (hβb j) (hβs j))

private theorem monomial_mem_pow_of_capped (k r : ℕ) (d : ι →₀ ℕ) (c : R)
    (hd : k * r ≤ cappedDegree k d) : monomial d c ∈ veroneseIdeal R ι r ^ k := by
  obtain ⟨a, ha, has⟩ := (bounded_sum_exists_iff (fun i => min (d i) k) (k * r)).mp hd
  have hmem := bounded_vector_mem_pow (R := R) k r a
    (fun i => (ha i).trans (min_le_right _ _)) has
  have hfactor : monomial d c = C c *
      (vectorMonomial (R := R) a * vectorMonomial (fun i => d i - a i)) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    congr 1
    rw [vectorMonomial, vectorMonomial, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [← pow_add]
    congr 1
    have := (ha i).trans (min_le_left (d i) k)
    omega
  rw [hfactor]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hmem)

/-- Exact membership in every power of the existing squarefree Veronese ideal. -/
theorem mem_veroneseIdeal_pow_iff (k r : ℕ) (P : MvPolynomial ι R) :
    P ∈ veroneseIdeal R ι r ^ k ↔ CappedWide k r P := by
  constructor
  · intro hP
    exact veroneseIdeal_pow_le_cappedWidthIdeal (R := R) (ι := ι) k r hP
  · intro hP
    rw [P.as_sum]
    apply Ideal.sum_mem
    intro d hd
    exact monomial_mem_pow_of_capped k r d _ (hP d (mem_support_iff.mp hd))

/-- A monomial belongs to the power exactly when its capped exponent sum reaches the degree. -/
theorem monomial_one_mem_veroneseIdeal_pow_iff [Nontrivial R]
    (k r : ℕ) (d : ι →₀ ℕ) :
    (monomial d (1 : R)) ∈ veroneseIdeal R ι r ^ k ↔ k * r ≤ cappedDegree k d := by
  constructor
  · intro h
    exact (mem_veroneseIdeal_pow_iff k r _).mp h d (by simp)
  · exact monomial_mem_pow_of_capped k r d 1

omit [DecidableEq ι] in
/-- Scaling both the exponent vector and the cap scales the capacity by the same factor. -/
theorem cappedDegree_scale (n k : ℕ) (d : ι →₀ ℕ) :
    cappedDegree (n * k) (n • d) = n * cappedDegree k d := by
  simp only [cappedDegree, Finsupp.smul_apply, smul_eq_mul, Nat.mul_min_mul_left,
    mul_sum]

/-- Taking a positive monomial power cannot create membership after rescaling the ideal power. -/
theorem veronese_monomial_power_root_closed [Nontrivial R]
    (n k r : ℕ) (d : ι →₀ ℕ) :
    (monomial d (1 : R)) ^ (n + 1) ∈ veroneseIdeal R ι r ^ ((n + 1) * k) ↔
      monomial d (1 : R) ∈ veroneseIdeal R ι r ^ k := by
  rw [monomial_pow, one_pow, monomial_one_mem_veroneseIdeal_pow_iff,
    monomial_one_mem_veroneseIdeal_pow_iff, cappedDegree_scale, mul_assoc]
  exact ⟨fun h => Nat.le_of_mul_le_mul_left h (by omega), Nat.mul_le_mul_left _⟩

end

/-- The full power filtration of the normal-crossing Jacobian ideal has the same capacity test. -/
theorem mem_normalCrossingJacobianIdeal_pow_iff {F : Type*} [Field F]
    (k r : ℕ) (P : MvPolynomial (Fin (r + 1)) F) :
    P ∈ normalCrossingJacobianIdeal (F := F) r ^ k ↔ CappedWide k r P := by
  rw [normalCrossingJacobianIdeal_eq_veroneseIdeal, mem_veroneseIdeal_pow_iff]

/-- The criterion is intrinsic: it also describes every power of the derivational critical ideal. -/
theorem mem_normalCrossingCriticalIdeal_pow_iff {F : Type*} [Field F]
    (k r : ℕ) (P : MvPolynomial (Fin (r + 1)) F) :
    P ∈ derivationalCriticalIdeal (R := F) (normalCrossingPolynomial (F := F) r) ^ k ↔
      CappedWide k r P := by
  rw [normalCrossingDerivationalCriticalIdeal_eq_veroneseIdeal, mem_veroneseIdeal_pow_iff]

end GaloisForLFunctions.VeroneseIdeal

#print axioms GaloisForLFunctions.VeroneseIdeal.mem_veroneseIdeal_pow_iff
#print axioms GaloisForLFunctions.VeroneseIdeal.veronese_monomial_power_root_closed
