import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs

/-!
# Route E hard-core pair-field finite identities

The prime-by-prime coprime pair field has local probabilities
`(p-1)/(p+1), 1/(p+1), 1/(p+1)` for neither, left, and right occupation.
Its two marginals are the critical Euler Bernoulli source. Conditioning on odd
union parity gives the density below. These theorems certify its exact finite
chi-square cost, the signed local cross-factor, and an unconditional finite
conjugate-character covariance sign. They do not give the missing physical
two-shell or RH-scale covariance estimate.
-/

open scoped BigOperators

namespace RHTower

open HTGeometry.ConstraintFrameRelativity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One-leg density after odd-union conditioning when union parity is fair. -/
def routeEHardCoreParityDensity (a : ι → ℝ) (S : Finset ι) : ℝ :=
  1 - (-1 : ℝ) ^ S.card * ∏ p ∈ Sᶜ, a p

/-- Exact Bernoulli chi-square cost of the parity-density correction. -/
theorem routeEHardCoreParityDensity_chiSquare (q a : ι → ℝ) :
    bernoulliExp q (fun S => (routeEHardCoreParityDensity a S - 1) ^ 2) =
      ∏ p, (q p + (1 - q p) * a p ^ 2) := by
  have h := bernoulliExp_prod q (fun _ => (1 : ℝ)) (fun p => a p ^ 2)
  calc
    _ = bernoulliExp q
      (fun S => (∏ p ∈ S, (1 : ℝ)) * ∏ p ∈ Sᶜ, a p ^ 2) := by
        congr 1
        funext S
        have hsign : ((-1 : ℝ) ^ S.card) ^ 2 = 1 := by
          rw [← pow_mul]
          simp
        simp only [routeEHardCoreParityDensity, sub_sub_cancel_left]
        rw [neg_sq, mul_pow, hsign, one_mul, Finset.prod_pow]
        simp
    _ = ∏ p, (q p + (1 - q p) * a p ^ 2) := by simpa using h

/-- Exact parity bias of the original product Bernoulli source. -/
theorem routeEHardCoreSourceParityBias (q : ι → ℝ) :
    bernoulliExp q (fun S => (-1 : ℝ) ^ S.card) =
      ∏ p, (1 - 2 * q p) := by
  have h := bernoulliExp_prod q (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
  calc
    _ = bernoulliExp q
      (fun S => (∏ p ∈ S, (-1 : ℝ)) * ∏ p ∈ Sᶜ, (1 : ℝ)) := by
        congr 1
        funext S
        simp
    _ = ∏ p, (q p * (-1) + (1 - q p) * 1) := h
    _ = ∏ p, (1 - 2 * q p) := by
      apply Finset.prod_congr rfl
      intro p hp
      ring

/-- Exact negative local interaction of the trinary field, over complex phases. -/
theorem routeEHardCoreLocalCrossFactor
    (p z w : ℂ) (hp : p + 1 ≠ 0) :
    (p - 1 + z + w) / (p + 1) -
      ((p + z) / (p + 1)) * ((p + w) / (p + 1)) =
        -((1 - z) * (1 - w)) / (p + 1) ^ 2 := by
  field_simp [hp]
  ring

/-- The critical local chi-square factor differs from squared parity bias by a cubic tail. -/
theorem routeEHardCoreLocalChiSquareFactor
    (p : ℝ) (hp : p ≠ 0) (hp1 : p + 1 ≠ 0) :
    1 - 4 * (p - 1) / (p * (p + 1)) =
      ((p - 1) / (p + 1)) ^ 2 + 4 / (p * (p + 1) ^ 2) := by
  field_simp [hp, hp1]
  ring

private theorem routeEHardCoreLocalSecondMoment
    (p : ℝ) (hp : p ≠ 0) (hp1 : p + 1 ≠ 0) :
    1 / (p + 1) + (1 - 1 / (p + 1)) * (1 - 2 / p) ^ 2 =
      1 - 4 * (p - 1) / (p * (p + 1)) := by
  field_simp [hp, hp1]
  ring

/-- Exact finite critical-source defect for arbitrary nonzero prime labels. -/
theorem routeEHardCoreCriticalChiSquareProduct
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0) :
    bernoulliExp (fun i => 1 / (p i + 1))
      (fun S => (routeEHardCoreParityDensity (fun i => 1 - 2 / p i) S - 1) ^ 2) =
      ∏ i, (1 - 4 * (p i - 1) / (p i * (p i + 1))) := by
  rw [routeEHardCoreParityDensity_chiSquare]
  apply Finset.prod_congr rfl
  intro i hi
  exact routeEHardCoreLocalSecondMoment (p i) (hp i) (hp1 i)

private theorem prod_le_prod_one_exception
    {α : Type*} [DecidableEq α] (P : Finset α) (e : α) (j m : α → ℝ)
    (hjrest : ∀ i ∈ P, i ≠ e → 0 ≤ j i)
    (hjm : ∀ i ∈ P, j i ≤ m i)
    (hm : ∀ i ∈ P, 0 ≤ m i) :
    (∏ i ∈ P, j i) ≤ ∏ i ∈ P, m i := by
  by_cases he : e ∈ P
  · by_cases hje : 0 ≤ j e
    · exact Finset.prod_le_prod
        (fun i hi => if hie : i = e then hie ▸ hje else hjrest i hi hie) hjm
    · have hrest : 0 ≤ ∏ i ∈ P.erase e, j i :=
        Finset.prod_nonneg fun i hi =>
          hjrest i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1
      have hleft : (∏ i ∈ P, j i) ≤ 0 := by
        rw [← Finset.mul_prod_erase P j he]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hje) hrest
      exact hleft.trans (Finset.prod_nonneg fun i hi => hm i hi)
  · exact Finset.prod_le_prod (fun i hi => hjrest i hi (by
      intro hie
      apply he
      simpa [hie] using hi)) hjm

/-- Real joint factor for conjugate unit phases with real part `r`. -/
def hardCoreJ (p r : ℝ) : ℝ := (p - 1 + 2 * r) / (p + 1)

/-- Squared marginal factor for conjugate unit phases with real part `r`. -/
def hardCoreM (p r : ℝ) : ℝ := (p ^ 2 + 2 * p * r + 1) / (p + 1) ^ 2

private theorem hardCoreJ_le_M (p r : ℝ) (hp : 0 ≤ p) (hr : r ≤ 1) :
    hardCoreJ p r ≤ hardCoreM p r := by
  have hp1 : 0 < p + 1 := by linarith
  have hd : hardCoreM p r - hardCoreJ p r = 2 * (1 - r) / (p + 1) ^ 2 := by
    unfold hardCoreM hardCoreJ
    field_simp [ne_of_gt hp1]
    ring
  have hnonneg : 0 ≤ 2 * (1 - r) / (p + 1) ^ 2 := by positivity
  linarith

private theorem hardCoreM_nonneg (p r : ℝ) (hp : 0 ≤ p) (hr : -1 ≤ r) :
    0 ≤ hardCoreM p r := by
  have hp1 : 0 < p + 1 := by linarith
  have hprod : 0 ≤ p * (r + 1) := mul_nonneg hp (by linarith)
  have hn : 0 ≤ p ^ 2 + 2 * p * r + 1 := by nlinarith [sq_nonneg (p - 1)]
  exact div_nonneg hn (sq_nonneg _)

private theorem hardCoreJ_nonneg (p r : ℝ) (hp : 3 ≤ p) (hr : -1 ≤ r) :
    0 ≤ hardCoreJ p r := by
  unfold hardCoreJ
  apply div_nonneg
  · linarith
  · linarith

/-- Every finite prime family has nonpositive conjugate-character cross-covariance
under the unconditioned trinary coprime field. Only prime `2` can contribute a
negative joint factor, so local comparison still multiplies globally. -/
theorem routeEHardCoreConjugateCovariance_nonpos
    (P : Finset Nat.Primes) (r : Nat.Primes → ℝ)
    (hr : ∀ p ∈ P, -1 ≤ r p ∧ r p ≤ 1) :
    (∏ p ∈ P, hardCoreJ (p : ℕ) (r p)) -
      (∏ p ∈ P, hardCoreM (p : ℕ) (r p)) ≤ 0 := by
  have hcmp : (∏ p ∈ P, hardCoreJ (p : ℕ) (r p)) ≤
      (∏ p ∈ P, hardCoreM (p : ℕ) (r p)) := by
    apply prod_le_prod_one_exception P (⟨2, Nat.prime_two⟩ : Nat.Primes)
    · intro p hpP hpne
      have hne : (p : ℕ) ≠ 2 := by
        intro h
        apply hpne
        exact Subtype.ext h
      have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
      have hp3 : 3 ≤ (p : ℕ) := by omega
      exact hardCoreJ_nonneg _ _ (by exact_mod_cast hp3) (hr p hpP).1
    · intro p hpP
      exact hardCoreJ_le_M _ _ (by exact_mod_cast Nat.zero_le (p : ℕ)) (hr p hpP).2
    · intro p hpP
      exact hardCoreM_nonneg _ _ (by exact_mod_cast Nat.zero_le (p : ℕ)) (hr p hpP).1
  linarith

/-- Unconditional prime-log-frequency version of the conjugate covariance sign. -/
theorem routeEHardCoreConjugateClockCovariance_nonpos
    (P : Finset Nat.Primes) (t : ℝ) :
    (∏ p ∈ P, hardCoreJ (p : ℕ) (Real.cos (t * Real.log (p : ℕ)))) -
      (∏ p ∈ P, hardCoreM (p : ℕ) (Real.cos (t * Real.log (p : ℕ)))) ≤ 0 := by
  exact routeEHardCoreConjugateCovariance_nonpos P
    (fun p => Real.cos (t * Real.log (p : ℕ)))
    (fun p hp => ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

end

end RHTower
