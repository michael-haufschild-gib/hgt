import GaloisForLFunctions.RHTower.Sieve.MaynardProductDefect
import GaloisForLFunctions.RHTower.Sieve.MaynardFactorTrivial
import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalDefectExcision
import GaloisForLFunctions.RHTower.Sieve.MaynardPointwiseExclusion

/-!
# Literal long-factor exclusion for Heath--Brown boxes

Sharp trivial bounds propagate the derivative-test saving on one zeta/logarithm atom through an
entire literal box.  After one explicit constant-absorption inequality, that box cannot attain its
full multiplicative threshold.  No independent local large-value label is required.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def heathBrownFactorTrivialConstant
    (kind : HeathBrownFactorKind) (q : ℕ) : ℝ :=
  match kind with
  | .moebius => 1
  | .zeta => 1
  | .log => Real.log (((2 ^ (q + 1) : ℕ) : ℝ))

theorem heathBrownFactorTrivialConstant_nonneg
    (kind : HeathBrownFactorKind) (q : ℕ) :
    0 ≤ heathBrownFactorTrivialConstant kind q := by
  cases kind <;> simp [heathBrownFactorTrivialConstant]
  positivity

theorem norm_heathBrownBoxFactorValue_le_trivial
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (y : ℝ)
    (i : HeathBrownBoxFactorIndex k c.m) :
    ‖heathBrownBoxFactorValue L X k c
        ((sigma : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
      heathBrownFactorTrivialConstant
          (heathBrownBoxFactorKind k c.m i)
          (heathBrownBoxFactorExponent c.a c.b c.q i) *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^
          (1 - sigma) := by
  rcases i with i | i
  · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
      heathBrownBoxFactorExponent, heathBrownFactorBase,
      heathBrownFactorTrivialConstant] using
      norm_LSeries_moebiusDyadicBlock_le_rpow L (c.a i) hsigma y
  · rcases i with i | i
    · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
        heathBrownBoxFactorExponent, heathBrownFactorBase,
        heathBrownFactorTrivialConstant] using
        norm_LSeries_zetaDyadicBlock_le_rpow X (c.b i) hsigma y
    · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
        heathBrownBoxFactorExponent, heathBrownFactorBase,
        heathBrownFactorTrivialConstant, mul_comm] using
        norm_LSeries_logDyadicBlock_le_rpow_mul_log X c.q hsigma y

theorem norm_heathBrownBoxFactorValue_prod_erase_le_trivial
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (y : ℝ)
    (j : HeathBrownBoxFactorIndex k c.m) :
    ‖∏ i ∈ (Finset.univ.erase j),
        heathBrownBoxFactorValue L X k c
          ((sigma : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
      (∏ i ∈ (Finset.univ.erase j),
        heathBrownFactorTrivialConstant
          (heathBrownBoxFactorKind k c.m i)
          (heathBrownBoxFactorExponent c.a c.b c.q i)) *
      (∏ i ∈ (Finset.univ.erase j),
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ))) ^
          (1 - sigma) := by
  let u : Finset (HeathBrownBoxFactorIndex k c.m) := Finset.univ.erase j
  let A : HeathBrownBoxFactorIndex k c.m → ℝ := fun i =>
    (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ))
  let C : HeathBrownBoxFactorIndex k c.m → ℝ := fun i =>
    heathBrownFactorTrivialConstant
      (heathBrownBoxFactorKind k c.m i)
      (heathBrownBoxFactorExponent c.a c.b c.q i)
  have hprod : ∏ i ∈ u,
      ‖heathBrownBoxFactorValue L X k c
        ((sigma : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
      ∏ i ∈ u, C i * A i ^ (1 - sigma) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      exact norm_heathBrownBoxFactorValue_le_trivial L X k c hsigma y i
  rw [Complex.norm_prod]
  calc
    ∏ i ∈ u,
        ‖heathBrownBoxFactorValue L X k c
          ((sigma : ℂ) + (y : ℝ) * Complex.I) i‖
        ≤ ∏ i ∈ u, C i * A i ^ (1 - sigma) := hprod
    _ = (∏ i ∈ u, C i) * (∏ i ∈ u, A i ^ (1 - sigma)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ i ∈ u, C i) * (∏ i ∈ u, A i) ^ (1 - sigma) := by
      rw [Real.finsetProd_rpow u A (fun i _ => by dsimp [A]; positivity)]
    _ = _ := by rfl

def heathBrownDerivativeConstant
    (X : ℕ) (kind : HeathBrownFactorKind) (q : ℕ) : ℝ :=
  match kind with
  | .moebius => 0
  | .zeta => 2560
  | .log => 5120 * Real.log (heathBrownDyadicFactorTop X q : ℝ)

def maynardDerivativeDeficit (k₀ : ℕ) : ℝ :=
  1 / (3 * (2 : ℝ) ^ k₀)

theorem HeathBrownBoxChoice.factorExponent_le_log_X_of_zeta_or_log
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (i : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m i = .zeta ∨
      heathBrownBoxFactorKind k c.m i = .log) :
    heathBrownBoxFactorExponent c.a c.b c.q i ≤ Nat.log 2 X := by
  rcases i with i | i
  · simp [heathBrownBoxFactorKind] at hkind
  · rcases i with i | i
    · exact dyadicChoice_le_log c.2.2.1.2 i
    · dsimp [heathBrownBoxFactorExponent, HeathBrownBoxChoice.q]
      omega

theorem norm_heathBrownBoxFactorValue_le_derivative_defect
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    (i : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m i = .zeta ∨
      heathBrownBoxFactorKind k c.m i = .log)
    (hX : 1 ≤ X)
    {sigma y : ℝ} (hsigma : 0 ≤ sigma) (hy : 0 < y)
    {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    (hq : heathBrownBoxFactorExponent c.a c.b c.q i ≤ Nat.log 2 X)
    (hfac : Nat.factorial (k₀ - 1) ≤
      2 ^ heathBrownBoxFactorExponent c.a c.b c.q i)
    (hlow : 8 * Real.pi *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^
          ((1 : ℝ) / 3) ≤ y)
    (hhigh : y ≤ 2 * Real.pi * 2 ^ k₀ *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^
          (k₀ - 1) *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^
          (-(1 / 3) : ℝ)) :
    ‖heathBrownBoxFactorValue L X k c
        ((sigma : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
      heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k c.m i)
          (heathBrownBoxFactorExponent c.a c.b c.q i) *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^
          (1 - sigma) *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ)) ^
          (-maynardDerivativeDeficit k₀) := by
  rcases i with i | i
  · simp [heathBrownBoxFactorKind] at hkind
  · rcases i with i | i
    · simpa [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
        heathBrownBoxFactorExponent, heathBrownFactorBase,
        heathBrownDerivativeConstant, maynardDerivativeDeficit] using
        norm_LSeries_zetaDyadicBlock_le (X := X) hX hq hsigma hy hk₀ hfac hlow hhigh
    · have h := norm_LSeries_logDyadicBlock_le (X := X) (q := c.q)
        hX hq hsigma hy hk₀ hfac hlow hhigh
      simp only [heathBrownBoxFactorValue, heathBrownBoxFactorKind,
        heathBrownBoxFactorExponent, heathBrownFactorBase,
        heathBrownDerivativeConstant, maynardDerivativeDeficit]
      calc
        _ ≤ 5120 * (((2 ^ c.q : ℕ) : ℝ)) ^ (1 - sigma) *
              (((2 ^ c.q : ℕ) : ℝ)) ^
                (-(1 / (3 * (2 : ℝ) ^ k₀))) *
              Real.log (heathBrownDyadicFactorTop X c.q : ℝ) := h
        _ = _ := by ring

def heathBrownComplementTrivialConstant
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m) : ℝ :=
  ∏ i ∈ (Finset.univ.erase j),
    heathBrownFactorTrivialConstant
      (heathBrownBoxFactorKind k c.m i)
      (heathBrownBoxFactorExponent c.a c.b c.q i)

theorem prod_univ_erase_eq_if_single_nontrivial
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (f : ι → M) (l j : ι) (hoff : ∀ i, i ≠ l → f i = 1) :
    (∏ i ∈ (Finset.univ.erase j), f i) = if j = l then 1 else f l := by
  by_cases hj : j = l
  · subst j
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i hi
    exact hoff i (Finset.ne_of_mem_erase hi)
  · rw [if_neg hj]
    apply Finset.prod_eq_single l
    · intro i hi hil
      exact hoff i hil
    · intro hlnot
      have hlj : l ≠ j := fun h => hj h.symm
      exact (hlnot (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩)).elim

/-- A literal box has only one logarithmic atom.  Thus the entire complementary trivial constant
is either one (when that atom is distinguished) or exactly its one logarithmic loss. -/
theorem heathBrownComplementTrivialConstant_eq
    {L X k : ℕ} (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m) :
    heathBrownComplementTrivialConstant c j =
      if heathBrownBoxFactorKind k c.m j = .log then 1
      else Real.log (((2 ^ (c.q + 1) : ℕ) : ℝ)) := by
  let logIndex : HeathBrownBoxFactorIndex k c.m := Sum.inr (Sum.inr ())
  let f : HeathBrownBoxFactorIndex k c.m → ℝ := fun i =>
    heathBrownFactorTrivialConstant
      (heathBrownBoxFactorKind k c.m i)
      (heathBrownBoxFactorExponent c.a c.b c.q i)
  have hoff : ∀ i, i ≠ logIndex → f i = 1 := by
    intro i hi
    rcases i with i | i
    · simp [f, heathBrownBoxFactorKind, heathBrownFactorTrivialConstant]
    · rcases i with i | i
      · simp [f, heathBrownBoxFactorKind, heathBrownFactorTrivialConstant]
      · simp [logIndex] at hi
  have h := prod_univ_erase_eq_if_single_nontrivial f logIndex j hoff
  rcases j with j | j
  · simpa [heathBrownComplementTrivialConstant, f, logIndex,
      heathBrownBoxFactorKind, heathBrownBoxFactorExponent,
      heathBrownFactorTrivialConstant] using h
  · rcases j with j | j
    · simpa [heathBrownComplementTrivialConstant, f, logIndex,
        heathBrownBoxFactorKind, heathBrownBoxFactorExponent,
        heathBrownFactorTrivialConstant] using h
    · rcases j with ⟨⟩
      simpa [heathBrownComplementTrivialConstant, f, logIndex,
        heathBrownBoxFactorKind, heathBrownBoxFactorExponent,
        heathBrownFactorTrivialConstant] using h

/-- One derivative-test factor rules out full threshold size of the literal box once its saving
absorbs its own constant and the sole complementary logarithmic loss. -/
theorem not_heathBrown_box_core_large_of_derivative_factor
    (L X k : ℕ) (c : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k c.m)
    (hkind : heathBrownBoxFactorKind k c.m j = .zeta ∨
      heathBrownBoxFactorKind k c.m j = .log)
    (hX : 1 ≤ X) {sigma y : ℝ} (hsigma : 0 ≤ sigma) (hy : 0 < y)
    {k₀ : ℕ} (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤
      2 ^ heathBrownBoxFactorExponent c.a c.b c.q j)
    (hlow : 8 * Real.pi *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
          ((1 : ℝ) / 3) ≤ y)
    (hhigh : y ≤ 2 * Real.pi * 2 ^ k₀ *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
          (k₀ - 1) *
        (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
          (-(1 / 3) : ℝ))
    (habsorb :
      (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k c.m j)
          (heathBrownBoxFactorExponent c.a c.b c.q j) *
        heathBrownComplementTrivialConstant c j) *
          (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q j : ℕ) : ℝ)) ^
            (-maynardDerivativeDeficit k₀) < 1) :
    ¬ (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤
      ‖heathBrownDyadicCoreProduct L X k c.m c.a c.b c.q
        ((sigma : ℂ) + (y : ℝ) * Complex.I)‖ := by
  let A : HeathBrownBoxFactorIndex k c.m → ℝ := fun i =>
    (((2 ^ heathBrownBoxFactorExponent c.a c.b c.q i : ℕ) : ℝ))
  let z : HeathBrownBoxFactorIndex k c.m → ℂ :=
    heathBrownBoxFactorValue L X k c
      ((sigma : ℂ) + (y : ℝ) * Complex.I)
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k c.m j)
    (heathBrownBoxFactorExponent c.a c.b c.q j)
  let D : ℝ := heathBrownComplementTrivialConstant c j
  let delta : ℝ := maynardDerivativeDeficit k₀
  have hnot := not_large_product_of_distinguished_defect_of_complement
    A z (1 - sigma) delta C D j (fun i => by dsimp [A]; positivity)
    (norm_heathBrownBoxFactorValue_le_derivative_defect
      L X k c j hkind hX hsigma hy hk₀
        (c.factorExponent_le_log_X_of_zeta_or_log j hkind)
        hfac hlow hhigh)
    (norm_heathBrownBoxFactorValue_prod_erase_le_trivial
      L X k c hsigma y j)
    (by simpa [A, C, D, delta] using habsorb)
  intro hcore
  apply hnot
  have hcast : (∏ i, A i) =
      (groupedDyadicLower
        (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) := by
    simp [A, groupedDyadicLower]
  rw [hcast]
  change (groupedDyadicLower
      (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤
    ‖∏ i : HeathBrownBoxFactorIndex k c.m,
      LSeries (complexCoeff (arithmeticDyadicBlock
        (heathBrownFactorBase L X (heathBrownBoxFactorKind k c.m i))
        (heathBrownBoxFactorExponent c.a c.b c.q i)))
          ((sigma : ℂ) + (y : ℝ) * Complex.I)‖
  rw [heathBrownBoxFactorProduct_eq_core]
  exact hcore

end RHTower.Sieve
