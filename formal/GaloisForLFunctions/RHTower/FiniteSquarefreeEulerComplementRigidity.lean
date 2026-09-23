import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# Finite squarefree Euler complement coefficients

This is the exact finite Boolean-complement coefficient algebra behind the
finite Euler functional-equation card.  It deliberately contains no analytic
continuation claim: a separate wrapper must derive these coefficient identities
from an equality of finite Dirichlet polynomials.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- The complement coefficient at a squarefree subset. -/
def finiteEulerComplementCoefficient (P S : Finset ℕ) (a : ℕ → ℂ) (C : ℂ) : ℂ :=
  C * (∏ p ∈ P \ S, a p) / (∏ p ∈ P \ S, (p : ℂ))

/-- The top Boolean coefficient is the complement constant. -/
theorem finiteEulerComplement_topCoefficient
    (P : Finset ℕ) (a : ℕ → ℂ) (C : ℂ)
    (hcoeff : ∀ S, S ⊆ P → (∏ p ∈ S, a p) =
      finiteEulerComplementCoefficient P S a C) :
    (∏ p ∈ P, a p) = C := by
  have h := hcoeff P (by simp)
  simpa [finiteEulerComplementCoefficient, Finset.sdiff_self] using h

/-- The complement of the one-prime-deleted Boolean coefficient is that prime. -/
theorem finiteEulerComplement_eraseCoefficient
    (P : Finset ℕ) (a : ℕ → ℂ) (C : ℂ) {p : ℕ} (hp : p ∈ P)
    (hcoeff : ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a C) :
    (∏ q ∈ P.erase p, a q) = C * a p / (p : ℂ) := by
  have h := hcoeff (P.erase p) (Finset.erase_subset p P)
  unfold finiteEulerComplementCoefficient at h
  rw [show P \ P.erase p = {p} by
    rw [Finset.sdiff_erase hp, Finset.sdiff_self, Finset.insert_empty]] at h
  simpa using h

/-- Exact finite rigidity: nonzero Boolean-complement coefficients force every
local Euler parameter to square to its prime. -/
theorem finiteEulerComplement_coefficients_force_localSquares
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (C : ℂ)
    (hC : C ≠ 0)
    (hcoeff : ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a C) :
    ∀ p ∈ P, a p ^ (2 : ℕ) = (p : ℂ) := by
  intro p hp
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (hP p hp))
  have htop := finiteEulerComplement_topCoefficient P a C hcoeff
  have herase := finiteEulerComplement_eraseCoefficient P a C hp hcoeff
  have hprod : (∏ q ∈ P.erase p, a q) * a p = C := by
    rw [Finset.prod_erase_mul P a hp, htop]
  rw [herase] at hprod
  field_simp [hpC, hC] at hprod
  exact hprod

/-- Conversely, the local square relations imply every Boolean-complement
coefficient identity with the top coefficient as complement constant. -/
theorem finiteEulerComplement_coefficients_of_localSquares
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (hlocal : ∀ p ∈ P, a p ^ (2 : ℕ) = (p : ℂ)) :
    ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a (∏ q ∈ P, a q) := by
  intro S hS
  let T : Finset ℕ := P \ S
  have hdisj : Disjoint S T := by
    exact Finset.disjoint_sdiff
  have hunion : S ∪ T = P := by
    exact Finset.union_sdiff_of_subset hS
  have hTsq : (∏ q ∈ T, a q) ^ (2 : ℕ) = (∏ q ∈ T, (q : ℂ)) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    exact hlocal q (Finset.sdiff_subset hq)
  have hTne : (∏ q ∈ T, a q) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    have hqP : q ∈ P := Finset.sdiff_subset hq
    have hqC : (q : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.Prime.ne_zero (hP q hqP))
    intro hzero
    have hsq := hlocal q hqP
    simp [hzero] at hsq
    exact hqC hsq.symm
  rw [finiteEulerComplementCoefficient]
  change (∏ q ∈ S, a q) = (∏ q ∈ P, a q) * (∏ q ∈ T, a q) /
    (∏ q ∈ T, (q : ℂ))
  rw [← hTsq, ← hunion, Finset.prod_union hdisj]
  field_simp [hTne]

/-- The finite prime mass in the centered functional equation. -/
def finiteEulerPrimeMass (P : Finset ℕ) : ℝ := ∏ p ∈ P, (p : ℝ)

/-- The Boolean-complement parity sign. -/
def finiteEulerComplementSign (P : Finset ℕ) : ℂ := (-1 : ℂ) ^ P.card

/-- The positive square root of the finite prime mass, embedded in `ℂ`. -/
def finiteEulerComplementRoot (P : Finset ℕ) : ℂ :=
  (Real.sqrt (finiteEulerPrimeMass P) : ℂ)

/-- The centered complement constant `ε (-1)^|P| √Q`. -/
def finiteEulerFunctionalConstant (P : Finset ℕ) (ε : ℂ) : ℂ :=
  ε * finiteEulerComplementSign P * finiteEulerComplementRoot P

theorem finiteEulerPrimeMass_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    0 < finiteEulerPrimeMass P := by
  unfold finiteEulerPrimeMass
  apply Finset.prod_pos
  intro p hp
  exact_mod_cast (Nat.Prime.pos (hP p hp))

theorem finiteEulerComplementRoot_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    finiteEulerComplementRoot P ≠ 0 := by
  unfold finiteEulerComplementRoot
  rw [Complex.ofReal_ne_zero]
  exact (Real.sqrt_pos.2 (finiteEulerPrimeMass_pos hP)).ne'

theorem finiteEulerComplementSign_sq (P : Finset ℕ) :
    finiteEulerComplementSign P * finiteEulerComplementSign P = 1 := by
  unfold finiteEulerComplementSign
  rw [← pow_add]
  have h : P.card + P.card = 2 * P.card := by omega
  rw [h]
  exact (even_two.mul_right P.card).neg_one_pow

/-- The top Boolean coefficient identifies the centered epsilon exactly. -/
theorem finiteEulerComplement_epsilon_formula
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hcoeff : ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε)) :
    ε = finiteEulerComplementSign P * (∏ q ∈ P, a q) /
      finiteEulerComplementRoot P := by
  have htop := finiteEulerComplement_topCoefficient P a (finiteEulerFunctionalConstant P ε) hcoeff
  rw [finiteEulerFunctionalConstant] at htop
  have hroot := finiteEulerComplementRoot_ne_zero hP
  have hsign := finiteEulerComplementSign_sq P
  apply (eq_div_iff hroot).2
  rw [htop]
  calc
    ε * finiteEulerComplementRoot P =
        (finiteEulerComplementSign P * finiteEulerComplementSign P) *
          (ε * finiteEulerComplementRoot P) := by
            rw [hsign]
            ring
    _ = finiteEulerComplementSign P *
        (ε * finiteEulerComplementSign P * finiteEulerComplementRoot P) := by
          ring

theorem finiteEulerPrimeMass_cast (P : Finset ℕ) :
    (finiteEulerPrimeMass P : ℂ) = ∏ p ∈ P, (p : ℂ) := by
  unfold finiteEulerPrimeMass
  simp

theorem finiteEulerComplementRoot_sq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    finiteEulerComplementRoot P ^ (2 : ℕ) = (finiteEulerPrimeMass P : ℂ) := by
  unfold finiteEulerComplementRoot
  rw [← Complex.ofReal_pow, Real.sq_sqrt (finiteEulerPrimeMass_pos hP).le]

theorem finiteEulerProduct_sq_eq_primeMass
    {P : Finset ℕ} (a : ℕ → ℂ)
    (hlocal : ∀ p ∈ P, a p ^ (2 : ℕ) = (p : ℂ)) :
    (∏ p ∈ P, a p) ^ (2 : ℕ) = (finiteEulerPrimeMass P : ℂ) := by
  rw [← Finset.prod_pow]
  calc
    (∏ p ∈ P, a p ^ (2 : ℕ)) = ∏ p ∈ P, (p : ℂ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hlocal p hp
    _ = (finiteEulerPrimeMass P : ℂ) := (finiteEulerPrimeMass_cast P).symm

/-- The exact Boolean coefficient system with nonzero epsilon forces `ε² = 1`. -/
theorem finiteEulerComplement_epsilon_sq
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ) (ε : ℂ)
    (hε : ε ≠ 0)
    (hcoeff : ∀ S, S ⊆ P → (∏ q ∈ S, a q) =
      finiteEulerComplementCoefficient P S a (finiteEulerFunctionalConstant P ε)) :
    ε ^ (2 : ℕ) = 1 := by
  have hC : finiteEulerFunctionalConstant P ε ≠ 0 := by
    unfold finiteEulerFunctionalConstant
    exact mul_ne_zero (mul_ne_zero hε (by simp [finiteEulerComplementSign]))
      (finiteEulerComplementRoot_ne_zero hP)
  have hlocal := finiteEulerComplement_coefficients_force_localSquares hP a
    (finiteEulerFunctionalConstant P ε) hC hcoeff
  have hprod := finiteEulerProduct_sq_eq_primeMass a hlocal
  have hroot := finiteEulerComplementRoot_sq hP
  have htop := finiteEulerComplement_topCoefficient P a (finiteEulerFunctionalConstant P ε) hcoeff
  rw [finiteEulerFunctionalConstant] at htop
  have hsign := finiteEulerComplementSign_sq P
  have hsignpow : finiteEulerComplementSign P ^ (2 : ℕ) = 1 := by
    simpa [pow_two] using hsign
  have hEq : ε ^ (2 : ℕ) * finiteEulerComplementRoot P ^ (2 : ℕ) =
      finiteEulerComplementRoot P ^ (2 : ℕ) := by
    calc
      ε ^ (2 : ℕ) * finiteEulerComplementRoot P ^ (2 : ℕ) =
          (ε * finiteEulerComplementSign P * finiteEulerComplementRoot P) ^ (2 : ℕ) := by
            rw [mul_pow, mul_pow, hsignpow]
            ring
      _ = (∏ q ∈ P, a q) ^ (2 : ℕ) := by rw [← htop]
      _ = finiteEulerPrimeMass P := hprod
      _ = finiteEulerComplementRoot P ^ (2 : ℕ) := hroot.symm
  apply (mul_right_cancel₀ (pow_ne_zero 2 (finiteEulerComplementRoot_ne_zero hP)))
  simpa using hEq

end

end RHTower
