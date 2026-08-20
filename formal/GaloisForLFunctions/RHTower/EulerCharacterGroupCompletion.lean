import GaloisForLFunctions.RHTower.EulerLaurentResidueDouble
import Mathlib.Algebra.Order.Positive.Field
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The Euler character monoid, its group completion, and the residue seam

Centering the Euler spectral parameter at `s = 1/2 + z` turns the positive Dirichlet characters
`n ↦ n^{-z}` into a multiplicative monoid indexed by the positive naturals.  That monoid is
cancellative and its group completion is canonically the multiplicative group of positive
rationals, so the *negative* Laurent half is not an added formal loop variable: it is the
functional-equation reflection of the actual Euler Dirichlet monoid.

This module formalizes that statement together with the constant-term residue seam:

* `EulerCharGroup` — positive rationals as a `CommGroup` (the group completion);
* `closure_natRange_eq_top`, `closure_primeRange_eq_top` — the positive naturals, and already the
  primes alone, generate it as a *group*: this is the minimality half of the group completion, and
  the "finite integer prime-exponent lattice" description;
* `eulerRatCharacter`, `eulerRatCharacter_mul`, `eulerRatCharacter_reflection`,
  `eulerRatCharacter_reflection_eq_inv`, `eulerRatCharacter_injective` — the character map is an
  injective monoid morphism and reflection inverts every character;
* `scaleDeriv`, `scaleDeriv_mul` (Leibniz), `constantTerm`, `constantTerm_scaleDeriv` — the scale
  derivation and the constant-term functional on `ℂ[ℚ_{>0}^×]`;
* `residuePairing`, `residuePairing_single`, `residuePairing_swap`,
  `residuePairing_natMode_eq_zero`, `residuePairing_opposite_ne_zero` — the residue seam: it is
  alternating, both Euler halves are isotropic, and every nontrivial mode pairs nondegenerately
  with its reflected mode;
* `cpow_neg_eq_eulerRatCharacter`, `eulerPrimeApartmentChart`,
  `eulerPrimeApartmentChart_reflected` — the squarefree prime-apartment charts.

The real-frequency residue weight and its `A₂` matrix lift are in
`GaloisForLFunctions.RHTower.EulerLaurentResidueDouble`.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The group completion of the multiplicative Euler Dirichlet monoid: the positive rationals. -/
abbrev EulerCharGroup := {q : ℚ // 0 < q}

namespace EulerCharGroup

/-- A positive natural as an element of the completed Euler character group. -/
def ofNat (n : ℕ) (hn : 0 < n) : EulerCharGroup := ⟨(n : ℚ), by exact_mod_cast hn⟩

@[simp]
theorem coe_ofNat (n : ℕ) (hn : 0 < n) : ((ofNat n hn : EulerCharGroup) : ℚ) = (n : ℚ) := rfl

/-- The real logarithm of a positive rational. -/
def logVal (q : EulerCharGroup) : ℝ := Real.log ((q : ℚ) : ℝ)

theorem coe_pos (q : EulerCharGroup) : (0 : ℝ) < ((q : ℚ) : ℝ) := by
  exact_mod_cast q.2

theorem coe_ne_zero (q : EulerCharGroup) : ((q : ℚ) : ℝ) ≠ 0 := (coe_pos q).ne'

@[simp]
theorem logVal_one : logVal (1 : EulerCharGroup) = 0 := by
  simp [logVal]

theorem logVal_mul (q r : EulerCharGroup) : logVal (q * r) = logVal q + logVal r := by
  simp only [logVal, Positive.val_mul, Rat.cast_mul]
  exact Real.log_mul (coe_ne_zero q) (coe_ne_zero r)

theorem logVal_inv (q : EulerCharGroup) : logVal q⁻¹ = -logVal q := by
  simp only [logVal, Positive.coe_inv, Rat.cast_inv]
  exact Real.log_inv _

theorem logVal_injective : Function.Injective logVal := by
  intro q r h
  apply Subtype.ext
  have hq : Real.exp (logVal q) = ((q : ℚ) : ℝ) := Real.exp_log (coe_pos q)
  have hr : Real.exp (logVal r) = ((r : ℚ) : ℝ) := Real.exp_log (coe_pos r)
  have hqr : ((q : ℚ) : ℝ) = ((r : ℚ) : ℝ) := by rw [← hq, ← hr, h]
  exact_mod_cast hqr

theorem logVal_eq_zero_iff (q : EulerCharGroup) : logVal q = 0 ↔ q = 1 := by
  constructor
  · intro h
    exact logVal_injective (by simpa using h)
  · rintro rfl
    simp

theorem logVal_eq_natLog {n : ℕ} (h : 0 < n) : logVal (ofNat n h) = Real.log (n : ℝ) := by
  simp [logVal, ofNat]

theorem logVal_pos_of_one_lt {n : ℕ} (hn : 1 < n) (h : 0 < n) :
    0 < logVal (ofNat n h) := by
  rw [logVal_eq_natLog h]
  refine Real.log_pos ?_
  exact_mod_cast hn

/-! ### Group completion: the positive naturals generate the group -/

/-- Every positive rational is a quotient of two positive naturals. -/
theorem exists_natCast_quotient (q : EulerCharGroup) :
    ∃ (m n : ℕ) (hm : 0 < m) (hn : 0 < n), q = ofNat m hm * (ofNat n hn)⁻¹ := by
  have hnum : 0 < (q : ℚ).num := Rat.num_pos.mpr q.2
  refine ⟨(q : ℚ).num.toNat, (q : ℚ).den, ?_, (q : ℚ).pos, ?_⟩
  · omega
  · apply Subtype.ext
    have hcast : (((q : ℚ).num.toNat : ℚ)) = ((q : ℚ).num : ℚ) := by
      have : ((q : ℚ).num.toNat : ℤ) = (q : ℚ).num := Int.toNat_of_nonneg hnum.le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
    simp only [Positive.val_mul, Positive.coe_inv, coe_ofNat, hcast]
    rw [← div_eq_mul_inv, Rat.num_div_den]

/-- **Group completion, minimality half.**  The positive Euler Dirichlet monoid generates the whole
positive-rational character group; no larger algebra is needed to be reflection-closed and no
smaller one suffices. -/
theorem closure_natRange_eq_top :
    Subgroup.closure {q : EulerCharGroup | ∃ n : ℕ, ∃ h : 0 < n, ofNat n h = q} = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro q
  obtain ⟨m, n, hm, hn, rfl⟩ := exists_natCast_quotient q
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨m, hm, rfl⟩)
    (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨n, hn, rfl⟩))

/-- Every positive natural mode is a finite product of prime modes. -/
theorem ofNat_mem_closure_primeRange {n : ℕ} (hn : 0 < n) :
    ofNat n hn ∈
      Subgroup.closure {q : EulerCharGroup | ∃ p : ℕ, ∃ h : p.Prime, ofNat p h.pos = q} := by
  induction n using Nat.recOnMul with
  | zero => exact absurd hn (lt_irrefl 0)
  | one =>
      have : ofNat 1 hn = 1 := by apply Subtype.ext; simp
      rw [this]
      exact Subgroup.one_mem _
  | prime p hp => exact Subgroup.subset_closure ⟨p, hp, by congr⟩
  | mul a b iha ihb =>
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp at hn
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp at hn
      have hprod : ofNat (a * b) hn = ofNat a ha * ofNat b hb := by
        apply Subtype.ext
        simp [ofNat]
      rw [hprod]
      exact Subgroup.mul_mem _ (iha ha) (ihb hb)

/-- **The prime-exponent lattice.**  The prime modes alone generate the completed character group:
by unique factorization every character is a finite integer combination of prime modes. -/
theorem closure_primeRange_eq_top :
    Subgroup.closure {q : EulerCharGroup | ∃ p : ℕ, ∃ h : p.Prime, ofNat p h.pos = q} = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro q
  obtain ⟨m, n, hm, hn, rfl⟩ := exists_natCast_quotient q
  exact Subgroup.mul_mem _ (ofNat_mem_closure_primeRange hm)
    (Subgroup.inv_mem _ (ofNat_mem_closure_primeRange hn))

end EulerCharGroup

/-! ## The characters of the completed group -/

open EulerCharGroup

/-- The centered Euler character of a positive rational: `χ_q(z) = q^{-z}`. -/
def eulerRatCharacter (q : EulerCharGroup) (z : ℂ) : ℂ :=
  eulerLaurentCharacter (logVal q) z

theorem eulerRatCharacter_mul (q r : EulerCharGroup) (z : ℂ) :
    eulerRatCharacter (q * r) z = eulerRatCharacter q z * eulerRatCharacter r z := by
  rw [eulerRatCharacter, logVal_mul, eulerLaurentCharacter_add]
  rfl

@[simp]
theorem eulerRatCharacter_one (z : ℂ) : eulerRatCharacter 1 z = 1 := by
  simp [eulerRatCharacter, eulerLaurentCharacter]

/-- **Source reflection supplies the opposite half.**  Reflection in the functional-equation fixed
point sends the character of `q` to the character of `q⁻¹`. -/
theorem eulerRatCharacter_reflection (q : EulerCharGroup) (z : ℂ) :
    eulerRatCharacter q (-z) = eulerRatCharacter q⁻¹ z := by
  rw [eulerRatCharacter, eulerRatCharacter, eulerLaurentCharacter_reflection, logVal_inv]

/-- Reflection inverts every character. -/
theorem eulerRatCharacter_reflection_eq_inv (q : EulerCharGroup) (z : ℂ) :
    eulerRatCharacter q (-z) = (eulerRatCharacter q z)⁻¹ :=
  eulerLaurentCharacter_reflection_eq_inv _ _

/-- The character map is injective, so the character algebra is canonically the group algebra of
the completed group. -/
theorem eulerRatCharacter_injective : Function.Injective eulerRatCharacter := by
  intro q r h
  apply logVal_injective
  have h1 := congrFun h 1
  simp only [eulerRatCharacter, eulerLaurentCharacter, mul_one] at h1
  have key : ((Real.exp (-logVal q) : ℝ) : ℂ) = ((Real.exp (-logVal r) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp]
    push_cast
    exact h1
  have h2 := Real.exp_injective (Complex.ofReal_inj.mp key)
  linarith

/-! ## The scale derivation and the constant-term residue seam -/

/-- The Euler character algebra `ℂ[ℚ_{>0}^×]`. -/
abbrev EulerCharAlgebra := MonoidAlgebra ℂ EulerCharGroup

/-- The eigenvalue of the scale derivation on the mode `χ_q`. -/
def scaleWeight (q : EulerCharGroup) : ℂ := -((logVal q : ℝ) : ℂ)

@[simp]
theorem scaleWeight_one : scaleWeight (1 : EulerCharGroup) = 0 := by
  simp [scaleWeight]

theorem scaleWeight_mul (q r : EulerCharGroup) :
    scaleWeight (q * r) = scaleWeight q + scaleWeight r := by
  simp only [scaleWeight, logVal_mul]
  push_cast
  ring

/-- The scale derivation `D` on the Euler character algebra. -/
def scaleDeriv (f : EulerCharAlgebra) : EulerCharAlgebra :=
  .ofCoeff (f.coeff.sum fun q a => Finsupp.single q (scaleWeight q * a))

theorem scaleDeriv_coeff (f : EulerCharAlgebra) (r : EulerCharGroup) :
    (scaleDeriv f).coeff r = scaleWeight r * f.coeff r := by
  classical
  show (f.coeff.sum fun q a => Finsupp.single q (scaleWeight q * a)) r = _
  rw [Finsupp.sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finsupp.sum_ite_eq' f.coeff r fun q a => scaleWeight q * a]
  by_cases h : r ∈ f.coeff.support
  · simp [h]
  · simp [h, Finsupp.notMem_support_iff.mp h]

theorem scaleDeriv_single (q : EulerCharGroup) (a : ℂ) :
    scaleDeriv (MonoidAlgebra.single q a) = MonoidAlgebra.single q (scaleWeight q * a) := by
  apply MonoidAlgebra.ext
  ext r
  rw [scaleDeriv_coeff, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single,
    Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : q = r
  · subst h; simp
  · simp [h]

theorem scaleDeriv_add (f g : EulerCharAlgebra) :
    scaleDeriv (f + g) = scaleDeriv f + scaleDeriv g := by
  apply MonoidAlgebra.ext
  ext r
  simp [scaleDeriv_coeff, MonoidAlgebra.coeff_add, mul_add]

@[simp]
theorem scaleDeriv_zero : scaleDeriv (0 : EulerCharAlgebra) = 0 := by
  apply MonoidAlgebra.ext
  ext r
  simp [scaleDeriv_coeff]

/-- **Leibniz rule.**  The scale derivation is a derivation of the Euler character algebra. -/
theorem scaleDeriv_mul (f g : EulerCharAlgebra) :
    scaleDeriv (f * g) = scaleDeriv f * g + f * scaleDeriv g := by
  classical
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      rw [add_mul, scaleDeriv_add, h₁, h₂, scaleDeriv_add, add_mul, add_mul]
      ring
  | single q a =>
      induction g using MonoidAlgebra.induction_linear with
      | zero => simp
      | add g₁ g₂ k₁ k₂ =>
          rw [mul_add, scaleDeriv_add, k₁, k₂, scaleDeriv_add, mul_add, mul_add]
          ring
      | single r b =>
          rw [MonoidAlgebra.single_mul_single, scaleDeriv_single, scaleDeriv_single,
            scaleDeriv_single, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
            ← MonoidAlgebra.single_add, scaleWeight_mul]
          congr 1
          ring

/-- The constant term: the coefficient of the neutral rational character. -/
def constantTerm (f : EulerCharAlgebra) : ℂ := f.coeff 1

theorem constantTerm_add (f g : EulerCharAlgebra) :
    constantTerm (f + g) = constantTerm f + constantTerm g := rfl

/-- The constant term of a scale derivative vanishes. -/
theorem constantTerm_scaleDeriv (f : EulerCharAlgebra) : constantTerm (scaleDeriv f) = 0 := by
  simp [constantTerm, scaleDeriv_coeff]

/-- The constant-term residue pairing `ω_E(f, g) = CT(f · D g)`. -/
def residuePairing (f g : EulerCharAlgebra) : ℂ := constantTerm (f * scaleDeriv g)

/-- **Exact pure-mode residue weight.**  `ω_E(χ_q, χ_r)` is `-log r` when `q r = 1` and `0`
otherwise. -/
theorem residuePairing_single (q r : EulerCharGroup) :
    residuePairing (MonoidAlgebra.single q (1 : ℂ)) (MonoidAlgebra.single r (1 : ℂ)) =
      if q * r = 1 then -((logVal r : ℝ) : ℂ) else 0 := by
  classical
  rw [residuePairing, scaleDeriv_single, MonoidAlgebra.single_mul_single, constantTerm,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : q * r = 1
  · simp [h, scaleWeight]
  · simp [h]

/-- The residue pairing is alternating: this is the constant-term derivation law `CT ∘ D = 0`. -/
theorem residuePairing_swap (f g : EulerCharAlgebra) :
    residuePairing f g = -residuePairing g f := by
  have h := constantTerm_scaleDeriv (f * g)
  rw [scaleDeriv_mul, constantTerm_add] at h
  rw [residuePairing, residuePairing, mul_comm g (scaleDeriv f)]
  linear_combination h

/-- **Same-half isotropy.**  Two positive Dirichlet modes never pair: `m n = 1` forces
`m = n = 1`, where the seam weight is zero. -/
theorem residuePairing_natMode_eq_zero {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    residuePairing (MonoidAlgebra.single (ofNat m hm) (1 : ℂ))
      (MonoidAlgebra.single (ofNat n hn) (1 : ℂ)) = 0 := by
  rw [residuePairing_single]
  by_cases h : ofNat m hm * ofNat n hn = 1
  · have hval : ((m : ℚ) * (n : ℚ)) = 1 := congrArg Subtype.val h
    have hmn : m * n = 1 := by exact_mod_cast hval
    have hn1 : n = 1 := by
      rcases n with _ | _ | n
      · omega
      · rfl
      · exfalso
        have hle : 1 * (n + 2) ≤ m * (n + 2) := Nat.mul_le_mul hm (le_refl (n + 2))
        rw [hmn, one_mul] at hle
        omega
    subst hn1
    have hone : ofNat 1 hn = 1 := by apply Subtype.ext; simp [ofNat]
    rw [if_pos h, hone]
    simp
  · rw [if_neg h]

/-- **Opposite-mode nondegeneracy.**  Every mode above the neutral one pairs with its
source-reflected mode with exact weight `log q`. -/
theorem residuePairing_opposite (q : EulerCharGroup) :
    residuePairing (MonoidAlgebra.single q (1 : ℂ)) (MonoidAlgebra.single q⁻¹ (1 : ℂ)) =
      ((logVal q : ℝ) : ℂ) := by
  rw [residuePairing_single, if_pos (mul_inv_cancel q), logVal_inv]
  push_cast
  ring

theorem residuePairing_opposite_ne_zero {q : EulerCharGroup} (hq : q ≠ 1) :
    residuePairing (MonoidAlgebra.single q (1 : ℂ)) (MonoidAlgebra.single q⁻¹ (1 : ℂ)) ≠ 0 := by
  rw [residuePairing_opposite]
  simpa using fun h => hq ((logVal_eq_zero_iff q).mp h)

/-! ## The squarefree prime-apartment charts -/

/-- The centered Dirichlet factor in terms of the Euler character. -/
theorem cpow_neg_eq_eulerRatCharacter {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ (-(1 / 2 + z)) =
      (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * eulerRatCharacter (ofNat n hn) z := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.natCast_log,
    Real.rpow_def_of_pos hnR, Complex.ofReal_exp, eulerRatCharacter, eulerLaurentCharacter,
    logVal_eq_natLog hn, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Positive prime-apartment chart.**  The centered local factor `1 + p^{-s}` at `s = 1/2 + z`. -/
theorem eulerPrimeApartmentChart {p : ℕ} (hp : 0 < p) (z : ℂ) :
    1 + (p : ℂ) ^ (-(1 / 2 + z)) =
      1 + (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * eulerRatCharacter (ofNat p hp) z := by
  rw [cpow_neg_eq_eulerRatCharacter hp]

/-- **Reflected prime-apartment chart.**  The reflected local factor `1 + p^{-(1-s)}` is the same
chart in the inverted character, i.e. the negative torsion chart of the same apartment. -/
theorem eulerPrimeApartmentChart_reflected {p : ℕ} (hp : 0 < p) (z : ℂ) :
    1 + (p : ℂ) ^ (-(1 / 2 + -z)) =
      1 + (((p : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * (eulerRatCharacter (ofNat p hp) z)⁻¹ := by
  rw [cpow_neg_eq_eulerRatCharacter hp, eulerRatCharacter_reflection_eq_inv]

end

end GaloisForLFunctions
