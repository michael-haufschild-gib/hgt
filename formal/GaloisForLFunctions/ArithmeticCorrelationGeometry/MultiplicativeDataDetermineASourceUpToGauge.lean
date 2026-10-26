import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Multiplicative data determine a source up to gauge

Let `a, b` be sources that are nonzero on a finite set `S` of positive integers. Their
**multiplicative data agree** if `|b_n| = |a_n|` on `S` and, along every multiplicative relation
`∏_{n ∈ S} n^{k_n} = 1` (`k ∈ ℤ^S`, `Σ k_n v(n) = 0` for the exponent vectors `v(n)`), the ratios
satisfy `∏ (b_n/a_n)^{k_n} = 1` (`AgreeMultiplicatively`). These are exactly the coincident
monomials of `MultiplicativeObservationIsGaugeInvariant` written with signed exponents.

**Theorem** (`agreeMultiplicatively_iff_exists_twist`). The multiplicative data of `a` and `b`
agree on `S` iff `b = χ_x a` on `S` for a gauge point `x`.

The reverse direction is gauge invariance. The forward direction is phase reconstruction: the
phases of `b/a` define a homomorphism on the relation-free quotient of `ℤ^S`, which embeds into
the exponent lattice `ℤ^{(primes)}`; the circle `ℝ/ℤ` is divisible, hence an injective `ℤ`-module
(`Module.Baer.of_divisible`), so the homomorphism extends to the whole lattice, i.e. to a point of
the gauge torus.

So multiplicative observation determines a source exactly up to its gauge orbit, and no further:
everything it cannot see — successor correlations, near-incidences, boundary corrections — is a
function on the orbit. "Arithmetic determination" of a mixed law is the choice of one point of the
orbit.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry

/-! ### Relations and phases -/

/-- The exponent vector of a signed combination `Σ k_n v(n)` of the elements of `S`. -/
def relVec (S : Finset ℕ) : (S →₀ ℤ) →+ (ℕ →₀ ℤ) :=
  Finsupp.liftAddHom fun n => zmultiplesHom _ (expVec n)

/-- **Agreement of multiplicative data on `S`.** -/
def AgreeMultiplicatively (S : Finset ℕ) (a b : ℕ → ℂ) : Prop :=
  (∀ n ∈ S, ‖b n‖ = ‖a n‖) ∧
    ∀ k : S →₀ ℤ, relVec S k = 0 → (k.prod fun n z => (b n / a n) ^ z) = 1

/-- The phase of a unimodular ratio. -/
def phase (z : ℂ) : UnitAddCircle := ((Complex.arg z / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem fourier_one_phase {z : ℂ} (hz : ‖z‖ = 1) : (fourier 1 (phase z) : ℂ) = z := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at h
  rw [phase, fourier_coe_apply]
  conv_rhs => rw [← h]
  congr 1
  push_cast
  field_simp

/-- `fourier 1` turns integer multiples into powers. -/
theorem fourier_one_zsmul (z : ℤ) (t : UnitAddCircle) :
    (fourier 1 (z • t) : ℂ) = (fourier 1 t : ℂ) ^ z := by
  rw [fourier_apply, fourier_apply, one_smul, one_smul, AddCircle.toCircle_zsmul]
  push_cast
  rfl

/-- `fourier 1` detects the zero of the circle. -/
theorem eq_zero_of_fourier_one_eq_one {t : UnitAddCircle} (h : (fourier 1 t : ℂ) = 1) : t = 0 := by
  rw [fourier_one] at h
  have h' : AddCircle.toCircle t = AddCircle.toCircle (0 : UnitAddCircle) := by
    rw [AddCircle.toCircle_zero]
    exact Subtype.ext h
  exact AddCircle.injective_toCircle one_ne_zero h'

/-- The phase homomorphism `k ↦ Σ k_n θ_n`. -/
def phaseHom (S : Finset ℕ) (θ : ℕ → UnitAddCircle) : (S →₀ ℤ) →+ UnitAddCircle :=
  Finsupp.liftAddHom fun n => zmultiplesHom _ (θ n)

theorem fourier_one_phaseHom (S : Finset ℕ) (θ : ℕ → UnitAddCircle) (k : S →₀ ℤ) :
    (fourier 1 (phaseHom S θ k) : ℂ) = k.prod fun n z => (fourier 1 (θ n) : ℂ) ^ z := by
  classical
  induction k using Finsupp.induction with
  | zero => simp [phaseHom]
  | single_add n z k hn hz ih =>
    rw [map_add, fourier_add_arg, Finsupp.prod_add_index_of_disjoint, ih]
    · congr 1
      rw [Finsupp.prod_single_index (by simp)]
      simp only [phaseHom, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
      exact fourier_one_zsmul z (θ n)
    · rw [Finsupp.support_single _ hz]
      simpa using hn

/-! ### Characters of the exponent lattice are gauge points -/

theorem torusCharacter_mul_conj (v : ℕ →₀ ℤ) (x : GaugeTorus) :
    torusCharacter v x * conj (torusCharacter v x) = 1 := by
  rw [← torusCharacter_neg_index, ← torusCharacter_add_index, add_neg_cancel, torusCharacter_zero]

theorem torusCharacter_ne_zero (v : ℕ →₀ ℤ) (x : GaugeTorus) : torusCharacter v x ≠ 0 := by
  intro h
  have := torusCharacter_mul_conj v x
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- Characters of integer multiples are powers. -/
theorem torusCharacter_zsmul (z : ℤ) (v : ℕ →₀ ℤ) (x : GaugeTorus) :
    torusCharacter (z • v) x = torusCharacter v x ^ z := by
  induction z using Int.induction_on with
  | zero => rw [zero_smul, torusCharacter_zero, zpow_zero]
  | succ i ih =>
    rw [add_smul, one_smul, torusCharacter_add_index, ih,
      zpow_add_one₀ (torusCharacter_ne_zero v x)]
  | pred i ih =>
    have hinv : conj (torusCharacter v x) = (torusCharacter v x)⁻¹ :=
      eq_inv_of_mul_eq_one_right (torusCharacter_mul_conj v x)
    rw [sub_smul, one_smul, sub_eq_add_neg, torusCharacter_add_index, ih, torusCharacter_neg_index,
      hinv, ← zpow_sub_one₀ (torusCharacter_ne_zero v x), sub_eq_add_neg]

/-- The gauge point of a character of the exponent lattice. -/
def gaugeOfChar (χ : (ℕ →₀ ℤ) →+ UnitAddCircle) : GaugeTorus := fun p => χ (Finsupp.single p 1)

theorem torusCharacter_gaugeOfChar (χ : (ℕ →₀ ℤ) →+ UnitAddCircle) (v : ℕ →₀ ℤ) :
    torusCharacter v (gaugeOfChar χ) = (fourier 1 (χ v) : ℂ) := by
  classical
  induction v using Finsupp.induction with
  | zero => simp [torusCharacter_zero]
  | single_add p z v hp hz ih =>
    rw [torusCharacter_add_index, ih, map_add, fourier_add_arg]
    congr 1
    rw [torusCharacter_apply_of_subset (s := {p}) Finsupp.support_single_subset,
      Finset.prod_singleton, Finsupp.single_eq_same, gaugeOfChar,
      show Finsupp.single p z = z • Finsupp.single p (1 : ℤ) by simp, map_zsmul, fourier_apply,
      fourier_apply, one_smul]

/-! ### Phase reconstruction -/

/-- **Phase reconstruction.** Phases that respect every multiplicative relation of `S` are the
values of a gauge twist on `S`. -/
theorem exists_twist_of_relations (S : Finset ℕ) (θ : ℕ → UnitAddCircle)
    (hrel : ∀ k : S →₀ ℤ, relVec S k = 0 → phaseHom S θ k = 0) :
    ∃ x : GaugeTorus, ∀ n ∈ S, twist x n = (fourier 1 (θ n) : ℂ) := by
  -- factor the phases through the image of the relation map, then extend
  have hker : (relVec S).ker ≤ (phaseHom S θ).ker := fun k hk => hrel k hk
  set Ψ := QuotientAddGroup.lift (relVec S).ker (phaseHom S θ) hker with hΨ
  set ι := QuotientAddGroup.kerLift (relVec S) with hι
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom ι
    (QuotientAddGroup.kerLift_injective _) Ψ
  refine ⟨gaugeOfChar χ, fun n hn => ?_⟩
  have hval : χ (expVec n) = θ n := by
    have h1 := congrArg (fun F => F (QuotientAddGroup.mk (Finsupp.single ⟨n, hn⟩ (1 : ℤ)))) hχ
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, hι, hΨ,
      QuotientAddGroup.kerLift_mk, QuotientAddGroup.lift_mk] at h1
    simpa [relVec, phaseHom] using h1
  rw [twist, torusCharacter_gaugeOfChar, hval]

/-- **Gauge twists agree multiplicatively with their source.** -/
theorem agreeMultiplicatively_twisted (S : Finset ℕ) {a : ℕ → ℂ} (ha : ∀ n ∈ S, a n ≠ 0)
    (x : GaugeTorus) : AgreeMultiplicatively S a (twisted x a) := by
  classical
  refine ⟨fun n _ => by rw [twisted, norm_mul, norm_twist, one_mul], fun k hk => ?_⟩
  have hratio : ∀ n : S, twisted x a n / a n = twist x n := fun n => by
    rw [twisted, mul_div_assoc, div_self (ha n n.2), mul_one]
  simp_rw [hratio]
  -- the product of twists is the torus character of the relation vector
  have hprod : ∀ k : S →₀ ℤ,
      (k.prod fun n z => twist x n ^ z) = torusCharacter (relVec S k) x := by
    intro k
    induction k using Finsupp.induction with
    | zero => simp [torusCharacter_zero]
    | single_add n z k hn hz ih =>
      rw [map_add, torusCharacter_add_index, ← ih, Finsupp.prod_add_index_of_disjoint]
      · congr 1
        rw [Finsupp.prod_single_index (by simp)]
        simp only [relVec, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
        rw [torusCharacter_zsmul]
        rfl
      · rw [Finsupp.support_single _ hz]
        simpa using hn
  rw [hprod, hk, torusCharacter_zero]

/-- **Multiplicative data determine a source exactly up to gauge.** -/
theorem agreeMultiplicatively_iff_exists_twist (S : Finset ℕ) {a b : ℕ → ℂ}
    (ha : ∀ n ∈ S, a n ≠ 0) :
    AgreeMultiplicatively S a b ↔ ∃ x : GaugeTorus, ∀ n ∈ S, b n = twisted x a n := by
  classical
  constructor
  · rintro ⟨hnorm, hrel⟩
    have hunit : ∀ n ∈ S, ‖b n / a n‖ = 1 := fun n hn => by
      rw [norm_div, hnorm n hn, div_self (norm_ne_zero_iff.mpr (ha n hn))]
    obtain ⟨x, hx⟩ := exists_twist_of_relations S (fun n => phase (b n / a n)) fun k hk => by
      have h2 : (fourier 1 (phaseHom S (fun n => phase (b n / a n)) k) : ℂ) = 1 := by
        rw [fourier_one_phaseHom, ← hrel k hk]
        exact Finset.prod_congr rfl fun n _ => by dsimp only; rw [fourier_one_phase (hunit n n.2)]
      exact eq_zero_of_fourier_one_eq_one h2
    refine ⟨x, fun n hn => ?_⟩
    rw [twisted, hx n hn, fourier_one_phase (hunit n hn), div_mul_cancel₀ _ (ha n hn)]
  · rintro ⟨x, hx⟩
    have hagree := agreeMultiplicatively_twisted S ha x
    refine ⟨fun n hn => by rw [hx n hn]; exact hagree.1 n hn, fun k hk => ?_⟩
    rw [← hagree.2 k hk]
    exact Finset.prod_congr rfl fun n _ => by dsimp only; rw [hx n n.2]

end GaloisForLFunctions.ArithmeticCorrelationGeometry
