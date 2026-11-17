import GaloisForLFunctions.RepresentationLifting.Differential.NilpotentDividedPowerConnection
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Abel

/-!
# Nilpotent residues of logarithmic connections

The Euler connection with a constant nilpotent residue splits by exponent
classes modulo p. Every nonzero class is invertible; the zero class carries
minus the residue. This gives exact kernel and range classifications, including
the explicit obstruction for the free square-zero residue.

The exponent splitting extends the local mechanism of Fersi,
arXiv:2611.20395, Section 4.4, to the existing divided-power coefficient module.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A nonzero scalar minus a nilpotent residue is an invertible coefficient map. -/
def nonresonantEquiv (N : Module.End K V) (hN : IsNilpotent N) (c : K) (hc : c ≠ 0) : V ≃ₗ[K] V :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (hN.smul c⁻¹).isUnit_one_sub.unit).trans
    (LinearEquiv.smulOfNeZero K V c hc)

theorem nonresonantEquiv_apply (N : Module.End K V) (hN : IsNilpotent N)
    (c : K) (hc : c ≠ 0) (v : V) :
    nonresonantEquiv N hN c hc v = c • v - N v := by
  change c • ((hN.smul c⁻¹).isUnit_one_sub.unit : Module.End K V) v = _
  rw [IsUnit.unit_spec]
  change c • (v - c⁻¹ • N v) = _
  rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Degreewise linear equivalences preserve finite coefficient support. -/
def coefficientEquiv (e : ℕ → V ≃ₗ[K] V) : (ℕ →₀ V) ≃ₗ[K] (ℕ →₀ V) where
  toFun f := Finsupp.onFinset f.support (fun n => e n (f n))
    (fun n hn => Finsupp.mem_support_iff.mpr (fun h => hn (by rw [h, map_zero])))
  invFun f := Finsupp.onFinset f.support (fun n => (e n).symm (f n))
    (fun n hn => Finsupp.mem_support_iff.mpr (fun h => hn (by rw [h, map_zero])))
  left_inv f := by ext n; exact (e n).symm_apply_apply (f n)
  right_inv f := by ext n; exact (e n).apply_symm_apply (f n)
  map_add' f g := by ext n; exact map_add (e n) (f n) (g n)
  map_smul' c f := by ext n; exact map_smul (e n) c (f n)

@[simp] theorem coefficientEquiv_apply (e : ℕ → V ≃ₗ[K] V) (f : ℕ →₀ V) (n : ℕ) :
    coefficientEquiv e f n = e n (f n) := rfl

variable (p : ℕ) {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

/-- Logarithmic Euler connection with a constant endomorphism residue. -/
def logarithmicConnection (N : Module.End (ZMod p) W) : Module.End (ZMod p) (ℕ →₀ W) where
  toFun f := Finsupp.onFinset f.support (fun n => (n : ZMod p) • f n - N (f n))
    (fun n hn => Finsupp.mem_support_iff.mpr (fun h => hn (by rw [h, smul_zero, map_zero, sub_self])))
  map_add' f g := by ext n; simp only [Finsupp.onFinset_apply, Finsupp.add_apply, smul_add, map_add]; abel
  map_smul' c f := by
    ext n
    change (n : ZMod p) • (c • f n) - N (c • f n) =
      c • ((n : ZMod p) • f n - N (f n))
    rw [map_smul, smul_sub, smul_comm (n : ZMod p) c]

@[simp] theorem logarithmicConnection_apply (N : Module.End (ZMod p) W) (f : ℕ →₀ W) (n : ℕ) :
    logarithmicConnection p N f n = (n : ZMod p) • f n - N (f n) := rfl

variable [Fact p.Prime]

/-- The nilpotent residue only obstructs the zero exponent class. -/
theorem logarithmicConnection_kernel (N : Module.End (ZMod p) W) (hN : IsNilpotent N)
    (f : ℕ →₀ W) : logarithmicConnection p N f = 0 ↔
      (∀ n : ℕ, (n : ZMod p) ≠ 0 → f n = 0) ∧ ∀ n : ℕ, N (f n) = 0 := by
  constructor
  · intro hf
    have he (n : ℕ) : (n : ZMod p) • f n - N (f n) = 0 :=
      congrArg (fun g : ℕ →₀ W => g n) hf
    have hn (n : ℕ) (h : (n : ZMod p) ≠ 0) : f n = 0 := by
      apply (nonresonantEquiv N hN (n : ZMod p) h).injective
      rw [map_zero, nonresonantEquiv_apply]
      exact he n
    refine ⟨hn, fun n => ?_⟩
    by_cases h : (n : ZMod p) = 0
    · simpa only [h, zero_smul, zero_sub, neg_eq_zero] using he n
    · rw [hn n h, map_zero]
  · rintro ⟨hf, hNf⟩
    ext n
    change (n : ZMod p) • f n - N (f n) = 0
    rw [hNf, sub_zero]
    by_cases h : (n : ZMod p) = 0
    · rw [h, zero_smul]
    · rw [hf n h, smul_zero]

/-- A coefficientwise gauge turns each nonresonant block into the identity. -/
def logarithmicGauge (N : Module.End (ZMod p) W) (hN : IsNilpotent N) :
    (ℕ →₀ W) ≃ₗ[ZMod p] (ℕ →₀ W) :=
  coefficientEquiv (fun n => if h : (n : ZMod p) = 0 then LinearEquiv.refl _ _
    else nonresonantEquiv N hN (n : ZMod p) h)

/-- Exact normal form: the zero exponent class carries minus the residue, and every other class is invertible. -/
theorem logarithmicConnection_normalForm (N : Module.End (ZMod p) W) (hN : IsNilpotent N)
    (f : ℕ →₀ W) (n : ℕ) :
    logarithmicConnection p N ((logarithmicGauge p N hN).symm f) n =
      if (n : ZMod p) = 0 then -N (f n) else f n := by
  classical
  let e : W ≃ₗ[ZMod p] W := if h : (n : ZMod p) = 0 then LinearEquiv.refl _ _
    else nonresonantEquiv N hN (n : ZMod p) h
  change (n : ZMod p) • e.symm (f n) - N (e.symm (f n)) = _
  by_cases h : (n : ZMod p) = 0
  · rw [if_pos h]
    simp only [e, dif_pos h, LinearEquiv.refl_symm, LinearEquiv.refl_apply, h, zero_smul, zero_sub]
  · simp only [if_neg h, e, dif_neg h]
    change (n : ZMod p) • (nonresonantEquiv N hN (n : ZMod p) h).symm (f n) -
      N ((nonresonantEquiv N hN (n : ZMod p) h).symm (f n)) = f n
    rw [← nonresonantEquiv_apply N hN (n : ZMod p) h, LinearEquiv.apply_symm_apply]

/-- The complete solvability obstruction consists of residue-image classes at p-divisible degrees. -/
theorem logarithmicConnection_range (N : Module.End (ZMod p) W) (hN : IsNilpotent N)
    (g : ℕ →₀ W) : (∃ f, logarithmicConnection p N f = g) ↔
      ∀ n : ℕ, (n : ZMod p) = 0 → ∃ v, N v = g n := by
  classical
  constructor
  · rintro ⟨f, rfl⟩ n hn
    refine ⟨-f n, ?_⟩
    simp only [map_neg, logarithmicConnection_apply, hn, zero_smul, zero_sub]
  · intro hg
    have hp (n : ℕ) : ∃ v : W, (n : ZMod p) • v - N v = g n := by
      by_cases hn : (n : ZMod p) = 0
      · obtain ⟨v, hv⟩ := hg n hn
        exact ⟨-v, by rw [hn, zero_smul, zero_sub, map_neg, neg_neg, hv]⟩
      · refine ⟨(nonresonantEquiv N hN (n : ZMod p) hn).symm (g n), ?_⟩
        rw [← nonresonantEquiv_apply N hN (n : ZMod p) hn, LinearEquiv.apply_symm_apply]
    choose v hv using hp
    let f : ℕ →₀ W := Finsupp.onFinset g.support
      (fun n => if n ∈ g.support then v n else 0)
      (fun n hn => by by_contra h; exact hn (if_neg h))
    refine ⟨f, ?_⟩
    ext n
    change (n : ZMod p) • (if n ∈ g.support then v n else 0) -
      N (if n ∈ g.support then v n else 0) = g n
    by_cases hn : n ∈ g.support
    · simpa only [if_pos hn] using hv n
    · rw [if_neg hn, smul_zero, map_zero, sub_self]
      exact (Finsupp.notMem_support_iff.mp hn).symm

/-- For the free square-zero residue, exactly the second components at p-divisible degrees obstruct solvability. -/
theorem squareZero_logarithmic_range (g : ℕ →₀ (W × W)) :
    (∃ f, logarithmicConnection p (squareZeroShift (ZMod p) W) f = g) ↔
      ∀ n : ℕ, (n : ZMod p) = 0 → (g n).2 = 0 := by
  rw [logarithmicConnection_range p (squareZeroShift (ZMod p) W)
    ⟨2, squareZeroShift_sq (ZMod p) W⟩]
  constructor
  · intro h n hn
    obtain ⟨v, hv⟩ := h n hn
    exact (congrArg Prod.snd hv).symm
  · intro h n hn
    refine ⟨(0, (g n).1), ?_⟩
    exact Prod.ext rfl (h n hn).symm

#print axioms squareZero_logarithmic_range

#print axioms logarithmicConnection_range

#print axioms logarithmicConnection_kernel
#print axioms logarithmicConnection_normalForm
end GaloisForLFunctions.RepresentationLifting.DividedPower
