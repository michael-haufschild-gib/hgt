import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ModuleFractionLocalization
import Mathlib.RingTheory.IsTensorProduct

/-! Localization commutes with a base-change map that intertwines denominator actions. -/

open TensorProduct

namespace GlobalTheory.ModuleFraction

variable {B R A₀ A M N : Type} [CommRing B] [CommRing R] [CommRing A₀] [CommRing A]
  [Algebra B R] [Algebra B A₀] [Algebra R A] [Algebra B A] [IsScalarTower B R A]
  [AddCommGroup M] [Module B M] [Module A₀ M] [IsScalarTower B A₀ M]
  [AddCommGroup N] [Module B N] [Module R N] [Module A N]
  [IsScalarTower B R N] [IsScalarTower R A N] [IsScalarTower B A N]

omit [Algebra B R] [Algebra R A] [IsScalarTower B R A] [Module R N]
  [IsScalarTower B R N] [IsScalarTower R A N] in
theorem exists_map_of_intertwine (f : M →ₗ[B] N) (u : A₀) (v : A)
    (h : ∀ (k : ℕ) y, f (u ^ k • y) = v ^ k • f y) :
    ∃ F : LocalizedModule.Away u M →ₗ[B] LocalizedModule.Away v N,
      ∀ (k : ℕ) y, F (frac u k y) = frac v k (f y) := by
  choose k a hka using fun z : LocalizedModule.Away u M => exists_frac z
  have evaluate (j : ℕ) (y : M) :
      frac v (k (frac u j y)) (f (a (frac u j y))) = frac v j (f y) := by
    obtain ⟨l, hl⟩ := frac_eq_iff.1 (hka (frac u j y))
    exact frac_eq_iff.2 ⟨l, by rw [← h, ← h, hl]⟩
  refine ⟨⟨⟨fun z => frac v (k z) (f (a z)), fun z w => ?_⟩, fun r z => ?_⟩, evaluate⟩
  · obtain ⟨j, x, rfl⟩ := exists_frac z
    obtain ⟨l, y, rfl⟩ := exists_frac w
    rw [← frac_add_pow_smul u j l x, ← frac_add_pow_smul u l j y, add_comm l j,
      ← map_add, evaluate, evaluate, evaluate, map_add, map_add]
  · obtain ⟨j, y, rfl⟩ := exists_frac z
    simp only [RingHom.id_apply]
    rw [← LinearMap.map_smul_of_tower, evaluate, evaluate, map_smul, LinearMap.map_smul_of_tower]

theorem isBaseChange_of_intertwine (f : M →ₗ[B] N) (hf : IsBaseChange R f) (u : A₀) (v : A)
    (h : ∀ (j : ℕ) y, f (u ^ j • y) = v ^ j • f y)
    (F : LocalizedModule.Away u M →ₗ[B] LocalizedModule.Away v N)
    (hF : ∀ (j : ℕ) y, F (frac u j y) = frac v j (f y)) : IsBaseChange R F := by
  let q (k : ℕ) : R ⊗[B] M →ₗ[R] R ⊗[B] LocalizedModule.Away u M :=
    ((frac u k).restrictScalars B).baseChange R
  let P (k : ℕ) : R ⊗[B] M →ₗ[R] R ⊗[B] M :=
    ((LinearMap.lsmul A₀ M (u ^ k)).restrictScalars B).baseChange R
  have hqP (k l : ℕ) (z : R ⊗[B] M) : q (k + l) (P l z) = q k z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r y => exact congrArg (r ⊗ₜ[B] ·) (frac_add_pow_smul u k l y)
    | add x y hx hy => simp only [map_add, hx, hy]
  have hP (l : ℕ) (z : R ⊗[B] M) : hf.equiv (P l z) = v ^ l • hf.equiv z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul r y => simp [P, IsBaseChange.equiv_tmul, h, smul_comm r]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  have hq (k : ℕ) (z : R ⊗[B] M) : F.liftBaseChange R (q k z) = frac v k (hf.equiv z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r y => simp [q, IsBaseChange.equiv_tmul, hF, LinearMap.map_smul_of_tower]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hrep (z : R ⊗[B] LocalizedModule.Away u M) : ∃ k y, q k y = z := by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, map_zero _⟩
    | tmul r z =>
      obtain ⟨k, y, rfl⟩ := exists_frac z
      exact ⟨k, r ⊗ₜ y, by simp [q]⟩
    | add x y hx hy =>
      obtain ⟨k, a, rfl⟩ := hx
      obtain ⟨l, b, rfl⟩ := hy
      exact ⟨k + l, P l a + P k b, by rw [map_add, hqP, add_comm k l, hqP]⟩
  suffices hb : Function.Bijective (F.liftBaseChange R) from
    IsBaseChange.of_equiv (LinearEquiv.ofBijective _ hb) fun z => by simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨k, y, rfl⟩ := hrep z
    rw [hq, frac_eq_zero_iff] at hz
    obtain ⟨l, hl⟩ := hz
    rw [← hP, map_eq_zero_iff _ hf.equiv.injective] at hl
    rw [← hqP k l, hl, map_zero]
  · intro z
    obtain ⟨k, y, rfl⟩ := exists_frac z
    obtain ⟨a, rfl⟩ := hf.equiv.surjective y
    exact ⟨q k a, hq k a⟩

end GlobalTheory.ModuleFraction
