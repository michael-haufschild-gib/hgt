import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GaussianPELForm
import Mathlib.LinearAlgebra.Matrix.Unique

/-! The Gaussian lattice realizes a split PEL datum of signature one. -/

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

open GaussOne

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private def gaussianSplit :
    (𝓞 Qi ⊗[ℤ] ℤ_[5]) ≃ₐ[𝓞 Qi] Matrix (Fin 1) (Fin 1) (𝓞 Qi ⊗[ℤ] ℤ_[5]) :=
  Matrix.uniqueAlgEquiv.symm

/-- The global datum with Gaussian multiplication and its standard polarization. -/
def gaussOneGlobalDatum : Gen.GDatum where
  F := Qi
  bar := barO
  bar_eq := barO_eq
  ω := ζO
  tr := 0
  nm := 1
  tr_eq := by rw [barO_ζO]; simp
  nm_eq := by rw [barO_ζO, mul_neg, ζO_sq]; simp
  disc_neg := by norm_num
  O := 𝓞 Qi
  freeO := inferInstance
  finO := inferInstance
  m := 1
  m_pos := one_pos
  rankO := by simpa only [one_pow, one_mul] using RingOfIntegers.rank Qi
  central := fun x _ => ⟨x, 1, one_ne_zero, by simp⟩
  star := barO.trans (RingEquiv.toOpposite (𝓞 Qi))
  star_star := fun x => by simp [barO_barO]
  star_F := fun c => by simp
  splitSome := ⟨5, inferInstance, ⟨gaussianSplit⟩⟩
  La := 𝓞 Qi
  freeLa := inferInstance
  finLa := inferInstance
  n := 1
  n_pos := le_rfl
  rankLa := by simpa only [one_mul] using RingOfIntegers.rank Qi
  EF := GaussOne.EF
  alt := EF_alt
  nondeg := EF_bij.1
  adj := fun b x y => by simpa using EF_adj b x y
  a := 1
  ρc := Complex.I
  ρc_root := by simp
  tau := ⟨fun _ => τ₀, fun i j _ => Subsingleton.elim i j⟩
  tau_ω := fun _ => τ₀_ii
  dom := by
    refine ⟨J, J_J, J_EF, J_pos, ?_, ?_⟩
    · intro b A hA
      rw [A_eq b A hA, J, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
      congr 1
      exact LinearMap.ext fun y => by simp [mul_left_comm]
    · intro c A hA
      have hA' : ∀ x : 𝓞 Qi, A (1 ⊗ₜ x) = 1 ⊗ₜ (c • x) := by simpa using hA
      rw [A_eq c A hA', J, ← LinearMap.baseChange_comp, ← LinearMap.mulLeft_mul,
        LinearMap.trace_baseChange, LinearMap.trace_baseChange]
      obtain ⟨a, b, rfl⟩ := coordO c
      rw [ζ_mul_coord, trace_mulLeft, trace_mulLeft]
      intro S
      have hS : S = (a : ℂ) + b * Complex.I := by
        simp only [S, Nat.cast_one, one_mul, Finset.univ_unique, Finset.sum_singleton, filt]
        show τ₀ _ + (starRingEnd ℂ) (τ₀ _) - (starRingEnd ℂ) (τ₀ _) = _
        rw [add_sub_cancel_right, τ₀_int]
      rw [hS]
      simp

/-- The rational prime five splits, and the lattice pairing is perfect there. -/
def gaussOneDatum : Datum 5 where
  toGDatum := gaussOneGlobalDatum
  disc_p := by norm_num [gaussOneGlobalDatum]
  split := ⟨2, by norm_num [gaussOneGlobalDatum]⟩
  splitP := ⟨gaussianSplit⟩
  perfP := ⟨1, Nat.coprime_one_left 5, fun f => by simpa using EF_bij.2 f⟩

theorem exists_datum_a_one :
    ∃ (_ : Fact (Nat.Prime 5)) (D : Datum 5), D.a = 1 ∧ D.n = 1 ∧ D.m = 1 :=
  ⟨inferInstance, gaussOneDatum, rfl, rfl, rfl⟩

theorem Gen.exists_gDatum_one_one_one : ∃ G : GDatum, G.a = 1 ∧ G.n = 1 ∧ G.m = 1 :=
  ⟨gaussOneGlobalDatum, rfl, rfl, rfl⟩

instance : Nonempty Gen.GDatum := ⟨gaussOneGlobalDatum⟩

end GlobalTheory.UPel.HT
