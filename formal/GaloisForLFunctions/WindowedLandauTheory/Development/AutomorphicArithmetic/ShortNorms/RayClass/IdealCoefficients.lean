import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.IntegralRayClasses

/-! Counting and von Mangoldt coefficients of a ray class grouped by absolute norm. -/

open Finset ArithmeticFunction NumberField GlobalTheory.Mem

noncomputable section

namespace GlobalTheory.Hk

section Ray

variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : GlobalTheory.Mem.RayData K M)

def idealsIn (g : D.G) (n : ℕ) : Set (Ideal (𝓞 K)) :=
  {I | I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g}

open Classical in

def lamIdeal (I : Ideal (𝓞 K)) : ℝ :=
  if ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k then Real.log (Ideal.absNorm I.radical) else 0

def aRay (g : D.G) (n : ℕ) : ℝ := ((idealsIn D g n).ncard : ℝ)

def lamRay (g : D.G) (n : ℕ) : ℝ := ∑ᶠ I ∈ idealsIn D g n, lamIdeal I

namespace RayCount

theorem idealsIn_finite (g : D.G) (n : ℕ) : (idealsIn D g n).Finite :=
  (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).subset fun _ h => h.2.2.1

theorem aRay_eq_card (g : D.G) (n : ℕ) : aRay D g n = ((idealsIn_finite D g n).toFinset.card : ℝ) := by
  rw [aRay, Set.ncard_eq_toFinset_card _ (idealsIn_finite D g n)]

theorem lamRay_eq_sum (g : D.G) (n : ℕ) : lamRay D g n = ∑ I ∈ (idealsIn_finite D g n).toFinset, lamIdeal I :=
  finsum_mem_eq_finite_toFinset_sum _ (idealsIn_finite D g n)

theorem lamIdeal_prime_pow (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h0 : P ≠ ⊥) (k : ℕ) (hk : 1 ≤ k) :
    lamIdeal (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [lamIdeal, if_pos ⟨P, k, hP, h0, hk, rfl⟩, Ideal.radical_pow _ (by omega), hP.radical]

theorem lamIdeal_of_not_prime_pow {I : Ideal (𝓞 K)}
    (h : ¬ ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) : lamIdeal I = 0 := by
  rw [lamIdeal, if_neg h]

theorem lamIdeal_unit : lamIdeal (⊤ : Ideal (𝓞 K)) = 0 := by
  unfold lamIdeal; split_ifs <;> simp

end RayCount

end Ray

end GlobalTheory.Hk
