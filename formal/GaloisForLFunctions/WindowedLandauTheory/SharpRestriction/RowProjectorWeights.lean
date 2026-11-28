import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.MonicPolynomialCoordinates
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

/-! The spectral idempotents sum to one over all monic labels.
The unipotent and Jacquet idempotents have positive identity
coefficients, so their label weights have total mass one. -/

noncomputable section

open Finset Polynomial Matrix
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

local instance factG {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

section Weights

variable {D : D7}

theorem wtOf_eq_zero_of_not_label {k : Fin 2} (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    {f : (ZMod (D.host.g k))[X]} (hf : ¬ IsLabel D k f) : wtOf D k a f = 0 := by
  unfold wtOf
  rw [D.ntypes.eSer_zero k f hf, mul_zero]
  simp

theorem sum_eSer (k : Fin 2) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (WindowedLandauTheory.CyclotomicNorms.monicOf c) = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  have hsurj (f : (ZMod (D.host.g k))[X]) (hf : f ∈ S) :
      f = monicOf (fun i : Fin D.R.r => f.coeff (i : ℕ)) := by
    obtain ⟨hm, hdeg, -⟩ := (hS f).1 hf
    exact (monicOf_coeffs f hm hdeg).symm
  have himg : ∑ f ∈ Finset.univ.image (fun c : Fin D.R.r → ZMod (D.host.g k) => WindowedLandauTheory.CyclotomicNorms.monicOf c),
      D.ntypes.eSer k f = ∑ c, D.ntypes.eSer k (WindowedLandauTheory.CyclotomicNorms.monicOf c) :=
    Finset.sum_image (fun a _ b _ h => monicOf_injective h)
  rw [← himg, ← hsum]
  symm
  apply Finset.sum_subset
  · intro f hf
    rw [Finset.mem_image]
    exact ⟨_, Finset.mem_univ _, (hsurj f hf).symm⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f (fun h => hf ((hS f).2 h))

theorem sum_wtOf (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (ha : (a.coeff 1).re ≠ 0) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), wtOf D k a (WindowedLandauTheory.CyclotomicNorms.monicOf c) = 1 := by
  have h := sum_eSer (D := D) k
  let L : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) →+ ℝ :=
    AddMonoidHom.mk' (fun x => (x.coeff 1).re) (fun x y => by simp)
  have hL : ∀ x, L x = (x.coeff 1).re := fun x => rfl
  have hs := map_sum L (fun c : Fin D.R.r → ZMod (D.host.g k) => a * D.ntypes.eSer k (WindowedLandauTheory.CyclotomicNorms.monicOf c)) Finset.univ
  simp only [hL] at hs
  rw [← Finset.mul_sum, h, mul_one] at hs
  unfold wtOf
  rw [← Finset.sum_div, ← hs, div_self ha]

end Weights

section Value

theorem entN_one_ne {A : Type} [Zero A] [One A] {N : ℕ} {a b : ℕ} (h : a ≠ b) :
    entN (1 : Matrix (Fin N) (Fin N) A) a b = 0 := by
  unfold entN
  split_ifs with h'
  · exact Matrix.one_apply_ne (fun he => h (congrArg Fin.val he))
  · rfl

theorem eDat_coeff_one_re_pos (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) (hP : P 1) (hφ : φ 1 = 0) :
    0 < ((eDat g N P φ ψ₀).coeff 1).re := by
  classical
  have h1 : (ψ₀ (φ 1))⁻¹ = 1 := by rw [hφ, AddChar.map_zero_eq_one, inv_one]
  have hc : 0 < (Finset.univ.filter
      (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g)))).card :=
    Finset.card_pos.mpr ⟨1, by simp [hP]⟩
  unfold eDat
  simp
  rw [Finset.sum_eq_single (1 : GL (Fin N) (ZMod g))]
  · simp [hφ]
    exact Finset.card_pos.mp hc
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (by simp [hP]) h

theorem eU_coeff_one_re_pos (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    0 < ((eU g N ψ₀).coeff 1).re := by
  unfold eU
  refine eDat_coeff_one_re_pos g N _ _ ψ₀ ?_ ?_
  · intro a b
    exact ⟨fun hab => Matrix.one_apply_ne hab.ne', fun hab => by subst hab; exact Matrix.one_apply_eq a⟩
  · exact Finset.sum_eq_zero fun i _ => entN_one_ne (by omega)

theorem eJ_coeff_one_re_pos (g N kk s : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    0 < ((eJ g N kk s ψ₀).coeff 1).re := by
  unfold eJ
  have e : ∀ a b : ℕ, a ≠ b → entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) a b = 0 :=
    fun a b h => entN_one_ne h
  refine eDat_coeff_one_re_pos g N _ _ ψ₀ ?_ ?_
  · refine ⟨?_, fun a _ h2 => e _ _ (by omega)⟩
    intro a b
    exact ⟨fun hab => Matrix.one_apply_ne hab.ne', fun hab => by subst hab; exact Matrix.one_apply_eq a⟩
  · unfold phiJ
    have h1 : ∑ i ∈ Finset.range (s - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) = 0 :=
      Finset.sum_eq_zero fun i _ => e _ _ (by omega)
    have h2 : ∑ i ∈ Finset.range (s - 1),
        entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + kk + 1 + i) (s + kk + 2 + i) = 0 :=
      Finset.sum_eq_zero fun i _ => e _ _ (by omega)
    have h3 : ∑ a ∈ Finset.range (kk - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + a) (s + a + 1) = 0 :=
      Finset.sum_eq_zero fun a _ => e _ _ (by omega)
    rw [h1, h2, h3]
    split_ifs with hs
    · rw [e (s - 1) (s + kk) (by omega), e (s + kk) (s + kk + 1) (by omega)]
      simp
    · simp

theorem eUk_coeff_one_re_pos {D : D7} (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    0 < ((eUk D k ψ₀).coeff 1).re := by
  exact eU_coeff_one_re_pos (D.host.g k) D.R.r ψ₀

theorem eJk_coeff_one_re_pos {D : D7} (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    0 < ((eJk D k ψ₀).coeff 1).re := by
  exact eJ_coeff_one_re_pos (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ₀

end Value

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.sum_wtOf
#print axioms WindowedLandauTheory.ConcN.eJk_coeff_one_re_pos
