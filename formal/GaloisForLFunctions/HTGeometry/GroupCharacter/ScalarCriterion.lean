import GaloisForLFunctions.HTGeometry.GroupCharacter.Eigenvalues
import GaloisForLFunctions.HTGeometry.GroupCharacter.RootsOfUnitySum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Minpoly.Field

/-!
# The scalar criterion

If `(1 / dim N) * chi hN g` is a nonzero algebraic integer, then `g` acts on `N` by a scalar.
This is the key step of Burnside's `p ^ a q ^ b` theorem.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra Polynomial

theorem exists_ofFn_of_multiset {α : Type*} (E : Multiset α) :
    ∃ f : Fin E.card → α, E = (List.ofFn f : List α) := by
  refine Quot.inductionOn E ?_
  intro l
  exact ⟨fun i => l.get i, by simp⟩

variable {G : Type u} [Group G] [Fintype G]

/-- **The scalar criterion.** -/
theorem exists_rho_eq_smul {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N)
    (hNbot : N ≠ ⊥) (g : G)
    (hint : IsIntegral ℤ ((Module.finrank ℂ ↥N : ℂ)⁻¹ * chi hN g))
    (hne : chi hN g ≠ 0) :
    ∃ ε : ℂ, rho hN g = ε • LinearMap.id := by
  classical
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hNbot
  set d := Module.finrank ℂ ↥N with hd
  have hd0 : d ≠ 0 := (Module.finrank_pos_iff.mpr inferInstance).ne'
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd0)
  set b := Module.finBasis ℂ ↥N with hb
  set A : Matrix (Fin d) (Fin d) ℂ := LinearMap.toMatrix b b (rho hN g) with hA
  set m := Fintype.card G with hm
  have hm0 : m ≠ 0 := Fintype.card_ne_zero
  have hApow : A ^ m = 1 := by
    rw [hA, LinearMap.toMatrix_pow, ← rho_pow, hm, pow_card_eq_one, rho_one]
    simp
  -- the eigenvalue data
  have hEcard : A.charpoly.roots.card = d := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hEroots : ∀ μ ∈ A.charpoly.roots, μ ^ m = 1 := by
    intro μ hμ
    have hne0 : A.charpoly ≠ 0 := (Matrix.charpoly_monic A).ne_zero
    have hroot : A.charpoly.eval μ = 0 := (Polynomial.mem_roots hne0).mp hμ
    rw [Matrix.eval_charpoly] at hroot
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
    have hAv : A.mulVec v = μ • v := by
      have hstep : ((Matrix.scalar (Fin d)) μ - A).mulVec v = 0 := hv
      rw [Matrix.sub_mulVec, sub_eq_zero] at hstep
      rw [← hstep]
      simp [Matrix.scalar_apply]
    have hpow : ∀ k : ℕ, (A ^ k).mulVec v = (μ ^ k) • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have hfin := hpow m
    rw [hApow] at hfin
    simp only [Matrix.one_mulVec] at hfin
    have hz : (μ ^ m - 1) • v = 0 := by rw [sub_smul, one_smul, ← hfin, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  have hEsum : A.charpoly.roots.sum = chi hN g := by
    rw [← Matrix.trace_eq_sum_roots_charpoly, hA, ← LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  obtain ⟨f, hf⟩ := exists_ofFn_of_multiset A.charpoly.roots
  have hfsum : ∑ i, f i = chi hN g := by
    have h1 : ((List.ofFn f : List ℂ) : Multiset ℂ).sum = ∑ i, f i := by
      rw [Multiset.sum_coe, List.sum_ofFn]
    rw [← h1, ← hf]
    exact hEsum
  have hfmem : ∀ i, f i ∈ A.charpoly.roots := by
    intro i
    have h1 : f i ∈ ((List.ofFn f : List ℂ) : Multiset ℂ) := by simp
    rwa [← hf] at h1
  have hfroots : ∀ i, f i ^ m = 1 := fun i => hEroots _ (hfmem i)
  have hcard0 : A.charpoly.roots.card ≠ 0 := by rw [hEcard]; exact hd0
  obtain ⟨ε, hε⟩ := eq_const_of_isIntegral_avg hcard0 hm0 f hfroots
    (by rw [hfsum, hEcard]; exact hint) (by rw [hfsum]; exact hne)
  -- the characteristic polynomial is `(X - ε) ^ d`
  have hrootsrep : A.charpoly.roots = Multiset.replicate d ε := by
    have h1 : ((List.ofFn f : List ℂ) : Multiset ℂ)
        = Multiset.replicate A.charpoly.roots.card ε := by
      rw [funext hε, List.ofFn_const, Multiset.coe_replicate]
    rw [hf, h1, hEcard]
  have hcharpoly : A.charpoly = (X - C ε) ^ d := by
    rw [Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _)
      (Matrix.charpoly_monic A), hrootsrep, Multiset.map_replicate, Multiset.prod_replicate]
  -- the minimal polynomial is `X - ε`
  haveI : Algebra.IsIntegral ℂ (Matrix (Fin d) (Fin d) ℂ) := Algebra.IsIntegral.of_finite _ _
  have hAint : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hdvd1 : minpoly ℂ A ∣ (X - C ε) ^ d := by
    rw [← hcharpoly]
    exact minpoly.dvd ℂ A (Matrix.aeval_self_charpoly A)
  have hdvd2 : minpoly ℂ A ∣ X ^ m - C 1 := by
    refine minpoly.dvd ℂ A ?_
    simp [hApow]
  have hεpow : ε ^ m = 1 := by
    have := hfroots ⟨0, Nat.pos_of_ne_zero hcard0⟩
    rwa [hε] at this
  have hεne : ε ≠ 0 := by
    intro h
    rw [h, zero_pow hm0] at hεpow
    exact zero_ne_one hεpow
  obtain ⟨e, hle, hassoc⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C ε) d).mp hdvd1
  have heq : minpoly ℂ A = (X - C ε) ^ e :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic hAint)
      ((Polynomial.monic_X_sub_C ε).pow e) hassoc
  have he1 : e = 1 := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e
      · exact absurd (by simpa using heq) (minpoly.ne_one ℂ A)
      · rfl
    · exfalso
      have hsq : (X - C ε) ^ 2 ∣ X ^ m - C 1 := by
        refine dvd_trans (pow_dvd_pow _ h) ?_
        rw [← heq]
        exact hdvd2
      have hder : (X - C ε) ∣ derivative (X ^ m - C (1 : ℂ)) := by
        have h0 := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hsq
        simpa using h0
      have hderiv : derivative (X ^ m - C (1 : ℂ)) = C (m : ℂ) * X ^ (m - 1) := by
        simp [derivative_X_pow]
      rw [hderiv, Polynomial.dvd_iff_isRoot] at hder
      have : (m : ℂ) * ε ^ (m - 1) = 0 := by simpa [Polynomial.IsRoot] using hder
      rcases mul_eq_zero.mp this with h1 | h1
      · exact (Nat.cast_ne_zero.mpr hm0) h1
      · exact hεne (pow_eq_zero_iff'.mp h1).1
  rw [he1, pow_one] at heq
  -- conclude
  have hzero : Polynomial.aeval A (minpoly ℂ A) = 0 := minpoly.aeval ℂ A
  rw [heq] at hzero
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at hzero
  refine ⟨ε, ?_⟩
  have hinj : Function.Injective (LinearMap.toMatrix b b) := (LinearMap.toMatrix b b).injective
  refine hinj ?_
  rw [← hA, hzero, map_smul, LinearMap.toMatrix_id]
  exact Algebra.algebraMap_eq_smul_one ε

end GaloisForLFunctions.HTGeometry.GroupCharacter
