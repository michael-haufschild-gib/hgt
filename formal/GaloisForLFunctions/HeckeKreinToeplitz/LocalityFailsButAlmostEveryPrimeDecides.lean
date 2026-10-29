import GaloisForLFunctions.HeckeKreinToeplitz.TheHeckeOrbitKernelOfAZeroConfiguration
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex

/-!
# Locality fails, but almost every prime decides

Positivity on coordinate circles is not positivity on the torus.

**Locality fails** (`locality_fails`). On `ℤ²` the kernel `δ₀ + 2(δ_{(1,1)} + δ_{(−1,−1)})` restricts to
`δ₀` on both coordinate axes, which is positive definite (`isPosDefKernel_delta`), yet the two
points `0, (1,1)` give the Gram matrix `[[1, 2], [2, 1]]` with a negative square. A kernel can be
positive on every coordinate circle and fail on the diagonal; this is the Toeplitz face of the
failure of multivariable Fejér–Riesz.

**Arithmetic kernels are decided by almost every prime**
(`negIndex_eq_zero_of_posDef_on_infinitely_many_towers`). For a positive-definite part plus the
reflected pairs of finitely many distinct points right of the critical line, at most `κ(κ−1)/2`
primes are blind, so positivity on infinitely many prime towers forces index zero, hence
positivity on `ℚ_{>0}`. The local-to-global law holds for the arithmetic class because every right
zero is off the unit circle at every prime and a pair of zeros aliases at most at one prime.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### The delta kernel -/

section Delta

variable {G : Type*} [Group G] [DecidableEq G]

/-- The kernel `δ₁`. -/
def deltaKernel (G : Type*) [Group G] [DecidableEq G] : G → ℂ := fun u => if u = 1 then 1 else 0

/-- `δ₁` is positive definite: on distinct points its Gram matrix is the identity. -/
theorem isPosDefKernel_delta : IsPosDefKernel (deltaKernel G) := by
  have hh : IsHermKernel (deltaKernel G) := fun u => by
    by_cases h : u = 1 <;> simp [deltaKernel, h, inv_eq_one]
  refine (isPosDefKernel_iff hh).mpr (nonpos_iff_eq_zero.mp ?_)
  rw [negIndex_le_iff]
  intro n x
  refine (Nat.cast_le.mpr (hermNegIndex_gram_le_image _ x)).trans (le_of_eq ?_)
  rw [Nat.cast_eq_zero]
  refine ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg fun c => ?_
  rw [hermQuad_gram]
  have : ∑ a : univ.image x, ∑ b : univ.image x,
      conj (c a) * deltaKernel G (((a : G))⁻¹ * (b : G)) * c b = ∑ a, conj (c a) * c a := by
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single a fun b hb => by
      have : ((a : G))⁻¹ * (b : G) ≠ 1 := fun h =>
        hb (Subtype.ext (inv_mul_eq_one.mp h).symm)
      simp [deltaKernel, this]]
    simp [deltaKernel]
  rw [this, re_sum]
  refine sum_nonneg fun a _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end Delta

/-! ### Locality fails on `ℤ²` -/

/-- The diagonal generator `(1, 1)` of `ℤ²`. -/
def diag : Multiplicative ℤ × Multiplicative ℤ := (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)

/-- The kernel `δ₀ + 2(δ_{(1,1)} + δ_{(−1,−1)})` on `ℤ²`. -/
def diagKernel (u : Multiplicative ℤ × Multiplicative ℤ) : ℂ :=
  if u = 1 then 1 else if u = diag ∨ u = diag⁻¹ then 2 else 0

theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ℤ)) ≠ 1 := by
  rw [Ne, ofAdd_eq_one]; exact one_ne_zero

theorem diagKernel_inl (a : Multiplicative ℤ) :
    diagKernel (MonoidHom.inl _ _ a) = deltaKernel (Multiplicative ℤ) a := by
  have h1 : (MonoidHom.inl _ _ a : Multiplicative ℤ × Multiplicative ℤ) ≠ diag := fun h =>
    ofAdd_one_ne_one (congrArg Prod.snd h).symm
  have h2 : (MonoidHom.inl _ _ a : Multiplicative ℤ × Multiplicative ℤ) ≠ diag⁻¹ := fun h =>
    ofAdd_one_ne_one (inv_eq_one.mp (congrArg Prod.snd h).symm)
  simp only [diagKernel, deltaKernel, h1, h2, or_self, if_false]
  by_cases ha : a = 1 <;> simp [ha]

theorem diagKernel_inr (b : Multiplicative ℤ) :
    diagKernel (MonoidHom.inr _ _ b) = deltaKernel (Multiplicative ℤ) b := by
  have h1 : (MonoidHom.inr _ _ b : Multiplicative ℤ × Multiplicative ℤ) ≠ diag := fun h =>
    ofAdd_one_ne_one (congrArg Prod.fst h).symm
  have h2 : (MonoidHom.inr _ _ b : Multiplicative ℤ × Multiplicative ℤ) ≠ diag⁻¹ := fun h =>
    ofAdd_one_ne_one (inv_eq_one.mp (congrArg Prod.fst h).symm)
  simp only [diagKernel, deltaKernel, h1, h2, or_self, if_false]
  by_cases hb : b = 1 <;> simp [hb]

/-- **Locality fails.** The kernel is positive definite on both coordinate axes of `ℤ²` but has a
negative square. -/
theorem locality_fails :
    IsPosDefKernel (diagKernel ∘ MonoidHom.inl _ _) ∧ IsPosDefKernel (diagKernel ∘ MonoidHom.inr _ _) ∧
      1 ≤ negIndex diagKernel := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show diagKernel ∘ MonoidHom.inl _ _ = deltaKernel (Multiplicative ℤ) from
      funext diagKernel_inl]
    exact isPosDefKernel_delta
  · rw [show diagKernel ∘ MonoidHom.inr _ _ = deltaKernel (Multiplicative ℤ) from
      funext diagKernel_inr]
    exact isPosDefKernel_delta
  · -- the two points `1, (1,1)` with coefficients `1, −1`
    set x : Fin 2 → Multiplicative ℤ × Multiplicative ℤ := ![1, diag]
    set c : Fin 2 → ℂ := ![1, -1]
    have hdiag : diag ≠ 1 := fun h => ofAdd_one_ne_one (congrArg Prod.fst h)
    have hneg : hermQuad (gram diagKernel x) c < 0 := by
      rw [hermQuad_gram]
      simp [Fin.sum_univ_two, x, c, diagKernel, hdiag]
      norm_num
    have h1 : Fintype.card (Fin 1) ≤ hermNegIndex (gram diagKernel x) :=
      card_le_hermNegIndex_of_forall_neg _ (LinearMap.toSpanSingleton ℂ _ c ∘ₗ
        LinearMap.proj (0 : Fin 1)) fun a ha => by
        have ha0 : a 0 ≠ 0 := fun h => ha (funext fun i => by fin_cases i; exact h)
        simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.toSpanSingleton_apply]
        rw [ArithmeticCastelnuovoSeveri.hermQuad_smul]
        exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr ha0) hneg
    rw [Fintype.card_fin] at h1
    exact (Nat.cast_le.mpr h1).trans (hermNegIndex_gram_le_negIndex _ x)

/-! ### Almost every prime decides arithmetic kernels -/

/-- **Positivity on infinitely many prime towers forces index zero** for a positive-definite part
plus the reflected pairs of distinct points right of the critical line. -/
theorem negIndex_eq_zero_of_posDef_on_infinitely_many_towers {κ : ℕ} {p : HeckeLattice → ℂ}
    (hp : IsPosDefKernel p) (ρ : Fin κ → ℂ) (hρ : Function.Injective ρ)
    (hre : ∀ j, 1 / 2 < (ρ j).re) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0)
    (h : {q : ℕ | ∃ hq : q.Prime, negIndex ((fun g => p g + ∑ j, pairKernel (zeroChar (ρ j))
      (ω j) g) ∘ zpowersHom _ (primeElt hq)) = 0}.Infinite) :
    negIndex (fun g => p g + ∑ j, pairKernel (zeroChar (ρ j)) (ω j) g) = 0 := by
  obtain ⟨q, ⟨hq, hq0⟩, hnb⟩ := (h.sdiff (ncard_blindPrimes_le ρ hρ).1).nonempty
  have hκ := negIndex_prime_eq_of_not_blind hp ρ hre ω hω hq hnb
  rw [hq0] at hκ
  rw [negIndex_hecke_pairs_eq hp ρ hρ hre ω hω]
  exact hκ.symm

end GaloisForLFunctions.HeckeKreinToeplitz
