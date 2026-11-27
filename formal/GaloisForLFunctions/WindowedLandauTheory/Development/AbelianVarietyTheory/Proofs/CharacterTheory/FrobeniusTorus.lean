import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobius
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteFieldFrobeniusPeriods
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-! Frobenius orbits and character orthogonality on finite-field tori. -/

open Polynomial

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] [Finite F]

theorem roots_minpoly_eq_map_range (α : AlgebraicClosure F) :
    ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots =
      (Multiset.range (minpoly F α).natDegree).map fun i => α ^ Nat.card F ^ i := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic F (AlgebraicClosure F)
  have hσ : ∀ (i : ℕ) (x : AlgebraicClosure F), (σ ^ i) x = x ^ Nat.card F ^ i := fun i x => by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Nat.card_eq_fintype_card]
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hne : (minpoly F α).map (algebraMap F (AlgebraicClosure F)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  have key : ∀ i j, i < j → j < (minpoly F α).natDegree →
      α ^ Nat.card F ^ i = α ^ Nat.card F ^ j → False := by
    intro i j hij hj h
    have hfix : α ^ Nat.card F ^ (j - i) = α := by
      apply (σ ^ i).injective
      rw [hσ, hσ, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
      exact h.symm
    have hdvd := (minpoly_natDegree_dvd_iff_pow α (j - i)).mpr hfix
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnodup : ((Multiset.range (minpoly F α).natDegree).map
      fun i => α ^ Nat.card F ^ i).Nodup := by
    refine (Multiset.nodup_range _).map_on ?_
    intro i hi j hj hij
    rw [Multiset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · rw [Multiset.le_iff_subset hnodup]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    rw [mem_roots hne, IsRoot, eval_map_algebraMap, ← hσ, aeval_algHom_apply, minpoly.aeval,
      map_zero]
  · calc ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).roots.card
        ≤ ((minpoly F α).map (algebraMap F (AlgebraicClosure F))).natDegree := card_roots' _
      _ = (minpoly F α).natDegree := natDegree_map _
      _ = _ := by simp

private theorem sum_range_mul_eq_nsmul_of_periodic {M : Type} [AddCommMonoid M] (f : ℕ → M) (d : ℕ)
    (hf : ∀ i j, f (d * j + i) = f i) (e : ℕ) :
    ∑ i ∈ Finset.range (d * e), f i = e • ∑ i ∈ Finset.range d, f i := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hf i e

/-- The characteristic root sum on a torus element is its sum over the full Frobenius orbit,
including repetitions when the minimal polynomial has smaller degree. -/
theorem torus_minpoly (θ : AlgebraicClosure F →* ℂ) (n : ℕ) (hn : 0 < n)
    (α : AlgebraicClosure F) (hα : α ^ (Nat.card F ^ n - 1) = 1) :
    (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧
      ∀ k : ℕ, rootSum θ k (minpoly F α ^ (n / (minpoly F α).natDegree)) =
        ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqn : 1 < Nat.card F ^ n := Nat.one_lt_pow (by omega) hq
  have hfix : α ^ Nat.card F ^ n = α := by
    calc α ^ Nat.card F ^ n = α ^ (Nat.card F ^ n - 1) * α := by
          rw [← pow_succ, Nat.sub_add_cancel hqn.le]
      _ = α := by rw [hα, one_mul]
  have hd := (minpoly_natDegree_dvd_iff_pow α n).mpr hfix
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hα
    exact zero_ne_one hα
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  refine ⟨hd, minpoly.coeff_zero_ne_zero hint hα0, fun k => ?_⟩
  obtain ⟨e, he⟩ := hd
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hint
  have hper : ∀ i j, α ^ Nat.card F ^ ((minpoly F α).natDegree * j + i) =
      α ^ Nat.card F ^ i := fun i j => by
    rw [pow_add, pow_mul,
      (minpoly_natDegree_dvd_iff_pow α _).mp (dvd_mul_right _ _)]
  rw [he, Nat.mul_div_cancel_left e hdpos,
    sum_range_mul_eq_nsmul_of_periodic (fun i => θ (α ^ Nat.card F ^ i) ^ k) _
      (fun i j => by simp only [hper]) e]
  unfold rootSum
  rw [Polynomial.map_pow, roots_pow, roots_minpoly_eq_map_range, Multiset.map_nsmul,
    Multiset.sum_nsmul, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

theorem finsum_rootsOfUnity_pow_mul_star {K : Type} [Field K] (θ : K →* ℂ) {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hω : IsPrimitiveRoot (θ ζ) N) (k l : ℕ) :
    ∑ᶠ α ∈ {α : K | α ^ N = 1}, θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD N] then ((N : ℕ) : ℂ) else 0 := by
  classical
  set ω := θ ζ with hωdef
  have hNe : N ≠ 0 := hN.ne'
  have : NeZero N := ⟨hNe⟩

  have hset : {α : K | α ^ N = 1} = (fun i : ℕ => ζ ^ i) '' (↑(Finset.range N) : Set ℕ) := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one h
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hζ.pow_inj hi hj h
  rw [hset, finsum_mem_image hinj, finsum_mem_coe_finset]
  have hnorm : ‖ω‖ = 1 := hω.norm'_eq_one hNe
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hstar : star ω = ω⁻¹ := by
    rw [Complex.inv_eq_conj hnorm]
    rfl

  set u := ω ^ k * (ω ^ l)⁻¹ with hu
  have hterm : ∀ i, θ (ζ ^ i) ^ k * star (θ (ζ ^ i) ^ l) = u ^ i := by
    intro i
    rw [map_pow, star_pow, star_pow, hstar, hu]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hm : ∀ a, ω ^ a = ω ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  have huN : u ^ N = 1 := by
    rw [hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
      hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  split_ifs with hkl
  · have hu1 : u = 1 := by
      rw [hu, hm k, hm l, show k % N = l % N from hkl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hω0)
    simp [hu1]
  · have hu1 : u ≠ 1 := by
      intro h
      have hkl' : ω ^ k = ω ^ l := (mul_inv_eq_one₀ (pow_ne_zero _ hω0)).mp (hu ▸ h)
      apply hkl
      exact hω.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [← hm, ← hm]; exact hkl')
    rw [geom_sum_eq hu1, huN, sub_self, zero_div]

/-- Lifted characters on the degree-`n` finite-field torus are orthogonal modulo its order. -/
theorem torus_orthogonality (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (n : ℕ) (hn : 0 < n) :
    (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧
      IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧
    ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
        θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqF : ((Nat.card F : ℕ) : F) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  set q := Nat.card F with hqdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  set N := q ^ n - 1 with hNdef
  have hN : 0 < N := by omega

  have hNF : (N : F) ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : F) = 0 := by
      rw [show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']
    rw [Nat.cast_add, h, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1
  letI : NeZero (N : F) := ⟨hNF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hω : IsPrimitiveRoot (θ ζ) N :=
    ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl =>
      hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩
  exact ⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩

end GlobalTheory.CuspGL
