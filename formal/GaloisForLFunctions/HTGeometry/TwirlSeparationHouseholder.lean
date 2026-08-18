import GaloisForLFunctions.HTGeometry.ReplicaContentPermutation
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Monomial separation and Householder transitivity

A coefficient family on ordered replica coordinates assembles into a multivariate polynomial whose
monomials are the contents.  If the pairing of that family with every positive pure tensor vanishes,
the polynomial vanishes on a box with infinite sides, hence identically, so every content-class sum
of the family vanishes.

A Householder reflection built from the difference of a basis vector and a real unit vector is a
self-adjoint involution, hence unitary, and carries the basis vector to that unit vector.  So the
unitary group acts transitively on the real unit vectors.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Separation

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The monomial exponent of an ordered replica coordinate. -/
def replicaExponent (r : ℕ) (x : Fin r → α) : α →₀ ℕ :=
  Multiset.toFinsupp ((symTupleIndex r x : Sym α r) : Multiset α)

theorem replicaExponent_eq_iff (r : ℕ) (x y : Fin r → α) :
    replicaExponent r x = replicaExponent r y ↔ symTupleIndex r x = symTupleIndex r y := by
  constructor
  · intro h
    exact Sym.coe_injective (Multiset.toFinsupp.injective h)
  · intro h
    exact congrArg Multiset.toFinsupp (congrArg Sym.toMultiset h)

/-- Evaluating the monomial of a replica coordinate is the pure replica tensor. -/
theorem finsuppProd_replicaExponent (r : ℕ) (x : Fin r → α) (t : α → ℂ) :
    ((replicaExponent r x).prod fun a e => t a ^ e) = finitePureTensorPower r t x := by
  classical
  rw [replicaExponent, Finsupp.prod, Multiset.toFinsupp_support]
  have hcount : ∀ a : α, (Multiset.toFinsupp
      ((symTupleIndex r x : Sym α r) : Multiset α)) a
      = Multiset.count a ((symTupleIndex r x : Sym α r) : Multiset α) := fun a => rfl
  rw [Finset.prod_congr rfl fun a _ => by rw [hcount a]]
  rw [← Finset.prod_multiset_map_count]
  show (Multiset.map t ((List.ofFn x : List α) : Multiset α)).prod = _
  rw [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  rfl

/-- **Monomial separation.**  If the pairing of a coefficient family with every strictly positive
pure replica tensor vanishes, then every content-class sum of the family vanishes. -/
theorem sum_symClass_eq_zero_of_forall_pos (r : ℕ) (c : (Fin r → α) → ℂ)
    (h : ∀ t : α → ℝ, (∀ a, 0 < t a) →
      (∑ x, c x * finitePureTensorPower r (fun a => (t a : ℂ)) x) = 0)
    (x0 : Fin r → α) :
    (∑ x ∈ symClass r x0, c x) = 0 := by
  classical
  set P : MvPolynomial α ℂ := ∑ x, MvPolynomial.monomial (replicaExponent r x) (c x) with hPdef
  have hbox : ∀ _a : α, (((fun u : ℝ => (u : ℂ)) '' Set.Ioi 0)).Infinite := by
    intro _a
    refine (Set.Ioi_infinite (0 : ℝ)).image ?_
    intro u _ v _ huv
    exact Complex.ofReal_injective (by simpa using huv)
  have hzero : P = 0 := by
    refine MvPolynomial.funext_set (p := P) (q := 0)
      (fun _ : α => ((fun u : ℝ => (u : ℂ)) '' Set.Ioi 0)) hbox ?_
    intro psi hpsi
    have hmem : ∀ a : α, psi a ∈ ((fun u : ℝ => (u : ℂ)) '' Set.Ioi (0 : ℝ)) := by
      intro a
      exact hpsi a (Set.mem_univ a)
    have hre : ∀ a : α, ((psi a).re : ℂ) = psi a ∧ 0 < (psi a).re := by
      intro a
      obtain ⟨u, hu, huv⟩ := hmem a
      refine ⟨?_, ?_⟩
      · rw [← huv]
        simp
      · rw [← huv]
        simpa using hu
    have hpsi_eq : (fun a => (((psi a).re : ℝ) : ℂ)) = psi := by
      funext a
      exact (hre a).1
    rw [map_zero, hPdef, map_sum]
    have hev : ∀ x : Fin r → α,
        MvPolynomial.eval psi (MvPolynomial.monomial (replicaExponent r x) (c x))
          = c x * finitePureTensorPower r (fun a => (((psi a).re : ℝ) : ℂ)) x := by
      intro x
      rw [MvPolynomial.eval_monomial, hpsi_eq, finsuppProd_replicaExponent]
    rw [Finset.sum_congr rfl fun x _ => hev x]
    exact h (fun a => (psi a).re) fun a => (hre a).2
  have hcoeff := congrArg (MvPolynomial.coeff (replicaExponent r x0)) hzero
  rw [hPdef, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  have hterm : ∀ x : Fin r → α,
      MvPolynomial.coeff (replicaExponent r x0)
        (MvPolynomial.monomial (replicaExponent r x) (c x))
        = if replicaExponent r x = replicaExponent r x0 then c x else 0 := by
    intro x
    rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_filter] at hcoeff
  have hset : (Finset.univ.filter fun x : Fin r → α =>
      replicaExponent r x = replicaExponent r x0) = symClass r x0 := by
    ext z
    simp [symClass, replicaExponent_eq_iff]
  rwa [hset] at hcoeff

end Separation

section Householder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Transitivity on real unit vectors.**  A Householder reflection is a self-adjoint involution
carrying a basis vector to any prescribed real unit vector. -/
theorem exists_unitary_mulVec_basis (t : α → ℝ)
    (hunit : ∑ a, t a ^ 2 = 1) (a0 : α) :
    ∃ A : Matrix α α ℂ, Aᴴ * A = 1 ∧
      A.mulVec (fun a => if a = a0 then (1 : ℂ) else 0) = fun a => (t a : ℂ) := by
  classical
  by_cases h1 : t a0 = 1
  · have hzero : ∀ a, a ≠ a0 → t a = 0 := by
      intro a hne
      have hsplit : t a0 ^ 2 + ∑ b ∈ Finset.univ.erase a0, t b ^ 2 = 1 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a0)] at hunit
        linarith [hunit]
      have hnnsum : 0 ≤ ∑ b ∈ Finset.univ.erase a0, t b ^ 2 :=
        Finset.sum_nonneg fun b _ => sq_nonneg _
      have hsum0 : ∑ b ∈ Finset.univ.erase a0, t b ^ 2 = 0 := by
        rw [h1] at hsplit
        linarith
      have hmem : a ∈ Finset.univ.erase a0 := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ a⟩
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg (t b))).mp hsum0 a hmem
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    refine ⟨1, by simp, ?_⟩
    funext a
    rw [Matrix.one_mulVec]
    by_cases ha : a = a0
    · subst ha
      rw [if_pos rfl, h1]
      norm_num
    · rw [if_neg ha, hzero a ha]
      norm_num
  · have hle : t a0 ≤ 1 := by
      nlinarith [Finset.single_le_sum (f := fun a => t a ^ 2)
        (fun a _ => sq_nonneg (t a)) (Finset.mem_univ a0), hunit, sq_nonneg (t a0 - 1)]
    have hlt : t a0 < 1 := lt_of_le_of_ne hle h1
    set v : α → ℝ := fun a => (if a = a0 then (1 : ℝ) else 0) - t a with hv
    set n : ℝ := 2 - 2 * t a0 with hn
    have hnpos : 0 < n := by rw [hn]; linarith
    have hvsq : ∑ a, v a ^ 2 = n := by
      have hexp : ∀ a : α, v a ^ 2 =
          (if a = a0 then (1 : ℝ) else 0) - 2 * (if a = a0 then (1 : ℝ) else 0) * t a
            + t a ^ 2 := by
        intro a
        have hva : v a = (if a = a0 then (1 : ℝ) else 0) - t a := rfl
        rw [hva]
        by_cases ha : a = a0
        · rw [if_pos ha]
          ring
        · rw [if_neg ha]
          ring
      rw [Finset.sum_congr rfl fun a _ => hexp a, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        hunit]
      have h1' : (∑ a : α, if a = a0 then (1 : ℝ) else 0) = 1 := by simp
      have h2' : (∑ a : α, 2 * (if a = a0 then (1 : ℝ) else 0) * t a) = 2 * t a0 := by
        rw [Finset.sum_congr rfl fun a _ => (by by_cases ha : a = a0 <;> simp [ha] :
          2 * (if a = a0 then (1 : ℝ) else 0) * t a = if a = a0 then 2 * t a else 0)]
        simp
      rw [h1', h2', hn]
      ring
    set k : ℝ := 2 / n with hk
    set Hr : Matrix α α ℝ := Matrix.of fun x y =>
      (if x = y then (1 : ℝ) else 0) - k * v x * v y with hHr
    set H : Matrix α α ℂ := Hr.map (fun u : ℝ => (u : ℂ)) with hH
    have hHsymm : ∀ x y : α, Hr x y = Hr y x := by
      intro x y
      rw [hHr]
      simp only [Matrix.of_apply]
      by_cases hxy : x = y
      · subst hxy
        ring
      · rw [if_neg hxy, if_neg fun hh => hxy hh.symm]
        ring
    have hHerm : Hᴴ = H := by
      funext x y
      rw [hH, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, RCLike.star_def,
        Complex.conj_ofReal, hHsymm]
    have hHentry : ∀ x y : α, H x y
        = (if x = y then (1 : ℂ) else 0) - (k : ℂ) * (v x : ℂ) * (v y : ℂ) := by
      intro x y
      rw [hH, Matrix.map_apply, hHr]
      simp only [Matrix.of_apply]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos hxy]
        push_cast
        ring
      · rw [if_neg hxy, if_neg hxy]
        push_cast
        ring
    have hsumv : (∑ a : α, (v a : ℂ) ^ 2) = ((n : ℝ) : ℂ) := by
      have hcast : ((∑ a, v a ^ 2 : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by rw [hvsq]
      rw [← hcast]
      push_cast
      ring
    have hknR : k * k * n = 2 * k := by
      rw [hk]
      field_simp
    have hkn : (k : ℂ) * (k : ℂ) * ((n : ℝ) : ℂ) = 2 * (k : ℂ) := by
      exact_mod_cast congrArg (fun u : ℝ => (u : ℂ)) hknR
    have hHH : H * H = 1 := by
      funext x y
      rw [Matrix.mul_apply, Matrix.one_apply]
      have hterm : ∀ z : α, H x z * H z y
          = (if x = z then (1 : ℂ) else 0) * (if z = y then (1 : ℂ) else 0)
            - (if x = z then (1 : ℂ) else 0) * ((k : ℂ) * (v z : ℂ) * (v y : ℂ))
            - ((k : ℂ) * (v x : ℂ) * (v z : ℂ)) * (if z = y then (1 : ℂ) else 0)
            + ((k : ℂ) * (k : ℂ) * (v x : ℂ) * (v y : ℂ)) * (v z : ℂ) ^ 2 := by
        intro z
        rw [hHentry, hHentry]
        ring
      have hs1 : (∑ z : α, (if x = z then (1 : ℂ) else 0) * (if z = y then (1 : ℂ) else 0))
          = if x = y then (1 : ℂ) else 0 := by
        have hstep : ∀ z : α, (if x = z then (1 : ℂ) else 0) * (if z = y then (1 : ℂ) else 0)
            = if x = z then (if z = y then (1 : ℂ) else 0) else 0 := by
          intro z
          by_cases h : x = z <;> simp [h]
        rw [Finset.sum_congr rfl fun z _ => hstep z,
          Finset.sum_ite_eq Finset.univ x (fun z => if z = y then (1 : ℂ) else 0)]
        simp
      have hs2 : (∑ z : α, (if x = z then (1 : ℂ) else 0) * ((k : ℂ) * (v z : ℂ) * (v y : ℂ)))
          = (k : ℂ) * (v x : ℂ) * (v y : ℂ) := by
        have hstep : ∀ z : α, (if x = z then (1 : ℂ) else 0) * ((k : ℂ) * (v z : ℂ) * (v y : ℂ))
            = if x = z then (k : ℂ) * (v z : ℂ) * (v y : ℂ) else 0 := by
          intro z
          by_cases h : x = z <;> simp [h]
        rw [Finset.sum_congr rfl fun z _ => hstep z,
          Finset.sum_ite_eq Finset.univ x (fun z => (k : ℂ) * (v z : ℂ) * (v y : ℂ))]
        simp
      have hs3 : (∑ z : α, ((k : ℂ) * (v x : ℂ) * (v z : ℂ)) * (if z = y then (1 : ℂ) else 0))
          = (k : ℂ) * (v x : ℂ) * (v y : ℂ) := by
        have hstep : ∀ z : α, ((k : ℂ) * (v x : ℂ) * (v z : ℂ)) * (if z = y then (1 : ℂ) else 0)
            = if z = y then (k : ℂ) * (v x : ℂ) * (v z : ℂ) else 0 := by
          intro z
          by_cases h : z = y <;> simp [h]
        rw [Finset.sum_congr rfl fun z _ => hstep z,
          Finset.sum_ite_eq' Finset.univ y (fun z => (k : ℂ) * (v x : ℂ) * (v z : ℂ))]
        simp
      have hs4 : (∑ z : α, ((k : ℂ) * (k : ℂ) * (v x : ℂ) * (v y : ℂ)) * (v z : ℂ) ^ 2)
          = ((k : ℂ) * (k : ℂ) * (v x : ℂ) * (v y : ℂ)) * ((n : ℝ) : ℂ) := by
        rw [← Finset.mul_sum, hsumv]
      rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs1, hs2, hs3, hs4]
      linear_combination ((v x : ℂ) * (v y : ℂ)) * hkn
    refine ⟨H, by rw [hHerm]; exact hHH, ?_⟩
    funext x
    rw [Matrix.mulVec, dotProduct]
    have hterm : ∀ y : α, H x y * (if y = a0 then (1 : ℂ) else 0)
        = if y = a0 then H x a0 else 0 := by
      intro y
      by_cases hy : y = a0
      · subst hy
        rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg hy, if_neg hy, mul_zero]
    rw [Finset.sum_congr rfl fun y _ => hterm y,
      Finset.sum_ite_eq' Finset.univ a0 (fun _ => H x a0)]
    simp only [Finset.mem_univ, if_true]
    rw [hHentry]
    have hva0 : v a0 = n / 2 := by
      have hv0 : v a0 = 1 - t a0 := by
        rw [hv]
        simp
      rw [hv0, hn]
      ring
    have hkvR : k * v a0 = 1 := by
      rw [hva0, hk]
      field_simp
    have hkv : (k : ℂ) * (v a0 : ℂ) = 1 := by
      exact_mod_cast congrArg (fun u : ℝ => (u : ℂ)) hkvR
    have hvx : (v x : ℂ) = (if x = a0 then (1 : ℂ) else 0) - (t x : ℂ) := by
      have hvxR : v x = (if x = a0 then (1 : ℝ) else 0) - t x := rfl
      rw [hvxR]
      by_cases hx : x = a0
      · rw [if_pos hx, if_pos hx]
        push_cast
        ring
      · rw [if_neg hx, if_neg hx]
        push_cast
        ring
    calc (if x = a0 then (1 : ℂ) else 0) - (k : ℂ) * (v x : ℂ) * (v a0 : ℂ)
        = (if x = a0 then (1 : ℂ) else 0) - ((k : ℂ) * (v a0 : ℂ)) * (v x : ℂ) := by ring
      _ = (if x = a0 then (1 : ℂ) else 0) - (v x : ℂ) := by rw [hkv, one_mul]
      _ = (t x : ℂ) := by rw [hvx]; ring

end Householder

end

end GaloisForLFunctions.HTGeometry
