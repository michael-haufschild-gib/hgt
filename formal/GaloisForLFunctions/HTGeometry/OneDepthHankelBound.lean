import GaloisForLFunctions.HTGeometry.PadeHankelObstruction
import GaloisForLFunctions.HTGeometry.LinearPartialFractions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The sharp fibre bound at depth one, for an arbitrary observed packet

At depth one the unknown jet is a single scalar, so the Padé–Hankel obstruction between two fibre
points becomes a pencil: fixing one fibre point, every other one is a zero of the determinant of a
matrix pencil in that scalar.  The pencil's leading matrix is the Hankel matrix of the fixed jet,
and that matrix is invertible whenever the observed reciprocal packet does not vanish at its depth —
otherwise the fixed jet's own reciprocal would already be short.

So the determinant is a nonzero polynomial of degree the second depth, and the fibre has at most one
more point than that: exactly the critical binomial multiplicity.  Unlike the exact count, this
needs no separability, no algebraically closed field, and no restriction on the observed packets.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-! ## The Hankel matrix of a pencil of jets -/

section Pencil

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- **The Hankel matrix is linear in the jet.** -/
theorem padeHankel_C_mul_add (a : R) (P W : R[X]) :
    padeHankel (C a * P + W) m n = a • padeHankel P m n + padeHankel W m n := by
  ext r j
  simp only [padeHankel, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_add, Polynomial.coeff_add]
  congr 1
  rw [show (X : R[X]) ^ (j : ℕ) * (C a * P) = C a * ((X : R[X]) ^ (j : ℕ) * P) by ring,
    Polynomial.coeff_C_mul]

end Pencil

/-! ## The determinant of a pencil is a polynomial of the size of the matrix -/

section Determinant

variable {K : Type*} [Field K] {n : ℕ}

/-- **The determinant of a pencil with invertible leading matrix is a characteristic
polynomial.** -/
theorem det_pencil_eq_charpoly (H₁ H₀ : Matrix (Fin n) (Fin n) K) (hH : H₁.det ≠ 0) (a : K) :
    (a • H₁ + H₀).det = H₁.det * (Matrix.charpoly (-(H₁⁻¹ * H₀))).eval a := by
  have hunit : IsUnit H₁.det := isUnit_iff_ne_zero.2 hH
  have hscalar : (Matrix.scalar (Fin n) a) = a • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hfac : a • H₁ + H₀ = H₁ * (Matrix.scalar (Fin n) a - -(H₁⁻¹ * H₀)) := by
    rw [hscalar, sub_neg_eq_add, Matrix.mul_add, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv H₁ hunit, Matrix.one_mul]
    congr 1
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [hfac, Matrix.det_mul, Matrix.eval_charpoly]

/-- **A pencil with invertible leading matrix has at most `n` degenerate members.** -/
theorem card_le_of_det_pencil_eq_zero (H₁ H₀ : Matrix (Fin n) (Fin n) K) (hH : H₁.det ≠ 0)
    (s : Finset K) (hs : ∀ a ∈ s, (a • H₁ + H₀).det = 0) : s.card ≤ n := by
  classical
  set f : K[X] := Matrix.charpoly (-(H₁⁻¹ * H₀)) with hf
  have hfmonic : f.Monic := Matrix.charpoly_monic _
  have hfdeg : f.natDegree = n := by
    rw [hf, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hroot : ∀ a ∈ s, f.IsRoot a := by
    intro a ha
    have := hs a ha
    rw [det_pencil_eq_charpoly H₁ H₀ hH a] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hH
    · exact h
  have hsub : s ⊆ f.roots.toFinset := by
    intro a ha
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hfmonic.ne_zero).2 (hroot a ha))
  calc s.card ≤ f.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = n := hfdeg

end Determinant

/-! ## The leading Hankel matrix of a fibre point -/

section Leading

variable {K : Type*} [Field K] {n : ℕ}

/-- **The Hankel matrix of the jet of a fibre point is invertible.**  A degeneracy would say that
the reciprocal of that jet already vanishes at the observed depth, contradicting the observation. -/
theorem det_padeHankel_fibre_ne_zero (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ 1 ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) (hVn : V.coeff n ≠ 0)
    (p : criticalFibre K 1 n U V) :
    (padeHankel (p.1.1 + U) 1 n).det ≠ 0 := by
  intro hdet
  obtain ⟨α, β, hβ0, hα, hβ, hdvd⟩ := (det_padeHankel_eq_zero_iff (m := 1) _).1 hdet
  have hfib : (X : K[X]) ^ (1 + n) ∣ ((p.1.1 + U) * (p.1.2 + V) - 1) :=
    (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hU hV _ _).1 p.2.2.2
  -- multiply the degeneracy by the reciprocal of the fibre point
  have hkey : (X : K[X]) ^ (1 + n) ∣ (α * (p.1.2 + V) - β) := by
    have hid : α * (p.1.2 + V) - β
        = (α - (p.1.1 + U) * β) * (p.1.2 + V) + ((p.1.1 + U) * (p.1.2 + V) - 1) * β := by
      ring
    rw [hid]
    exact dvd_add (Dvd.dvd.mul_right hdvd _) (Dvd.dvd.mul_right hfib _)
  have hcoeff : (α * (p.1.2 + V) - β).coeff n = 0 :=
    (Polynomial.X_pow_dvd_iff.1 hkey) n (by omega)
  have hαC : α = C (α.coeff 0) := eq_C_of_degree_lt_one (by exact_mod_cast hα)
  have hβn : β.coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hβ (le_refl _))
  have hpn : (p.1.2 + V).coeff n = V.coeff n := by
    rw [Polynomial.coeff_add, Polynomial.coeff_eq_zero_of_degree_lt p.2.2.1, zero_add]
  have hα0 : α.coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, hβn, sub_zero, hαC, Polynomial.coeff_C_mul, hpn] at hcoeff
    rcases mul_eq_zero.1 hcoeff with h | h
    · exact h
    · exact absurd h hVn
  have hαzero : α = 0 := by rw [hαC, hα0, map_zero]
  rw [hαzero, zero_sub, dvd_neg] at hdvd
  refine hβ0 ?_
  have hP0 : ((p.1.1 + U).coeff 0) ≠ 0 :=
    coeff_zero_add_ne_zero_of_dvd (by omega) hU0 hV0 p.2.2.2
  have hdvdβ : (X : K[X]) ^ (1 + n) ∣ β :=
    dvd_of_mul_dvd_of_coeff_zero_ne_zero hP0 hdvd
  refine Polynomial.eq_zero_of_dvd_of_degree_lt hdvdβ ?_
  rw [Polynomial.degree_X_pow]
  exact lt_of_lt_of_le hβ (by exact_mod_cast Nat.le_add_left n 1)

end Leading

/-! ## The bound -/

section Bound

variable {K : Type*} [Field K] {n : ℕ}

/-- **At depth one the fibre has at most the critical binomial multiplicity of points, for every
observed packet.**  Fixing one fibre point, the Padé–Hankel obstruction makes every other one a zero
of a pencil determinant whose leading matrix is invertible, so there are at most `n` of them. -/
theorem nat_card_criticalFibre_one_le_of_tail (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ 1 ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0) (hVn : V.coeff n ≠ 0) :
    Nat.card (criticalFibre K 1 n U V) ≤ criticalHorizonMultiplicity 1 n := by
  classical
  have hmult : criticalHorizonMultiplicity 1 n = n + 1 := by
    rw [criticalHorizonMultiplicity, Nat.choose_one_right]
    omega
  rw [hmult]
  rcases isEmpty_or_nonempty (criticalFibre K 1 n U V) with hempty | hne
  · rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  obtain ⟨p₀⟩ := hne
  have hH : (padeHankel (p₀.1.1 + U) 1 n).det ≠ 0 :=
    det_padeHankel_fibre_ne_zero hn hU hV hU0 hV0 hVn p₀
  set H₁ : Matrix (Fin n) (Fin n) K := padeHankel (p₀.1.1 + U) 1 n with hH₁
  set H₀ : Matrix (Fin n) (Fin n) K := padeHankel ((p₀.1.1 + U) * U) 1 n with hH₀
  set f : K[X] := Matrix.charpoly (-(H₁⁻¹ * H₀)) with hf
  have hfmonic : f.Monic := Matrix.charpoly_monic _
  set T : Finset K := insert (p₀.1.1.coeff 0) f.roots.toFinset with hT
  have hCp : ∀ p : criticalFibre K 1 n U V, p.1.1 = C (p.1.1.coeff 0) := fun p =>
    eq_C_of_degree_lt_one (by exact_mod_cast p.2.1)
  have hmem : ∀ p : criticalFibre K 1 n U V, p.1.1.coeff 0 ∈ T := by
    intro p
    rcases eq_or_ne p p₀ with rfl | hp
    · exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Multiset.mem_toFinset.2
        ((Polynomial.mem_roots hfmonic.ne_zero).2 ?_))
      have hprod := det_padeHankel_product_eq_zero (by omega) hn hU hV hU0 hV0 p₀ p (Ne.symm hp)
      have hrw : (p₀.1.1 + U) * (p.1.1 + U)
          = C (p.1.1.coeff 0) * (p₀.1.1 + U) + (p₀.1.1 + U) * U := by
        rw [← hCp p]
        ring
      rw [hrw, padeHankel_C_mul_add, ← hH₁, ← hH₀, det_pencil_eq_charpoly H₁ H₀ hH] at hprod
      rcases mul_eq_zero.1 hprod with h | h
      · exact absurd h hH
      · exact h
  have hinj : Function.Injective
      (fun p : criticalFibre K 1 n U V => (⟨p.1.1.coeff 0, hmem p⟩ : T)) := by
    intro p q hpq
    refine criticalFibre_fst_injective (by omega) hn hU0 hV0 ?_
    show p.1.1 = q.1.1
    rw [hCp p, hCp q]
    exact congrArg C (congrArg Subtype.val hpq)
  calc Nat.card (criticalFibre K 1 n U V) ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ n + 1 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        have hroots : f.roots.toFinset.card ≤ n := by
          calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
            _ ≤ f.natDegree := Polynomial.card_roots' f
            _ = n := by rw [hf, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        omega


/-- **A degenerate depth-one equation strictly loses jets.**  When the exactness criterion fails the
fibre has strictly fewer than the critical binomial multiplicity of points. -/
theorem nat_card_criticalFibre_one_lt_of_not [IsAlgClosed K] [DecidableEq K] (hn : 0 < n)
    {U V : K[X]} (hU0 : U.coeff 0 = 0) (hU : (X : K[X]) ^ 1 ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hV0 : V.coeff 0 = 0) (hVn : V.coeff n ≠ 0)
    (hbad : ¬ ((oneDeepEquation U (V.coeff n) n).Separable ∧
      ¬ (oneDeepEquation U (V.coeff n) n).IsRoot 0)) :
    Nat.card (criticalFibre K 1 n U V) < criticalHorizonMultiplicity 1 n := by
  have hle := nat_card_criticalFibre_one_le_of_tail hn hU hV hU0 hV0 hVn
  have hne : Nat.card (criticalFibre K 1 n U V) ≠ criticalHorizonMultiplicity 1 n := fun h =>
    hbad ((nat_card_criticalFibre_one_eq_iff hn hU0 hU hV hVn).1 h)
  omega

end Bound

end GaloisForLFunctions.HTGeometry
