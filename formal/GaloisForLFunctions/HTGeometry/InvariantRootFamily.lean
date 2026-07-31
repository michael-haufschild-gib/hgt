import GaloisForLFunctions.HTGeometry.SymmetricSumOverRoots

/-!
# Monic polynomials built from a rename-invariant family of root expressions

Let `ρ` index the complex roots of a monic integer polynomial.  Given a multiset `T` of integer
polynomial expressions in those roots whose multiset is invariant under renaming the roots, the
monic polynomial `∏_{q ∈ T} (X − q(ρ))` has integer coefficients: each coefficient is, up to sign,
an elementary symmetric function of `T`, which is rename-invariant and therefore an integer by
`aeval_isInt_of_isSymmetric`.

This is the construction step of the Lindemann–Weierstrass argument, where `T` runs over the subset
sums of a fixed size of the conjugates.

* `esymm_map_ringHom` — a ring homomorphism commutes with the elementary symmetric functions.
* `isSymmetric_esymm_of_invariant` — an invariant multiset has symmetric elementary symmetric
  functions.
* `coeff_prod_X_sub_C_isInt` — the coefficients are integers.
* `exists_monic_int_map_eq_prod` — hence the product is the image of a monic integer polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Finset

/-- A ring homomorphism commutes with the elementary symmetric functions of a multiset. -/
theorem esymm_map_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Multiset R) (j : ℕ) : f (T.esymm j) = (T.map f).esymm j := by
  rw [Multiset.esymm, Multiset.esymm, map_multiset_sum, Multiset.map_map,
    Multiset.powersetCard_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => ?_)
  simp [Function.comp, map_multiset_prod]

/-- The elementary symmetric functions of a rename-invariant multiset are symmetric. -/
theorem isSymmetric_esymm_of_invariant {n : ℕ} (T : Multiset (MvPolynomial (Fin n) ℤ))
    (hT : ∀ e : Equiv.Perm (Fin n), T.map (MvPolynomial.rename e) = T) (j : ℕ) :
    (T.esymm j).IsSymmetric := by
  intro e
  rw [show (MvPolynomial.rename e : MvPolynomial (Fin n) ℤ → MvPolynomial (Fin n) ℤ)
      = ((MvPolynomial.rename e : MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ) :
        MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ) from rfl]
  rw [esymm_map_ringHom]
  rw [show Multiset.map
      ((MvPolynomial.rename e : MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ) :
        MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℤ) T
      = T.map (MvPolynomial.rename e) from rfl]
  rw [hT e]

/-- **The coefficients of the monic polynomial with a rename-invariant root family are integers.** -/
theorem coeff_prod_X_sub_C_isInt {m : ℤ[X]} (hm : m.Monic) {n : ℕ} (hn : m.natDegree = n)
    {ρ : Fin n → ℂ} (hρ : m.aroots ℂ = Multiset.map ρ (Finset.univ : Finset (Fin n)).val)
    (T : Multiset (MvPolynomial (Fin n) ℤ))
    (hT : ∀ e : Equiv.Perm (Fin n), T.map (MvPolynomial.rename e) = T) (k : ℕ) :
    ∃ z : ℤ, MvPolynomial.aeval ρ
      ((T.map (fun q => (Polynomial.X - Polynomial.C q))).prod.coeff k) = (z : ℂ) := by
  classical
  by_cases hk : k ≤ Multiset.card T
  · rw [Multiset.prod_X_sub_C_coeff T hk]
    have hsym : (((-1 : MvPolynomial (Fin n) ℤ) ^ (Multiset.card T - k))
        * T.esymm (Multiset.card T - k)).IsSymmetric := by
      intro e
      rw [map_mul, map_pow, map_neg, map_one,
        isSymmetric_esymm_of_invariant T hT (Multiset.card T - k) e]
    exact aeval_isInt_of_isSymmetric hm hn hρ hsym
  · refine ⟨0, ?_⟩
    have hmonic : ∀ q ∈ T.map (fun q => (Polynomial.X - Polynomial.C q)),
        Polynomial.Monic q := by
      intro q hq
      rw [Multiset.mem_map] at hq
      obtain ⟨a, -, rfl⟩ := hq
      exact Polynomial.monic_X_sub_C a
    have hdeg : (T.map (fun q => (Polynomial.X - Polynomial.C q))).prod.natDegree
        = Multiset.card T := by
      rw [Polynomial.natDegree_multiset_prod_of_monic _ hmonic, Multiset.map_map]
      simp
    have hzero : (T.map (fun q => (Polynomial.X - Polynomial.C q))).prod.coeff k = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      omega
    rw [hzero]
    simp

/-- **The monic polynomial with a rename-invariant root family is defined over the integers.** -/
theorem exists_monic_int_map_eq_prod {m : ℤ[X]} (hm : m.Monic) {n : ℕ} (hn : m.natDegree = n)
    {ρ : Fin n → ℂ} (hρ : m.aroots ℂ = Multiset.map ρ (Finset.univ : Finset (Fin n)).val)
    (T : Multiset (MvPolynomial (Fin n) ℤ))
    (hT : ∀ e : Equiv.Perm (Fin n), T.map (MvPolynomial.rename e) = T) :
    ∃ F : ℤ[X], F.Monic ∧ F.natDegree = Multiset.card T ∧
      F.map (algebraMap ℤ ℂ)
        = (T.map (fun q => Polynomial.X - Polynomial.C (MvPolynomial.aeval ρ q))).prod := by
  classical
  set d := Multiset.card T with hd
  set P : (MvPolynomial (Fin n) ℤ)[X] :=
    (T.map (fun q => (Polynomial.X - Polynomial.C q))).prod with hP
  have hmonicfactors : ∀ q ∈ T.map (fun q => (Polynomial.X - Polynomial.C q)),
      Polynomial.Monic q := by
    intro q hq
    rw [Multiset.mem_map] at hq
    obtain ⟨a, -, rfl⟩ := hq
    exact Polynomial.monic_X_sub_C a
  have hPmonic : P.Monic :=
    monic_multiset_prod_of_monic T (fun q => (Polynomial.X - Polynomial.C q))
      (fun i _ => monic_X_sub_C i)
  have hPdeg : P.natDegree = d := by
    rw [hP, Polynomial.natDegree_multiset_prod_of_monic _ hmonicfactors, Multiset.map_map, hd]
    simp
  choose z hz using coeff_prod_X_sub_C_isInt hm hn hρ T hT
  -- the map of `P` to `ℂ` is the target product
  have hPmap : P.map ((MvPolynomial.aeval ρ : MvPolynomial (Fin n) ℤ →ₐ[ℤ] ℂ) :
        MvPolynomial (Fin n) ℤ →+* ℂ)
      = (T.map (fun q => Polynomial.X - Polynomial.C (MvPolynomial.aeval ρ q))).prod := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun q _ => ?_)
    simp [Function.comp]
  -- the integer polynomial
  set Fp : ℤ[X] := ∑ k ∈ Finset.range (d + 1), Polynomial.monomial k (z k) with hFp
  have hzzero : ∀ j, d < j → z j = 0 := by
    intro j hj
    have hc : P.coeff j = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [hPdeg]; exact hj
    have := hz j
    rw [hc, map_zero] at this
    exact_mod_cast this.symm
  have hcoeff : ∀ j, Fp.coeff j = z j := by
    intro j
    rw [hFp, Polynomial.finsetSum_coeff]
    rw [Finset.sum_congr rfl fun k _ => Polynomial.coeff_monomial (n := k) (m := j) (a := z k)]
    rw [Finset.sum_ite_eq' (Finset.range (d + 1)) j z]
    by_cases hj : j ∈ Finset.range (d + 1)
    · rw [if_pos hj]
    · rw [if_neg hj]
      rw [Finset.mem_range] at hj
      exact (hzzero j (by omega)).symm
  have hzd : z d = 1 := by
    have hc : P.coeff d = 1 := by
      have := hPmonic
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hPdeg] at this
      exact this
    have := hz d
    rw [hc, map_one] at this
    exact_mod_cast this.symm
  have hdegle : Fp.natDegree ≤ d := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
    rw [hcoeff j]
    exact hzzero j (by exact_mod_cast hj)
  have hdegeq : Fp.natDegree = d := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegle ?_
    rw [hcoeff d, hzd]
    exact one_ne_zero
  refine ⟨Fp, ?_, hdegeq, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hdegeq, hcoeff d, hzd]
  · rw [← hPmap]
    refine Polynomial.ext fun j => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hcoeff j, RingHom.coe_coe, hz j]
    simp

end GaloisForLFunctions.HTGeometry
