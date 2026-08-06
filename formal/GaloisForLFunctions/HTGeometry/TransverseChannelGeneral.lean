import GaloisForLFunctions.HTGeometry.PadeHankelObstruction

/-!
# The transverse channel at any nonsingular longitudinal jet

Section 5 of the critical-multiplicity card was first formalized at one explicit longitudinal jet,
the unipotent `1 + t^m`.  The nonsingular locus is now known exactly — it is the complement of the
Padé–Hankel hypersurface — so the whole argument runs at every jet in it.

A transverse channel over such a jet is uniquely liftable, and any number of them multiply the
count of compatible sources by one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- **The transverse system is bijective at every jet off the Padé–Hankel hypersurface.** -/
theorem bijective_transverseDifferential_of_det {p : K[X]} (hdet : (padeHankel p m n).det ≠ 0) :
    Function.Bijective (transverseDifferential p m n (m + n)) := by
  have hdim : Module.finrank K (fibreTangentSpace K m n)
      = Module.finrank K (degreeLT K (m + n)) := by
    rw [Module.finrank_prod, finrank_degreeLT, finrank_degreeLT, finrank_degreeLT]
  have hinj := (injective_transverseDifferential_iff (m := m) (n := n) p).2 hdet
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

/-- **Every transverse observation over a nonsingular jet has exactly one lift.** -/
theorem exists_unique_transverse_of_det {p : K[X]} (hdet : (padeHankel p m n).det ≠ 0)
    (U V : K[X]) :
    ∃! q : K[X] × K[X], (q.1.degree < (m : ℕ) ∧ q.2.degree < (n : ℕ)) ∧
      (X : K[X]) ^ (m + n) ∣ ((q.1 + U) - p * (q.2 + V)) := by
  set L : ℕ := m + n with hLdef
  have hkey : ∀ q : fibreTangentSpace K m n,
      (transverseDifferential p m n L q
          = -(⟨(U - p * V) %ₘ X ^ L, by
              rw [mem_degreeLT]
              have hlt := degree_modByMonic_lt (U - p * V) (monic_X_pow (R := K) L)
              rwa [degree_X_pow] at hlt⟩ : degreeLT K L))
        ↔ (X : K[X]) ^ L ∣ (((q.1 : K[X]) + U) - p * ((q.2 : K[X]) + V)) := by
    intro q
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := K) L)]
    rw [show ((q.1 : K[X]) + U) - p * ((q.2 : K[X]) + V)
        = ((q.1 : K[X]) - p * (q.2 : K[X])) + (U - p * V) by ring,
      Polynomial.add_modByMonic, add_eq_zero_iff_eq_neg]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  obtain ⟨hinj, hsurj⟩ := bijective_transverseDifferential_of_det hdet
  obtain ⟨q, hq⟩ := hsurj _
  refine ⟨((q.1 : K[X]), (q.2 : K[X])), ⟨⟨mem_degreeLT.1 q.1.2, mem_degreeLT.1 q.2.2⟩,
    (hkey q).1 hq⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hdvd⟩
  have hq' : transverseDifferential p m n L (⟨a, mem_degreeLT.2 ha⟩, ⟨b, mem_degreeLT.2 hb⟩) = _ :=
    (hkey (⟨a, mem_degreeLT.2 ha⟩, ⟨b, mem_degreeLT.2 hb⟩)).2 hdvd
  have hqq := hinj (hq'.trans hq.symm)
  exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst hqq))
    (congrArg Subtype.val (congrArg Prod.snd hqq))

/-- **A transverse channel over a nonsingular jet contributes exactly one point.** -/
theorem nat_card_transverseFibre_of_det {p : K[X]} (hdet : (padeHankel p m n).det ≠ 0)
    (U V : K[X]) :
    Nat.card (transverseFibre K m n p U V) = 1 := by
  obtain ⟨q, hq, huniq⟩ := exists_unique_transverse_of_det hdet U V
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => ?_⟩, ⟨⟨q, hq.1.1, hq.1.2, hq.2⟩⟩⟩
  exact Subtype.ext ((huniq a.1 ⟨⟨a.2.1, a.2.2.1⟩, a.2.2.2⟩).trans
    (huniq b.1 ⟨⟨b.2.1, b.2.2.1⟩, b.2.2.2⟩).symm)

/-- **The critical multiplicity is stable under any number of transverse channels over nonsingular
longitudinal jets.** -/
theorem nat_card_criticalFibre_prod_transverse_channels_of_det [IsAlgClosed K] {d : ℕ}
    (hm : 0 < m) (hn : 0 < n) {U V : K[X]}
    (hU : U.degree ≤ (m : ℕ)) (hV : V.degree ≤ (n : ℕ)) (hUm : U.coeff m ≠ 0)
    (hVn : V.coeff n ≠ 0) (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hsep : (1 + U * V).Separable) (P : Fin d → K[X])
    (hdet : ∀ i, (padeHankel (P i) m n).det ≠ 0) (U' V' : Fin d → K[X]) :
    Nat.card (criticalFibre K m n U V ×
        ∀ i : Fin d, transverseFibre K m n (P i) (U' i) (V' i))
      = criticalHorizonMultiplicity m n := by
  rw [Nat.card_prod, Nat.card_pi,
    Finset.prod_congr rfl (fun i _ => nat_card_transverseFibre_of_det (hdet i) (U' i) (V' i)),
    Finset.prod_const_one, mul_one,
    nat_card_criticalFibre_criticalTails hm hn hU hV hUm hVn hU0 hV0 hsep]


/-! ## The determinant at the unipotent jet -/

/-- The Padé–Hankel entries of the unipotent jet. -/
theorem padeHankel_one_add_X_pow_apply (r j : Fin n) :
    padeHankel ((1 : K[X]) + X ^ m) m n r j
      = (if m + (r : ℕ) = (j : ℕ) then 1 else 0) + (if (r : ℕ) = (j : ℕ) then 1 else 0) := by
  rw [padeHankel_apply, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    ← pow_add, Polynomial.coeff_X_pow]
  congr 1
  by_cases h : (r : ℕ) = (j : ℕ)
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- **The transverse convolution determinant at the unipotent jet is one.**  The matrix is the
identity plus a strictly upper triangular part, so the nonsingular locus of section 5 is inhabited
with the determinant taking its simplest possible value. -/
theorem det_padeHankel_one_add_X_pow (hm : 0 < m) :
    (padeHankel ((1 : K[X]) + X ^ m) m n).det = 1 := by
  have htri : (padeHankel ((1 : K[X]) + X ^ m) m n).BlockTriangular id := by
    intro r j hlt
    rw [padeHankel_one_add_X_pow_apply]
    have hjr : (j : ℕ) < (r : ℕ) := hlt
    rw [if_neg (by omega), if_neg (by omega), add_zero]
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_eq_one fun r _ => ?_
  rw [padeHankel_one_add_X_pow_apply, if_neg (by omega), if_pos rfl, zero_add]

/-- **The unipotent jet lies in the nonsingular locus.** -/
theorem det_padeHankel_one_add_X_pow_ne_zero (hm : 0 < m) :
    (padeHankel ((1 : K[X]) + X ^ m) m n).det ≠ 0 := by
  rw [det_padeHankel_one_add_X_pow hm]
  exact one_ne_zero

end GaloisForLFunctions.HTGeometry
