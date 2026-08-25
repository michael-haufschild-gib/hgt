import GaloisForLFunctions.HTGeometry.CriticalObservationChartRing
import GaloisForLFunctions.HTGeometry.LocalizationTwoPrimeUnits
import GaloisForLFunctions.HTGeometry.LocalizationAwayRingEquiv

/-!
# The critical observation chart is a standard two-torus chart

The observation coordinates consist of two nonempty finite blocks.  Reindex them so that the
distinguished coordinate in each block is first, and then transport localization away from their
product.  This gives the exact coordinate-ring identification with `(G_m)^2 x A^(m+n-2)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

private theorem equivCast_fin_val {a b : ℕ} (h : a = b) (x : Fin a) :
    ((Equiv.cast (congrArg Fin h)) x).val = x.val := by
  subst h
  rfl

/-- Reindex the two observation-coordinate blocks with their marked coordinates first. -/
noncomputable def criticalObservationTorusIndexEquiv (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] :
    Fin n ⊕ Fin m ≃ Fin ((n + m - 2) + 2) := by
  have hm : 0 < m := Fact.out
  have hn : 0 < n := Fact.out
  have hnle : n < n + m := by omega
  have htotal : n + m = (n + m - 2) + 2 := by omega
  exact finSumFinEquiv.trans
    ((Equiv.swap (⟨n, hnle⟩ : Fin (n + m)) (⟨1, by omega⟩ : Fin (n + m))).trans
      (Equiv.cast (congrArg Fin htotal)))

theorem criticalObservationTorusIndexEquiv_inl_zero (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationTorusIndexEquiv m n (Sum.inl (⟨0, Fact.out⟩ : Fin n)) =
      (⟨0, by omega⟩ : Fin ((n + m - 2) + 2)) := by
  apply Fin.ext
  have hm : 0 < m := Fact.out
  have hn : 0 < n := Fact.out
  simp only [criticalObservationTorusIndexEquiv, Equiv.trans_apply,
    finSumFinEquiv_apply_left]
  rw [equivCast_fin_val, Equiv.swap_apply_def]
  have h0n : Fin.castAdd m (⟨0, hn⟩ : Fin n) ≠ (⟨n, by omega⟩ : Fin (n + m)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have h01 : Fin.castAdd m (⟨0, hn⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin (n + m)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  rw [if_neg h0n, if_neg h01]
  simp
  all_goals omega

theorem criticalObservationTorusIndexEquiv_inr_zero (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationTorusIndexEquiv m n (Sum.inr (⟨0, Fact.out⟩ : Fin m)) =
      (⟨1, by omega⟩ : Fin ((n + m - 2) + 2)) := by
  apply Fin.ext
  have hm : 0 < m := Fact.out
  have hn : 0 < n := Fact.out
  simp only [criticalObservationTorusIndexEquiv, Equiv.trans_apply,
    finSumFinEquiv_apply_right]
  rw [equivCast_fin_val]
  have hnat : Fin.natAdd n (⟨0, hm⟩ : Fin m) = (⟨n, by omega⟩ : Fin (n + m)) :=
    Fin.ext (by simp)
  rw [hnat, Equiv.swap_apply_left]
  all_goals omega

/-- Polynomial-coordinate equivalence underlying the chart identification. -/
noncomputable def criticalObservationPolynomialTorusEquiv
    (K : Type*) [Field K] (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationRing K m n ≃+*
      MvPolynomial (Fin ((n + m - 2) + 2)) K :=
  (MvPolynomial.renameEquiv K (criticalObservationTorusIndexEquiv m n)).toRingEquiv

theorem criticalObservationPolynomialTorusEquiv_marked
    (K : Type*) [Field K] (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationPolynomialTorusEquiv K m n
        (criticalObservationMarked K (m := m) (n := n)) =
      (X 0 * X 1 : MvPolynomial (Fin ((n + m - 2) + 2)) K) := by
  simp [criticalObservationPolynomialTorusEquiv, criticalObservationMarked,
    criticalObservationTorusIndexEquiv_inl_zero,
    criticalObservationTorusIndexEquiv_inr_zero]

/-- **The critical observation chart is the standard two-torus affine chart.** -/
noncomputable def criticalObservationChartTorusEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationChartRing K m n ≃+* TorusChart K (n + m - 2) :=
  awayRingEquiv (criticalObservationPolynomialTorusEquiv K m n)
    (criticalObservationPolynomialTorusEquiv_marked K m n)

theorem criticalObservationChartTorusEquiv_algebraMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)]
    (p : criticalObservationRing K m n) :
    criticalObservationChartTorusEquiv K m n
        (algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n) p) =
      algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
        (TorusChart K (n + m - 2))
        (criticalObservationPolynomialTorusEquiv K m n p) := by
  simpa [criticalObservationChartTorusEquiv] using
    awayRingEquiv_algebraMap
      (criticalObservationPolynomialTorusEquiv K m n)
      (criticalObservationPolynomialTorusEquiv_marked K m n) p

/-- The chart identification respects the ground-field algebra structures. -/
noncomputable def criticalObservationChartTorusAlgEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationChartRing K m n ≃ₐ[K] TorusChart K (n + m - 2) :=
  AlgEquiv.ofRingEquiv (f := criticalObservationChartTorusEquiv K m n) fun x => by
    change criticalObservationChartTorusEquiv K m n
        (algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n) (C x)) =
      algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
        (TorusChart K (n + m - 2)) (C x)
    rw [criticalObservationChartTorusEquiv_algebraMap]
    simp [criticalObservationPolynomialTorusEquiv]

theorem criticalObservationChartTorusEquiv_inl_zero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationChartTorusEquiv K m n
        (algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n)
          (X (Sum.inl (⟨0, Fact.out⟩ : Fin n)))) =
      algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
        (TorusChart K (n + m - 2)) (X 0) := by
  rw [criticalObservationChartTorusEquiv_algebraMap]
  congr 1
  simp [criticalObservationPolynomialTorusEquiv,
    criticalObservationTorusIndexEquiv_inl_zero]

theorem criticalObservationChartTorusEquiv_inr_zero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationChartTorusEquiv K m n
        (algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n)
          (X (Sum.inr (⟨0, Fact.out⟩ : Fin m)))) =
      algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
        (TorusChart K (n + m - 2)) (X 1) := by
  rw [criticalObservationChartTorusEquiv_algebraMap]
  congr 1
  simp [criticalObservationPolynomialTorusEquiv,
    criticalObservationTorusIndexEquiv_inr_zero]

/-- **Every unit of the actual critical observation chart is a Laurent monomial in the two marked
coordinates, up to a nonzero ground-field constant.** -/
theorem exists_monomial_of_isUnit_criticalObservationChart
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]
    (u : (criticalObservationChartRing K m n)ˣ) :
    ∃ (c : K) (s t a : ℕ), IsUnit c ∧
      (u : criticalObservationChartRing K m n) *
          algebraMap (criticalObservationRing K m n)
            (criticalObservationChartRing K m n) (criticalObservationMarked K) ^ a
        = algebraMap (criticalObservationRing K m n)
            (criticalObservationChartRing K m n)
            (C c * X (Sum.inl (⟨0, Fact.out⟩ : Fin n)) ^ s *
              X (Sum.inr (⟨0, Fact.out⟩ : Fin m)) ^ t) := by
  let e := criticalObservationChartTorusEquiv K m n
  let ep := criticalObservationPolynomialTorusEquiv K m n
  let uT : (TorusChart K (n + m - 2))ˣ := Units.map e.toMonoidHom u
  obtain ⟨c, s, t, a, hc, hT⟩ := exists_monomial_of_isUnit_torusChart uT
  refine ⟨c, s, t, a, hc, ?_⟩
  have esymm_alg (p : MvPolynomial (Fin ((n + m - 2) + 2)) K) :
      e.symm (algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
        (TorusChart K (n + m - 2)) p) =
      algebraMap (criticalObservationRing K m n)
        (criticalObservationChartRing K m n) (ep.symm p) := by
    apply e.injective
    rw [e.apply_symm_apply]
    simpa [e, ep] using
      (criticalObservationChartTorusEquiv_algebraMap K m n (ep.symm p)).symm
  have epLeft : ep.symm (X 0) =
      X (Sum.inl (⟨0, Fact.out⟩ : Fin n)) := by
    apply ep.injective
    simp [ep, criticalObservationPolynomialTorusEquiv,
      criticalObservationTorusIndexEquiv_inl_zero]
  have epRight : ep.symm (X 1) =
      X (Sum.inr (⟨0, Fact.out⟩ : Fin m)) := by
    apply ep.injective
    simp [ep, criticalObservationPolynomialTorusEquiv,
      criticalObservationTorusIndexEquiv_inr_zero]
  have epMarked : ep.symm (X 0 * X 1) = criticalObservationMarked K := by
    apply ep.injective
    simpa [ep] using (criticalObservationPolynomialTorusEquiv_marked K m n).symm
  have epC : ep.symm (C c) = C c := by
    apply ep.injective
    simp [ep, criticalObservationPolynomialTorusEquiv]
  have he := congrArg e.symm hT
  simpa [e, ep, uT, esymm_alg, epLeft, epRight, epMarked, epC,
    criticalObservationMarked, map_mul, map_pow] using he

/-- **Kummer exponent divisibility on the actual critical observation chart.**  If a chart unit is
an `r`-th power, both exponent differences in any cleared presentation by the two marked
observation coordinates are divisible by `r`. -/
theorem dvd_exponents_of_eq_pow_criticalObservationChart
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]
    {u w : (criticalObservationChartRing K m n)ˣ} {r : ℕ} (hw : u = w ^ r)
    {c c' : (criticalObservationRing K m n)ˣ} {s t a s' t' a' : ℕ}
    (h : (u : criticalObservationChartRing K m n) *
        algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n) (criticalObservationMarked K) ^ a
      = algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n)
          ((c : criticalObservationRing K m n) *
            X (Sum.inl (⟨0, Fact.out⟩ : Fin n)) ^ s *
            X (Sum.inr (⟨0, Fact.out⟩ : Fin m)) ^ t))
    (h' : (w : criticalObservationChartRing K m n) *
        algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n) (criticalObservationMarked K) ^ a'
      = algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n)
          ((c' : criticalObservationRing K m n) *
            X (Sum.inl (⟨0, Fact.out⟩ : Fin n)) ^ s' *
            X (Sum.inr (⟨0, Fact.out⟩ : Fin m)) ^ t')) :
    (r : ℤ) ∣ ((s : ℤ) - (a : ℤ)) ∧ (r : ℤ) ∣ ((t : ℤ) - (a : ℤ)) := by
  let e := criticalObservationChartTorusEquiv K m n
  let uT : (TorusChart K (n + m - 2))ˣ := Units.map e.toMonoidHom u
  let wT : (TorusChart K (n + m - 2))ˣ := Units.map e.toMonoidHom w
  let cT : (MvPolynomial (Fin ((n + m - 2) + 2)) K)ˣ :=
    Units.map (criticalObservationPolynomialTorusEquiv K m n).toMonoidHom c
  let cT' : (MvPolynomial (Fin ((n + m - 2) + 2)) K)ˣ :=
    Units.map (criticalObservationPolynomialTorusEquiv K m n).toMonoidHom c'
  have hwT : uT = wT ^ r := by
    dsimp [uT, wT]
    rw [hw]
    exact map_pow _ _ _
  have hepLeft : criticalObservationPolynomialTorusEquiv K m n
      (X (Sum.inl (⟨0, Fact.out⟩ : Fin n))) =
      (X 0 : MvPolynomial (Fin ((n + m - 2) + 2)) K) := by
    simp [criticalObservationPolynomialTorusEquiv,
      criticalObservationTorusIndexEquiv_inl_zero]
  have hepRight : criticalObservationPolynomialTorusEquiv K m n
      (X (Sum.inr (⟨0, Fact.out⟩ : Fin m))) =
      (X 1 : MvPolynomial (Fin ((n + m - 2) + 2)) K) := by
    simp [criticalObservationPolynomialTorusEquiv,
      criticalObservationTorusIndexEquiv_inr_zero]
  have hT : (uT : TorusChart K (n + m - 2)) *
        algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
          (TorusChart K (n + m - 2)) (X 0 * X 1) ^ a
      = algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
          (TorusChart K (n + m - 2))
          ((cT : MvPolynomial (Fin ((n + m - 2) + 2)) K) * X 0 ^ s * X 1 ^ t) := by
    have he := congrArg e h
    simpa [e, uT, cT, map_mul, map_pow,
      criticalObservationChartTorusEquiv_algebraMap,
      criticalObservationPolynomialTorusEquiv_marked,
      hepLeft, hepRight] using he
  have hT' : (wT : TorusChart K (n + m - 2)) *
        algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
          (TorusChart K (n + m - 2)) (X 0 * X 1) ^ a'
      = algebraMap (MvPolynomial (Fin ((n + m - 2) + 2)) K)
          (TorusChart K (n + m - 2))
          ((cT' : MvPolynomial (Fin ((n + m - 2) + 2)) K) * X 0 ^ s' * X 1 ^ t') := by
    have he := congrArg e h'
    simpa [e, wT, cT', map_mul, map_pow,
      criticalObservationChartTorusEquiv_algebraMap,
      criticalObservationPolynomialTorusEquiv_marked,
      hepLeft, hepRight] using he
  exact dvd_exponents_of_eq_pow_torusChart hwT hT hT'

end GaloisForLFunctions.HTGeometry
