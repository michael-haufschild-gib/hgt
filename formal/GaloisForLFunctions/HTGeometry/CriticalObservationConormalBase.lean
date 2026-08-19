import GaloisForLFunctions.HTGeometry.CriticalObservationCotangentBasis

/-!
# The conormal direction is defined over the observation side, and is nonzero

The branch divisor is generically smooth.  Concretely: the centre of the observation Schur place on
the observation coordinate ring is a prime `𝔭`; a nonzero element of `𝔭` of minimal total degree
cannot have all its partial derivatives again in `𝔭`, since differentiation strictly drops the
total degree and a polynomial with all partial derivatives zero is constant in characteristic zero.

```text
totalDegree_pderiv_lt_of_ne_zero
totalDegree_eq_zero_of_forall_pderiv_eq_zero
criticalObservationSchurCentre                       the centre of the Schur place
exists_ne_zero_mem_criticalObservationSchurCentre
exists_mem_maximalIdeal_repr_D_notMem_maximalIdeal
    ** some non-unit of the observation Schur place has a differential with a unit coordinate **
```

Together with `criticalSchur_jacobian_conormal_mem_maximalIdeal` this says the conormal line of the
branch at the source Schur place is spanned by a **nonzero** vector with entries pulled back from
the observation side.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Differentiating drops the total degree. -/
theorem totalDegree_pderiv_lt_of_ne_zero {p : MvPolynomial σ R} (i : σ) (hne : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hkey : ∀ m ∈ (pderiv i p).support, (m.sum fun _ e => e) < p.totalDegree := by
    intro m hm
    have hc : coeff m (pderiv i p) ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hc
    have hc2 : coeff (m + Finsupp.single i 1) p ≠ 0 := fun h => hc (by rw [h, zero_mul])
    have hle : ((m + Finsupp.single i 1).sum fun _ e => e) ≤ p.totalDegree :=
      MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc2)
    have hsum : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    omega
  obtain ⟨m₀, hm₀⟩ := Finset.nonempty_iff_ne_empty.mpr
    (fun h => hne (MvPolynomial.support_eq_empty.mp h))
  have hpos : 0 < p.totalDegree := lt_of_le_of_lt (Nat.zero_le _) (hkey m₀ hm₀)
  rw [MvPolynomial.totalDegree]
  exact Finset.sup_lt_iff hpos |>.mpr hkey

/-- In characteristic zero, a polynomial with all partial derivatives zero is constant. -/
theorem totalDegree_eq_zero_of_forall_pderiv_eq_zero [CharZero R] [NoZeroDivisors R]
    {p : MvPolynomial σ R} (h : ∀ i, pderiv i p = 0) : p.totalDegree = 0 := by
  classical
  by_contra hpos
  obtain ⟨m, hm, hmdeg⟩ : ∃ m ∈ p.support, 0 < (m.sum fun _ e => e) := by
    by_contra hcon
    push Not at hcon
    apply hpos
    refine Nat.le_zero.mp (Finset.sup_le fun m hm => ?_)
    exact Nat.le_zero.mpr (Nat.le_zero.mp (hcon m hm))
  obtain ⟨i, hi⟩ : ∃ i, 0 < m i := by
    by_contra hcon
    push Not at hcon
    have : m = 0 := Finsupp.ext fun i => Nat.le_zero.mp (hcon i)
    rw [this] at hmdeg
    simp at hmdeg
  have hadd : (m - Finsupp.single i 1) + Finsupp.single i 1 = m := by
    ext j
    by_cases hj : j = i
    · subst hj
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · have hz : (Finsupp.single i 1 : σ →₀ ℕ) j = 0 :=
        Finsupp.single_eq_of_ne hj
      rw [Finsupp.add_apply, Finsupp.tsub_apply, hz]
      omega
  have hcoeff := MvPolynomial.coeff_pderiv (i := i) p (m - Finsupp.single i 1)
  rw [h i, MvPolynomial.coeff_zero, hadd] at hcoeff
  have hidxN : (m - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = m i := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hidx : ((m - Finsupp.single i 1 : σ →₀ ℕ) i : R) + 1 = (m i : R) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : R)) hidxN
  rw [hidx] at hcoeff
  have hne : (m i : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rcases mul_eq_zero.mp hcoeff.symm with h1 | h1
  · exact (MvPolynomial.mem_support_iff.mp hm) h1
  · exact hne h1


noncomputable section

open KaehlerDifferential IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The centre of the observation Schur place on the observation coordinate ring. -/
def criticalObservationSchurCentre : Ideal (criticalObservationRing K m n) :=
  (maximalIdeal (criticalSchurObservationValuationSubring K (Fact.out : 0 < m)
    (Fact.out : 0 < n))).comap
    (algebraMap (criticalObservationRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))

instance criticalObservationSchurCentre_isPrime :
    (criticalObservationSchurCentre K (m := m) (n := n)).IsPrime :=
  Ideal.comap_isPrime _ _

theorem criticalObservationSchurCentre_ne_top :
    criticalObservationSchurCentre K (m := m) (n := n) ≠ ⊤ :=
  (criticalObservationSchurCentre_isPrime K (m := m) (n := n)).ne_top

/-- The centre contains a nonzero polynomial. -/
theorem exists_ne_zero_mem_criticalObservationSchurCentre :
    ∃ r : criticalObservationRing K m n,
      r ∈ criticalObservationSchurCentre K (m := m) (n := n) ∧ r ≠ 0 := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible
    (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (M := (criticalSchurChartUnder K (m := m) (n := n)).primeCompl) w
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj
    (M := Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) c
  have hsu : IsUnit (algebraMap (criticalObservationChartRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
      (s : criticalObservationChartRing K m n)) :=
    IsLocalization.map_units (M := (criticalSchurChartUnder K (m := m) (n := n)).primeCompl) _ s
  have htu : IsUnit (algebraMap (criticalObservationRing K m n)
      (criticalObservationChartRing K m n) (t : criticalObservationRing K m n)) :=
    IsLocalization.map_units
      (M := Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) _ t
  refine ⟨r, ?_, ?_⟩
  · show algebraMap (criticalObservationRing K m n)
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) r
      ∈ maximalIdeal _
    have hstep : algebraMap (criticalObservationRing K m n)
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) r
        = w * algebraMap (criticalObservationChartRing K m n) _
            (s : criticalObservationChartRing K m n)
          * algebraMap (criticalObservationChartRing K m n) _
            (algebraMap (criticalObservationRing K m n) (criticalObservationChartRing K m n)
              (t : criticalObservationRing K m n)) := by
      rw [hcs]
      rw [IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
        (criticalObservationChartRing K m n)
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) r,
        ← hrt, map_mul]
    rw [hstep]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      ((IsLocalRing.mem_maximalIdeal _).mpr hw.not_isUnit))
  · intro hr0
    apply hw.ne_zero
    have hc0 : c = 0 := by
      have := hrt
      rw [hr0, map_zero] at this
      exact (htu.mul_left_eq_zero).mp this
    have := hcs
    rw [hc0, map_zero] at this
    exact (hsu.mul_left_eq_zero).mp this

/-- **The conormal direction of the branch is defined over the observation side.**  Some non-unit
of the observation Schur place has a differential with a unit coordinate. -/
theorem exists_mem_maximalIdeal_repr_D_notMem_maximalIdeal :
    ∃ a : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n),
      a ∈ maximalIdeal
        (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) ∧
      ∃ s : Fin m ⊕ Fin n,
        (criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
          (KaehlerDifferential.D K
            (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            a) s
        ∉ maximalIdeal
          (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  classical
  obtain ⟨r₀, hr₀p, hr₀0⟩ := exists_ne_zero_mem_criticalObservationSchurCentre K (m := m) (n := n)
  have hex : ∃ d : ℕ, ∃ r : criticalObservationRing K m n,
      r ∈ criticalObservationSchurCentre K (m := m) (n := n) ∧ r ≠ 0 ∧ r.totalDegree = d :=
    ⟨r₀.totalDegree, r₀, hr₀p, hr₀0, rfl⟩
  obtain ⟨r, hrp, hr0, hrd⟩ := Nat.find_spec hex
  have hmin : ∀ q : criticalObservationRing K m n,
      q ∈ criticalObservationSchurCentre K (m := m) (n := n) → q ≠ 0 →
      Nat.find hex ≤ q.totalDegree := fun q hq hq0 => Nat.find_min' hex ⟨q, hq, hq0, rfl⟩
  have hdegpos : 0 < r.totalDegree := by
    rcases Nat.eq_zero_or_pos r.totalDegree with h | h
    · exfalso
      have hc : r = MvPolynomial.C (MvPolynomial.coeff 0 r) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
      have hcne : MvPolynomial.coeff 0 r ≠ 0 := fun h0 => hr0 (by rw [hc, h0, map_zero])
      refine criticalObservationSchurCentre_ne_top K (m := m) (n := n) ?_
      refine Ideal.eq_top_of_isUnit_mem _ hrp ?_
      rw [hc]
      exact isUnit_iff_exists_inv.mpr ⟨MvPolynomial.C (MvPolynomial.coeff 0 r)⁻¹,
        by rw [← map_mul, mul_inv_cancel₀ hcne, map_one]⟩
    · exact h
  have hsome : ∃ s : Fin n ⊕ Fin m, MvPolynomial.pderiv s r
      ∉ criticalObservationSchurCentre K (m := m) (n := n) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ s : Fin n ⊕ Fin m, MvPolynomial.pderiv s r = 0 := by
      intro s
      by_contra hne
      have hlt := totalDegree_pderiv_lt_of_ne_zero (R := K) s hne
      have := hmin _ (hcon s) hne
      omega
    have := totalDegree_eq_zero_of_forall_pderiv_eq_zero hall
    omega
  obtain ⟨s, hs⟩ := hsome
  refine ⟨algebraMap (criticalObservationRing K m n) _ r, hrp,
    (Equiv.sumComm (Fin n) (Fin m)) s, ?_⟩
  have hre : (criticalObservationBlockCotangentBasis K (m := m) (n := n)).repr
      (KaehlerDifferential.D K _ (algebraMap (criticalObservationRing K m n) _ r))
      ((Equiv.sumComm (Fin n) (Fin m)) s)
      = (criticalObservationSchurCotangentBasis K (m := m) (n := n)).repr
        (KaehlerDifferential.D K _ (algebraMap (criticalObservationRing K m n) _ r)) s := by
    show (Module.Basis.reindex _ _).repr _ _ = _
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
  rw [hre]
  show (criticalObservationSchurCotangentBasis K (m := m) (n := n)).repr _ _ ∉ _
  rw [show (criticalObservationSchurCotangentBasis K (m := m) (n := n)).repr
      (KaehlerDifferential.D K _ (algebraMap (criticalObservationRing K m n) _ r)) s
      = algebraMap (criticalObservationRing K m n) _ (MvPolynomial.pderiv s r) from
    formallyEtaleCotangentBasis_repr_D_algebraMap K _ r s]
  exact hs

end

end GaloisForLFunctions.HTGeometry
