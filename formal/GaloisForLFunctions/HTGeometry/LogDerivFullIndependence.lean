import GaloisForLFunctions.HTGeometry.LogDerivFullJetGauge
import GaloisForLFunctions.HTGeometry.ExponentialFullIndependence
import GaloisForLFunctions.HTGeometry.AnalyticJetRealization
import GaloisForLFunctions.HTGeometry.JetDifferentialFieldHom
import GaloisForLFunctions.HTGeometry.ExponentialLinearIndependence

/-!
# Full jet independence for a logarithmic-derivative family

A family solving `E' = f^{(r)} E` inherits jet independence from its base: the jets of `E` factor as
`E` times polynomials in the jets of `f`, so a relation becomes a linear relation in monomials whose
logarithmic derivatives are the pairwise distinct degree-one forms `<alpha, f^{(r)}>`, and Artin
shortening kills every coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Filter Topology
open scoped Differential

noncomputable section

/-- The degree-one form in the `r`-th jets attached to a tuple of coefficients. -/
def fullLinFormAt (r m : ℕ) (c : Fin m → ℂ) : MvPolynomial (FullJetIndex m) ℂ :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X (Sum.inr (i, r))

theorem fullLinFormAt_sub (r m : ℕ) (c d : Fin m → ℂ) :
    fullLinFormAt r m c - fullLinFormAt r m d = fullLinFormAt r m (fun i => c i - d i) := by
  rw [fullLinFormAt, fullLinFormAt, fullLinFormAt, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub]
  ring

theorem coeff_fullLinFormAt {r m : ℕ} (c : Fin m → ℂ) (i : Fin m) :
    MvPolynomial.coeff (Finsupp.single (Sum.inr (i, r)) 1) (fullLinFormAt r m c) = c i := by
  classical
  rw [fullLinFormAt, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos rfl, mul_one]
  · intro j _ hj
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg ?_, mul_zero]
    intro hcon
    exact hj (by simpa using Finsupp.single_left_injective (one_ne_zero) hcon)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem totalDegree_fullLinFormAt_le (r m : ℕ) (c : Fin m → ℂ) :
    (fullLinFormAt r m c).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun i _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]

theorem fullLinFormAt_totalDegree_eq_one {r m : ℕ} {c : Fin m → ℂ} (i : Fin m) (hi : c i ≠ 0) :
    (fullLinFormAt r m c).totalDegree = 1 := by
  classical
  refine le_antisymm (totalDegree_fullLinFormAt_le r m c) ?_
  rcases Nat.eq_zero_or_pos (fullLinFormAt r m c).totalDegree with h0 | hpos
  · exfalso
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
    have hco := coeff_fullLinFormAt (r := r) c i
    rw [h0, MvPolynomial.coeff_C, if_neg ?_] at hco
    · exact hi hco.symm
    · intro hcon
      exact (Finsupp.single_ne_zero.mpr one_ne_zero) hcon.symm
  · exact hpos

theorem fullLinFormAt_ne_zero {r m : ℕ} {c : Fin m → ℂ} (i : Fin m) (hi : c i ≠ 0) :
    fullLinFormAt r m c ≠ 0 := by
  intro h
  have hdeg := fullLinFormAt_totalDegree_eq_one (r := r) i hi
  rw [h, MvPolynomial.totalDegree_zero] at hdeg
  exact zero_ne_one hdeg

/-- **Exponentials of a differentially independent family are differentially independent.**  A
polynomial in the spectral variable and the jets of `exp (sigma i)` which vanishes identically on the
domain is zero, provided the same holds for the exponents. -/
theorem logDeriv_fullJet_independent {r m : ℕ} {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hreal : ∀ (n : ℕ) (z₀ : ℂ) (y : Fin m → ℕ → ℂ), (∀ i, y i 0 ≠ 0) →
      ∃ (V : Set ℂ) (base' sol' : Fin m → ℂ → ℂ), IsOpen V ∧ z₀ ∈ V ∧
        (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (base' i) w) ∧
        (∀ i, ∀ w ∈ V, ContDiffAt ℂ (⊤ : ℕ∞) (sol' i) w) ∧
        (∀ i, ∀ w ∈ V, deriv (sol' i) w = iteratedDeriv r (base' i) w * sol' i w) ∧
        (∀ i, ∀ k ≤ n, iteratedDeriv k (sol' i) z₀ = y i k))
    {sigma sol : Fin m → ℂ → ℂ} (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U)
    (hsolA : ∀ i, AnalyticOnNhd ℂ (sol i) U)
    (hsolne : ∀ i, ∀ z ∈ U, sol i z ≠ 0)
    (hrel : ∀ i, ∀ z ∈ U, deriv (sol i) z = iteratedDeriv r (sigma i) z * sol i z)
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec sigma z) P = 0) → P = 0)
    (Q : MvPolynomial (FullJetIndex m) ℂ)
    (hQ : ∀ z ∈ U, MvPolynomial.eval (fullJetVec sol z) Q = 0) :
    Q = 0 := by
  classical
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroFieldDifferential hUo hUc hUne
  have hsm : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w :=
    fun i => contDiffAt_of_analyticOnNhd (hs i)
  have hsolsm : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sol i) w :=
    fun i => contDiffAt_of_analyticOnNhd (hsolA i)
  have hrelU : ∀ i, ∀ w ∈ U, deriv (sol i) w = iteratedDeriv r (sigma i) w * sol i w := hrel
  have hsexp : ∀ i, AnalyticOnNhd ℂ (sol i) U := hsolA
  -- the realization of the jet ring inside the meromorphic differential field
  set g : MvPolynomial (FullJetIndex m) ℂ →+* Bottcher.meroField U :=
    (algebraMap (Bottcher.analyticSubring U) (Bottcher.meroField U)).comp (jetAnalyticHom hs)
    with hgdef
  have hginj : Function.Injective g := by
    intro a b hab
    rw [hgdef] at hab
    simp only [RingHom.comp_apply] at hab
    exact jetAnalyticHom_injective hs hind
      (IsFractionRing.injective (Bottcher.analyticSubring U) (Bottcher.meroField U) hab)
  have hgderiv : ∀ p, g (jetLikeDerivation (fullJetShift m) p) = (g p)′ := by
    intro p
    rw [hgdef]
    simp only [RingHom.comp_apply]
    rw [meroFieldDifferential_algebraMap hUo hUc hUne, analyticSubringDeriv_jetAnalyticHom hUo hs p]
    rfl
  -- the exponentials as elements of the field
  set EA : Fin m → Bottcher.analyticSubring U := fun i => analyticFunGerm (hsexp i) with hEA
  set EE : Fin m → Bottcher.meroField U :=
    fun i => algebraMap (Bottcher.analyticSubring U) (Bottcher.meroField U) (EA i) with hEE
  have hEAne : ∀ i, EA i ≠ 0 := by
    intro i hcon
    obtain ⟨z, hz⟩ := hUne
    have hval := congrArg Subtype.val hcon
    simp only [hEA, analyticFunGerm_coe, ZeroMemClass.coe_zero] at hval
    rw [← Germ.coe_zero, Germ.coe_eq] at hval
    exact hsolne i z hz (by simpa using eventually_principal.mp hval z hz)
  have hEEne : ∀ i, EE i ≠ 0 := by
    intro i hcon
    refine hEAne i (IsFractionRing.injective (Bottcher.analyticSubring U)
      (Bottcher.meroField U) ?_)
    rw [map_zero]
    rw [hEE] at hcon
    exact hcon
  have hEAderiv : ∀ i, analyticSubringDeriv hUo (EA i)
      = jetAnalyticHom hs (MvPolynomial.X (Sum.inr (i, r))) * EA i := by
    intro i
    refine analyticSubring_eq_of_eqOn (f := deriv (sol i))
      (h := fun w => MvPolynomial.eval (fullJetVec sigma w) (MvPolynomial.X (Sum.inr (i, r)))
        * sol i w) ?_ ?_ ?_
    · rw [analyticSubringDeriv_coe]
      simp only [hEA, analyticFunGerm_coe]
      rw [analyticGermDeriv_coe]
    · refine analyticSubring_coe_mul (jetAnalyticHom_coe hs _) ?_
      simp only [hEA, analyticFunGerm_coe]
    · intro z hz
      rw [MvPolynomial.eval_X, fullJetVec_inr]
      exact hrel i z hz
  have hEEderiv : ∀ i, (EE i)′ = g (MvPolynomial.X (Sum.inr (i, r))) * EE i := by
    intro i
    rw [hEE, hgdef]
    simp only [RingHom.comp_apply]
    rw [meroFieldDifferential_algebraMap hUo hUc hUne, hEAderiv i, map_mul]
  -- the relation, grouped by exponential monomials
  set W : FullLogRing m := fullLogSubstHom r m Q with hW
  have hWzero : MvPolynomial.eval₂ g EE W = 0 := by
    have hcomp : ((MvPolynomial.eval₂Hom g EE : FullLogRing m →+* Bottcher.meroField U).comp
          (fullLogSubstHom r m))
        = (algebraMap (Bottcher.analyticSubring U) (Bottcher.meroField U)).comp
            (jetAnalyticHom hsexp) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp only [hgdef, RingHom.comp_apply, fullLogSubstHom_C, MvPolynomial.eval₂Hom_C]
        congr 1
        refine analyticSubring_eq_of_eqOn (jetAnalyticHom_coe hs _) (jetAnalyticHom_coe hsexp _) ?_
        intro z _
        simp only [MvPolynomial.eval_C]
      · rcases v with u | ⟨i, k⟩
        · simp only [hgdef, RingHom.comp_apply, fullLogSubstHom_X, fullLogSubst, Sum.elim_inl,
            MvPolynomial.eval₂Hom_C]
          congr 1
          refine analyticSubring_eq_of_eqOn (jetAnalyticHom_coe hs _)
            (jetAnalyticHom_coe hsexp _) ?_
          intro z _
          simp only [MvPolynomial.eval_X, fullJetVec_inl]
        · simp only [hgdef, hEE, RingHom.comp_apply, fullLogSubstHom_X, fullLogSubst, Sum.elim_inr,
            map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
          rw [← map_mul]
          congr 1
          refine analyticSubring_eq_of_eqOn
            (analyticSubring_coe_mul (f := sol i)
              (h := fun w => MvPolynomial.eval (fullJetVec sigma w) (fullLogJetNum r m i k))
              (by simp only [hEA, analyticFunGerm_coe]) (jetAnalyticHom_coe hs _))
            (jetAnalyticHom_coe hsexp _) ?_
          intro z hz
          rw [MvPolynomial.eval_X]
          exact (fullJetVec_logDeriv_apply hUo hsm hsolsm hrelU hz i k).symm
    have happ := congrArg
      (fun f : MvPolynomial (FullJetIndex m) ℂ →+* Bottcher.meroField U => f Q) hcomp
    simp only [RingHom.comp_apply] at happ
    have hQ0 : jetAnalyticHom hsexp Q = 0 := by
      apply Subtype.ext
      rw [jetAnalyticHom_coe, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr hQ
    rw [hW]
    have hcast : MvPolynomial.eval₂ g EE (fullLogSubstHom r m Q)
        = (MvPolynomial.eval₂Hom g EE : FullLogRing m →+* Bottcher.meroField U)
            (fullLogSubstHom r m Q) := rfl
    rw [hcast, happ, hQ0, map_zero]
  -- Artin shortening kills every coefficient
  have hcoeff : ∀ d ∈ W.support, MvPolynomial.coeff d W = 0 := by
    intro d hd
    have hFd : ∀ a ∈ jetSubfield hginj, a′ ∈ jetSubfield hginj :=
      jetSubfield_deriv_mem hginj hgderiv
    set E : ↥W.support → Bottcher.meroField U :=
      fun e => ∏ i ∈ (e : Fin m →₀ ℕ).support, EE i ^ (e : Fin m →₀ ℕ) i with hE
    set tau : ↥W.support → Bottcher.meroField U :=
      fun e => g (fullLinFormAt r m fun i => (((e : Fin m →₀ ℕ) i : ℕ) : ℂ)) with htau
    set cc : ↥W.support → Bottcher.meroField U :=
      fun e => g (MvPolynomial.coeff (e : Fin m →₀ ℕ) W) with hcc
    have hEne : ∀ e, E e ≠ 0 := by
      intro e
      rw [hE]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hEEne i)
    have hEd : ∀ e, (E e)′ = tau e * E e := by
      intro e
      rw [hE]
      simp only
      rw [deriv_prod_pow _ EE (fun i => g (MvPolynomial.X (Sum.inr (i, r))))
        (fun i _ => hEEderiv i)]
      congr 1
      rw [htau]
      simp only [fullLinFormAt, map_sum, map_mul]
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
      · intro i _ hi
        rw [Finsupp.notMem_support_iff.mp hi]
        simp only [Nat.cast_zero, zero_mul]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_C_natCast]
    have htauF : ∀ e, tau e ∈ jetSubfield hginj := by
      intro e
      rw [htau]
      exact mem_jetSubfield hginj _
    have hccF : ∀ e, cc e ∈ jetSubfield hginj := by
      intro e
      rw [hcc]
      exact mem_jetSubfield hginj _
    have hexcl : ∀ e₁ e₂ : ↥W.support, e₁ ≠ e₂ →
        ∀ c ∈ jetSubfield hginj, c ≠ 0 → c′ ≠ (tau e₁ - tau e₂) * c := by
      intro e₁ e₂ hne c hcF hc
      obtain ⟨i, hi⟩ : ∃ i, (e₁ : Fin m →₀ ℕ) i ≠ (e₂ : Fin m →₀ ℕ) i := by
        refine DFunLike.ne_iff.mp ?_
        intro hcon
        exact hne (Subtype.ext hcon)
      have hci : ((((e₁ : Fin m →₀ ℕ) i : ℕ) : ℂ) - (((e₂ : Fin m →₀ ℕ) i : ℕ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact fun hcon => hi (Nat.cast_injective hcon)
      have hdiff : tau e₁ - tau e₂
          = g (fullLinFormAt r m fun j => (((e₁ : Fin m →₀ ℕ) j : ℕ) : ℂ)
              - (((e₂ : Fin m →₀ ℕ) j : ℕ) : ℂ)) := by
        rw [htau, ← map_sub, fullLinFormAt_sub]
      rw [hdiff]
      exact jetSubfield_logDeriv_impossible (totalDegree_fullJetShift_le m) hginj hgderiv
        (fullLinFormAt_ne_zero i hci) (fullLinFormAt_totalDegree_eq_one i hci) hcF hc
    have hsum : ∑ e : ↥W.support, cc e * E e = 0 := by
      rw [hcc, hE]
      simp only
      rw [Finset.sum_coe_sort W.support
        (fun d => g (MvPolynomial.coeff d W) * ∏ i ∈ d.support, EE i ^ d i),
        ← MvPolynomial.eval₂_eq g EE W]
      exact hWzero
    have hzero := eq_zero_of_sum_expLike_eq_zero (jetSubfield hginj) hFd E tau hEne hEd htauF
      hexcl cc hccF hsum
    have hd0 := hzero ⟨d, hd⟩
    rw [hcc] at hd0
    refine hginj ?_
    rw [map_zero]
    exact hd0
  have hW0 : W = 0 := by
    refine MvPolynomial.ext W 0 fun d => ?_
    rw [MvPolynomial.coeff_zero]
    by_cases hd : d ∈ W.support
    · exact hcoeff d hd
    · exact MvPolynomial.notMem_support_iff.mp hd
  refine fullLogSubstHom_injective r m hreal ?_
  rw [map_zero, ← hW]
  exact hW0


end

end GaloisForLFunctions.HTGeometry
