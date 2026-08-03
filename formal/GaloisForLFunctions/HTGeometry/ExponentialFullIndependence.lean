import GaloisForLFunctions.HTGeometry.AnalyticJetRealization
import GaloisForLFunctions.HTGeometry.FullExponentialJetGauge
import GaloisForLFunctions.HTGeometry.JetDifferentialFieldHom
import GaloisForLFunctions.HTGeometry.ExponentialLinearIndependence

/-!
# Exponentials of a differentially independent family are differentially independent

A differential relation among `exp (sigma 1), ..., exp (sigma m)` is, after substituting the
exponential jet formula, a linear relation

`sum over alpha of (prod_i exp (sigma i) ^ alpha i) * R_alpha (z, jets sigma) = 0`

in the exponential monomials, with coefficients rational in the jets of the exponents.  Inside the
meromorphic differential field of the domain the exponential monomials are exponential-like elements
whose exponents are the degree-one forms `<alpha, sigma'>`, so Artin shortening applies: it would
force a differential rational function of the exponents to have a logarithmic derivative of degree
one, which is impossible.  Hence every `R_alpha` vanishes, and since the exponential jet
substitution is injective the original relation was trivial.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped Differential

noncomputable section

/-- The degree-one form in the first jets attached to a tuple of coefficients. -/
def fullLinForm (m : ℕ) (c : Fin m → ℂ) : MvPolynomial (FullJetIndex m) ℂ :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X (Sum.inr (i, 1))

theorem fullLinForm_sub (m : ℕ) (c d : Fin m → ℂ) :
    fullLinForm m c - fullLinForm m d = fullLinForm m (fun i => c i - d i) := by
  rw [fullLinForm, fullLinForm, fullLinForm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub]
  ring

theorem coeff_fullLinForm {m : ℕ} (c : Fin m → ℂ) (i : Fin m) :
    MvPolynomial.coeff (Finsupp.single (Sum.inr (i, 1)) 1) (fullLinForm m c) = c i := by
  classical
  rw [fullLinForm, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos rfl, mul_one]
  · intro j _ hj
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg ?_, mul_zero]
    intro hcon
    exact hj (by simpa using Finsupp.single_left_injective (one_ne_zero) hcon)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem totalDegree_fullLinForm_le (m : ℕ) (c : Fin m → ℂ) :
    (fullLinForm m c).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun i _ => ?_
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]

theorem fullLinForm_totalDegree_eq_one {m : ℕ} {c : Fin m → ℂ} (i : Fin m) (hi : c i ≠ 0) :
    (fullLinForm m c).totalDegree = 1 := by
  classical
  refine le_antisymm (totalDegree_fullLinForm_le m c) ?_
  rcases Nat.eq_zero_or_pos (fullLinForm m c).totalDegree with h0 | hpos
  · exfalso
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
    have hco := coeff_fullLinForm c i
    rw [h0, MvPolynomial.coeff_C, if_neg ?_] at hco
    · exact hi hco.symm
    · intro hcon
      exact (Finsupp.single_ne_zero.mpr one_ne_zero) hcon.symm
  · exact hpos

theorem fullLinForm_ne_zero {m : ℕ} {c : Fin m → ℂ} (i : Fin m) (hi : c i ≠ 0) :
    fullLinForm m c ≠ 0 := by
  intro h
  have hdeg := fullLinForm_totalDegree_eq_one i hi
  rw [h, MvPolynomial.totalDegree_zero] at hdeg
  exact zero_ne_one hdeg

theorem map_C_natCast {R : Type*} [CommRing R] {ι : Type*} (g : MvPolynomial ι ℂ →+* R) (k : ℕ) :
    g (MvPolynomial.C (k : ℂ)) = (k : R) := by
  rw [map_natCast MvPolynomial.C k, map_natCast]

/-- **Exponentials of a differentially independent family are differentially independent.**  A
polynomial in the spectral variable and the jets of `exp (sigma i)` which vanishes identically on the
domain is zero, provided the same holds for the exponents. -/
theorem exp_fullJet_independent {m : ℕ} {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) {sigma : Fin m → ℂ → ℂ} (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U)
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec sigma z) P = 0) → P = 0)
    (Q : MvPolynomial (FullJetIndex m) ℂ)
    (hQ : ∀ z ∈ U, MvPolynomial.eval (fullJetVec (fun i w => Complex.exp (sigma i w)) z) Q = 0) :
    Q = 0 := by
  classical
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := meroFieldDifferential hUo hUc hUne
  have hsm : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w :=
    fun i => contDiffAt_of_analyticOnNhd (hs i)
  have hsexp : ∀ i, AnalyticOnNhd ℂ (fun w => Complex.exp (sigma i w)) U :=
    fun i z hz => (hs i z hz).cexp
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
    exact Complex.exp_ne_zero (sigma i z) (eventually_principal.mp hval z hz)
  have hEEne : ∀ i, EE i ≠ 0 := by
    intro i hcon
    refine hEAne i (IsFractionRing.injective (Bottcher.analyticSubring U)
      (Bottcher.meroField U) ?_)
    rw [map_zero]
    rw [hEE] at hcon
    exact hcon
  have hEAderiv : ∀ i, analyticSubringDeriv hUo (EA i)
      = jetAnalyticHom hs (MvPolynomial.X (Sum.inr (i, 1))) * EA i := by
    intro i
    refine analyticSubring_eq_of_eqOn (f := deriv (fun w => Complex.exp (sigma i w)))
      (h := fun w => MvPolynomial.eval (fullJetVec sigma w) (MvPolynomial.X (Sum.inr (i, 1)))
        * Complex.exp (sigma i w)) ?_ ?_ ?_
    · rw [analyticSubringDeriv_coe]
      simp only [hEA, analyticFunGerm_coe]
      rw [analyticGermDeriv_coe]
    · refine analyticSubring_coe_mul (jetAnalyticHom_coe hs _) ?_
      simp only [hEA, analyticFunGerm_coe]
    · intro z hz
      rw [deriv_cexp ((hs i z hz).differentiableAt), MvPolynomial.eval_X, fullJetVec_inr,
        iteratedDeriv_one]
      ring
  have hEEderiv : ∀ i, (EE i)′ = g (MvPolynomial.X (Sum.inr (i, 1))) * EE i := by
    intro i
    rw [hEE, hgdef]
    simp only [RingHom.comp_apply]
    rw [meroFieldDifferential_algebraMap hUo hUc hUne, hEAderiv i, map_mul]
  -- the relation, grouped by exponential monomials
  set W : FullExpRing m := fullExpSubstHom m Q with hW
  have hWzero : MvPolynomial.eval₂ g EE W = 0 := by
    have hcomp : ((MvPolynomial.eval₂Hom g EE : FullExpRing m →+* Bottcher.meroField U).comp
          (fullExpSubstHom m))
        = (algebraMap (Bottcher.analyticSubring U) (Bottcher.meroField U)).comp
            (jetAnalyticHom hsexp) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp only [hgdef, RingHom.comp_apply, fullExpSubstHom_C, MvPolynomial.eval₂Hom_C]
        congr 1
        refine analyticSubring_eq_of_eqOn (jetAnalyticHom_coe hs _) (jetAnalyticHom_coe hsexp _) ?_
        intro z _
        simp only [MvPolynomial.eval_C]
      · rcases v with u | ⟨i, k⟩
        · simp only [hgdef, RingHom.comp_apply, fullExpSubstHom_X, fullExpSubst, Sum.elim_inl,
            MvPolynomial.eval₂Hom_C]
          congr 1
          refine analyticSubring_eq_of_eqOn (jetAnalyticHom_coe hs _)
            (jetAnalyticHom_coe hsexp _) ?_
          intro z _
          simp only [MvPolynomial.eval_X, fullJetVec_inl]
        · simp only [hgdef, hEE, RingHom.comp_apply, fullExpSubstHom_X, fullExpSubst, Sum.elim_inr,
            map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
          rw [← map_mul]
          congr 1
          refine analyticSubring_eq_of_eqOn
            (analyticSubring_coe_mul (f := fun w => Complex.exp (sigma i w))
              (h := fun w => MvPolynomial.eval (fullJetVec sigma w) (fullExpJetNum m i k))
              (by simp only [hEA, analyticFunGerm_coe]) (jetAnalyticHom_coe hs _))
            (jetAnalyticHom_coe hsexp _) ?_
          intro z hz
          rw [MvPolynomial.eval_X]
          exact (fullJetVec_exp_apply hUo hsm hz i k).symm
    have happ := congrArg
      (fun f : MvPolynomial (FullJetIndex m) ℂ →+* Bottcher.meroField U => f Q) hcomp
    simp only [RingHom.comp_apply] at happ
    have hQ0 : jetAnalyticHom hsexp Q = 0 := by
      apply Subtype.ext
      rw [jetAnalyticHom_coe, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
      exact eventually_principal.mpr hQ
    rw [hW]
    have hcast : MvPolynomial.eval₂ g EE (fullExpSubstHom m Q)
        = (MvPolynomial.eval₂Hom g EE : FullExpRing m →+* Bottcher.meroField U)
            (fullExpSubstHom m Q) := rfl
    rw [hcast, happ, hQ0, map_zero]
  -- Artin shortening kills every coefficient
  have hcoeff : ∀ d ∈ W.support, MvPolynomial.coeff d W = 0 := by
    intro d hd
    have hFd : ∀ a ∈ jetSubfield hginj, a′ ∈ jetSubfield hginj :=
      jetSubfield_deriv_mem hginj hgderiv
    set E : ↥W.support → Bottcher.meroField U :=
      fun e => ∏ i ∈ (e : Fin m →₀ ℕ).support, EE i ^ (e : Fin m →₀ ℕ) i with hE
    set tau : ↥W.support → Bottcher.meroField U :=
      fun e => g (fullLinForm m fun i => (((e : Fin m →₀ ℕ) i : ℕ) : ℂ)) with htau
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
      rw [deriv_prod_pow _ EE (fun i => g (MvPolynomial.X (Sum.inr (i, 1))))
        (fun i _ => hEEderiv i)]
      congr 1
      rw [htau]
      simp only [fullLinForm, map_sum, map_mul]
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
          = g (fullLinForm m fun j => (((e₁ : Fin m →₀ ℕ) j : ℕ) : ℂ)
              - (((e₂ : Fin m →₀ ℕ) j : ℕ) : ℂ)) := by
        rw [htau, ← map_sub, fullLinForm_sub]
      rw [hdiff]
      exact jetSubfield_logDeriv_impossible (totalDegree_fullJetShift_le m) hginj hgderiv
        (fullLinForm_ne_zero i hci) (fullLinForm_totalDegree_eq_one i hci) hcF hc
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
  refine fullExpSubstHom_injective m ?_
  rw [map_zero, ← hW]
  exact hW0

/-- **The exponential gauge.**  If a finite analytic family satisfies no differential relation on a
connected domain, neither does the family of its exponentials. -/
theorem not_familyDifferentiallyAlgebraicOn_exp {m : ℕ} {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, AnalyticOnNhd ℂ (sigma i) U)
    (hind : ¬ FamilyDifferentiallyAlgebraicOn sigma U) :
    ¬ FamilyDifferentiallyAlgebraicOn (fun i w => Complex.exp (sigma i w)) U := by
  rintro ⟨n, Q, hQne, hQ0⟩
  have hev : ∀ z ∈ U, MvPolynomial.eval (fullJetVec (fun i w => Complex.exp (sigma i w)) z)
      (MvPolynomial.rename (jetEmbed m n) Q) = 0 := by
    intro z hz
    rw [eval_rename_jetEmbed]
    exact hQ0 z hz
  have hfull := exp_fullJet_independent hUo hUc hUne hs
    (fun P hP => fullJet_independent_of_not_familyDifferentiallyAlgebraicOn hind P hP)
    (MvPolynomial.rename (jetEmbed m n) Q) hev
  refine hQne (MvPolynomial.rename_injective _ (jetEmbed_injective m n) ?_)
  rw [hfull, map_zero]

end

end GaloisForLFunctions.HTGeometry

