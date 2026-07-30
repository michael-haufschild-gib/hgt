import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp

/-!
# Local hypertranscendence of `digamma ∘ Gamma`

This strengthens the global total-function capstone to the analytic-germ statement needed in
classical differential algebra.  The regular set is the complement of the countable union of
Gamma level sets `Gamma z = -m`; it is open and path connected.  Hence a differential relation
on any nonempty regular open patch propagates to every regular factorial microscope.  The same
initial-form and Möbius-pullback contradiction then rules it out.

The terminal result is `no_local_differential_relation_digamma_comp_Gamma`.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def digammaGammaRegularSet : Set ℂ :=
  {z : ℂ | ∀ m : ℕ, Complex.Gamma z ≠ -(m : ℂ)}

theorem digammaGammaRegularSet_input_offPoles {z : ℂ}
    (hz : z ∈ digammaGammaRegularSet) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n hzn
  have h0 := hz 0
  rw [hzn, Complex.Gamma_neg_nat_eq_zero] at h0
  simp at h0

theorem analyticAt_digamma_comp_Gamma {z : ℂ}
    (hz : z ∈ digammaGammaRegularSet) :
    AnalyticAt ℂ (fun w => Complex.digamma (Complex.Gamma w)) z := by
  have hin := digammaGammaRegularSet_input_offPoles hz
  have hout : ∀ m : ℕ, Complex.Gamma z ≠ -(m : ℂ) := hz
  exact AnalyticAt.comp (f := Complex.Gamma) (x := z)
    (analyticAt_digamma_of_offPoles hout) (analyticAt_Gamma z hin)

theorem isOpen_digammaGammaRegularSet : IsOpen digammaGammaRegularSet := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hin := digammaGammaRegularSet_input_offPoles hz
  have hcont := (analyticAt_Gamma z hin).continuousAt
  exact hcont (offPoles_isOpen.mem_nhds hz)

theorem gammaLevelSet_countable (m : ℕ) :
    {z : ℂ | Complex.Gamma z = -(m : ℂ)}.Countable := by
  let Ω : Set ℂ := {z : ℂ | ∀ n : ℕ, z ≠ -(n : ℂ)}
  let f : ℂ → ℂ := fun z => Complex.Gamma z + (m : ℂ)
  have hΩconn : IsConnected Ω := by
    refine ⟨⟨1, ?_⟩, offPoles_isPreconnected⟩
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfan : AnalyticOnNhd ℂ f Ω := by
    intro z hz
    exact (analyticAt_Gamma z hz).add analyticAt_const
  have h1Ω : (1 : ℂ) ∈ Ω := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hf1 : f 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [f] at hre
    have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hcodiscrete : f ⁻¹' {0}ᶜ ∈ codiscreteWithin Ω :=
    hfan.preimage_zero_mem_codiscreteWithin hf1 h1Ω hΩconn
  have hdisc : IsDiscrete (f ⁻¹' {0} ∩ Ω) :=
    isDiscrete_of_codiscreteWithin hcodiscrete
  have hzeroCount : (f ⁻¹' {0} ∩ Ω).Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  have hΩcompl : Ωᶜ.Countable := by
    have heq : Ωᶜ = Set.range (fun n : ℕ => (-(n : ℂ))) := by
      ext z
      simp only [Ω, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_ne_iff,
        Set.mem_range]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := h
        exact ⟨n, hn.symm⟩
      · intro h
        obtain ⟨n, hn⟩ := h
        exact ⟨n, hn.symm⟩
    rw [heq]
    exact Set.countable_range _
  apply (hΩcompl.union hzeroCount).mono
  intro z hz
  by_cases hzΩ : z ∈ Ω
  · right
    refine ⟨?_, hzΩ⟩
    change Complex.Gamma z = -(m : ℂ) at hz
    change Complex.Gamma z + (m : ℂ) = 0
    rw [hz]
    ring
  · left
    exact hzΩ

theorem digammaGammaRegularSet_compl_countable :
    digammaGammaRegularSetᶜ.Countable := by
  have heq : digammaGammaRegularSetᶜ =
      ⋃ m : ℕ, {z : ℂ | Complex.Gamma z = -(m : ℂ)} := by
    ext z
    simp [digammaGammaRegularSet]
  rw [heq]
  exact Set.countable_iUnion gammaLevelSet_countable

theorem digammaGammaRegularSet_isPreconnected :
    IsPreconnected digammaGammaRegularSet := by
  rw [show digammaGammaRegularSet = digammaGammaRegularSetᶜᶜ by simp]
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_
    digammaGammaRegularSet_compl_countable).isConnected.isPreconnected
  rw [Complex.rank_real_complex]
  norm_num

def DifferentiallyAlgebraicOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
    ∀ z ∈ U, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)) P = 0

theorem analyticAt_digammaGammaDifferentialEval (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) {z : ℂ}
    (hz : z ∈ digammaGammaRegularSet) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval
      (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
        (fun s => Complex.digamma (Complex.Gamma s)) w)) P) z := by
  have hf := analyticAt_digamma_comp_Gamma hz
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
            (fun s => Complex.digamma (Complex.Gamma s)) w)) (P + Q)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
                (fun s => Complex.digamma (Complex.Gamma s)) w)) P +
            MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
                (fun s => Complex.digamma (Complex.Gamma s)) w)) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval
          (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
            (fun s => Complex.digamma (Complex.Gamma s)) w))
              (P * MvPolynomial.X i)) =
          fun w => MvPolynomial.eval
              (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
                (fun s => Complex.digamma (Complex.Gamma s)) w)) P *
            (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
              (fun s => Complex.digamma (Complex.Gamma s)) w) : Fin (n + 2) → ℂ) i := by
        funext w
        simp
      rw [heq]
      refine hP.mul ?_
      induction i using Fin.cases with
      | zero =>
          simp only [Fin.cons_zero]
          exact analyticAt_id
      | succ j =>
          simp only [Fin.cons_succ]
          exact analyticAt_iteratedDeriv_of_analyticAt hf (j : ℕ)

theorem differentialRelation_digammaGamma_propagates
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ digammaGammaRegularSet)
    (hrel : ∀ z ∈ V, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
        (fun s => Complex.digamma (Complex.Gamma s)) z)) P = 0) :
    ∀ z ∈ digammaGammaRegularSet, MvPolynomial.eval
      (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
        (fun s => Complex.digamma (Complex.Gamma s)) z)) P = 0 := by
  let E : ℂ → ℂ := fun z => MvPolynomial.eval
    (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
      (fun s => Complex.digamma (Complex.Gamma s)) z)) P
  obtain ⟨z₀, hz₀V⟩ := hVne
  have hz₀reg : z₀ ∈ digammaGammaRegularSet := hVreg hz₀V
  have han : AnalyticOnNhd ℂ E digammaGammaRegularSet := by
    intro z hz
    exact analyticAt_digammaGammaDifferentialEval n P hz
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in 𝓝 z₀, E z = 0 := by
    filter_upwards [hVopen.mem_nhds hz₀V] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    digammaGammaRegularSet_isPreconnected hz₀reg hfreq

theorem factorialInitialForm_vanishes_of_eventually_rescaled_relations {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (x : ℂ)
    (G : ℕ → Fin (r + 1) → ℂ) (J : Fin (r + 1) → ℂ)
    (hG : ∀ j, Tendsto (fun n => G n j) atTop (𝓝 (J j)))
    (hrel : ∀ᶠ n : ℕ in atTop, ∑ α ∈ P.support,
      factorialInitialCoefficient P α n x * differentialJetMonomial (G n) α = 0) :
    MvPolynomial.eval J (factorialInitialForm P) = 0 := by
  have hlim : Tendsto
      (fun n => ∑ α ∈ P.support,
        factorialInitialCoefficient P α n x * differentialJetMonomial (G n) α)
      atTop
      (𝓝 (∑ α ∈ P.support,
        factorialInitialLimitCoefficient P α * differentialJetMonomial J α)) := by
    apply tendsto_finsetSum
    intro α hα
    exact (tendsto_factorialInitialCoefficient P hα x).mul
      (tendsto_differentialJetMonomial hG α)
  have hzero : Tendsto
      (fun n => ∑ α ∈ P.support,
        factorialInitialCoefficient P α n x * differentialJetMonomial (G n) α)
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hrel.mono fun _ hn => hn.symm)
  rw [eval_factorialInitialForm]
  exact tendsto_nhds_unique hlim hzero

theorem exists_nonzero_factorialInitialForm_of_eventual_differentialRelation
    {h f : ℂ → ℂ} {U : Set ℂ} {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (hP0 : P ≠ 0)
    (hrel : ∀ x ∈ U, ∀ᶠ n : ℕ in atTop,
      MvPolynomial.eval
        (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) h
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x))) P = 0)
    (hjet : ∀ x ∈ U, ∀ j : ℕ,
      Tendsto (fun n => iteratedDeriv j (factorialBlowUpZoom h n) x) atTop
        (𝓝 (iteratedDeriv j f x))) :
    ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q ≠ 0 ∧ ∀ x ∈ U,
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) f x) Q = 0 := by
  refine ⟨factorialInitialForm P, factorialInitialForm_ne_zero hP0, ?_⟩
  intro x hx
  apply factorialInitialForm_vanishes_of_eventually_rescaled_relations P x
    (fun n j => iteratedDeriv (j : ℕ) (factorialBlowUpZoom h n) x)
    (fun j => iteratedDeriv (j : ℕ) f x)
  · intro j
    exact hjet x hx (j : ℕ)
  · filter_upwards [hrel x hx] with n hn
    exact factorialInitialRelation_of_relation_at h P n x hn

theorem eventually_factorialBlowUp_input_digammaGammaRegular
    {x : ℂ} (hx : x ∈ reciprocalGammaBlowUpDisk) :
    ∀ᶠ n : ℕ in atTop,
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) ∈ digammaGammaRegularSet := by
  have hx0 := reciprocalGammaBlowUpDisk_ne_zero hx
  have hGamma :=
    tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.tendsto_at hx0
  have hRe : Tendsto
      (fun n : ℕ => (Complex.Gamma
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x)).re)
      atTop (𝓝 (((-x)⁻¹ : ℂ).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hGamma
  have hpos : 0 < (((-x)⁻¹ : ℂ).re) := reciprocalGammaBlowUpDisk_inv_neg_re_pos hx
  filter_upwards [hRe.eventually (Ioi_mem_nhds hpos)] with n hn
  intro m heq
  have hre := congrArg Complex.re heq
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem autonomous_annihilator_digammaReciprocalLimit_eq_zero {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (hQvan : ∀ x ∈ reciprocalGammaBlowUpDisk,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) digammaReciprocalLimit x) Q = 0) :
    Q = 0 := by
  by_contra hQ
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := mobiusJetPullback r Q
  have hGne : G ≠ 0 := mobiusJetPullback_ne_zero hQ
  have honeOff : ∀ p : ℕ, (1 : ℂ) ≠ -(p : ℂ) := by
    intro p hp
    have hre := congrArg Complex.re hp
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith
  have hphiCont : ContinuousAt (fun z : ℂ => -z⁻¹) 1 := by
    exact ContinuousAt.comp continuous_neg.continuousAt
      (ContinuousAt.inv₀ continuousAt_id (one_ne_zero : (1 : ℂ) ≠ 0))
  have hcenter : -((1 : ℂ)⁻¹) ∈ reciprocalGammaBlowUpDisk := by
    simp [reciprocalGammaBlowUpDisk]
  have hpre : ∀ᶠ z : ℂ in 𝓝 1, -z⁻¹ ∈ reciprocalGammaBlowUpDisk :=
    hphiCont (isOpen_reciprocalGammaBlowUpDisk.mem_nhds hcenter)
  have hlocal : ∀ᶠ z : ℂ in 𝓝 1, polyJetEval (r + 1) z G = 0 := by
    filter_upwards [hpre, offPoles_isOpen.mem_nhds honeOff,
      (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))]
      with z hzU hzOff hz0mem
    have hz0 : z ≠ 0 := Set.mem_compl_singleton_iff.mp hz0mem
    have hvalue := hQvan (-z⁻¹) hzU
    have hmv : mobiusJetValue r Complex.digamma z =
        fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) digammaReciprocalLimit (-z⁻¹) := by
      funext j
      exact mobiusJetValue_digamma_eq_limitJet r z hzOff hz0 j
    change MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) Complex.digamma z) G = 0
    rw [show G = mobiusJetPullback r Q from rfl, eval₂_mobiusJetPullback, hmv]
    exact hvalue
  exact hGne (polyJetEval_eq_zero_of_eventually G honeOff hlocal)

theorem no_local_differential_relation_digamma_comp_Gamma
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ digammaGammaRegularSet) :
    ¬ DifferentiallyAlgebraicOn (fun z => Complex.digamma (Complex.Gamma z)) V := by
  rintro ⟨r, P, hP0, hP⟩
  have hPreg := differentialRelation_digammaGamma_propagates
    hVopen hVne hVreg hP
  obtain ⟨Q, hQ0, hQvan⟩ :=
    exists_nonzero_factorialInitialForm_of_eventual_differentialRelation
      (h := fun z => Complex.digamma (Complex.Gamma z))
      (f := digammaReciprocalLimit) (U := reciprocalGammaBlowUpDisk) P hP0
      (fun x hx => by
        filter_upwards [eventually_factorialBlowUp_input_digammaGammaRegular hx]
          with n hn
        exact hPreg _ hn)
      (fun x hx j => iteratedDeriv_digammaGamma_factorialBlowUp_tendsto hx j)
  exact hQ0 (autonomous_annihilator_digammaReciprocalLimit_eq_zero Q hQvan)

end

end GaloisForLFunctions
