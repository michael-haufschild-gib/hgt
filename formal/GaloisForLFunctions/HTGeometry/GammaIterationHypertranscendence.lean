import GaloisForLFunctions.HTGeometry.GammaGammaLocalHypertranscendence

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

def gammaIterate : ℕ → ℂ → ℂ
  | 0 => id
  | k + 1 => fun z => gammaIterate k (Complex.Gamma z)

@[simp] theorem gammaIterate_zero (z : ℂ) : gammaIterate 0 z = z := rfl

@[simp] theorem gammaIterate_succ (k : ℕ) (z : ℂ) :
    gammaIterate (k + 1) z = gammaIterate k (Complex.Gamma z) := rfl

def gammaIterateRegularSet : ℕ → Set ℂ
  | 0 => Set.univ
  | k + 1 => {z : ℂ | (∀ m : ℕ, z ≠ -(m : ℂ)) ∧
      Complex.Gamma z ∈ gammaIterateRegularSet k}

@[simp] theorem gammaIterateRegularSet_zero : gammaIterateRegularSet 0 = Set.univ := rfl

theorem gammaIterateRegularSet_succ (k : ℕ) :
    gammaIterateRegularSet (k + 1) =
      {z : ℂ | (∀ m : ℕ, z ≠ -(m : ℂ)) ∧
        Complex.Gamma z ∈ gammaIterateRegularSet k} := rfl

theorem one_mem_gammaIterateRegularSet : ∀ k : ℕ, (1 : ℂ) ∈ gammaIterateRegularSet k
  | 0 => Set.mem_univ 1
  | k + 1 => by
      rw [gammaIterateRegularSet_succ]
      refine ⟨?_, ?_⟩
      · intro m hm
        have hre := congrArg Complex.re hm
        simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      · simpa using one_mem_gammaIterateRegularSet k

@[simp] theorem gammaIterate_one : ∀ k : ℕ, gammaIterate k 1 = 1
  | 0 => rfl
  | k + 1 => by simp [gammaIterate, gammaIterate_one k]

theorem analyticAt_gammaIterate : ∀ {k : ℕ} {z : ℂ},
    z ∈ gammaIterateRegularSet k → AnalyticAt ℂ (gammaIterate k) z
  | 0, z, _ => by simpa [gammaIterate] using (analyticAt_id : AnalyticAt ℂ id z)
  | k + 1, z, hz => by
      rw [gammaIterateRegularSet_succ] at hz
      exact AnalyticAt.comp (f := Complex.Gamma) (x := z)
        (analyticAt_gammaIterate hz.2) (analyticAt_Gamma z hz.1)

theorem isOpen_gammaIterateRegularSet : ∀ k : ℕ, IsOpen (gammaIterateRegularSet k)
  | 0 => isOpen_univ
  | k + 1 => by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      rw [gammaIterateRegularSet_succ] at hz ⊢
      have hGamma := (analyticAt_Gamma z hz.1).continuousAt
      exact inter_mem (offPoles_isOpen.mem_nhds hz.1)
        (hGamma ((isOpen_gammaIterateRegularSet k).mem_nhds hz.2))

theorem gammaFiber_countable (c : ℂ) :
    {z : ℂ | Complex.Gamma z = c}.Countable := by
  let Ω : Set ℂ := {z : ℂ | ∀ n : ℕ, z ≠ -(n : ℂ)}
  let f : ℂ → ℂ := fun z => Complex.Gamma z - c
  have hΩconn : IsConnected Ω := by
    refine ⟨⟨1, ?_⟩, offPoles_isPreconnected⟩
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfan : AnalyticOnNhd ℂ f Ω := by
    intro z hz
    exact (analyticAt_Gamma z hz).sub analyticAt_const
  have hΩcompl : Ωᶜ.Countable := by
    have heq : Ωᶜ = Set.range (fun n : ℕ => (-(n : ℂ))) := by
      ext z
      simp only [Ω, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_ne_iff,
        Set.mem_range]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, hn.symm⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, hn.symm⟩
    rw [heq]
    exact Set.countable_range _
  obtain ⟨z₀, hz₀Ω, hfz₀⟩ : ∃ z₀ : ℂ, z₀ ∈ Ω ∧ f z₀ ≠ 0 := by
    by_cases hc : c = 1
    · refine ⟨3, ?_, ?_⟩
      · intro n hn
        have hre := congrArg Complex.re hn
        norm_num at hre
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · subst c
        norm_num [f, Complex.Gamma_nat_eq_factorial]
    · refine ⟨1, ?_, ?_⟩
      · intro n hn
        have hre := congrArg Complex.re hn
        simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · simpa [f] using sub_ne_zero.mpr (Ne.symm hc)
  have hcodiscrete : f ⁻¹' {0}ᶜ ∈ codiscreteWithin Ω :=
    hfan.preimage_zero_mem_codiscreteWithin hfz₀ hz₀Ω hΩconn
  have hdisc : IsDiscrete (f ⁻¹' {0} ∩ Ω) :=
    isDiscrete_of_codiscreteWithin hcodiscrete
  have hzeroCount : (f ⁻¹' {0} ∩ Ω).Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  apply (hΩcompl.union hzeroCount).mono
  intro z hz
  by_cases hzΩ : z ∈ Ω
  · right
    refine ⟨?_, hzΩ⟩
    change Complex.Gamma z - c = 0
    rw [hz]
    ring
  · exact Or.inl hzΩ

theorem gamma_preimage_countable {S : Set ℂ} (hS : S.Countable) :
    (Complex.Gamma ⁻¹' S).Countable := by
  letI := hS.to_subtype
  have heq : Complex.Gamma ⁻¹' S =
      ⋃ c : S, {z : ℂ | Complex.Gamma z = c.1} := by
    ext z
    simp
  rw [heq]
  exact Set.countable_iUnion fun c => gammaFiber_countable c.1

theorem gammaIterateRegularSet_compl_countable : ∀ k : ℕ,
    (gammaIterateRegularSet k)ᶜ.Countable
  | 0 => by simp
  | k + 1 => by
      have hpoles : ({z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)}ᶜ).Countable := by
        have heq : {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)}ᶜ =
            Set.range (fun m : ℕ => (-(m : ℂ))) := by
          ext z
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_ne_iff,
            Set.mem_range]
          constructor
          · rintro ⟨m, hm⟩
            exact ⟨m, hm.symm⟩
          · rintro ⟨m, hm⟩
            exact ⟨m, hm.symm⟩
        rw [heq]
        exact Set.countable_range _
      have hpre := gamma_preimage_countable (gammaIterateRegularSet_compl_countable k)
      have hsub : (gammaIterateRegularSet (k + 1))ᶜ ⊆
          {z : ℂ | ∀ m : ℕ, z ≠ -(m : ℂ)}ᶜ ∪
            Complex.Gamma ⁻¹' (gammaIterateRegularSet k)ᶜ := by
        intro z hz
        rw [gammaIterateRegularSet_succ] at hz
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hz
        exact hz
      exact (hpoles.union hpre).mono hsub

theorem gammaIterateRegularSet_isPreconnected (k : ℕ) :
    IsPreconnected (gammaIterateRegularSet k) := by
  rw [show gammaIterateRegularSet k = (gammaIterateRegularSet k)ᶜᶜ by simp]
  refine (Set.Countable.isPathConnected_compl_of_one_lt_rank ?_
    (gammaIterateRegularSet_compl_countable k)).isConnected.isPreconnected
  rw [Complex.rank_real_complex]
  norm_num

def localGammaMicroscopeDomain (Ω : Set ℂ) : Set ℂ :=
  {x : ℂ | x ≠ 0 ∧ (-x)⁻¹ ∈ Ω}

theorem isOpen_localGammaMicroscopeDomain {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsOpen (localGammaMicroscopeDomain Ω) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := hx.1
  have hphi : ContinuousAt (fun y : ℂ => (-y)⁻¹) x :=
    continuousAt_neg.inv₀ (neg_ne_zero.mpr hx0)
  have hzero : {y : ℂ | y ≠ 0} ∈ 𝓝 x :=
    isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hx0)
  have himage : {y : ℂ | (-y)⁻¹ ∈ Ω} ∈ 𝓝 x :=
    hphi (hΩ.mem_nhds hx.2)
  simpa [localGammaMicroscopeDomain, Set.setOf_and] using inter_mem hzero himage

theorem neg_one_mem_localGammaMicroscopeDomain {Ω : Set ℂ} (h1 : (1 : ℂ) ∈ Ω) :
    (-1 : ℂ) ∈ localGammaMicroscopeDomain Ω := by
  refine ⟨by norm_num, ?_⟩
  simpa using h1

theorem tendsto_outer_Gamma_factorialBlowUp_locallyUniformlyOn_local
    (u : ℂ → ℂ) {Ω : Set ℂ} (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z) :
    TendstoLocallyUniformlyOn
      (fun (n : ℕ) (x : ℂ) => u
        (Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x)))
      (outerReciprocalLimit u) atTop (localGammaMicroscopeDomain Ω) := by
  have hGamma := tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.mono
    (fun (x : ℂ) (hx : x ∈ localGammaMicroscopeDomain Ω) => hx.1)
  have hlimit : ContinuousOn (fun x : ℂ => (-x)⁻¹) (localGammaMicroscopeDomain Ω) :=
    continuous_neg.continuousOn.inv₀ (fun x hx => neg_ne_zero.mpr hx.1)
  apply continuousAt_comp_tendstoLocallyUniformlyOn _ hlimit hGamma
  intro x hx
  exact (hu ((-x)⁻¹) hx.2).continuousAt

theorem exists_eventually_differentiable_outerGammaZoom_near_local
    (u : ℂ → ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z)
    {x : ℂ} (hx : x ∈ localGammaMicroscopeDomain Ω) :
    ∃ V : Set ℂ, IsOpen V ∧ x ∈ V ∧ V ⊆ localGammaMicroscopeDomain Ω ∧
      ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ
        (factorialBlowUpZoom (fun z => u (Complex.Gamma z)) n) V := by
  let limit : ℂ → ℂ := fun y => (-y)⁻¹
  have hx0 : x ≠ 0 := hx.1
  have hlimitx0 : limit x ≠ 0 := inv_ne_zero (neg_ne_zero.mpr hx0)
  have hlimitAt : ContinuousAt limit x :=
    continuousAt_neg.inv₀ (neg_ne_zero.mpr hx0)
  obtain ⟨ε, hε, huBall⟩ := (hu (limit x) hx.2).exists_ball_analyticOnNhd
  let ρ : ℝ := min ε ‖limit x‖ / 4
  have hnorm : 0 < ‖limit x‖ := norm_pos_iff.mpr hlimitx0
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have h2ρeps : 2 * ρ < ε := by
    have hmin : min ε ‖limit x‖ ≤ ε := min_le_left _ _
    dsimp [ρ]
    linarith
  have h2ρnorm : 2 * ρ < ‖limit x‖ := by
    have hmin : min ε ‖limit x‖ ≤ ‖limit x‖ := min_le_right _ _
    dsimp [ρ]
    linarith
  rw [Metric.continuousAt_iff] at hlimitAt
  obtain ⟨δ, hδ, hlimitMap⟩ := hlimitAt ρ hρ
  have hGammaOn : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (y : ℂ) =>
        Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * y))
      limit atTop (localGammaMicroscopeDomain Ω) :=
    tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.mono (fun y hy => hy.1)
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hGammaOn
  obtain ⟨t, ht, hGt⟩ := hGammaOn ρ hρ x hx
  rw [(isOpen_localGammaMicroscopeDomain hΩ).nhdsWithin_eq hx] at ht
  have hnbhd : t ∩ Metric.ball x δ ∩ localGammaMicroscopeDomain Ω ∈ 𝓝 x :=
    inter_mem (inter_mem ht (Metric.ball_mem_nhds x hδ))
      ((isOpen_localGammaMicroscopeDomain hΩ).mem_nhds hx)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hnbhd
  refine ⟨V, hVopen, hxV, fun y hy => (hVsub hy).2, ?_⟩
  filter_upwards [hGt] with n hn
  intro y hy
  have hyall := hVsub hy
  have hyt : y ∈ t := hyall.1.1
  have hyball : y ∈ Metric.ball x δ := hyall.1.2
  let input : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * y
  let gammaValue : ℂ := Complex.Gamma input
  have hcloseGamma : dist (limit y) gammaValue < ρ := hn y hyt
  have hcloseLimit : dist (limit y) (limit x) < ρ := hlimitMap hyball
  have hclose : dist gammaValue (limit x) < 2 * ρ := by
    calc
      dist gammaValue (limit x) ≤ dist gammaValue (limit y) + dist (limit y) (limit x) :=
        dist_triangle _ _ _
      _ < 2 * ρ := by rw [dist_comm gammaValue (limit y)]; linarith
  have hgammaBall : gammaValue ∈ Metric.ball (limit x) ε := by
    rw [Metric.mem_ball]
    exact lt_trans hclose h2ρeps
  have hgamma0 : gammaValue ≠ 0 := by
    intro hzero
    rw [hzero, dist_zero_left] at hclose
    exact (not_lt_of_ge (le_of_lt h2ρnorm)) hclose
  have hinputRegular : ∀ m : ℕ, input ≠ -(m : ℂ) := by
    intro m heq
    have hzero : gammaValue = 0 := by
      simp [gammaValue, input, heq, Complex.Gamma_neg_nat_eq_zero]
    exact hgamma0 hzero
  have hinputDiff : DifferentiableAt ℂ (fun z : ℂ =>
      -(n : ℂ) + reciprocalGammaFactorialScale n * z) y := by fun_prop
  have hGammaDiff : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * z)) y :=
    (Complex.differentiableAt_Gamma input hinputRegular).comp y hinputDiff
  have huDiff : DifferentiableAt ℂ u gammaValue :=
    (huBall gammaValue hgammaBall).differentiableAt
  have hcomp := huDiff.comp y hGammaDiff
  simpa [factorialBlowUpZoom, input, gammaValue, Function.comp_def] using!
    hcomp.differentiableWithinAt

theorem iteratedDeriv_outerGamma_factorialBlowUp_tendsto_local
    (u : ℂ → ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z)
    {x : ℂ} (hx : x ∈ localGammaMicroscopeDomain Ω) (j : ℕ) :
    Tendsto
      (fun n => iteratedDeriv j
        (factorialBlowUpZoom (fun z => u (Complex.Gamma z)) n) x)
      atTop (𝓝 (iteratedDeriv j (outerReciprocalLimit u) x)) := by
  obtain ⟨V, hVopen, hxV, hVU, hdiff⟩ :=
    exists_eventually_differentiable_outerGammaZoom_near_local u hΩ hu hx
  have hconv :=
    (tendsto_outer_Gamma_factorialBlowUp_locallyUniformlyOn_local u hu).mono hVU
  exact iteratedDeriv_tendsto_of_locallyUniform hVopen hconv hdiff j hxV

theorem mobiusJetValue_outer_eq_limitJet_local
    {u : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z)
    (r : ℕ) {z : ℂ} (hz : z ∈ Ω) (hz0 : z ≠ 0) (j : Fin (r + 1)) :
    mobiusJetValue r u z j =
      iteratedDeriv (j : ℕ) (outerReciprocalLimit u) (-z⁻¹) := by
  rw [mobiusJetValue_eq_mobiusJetExpansion]
  exact (iteratedDeriv_outerReciprocalLimit_neg_inv_eq_mobiusJetExpansion_local
    hΩ hu (j : ℕ) z hz hz0).symm

theorem no_eventual_differential_relation_outer_comp_Gamma_local
    (u : ℂ → ℂ) {Ω : Set ℂ} (hΩ : IsOpen Ω) (h1 : (1 : ℂ) ∈ Ω)
    (hu : ∀ z ∈ Ω, AnalyticAt ℂ u z)
    (hrigid : LocallyPolynomialJetRigidAt u 1)
    {r : ℕ} (P : MvPolynomial (Fin (r + 2)) ℂ) (hP0 : P ≠ 0) :
    ¬ ∀ x ∈ localGammaMicroscopeDomain Ω, ∀ᶠ n : ℕ in atTop,
      MvPolynomial.eval
        (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x)
          (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ)
            (fun z => u (Complex.Gamma z))
            (-(n : ℂ) + reciprocalGammaFactorialScale n * x))) P = 0 := by
  intro hrel
  obtain ⟨Q, hQ0, hQvan⟩ :=
    exists_nonzero_factorialInitialForm_of_eventual_differentialRelation
      (h := fun z => u (Complex.Gamma z))
      (f := outerReciprocalLimit u) (U := localGammaMicroscopeDomain Ω) P hP0 hrel
      (fun x hx j => iteratedDeriv_outerGamma_factorialBlowUp_tendsto_local
        u hΩ hu hx j)
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := mobiusJetPullback r Q
  have hGne : G ≠ 0 := mobiusJetPullback_ne_zero hQ0
  apply (hrigid r G hGne)
  have hzeroNhd : {z : ℂ | z ≠ 0} ∈ 𝓝 1 :=
    isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (one_ne_zero : (1 : ℂ) ≠ 0))
  filter_upwards [hΩ.mem_nhds h1, hzeroNhd] with z hzΩ hz0
  have hx0 : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz0)
  have hxΩ : (-(-z⁻¹))⁻¹ ∈ Ω := by
    rw [neg_inv_neg_inv hz0]
    exact hzΩ
  have hx : -z⁻¹ ∈ localGammaMicroscopeDomain Ω := ⟨hx0, hxΩ⟩
  have hvalue := hQvan (-z⁻¹) hx
  have hmv : mobiusJetValue r u z =
      fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (outerReciprocalLimit u) (-z⁻¹) := by
    funext j
    exact mobiusJetValue_outer_eq_limitJet_local hΩ hu r hzΩ hz0 j
  rw [show G = mobiusJetPullback r Q from rfl, eval₂_mobiusJetPullback, hmv]
  exact hvalue

def gammaIteratePolyJetEval (k m : ℕ) (z : ℂ) :
    MvPolynomial (Fin m) (Polynomial ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.evalRingHom z)
    (fun j => iteratedDeriv (j : ℕ) (gammaIterate k) z)

theorem analyticAt_gammaIteratePolyJetEval {k m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ)) {z : ℂ}
    (hz : z ∈ gammaIterateRegularSet k) :
    AnalyticAt ℂ (fun w => gammaIteratePolyJetEval k m w G) z := by
  have hf := analyticAt_gammaIterate hz
  induction G using MvPolynomial.induction_on with
  | C p =>
      have heq : (fun w => gammaIteratePolyJetEval k m w (MvPolynomial.C p)) =
          fun w => p.eval w := by
        funext w
        simp [gammaIteratePolyJetEval]
      rw [heq]
      exact (AnalyticOnNhd.eval_polynomial p) z (Set.mem_univ z)
  | add P Q hP hQ =>
      have heq : (fun w => gammaIteratePolyJetEval k m w (P + Q)) =
          fun w => gammaIteratePolyJetEval k m w P +
            gammaIteratePolyJetEval k m w Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => gammaIteratePolyJetEval k m w (P * MvPolynomial.X i)) =
          fun w => gammaIteratePolyJetEval k m w P *
            iteratedDeriv (i : ℕ) (gammaIterate k) w := by
        funext w
        simp [gammaIteratePolyJetEval]
      rw [heq]
      exact hP.mul (analyticAt_iteratedDeriv_of_analyticAt hf (i : ℕ))

theorem gammaIteratePolyJetEval_propagates {k m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ))
    (hlocal : ∀ᶠ z in 𝓝 1, gammaIteratePolyJetEval k m z G = 0) :
    ∀ z ∈ gammaIterateRegularSet k, gammaIteratePolyJetEval k m z G = 0 := by
  let E : ℂ → ℂ := fun z => gammaIteratePolyJetEval k m z G
  have han : AnalyticOnNhd ℂ E (gammaIterateRegularSet k) := by
    intro z hz
    exact analyticAt_gammaIteratePolyJetEval G hz
  letI : NeBot (𝓝[≠] (1 : ℂ)) := NormedField.nhdsNE_neBot 1
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (gammaIterateRegularSet_isPreconnected k)
    (one_mem_gammaIterateRegularSet k) hfreq

theorem zero_not_mem_gammaIterateRegularSet {k : ℕ} (hk : 1 ≤ k) :
    (0 : ℂ) ∉ gammaIterateRegularSet k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 1 + j = j + 1 by omega, gammaIterateRegularSet_succ]
  intro h
  exact h.1 0 (by norm_num)

theorem eventually_factorialBlowUp_input_gammaIterateRegular
    {k : ℕ} (hk : 1 ≤ k) {x : ℂ}
    (hx : x ∈ localGammaMicroscopeDomain (gammaIterateRegularSet k)) :
    ∀ᶠ n : ℕ in atTop,
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) ∈
        gammaIterateRegularSet (k + 1) := by
  have hGamma :=
    tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.tendsto_at hx.1
  have hmem : ∀ᶠ n : ℕ in atTop,
      Complex.Gamma (-(n : ℂ) + reciprocalGammaFactorialScale n * x) ∈
        gammaIterateRegularSet k :=
    hGamma.eventually ((isOpen_gammaIterateRegularSet k).mem_nhds hx.2)
  filter_upwards [hmem] with n hn
  rw [gammaIterateRegularSet_succ]
  refine ⟨?_, hn⟩
  intro m heq
  have hzero : Complex.Gamma
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) = 0 := by
    rw [heq, Complex.Gamma_neg_nat_eq_zero]
  rw [hzero] at hn
  exact zero_not_mem_gammaIterateRegularSet hk hn

theorem hypertranscendental_of_locallyPolynomialJetRigidAt
    {u : ℂ → ℂ} (hrigid : LocallyPolynomialJetRigidAt u 1) :
    Hypertranscendental u := by
  rintro ⟨r, P, hP0, hP⟩
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := reshapeJet r P
  have hG : G ≠ 0 := by
    exact fun hzero => hP0 (reshapeJet_injective r (by simpa [G] using hzero))
  apply (hrigid r G hG)
  filter_upwards [] with z
  rw [show G = reshapeJet r P from rfl, eval₂_reshapeJet]
  exact hP z

theorem locallyPolynomialJetRigidAt_gammaIterate_succ
    {k : ℕ} (hk : 1 ≤ k)
    (hrigid : LocallyPolynomialJetRigidAt (gammaIterate k) 1) :
    LocallyPolynomialJetRigidAt (gammaIterate (k + 1)) 1 := by
  intro r G hG hlocal
  let P : MvPolynomial (Fin (r + 2)) ℂ := reshapeJetInv r G
  have hP0 : P ≠ 0 := by
    intro hP
    apply hG
    apply reshapeJetInv_injective r
    simpa [P] using hP
  have hreshape : reshapeJet r P = G := by
    exact RingHom.congr_fun (reshapeJet_comp_reshapeJetInv r) G
  have hprop : ∀ z ∈ gammaIterateRegularSet (k + 1),
      gammaIteratePolyJetEval (k + 1) (r + 1) z G = 0 :=
    gammaIteratePolyJetEval_propagates G (by
      simpa [gammaIteratePolyJetEval] using hlocal)
  apply no_eventual_differential_relation_outer_comp_Gamma_local
    (gammaIterate k) (isOpen_gammaIterateRegularSet k)
    (one_mem_gammaIterateRegularSet k) (fun z hz => analyticAt_gammaIterate hz)
    hrigid P hP0
  intro x hx
  filter_upwards [eventually_factorialBlowUp_input_gammaIterateRegular hk hx] with n hn
  let z : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  let v : Fin (r + 1) → ℂ :=
    fun j => iteratedDeriv (j : ℕ) (gammaIterate (k + 1)) z
  have hGzero : MvPolynomial.eval₂ (Polynomial.evalRingHom z) v G = 0 := by
    simpa [gammaIteratePolyJetEval, z, v] using hprop z hn
  change MvPolynomial.eval (Fin.cons z v) P = 0
  rw [← eval₂_reshapeJet r z v P, hreshape]
  exact hGzero

theorem locallyPolynomialJetRigidAt_gammaIterate :
    ∀ (k : ℕ), 1 ≤ k → LocallyPolynomialJetRigidAt (gammaIterate k) 1
  | 0, hk => by omega
  | k + 1, _ => by
      by_cases hk0 : k = 0
      · subst k
        simpa [gammaIterate] using locallyPolynomialJetRigidAt_Gamma
      · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        exact locallyPolynomialJetRigidAt_gammaIterate_succ hk
          (locallyPolynomialJetRigidAt_gammaIterate k hk)

theorem hypertranscendental_gammaIterate (k : ℕ) (hk : 1 ≤ k) :
    Hypertranscendental (gammaIterate k) :=
  hypertranscendental_of_locallyPolynomialJetRigidAt
    (locallyPolynomialJetRigidAt_gammaIterate k hk)

theorem gammaIteratePolyJetEval_propagates_from_open
    {k m : ℕ} (G : MvPolynomial (Fin m) (Polynomial ℂ))
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ gammaIterateRegularSet k)
    (hrel : ∀ z ∈ V, gammaIteratePolyJetEval k m z G = 0) :
    ∀ z ∈ gammaIterateRegularSet k, gammaIteratePolyJetEval k m z G = 0 := by
  let E : ℂ → ℂ := fun z => gammaIteratePolyJetEval k m z G
  obtain ⟨z₀, hz₀V⟩ := hVne
  have hz₀reg : z₀ ∈ gammaIterateRegularSet k := hVreg hz₀V
  have han : AnalyticOnNhd ℂ E (gammaIterateRegularSet k) := by
    intro z hz
    exact analyticAt_gammaIteratePolyJetEval G hz
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in 𝓝 z₀, E z = 0 := by
    filter_upwards [hVopen.mem_nhds hz₀V] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (gammaIterateRegularSet_isPreconnected k) hz₀reg hfreq

theorem no_local_differential_relation_gammaIterate
    {k : ℕ} (hk : 1 ≤ k)
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ gammaIterateRegularSet k) :
    ¬ DifferentiallyAlgebraicOn (gammaIterate k) V := by
  rintro ⟨r, P, hP0, hP⟩
  let G : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := reshapeJet r P
  have hG : G ≠ 0 := by
    intro hzero
    apply hP0
    apply reshapeJet_injective r
    simpa [G] using hzero
  have hrelG : ∀ z ∈ V, gammaIteratePolyJetEval k (r + 1) z G = 0 := by
    intro z hz
    change MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun j : Fin (r + 1) => iteratedDeriv (j : ℕ) (gammaIterate k) z)
      (reshapeJet r P) = 0
    rw [eval₂_reshapeJet]
    exact hP z hz
  have hprop := gammaIteratePolyJetEval_propagates_from_open
    G hVopen hVne hVreg hrelG
  apply (locallyPolynomialJetRigidAt_gammaIterate k hk r G hG)
  filter_upwards [(isOpen_gammaIterateRegularSet k).mem_nhds
    (one_mem_gammaIterateRegularSet k)] with z hz
  exact hprop z hz

end

end GaloisForLFunctions
