import GaloisForLFunctions.HTGeometry.GammaIterationHypertranscendence

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

theorem gammaIterateRegularSet_succ_subset : ∀ k : ℕ,
    gammaIterateRegularSet (k + 1) ⊆ gammaIterateRegularSet k
  | 0 => Set.subset_univ _
  | k + 1 => by
      intro z hz
      rw [gammaIterateRegularSet_succ] at hz ⊢
      exact ⟨hz.1, gammaIterateRegularSet_succ_subset k hz.2⟩

theorem gammaIterateRegularSet_antitone : Antitone gammaIterateRegularSet :=
  antitone_nat_of_succ_le gammaIterateRegularSet_succ_subset

def gammaIterateTuple (k : ℕ) (z : ℂ) : Fin (k + 1) → ℂ :=
  Fin.cons z (fun j : Fin k => gammaIterate ((j : ℕ) + 1) z)

theorem gammaIterateTuple_apply (k : ℕ) (z : ℂ) (i : Fin (k + 1)) :
    gammaIterateTuple k z i = gammaIterate (i : ℕ) z := by
  induction i using Fin.cases with
  | zero => simp [gammaIterateTuple, gammaIterate]
  | succ j => simp [gammaIterateTuple]

theorem eval₂_function_apply {ι : Type*} (f : ι → (ℂ → ℂ))
    (P : MvPolynomial ι ℂ) (z : ℂ) :
    (MvPolynomial.eval₂ (algebraMap ℂ (ℂ → ℂ)) f P) z =
      MvPolynomial.eval (fun i => f i z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP]

def LocallyAlgebraicallyIndependentGammaIterates (k : ℕ) : Prop :=
  ∀ P : MvPolynomial (Fin (k + 1)) ℂ, P ≠ 0 →
    ¬ ∀ᶠ z : ℂ in 𝓝 1, MvPolynomial.eval (gammaIterateTuple k z) P = 0

theorem analyticAt_gammaIterateTupleCoordinate {k : ℕ} {z : ℂ}
    (hz : z ∈ gammaIterateRegularSet k) (i : Fin (k + 1)) :
    AnalyticAt ℂ (fun w => gammaIterateTuple k w i) z := by
  induction i using Fin.cases with
  | zero => simpa [gammaIterateTuple] using (analyticAt_id : AnalyticAt ℂ id z)
  | succ j =>
      have hj : (j : ℕ) + 1 ≤ k := by omega
      have hzj : z ∈ gammaIterateRegularSet ((j : ℕ) + 1) :=
        gammaIterateRegularSet_antitone hj hz
      simpa [gammaIterateTuple] using analyticAt_gammaIterate hzj

theorem analyticAt_gammaIterateTupleEval {k : ℕ}
    (P : MvPolynomial (Fin (k + 1)) ℂ) {z : ℂ}
    (hz : z ∈ gammaIterateRegularSet k) :
    AnalyticAt ℂ (fun w => MvPolynomial.eval (gammaIterateTuple k w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) z)
  | add P Q hP hQ =>
      have heq : (fun w => MvPolynomial.eval (gammaIterateTuple k w) (P + Q)) =
          fun w => MvPolynomial.eval (gammaIterateTuple k w) P +
            MvPolynomial.eval (gammaIterateTuple k w) Q := by
        funext w
        simp
      rw [heq]
      exact hP.add hQ
  | mul_X P i hP =>
      have heq : (fun w => MvPolynomial.eval (gammaIterateTuple k w)
          (P * MvPolynomial.X i)) =
          fun w => MvPolynomial.eval (gammaIterateTuple k w) P *
            gammaIterateTuple k w i := by
        funext w
        simp
      rw [heq]
      exact hP.mul (analyticAt_gammaIterateTupleCoordinate hz i)

theorem gammaIterateTupleRelation_propagates_from_open
    {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℂ)
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ gammaIterateRegularSet k)
    (hrel : ∀ z ∈ V, MvPolynomial.eval (gammaIterateTuple k z) P = 0) :
    ∀ z ∈ gammaIterateRegularSet k,
      MvPolynomial.eval (gammaIterateTuple k z) P = 0 := by
  let E : ℂ → ℂ := fun z => MvPolynomial.eval (gammaIterateTuple k z) P
  obtain ⟨z₀, hz₀V⟩ := hVne
  have hz₀reg : z₀ ∈ gammaIterateRegularSet k := hVreg hz₀V
  have han : AnalyticOnNhd ℂ E (gammaIterateRegularSet k) := by
    intro z hz
    exact analyticAt_gammaIterateTupleEval P hz
  letI : NeBot (𝓝[≠] z₀) := NormedField.nhdsNE_neBot z₀
  have hlocal : ∀ᶠ z in 𝓝 z₀, E z = 0 := by
    filter_upwards [hVopen.mem_nhds hz₀V] with z hz
    exact hrel z hz
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (gammaIterateRegularSet_isPreconnected k) hz₀reg hfreq

theorem gammaIterateTupleRelation_propagates
    {k : ℕ} (P : MvPolynomial (Fin (k + 1)) ℂ)
    (hlocal : ∀ᶠ z in 𝓝 1, MvPolynomial.eval (gammaIterateTuple k z) P = 0) :
    ∀ z ∈ gammaIterateRegularSet k,
      MvPolynomial.eval (gammaIterateTuple k z) P = 0 := by
  let E : ℂ → ℂ := fun z => MvPolynomial.eval (gammaIterateTuple k z) P
  have han : AnalyticOnNhd ℂ E (gammaIterateRegularSet k) := by
    intro z hz
    exact analyticAt_gammaIterateTupleEval P hz
  letI : NeBot (𝓝[≠] (1 : ℂ)) := NormedField.nhdsNE_neBot 1
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), E z = 0 :=
    (hlocal.filter_mono nhdsWithin_le_nhds).frequently
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (gammaIterateRegularSet_isPreconnected k)
    (one_mem_gammaIterateRegularSet k) hfreq

theorem locallyAlgebraicallyIndependentGammaIterates_one :
    LocallyAlgebraicallyIndependentGammaIterates 1 := by
  intro P hP hlocal
  let G : MvPolynomial (Fin 1) (Polynomial ℂ) := reshapeJet 0 P
  have hG : G ≠ 0 := fun hzero => hP (reshapeJet_injective 0 (by simpa [G] using hzero))
  apply (locallyPolynomialJetRigidAt_gammaIterate 1 (by omega) 0 G hG)
  filter_upwards [hlocal] with z hz
  have hval : MvPolynomial.eval₂ (Polynomial.evalRingHom z)
      (fun _ : Fin 1 => Complex.Gamma z) G = 0 := by
    rw [show G = reshapeJet 0 P from rfl, eval₂_reshapeJet]
    simpa [gammaIterateTuple, gammaIterate] using hz
  simpa [gammaIterate, iteratedDeriv_zero] using hval

def algebraicPolynomialTopPointDegree {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) : ℕ :=
  P.support.sup differentialMonomialPointExponent

theorem exists_algebraic_top_point_monomial {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} (hP : P ≠ 0) :
    ∃ α ∈ P.support,
      differentialMonomialPointExponent α = algebraicPolynomialTopPointDegree P := by
  have hsupp : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP
  obtain ⟨α, hα, hαtop⟩ := Finset.exists_mem_eq_sup P.support hsupp
    differentialMonomialPointExponent
  exact ⟨α, hα, hαtop.symm⟩

theorem algebraicMonomialPointExponent_le_top {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} {α : Fin (r + 2) →₀ ℕ}
    (hα : α ∈ P.support) :
    differentialMonomialPointExponent α ≤ algebraicPolynomialTopPointDegree P :=
  Finset.le_sup hα

noncomputable def algebraicFactorialInitialForm {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) : MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ α ∈ P.support.filter (fun α =>
      differentialMonomialPointExponent α = algebraicPolynomialTopPointDegree P),
    MvPolynomial.monomial (differentialJetExponent α)
      (((-1 : ℂ) ^ algebraicPolynomialTopPointDegree P) * MvPolynomial.coeff α P)

theorem algebraicFactorialInitialForm_ne_zero {r : ℕ}
    {P : MvPolynomial (Fin (r + 2)) ℂ} (hP : P ≠ 0) :
    algebraicFactorialInitialForm P ≠ 0 := by
  classical
  obtain ⟨β, hβsupp, hβpoint⟩ := exists_algebraic_top_point_monomial hP
  have hβfilter : β ∈ P.support.filter (fun α =>
      differentialMonomialPointExponent α = algebraicPolynomialTopPointDegree P) :=
    Finset.mem_filter.mpr ⟨hβsupp, hβpoint⟩
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (differentialJetExponent β)) hzero
  rw [algebraicFactorialInitialForm, MvPolynomial.coeff_sum] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single β] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (MvPolynomial.mem_support_iff.mp hβsupp)) hcoeff
  · intro α hα hαne
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro htail
    apply hαne
    exact differentialExponent_eq_of_tail_eq_of_point_eq htail
      ((Finset.mem_filter.mp hα).2.trans hβpoint.symm)
  · intro hnot
    exact (hnot hβfilter).elim

def algebraicFactorialInitialLimitCoefficient {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (α : Fin (r + 2) →₀ ℕ) : ℂ :=
  if differentialMonomialPointExponent α = algebraicPolynomialTopPointDegree P then
    (-1 : ℂ) ^ algebraicPolynomialTopPointDegree P * MvPolynomial.coeff α P
  else 0

theorem eval_algebraicFactorialInitialForm {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (y : Fin (r + 1) → ℂ) :
    MvPolynomial.eval y (algebraicFactorialInitialForm P) =
      ∑ α ∈ P.support,
        algebraicFactorialInitialLimitCoefficient P α * differentialJetMonomial y α := by
  classical
  rw [algebraicFactorialInitialForm, map_sum]
  simp only [MvPolynomial.eval_monomial]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases htop :
      differentialMonomialPointExponent α = algebraicPolynomialTopPointDegree P
  · simp [htop, algebraicFactorialInitialLimitCoefficient, differentialJetMonomial]
  · simp [htop, algebraicFactorialInitialLimitCoefficient, differentialJetMonomial]

def algebraicFactorialInitialCoefficient {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (α : Fin (r + 2) →₀ ℕ)
    (n : ℕ) (x : ℂ) : ℂ :=
  MvPolynomial.coeff α P *
    factorialBlowUpMonomialCoefficient n x 0
      (differentialMonomialPointExponent α) (algebraicPolynomialTopPointDegree P)

theorem tendsto_algebraicFactorialInitialCoefficient {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) {α : Fin (r + 2) →₀ ℕ}
    (hα : α ∈ P.support) (x : ℂ) :
    Tendsto (fun n => algebraicFactorialInitialCoefficient P α n x) atTop
      (𝓝 (algebraicFactorialInitialLimitCoefficient P α)) := by
  have hpoint := algebraicMonomialPointExponent_le_top hα
  by_cases hp :
      differentialMonomialPointExponent α = algebraicPolynomialTopPointDegree P
  · have htop := tendsto_factorialBlowUpMonomialCoefficient_top x
        (algebraicPolynomialTopPointDegree P)
    simpa [algebraicFactorialInitialCoefficient,
      algebraicFactorialInitialLimitCoefficient, hp, mul_comm] using
      htop.const_mul (MvPolynomial.coeff α P)
  · have hplt :
        differentialMonomialPointExponent α < algebraicPolynomialTopPointDegree P :=
      lt_of_le_of_ne hpoint hp
    have hzero := tendsto_factorialBlowUpMonomialCoefficient_of_pointExponent_lt x hplt
    simpa [algebraicFactorialInitialCoefficient,
      algebraicFactorialInitialLimitCoefficient, hp] using
      hzero.const_mul (MvPolynomial.coeff α P)

theorem algebraicFactorialInitialForm_vanishes_of_rescaled_relations {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (x : ℂ)
    (G : ℕ → Fin (r + 1) → ℂ) (J : Fin (r + 1) → ℂ)
    (hG : ∀ j, Tendsto (fun n => G n j) atTop (𝓝 (J j)))
    (hrel : ∀ᶠ n : ℕ in atTop, ∑ α ∈ P.support,
      algebraicFactorialInitialCoefficient P α n x *
        differentialJetMonomial (G n) α = 0) :
    MvPolynomial.eval J (algebraicFactorialInitialForm P) = 0 := by
  have hlim : Tendsto
      (fun n => ∑ α ∈ P.support,
        algebraicFactorialInitialCoefficient P α n x *
          differentialJetMonomial (G n) α)
      atTop
      (𝓝 (∑ α ∈ P.support,
        algebraicFactorialInitialLimitCoefficient P α *
          differentialJetMonomial J α)) := by
    apply tendsto_finsetSum
    intro α hα
    exact (tendsto_algebraicFactorialInitialCoefficient P hα x).mul
      (tendsto_differentialJetMonomial hG α)
  have hzero : Tendsto
      (fun n => ∑ α ∈ P.support,
        algebraicFactorialInitialCoefficient P α n x *
          differentialJetMonomial (G n) α)
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hrel.mono fun _ hn => hn.symm)
  rw [eval_algebraicFactorialInitialForm]
  exact tendsto_nhds_unique hlim hzero

theorem algebraicFactorialInitialRelation_of_relation_at {r : ℕ}
    (P : MvPolynomial (Fin (r + 2)) ℂ) (n : ℕ) (x : ℂ)
    (y : Fin (r + 1) → ℂ)
    (hP : MvPolynomial.eval
      (Fin.cons (-(n : ℂ) + reciprocalGammaFactorialScale n * x) y) P = 0) :
    ∑ α ∈ P.support,
      algebraicFactorialInitialCoefficient P α n x *
        differentialJetMonomial y α = 0 := by
  let point : ℂ := -(n : ℂ) + reciprocalGammaFactorialScale n * x
  calc
    (∑ α ∈ P.support,
      algebraicFactorialInitialCoefficient P α n x * differentialJetMonomial y α) =
        (1 / (((n + 1 : ℕ) : ℂ) ^ algebraicPolynomialTopPointDegree P)) *
          ∑ α ∈ P.support, MvPolynomial.coeff α P *
            (point ^ differentialMonomialPointExponent α *
              differentialJetMonomial y α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α hα
      rw [algebraicFactorialInitialCoefficient,
        factorialBlowUpMonomialCoefficient]
      simp only [pow_zero, one_mul]
      dsimp only [point]
      ring
    _ = (1 / (((n + 1 : ℕ) : ℂ) ^ algebraicPolynomialTopPointDegree P)) *
        MvPolynomial.eval (Fin.cons point y) P := by
      rw [eval_differentialPolynomial_as_sum]
    _ = 0 := by rw [show MvPolynomial.eval (Fin.cons point y) P = 0 by
      simpa [point] using hP, mul_zero]

theorem tendsto_gammaIterate_succ_factorialBlowUp
    {k : ℕ} {x : ℂ}
    (hx : x ∈ localGammaMicroscopeDomain (gammaIterateRegularSet k))
    (j : Fin (k + 1)) :
    Tendsto
      (fun n : ℕ => gammaIterate ((j : ℕ) + 1)
        (-(n : ℂ) + reciprocalGammaFactorialScale n * x))
      atTop (𝓝 (gammaIterate (j : ℕ) ((-x)⁻¹))) := by
  have hj : (j : ℕ) ≤ k := Nat.le_of_lt_succ j.isLt
  have hxj : (-x)⁻¹ ∈ gammaIterateRegularSet (j : ℕ) :=
    gammaIterateRegularSet_antitone hj hx.2
  have hGamma :=
    tendsto_Gamma_factorialBlowUp_locallyUniformlyOn_ne_zero.tendsto_at hx.1
  have hcomp := (analyticAt_gammaIterate hxj).continuousAt.tendsto.comp hGamma
  simpa [gammaIterate] using hcomp

theorem locallyAlgebraicallyIndependentGammaIterates_succ
    {k : ℕ} (hk : 1 ≤ k)
    (hind : LocallyAlgebraicallyIndependentGammaIterates k) :
    LocallyAlgebraicallyIndependentGammaIterates (k + 1) := by
  intro P hP hlocal
  have hprop : ∀ z ∈ gammaIterateRegularSet (k + 1),
      MvPolynomial.eval (gammaIterateTuple (k + 1) z) P = 0 :=
    gammaIterateTupleRelation_propagates P hlocal
  let Q : MvPolynomial (Fin (k + 1)) ℂ := algebraicFactorialInitialForm P
  have hQ : Q ≠ 0 := algebraicFactorialInitialForm_ne_zero hP
  apply (hind Q hQ)
  have hzeroNhd : {z : ℂ | z ≠ 0} ∈ 𝓝 1 :=
    isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (one_ne_zero : (1 : ℂ) ≠ 0))
  filter_upwards [(isOpen_gammaIterateRegularSet k).mem_nhds
    (one_mem_gammaIterateRegularSet k), hzeroNhd] with z hzreg hz0
  have hx : -z⁻¹ ∈ localGammaMicroscopeDomain (gammaIterateRegularSet k) := by
    refine ⟨neg_ne_zero.mpr (inv_ne_zero hz0), ?_⟩
    rw [neg_inv_neg_inv hz0]
    exact hzreg
  let G : ℕ → Fin (k + 1) → ℂ := fun n j =>
    gammaIterate ((j : ℕ) + 1)
      (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹))
  let J : Fin (k + 1) → ℂ := gammaIterateTuple k z
  have hG : ∀ j, Tendsto (fun n => G n j) atTop (𝓝 (J j)) := by
    intro j
    have h := tendsto_gammaIterate_succ_factorialBlowUp hx j
    simpa [G, J, gammaIterateTuple_apply, neg_inv_neg_inv hz0] using h
  have hrel : ∀ᶠ n : ℕ in atTop, ∑ α ∈ P.support,
      algebraicFactorialInitialCoefficient P α n (-z⁻¹) *
        differentialJetMonomial (G n) α = 0 := by
    filter_upwards [eventually_factorialBlowUp_input_gammaIterateRegular hk hx]
      with n hn
    apply algebraicFactorialInitialRelation_of_relation_at P n (-z⁻¹) (G n)
    simpa [G, gammaIterateTuple] using hprop
      (-(n : ℂ) + reciprocalGammaFactorialScale n * (-z⁻¹)) hn
  have hvan := algebraicFactorialInitialForm_vanishes_of_rescaled_relations
    P (-z⁻¹) G J hG hrel
  simpa [Q, J] using hvan

theorem locallyAlgebraicallyIndependentGammaIterates :
    ∀ (k : ℕ), 1 ≤ k → LocallyAlgebraicallyIndependentGammaIterates k
  | 0, hk => by omega
  | k + 1, _ => by
      by_cases hk0 : k = 0
      · subst k
        exact locallyAlgebraicallyIndependentGammaIterates_one
      · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        exact locallyAlgebraicallyIndependentGammaIterates_succ hk
          (locallyAlgebraicallyIndependentGammaIterates k hk)

def gammaIterateFunctionTuple (k : ℕ) : Fin (k + 1) → (ℂ → ℂ) :=
  fun i z => gammaIterateTuple k z i

theorem algebraicIndependent_gammaIterateFunctionTuple (k : ℕ) (hk : 1 ≤ k) :
    AlgebraicIndependent ℂ (gammaIterateFunctionTuple k) := by
  rw [algebraicIndependent_iff]
  intro P hEval
  by_contra hP
  apply locallyAlgebraicallyIndependentGammaIterates k hk P hP
  filter_upwards [] with z
  have hz := congrFun hEval z
  have hz' :
      (MvPolynomial.eval₂ (algebraMap ℂ (ℂ → ℂ))
        (gammaIterateFunctionTuple k) P) z = 0 := by
    simpa [MvPolynomial.aeval_def] using hz
  rw [eval₂_function_apply] at hz'
  simpa [gammaIterateFunctionTuple] using hz'

/-- The complete countable tower
`z, Gamma z, Gamma (Gamma z), ...` is algebraically independent over `ℂ`.

This is stronger than algebraic independence at every fixed finite depth: it
packages the iterates as one infinite-rank algebraically independent family. -/
theorem algebraicIndependent_gammaIterates :
    AlgebraicIndependent ℂ gammaIterate := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  rcases ht.bddAbove with ⟨k, hk⟩
  let f : t → Fin ((k + 1) + 1) := fun i =>
    ⟨i, Nat.lt_succ_of_le (Nat.le_succ_of_le (hk i.2))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hprefix := algebraicIndependent_gammaIterateFunctionTuple
    (k + 1) (Nat.le_add_left 1 k)
  have hsub := hprefix.comp f hf
  have heq : gammaIterateFunctionTuple (k + 1) ∘ f =
      fun i : t => gammaIterate (i : ℕ) := by
    funext i z
    exact gammaIterateTuple_apply (k + 1) z (f i)
  rw [heq] at hsub
  exact hsub

theorem no_local_algebraic_relation_gammaIterates
    {k : ℕ} (hk : 1 ≤ k)
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hVreg : V ⊆ gammaIterateRegularSet k)
    (P : MvPolynomial (Fin (k + 1)) ℂ) (hP : P ≠ 0) :
    ¬ ∀ z ∈ V, MvPolynomial.eval (gammaIterateTuple k z) P = 0 := by
  intro hrel
  have hprop := gammaIterateTupleRelation_propagates_from_open
    P hVopen hVne hVreg hrel
  apply (locallyAlgebraicallyIndependentGammaIterates k hk P hP)
  filter_upwards [(isOpen_gammaIterateRegularSet k).mem_nhds
    (one_mem_gammaIterateRegularSet k)] with z hz
  exact hprop z hz

end

end GaloisForLFunctions
