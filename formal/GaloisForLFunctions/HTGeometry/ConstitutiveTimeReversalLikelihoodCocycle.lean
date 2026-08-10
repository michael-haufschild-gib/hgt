import Mathlib

/-!
# Time-reversal likelihood cocycle

A path law `P` on a measurable space together with a measurable involution `Θ` produces the
time-asymmetry variable `Σ = log (dP/dΘ_*P)`.  Reversal flips its sign, its exponential has mean
one, and its mean is exactly the Kullback–Leibler divergence between the forward and reversed laws —
so positivity of production appears only after averaging against the constitutive path law.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory

section LikelihoodCocycle

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The reversed path law `P^Θ = Θ_*P`. -/
noncomputable def revLaw (P : Measure Ω) (Θ : Ω → Ω) : Measure Ω := Measure.map Θ P

/-- The time-asymmetry variable `Σ = log (dP/dP^Θ)`, equation (1). -/
noncomputable def timeAsymmetry (P : Measure Ω) (Θ : Ω → Ω) : Ω → ℝ := llr P (revLaw P Θ)

theorem revLaw_revLaw (P : Measure Ω) {Θ : Ω → Ω} (hΘ : Measurable Θ)
    (hinv : ∀ x, Θ (Θ x) = x) : revLaw (revLaw P Θ) Θ = P := by
  rw [revLaw, revLaw, Measure.map_map hΘ hΘ]
  have : Θ ∘ Θ = id := funext hinv
  rw [this, Measure.map_id]

/-- A measurable involution generates the whole σ-algebra by comap. -/
theorem comap_of_involution {Θ : Ω → Ω} (hΘ : Measurable Θ) (hinv : ∀ x, Θ (Θ x) = x) :
    MeasurableSpace.comap Θ ‹MeasurableSpace Ω› = ‹MeasurableSpace Ω› := by
  refine le_antisymm hΘ.comap_le ?_
  intro s hs
  exact ⟨Θ ⁻¹' s, hΘ hs, by ext x; simp [hinv x]⟩

variable (P : Measure Ω) [IsProbabilityMeasure P] {Θ : Ω → Ω}

/-- **Equation (2).**  Reversal flips the sign of the time-asymmetry variable. -/
theorem timeAsymmetry_comp_involution (hΘ : Measurable Θ) (hinv : ∀ x, Θ (Θ x) = x)
    (hac : P ≪ revLaw P Θ) (hca : revLaw P Θ ≪ P) :
    (fun x => timeAsymmetry P Θ (Θ x)) =ᵐ[P] fun x => -timeAsymmetry P Θ x := by
  set Q : Measure Ω := revLaw P Θ with hQ
  have hQprob : IsProbabilityMeasure Q := by
    rw [hQ, revLaw]
    exact Measure.isProbabilityMeasure_map hΘ.aemeasurable
  have hmapQ : Measure.map Θ Q = P := by
    rw [hQ]
    exact revLaw_revLaw P hΘ hinv
  have hmapP : Measure.map Θ P = Q := rfl
  have hσ : SigmaFinite (Measure.map Θ P) := by
    rw [hmapP]; infer_instance
  have hmapDeriv := toReal_rnDeriv_map (μ := Q) (ν := P) hca hΘ
  rw [hmapQ, hmapP] at hmapDeriv
  have hcondExp : P[(fun a => (Q.rnDeriv P a).toReal) | MeasurableSpace.comap Θ ‹MeasurableSpace Ω›]
      = fun a => (Q.rnDeriv P a).toReal := by
    rw [comap_of_involution hΘ hinv]
    exact condExp_of_stronglyMeasurable le_rfl
      (Measurable.stronglyMeasurable (by fun_prop)) Measure.integrable_toReal_rnDeriv
  rw [hcondExp] at hmapDeriv
  have hneg := neg_llr (μ := P) (ν := Q) hac
  filter_upwards [hmapDeriv, hneg] with x hx hxneg
  show llr P Q (Θ x) = -llr P Q x
  rw [Pi.neg_apply] at hxneg
  rw [hxneg, llr, llr, hx]

/-- **Equation (3).**  The exponentiated production has mean one. -/
theorem integral_exp_neg_timeAsymmetry (hΘ : Measurable Θ) (hac : P ≪ revLaw P Θ)
    (hca : revLaw P Θ ≪ P) :
    ∫ x, Real.exp (-timeAsymmetry P Θ x) ∂P = 1 := by
  have hQprob : IsProbabilityMeasure (revLaw P Θ) := by
    rw [revLaw]
    exact Measure.isProbabilityMeasure_map hΘ.aemeasurable
  have h1 : (fun x => Real.exp (-timeAsymmetry P Θ x))
      =ᵐ[P] fun x => ((revLaw P Θ).rnDeriv P x).toReal := exp_neg_llr hac
  rw [integral_congr_ae h1, Measure.integral_toReal_rnDeriv hca]
  simp

/-- **Equation (4).**  The mean production is exactly the relative entropy of the forward law
against the reversed law. -/
theorem integral_timeAsymmetry_eq_klDiv (hΘ : Measurable Θ) (hac : P ≪ revLaw P Θ) :
    ∫ x, timeAsymmetry P Θ x ∂P = (klDiv P (revLaw P Θ)).toReal := by
  haveI : IsProbabilityMeasure (revLaw P Θ) := by
    rw [revLaw]
    exact Measure.isProbabilityMeasure_map hΘ.aemeasurable
  refine (toReal_klDiv_of_measure_eq hac ?_).symm
  rw [measure_univ, measure_univ]

/-- **Equation (4), positivity.** -/
theorem integral_timeAsymmetry_nonneg (hΘ : Measurable Θ) (hac : P ≪ revLaw P Θ) :
    0 ≤ ∫ x, timeAsymmetry P Θ x ∂P := by
  rw [integral_timeAsymmetry_eq_klDiv P hΘ hac]
  exact ENNReal.toReal_nonneg

/-- **Equation (4), equality criterion.**  The mean production vanishes exactly when the law is
reversible. -/
theorem integral_timeAsymmetry_eq_zero_iff (hΘ : Measurable Θ) (hac : P ≪ revLaw P Θ)
    (h_int : Integrable (timeAsymmetry P Θ) P) :
    ∫ x, timeAsymmetry P Θ x ∂P = 0 ↔ P = revLaw P Θ := by
  have hQprob : IsProbabilityMeasure (revLaw P Θ) := by
    rw [revLaw]
    exact Measure.isProbabilityMeasure_map hΘ.aemeasurable
  rw [integral_timeAsymmetry_eq_klDiv P hΘ hac]
  rw [ENNReal.toReal_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact klDiv_eq_zero_iff.mp h
    · exact absurd h (klDiv_ne_top hac h_int)
  · intro h
    left
    rw [klDiv_eq_zero_iff]
    exact h

end LikelihoodCocycle

/-! ## Observer contraction -/

section ObserverContraction

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  (P : Measure Ω) [IsProbabilityMeasure P] {Θ : Ω → Ω} {θ : Y → Y} {q : Ω → Y}

omit [IsProbabilityMeasure P] in
/-- Compatibility of the observer with the two reversals, equation (5), transports the reversed law
along the observer. -/
theorem revLaw_map (hq : Measurable q) (hΘ : Measurable Θ) (hθ : Measurable θ)
    (hcomp : ∀ x, q (Θ x) = θ (q x)) :
    revLaw (Measure.map q P) θ = Measure.map q (revLaw P Θ) := by
  rw [revLaw, revLaw, Measure.map_map hθ hq, Measure.map_map hq hΘ]
  congr 1
  funext x
  exact (hcomp x).symm

/-- **Equation (7).**  The observer's exponentiated production, pulled back along the observer, is
the conditional expectation of the full exponentiated production. -/
theorem exp_neg_timeAsymmetry_observer (hq : Measurable q) (hΘ : Measurable Θ)
    (hθ : Measurable θ) (hcomp : ∀ x, q (Θ x) = θ (q x))
    (hac : P ≪ revLaw P Θ) (hca : revLaw P Θ ≪ P) :
    (fun x => Real.exp (-timeAsymmetry (Measure.map q P) θ (q x)))
      =ᵐ[P] P[(fun x => Real.exp (-timeAsymmetry P Θ x))
        | MeasurableSpace.comap q ‹MeasurableSpace Y›] := by
  haveI hQprob : IsProbabilityMeasure (revLaw P Θ) := by
    rw [revLaw]
    exact Measure.isProbabilityMeasure_map hΘ.aemeasurable
  haveI hmapP : IsProbabilityMeasure (Measure.map q P) :=
    Measure.isProbabilityMeasure_map hq.aemeasurable
  haveI hmapRev : IsProbabilityMeasure (revLaw (Measure.map q P) θ) := by
    rw [revLaw]
    exact Measure.isProbabilityMeasure_map hθ.aemeasurable
  -- the map-level Radon–Nikodym identity
  have hmapDeriv := toReal_rnDeriv_map (μ := revLaw P Θ) (ν := P) hca hq
  -- rewrite the left side into the observer's own likelihood ratio
  have hrev : Measure.map q (revLaw P Θ) = revLaw (Measure.map q P) θ :=
    (revLaw_map P hq hΘ hθ hcomp).symm
  rw [hrev] at hmapDeriv
  -- both sides are exponentials of minus the corresponding asymmetry variables
  have hleft : (fun x => Real.exp (-timeAsymmetry (Measure.map q P) θ (q x)))
      =ᵐ[P] fun x => ((revLaw (Measure.map q P) θ).rnDeriv (Measure.map q P) (q x)).toReal := by
    have hac' : Measure.map q P ≪ revLaw (Measure.map q P) θ := by
      rw [← hrev]
      exact hac.map hq
    have hQ := exp_neg_llr (μ := Measure.map q P) (ν := revLaw (Measure.map q P) θ) hac'
    exact ae_of_ae_map hq.aemeasurable hQ
  have hright : (fun x => Real.exp (-timeAsymmetry P Θ x))
      =ᵐ[P] fun x => ((revLaw P Θ).rnDeriv P x).toReal := exp_neg_llr hac
  refine hleft.trans (hmapDeriv.trans ?_)
  exact (condExp_congr_ae hright).symm

end ObserverContraction

/-! ## §4 — a closed recurrent observer with escaping produced history

The deterministic core of Theorem 4.1: a `±1` path that diverges to `+∞` hits every level above its
start, so a finite mod-`m` observer returns to `0` at arbitrarily late times, while the underlying
path escapes and the production rate keeps its limit along those returns. -/

section RecurrentObserver

open Filter

variable {X : ℕ → ℤ}

/-- A `±1` path that diverges hits every level above its start. -/
theorem exists_hit_of_tendsto (hstep : ∀ n, X (n + 1) = X n + 1 ∨ X (n + 1) = X n - 1)
    (hdiv : Tendsto X atTop atTop) {k : ℤ} (hk : X 0 ≤ k) : ∃ n, X n = k := by
  classical
  obtain ⟨N, hN⟩ := (hdiv.eventually_ge_atTop k).exists
  have hex : ∃ n, k ≤ X n := ⟨N, hN⟩
  classical
  obtain ⟨n, hn, hmin⟩ := Nat.findX hex
  refine ⟨n, le_antisymm ?_ hn⟩
  rcases Nat.eq_zero_or_pos n with hz | hpos
  · rw [hz] at hn ⊢
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hj : ¬ k ≤ X j := hmin j (by omega)
    rcases hstep j with h | h <;> omega

/-- Every level is reached only after at least that many steps, since the path moves by one. -/
theorem le_of_hit (hstep : ∀ n, X (n + 1) = X n + 1 ∨ X (n + 1) = X n - 1) (n : ℕ) :
    X n ≤ X 0 + n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases hstep m with h | h <;> push_cast <;> omega

/-- **Theorem 4.1, recurrence with escape.**  The finite mod-`m` observer returns to zero at
arbitrarily late times, and the underlying path escapes along those returns. -/
theorem returns_unbounded (hstep : ∀ n, X (n + 1) = X n + 1 ∨ X (n + 1) = X n - 1)
    (hdiv : Tendsto X atTop atTop) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∃ n, N ≤ n ∧ (m : ℤ) ∣ X n ∧ (N : ℤ) ≤ X n := by
  set B : ℤ := max (X 0) (max (N : ℤ) ((N : ℤ) + X 0)) with hB
  set j : ℕ := B.toNat with hjdef
  have hjB : B ≤ (j : ℤ) := Int.self_le_toNat B
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hjnn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
  have hmj : (j : ℤ) ≤ (m : ℤ) * (j : ℤ) := by nlinarith
  set M : ℤ := (m : ℤ) * (j : ℤ) with hM
  have hBM : B ≤ M := le_trans hjB hmj
  have h0 : X 0 ≤ M := le_trans (le_max_left _ _) hBM
  have h1 : (N : ℤ) ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hBM
  have h2 : (N : ℤ) + X 0 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hBM
  obtain ⟨n, hn⟩ := exists_hit_of_tendsto hstep hdiv h0
  have hle := le_of_hit hstep n
  rw [hn] at hle
  refine ⟨n, ?_, ⟨j, hn⟩, by rw [hn]; exact h1⟩
  omega

/-- **Equation (12).**  The production rate along any divergent subsequence keeps the limit of the
production rate of the path. -/
theorem tendsto_production_along_subsequence {c : ℝ} {τ : ℕ → ℕ}
    (hrate : Tendsto (fun n : ℕ => (X n : ℝ) / (n : ℝ)) atTop (nhds c))
    (hτ : Tendsto τ atTop atTop) :
    Tendsto (fun j : ℕ => (X (τ j) : ℝ) / ((τ j : ℕ) : ℝ)) atTop (nhds c) :=
  hrate.comp hτ

end RecurrentObserver

/-! ## Kullback–Leibler divergence under a measurable embedding

Mathlib has no invariance lemma for `klDiv` under a measurable embedding; it is proved here from
`MeasurableEmbedding.rnDeriv_map` and the change of variables for `lintegral`. -/

section EmbeddingInvariance

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

theorem absolutelyContinuous_map_iff_of_measurableEmbedding (hf : MeasurableEmbedding f)
    {μ ν : Measure α} : μ.map f ≪ ν.map f ↔ μ ≪ ν := by
  constructor
  · intro h
    refine Measure.AbsolutelyContinuous.mk fun s hs hνs => ?_
    have h1 : (ν.map f) (f '' s) = 0 := by rw [hf.map_apply, hf.injective.preimage_image]; exact hνs
    have h2 : (μ.map f) (f '' s) = 0 := h h1
    rwa [hf.map_apply, hf.injective.preimage_image] at h2
  · exact fun h => hf.absolutelyContinuous_map h

/-- **`klDiv` is invariant under a measurable embedding.** -/
theorem klDiv_map_measurableEmbedding (hf : MeasurableEmbedding f) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  haveI : IsFiniteMeasure (μ.map f) := Measure.isFiniteMeasure_map μ f
  haveI : IsFiniteMeasure (ν.map f) := Measure.isFiniteMeasure_map ν f
  by_cases hac : μ ≪ ν
  · rw [klDiv_eq_lintegral_klFun_of_ac (hf.absolutelyContinuous_map hac),
      klDiv_eq_lintegral_klFun_of_ac hac, hf.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · rw [klDiv_of_not_ac hac, klDiv_of_not_ac]
    rwa [absolutelyContinuous_map_iff_of_measurableEmbedding hf]

end EmbeddingInvariance

/-! ## The graph embedding of an observer -/

section GraphEmbedding

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableEq Y] {q : Ω → Y}

/-- The graph map `ω ↦ (q ω, ω)` of a measurable observer is a measurable embedding. -/
theorem measurableEmbedding_graph (hq : Measurable q) :
    MeasurableEmbedding (fun ω => (q ω, ω)) where
  injective := by
    intro a b hab
    exact congrArg Prod.snd hab
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    have himg : (fun ω => (q ω, ω)) '' s
        = (Prod.snd ⁻¹' s) ∩ {p : Y × Ω | p.1 = q p.2} := by
      ext p
      constructor
      · rintro ⟨ω, hω, rfl⟩
        exact ⟨hω, rfl⟩
      · rintro ⟨h1, h2⟩
        exact ⟨p.2, h1, Prod.ext h2.symm rfl⟩
    rw [himg]
    exact (measurable_snd hs).inter (measurableSet_eq_fun measurable_fst (hq.comp measurable_snd))

end GraphEmbedding

/-! ## §3, equations (8) and (9) — data processing and the exact gap

Mathlib has no data-processing inequality for `klDiv`.  It is obtained here by pushing both laws
forward along the graph embedding of the observer, disintegrating the joint law, and applying the
chain rule. -/

section DataProcessing

open ProbabilityTheory

variable {Ω Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace Y] [MeasurableEq Y] {q : Ω → Y}

/-- The joint law of the observer and the state. -/
noncomputable def jointLaw (P : Measure Ω) (q : Ω → Y) : Measure (Y × Ω) :=
  P.map (fun ω => (q ω, ω))

instance instIsFiniteMeasureJointLaw (P : Measure Ω) [IsFiniteMeasure P] (q : Ω → Y) :
    IsFiniteMeasure (jointLaw P q) := by
  rw [jointLaw]
  exact Measure.isFiniteMeasure_map P _

omit [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableEq Y] in
theorem jointLaw_fst (P : Measure Ω) [IsFiniteMeasure P] (hq : Measurable q) :
    (jointLaw P q).fst = P.map q := by
  rw [jointLaw, Measure.fst, Measure.map_map measurable_fst (by fun_prop)]
  rfl

omit [StandardBorelSpace Ω] [Nonempty Ω] in
theorem klDiv_jointLaw (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hq : Measurable q) : klDiv (jointLaw P q) (jointLaw Q q) = klDiv P Q :=
  klDiv_map_measurableEmbedding (measurableEmbedding_graph hq) P Q

/-- **Equation (9), chain-rule form.**  The full production splits exactly into the observed part
and a nonnegative conditional part. -/
theorem klDiv_eq_map_add_cond (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hq : Measurable q) :
    klDiv P Q = klDiv (P.map q) (Q.map q)
      + klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
        ((jointLaw P q).fst ⊗ₘ (jointLaw Q q).condKernel) := by
  have hP : (jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel = jointLaw P q :=
    Measure.disintegrate _ _
  have hQ : (jointLaw Q q).fst ⊗ₘ (jointLaw Q q).condKernel = jointLaw Q q :=
    Measure.disintegrate _ _
  calc klDiv P Q = klDiv (jointLaw P q) (jointLaw Q q) := (klDiv_jointLaw P Q hq).symm
    _ = klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
          ((jointLaw Q q).fst ⊗ₘ (jointLaw Q q).condKernel) := by rw [hP, hQ]
    _ = klDiv (jointLaw P q).fst (jointLaw Q q).fst
          + klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
            ((jointLaw P q).fst ⊗ₘ (jointLaw Q q).condKernel) := klDiv_compProd_eq_add _ _ _ _
    _ = _ := by rw [jointLaw_fst P hq, jointLaw_fst Q hq]

/-- **Equation (8).**  The data-processing inequality: no observer can increase the mean
production. -/
theorem klDiv_map_le (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hq : Measurable q) : klDiv (P.map q) (Q.map q) ≤ klDiv P Q := by
  rw [klDiv_eq_map_add_cond P Q hq]
  exact le_self_add

/-- **The sufficiency criterion of Theorem 3.1.**  The observer loses nothing exactly when the
conditional term vanishes, that is when the two disintegrations agree over the observation. -/
theorem klDiv_map_eq_iff (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hq : Measurable q) (hfin : klDiv (P.map q) (Q.map q) ≠ ⊤) :
    klDiv (P.map q) (Q.map q) = klDiv P Q
      ↔ (jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel
        = (jointLaw P q).fst ⊗ₘ (jointLaw Q q).condKernel := by
  rw [klDiv_eq_map_add_cond P Q hq]
  constructor
  · intro h
    have hzero : klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
        ((jointLaw P q).fst ⊗ₘ (jointLaw Q q).condKernel) = 0 := by
      have hsym := h.symm
      have hcancel := ENNReal.add_right_inj hfin
        (b := klDiv ((jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel)
          ((jointLaw P q).fst ⊗ₘ (jointLaw Q q).condKernel)) (c := 0)
      simpa using hcancel.mp (by simpa using hsym)
    exact klDiv_eq_zero_iff.mp hzero
  · intro h
    rw [klDiv_eq_zero_iff.mpr h, add_zero]

end DataProcessing

/-! ## §4 — the random-walk model -/

section RandomWalkModel

open Filter ProbabilityTheory

/-- A path with positive asymptotic rate diverges. -/
theorem tendsto_atTop_of_rate {X : ℕ → ℤ} {c : ℝ} (hc : 0 < c)
    (hrate : Tendsto (fun n : ℕ => (X n : ℝ) / (n : ℝ)) atTop (nhds c)) :
    Tendsto X atTop atTop := by
  have hhalf : ∀ᶠ n : ℕ in atTop, c / 2 < (X n : ℝ) / (n : ℝ) :=
    hrate.eventually_const_lt (by linarith)
  refine tendsto_atTop.mpr fun b => ?_
  have hbig : ∀ᶠ n : ℕ in atTop, (b : ℝ) ≤ c / 2 * (n : ℝ) := by
    have : Tendsto (fun n : ℕ => c / 2 * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop _
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  filter_upwards [hhalf, hbig, hpos] with n h1 h2 h3
  have h4 : c / 2 * (n : ℝ) < (X n : ℝ) := (lt_div_iff₀ h3).mp h1
  have : (b : ℝ) ≤ (X n : ℝ) := le_of_lt (lt_of_le_of_lt h2 h4)
  exact_mod_cast this

/-- **Theorem 4.1.**  A `±1` path with positive asymptotic rate is invisible to the finite mod-`m`
observer at arbitrarily late times, while the path itself escapes and the production rate keeps its
strictly positive limit. -/
theorem closed_observer_open_history {X : ℕ → ℤ} {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m)
    (hstep : ∀ n, X (n + 1) = X n + 1 ∨ X (n + 1) = X n - 1)
    (hrate : Tendsto (fun n : ℕ => (X n : ℝ) / (n : ℝ)) atTop (nhds c)) (N : ℕ) :
    ∃ n, N ≤ n ∧ (m : ℤ) ∣ X n ∧ (N : ℤ) ≤ X n :=
  returns_unbounded hstep (tendsto_atTop_of_rate hc hrate) hm N

/-- **Equation (10).**  The likelihood production of an `n`-step path. -/
noncomputable def walkProduction (X : ℕ → ℤ) (p r : ℝ) (n : ℕ) : ℝ :=
  (X n : ℝ) * Real.log (p / r)

/-- **Equation (12).**  The asymptotic production rate is `c · log (p / r)`, strictly positive when
the drift and the odds ratio are. -/
theorem tendsto_walkProduction_rate {X : ℕ → ℤ} {c p r : ℝ}
    (hrate : Tendsto (fun n : ℕ => (X n : ℝ) / (n : ℝ)) atTop (nhds c)) :
    Tendsto (fun n : ℕ => walkProduction X p r n / (n : ℝ)) atTop
      (nhds (c * Real.log (p / r))) := by
  have hfun : (fun n : ℕ => walkProduction X p r n / (n : ℝ))
      = fun n : ℕ => ((X n : ℝ) / (n : ℝ)) * Real.log (p / r) := by
    funext n
    rw [walkProduction]
    ring
  rw [hfun]
  exact hrate.mul_const _

theorem walkProduction_rate_pos {c p r : ℝ} (hc : 0 < c) (hpr : 1 < p / r) :
    0 < c * Real.log (p / r) :=
  mul_pos hc (Real.log_pos hpr)

/-! ### The increments -/

variable {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ → Ω → ℤ}

/-- The `n`-step displacement of the increment sequence. -/
def walk (ξ : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) : ℤ := ∑ j ∈ Finset.range n, ξ j ω

omit [MeasurableSpace Ω] in
theorem walk_step (hpm : ∀ j ω, ξ j ω = 1 ∨ ξ j ω = -1) (n : ℕ) (ω : Ω) :
    walk ξ (n + 1) ω = walk ξ n ω + 1 ∨ walk ξ (n + 1) ω = walk ξ n ω - 1 := by
  rw [walk, walk, Finset.sum_range_succ]
  rcases hpm n ω with h | h
  · left; rw [h]
  · right; rw [h]; ring

/-- The mean increment of a `±1` variable with success probability `p` is `2p − 1`. -/
theorem integral_increment (P : Measure Ω) [IsProbabilityMeasure P] {p : ℝ}
    (hpm : ∀ ω, ξ 0 ω = 1 ∨ ξ 0 ω = -1) (hmeas : MeasurableSet {ω | ξ 0 ω = 1})
    (hlaw : P.real {ω | ξ 0 ω = 1} = p) :
    ∫ ω, ((ξ 0 ω : ℤ) : ℝ) ∂P = 2 * p - 1 := by
  have hpoint : ∀ ω, ((ξ 0 ω : ℤ) : ℝ)
      = 2 * Set.indicator {ω | ξ 0 ω = 1} (1 : Ω → ℝ) ω - 1 := by
    intro ω
    rcases hpm ω with h | h
    · rw [Set.indicator_of_mem (by exact h), h]
      norm_num
    · rw [Set.indicator_of_notMem (by simp [h]), h]
      norm_num
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_sub, integral_const_mul, integral_indicator_one hmeas, hlaw]
  · simp
  · exact (integrable_const _).indicator hmeas |>.const_mul 2
  · exact integrable_const _

/-- **Theorem 4.1, probabilistic form.**  For an independent, identically distributed `±1`
increment sequence with mean `2p − 1 > 0`, almost every path is invisible to the finite mod-`m`
observer at arbitrarily late times while the path itself escapes, and the production rate keeps its
strictly positive limit. -/
theorem ae_closed_observer_open_history (P : Measure Ω) [IsProbabilityMeasure P] {p : ℝ}
    (hpm : ∀ j ω, ξ j ω = 1 ∨ ξ j ω = -1)
    (hint : Integrable (fun ω => ((ξ 0 ω : ℤ) : ℝ)) P)
    (hindep : Pairwise
      (Function.onFun (fun x y => IndepFun x y P) fun n ω => ((ξ n ω : ℤ) : ℝ)))
    (hident : ∀ i, IdentDistrib (fun ω => ((ξ i ω : ℤ) : ℝ))
      (fun ω => ((ξ 0 ω : ℤ) : ℝ)) P P)
    (hmean : ∫ ω, ((ξ 0 ω : ℤ) : ℝ) ∂P = 2 * p - 1) (hp : 1 / 2 < p) {m : ℕ} (hm : 0 < m) :
    ∀ᵐ ω ∂P, ∀ N : ℕ,
      ∃ n, N ≤ n ∧ (m : ℤ) ∣ walk ξ n ω ∧ (N : ℤ) ≤ walk ξ n ω := by
  have hc : 0 < 2 * p - 1 := by linarith
  have hslln := strong_law_ae (μ := P) (fun n ω => ((ξ n ω : ℤ) : ℝ)) hint hindep hident
  rw [hmean] at hslln
  filter_upwards [hslln] with ω hω
  intro N
  refine closed_observer_open_history hc hm (fun n => walk_step hpm n ω) ?_ N
  have hfun : (fun n : ℕ => ((walk ξ n ω : ℤ) : ℝ) / (n : ℝ))
      = fun n : ℕ => ((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ((ξ i ω : ℤ) : ℝ) := by
    funext n
    rw [walk, smul_eq_mul]
    push_cast
    rw [div_eq_inv_mul]
  rw [hfun]
  exact hω

end RandomWalkModel

/-! ## The conditional Kullback–Leibler divergence as an integral

Mathlib's chain rule leaves the conditional term as a divergence of composition-products.  This
section identifies it with the integral of the fibrewise divergences, which is what equation (9)
asserts. -/

section ConditionalKL

open ProbabilityTheory

variable {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
  [MeasurableSpace.CountableOrCountablyGenerated Y Ω]

/-- The Radon–Nikodym derivative of two composition-products with a common first factor is the
kernel Radon–Nikodym derivative. -/
theorem rnDeriv_compProd_right (μ : Measure Y) [IsFiniteMeasure μ]
    (κ η : Kernel Y Ω) [IsFiniteKernel κ] [IsFiniteKernel η] (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p => κ.rnDeriv η p.1 p.2 := by
  have hker : ∀ᵐ y ∂μ, κ y ≪ η y := Measure.absolutelyContinuous_compProd_right_iff.mp hac
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
    (Kernel.measurable_rnDeriv κ η) fun s hs _ => ?_
  rw [Measure.setLIntegral_rnDeriv hac, Measure.compProd_apply hs,
    ← lintegral_indicator hs, Measure.lintegral_compProd
      ((Kernel.measurable_rnDeriv κ η).indicator hs)]
  refine lintegral_congr_ae ?_
  filter_upwards [hker] with y hy
  have hslice : ∀ ω : Ω, s.indicator (fun p : Y × Ω => κ.rnDeriv η p.1 p.2) (y, ω)
      = (Prod.mk y ⁻¹' s).indicator (fun ω : Ω => κ.rnDeriv η y ω) ω := by
    intro ω
    by_cases h : (y, ω) ∈ s <;> simp [h]
  rw [lintegral_congr fun ω => hslice ω, lintegral_indicator (hs.preimage (by fun_prop))]
  have hinner : ∫⁻ ω in Prod.mk y ⁻¹' s, κ.rnDeriv η y ω ∂(η y)
      = ∫⁻ ω in Prod.mk y ⁻¹' s, ((κ y).rnDeriv (η y)) ω ∂(η y) := by
    refine lintegral_congr_ae ?_
    exact ae_restrict_of_ae (Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := y))
  rw [hinner, Measure.setLIntegral_rnDeriv hy]

/-- **The conditional divergence is the integral of the fibrewise divergences.** -/
theorem klDiv_compProd_right (μ : Measure Y) [IsFiniteMeasure μ]
    (κ η : Kernel Y Ω) [IsMarkovKernel κ] [IsMarkovKernel η] (hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ y, klDiv (κ y) (η y) ∂μ := by
  have hker : ∀ᵐ y ∂μ, κ y ≪ η y := Measure.absolutelyContinuous_compProd_right_iff.mp hac
  rw [klDiv_eq_lintegral_klFun_of_ac hac,
    lintegral_congr_ae (by
      filter_upwards [rnDeriv_compProd_right μ κ η hac] with p hp
      rw [hp] :
      (fun p => ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal))
        =ᵐ[μ ⊗ₘ η] fun p => ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal)),
    Measure.lintegral_compProd (by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [hker] with y hy
  rw [klDiv_eq_lintegral_klFun_of_ac hy]
  refine lintegral_congr_ae ?_
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := y)] with ω hω
  rw [hω]

end ConditionalKL

/-! ## §3, equation (9) in its stated form -/

section ExactGap

open ProbabilityTheory

variable {Ω Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace Y] [MeasurableEq Y] [MeasurableSpace.CountableOrCountablyGenerated Y Ω]
  {q : Ω → Y}

/-- **Equation (9).**  The exact gap between the full production and the observed production is the
integral of the fibrewise productions over the observed law. -/
theorem klDiv_eq_map_add_integral (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hq : Measurable q)
    (hac : (jointLaw P q).fst ⊗ₘ (jointLaw P q).condKernel
      ≪ (jointLaw P q).fst ⊗ₘ (jointLaw Q q).condKernel) :
    klDiv P Q = klDiv (P.map q) (Q.map q)
      + ∫⁻ y, klDiv ((jointLaw P q).condKernel y) ((jointLaw Q q).condKernel y) ∂(P.map q) := by
  rw [klDiv_eq_map_add_cond P Q hq, klDiv_compProd_right _ _ _ hac, jointLaw_fst P hq]

end ExactGap

end GaloisForLFunctions.HTGeometry
