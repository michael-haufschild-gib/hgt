import GaloisForLFunctions.HTGeometry.MeromorphicTranslationDefectCountability

/-!
# Bounded-complexity accumulation and complexity escape for meromorphic sources

The card `ht-da-translation-spectrum-countability` sharpens countability of the differentially
algebraic translation spectrum to a rigidity statement: at a *fixed* differential order and total
jet degree, the set of shifts whose defect satisfies such a relation is closed-discrete unless the
source itself satisfies an algebraic differential equation.

The proof is the same dichotomy as for countability, with one extra freedom: the sample disc is
chosen so that no node is moved onto the singular set by any shift of the given accumulating
sequence.  That is possible because only countably many radii are forbidden while an interval of
radii is uncountable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

/-! ## Bounded-complexity relations on a domain -/

/-- A nonzero algebraic differential equation of jet order `n` and total degree at most `d`, valid
on `U`. -/
def HasDifferentialRelationOfComplexityOn (f : ℂ → ℂ) (U : Set ℂ) (n d : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin (n + 2)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
    ∀ z ∈ U, MvPolynomial.eval (entireJetVector f n z) P = 0

theorem exists_jetRelationOn_of_hasDifferentialRelationOfComplexityOn {f : ℂ → ℂ} {U : Set ℂ}
    {n d : ℕ} (h : HasDifferentialRelationOfComplexityOn f U n d) :
    ∃ c : JetExponent n d → ℂ, c ≠ 0 ∧ JetRelationOn f U n d c := by
  classical
  obtain ⟨P, hP0, hPdeg, hP⟩ := h
  refine ⟨fun m => MvPolynomial.coeff (jetExponentToFinsupp m) P, ?_, ?_⟩
  · intro hc
    refine hP0 (MvPolynomial.ext P 0 fun μ => ?_)
    by_cases hμ : μ ∈ P.support
    · have hbd : ∀ i, μ i ≤ d := fun i =>
        le_trans (le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)) hPdeg
      have hmem : jetExponentToFinsupp
          (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ : Fin (d + 1))) = μ := by
        ext i
        rfl
      have hcμ := congrFun hc
        (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ : Fin (d + 1)))
      rw [hmem] at hcμ
      simpa using hcμ
    · simp [MvPolynomial.notMem_support_iff.1 hμ]
  · intro z hz
    have hbd : ∀ μ ∈ P.support, ∀ i, μ i ≤ d := fun μ hμ i =>
      le_trans (le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)) hPdeg
    have hsum := sum_jetExponent_eq_sum_support (d := d) P hbd
      (fun μ => MvPolynomial.coeff μ P *
        ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (μ i))
      (fun μ hμ => by simp [MvPolynomial.notMem_support_iff.1 hμ])
    rw [show (∑ m : JetExponent n d,
        MvPolynomial.coeff (jetExponentToFinsupp m) P * jetMon f n d m z) =
        ∑ m : JetExponent n d,
          (fun μ => MvPolynomial.coeff μ P *
            ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (μ i))
            (jetExponentToFinsupp m) from rfl,
      hsum, ← eval_entireJetVector_eq_sum]
    exact hP z hz

theorem forall_domainCoordinateMinor_det_eq_zero_of_jetRelationOn {f : ℂ → ℂ} {U : Set ℂ}
    {z₀ : ℂ} {r : ℝ} {n d : ℕ} {c : JetExponent n d → ℂ} (hc0 : c ≠ 0)
    (hrel : JetRelationOn f U n d c) (hnodes : ∀ k, domainSampleNode z₀ r k ∈ U) :
    ∀ φ : JetExponent n d → ℕ, (coordinateMinor (domainJetSampleRow f z₀ r n d) φ).det = 0 := by
  classical
  rw [← not_linearIndependent_iff_forall_domainCoordinateMinor_det_eq_zero]
  rw [Fintype.linearIndependent_iff]
  push Not
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, c m₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc0 (funext hall)
  refine ⟨c, ?_, m₀, hm₀⟩
  funext k
  have := hrel _ (hnodes k)
  simpa [Finset.sum_apply, domainJetSampleRow] using this

theorem forall_domainCoordinateMinor_det_eq_zero_of_complexityOn {f : ℂ → ℂ} {U : Set ℂ}
    {z₀ : ℂ} {r : ℝ} {n d : ℕ}
    (h : HasDifferentialRelationOfComplexityOn f U n d)
    (hnodes : ∀ k, domainSampleNode z₀ r k ∈ U) :
    ∀ φ : JetExponent n d → ℕ, (coordinateMinor (domainJetSampleRow f z₀ r n d) φ).det = 0 := by
  obtain ⟨c, hc0, hrel⟩ := exists_jetRelationOn_of_hasDifferentialRelationOfComplexityOn h
  exact forall_domainCoordinateMinor_det_eq_zero_of_jetRelationOn hc0 hrel hnodes

/-- Enlarging the jet order preserves a bounded-degree relation on a domain. -/
theorem HasDifferentialRelationOfComplexityOn.mono_order {f : ℂ → ℂ} {U : Set ℂ} {n N d : ℕ}
    (h : HasDifferentialRelationOfComplexityOn f U n d) (hnN : n ≤ N) :
    HasDifferentialRelationOfComplexityOn f U N d := by
  obtain ⟨P, hP0, hPdeg, hP⟩ := h
  refine ⟨MvPolynomial.rename (jetOrderEmbed hnN) P, ?_,
    le_trans (MvPolynomial.totalDegree_rename_le _ _) hPdeg, ?_⟩
  · intro hzero
    apply hP0
    apply MvPolynomial.rename_injective _ (jetOrderEmbed_injective hnN)
    simpa using hzero
  · intro z hz
    rw [MvPolynomial.eval_rename]
    have hvec : entireJetVector f N z ∘ jetOrderEmbed hnN = entireJetVector f n z := by
      funext i
      exact entireJetVector_jetOrderEmbed hnN z i
    rw [hvec]
    exact hP z hz

/-! ## A sample disc whose nodes avoid a prescribed countable set -/

/-- A singularity-free sample disc all of whose nodes avoid a prescribed countable set. -/
theorem exists_center_radius_nodes_avoiding {S T : Set ℂ} (hSclosed : IsClosed S)
    (hScount : S.Countable) (hT : T.Countable) :
    ∃ (z₀ : ℂ) (R : ℝ), 0 < R ∧ z₀ ∈ Sᶜ ∧ (∀ w : ℂ, dist w z₀ < 3 * R → w ∈ Sᶜ) ∧
      (∀ k, domainSampleNode z₀ R k ∉ T) := by
  classical
  have hopen : IsOpen (Sᶜ) := hSclosed.isOpen_compl
  obtain ⟨z₀, hz₀⟩ : ∃ z : ℂ, z ∈ Sᶜ := by
    by_contra hno
    push Not at hno
    have hall : ∀ z : ℂ, z ∈ S := by
      intro z
      have := hno z
      simpa using this
    have huniv : (Set.univ : Set ℝ).Countable := by
      have hpre : (Set.univ : Set ℝ) = (fun x : ℝ => (x : ℂ)) ⁻¹' S := by
        ext x
        simp [hall]
      rw [hpre]
      exact hScount.preimage Complex.ofReal_injective
    exact Cardinal.not_countable_real huniv
  obtain ⟨ε, hε, hballsub⟩ := Metric.isOpen_iff.1 hopen z₀ hz₀
  -- forbidden radii: for each node index, a countable set
  set BadR : Set ℝ := ⋃ k : ℕ, {t : ℝ | z₀ + (((t / ((k : ℝ) + 2)) : ℝ) : ℂ) ∈ T} with hBadR
  have hBadRcount : BadR.Countable := by
    refine Set.countable_iUnion fun k => ?_
    have hinj : Function.Injective
        (fun t : ℝ => z₀ + (((t / ((k : ℝ) + 2)) : ℝ) : ℂ)) := by
      intro s t hst
      have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
      have := add_left_cancel hst
      have hr : (s / ((k : ℝ) + 2)) = (t / ((k : ℝ) + 2)) := by
        exact_mod_cast this
      field_simp at hr
      exact hr
    exact hT.preimage hinj
  obtain ⟨R, hRmem, hRnot⟩ : ∃ R ∈ Set.Ioo (0 : ℝ) (ε / 4), R ∉ BadR := by
    by_contra hno
    push Not at hno
    have hsub : Set.Ioo (0 : ℝ) (ε / 4) ⊆ BadR := fun x hx => hno x hx
    have hc := hBadRcount.mono hsub
    rw [Cardinal.Real.Ioo_countable_iff] at hc
    have : (0:ℝ) < ε / 4 := by positivity
    linarith
  refine ⟨z₀, R, hRmem.1, hz₀, ?_, ?_⟩
  · intro w hw
    refine hballsub ?_
    rw [Metric.mem_ball]
    have h3 : 3 * R < ε := by
      have := hRmem.2
      linarith
    linarith
  · intro k hmem
    exact hRnot (Set.mem_iUnion.2 ⟨k, by simpa [domainSampleNode] using hmem⟩)

/-! ## The accumulation theorem -/

/-- **Bounded-complexity accumulation.**  If, at one fixed jet order and total degree, the
translation defects of a source analytic off a closed countable set satisfy nonzero algebraic
differential equations along an injective convergent sequence of shifts, then the source itself
satisfies an algebraic differential equation. -/
theorem differentiallyAlgebraicOn_of_boundedComplexity_defects_accumulate {F : ℂ → ℂ} {S : Set ℂ}
    (hSclosed : IsClosed S) (hScount : S.Countable) (hF : AnalyticOnNhd ℂ F Sᶜ)
    {n d : ℕ} {u : ℕ → ℂ} {h₀ : ℂ} (huinj : Function.Injective u)
    (hu : ∀ k, HasDifferentialRelationOfComplexityOn (fun z => F (z + u k) - F z)
      (defectDomain S (u k)) n d)
    (hutend : Tendsto u atTop (𝓝 h₀)) :
    DifferentiallyAlgebraicOn F Sᶜ := by
  classical
  set T : Set ℂ := (⋃ k : ℕ, ((fun w : ℂ => w + u k) ⁻¹' S)) ∪ ((fun w : ℂ => w + h₀) ⁻¹' S)
    with hTdef
  have hTcount : T.Countable := by
    refine Set.Countable.union (Set.countable_iUnion fun k => ?_)
      (hScount.preimage (fun x y hxy => by simpa using hxy))
    exact hScount.preimage (fun x y hxy => by simpa using hxy)
  obtain ⟨z₀, R, hRpos, hz₀, hnear, hnodesT⟩ :=
    exists_center_radius_nodes_avoiding hSclosed hScount hTcount
  set a : ℕ → ℂ := domainSampleNode z₀ R with hadef
  have hnodedist : ∀ k, dist (a k) z₀ ≤ R / 2 := by
    intro k
    rw [hadef, dist_domainSampleNode z₀ hRpos k]
    have hk : (2:ℝ) ≤ (k : ℝ) + 2 := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_le_div_of_nonneg_left hRpos.le (by norm_num) hk
  have hnodes : ∀ k, a k ∈ Sᶜ := by
    intro k
    refine hnear _ ?_
    have := hnodedist k
    linarith
  have hshift : ∀ h : ℂ, ‖h‖ < R → ∀ k, a k + h ∈ Sᶜ := by
    intro h hh k
    refine hnear _ ?_
    have h1 : dist (a k + h) (a k) = ‖h‖ := by simp [dist_eq_norm]
    have h2 := dist_triangle (a k + h) (a k) z₀
    have h3 := hnodedist k
    rw [h1] at h2
    linarith
  -- nodes are never moved onto the singular set by the sequence or its limit
  have hnodeu : ∀ (k j : ℕ), a j + u k ∈ Sᶜ := by
    intro k j hmem
    exact hnodesT j (Or.inl (Set.mem_iUnion.2 ⟨k, hmem⟩))
  have hnodeh₀ : ∀ j : ℕ, a j + h₀ ∈ Sᶜ := by
    intro j hmem
    exact hnodesT j (Or.inr hmem)
  -- the shift-analytic minor determinants vanish along the sequence
  have hvanish : ∀ (φ : JetExponent n d → ℕ) (k : ℕ),
      defectShiftMinorDet F z₀ R n d φ (u k) = 0 := by
    intro φ k
    rw [defectShiftMinorDet_eq hF n d φ hnodes (fun j => hnodeu k j)]
    refine forall_domainCoordinateMinor_det_eq_zero_of_complexityOn (hu k) ?_ φ
    intro j
    exact mem_defectDomain (hnodes j) (by simpa using hnodeu k j)
  -- identity theorem in the shift parameter
  have hrel : ∀ (φ : JetExponent n d → ℕ) (h : ℂ), ‖h‖ < R →
      (coordinateMinor (domainJetSampleRow (fun z => F (z + h) - F z) z₀ R n d) φ).det = 0 := by
    intro φ h hh
    set U : Set ℂ := (⋃ i : JetExponent n d, ((fun w : ℂ => a (φ i) + w) ⁻¹' S))ᶜ with hUdef
    have hUcount : (⋃ i : JetExponent n d, ((fun w : ℂ => a (φ i) + w) ⁻¹' S)).Countable :=
      Set.countable_iUnion fun i => hScount.preimage (fun x y hxy => by simpa using hxy)
    have hmemU : ∀ w : ℂ, (∀ j, a j + w ∈ Sᶜ) → w ∈ U := by
      intro w hw
      simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
      intro i
      exact hw (φ i)
    have hh₀U : h₀ ∈ U := hmemU h₀ hnodeh₀
    have hukU : ∀ k, u k ∈ U := fun k => hmemU (u k) (fun j => hnodeu k j)
    have hUconn : IsPreconnected U := isPreconnected_compl_of_countable hUcount hh₀U
    have hUanal : AnalyticOnNhd ℂ (defectShiftMinorDet F z₀ R n d φ) U := by
      intro w hw
      refine analyticAt_defectShiftMinorDet hF n d φ ?_
      intro i
      simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists] at hw
      exact hw i
    have hne : ∀ᶠ k in atTop, u k ≠ h₀ := by
      by_cases hex : ∃ k₀, u k₀ = h₀
      · obtain ⟨k₀, hk₀⟩ := hex
        filter_upwards [eventually_gt_atTop k₀] with k hk hkeq
        exact (Nat.ne_of_gt hk) (huinj (hkeq.trans hk₀.symm))
      · push Not at hex
        exact Filter.Eventually.of_forall hex
    have huwithin : Tendsto u atTop (𝓝[≠] h₀) := tendsto_nhdsWithin_iff.mpr ⟨hutend, hne⟩
    have hfreq : ∃ᶠ w in 𝓝[≠] h₀, defectShiftMinorDet F z₀ R n d φ w = 0 :=
      huwithin.frequently (Filter.Frequently.of_forall fun k => hvanish φ k)
    have hzero := hUanal.eqOn_zero_of_preconnected_of_frequently_eq_zero hUconn hh₀U hfreq
    have hhU : h ∈ U := hmemU h (fun j => hshift h hh j)
    have hzh : defectShiftMinorDet F z₀ R n d φ h = 0 := hzero hhU
    rwa [defectShiftMinorDet_eq hF n d φ hnodes (fun j => hshift h hh j)] at hzh
  have hconn : IsPreconnected (Sᶜ) := isPreconnected_compl_of_countable hScount hz₀
  exact differentiallyAlgebraicOn_of_deriv
    (differentiallyAlgebraicOn_deriv_of_uniform_domain_translation_relations
      hconn hF hRpos hz₀ hnodes hRpos hshift hrel)

/-- **Complexity escape.**  Along an injective convergent sequence of shifts whose translation
defects all satisfy nonzero algebraic differential equations, a hypertranscendental source forbids
the differential orders and total jet degrees from both staying bounded. -/
theorem not_exists_injective_tendsto_boundedComplexity_defect {F : ℂ → ℂ} {S : Set ℂ}
    (hSclosed : IsClosed S) (hScount : S.Countable) (hF : AnalyticOnNhd ℂ F Sᶜ)
    (hFht : ¬ DifferentiallyAlgebraicOn F Sᶜ) (N d : ℕ) :
    ¬ ∃ (u : ℕ → ℂ) (ord : ℕ → ℕ) (h₀ : ℂ), Function.Injective u ∧
      Tendsto u atTop (𝓝 h₀) ∧ (∀ k, ord k ≤ N) ∧
      ∀ k, HasDifferentialRelationOfComplexityOn (fun z => F (z + u k) - F z)
        (defectDomain S (u k)) (ord k) d := by
  rintro ⟨u, ord, h₀, huinj, hutend, hord, hu⟩
  exact hFht (differentiallyAlgebraicOn_of_boundedComplexity_defects_accumulate
    hSclosed hScount hF huinj (fun k => (hu k).mono_order (hord k)) hutend)

end

end GaloisForLFunctions.HTGeometry
