import GaloisForLFunctions.HTGeometry.DomainTranslationSlopeMinor
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# Countability of the DA translation spectrum of a meromorphic hypertranscendental source

`EntireTranslationDefectCountability` proves that a hypertranscendental *entire* function has at
most countably many differentially algebraic additive translation defects.  The card
`ht-da-translation-spectrum-countability` states the theorem for meromorphic sources.

A meromorphic function on `ℂ` is analytic off a closed countable set, so this module proves the
statement in that generality: `F` analytic on `Sᶜ` for a closed countable `S`.  Two features of the
plane make the argument work verbatim:

* the complement of a countable set in `ℂ` is preconnected, so the identity theorem still upgrades
  a sample-node relation to a relation on the whole domain;
* the sample nodes sit inside one singularity-free disc, and only countably many shifts move a node
  onto the singular set.

The dichotomy is the same as in the entire case.  Either one bounded complexity level annihilates
every small translation defect — and then the normalized `h → 0` limit makes the source itself
differentially algebraic — or each complexity level contributes only the countable zero set of a
function of the shift that is analytic off a countable set.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

/-! ## Domains with countable closed singular sets -/

theorem not_countable_univ_complex : ¬ (Set.univ : Set ℂ).Countable := by
  intro h
  refine Cardinal.not_countable_real ?_
  have hpre : (Set.univ : Set ℝ) = (fun x : ℝ => (x : ℂ)) ⁻¹' (Set.univ : Set ℂ) := by
    ext x; simp
  rw [hpre]
  exact h.preimage Complex.ofReal_injective

theorem nonempty_compl_of_countable {K : Set ℂ} (hK : K.Countable) : (Kᶜ).Nonempty := by
  by_contra hno
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hno
  exact not_countable_univ_complex (hno ▸ hK)

theorem infinite_compl_of_countable {K : Set ℂ} (hK : K.Countable) : (Kᶜ).Infinite := by
  intro hfin
  refine not_countable_univ_complex ?_
  have huniv : (Set.univ : Set ℂ) = K ∪ Kᶜ := by simp
  rw [huniv]
  exact hK.union hfin.countable

theorem isPreconnected_compl_of_countable {K : Set ℂ} (hK : K.Countable) {a : ℂ} (ha : a ∈ Kᶜ) :
    IsPreconnected Kᶜ := by
  have hset : (Set.univ \ K) = Kᶜ := by
    ext z; simp
  have hpre := isPreconnected_diff_of_countable_of_convex_complex (V := (Set.univ : Set ℂ))
    convex_univ isOpen_univ hK (a := a) ⟨Set.mem_univ a, ha⟩
  rwa [hset] at hpre

/-- The singular set of the translation defect at shift `h`. -/
def defectSingularSet (S : Set ℂ) (h : ℂ) : Set ℂ := S ∪ (fun z : ℂ => z + h) ⁻¹' S

/-- The domain of the translation defect at shift `h`. -/
def defectDomain (S : Set ℂ) (h : ℂ) : Set ℂ := (defectSingularSet S h)ᶜ

theorem countable_defectSingularSet {S : Set ℂ} (hS : S.Countable) (h : ℂ) :
    (defectSingularSet S h).Countable :=
  hS.union (hS.preimage (fun x y hxy => by simpa using hxy))

theorem isClosed_defectSingularSet {S : Set ℂ} (hS : IsClosed S) (h : ℂ) :
    IsClosed (defectSingularSet S h) :=
  hS.union (IsClosed.preimage (by fun_prop) hS)

theorem isOpen_defectDomain {S : Set ℂ} (hS : IsClosed S) (h : ℂ) :
    IsOpen (defectDomain S h) :=
  (isClosed_defectSingularSet hS h).isOpen_compl

theorem mem_defectDomain {S : Set ℂ} {h z : ℂ} (hz : z ∉ S) (hzh : z + h ∉ S) :
    z ∈ defectDomain S h := by
  simp only [defectDomain, defectSingularSet, Set.mem_compl_iff, Set.mem_union,
    Set.mem_preimage, not_or]
  exact ⟨hz, hzh⟩

theorem defectDomain_subset_compl (S : Set ℂ) (h : ℂ) : defectDomain S h ⊆ Sᶜ := by
  intro z hz
  simp only [defectDomain, defectSingularSet, Set.mem_compl_iff, Set.mem_union,
    Set.mem_preimage, not_or] at hz
  exact hz.1

theorem defectDomain_shift_mem_compl {S : Set ℂ} {h z : ℂ} (hz : z ∈ defectDomain S h) :
    z + h ∈ Sᶜ := by
  simp only [defectDomain, defectSingularSet, Set.mem_compl_iff, Set.mem_union,
    Set.mem_preimage, not_or] at hz
  exact hz.2

theorem analyticOnNhd_translationDefect {F : ℂ → ℂ} {S : Set ℂ}
    (hF : AnalyticOnNhd ℂ F Sᶜ) (h : ℂ) :
    AnalyticOnNhd ℂ (fun z => F (z + h) - F z) (defectDomain S h) := by
  intro z hz
  simp only [defectDomain, defectSingularSet, Set.mem_compl_iff, Set.mem_union,
    Set.mem_preimage, not_or] at hz
  have h1 : AnalyticAt ℂ F (z + h) := hF (z + h) hz.2
  have h2 : AnalyticAt ℂ F z := hF z hz.1
  have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) z := analyticAt_id.add analyticAt_const
  have hcomp : AnalyticAt ℂ (F ∘ fun w : ℂ => w + h) z :=
    AnalyticAt.comp (𝕜 := ℂ) (g := F) (f := fun w : ℂ => w + h) (x := z) h1 hinner
  exact hcomp.sub h2

/-! ## Jets of a translation defect, as functions of the shift -/

theorem iteratedDeriv_translationDefect {F : ℂ → ℂ} {a h : ℂ} (j : ℕ)
    (hFa : AnalyticAt ℂ F a) (hFah : AnalyticAt ℂ F (a + h)) :
    iteratedDeriv j (fun z => F (z + h) - F z) a
      = iteratedDeriv j F (a + h) - iteratedDeriv j F a := by
  have hinner : AnalyticAt ℂ (fun w : ℂ => w + h) a := analyticAt_id.add analyticAt_const
  have hcomp : AnalyticAt ℂ (F ∘ fun w : ℂ => w + h) a :=
    AnalyticAt.comp (𝕜 := ℂ) (g := F) (f := fun w : ℂ => w + h) (x := a) hFah hinner
  have htrans : ContDiffAt ℂ (j : ℕ) (fun z => F (z + h)) a := hcomp.contDiffAt
  have hbase : ContDiffAt ℂ (j : ℕ) F a := hFa.contDiffAt
  rw [show (fun z => F (z + h) - F z) = (fun z => F (z + h)) - F from rfl]
  rw [iteratedDeriv_sub htrans hbase, iteratedDeriv_comp_add_right]

/-- The jet vector of the translation defect at `a`, written manifestly through the jets of `F`. -/
def defectJetVector (F : ℂ → ℂ) (a : ℂ) (n : ℕ) (h : ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons a fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) F (a + h) - iteratedDeriv (j : ℕ) F a

/-- The differential monomial of a translation defect, as a function of the shift. -/
def defectMonAt (F : ℂ → ℂ) (a : ℂ) (n d : ℕ) (m : JetExponent n d) (h : ℂ) : ℂ :=
  ∏ i : Fin (n + 2), (defectJetVector F a n h i) ^ (m i : ℕ)

theorem defectJetVector_eq_entireJetVector {F : ℂ → ℂ} {a h : ℂ} (n : ℕ)
    (hFa : AnalyticAt ℂ F a) (hFah : AnalyticAt ℂ F (a + h)) :
    defectJetVector F a n h = entireJetVector (fun z => F (z + h) - F z) n a := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      simp only [defectJetVector, entireJetVector, Fin.cons_succ]
      exact (iteratedDeriv_translationDefect (j : ℕ) hFa hFah).symm

theorem defectMonAt_eq_jetMon {F : ℂ → ℂ} {a h : ℂ} (n d : ℕ) (m : JetExponent n d)
    (hFa : AnalyticAt ℂ F a) (hFah : AnalyticAt ℂ F (a + h)) :
    defectMonAt F a n d m h = jetMon (fun z => F (z + h) - F z) n d m a := by
  unfold defectMonAt jetMon
  rw [defectJetVector_eq_entireJetVector n hFa hFah]

theorem analyticAt_defectMonAt {F : ℂ → ℂ} {S : Set ℂ} (hF : AnalyticOnNhd ℂ F Sᶜ)
    {a h₀ : ℂ} (hah : a + h₀ ∈ Sᶜ) (n d : ℕ) (m : JetExponent n d) :
    AnalyticAt ℂ (defectMonAt F a n d m) h₀ := by
  have hbase : ∀ i : Fin (n + 2),
      AnalyticAt ℂ (fun h : ℂ => (defectJetVector F a n h i) ^ (m i : ℕ)) h₀ := by
    intro i
    refine AnalyticAt.pow ?_ _
    induction i using Fin.cases with
    | zero =>
        simpa [defectJetVector] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) h₀)
    | succ j =>
        have hd : AnalyticAt ℂ (iteratedDeriv (j : ℕ) F) (a + h₀) :=
          analyticOnNhd_iteratedDeriv hF (j : ℕ) (a + h₀) hah
        have hinner : AnalyticAt ℂ (fun h : ℂ => a + h) h₀ := analyticAt_const.add analyticAt_id
        have hcomp : AnalyticAt ℂ (iteratedDeriv (j : ℕ) F ∘ fun h : ℂ => a + h) h₀ :=
          AnalyticAt.comp (𝕜 := ℂ) (g := iteratedDeriv (j : ℕ) F)
            (f := fun h : ℂ => a + h) (x := h₀) hd hinner
        have : AnalyticAt ℂ
            (fun h : ℂ => iteratedDeriv (j : ℕ) F (a + h) - iteratedDeriv (j : ℕ) F a) h₀ :=
          hcomp.sub analyticAt_const
        simpa [defectJetVector] using this
  have heq : defectMonAt F a n d m
      = ∏ i : Fin (n + 2), fun h : ℂ => (defectJetVector F a n h i) ^ (m i : ℕ) := by
    funext h
    simp [defectMonAt, Finset.prod_apply]
  rw [heq]
  exact Finset.analyticAt_prod _ fun i _ => hbase i

/-! ## The shift-analytic minor determinant -/

/-- The sample minor determinant of the translation defects, as a function of the shift. -/
def defectShiftMinorDet (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) (h : ℂ) : ℂ :=
  (Matrix.of fun i j : JetExponent n d =>
    defectMonAt F (domainSampleNode z₀ r (φ i)) n d j h).det

theorem defectShiftMinorDet_eq {F : ℂ → ℂ} {S : Set ℂ} {z₀ : ℂ} {r : ℝ} {h : ℂ}
    (hF : AnalyticOnNhd ℂ F Sᶜ) (n d : ℕ) (φ : JetExponent n d → ℕ)
    (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Sᶜ)
    (hshift : ∀ k, domainSampleNode z₀ r k + h ∈ Sᶜ) :
    defectShiftMinorDet F z₀ r n d φ h =
      (coordinateMinor (domainJetSampleRow (fun z => F (z + h) - F z) z₀ r n d) φ).det := by
  unfold defectShiftMinorDet
  congr 1
  ext i j
  rw [coordinateMinor_apply, domainJetSampleRow]
  exact defectMonAt_eq_jetMon n d j (hF _ (hnodes (φ i))) (hF _ (hshift (φ i)))

theorem analyticAt_defectShiftMinorDet {F : ℂ → ℂ} {S : Set ℂ} (hF : AnalyticOnNhd ℂ F Sᶜ)
    {z₀ : ℂ} {r : ℝ} (n d : ℕ) (φ : JetExponent n d → ℕ) {h₀ : ℂ}
    (hshift : ∀ i : JetExponent n d, domainSampleNode z₀ r (φ i) + h₀ ∈ Sᶜ) :
    AnalyticAt ℂ (defectShiftMinorDet F z₀ r n d φ) h₀ := by
  classical
  have hentry : ∀ i j : JetExponent n d,
      AnalyticAt ℂ (defectMonAt F (domainSampleNode z₀ r (φ i)) n d j) h₀ :=
    fun i j => analyticAt_defectMonAt hF (hshift i) n d j
  have hdet : defectShiftMinorDet F z₀ r n d φ
      = ∑ σ : Equiv.Perm (JetExponent n d), fun h : ℂ => (Equiv.Perm.sign σ : ℂ) *
          ∏ i : JetExponent n d,
            defectMonAt F (domainSampleNode z₀ r (φ (σ i))) n d i h := by
    funext h
    rw [defectShiftMinorDet, Matrix.det_apply']
    simp [Finset.sum_apply]
  rw [hdet]
  refine Finset.analyticAt_sum _ fun σ _ => ?_
  refine analyticAt_const.mul ?_
  have hprodeq : (fun h : ℂ => ∏ i : JetExponent n d,
        defectMonAt F (domainSampleNode z₀ r (φ (σ i))) n d i h)
      = ∏ i : JetExponent n d, defectMonAt F (domainSampleNode z₀ r (φ (σ i))) n d i := by
    funext h
    simp [Finset.prod_apply]
  rw [hprodeq]
  exact Finset.analyticAt_prod _ fun i _ => hentry (σ i) i

/-! ## The countability theorem -/

/-- The set of shifts whose translation defect satisfies an algebraic differential equation. -/
def defectDAStabilizer (F : ℂ → ℂ) (S : Set ℂ) : Set ℂ :=
  {h : ℂ | DifferentiallyAlgebraicOn (fun z => F (z + h) - F z) (defectDomain S h)}

/-- **Meromorphic translation-spectrum countability.**  A source analytic off a closed countable
set and satisfying no algebraic differential equation there has at most countably many
differentially algebraic additive translation defects. -/
theorem countable_defectDAStabilizer {F : ℂ → ℂ} {S : Set ℂ}
    (hSclosed : IsClosed S) (hScount : S.Countable)
    (hF : AnalyticOnNhd ℂ F Sᶜ)
    (hFht : ¬ DifferentiallyAlgebraicOn F Sᶜ) :
    (defectDAStabilizer F S).Countable := by
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
  set R : ℝ := ε / 4 with hRdef
  have hRpos : 0 < R := by positivity
  have hnear : ∀ w : ℂ, dist w z₀ < 3 * R → w ∈ Sᶜ := by
    intro w hw
    refine hballsub ?_
    rw [Metric.mem_ball]
    have h3 : 3 * R < ε := by rw [hRdef]; linarith
    linarith
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
    have h1 : dist (a k + h) (a k) = ‖h‖ := by
      simp [dist_eq_norm]
    have h2 := dist_triangle (a k + h) (a k) z₀
    have h3 := hnodedist k
    rw [h1] at h2
    linarith
  by_cases hcase : ∃ n d : ℕ, ∀ (φ : JetExponent n d → ℕ) (h : ℂ), ‖h‖ < R →
      (coordinateMinor (domainJetSampleRow (fun z => F (z + h) - F z) z₀ R n d) φ).det = 0
  · exfalso
    obtain ⟨n, d, hrel⟩ := hcase
    have hconn : IsPreconnected (Sᶜ) := isPreconnected_compl_of_countable hScount hz₀
    have hderiv : DifferentiallyAlgebraicOn (deriv F) Sᶜ :=
      differentiallyAlgebraicOn_deriv_of_uniform_domain_translation_relations
        hconn hF hRpos hz₀ hnodes hRpos hshift hrel
    exact hFht (differentiallyAlgebraicOn_of_deriv hderiv)
  · push Not at hcase
    choose φ hshiftWit hwitlt hwitne using hcase
    set Bad : Set ℂ := ((fun h : ℂ => z₀ + h) ⁻¹' S) ∪ ⋃ k : ℕ, ((fun h : ℂ => a k + h) ⁻¹' S)
      with hBaddef
    have hBadCount : Bad.Countable := by
      refine Set.Countable.union ?_ (Set.countable_iUnion fun k => ?_)
      · exact hScount.preimage (fun x y hxy => by simpa using hxy)
      · exact hScount.preimage (fun x y hxy => by simpa using hxy)
    set U : ℕ × ℕ → Set ℂ := fun p =>
      (⋃ i : JetExponent p.1 p.2, ((fun h : ℂ => a (φ p.1 p.2 i) + h) ⁻¹' S))ᶜ with hUdef
    have hUcount : ∀ p : ℕ × ℕ,
        (⋃ i : JetExponent p.1 p.2, ((fun h : ℂ => a (φ p.1 p.2 i) + h) ⁻¹' S)).Countable := by
      intro p
      exact Set.countable_iUnion fun i => hScount.preimage (fun x y hxy => by simpa using hxy)
    have hmemU : ∀ (p : ℕ × ℕ) (h : ℂ), (∀ k, a k + h ∈ Sᶜ) → h ∈ U p := by
      intro p h hk
      simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
      intro i
      exact hk (φ p.1 p.2 i)
    have hUanal : ∀ p : ℕ × ℕ,
        AnalyticOnNhd ℂ (defectShiftMinorDet F z₀ R p.1 p.2 (φ p.1 p.2)) (U p) := by
      intro p h₀ hh₀
      refine analyticAt_defectShiftMinorDet hF p.1 p.2 (φ p.1 p.2) ?_
      intro i
      simp only [hUdef, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists] at hh₀
      exact hh₀ i
    have hUwit : ∀ p : ℕ × ℕ, hshiftWit p.1 p.2 ∈ U p := by
      intro p
      exact hmemU p _ (hshift _ (hwitlt p.1 p.2))
    have hUwitne : ∀ p : ℕ × ℕ,
        defectShiftMinorDet F z₀ R p.1 p.2 (φ p.1 p.2) (hshiftWit p.1 p.2) ≠ 0 := by
      intro p
      rw [defectShiftMinorDet_eq hF p.1 p.2 (φ p.1 p.2) hnodes (hshift _ (hwitlt p.1 p.2))]
      exact hwitne p.1 p.2
    have hUconn : ∀ p : ℕ × ℕ, IsPreconnected (U p) := fun p =>
      isPreconnected_compl_of_countable (hUcount p) (hUwit p)
    have hzeroCount : ∀ p : ℕ × ℕ,
        {h ∈ U p | defectShiftMinorDet F z₀ R p.1 p.2 (φ p.1 p.2) h = 0}.Countable := fun p =>
      Bottcher.analyticOnNhd_zeros_countable (hUanal p) (hUconn p) (hUwit p) (hUwitne p)
    refine Set.Countable.mono ?_ (Set.Countable.union hBadCount
      (Set.countable_iUnion fun p : ℕ × ℕ => hzeroCount p))
    intro h hh
    by_cases hbad : h ∈ Bad
    · exact Or.inl hbad
    · refine Or.inr ?_
      have hgood : ∀ k, a k + h ∈ Sᶜ := by
        intro k hmem
        exact hbad (Or.inr (Set.mem_iUnion.2 ⟨k, hmem⟩))
      have hz₀good : z₀ + h ∉ S := fun hmem => hbad (Or.inl hmem)
      have hz₀dom : z₀ ∈ defectDomain S h := mem_defectDomain hz₀ hz₀good
      have hnodesdom : ∀ k, a k ∈ defectDomain S h := fun k =>
        mem_defectDomain (hnodes k) (hgood k)
      have hdomconn : IsPreconnected (defectDomain S h) :=
        isPreconnected_compl_of_countable (countable_defectSingularSet hScount h) hz₀dom
      have hdefanal : AnalyticOnNhd ℂ (fun z => F (z + h) - F z) (defectDomain S h) :=
        analyticOnNhd_translationDefect hF h
      obtain ⟨n, d, hall⟩ :=
        (differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero (z₀ := z₀) (r := R)
          hdomconn hdefanal hz₀dom hnodesdom hRpos).1 hh
      refine Set.mem_iUnion.2 ⟨(n, d), ?_, ?_⟩
      · exact hmemU (n, d) h hgood
      · rw [defectShiftMinorDet_eq hF n d (φ n d) hnodes hgood]
        exact hall (φ n d)

end

end GaloisForLFunctions.HTGeometry
