import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliContextuality
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.GaussianDeterminantTubeUpperBound
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity

/-!
# Distance to noncontextual nearest-neighbour Pauli support

Onsite coordinates already detect a necessary condition for any
noncontextual approximant. The projected coefficient tube has an exact
Gaussian mass because the constraint is rowwise with at most one exception.
-/

open Matrix Filter Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- Sites with at least two onsite coordinates strictly above the radius. -/
def thresholdMultiAxisSites (u : PathShell n) (r : ℝ) : Set (Fin (n + 2)) :=
  multiAxisSites {ia | r < |u (.inl ia)|}

private theorem pauliNoncontextual_precomp {ι κ R : Type*} [Mul R] {A : ι → R}
    (h : PauliNoncontextual A) (f : κ → ι) : PauliNoncontextual (A ∘ f) := by
  have hn (i : κ) : PauliNoncentral (A ∘ f) i → PauliNoncentral A (f i) := by
    rintro ⟨j, hj⟩
    exact ⟨f j, hj⟩
  exact fun i j k hi hj hk hij hik => h (f i) (f j) (f k) (hn i hi) (hn j hj) (hn k hk) hij hik

/-- With no bonds, at most one multiaxis site is sufficient for
noncontextuality of the full path support. -/
theorem path_noncontextual_of_zero_bonds (v : PathShell n)
    (hz : ∀ e : Fin (n + 1) × (Fin 3 × Fin 3), v (.inr e) = 0)
    (h : (multiAxisSites {ia | v (.inl ia) ≠ 0}).Subsingleton) :
    PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) := by
  have hb := (onsiteSupport_noncontextual_iff {ia | v (.inl ia) ≠ 0}).mpr h
  let f : ActivePathLabels v → {ia : Fin (n + 2) × Fin 3 // v (.inl ia) ≠ 0}
    | ⟨.inl ia, hi⟩ => ⟨ia, hi⟩
    | ⟨.inr e, he⟩ => (he (hz e)).elim
  have hf : (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) =
      fun l => finitePauliMatrix (onsiteWord (f l).1.1 (f l).1.2) := by
    funext l
    rcases l with ⟨ia | e, he⟩
    · rfl
    · exact (he (hz e)).elim
  rw [hf]
  exact pauliNoncontextual_precomp hb f

/-- Any noncontextual approximant within the onsite coefficient radius
forces all above-radius multiaxis sites into a single site. -/
theorem thresholdMultiAxisSites_subsingleton_of_approx (u v : PathShell n) (r : ℝ)
    (hv : PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)))
    (h : ∀ ia : Fin (n + 2) × Fin 3, |u (.inl ia) - v (.inl ia)| ≤ r) :
    (thresholdMultiAxisSites u r).Subsingleton := by
  have hkeep (ia : Fin (n + 2) × Fin 3) (ha : r < |u (.inl ia)|) : v (.inl ia) ≠ 0 := by
    intro hz
    have hw := h ia
    rw [hz, sub_zero] at hw
    exact (not_lt_of_ge hw) ha
  have hsub : thresholdMultiAxisSites u r ⊆ multiAxisSites {ia | v (.inl ia) ≠ 0} := by
    rintro s ⟨a, b, ha, hb, hne⟩
    exact ⟨a, b, hkeep _ ha, hkeep _ hb, hne⟩
  exact fun _ hx _ hy => (path_noncontextual_forbids_two_multiaxis_sites v hv) (hsub hx) (hsub hy)

/-- The onsite coefficient tube is exact. Weak axes can be deleted,
and all bonds can be set to zero in the approximant. -/
theorem exists_noncontextual_onsite_approx_iff (u : PathShell n) {r : ℝ} (hr : 0 ≤ r) :
    (∃ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) ∧
      ∀ ia : Fin (n + 2) × Fin 3, |u (.inl ia) - v (.inl ia)| ≤ r) ↔
      (thresholdMultiAxisSites u r).Subsingleton := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact thresholdMultiAxisSites_subsingleton_of_approx u v r hv h
  · intro h
    let v : PathShell n := WithLp.toLp 2 fun l => match l with
      | .inl ia => if r < |u (.inl ia)| then u (.inl ia) else 0
      | .inr _ => 0
    have hActive : {ia : Fin (n + 2) × Fin 3 | v (.inl ia) ≠ 0} = {ia | r < |u (.inl ia)|} := by
      ext ia
      change (if r < |u (.inl ia)| then u (.inl ia) else 0) ≠ 0 ↔ r < |u (.inl ia)|
      by_cases hia : r < |u (.inl ia)|
      · simp only [hia, iff_true]
        exact abs_pos.mp (hr.trans_lt hia)
      · simp [hia]
    refine ⟨v, ?_, fun ia => ?_⟩
    · apply path_noncontextual_of_zero_bonds v (fun _ => rfl)
      rw [hActive]
      exact h
    · change |u (.inl ia) - (if r < |u (.inl ia)| then u (.inl ia) else 0)| ≤ r
      by_cases hi : r < |u (.inl ia)|
      · simpa only [if_pos hi, sub_self, abs_zero] using hr
      · simpa only [if_neg hi, sub_zero] using le_of_not_gt hi

/-- Orthogonality of the path Pauli words converts operator error into
a bound on the full Euclidean coefficient error. -/
theorem pathShell_dist_le_pathHamiltonian_dist (u v : PathShell n) :
    ‖u - v‖ ≤ ‖pathHamiltonian u - pathHamiltonian v‖ := by
  classical
  let e : PathLabel n ↪ (Fin (n + 2) → Option (Fin 3)) := ⟨pathWord, pathWord_injective⟩
  let E := Finset.univ.map e
  let J (P : Fin (n + 2) → Option (Fin 3)) : ℂ :=
    if h : ∃ l : PathLabel n, pathWord l = P then ((u h.choose - v h.choose : ℝ) : ℂ) else 0
  have hJ (l : PathLabel n) : J (e l) = ((u l - v l : ℝ) : ℂ) := by
    have hl : ∃ j : PathLabel n, pathWord j = e l := ⟨l, rfl⟩
    have he : hl.choose = l := pathWord_injective hl.choose_spec
    simp only [J, dif_pos hl, he]
  have hzero (P : Fin (n + 2) → Option (Fin 3)) (hp : P ∉ E) : J P = 0 := by
    refine dif_neg ?_
    rintro ⟨l, hl⟩
    exact hp (Finset.mem_map.mpr ⟨l, Finset.mem_univ _, hl⟩)
  have hH : (∑ P, J P • finitePauliMatrix P) = pathHamiltonian u - pathHamiltonian v := by
    have hE : (∑ P ∈ E, J P • finitePauliMatrix P) = ∑ P, J P • finitePauliMatrix P :=
      Finset.sum_subset (Finset.subset_univ _) fun P _ hp => by rw [hzero P hp, zero_smul]
    rw [← hE, pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, ← Finset.sum_sub_distrib]
    change (∑ P ∈ Finset.univ.map e, J P • finitePauliMatrix P) = _
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hJ, Complex.ofReal_sub, sub_smul]
    rfl
  have hsq : (∑ P, ‖J P‖ ^ 2) = ∑ l : PathLabel n, ‖(u - v) l‖ ^ 2 := by
    have hE : (∑ P ∈ E, ‖J P‖ ^ 2) = ∑ P, ‖J P‖ ^ 2 :=
      Finset.sum_subset (Finset.subset_univ _) fun P _ hp => by rw [hzero P hp, norm_zero, zero_pow (by omega)]
    rw [← hE]
    change (∑ P ∈ Finset.univ.map e, ‖J P‖ ^ 2) = _
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun l _ => by rw [hJ, Complex.norm_real]; rfl
  rw [EuclideanSpace.norm_eq, ← hsq, ← hH]
  exact le_opNorm_pauliCombination J

private theorem abs_pathShell_sub_apply_le_norm (u v : PathShell n) (l : PathLabel n) :
    |u l - v l| ≤ ‖u - v‖ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (abs_nonneg (u l - v l))]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun i _ => sq_nonneg (‖(u - v) i‖)) (Finset.mem_univ l)

/-- An operator-norm tube around noncontextual path Hamiltonians is
contained in the exact onsite coefficient tube of the same radius. -/
theorem thresholdMultiAxisSites_subsingleton_of_operator_approx (u v : PathShell n) (r : ℝ)
    (hv : PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)))
    (h : ‖pathHamiltonian u - pathHamiltonian v‖ ≤ r) :
    (thresholdMultiAxisSites u r).Subsingleton :=
  thresholdMultiAxisSites_subsingleton_of_approx u v r hv fun ia =>
    (abs_pathShell_sub_apply_le_norm u v (.inl ia)).trans ((pathShell_dist_le_pathHamiltonian_dist u v).trans h)

/-- Outcomes with at most one coordinate outside the specified set. -/
def atMostOneOutside {ι X : Type*} (A : Set X) : Set (ι → X) :=
  {x | ({i | x i ∉ A} : Set ι).Subsingleton}

private def exceptionBox {ι X : Type*} [Fintype ι] [DecidableEq ι] (A : Set X) (i : Option ι) : Set (ι → X) :=
  ((Finset.univ : Finset ι) : Set ι).pi fun j => if i = some j then Aᶜ else A

private theorem mem_exceptionBox_iff {ι X : Type*} [Fintype ι] [DecidableEq ι]
    (A : Set X) (i : Option ι) (x : ι → X) :
    x ∈ exceptionBox A i ↔ ∀ j, (x j ∉ A ↔ i = some j) := by
  have he : x ∈ exceptionBox A i ↔ ∀ j, x j ∈ if i = some j then Aᶜ else A := by
    simp [exceptionBox, Set.mem_pi]
  rw [he]
  constructor
  · intro hx j
    have h := hx j
    by_cases hi : i = some j
    · rw [if_pos hi] at h
      exact ⟨fun _ => hi, fun _ => h⟩
    · rw [if_neg hi] at h
      exact ⟨fun hn => (hn h).elim, fun he => (hi he).elim⟩
  · intro hx j
    by_cases hi : i = some j
    · rw [if_pos hi]
      exact (hx j).mpr hi
    · rw [if_neg hi]
      by_contra hn
      exact hi ((hx j).mp hn)

private theorem atMostOneOutside_eq_union {ι X : Type*} [Fintype ι] [DecidableEq ι] (A : Set X) :
    atMostOneOutside (ι := ι) A = ⋃ i : Option ι, exceptionBox A i := by
  ext x
  rw [mem_iUnion]
  constructor
  · intro hx
    change ({i | x i ∉ A} : Set ι).Subsingleton at hx
    by_cases he : ∃ j, x j ∉ A
    · obtain ⟨j, hj⟩ := he
      refine ⟨some j, (mem_exceptionBox_iff A _ _).mpr fun k => ?_⟩
      exact ⟨fun hk => congrArg some (hx hj hk), fun h => (Option.some.inj h) ▸ hj⟩
    · refine ⟨none, (mem_exceptionBox_iff A _ _).mpr fun j => ?_⟩
      exact ⟨fun hj => (he ⟨j, hj⟩).elim, fun h => by cases h⟩
  · rintro ⟨i, hi⟩
    intro j hj k hk
    have hc := (mem_exceptionBox_iff A i x).mp hi
    exact Option.some.inj (((hc j).mp hj).symm.trans ((hc k).mp hk))

private theorem exceptionBox_measurable {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] {A : Set X} (hA : MeasurableSet A) (i : Option ι) :
    MeasurableSet (exceptionBox A i) := by
  unfold exceptionBox
  apply MeasurableSet.pi (Set.to_countable _)
  intro j _
  split_ifs
  · exact hA.compl
  · exact hA

theorem measurableSet_atMostOneOutside {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {A : Set X} (hA : MeasurableSet A) : MeasurableSet (atMostOneOutside (ι := ι) A) := by
  classical
  rw [atMostOneOutside_eq_union]
  exact MeasurableSet.iUnion (exceptionBox_measurable hA)

/-- Exact probability of at most one exception in finitely many iid coordinates. -/
theorem infinitePi_atMostOneOutside {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {A : Set X} (hA : MeasurableSet A) :
    (Measure.infinitePi fun _ : ι => μ) (atMostOneOutside (ι := ι) A) =
      μ A ^ Fintype.card ι + (Fintype.card ι : ℝ≥0∞) * (μ Aᶜ * μ A ^ (Fintype.card ι - 1)) := by
  classical
  let ν := Measure.infinitePi fun _ : ι => μ
  have hdisj : Pairwise (Function.onFun Disjoint (exceptionBox A : Option ι → Set (ι → X))) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro x hi hj
    have hs (k : ι) : i = some k ↔ j = some k :=
      (((mem_exceptionBox_iff A i x).mp hi) k).symm.trans (((mem_exceptionBox_iff A j x).mp hj) k)
    apply hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some k => cases (hs k).mpr rfl
    | some k => exact ((hs k).mp rfl).symm
  have hbox (i : Option ι) : ν (exceptionBox A i) = ∏ j : ι, μ (if i = some j then Aᶜ else A) := by
    unfold ν exceptionBox
    apply Measure.infinitePi_pi (fun _ : ι => μ)
    intro j _
    split_ifs
    · exact hA.compl
    · exact hA
  have hnone : ν (exceptionBox A (none : Option ι)) = μ A ^ Fintype.card ι := by
    rw [hbox]
    simp
  have hsome (i : ι) : ν (exceptionBox A (some i)) = μ Aᶜ * μ A ^ (Fintype.card ι - 1) := by
    rw [hbox, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    have he : (∏ j ∈ Finset.univ.erase i, μ (if some i = some j then Aᶜ else A)) =
        μ A ^ (Fintype.card ι - 1) := by
      calc
        _ = ∏ _ ∈ Finset.univ.erase i, μ A := by
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [if_neg fun h => (Finset.ne_of_mem_erase hj) (Option.some.inj h).symm]
        _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    rw [he]
  change ν (atMostOneOutside (ι := ι) A) = _
  rw [atMostOneOutside_eq_union, measure_iUnion hdisj (exceptionBox_measurable hA), tsum_fintype,
    Fintype.sum_option, hnone]
  simp only [hsome, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private def weakAxis (r : ℝ) : Set ℝ := {x | |x| ≤ r}

private theorem measurableSet_weakAxis (r : ℝ) : MeasurableSet (weakAxis r) :=
  measurableSet_le measurable_id.abs measurable_const

private def simpleOnsiteRow (r : ℝ) : Set (Fin 3 → ℝ) := atMostOneOutside (weakAxis r)

/-- The joint standard Gaussian law of a site's three onsite axes. -/
def gaussianOnsiteRowLaw : Measure (Fin 3 → ℝ) :=
  Measure.infinitePi fun _ => gaussianReal 0 1

/-- The one-coordinate mass of the interval from `-r` to `r`. -/
def gaussianWeakAxisMass (r : ℝ) : ℝ≥0∞ := (gaussianReal 0 1) (weakAxis r)

/-- Probability that at most one of a site's three axes exceeds the radius. -/
def gaussianSimpleOnsiteMass (r : ℝ) : ℝ≥0∞ := gaussianOnsiteRowLaw (simpleOnsiteRow r)

theorem gaussianSimpleOnsiteMass_eq (r : ℝ) : gaussianSimpleOnsiteMass r =
    gaussianWeakAxisMass r ^ 3 + 3 * ((1 - gaussianWeakAxisMass r) * gaussianWeakAxisMass r ^ 2) := by
  have hc : (gaussianReal 0 1) (weakAxis r)ᶜ = 1 - gaussianWeakAxisMass r := by
    unfold gaussianWeakAxisMass
    rw [measure_compl (measurableSet_weakAxis r) (measure_ne_top _ _), measure_univ]
  unfold gaussianSimpleOnsiteMass gaussianWeakAxisMass simpleOnsiteRow gaussianOnsiteRowLaw
  rw [infinitePi_atMostOneOutside (ι := Fin 3) (gaussianReal 0 1) (measurableSet_weakAxis r), hc]
  rfl

/-- The three onsite coefficients at one site in the infinite disorder draw. -/
def gaussianOnsiteRow (ω : PathPauliDisorder) (i : ℕ) (a : Fin 3) : ℝ := ω (i, .inl a)

/-- Selecting distinct sites preserves the independent onsite row laws. -/
theorem measurePreserving_gaussianOnsiteRows {ι : Type*} (site : ι → ℕ) (hsite : Function.Injective site) :
    MeasurePreserving (fun ω i => gaussianOnsiteRow ω (site i)) pathPauliDisorderLaw
      (Measure.infinitePi fun _ : ι => gaussianOnsiteRowLaw) := by
  let F (p : ι × Fin 3) : ℕ × PathPauliDirections := (site p.1, .inl p.2)
  have hf : Function.Injective F := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    obtain ⟨he, hb⟩ := Prod.mk.inj h
    exact Prod.ext (hsite he) (Sum.inl.inj hb)
  let R (ω : PathPauliDisorder) (p : ι × Fin 3) := ω (F p)
  let ν : Measure ((ι × Fin 3) → ℝ) := Measure.infinitePi fun _ => gaussianReal 0 1
  have hR : MeasurePreserving R pathPauliDisorderLaw ν :=
    ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _), Measure.map_infinitePi_infinitePi_of_inj hf⟩
  have hC : MeasurePreserving (MeasurableEquiv.curry ι (Fin 3) ℝ) ν
      (Measure.infinitePi fun _ : ι => gaussianOnsiteRowLaw) :=
    ⟨(MeasurableEquiv.curry ..).measurable, Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)⟩
  exact hC.comp hR

private def onsiteRows (n : ℕ) (ω : PathPauliDisorder) (i : Fin (n + 2)) : Fin 3 → ℝ :=
  gaussianOnsiteRow ω i.val

private theorem measurePreserving_onsiteRows (n : ℕ) :
    MeasurePreserving (onsiteRows n) pathPauliDisorderLaw
      (Measure.infinitePi fun _ : Fin (n + 2) => gaussianOnsiteRowLaw) :=
  measurePreserving_gaussianOnsiteRows Fin.val Fin.val_injective

/-- The Gaussian tube measured only in the onsite coordinate projection. -/
def noncontextualOnsiteTube (n : ℕ) (r : ℝ) : Set PathPauliDisorder :=
  {ω | ∃ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) ∧
    ∀ ia : Fin (n + 2) × Fin 3, |pathPauliDisorderShell ω n (.inl ia) - v (.inl ia)| ≤ r}

/-- The Gaussian operator-norm tube around noncontextual path Hamiltonians. -/
def noncontextualOperatorTube (n : ℕ) (r : ℝ) : Set PathPauliDisorder :=
  {ω | ∃ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) ∧
    ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖ ≤ r}

private theorem noncontextualOnsiteTube_eq (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    noncontextualOnsiteTube n r = onsiteRows n ⁻¹' atMostOneOutside (simpleOnsiteRow r) := by
  ext ω
  change (∃ v : PathShell n, PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) ∧
    ∀ ia : Fin (n + 2) × Fin 3, |pathPauliDisorderShell ω n (.inl ia) - v (.inl ia)| ≤ r) ↔
    ({i | onsiteRows n ω i ∉ simpleOnsiteRow r} : Set (Fin (n + 2))).Subsingleton
  rw [exists_noncontextual_onsite_approx_iff _ hr]
  have he : thresholdMultiAxisSites (pathPauliDisorderShell ω n) r = {i | onsiteRows n ω i ∉ simpleOnsiteRow r} := by
    ext i
    change (∃ a b : Fin 3, r < |onsiteRows n ω i a| ∧ r < |onsiteRows n ω i b| ∧ a ≠ b) ↔
      ¬ ({a | ¬ |onsiteRows n ω i a| ≤ r} : Set (Fin 3)).Subsingleton
    constructor
    · rintro ⟨a, b, ha, hb, hne⟩ hs
      exact hne (hs (not_le_of_gt ha) (not_le_of_gt hb))
    · intro h
      by_contra hbad
      apply h
      intro a ha b hb
      by_contra hne
      exact hbad ⟨a, b, lt_of_not_ge ha, lt_of_not_ge hb, hne⟩
  rw [he]

/-- Exact Gaussian mass of the projected tube, including the one
allowed multiaxis site. -/
theorem gaussian_measure_noncontextualOnsiteTube (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    pathPauliDisorderLaw (noncontextualOnsiteTube n r) = gaussianSimpleOnsiteMass r ^ (n + 2) +
      ((n + 2 : ℕ) : ℝ≥0∞) * ((1 - gaussianSimpleOnsiteMass r) * gaussianSimpleOnsiteMass r ^ (n + 1)) := by
  have hrow : MeasurableSet (simpleOnsiteRow r) := measurableSet_atMostOneOutside (measurableSet_weakAxis r)
  have hp := measurePreserving_onsiteRows n
  letI : IsProbabilityMeasure gaussianOnsiteRowLaw := by unfold gaussianOnsiteRowLaw; infer_instance
  have hc : gaussianOnsiteRowLaw (simpleOnsiteRow r)ᶜ = 1 - gaussianSimpleOnsiteMass r := by
    unfold gaussianSimpleOnsiteMass
    rw [measure_compl hrow (measure_ne_top _ _), measure_univ]
  rw [noncontextualOnsiteTube_eq n hr, ← Measure.map_apply hp.measurable (measurableSet_atMostOneOutside hrow),
    hp.map_eq, infinitePi_atMostOneOutside gaussianOnsiteRowLaw hrow, hc, Fintype.card_fin]
  rfl

/-- Every operator-norm tube around the noncontextual path class obeys
the exact onsite mass as an upper bound. -/
theorem gaussian_measure_noncontextualOperatorTube_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    pathPauliDisorderLaw (noncontextualOperatorTube n r) ≤ gaussianSimpleOnsiteMass r ^ (n + 2) +
      ((n + 2 : ℕ) : ℝ≥0∞) * ((1 - gaussianSimpleOnsiteMass r) * gaussianSimpleOnsiteMass r ^ (n + 1)) := by
  rw [← gaussian_measure_noncontextualOnsiteTube n hr]
  apply measure_mono
  rintro ω ⟨v, hv, h⟩
  exact ⟨v, hv, fun ia => (abs_pathShell_sub_apply_le_norm _ _ (.inl ia)).trans
    ((pathShell_dist_le_pathHamiltonian_dist _ _).trans h)⟩

/-- A Gaussian onsite row always has positive probability of two
above-radius axes. -/
theorem gaussianSimpleOnsiteMass_lt_one (r : ℝ) : gaussianSimpleOnsiteMass r < 1 := by
  let A := simpleOnsiteRow r
  let W := Icc (r + 1) (r + 2)
  let C : Set (Fin 3 → ℝ) := ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).pi fun _ => W
  have hc : C ⊆ Aᶜ := by
    intro x hx ha
    have hs (i : Fin 3) : x i ∉ weakAxis r := by
      have hi : x i ∈ W := (Set.mem_pi.mp hx) i (by simp)
      have hr : r < x i := by have := hi.1; linarith
      exact not_le_of_gt (hr.trans_le (le_abs_self _))
    have he : (0 : Fin 3) = 1 := ha (hs 0) (hs 1)
    exact Fin.zero_ne_one he
  have hmass : gaussianOnsiteRowLaw C = (gaussianReal 0 1 W) ^ 3 := by
    unfold gaussianOnsiteRowLaw C
    rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_Icc), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hp : 0 < gaussianOnsiteRowLaw Aᶜ := by
    apply lt_of_lt_of_le _ (measure_mono hc)
    rw [hmass]
    exact pos_iff_ne_zero.mpr (pow_ne_zero 3 (gaussianReal_Icc_pos (by linarith : r + 1 < r + 2)).ne')
  letI : IsProbabilityMeasure gaussianOnsiteRowLaw := by unfold gaussianOnsiteRowLaw; infer_instance
  have hA : MeasurableSet A := measurableSet_atMostOneOutside (measurableSet_weakAxis r)
  rw [measure_compl hA (measure_ne_top _ _), measure_univ] at hp
  exact tsub_pos_iff_lt.mp hp

/-- The simple-row probability has exactly quadratic order in the
one-axis interval mass. -/
theorem gaussianSimpleOnsiteMass_bounds (r : ℝ) :
    gaussianWeakAxisMass r ^ 2 ≤ gaussianSimpleOnsiteMass r ∧
      gaussianSimpleOnsiteMass r ≤ 3 * gaussianWeakAxisMass r ^ 2 := by
  let q := gaussianWeakAxisMass r
  have hq : q ≤ 1 := by
    change gaussianReal 0 1 (weakAxis r) ≤ 1
    simpa only [measure_univ] using
      (measure_mono (subset_univ (weakAxis r)) : gaussianReal 0 1 (weakAxis r) ≤ gaussianReal 0 1 univ)
  have hsum : q + (1 - q) = 1 := add_tsub_cancel_of_le hq
  have hp : gaussianSimpleOnsiteMass r = (q + 3 * (1 - q)) * q ^ 2 := by
    rw [gaussianSimpleOnsiteMass_eq]
    change q ^ 3 + 3 * ((1 - q) * q ^ 2) = _
    ring
  have hb : ∀ x : ℝ≥0∞, x ≤ 3 * x := fun x => by
    simpa only [one_mul] using mul_le_mul_left (show (1 : ℝ≥0∞) ≤ 3 by norm_num) x
  rw [hp]
  constructor
  · calc
      q ^ 2 = 1 * q ^ 2 := (one_mul _).symm
      _ ≤ (q + 3 * (1 - q)) * q ^ 2 := by
        apply mul_le_mul_left
        calc
          1 = q + (1 - q) := hsum.symm
          _ ≤ _ := add_le_add (le_refl _) (hb _)
  · apply mul_le_mul_left
    calc
      q + 3 * (1 - q) ≤ 3 * q + 3 * (1 - q) := add_le_add (hb _) (le_refl _)
      _ = 3 * (q + (1 - q)) := by rw [mul_add]
      _ = 3 := by rw [hsum, mul_one]

private theorem gaussianWeakAxisMass_le (r : ℝ) :
    gaussianWeakAxisMass r ≤ ENNReal.ofReal (2 * gaussianDensityPeak * r) := by
  have he : weakAxis r = Icc (-r) r := by
    ext x
    change |x| ≤ r ↔ -r ≤ x ∧ x ≤ r
    exact abs_le
  calc
    _ ≤ (ENNReal.ofReal gaussianDensityPeak • (volume : Measure ℝ)) (weakAxis r) :=
      gaussianReal_le_densityPeak_smul_volume _
    _ = _ := by
      rw [he, Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
        ← ENNReal.ofReal_mul gaussianDensityPeak_pos.le]
      congr 1
      ring

/-- Fixed-radius operator tubes decay exponentially with the number
of sites, at the simple-row probability raised to the number of
nonexceptional sites. -/
theorem gaussian_measure_noncontextualOperatorTube_le_power (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    pathPauliDisorderLaw (noncontextualOperatorTube n r) ≤
      ((n + 3 : ℕ) : ℝ≥0∞) * gaussianSimpleOnsiteMass r ^ (n + 1) := by
  let p := gaussianSimpleOnsiteMass r
  have hp : p ≤ 1 := (gaussianSimpleOnsiteMass_lt_one r).le
  refine (gaussian_measure_noncontextualOperatorTube_le n hr).trans ?_
  have hpow : p ^ (n + 2) ≤ p ^ (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ]
    simpa only [mul_one] using mul_le_mul_right hp (p ^ (n + 1))
  have hterm : (1 - p) * p ^ (n + 1) ≤ p ^ (n + 1) := by
    simpa only [one_mul] using mul_le_mul_left (tsub_le_self : 1 - p ≤ 1) (p ^ (n + 1))
  change p ^ (n + 2) + ((n + 2 : ℕ) : ℝ≥0∞) * ((1 - p) * p ^ (n + 1)) ≤ _
  refine (add_le_add hpow (mul_le_mul_right hterm _)).trans_eq ?_
  have he : ((n + 3 : ℕ) : ℝ≥0∞) = 1 + ((n + 2 : ℕ) : ℝ≥0∞) := by push_cast; ring
  change p ^ (n + 1) + ((n + 2 : ℕ) : ℝ≥0∞) * p ^ (n + 1) = ((n + 3 : ℕ) : ℝ≥0∞) * p ^ (n + 1)
  rw [he, add_mul, one_mul]

/-- At small radius the operator-tube bound has power `2(n+1)` in
the radius, reflecting the two axes that must vanish per regular site. -/
theorem gaussian_measure_noncontextualOperatorTube_smallBall (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    pathPauliDisorderLaw (noncontextualOperatorTube n r) ≤
      ((n + 3 : ℕ) : ℝ≥0∞) * (3 * ENNReal.ofReal (2 * gaussianDensityPeak * r) ^ 2) ^ (n + 1) := by
  refine (gaussian_measure_noncontextualOperatorTube_le_power n hr).trans ?_
  apply mul_le_mul_right
  apply pow_le_pow_left'
  exact (gaussianSimpleOnsiteMass_bounds r).2.trans
    (mul_le_mul_right (pow_le_pow_left' (gaussianWeakAxisMass_le r) 2) 3)

/-- A single infinite disorder draw eventually avoids each fixed
operator-norm tube around noncontextual support. -/
theorem gaussian_ae_eventually_outside_noncontextualOperatorTube (r : ℝ) (hr : 0 ≤ r) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n in atTop, ω ∉ noncontextualOperatorTube n r := by
  let p := gaussianSimpleOnsiteMass r
  let q := p.toReal
  have hp : p < 1 := gaussianSimpleOnsiteMass_lt_one r
  have hpTop : p ≠ ∞ := (hp.trans_le le_top).ne
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal hpTop ENNReal.one_ne_top).mpr hp
  have hs : Summable fun n : ℕ => ((n + 3 : ℕ) : ℝ) * q ^ (n + 1) := by
    have h₁ := summable_pow_mul_geometric_of_norm_lt_one 1 hq
    have h₂ := summable_geometric_of_norm_lt_one hq
    have he : (fun n : ℕ => (((n : ℝ) ^ 1 * q ^ n) + 3 * q ^ n) * q) =
        fun n : ℕ => ((n + 3 : ℕ) : ℝ) * q ^ (n + 1) := by
      funext n
      push_cast
      rw [pow_succ]
      ring
    rw [← he]
    exact (h₁.add (h₂.mul_left 3)).mul_right q
  have he (n : ℕ) : ((n + 3 : ℕ) : ℝ≥0∞) * p ^ (n + 1) =
      ENNReal.ofReal (((n + 3 : ℕ) : ℝ) * q ^ (n + 1)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((n + 3 : ℕ) : ℝ)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hpTop]
  have hbudget : (∑' n : ℕ, ((n + 3 : ℕ) : ℝ≥0∞) * p ^ (n + 1)) ≠ ∞ := by
    rw [tsum_congr he, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs]
    exact ENNReal.ofReal_ne_top
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top hbudget
  exact ENNReal.tsum_le_tsum fun n => gaussian_measure_noncontextualOperatorTube_le_power n hr

/-- On the same Gaussian draw, the operator-norm distance from every
noncontextual path Hamiltonian eventually exceeds any fixed radius. -/
theorem gaussian_ae_eventually_away_from_noncontextual :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ r : ℝ, ∀ᶠ n in atTop, ∀ v : PathShell n,
      PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1)) →
      r < ‖pathHamiltonian (pathPauliDisorderShell ω n) - pathHamiltonian v‖ := by
  have ha (m : ℕ) := gaussian_ae_eventually_outside_noncontextualOperatorTube (m : ℝ) (by positivity)
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  intro r
  obtain ⟨m, hm⟩ := exists_nat_ge r
  filter_upwards [hω m] with n hn
  intro v hv
  apply hm.trans_lt
  exact lt_of_not_ge fun he => hn ⟨v, hv, he⟩

#print axioms exists_noncontextual_onsite_approx_iff
#print axioms path_noncontextual_of_zero_bonds
#print axioms measurePreserving_gaussianOnsiteRows
#print axioms pathShell_dist_le_pathHamiltonian_dist
#print axioms thresholdMultiAxisSites_subsingleton_of_operator_approx
#print axioms infinitePi_atMostOneOutside
#print axioms gaussianSimpleOnsiteMass_eq
#print axioms gaussian_measure_noncontextualOnsiteTube
#print axioms gaussian_measure_noncontextualOperatorTube_le
#print axioms gaussianSimpleOnsiteMass_lt_one
#print axioms gaussianSimpleOnsiteMass_bounds
#print axioms gaussian_measure_noncontextualOperatorTube_le_power
#print axioms gaussian_measure_noncontextualOperatorTube_smallBall
#print axioms gaussian_ae_eventually_away_from_noncontextual

end

end GaloisForLFunctions.HTGeometry
