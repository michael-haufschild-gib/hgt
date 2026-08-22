import GaloisForLFunctions.HTGeometry.SliceDerivativeJointHolomorphy
import GaloisForLFunctions.HTGeometry.LinearIndependentMinorCertificate
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# The differential-algebraic fibre locus of a jointly entire family

An algebraic differential equation of jet order `n` and exponent bound `d` is a linear relation
among the finitely many differential monomials of that complexity.  For an entire function such a
relation is decided by the values of the monomials at a sequence of sample points accumulating at
the origin, hence by the vanishing of every square sample minor.

Each sample minor of a jointly entire family is entire in the family parameter.  Either one
complexity level has all its minors identically zero -- and then every fibre satisfies an algebraic
differential equation -- or every complexity level contributes only the countable zero set of a
nonzero entire function.  This is the countable-or-everything dichotomy for the fibre locus.
-/


namespace GaloisForLFunctions.HTGeometry

open Complex Set Filter Topology MeasureTheory

noncomputable section

/-- The jet vector `(z, f z, f' z, …, f⁽ⁿ⁾ z)`. -/
def entireJetVector (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z

/-- Exponent vectors of jet order `n` with every exponent at most `d`. -/
abbrev JetExponent (n d : ℕ) : Type := Fin (n + 2) → Fin (d + 1)

/-- The finitely supported exponent vector attached to a bounded exponent tuple. -/
def jetExponentToFinsupp {n d : ℕ} (m : JetExponent n d) : Fin (n + 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (m i : ℕ)

theorem jetExponentToFinsupp_apply {n d : ℕ} (m : JetExponent n d) (i : Fin (n + 2)) :
    jetExponentToFinsupp m i = (m i : ℕ) := rfl

theorem jetExponentToFinsupp_injective {n d : ℕ} :
    Function.Injective (jetExponentToFinsupp (n := n) (d := d)) := by
  intro m m' h
  funext i
  have := congrArg (fun g => g i) h
  simpa [jetExponentToFinsupp_apply, Fin.ext_iff] using this

/-- The differential monomial attached to a bounded exponent tuple. -/
def jetMon (f : ℂ → ℂ) (n d : ℕ) (m : JetExponent n d) : ℂ → ℂ :=
  fun z => ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (m i : ℕ)

theorem eval_entireJetVector_eq_sum (f : ℂ → ℂ) (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (z : ℂ) :
    MvPolynomial.eval (entireJetVector f n z) P
      = ∑ m ∈ P.support, MvPolynomial.coeff m P *
          ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (m i) := by
  rw [MvPolynomial.eval_eq']

theorem differentiable_iteratedDeriv_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (j : ℕ) : Differentiable ℂ (iteratedDeriv j f) := by
  induction j generalizing f with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ j ih =>
      have := ih (f := deriv f) hf.deriv
      simpa [iteratedDeriv_succ'] using this

theorem differentiable_jetMon {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n d : ℕ)
    (m : JetExponent n d) : Differentiable ℂ (jetMon f n d m) := by
  have h : Differentiable ℂ
      (∏ i : Fin (n + 2), fun z : ℂ => (entireJetVector f n z i) ^ (m i : ℕ)) := by
    refine Differentiable.finsetProd fun i _ => ?_
    refine Differentiable.pow ?_ _
    induction i using Fin.cases with
    | zero => simp [entireJetVector]
    | succ j => simpa [entireJetVector] using differentiable_iteratedDeriv_of_differentiable hf j
  have heq : jetMon f n d m
      = (∏ i : Fin (n + 2), fun z : ℂ => (entireJetVector f n z i) ^ (m i : ℕ)) := by
    funext z
    simp [jetMon, Finset.prod_apply]
  rw [heq]
  exact h

theorem finsupp_apply_le_sum {n : ℕ} (m : Fin n →₀ ℕ) (i : Fin n) :
    m i ≤ m.sum fun _ e => e := by
  classical
  by_cases hi : i ∈ m.support
  · exact Finset.single_le_sum (f := fun j => m j) (fun j _ => Nat.zero_le _) hi
  · simp [Finsupp.notMem_support_iff.1 hi]

/-- A bounded-exponent linear relation among the differential monomials of `f`. -/
def JetRelation (f : ℂ → ℂ) (n d : ℕ) (c : JetExponent n d → ℂ) : Prop :=
  ∀ z : ℂ, ∑ m : JetExponent n d, c m * jetMon f n d m z = 0

theorem sum_jetExponent_eq_sum_support {n d : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hd : ∀ μ ∈ P.support, ∀ i, μ i ≤ d) (g : (Fin (n + 2) →₀ ℕ) → ℂ)
    (hg : ∀ μ, μ ∉ P.support → g μ = 0) :
    ∑ m : JetExponent n d, g (jetExponentToFinsupp m) = ∑ μ ∈ P.support, g μ := by
  classical
  rw [← Finset.sum_image (f := g) (g := jetExponentToFinsupp (n := n) (d := d))
    (fun a _ b _ h => jetExponentToFinsupp_injective h)]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro μ hμ
    refine Finset.mem_image.2 ⟨fun i => ⟨μ i, Nat.lt_succ_of_le (hd μ hμ i)⟩, Finset.mem_univ _, ?_⟩
    ext i
    rfl
  · intro μ _ hμ
    exact hg μ hμ

theorem differentiallyAlgebraic_iff_exists_jetRelation (f : ℂ → ℂ) :
    DifferentiallyAlgebraic f ↔
      ∃ (n d : ℕ) (c : JetExponent n d → ℂ), c ≠ 0 ∧ JetRelation f n d c := by
  classical
  constructor
  · rintro ⟨n, P, hP0, hP⟩
    refine ⟨n, P.totalDegree, fun m => MvPolynomial.coeff (jetExponentToFinsupp m) P, ?_, ?_⟩
    · intro hc
      refine hP0 (MvPolynomial.ext P 0 fun μ => ?_)
      by_cases hμ : μ ∈ P.support
      · have hbd : ∀ i, μ i ≤ P.totalDegree := fun i =>
          le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)
        have hmem : jetExponentToFinsupp (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ :
            Fin (P.totalDegree + 1))) = μ := by
          ext i
          rfl
        have := congrFun hc (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ : Fin (P.totalDegree + 1)))
        rw [hmem] at this
        simpa using this
      · simp [MvPolynomial.notMem_support_iff.1 hμ]
    · intro z
      have hbd : ∀ μ ∈ P.support, ∀ i, μ i ≤ P.totalDegree := fun μ hμ i =>
        le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)
      have := sum_jetExponent_eq_sum_support (d := P.totalDegree) P hbd
        (fun μ => MvPolynomial.coeff μ P * ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (μ i))
        (fun μ hμ => by simp [MvPolynomial.notMem_support_iff.1 hμ])
      rw [show (∑ m : JetExponent n P.totalDegree,
          (fun m => MvPolynomial.coeff (jetExponentToFinsupp m) P) m * jetMon f n P.totalDegree m z)
          = ∑ m : JetExponent n P.totalDegree,
            (fun μ => MvPolynomial.coeff μ P * ∏ i : Fin (n + 2),
              (entireJetVector f n z i) ^ (μ i)) (jetExponentToFinsupp m) from rfl, this,
        ← eval_entireJetVector_eq_sum]
      exact hP z
  · rintro ⟨n, d, c, hc0, hrel⟩
    refine ⟨n, ∑ m : JetExponent n d, MvPolynomial.monomial (jetExponentToFinsupp m) (c m), ?_, ?_⟩
    · intro hP
      apply hc0
      funext m
      have := congrArg (MvPolynomial.coeff (jetExponentToFinsupp m)) hP
      rw [MvPolynomial.coeff_sum] at this
      rw [Finset.sum_eq_single m] at this
      · simpa [MvPolynomial.coeff_monomial] using this
      · intro b _ hb
        rw [MvPolynomial.coeff_monomial, if_neg]
        exact fun h => hb (jetExponentToFinsupp_injective h)
      · intro h
        exact absurd (Finset.mem_univ m) h
    · intro z
      rw [MvPolynomial.eval_sum]
      have : ∀ m : JetExponent n d,
          MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
            (MvPolynomial.monomial (jetExponentToFinsupp m) (c m))
            = c m * jetMon f n d m z := by
        intro m
        rw [MvPolynomial.eval_monomial, Finsupp.prod_pow]
        rfl
      rw [Finset.sum_congr rfl fun m _ => this m]
      exact hrel z

/-- Sample points accumulating at the origin. -/
def sampleNode (k : ℕ) : ℂ := ((k : ℂ) + 1)⁻¹

theorem sampleNode_ne_zero (k : ℕ) : sampleNode k ≠ 0 := by
  refine inv_ne_zero ?_
  intro h
  have : ((k : ℂ) + 1).re = 0 := by rw [h]; simp
  simp at this
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem tendsto_sampleNode : Tendsto sampleNode atTop (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within sampleNode ?_ ?_
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ k : ℕ, ‖sampleNode k‖ = 1 / ((k : ℝ) + 1) := by
      intro k
      rw [sampleNode, norm_inv, one_div]
      congr 1
      rw [show ((k : ℂ) + 1) = ((((k : ℝ) + 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hbase : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [hnorm] using hbase
  · filter_upwards with k using sampleNode_ne_zero k

/-- The sample row of a differential monomial. -/
def jetSampleRow (f : ℂ → ℂ) (n d : ℕ) (m : JetExponent n d) : ℕ → ℂ :=
  fun k => jetMon f n d m (sampleNode k)

theorem jetRelation_iff_rows {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n d : ℕ)
    (c : JetExponent n d → ℂ) :
    JetRelation f n d c ↔ ∀ k : ℕ, ∑ m : JetExponent n d, c m * jetSampleRow f n d m k = 0 := by
  refine ⟨fun h k => h (sampleNode k), fun h => ?_⟩
  have hgdiff : Differentiable ℂ (fun z => ∑ m : JetExponent n d, c m * jetMon f n d m z) := by
    have h : Differentiable ℂ (∑ m : JetExponent n d, fun z : ℂ => c m * jetMon f n d m z) :=
      Differentiable.sum fun m _ => (differentiable_jetMon hf n d m).const_mul _
    have heq : (fun z => ∑ m : JetExponent n d, c m * jetMon f n d m z)
        = ∑ m : JetExponent n d, fun z : ℂ => c m * jetMon f n d m z := by
      funext z
      simp [Finset.sum_apply]
    rw [heq]
    exact h
  have hga : AnalyticOnNhd ℂ (fun z => ∑ m : JetExponent n d, c m * jetMon f n d m z) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 hgdiff
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (∑ m : JetExponent n d, c m * jetMon f n d m z) = 0 :=
    tendsto_sampleNode.frequently (Filter.Frequently.of_forall fun k => h k)
  have := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ 0) hfreq
  intro z
  exact this (Set.mem_univ z)

theorem exists_jetRelation_iff_not_linearIndependent (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (n d : ℕ) :
    (∃ c : JetExponent n d → ℂ, c ≠ 0 ∧ JetRelation f n d c)
      ↔ ¬ LinearIndependent ℂ (jetSampleRow f n d) := by
  classical
  rw [Fintype.linearIndependent_iff]
  push Not
  constructor
  · rintro ⟨c, hc0, hrel⟩
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, c m₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc0 (funext hall)
    refine ⟨c, ?_, m₀, hm₀⟩
    funext k
    have := (jetRelation_iff_rows hf n d c).1 hrel k
    simpa [Finset.sum_apply] using this
  · rintro ⟨c, hsum, m₀, hm₀⟩
    refine ⟨c, ?_, ?_⟩
    · intro h
      exact hm₀ (by rw [h]; rfl)
    · refine (jetRelation_iff_rows hf n d c).2 fun k => ?_
      have := congrFun hsum k
      simpa [Finset.sum_apply] using this

theorem not_linearIndependent_iff_forall_coordinateMinor_det_eq_zero (f : ℂ → ℂ) (n d : ℕ) :
    ¬ LinearIndependent ℂ (jetSampleRow f n d)
      ↔ ∀ φ : JetExponent n d → ℕ, (coordinateMinor (jetSampleRow f n d) φ).det = 0 := by
  classical
  constructor
  · intro h φ
    by_contra hdet
    exact h (linearIndependent_of_coordinateMinor_det_ne_zero _ φ hdet)
  · intro h hind
    obtain ⟨φ, hφ⟩ := exists_coordinateMinor_det_ne_zero _ hind
    exact hφ (h φ)

/-- **The determinant certificate for an algebraic differential equation.**  An entire function
satisfies an algebraic differential equation exactly when, at some jet order and exponent bound,
every sample minor of its differential monomials is singular. -/
theorem differentiallyAlgebraic_iff_forall_coordinateMinor_det_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) :
    DifferentiallyAlgebraic f ↔
      ∃ n d : ℕ, ∀ φ : JetExponent n d → ℕ, (coordinateMinor (jetSampleRow f n d) φ).det = 0 := by
  rw [differentiallyAlgebraic_iff_exists_jetRelation]
  constructor
  · rintro ⟨n, d, c, hc0, hrel⟩
    exact ⟨n, d, (not_linearIndependent_iff_forall_coordinateMinor_det_eq_zero f n d).1
      ((exists_jetRelation_iff_not_linearIndependent f hf n d).1 ⟨c, hc0, hrel⟩)⟩
  · rintro ⟨n, d, h⟩
    obtain ⟨c, hc0, hrel⟩ := (exists_jetRelation_iff_not_linearIndependent f hf n d).2
      ((not_linearIndependent_iff_forall_coordinateMinor_det_eq_zero f n d).2 h)
    exact ⟨n, d, c, hc0, hrel⟩

/-- The sample minor determinant of a fibre of a two-variable family. -/
def familyMinorDet (Φ : ℂ × ℂ → ℂ) (n d : ℕ) (φ : JetExponent n d → ℕ) (t : ℂ) : ℂ :=
  (coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ).det

theorem differentiable_param_entireJetVector {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (n : ℕ)
    (z : ℂ) (a : Fin (n + 2)) :
    Differentiable ℂ fun t : ℂ => entireJetVector (fun w => Φ (t, w)) n z a := by
  induction a using Fin.cases with
  | zero => simp [entireJetVector]
  | succ j => simpa [entireJetVector] using differentiable_param_iteratedDeriv hΦ (j : ℕ) z

theorem differentiable_familyMinorDet {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) : Differentiable ℂ (familyMinorDet Φ n d φ) := by
  classical
  have hentry : ∀ i j : JetExponent n d, Differentiable ℂ fun t : ℂ =>
      coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ i j := by
    intro i j
    have h : Differentiable ℂ (∏ a : Fin (n + 2), fun t : ℂ =>
        (entireJetVector (fun w => Φ (t, w)) n (sampleNode (φ i)) a) ^ (j a : ℕ)) :=
      Differentiable.finsetProd fun a _ =>
        ((differentiable_param_entireJetVector hΦ n (sampleNode (φ i)) a).pow _)
    have heq : (fun t : ℂ => coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ i j)
        = (∏ a : Fin (n + 2), fun t : ℂ =>
            (entireJetVector (fun w => Φ (t, w)) n (sampleNode (φ i)) a) ^ (j a : ℕ)) := by
      funext t
      simp [coordinateMinor, jetSampleRow, jetMon, Finset.prod_apply]
    rw [heq]
    exact h
  have hdet : Differentiable ℂ fun t : ℂ =>
      ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i := by
    have h : Differentiable ℂ (∑ σ : Equiv.Perm (JetExponent n d), fun t : ℂ =>
        (Equiv.Perm.sign σ : ℂ) *
          ∏ i : JetExponent n d, coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i) := by
      refine Differentiable.sum fun σ _ => ?_
      refine Differentiable.const_mul ?_ _
      have hp : Differentiable ℂ (∏ i : JetExponent n d, fun t : ℂ =>
          coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i) :=
        Differentiable.finsetProd fun i _ => hentry (σ i) i
      have heq : (fun t : ℂ => ∏ i : JetExponent n d,
          coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i)
          = (∏ i : JetExponent n d, fun t : ℂ =>
              coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i) := by
        funext t
        simp [Finset.prod_apply]
      rw [heq]
      exact hp
    have heq : (fun t : ℂ => ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i)
        = (∑ σ : Equiv.Perm (JetExponent n d), fun t : ℂ => (Equiv.Perm.sign σ : ℂ) *
            ∏ i : JetExponent n d,
              coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i) := by
      funext t
      simp [Finset.sum_apply]
    rw [heq]
    exact h
  have hfin : familyMinorDet Φ n d φ = fun t : ℂ =>
      ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, coordinateMinor (jetSampleRow (fun z => Φ (t, z)) n d) φ (σ i) i := by
    funext t
    rw [familyMinorDet, Matrix.det_apply']
  rw [hfin]
  exact hdet

theorem differentiable_fibre {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (t : ℂ) :
    Differentiable ℂ fun z => Φ (t, z) :=
  hΦ.comp (by fun_prop)

/-- **The differential-algebraic fibre locus of a jointly entire one-parameter family is either the
whole parameter plane or countable.**  At each jet order and exponent bound the fibre relation is
the simultaneous vanishing of a countable family of sample minors, each entire in the parameter.  If
one such family vanishes identically, every fibre satisfies an algebraic differential equation;
otherwise each order contributes only the countable zero set of one nonzero entire function. -/
theorem entireFamily_daLocus_eq_univ_or_countable {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) :
    {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)} = Set.univ ∨
      {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)}.Countable := by
  classical
  by_cases hcase : ∃ n d : ℕ, ∀ (φ : JetExponent n d → ℕ) (t : ℂ), familyMinorDet Φ n d φ t = 0
  · left
    obtain ⟨n, d, h⟩ := hcase
    refine Set.eq_univ_of_forall fun t => ?_
    exact (differentiallyAlgebraic_iff_forall_coordinateMinor_det_eq_zero
      (differentiable_fibre hΦ t)).2 ⟨n, d, fun φ => h φ t⟩
  · right
    push Not at hcase
    choose φ t ht using hcase
    have hsub : {s : ℂ | DifferentiallyAlgebraic fun z => Φ (s, z)} ⊆
        ⋃ p : ℕ × ℕ, {s : ℂ | familyMinorDet Φ p.1 p.2 (φ p.1 p.2) s = 0} := by
      intro s hs
      obtain ⟨n, d, h⟩ := (differentiallyAlgebraic_iff_forall_coordinateMinor_det_eq_zero
        (differentiable_fibre hΦ s)).1 hs
      exact Set.mem_iUnion.2 ⟨(n, d), h (φ n d)⟩
    refine Set.Countable.mono hsub (Set.countable_iUnion fun p => ?_)
    exact HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd
      (Complex.analyticOnNhd_univ_iff_differentiable.2
        (differentiable_familyMinorDet hΦ p.1 p.2 (φ p.1 p.2)))
      ⟨t p.1 p.2, ht p.1 p.2⟩

/-! ### The no-transition corollaries -/

/-- **The no-transition corollary.**  A jointly entire family with one hypertranscendental fibre has
a countable differential-algebraic fibre locus. -/
theorem countable_daLocus_of_exists_hypertranscendental_fibre {Φ : ℂ × ℂ → ℂ}
    (hΦ : Differentiable ℂ Φ) {t₀ : ℂ} (ht₀ : ¬ DifferentiallyAlgebraic fun z => Φ (t₀, z)) :
    {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)}.Countable := by
  rcases entireFamily_daLocus_eq_univ_or_countable hΦ with huniv | hcount
  · exact absurd (by rw [huniv]; trivial : t₀ ∈ {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)})
      ht₀
  · exact hcount

/-- No uncountable set of parameters is contained in the differential-algebraic locus of a family
with one hypertranscendental fibre.  Intervals, arcs and sets of positive planar measure are all
uncountable, so none of them can be the locus. -/
theorem not_subset_daLocus_of_not_countable {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {t₀ : ℂ}
    (ht₀ : ¬ DifferentiallyAlgebraic fun z => Φ (t₀, z)) {S : Set ℂ} (hS : ¬ S.Countable) :
    ¬ S ⊆ {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)} := fun hsub =>
  hS ((countable_daLocus_of_exists_hypertranscendental_fibre hΦ ht₀).mono hsub)

/-- The differential-algebraic locus of a family with one hypertranscendental fibre is a Lebesgue
null set. -/
theorem volume_daLocus_eq_zero {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {t₀ : ℂ}
    (ht₀ : ¬ DifferentiallyAlgebraic fun z => Φ (t₀, z)) :
    volume {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)} = 0 :=
  (countable_daLocus_of_exists_hypertranscendental_fibre hΦ ht₀).measure_zero volume

/-- **No real threshold.**  The differential-algebraic locus of a family with one hypertranscendental
fibre is never a closed real half-line: such a half-line is uncountable. -/
theorem daLocus_ne_real_halfLine {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {t₀ : ℂ}
    (ht₀ : ¬ DifferentiallyAlgebraic fun z => Φ (t₀, z)) (lam : ℝ) :
    {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)}
      ≠ {t : ℂ | t.im = 0 ∧ lam ≤ t.re} := by
  intro hEq
  refine not_subset_daLocus_of_not_countable hΦ ht₀ (S := {t : ℂ | t.im = 0 ∧ lam ≤ t.re}) ?_
    (le_of_eq hEq.symm)
  intro hcount
  have hinj : Function.Injective fun x : ℝ => ((lam + Real.exp x : ℝ) : ℂ) := by
    intro a b hab
    have h := Complex.ofReal_injective hab
    exact Real.exp_injective (by linarith)
  have hpre : (fun x : ℝ => ((lam + Real.exp x : ℝ) : ℂ)) ⁻¹' {t : ℂ | t.im = 0 ∧ lam ≤ t.re}
      = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Complex.ofReal_im, Complex.ofReal_re,
      Set.mem_univ, iff_true, true_and]
    have := (Real.exp_pos x).le
    linarith
  have huniv : (Set.univ : Set ℝ).Countable := by
    rw [← hpre]
    exact hcount.preimage hinj
  exact Cardinal.not_countable_real huniv

end

end GaloisForLFunctions.HTGeometry
