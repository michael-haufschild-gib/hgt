import GaloisForLFunctions.HTGeometry.HolomorphicCompactOpenDomain
import GaloisForLFunctions.HTGeometry.AsymptoticFlatHypertranscendentalInvisibility
import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull

/-!
# The differentially algebraic locus is meagre in the compact-open topology

An algebraic differential equation of jet order `n` and exponent bound `d` is a linear relation
among the finitely many differential monomials of that complexity, so the differentially algebraic
locus of `O(Ω)` is the countable union of the bounded-complexity strata

```text
L (n,d) = {F : every square jet-sample determinant at points of Ω vanishes}.
```

Each stratum is closed, because a fixed jet at a fixed point of `Ω` is a continuous functional on
the compact-open holomorphic space.  Each stratum has empty interior, because at any finite set of
distinct points one can prescribe the jets

```text
v (i,c) = a i ^ ((d+1) ^ (c+1))
```

by Hermite interpolation; the resulting sample matrix is a Vandermonde matrix in disguise, since
the base-`(d+1)` digit map on exponent tuples is a bijection onto `Fin ((d+1)^(n+2))`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

variable {Ω : Set ℂ}

/-- The square sample matrix of the differential monomials at a tuple of evaluation points. -/
def jetSampleMatrix (f : ℂ → ℂ) (n d : ℕ) (p : JetExponent n d → ℂ) :
    Matrix (JetExponent n d) (JetExponent n d) ℂ :=
  Matrix.of fun i j => jetMon f n d j (p i)

/-- The bounded-complexity stratum of the compact-open holomorphic space. -/
def daCompactOpenStratum (Ω : Set ℂ) (n d : ℕ) : Set (HoloCO Ω) :=
  {F | ∀ p : JetExponent n d → ℂ, (∀ i, p i ∈ Ω) →
    (jetSampleMatrix (holoCOFun F) n d p).det = 0}

/-- The differentially algebraic locus of the compact-open holomorphic space. -/
def daCompactOpenLocus (Ω : Set ℂ) : Set (HoloCO Ω) :=
  {F | DifferentiallyAlgebraicOn (holoCOFun F) Ω}

/-! ## Each stratum is closed -/

theorem continuous_jetSampleMatrix_det (hΩ : IsOpen Ω) (n d : ℕ) {p : JetExponent n d → ℂ}
    (hp : ∀ i, p i ∈ Ω) :
    Continuous fun F : HoloCO Ω => (jetSampleMatrix (holoCOFun F) n d p).det := by
  classical
  have hentry : ∀ i j : JetExponent n d,
      Continuous fun F : HoloCO Ω => jetMon (holoCOFun F) n d j (p i) := by
    intro i j
    have hfac : ∀ c : Fin (n + 2),
        Continuous fun F : HoloCO Ω => (entireJetVector (holoCOFun F) n (p i) c) ^ (j c : ℕ) := by
      intro c
      refine Continuous.pow ?_ _
      induction c using Fin.cases with
      | zero => simpa [entireJetVector] using (continuous_const :
          Continuous fun _ : HoloCO Ω => p i)
      | succ e =>
          simpa [entireJetVector] using continuous_holoCOJet hΩ (p i) (hp i) (e : ℕ)
    have : Continuous fun F : HoloCO Ω =>
        ∏ c : Fin (n + 2), (entireJetVector (holoCOFun F) n (p i) c) ^ (j c : ℕ) :=
      continuous_finsetProd _ fun c _ => hfac c
    exact this
  have hdet : Continuous fun F : HoloCO Ω =>
      ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, jetSampleMatrix (holoCOFun F) n d p (σ i) i := by
    refine continuous_finsetSum _ fun σ _ => ?_
    refine continuous_const.mul ?_
    exact continuous_finsetProd _ fun i _ => hentry (σ i) i
  simpa only [Matrix.det_apply'] using hdet

theorem isClosed_daCompactOpenStratum (hΩ : IsOpen Ω) (n d : ℕ) :
    IsClosed (daCompactOpenStratum Ω n d) := by
  have hrw : daCompactOpenStratum Ω n d =
      ⋂ p : {p : JetExponent n d → ℂ // ∀ i, p i ∈ Ω},
        {F : HoloCO Ω | (jetSampleMatrix (holoCOFun F) n d p.1).det = 0} := by
    ext F
    simp only [daCompactOpenStratum, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h p
      exact h p.1 p.2
    · intro h p hp
      exact h ⟨p, hp⟩
  rw [hrw]
  refine isClosed_iInter fun p => ?_
  exact isClosed_eq (continuous_jetSampleMatrix_det hΩ n d p.2) continuous_const


/-! ## The stratification of the differentially algebraic locus -/

theorem exists_sampleDisc (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ (z₀ : ℂ) (r : ℝ), 0 < r ∧ z₀ ∈ Ω ∧ ∀ k, domainSampleNode z₀ r k ∈ Ω := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  refine ⟨z₀, ε / 2, by positivity, hz₀, fun k => ?_⟩
  refine hball ?_
  rw [Metric.mem_ball, dist_domainSampleNode z₀ (by positivity : (0:ℝ) < ε / 2) k]
  have hk : (2:ℝ) ≤ (k : ℝ) + 2 := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h1 : ε / 2 / ((k:ℝ) + 2) ≤ ε / 2 / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hk
  linarith

theorem domainSampleNode_injective (z₀ : ℂ) {r : ℝ} (hr : 0 < r) :
    Function.Injective (domainSampleNode z₀ r) := by
  intro i j hij
  have hi := dist_domainSampleNode z₀ hr i
  have hj := dist_domainSampleNode z₀ hr j
  rw [hij, hj] at hi
  have hine : ((i : ℝ) + 2) ≠ 0 := by positivity
  have hjne : ((j : ℝ) + 2) ≠ 0 := by positivity
  rw [div_eq_div_iff hjne hine] at hi
  have hcast : ((i : ℝ) + 2) = ((j : ℝ) + 2) := mul_left_cancel₀ (ne_of_gt hr) hi
  have hij' : (i : ℝ) = (j : ℝ) := by linarith
  exact_mod_cast hij'

theorem daCompactOpenLocus_subset_iUnion (Ω : Set ℂ) :
    daCompactOpenLocus Ω ⊆ ⋃ q : ℕ × ℕ, daCompactOpenStratum Ω q.1 q.2 := by
  classical
  intro F hF
  obtain ⟨n, d, c, hc0, hrel⟩ :=
    (differentiallyAlgebraicOn_iff_exists_jetRelationOn (holoCOFun F) Ω).1 hF
  refine Set.mem_iUnion.2 ⟨(n, d), fun p hp => ?_⟩
  refine (Matrix.exists_mulVec_eq_zero_iff (M := jetSampleMatrix (holoCOFun F) n d p)).1 ⟨c, hc0, ?_⟩
  funext i
  have := hrel (p i) (hp i)
  simpa [Matrix.mulVec, dotProduct, jetSampleMatrix, mul_comm] using this

theorem iUnion_subset_daCompactOpenLocus (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hne : Ω.Nonempty) :
    (⋃ q : ℕ × ℕ, daCompactOpenStratum Ω q.1 q.2) ⊆ daCompactOpenLocus Ω := by
  classical
  obtain ⟨z₀, r, hr, hz₀, hnodes⟩ := exists_sampleDisc hΩ hne
  intro F hF
  obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hF
  refine (differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero (z₀ := z₀) (r := r)
    hconn (analyticOnNhd_holoCOFun hΩ F) hz₀ hnodes hr).2 ⟨q.1, q.2, fun φ => ?_⟩
  have hmat : coordinateMinor (domainJetSampleRow (holoCOFun F) z₀ r q.1 q.2) φ
      = jetSampleMatrix (holoCOFun F) q.1 q.2 (fun i => domainSampleNode z₀ r (φ i)) := by
    ext i j
    rfl
  rw [hmat]
  exact hq _ (fun i => hnodes (φ i))

theorem daCompactOpenLocus_eq_iUnion (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hne : Ω.Nonempty) :
    daCompactOpenLocus Ω = ⋃ q : ℕ × ℕ, daCompactOpenStratum Ω q.1 q.2 :=
  Set.Subset.antisymm (daCompactOpenLocus_subset_iUnion Ω)
    (iUnion_subset_daCompactOpenLocus hΩ hconn hne)

/-! ## The Vandermonde witness -/

/-- The base-`(d+1)` digit expansion turns the exponent tuples into `Fin ((d+1)^(n+2))`. -/
theorem prod_geometricJet_pow (n d : ℕ) (a : ℂ) (j : JetExponent n d) :
    (∏ c : Fin (n + 2), (a ^ ((d + 1) ^ (c : ℕ))) ^ (j c : ℕ))
      = a ^ ((finFunctionFinEquiv j : Fin ((d + 1) ^ (n + 2))) : ℕ) := by
  rw [finFunctionFinEquiv_apply]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring


/-! ## Each stratum has empty interior -/

theorem exists_small_ne_zero_of_entire {Θ : ℂ → ℂ} (hΘ : Differentiable ℂ Θ)
    {t₀ : ℂ} (h1 : Θ t₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) : ∃ t : ℂ, ‖t‖ < ε ∧ Θ t ≠ 0 := by
  by_contra hno
  push Not at hno
  have hcount : {z : ℂ | Θ z = 0}.Countable :=
    _root_.HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd
      (Complex.analyticOnNhd_univ_iff_differentiable.2 hΘ) ⟨t₀, h1⟩
  have hsub : Set.Ioo (0:ℝ) ε ⊆ (fun x : ℝ => (x : ℂ)) ⁻¹' {z : ℂ | Θ z = 0} := by
    intro x hx
    refine hno _ ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
    exact hx.2
  have hIoo : (Set.Ioo (0:ℝ) ε).Countable :=
    Set.Countable.mono hsub (hcount.preimage Complex.ofReal_injective)
  rw [Cardinal.Real.Ioo_countable_iff] at hIoo
  linarith

/-- A polynomial as an element of the compact-open holomorphic space. -/
def holoCOofPolynomial (_hΩ : IsOpen Ω) (B : Polynomial ℂ) : HoloCO Ω := by
  classical
  refine ⟨⟨fun z : ↥Ω => B.eval (z : ℂ), by fun_prop⟩, ?_⟩
  show DifferentiableOn ℂ (holoExtend Ω (fun z : ↥Ω => B.eval (z : ℂ))) Ω
  have heq : Set.EqOn (holoExtend Ω (fun z : ↥Ω => B.eval (z : ℂ))) (fun z => B.eval z) Ω := by
    intro z hz
    exact holoExtend_of_mem _ hz
  exact DifferentiableOn.congr (B.differentiable.differentiableOn) (fun z hz => heq hz)

theorem holoCOFun_ofPolynomial_eqOn (hΩ : IsOpen Ω) (B : Polynomial ℂ) :
    Set.EqOn (holoCOFun (holoCOofPolynomial hΩ B)) (fun z => B.eval z) Ω := by
  intro z hz
  simp only [holoCOFun, holoCOofPolynomial]
  exact holoExtend_of_mem _ hz

theorem iteratedDeriv_holoCOofPolynomial (hΩ : IsOpen Ω) (B : Polynomial ℂ) {a : ℂ} (ha : a ∈ Ω)
    (c : ℕ) :
    iteratedDeriv c (holoCOFun (holoCOofPolynomial hΩ B)) a
      = iteratedDeriv c (fun z => B.eval z) a := by
  refine Filter.EventuallyEq.iteratedDeriv_eq c ?_
  filter_upwards [hΩ.mem_nhds ha] with w hw using holoCOFun_ofPolynomial_eqOn hΩ B hw

theorem iteratedDeriv_holoCOFun_add_smul (hΩ : IsOpen Ω) (F G : HoloCO Ω) (t : ℂ) {a : ℂ}
    (ha : a ∈ Ω) (c : ℕ) :
    iteratedDeriv c (holoCOFun (F + t • G)) a
      = iteratedDeriv c (holoCOFun F) a + t * iteratedDeriv c (holoCOFun G) a := by
  have hfun : holoCOFun (F + t • G) = fun z => holoCOFun F z + t * holoCOFun G z := by
    funext z
    simp only [holoCOFun]
    rw [show ((F + t • G : HoloCO Ω) : ↥Ω → ℂ) = (F : ↥Ω → ℂ) + t • (G : ↥Ω → ℂ) from rfl,
      holoExtend_add, holoExtend_smul]
    simp
  rw [hfun]
  have hFc : ContDiffAt ℂ (c : ℕ) (holoCOFun F) a := (analyticOnNhd_holoCOFun hΩ F a ha).contDiffAt
  have hGc : ContDiffAt ℂ (c : ℕ) (fun z => t * holoCOFun G z) a :=
    (analyticAt_const.mul (analyticOnNhd_holoCOFun hΩ G a ha)).contDiffAt
  have hGc' : ContDiffAt ℂ (c : ℕ) (holoCOFun G) a := (analyticOnNhd_holoCOFun hΩ G a ha).contDiffAt
  have hsum : (fun z => holoCOFun F z + t * holoCOFun G z)
      = holoCOFun F + fun z => t * holoCOFun G z := rfl
  rw [hsum, iteratedDeriv_add hFc hGc, iteratedDeriv_const_mul _ hGc']


/-- **No bounded-complexity stratum has interior.**  Every holomorphic function on `Ω` is the
compact-open limit of functions whose jet-sample matrix at one fixed geometric jet configuration is
a nonsingular Vandermonde matrix. -/
theorem exists_tendsto_notMem_daCompactOpenStratum (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (n d : ℕ) (F : HoloCO Ω) :
    ∃ G : ℕ → HoloCO Ω, Tendsto G atTop (𝓝 F) ∧ ∀ k, G k ∉ daCompactOpenStratum Ω n d := by
  classical
  obtain ⟨z₀, r, hr, hz₀, hnodes⟩ := exists_sampleDisc hΩ hne
  set κ : JetExponent n d → ℕ := fun i => ((Fintype.equivFin (JetExponent n d) i : Fin _) : ℕ)
    with hκdef
  have hκinj : Function.Injective κ :=
    Fin.val_injective.comp (Fintype.equivFin (JetExponent n d)).injective
  set a : JetExponent n d → ℂ := fun i => domainSampleNode z₀ r (κ i) with hadef
  have hainj : Function.Injective a := (domainSampleNode_injective z₀ hr).comp hκinj
  have hamem : ∀ i, a i ∈ Ω := fun i => hnodes (κ i)
  set w : JetExponent n d → ℕ → ℂ := fun i c => (a i) ^ ((d + 1) ^ (c + 1)) with hwdef
  set u : JetExponent n d → ℕ → ℂ := fun i c => iteratedDeriv c (holoCOFun F) (a i) with hudef
  obtain ⟨B, hB⟩ := exists_polynomial_iteratedDeriv_eval_eq a hainj (fun _ => n)
    (fun i c => w i c - u i c)
  set Pel : HoloCO Ω := holoCOofPolynomial hΩ B with hPeldef
  set jv : ℂ → JetExponent n d → Fin (n + 2) → ℂ := fun t i =>
    Fin.cons (a i) (fun e : Fin (n + 1) => u i (e : ℕ) + t * (w i (e : ℕ) - u i (e : ℕ)))
    with hjvdef
  set Θ : ℂ → ℂ := fun t =>
    (Matrix.of fun i j : JetExponent n d => ∏ c : Fin (n + 2), (jv t i c) ^ (j c : ℕ)).det
    with hΘdef
  -- the geometric configuration at `t = 1`
  have hjvone : ∀ (i : JetExponent n d) (c : Fin (n + 2)),
      jv 1 i c = (a i) ^ ((d + 1) ^ (c : ℕ)) := by
    intro i c
    induction c using Fin.cases with
    | zero => simp [hjvdef]
    | succ e => simp [hjvdef, hwdef]
  have hΘ1 : Θ 1 ≠ 0 := by
    set e2 : JetExponent n d ≃ Fin ((d + 1) ^ (n + 2)) := finFunctionFinEquiv with he2def
    have hmat : (Matrix.of fun i j : JetExponent n d => ∏ c : Fin (n + 2), (jv 1 i c) ^ (j c : ℕ))
        = (Matrix.vandermonde fun k : Fin ((d + 1) ^ (n + 2)) => a (e2.symm k)).submatrix e2 e2 := by
      ext i j
      simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply,
        Equiv.symm_apply_apply]
      rw [Finset.prod_congr rfl fun c _ => by rw [hjvone i c], prod_geometricJet_pow]
    simp only [hΘdef]
    rw [hmat, Matrix.det_submatrix_equiv_self]
    exact Matrix.det_vandermonde_ne_zero_iff.2 (hainj.comp e2.symm.injective)
  -- `Θ` is entire
  have hjvdiff : ∀ (i : JetExponent n d) (c : Fin (n + 2)),
      Differentiable ℂ fun t : ℂ => jv t i c := by
    intro i c
    induction c using Fin.cases with
    | zero => simpa [hjvdef] using (differentiable_const (a i))
    | succ e =>
        simp only [hjvdef, Fin.cons_succ]
        exact (differentiable_const _).add
          ((differentiable_id).mul (differentiable_const _))
  have hΘdiff : Differentiable ℂ Θ := by
    have hentry : ∀ i j : JetExponent n d,
        Differentiable ℂ fun t : ℂ => ∏ c : Fin (n + 2), (jv t i c) ^ (j c : ℕ) := by
      intro i j
      have heq : (fun t : ℂ => ∏ c : Fin (n + 2), (jv t i c) ^ (j c : ℕ))
          = ∏ c : Fin (n + 2), (fun t : ℂ => (jv t i c) ^ (j c : ℕ)) := by
        funext t
        simp [Finset.prod_apply]
      rw [heq]
      exact Differentiable.finsetProd fun c _ => ((hjvdiff i c).pow _)
    have hsum : Differentiable ℂ fun t : ℂ =>
        ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
          ∏ i : JetExponent n d, ∏ c : Fin (n + 2), (jv t (σ i) c) ^ ((i : JetExponent n d) c : ℕ) := by
      have heq : (fun t : ℂ =>
          ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
            ∏ i : JetExponent n d, ∏ c : Fin (n + 2),
              (jv t (σ i) c) ^ ((i : JetExponent n d) c : ℕ))
          = ∑ σ : Equiv.Perm (JetExponent n d), fun t : ℂ => (Equiv.Perm.sign σ : ℂ) *
            ∏ i : JetExponent n d, ∏ c : Fin (n + 2),
              (jv t (σ i) c) ^ ((i : JetExponent n d) c : ℕ) := by
        funext t
        simp [Finset.sum_apply]
      rw [heq]
      refine Differentiable.sum fun σ _ => ?_
      refine (differentiable_const _).mul ?_
      have heq2 : (fun t : ℂ => ∏ i : JetExponent n d, ∏ c : Fin (n + 2),
            (jv t (σ i) c) ^ ((i : JetExponent n d) c : ℕ))
          = ∏ i : JetExponent n d, fun t : ℂ => ∏ c : Fin (n + 2),
            (jv t (σ i) c) ^ ((i : JetExponent n d) c : ℕ) := by
        funext t
        simp [Finset.prod_apply]
      rw [heq2]
      exact Differentiable.finsetProd fun i _ => hentry (σ i) i
    have hrw : Θ = fun t : ℂ =>
        ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
          ∏ i : JetExponent n d, ∏ c : Fin (n + 2),
            (jv t (σ i) c) ^ ((i : JetExponent n d) c : ℕ) := by
      funext t
      simp only [hΘdef]
      exact Matrix.det_apply' _
    rw [hrw]
    exact hsum
  -- the actual jet-sample matrix of the perturbed function
  have hΘeq : ∀ t : ℂ, Θ t = (jetSampleMatrix (holoCOFun (F + t • Pel)) n d a).det := by
    intro t
    simp only [hΘdef]
    congr 1
    ext i j
    simp only [Matrix.of_apply, jetSampleMatrix, jetMon]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    induction c using Fin.cases with
    | zero => simp [entireJetVector, hjvdef]
    | succ e =>
        simp only [entireJetVector, Fin.cons_succ, hjvdef]
        rw [iteratedDeriv_holoCOFun_add_smul hΩ F Pel t (hamem i) (e : ℕ), hPeldef,
          iteratedDeriv_holoCOofPolynomial hΩ B (hamem i) (e : ℕ),
          hB i (e : ℕ) (Nat.lt_succ_iff.1 e.2)]
  -- small shifts with nonvanishing determinant
  have hchoice : ∀ k : ℕ, ∃ t : ℂ, ‖t‖ < 1 / (k + 1) ∧ Θ t ≠ 0 := by
    intro k
    exact exists_small_ne_zero_of_entire hΘdiff hΘ1 (by positivity)
  choose t ht htne using hchoice
  have htend : Tendsto t atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => (ht k).le) ?_
    exact Filter.Tendsto.congr (fun k => by rw [one_div])
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun k => F + t k • Pel, ?_, fun k hk => ?_⟩
  · have h1 : Tendsto (fun k => t k • Pel) atTop (𝓝 ((0 : ℂ) • Pel)) :=
      htend.smul tendsto_const_nhds
    rw [zero_smul] at h1
    have h2 := h1.const_add F
    simpa using h2
  · exact htne k ((hΘeq (t k)).trans (hk a hamem))

/-- Each bounded-complexity stratum is nowhere dense. -/
theorem isNowhereDense_daCompactOpenStratum (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (n d : ℕ) :
    IsNowhereDense (daCompactOpenStratum Ω n d) := by
  refine isNowhereDense_of_isClosed_of_interior_eq_empty (isClosed_daCompactOpenStratum hΩ n d) ?_
  rw [Set.eq_empty_iff_forall_notMem]
  intro F hF
  obtain ⟨G, hGtend, hGnot⟩ := exists_tendsto_notMem_daCompactOpenStratum hΩ hne n d F
  have hmem : ∀ᶠ k in atTop, G k ∈ interior (daCompactOpenStratum Ω n d) :=
    hGtend (isOpen_interior.mem_nhds hF)
  obtain ⟨k, hk⟩ := hmem.exists
  exact hGnot k (interior_subset hk)


/-! ## Meagreness of the differentially algebraic locus -/

/-- **The differentially algebraic locus is meagre.** -/
theorem isMeagre_daCompactOpenLocus (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hne : Ω.Nonempty) : IsMeagre (daCompactOpenLocus Ω) := by
  rw [daCompactOpenLocus_eq_iUnion hΩ hconn hne]
  refine isMeagre_iUnion fun q => ?_
  exact (isNowhereDense_daCompactOpenStratum hΩ hne q.1 q.2).isMeagre

/-- **The hypertranscendental locus is a dense `Gδ`.** -/
theorem isGδ_htCompactOpenLocus (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    IsGδ ((daCompactOpenLocus Ω)ᶜ) := by
  have hrw : (daCompactOpenLocus Ω)ᶜ = ⋂ q : ℕ × ℕ, (daCompactOpenStratum Ω q.1 q.2)ᶜ := by
    rw [daCompactOpenLocus_eq_iUnion hΩ hconn hne, Set.compl_iUnion]
  rw [hrw]
  exact IsGδ.iInter_of_isOpen fun q => (isClosed_daCompactOpenStratum hΩ q.1 q.2).isOpen_compl

theorem dense_htCompactOpenLocus (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    Dense ((daCompactOpenLocus Ω)ᶜ) := by
  haveI := baireSpace_holoCO hΩ
  exact dense_of_mem_residual (isMeagre_daCompactOpenLocus hΩ hconn hne)

/-! ## The continuous phase-selector law -/

/-- **No continuous map separates two dense classes.**  A continuous map into a Hausdorff space
which is constant on a dense set is that constant everywhere; in particular, if it is constant on
each of two dense sets, the two constants agree and the map is constant. -/
theorem eq_const_of_continuous_of_dense_eqOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {A : Set X} (hA : Dense A) {Φ : X → Y} (hΦ : Continuous Φ)
    {a : Y} (hAc : ∀ x ∈ A, Φ x = a) : Φ = fun _ => a :=
  hΦ.ext_on hA continuous_const (fun x hx => hAc x hx)

theorem const_eq_const_of_continuous_of_dense {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {A B : Set X} (hA : Dense A) {Φ : X → Y}
    (hΦ : Continuous Φ) {a b : Y} (hAc : ∀ x ∈ A, Φ x = a) (hBc : ∀ x ∈ B, Φ x = b)
    (hBne : B.Nonempty) : a = b := by
  obtain ⟨x, hx⟩ := hBne
  have hconst := eq_const_of_continuous_of_dense_eqOn hA hΦ hAc
  have h1 : Φ x = a := by rw [hconst]
  rw [← h1, hBc x hx]

end

end GaloisForLFunctions.HTGeometry
