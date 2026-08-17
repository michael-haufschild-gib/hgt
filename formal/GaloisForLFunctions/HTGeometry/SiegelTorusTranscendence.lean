import GaloisForLFunctions.HTGeometry.SiegelChartConstruction
import GaloisForLFunctions.HTGeometry.SiegelLocalCharts
import GaloisForLFunctions.HTGeometry.SiegelCountParameters
import GaloisForLFunctions.HTGeometry.SiegelLatticeTransition
import GaloisForLFunctions.HTGeometry.SiegelAlgebraicRelation

/-!
# Siegel's bound for a compact complex torus

Any `n + 2` meromorphic functions on `ℂ^{n+1}` that are invariant under a subgroup with compact
quotient are algebraically dependent over `ℂ`.  Equivalently: the field of meromorphic functions of
a compact complex torus has transcendence degree at most its dimension.

The proof is the chartwise Schwarz count.  Cover a fundamental set by finitely many polydiscs; on
each, present every function by a *reduced* quotient of holomorphic functions.  A linear-algebra
count produces a nonzero coefficient vector whose denominator-cleared combination has a high-order
zero at every centre; the Schwarz lemma then gains a factor `(r/R)^N` on each chart, and the only
thing that can spoil the closing is the comparison of one chart with another across a period.  That
comparison is bounded exactly because the presentations are reduced: two reduced presentations of
the same fraction differ by a unit factor, and reducedness — being an open condition — holds at
every point of the chart, not only at its centre.  The comparison constant is therefore `C^m` in the
degree, which a jet order proportional to `m` beats.

The vanishing on the small polydiscs is finally globalised: the cleared combination of the *global*
presentations is entire and vanishes on a nonempty open set, hence identically.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- **Evaluating the Siegel polynomial in any commutative `ℂ`-algebra.** -/
theorem aeval_siegelPoly {N m : ℕ} {K : Type*} [CommRing K] [Algebra ℂ K]
    (a : (Fin (N + 1) → Fin (m + 1)) → ℂ) (x : Fin (N + 1) → K) :
    MvPolynomial.aeval x (siegelPoly a)
      = ∑ β : Fin (N + 1) → Fin (m + 1), algebraMap ℂ K (a β) * ∏ k, (x k) ^ (β k : ℕ) := by
  classical
  rw [siegelPoly, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [MvPolynomial.aeval_monomial]
  congr 1
  refine Finsupp.prod_fintype _ _ ?_
  intro k
  rw [pow_zero]

theorem polydiscSet_subset_ball {c : Fin n → ℂ} {R ρ : ℝ} (hR : 0 ≤ R) (hRρ : R < ρ) :
    polydiscSet c (fun _ => R) ⊆ ball c ρ := by
  intro z hz
  refine mem_ball.mpr (lt_of_le_of_lt ?_ hRρ)
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg hR).mpr fun i => ?_
  have := hz i
  rw [mem_ball, Complex.dist_eq] at this
  exact le_of_lt (by simpa using this)


/-- A finite product of analytic functions is analytic. -/
theorem analyticAt_prod_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    {ι : Type*} (s : Finset ι) {g : ι → E → ℂ} (hg : ∀ i ∈ s, AnalyticAt ℂ (g i) p) :
    AnalyticAt ℂ (fun w => ∏ i ∈ s, g i w) p := by
  have h : (fun w => ∏ i ∈ s, g i w) = ∏ i ∈ s, g i := by
    funext w
    simp
  rw [h]
  exact Finset.analyticAt_prod s hg

/-- A finite product of germs, none of which vanishes identically near a point, does not vanish
identically near that point. -/
theorem not_eventuallyEq_zero_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p : E}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → E → ℂ}
    (hg : ∀ i, AnalyticAt ℂ (g i) p) (hne : ∀ i, ¬ (g i) =ᶠ[𝓝 p] 0) :
    ¬ (fun w => ∏ i ∈ s, g i w) =ᶠ[𝓝 p] 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro hcon
      have h2 := hcon.self_of_nhds
      simp only [Finset.prod_empty, Pi.zero_apply] at h2
      exact one_ne_zero h2
  | insert a s ha ih =>
      intro hcon
      refine ih ?_
      have hprodan : AnalyticAt ℂ (fun w => ∏ i ∈ s, g i w) p :=
        analyticAt_prod_fun s fun i _ => hg i
      refine eventuallyEq_zero_of_mul_eventuallyEq_zero (hg a) hprodan (hne a) ?_
      filter_upwards [hcon] with w hw
      have hw' : ∏ i ∈ insert a s, g i w = 0 := hw
      rwa [Finset.prod_insert ha] at hw'

/-- **Siegel's bound, cleared form.**  Any `n + 2` meromorphic functions on `ℂ^{n+1}` invariant
under a subgroup with compact quotient satisfy a nonzero polynomial relation over `ℂ`, in the
denominator-cleared form that holds at *every* point. -/
theorem exists_ne_zero_siegelHomCombination_of_periodic_meromorphic
    {P : AddSubgroup (Fin (n + 1) → ℂ)} (hP : CompactSpace ((Fin (n + 1) → ℂ) ⧸ P))
    {A B : Fin (n + 2) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0)
    (hper : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p)) :
    ∃ (m : ℕ) (a : (Fin (n + 2) → Fin (m + 1)) → ℂ), a ≠ 0 ∧
      ∀ z : Fin (n + 1) → ℂ, siegelHomCombination A B m a z = 0 := by
  classical
  -- a compact fundamental set, and one radius carrying a reduced chart at every point
  obtain ⟨K, -, hKcomp, -, hfund, -, -⟩ :=
    exists_finite_centres_of_compactSpace_quotient (E := Fin (n + 1) → ℂ) hP one_pos
  obtain ⟨ρ, hρ, hchart⟩ :=
    exists_uniform_chartPackage_everywhere hA hB hB0 hper hKcomp hfund
  set R₁ : ℝ := ρ / 2 with hR₁def
  set R : ℝ := ρ / 4 with hRdef
  set r : ℝ := ρ / 8 with hrdef
  have hR₁pos : 0 < R₁ := by rw [hR₁def]; linarith
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hRR₁ : R < R₁ := by rw [hRdef, hR₁def]; linarith
  have hrR : r < R := by rw [hrdef, hRdef]; linarith
  have hRρ : R < ρ := by rw [hRdef]; linarith
  have hR₁ρ : R₁ < ρ := by rw [hR₁def]; linarith
  -- the centres
  obtain ⟨s, hsfin, hsne, hcov⟩ :=
    exists_period_centre_of_compactSpace_quotient (E := Fin (n + 1) → ℂ) hP
      (show (0 : ℝ) < r / 2 by linarith)
  letI : Fintype ↥s := hsfin.fintype
  have hsnetype : Nonempty ↥s := hsne.to_subtype
  set c : ↥s → (Fin (n + 1) → ℂ) := Subtype.val with hcdef
  choose A' B' hpack using fun i : ↥s => hchart (c i)
  -- the hypotheses of the transition
  have hAan : ∀ (i : ↥s) (k : Fin (n + 2)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (A' i k) z :=
    fun i k z hz => (hpack i).1 k z hz
  have hBan : ∀ (i : ↥s) (k : Fin (n + 2)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (B' i k) z :=
    fun i k z hz => (hpack i).2.1 k z hz
  have hred : ∀ (i : ↥s) (k : Fin (n + 2)) (z : Fin (n + 1) → ℂ), z ∈ ball (c i) ρ →
      ∀ (h1 : AnalyticAt ℂ (A' i k) z) (h2 : AnalyticAt ℂ (B' i k) z),
        IsRelPrime (analyticGermOf h1) (analyticGermOf h2) :=
    fun i k z hz h1 h2 => (hpack i).2.2.1 k z hz h1 h2
  have hBne : ∀ (i : ↥s) (k : Fin (n + 2)), ∀ z ∈ ball (c i) ρ, ¬ (B' i k) =ᶠ[𝓝 z] 0 :=
    fun i k z hz => (hpack i).2.2.2.1 k z hz
  have hcross : ∀ (i j : ↥s) (k : Fin (n + 2)) (p : Fin (n + 1) → ℂ), p ∈ P →
      ∀ z : Fin (n + 1) → ℂ, z ∈ ball (c i) ρ → z - p ∈ ball (c j) ρ →
        A' i k z * B' j k (z - p) = A' j k (z - p) * B' i k z :=
    fun i j k p hp z hz₁ hz₂ =>
      chartPackage_cross hA hB hB0 hper (hpack i) (hpack j) hp k hz₁ hz₂
  have hcover : ∀ z : Fin (n + 1) → ℂ, ∃ p ∈ P, ∃ j : ↥s,
      ‖z - p - c j‖ ≤ r / 2 ∧ z - p ∈ ball (c j) ρ := by
    intro z
    obtain ⟨p, hp, w, hw, hzw⟩ := hcov z
    refine ⟨p, hp, ⟨w, hw⟩, hzw, ?_⟩
    refine mem_ball.mpr ?_
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hzw (by linarith)
  obtain ⟨C, hC0, htr⟩ :=
    exists_uniform_siegelTransition (c := c) (A := A') (B := B') (P := P) (ρ := ρ) (r := r)
      hrpos hRρ hAan hBan hred hBne hcross hcover
  -- the counting parameters
  set D : ℝ := (max 1 C) ^ (n + 2) with hDdef
  have hD1 : 1 ≤ D := one_le_pow₀ (le_max_left 1 C)
  set q : ℝ := r / R with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq1 : q < 1 := by
    rw [hqdef, div_lt_one hRpos]
    exact hrR
  set S : ℝ := ∑' j : ℕ, (((j + 1) ^ (n + 1) : ℕ) : ℝ) * q ^ j with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact tsum_nonneg fun j => by positivity
  obtain ⟨N, m, -, hcount, hlt⟩ :=
    exists_siegel_count_params (n + 1) (Fintype.card ↥s) hD1 hS0 hq0 hq1
  -- the transition, in the form the chart assembly consumes
  have htrans : ∀ (a : (Fin (n + 2) → Fin (m + 1)) → ℂ) (i : ↥s) (t : Fin (n + 1) → ℝ),
      ∃ (j : ↥s) (y : Fin (n + 1) → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ D ^ m ∧
        siegelHomCombination (A' i) (B' i) m a (torusMap (c i) (fun _ => R) t)
          = u * siegelHomCombination (A' j) (B' j) m a (c j + y) := by
    intro a i t
    obtain ⟨j, y, u, hy, hu, heq⟩ :=
      htrans_of_uniform_siegelTransition (c := c) (A := A') (B := B') (P := P) (r := r)
        hRpos.le htr m a i t
    refine ⟨j, y, u, hy, ?_, heq⟩
    rwa [hDdef, ← pow_mul]
  -- the chartwise count
  have hA'diff : ∀ (i : ↥s) (k : Fin (n + 2)),
      DifferentiableOn ℂ (A' i k) (polydiscSet (c i) (fun _ => R₁)) := by
    intro i k z hz
    exact ((hpack i).1 k z (polydiscSet_subset_ball hR₁pos.le hR₁ρ hz)).differentiableAt
      |>.differentiableWithinAt
  have hB'diff : ∀ (i : ↥s) (k : Fin (n + 2)),
      DifferentiableOn ℂ (B' i k) (polydiscSet (c i) (fun _ => R₁)) := by
    intro i k z hz
    exact ((hpack i).2.1 k z (polydiscSet_subset_ball hR₁pos.le hR₁ρ hz)).differentiableAt
      |>.differentiableWithinAt
  obtain ⟨a, ha0, hvan⟩ :=
    exists_ne_zero_chart_vanishing_of_transition_local (m := m) (N := N) A' B' c hRpos hRR₁
      hrpos.le hrR (by positivity) hA'diff hB'diff hcount htrans hlt
  refine ⟨m, a, ha0, ?_⟩
  -- the cleared combination of the global presentations is entire and vanishes on an open set
  set H : (Fin (n + 1) → ℂ) → ℂ := siegelHomCombination A B m a with hHdef
  have hAuniv : ∀ k, AnalyticOnNhd ℂ (A k) Set.univ := fun k z _ =>
    analyticAt_of_differentiableOn isOpen_univ (hA k).differentiableOn (Set.mem_univ z)
  have hBuniv : ∀ k, AnalyticOnNhd ℂ (B k) Set.univ := fun k z _ =>
    analyticAt_of_differentiableOn isOpen_univ (hB k).differentiableOn (Set.mem_univ z)
  have hAcd : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (A k) := by
    intro k
    rw [← contDiffOn_univ]
    exact (hAuniv k).contDiffOn uniqueDiffOn_univ
  have hBcd : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (B k) := by
    intro k
    rw [← contDiffOn_univ]
    exact (hBuniv k).contDiffOn uniqueDiffOn_univ
  have hHan : AnalyticOnNhd ℂ H Set.univ := fun z _ =>
    analyticAt_of_differentiableOn isOpen_univ
      (differentiable_siegelHomCombination hAcd hBcd a).differentiableOn (Set.mem_univ z)
  obtain ⟨i₀⟩ := hsnetype
  -- a point of the small polydisc where no denominator vanishes
  have hi₀ρ : ball (c i₀) r ⊆ ball (c i₀) ρ := ball_subset_ball (by linarith)
  have hBk : ∀ (k : Fin (n + 2)) (z : Fin (n + 1) → ℂ), AnalyticAt ℂ (B k) z := fun k z =>
    analyticAt_of_differentiableOn isOpen_univ (hB k).differentiableOn (Set.mem_univ z)
  have hi₀ : c i₀ ∈ ball (c i₀) ρ := mem_ball_self hρ
  have hB'k : ∀ k : Fin (n + 2), AnalyticAt ℂ (B' i₀ k) (c i₀) := fun k => hBan i₀ k _ hi₀
  have hBglobalne : ∀ k : Fin (n + 2), ¬ (B k) =ᶠ[𝓝 (c i₀)] 0 := by
    intro k hcon
    obtain ⟨z, hz⟩ := hB0 k
    exact hz ((hBuniv k).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ (c i₀)) hcon (Set.mem_univ z))
  have hprod₁ : ¬ (fun w => ∏ k, B' i₀ k w) =ᶠ[𝓝 (c i₀)] 0 :=
    not_eventuallyEq_zero_prod Finset.univ hB'k (fun k => hBne i₀ k _ hi₀)
  have hprod₂ : ¬ (fun w => ∏ k, B k w) =ᶠ[𝓝 (c i₀)] 0 :=
    not_eventuallyEq_zero_prod Finset.univ (fun k => hBuniv k (c i₀) (Set.mem_univ _))
      hBglobalne
  have hprodne : ¬ (fun w => (∏ k, B' i₀ k w) * ∏ k, B k w) =ᶠ[𝓝 (c i₀)] 0 := by
    intro hcon
    exact hprod₂ (eventuallyEq_zero_of_mul_eventuallyEq_zero
      (analyticAt_prod_fun Finset.univ fun k _ => hB'k k)
      (analyticAt_prod_fun Finset.univ fun k _ => hBuniv k (c i₀) (Set.mem_univ _))
      hprod₁ hcon)
  obtain ⟨w₀, hw₀ball, hw₀ne⟩ := exists_ne_zero_of_not_eventuallyEq_zero hprodne hrpos
  have hne_of : ∀ w, (∏ k, B' i₀ k w) * (∏ k, B k w) ≠ 0 →
      (∀ k, B' i₀ k w ≠ 0) ∧ ∀ k, B k w ≠ 0 := by
    intro w hw
    constructor
    · intro k hk
      refine hw ?_
      have hz : ∏ k, B' i₀ k w = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk
      rw [hz, zero_mul]
    · intro k hk
      refine hw ?_
      have hz : ∏ k, B k w = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk
      rw [hz, mul_zero]
  -- the cleared global combination vanishes near `w₀`
  have hzero_of : ∀ w ∈ ball (c i₀) r, (∀ k, B' i₀ k w ≠ 0) → (∀ k, B k w ≠ 0) → H w = 0 := by
    intro w hw hB'w hBw
    have hy : ‖w - c i₀‖ ≤ r := by
      have := mem_ball.mp hw
      rw [dist_eq_norm] at this
      exact this.le
    have hvanw : siegelHomCombination (A' i₀) (B' i₀) m a w = 0 := by
      have := hvan i₀ (w - c i₀) hy
      rwa [show c i₀ + (w - c i₀) = w from by abel] at this
    have hcomb₁ : siegelCombination (fun k w => A' i₀ k w / B' i₀ k w) a w = 0 :=
      siegelCombination_eq_zero_of_hom_eq_zero (A' i₀) (B' i₀) a w hB'w hvanw
    have hquot : ∀ k, A' i₀ k w / B' i₀ k w = A k w / B k w := by
      intro k
      have hcr := (hpack i₀).2.2.2.2 k w (hi₀ρ hw)
      rw [div_eq_div_iff (hB'w k) (hBw k)]
      exact hcr.symm
    have hcomb₂ : siegelCombination (fun k w => A k w / B k w) a w = 0 := by
      rw [← hcomb₁]
      exact (siegelCombination_congr (fun k w => A k w / B k w)
        (fun k w => A' i₀ k w / B' i₀ k w) a w (fun k => (hquot k).symm))
    rw [hHdef, siegelHomCombination_eq A B a w hBw, hcomb₂, zero_mul]
  have hHev : H =ᶠ[𝓝 w₀] 0 := by
    have hball : ∀ᶠ w in 𝓝 w₀, w ∈ ball (c i₀) r := isOpen_ball.mem_nhds hw₀ball
    have hB'ev : ∀ᶠ w in 𝓝 w₀, ∀ k, B' i₀ k w ≠ 0 := by
      refine Filter.eventually_all.mpr fun k => ?_
      exact ((hBan i₀ k w₀ (hi₀ρ hw₀ball)).continuousAt).eventually_ne
        ((hne_of w₀ hw₀ne).1 k)
    have hBev : ∀ᶠ w in 𝓝 w₀, ∀ k, B k w ≠ 0 := by
      refine Filter.eventually_all.mpr fun k => ?_
      exact ((hBk k w₀).continuousAt).eventually_ne ((hne_of w₀ hw₀ne).2 k)
    filter_upwards [hball, hB'ev, hBev] with w h1 h2 h3
    exact hzero_of w h1 h2 h3
  have hHzero : ∀ z : Fin (n + 1) → ℂ, H z = 0 := fun z =>
    hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ w₀) hHev (Set.mem_univ z)
  exact hHzero

/-- **Siegel's bound.**  Any `n + 2` meromorphic functions on `ℂ^{n+1}` invariant under a subgroup
with compact quotient satisfy a nonzero polynomial relation over `ℂ`. -/
theorem exists_ne_zero_poly_of_periodic_meromorphic
    {P : AddSubgroup (Fin (n + 1) → ℂ)} (hP : CompactSpace ((Fin (n + 1) → ℂ) ⧸ P))
    {A B : Fin (n + 2) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0)
    (hper : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p)) :
    ∃ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 ∧
      ∀ z : Fin (n + 1) → ℂ, (∀ k, B k z ≠ 0) →
        MvPolynomial.eval (fun k => A k z / B k z) Q = 0 := by
  obtain ⟨m, a, ha0, hzero⟩ :=
    exists_ne_zero_siegelHomCombination_of_periodic_meromorphic hP hA hB hB0 hper
  refine ⟨siegelPoly a, siegelPoly_ne_zero ha0, ?_⟩
  intro z hBz
  rw [eval_siegelPoly_eq_siegelCombination (fun k w => A k w / B k w) a z]
  exact siegelCombination_eq_zero_of_hom_eq_zero A B a z hBz (hzero z)

end GaloisForLFunctions.HTGeometry
