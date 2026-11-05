import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistenceDecidesRH
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheArchimedeanPlaceAloneIsNotWeilPositive

/-!
# The window cone collapses onto the von Mangoldt weights

The window cone `𝒜(c)` is the set of weights with `W_λ ≥ 0` on `[−c, c]`. It is convex, antitone in `c`,
and depends only on the weights at `n ≤ e^{2c}`. Each coordinate seen with a margin to the edge lies in the
box `|λ(n)| ≤ √n(log n + C₀)`. The box is compact, Weil's functional is affine in the finitely many weights
each test sees, and the full Weil cone has at most one point. Hence, unconditionally:

* **Limit points** (`exists_subseq_tendsto_of_mem_windowCone`): a sequence `λ_k ∈ 𝒜(c_k)`, `c_k → ∞`, has a
  coordinatewise convergent subsequence, and every such limit is full-cone positive.
* **Effective uniqueness, qualitative form** (`exists_forall_abs_sub_vonMangoldt_lt`): for every `n ≥ 2` and
  `ε > 0` there is `c₀` with `|λ(n) − Λ(n)| < ε` for all `λ ∈ 𝒜(c)`, `c ≥ c₀`. The band of each weight
  shrinks to `Λ(n)` or the cone is empty.
* **Extinction** (`exists_extinction_of_ne_vonMangoldt`): a prescribed value `t ≠ Λ(n)` of one weight
  is excluded from `𝒜(c)` at a finite aperture, whatever the other weights do.
* **Dichotomy** (`exists_windowCone_eq_empty_iff`): if RH fails then `𝒜(c) = ∅` from a finite aperture on.

So "choose other weights" closes at each finite level. The rate is the content of the margin law and of the
polarization readings.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

/-- The window cone `𝒜(c)`. -/
def windowCone (c : ℝ) : Set (ℕ → ℝ) := {lam | WeilPositiveFullUpTo lam c}

theorem windowCone_anti {c c' : ℝ} (h : c' ≤ c) : windowCone c ⊆ windowCone c' :=
  fun _ hlam f hf hfs => hlam f hf (hfs.trans (Icc_subset_Icc (by linarith) h))

theorem convex_windowCone (c : ℝ) : Convex ℝ (windowCone c) :=
  DimensionZeroGeometryOfSpecZ.convex_setOf_weilPositiveFullUpTo c

/-- The cone sees only the weights at `n ≤ e^{2c}`. -/
theorem mem_windowCone_congr {c : ℝ} {lam lam' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (2 * c) → lam n = lam' n) :
    lam ∈ windowCone c ↔ lam' ∈ windowCone c :=
  DimensionZeroGeometryOfSpecZ.weilPositiveFullUpTo_congr h

/-- The box bound on the cone. -/
theorem abs_le_boxWidth_of_mem_windowCone {lam : ℕ → ℝ} {c : ℝ} (h : lam ∈ windowCone c) {n : ℕ}
    (hn : 2 ≤ n) (hc : atomLevel n ≤ c) : |lam n| ≤ boxWidth n :=
  abs_le_boxWidth_of_weilPositiveUpTo (weilPositiveUpTo_of_weilPositiveFullUpTo h) hn hc

/-- **Limit points of the cones.** A sequence of cone points at growing windows has a coordinatewise
convergent subsequence on `n ≥ 2`, and its limit is full-cone positive. -/
theorem exists_subseq_tendsto_of_mem_windowCone {lam : ℕ → ℕ → ℝ} {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop) (h : ∀ k, lam k ∈ windowCone (c k)) :
    ∃ (lam₀ : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ n, 2 ≤ n → Tendsto (fun j => lam (φ j) n) atTop (𝓝 (lam₀ n))) ∧
      WeilPositiveFull lam₀ := by
  set clamp : ℕ → ℕ → ℝ := fun k n => max (-boxWidth n) (min (boxWidth n) (lam k n)) with hclamp
  have hK : IsCompact (Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ k, clamp k ∈ Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) := by
    intro k n _
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [hclamp, mem_Icc]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  obtain ⟨lam₀, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hcoord : ∀ n, Tendsto (fun j => clamp (φ j) n) atTop (𝓝 (lam₀ n)) :=
    fun n => tendsto_pi_nhds.mp hlim n
  have hcφ : Tendsto (fun j => c (φ j)) atTop atTop := hc.comp hφ.tendsto_atTop
  have hagree : ∀ n, 2 ≤ n → ∀ᶠ j in atTop, clamp (φ j) n = lam (φ j) n := by
    intro n hn
    filter_upwards [hcφ.eventually_ge_atTop (atomLevel n)] with j hj
    have hbox := abs_le_boxWidth_of_mem_windowCone (h (φ j)) hn hj
    rw [abs_le] at hbox
    simp only [hclamp]
    rw [min_eq_right hbox.2, max_eq_right hbox.1]
  refine ⟨lam₀, φ, hφ, fun n hn => ?_, fun f hf hfc => ?_⟩
  · refine (hcoord n).congr' ?_
    filter_upwards [hagree n hn] with j hj
    exact hj
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hfs : ∀ A : ℝ, |R| ≤ A → tsupport f ⊆ Icc (-A) A := fun A hA x hx => by
    have hx' := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx'
    exact abs_le.mp (hx'.trans ((le_abs_self R).trans hA))
  set k := EF.weilTest f f with hk
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero (EF.weilTest_hasCompactSupport hfc hfc)
  set E : (ℕ → ℝ) → ℝ := fun l => (weilFullFunctional (fun _ => 0) k).re -
    ∑ n ∈ Finset.range N, (if 2 ≤ n then l n / Real.sqrt n else 0) *
      (k (Real.log n) + k (-Real.log n)).re with hE
  have hEq : ∀ l, (weilFullFunctional l k).re = E l := fun l => re_weilFullFunctional_eq_affine l hN
  have hElim : Tendsto (fun j => E (clamp (φ j))) atTop (𝓝 (E lam₀)) := by
    simp only [hE]
    refine tendsto_const_nhds.sub (tendsto_finsetSum _ fun n _ => ?_)
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn]
      exact ((hcoord n).div_const _).mul_const _
    · simp only [if_neg hn]
      exact tendsto_const_nhds
  have hEagree : ∀ᶠ j in atTop, E (clamp (φ j)) = E (lam (φ j)) := by
    have hall : ∀ᶠ j in atTop, ∀ n ∈ (Finset.range N).filter (fun n => 2 ≤ n),
        clamp (φ j) n = lam (φ j) n :=
      (Finset.eventually_all _).mpr fun n hn => hagree n (Finset.mem_filter.mp hn).2
    filter_upwards [hall] with j hj
    simp only [hE]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, if_pos h2, hj n (Finset.mem_filter.mpr ⟨hn, h2⟩)]
    · rw [if_neg h2, if_neg h2]
  have hEpos : ∀ᶠ j in atTop, 0 ≤ E (clamp (φ j)) := by
    filter_upwards [hEagree, hcφ.eventually_ge_atTop |R|] with j hj hjR
    rw [hj, ← hEq]
    exact h (φ j) f hf (hfs _ hjR)
  rw [hEq]
  exact ge_of_tendsto hElim hEpos

/-- **Effective uniqueness, qualitative form.** Every weight of every cone point at a large window is
close to the von Mangoldt weight. -/
theorem exists_forall_abs_sub_vonMangoldt_lt {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → ∀ lam ∈ windowCone c,
      |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| < ε := by
  by_contra hcon
  push Not at hcon
  have hex : ∀ k : ℕ, ∃ c : ℝ, (k : ℝ) ≤ c ∧ ∃ lam ∈ windowCone c,
      ε ≤ |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| := fun k => by
    obtain ⟨c, hc, lam, hlam, hle⟩ := hcon k
    exact ⟨c, hc, lam, hlam, hle⟩
  choose c hc lam hlam hle using hex
  have hctop : Tendsto c atTop atTop :=
    tendsto_atTop_mono hc tendsto_natCast_atTop_atTop
  obtain ⟨lam₀, φ, hφ, hlim, hW⟩ := exists_subseq_tendsto_of_mem_windowCone hctop hlam
  have heq := WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW n hn
  have ht : Tendsto (fun j => |lam (φ j) n - (ArithmeticFunction.vonMangoldt n : ℝ)|) atTop
      (𝓝 |lam₀ n - (ArithmeticFunction.vonMangoldt n : ℝ)|) :=
    ((hlim n hn).sub_const _).abs
  rw [heq, sub_self, abs_zero] at ht
  have h0 : ε ≤ (0 : ℝ) := ge_of_tendsto' ht fun j => hle (φ j)
  linarith

/-- **Extinction.** A value `t ≠ Λ(n)` of the weight at `n` is excluded from every cone beyond a finite
aperture, whatever the other weights do. -/
theorem exists_extinction_of_ne_vonMangoldt {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht : t ≠ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → ∀ lam ∈ windowCone c, lam n ≠ t := by
  obtain ⟨c₀, h⟩ := exists_forall_abs_sub_vonMangoldt_lt hn
    (abs_pos.mpr (sub_ne_zero.mpr ht))
  refine ⟨c₀, fun c hc lam hlam hne => ?_⟩
  exact lt_irrefl _ (by simpa [hne] using h c hc lam hlam)

/-- **Dichotomy.** RH holds iff every cone is nonempty; otherwise all cones past a finite aperture are
empty. -/
theorem exists_windowCone_eq_empty_iff :
    ¬ RiemannHypothesis ↔ ∃ c₀ : ℝ, ∀ c, c₀ ≤ c → windowCone c = ∅ := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := exists_level_forall_not_weilPositiveFullUpTo_of_not_riemannHypothesis h
    refine ⟨A, fun c hc => Set.eq_empty_of_forall_notMem fun lam hlam => ?_⟩
    exact hA lam (windowCone_anti hc hlam)
  · rintro ⟨c₀, h⟩ hRH
    obtain ⟨lam, hlam⟩ := riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo.mp hRH c₀
    have : lam ∈ windowCone c₀ := hlam
    rw [h c₀ le_rfl] at this
    exact this

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
