import GaloisForLFunctions.HTGeometry.GermReducedPresentation
import GaloisForLFunctions.HTGeometry.UniformLocalBound
import GaloisForLFunctions.HTGeometry.GermTranslationFactorial

/-!
# A uniform transition constant for reduced chart data

The comparison a chartwise Siegel count needs on the overlaps: for a point on the large torus of one
chart, a period carrying it into the small polydisc of another chart, together with a bounded factor
relating the two presentations.

Two reduced presentations of the same meromorphic data differ by a single unit factor, and
reducedness of a presentation is an open condition, so the unit factor exists at every point of the
chart, not only at its centre.  The factor is analytic, hence bounded near each point; the closed
polydisc of a chart is compact, so one constant serves the whole chart, and there are finitely many
charts.

The factor is *independent of the degree* of the count: the transition factor of the
denominator-cleared combination of degree `m` is the `m`-th power of the product of the unit
factors, so the comparison constant grows like `C^m` while the Schwarz gain falls like `(r/R)^N`,
and the count closes with `N` proportional to `m`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n N : ℕ} {ι : Type*}

/-- **Reducedness is preserved by translation.** -/
theorem isRelPrime_germ_translate {p w : Fin n → ℂ} {A B : (Fin n → ℂ) → ℂ}
    (hA : AnalyticAt ℂ A (w - p)) (hB : AnalyticAt ℂ B (w - p))
    (hA' : AnalyticAt ℂ (fun z => A (z - p)) w) (hB' : AnalyticAt ℂ (fun z => B (z - p)) w)
    (h : IsRelPrime (analyticGermOf hA) (analyticGermOf hB)) :
    IsRelPrime (analyticGermOf hA') (analyticGermOf hB') :=
  (isRelPrime_analyticGermOf_pullback_iff (Φ := fun z : Fin n → ℂ => z - p)
    (Ψ := fun z : Fin n → ℂ => z + p) (a := w) (b := w - p)
    (analyticAt_sub_const p w) (analyticAt_add_const p (w - p)) rfl (by abel)
    (Filter.Eventually.of_forall fun z => by simp)
    (Filter.Eventually.of_forall fun z => by simp)
    hA hB hA' hB').mpr h

/-- The transition datum at one point of one chart: a period carrying the point into the small
polydisc of another chart, and the bounded unit factors relating the two presentations. -/
def SiegelTransitionAt (c : ι → (Fin n → ℂ)) (A B : ι → Fin (N + 1) → (Fin n → ℂ) → ℂ)
    (P : AddSubgroup (Fin n → ℂ)) (r : ℝ) (i : ι) (C : ℝ) (z : Fin n → ℂ) : Prop :=
  ∃ (j : ι) (p : Fin n → ℂ) (v : Fin (N + 1) → ℂ), p ∈ P ∧ ‖z - p - c j‖ ≤ r ∧
    (∀ k, ‖v k‖ ≤ C) ∧ (∀ k, A i k z = v k * A j k (z - p)) ∧
    (∀ k, B i k z = v k * B j k (z - p))

theorem siegelTransitionAt_mono {c : ι → (Fin n → ℂ)}
    {A B : ι → Fin (N + 1) → (Fin n → ℂ) → ℂ} {P : AddSubgroup (Fin n → ℂ)} {r : ℝ} {i : ι}
    {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) {z : Fin n → ℂ} (hz : SiegelTransitionAt c A B P r i C₁ z) :
    SiegelTransitionAt c A B P r i C₂ z := by
  obtain ⟨j, p, v, hp, hy, hv, hA, hB⟩ := hz
  exact ⟨j, p, v, hp, hy, fun k => le_trans (hv k) h, hA, hB⟩

section

variable {c : ι → (Fin n → ℂ)} {A B : ι → Fin (N + 1) → (Fin n → ℂ) → ℂ}
  {P : AddSubgroup (Fin n → ℂ)} {ρ r : ℝ}

/-- **The transition datum exists, with a local bound, near every point of a chart.** -/
theorem eventually_siegelTransitionAt (hr : 0 < r)
    (hAan : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (A i k) z)
    (hBan : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (B i k) z)
    (hred : ∀ (i : ι) (k : Fin (N + 1)) (z : Fin n → ℂ), z ∈ ball (c i) ρ →
      ∀ (h1 : AnalyticAt ℂ (A i k) z) (h2 : AnalyticAt ℂ (B i k) z),
        IsRelPrime (analyticGermOf h1) (analyticGermOf h2))
    (hBne : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, ¬ (B i k) =ᶠ[𝓝 z] 0)
    (hcross : ∀ (i j : ι) (k : Fin (N + 1)) (p : Fin n → ℂ), p ∈ P → ∀ z : Fin n → ℂ,
      z ∈ ball (c i) ρ → z - p ∈ ball (c j) ρ →
        A i k z * B j k (z - p) = A j k (z - p) * B i k z)
    (hcover : ∀ z : Fin n → ℂ, ∃ p ∈ P, ∃ j : ι, ‖z - p - c j‖ ≤ r / 2 ∧ z - p ∈ ball (c j) ρ)
    (i : ι) {w : Fin n → ℂ} (hw : w ∈ ball (c i) ρ) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 w, SiegelTransitionAt c A B P r i C z := by
  classical
  obtain ⟨p, hpP, j, hyw, hwj⟩ := hcover w
  -- the translated presentation of the second chart, at `w`
  have hA₂ : ∀ k : Fin (N + 1), AnalyticAt ℂ (fun z : Fin n → ℂ => A j k (z - p)) w := by
    intro k
    exact AnalyticAt.comp (g := A j k) (f := fun z : Fin n → ℂ => z - p)
      (hAan j k (w - p) hwj) (analyticAt_sub_const p w)
  have hB₂ : ∀ k : Fin (N + 1), AnalyticAt ℂ (fun z : Fin n → ℂ => B j k (z - p)) w := by
    intro k
    exact AnalyticAt.comp (g := B j k) (f := fun z : Fin n → ℂ => z - p)
      (hBan j k (w - p) hwj) (analyticAt_sub_const p w)
  have hred₂ : ∀ k : Fin (N + 1),
      IsRelPrime (analyticGermOf (hA₂ k)) (analyticGermOf (hB₂ k)) := by
    intro k
    exact isRelPrime_germ_translate (hAan j k (w - p) hwj) (hBan j k (w - p) hwj)
      (hA₂ k) (hB₂ k) (hred j k (w - p) hwj _ _)
  have hB₂ne : ∀ k : Fin (N + 1), ¬ (fun z : Fin n → ℂ => B j k (z - p)) =ᶠ[𝓝 w] 0 := by
    intro k hcon
    refine hBne j k (w - p) hwj ?_
    have htend : Filter.Tendsto (fun z : Fin n → ℂ => z + p) (𝓝 (w - p)) (𝓝 w) := by
      have h1 : Filter.Tendsto (fun z : Fin n → ℂ => z + p) (𝓝 (w - p)) (𝓝 (w - p + p)) :=
        (analyticAt_add_const p (w - p)).continuousAt
      rwa [sub_add_cancel] at h1
    filter_upwards [htend.eventually hcon] with z hz
    have hz' : B j k (z + p - p) = 0 := hz
    rwa [add_sub_cancel_right] at hz'
  have hcr : ∀ k : Fin (N + 1),
      (fun z : Fin n → ℂ => A i k z * B j k (z - p)) =ᶠ[𝓝 w]
        fun z : Fin n → ℂ => A j k (z - p) * B i k z := by
    intro k
    have hopen : ∀ᶠ z in 𝓝 w, z ∈ ball (c i) ρ ∧ z - p ∈ ball (c j) ρ := by
      refine Filter.Eventually.and (Metric.isOpen_ball.mem_nhds hw) ?_
      have htend : Filter.Tendsto (fun z : Fin n → ℂ => z - p) (𝓝 w) (𝓝 (w - p)) :=
        (analyticAt_sub_const p w).continuousAt
      exact htend.eventually (Metric.isOpen_ball.mem_nhds hwj)
    filter_upwards [hopen] with z hz
    exact hcross i j k p hpP z hz.1 hz.2
  -- the unit factors
  have hunit : ∀ k : Fin (N + 1), ∃ v : (Fin n → ℂ) → ℂ, AnalyticAt ℂ v w ∧ v w ≠ 0 ∧
      (A i k) =ᶠ[𝓝 w] (fun z => v z * A j k (z - p)) ∧
      (B i k) =ᶠ[𝓝 w] fun z => v z * B j k (z - p) := by
    intro k
    exact exists_unit_factor_of_reduced_at (hAan i k w hw) (hBan i k w hw) (hA₂ k) (hB₂ k)
      (hred i k w hw _ _) (hred₂ k) (hB₂ne k) (hcr k)
  choose v hvA _hvne hvAeq hvBeq using hunit
  -- each factor is bounded near `w`
  have hbound : ∀ k : Fin (N + 1), ∃ Ck : ℝ, ∀ᶠ z in 𝓝 w, ‖v k z‖ ≤ Ck := by
    intro k
    obtain ⟨rk, Ck, hrk, -, hspec⟩ := exists_norm_bound_of_analyticAt (hvA k)
    exact ⟨Ck, by filter_upwards [Metric.ball_mem_nhds w hrk] with z hz using hspec z hz⟩
  choose Ck hCk using hbound
  refine ⟨Finset.univ.sup' Finset.univ_nonempty Ck, ?_⟩
  have hy : ∀ᶠ z in 𝓝 w, ‖z - p - c j‖ ≤ r := by
    have htend : Filter.Tendsto (fun z : Fin n → ℂ => ‖z - p - c j‖) (𝓝 w) (𝓝 ‖w - p - c j‖) := by
      refine Filter.Tendsto.norm ?_
      have h1 : Filter.Tendsto (fun z : Fin n → ℂ => z - p - c j) (𝓝 w) (𝓝 (w - p - c j)) := by
        have h2 : Filter.Tendsto (fun z : Fin n → ℂ => z - p) (𝓝 w) (𝓝 (w - p)) :=
          (analyticAt_sub_const p w).continuousAt
        have h3 : Filter.Tendsto (fun z : Fin n → ℂ => z - c j) (𝓝 (w - p)) (𝓝 (w - p - c j)) :=
          (analyticAt_sub_const (c j) (w - p)).continuousAt
        exact h3.comp h2
      exact h1
    have hlt : ‖w - p - c j‖ < r := lt_of_le_of_lt hyw (by linarith)
    exact (Filter.Tendsto.eventually_lt_const hlt htend).mono fun z hz => le_of_lt hz
  filter_upwards [hy, Filter.eventually_all.mpr hCk, Filter.eventually_all.mpr hvAeq,
    Filter.eventually_all.mpr hvBeq] with z hz1 hz2 hz3 hz4
  refine ⟨j, p, fun k => v k z, hpP, hz1, ?_, ?_, ?_⟩
  · intro k
    exact le_trans (hz2 k) (Finset.le_sup' Ck (Finset.mem_univ k))
  · intro k
    exact hz3 k
  · intro k
    exact hz4 k

/-- **A uniform transition constant on one chart.** -/
theorem exists_uniform_siegelTransition_chart (hr : 0 < r) {R : ℝ} (hRρ : R < ρ)
    (hAan : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (A i k) z)
    (hBan : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (B i k) z)
    (hred : ∀ (i : ι) (k : Fin (N + 1)) (z : Fin n → ℂ), z ∈ ball (c i) ρ →
      ∀ (h1 : AnalyticAt ℂ (A i k) z) (h2 : AnalyticAt ℂ (B i k) z),
        IsRelPrime (analyticGermOf h1) (analyticGermOf h2))
    (hBne : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, ¬ (B i k) =ᶠ[𝓝 z] 0)
    (hcross : ∀ (i j : ι) (k : Fin (N + 1)) (p : Fin n → ℂ), p ∈ P → ∀ z : Fin n → ℂ,
      z ∈ ball (c i) ρ → z - p ∈ ball (c j) ρ →
        A i k z * B j k (z - p) = A j k (z - p) * B i k z)
    (hcover : ∀ z : Fin n → ℂ, ∃ p ∈ P, ∃ j : ι, ‖z - p - c j‖ ≤ r / 2 ∧ z - p ∈ ball (c j) ρ)
    (i : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedBall (c i) R, SiegelTransitionAt c A B P r i C z := by
  refine exists_uniform_bound_of_local (isCompact_closedBall (c i) R)
    (fun C₁ C₂ x h hx => siegelTransitionAt_mono h hx) ?_
  intro x hx
  have hxball : x ∈ ball (c i) ρ := by
    refine mem_ball.mpr (lt_of_le_of_lt ?_ hRρ)
    exact mem_closedBall.mp hx
  obtain ⟨C, hC⟩ := eventually_siegelTransitionAt hr hAan hBan hred hBne hcross hcover i hxball
  exact ⟨{z | SiegelTransitionAt c A B P r i C z}, hC, C, fun z hz => hz⟩

/-- **One transition constant for all the charts.** -/
theorem exists_uniform_siegelTransition [Fintype ι] [Nonempty ι] (hr : 0 < r) {R : ℝ}
    (hRρ : R < ρ)
    (hAan : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (A i k) z)
    (hBan : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, AnalyticAt ℂ (B i k) z)
    (hred : ∀ (i : ι) (k : Fin (N + 1)) (z : Fin n → ℂ), z ∈ ball (c i) ρ →
      ∀ (h1 : AnalyticAt ℂ (A i k) z) (h2 : AnalyticAt ℂ (B i k) z),
        IsRelPrime (analyticGermOf h1) (analyticGermOf h2))
    (hBne : ∀ (i : ι) (k : Fin (N + 1)), ∀ z ∈ ball (c i) ρ, ¬ (B i k) =ᶠ[𝓝 z] 0)
    (hcross : ∀ (i j : ι) (k : Fin (N + 1)) (p : Fin n → ℂ), p ∈ P → ∀ z : Fin n → ℂ,
      z ∈ ball (c i) ρ → z - p ∈ ball (c j) ρ →
        A i k z * B j k (z - p) = A j k (z - p) * B i k z)
    (hcover : ∀ z : Fin n → ℂ, ∃ p ∈ P, ∃ j : ι, ‖z - p - c j‖ ≤ r / 2 ∧ z - p ∈ ball (c j) ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι), ∀ z ∈ closedBall (c i) R, SiegelTransitionAt c A B P r i C z := by
  classical
  choose Ci hCi hCispec using fun i : ι =>
    exists_uniform_siegelTransition_chart (c := c) (A := A) (B := B) (P := P) (ρ := ρ)
      hr hRρ hAan hBan hred hBne hcross hcover i
  refine ⟨Finset.univ.sup' Finset.univ_nonempty Ci, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact le_trans (hCi i) (Finset.le_sup' Ci (Finset.mem_univ i))
  · intro i z hz
    exact siegelTransitionAt_mono (Finset.le_sup' Ci (Finset.mem_univ i)) (hCispec i z hz)

/-- **The transition structure the chartwise count consumes.**  The comparison factor is the
`m`-th power of the product of the unit factors, so it grows like `C^m` in the degree. -/
theorem htrans_of_uniform_siegelTransition [Fintype ι] {C R : ℝ} (hR : 0 ≤ R)
    (htr : ∀ (i : ι), ∀ z ∈ closedBall (c i) R, SiegelTransitionAt c A B P r i C z)
    (m : ℕ) (a : (Fin (N + 1) → Fin (m + 1)) → ℂ) (i : ι) (t : Fin n → ℝ) :
    ∃ (j : ι) (y : Fin n → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ (max 1 C) ^ ((N + 1) * m) ∧
      siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
        = u * siegelHomCombination (A j) (B j) m a (c j + y) := by
  classical
  set w : Fin n → ℂ := torusMap (c i) (fun _ => R) t with hwdef
  have hwmem : w ∈ closedBall (c i) R := by
    refine mem_closedBall.mpr ?_
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg hR).mpr fun k => ?_
    have hk : (w - c i) k = w k - c i k := rfl
    rw [hk, hwdef, norm_torusMap_sub_center, abs_of_nonneg hR]
  obtain ⟨j, p, v, -, hy, hv, hAeq, hBeq⟩ := htr i w hwmem
  refine ⟨j, w - p - c j, ∏ k, (v k) ^ m, hy, ?_, ?_⟩
  · rw [norm_prod]
    have hstep : ∀ k : Fin (N + 1), ‖(v k) ^ m‖ ≤ (max 1 C) ^ m := by
      intro k
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (le_trans (hv k) (le_max_right 1 C)) m
    refine le_trans (Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hstep k)) ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
  · have hid := siegelHomCombination_of_unit_factors (m := m) (A i) (B i)
      (fun k z => A j k (z - p)) (fun k z => B j k (z - p)) v w hAeq hBeq a
    have hshift : c j + (w - p - c j) = w - p := by abel
    rw [hshift]
    exact hid

end

end GaloisForLFunctions.HTGeometry
