import GaloisForLFunctions.RHTower.DeningerCircleComplete

/-!
# The circle of smooth periodic functions is complete

The `C^r` seminorms increase with `r`, so the neighbourhood filter of the origin has a basis indexed
by a single order and a radius.  Sequential completeness then upgrades to completeness, because the
uniformity is countably generated.

* `deningerPeriodicSupLe_mono` : the seminorms increase with the order.
* `DeningerCircle.hasBasis_nhds_zero` : the single-index basis.
-/

namespace RHTower

open Filter Topology Uniformity GaloisForLFunctions

/-- **The `C^r` seminorms increase with `r`.** -/
theorem deningerPeriodicSupLe_mono {L : ℝ} (hL : 0 < L) {r r' : ℕ} (h : r ≤ r')
    (F : DeningerSmoothPeriodic L) :
    deningerPeriodicSupLe r F ≤ deningerPeriodicSupLe r' F := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (fun i hi => Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hi) (Nat.succ_le_succ h)))
    fun i _ _ => deningerPeriodicSup_nonneg hL i F

namespace DeningerCircle

variable {P : {x : ℝ // 0 < x}}

/-- The seminorm family is monotone. -/
theorem seminorms_mono {r r' : ℕ} (h : r ≤ r') (F : DeningerCircle P) :
    seminorms P r F ≤ seminorms P r' F :=
  deningerPeriodicSupLe_mono P.2 h (toPeriodic F)

/-- **A single-index basis of the neighbourhood filter of the origin.** -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : DeningerCircle P)).HasBasis (fun rε : ℕ × ℝ => 0 < rε.2)
      fun rε => {x : DeningerCircle P | seminorms P rε.1 x < rε.2} := by
  refine ((withSeminorms P).hasBasis_zero_ball).to_hasBasis ?_ ?_
  · rintro ⟨s, ε⟩ hε
    refine ⟨(s.sup id, ε), hε, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq] at hx
    refine (Seminorm.mem_ball_zero _).2 ?_
    have hsem : s.sup (seminorms P) ≤ seminorms P (s.sup (id : ℕ → ℕ)) := by
      refine Finset.sup_le fun i hi => ?_
      have hle : i ≤ s.sup (id : ℕ → ℕ) := by
        simpa using Finset.le_sup (f := (id : ℕ → ℕ)) hi
      exact fun y => seminorms_mono hle y
    exact lt_of_le_of_lt (hsem x) hx
  · rintro ⟨r, ε⟩ hε
    refine ⟨({r}, ε), hε, fun x hx => ?_⟩
    have := (Seminorm.mem_ball_zero _).1 hx
    simpa using this

end DeningerCircle

/-- Iterated derivatives are additive on the line. -/
theorem iteratedDeriv_sub_apply_real {f g : ℝ → ℂ} {n : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_sub_apply hf hg,
    ContinuousMultilinearMap.sub_apply]

/-- **Uniform convergence of every derivative gives convergence in every `C^r` seminorm.** -/
theorem deningerPeriodicSup_tendsto_zero {L : ℝ} (hL : 0 < L)
    (F : ℕ → DeningerSmoothPeriodic L) (G : DeningerSmoothPeriodic L)
    (h : ∀ r, TendstoUniformly
      (fun n => iteratedDeriv r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)))
      (iteratedDeriv r ((G : DeningerSmoothPeriodic L) : ℝ → ℂ)) atTop) (r : ℕ) :
    Filter.Tendsto (fun n => deningerPeriodicSup r (F n - G)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.1 (h r)) (ε / 2) (by linarith)
    |>.exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have hbd : deningerPeriodicSup r (F n - G) ≤ ε / 2 := by
    refine ciSup_le fun x => ?_
    have hsplit : iteratedFDeriv ℝ r (((F n - G : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
        = iteratedFDeriv ℝ r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
          - iteratedFDeriv ℝ r ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) x := by
      have hsub : (((F n - G : DeningerSmoothPeriodic L) : ℝ → ℂ))
          = (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ))
            - ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) := rfl
      rw [hsub]
      exact iteratedFDeriv_sub_apply
        ((deningerSmoothPeriodic_contDiff (F n)).of_le (by exact_mod_cast le_top)).contDiffAt
        ((deningerSmoothPeriodic_contDiff G).of_le (by exact_mod_cast le_top)).contDiffAt
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hval : iteratedDeriv r (((F n - G : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
        = iteratedDeriv r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
          - iteratedDeriv r ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) x := by
      have hsub : (((F n - G : DeningerSmoothPeriodic L) : ℝ → ℂ))
          = (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ))
            - ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) := rfl
      rw [hsub]
      exact iteratedDeriv_sub_apply_real
        ((deningerSmoothPeriodic_contDiff (F n)).of_le (by exact_mod_cast le_top)).contDiffAt
        ((deningerSmoothPeriodic_contDiff G).of_le (by exact_mod_cast le_top)).contDiffAt
    rw [hval]
    have := hN n hn x
    rw [dist_eq_norm] at this
    have hsymm : ‖iteratedDeriv r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)) x
        - iteratedDeriv r ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) x‖
        = ‖iteratedDeriv r ((G : DeningerSmoothPeriodic L) : ℝ → ℂ) x
          - iteratedDeriv r (((F n : DeningerSmoothPeriodic L) : ℝ → ℂ)) x‖ := by
      rw [← norm_neg]
      congr 1
      abel
    rw [hsymm]
    linarith [this]
  have hnn : 0 ≤ deningerPeriodicSup r (F n - G) := deningerPeriodicSup_nonneg hL r _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

/-- **The smooth periodic space is complete.** -/
noncomputable instance DeningerCircle.instCompleteSpace {P : {x : ℝ // 0 < x}} :
    CompleteSpace (DeningerCircle P) := by
  haveI hcg : (𝓤 (DeningerCircle P)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
  have huni : (𝓤 (DeningerCircle P)).HasBasis (fun rε : ℕ × ℝ => 0 < rε.2)
      (fun rε => (fun q : DeningerCircle P × DeningerCircle P => q.2 - q.1) ⁻¹'
        {x : DeningerCircle P | DeningerCircle.seminorms P rε.1 x < rε.2}) := by
    rw [uniformity_eq_comap_nhds_zero]
    exact DeningerCircle.hasBasis_nhds_zero.comap _
  rw [huni.cauchySeq_iff] at hu
  have hcauchy : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerPeriodicSup r (DeningerCircle.toPeriodic (u p)
        - DeningerCircle.toPeriodic (u q)) < ε := by
    intro r ε hε
    obtain ⟨N, hN⟩ := hu (r, ε) hε
    refine ⟨N, fun p hp q hq => ?_⟩
    have hmem := hN q hq p hp
    have hlt : DeningerCircle.seminorms P r (u p - u q) < ε := hmem
    exact lt_of_le_of_lt (deningerPeriodicSup_le_supLe P.2 (le_refl r) _) hlt
  obtain ⟨G, hG⟩ :=
    deningerSmoothPeriodic_exists_limit P.2 (fun n => DeningerCircle.toPeriodic (u n)) hcauchy
  refine ⟨DeningerCircle.toPeriodic.symm G, ?_⟩
  rw [← tendsto_sub_nhds_zero_iff, DeningerCircle.hasBasis_nhds_zero.tendsto_right_iff]
  rintro ⟨r, ε⟩ hε
  have hsum : Filter.Tendsto
      (fun n => ∑ m ∈ Finset.range (r + 1),
        deningerPeriodicSup m (DeningerCircle.toPeriodic (u n) - G)) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.range (r + 1))
      fun m _ => deningerPeriodicSup_tendsto_zero P.2
        (fun n => DeningerCircle.toPeriodic (u n)) G hG m
    simpa using this
  have := (Metric.tendsto_atTop.1 hsum) ε hε
  obtain ⟨N, hN⟩ := this
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  rw [Real.dist_eq, sub_zero] at hb
  have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.range (r + 1),
      deningerPeriodicSup m (DeningerCircle.toPeriodic (u n) - G) :=
    Finset.sum_nonneg fun m _ => deningerPeriodicSup_nonneg P.2 m _
  rw [abs_of_nonneg hnn] at hb
  exact hb

end RHTower
