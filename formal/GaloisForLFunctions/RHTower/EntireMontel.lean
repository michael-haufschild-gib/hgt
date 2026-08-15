import GaloisForLFunctions.Bottcher.MontelNormal

/-!
# Montel's theorem for entire families

A family of entire functions bounded uniformly on every ball has a subsequence converging locally
uniformly on the whole plane.  The one-ball form of Montel's theorem extracts a subsequence
converging uniformly on one closed ball; iterating it along an exhaustion by balls and taking the
diagonal gives a single subsequence that works on every ball at once.
-/

open Metric Filter Topology

noncomputable section

namespace RHTower

/-- One extraction step of Montel's theorem, on the closed ball of radius `m + 1`. -/
theorem exists_subseq_tendstoUniformlyOn_closedBall {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hbd : ∀ R : ℝ, ∃ C : ℝ, ∀ n, ∀ z ∈ ball (0 : ℂ) R, ‖F n z‖ ≤ C)
    (ψ : ℕ → ℕ) (m : ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun k => F (ψ (σ k))) g atTop (closedBall 0 ((m : ℝ) + 1)) := by
  obtain ⟨C, hC⟩ := hbd (2 * (m : ℝ) + 3)
  obtain ⟨σ, g, hσ, hconv, _⟩ :=
    Bottcher.montel_subseq (F := fun k => F (ψ k)) (c := 0) (C := C)
      (R := 2 * (m : ℝ) + 3) (r := (m : ℝ) + 1)
      (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (fun k => (hF (ψ k)).differentiableOn)
      (fun k z hz => hC (ψ k) z hz)
  exact ⟨σ, hσ, g, hconv⟩

/-- **Montel's theorem for entire families.**  A family of entire functions bounded uniformly on
every ball has a subsequence converging locally uniformly on the plane. -/
theorem exists_subseq_tendstoLocallyUniformly {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hbd : ∀ R : ℝ, ∃ C : ℝ, ∀ n, ∀ z ∈ ball (0 : ℂ) R, ‖F n z‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformly (fun k => F (φ k)) g atTop := by
  classical
  choose σ hσmono G hG using exists_subseq_tendstoUniformlyOn_closedBall hF hbd
  obtain ⟨Ψ, hΨ0, hΨs⟩ : ∃ Ψ : ℕ → (ℕ → ℕ), Ψ 0 = id ∧
      ∀ j, Ψ (j + 1) = Ψ j ∘ σ (Ψ j) j :=
    ⟨fun m => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun j ih => ih ∘ σ ih j) m, rfl,
      fun _ => rfl⟩
  have hΨmono : ∀ m, StrictMono (Ψ m) := by
    intro m
    induction m with
    | zero => rw [hΨ0]; exact strictMono_id
    | succ j ih => rw [hΨs j]; exact ih.comp (hσmono (Ψ j) j)
  have hΨsub : ∀ m j, m ≤ j → ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ k, Ψ j k = Ψ m (ρ k) := by
    intro m j hmj
    induction j, hmj using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, fun k => rfl⟩
    | succ j hmj ih =>
        obtain ⟨ρ, hρ, hρeq⟩ := ih
        refine ⟨ρ ∘ σ (Ψ j) j, hρ.comp (hσmono (Ψ j) j), fun k => ?_⟩
        rw [hΨs j]
        exact hρeq _
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℕ → ℕ, φ = fun k => Ψ (k + 1) k := ⟨_, rfl⟩
  have hφmono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨ρ, hρ, hρeq⟩ := hΨsub (k + 1) (k + 2) (by omega)
    rw [hφdef]
    simp only
    rw [hρeq (k + 1)]
    exact hΨmono (k + 1) (lt_of_lt_of_le (Nat.lt_succ_self k) hρ.le_apply)
  have hball : ∀ m : ℕ,
      TendstoUniformlyOn (fun k => F (φ k)) (G (Ψ m) m) atTop (closedBall 0 ((m : ℝ) + 1)) := by
    intro m
    have hbase : TendstoUniformlyOn (fun k => F (Ψ (m + 1) k)) (G (Ψ m) m) atTop
        (closedBall 0 ((m : ℝ) + 1)) := by
      have h := hG (Ψ m) m
      refine h.congr (Filter.Eventually.of_forall fun k => ?_)
      intro z _
      rw [hΨs m]
      rfl
    rw [Metric.tendstoUniformlyOn_iff] at hbase ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hbase ε hε)
    refine eventually_atTop.2 ⟨max N m, fun k hk z hz => ?_⟩
    obtain ⟨ρ, hρ, hρeq⟩ := hΨsub (m + 1) (k + 1) (by omega)
    have hkφ : φ k = Ψ (m + 1) (ρ k) := by rw [hφdef]; exact hρeq k
    have hρk : N ≤ ρ k := le_trans (le_trans (le_max_left N m) hk) hρ.le_apply
    rw [hkφ]
    exact hN (ρ k) hρk z hz
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, ∀ z : ℂ, Tendsto (fun k => F (φ k) z) atTop (nhds (g z)) := by
    have hexists : ∀ z : ℂ, ∃ L : ℂ, Tendsto (fun k => F (φ k) z) atTop (nhds L) := by
      intro z
      obtain ⟨m, hm⟩ := exists_nat_ge ‖z‖
      refine ⟨G (Ψ m) m z, ?_⟩
      have hzmem : z ∈ closedBall (0 : ℂ) ((m : ℝ) + 1) := by
        rw [mem_closedBall, dist_zero_right]
        linarith
      exact (hball m).tendsto_at hzmem
    exact ⟨fun z => (hexists z).choose, fun z => (hexists z).choose_spec⟩
  refine ⟨φ, g, hφmono, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨m, hm⟩ := exists_nat_ge R
  have hKsub : K ⊆ closedBall (0 : ℂ) ((m : ℝ) + 1) :=
    hR.trans (closedBall_subset_closedBall (by linarith))
  refine TendstoUniformlyOn.mono ?_ hKsub
  refine (hball m).congr_right fun z hz => ?_
  exact tendsto_nhds_unique ((hball m).tendsto_at hz) (hg z)

/-- **Montel with an eventual bound.**  Only an eventual uniform bound on each ball is needed: the
finitely many remaining members are individually bounded there by compactness. -/
theorem exists_subseq_tendstoLocallyUniformly_of_eventually_bounded {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hbd : ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ n in atTop, ∀ z ∈ ball (0 : ℂ) R, ‖F n z‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoLocallyUniformly (fun k => F (φ k)) g atTop := by
  classical
  refine exists_subseq_tendstoLocallyUniformly hF fun R => ?_
  obtain ⟨C, hC⟩ := hbd R
  obtain ⟨N, hN⟩ := eventually_atTop.1 hC
  choose Cn hCn using fun n =>
    (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn (hF n).continuous.continuousOn
  obtain ⟨M, hM⟩ := Finset.exists_le ((Finset.range N).image Cn)
  refine ⟨max C M, fun n z hz => ?_⟩
  by_cases hn : N ≤ n
  · exact le_trans (hN n hn z hz) (le_max_left _ _)
  · refine le_trans (hCn n z (ball_subset_closedBall hz)) (le_trans ?_ (le_max_right _ _))
    exact hM (Cn n) (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)

end RHTower

end
