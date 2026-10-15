import GaloisForLFunctions.RHTower.PrimeBlindFiniteLevelFarkas
import GaloisForLFunctions.RHTower.WeilFullConeKreinMilmanReduction

/-!
# The finite-level certificates squeeze onto the von Mangoldt function

A *level-`L` certificate* is a weight vector `μ` on the nodes `n ≥ 2` that is Weil-positive at pole
weight `1` on every test supported in `[−L, L]` and lies in the canonical box
`|μ(n)| ≤ coordBound n` cut out by the two pair tests at `n` (`weilBox`, `levelCertificates`).

* The certificate sets are compact and decrease with the level.
* Under RH the von Mangoldt function is a certificate at every level, and conversely a certificate
  at every level forces RH (`riemannHypothesis_iff_forall_levelCertificates_nonempty`), by Cantor's
  intersection theorem and the uniqueness of the Weil cone.
* **Squeeze.**  Unconditionally, for every node `n` and `ε > 0` there is a level beyond which every
  certificate satisfies `|μ(n) − Λ(n)| < ε` (`exists_level_forall_levelCertificates_abs_sub_lt`).
  Consequently any choice of certificates `μ_L ∈ levelCertificates L` converges coordinatewise to
  `Λ` (`tendsto_levelCertificates_apply`): the finite-level archimedean problems determine the
  prime weights in the limit, and under RH such choices exist at every level.
-/

open Complex MeasureTheory Set Finsupp Zeta23 Filter Topology

namespace RHTower.WeilOneSided

open WeilSpectral

noncomputable section

/-- The pair test at node `j` has level `log j + r_j`. -/
theorem levelTest_pairTestFn (j : ℕ) (σ : ℝ) :
    LevelTest (Real.log j + bumpRadius j) (pairTestFn j σ) := by
  intro u hu
  change pairTest j σ u ≠ 0 at hu
  by_contra h
  push Not at h
  apply hu
  have hr : bumpRadius j = 1 / (4 * ((j : ℝ) + 1)) := rfl
  have hlog : 0 ≤ Real.log j := Real.log_natCast_nonneg j
  rw [hr] at h
  have h1 : 1 / (4 * ((j : ℝ) + 1)) < |u| := by linarith
  have h2 : 1 / (4 * ((j : ℝ) + 1)) < |u - Real.log j| := by
    have := abs_sub_abs_le_abs_sub u (Real.log j)
    rw [abs_of_nonneg hlog] at this
    linarith
  simp [pairTest, narrowBumpC_eq_zero j h1, narrowBumpC_eq_zero j h2]

/-- The canonical box: each coordinate bounded by the pair tests. -/
def weilBox : Set (LogIndex → ℝ) := univ.pi fun j => Icc (-coordBound j) (coordBound j)

theorem isCompact_weilBox : IsCompact weilBox := isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_weilBox : IsClosed weilBox := isClosed_set_pi fun _ _ => isClosed_Icc

/-- The level-`L` certificates: weight vectors in the box that are Weil-positive at pole weight `1`
on all tests supported in `[−L, L]`. -/
def levelCertificates (L : ℝ) : Set (LogIndex → ℝ) := weilBox ∩ {μ | LevelWeilPositiveAt L 1 μ}

theorem isClosed_setOf_levelWeilPositiveAt_one (L : ℝ) :
    IsClosed {μ : LogIndex → ℝ | LevelWeilPositiveAt L 1 μ} := by
  have e : {μ : LogIndex → ℝ | LevelWeilPositiveAt L 1 μ} = ⋂ (f : WeilTestFn) (_ : LevelTest L f),
      {μ | linearCombination ℝ μ (logVector f) ≤
        weilArchRe (EF.weilTest f.1 f.1) + (1 - 1) * (weilPoleTerm (EF.weilTest f.1 f.1)).re} := by
    ext μ
    simp only [mem_setOf_eq, mem_iInter, LevelWeilPositiveAt]
  rw [e]
  exact isClosed_iInter fun f => isClosed_iInter fun _ =>
    isClosed_le (continuous_linearCombination_logVector f) continuous_const

theorem isClosed_levelCertificates (L : ℝ) : IsClosed (levelCertificates L) :=
  isClosed_weilBox.inter (isClosed_setOf_levelWeilPositiveAt_one L)

theorem isCompact_levelCertificates (L : ℝ) : IsCompact (levelCertificates L) :=
  isCompact_weilBox.inter_right (isClosed_setOf_levelWeilPositiveAt_one L)

theorem levelCertificates_antitone {L L' : ℝ} (h : L ≤ L') :
    levelCertificates L' ⊆ levelCertificates L :=
  fun _ ⟨hb, hμ⟩ => ⟨hb, fun f hf => hμ f (hf.mono h)⟩

/-- Under RH the von Mangoldt function is a certificate at every level. -/
theorem vonMangoldt_mem_levelCertificates (hRH : RiemannHypothesis) (L : ℝ) :
    (fun j : LogIndex => (ArithmeticFunction.vonMangoldt j : ℝ)) ∈ levelCertificates L := by
  have hcone := vonMangoldt_mem_weilCone_of_riemannHypothesis hRH
  refine ⟨?_, fun f _ => ?_⟩
  · rw [weilBox, mem_univ_pi]
    intro j
    exact abs_le.mp (abs_le_coordBound_of_mem_weilCone hcone j)
  · have := (mem_weilCone_iff _).mp hcone f
    simp only [sub_self, zero_mul, add_zero]
    exact this

/-- A certificate at every level lies in the Weil cone. -/
theorem mem_weilCone_of_forall_levelCertificates {μ : LogIndex → ℝ}
    (h : ∀ n : ℕ, μ ∈ levelCertificates ((n : ℝ) + 1)) : μ ∈ weilCone := by
  rw [mem_weilCone_iff]
  intro f
  obtain ⟨L, -, hfL⟩ := exists_levelTest f
  obtain ⟨n, hn⟩ := exists_nat_ge L
  have := (h n).2 f (hfL.mono (by linarith))
  simpa using this

/-- **RH is the existence of a certificate at every level.** -/
theorem riemannHypothesis_iff_forall_levelCertificates_nonempty :
    RiemannHypothesis ↔ ∀ L : ℝ, (levelCertificates L).Nonempty := by
  constructor
  · intro hRH L
    exact ⟨_, vonMangoldt_mem_levelCertificates hRH L⟩
  · intro h
    have hne : ∀ n : ℕ, (levelCertificates ((n : ℝ) + 1)).Nonempty := fun n => h _
    have hsub : ∀ n : ℕ, levelCertificates (((n + 1 : ℕ) : ℝ) + 1) ⊆
        levelCertificates ((n : ℝ) + 1) :=
      fun n => levelCertificates_antitone (by push_cast; linarith)
    obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n : ℕ => levelCertificates ((n : ℝ) + 1)) hsub hne (isCompact_levelCertificates _)
      (fun n => isClosed_levelCertificates _)
    rw [mem_iInter] at hμ
    have hcone : WeilPositiveFull (extendLog μ) := mem_weilCone_of_forall_levelCertificates hμ
    exact (weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp hcone).1

/-- **Squeeze.**  For every node `n` and `ε > 0`, beyond some level every certificate is within `ε`
of `Λ(n)` at the node `n`.  No hypothesis on `ζ` is used. -/
theorem exists_level_forall_levelCertificates_abs_sub_lt (n : LogIndex) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ L : ℝ, (N : ℝ) ≤ L → ∀ μ ∈ levelCertificates L,
      |μ n - (ArithmeticFunction.vonMangoldt n : ℝ)| < ε := by
  by_contra hcon
  push Not at hcon
  set S : ℕ → Set (LogIndex → ℝ) := fun k =>
    levelCertificates ((k : ℝ) + 1) ∩ {μ | ε ≤ |μ n - (ArithmeticFunction.vonMangoldt n : ℝ)|}
    with hS
  have hne : ∀ k, (S k).Nonempty := by
    intro k
    obtain ⟨L, hL, μ, hμ, hεμ⟩ := hcon (k + 1)
    refine ⟨μ, levelCertificates_antitone (by push_cast at hL; linarith) hμ, hεμ⟩
  have hsub : ∀ k, S (k + 1) ⊆ S k := fun k =>
    inter_subset_inter (levelCertificates_antitone (by push_cast; linarith)) le_rfl
  have hclε : IsClosed {μ : LogIndex → ℝ | ε ≤ |μ n - (ArithmeticFunction.vonMangoldt n : ℝ)|} :=
    isClosed_le continuous_const (((continuous_apply n).sub continuous_const).abs)
  have hcl : ∀ k, IsClosed (S k) := fun k => (isClosed_levelCertificates _).inter hclε
  have hcpt : IsCompact (S 0) := (isCompact_levelCertificates _).inter_right hclε
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hsub hne
    hcpt hcl
  rw [mem_iInter] at hμ
  have hcone : WeilPositiveFull (extendLog μ) :=
    mem_weilCone_of_forall_levelCertificates fun k => (hμ k).1
  have hΛ := eq_vonMangoldt_of_weilPositiveFull hcone n n.2
  rw [extendLog_coe] at hΛ
  have hε' := (hμ 0).2
  simp only [mem_setOf_eq] at hε'
  rw [hΛ, sub_self, abs_zero] at hε'
  linarith

/-- **The level certificates converge to the von Mangoldt function.**  Any choice of a certificate
at each level converges coordinatewise to `Λ`. -/
theorem tendsto_levelCertificates_apply (n : LogIndex) {μ : ℝ → LogIndex → ℝ}
    (hμ : ∀ L, μ L ∈ levelCertificates L) :
    Tendsto (fun L => μ L n) atTop (𝓝 (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_level_forall_levelCertificates_abs_sub_lt n hε
  exact ⟨N, fun L hL => by rw [Real.dist_eq]; exact hN L hL (μ L) (hμ L)⟩

/-- Under RH certificates exist at every level and every choice of them converges to `Λ`. -/
theorem exists_levelCertificates_tendsto_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ μ : ℝ → LogIndex → ℝ, (∀ L, μ L ∈ levelCertificates L) ∧
      ∀ n : LogIndex, Tendsto (fun L => μ L n) atTop (𝓝 (ArithmeticFunction.vonMangoldt n : ℝ)) :=
  ⟨fun _ j => (ArithmeticFunction.vonMangoldt j : ℝ), fun L => vonMangoldt_mem_levelCertificates hRH L,
    fun n => tendsto_levelCertificates_apply n fun L => vonMangoldt_mem_levelCertificates hRH L⟩

end

end RHTower.WeilOneSided
