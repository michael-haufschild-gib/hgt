import GaloisForLFunctions.RHTower.DeningerLocallyConstantTestSpace

/-!
# The finest locally convex topology on a countable-dimensional space is sequentially complete

A sequence which is Cauchy for every seminorm is bounded for every seminorm.  If its coordinates
in a basis were nonzero at infinitely many indices, a weighted `ℓ¹` seminorm with weights growing
along those indices would be unbounded on the sequence; so all the terms have coordinates
supported in one finite set of indices.

There the sequence is a finite combination of basis vectors whose coefficients are Cauchy in the
scalar field, hence convergent, and the limit combination is a limit of the sequence for every
seminorm at once.

* `DeningerFinestCauchy`, `DeningerFinestTendsto` : Cauchy and convergence for all seminorms.
* `deningerFinestCauchy_bounded` : a Cauchy sequence is bounded in every seminorm.
* `deningerFinestCauchy_support_finite` : its coordinates live in finitely many indices.
* `deningerFinest_seqComplete` : **the finest locally convex topology is sequentially complete.**
-/

namespace RHTower

section FinestComplete

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- A sequence is Cauchy for the finest locally convex topology when it is Cauchy for every
seminorm. -/
def DeningerFinestCauchy (x : ℕ → E) : Prop :=
  ∀ (p : Seminorm 𝕜 E) (ε : ℝ), 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, p (x m - x n) < ε

/-- A sequence converges for the finest locally convex topology when it converges for every
seminorm. -/
def DeningerFinestTendsto (x : ℕ → E) (a : E) : Prop :=
  ∀ (p : Seminorm 𝕜 E) (ε : ℝ), 0 < ε → ∃ N, ∀ n ≥ N, p (x n - a) < ε

/-- **A Cauchy sequence is bounded in every seminorm.** -/
theorem deningerFinestCauchy_bounded {x : ℕ → E} (hx : DeningerFinestCauchy (𝕜 := 𝕜) x)
    (p : Seminorm 𝕜 E) : ∃ M : ℝ, ∀ n, p (x n) ≤ M := by
  obtain ⟨N, hN⟩ := hx p 1 one_pos
  refine ⟨(Finset.range (N + 1)).sup' (by simp) (fun i => p (x i)) + 1, fun n => ?_⟩
  by_cases hn : n ≤ N
  · have hmem : n ∈ Finset.range (N + 1) := by simp; omega
    have := Finset.le_sup' (fun i => p (x i)) hmem
    linarith
  · have hle : p (x n - x N) < 1 := hN n (by omega) N (le_refl N)
    have hsplit : p (x n) ≤ p (x N) + p (x n - x N) := by
      have hxn : x n = x N + (x n - x N) := by abel
      calc p (x n) = p (x N + (x n - x N)) := by rw [← hxn]
        _ ≤ p (x N) + p (x n - x N) := map_add_le_add p _ _
    have hmem : N ∈ Finset.range (N + 1) := by simp
    have := Finset.le_sup' (fun i => p (x i)) hmem
    linarith

variable [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- **The coordinates of a Cauchy sequence are supported in finitely many indices.**  Otherwise a
weighted `ℓ¹` seminorm with weights growing along the exceptional indices would be unbounded. -/
theorem deningerFinestCauchy_support_finite (b : Module.Basis ℕ 𝕜 E) {x : ℕ → E}
    (hx : DeningerFinestCauchy (𝕜 := 𝕜) x) :
    {k : ℕ | ∃ n, b.repr (x n) k ≠ 0}.Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  choose! n hn using fun k (hk : k ∈ {k : ℕ | ∃ n, b.repr (x n) k ≠ 0}) => hk
  set w : ℕ → ℝ := fun k =>
    if hk : k ∈ {k : ℕ | ∃ n, b.repr (x n) k ≠ 0}
      then (k : ℝ) / ‖b.repr (x (n k)) k‖ else 1 with hwdef
  have hwnonneg : ∀ k, 0 ≤ w k := by
    intro k
    rw [hwdef]
    by_cases hk : k ∈ {k : ℕ | ∃ n, b.repr (x n) k ≠ 0}
    · simp only [dif_pos hk]
      positivity
    · simp only [dif_neg hk]
      norm_num
  obtain ⟨M, hM⟩ := deningerFinestCauchy_bounded hx (deningerBasisSeminorm b w hwnonneg)
  obtain ⟨k, hk, hkM⟩ := hinf.exists_gt ⌈M⌉₊
  have hcoord := deningerBasisSeminorm_coord_le b w hwnonneg (x (n k)) k
  have hne : b.repr (x (n k)) k ≠ 0 := hn k hk
  have hpos : 0 < ‖b.repr (x (n k)) k‖ := norm_pos_iff.mpr hne
  have hval : w k * ‖b.repr (x (n k)) k‖ = (k : ℝ) := by
    rw [hwdef]
    simp only [dif_pos hk]
    field_simp
  rw [hval] at hcoord
  have hMk : (M : ℝ) < (k : ℝ) := by
    have h1 : (⌈M⌉₊ : ℝ) < (k : ℝ) := by exact_mod_cast hkM
    exact lt_of_le_of_lt (Nat.le_ceil M) h1
  have := hM (n k)
  linarith

/-- **A Cauchy sequence whose coordinates vanish outside a finite set of indices converges.**  The
finitely many coordinates are Cauchy in the scalar field, and their limits assemble the limit. -/
theorem deningerFinest_tendsto_of_support {ι : Type*} (b : Module.Basis ι 𝕜 E) {x : ℕ → E}
    (s : Finset ι) (hs : ∀ k ∉ s, ∀ n, b.repr (x n) k = 0)
    (hx : DeningerFinestCauchy (𝕜 := 𝕜) x) : ∃ a, DeningerFinestTendsto (𝕜 := 𝕜) x a := by
  classical
  have hcoordCauchy : ∀ k, CauchySeq fun n => b.repr (x n) k := by
    intro k
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hx ((normSeminorm 𝕜 𝕜).comp (b.coord k)) ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn N (le_refl N)
    have hval : ‖b.repr (x n) k - b.repr (x N) k‖ < ε := by
      have hcoe : ((normSeminorm 𝕜 𝕜).comp (b.coord k)) (x n - x N)
          = ‖b.repr (x n) k - b.repr (x N) k‖ := by
        show ‖b.coord k (x n - x N)‖ = _
        rw [map_sub]
        rfl
      rwa [hcoe] at h
    rwa [dist_eq_norm]
  choose a ha using fun k => cauchySeq_tendsto_of_complete (hcoordCauchy k)
  refine ⟨∑ k ∈ s, a k • b k, ?_⟩
  intro p ε hε
  set Mp : ℝ := ∑ k ∈ s, p (b k) with hMp
  have hMpnonneg : 0 ≤ Mp := Finset.sum_nonneg fun k _ => apply_nonneg p _
  have hδ : 0 < ε / (Mp + 1) := by positivity
  have hNk : ∀ k, ∃ N, ∀ n ≥ N, ‖b.repr (x n) k - a k‖ < ε / (Mp + 1) := by
    intro k
    have hev := (ha k).eventually (Metric.ball_mem_nhds (a k) hδ)
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    exact ⟨N, fun n hn => by simpa [dist_eq_norm] using hN n hn⟩
  choose N hN using hNk
  refine ⟨s.sup N, fun n hn => ?_⟩
  have hxn : x n = ∑ k ∈ s, b.repr (x n) k • b k := by
    conv_lhs => rw [← b.linearCombination_repr (x n)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_subset ?_ ?_
    · intro k hk
      by_contra hmem
      exact (Finsupp.mem_support_iff.mp hk) (hs k hmem n)
    · intro k _ hk
      have hzero : b.repr (x n) k = 0 := by simpa using hk
      rw [hzero, zero_smul]
  have hdiff : x n - ∑ k ∈ s, a k • b k
      = ∑ k ∈ s, (b.repr (x n) k - a k) • b k := by
    conv_lhs => rw [hxn]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [sub_smul]
  rw [hdiff]
  refine lt_of_le_of_lt (deningerSeminorm_finset_sum_le p _ _) ?_
  have hbound : ∀ k ∈ s, p ((b.repr (x n) k - a k) • b k) ≤ ε / (Mp + 1) * p (b k) := by
    intro k hk
    rw [map_smul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg p _)
    exact le_of_lt (hN k n (le_trans (Finset.le_sup hk) hn))
  refine lt_of_le_of_lt (Finset.sum_le_sum hbound) ?_
  rw [← Finset.mul_sum, ← hMp]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **The finest locally convex topology on a countable-dimensional space is sequentially
complete.** -/
theorem deningerFinest_seqComplete (b : Module.Basis ℕ 𝕜 E) {x : ℕ → E}
    (hx : DeningerFinestCauchy (𝕜 := 𝕜) x) : ∃ a, DeningerFinestTendsto (𝕜 := 𝕜) x a := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k, K ≤ k → ∀ n, b.repr (x n) k = 0 := by
    obtain ⟨K, hK⟩ := (deningerFinestCauchy_support_finite b hx).bddAbove
    refine ⟨K + 1, fun k hk n => ?_⟩
    by_contra hne
    have hmem : k ∈ {k : ℕ | ∃ n, b.repr (x n) k ≠ 0} := ⟨n, hne⟩
    have := hK hmem
    omega
  refine deningerFinest_tendsto_of_support b (Finset.range K) (fun k hk n => ?_) hx
  exact hK k (by simpa using hk) n

/-- **Sequential completeness for a finite basis.** -/
theorem deningerFinest_seqComplete_of_finite {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 E)
    {x : ℕ → E} (hx : DeningerFinestCauchy (𝕜 := 𝕜) x) :
    ∃ a, DeningerFinestTendsto (𝕜 := 𝕜) x a :=
  deningerFinest_tendsto_of_support b Finset.univ (fun k hk _ => absurd (Finset.mem_univ k) hk) hx

/-- **Sequential completeness for a countable basis.** -/
theorem deningerFinest_seqComplete_of_countable {ι : Type*} [Countable ι]
    (b : Module.Basis ι 𝕜 E) {x : ℕ → E} (hx : DeningerFinestCauchy (𝕜 := 𝕜) x) :
    ∃ a, DeningerFinestTendsto (𝕜 := 𝕜) x a := by
  rcases finite_or_infinite ι with _ | _
  · haveI : Fintype ι := Fintype.ofFinite ι
    exact deningerFinest_seqComplete_of_finite b hx
  · obtain ⟨e⟩ : Nonempty (ι ≃ ℕ) := ⟨(nonempty_denumerable ι).some.eqv⟩
    exact deningerFinest_seqComplete (b.reindex e) hx

end FinestComplete

section TestComplete

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]

/-- **The locally constant test space is sequentially complete** for its finest locally convex
topology: a sequence Cauchy in every seminorm converges in every seminorm. -/
theorem deningerTestSpace_seqComplete {x : ℕ → DeningerTestSpace Y}
    (hx : DeningerFinestCauchy (𝕜 := ℝ) x) : ∃ a, DeningerFinestTendsto (𝕜 := ℝ) x a := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (deningerTestIndicators Y)
  haveI : Countable b := (deningerTestIndicators_countable.mono hbS).to_subtype
  refine deningerFinest_seqComplete_of_countable (Module.Basis.mk hli ?_) hx
  rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspan, deningerTestIndicators_span]

end TestComplete

end RHTower
