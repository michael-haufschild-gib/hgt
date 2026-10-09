import GaloisForLFunctions.Bottcher.MontelNormal

/-!
# Montel's theorem on an open set

A uniformly bounded sequence of functions holomorphic on an open set `U ⊆ ℂ` has a subsequence
converging locally uniformly on `U`.

**Proof.** `U` is covered by countably many open discs `ball c_k r_k` with `ball c_k (3 r_k) ⊆ U`
(Lindelöf). On each closed disc `closedBall c_k r_k` the one-disc Montel theorem extracts a uniformly
convergent subsequence. Iterating the extraction along `k` and taking the diagonal gives one
subsequence that converges uniformly on every closed disc. The limits agree on overlaps, and the
open discs cover `U`.
-/

open Complex Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Countably many discs `ball c_k r_k`, each with `ball c_k (3 r_k) ⊆ U`, cover a nonempty open
set `U`. -/
theorem exists_nat_ball_cover_of_isOpen {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ (c : ℕ → ℂ) (r : ℕ → ℝ), (∀ k, 0 < r k) ∧ (∀ k, ball (c k) (3 * r k) ⊆ U) ∧
      ∀ z ∈ U, ∃ k, z ∈ ball (c k) (r k) := by
  have hrad : ∀ z : U, ∃ r : ℝ, 0 < r ∧ ball (z : ℂ) (3 * r) ⊆ U := by
    intro z
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z z.2
    exact ⟨ε / 3, by positivity, by rwa [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)]⟩
  choose ρ hρpos hρU using hrad
  obtain ⟨T, hTc, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable (fun z : U => ball (z : ℂ) (ρ z))
    (fun z => isOpen_ball)
  have hTne : T.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hne
    have hmem : z₀ ∈ ⋃ z : U, ball (z : ℂ) (ρ z) :=
      mem_iUnion.mpr ⟨⟨z₀, hz₀⟩, mem_ball_self (hρpos _)⟩
    rw [← hTcover] at hmem
    obtain ⟨z, hz, -⟩ := mem_iUnion₂.mp hmem
    exact ⟨z, hz⟩
  obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
  refine ⟨fun k => (e k : ℂ), fun k => ρ (e k), fun k => hρpos _, fun k => hρU _, ?_⟩
  intro z hz
  have hmem : z ∈ ⋃ w : U, ball (w : ℂ) (ρ w) := mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hρpos _)⟩
  rw [← hTcover] at hmem
  obtain ⟨w, hwT, hzw⟩ := mem_iUnion₂.mp hmem
  rw [he] at hwT
  obtain ⟨k, rfl⟩ := hwT
  exact ⟨k, hzw⟩

/-- Reindexing a uniformly convergent sequence along indices tending to infinity. -/
theorem tendstoUniformlyOn_comp_nat_tendsto {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ}
    (h : TendstoUniformlyOn G g atTop s) {τ : ℕ → ℕ} (hτ : Tendsto τ atTop atTop) :
    TendstoUniformlyOn (fun n => G (τ n)) g atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  exact hτ.eventually (h ε hε)

/-- **Montel's theorem on an open set.** -/
theorem exists_tendstoLocallyUniformlyOn_subseq_of_bounded {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {C : ℝ} (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbd : ∀ n, ∀ z ∈ U, ‖F n z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (fun k => F (φ k)) g atTop U := by
  classical
  rcases U.eq_empty_or_nonempty with hUe | hne
  · refine ⟨id, strictMono_id, fun _ => 0, ?_⟩
    rw [hUe]
    intro u _ x hx
    exact absurd hx (notMem_empty x)
  obtain ⟨c, r, hr, hball, hcover⟩ := exists_nat_ball_cover_of_isOpen hU hne
  -- one extraction step on disc `k`
  have hext : ∀ (k : ℕ) (ψ : ℕ → ℕ), ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∃ g : ℂ → ℂ,
      TendstoUniformlyOn (fun j => F (ψ (θ j))) g atTop (closedBall (c k) (r k)) := by
    intro k ψ
    obtain ⟨θ, g, hθ, hg, -⟩ := Bottcher.montel_subseq (F := fun n => F (ψ n)) (c := c k)
      (R := 3 * r k) (C := C) (r := r k) (hr k) (by linarith [hr k])
      (fun n => (hF (ψ n)).mono (hball k)) (fun n z hz => hbd (ψ n) z (hball k hz))
    exact ⟨θ, hθ, g, hg⟩
  choose θ hθ g hg using hext
  -- iterated extraction
  let seq : ℕ → ℕ → ℕ := fun k => Nat.rec (θ 0 id) (fun j s => s ∘ θ (j + 1) s) k
  have hseq0 : seq 0 = θ 0 id := rfl
  have hseqS : ∀ j, seq (j + 1) = seq j ∘ θ (j + 1) (seq j) := fun j => rfl
  have hseqmono : ∀ k, StrictMono (seq k) := by
    intro k
    induction k with
    | zero => rw [hseq0]; exact hθ 0 id
    | succ j ih => rw [hseqS]; exact ih.comp (hθ _ _)
  have hseqconv : ∀ k, ∃ gk : ℂ → ℂ,
      TendstoUniformlyOn (fun n => F (seq k n)) gk atTop (closedBall (c k) (r k)) := by
    intro k
    cases k with
    | zero => exact ⟨g 0 id, by simpa [hseq0] using hg 0 id⟩
    | succ j => exact ⟨g (j + 1) (seq j), by rw [hseqS]; exact hg (j + 1) (seq j)⟩
  have hsub : ∀ k j, k ≤ j → ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ seq j = seq k ∘ ρ := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact ⟨id, strictMono_id, rfl⟩
    | succ j _ ih =>
      obtain ⟨ρ, hρ, hρeq⟩ := ih
      refine ⟨ρ ∘ θ (j + 1) (seq j), hρ.comp (hθ _ _), ?_⟩
      rw [hseqS, hρeq]
      rfl
  -- the diagonal subsequence
  let Φ : ℕ → ℕ := fun n => seq n n
  have hΦmono : StrictMono Φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    show seq n n < seq (n + 1) (n + 1)
    rw [hseqS]
    exact hseqmono n (lt_of_lt_of_le (Nat.lt_succ_self n) ((hθ (n + 1) (seq n)).id_le (n + 1)))
  have hΦconv : ∀ k, ∃ gk : ℂ → ℂ,
      TendstoUniformlyOn (fun n => F (Φ n)) gk atTop (closedBall (c k) (r k)) := by
    intro k
    obtain ⟨gk, hgk⟩ := hseqconv k
    choose ρ hρ hρeq using fun j (hkj : k ≤ j) => hsub k j hkj
    let τ : ℕ → ℕ := fun n => if h : k ≤ n then ρ n h n else n
    have hτge : ∀ n, n ≤ τ n := by
      intro n
      by_cases h : k ≤ n
      · simp only [τ, dif_pos h]; exact (hρ n h).id_le n
      · simp only [τ, dif_neg h, le_refl]
    have hτ : Tendsto τ atTop atTop := tendsto_atTop_mono hτge tendsto_id
    refine ⟨gk, (tendstoUniformlyOn_comp_nat_tendsto hgk hτ).congr ?_⟩
    filter_upwards [eventually_ge_atTop k] with n hn
    intro z _
    show F (seq k (τ n)) z = F (seq n n) z
    simp only [τ, dif_pos hn]
    rw [hρeq n hn]
    rfl
  choose gk hgk using hΦconv
  -- the global limit
  have hpt : ∀ z ∈ U, ∃ k, z ∈ ball (c k) (r k) := hcover
  choose! kz hkz using hpt
  let G : ℂ → ℂ := fun z => gk (kz z) z
  have hGeq : ∀ k, ∀ z ∈ closedBall (c k) (r k), z ∈ U → G z = gk k z := by
    intro k z hzk hzU
    have h1 : Tendsto (fun n => F (Φ n) z) atTop (𝓝 (gk (kz z) z)) :=
      (hgk (kz z)).tendsto_at (ball_subset_closedBall (hkz z hzU))
    have h2 : Tendsto (fun n => F (Φ n) z) atTop (𝓝 (gk k z)) := (hgk k).tendsto_at hzk
    exact tendsto_nhds_unique h1 h2
  refine ⟨Φ, hΦmono, G, tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz => ?_⟩
  set k := kz z
  refine ⟨closedBall (c k) (r k) ∩ U, ?_, ?_⟩
  · rw [inter_comm]
    exact inter_mem_nhdsWithin U
      (mem_of_superset (isOpen_ball.mem_nhds (hkz z hz)) ball_subset_closedBall)
  · refine ((hgk k).mono inter_subset_left).congr_right ?_
    intro w hw
    exact (hGeq k w hw.1 hw.2).symm

end GaloisForLFunctions.HTGeometry
