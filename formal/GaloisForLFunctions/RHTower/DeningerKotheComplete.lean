import GaloisForLFunctions.RHTower.DeningerKotheSpace

/-!
# Completeness of a Köthe sequence space

A sequence which is Cauchy for every weighted `ℓ¹` seminorm of a Köthe datum has a limit in the
space.  Each coordinate is Cauchy in the scalar field because the coordinate is dominated by the
seminorm; the coordinatewise limit lies in the space because every finite weighted partial sum is
a limit of partial sums bounded by the uniform bound of a Cauchy sequence; and the same finite
comparison, applied to the differences, gives convergence in each seminorm.

* `DeningerKotheCauchy`, `DeningerKotheTendsto` : the two notions for the whole family.
* `deningerKothe_exists_limit` : **sequential completeness.**
-/

namespace RHTower

open Filter Topology

section KotheComplete

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type} (W : DeningerKotheData ι)

/-- A sequence is Cauchy when it is Cauchy for every seminorm of the family. -/
def DeningerKotheCauchy (a : ℕ → DeningerKotheCarrier 𝕜 W) : Prop :=
  ∀ k : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
    deningerKotheSeminorm W k (a i - a j) < ε

/-- A sequence converges when it converges in every seminorm of the family. -/
def DeningerKotheTendsto (a : ℕ → DeningerKotheCarrier 𝕜 W)
    (L : DeningerKotheCarrier 𝕜 W) : Prop :=
  ∀ k : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, deningerKotheSeminorm W k (a i - L) < ε

variable {W}

private theorem deningerKothe_coord_sub (a b : DeningerKotheCarrier 𝕜 W) (c : ι) :
    ((a - b : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) c
      = (a : ι → 𝕜) c - (b : ι → 𝕜) c := by
  rw [Submodule.coe_sub, Pi.sub_apply]

private theorem deningerKothe_finsetSum_le (k : ℕ) (a : DeningerKotheCarrier 𝕜 W)
    (S : Finset ι) :
    ∑ c ∈ S, W.w k c * ‖(a : ι → 𝕜) c‖ ≤ deningerKotheSeminorm W k a := by
  rw [deningerKotheSeminorm_apply]
  exact Summable.sum_le_tsum S (fun c _ => mul_nonneg (W.pos k c).le (norm_nonneg _))
    (deningerKothe_summable W a k)

/-- A Cauchy sequence is bounded in every seminorm. -/
private theorem deningerKothe_bounded_of_cauchy {a : ℕ → DeningerKotheCarrier 𝕜 W}
    (h : DeningerKotheCauchy W a) (k : ℕ) :
    ∃ C : ℝ, ∀ i, deningerKotheSeminorm W k (a i) ≤ C := by
  obtain ⟨N, hN⟩ := h k 1 one_pos
  refine ⟨1 + deningerKotheSeminorm W k (a N)
      + ∑ j ∈ Finset.range N, deningerKotheSeminorm W k (a j), fun i => ?_⟩
  have hnonnegSum : 0 ≤ ∑ j ∈ Finset.range N, deningerKotheSeminorm W k (a j) :=
    Finset.sum_nonneg fun j _ => apply_nonneg _ _
  rcases lt_or_ge i N with hlt | hge
  · have hmem : deningerKotheSeminorm W k (a i)
        ≤ ∑ j ∈ Finset.range N, deningerKotheSeminorm W k (a j) :=
      Finset.single_le_sum (f := fun j => deningerKotheSeminorm W k (a j))
        (fun j _ => apply_nonneg _ _) (Finset.mem_range.mpr hlt)
    have h1 : 0 ≤ deningerKotheSeminorm W k (a N) := apply_nonneg _ _
    linarith
  · have hle : deningerKotheSeminorm W k (a i)
        ≤ deningerKotheSeminorm W k (a i - a N) + deningerKotheSeminorm W k (a N) := by
      have hadd := map_add_le_add (deningerKotheSeminorm W k) (a i - a N) (a N)
      rwa [sub_add_cancel] at hadd
    have hlt1 : deningerKotheSeminorm W k (a i - a N) < 1 := hN i hge N le_rfl
    linarith

/-- **Sequential completeness of a Köthe space.** -/
theorem deningerKothe_exists_limit (a : ℕ → DeningerKotheCarrier 𝕜 W)
    (h : DeningerKotheCauchy W a) :
    ∃ L : DeningerKotheCarrier 𝕜 W, DeningerKotheTendsto W a L := by
  have hcoord : ∀ c : ι, CauchySeq fun i => ((a i : ι → 𝕜) c) := by
    intro c
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h 0 (W.w 0 c * ε) (mul_pos (W.pos 0 c) hε)
    refine ⟨N, fun i hi j hj => ?_⟩
    have hlt := hN i hi j hj
    have hle : W.w 0 c * ‖((a i - a j : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) c‖
        ≤ deningerKotheSeminorm W 0 (a i - a j) :=
      deningerKotheSeminorm_coord_le W 0 (a i - a j) c
    rw [deningerKothe_coord_sub] at hle
    rw [dist_eq_norm]
    have hw := W.pos 0 c
    nlinarith [norm_nonneg ((a i : ι → 𝕜) c - (a j : ι → 𝕜) c)]
  choose L hL using fun c : ι => cauchySeq_tendsto_of_complete (hcoord c)
  have hnormTend : ∀ (k : ℕ) (S : Finset ι),
      Tendsto (fun i => ∑ c ∈ S, W.w k c * ‖(a i : ι → 𝕜) c‖) atTop
        (nhds (∑ c ∈ S, W.w k c * ‖L c‖)) := by
    intro k S
    refine tendsto_finsetSum S fun c _ => ?_
    exact ((hL c).norm).const_mul (W.w k c)
  have hLmem : ∀ k : ℕ, Summable fun c => W.w k c * ‖L c‖ := by
    intro k
    obtain ⟨C, hC⟩ := deningerKothe_bounded_of_cauchy h k
    refine summable_of_sum_le (c := C)
      (fun c => mul_nonneg (W.pos k c).le (norm_nonneg _)) ?_
    intro S
    refine le_of_tendsto' (hnormTend k S) fun i => ?_
    exact le_trans (deningerKothe_finsetSum_le k (a i) S) (hC i)
  refine ⟨⟨L, hLmem⟩, ?_⟩
  intro k ε hε
  obtain ⟨N, hN⟩ := h k (ε / 2) (by linarith)
  refine ⟨N, fun i hi => ?_⟩
  have hdiffTend : ∀ S : Finset ι,
      Tendsto (fun j => ∑ c ∈ S, W.w k c * ‖(a i : ι → 𝕜) c - (a j : ι → 𝕜) c‖) atTop
        (nhds (∑ c ∈ S, W.w k c * ‖(a i : ι → 𝕜) c - L c‖)) := by
    intro S
    refine tendsto_finsetSum S fun c _ => ?_
    exact ((tendsto_const_nhds.sub (hL c)).norm).const_mul (W.w k c)
  have hbound : ∀ S : Finset ι,
      ∑ c ∈ S, W.w k c *
        ‖((a i - ⟨L, hLmem⟩ : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) c‖ ≤ ε / 2 := by
    intro S
    have heq : ∑ c ∈ S, W.w k c *
        ‖((a i - ⟨L, hLmem⟩ : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) c‖
        = ∑ c ∈ S, W.w k c * ‖(a i : ι → 𝕜) c - L c‖ := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [deningerKothe_coord_sub]
    rw [heq]
    refine le_of_tendsto (hdiffTend S) ?_
    filter_upwards [eventually_ge_atTop N] with j hj
    have hle : ∑ c ∈ S, W.w k c * ‖(a i : ι → 𝕜) c - (a j : ι → 𝕜) c‖
        ≤ deningerKotheSeminorm W k (a i - a j) := by
      have := deningerKothe_finsetSum_le k (a i - a j) S
      refine le_trans (le_of_eq ?_) this
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [deningerKothe_coord_sub]
    exact le_trans hle (hN i hi j hj).le
  have htsum : deningerKotheSeminorm W k (a i - ⟨L, hLmem⟩) ≤ ε / 2 := by
    rw [deningerKotheSeminorm_apply]
    exact Real.tsum_le_of_sum_le
      (fun c => mul_nonneg (W.pos k c).le (norm_nonneg _)) hbound
  linarith

/-- Convergence in the seminorm family is coordinatewise convergence. -/
theorem DeningerKotheTendsto.coord {a : ℕ → DeningerKotheCarrier 𝕜 W}
    {L : DeningerKotheCarrier 𝕜 W} (h : DeningerKotheTendsto W a L) (c : ι) :
    Tendsto (fun i => ((a i : ι → 𝕜) c)) atTop (nhds ((L : ι → 𝕜) c)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h 0 (W.w 0 c * ε) (mul_pos (W.pos 0 c) hε)
  refine ⟨N, fun i hi => ?_⟩
  have hlt := hN i hi
  have hle : W.w 0 c * ‖((a i - L : DeningerKotheCarrier 𝕜 W) : ι → 𝕜) c‖
      ≤ deningerKotheSeminorm W 0 (a i - L) :=
    deningerKotheSeminorm_coord_le W 0 (a i - L) c
  rw [deningerKothe_coord_sub] at hle
  rw [dist_eq_norm]
  have hw := W.pos 0 c
  nlinarith [norm_nonneg ((a i : ι → 𝕜) c - (L : ι → 𝕜) c)]

/-- **The finitely supported group algebra is dense.**  Every Köthe sequence is approximated in
every seminorm by the truncation of its own coordinate expansion. -/
theorem deningerKothe_exists_finite_approx [DecidableEq ι]
    (a : DeningerKotheCarrier 𝕜 W) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ι,
      deningerKotheSeminorm W k
        (a - ∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta W i) < ε := by
  set g : ι → ℝ := fun i => W.w k i * ‖(a : ι → 𝕜) i‖ with hg
  have hgsum : Summable g := deningerKothe_summable W a k
  have htail := tendsto_tsum_compl_atTop_zero g
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨S, hS⟩ := htail ε hε
  refine ⟨S, ?_⟩
  have hcoord : ∀ j, W.w k j *
      ‖((a - ∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta W i :
          DeningerKotheCarrier 𝕜 W) : ι → 𝕜) j‖
      = ({j | j ∉ S} : Set ι).indicator g j := by
    intro j
    have hval : ((a - ∑ i ∈ S, (a : ι → 𝕜) i • deningerKotheDelta W i :
        DeningerKotheCarrier 𝕜 W) : ι → 𝕜) j
        = (a : ι → 𝕜) j - (if j ∈ S then (a : ι → 𝕜) j else 0) := by
      rw [deningerKothe_coord_sub, deningerKothe_partialSum_coord W a S j]
    rw [hval]
    by_cases hj : j ∈ S
    · simp [hj, Set.indicator_of_notMem]
    · rw [Set.indicator_of_mem (by simpa using hj)]
      simp [hj, hg]
  rw [deningerKotheSeminorm_apply, tsum_congr hcoord, ← tsum_subtype]
  have hnonneg : 0 ≤ ∑' x : {x // x ∉ S}, g x :=
    tsum_nonneg fun x => mul_nonneg (W.pos k x).le (norm_nonneg _)
  have hlt := hS S le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hlt
  exact hlt

end KotheComplete

end RHTower
