import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Scheffé's lemma for counting measure

Pointwise convergence of probability vectors upgrades to `l^(1 : ℕ)` convergence.  Only the total masses
being equal makes this work: the positive and negative deficits then have the same sum, so the
`l^(1 : ℕ)` distance is twice the positive deficit, and that is dominated by the limit vector and tends
to zero termwise.

This is the step that turns coordinatewise convergence of the surviving masses into control of the
whole family, which is what tightness of the physical measures rests on.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- A summable family has arbitrarily small tails outside a finite set. -/
theorem exists_finset_tsum_compl_lt {ι : Type*} {f : ι → ℝ} {S : ℝ}
    (hf : HasSum f S) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, ∑' (x : ↑((↑F : Set ι)ᶜ)), f ↑x < ε := by
  have hev : ∀ᶠ s : Finset ι in atTop, |∑ i ∈ s, f i - S| < ε := by
    have h := Metric.tendsto_nhds.mp hf ε hε
    simpa [Real.dist_eq] using h
  obtain ⟨F, hF⟩ := eventually_atTop.mp hev
  refine ⟨F, ?_⟩
  have hsplit := hf.summable.sum_add_tsum_compl (s := F)
  rw [hf.tsum_eq] at hsplit
  have hFle := abs_lt.mp (hF F le_rfl)
  linarith [hFle.1]

/-- A summable positive sector can be absorbed into a finite packet without changing a prescribed
subunit complementary budget.  More precisely, if both sides of a predicate are summable and the
complementary total is below one, every finite packet inside the predicate extends to a finite
packet, still inside the predicate, whose entire remaining tail is below one. -/
theorem exists_finset_absorber_of_compl_tsum_lt_one
    {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (hf0 : ∀ q, 0 ≤ f q)
    (P : Set ι)
    (hPsum : Summable (fun q : P => f (q : ι)))
    (hCsum : Summable (fun q : ↥(Pᶜ) => f (q : ι)))
    (hClt : (∑' q : ↥(Pᶜ), f (q : ι)) < 1)
    (B : Finset ι) (hBP : ∀ q ∈ B, q ∈ P) :
    ∃ S : Finset ι, B ⊆ S ∧ (∀ q ∈ S, q ∈ P) ∧
      Summable (fun q : ↥((↑S : Set ι)ᶜ) => f (q : ι)) ∧
      (∑' q : ↥((↑S : Set ι)ᶜ), f (q : ι)) < 1 := by
  classical
  let C := ∑' q : ↥(Pᶜ), f (q : ι)
  have hε : 0 < 1 - C := by dsimp only [C]; linarith
  obtain ⟨F, hFtail⟩ := exists_finset_tsum_compl_lt hPsum.hasSum hε
  let S : Finset ι := B ∪ F.image Subtype.val
  have hBS : B ⊆ S := Finset.subset_union_left
  have hSP : ∀ q ∈ S, q ∈ P := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqB | hqF
    · exact hBP q hqB
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hqF
      exact r.property
  have hf : Summable f := hPsum.add_compl hCsum
  have hSsum : Summable (fun q : ↥((↑S : Set ι)ᶜ) => f (q : ι)) := hf.subtype _
  let A : Set ↥((↑S : Set ι)ᶜ) := {q | (q : ι) ∈ P}
  have hAsum : Summable (fun q : A => f ((q : ↥((↑S : Set ι)ᶜ)) : ι)) :=
    hSsum.subtype A
  have hAcsum : Summable (fun q : ↥(Aᶜ) => f ((q : ↥((↑S : Set ι)ᶜ)) : ι)) :=
    hSsum.subtype Aᶜ
  let eP : A → ↥((↑F : Set P)ᶜ) := fun q =>
    ⟨⟨((q : ↥((↑S : Set ι)ᶜ)) : ι), q.property⟩, by
      intro hqF
      have himage : ((q : ↥((↑S : Set ι)ᶜ)) : ι) ∈ F.image Subtype.val :=
        Finset.mem_image.mpr ⟨⟨((q : ↥((↑S : Set ι)ᶜ)) : ι), q.property⟩, hqF, rfl⟩
      exact (q : ↥((↑S : Set ι)ᶜ)).property (Finset.mem_union_right B himage)⟩
  have hePinj : Function.Injective eP := by
    intro q r hqr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥((↑F : Set P)ᶜ) => ((z : P) : ι)) hqr
  have hPtailSum : Summable (fun q : ↥((↑F : Set P)ᶜ) => f ((q : P) : ι)) :=
    hPsum.subtype _
  have hAle : (∑' q : A, f ((q : ↥((↑S : Set ι)ᶜ)) : ι)) ≤
      ∑' q : ↥((↑F : Set P)ᶜ), f ((q : P) : ι) := by
    exact hAsum.tsum_le_tsum_of_inj eP hePinj
      (fun q _ => hf0 ((q : P) : ι)) (fun q => le_rfl) hPtailSum
  let eC : ↥(Aᶜ) → ↥(Pᶜ) := fun q =>
    ⟨((q : ↥((↑S : Set ι)ᶜ)) : ι), by
      have hnot : ¬ ((q : ↥((↑S : Set ι)ᶜ)) : ι) ∈ P := by
        simpa only [A, Set.mem_compl_iff, Set.mem_setOf_eq] using q.property
      exact hnot⟩
  have heCinj : Function.Injective eC := by
    intro q r hqr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Pᶜ) => (z : ι)) hqr
  have hCle : (∑' q : ↥(Aᶜ), f ((q : ↥((↑S : Set ι)ᶜ)) : ι)) ≤ C := by
    dsimp only [C]
    exact hAcsum.tsum_le_tsum_of_inj eC heCinj
      (fun q _ => hf0 (q : ι)) (fun q => le_rfl) hCsum
  have hsplit :
      (∑' q : A, f ((q : ↥((↑S : Set ι)ᶜ)) : ι)) +
        (∑' q : ↥(Aᶜ), f ((q : ↥((↑S : Set ι)ᶜ)) : ι)) =
          (∑' q : ↥((↑S : Set ι)ᶜ), f (q : ι)) :=
    Summable.tsum_add_tsum_compl (f := fun q : ↥((↑S : Set ι)ᶜ) => f (q : ι))
      (s := A) hAsum hAcsum
  refine ⟨S, hBS, hSP, hSsum, ?_⟩
  rw [← hsplit]
  linarith

/-- **Scheffé, positive-deficit form.**  The positive deficits of a pointwise convergent family
below a summable envelope have vanishing total. -/
theorem tendsto_tsum_posPart_of_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {plim : ι → ℝ} {S : ℝ}
    (hp0 : ∀ n k, 0 ≤ p n k) (hplimsum : HasSum plim S)
    (hconv : ∀ k, Tendsto (fun n => p n k) atTop (nhds (plim k))) :
    Tendsto (fun n => ∑' k, max (plim k - p n k) 0) atTop (nhds 0) := by
  have hplim0 : ∀ k, 0 ≤ plim k := by
    intro k
    exact ge_of_tendsto (hconv k) (Eventually.of_forall fun n => hp0 n k)
  have hdle : ∀ n k, max (plim k - p n k) 0 ≤ plim k := by
    intro n k
    refine max_le ?_ (hplim0 k)
    linarith [hp0 n k]
  have hd0 : ∀ n k, 0 ≤ max (plim k - p n k) 0 := fun n k => le_max_right _ _
  have hdsum : ∀ n, Summable (fun k => max (plim k - p n k) 0) := fun n =>
    Summable.of_nonneg_of_le (hd0 n) (hdle n) hplimsum.summable
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_lt hplimsum (half_pos hε)
  -- the finite head tends to zero
  have hhead : Tendsto (fun n => ∑ k ∈ F, max (plim k - p n k) 0) atTop (nhds 0) := by
    have hz : (0 : ℝ) = ∑ _k ∈ F, (0 : ℝ) := by simp
    rw [hz]
    refine tendsto_finsetSum F fun k _ => ?_
    have hcont : Tendsto (fun n => plim k - p n k) atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := plim k) (f := atTop (α := ℕ))).sub (hconv k)
      simpa using this
    have : Tendsto (fun n => max (plim k - p n k) 0) atTop (nhds (max 0 0)) :=
      (continuous_id.max continuous_const).continuousAt.tendsto.comp hcont
    simpa using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hbase := hN n hn
  rw [Real.dist_eq, sub_zero] at hbase ⊢
  have hsplit := (hdsum n).sum_add_tsum_compl (s := F)
  have htail : ∑' (x : ↑((↑F : Set ι)ᶜ)), max (plim ↑x - p n ↑x) 0
      ≤ ∑' (x : ↑((↑F : Set ι)ᶜ)), plim ↑x := by
    refine Summable.tsum_le_tsum (fun x => hdle n x) ?_ ?_
    · exact (hdsum n).subtype _
    · exact hplimsum.summable.subtype _
  have hnn : 0 ≤ ∑' k, max (plim k - p n k) 0 := tsum_nonneg (hd0 n)
  have hheadabs : ∑ k ∈ F, max (plim k - p n k) 0 < ε / 2 := by
    have := abs_lt.mp hbase
    linarith [this.2]
  rw [abs_of_nonneg hnn]
  linarith [hsplit, htail, hF]

/-- **Scheffé for counting measure.**  Pointwise convergence of probability vectors implies `l^(1 : ℕ)`
convergence: the `l^(1 : ℕ)` distance is twice the positive deficit, because equal totals force the two
deficits to agree. -/
theorem tendsto_tsum_abs_sub_of_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {plim : ι → ℝ} {S : ℝ}
    (hp0 : ∀ n k, 0 ≤ p n k) (hpsum : ∀ n, HasSum (p n) S) (hplimsum : HasSum plim S)
    (hconv : ∀ k, Tendsto (fun n => p n k) atTop (nhds (plim k))) :
    Tendsto (fun n => ∑' k, |p n k - plim k|) atTop (nhds 0) := by
  have hplim0 : ∀ k, 0 ≤ plim k := by
    intro k
    exact ge_of_tendsto (hconv k) (Eventually.of_forall fun n => hp0 n k)
  have key : ∀ n, ∑' k, |p n k - plim k| = 2 * ∑' k, max (plim k - p n k) 0 := by
    intro n
    have hposS : Summable (fun k => max (plim k - p n k) 0) :=
      Summable.of_nonneg_of_le (fun k => le_max_right _ _)
        (fun k => max_le (by linarith [hp0 n k]) (hplim0 k)) hplimsum.summable
    have hnegS : Summable (fun k => max (p n k - plim k) 0) :=
      Summable.of_nonneg_of_le (fun k => le_max_right _ _)
        (fun k => max_le (by linarith [hplim0 k]) (hp0 n k)) (hpsum n).summable
    have hdiff : HasSum (fun k => plim k - p n k) 0 := by
      have := hplimsum.sub (hpsum n)
      simpa using this
    have hsplitfun : ∀ k, plim k - p n k
        = max (plim k - p n k) 0 - max (p n k - plim k) 0 := by
      intro k
      rcases le_total (plim k) (p n k) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
    have habsfun : ∀ k, |p n k - plim k|
        = max (plim k - p n k) 0 + max (p n k - plim k) 0 := by
      intro k
      rcases le_total (plim k) (p n k) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith),
          abs_of_nonneg (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith),
          abs_of_nonpos (by linarith)]
        ring
    have heq : ∑' k, max (plim k - p n k) 0 = ∑' k, max (p n k - plim k) 0 := by
      have h0 : ∑' k, (plim k - p n k) = 0 := hdiff.tsum_eq
      rw [tsum_congr hsplitfun, hposS.tsum_sub hnegS] at h0
      linarith
    rw [tsum_congr habsfun, hposS.tsum_add hnegS, ← heq]
    ring
  have hmain := tendsto_tsum_posPart_of_tendsto hp0 hplimsum hconv
  have := hmain.const_mul (2 : ℝ)
  simpa [key] using this

/-- The absolute deficit of a nonnegative family below a summable one is summable. -/
theorem summable_abs_sub {ι : Type*} {f g : ι → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Summable f) (hg : Summable g) : Summable (fun k => |f k - g k|) := by
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) (hf.add hg)
  calc |f k - g k| ≤ |f k| + |g k| := abs_sub _ _
    _ = f k + g k := by rw [abs_of_nonneg (hf0 k), abs_of_nonneg (hg0 k)]

/-- **A finite head captures all but arbitrarily small mass, uniformly in `n`.**  This is the
tightness clause of the Corollary: one finite label set works for the whole family eventually,
because the limit's tail is small and the `l^(1 : ℕ)` distance to the limit is eventually small. -/
theorem exists_finset_eventually_tsum_compl_lt {ι : Type*} {p : ℕ → ι → ℝ} {plim : ι → ℝ} {S : ℝ}
    (hp0 : ∀ n k, 0 ≤ p n k) (hpsum : ∀ n, HasSum (p n) S) (hplimsum : HasSum plim S)
    (hconv : ∀ k, Tendsto (fun n => p n k) atTop (nhds (plim k))) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, ∀ᶠ n in atTop, ∑' (x : ↑((↑F : Set ι)ᶜ)), p n ↑x < ε := by
  have hplim0 : ∀ k, 0 ≤ plim k := fun k =>
    ge_of_tendsto (hconv k) (Eventually.of_forall fun n => hp0 n k)
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_lt hplimsum (half_pos hε)
  refine ⟨F, ?_⟩
  have hsch := tendsto_tsum_abs_sub_of_tendsto hp0 hpsum hplimsum hconv
  have hev : ∀ᶠ n in atTop, ∑' k, |p n k - plim k| < ε / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hsch (ε / 2) (half_pos hε)] with n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg fun k => abs_nonneg _)] at hn
    exact hn
  filter_upwards [hev] with n hn
  have habsS : Summable (fun k => |p n k - plim k|) :=
    summable_abs_sub (hp0 n) hplim0 (hpsum n).summable hplimsum.summable
  set A : ↑((↑F : Set ι)ᶜ) → ℝ := fun x => plim ↑x with hAdef
  set B : ↑((↑F : Set ι)ᶜ) → ℝ := fun x => |p n ↑x - plim ↑x| with hBdef
  set C : ↑((↑F : Set ι)ᶜ) → ℝ := fun x => p n ↑x with hCdef
  have hA : Summable A := hplimsum.summable.subtype _
  have hB : Summable B := habsS.subtype _
  have hC : Summable C := (hpsum n).summable.subtype _
  have hbound : ∑' x, C x ≤ ∑' x, A x + ∑' x, B x := by
    rw [← hA.tsum_add hB]
    refine Summable.tsum_le_tsum (fun x => ?_) hC (hA.add hB)
    have := le_abs_self (p n ↑x - plim ↑x)
    simp only [hAdef, hBdef, hCdef]
    linarith
  have htail : ∑' (x : ↑((↑F : Set ι)ᶜ)), |p n ↑x - plim ↑x| ≤ ∑' k, |p n k - plim k| := by
    have hnn : ∀ k, 0 ≤ |p n k - plim k| := fun k => abs_nonneg _
    have hsplit := habsS.sum_add_tsum_compl (s := F)
    have hfin : 0 ≤ ∑ k ∈ F, |p n k - plim k| :=
      Finset.sum_nonneg fun k _ => hnn k
    linarith
  linarith

/-- One finite head controlling both the limit's tail and, eventually, the family's tails. -/
theorem exists_finset_tail_bounds {ι : Type*} {p : ℕ → ι → ℝ} {plim : ι → ℝ} {S : ℝ}
    (hp0 : ∀ n k, 0 ≤ p n k) (hpsum : ∀ n, HasSum (p n) S) (hplimsum : HasSum plim S)
    (hconv : ∀ k, Tendsto (fun n => p n k) atTop (nhds (plim k))) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ι, (∑' (x : ↑((↑F : Set ι)ᶜ)), plim ↑x < ε) ∧
      (∀ᶠ n in atTop, ∑' (x : ↑((↑F : Set ι)ᶜ)), p n ↑x < ε) := by
  have hplim0 : ∀ k, 0 ≤ plim k := fun k =>
    ge_of_tendsto (hconv k) (Eventually.of_forall fun n => hp0 n k)
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_lt hplimsum (half_pos hε)
  refine ⟨F, by linarith, ?_⟩
  have hsch := tendsto_tsum_abs_sub_of_tendsto hp0 hpsum hplimsum hconv
  have hev : ∀ᶠ n in atTop, ∑' k, |p n k - plim k| < ε / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hsch (ε / 2) (half_pos hε)] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun k => abs_nonneg _)] at hn
    exact hn
  filter_upwards [hev] with n hn
  have habsS : Summable (fun k => |p n k - plim k|) :=
    summable_abs_sub (hp0 n) hplim0 (hpsum n).summable hplimsum.summable
  set A : ↑((↑F : Set ι)ᶜ) → ℝ := fun x => plim ↑x with hAdef
  set B : ↑((↑F : Set ι)ᶜ) → ℝ := fun x => |p n ↑x - plim ↑x| with hBdef
  set C : ↑((↑F : Set ι)ᶜ) → ℝ := fun x => p n ↑x with hCdef
  have hA : Summable A := hplimsum.summable.subtype _
  have hB : Summable B := habsS.subtype _
  have hC : Summable C := (hpsum n).summable.subtype _
  have hbound : ∑' x, C x ≤ ∑' x, A x + ∑' x, B x := by
    rw [← hA.tsum_add hB]
    refine Summable.tsum_le_tsum (fun x => ?_) hC (hA.add hB)
    have := le_abs_self (p n ↑x - plim ↑x)
    simp only [hAdef, hBdef, hCdef]
    linarith
  have htail : ∑' x, B x ≤ ∑' k, |p n k - plim k| := by
    have hsplit := habsS.sum_add_tsum_compl (s := F)
    have hfin : 0 ≤ ∑ k ∈ F, |p n k - plim k| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  linarith

/-- A bounded test function scales the absolute tested sum by its bound. -/
theorem abs_tsum_mul_le {ι : Type*} {q : ι → ℝ} {y : ι → ℝ} {f : ℝ → ℝ} {M : ℝ}
    (hq0 : ∀ k, 0 ≤ q k) (hqs : Summable q) (hM : ∀ t, |f t| ≤ M) :
    |∑' k, q k * f (y k)| ≤ M * ∑' k, q k := by
  have hb : ∀ k, ‖q k * f (y k)‖ ≤ M * q k := by
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 k)]
    calc q k * |f (y k)| ≤ q k * M := mul_le_mul_of_nonneg_left (hM _) (hq0 k)
      _ = M * q k := mul_comm _ _
  have hns : Summable (fun k => ‖q k * f (y k)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb (hqs.mul_left M)
  have h1 := norm_tsum_le_tsum_norm hns
  rw [Real.norm_eq_abs] at h1
  refine le_trans h1 ?_
  have hmul : ∑' k, M * q k = M * ∑' k, q k := hqs.tsum_mul_left M
  rw [← hmul]
  exact Summable.tsum_le_tsum hb hns (hqs.mul_left M)

/-- **Tested convergence.**  If the masses converge coordinatewise with equal totals and the
positions converge coordinatewise, then every bounded continuous test function has convergent
tested sums.  This is weak convergence of the associated atomic measures, stated on the sums
themselves. -/
theorem tendsto_tsum_mul_comp_of_tendsto {ι : Type*} {p : ℕ → ι → ℝ} {plim : ι → ℝ} {S : ℝ}
    {x : ℕ → ι → ℝ} {xlim : ι → ℝ} {f : ℝ → ℝ} {M : ℝ}
    (hp0 : ∀ n k, 0 ≤ p n k) (hpsum : ∀ n, HasSum (p n) S) (hplimsum : HasSum plim S)
    (hconv : ∀ k, Tendsto (fun n => p n k) atTop (nhds (plim k)))
    (hx : ∀ k, Tendsto (fun n => x n k) atTop (nhds (xlim k)))
    (hf : Continuous f) (hM : ∀ t, |f t| ≤ M) :
    Tendsto (fun n => ∑' k, p n k * f (x n k)) atTop
      (nhds (∑' k, plim k * f (xlim k))) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0)
  have hplim0 : ∀ k, 0 ≤ plim k := fun k =>
    ge_of_tendsto (hconv k) (Eventually.of_forall fun n => hp0 n k)
  have hsumn : ∀ n, Summable (fun k => p n k * f (x n k)) := by
    intro n
    refine Summable.of_norm_bounded (((hpsum n).summable).mul_left M) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 n k)]
    calc p n k * |f (x n k)| ≤ p n k * M := mul_le_mul_of_nonneg_left (hM _) (hp0 n k)
      _ = M * p n k := mul_comm _ _
  have hsumlim : Summable (fun k => plim k * f (xlim k)) := by
    refine Summable.of_norm_bounded ((hplimsum.summable).mul_left M) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hplim0 k)]
    calc plim k * |f (xlim k)| ≤ plim k * M := mul_le_mul_of_nonneg_left (hM _) (hplim0 k)
      _ = M * plim k := mul_comm _ _
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := ε / (4 * (M + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨F, hFlim, hFev⟩ := exists_finset_tail_bounds hp0 hpsum hplimsum hconv hδ
  -- the finite head converges
  have hhead : Tendsto (fun n => ∑ k ∈ F, p n k * f (x n k)) atTop
      (nhds (∑ k ∈ F, plim k * f (xlim k))) :=
    tendsto_finsetSum F fun k _ =>
      (hconv k).mul ((hf.continuousAt (x := xlim k)).tendsto.comp (hx k))
  have hheadev : ∀ᶠ n in atTop,
      |∑ k ∈ F, p n k * f (x n k) - ∑ k ∈ F, plim k * f (xlim k)| < ε / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hhead (ε / 2) (half_pos hε)] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [hFev, hheadev] with n hnF hnH
  -- split both sums into head and tail
  have hsplitn := (hsumn n).sum_add_tsum_compl (s := F)
  have hsplitlim := hsumlim.sum_add_tsum_compl (s := F)
  have htailn : |∑' (y : ↑((↑F : Set ι)ᶜ)), p n ↑y * f (x n ↑y)| ≤ M * δ := by
    refine le_trans (abs_tsum_mul_le (fun z => hp0 n ↑z) ((hpsum n).summable.subtype _) hM) ?_
    exact mul_le_mul_of_nonneg_left (le_of_lt hnF) hM0
  have htaillim : |∑' (y : ↑((↑F : Set ι)ᶜ)), plim ↑y * f (xlim ↑y)| ≤ M * δ := by
    refine le_trans (abs_tsum_mul_le (fun z => hplim0 ↑z) (hplimsum.summable.subtype _) hM) ?_
    exact mul_le_mul_of_nonneg_left (le_of_lt hFlim) hM0
  have hMδ : M * δ ≤ ε / 4 := by
    rw [hδdef]
    have key : M * (ε / (4 * (M + 1))) = (M * ε) / (4 * (M + 1)) := by ring
    rw [key, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith [hε.le, hM0]
  rw [Real.dist_eq]
  have ht1 := abs_le.mp htailn
  have ht2 := abs_le.mp htaillim
  have hh := abs_lt.mp hnH
  rw [abs_lt]
  constructor <;> linarith [hsplitn, hsplitlim, ht1.1, ht1.2, ht2.1, ht2.2, hh.1, hh.2, hMδ]

end GaloisForLFunctions.HTGeometry
