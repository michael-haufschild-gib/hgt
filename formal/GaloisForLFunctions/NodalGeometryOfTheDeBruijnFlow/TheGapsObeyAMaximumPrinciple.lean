import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheMeshPairOfAPacketOpens
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheZeroNumberDropsOnlyAtCollisions

/-!
# The gaps obey a maximum principle

The local repulsion law, in the form that needs no information from outside a parabolic cylinder. Fix an interval of heights `[A, B]`, a time interval
`[a, b]` with `b log B ≤ 1`, and let all zeros of the flow with real part in `[A, B]` be real and simple during `[a, b]`. If the squared gaps are at least `m₀` at time `a`,
and at least `m₀ + r(s − a)` for pairs touching the lateral layers `[A, A + 2)`, `(B − 2, B]`, then they are at least `m₀ + r(s − a)` in the whole cylinder, for `r ≍ 1/log B` and as long as the
barrier stays below `≍ log⁻²B` (`exists_gap_maximum_principle`).

So a pair of zeros below the mean spacing cannot arise in the interior of a real cylinder: the gaps of the cylinder are controlled by those
of its parabolic boundary, and the barrier rises at rate `≍ 1/log B`. Starting from `m₀ = 0` this is the law `g² ≳ (t − a)/log B`, the cluster
of `≍ log B` zeros being the only configuration that opens this slowly. The proof is a first touch: the first pair to reach the barrier is a
mesh pair of the packet around it, and there the rate of the squared gap is at least `16/n − O(g² log B)` (`gap_barrier_of_rate`).

Away from crowds the factor `1/log B` disappears. If at most `n` zeros lie within `ρ` of each zero of the cylinder, and the others have energy at most `E`, then the barrier rises at rate `8/n`, up to the level `1/(n(2E + log B))`
(`exists_gap_maximum_principle_of_count`). At normal density `E ≍ log²B/n`, and the barrier reads `min((t − a)/n, log⁻²B)`: the form of the central inequality.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## Real branches -/

/-- A window of total multiplicity one contains exactly one real zero. -/
theorem exists_unique_of_realZeroCount_eq_one {s a b : ℝ} (hs : 0 ≤ s) (h : realZeroCount s a b = 1) :
    ∃ y, y ∈ Icc a b ∧ riemannHeat s (y : ℂ) = 0 ∧
      ∀ y' ∈ Icc a b, riemannHeat s (y' : ℂ) = 0 → y' = y := by
  classical
  have hcard : (realZeroFinset s a b).card ≤ 1 := by
    have h1 : (realZeroFinset s a b).card ≤ realZeroCount s a b := by
      rw [realZeroCount, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun y hy =>
        one_le_zeroMult_riemannHeat hs ((mem_realZeroFinset hs).mp hy).2
    omega
  have hne : (realZeroFinset s a b).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    simp [realZeroCount, hn] at h
  obtain ⟨y, hy⟩ := hne
  refine ⟨y, ((mem_realZeroFinset hs).mp hy).1, ((mem_realZeroFinset hs).mp hy).2, fun y' hy' h0 => ?_⟩
  exact Finset.card_le_one.mp hcard y' ((mem_realZeroFinset hs).mpr ⟨hy', h0⟩) y hy

/-- **The real branch through a simple real zero**, in both time directions. -/
theorem exists_real_branch {s₀ : ℝ} (hs₀ : 0 < s₀) {x₀ : ℝ} (hz : riemannHeat s₀ (x₀ : ℂ) = 0)
    (hd : deriv (riemannHeat s₀) (x₀ : ℂ) ≠ 0) :
    ∃ ε₀ > 0, ∃ x : ℝ → ℝ, x s₀ = x₀ ∧ ContinuousAt x s₀ ∧
      (∀ᶠ s in 𝓝 s₀, riemannHeat s (x s : ℂ) = 0) ∧
      ∀ᶠ s in 𝓝 s₀, ∀ y : ℝ, |y - x₀| ≤ ε₀ → riemannHeat s (y : ℂ) = 0 → y = x s := by
  classical
  obtain ⟨ε₀, hε₀, hlaw⟩ := exists_local_realZeroCount_at_point hs₀ x₀ hz
  have hm := zeroMult_riemannHeat_eq_one hs₀.le hz hd
  have hcount (ε : ℝ) (hε : 0 < ε) (hεε₀ : ε ≤ ε₀) :
      ∀ᶠ s in 𝓝 s₀, 0 < s ∧ realZeroCount s (x₀ - ε) (x₀ + ε) = 1 := by
    obtain ⟨δ, hδ, h⟩ := hlaw ε hε hεε₀
    filter_upwards [Metric.ball_mem_nhds s₀ hδ] with s hs
    have hs' : |s - s₀| < δ := by simpa only [mem_ball, Real.dist_eq] using hs
    obtain ⟨hpos, h1, h2⟩ := h s hs'
    refine ⟨hpos, ?_⟩
    rcases le_or_gt s₀ s with h | h
    · rw [h1 h, hm]
    · rw [h2 h, hm]
  have hch (s : ℝ) : ∃ y : ℝ, (0 < s ∧ realZeroCount s (x₀ - ε₀) (x₀ + ε₀) = 1) →
      y ∈ Icc (x₀ - ε₀) (x₀ + ε₀) ∧ riemannHeat s (y : ℂ) = 0 ∧
        ∀ y' ∈ Icc (x₀ - ε₀) (x₀ + ε₀), riemannHeat s (y' : ℂ) = 0 → y' = y := by
    by_cases h : 0 < s ∧ realZeroCount s (x₀ - ε₀) (x₀ + ε₀) = 1
    · obtain ⟨y, hy⟩ := exists_unique_of_realZeroCount_eq_one h.1.le h.2
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x₀, fun h' => (h h').elim⟩
  choose x hx using hch
  have hev := hcount ε₀ hε₀ le_rfl
  have hwin (y : ℝ) (hy : |y - x₀| ≤ ε₀) : y ∈ Icc (x₀ - ε₀) (x₀ + ε₀) := by
    rw [abs_le] at hy
    constructor <;> linarith only [hy.1, hy.2]
  have hs₀ev : x s₀ = x₀ := by
    have hat := hev.self_of_nhds
    exact ((hx s₀ hat).2.2 x₀ (hwin x₀ (by simpa using hε₀.le)) hz).symm
  refine ⟨ε₀, hε₀, x, hs₀ev, ?_, ?_, ?_⟩
  · rw [Metric.continuousAt_iff']
    intro ε hε
    have hε' : 0 < min (ε / 2) ε₀ := lt_min (by positivity) hε₀
    filter_upwards [hev, hcount _ hε' (min_le_right _ _)] with s h1 h2
    obtain ⟨y, hy, hy0, -⟩ := exists_unique_of_realZeroCount_eq_one h2.1.le h2.2
    have hyabs : |y - x₀| ≤ min (ε / 2) ε₀ := by
      rw [abs_le]
      constructor <;> linarith only [hy.1, hy.2]
    have heq := (hx s h1).2.2 y (hwin y (hyabs.trans (min_le_right _ _))) hy0
    rw [Real.dist_eq, hs₀ev, ← heq]
    have := hyabs.trans (min_le_left _ _)
    linarith only [this, hε]
  · filter_upwards [hev] with s h1
    exact (hx s h1).2.1
  · filter_upwards [hev] with s h1 y hy hy0
    exact (hx s h1).2.2 y (hwin y hy) hy0

/-- Joint continuity of the flow at positive time. -/
theorem tendsto_riemannHeat_comp {ι : Type*} {l : Filter ι} {s₀ : ℝ} (hs₀ : 0 < s₀) {u : ι → ℝ} {w : ι → ℂ}
    {z : ℂ} (hu : Tendsto u l (𝓝 s₀)) (hw : Tendsto w l (𝓝 z)) :
    Tendsto (fun i => riemannHeat (u i) (w i)) l (𝓝 (riemannHeat s₀ z)) := by
  have hF := tendstoLocallyUniformly_riemannHeat_clamped_nhds s₀
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, ht, hev⟩ := Metric.tendstoLocallyUniformly_iff.mp hF (ε / 2) (by positivity) z
  have hcont : ContinuousAt (riemannHeat s₀) z := (differentiable_riemannHeat hs₀.le z).continuousAt
  have hc2 : ∀ᶠ v in 𝓝 z, dist (riemannHeat s₀ v) (riemannHeat s₀ z) < ε / 2 :=
    Metric.continuousAt_iff'.mp hcont (ε / 2) (by positivity)
  filter_upwards [hu.eventually hev, hw ht,
    hw.eventually hc2, hu.eventually (lt_mem_nhds hs₀)] with i h1 h2 h3 h4
  have h5 := h1 (w i) h2
  rw [max_eq_left h4.le, max_eq_left hs₀.le] at h5
  calc dist (riemannHeat (u i) (w i)) (riemannHeat s₀ z)
      ≤ dist (riemannHeat (u i) (w i)) (riemannHeat s₀ (w i)) +
          dist (riemannHeat s₀ (w i)) (riemannHeat s₀ z) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [dist_comm (riemannHeat (u i) (w i))]
        exact add_lt_add h5 h3
    _ = ε := by ring

/-! ## The first touch -/

/-- **The first touch.** In a parabolic cylinder over a real simple window `[A, B]`, the squared gaps stay above the barrier `m₀ + r(s − a)` if they do so on the parabolic boundary, and if every pair touching the barrier from above, as a mesh pair of the cylinder, has its squared gap opening at a rate larger than `r`. -/
theorem gap_barrier_of_rate {A B a b m₀ r : ℝ} (ha : 0 < a)
    (hreal : ∀ s ∈ Icc a b, ∀ z : ℂ, riemannHeat s z = 0 → z.re ∈ Icc A B →
      z.im = 0 ∧ deriv (riemannHeat s) z ≠ 0)
    (hstart : ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat a (x : ℂ) = 0 →
      riemannHeat a (x' : ℂ) = 0 → m₀ ≤ (x' - x) ^ 2)
    (hlat : ∀ s ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat s (x : ℂ) = 0 →
      riemannHeat s (x' : ℂ) = 0 → (x < A + 2 ∨ B - 2 < x') → m₀ + r * (s - a) ≤ (x' - x) ^ 2)
    (hrate : ∀ c ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc (A + 2) (B - 2) → x' ∈ Icc (A + 2) (B - 2) →
      riemannHeat c (x : ℂ) = 0 → riemannHeat c (x' : ℂ) = 0 → (x' - x) ^ 2 = m₀ + r * (c - a) →
      (∀ q q' : ℝ, q < q' → q ∈ Icc A B → q' ∈ Icc A B → riemannHeat c (q : ℂ) = 0 → riemannHeat c (q' : ℂ) = 0 →
        (x' - x) ^ 2 ≤ (q' - q) ^ 2) →
      r < 2 * (x' - x) * ((zeroVelocity c (x' : ℂ)).re - (zeroVelocity c (x : ℂ)).re)) :
    ∀ s ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat s (x : ℂ) = 0 →
      riemannHeat s (x' : ℂ) = 0 → m₀ + r * (s - a) ≤ (x' - x) ^ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s₁, hs₁, y₁, y₁', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hcon
  set m : ℝ → ℝ := fun s => m₀ + r * (s - a) with hm
  -- the violating times
  set T : Set ℝ := {s | s ∈ Icc a b ∧ ∃ x x' : ℝ, x < x' ∧ x ∈ Icc A B ∧ x' ∈ Icc A B ∧
    riemannHeat s (x : ℂ) = 0 ∧ riemannHeat s (x' : ℂ) = 0 ∧ (x' - x) ^ 2 < m s} with hT
  have hTne : T.Nonempty := ⟨s₁, hs₁, y₁, y₁', h₁, h₂, h₃, h₄, h₅, h₆⟩
  have hTbdd : BddBelow T := ⟨a, fun s hs => hs.1.1⟩
  set c := sInf T with hc
  have hac : a ≤ c := le_csInf hTne fun s hs => hs.1.1
  have hcb : c ≤ b := (csInf_le hTbdd ⟨hs₁, y₁, y₁', h₁, h₂, h₃, h₄, h₅, h₆⟩).trans hs₁.2
  have hcI : c ∈ Icc a b := ⟨hac, hcb⟩
  have hcpos : 0 < c := ha.trans_le hac
  obtain ⟨u, -, hu, huT⟩ := exists_seq_tendsto_sInf hTne hTbdd
  choose p p' hp using fun n => (huT n).2
  -- violating pairs avoid the lateral layers
  have hinner (s : ℝ) (hs : s ∈ Icc a b) (x x' : ℝ) (h1 : x < x') (h2 : x ∈ Icc A B) (h3 : x' ∈ Icc A B)
      (h4 : riemannHeat s (x : ℂ) = 0) (h5 : riemannHeat s (x' : ℂ) = 0) (h6 : (x' - x) ^ 2 < m s) :
      A + 2 ≤ x ∧ x' ≤ B - 2 := by
    by_contra hn
    have hn' : x < A + 2 ∨ B - 2 < x' := by
      by_contra hk
      push Not at hk
      exact hn hk
    exact absurd (hlat s hs x x' h1 h2 h3 h4 h5 hn') (not_le.mpr h6)
  -- a limit pair
  have hmem (n : ℕ) : (p n, p' n) ∈ Icc (A + 2) (B - 2) ×ˢ Icc (A + 2) (B - 2) := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp n
    obtain ⟨h7, h8⟩ := hinner (u n) (huT n).1 (p n) (p' n) h1 h2 h3 h4 h5 h6
    exact ⟨⟨h7, by linarith only [h1, h8]⟩, ⟨by linarith only [h1, h7], h8⟩⟩
  obtain ⟨⟨x, x'⟩, hxmem, φ, hφ, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hmem
  have hlim1 : Tendsto (fun n => p (φ n)) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hlim
  have hlim2 : Tendsto (fun n => p' (φ n)) atTop (𝓝 x') := (continuous_snd.tendsto _).comp hlim
  have huφ : Tendsto (fun n => u (φ n)) atTop (𝓝 c) := hu.comp hφ.tendsto_atTop
  have hzero (y : ℕ → ℝ) (ylim : ℝ) (hy : Tendsto y atTop (𝓝 ylim))
      (h0 : ∀ n, riemannHeat (u (φ n)) (y n : ℂ) = 0) : riemannHeat c (ylim : ℂ) = 0 := by
    have h := tendsto_riemannHeat_comp hcpos huφ (Complex.continuous_ofReal.continuousAt.tendsto.comp hy)
    refine tendsto_nhds_unique h ?_
    simp only [Function.comp_def, h0]
    exact tendsto_const_nhds
  have hx0 : riemannHeat c (x : ℂ) = 0 := hzero _ x hlim1 fun n => (hp (φ n)).2.2.2.1
  have hx'0 : riemannHeat c (x' : ℂ) = 0 := hzero _ x' hlim2 fun n => (hp (φ n)).2.2.2.2.1
  have hxin : x ∈ Icc (A + 2) (B - 2) := hxmem.1
  have hx'in : x' ∈ Icc (A + 2) (B - 2) := hxmem.2
  have hAB (y : ℝ) (hy : y ∈ Icc (A + 2) (B - 2)) : y ∈ Icc A B :=
    ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  have hsimple (y : ℝ) (hy0 : riemannHeat c (y : ℂ) = 0) (hy : y ∈ Icc A B) :
      deriv (riemannHeat c) (y : ℂ) ≠ 0 :=
    (hreal c hcI _ hy0 (by rwa [Complex.ofReal_re])).2
  -- branches through the limit points
  obtain ⟨ε, hε, y, hy0, hyc, hyz, hyu⟩ := exists_real_branch hcpos hx0 (hsimple x hx0 (hAB x hxin))
  obtain ⟨ε', hε', y', hy'0, hy'c, hy'z, hy'u⟩ :=
    exists_real_branch hcpos hx'0 (hsimple x' hx'0 (hAB x' hx'in))
  -- along the sequence the pair lies on the branches
  have hevyu := huφ.eventually hyu
  have hevy'u := huφ.eventually hy'u
  have hevp : ∀ᶠ n in atTop, |p (φ n) - x| ≤ ε := by
    have := (hlim1.sub_const x).abs
    simp only [sub_self, abs_zero] at this
    exact (this.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  have hevp' : ∀ᶠ n in atTop, |p' (φ n) - x'| ≤ ε' := by
    have := (hlim2.sub_const x').abs
    simp only [sub_self, abs_zero] at this
    exact (this.eventually (gt_mem_nhds hε')).mono fun _ h => h.le
  -- the two limit points differ
  have hle : x ≤ x' := le_of_tendsto_of_tendsto' hlim1 hlim2 fun n => (hp (φ n)).1.le
  have hne : x ≠ x' := by
    intro heq
    have hevq : ∀ᶠ n in atTop, |p' (φ n) - x| ≤ ε := by
      have := (hlim2.sub_const x).abs
      rw [← heq] at this
      simp only [sub_self, abs_zero] at this
      exact (this.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
    obtain ⟨n, h1, h2, h3⟩ := (hevyu.and (hevp.and hevq)).exists
    have hA' := h1 _ h2 (hp (φ n)).2.2.2.1
    have hC := h1 _ h3 (hp (φ n)).2.2.2.2.1
    have := (hp (φ n)).1
    rw [hA', hC] at this
    exact lt_irrefl _ this
  have hlt : x < x' := lt_of_le_of_ne hle hne
  -- no pair is below the barrier at time `c`
  have hall : ∀ q q' : ℝ, q < q' → q ∈ Icc A B → q' ∈ Icc A B → riemannHeat c (q : ℂ) = 0 →
      riemannHeat c (q' : ℂ) = 0 → m c ≤ (q' - q) ^ 2 := by
    intro q q' h1 h2 h3 h4 h5
    by_contra hn
    have hn' := not_le.mp hn
    rcases hac.eq_or_lt with heq | hlt'
    · have h := hstart q q' h1 h2 h3 (by rw [heq]; exact h4) (by rw [heq]; exact h5)
      have hmc : m c = m₀ := by
        simp only [hm]
        rw [← heq, sub_self, mul_zero, add_zero]
      rw [hmc] at hn'
      exact absurd h (not_le.mpr hn')
    · obtain ⟨h6, h7⟩ := hinner c hcI q q' h1 h2 h3 h4 h5 hn'
      obtain ⟨-, -, z, hz0, hzc, hzz, -⟩ := exists_real_branch hcpos h4 (hsimple q h4 h2)
      obtain ⟨-, -, z', hz'0, hz'c, hz'z, -⟩ := exists_real_branch hcpos h5 (hsimple q' h5 h3)
      have hmcont : ContinuousAt m c := by
        simp only [hm]
        fun_prop
      have hG : ContinuousAt (fun s => m s - (z' s - z s) ^ 2) c := hmcont.sub ((hz'c.sub hzc).pow 2)
      have hG0 : 0 < m c - (z' c - z c) ^ 2 := by
        rw [hz0, hz'0]
        linarith only [hn']
      have hev1 := hG.eventually (lt_mem_nhds hG0)
      have hev2 : ∀ᶠ s in 𝓝 c, z s < z' s := by
        have hc' : ContinuousAt (fun s => z' s - z s) c := hz'c.sub hzc
        have h8 : 0 < z' c - z c := by
          rw [hz0, hz'0]
          linarith only [h1]
        filter_upwards [hc'.eventually (lt_mem_nhds h8)] with s hs
        linarith only [hs]
      have hev3 : ∀ᶠ s in 𝓝 c, |z s - q| < 1 := by
        have hc' : ContinuousAt (fun s => |z s - q|) c := (hzc.sub continuousAt_const).abs
        have h8 : |z c - q| < 1 := by
          rw [hz0, sub_self, abs_zero]
          norm_num
        exact hc'.eventually (gt_mem_nhds h8)
      have hev4 : ∀ᶠ s in 𝓝 c, |z' s - q'| < 1 := by
        have hc' : ContinuousAt (fun s => |z' s - q'|) c := (hz'c.sub continuousAt_const).abs
        have h8 : |z' c - q'| < 1 := by
          rw [hz'0, sub_self, abs_zero]
          norm_num
        exact hc'.eventually (gt_mem_nhds h8)
      have hleft : ∀ᶠ s in 𝓝[<] c, s ∈ Ioo a c := Ioo_mem_nhdsLT hlt'
      obtain ⟨s, hs, h8, h9, h10, h11, h12, h13⟩ := (hleft.and
        ((hev1.and (hev2.and (hev3.and (hev4.and (hzz.and hz'z))))).filter_mono
          nhdsWithin_le_nhds)).exists
      have h14 := abs_lt.mp h10
      have h15 := abs_lt.mp h11
      have hsT : s ∈ T := ⟨⟨hs.1.le, hs.2.le.trans hcb⟩, z s, z' s, h9,
        ⟨by linarith only [h14.1, h6], by linarith only [h14.2, h1, h7]⟩,
        ⟨by linarith only [h15.1, h1, h6], by linarith only [h15.2, h7]⟩, h12, h13,
        by linarith only [h8]⟩
      exact absurd (csInf_le hTbdd hsT) (not_le.mpr hs.2)
  -- the limit pair touches the barrier
  have hmcont : Continuous m := by
    simp only [hm]
    fun_prop
  have hupper : (x' - x) ^ 2 ≤ m c := by
    have h1 : Tendsto (fun n => (p' (φ n) - p (φ n)) ^ 2) atTop (𝓝 ((x' - x) ^ 2)) :=
      (hlim2.sub hlim1).pow 2
    have h2 : Tendsto (fun n => m (u (φ n))) atTop (𝓝 (m c)) := (hmcont.tendsto c).comp huφ
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => (hp (φ n)).2.2.2.2.2.le
  have htouch : (x' - x) ^ 2 = m c := le_antisymm hupper (hall x x' hlt (hAB x hxin) (hAB x' hx'in) hx0 hx'0)
  -- the rate at the touching pair
  have hDpos' : 0 < 2 * (x' - x) * ((zeroVelocity c (x' : ℂ)).re - (zeroVelocity c (x : ℂ)).re) - r := by
    have := hrate c hcI x x' hlt hxin hx'in hx0 hx'0 htouch (fun q q' h1 h2 h3 h4 h5 => by
      rw [htouch]
      exact hall q q' h1 h2 h3 h4 h5)
    linarith only [this]
  -- derivative of the touching function
  have hdy := hasDerivAt_real_zero_path hcpos hyc hyz (by rw [hy0]; exact hsimple x hx0 (hAB x hxin))
  have hdy' := hasDerivAt_real_zero_path hcpos hy'c hy'z (by rw [hy'0]; exact hsimple x' hx'0 (hAB x' hx'in))
  rw [hy0] at hdy
  rw [hy'0] at hdy'
  have hmd : HasDerivAt m r c := by
    have h := (((hasDerivAt_id c).sub_const a).const_mul r).const_add m₀
    simpa only [hm, id, mul_one] using h
  set G : ℝ → ℝ := fun s => (y' s - y s) ^ 2 - m s with hGdef
  have hGd : HasDerivAt G (2 * (x' - x) * ((zeroVelocity c (x' : ℂ)).re - (zeroVelocity c (x : ℂ)).re) - r) c := by
    have h := ((hdy'.sub hdy).pow 2).sub hmd
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply, hy0, hy'0]
    norm_num
  have hGc : G c = 0 := by
    simp only [hGdef, hy0, hy'0]
    linarith only [htouch]
  have hslope : ∀ᶠ s in 𝓝[≠] c, 0 < slope G c s :=
    (hasDerivAt_iff_tendsto_slope.mp hGd).eventually (lt_mem_nhds hDpos')
  rw [eventually_nhdsWithin_iff] at hslope
  obtain ⟨n, h1, h2, h3, h4, h5⟩ := (hevyu.and (hevp.and (hevy'u.and (hevp'.and
    (huφ.eventually hslope))))).exists
  have hA' := h1 _ h2 (hp (φ n)).2.2.2.1
  have hC := h3 _ h4 (hp (φ n)).2.2.2.2.1
  have hGneg : G (u (φ n)) < 0 := by
    simp only [hGdef]
    rw [← hA', ← hC]
    linarith only [(hp (φ n)).2.2.2.2.2]
  have hcu : c ≤ u (φ n) := csInf_le hTbdd (huT (φ n))
  rcases hcu.eq_or_lt with heq | hltu
  · rw [← heq, hGc] at hGneg
    exact lt_irrefl _ hGneg
  · have h6 := h5 hltu.ne'
    rw [slope_def_field, hGc, sub_zero] at h6
    have h7 := (div_pos_iff_of_pos_right (sub_pos.mpr hltu)).mp h6
    exact absurd hGneg (not_lt.mpr h7.le)

/-- The height needed for the logarithm to be large. -/
private theorem eight_le_log_of_le {A : ℝ} (hA : 4096 ≤ A) : 8 ≤ Real.log A := by
  have h1 : Real.exp 8 ≤ 4096 := by
    have h2 := Real.exp_one_lt_d9
    have h3 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    calc Real.exp 1 ^ 8 ≤ 2.7182818286 ^ 8 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 8
      _ ≤ 4096 := by norm_num
  have h4 := Real.log_le_log (Real.exp_pos 8) (h1.trans hA)
  rwa [Real.log_exp] at h4

/-- **The maximum principle for the gaps.** In a parabolic cylinder over a real simple window `[A, B]`, the squared gaps stay above
the barrier `m₀ + (s − a)/(C log B)` if they do so on the parabolic boundary: at time `a` and on the lateral layers. The barrier must stay below
`(C log B)⁻²`. -/
theorem exists_gap_maximum_principle :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ A B a b m₀ : ℝ, X₀ ≤ A → 0 < a → a ≤ b → b ≤ 1 / 8 →
      b * Real.log B ≤ 1 → m₀ + (b - a) / (C * Real.log B) ≤ 1 / (C * Real.log B) ^ 2 →
      (∀ s ∈ Icc a b, ∀ z : ℂ, riemannHeat s z = 0 → z.re ∈ Icc A B →
        z.im = 0 ∧ deriv (riemannHeat s) z ≠ 0) →
      (∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat a (x : ℂ) = 0 →
        riemannHeat a (x' : ℂ) = 0 → m₀ ≤ (x' - x) ^ 2) →
      (∀ s ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat s (x : ℂ) = 0 →
        riemannHeat s (x' : ℂ) = 0 → (x < A + 2 ∨ B - 2 < x') →
        m₀ + (s - a) / (C * Real.log B) ≤ (x' - x) ^ 2) →
      ∀ s ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat s (x : ℂ) = 0 →
        riemannHeat s (x' : ℂ) = 0 → m₀ + (s - a) / (C * Real.log B) ≤ (x' - x) ^ 2 := by
  obtain ⟨C₀, hC₀, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨2 * C₀ + 1, by positivity, X₀, hX₀, ?_⟩
  intro A B a b m₀ hA ha hab hb hbX hcap hreal hstart hlat s hs y₁ y₁' h₁ h₂ h₃ h₄ h₅
  have hBA : A ≤ B := h₂.1.trans h₂.2
  have hAbig : 4096 ≤ A := hX₀.trans hA
  have hLA : 8 ≤ Real.log A := eight_le_log_of_le hAbig
  have hlogAB : Real.log A ≤ Real.log B := Real.log_le_log (by linarith only [hAbig]) hBA
  set L := Real.log B with hLdef
  have hL : 0 < L := by linarith only [hLA, hlogAB]
  set K := C₀ * L with hK
  have hKpos : 0 < K := by positivity
  set D := (2 * C₀ + 1) * L with hD
  have hDpos : 0 < D := by positivity
  have hDK : 2 * K ≤ D := by
    rw [hD, hK]
    nlinarith only [hL]
  have hDL : L ≤ D := by
    rw [hD]
    nlinarith only [hL, hC₀]
  have hD1 : 1 ≤ D := by linarith only [hDL, hLA, hlogAB]
  set r := 1 / D with hr
  have hrpos : 0 < r := by positivity
  have hdiv (u : ℝ) : u / D = r * u := by
    rw [hr]
    ring
  simp only [hdiv] at hcap hlat ⊢
  refine gap_barrier_of_rate ha hreal hstart hlat ?_ s hs y₁ y₁' h₁ h₂ h₃ h₄ h₅
  intro c hcI x x' hlt hxin hx'in hx0 hx'0 htouch hmin
  have hcpos : 0 < c := ha.trans_le hcI.1
  have hcb := hcI.2
  have hgcap : (x' - x) ^ 2 ≤ 1 / D ^ 2 := by
    rw [htouch]
    have h1 := mul_le_mul_of_nonneg_left hcb hrpos.le
    linarith only [h1, hcap]
  have hg1 : x' - x < 1 := by
    have h1 : (x' - x) ^ 2 < 1 := by
      refine hgcap.trans_lt ?_
      rw [div_lt_one (by positivity)]
      nlinarith only [hD1, hLA, hlogAB, hDL]
    nlinarith only [h1, sub_pos.mpr hlt]
  -- the rate at the touching pair, in the packet around `x`
  have hxA : X₀ ≤ x := by linarith only [hA, hxin.1]
  have hxpos : 0 < x := by linarith only [hxin.1, hAbig]
  have hlogx : Real.log x ≤ L := Real.log_le_log hxpos (by linarith only [hxin.2])
  have hcX : c * Real.log x ≤ 1 := by
    have h1 : c * Real.log x ≤ c * L := mul_le_mul_of_nonneg_left hlogx hcpos.le
    have h2 : c * L ≤ b * L := mul_le_mul_of_nonneg_right hcb hL.le
    linarith only [h1, h2, hbX]
  obtain ⟨S, Q, hpacket, hcount, -, hQ⟩ := hforce x hxA c hcpos.le (hcb.trans hb) hcX
  have hC₀log : C₀ * Real.log x ≤ K := mul_le_mul_of_nonneg_left hlogx hC₀.le
  have hSin (w : ℂ) (hw : w ∈ S) : w.re ∈ Icc A B := by
    have h1 := abs_le.mp ((hpacket w).mp hw).2
    exact ⟨by linarith only [h1.1, hxin.1], by linarith only [h1.2, hxin.2]⟩
  have hSreal (w : ℂ) (hw : w ∈ S) : w.im = 0 ∧ deriv (riemannHeat c) w ≠ 0 :=
    hreal c hcI w ((hpacket w).mp hw).1 (hSin w hw)
  have hrate := mesh_pair_rate_ge (K := K) (X := x) hcpos hpacket
    (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2.1.trans hC₀log, (hQ z h1 h2).2.2.2.2⟩) hlt
    (by rw [sub_self, abs_zero]; norm_num)
    (by rw [abs_of_pos (sub_pos.mpr hlt)]; exact hg1) hx0 hx'0
    (fun w hw => (hSreal w hw).1) (fun w hw => (hSreal w hw).2)
    (by
      intro w hw w' hw' hww
      have hwof (v : ℂ) (hv : v ∈ S) : v = ((v.re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [(hSreal v hv).1])
      have hre : w.re ≠ w'.re := fun h => hww (by rw [hwof w hw, hwof w' hw', h])
      have hz1 : riemannHeat c ((w.re : ℝ) : ℂ) = 0 := by
        rw [← hwof w hw]
        exact ((hpacket w).mp hw).1
      have hz2 : riemannHeat c ((w'.re : ℝ) : ℂ) = 0 := by
        rw [← hwof w' hw']
        exact ((hpacket w').mp hw').1
      have hsq : (x' - x) ^ 2 ≤ (w.re - w'.re) ^ 2 := by
        rcases lt_or_gt_of_ne hre with h | h
        · have := hmin _ _ h (hSin w hw) (hSin w' hw') hz1 hz2
          rwa [show (w'.re - w.re) ^ 2 = (w.re - w'.re) ^ 2 by ring] at this
        · exact hmin _ _ h (hSin w' hw') (hSin w hw) hz2 hz1
      exact (le_abs_self _).trans (sq_le_sq.mp hsq))
  have hcard : (S.card : ℝ) ≤ K := by
    refine le_trans ?_ (hcount.trans hC₀log)
    have : S.card ≤ ∑ w ∈ S, zeroMult (riemannHeat c) w := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun w hw =>
        one_le_zeroMult_riemannHeat hcpos.le ((hpacket w).mp hw).1
    exact_mod_cast this
  have hxS : (x : ℂ) ∈ S := (hpacket _).mpr ⟨hx0, by
    rw [Complex.ofReal_re, sub_self, abs_zero]
    norm_num⟩
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨_, hxS⟩
  have h16 : 16 / K ≤ 16 / (S.card : ℝ) := div_le_div_of_nonneg_left (by norm_num) hSpos hcard
  have hgcap2 : (x' - x) ^ 2 ≤ 1 / (2 * K) ^ 2 := by
    refine hgcap.trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hDK 2))
  have hquad : 4 * K * (x' - x) ^ 2 ≤ 1 / K := by
    have := mul_le_mul_of_nonneg_left hgcap2 (by positivity : 0 ≤ 4 * K)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hrK : r ≤ 1 / (2 * K) := one_div_le_one_div_of_le (by positivity) hDK
  have h1 : 16 / K = 16 * (1 / K) := by ring
  have h2 : 1 / (2 * K) = (1 / K) / 2 := by
    field_simp
  have h3 : 0 < 1 / K := by positivity
  rw [h2] at hrK
  linarith only [hrate, h16, hquad, h1, h3, hrK]

/-- **The maximum principle away from crowds.** Let at most `n` zeros of the flow lie within `ρ` of each zero of the cylinder, and let the other zeros of its packet have energy at most `E` there. Then the squared gaps stay above the barrier `m₀ + (8/n)(s − a)` if they do so on the parabolic boundary, as long as the barrier stays below `1/(n(2E + C log B))`. -/
theorem exists_gap_maximum_principle_of_count :
    ∃ C > 0, ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ (A B a b m₀ ρ E : ℝ) (n : ℕ), X₀ ≤ A → 0 < a → a ≤ b → b ≤ 1 / 8 →
      b * Real.log B ≤ 1 → 0 < n → 0 ≤ E → 0 < ρ → m₀ + 8 / (n : ℝ) * (b - a) < 1 →
      4 * (m₀ + 8 / (n : ℝ) * (b - a)) ≤ ρ ^ 2 →
      (m₀ + 8 / (n : ℝ) * (b - a)) * (4 * (2 * E + C * Real.log B)) ≤ 4 / (n : ℝ) →
      (∀ s ∈ Icc a b, ∀ z : ℂ, riemannHeat s z = 0 → z.re ∈ Icc A B →
        z.im = 0 ∧ deriv (riemannHeat s) z ≠ 0) →
      (∀ s ∈ Icc a b, ∀ x ∈ Icc (A + 2) (B - 2), riemannHeat s (x : ℂ) = 0 → ∀ Z : Finset ℂ,
        (∀ w, w ∈ Z ↔ riemannHeat s w = 0 ∧ |w.re - x| ≤ 2) →
        ((Z.filter fun w => |w.re - x| < ρ).card : ℝ) ≤ n ∧
        ∑ w ∈ Z.filter (fun w => ρ ≤ |w.re - x|), (zeroMult (riemannHeat s) w : ℝ) / (w.re - x) ^ 2 ≤ E) →
      (∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat a (x : ℂ) = 0 →
        riemannHeat a (x' : ℂ) = 0 → m₀ ≤ (x' - x) ^ 2) →
      (∀ s ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat s (x : ℂ) = 0 →
        riemannHeat s (x' : ℂ) = 0 → (x < A + 2 ∨ B - 2 < x') →
        m₀ + 8 / (n : ℝ) * (s - a) ≤ (x' - x) ^ 2) →
      ∀ s ∈ Icc a b, ∀ x x' : ℝ, x < x' → x ∈ Icc A B → x' ∈ Icc A B → riemannHeat s (x : ℂ) = 0 →
        riemannHeat s (x' : ℂ) = 0 → m₀ + 8 / (n : ℝ) * (s - a) ≤ (x' - x) ^ 2 := by
  obtain ⟨C₀, hC₀, X₀, hX₀, hforce⟩ := exists_uniform_riemannHeat_exterior_force
  refine ⟨C₀, hC₀, X₀, hX₀, ?_⟩
  intro A B a b m₀ ρ E n hA ha hab hb hbX hn hE hρ hone hρcap hcap hreal hlocal hstart hlat s hs y₁ y₁' h₁ h₂ h₃ h₄ h₅
  have hBA : A ≤ B := h₂.1.trans h₂.2
  have hAbig : 4096 ≤ A := hX₀.trans hA
  have hLA : 8 ≤ Real.log A := eight_le_log_of_le hAbig
  have hlogAB : Real.log A ≤ Real.log B := Real.log_le_log (by linarith only [hAbig]) hBA
  set L := Real.log B with hLdef
  have hL : 0 < L := by linarith only [hLA, hlogAB]
  set K := C₀ * L with hK
  have hKpos : 0 < K := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set r := 8 / (n : ℝ) with hr
  have hrpos : 0 < r := by positivity
  refine gap_barrier_of_rate ha hreal hstart hlat ?_ s hs y₁ y₁' h₁ h₂ h₃ h₄ h₅
  intro c hcI x x' hlt hxin hx'in hx0 hx'0 htouch hmin
  have hcpos : 0 < c := ha.trans_le hcI.1
  have hcb := hcI.2
  have hgb : (x' - x) ^ 2 ≤ m₀ + r * (b - a) := by
    rw [htouch]
    have h1 := mul_le_mul_of_nonneg_left hcb hrpos.le
    linarith only [h1]
  have hgpos : 0 < x' - x := sub_pos.mpr hlt
  have hg1 : x' - x < 1 := by
    have h1 : (x' - x) ^ 2 < 1 := hgb.trans_lt hone
    nlinarith only [h1, hgpos]
  have h2gρ : 2 * (x' - x) ≤ ρ := by
    have h1 : (2 * (x' - x)) ^ 2 ≤ ρ ^ 2 := by nlinarith only [hgb, hρcap]
    exact (sq_le_sq₀ (by positivity) hρ.le).mp h1
  -- the packet around `x`
  have hxA : X₀ ≤ x := by linarith only [hA, hxin.1]
  have hxpos : 0 < x := by linarith only [hxin.1, hAbig]
  have hlogx : Real.log x ≤ L := Real.log_le_log hxpos (by linarith only [hxin.2])
  have hcX : c * Real.log x ≤ 1 := by
    have h1 : c * Real.log x ≤ c * L := mul_le_mul_of_nonneg_left hlogx hcpos.le
    have h2 : c * L ≤ b * L := mul_le_mul_of_nonneg_right hcb hL.le
    linarith only [h1, h2, hbX]
  obtain ⟨S, Q, hpacket, -, -, hQ⟩ := hforce x hxA c hcpos.le (hcb.trans hb) hcX
  have hC₀log : C₀ * Real.log x ≤ K := mul_le_mul_of_nonneg_left hlogx hC₀.le
  have hSin (w : ℂ) (hw : w ∈ S) : w.re ∈ Icc A B := by
    have h1 := abs_le.mp ((hpacket w).mp hw).2
    exact ⟨by linarith only [h1.1, hxin.1], by linarith only [h1.2, hxin.2]⟩
  have hSreal (w : ℂ) (hw : w ∈ S) : w.im = 0 ∧ deriv (riemannHeat c) w ≠ 0 :=
    hreal c hcI w ((hpacket w).mp hw).1 (hSin w hw)
  obtain ⟨hcount, hfar⟩ := hlocal c hcI x hxin hx0 S hpacket
  have hrate := local_pair_rate_ge (K := K) (E := E) (ρ := ρ) (n := n) (X := x) hcpos hpacket
    (fun z h1 h2 => ⟨(hQ z h1 h2).1, (hQ z h1 h2).2.2.1.trans hC₀log, (hQ z h1 h2).2.2.2.2⟩) hlt
    (by rw [sub_self, abs_zero]; norm_num)
    (by rw [abs_of_pos hgpos]; exact hg1) hx0 hx'0
    (fun w hw => (hSreal w hw).1) (fun w hw => (hSreal w hw).2) h2gρ
    (by
      intro w hw w' hw' hww _ _
      have hwof (v : ℂ) (hv : v ∈ S) : v = ((v.re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [(hSreal v hv).1])
      have hre : w.re ≠ w'.re := fun h => hww (by rw [hwof w hw, hwof w' hw', h])
      have hz1 : riemannHeat c ((w.re : ℝ) : ℂ) = 0 := by
        rw [← hwof w hw]
        exact ((hpacket w).mp hw).1
      have hz2 : riemannHeat c ((w'.re : ℝ) : ℂ) = 0 := by
        rw [← hwof w' hw']
        exact ((hpacket w').mp hw').1
      have hsq : (x' - x) ^ 2 ≤ (w.re - w'.re) ^ 2 := by
        rcases lt_or_gt_of_ne hre with h | h
        · have := hmin _ _ h (hSin w hw) (hSin w' hw') hz1 hz2
          rwa [show (w'.re - w.re) ^ 2 = (w.re - w'.re) ^ 2 by ring] at this
        · exact hmin _ _ h (hSin w' hw') (hSin w hw) hz2 hz1
      exact (le_abs_self _).trans (sq_le_sq.mp hsq)) hcount hfar
  have hEK : 0 ≤ 4 * (2 * E + K) := by positivity
  have hcap' : (x' - x) ^ 2 * (4 * (2 * E + K)) ≤ 4 / (n : ℝ) :=
    (mul_le_mul_of_nonneg_right hgb hEK).trans hcap
  have hval : 16 / (n : ℝ) = 4 / (n : ℝ) + 4 / (n : ℝ) + 8 / (n : ℝ) := by ring
  have hpos4 : 0 < 4 / (n : ℝ) := by positivity
  have hfinal : 4 * (2 * E + K) * (x' - x) ^ 2 ≤ 4 / (n : ℝ) := by
    calc 4 * (2 * E + K) * (x' - x) ^ 2 = (x' - x) ^ 2 * (4 * (2 * E + K)) := by ring
      _ ≤ _ := hcap'
  rw [hr]
  linarith only [hrate, hfinal, hval, hpos4]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
