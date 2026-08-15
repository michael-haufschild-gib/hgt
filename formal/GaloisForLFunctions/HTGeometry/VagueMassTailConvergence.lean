import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Tail values from local convergence and convergence of total mass

A family of nonnegative densities on `(c, ∞)` that converges on every bounded subinterval, and whose
total mass converges, has convergent tail integrals — with no tightness estimate at either end.

Mass cannot escape: dropping the piece near `c` gives

```text
∫_(k,∞) ρ_i = ∫_(c,∞) ρ_i − ∫_(c,a] ρ_i − ∫_(a,k] ρ_i ≤ ∫_(c,∞) ρ_i − ∫_(a,k] ρ_i ,
```

so the upper limit is at most `∫_(c,a] ρ + ∫_(k,∞) ρ` for every `a > c`, and letting `a` decrease to
`c` removes the first term; the lower limit is at least `∫_(k,b] ρ` for every `b`, and letting `b`
grow removes the deficit.  This is "vague convergence plus convergence of masses gives weak
convergence", in the form the tail sets need.
-/

open MeasureTheory Set Filter

open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*} {l : Filter ι} {ρn : ι → ℝ → ℝ} {ρ : ℝ → ℝ} {c : ℝ}

/-- Splitting the half-line at two interior points. -/
theorem setIntegral_Ioi_split {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi c))
    {a k : ℝ} (hca : c ≤ a) (hak : a ≤ k) :
    ∫ x in Ioi c, f x
      = (∫ x in Ioc c a, f x) + (∫ x in Ioc a k, f x) + ∫ x in Ioi k, f x := by
  have hck : c ≤ k := le_trans hca hak
  have hcup1 : Ioc c k ∪ Ioi k = Ioi c := Ioc_union_Ioi_eq_Ioi hck
  have hcup2 : Ioc c a ∪ Ioc a k = Ioc c k := Ioc_union_Ioc_eq_Ioc hca hak
  have h1 : ∫ x in Ioi c, f x = (∫ x in Ioc c k, f x) + ∫ x in Ioi k, f x := by
    rw [← hcup1]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hf.mono_set (by rw [← hcup1]; exact subset_union_left))
      (hf.mono_set (by rw [← hcup1]; exact subset_union_right))
  have hdisj : Disjoint (Ioc c a) (Ioc a k) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx'.1 (not_lt.mpr hx.2)
  have h2 : ∫ x in Ioc c k, f x = (∫ x in Ioc c a, f x) + ∫ x in Ioc a k, f x := by
    rw [← hcup2]
    refine setIntegral_union hdisj measurableSet_Ioc ?_ ?_
    · exact hf.mono_set Ioc_subset_Ioi_self
    · exact hf.mono_set fun x hx => lt_of_le_of_lt hca hx.1
  rw [h1, h2]

/-- The mass near the left endpoint can be made small. -/
theorem exists_left_piece_small (hint : IntegrableOn ρ (Ioi c))
    {ε : ℝ} (hε : 0 < ε) {k : ℝ} (hk : c < k) :
    ∃ a : ℝ, c < a ∧ a < k ∧ ∫ x in Ioc c a, ρ x < ε := by
  classical
  have hunion : (⋃ n : ℕ, Ioi (c + 1 / ((n : ℝ) + 1))) = Ioi c := by
    ext x
    constructor
    · rintro ⟨s, ⟨n, rfl⟩, hx⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [mem_Ioi] at hx ⊢
      linarith
    · intro hx
      simp only [mem_Ioi] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < x - c by linarith)
      refine ⟨_, ⟨n, rfl⟩, ?_⟩
      simp only [mem_Ioi]
      linarith
  have hmono : Monotone fun n : ℕ => Ioi (c + 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    refine Ioi_subset_Ioi ?_
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
      linarith
    linarith
  have hintU : IntegrableOn ρ (⋃ n : ℕ, Ioi (c + 1 / ((n : ℝ) + 1))) := by
    rw [hunion]; exact hint
  have htend := tendsto_setIntegral_of_monotone (fun n => measurableSet_Ioi) hmono hintU
  rw [hunion] at htend
  have hsub : ∀ n : ℕ, ∫ x in Ioc c (c + 1 / ((n : ℝ) + 1)), ρ x
      = (∫ x in Ioi c, ρ x) - ∫ x in Ioi (c + 1 / ((n : ℝ) + 1)), ρ x := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hle : c ≤ c + 1 / ((n : ℝ) + 1) := by linarith
    have hcup : Ioc c (c + 1 / ((n : ℝ) + 1)) ∪ Ioi (c + 1 / ((n : ℝ) + 1)) = Ioi c :=
      Ioc_union_Ioi_eq_Ioi hle
    have hsplit : ∫ x in Ioi c, ρ x
        = (∫ x in Ioc c (c + 1 / ((n : ℝ) + 1)), ρ x)
          + ∫ x in Ioi (c + 1 / ((n : ℝ) + 1)), ρ x := by
      rw [← hcup]
      exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set (by rw [← hcup]; exact subset_union_left))
        (hint.mono_set (by rw [← hcup]; exact subset_union_right))
    linarith
  have hzero : Tendsto (fun n : ℕ => ∫ x in Ioc c (c + 1 / ((n : ℝ) + 1)), ρ x) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∫ x in Ioi c, ρ x) (f := (atTop : Filter ℕ))).sub htend
    rw [sub_self] at h
    exact h.congr fun n => (hsub n).symm
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0:ℝ) < k - c by linarith)
  obtain ⟨N, hNε, hNm⟩ :=
    ((hzero.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop m)).exists
  have hposN : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  refine ⟨c + 1 / ((N : ℝ) + 1), by linarith, ?_, hNε⟩
  have h1 : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hNm
    linarith
  linarith

/-- The tail is exhausted from the left. -/
theorem exists_right_piece_close (hint : IntegrableOn ρ (Ioi c))
    {ε : ℝ} (hε : 0 < ε) {k : ℝ} (hk : c < k) :
    ∃ b : ℝ, k < b ∧ (∫ x in Ioi k, ρ x) - ε < ∫ x in Ioc k b, ρ x := by
  classical
  have hunion : (⋃ n : ℕ, Ioc k (k + ((n : ℝ) + 1))) = Ioi k := by
    ext x
    constructor
    · rintro ⟨s, ⟨n, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      simp only [mem_Ioi] at hx
      obtain ⟨n, hn⟩ := exists_nat_gt (x - k)
      refine ⟨_, ⟨n, rfl⟩, ⟨hx, ?_⟩⟩
      have : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
      linarith
  have hmono : Monotone fun n : ℕ => Ioc k (k + ((n : ℝ) + 1)) := by
    intro m n hmn
    refine Ioc_subset_Ioc_right ?_
    have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    linarith
  have hintU : IntegrableOn ρ (⋃ n : ℕ, Ioc k (k + ((n : ℝ) + 1))) := by
    rw [hunion]
    exact hint.mono_set (Ioi_subset_Ioi hk.le)
  have htend := tendsto_setIntegral_of_monotone (fun n => measurableSet_Ioc) hmono hintU
  rw [hunion] at htend
  obtain ⟨N, hN⟩ := (htend.eventually (Metric.ball_mem_nhds _ hε)).exists
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  refine ⟨k + ((N : ℝ) + 1), by linarith, ?_⟩
  have hd := hN
  rw [Real.dist_eq, abs_lt] at hd
  linarith [hd.1]

/-- **Local convergence plus convergence of masses gives convergence of tails.** -/
theorem tendsto_setIntegral_Ioi_of_local_of_mass
    (hρn0 : ∀ i x, 0 ≤ ρn i x)
    (hintn : ∀ i, IntegrableOn (ρn i) (Ioi c)) (hint : IntegrableOn ρ (Ioi c))
    (hloc : ∀ α β : ℝ, c < α → α < β →
      Tendsto (fun i => ∫ x in Ioc α β, ρn i x) l (𝓝 (∫ x in Ioc α β, ρ x)))
    (hmass : Tendsto (fun i => ∫ x in Ioi c, ρn i x) l (𝓝 (∫ x in Ioi c, ρ x)))
    {k : ℝ} (hk : c < k) :
    Tendsto (fun i => ∫ x in Ioi k, ρn i x) l (𝓝 (∫ x in Ioi k, ρ x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨a, hca, hak, ha⟩ := exists_left_piece_small hint hε3 hk
  obtain ⟨b, hkb, hb⟩ := exists_right_piece_close hint hε3 hk
  filter_upwards [(hloc a k hca hak).eventually (Metric.ball_mem_nhds _ hε3),
    (hloc k b hk hkb).eventually (Metric.ball_mem_nhds _ hε3),
    hmass.eventually (Metric.ball_mem_nhds _ hε3)] with i h1 h2 h3
  rw [Real.dist_eq, abs_lt] at h1 h2 h3 ⊢
  have hsplitρ := setIntegral_Ioi_split hint hca.le hak.le
  have hsplitn := setIntegral_Ioi_split (hintn i) hca.le hak.le
  have hnn1 : (0 : ℝ) ≤ ∫ x in Ioc c a, ρn i x :=
    setIntegral_nonneg measurableSet_Ioc fun x _ => hρn0 i x
  have hlow : ∫ x in Ioc k b, ρn i x ≤ ∫ x in Ioi k, ρn i x := by
    refine setIntegral_mono_set ((hintn i).mono_set (Ioi_subset_Ioi hk.le))
      (Filter.Eventually.of_forall fun x => hρn0 i x)
      (Filter.Eventually.of_forall fun x hx => hx.1)
  constructor
  · linarith [h2.1, hb, hlow]
  · linarith [h1.1, h3.2, ha, hnn1, hsplitρ, hsplitn]

end GaloisForLFunctions.HTGeometry
