import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTwistedDensityOfTheCarrierIsWeilsSymbol

/-!
# Sums over the degree points of a tail are Riemann sums

A tail at scale `N` has the degree points `1, …, N`; in the coordinate `t = n/N` they are the
points of mesh `1/N` in `(0, 1]`. A sum over the tail of a profile `f(n/N)`, per degree point, is
the Riemann sum `(1/N) Σ_{n ≤ N} f(n/N)` (`tailRiemannSum`).

`RiemannOn f`: `f` is integrable on `(0, 1]` and its Riemann sums tend to `∫_0^1 f`. The class is
closed under linear combinations and contains

* the bounded functions continuous on `(0, 1]` (`riemannOn_of_continuousOn_of_bounded`);
* the nonnegative antitone integrable functions on `(0, 1]`, which may be unbounded at `0`
  (`riemannOn_of_antitoneOn`), and their cuts at a point (`riemannOn_indicator_Iic`).

For an antitone profile the Riemann sum is at most the integral at every scale
(`tailRiemannSum_le_integral`): each term is at most the integral over the cell to its left.
-/

open Finset Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The Riemann sum of `f` at the points `n/N`, `1 ≤ n ≤ N`. -/
def tailRiemannSum (f : ℝ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) / N)) / N

/-- `f` is integrable on `(0, 1]` and its Riemann sums at the points `n/N` tend to its
integral. -/
def RiemannOn (f : ℝ → ℝ) : Prop :=
  IntegrableOn f (Set.Ioc 0 1) ∧
    Tendsto (fun N : ℕ => tailRiemannSum f N) atTop (𝓝 (∫ t in Set.Ioc 0 1, f t))

theorem sum_Icc_one_shift (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ k ∈ range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem natCast_div_mem_Ioc {n N : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    (n : ℝ) / N ∈ Set.Ioc (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (h1.trans h2)
  exact ⟨div_pos hn0 hN0, (div_le_one hN0).mpr (by exact_mod_cast h2)⟩

theorem tailRiemannSum_congr {f g : ℝ → ℝ} (h : ∀ t ∈ Set.Ioc (0 : ℝ) 1, f t = g t) (N : ℕ) :
    tailRiemannSum f N = tailRiemannSum g N := by
  unfold tailRiemannSum
  rw [Finset.sum_congr rfl fun n hn => h _ (natCast_div_mem_Ioc hn)]

/-! ### The class is a vector space -/

namespace RiemannOn

variable {f g : ℝ → ℝ}

theorem congr (hf : RiemannOn f) (h : ∀ t ∈ Set.Ioc (0 : ℝ) 1, f t = g t) : RiemannOn g := by
  refine ⟨hf.1.congr_fun (fun t ht => h t ht) measurableSet_Ioc, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioc (fun t ht => h t ht)]
  exact hf.2.congr fun N => tailRiemannSum_congr h N

theorem add (hf : RiemannOn f) (hg : RiemannOn g) : RiemannOn (fun t => f t + g t) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  rw [integral_add hf.1 hg.1]
  refine (hf.2.add hg.2).congr fun N => ?_
  simp only [tailRiemannSum, Finset.sum_add_distrib, add_div]

theorem const_mul (c : ℝ) (hf : RiemannOn f) : RiemannOn (fun t => c * f t) := by
  refine ⟨hf.1.const_mul c, ?_⟩
  rw [integral_const_mul]
  refine (hf.2.const_mul c).congr fun N => ?_
  rw [tailRiemannSum, tailRiemannSum, ← Finset.mul_sum, mul_div_assoc]

theorem sub (hf : RiemannOn f) (hg : RiemannOn g) : RiemannOn (fun t => f t - g t) :=
  (hf.add (hg.const_mul (-1))).congr fun t _ => by ring

end RiemannOn

theorem riemannOn_zero : RiemannOn (fun _ => 0) := by
  refine ⟨integrableOn_zero, ?_⟩
  have h : ∀ N : ℕ, tailRiemannSum (fun _ => 0) N = 0 := fun N => by simp [tailRiemannSum]
  simp only [h, integral_zero]
  exact tendsto_const_nhds

theorem riemannOn_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, RiemannOn (f i)) : RiemannOn (fun t => ∑ i ∈ s, f i t) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using riemannOn_zero
  · intro a s ha ih h
    have h1 := (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact h1.congr fun t _ => by rw [Finset.sum_insert ha]

/-! ### Bounded continuous profiles -/

/-- A bounded function continuous on `(0, 1]` has convergent Riemann sums. -/
theorem riemannOn_of_continuousOn_of_bounded {g : ℝ → ℝ} {B : ℝ}
    (hg : ContinuousOn g (Set.Ioc 0 1)) (hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, |g r| ≤ B) :
    RiemannOn g := by
  have hint : IntegrableOn g (Set.Ioc 0 1) := by
    refine Integrable.mono' (integrableOn_const (C := B) (by simp))
      (hg.aestronglyMeasurable measurableSet_Ioc) ?_
    exact (ae_restrict_mem measurableSet_Ioc).mono fun r hr => by
      rw [Real.norm_eq_abs]
      exact hB r hr
  refine ⟨hint, ?_⟩
  have h := tendsto_riemannSum_of_continuousOn_Ioc hg hB
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  refine h.congr fun N => ?_
  rw [tailRiemannSum, sum_Icc_one_shift, div_eq_inv_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.cast_succ]

/-! ### Antitone profiles -/

section Antitone

variable {h : ℝ → ℝ}

private theorem cell_subset {N k : ℕ} (hk : k < N) :
    Set.Ioc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) ⊆ Set.Ioc (0 : ℝ) 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  intro x hx
  refine ⟨lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg k) hN0.le) hx.1, hx.2.trans ?_⟩
  rw [div_le_one hN0]
  exact_mod_cast hk

private theorem cell_le (N k : ℕ) : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N :=
  div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (Nat.cast_nonneg N)

private theorem cell_width {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [Nat.cast_succ]
  field_simp
  ring

/-- **The Riemann sum of an antitone profile is at most its integral**, at every scale. -/
theorem tailRiemannSum_le_integral (hanti : AntitoneOn h (Set.Ioc 0 1))
    (hint : IntegrableOn h (Set.Ioc 0 1)) {N : ℕ} (hN : 1 ≤ N) :
    tailRiemannSum h N ≤ ∫ t in Set.Ioc 0 1, h t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hii : ∀ k < N, IntervalIntegrable h volume ((fun k : ℕ => (k : ℝ) / N) k)
      ((fun k : ℕ => (k : ℝ) / N) (k + 1)) := fun k hk =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (cell_le N k)).mpr
      (hint.mono_set (cell_subset hk))
  have hcell : ∀ k ∈ range N, h (((k + 1 : ℕ) : ℝ) / N) / N ≤
      ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, h x := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hconst : ∫ _x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, h (((k + 1 : ℕ) : ℝ) / N) =
        h (((k + 1 : ℕ) : ℝ) / N) / N := by
      rw [intervalIntegral.integral_const, smul_eq_mul, cell_width hN k]
      ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on_of_le_Ioo (cell_le N k) intervalIntegrable_const
      (hii k hk') fun x hx => ?_
    have hlt : (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N := hx.1.trans hx.2
    exact hanti (cell_subset hk' ⟨hx.1, hx.2.le⟩) (cell_subset hk' ⟨hlt, le_rfl⟩) hx.2.le
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hii
  have h0 : ((0 : ℕ) : ℝ) / N = 0 := by simp
  have h1 : (N : ℝ) / N = 1 := div_self hN0.ne'
  simp only [h0, h1] at hsum
  rw [intervalIntegral.integral_of_le zero_le_one] at hsum
  rw [← hsum, tailRiemannSum, sum_Icc_one_shift, Finset.sum_div]
  exact Finset.sum_le_sum hcell

/-- The Riemann sum of a nonnegative antitone profile is at least its integral over
`(1/N, 1]`. -/
theorem integral_le_tailRiemannSum (hanti : AntitoneOn h (Set.Ioc 0 1))
    (hnn : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ h t) (hint : IntegrableOn h (Set.Ioc 0 1)) {N : ℕ}
    (hN : 1 ≤ N) : ∫ t in (1 / (N : ℝ))..1, h t ≤ tailRiemannSum h N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hmem : ∀ k, k < M → Set.Ioc (((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ))
      (((k + 1 + 1 : ℕ) : ℝ) / (M + 1 : ℕ)) ⊆ Set.Ioc (0 : ℝ) 1 := fun k hk =>
    cell_subset (by omega : k + 1 < M + 1)
  have hii : ∀ k < M, IntervalIntegrable h volume
      ((fun k : ℕ => ((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)) k)
      ((fun k : ℕ => ((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)) (k + 1)) := fun k hk =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (cell_le (M + 1) (k + 1))).mpr
      (hint.mono_set (hmem k hk))
  have hcell : ∀ k ∈ range M, ∫ x in ((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)..
      ((k + 1 + 1 : ℕ) : ℝ) / (M + 1 : ℕ), h x ≤
        h (((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)) / (M + 1 : ℕ) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hconst : ∫ _x in ((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)..((k + 1 + 1 : ℕ) : ℝ) / (M + 1 : ℕ),
        h (((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)) = h (((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ)) / (M + 1 : ℕ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, cell_width hN (k + 1)]
      ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on_of_le_Ioo (cell_le (M + 1) (k + 1)) (hii k hk')
      intervalIntegrable_const fun x hx => ?_
    have hleft : ((k + 1 : ℕ) : ℝ) / (M + 1 : ℕ) ∈ Set.Ioc (0 : ℝ) 1 :=
      natCast_div_mem_Ioc (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact hanti hleft (hmem k hk' ⟨hx.1, hx.2.le⟩) hx.1.le
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hii
  have h0 : (((0 + 1 : ℕ) : ℝ)) / (M + 1 : ℕ) = 1 / ((M + 1 : ℕ) : ℝ) := by simp
  have h1 : ((M + 1 : ℕ) : ℝ) / (M + 1 : ℕ) = 1 := div_self hN0.ne'
  simp only [h0, h1] at hsum
  rw [← hsum, tailRiemannSum, sum_Icc_one_shift, Finset.sum_div, Finset.sum_range_succ]
  refine (Finset.sum_le_sum hcell).trans (le_add_of_nonneg_right ?_)
  exact div_nonneg (hnn _ (natCast_div_mem_Ioc (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)))
    hN0.le

/-- **A nonnegative antitone integrable profile on `(0, 1]` has convergent Riemann sums**; it may
be unbounded at `0`. -/
theorem riemannOn_of_antitoneOn (hanti : AntitoneOn h (Set.Ioc 0 1))
    (hnn : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ h t) (hint : IntegrableOn h (Set.Ioc 0 1)) :
    RiemannOn h := by
  refine ⟨hint, ?_⟩
  have hii : IntervalIntegrable h volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint
  -- the integral over `(1/N, 1]` tends to the integral over `(0, 1]`
  have hcont := intervalIntegral.continuousOn_primitive_interval' hii
    (a := 1) Set.right_mem_uIcc
  have hto : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝[Set.uIcc (0 : ℝ) 1] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Set.uIcc_of_le zero_le_one]
    exact ⟨by positivity, by rw [div_le_one (by positivity)]; exact hN1⟩
  have hprim := (hcont 0 Set.left_mem_uIcc).tendsto.comp hto
  have hprim' : Tendsto (fun N : ℕ => ∫ t in (1 / (N : ℝ))..1, h t) atTop
      (𝓝 (∫ t in Set.Ioc 0 1, h t)) := by
    have hneg := hprim.neg
    rw [← intervalIntegral.integral_symm, intervalIntegral.integral_of_le zero_le_one] at hneg
    refine hneg.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← intervalIntegral.integral_symm]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hprim' tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact integral_le_tailRiemannSum hanti hnn hint hN
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact tailRiemannSum_le_integral hanti hint hN

/-- A cut of a nonnegative antitone integrable profile at a point is again antitone. -/
theorem riemannOn_indicator_Iic (hanti : AntitoneOn h (Set.Ioc 0 1))
    (hnn : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ h t) (hint : IntegrableOn h (Set.Ioc 0 1)) (c : ℝ) :
    RiemannOn ((Set.Iic c).indicator h) := by
  refine riemannOn_of_antitoneOn ?_ ?_ (hint.indicator measurableSet_Iic)
  · intro s hs t ht hst
    by_cases htc : t ≤ c
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr htc),
        Set.indicator_of_mem (Set.mem_Iic.mpr (hst.trans htc))]
      exact hanti hs ht hst
    · rw [Set.indicator_of_notMem (by simpa using htc)]
      by_cases hsc : s ≤ c
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hsc)]
        exact hnn s hs
      · exact (Set.indicator_of_notMem (by simpa using hsc) h).ge
  · intro t ht
    by_cases htc : t ≤ c
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr htc)]
      exact hnn t ht
    · exact (Set.indicator_of_notMem (by simpa using htc) h).ge

end Antitone

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
