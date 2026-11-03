import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateHorizonAtTheFirstPrime

/-!
# The rational lattice of a window

The folds of a window act on its points by `u ↦ u + log n`, so a point `x` and the points `x + log r`,
`r` a positive rational, form an orbit on which the folds are multiplications by `n`. A finite set
`S ⊂ ℚ_{>0}` whose spread `log(max S/min S)` is shorter than the window can be realized by narrow
bumps at the points `x + log r`; the bumps are disjoint, and translating by `log n` moves the bump of `r`
onto the bump of `nr` and away from every other bump.

* **The rational lattice** (`exists_rationalLattice`): for every finite configuration `S ⊂ ℚ_{>0}` of
  spread `< A` and every `N`, there are a profile and a position such that for all amplitudes `y`,
  `ι_S(y) = Σ_{r∈S} y_r φ(· − x − log r)` is a window test and
  `∫ ι_S(y)(u) ι_S(y)(u + log n) du = ‖φ‖² Σ_{r, s ∈ S, s = nr} y_r y_s` for `1 ≤ n ≤ N`.
* **Hecke graph bound** (`exists_windowTest_eq_heckeForm`): every arithmetic window form
  `‖H‖² + Σ_{2≤n≤N} c_n ∫H(u)H(u + log n)` takes, on the rational lattice, the value
  `‖φ‖²(Σ_r y_r² + Σ_n c_n Σ_{s = nr} y_r y_s)`: the Hecke operator of `ℤ[ℚ_{>0}^×]` on the finite
  configuration. A negative graph form gives a negative window form.

The integers `m ≤ e^A` are one configuration (the atomic lattice, a star at each prime); the
second-stage path `{1, 3/2, 2, 3}` is another, and numerically the window horizons are the thresholds
of these rational Hecke graphs.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ MeasureTheory Set

variable {A : ℝ}

/-- The rational lattice map: amplitudes on `S` to bumps at `x + log r`. -/
def ratLattice (S : Finset ℚ) (x : ℝ) (φ : ContDiffBump (0 : ℝ)) (y : ℚ → ℝ) (u : ℝ) : ℝ :=
  ∑ r ∈ S, y r * φ (u - (x + Real.log r))

/-- A finite set of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_finset (T : Finset ℝ) (h : ∀ t ∈ T, 0 < t) :
    ∃ ε > 0, ∀ t ∈ T, ε ≤ t := by
  by_cases hT : T.Nonempty
  · exact ⟨T.min' hT, h _ (T.min'_mem hT), fun t ht => T.min'_le t ht⟩
  · exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hT⟩

/-- Off the multiplicative coincidences the positions are separated. -/
theorem log_sub_ne_zero {r s : ℚ} {n : ℕ} (hr : 0 < r) (hs : 0 < s) (hn : 1 ≤ n)
    (h : (s : ℝ) ≠ n * r) : Real.log s - Real.log r - Real.log n ≠ 0 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  intro h0
  apply h
  have : Real.log s = Real.log (n * r) := by rw [Real.log_mul hn'.ne' hr'.ne']; linarith
  exact Real.log_injOn_pos hs' (mul_pos hn' hr') this

/-- **The rational lattice of a window**: a finite configuration of spread `< A` is realized by
disjoint bumps whose translates by `log n` meet exactly along multiplication by `n`. -/
theorem exists_rationalLattice (S : Finset ℚ) (hpos : ∀ r ∈ S, 0 < r)
    (hspread : ∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) (N : ℕ) :
    ∃ (x : ℝ) (φ : ContDiffBump (0 : ℝ)), 0 < ∫ u, φ u ^ 2 ∧
      (∀ y, IsWindowTest A (ratLattice S x φ y)) ∧
      ∀ y, ∀ n ∈ Finset.Icc 1 N, ∫ u, ratLattice S x φ y u * ratLattice S x φ y (u + Real.log n) =
        (∫ u, φ u ^ 2) * ∑ r ∈ S, ∑ s ∈ S, if (s : ℝ) = n * r then y r * y s else 0 := by
  classical
  -- separation of the non-coincident positions
  set T : Finset ℝ := ((S ×ˢ S ×ˢ Finset.Icc 1 N).filter
    (fun t => (t.2.1 : ℝ) ≠ t.2.2 * t.1)).image
      (fun t => |Real.log t.2.1 - Real.log t.1 - Real.log t.2.2|)
  have hT : ∀ t ∈ T, 0 < t := by
    intro t ht
    obtain ⟨⟨r, s, n⟩, hmem, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hm, hne⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hr, hsn⟩ := Finset.mem_product.mp hm
    obtain ⟨hs, hn⟩ := Finset.mem_product.mp hsn
    exact abs_pos.mpr (log_sub_ne_zero (hpos r hr) (hpos s hs) (Finset.mem_Icc.mp hn).1 hne)
  obtain ⟨ε, hε, hεT⟩ := exists_pos_le_of_finset T hT
  -- room inside the window
  by_cases hSe : S.Nonempty
  swap
  · -- empty configuration: the zero test
    refine ⟨0, ⟨1, 2, one_pos, by norm_num⟩, ?_, fun y => ?_, fun y n _ => ?_⟩
    · rw [integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _)
        (_root_.RHTower.WeilMarkovPole.integrable_sq (ContDiffBump.continuous _)
          (ContDiffBump.hasCompactSupport _))]
      have : Function.support (fun u => (⟨1, 2, one_pos, by norm_num⟩ : ContDiffBump (0 : ℝ)) u ^ 2)
          = Metric.ball (0 : ℝ) 2 := by
        rw [← ContDiffBump.support_eq (⟨1, 2, one_pos, by norm_num⟩ : ContDiffBump (0 : ℝ))]
        ext u; simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero]
      rw [this, Real.volume_ball]; exact ENNReal.ofReal_pos.mpr (by norm_num)
    · have : ratLattice S 0 ⟨1, 2, one_pos, by norm_num⟩ y = fun _ => 0 := by
        funext u; simp [ratLattice, Finset.not_nonempty_iff_eq_empty.mp hSe]
      rw [this]; exact ⟨contDiff_const, fun _ _ => rfl⟩
    · simp [ratLattice, Finset.not_nonempty_iff_eq_empty.mp hSe]
  set m := S.min' hSe
  set M := S.max' hSe
  have hm : m ∈ S := S.min'_mem hSe
  have hM : M ∈ S := S.max'_mem hSe
  have hlog_le : ∀ r ∈ S, Real.log m ≤ Real.log r ∧ Real.log r ≤ Real.log M := fun r hr => by
    have h1 : m ≤ r := S.min'_le r hr
    have h2 : r ≤ M := S.le_max' r hr
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    constructor
    · exact Real.log_le_log hm0 (by exact_mod_cast h1)
    · exact Real.log_le_log (by exact_mod_cast hpos r hr) (by exact_mod_cast h2)
  have hgap : 0 < A - (Real.log M - Real.log m) := by linarith [hspread m hm M hM]
  set ρ := min (ε / 2) ((A - (Real.log M - Real.log m)) / 4) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρε : 2 * ρ ≤ ε := by have := min_le_left (ε / 2) ((A - (Real.log M - Real.log m)) / 4); linarith
  have hρA : 4 * ρ ≤ A - (Real.log M - Real.log m) := by
    have := min_le_right (ε / 2) ((A - (Real.log M - Real.log m)) / 4); linarith
  let φ : ContDiffBump (0 : ℝ) := ⟨ρ / 2, ρ, by linarith, by linarith⟩
  have hro : φ.rOut = ρ := rfl
  set x := -A + 2 * ρ - Real.log m
  have hsupp : ∀ v, φ v ≠ 0 → |v| < ρ := fun v hv => by
    have : v ∈ Function.support φ := hv
    rw [φ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, hro] at this
    exact this
  have iφ : Integrable fun u => φ u ^ 2 := _root_.RHTower.WeilMarkovPole.integrable_sq φ.continuous
    φ.hasCompactSupport
  have hI : 0 < ∫ u, φ u ^ 2 := by
    rw [integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _) iφ]
    have : Function.support (fun u => φ u ^ 2) = Metric.ball (0 : ℝ) ρ := by
      rw [← hro, ← φ.support_eq]
      ext u
      simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero]
    rw [this, Real.volume_ball]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  refine ⟨x, φ, hI, fun y => ?_, fun y n hn => ?_⟩
  · -- window test
    refine ⟨?_, fun v hv => ?_⟩
    · unfold ratLattice
      exact ContDiff.sum fun r _ => contDiff_const.mul (φ.contDiff.comp (contDiff_id.sub contDiff_const))
    · unfold ratLattice
      refine Finset.sum_eq_zero fun r hr => ?_
      have hz : φ (v - (x + Real.log r)) = 0 := by
        by_contra hne
        have := abs_lt.mp (hsupp _ hne)
        obtain ⟨h1, h2⟩ := hlog_le r hr
        rcases not_and_or.mp hv with hv | hv
        · push Not at hv; linarith [this.1, this.2]
        · push Not at hv; linarith [this.1, this.2]
      rw [hz, mul_zero]
  · -- the fold by `log n` meets exactly along `s = nr`
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcont : ∀ a : ℝ, Continuous fun u => φ (u - a) := fun a =>
      φ.continuous.comp (continuous_id.sub continuous_const)
    have hterm : ∀ r ∈ S, ∀ s ∈ S, ∫ u, y r * φ (u - (x + Real.log r)) *
        (y s * φ (u + Real.log n - (x + Real.log s))) =
        if (s : ℝ) = n * r then y r * y s * ∫ u, φ u ^ 2 else 0 := fun r hr s hs => by
      split_ifs with hsn
      · have hlog : Real.log s = Real.log n + Real.log r := by
          rw [hsn, Real.log_mul (by exact_mod_cast (by omega : n ≠ 0))
            (by exact_mod_cast (hpos r hr).ne')]
        have e : ∀ u, u + Real.log n - (x + Real.log s) = u - (x + Real.log r) := fun u => by
          rw [hlog]; ring
        simp_rw [e]
        rw [← integral_sub_right_eq_self (μ := volume) (fun u => φ u ^ 2) (x + Real.log r),
          ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
      · have hsep : ε ≤ |Real.log s - Real.log r - Real.log n| :=
          hεT _ (Finset.mem_image.mpr ⟨(r, s, n), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hr, Finset.mem_product.mpr ⟨hs, hn⟩⟩, hsn⟩, rfl⟩)
        have hz : ∀ u, φ (u - (x + Real.log r)) * φ (u + Real.log n - (x + Real.log s)) = 0 :=
          fun u => by
            by_contra hne
            have h1 := abs_lt.mp (hsupp _ (left_ne_zero_of_mul hne))
            have h2 := abs_lt.mp (hsupp _ (right_ne_zero_of_mul hne))
            have : |Real.log s - Real.log r - Real.log n| < 2 * ρ := by
              rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
            linarith
        have : (fun u => y r * φ (u - (x + Real.log r)) *
            (y s * φ (u + Real.log n - (x + Real.log s)))) = fun _ => 0 := by
          funext u
          rw [show y r * φ (u - (x + Real.log r)) * (y s * φ (u + Real.log n - (x + Real.log s))) =
            y r * y s * (φ (u - (x + Real.log r)) * φ (u + Real.log n - (x + Real.log s))) by ring,
            hz u, mul_zero]
        rw [this, integral_zero]
    have hint : ∀ r s : ℚ, Integrable fun u => y r * φ (u - (x + Real.log r)) *
        (y s * φ (u + Real.log n - (x + Real.log s))) := fun r s =>
      (((continuous_const.mul (hcont _)).mul (continuous_const.mul
        (φ.continuous.comp ((continuous_add_const _).sub continuous_const))))).integrable_of_hasCompactSupport
        ((φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (x + Real.log r))).mul_left.mul_right)
    have hexp : ∀ u, ratLattice S x φ y u * ratLattice S x φ y (u + Real.log n) =
        ∑ r ∈ S, ∑ s ∈ S, y r * φ (u - (x + Real.log r)) *
          (y s * φ (u + Real.log n - (x + Real.log s))) := fun u => by
      unfold ratLattice
      rw [Finset.sum_mul_sum]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ => hint r s]
    simp_rw [integral_finsetSum _ fun s _ => hint _ s]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hterm r hr s hs]
    split_ifs <;> ring

/-- **The Hecke graph bound**: on the rational lattice, an arithmetic window form takes the value of
the Hecke graph form of the configuration. -/
theorem exists_windowTest_eq_heckeForm (S : Finset ℚ) (hpos : ∀ r ∈ S, 0 < r)
    (hspread : ∀ r ∈ S, ∀ s ∈ S, Real.log s - Real.log r < A) (N : ℕ) (c : ℕ → ℝ) (y : ℚ → ℝ) :
    ∃ H, IsWindowTest A H ∧ ∃ I > 0,
      (∫ u, H u ^ 2) + ∑ n ∈ Finset.Icc 2 N, c n * ∫ u, H u * H (u + Real.log n) =
        I * ((∑ r ∈ S, y r ^ 2) + ∑ n ∈ Finset.Icc 2 N, c n *
          ∑ r ∈ S, ∑ s ∈ S, if (s : ℝ) = n * r then y r * y s else 0) := by
  obtain ⟨x, φ, hI, hH, hcorr⟩ := exists_rationalLattice S hpos hspread (max N 1)
  refine ⟨ratLattice S x φ y, hH y, ∫ u, φ u ^ 2, hI, ?_⟩
  have h1 := hcorr y 1 (Finset.mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩)
  have hsq : ∫ u, ratLattice S x φ y u ^ 2 = (∫ u, φ u ^ 2) * ∑ r ∈ S, y r ^ 2 := by
    have e : ∫ u, ratLattice S x φ y u ^ 2 =
        ∫ u, ratLattice S x φ y u * ratLattice S x φ y (u + Real.log (1 : ℕ)) :=
      integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])
    rw [e, h1]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.sum_eq_single_of_mem r hr fun s _ hs => by
      rw [if_neg]; intro h; apply hs; exact_mod_cast (by simpa using h)]
    simp [sq]
  have hsum : ∑ n ∈ Finset.Icc 2 N, c n *
      ∫ u, ratLattice S x φ y u * ratLattice S x φ y (u + Real.log n) =
      (∫ u, φ u ^ 2) * ∑ n ∈ Finset.Icc 2 N, c n *
        ∑ r ∈ S, ∑ s ∈ S, (if (s : ℝ) = n * r then y r * y s else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ∈ Finset.Icc 1 (max N 1) := by
      obtain ⟨a, b⟩ := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨by omega, le_max_of_le_left b⟩
    rw [hcorr y n hn']
    ring
  rw [hsq, hsum]
  ring

end GaloisForLFunctions.WindowTowerOfSpecZ
