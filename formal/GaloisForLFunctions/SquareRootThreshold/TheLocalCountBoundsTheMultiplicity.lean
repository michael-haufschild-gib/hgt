import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount

/-!
# The local count bounds the multiplicity

The disc `|ρ − (½ + δ + it)| ≤ δ` of the local count touches the critical line only at `½ + it`.
A critical zero `½ + iγ` lies in this disc at `t = γ` for every `δ`, so the local count with
constant `C` forces multiplicity `≤ C` (`mult_le_of_localCountBound`, `δ → 0`).  Bounded
multiplicity of critical zeros is not known even under the Riemann hypothesis.

**Falsifier** (`exists_zeroConfig_rvm_rh_not_localCountBound`).  Superposing on the zeros of `ζ` the
critical clusters `½ + i exp(eᵏ)` of multiplicity `⌊log γ⌋ = ⌊eᵏ⌋` (`criticalClusterConfig`) keeps
Riemann–von Mangoldt, adds no off-line zero (the off-line counts `N − N₀` are those of `ζ`, and the
configuration is critical whenever `ζ` is), changes every window count by `≤ 4 log(|T₂| + 3)`, and
violates the local count for every constant.  So the local count does not follow from the Riemann
hypothesis together with counting inputs: at the tangency point it is a multiplicity statement.

**The off-line local bound forces a critical proportion one**
(`tendsto_N0_div_N_of_offLineLocallyBounded`).  If every window `(S − 1, S + 1]` holds at most `M`
off-line zeros, then `N(T, 2T) − N₀(T, 2T) ≤ M(T/2 + 1)` while Riemann–von Mangoldt gives
`N(T, 2T) ≍ T log T`, so `N₀(T, 2T)/N(T, 2T) → 1`: the input of the lag family implies that almost
all zeros are critical.

**The depth mass** (`not_offLineDepthLocallyBounded_superpose`).  The clusters of
`CountingInputsDoNotBoundTheLocalCount` also violate every bound `Σ m (Re ρ − ½)²` over the windows
`(S − 1, S + 1]`: a cluster carries `2⌊eᵏ⌋/(k + 3)² → ∞`.  So the depth-weighted local input does not
follow from counting either.
-/

open Complex Set Zeta23 Filter Topology

namespace RHTower.LocalCountFalsifier

noncomputable section

open Classical

/-! ## The local count bounds the multiplicity -/

/-- **The local count bounds critical multiplicities.**  If the local count holds with constant `C`,
every critical zero above height `3` has multiplicity at most `C`. -/
theorem mult_le_of_localCountBound {Z : ZeroConfig} {C : ℝ} (h : LocalCountBound Z C) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) (hre : ρ.re = 1 / 2) (him : 3 ≤ ρ.im) : (Z.mult ρ : ℝ) ≤ C := by
  have hdisc : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → (Z.mult ρ : ℝ) ≤ C * (δ * Real.log ρ.im + 1) := by
    intro δ hδ0 hδ
    have hmem : ρ ∈ Metric.closedBall (((1 / 2 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I) δ := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : ρ - (((1 / 2 + δ : ℝ) : ℂ) + (ρ.im : ℂ) * I) = ((-δ : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hre]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδ0]
    have h1 := mult_le_discCount Z hδ hρ hmem
    exact le_trans (by exact_mod_cast h1) (h δ ρ.im hδ0 hδ him)
  by_contra hlt
  push Not at hlt
  have hL : 0 < Real.log ρ.im := Real.log_pos (by linarith)
  set ε := (Z.mult ρ : ℝ) - C with hε
  have hε0 : 0 < ε := by linarith
  set δ := min (1 / 2) (ε / (2 * (|C| * Real.log ρ.im + 1))) with hδ
  have hD : 0 < 2 * (|C| * Real.log ρ.im + 1) := by positivity
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos hε0 hD)
  have hδ1 : δ ≤ ε / (2 * (|C| * Real.log ρ.im + 1)) := min_le_right _ _
  have key : |C| * (δ * Real.log ρ.im) < ε := by
    have h2 : δ * (2 * (|C| * Real.log ρ.im + 1)) ≤ ε := by rwa [le_div_iff₀ hD] at hδ1
    nlinarith [abs_nonneg C, mul_nonneg (abs_nonneg C) hL.le]
  have h3 := hdisc δ hδ0 (min_le_left _ _)
  have h4 : C * (δ * Real.log ρ.im) ≤ |C| * (δ * Real.log ρ.im) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  nlinarith

/-! ## Critical clusters -/

/-- `½ + i exp(eᵏ)`. -/
def criticalPoint (k : ℕ) : ℂ := ⟨1 / 2, Real.exp (Real.exp k)⟩

theorem criticalPoint_re (k : ℕ) : (criticalPoint k).re = 1 / 2 := rfl

theorem criticalPoint_im (k : ℕ) : (criticalPoint k).im = Real.exp (Real.exp k) := rfl

/-- **The critical clusters.**  At each height `exp(eᵏ)` the critical point of multiplicity
`⌊log γ⌋ = ⌊eᵏ⌋`. -/
def criticalClusterConfig : ZeroConfig where
  carrier := Set.range criticalPoint
  mult := fun ρ => ⌊Real.log ρ.im⌋₊
  one_le_mult := by
    rintro _ ⟨k, rfl⟩
    rw [criticalPoint_im, Real.log_exp]
    exact Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_exp (Nat.cast_nonneg k))
  strip := by
    rintro _ ⟨k, rfl⟩
    rw [criticalPoint_re]; constructor <;> norm_num
  reflect_mem := by
    rintro _ ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    apply Complex.ext <;> simp [reflect, criticalPoint]
    norm_num
  mult_reflect := fun ρ _ => by simp [reflect]
  finite_window := by
    intro T₁ T₂
    have hF : (Finset.range ⌈T₂⌉₊ : Set ℕ).Finite := Finset.finite_toSet _
    refine (hF.image criticalPoint).subset ?_
    rintro _ ⟨⟨k, rfl⟩, -, h2⟩
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_ceil.mpr (by rw [criticalPoint_im] at h2; linarith [le_exp_exp k])

theorem criticalClusterConfig_mult (k : ℕ) :
    criticalClusterConfig.mult (criticalPoint k) = ⌊Real.exp k⌋₊ := by
  show ⌊Real.log (criticalPoint k).im⌋₊ = _
  rw [criticalPoint_im, Real.log_exp]

/-- **The critical clusters are sparse.**  `N(T₁, T₂) ≤ 4 log(|T₂| + 3)`. -/
theorem criticalClusterConfig_N_le (T₁ T₂ : ℝ) :
    (criticalClusterConfig.N T₁ T₂ : ℝ) ≤ 4 * Real.log (|T₂| + 3) := by
  have hlog0 : 0 ≤ Real.log (|T₂| + 3) := Real.log_nonneg (by linarith [abs_nonneg T₂])
  rcases (criticalClusterConfig.window T₁ T₂).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have : criticalClusterConfig.N T₁ T₂ = 0 := by
      simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [this, Nat.cast_zero]; positivity
  have hT₂ : Real.exp 1 ≤ T₂ := by
    obtain ⟨⟨k, rfl⟩, -, h2⟩ := hρ₀
    rw [criticalPoint_im] at h2
    exact le_trans (Real.exp_le_exp.mpr (Real.one_le_exp (Nat.cast_nonneg k))) h2
  have hT₂0 : 0 < T₂ := lt_of_lt_of_le (Real.exp_pos 1) hT₂
  have hL1 : 1 ≤ Real.log T₂ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hT₂
  set n : ℕ := ⌊Real.log (Real.log T₂)⌋₊ + 1 with hn
  set S : Finset ℂ := (Finset.range n).image criticalPoint with hS
  have hfin := criticalClusterConfig.finite_window T₁ T₂
  have hsub : hfin.toFinset ⊆ S := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨k, rfl⟩, -, h2⟩ := hρ
    rw [criticalPoint_im] at h2
    refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
    have h1 : Real.exp k ≤ Real.log T₂ := by
      rw [← Real.log_exp (Real.exp k)]; exact Real.log_le_log (Real.exp_pos _) h2
    have h3 : (k : ℝ) ≤ Real.log (Real.log T₂) := by
      rw [← Real.log_exp k]; exact Real.log_le_log (Real.exp_pos _) h1
    rw [Finset.mem_range, hn]
    have := Nat.le_floor h3
    omega
  have hN : criticalClusterConfig.N T₁ T₂ ≤ ∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ := by
    calc criticalClusterConfig.N T₁ T₂ = ∑ ρ ∈ hfin.toFinset, criticalClusterConfig.mult ρ :=
          finsum_mem_eq_finite_toFinset_sum _ hfin
      _ ≤ ∑ ρ ∈ S, criticalClusterConfig.mult ρ := Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ k ∈ Finset.range n, criticalClusterConfig.mult (criticalPoint k) :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ = ∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ :=
          Finset.sum_congr rfl fun k _ => criticalClusterConfig_mult k
  have hcast : ((∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.range n, Real.exp k := by
    push_cast
    exact Finset.sum_le_sum fun k _ => Nat.floor_le (Real.exp_pos (k : ℝ)).le
  have hexpn : Real.exp n ≤ Real.exp 1 * Real.log T₂ := by
    have hfl : (⌊Real.log (Real.log T₂)⌋₊ : ℝ) ≤ Real.log (Real.log T₂) :=
      Nat.floor_le (Real.log_nonneg hL1)
    have : Real.exp (⌊Real.log (Real.log T₂)⌋₊ : ℝ) ≤ Real.log T₂ := by
      calc _ ≤ Real.exp (Real.log (Real.log T₂)) := Real.exp_le_exp.mpr hfl
        _ = Real.log T₂ := Real.exp_log (by linarith)
    rw [hn, Nat.cast_add, Nat.cast_one, Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos 1).le
  have hlogT : Real.log T₂ ≤ Real.log (|T₂| + 3) :=
    Real.log_le_log hT₂0 (by rw [abs_of_pos hT₂0]; linarith)
  have he := Real.exp_pos 1
  calc (criticalClusterConfig.N T₁ T₂ : ℝ)
      ≤ ((∑ k ∈ Finset.range n, ⌊Real.exp k⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN
    _ ≤ 2 * Real.exp n / Real.exp 1 := hcast.trans (sum_range_exp_le n)
    _ ≤ 2 * Real.log T₂ := by rw [div_le_iff₀ he]; nlinarith
    _ ≤ 4 * Real.log (|T₂| + 3) := by linarith

/-- The critical clusters are on the line: their critical count is their count. -/
theorem criticalClusterConfig_N0 (T₁ T₂ : ℝ) :
    criticalClusterConfig.N0 T₁ T₂ = criticalClusterConfig.N T₁ T₂ := by
  have hS : criticalClusterConfig.window T₁ T₂ ∩ ZeroConfig.onLine
      = criticalClusterConfig.window T₁ T₂ := by
    refine Set.inter_eq_left.mpr ?_
    rintro _ ⟨⟨k, rfl⟩, -⟩
    exact criticalPoint_re k
  unfold ZeroConfig.N0 ZeroConfig.N
  rw [hS]

/-! ## The falsifier -/

/-- **The local count is not implied by the Riemann hypothesis with counting.**  The zeros of `ζ`
with the critical clusters satisfy Riemann–von Mangoldt, have the off-line counts of `ζ` and are all
critical when those of `ζ` are, change every window count by at most `4 log(|T₂| + 3)`, and violate
the local count for every constant. -/
theorem exists_zeroConfig_rvm_rh_not_localCountBound :
    ∃ Z' : ZeroConfig, RiemannVonMangoldt Z' ∧
      ((∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) → ∀ ρ ∈ Z'.carrier, ρ.re = 1 / 2) ∧
      (∀ T₁ T₂ : ℝ, (Z'.N T₁ T₂ : ℤ) - Z'.N0 T₁ T₂
        = (zetaZeroConfig.N T₁ T₂ : ℤ) - zetaZeroConfig.N0 T₁ T₂) ∧
      (∀ T₁ T₂ : ℝ, zetaZeroConfig.N T₁ T₂ ≤ Z'.N T₁ T₂ ∧
        (Z'.N T₁ T₂ : ℝ) ≤ zetaZeroConfig.N T₁ T₂ + 4 * Real.log (|T₂| + 3)) ∧
      ∀ C : ℝ, ¬ LocalCountBound Z' C := by
  refine ⟨superpose zetaZeroConfig criticalClusterConfig,
    riemannVonMangoldt_superpose_of_N_le riemannVonMangoldt_zeta criticalClusterConfig_N_le,
    ?_, fun T₁ T₂ => ?_, fun T₁ T₂ => ?_, fun C hC => ?_⟩
  · rintro hRH ρ (h | ⟨k, rfl⟩)
    · exact hRH ρ h
    · exact criticalPoint_re k
  · rw [N_superpose, N0_superpose, criticalClusterConfig_N0]
    push_cast; ring
  · rw [N_superpose]
    refine ⟨Nat.le_add_right _ _, ?_⟩
    rw [Nat.cast_add]
    linarith [criticalClusterConfig_N_le T₁ T₂]
  · -- a cluster of multiplicity `⌊eᵏ⌋ > C`
    obtain ⟨k, hk⟩ := exists_nat_gt (|C| + 1)
    have hmem : criticalPoint k ∈ (superpose zetaZeroConfig criticalClusterConfig).carrier :=
      Or.inr ⟨k, rfl⟩
    have him : 3 ≤ (criticalPoint k).im := by
      rw [criticalPoint_im]
      have := le_exp_exp k
      linarith [abs_nonneg C]
    have hle := mult_le_of_localCountBound hC hmem (criticalPoint_re k) him
    have hge : ⌊Real.exp k⌋₊
        ≤ (superpose zetaZeroConfig criticalClusterConfig).mult (criticalPoint k) := by
      have hc : criticalPoint k ∈ criticalClusterConfig.carrier := ⟨k, rfl⟩
      show _ ≤ (if criticalPoint k ∈ zetaZeroConfig.carrier then
          zetaZeroConfig.mult (criticalPoint k) else 0)
        + (if criticalPoint k ∈ criticalClusterConfig.carrier then
          criticalClusterConfig.mult (criticalPoint k) else 0)
      rw [if_pos hc, criticalClusterConfig_mult]
      omega
    have hfl : Real.exp k - 1 < (⌊Real.exp k⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (Real.exp k); linarith
    have hek : (k : ℝ) + 1 ≤ Real.exp k := Real.add_one_le_exp _
    have hgeR : (⌊Real.exp k⌋₊ : ℝ) ≤ (superpose zetaZeroConfig criticalClusterConfig).mult
        (criticalPoint k) := by exact_mod_cast hge
    linarith [le_abs_self C]

/-! ## The off-line local bound forces a critical proportion one -/

/-- The off-line part of a zero configuration. -/
def offLinePart (Z : ZeroConfig) : ZeroConfig where
  carrier := Z.carrier ∩ {ρ | ρ.re ≠ 1 / 2}
  mult := Z.mult
  one_le_mult := fun ρ h => Z.one_le_mult ρ h.1
  strip := fun ρ h => Z.strip ρ h.1
  reflect_mem := by
    rintro ρ ⟨h1, h2⟩
    refine ⟨Z.reflect_mem ρ h1, ?_⟩
    show (reflect ρ).re ≠ 1 / 2
    have : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    rw [this]
    intro h; exact h2 (by linarith)
  mult_reflect := fun ρ h => Z.mult_reflect ρ h.1
  finite_window := fun T₁ T₂ =>
    (Z.finite_window T₁ T₂).subset fun ρ hρ => ⟨hρ.1.1, hρ.2⟩

/-- `N = N₀ + N_off`. -/
theorem N_eq_N0_add_offLinePart (Z : ZeroConfig) (T₁ T₂ : ℝ) :
    Z.N T₁ T₂ = Z.N0 T₁ T₂ + (offLinePart Z).N T₁ T₂ := by
  have hfin := Z.finite_window T₁ T₂
  have hsplit : Z.window T₁ T₂ = Z.window T₁ T₂ ∩ ZeroConfig.onLine ∪
      (offLinePart Z).window T₁ T₂ := by
    ext ρ
    simp only [ZeroConfig.window, offLinePart, ZeroConfig.onLine, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    tauto
  have hdisj : Disjoint (Z.window T₁ T₂ ∩ ZeroConfig.onLine) ((offLinePart Z).window T₁ T₂) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨-, h1⟩ ⟨⟨-, h2⟩, -⟩
    exact h2 h1
  calc Z.N T₁ T₂ = ∑ᶠ ρ ∈ Z.window T₁ T₂, Z.mult ρ := rfl
    _ = ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ ZeroConfig.onLine ∪ (offLinePart Z).window T₁ T₂, Z.mult ρ := by
        rw [← hsplit]
    _ = ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ ZeroConfig.onLine, Z.mult ρ
          + ∑ᶠ ρ ∈ (offLinePart Z).window T₁ T₂, Z.mult ρ :=
        finsum_mem_union hdisj (hfin.subset Set.inter_subset_left)
          ((offLinePart Z).finite_window T₁ T₂)
    _ = Z.N0 T₁ T₂ + (offLinePart Z).N T₁ T₂ := rfl

/-- The off-line windows of length `2` add up: `N_off(a, a + 2k) ≤ kM`. -/
theorem offLinePart_N_le {Z : ZeroConfig} {M : ℕ} (hM : OffLineLocallyBounded Z M) (a : ℝ) :
    ∀ k : ℕ, (offLinePart Z).N a (a + 2 * k) ≤ k * M
  | 0 => by
    simp only [Nat.cast_zero, mul_zero, add_zero, zero_mul, nonpos_iff_eq_zero]
    unfold ZeroConfig.N ZeroConfig.window
    refine finsum_mem_of_eqOn_zero fun ρ hρ => ?_
    exact absurd hρ.2.2 (not_le.mpr hρ.2.1)
  | k + 1 => by
    have h1 := offLinePart_N_le hM a k
    have hadd := Assembly.N_add (offLinePart Z) (a := a) (b := a + 2 * k) (c := a + 2 * ↑(k + 1))
      (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by push_cast; linarith)
    have h2 : (offLinePart Z).N (a + 2 * k) (a + 2 * ↑(k + 1)) ≤ M := by
      have := hM (a + 2 * k + 1)
      have e1 : a + 2 * k + 1 - 1 = a + 2 * k := by ring
      have e2 : a + 2 * k + 1 + 1 = a + 2 * ↑(k + 1) := by push_cast; ring
      rw [e1, e2] at this
      refine le_of_eq_of_le ?_ this
      unfold ZeroConfig.N ZeroConfig.window
      refine finsum_mem_congr ?_ fun _ _ => rfl
      ext ρ
      simp only [offLinePart, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    rw [hadd]
    nlinarith

/-- **The off-line local bound forces a critical proportion one.**  If every window `(S − 1, S + 1]`
holds at most `M` off-line zeros and Riemann–von Mangoldt holds, then `N₀(T, 2T)/N(T, 2T) → 1`. -/
theorem tendsto_N0_div_N_of_offLineLocallyBounded {Z : ZeroConfig} {M : ℕ}
    (hM : OffLineLocallyBounded Z M) (hZ : RiemannVonMangoldt Z) :
    Tendsto (fun T => (Z.N0 T (2 * T) : ℝ) / Z.N T (2 * T)) atTop (𝓝 1) := by
  obtain ⟨C, T₀, hC⟩ := hZ.main
  -- `N_off(T, 2T) ≤ M(T/2 + 1)`
  have hoff : ∀ T : ℝ, 0 ≤ T →
      ((offLinePart Z).N T (2 * T) : ℝ) ≤ M * (T / 2 + 1) := by
    intro T hT
    set k := ⌈T / 2⌉₊ with hk
    have hk1 : T / 2 ≤ k := Nat.le_ceil _
    have hk2 : (k : ℝ) < T / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
    have hmono : (offLinePart Z).N T (2 * T) ≤ (offLinePart Z).N T (T + 2 * k) := by
      rw [Assembly.N_add (offLinePart Z) (a := T) (b := 2 * T) (c := T + 2 * k) (by linarith)
        (by linarith)]
      exact Nat.le_add_right _ _
    have h := offLinePart_N_le hM T k
    have : ((offLinePart Z).N T (2 * T) : ℝ) ≤ k * M := by exact_mod_cast hmono.trans h
    nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  -- `N(T, 2T) ≥ (T/4π) log T` for large `T`
  have hlog : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hNlow : ∀ᶠ T in atTop, T / (4 * Real.pi) * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
    have hratio : Tendsto (fun T : ℝ => C * Real.log T / T) atTop (𝓝 0) := by
      have := (Real.isLittleO_log_id_atTop).tendsto_div_nhds_zero
      simpa [mul_div_assoc] using this.const_mul C
    filter_upwards [eventually_ge_atTop (max T₀ (2 * Real.pi * Real.exp 8)),
      hratio.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (8 * Real.pi) by positivity))]
      with T hT hr
    have hT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
    have hTe : 2 * Real.pi * Real.exp 8 ≤ T := le_trans (le_max_right _ _) hT
    have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hTe
    have h1 := (abs_le.mp (hC T hT₀)).1
    -- `ell1 T ≥ log T − 2 log(2π)` and `log(T/2π) ≥ 8`
    have hl : l T = Real.log T - Real.log (2 * Real.pi) := by
      rw [l, Real.log_div hT0.ne' (by positivity)]
    have hlT : 8 ≤ l T := by
      rw [l, ← Real.log_exp 8]
      exact Real.log_le_log (Real.exp_pos 8) (by rw [le_div_iff₀ (by positivity)]; linarith)
    have hell : Real.log T / 2 + 2 ≤ ell1 T := by
      have h2 : (0 : ℝ) ≤ 2 * Real.log 2 - 1 := by
        have := Real.log_two_gt_d9; linarith
      have hlog2π : Real.log (2 * Real.pi) ≤ 3 * Real.log 2 := by
        rw [show (3 : ℝ) * Real.log 2 = Real.log (2 ^ 3) by rw [Real.log_pow]; norm_num]
        exact Real.log_le_log (by positivity) (by nlinarith [Real.pi_lt_d2])
      have hlog2 := Real.log_two_gt_d9
      rw [ell1]
      linarith
    have hCl : C * Real.log T ≤ T / (8 * Real.pi) := by
      rw [div_lt_iff₀ hT0] at hr
      have e8 : 1 / (8 * Real.pi) * T = T / (8 * Real.pi) := by ring
      linarith
    have hmain : T / (2 * Real.pi) * ell1 T ≥ T / (2 * Real.pi) * (Real.log T / 2 + 2) :=
      mul_le_mul_of_nonneg_left hell (by positivity)
    have e : T / (2 * Real.pi) * (Real.log T / 2 + 2) = T / (4 * Real.pi) * Real.log T
        + T / Real.pi := by field_simp; ring
    have hTπ : T / (8 * Real.pi) ≤ T / Real.pi := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [Real.pi_pos]
    linarith
  -- squeeze `1 − M(T/2 + 1)/((T/4π) log T) ≤ N₀/N ≤ 1`
  have hupper : ∀ᶠ T in atTop, (Z.N0 T (2 * T) : ℝ) / Z.N T (2 * T) ≤ 1 := by
    filter_upwards [hNlow, eventually_gt_atTop (1 : ℝ)] with T hN hT
    have hNpos : 0 < (Z.N T (2 * T) : ℝ) :=
      lt_of_lt_of_le (by have := Real.log_pos hT; positivity) hN
    rw [div_le_one hNpos]
    have h := N_eq_N0_add_offLinePart Z T (2 * T)
    have hle : Z.N0 T (2 * T) ≤ Z.N T (2 * T) := by rw [h]; exact Nat.le_add_right _ _
    exact_mod_cast hle
  have hlower : ∀ᶠ T in atTop,
      1 - M * (T / 2 + 1) / (T / (4 * Real.pi) * Real.log T) ≤
        (Z.N0 T (2 * T) : ℝ) / Z.N T (2 * T) := by
    filter_upwards [hNlow, eventually_gt_atTop (1 : ℝ)] with T hN hT
    have hL := Real.log_pos hT
    have hD : 0 < T / (4 * Real.pi) * Real.log T := by positivity
    have hNpos : 0 < (Z.N T (2 * T) : ℝ) := lt_of_lt_of_le hD hN
    have hsplit : (Z.N0 T (2 * T) : ℝ) = Z.N T (2 * T) - (offLinePart Z).N T (2 * T) := by
      have := N_eq_N0_add_offLinePart Z T (2 * T)
      rw [this]; push_cast; ring
    rw [hsplit, sub_div, div_self hNpos.ne']
    have hO := hoff T (by linarith)
    have hO0 : (0 : ℝ) ≤ (offLinePart Z).N T (2 * T) := Nat.cast_nonneg _
    have : ((offLinePart Z).N T (2 * T) : ℝ) / Z.N T (2 * T)
        ≤ M * (T / 2 + 1) / (T / (4 * Real.pi) * Real.log T) :=
      div_le_div₀ (by positivity) hO hD hN
    linarith
  have hzero : Tendsto (fun T : ℝ => M * (T / 2 + 1) / (T / (4 * Real.pi) * Real.log T))
      atTop (𝓝 0) := by
    have hT : Tendsto (fun T : ℝ => (T / 2 + 1) / T) atTop (𝓝 (1 / 2)) := by
      have hinv0 : Tendsto (fun T : ℝ => 1 / T) atTop (𝓝 0) := by
        simpa only [one_div] using tendsto_inv_atTop_zero
      have h1 : Tendsto (fun T : ℝ => 1 / 2 + 1 / T) atTop (𝓝 (1 / 2 + 0)) :=
        tendsto_const_nhds.add hinv0
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
      field_simp
    have hinv := tendsto_inv_atTop_zero.comp hlog
    have h := (hT.mul hinv).const_mul (4 * Real.pi * M)
    rw [mul_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hL := Real.log_pos hT
    simp only [Function.comp]
    field_simp
  have hlim : Tendsto (fun T : ℝ => 1 - M * (T / 2 + 1) / (T / (4 * Real.pi) * Real.log T))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlower hupper

/-! ## The depth mass -/

/-- The off-line depth mass `Σ m (Re ρ − ½)²` of every window `(S − 1, S + 1]` is at most `W`. -/
def OffLineDepthLocallyBounded (Z : ZeroConfig) (W : ℝ) : Prop :=
  ∀ S : ℝ, ∑ᶠ ρ ∈ Z.window (S - 1) (S + 1), (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 ≤ W

/-- **The clusters violate every depth-mass bound.** -/
theorem not_offLineDepthLocallyBounded_superpose (Z : ZeroConfig) (W : ℝ) :
    ¬ OffLineDepthLocallyBounded (superpose Z clusterConfig) W := by
  intro h
  -- `⌊eᵏ⌋/(k + 3)² > W` for large `k`
  have hgrow : Tendsto (fun k : ℕ => (⌊Real.exp k⌋₊ : ℝ) / ((k : ℝ) + 3) ^ 2) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (Real.exp k - 1) / ((k : ℝ) + 3) ^ 2) atTop atTop := by
      have hexp : Tendsto (fun x : ℝ => Real.exp x / (x + 3) ^ 2) atTop atTop := by
        have := (Real.tendsto_exp_div_pow_atTop 2).comp (tendsto_atTop_add_const_right atTop 3
          tendsto_id)
        refine tendsto_atTop_mono' atTop ?_ ((this.const_mul_atTop (show (0 : ℝ) < Real.exp (-3)
          by positivity)))
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        simp only [Function.comp, id]
        rw [show Real.exp (x + 3) = Real.exp x * Real.exp 3 by rw [Real.exp_add]]
        have he3 : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; simp
        have hx3 : 0 < (x + 3) ^ 2 := by positivity
        rw [mul_div_assoc', mul_comm (Real.exp x), ← mul_assoc, he3, one_mul]
      have hsub : Tendsto (fun x : ℝ => (Real.exp x - 1) / (x + 3) ^ 2) atTop atTop := by
        refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-1) hexp)
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        have hx3 : 1 ≤ (x + 3) ^ 2 := by nlinarith
        rw [sub_div]
        have : 1 / (x + 3) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hx3
        linarith
      exact hsub.comp tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono (fun k => ?_) h1
    have := Nat.lt_floor_add_one (Real.exp k)
    have hk : 0 < ((k : ℝ) + 3) ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hk.le
  obtain ⟨k, hk⟩ := (hgrow.eventually_gt_atTop W).exists
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.exp (Real.exp k) := ⟨_, rfl⟩
  have hfin := (superpose Z clusterConfig).finite_window (T - 1) (T + 1)
  have hmem : clusterPoint 1 k ∈ (superpose Z clusterConfig).window (T - 1) (T + 1) := by
    refine ⟨Or.inr (Or.inl ⟨k, rfl⟩), ?_, ?_⟩
    · rw [clusterPoint_im, ← hT]; linarith
    · rw [clusterPoint_im, ← hT]; linarith
  have h1 := h T
  rw [show T + 1 = T + 1 from rfl] at h1
  have e1 : T - 1 = T - 1 := rfl
  unfold ZeroConfig.window at h1 hmem
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
  have h2 := Finset.single_le_sum (f := fun ρ => ((superpose Z clusterConfig).mult ρ : ℝ) *
      (ρ.re - 1 / 2) ^ 2) (fun ρ _ => by positivity) (hfin.mem_toFinset.mpr hmem)
  have h3 : (⌊Real.exp k⌋₊ : ℝ) ≤ (superpose Z clusterConfig).mult (clusterPoint 1 k) := by
    have hc : clusterPoint 1 k ∈ clusterConfig.carrier := Or.inl ⟨k, rfl⟩
    have : ⌊Real.exp k⌋₊ ≤ (superpose Z clusterConfig).mult (clusterPoint 1 k) := by
      show _ ≤ (if clusterPoint 1 k ∈ Z.carrier then Z.mult (clusterPoint 1 k) else 0)
        + (if clusterPoint 1 k ∈ clusterConfig.carrier then
          clusterConfig.mult (clusterPoint 1 k) else 0)
      rw [if_pos hc, clusterConfig_mult]
      omega
    exact_mod_cast this
  have hre : ((clusterPoint 1 k).re - 1 / 2) ^ 2 = 1 / ((k : ℝ) + 3) ^ 2 := by
    rw [clusterPoint_re]; ring
  have h4 : (⌊Real.exp k⌋₊ : ℝ) / ((k : ℝ) + 3) ^ 2 ≤
      ((superpose Z clusterConfig).mult (clusterPoint 1 k) : ℝ) * ((clusterPoint 1 k).re - 1 / 2) ^ 2 := by
    rw [hre, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right h3 (by positivity)
  linarith

end

end RHTower.LocalCountFalsifier
