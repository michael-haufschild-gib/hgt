import Zeta23.ThmE.LocalCountChi
import Zeta23.Tail

/-!
# A conductor-uniform local zero count for primitive Dirichlet `L`-functions

**Theorem** (`exists_uniform_localCount`).  There is an absolute constant `A₀ ≥ 1` such that for
every modulus `q > 1`, every primitive character `χ` modulo `q` and every real `t`,

`N_χ(t, t + 1] ≤ A₀ · log(q (|t| + 3))`,

where `N_χ(t, t + 1]` counts the nontrivial zeros of `L(s, χ)` with ordinate in `(t, t + 1]`, with
multiplicity.

**Corollaries.**  `uniform_localCount_log`: the same count is at most `A₀ (1 + log q) log(|t| + 3)`, the
form consumed by Alpöge–Furman's tail estimates; `uniform_NII_le`: for `T ≥ 300` the number of zeros of
`L(s, χ)` with ordinate in `(T − √T, T] ∪ (2T, 2T + √T]` is at most `3 A₀ (1 + log q) √T log(4T)`.

The proof is the Jensen argument of `Zeta23.ThmE.localCountChi`: by the functional equation half of
the zeros in the window have `Re ρ ≥ ½`; these lie in the disc of radius `0.84 · 1.9` about
`c₀ = 2 + (t + ½) i`, where `|L(c₀, χ)| ≥ 1/3`.  The only change is the growth input on the larger
disc of radius `0.95 · 1.9`, which stays in `Re s ≥ 0.195`: there the conductor-uniform bound
`‖L(s, χ)‖ ≤ 8 q (|Im s| + 3)` (`Zeta23.ThmE.LFunction_growth_right_uniform`) replaces the
character-dependent polynomial bound.  Jensen's formula with radii `0.84 < 0.95` then gives
`N ≤ 2 log(24 q (|t| + 6)) / log(0.95/0.84)`.
-/

open Complex Set DirichletCharacter

noncomputable section

namespace RHTower

open Zeta23 Zeta23.ThmE

/-- `log(24 q (|t| + 6)) ≤ (log 24 + 2) · log(q (|t| + 3))` for every modulus `q ≥ 1`. -/
lemma log_uniform_disc_bound {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    Real.log (24 * q * (|t| + 6)) ≤ (Real.log 24 + 2) * Real.log (q * (|t| + 3)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : 0 ≤ |t| := abs_nonneg t
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hlog6 : Real.log (|t| + 6) ≤ 2 * Real.log (|t| + 3) := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hsplit : Real.log (24 * q * (|t| + 6))
      = Real.log 24 + Real.log q + Real.log (|t| + 6) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
  have hsplit' : Real.log (q * (|t| + 3)) = Real.log q + Real.log (|t| + 3) :=
    Real.log_mul (by positivity) (by positivity)
  have hlog24 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  rw [hsplit, hsplit']
  nlinarith

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- On the disc of radius `0.95` the rescaled function `w ↦ L(c₀ + 1.9 w, χ) u`, with
`c₀ = 2 + (t + ½) i` and `‖u‖ ≤ 3`, is at most `24 q (|t| + 6)`. -/
lemma norm_gfunL_le_uniform (hχ1 : χ ≠ 1) (t : ℝ) {u : ℂ} (hu : ‖u‖ ≤ 3) {z : ℂ}
    (hz : ‖z‖ ≤ 0.95) :
    ‖gfunL χ (2 + (t + 1/2 : ℝ) * I) ((19/10 : ℝ) : ℂ) u z‖ ≤ 24 * q * (|t| + 6) := by
  set s : ℂ := 2 + (t + 1/2 : ℝ) * I + ((19/10 : ℝ) : ℂ) * z with hs
  have hzre := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have hzim := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have hsre : s.re = 2 + 1.9 * z.re := by
    rw [hs]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat]
    ring
  have hsim : s.im = (t + 1/2) + 1.9 * z.im := by
    rw [hs]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.im_ofNat]
    ring
  have h1 : (0.15 : ℝ) ≤ s.re := by rw [hsre]; nlinarith
  have hgrowth := LFunction_growth_right_uniform hχ1 h1
  have hbase : |s.im| + 3 ≤ |t| + 6 := by
    rw [hsim]
    have h4 := abs_add_le (t + 1/2) (1.9 * z.im)
    have h5 : |1.9 * z.im| ≤ 1.9 * 0.95 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]
      nlinarith [abs_le.mpr ⟨hzim.1, hzim.2⟩]
    have h6 : |t + 1/2| ≤ |t| + 1/2 := by simpa using abs_add_le t (1/2)
    linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc ‖gfunL χ (2 + (t + 1/2 : ℝ) * I) ((19/10 : ℝ) : ℂ) u z‖
      = ‖χ.LFunction s‖ * ‖u‖ := by rw [gfunL, hs]; exact norm_mul _ _
    _ ≤ (8 * q * (|t| + 6)) * 3 := by
        apply mul_le_mul _ hu (norm_nonneg _) (by positivity)
        exact hgrowth.trans (mul_le_mul_of_nonneg_left hbase (by positivity))
    _ = 24 * q * (|t| + 6) := by ring

/-- **Conductor-uniform local zero count.**  For every modulus `q > 1`, every primitive `χ` modulo
`q` and every real `t`, `N_χ(t, t + 1] ≤ A₀ log(q (|t| + 3))` with
`A₀ = 2 (log 24 + 2) / log(0.95/0.84)`, independent of `q`, `χ` and `t`. -/
theorem uniform_localCount (hq : 1 < q) (hprim : χ.IsPrimitive) (t : ℝ) :
    (NcountL χ t (t + 1) : ℝ) ≤
      2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * Real.log (q * (|t| + 3)) := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  have hs : LSeam χ := LSeam_of hq hprim
  set r : ℝ := 0.84 with hr
  set R : ℝ := 0.95 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  have hhalf : (NcountL χ t (t + 1) : ℝ) ≤
      2 * ∑ᶠ ρ ∈ (LZeros hs).window t (t + 1) ∩ {ρ : ℂ | 1/2 ≤ ρ.re}, ((LZeros hs).mult ρ : ℝ) := by
    have := (LZeros hs).N_le_two_mul_half t (t + 1)
    rwa [LZeros_N] at this
  set c₀ : ℂ := 2 + (t + 1/2 : ℝ) * I with hc₀
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  have hLc₀ : (1/3 : ℝ) ≤ ‖χ.LFunction c₀‖ := LFunction_lower_bound_two (by simp [hc₀])
  have hLc₀ne : χ.LFunction c₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hLc₀; norm_num at hLc₀
  set u : ℂ := (χ.LFunction c₀)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hLc₀ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  set G : ℂ → ℂ := gfunL χ c₀ κ u with hG
  have hfAnalytic : AnalyticOnNhd ℂ G (Metric.closedBall (0:ℂ) 1) :=
    fun z _ => gfunL_analyticAt hχ1 c₀ κ u z
  have hG0 : G 0 = 1 := by
    simp only [hG, gfunL, mul_zero, add_zero, hu]
    exact mul_inv_cancel₀ hLc₀ne
  have hfin : (SetOfZeros 1 G).Finite := by
    have h := RvM.finite_zeros_closedBall (f := G) (R := 1.05) (r := 1) (by norm_num)
      (fun z _ => gfunL_analyticAt hχ1 c₀ κ u z) (z₀ := 0) (by simp; norm_num)
      (by rw [hG0]; exact one_ne_zero)
    exact h.subset (by intro z hz; exact hz)
  set B : ℝ := 24 * q * (|t| + 6) with hB
  have hfz : ∀ z : ℂ, ‖z‖ ≤ R → ‖G z‖ ≤ B := fun z hz =>
    norm_gfunL_le_uniform hχ1 t hnu (by simpa [hR] using hz)
  have hrlt1 : r < 1 := by norm_num [hr]
  have hZ := ZerosBound (B := B) (r := r) (R := R) (by norm_num [hr]) hrlt1
    (by norm_num [hr, hR]) (by norm_num [hR]) hfAnalytic hG0 hfin hfz
  set Z : Finset ℂ := (finiteSetOfZeros_mono hrlt1 hfin).toFinset with hZdef
  set W : Set ℂ := (LZeros hs).window t (t + 1) ∩ {ρ : ℂ | 1/2 ≤ ρ.re} with hW
  have hWfin : W.Finite := ((LZeros hs).window_finite t (t + 1)).subset inter_subset_left
  set φ : ℂ → ℂ := fun ρ => (ρ - c₀) / κ with hφ
  have hφinj : Function.Injective φ := by
    intro a b h; simp only [hφ] at h
    have := congrArg (fun w => c₀ + κ * w) h
    simpa [mul_div_cancel₀ _ hκ0] using this
  have hφinv : ∀ ρ, c₀ + κ * φ ρ = ρ := by intro ρ; simp only [hφ]; field_simp; ring
  have hmemS : ∀ ρ ∈ W, φ ρ ∈ Z := by
    rintro ρ ⟨⟨hρZ, hρt, hρt1⟩, hρre⟩
    have hρ : IsNontrivialZeroL χ ρ := by rwa [LZeros_carrier] at hρZ
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · show ‖φ ρ‖ ≤ r
      simp only [hφ, norm_div, hnormκ]
      rw [div_le_iff₀ (by norm_num), hr]
      have hre : (ρ - c₀).re = ρ.re - 2 := by simp [hc₀]
      have him : (ρ - c₀).im = ρ.im - (t + 1/2) := by simp [hc₀]
      have hsq : ‖ρ - c₀‖ ^ 2 ≤ (0.84 * 1.9) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        have := hρ.2.2; have := hρre.out
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hsq
    · show G (φ ρ) = 0
      simp only [hG, gfunL, hφinv]
      rw [hρ.1, zero_mul]
  have hmult : ∀ ρ ∈ W, ((LZeros hs).mult ρ : ℝ) = (analyticOrderNatAt G (φ ρ) : ℝ) := by
    rintro ρ ⟨⟨hρZ, -, -⟩, -⟩
    rw [LZeros_mult, hG, analyticOrderNatAt_gfunL hχ1 hκ0 hu0, hφinv]
  have hsum : (∑ᶠ ρ ∈ W, ((LZeros hs).mult ρ : ℝ)) ≤
      ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ)),
      ← Finset.sum_image (f := fun w => (analyticOrderNatAt G w : ℝ))
        (fun a _ b _ h => hφinj h)]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      exact hmemS ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  have hlogB := log_uniform_disc_bound (q := q) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) t
  have hZ' : ((∑ ρ' ∈ Z, analyticOrderNatAt G ρ' : ℕ) : ℝ) ≤
      1 / Real.log (R / r) * Real.log B := by exact_mod_cast hZ
  have hstep : 1 / Real.log (R / r) * Real.log B ≤
      1 / Real.log (R / r) * ((Real.log 24 + 2) * Real.log (q * (|t| + 3))) :=
    mul_le_mul_of_nonneg_left (by simpa [hB] using hlogB) (by positivity)
  calc (NcountL χ t (t + 1) : ℝ)
      ≤ 2 * ∑ᶠ ρ ∈ W, ((LZeros hs).mult ρ : ℝ) := hhalf
    _ ≤ 2 * (1 / Real.log (R / r) * ((Real.log 24 + 2) * Real.log (q * (|t| + 3)))) := by
        linarith [hsum]
    _ = 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * Real.log (q * (|t| + 3)) := by
        rw [hr, hR]; ring

/-- **Conductor-uniform local zero count**, existential form: one absolute constant serves every
modulus `q > 1`, every primitive character modulo `q` and every height `t`. -/
theorem exists_uniform_localCount :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
      ∀ t : ℝ, (NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)) := by
  refine ⟨2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84), ?_, fun q _ χ hq hprim t =>
    uniform_localCount hq hprim t⟩
  have h1 : 0 < Real.log (0.95 / 0.84) := Real.log_pos (by norm_num)
  have h2 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  positivity

/-- The uniform constant `A₀ = 2 (log 24 + 2) / log(0.95/0.84)` is at least `1`. -/
lemma one_le_uniformLocalCountConst :
    (1 : ℝ) ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) := by
  have h1 : 0 < Real.log (0.95 / 0.84) := Real.log_pos (by norm_num)
  have h2 : Real.log (0.95 / 0.84) ≤ 0.95 / 0.84 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have h3 : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  rw [le_div_iff₀ h1]
  linarith

/-- **Uniform local count, Tail form.**  `N_χ(t, t + 1] ≤ A₀ (1 + log q) log(|t| + 3)`. -/
theorem uniform_localCount_log (hq : 1 < q) (hprim : χ.IsPrimitive) (t : ℝ) :
    (NcountL χ t (t + 1) : ℝ) ≤
      2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (1 + Real.log q) * Real.log (|t| + 3) := by
  have h := uniform_localCount hq hprim t
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlog3 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      (by have := Real.exp_one_lt_d9; linarith [abs_nonneg t])
  have hsplit : Real.log (q * (|t| + 3)) ≤ (1 + Real.log q) * Real.log (|t| + 3) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    nlinarith
  have hA : 0 ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) :=
    zero_le_one.trans one_le_uniformLocalCountConst
  calc (NcountL χ t (t + 1) : ℝ)
      ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * Real.log (q * (|t| + 3)) := h
    _ ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * ((1 + Real.log q) * Real.log (|t| + 3)) :=
        mul_le_mul_of_nonneg_left hsplit hA
    _ = _ := by ring

/-- **Uniform boundary count.**  For `T ≥ 300`, the zeros of `L(s, χ)` in the two boundary strips
`(T − √T, T]` and `(2T, 2T + √T]` number at most `3 A₀ (1 + log q) √T log(4T)`. -/
theorem uniform_NII_le (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : Tail.T₀ ≤ T) :
    (Assembly.NII (LZeros (LSeam_of hq hprim)) T : ℝ) ≤
      3 * (2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (1 + Real.log q)) *
        Real.sqrt T * Real.log (4 * T) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hA₀ : (1 : ℝ) ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (1 + Real.log q) := by
    have := one_le_uniformLocalCountConst
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
    nlinarith
  refine Tail.NII_le (LZeros (LSeam_of hq hprim)) hA₀ (fun t => ?_) hT
  rw [LZeros_N]
  exact uniform_localCount_log hq hprim t

end RHTower
