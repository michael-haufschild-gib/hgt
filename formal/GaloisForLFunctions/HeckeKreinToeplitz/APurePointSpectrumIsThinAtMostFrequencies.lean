import Mathlib

/-!
# A pure-point spectrum is thin at most frequencies

A positive-definite kernel on `ℤ` with pure-point spectrum, `B(d) = Σ_i w_i e^{−i d θ_i}` with
`w_i ≥ 0` summable, has Toeplitz energy `Σ_i w_i |D_L(θ_i − θ₀)|²` on the modulated block
`(e^{i l θ₀})_{l < L}`, where `D_L(x) = Σ_{l<L} e^{i l x}` is the Dirichlet block (`dirichletBlock`).
This energy is at most `ε L` for a frequency `θ₀` in any prescribed arc, once `L` is large
(`exists_frequency_thin`). An absolutely continuous spectrum would give energy `≍ L`; atoms give
`o(L)` away from finitely many of them.

* **Grid identity** (`sum_grid_normSq_dirichletBlock`): for `L ≤ M`, the average of `|D_L|²` over the
  `M` equally spaced points of any shifted grid is exactly `L`. This is orthogonality of the
  `M`-th roots of unity; no integration is needed.
* **Decay away from `2πℤ`** (`norm_dirichletBlock_le_of_far`): `|D_L(x)| ≤ π/r` when `x` keeps
  distance `r` from `2πℤ`.
* **Few grid points are near an atom** (`card_near_le`): at most `M r/π + 1` points of a grid of
  `M` points lie within `r` of a given point modulo `2π`.

The selection splits the atoms into finitely many heavy ones, avoided by distance, and a light
tail of total weight `η`, controlled on average by the grid identity and Markov's inequality.
-/

open Complex Finset Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### The Dirichlet block -/

/-- The Dirichlet block `D_L(x) = Σ_{l<L} e^{i l x}`. -/
def dirichletBlock (L : ℕ) (x : ℝ) : ℂ := ∑ l ∈ range L, cexp (I * x) ^ l

theorem norm_dirichletBlock_le_card (L : ℕ) (x : ℝ) : ‖dirichletBlock L x‖ ≤ L := by
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ l ∈ range L, ‖cexp (I * x) ^ l‖ = 1 := fun l _ => by
    rw [norm_pow, mul_comm, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul, mul_one]

/-- `D_L` is `2π`-periodic. -/
theorem dirichletBlock_sub_two_pi_mul (L : ℕ) (x : ℝ) (k : ℤ) :
    dirichletBlock L (x - 2 * π * k) = dirichletBlock L x := by
  have h : cexp (I * ((x - 2 * π * k : ℝ) : ℂ)) = cexp (I * x) := by
    rw [show I * ((x - 2 * π * k : ℝ) : ℂ) = I * x + (-k : ℤ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [dirichletBlock, h]

theorem norm_dirichletBlock_neg (L : ℕ) (x : ℝ) :
    ‖dirichletBlock L (-x)‖ = ‖dirichletBlock L x‖ := by
  have h : dirichletBlock L (-x) = (starRingEnd ℂ) (dirichletBlock L x) := by
    simp only [dirichletBlock, map_sum, map_pow, ← Complex.exp_conj, map_mul, Complex.conj_I,
      Complex.conj_ofReal, Complex.ofReal_neg]
    congr 1
    funext l
    ring_nf
  rw [h, Complex.norm_conj]

/-- **Geometric bound** `|D_L(x)| ≤ 1/|sin(x/2)|`. -/
theorem norm_dirichletBlock_le_inv_sin (L : ℕ) {x : ℝ} (hx : Real.sin (x / 2) ≠ 0) :
    ‖dirichletBlock L x‖ ≤ 1 / |Real.sin (x / 2)| := by
  set z := cexp (I * x)
  have hz1 : ‖z - 1‖ = 2 * |Real.sin (x / 2)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_two]
  have hzne : z ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hz1
    have := abs_pos.mpr hx
    linarith
  have hzL : ‖z ^ L - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have hz : ‖z‖ = 1 := by simp only [z]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
    rw [norm_pow, hz, one_pow, norm_one]
    norm_num
  rw [dirichletBlock, geom_sum_eq hzne, norm_div, hz1]
  have hs := abs_pos.mpr hx
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith

/-- **Decay away from `2πℤ`.** If `x` keeps distance `r > 0` from `2πℤ`, then `|D_L(x)| ≤ π/r`. -/
theorem norm_dirichletBlock_le_of_far (L : ℕ) {x r : ℝ} (hr : 0 < r)
    (hfar : ∀ k : ℤ, r ≤ |x - 2 * π * k|) : ‖dirichletBlock L x‖ ≤ π / r := by
  set k₀ := round (x / (2 * π))
  set y := x - 2 * π * k₀
  have hπ := Real.pi_pos
  have hy : |y| ≤ π := by
    have h := abs_sub_round (x / (2 * π))
    have : y = 2 * π * (x / (2 * π) - k₀) := by
      simp only [y]; field_simp
    rw [this, abs_mul, abs_of_pos (by positivity)]
    nlinarith
  have hry : r ≤ |y| := hfar k₀
  have hsin : |y| / π ≤ |Real.sin (y / 2)| := by
    have h := Real.mul_le_sin (x := |y| / 2) (by positivity) (by linarith)
    have hy' := abs_le.mp hy
    have hs : Real.sin (|y| / 2) = |Real.sin (y / 2)| := by
      rcases le_or_gt 0 y with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
          (by linarith))]
      · rw [abs_of_neg h0, abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith)
          (by linarith)), neg_div, Real.sin_neg]
    rw [← hs]
    calc |y| / π = 2 / π * (|y| / 2) := by ring
      _ ≤ _ := h
  have hpos : 0 < |Real.sin (y / 2)| := lt_of_lt_of_le (div_pos (hr.trans_le hry) hπ) hsin
  rw [← dirichletBlock_sub_two_pi_mul L x k₀]
  refine (norm_dirichletBlock_le_inv_sin L (abs_pos.mp hpos)).trans ?_
  rw [div_le_div_iff₀ hpos hr]
  have : π * |Real.sin (y / 2)| ≥ |y| := by
    have := (div_le_iff₀ hπ).mp hsin
    linarith
  linarith

/-! ### Orthogonality on a grid -/

/-- The `M`-th roots of unity of a nonzero residue sum to zero. -/
theorem sum_range_exp_two_pi_mul_eq_zero {M : ℕ} {d : ℤ} (hd0 : d ≠ 0) (hdM : |d| < M) :
    ∑ m ∈ range M, cexp (2 * π * I * d / M) ^ m = 0 := by
  have hM : (0 : ℝ) < M := by
    have : (0 : ℤ) < M := lt_of_le_of_lt (abs_nonneg d) hdM
    exact_mod_cast this
  set ζ := cexp (2 * π * I * d / M)
  have hζM : ζ ^ M = 1 := by
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [← Complex.exp_nat_mul, show (M : ℂ) * (2 * π * I * d / M) = d * (2 * π * I) by
      field_simp, Complex.exp_int_mul_two_pi_mul_I]
  have hζ : ζ ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have h2 : (d : ℂ) = n * M := by
      have hπI : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp at hn
      linear_combination hn
    have h3 : d = n * M := by exact_mod_cast h2
    rcases eq_or_ne n 0 with hn0 | hn0
    · exact hd0 (by rw [h3, hn0, zero_mul])
    · have : (M : ℤ) ≤ |d| := by
        rw [h3, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ M)]
        exact le_mul_of_one_le_left (by positivity) (Int.one_le_abs hn0)
      omega
  rw [geom_sum_eq hζ, hζM, sub_self, zero_div]

/-- **Grid identity.** For `L ≤ M` the sum of `|D_L|²` over a shifted grid of `M` points is `M L`. -/
theorem sum_grid_normSq_dirichletBlock {L M : ℕ} (hLM : L ≤ M) (x : ℝ) :
    ∑ m ∈ range M, ‖dirichletBlock L (x - 2 * π * m / M)‖ ^ 2 = M * L := by
  have hexp : ∀ y : ℝ, (‖dirichletBlock L y‖ ^ 2 : ℂ) =
      ∑ l ∈ range L, ∑ l' ∈ range L, cexp (I * y * ((l : ℤ) - l' : ℤ)) := by
    intro y
    rw [← Complex.mul_conj', dirichletBlock, map_sum, sum_mul_sum]
    refine sum_congr rfl fun l _ => sum_congr rfl fun l' _ => ?_
    rw [map_pow, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hexp]
  have hinner : ∀ l ∈ range L, ∀ l' ∈ range L,
      ∑ m ∈ range M, cexp (I * ((x - 2 * π * m / M : ℝ) : ℂ) * ((l : ℤ) - l' : ℤ)) =
        if l = l' then (M : ℂ) else 0 := by
    intro l hl l' hl'
    have hsplit : ∀ m : ℕ, cexp (I * ((x - 2 * π * m / M : ℝ) : ℂ) * ((l : ℤ) - l' : ℤ)) =
        cexp (I * x * ((l : ℤ) - l' : ℤ)) * cexp (2 * π * I * (((l' : ℤ) - l : ℤ) : ℂ) / M) ^ m := by
      intro m
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hsplit, ← mul_sum]
    split_ifs with h
    · subst h
      simp
    · rw [sum_range_exp_two_pi_mul_eq_zero (by omega), mul_zero]
      have hl := mem_range.mp hl
      have hl' := mem_range.mp hl'
      rw [abs_lt]
      constructor <;> omega
  calc ∑ m ∈ range M, ∑ l ∈ range L, ∑ l' ∈ range L,
        cexp (I * ((x - 2 * π * m / M : ℝ) : ℂ) * ((l : ℤ) - l' : ℤ))
      = ∑ l ∈ range L, ∑ l' ∈ range L, ∑ m ∈ range M,
        cexp (I * ((x - 2 * π * m / M : ℝ) : ℂ) * ((l : ℤ) - l' : ℤ)) := by
        rw [sum_comm]; exact sum_congr rfl fun l _ => sum_comm
    _ = ∑ l ∈ range L, ∑ l' ∈ range L, if l = l' then (M : ℂ) else 0 :=
        sum_congr rfl fun l hl => sum_congr rfl fun l' hl' => hinner l hl l' hl'
    _ = M * L := by
        rw [sum_congr rfl fun l hl => by rw [sum_ite_eq, if_pos hl], sum_const, card_range,
          nsmul_eq_mul, mul_comm]

/-! ### Grid points near a given point -/

open Classical in
/-- **Few grid points are near a point.** At most `M r/π + 1` of the points `2πm/M`, `m < M`, lie
within `r` of `x` modulo `2π`. -/
theorem card_near_le {M : ℕ} (hM : 0 < M) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (((range M).filter fun m : ℕ => ∃ k : ℤ, |x - 2 * π * m / M - 2 * π * k| < r).card : ℝ) ≤
      M * r / π + 1 := by
  classical
  set S := (range M).filter fun m : ℕ => ∃ k : ℤ, |x - 2 * π * m / M - 2 * π * k| < r
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hπ := Real.pi_pos
  set A : ℝ := M * (x - r) / (2 * π)
  set B : ℝ := M * (x + r) / (2 * π)
  -- each near point carries an integer `m + M k` in `(A, B)`
  let kOf : ℕ → ℤ := fun m =>
    if h : ∃ k : ℤ, |x - 2 * π * m / M - 2 * π * k| < r then h.choose else 0
  let j : ℕ → ℤ := fun m => m + M * kOf m
  have hj : ∀ m ∈ S, A < j m ∧ (j m : ℝ) < B := by
    intro m hm
    have hex := (mem_filter.mp hm).2
    have hk : |x - 2 * π * m / M - 2 * π * kOf m| < r := by
      simp only [kOf, dif_pos hex]; exact hex.choose_spec
    have hval : (j m : ℝ) = M * (x - (x - 2 * π * m / M - 2 * π * kOf m)) / (2 * π) := by
      simp only [j]; push_cast; field_simp; ring
    rw [abs_lt] at hk
    constructor
    · rw [hval]; simp only [A]
      apply div_lt_div_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_left (by linarith) hMr
    · rw [hval]; simp only [B]
      apply div_lt_div_of_pos_right _ (by positivity)
      exact mul_lt_mul_of_pos_left (by linarith) hMr
  have hinj : Set.InjOn j S := by
    intro m hm m' hm' h
    have hm1 := mem_range.mp (mem_filter.mp hm).1
    have hm1' := mem_range.mp (mem_filter.mp hm').1
    simp only [j] at h
    have hdiv : (M : ℤ) ∣ (m : ℤ) - m' := ⟨kOf m' - kOf m, by linarith⟩
    have hlt : |(m : ℤ) - m'| < M := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdiv hlt
    omega
  have hcard := Finset.card_le_card_of_injOn j (s := S) (t := Finset.Icc ⌈A⌉ ⌊B⌋)
    (fun m hm => by
      obtain ⟨h1, h2⟩ := hj m hm
      exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr h1.le, Int.le_floor.mpr h2.le⟩) hinj
  rw [Int.card_Icc] at hcard
  have hcast : (S.card : ℝ) ≤ ((⌊B⌋ + 1 - ⌈A⌉).toNat : ℝ) := by exact_mod_cast hcard
  refine hcast.trans ?_
  rcases le_or_gt 0 (⌊B⌋ + 1 - ⌈A⌉) with h0 | h0
  · rw [show (((⌊B⌋ + 1 - ⌈A⌉).toNat : ℕ) : ℝ) = ((⌊B⌋ + 1 - ⌈A⌉ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h0]
    push_cast
    have h1 := Int.floor_le B
    have h2 := Int.le_ceil A
    have hBA : B - A = M * r / π := by simp only [A, B]; field_simp; ring
    linarith
  · rw [Int.toNat_of_nonpos h0.le]
    push_cast
    positivity

/-! ### Frequency selection -/

/-- **A pure-point spectrum is thin at most frequencies.** For nonnegative summable weights `w` at
frequencies `θ`, every `ε > 0` and every arc `[π − δ, π + δ]`, all large `L` admit a frequency `θ₀`
in the arc with `Σ_i w_i |D_L(θ_i − θ₀)|² ≤ ε L`. -/
theorem exists_frequency_thin {ι : Type*} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w)
    (θ : ι → ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδπ : δ ≤ π) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∃ θ₀ : ℝ, |θ₀ - π| ≤ δ ∧
      Summable (fun i => w i * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2) ∧
      ∑' i, w i * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2 ≤ ε * L := by
  classical
  have hπ := Real.pi_pos
  -- the light tail
  set η : ℝ := ε * δ / (8 * π)
  have hη : 0 < η := by positivity
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∑' i : {x // x ∉ F}, w i < η :=
    ((tendsto_tsum_compl_atTop_zero w).eventually (gt_mem_nhds hη)).exists
  set W : ℝ := ∑ i ∈ F, w i
  have hW : 0 ≤ W := sum_nonneg fun i _ => hw0 i
  set K : ℕ := F.card
  -- the large-`L` thresholds
  have hlim1 : Tendsto (fun L : ℕ => (K : ℝ) * Real.sqrt ((2 * W + 1) / (ε * L))) atTop (𝓝 0) := by
    have h : Tendsto (fun L : ℕ => (2 * W + 1) / (ε * L)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop hε)
    simpa using (h.sqrt).const_mul (K : ℝ)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (hlim1.eventually (gt_mem_nhds
    (show (0 : ℝ) < δ / (4 * π) by positivity)))
  obtain ⟨L₂, hL₂⟩ := exists_nat_gt ((K + 1) * 4 * π / δ)
  refine ⟨max (max L₁ L₂) 1, fun L hL => ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  -- the grid of `L` points, starting at the left end of the arc
  set grid : ℕ → ℝ := fun m => π - δ + 2 * π * m / L
  have hterm0 : ∀ θ₀ i, 0 ≤ w i * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2 := fun θ₀ i =>
    mul_nonneg (hw0 i) (by positivity)
  have hsum : ∀ θ₀ : ℝ, Summable (fun i => w i * ‖dirichletBlock L (θ i - θ₀)‖ ^ 2) := by
    intro θ₀
    refine (hw.mul_right ((L : ℝ) ^ 2)).of_nonneg_of_le (hterm0 θ₀) fun i => ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_dirichletBlock_le_card L _) 2) (hw0 i)
  -- light part
  set light : ℕ → ℝ := fun m => ∑' i : {x // x ∉ F}, w i * ‖dirichletBlock L (θ i - grid m)‖ ^ 2
  have hlight_sum : ∑ m ∈ range L, light m ≤ L * L * η := by
    have hsl : ∀ m, Summable (fun i : {x // x ∉ F} =>
        w i * ‖dirichletBlock L (θ i - grid m)‖ ^ 2) := fun m => (hsum (grid m)).subtype _
    rw [← Summable.tsum_finsetSum fun m _ => hsl m]
    have hgrid : ∀ i : {x // x ∉ F}, ∑ m ∈ range L, w i * ‖dirichletBlock L (θ i - grid m)‖ ^ 2 =
        w i * (L * L) := by
      intro i
      rw [← mul_sum]
      congr 1
      have := sum_grid_normSq_dirichletBlock (le_refl L) (θ i - (π - δ))
      simpa [grid, sub_sub] using this
    rw [tsum_congr hgrid, tsum_mul_right]
    have := hF.le
    nlinarith [show (0 : ℝ) ≤ L * L by positivity]
  -- the arc
  set A := range (min L (⌊L * δ / π⌋₊ + 1))
  have hA_arc : ∀ m ∈ A, |grid m - π| ≤ δ := by
    intro m hm
    have hm := mem_range.mp hm
    have hm2 : (m : ℝ) ≤ L * δ / π := by
      have := Nat.lt_succ_iff.mp (lt_of_lt_of_le hm (min_le_right _ _))
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
    have h0 : 0 ≤ 2 * π * m / L := by positivity
    have h1 : 2 * π * m / L ≤ 2 * δ := by
      rw [div_le_iff₀ hLpos]
      have := (le_div_iff₀ hπ).mp hm2
      nlinarith
    rw [abs_le]; simp only [grid]; constructor <;> linarith
  have hA_card : L * δ / π ≤ A.card := by
    rw [card_range]
    rcases le_total L (⌊L * δ / π⌋₊ + 1) with h | h
    · rw [min_eq_left h]
      rw [div_le_iff₀ hπ]; nlinarith
    · rw [min_eq_right h]
      exact_mod_cast (Nat.lt_floor_add_one (L * δ / π)).le
  -- the bad sets
  set Bl := A.filter fun m => ε * L / 2 < light m
  set r : ℝ := π * Real.sqrt ((2 * W + 1) / (ε * L))
  have hr : 0 < r := by positivity
  set Bh := F.biUnion fun i => (range L).filter fun m : ℕ =>
    ∃ k : ℤ, |(θ i - (π - δ)) - 2 * π * m / L - 2 * π * k| < r
  -- Markov for the light part
  have hBl : (Bl.card : ℝ) * (ε * L / 2) ≤ L * L * η := by
    have h1 := Finset.card_nsmul_le_sum Bl light (ε * L / 2) fun m hm => (mem_filter.mp hm).2.le
    rw [nsmul_eq_mul] at h1
    refine h1.trans (le_trans ?_ hlight_sum)
    refine sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans fun m hm => mem_range.mpr
      (lt_of_lt_of_le (mem_range.mp hm) (min_le_left _ _))) fun m _ _ => ?_
    exact tsum_nonneg fun i => hterm0 _ _
  have hBl' : (Bl.card : ℝ) ≤ L * δ / (4 * π) := by
    have h2 : (Bl.card : ℝ) ≤ L * L * η / (ε * L / 2) := by
      rw [le_div_iff₀ (by positivity)]; exact hBl
    refine h2.trans (le_of_eq ?_)
    have hL0 : (L : ℝ) ≠ 0 := hLpos.ne'
    have hε0 : ε ≠ 0 := hε.ne'
    simp only [η]; field_simp; ring
  have hBh : (Bh.card : ℝ) ≤ K * (L * r / π + 1) := by
    refine (Nat.cast_le.mpr card_biUnion_le).trans ?_
    push_cast
    refine (sum_le_sum fun i _ => card_near_le (by omega) _ hr.le).trans ?_
    rw [sum_const, nsmul_eq_mul]
  have hKr : (K : ℝ) * (r / π) < δ / (4 * π) := by
    have h := hL₁ L ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
    have : (K : ℝ) * (r / π) = K * Real.sqrt ((2 * W + 1) / (ε * L)) := by
      simp only [r]; field_simp
    rw [this]; exact h
  have hK1 : ((K : ℝ) + 1) < L * δ / (4 * π) := by
    have hL2 : (L₂ : ℝ) ≤ L := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hL)
    have h := hL₂
    rw [lt_div_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at h
    nlinarith
  have hcard : (Bl ∪ Bh).card < A.card := by
    have h1 : ((Bl ∪ Bh).card : ℝ) ≤ Bl.card + Bh.card := by exact_mod_cast card_union_le _ _
    have h2 : (K : ℝ) * (L * r / π + 1) ≤ L * δ / (4 * π) + K := by
      have e : (K : ℝ) * (L * r / π + 1) = L * (K * (r / π)) + K := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hKr.le hLpos.le
      have e2 : (L : ℝ) * (δ / (4 * π)) = L * δ / (4 * π) := by ring
      linarith
    have h3 : ((Bl ∪ Bh).card : ℝ) < A.card := by
      have e3 : (L : ℝ) * δ / π = 4 * (L * δ / (4 * π)) := by ring
      linarith
    exact_mod_cast h3
  obtain ⟨m, hmA, hmbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hmBl : ¬ ε * L / 2 < light m := fun h => hmbad (mem_union_left _ (mem_filter.mpr ⟨hmA, h⟩))
  have hmL : m < L := lt_of_lt_of_le (mem_range.mp hmA) (min_le_left _ _)
  have hfar : ∀ i ∈ F, ∀ k : ℤ, r ≤ |θ i - grid m - 2 * π * k| := by
    intro i hi k
    by_contra hk
    push Not at hk
    refine hmbad (mem_union_right _ (mem_biUnion.mpr ⟨i, hi, mem_filter.mpr
      ⟨mem_range.mpr hmL, k, ?_⟩⟩))
    have e : θ i - (π - δ) - 2 * π * m / L - 2 * π * k = θ i - grid m - 2 * π * k := by
      simp only [grid]; ring
    rw [e]; exact hk
  refine ⟨grid m, hA_arc m hmA, hsum _, ?_⟩
  -- heavy part: every heavy atom is far
  have hheavy : ∑ i ∈ F, w i * ‖dirichletBlock L (θ i - grid m)‖ ^ 2 ≤ ε * L / 2 := by
    have hb : ∀ i ∈ F, w i * ‖dirichletBlock L (θ i - grid m)‖ ^ 2 ≤ w i * (π / r) ^ 2 := by
      intro i hi
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (hw0 i)
      exact norm_dirichletBlock_le_of_far L hr (hfar i hi)
    refine (sum_le_sum hb).trans ?_
    rw [← sum_mul]
    have hr2 : (π / r) ^ 2 = ε * L / (2 * W + 1) := by
      simp only [r]
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
    rw [hr2, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [show (0 : ℝ) ≤ ε * L by positivity]
  have hsplit := (hsum (grid m)).tsum_subtype_add_tsum_subtype_compl (F : Set ι)
  rw [← hsplit, Finset.tsum_subtype' F (fun i => w i * ‖dirichletBlock L (θ i - grid m)‖ ^ 2)]
  have hcompl : ∑' x : ↑((F : Set ι)ᶜ), w x * ‖dirichletBlock L (θ x - grid m)‖ ^ 2 = light m := rfl
  rw [hcompl]
  push Not at hmBl
  linarith

end GaloisForLFunctions.HeckeKreinToeplitz
