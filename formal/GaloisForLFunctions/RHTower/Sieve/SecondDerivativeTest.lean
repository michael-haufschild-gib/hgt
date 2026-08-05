import GaloisForLFunctions.RHTower.Sieve.KuzminLandauInterval
import GaloisForLFunctions.RHTower.Sieve.MonotoneFibers

/-!
# The second-derivative test

For a phase `g` whose second derivative is pinned between `λ` and `h·λ` on the span of `N`
unit-spaced sample points, with `0 < λ ≤ 1`, the exponential sum is at most
`(2Nhλ + 3)·(3/√λ + 1)`, hence `8Nh√λ + 12/√λ`.

The derivative range is classified by the region index `I(y) = ⌊y−δ⌋ + ⌊y+δ⌋` with
`δ = √λ/2`: the index is monotone along the samples, its even fibres are runs where the
derivative stays inside one integer band `[m+δ, m+1−δ]` (where Kuzmin–Landau applies
uniformly in the run length), its odd fibres are runs where the derivative is within `δ` of
an integer (short, because `g'' ≥ λ` drives the derivative through the width-`2δ` gap in at
most `2δ/λ` unit steps), and the number of fibres is controlled by the total variation of
the derivative.
-/

namespace RHTower.Sieve

open Real

/-- The band-or-gap region index of a derivative value. -/
noncomputable def regionIdx (δ y : ℝ) : ℤ := ⌊y - δ⌋ + ⌊y + δ⌋

theorem regionIdx_mono (δ : ℝ) : Monotone (regionIdx δ) := fun _ _ h =>
  add_le_add (Int.floor_mono (by linarith)) (Int.floor_mono (by linarith))

/-- The index moves at most twice as fast as the value, plus the endpoint slack. -/
theorem regionIdx_diff_le (δ : ℝ) {y y' : ℝ} (_ : y ≤ y') :
    ((regionIdx δ y' - regionIdx δ y : ℤ) : ℝ) ≤ 2 * (y' - y) + 2 := by
  have h1 : ((⌊y' - δ⌋ : ℤ) : ℝ) ≤ y' - δ := Int.floor_le _
  have h2 : ((⌊y' + δ⌋ : ℤ) : ℝ) ≤ y' + δ := Int.floor_le _
  have h3 : y - δ - 1 < ((⌊y - δ⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  have h4 : y + δ - 1 < ((⌊y + δ⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  simp only [regionIdx]
  push_cast
  linarith

/-- The two floors of the index differ by at most one when `2δ ≤ 1`. -/
theorem regionIdx_floor_pair {δ : ℝ} (y : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) :
    ⌊y - δ⌋ ≤ ⌊y + δ⌋ ∧ ⌊y + δ⌋ ≤ ⌊y - δ⌋ + 1 := by
  refine ⟨Int.floor_mono (by linarith), ?_⟩
  calc ⌊y + δ⌋ ≤ ⌊(y - δ) + 1⌋ := Int.floor_mono (by linarith)
    _ = ⌊y - δ⌋ + 1 := Int.floor_add_one _

/-- An even region index pins the value inside the integer band `[m+δ, m+1−δ)`. -/
theorem regionIdx_even_band {δ y : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) {m : ℤ}
    (h : regionIdx δ y = m + m) : (m : ℝ) + δ ≤ y ∧ y ≤ (m : ℝ) + 1 - δ := by
  obtain ⟨hab, hba⟩ := regionIdx_floor_pair y hδ0 hδ1
  simp only [regionIdx] at h
  have hlo : ⌊y - δ⌋ = m := by omega
  have hhi : ⌊y + δ⌋ = m := by omega
  constructor
  · have h1 : ((m : ℤ) : ℝ) ≤ y - δ := by rw [← hlo]; exact Int.floor_le _
    linarith
  · have h2 := Int.lt_floor_add_one (y + δ)
    rw [hhi] at h2
    linarith

/-- An odd region index pins the value inside the gap `[m+1−δ, m+1+δ)` around an integer. -/
theorem regionIdx_odd_gap {δ y : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) {m : ℤ}
    (h : regionIdx δ y = 2 * m + 1) : (m : ℝ) + 1 - δ ≤ y ∧ y < (m : ℝ) + 1 + δ := by
  obtain ⟨hab, hba⟩ := regionIdx_floor_pair y hδ0 hδ1
  simp only [regionIdx] at h
  have hlo : ⌊y - δ⌋ = m := by omega
  have hhi : ⌊y + δ⌋ = m + 1 := by omega
  constructor
  · have h1 : ((m + 1 : ℤ) : ℝ) ≤ y + δ := by rw [← hhi]; exact Int.floor_le _
    push_cast at h1
    linarith
  · have h2 := Int.lt_floor_add_one (y - δ)
    rw [hlo] at h2
    linarith

/-- **The second-derivative test.**  If `λ ≤ g'' ≤ h·λ` on the span of `N` unit-spaced
sample points, with `0 < λ ≤ 1`, then

  `‖∑_{n<N} e(g(x₀+n))‖ ≤ (2·N·h·λ + 3)·(3/√λ + 1)`. -/
theorem second_derivative_test (g g' g'' : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hd1 : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), HasDerivAt g (g' x) x)
    (hd2 : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), HasDerivAt g' (g'' x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ g'' x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), g'' x ≤ hgrow * lam) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ (2 * N * hgrow * lam + 3) * (3 / Real.sqrt lam + 1) := by
  classical
  set span := Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) with hspan
  have hsq0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hsq1 : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr hlam1
  have hsqsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam0.le
  set δ := Real.sqrt lam / 2 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : 2 * δ ≤ 1 := by rw [hδdef]; linarith
  have h2δ : 2 * δ = Real.sqrt lam := by rw [hδdef]; ring
  -- sample points live on the span
  have hsample : ∀ n : ℕ, n < N → x₀ + (n : ℝ) ∈ span := by
    intro n hn
    rw [hspan, Set.mem_Icc]
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hle : (n : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      have : n ≤ N - 1 := by omega
      exact_mod_cast this
    exact ⟨by linarith, by linarith⟩
  -- mean value bounds for the derivative increments
  have hslope : ∀ a b : ℝ, a ∈ span → b ∈ span → a < b →
      ∃ ξ ∈ Set.Ioo a b, g'' ξ = (g' b - g' a) / (b - a) := by
    intro a b ha hb hab
    have hsub : Set.Icc a b ⊆ span := by
      rw [hspan] at ha hb ⊢
      exact Set.Icc_subset_Icc ha.1 hb.2
    have hcont : ContinuousOn g' (Set.Icc a b) := fun x hx =>
      (hd2 x (hsub hx)).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Set.Ioo a b, HasDerivAt g' (g'' x) x := fun x hx =>
      hd2 x (hsub (Set.mem_Icc_of_Ioo hx))
    exact exists_hasDerivAt_eq_slope g' g'' hab hcont hd
  have hξspan : ∀ a b ξ : ℝ, a ∈ span → b ∈ span → ξ ∈ Set.Ioo a b → ξ ∈ span := by
    intro a b ξ ha hb hξ
    rw [hspan] at ha hb ⊢
    exact ⟨le_trans ha.1 hξ.1.le, le_trans hξ.2.le hb.2⟩
  have hgap_lo : ∀ a b : ℝ, a ∈ span → b ∈ span → a ≤ b →
      lam * (b - a) ≤ g' b - g' a := by
    intro a b ha hb hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · obtain ⟨ξ, hξ, hval⟩ := hslope a b ha hb hlt
      have hpos : 0 < b - a := by linarith
      rw [eq_div_iff (ne_of_gt hpos)] at hval
      calc lam * (b - a) ≤ g'' ξ * (b - a) :=
            mul_le_mul_of_nonneg_right (hlo ξ (hξspan a b ξ ha hb hξ)) hpos.le
        _ = g' b - g' a := hval
  have hgap_hi : ∀ a b : ℝ, a ∈ span → b ∈ span → a ≤ b →
      g' b - g' a ≤ hgrow * lam * (b - a) := by
    intro a b ha hb hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · obtain ⟨ξ, hξ, hval⟩ := hslope a b ha hb hlt
      have hpos : 0 < b - a := by linarith
      rw [eq_div_iff (ne_of_gt hpos)] at hval
      calc g' b - g' a = g'' ξ * (b - a) := hval.symm
        _ ≤ hgrow * lam * (b - a) :=
            mul_le_mul_of_nonneg_right (hhi ξ (hξspan a b ξ ha hb hξ)) hpos.le
  have hmono : MonotoneOn g' span := by
    intro a ha b hb hab
    have h1 := hgap_lo a b ha hb hab
    have h2 : 0 ≤ lam * (b - a) := mul_nonneg hlam0.le (by linarith)
    linarith
  -- the classification and its monotonicity along the samples
  set K : ℕ → ℤ := fun n => regionIdx δ (g' (x₀ + (n : ℝ))) with hKdef
  have hK : ∀ a b : ℕ, a ≤ b → b < N → K a ≤ K b := by
    intro a b hab hbN
    have haN : a < N := lt_of_le_of_lt hab hbN
    have hle : x₀ + (a : ℝ) ≤ x₀ + (b : ℝ) := by
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    have hg := hmono (hsample a haN) (hsample b hbN) hle
    simp only [hKdef]
    exact regionIdx_mono δ hg
  -- every fibre contributes at most `3/√λ + 1`
  have hfibre : ∀ v ∈ (Finset.range N).image K,
      ‖∑ n ∈ (Finset.range N).filter (fun n => K n = v),
          Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
        ≤ 3 / Real.sqrt lam + 1 := by
    intro v _
    obtain ⟨l, u, hIco⟩ := filter_eq_Ico_of_monotone hK v
    rw [hIco]
    rcases Nat.lt_or_ge l u with hlu | hlu
    swap
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, norm_zero]
      positivity
    have hlmem : l ∈ (Finset.range N).filter (fun n => K n = v) := by
      rw [hIco]; exact Finset.mem_Ico.mpr ⟨le_refl l, hlu⟩
    have humem : u - 1 ∈ (Finset.range N).filter (fun n => K n = v) := by
      rw [hIco]; exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range] at hlmem humem
    obtain ⟨M, hM⟩ : ∃ M, u = l + M + 1 := ⟨u - l - 1, by omega⟩
    have huN : u ≤ N := by omega
    have hend_u_eq : (x₀ + (l : ℝ)) + ((M : ℕ) : ℝ) = x₀ + ((u - 1 : ℕ) : ℝ) := by
      have hu1 : u - 1 = l + M := by omega
      rw [hu1]; push_cast; ring
    rcases Int.even_or_odd v with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- band fibre: Kuzmin–Landau on the run
      have hKl : regionIdx δ (g' (x₀ + (l : ℝ))) = m + m := by
        have h := hlmem.2; simp only [hKdef] at h; omega
      have hKu : regionIdx δ (g' (x₀ + ((u - 1 : ℕ) : ℝ))) = m + m := by
        have h := humem.2; simp only [hKdef] at h; omega
      have hband_l := regionIdx_even_band hδ0.le hδ1 hKl
      have hband_u := regionIdx_even_band hδ0.le hδ1 hKu
      have hsub2 : Set.Icc (x₀ + (l : ℝ)) ((x₀ + (l : ℝ)) + ((M : ℕ) : ℝ)) ⊆ span := by
        rw [hspan]
        apply Set.Icc_subset_Icc
        · have h0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
          linarith
        · have h1 : l + M ≤ N - 1 := by omega
          have h2 : ((l + M : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at h2
          linarith
      have hband_lo' : ∀ x ∈ Set.Icc (x₀ + (l : ℝ)) ((x₀ + (l : ℝ)) + ((M : ℕ) : ℝ)),
          (m : ℝ) + δ ≤ g' x := by
        intro x hx
        have hge : g' (x₀ + (l : ℝ)) ≤ g' x :=
          hmono (hsample l (by omega)) (hsub2 hx) hx.1
        linarith [hband_l.1]
      have hband_hi' : ∀ x ∈ Set.Icc (x₀ + (l : ℝ)) ((x₀ + (l : ℝ)) + ((M : ℕ) : ℝ)),
          g' x ≤ (m : ℝ) + 1 - δ := by
        intro x hx
        have hxle : x ≤ x₀ + ((u - 1 : ℕ) : ℝ) := by rw [← hend_u_eq]; exact hx.2
        have hle2 : g' x ≤ g' (x₀ + ((u - 1 : ℕ) : ℝ)) :=
          hmono (hsub2 hx) (hsample (u - 1) (by omega)) hxle
        linarith [hband_u.2]
      have hd1' : ∀ x ∈ Set.Icc (x₀ + (l : ℝ)) ((x₀ + (l : ℝ)) + ((M : ℕ) : ℝ)),
          HasDerivAt g (g' x) x := fun x hx => hd1 x (hsub2 hx)
      have hKL := kuzminLandau_interval g g' (x₀ + (l : ℝ)) M m hδ0 hd1'
        (hmono.mono hsub2) hband_lo' hband_hi'
      have hreidx : ∑ n ∈ Finset.Ico l u,
          Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)
          = ∑ j ∈ Finset.range (u - l),
              Complex.exp (((2 * Real.pi * g (x₀ + l + j) : ℝ) : ℂ) * Complex.I) := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        have harg : x₀ + ((l + j : ℕ) : ℝ) = x₀ + (l : ℝ) + (j : ℝ) := by
          push_cast; ring
        rw [harg]
      have hrange : u - l = M + 1 := by omega
      rw [hreidx, hrange]
      simpa only [h2δ] using hKL
    · -- gap fibre: the slope forces the run through the gap quickly
      have hKl : regionIdx δ (g' (x₀ + (l : ℝ))) = 2 * m + 1 := by
        have h := hlmem.2; simp only [hKdef] at h; omega
      have hKu : regionIdx δ (g' (x₀ + ((u - 1 : ℕ) : ℝ))) = 2 * m + 1 := by
        have h := humem.2; simp only [hKdef] at h; omega
      have hgap_l := regionIdx_odd_gap hδ0.le hδ1 hKl
      have hgap_u := regionIdx_odd_gap hδ0.le hδ1 hKu
      have htriv : ‖∑ n ∈ Finset.Ico l u,
          Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
          ≤ ((u - l : ℕ) : ℝ) := by
        calc ‖∑ n ∈ Finset.Ico l u,
              Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
            ≤ ∑ n ∈ Finset.Ico l u,
              ‖Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ :=
              norm_sum_le _ _
          _ = ∑ _n ∈ Finset.Ico l u, (1 : ℝ) :=
              Finset.sum_congr rfl fun n _ => Complex.norm_exp_ofReal_mul_I _
          _ = ((u - l : ℕ) : ℝ) := by
              rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      have hcount : ((u - l : ℕ) : ℝ) ≤ 1 / Real.sqrt lam + 1 := by
        have hinv0 : (0 : ℝ) ≤ 1 / Real.sqrt lam := by positivity
        rcases Nat.lt_or_ge (u - l) 2 with hc | hc
        · have h1 : ((u - l : ℕ) : ℝ) ≤ 1 := by
            have : u - l ≤ 1 := by omega
            exact_mod_cast this
          linarith
        · have hle : x₀ + (l : ℝ) ≤ x₀ + ((u - 1 : ℕ) : ℝ) := by
            have h1 : ((l : ℕ) : ℝ) ≤ ((u - 1 : ℕ) : ℝ) := by
              have : l ≤ u - 1 := by omega
              exact_mod_cast this
            linarith
          have hlow := hgap_lo (x₀ + (l : ℝ)) (x₀ + ((u - 1 : ℕ) : ℝ))
            (hsample l (by omega)) (hsample (u - 1) (by omega)) hle
          have hxdiff : (x₀ + ((u - 1 : ℕ) : ℝ)) - (x₀ + (l : ℝ)) = ((M : ℕ) : ℝ) := by
            have hu1 : u - 1 = l + M := by omega
            rw [hu1]; push_cast; ring
          rw [hxdiff] at hlow
          have hgapw : g' (x₀ + ((u - 1 : ℕ) : ℝ)) - g' (x₀ + (l : ℝ)) < 2 * δ := by
            linarith [hgap_l.1, hgap_u.2]
          have hMlam : lam * ((M : ℕ) : ℝ) < Real.sqrt lam := by
            rw [← h2δ]
            exact lt_of_le_of_lt hlow hgapw
          have hMss : Real.sqrt lam * (((M : ℕ) : ℝ) * Real.sqrt lam)
              < Real.sqrt lam * 1 := by
            have hrw : Real.sqrt lam * (((M : ℕ) : ℝ) * Real.sqrt lam)
                = lam * ((M : ℕ) : ℝ) := by
              linear_combination ((M : ℕ) : ℝ) * hsqsq
            rw [hrw, mul_one]
            exact hMlam
          have hMs : ((M : ℕ) : ℝ) * Real.sqrt lam < 1 :=
            lt_of_mul_lt_mul_left hMss hsq0.le
          have hinv : Real.sqrt lam * (Real.sqrt lam)⁻¹ = 1 := mul_inv_cancel₀ hsq0.ne'
          have hMone : ((M : ℕ) : ℝ) < 1 / Real.sqrt lam := by
            rw [div_eq_mul_inv, one_mul]
            nlinarith [hMs, hsq0, hinv]
          have hcast : ((u - l : ℕ) : ℝ) = ((M : ℕ) : ℝ) + 1 := by
            have : u - l = M + 1 := by omega
            exact_mod_cast this
          rw [hcast]
          linarith
      calc ‖∑ n ∈ Finset.Ico l u,
            Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
          ≤ ((u - l : ℕ) : ℝ) := htriv
        _ ≤ 1 / Real.sqrt lam + 1 := hcount
        _ ≤ 3 / Real.sqrt lam + 1 := by
            have ht : (0 : ℝ) ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg lam)
            rw [div_eq_mul_inv, div_eq_mul_inv]
            linarith
  -- the number of fibres is controlled by the total variation of the derivative
  have hx0span : x₀ ∈ span := by
    rw [hspan]
    exact ⟨le_refl x₀, le_add_of_nonneg_right (Nat.cast_nonneg _)⟩
  have hgrow1 : 1 ≤ hgrow := by
    have h1 := hlo x₀ hx0span
    have h2 := hhi x₀ hx0span
    nlinarith [hlam0]
  have himage : (((Finset.range N).image K).card : ℝ) ≤ 2 * N * hgrow * lam + 3 := by
    have hcard := card_image_le_of_monotone hN hK
    have hle0 : x₀ + ((0 : ℕ) : ℝ) ≤ x₀ + ((N - 1 : ℕ) : ℝ) := by
      have h0 : ((0 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
      linarith
    have hgmono : g' (x₀ + ((0 : ℕ) : ℝ)) ≤ g' (x₀ + ((N - 1 : ℕ) : ℝ)) :=
      hmono (hsample 0 (by omega)) (hsample (N - 1) (by omega)) hle0
    have hdiffK : ((K (N - 1) - K 0 : ℤ) : ℝ)
        ≤ 2 * (g' (x₀ + ((N - 1 : ℕ) : ℝ)) - g' (x₀ + ((0 : ℕ) : ℝ))) + 2 := by
      simp only [hKdef]
      exact regionIdx_diff_le δ hgmono
    have hvar := hgap_hi (x₀ + ((0 : ℕ) : ℝ)) (x₀ + ((N - 1 : ℕ) : ℝ))
      (hsample 0 (by omega)) (hsample (N - 1) (by omega)) hle0
    have hNb : (x₀ + ((N - 1 : ℕ) : ℝ)) - (x₀ + ((0 : ℕ) : ℝ)) ≤ (N : ℝ) := by
      have h1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
      push_cast
      linarith
    have hmul : hgrow * lam * ((x₀ + ((N - 1 : ℕ) : ℝ)) - (x₀ + ((0 : ℕ) : ℝ)))
        ≤ hgrow * lam * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hNb (mul_nonneg (by linarith) hlam0.le)
    calc (((Finset.range N).image K).card : ℝ)
        ≤ ((K (N - 1) - K 0 : ℤ) : ℝ) + 1 := hcard
      _ ≤ 2 * N * hgrow * lam + 3 := by linarith
  calc ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ v ∈ (Finset.range N).image K,
          ‖∑ n ∈ (Finset.range N).filter (fun n => K n = v),
              Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le_sum_image_fibers _ K N
    _ ≤ ∑ _v ∈ (Finset.range N).image K, (3 / Real.sqrt lam + 1) :=
        Finset.sum_le_sum hfibre
    _ = (((Finset.range N).image K).card : ℝ) * (3 / Real.sqrt lam + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * N * hgrow * lam + 3) * (3 / Real.sqrt lam + 1) := by
        apply mul_le_mul_of_nonneg_right himage
        positivity

/-- The second-derivative test, expanded form: `‖S‖ ≤ 8·N·h·√λ + 12/√λ`. -/
theorem second_derivative_test' (g g' g'' : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    {lam hgrow : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hd1 : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), HasDerivAt g (g' x) x)
    (hd2 : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), HasDerivAt g' (g'' x) x)
    (hlo : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), lam ≤ g'' x)
    (hhi : ∀ x ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)), g'' x ≤ hgrow * lam) :
    ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ 8 * N * hgrow * Real.sqrt lam + 12 / Real.sqrt lam := by
  have hmain := second_derivative_test g g' g'' x₀ N hN hlam0 hlam1 hd1 hd2 hlo hhi
  have hsq0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hsq1 : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr hlam1
  have hsqsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam0.le
  have hinv : Real.sqrt lam * (Real.sqrt lam)⁻¹ = 1 := mul_inv_cancel₀ hsq0.ne'
  have hx0 : x₀ ∈ Set.Icc x₀ (x₀ + ((N - 1 : ℕ) : ℝ)) :=
    ⟨le_refl x₀, le_add_of_nonneg_right (Nat.cast_nonneg _)⟩
  have hgrow1 : 1 ≤ hgrow := by
    have h1 := hlo x₀ hx0
    have h2 := hhi x₀ hx0
    nlinarith [hlam0]
  have hlam_le : lam ≤ Real.sqrt lam := by nlinarith [hsq0, hsq1, hsqsq]
  have hNh0 : (0 : ℝ) ≤ 2 * (N : ℝ) * hgrow := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : (0 : ℝ) ≤ 2 * (N : ℝ) := by linarith
    exact mul_nonneg h1 (by linarith)
  have hterm : 2 * (N : ℝ) * hgrow * lam ≤ 2 * (N : ℝ) * hgrow * Real.sqrt lam :=
    mul_le_mul_of_nonneg_left hlam_le hNh0
  have h3 : (3 : ℝ) ≤ 3 / Real.sqrt lam := by
    have h1 : (1 : ℝ) ≤ (Real.sqrt lam)⁻¹ := by
      have ht : (0 : ℝ) ≤ (Real.sqrt lam)⁻¹ := inv_nonneg.mpr hsq0.le
      nlinarith [hsq1, hinv]
    rw [div_eq_mul_inv]
    linarith
  have hexp : (2 * (N : ℝ) * hgrow * lam + 3) * (3 / Real.sqrt lam + 1)
      = 6 * (N : ℝ) * hgrow * Real.sqrt lam + 2 * (N : ℝ) * hgrow * lam
        + 9 / Real.sqrt lam + 3 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (-(6 * (N : ℝ) * hgrow * (Real.sqrt lam)⁻¹)) * hsqsq
      + (6 * (N : ℝ) * hgrow * Real.sqrt lam) * hinv
  calc ‖∑ n ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * g (x₀ + n) : ℝ) : ℂ) * Complex.I)‖
      ≤ (2 * N * hgrow * lam + 3) * (3 / Real.sqrt lam + 1) := hmain
    _ = 6 * (N : ℝ) * hgrow * Real.sqrt lam + 2 * (N : ℝ) * hgrow * lam
        + 9 / Real.sqrt lam + 3 := hexp
    _ ≤ 8 * N * hgrow * Real.sqrt lam + 12 / Real.sqrt lam := by
        have ha : 9 / Real.sqrt lam + 3 / Real.sqrt lam = 12 / Real.sqrt lam := by
          ring
        linarith [hterm, h3]

end RHTower.Sieve
