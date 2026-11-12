import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormOnStepPacketsIsTheChargesAPotentialAndADirichletForm
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The neutral part of a block and a far window is minus the product of their charges

Let `a ≥ 1` be a block and `1 ≤ c ≤ d`. The neutral part of the block matrix, summed over the
blocks of the far window `(Mc, Md]` against the block `a`, per point of the scale, tends to
minus the degree of `a` times the length of the window
(`tendsto_sum_Ico_neutralBlock_div`):

  `(1/M) Σ_{Mc ≤ l < Md} N(a, l) → −(d − c) · d(a)`.

For `a < l` the neutral part is minus the jet minus the contact (`neutralBlock_of_lt`).

* **Jets.** The second difference of `n log n` is at most `2/n` (`xLogXDiff_le`:
  `log(1 + 1/n) ≤ 1/n` and `log(1 − 1/n) ≤ −1/n`), so the jets of the window stay bounded
  (`sum_Ico_blockJet_le`).
* **Contacts.** The graph of the floor map `l ↦ ⌊l/k⌋` is the increment of the overlap
  `(l/k − a)⁺ − (l/k − a − 1)⁺`, so the contacts of the window telescope
  (`sum_Ico_floorContact`) to a difference of `Σ_k Λ(k)(y/k − x)⁺`
  `= y Σ_{k ≤ y/x} Λ(k)/k − x ψ(y/x)` (`contactSum_eq`). By Mertens' theorem with Euler's
  constant and the prime number theorem, `Σ_k Λ(k)[(y/k − a)⁺ − (y/k − a − 1)⁺]/y` tends to
  `log((a + 1)/a)` (`tendsto_contactGap_div`).

Beyond the ratio of the two blocks the contacts do not depend on the cutoff
(`neutralBlock_eq_of_le`).
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The cutoff of the contacts -/

/-- Beyond the ratio of the two blocks the contacts do not depend on the cutoff. -/
theorem floorContact_eq_of_le {Q Q' a b : ℕ} (hQ : Q ≤ Q') (hb : b < (Q + 1) * a) :
    floorContact Q' a b = floorContact Q a b := by
  unfold floorContact
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hQ) fun k hk hk' => ?_).symm
  have hkQ : Q + 1 ≤ k := by
    by_contra h
    exact hk' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, by omega⟩)
  refine if_neg fun hdiv => ?_
  have h1 : a * k ≤ b := by
    rw [← hdiv]
    exact Nat.div_mul_le_self b k
  have hb' : b < a * (Q + 1) := by
    rw [Nat.mul_comm]
    exact hb
  exact absurd ((Nat.mul_le_mul_left a hkQ).trans h1) (not_le.mpr hb')

theorem neutralBlock_eq_of_le {Q Q' a b : ℕ} (hQ : Q ≤ Q')
    (hab : max a b < (Q + 1) * min a b) : neutralBlock Q' a b = neutralBlock Q a b := by
  unfold neutralBlock blockMatrix
  rw [floorContact_eq_of_le hQ hab]

/-- For `a < b` the neutral part is minus the jet minus the contact. -/
theorem neutralBlock_of_lt {a b : ℕ} (hab : a < b) (Q : ℕ) :
    neutralBlock Q a b = -blockJet a b - floorContact Q a b := by
  rw [neutralBlock, blockMatrix_of_lt hab]
  ring

/-! ### The jets of a far window are bounded -/

/-- The second difference of `n log n` at `n ≥ 1` is at most `2/n`. -/
theorem xLogXDiff_le {n : ℕ} (hn : 1 ≤ n) : xLogXDiff n ≤ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e3 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  -- `log(n + 1) ≤ log n + 1/n`
  have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log n + 1 / n := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at h
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have h1' := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  -- `(n − 1) log(n − 1) ≤ (n − 1)(log n − 1/n)`
  have h2 : ((n - 1 : ℕ) : ℝ) * Real.log ((n - 1 : ℕ) : ℝ) ≤
      ((n : ℝ) - 1) * (Real.log n - 1 / n) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
    rw [hcast]
    rcases Nat.eq_or_lt_of_le hn with h | h
    · rw [← h]
      simp
    · have hm : (0 : ℝ) < (n : ℝ) - 1 := by
        have : (1 : ℝ) < n := by exact_mod_cast h
        linarith
      have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) - 1) / n by positivity)
      rw [Real.log_div hm.ne' hn0.ne'] at hl
      have e : ((n : ℝ) - 1) / n - 1 = -(1 / n) := by field_simp; ring
      exact mul_le_mul_of_nonneg_left (by linarith) hm.le
  have e4 : ((n : ℝ) + 1) * (Real.log n + 1 / n) - 2 * (n * Real.log n) +
      ((n : ℝ) - 1) * (Real.log n - 1 / n) = 2 / n := by ring
  unfold xLogXDiff xLogX
  rw [e3]
  linarith

theorem blockJet_nonneg_of_lt {a l : ℕ} (hal : a < l) : 0 ≤ blockJet a l := by
  have h1 := xLogXDiff_pos (n := a + l + 1) (by omega)
  have h2 := xLogXDiff_pos (n := l - a) (by omega)
  unfold blockJet
  linarith

/-- The jet of two blocks is at most twice the inverse of their distance. -/
theorem blockJet_le {a l : ℕ} (hal : a < l) : blockJet a l ≤ 2 / ((l : ℝ) - a) := by
  have hla : (0 : ℝ) < (l : ℝ) - a := sub_pos.mpr (by exact_mod_cast hal)
  have h1 := xLogXDiff_le (n := a + l + 1) (by omega)
  have h2 := xLogXDiff_le (n := l - a) (by omega)
  have c2 : ((l - a : ℕ) : ℝ) = (l : ℝ) - a := Nat.cast_sub hal.le
  have h3 : (2 : ℝ) / ((a + l + 1 : ℕ) : ℝ) ≤ 2 / ((l : ℝ) - a) := by
    apply div_le_div_of_nonneg_left (by norm_num) hla
    push_cast
    linarith [show (0 : ℝ) ≤ a from Nat.cast_nonneg a]
  rw [c2] at h2
  unfold blockJet
  linarith

/-- **The jets between a block and a window above it** are at most the length of the window
times twice the inverse of the distance. -/
theorem sum_Ico_blockJet_le {a L₁ L₂ : ℕ} (hL : a < L₁) (h12 : L₁ ≤ L₂) :
    ∑ l ∈ Ico L₁ L₂, blockJet a l ≤ ((L₂ : ℝ) - L₁) * (2 / ((L₁ : ℝ) - a)) := by
  have hLa : (0 : ℝ) < (L₁ : ℝ) - a := sub_pos.mpr (by exact_mod_cast hL)
  have hterm : ∀ l ∈ Ico L₁ L₂, blockJet a l ≤ 2 / ((L₁ : ℝ) - a) := fun l hl => by
    have hl1 := (Finset.mem_Ico.mp hl).1
    refine (blockJet_le (lt_of_lt_of_le hL hl1)).trans ?_
    apply div_le_div_of_nonneg_left (by norm_num) hLa
    have : (L₁ : ℝ) ≤ l := by exact_mod_cast hl1
    linarith
  have h := Finset.sum_le_card_nsmul _ _ _ hterm
  rwa [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub h12] at h

/-! ### The contacts of a far window -/

/-- The contacts of the windows `(x, y]`: `Σ_k Λ(k) (y/k − x)⁺`. -/
def contactSum (Q : ℕ) (x y : ℝ) : ℝ := ∑ k ∈ Icc 2 Q, (Λ k : ℝ) * max (y / k - x) 0

/-- **The contacts of a window in closed form**: `y Σ_{k ≤ y/x} Λ(k)/k − x ψ(y/x)`. -/
theorem contactSum_eq {Q : ℕ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (hQ : ⌊y / x⌋₊ ≤ Q) :
    contactSum Q x y =
      y * (∑ k ∈ Icc 0 ⌊y / x⌋₊, (Λ k : ℝ) / k) - x * Chebyshev.psi (y / x) := by
  have hyx : 0 ≤ y / x := div_nonneg hy hx.le
  have hterm : ∀ k : ℕ, (Λ k : ℝ) * max (y / k - x) 0 =
      if k ≤ ⌊y / x⌋₊ then y * ((Λ k : ℝ) / k) - x * (Λ k : ℝ) else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    by_cases hle : k ≤ ⌊y / x⌋₊
    · have h1 : (k : ℝ) ≤ y / x := (Nat.le_floor_iff hyx).mp hle
      have h2 : x ≤ y / k := by
        rw [le_div_iff₀ hk0]
        have := (le_div_iff₀ hx).mp h1
        linarith
      rw [if_pos hle, max_eq_left (sub_nonneg.mpr h2)]
      ring
    · have h1 : y / x < k := (Nat.floor_lt hyx).mp (not_le.mp hle)
      have h2 : y / k ≤ x := by
        rw [div_le_iff₀ hk0]
        have := (div_lt_iff₀ hx).mp h1
        linarith
      rw [if_neg hle, max_eq_right (sub_nonpos.mpr h2), mul_zero]
  have h01 : ∀ k ∈ Icc 0 Q, k ∉ Icc 2 Q → (Λ k : ℝ) * max (y / k - x) 0 = 0 := by
    intro k hk hk'
    have hk2 : k < 2 := by
      by_contra h
      exact hk' (Finset.mem_Icc.mpr ⟨not_lt.mp h, (Finset.mem_Icc.mp hk).2⟩)
    interval_cases k <;> simp
  have hset : (Icc 0 Q).filter (fun k => k ≤ ⌊y / x⌋₊) = Icc 0 ⌊y / x⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [contactSum, Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 2)) h01,
    Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_filter, hset,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Chebyshev.psi_eq_sum_Icc]

/-- The graph of the floor map `l ↦ ⌊l/k⌋` over the blocks `L₁ ≤ l < L₂` is the increment of
the overlap `(l/k − a)⁺ − (l/k − a − 1)⁺`. -/
theorem sum_Ico_floor_indicator {k : ℕ} (hk : 1 ≤ k) (a : ℕ) {L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    ∑ l ∈ Ico L₁ L₂, (if l / k = a then 1 / (k : ℝ) else 0) =
      (max ((L₂ : ℝ) / k - a) 0 - max ((L₂ : ℝ) / k - ((a : ℝ) + 1)) 0) -
        (max ((L₁ : ℝ) / k - a) 0 - max ((L₁ : ℝ) / k - ((a : ℝ) + 1)) 0) := by
  induction L₂, hL using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih, ← max_mixed hk a n]
    push_cast
    ring

/-- **The contacts between a block and a window above it telescope.** -/
theorem sum_Ico_floorContact (Q a : ℕ) {L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    ∑ l ∈ Ico L₁ L₂, floorContact Q a l =
      (contactSum Q a L₂ - contactSum Q ((a : ℝ) + 1) L₂) -
        (contactSum Q a L₁ - contactSum Q ((a : ℝ) + 1) L₁) := by
  unfold floorContact contactSum
  rw [Finset.sum_comm]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  have e : ∑ l ∈ Ico L₁ L₂, (if l / k = a then (Λ k : ℝ) / k else 0) =
      (Λ k : ℝ) * ∑ l ∈ Ico L₁ L₂, (if l / k = a then 1 / (k : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · ring
    · ring
  rw [e, sum_Ico_floor_indicator hk1 a hL]
  ring

/-- The contacts of the block `a` with the windows up to `y`: the difference of the contacts of
the windows `(a, y]` and `(a + 1, y]`, in closed form. -/
def contactGap (a : ℕ) (y : ℝ) : ℝ :=
  (y * (∑ k ∈ Icc 0 ⌊y / a⌋₊, (Λ k : ℝ) / k) - a * Chebyshev.psi (y / a)) -
    (y * (∑ k ∈ Icc 0 ⌊y / ((a : ℝ) + 1)⌋₊, (Λ k : ℝ) / k) -
      ((a : ℝ) + 1) * Chebyshev.psi (y / ((a : ℝ) + 1)))

theorem contactSum_sub_eq_contactGap {Q a : ℕ} (ha : 1 ≤ a) {y : ℝ} (hy : 0 ≤ y)
    (hQ : ⌊y / a⌋₊ ≤ Q) :
    contactSum Q a y - contactSum Q ((a : ℝ) + 1) y = contactGap a y := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hle : y / ((a : ℝ) + 1) ≤ y / a :=
    div_le_div_of_nonneg_left hy ha0 (by linarith)
  rw [contactSum_eq ha0 hy hQ,
    contactSum_eq (by linarith) hy ((Nat.floor_le_floor hle).trans hQ), contactGap]

/-- **Mertens and the prime number theorem for the contacts of a block**: per point of the
scale they tend to the degree of the block. -/
theorem tendsto_contactGap_div {a : ℕ} (ha : 1 ≤ a) :
    Tendsto (fun y : ℝ => contactGap a y / y) atTop (𝓝 (blockDegree a)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hL := _root_.RHTower.tendsto_real_sum_vonMangoldt_div_sub_log
  have hψ := _root_.RHTower.tendsto_psi_div_self
  have ta : Tendsto (fun y : ℝ => y / a) atTop atTop := tendsto_id.atTop_div_const ha0
  have tb : Tendsto (fun y : ℝ => y / ((a : ℝ) + 1)) atTop atTop :=
    tendsto_id.atTop_div_const ha1
  have hlim := ((((hL.comp ta).sub (hL.comp tb)).add_const (blockDegree a)).sub
    (hψ.comp ta)).add (hψ.comp tb)
  have hval : -Real.eulerMascheroniConstant - -Real.eulerMascheroniConstant + blockDegree a -
      1 + 1 = blockDegree a := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hy0 := hy.ne'
  have ha0' := ha0.ne'
  have ha1' := ha1.ne'
  have hlog : blockDegree a = Real.log (y / a) - Real.log (y / ((a : ℝ) + 1)) := by
    rw [Real.log_div hy0 ha0', Real.log_div hy0 ha1', blockDegree]
    push_cast
    ring
  simp only [Function.comp, contactGap]
  rw [hlog]
  field_simp
  ring

/-! ### A block and a far window -/

/-- **The neutral part of a block and a far window**: per point of the scale it tends to minus
the degree of the block times the length of the window. -/
theorem tendsto_sum_Ico_neutralBlock_div {a : ℕ} (ha : 1 ≤ a) {c d : ℕ} (hc : 1 ≤ c)
    (hcd : c ≤ d) (Q : ℕ → ℕ) (hQ : ∀ᶠ M : ℕ in atTop, M * d ≤ Q M) :
    Tendsto (fun M : ℕ => (∑ l ∈ Ico (M * c) (M * d), neutralBlock (Q M) a l) / M) atTop
      (𝓝 (-(((d : ℝ) - c) * blockDegree a))) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hd1 : 1 ≤ d := hc.trans hcd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hG := tendsto_contactGap_div ha
  have hmul : ∀ e : ℕ, 1 ≤ e → Tendsto (fun M : ℕ => ((M * e : ℕ) : ℝ)) atTop atTop :=
    fun e he => tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_right M he) tendsto_id)
  have hGd := hG.comp (hmul d hd1)
  have hGc := hG.comp (hmul c hc)
  -- the jets of the window, per point of the scale, tend to zero
  have hJ : Tendsto (fun M : ℕ => (∑ l ∈ Ico (M * c) (M * d), blockJet a l) / M) atTop
      (𝓝 0) := by
    have hden : Tendsto (fun M : ℕ => (M : ℝ) * c - a) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hc0
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(a : ℝ)) h
    have hup : Tendsto (fun M : ℕ => 2 * ((d : ℝ) - c) / ((M : ℝ) * c - a)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop a] with M hM
      have hMc : a < M * c := lt_of_lt_of_le hM (Nat.le_mul_of_pos_right M hc)
      exact div_nonneg (Finset.sum_nonneg fun l hl =>
        blockJet_nonneg_of_lt (lt_of_lt_of_le hMc (Finset.mem_Ico.mp hl).1)) (Nat.cast_nonneg M)
    · filter_upwards [eventually_gt_atTop a] with M hM
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      have hMc : a < M * c := lt_of_lt_of_le hM (Nat.le_mul_of_pos_right M hc)
      have hMc' : (0 : ℝ) < (M : ℝ) * c - a := by
        have : ((a : ℕ) : ℝ) < ((M * c : ℕ) : ℝ) := by exact_mod_cast hMc
        push_cast at this
        linarith
      have h := sum_Ico_blockJet_le hMc (Nat.mul_le_mul_left M hcd)
      have h' := div_le_div_of_nonneg_right h hM0.le
      refine h'.trans (le_of_eq ?_)
      push_cast
      field_simp
  -- the neutral part of the window: jets and the contact gap
  have key : ∀ J gd gc Md Mc Mr dr cr : ℝ, Md = Mr * dr → Mc = Mr * cr → 0 < Mr → 0 < dr →
      0 < cr → (-J - (gd - gc)) / Mr = -(J / Mr) - (dr * (gd / Md) - cr * (gc / Mc)) := by
    intro J gd gc Md Mc Mr dr cr h1 h2 h3 h4 h5
    subst h1 h2
    have := h3.ne'
    have := h4.ne'
    have := h5.ne'
    field_simp
  have hmain : ∀ᶠ M : ℕ in atTop,
      (∑ l ∈ Ico (M * c) (M * d), neutralBlock (Q M) a l) / M =
        -((∑ l ∈ Ico (M * c) (M * d), blockJet a l) / M) -
          ((d : ℝ) * (contactGap a ((M * d : ℕ) : ℝ) / ((M * d : ℕ) : ℝ)) -
            c * (contactGap a ((M * c : ℕ) : ℝ) / ((M * c : ℕ) : ℝ))) := by
    filter_upwards [hQ, eventually_gt_atTop a] with M hQM hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hMc : a < M * c := lt_of_lt_of_le hM (Nat.le_mul_of_pos_right M hc)
    have hle : M * c ≤ M * d := Nat.mul_le_mul_left M hcd
    have hsum : ∑ l ∈ Ico (M * c) (M * d), neutralBlock (Q M) a l =
        -(∑ l ∈ Ico (M * c) (M * d), blockJet a l) -
          ∑ l ∈ Ico (M * c) (M * d), floorContact (Q M) a l := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l hl =>
        neutralBlock_of_lt (lt_of_lt_of_le hMc (Finset.mem_Ico.mp hl).1) _
    -- the cutoff contains every contact of the window
    have hfl : ∀ e : ℕ, e ≤ d → ⌊((M * e : ℕ) : ℝ) / a⌋₊ ≤ Q M := by
      intro e he
      have h1 : ((M * e : ℕ) : ℝ) / a ≤ ((M * e : ℕ) : ℝ) :=
        div_le_self (Nat.cast_nonneg _) (by exact_mod_cast ha)
      have h2 := Nat.floor_le_floor h1
      rw [Nat.floor_natCast] at h2
      exact h2.trans ((Nat.mul_le_mul_left M he).trans hQM)
    rw [hsum, sum_Ico_floorContact (Q M) a hle,
      contactSum_sub_eq_contactGap ha (Nat.cast_nonneg _) (hfl d le_rfl),
      contactSum_sub_eq_contactGap ha (Nat.cast_nonneg _) (hfl c hcd)]
    exact key _ _ _ _ _ _ _ _ (by push_cast; ring) (by push_cast; ring) hM0 hd0 hc0
  have hlim := hJ.neg.sub ((hGd.const_mul (d : ℝ)).sub (hGc.const_mul (c : ℝ)))
  have hval : -(0 : ℝ) - ((d : ℝ) * blockDegree a - c * blockDegree a) =
      -(((d : ℝ) - c) * blockDegree a) := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmain] with M hM
  exact hM.symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
