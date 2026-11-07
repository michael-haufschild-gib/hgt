import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheDatumRegionLiesLeftOfTheResidueLine

/-!
# The cone bounds the second moment of its weights and has positive support density

The narrow pole-free resonator `Σ_m c_m g_w'(· − log m + (log N)/2)` is a window test for every real coefficient
vector, and on a pole-free test the datum energy sees neither the pole weight nor more than `|s|` of the
conductor. So every point of every datum cone satisfies the multiplicative Toeplitz inequality
(`cone_toeplitz_bound`)

  `2 Σ_{2 ≤ n ≤ N} λ(n) n^{−1/2} Σ_m c(nm) c(m) ≤ (log N + C_s) Σ_m c(m)²`,  `½ log N + 1 ≤ c`,

with no sign condition on `c`. Star resonators on primitive sets turn it into a second-moment law.

* **Second moment** (`sum_sq_Ioc_le`). `Σ_{N < n ≤ 2N} λ(n)² ≤ 2N (log 2N + C_s)²`, for every pole weight and
  conductor, at every scale of the box. The box allows `λ(n)² ≍ n (log n)²` at each `n`; the cone allows it only at
  `O((log N)²)` of the integers of a dyadic block (`card_large_le`).
* **First moment** (`sum_abs_Ioc_le`). `Σ_{N < n ≤ 2N} |λ(n)| ≤ (3/2) N (log 2N + C_s + 1)`.
* **Positive support density** (`local_floor_le_card_mul`, `exists_card_pos_ge`). Against the floor of the local
  law, Cauchy–Schwarz on the positive part gives, for `β ≥ 0`,
  `βJ²(e^a − 2) − D_s ≤ e^{1/6} ∫φ · √#P · (log M + C_s)`, where `P` is the set of `n` with `|log n − 2a| < 2r`
  and `λ(n) > 0`. Every point of `𝒜(c)` is positive on at least `κ X/(log X)²` integers of
  `|log(n/X)| < 2r`, for `X₀ ≤ X ≤ e^{2c−4}`.

The support bound is Chebyshev's lower bound `π(2X) − π(X) ≫ X/log X` up to one logarithm, for every weight
system positive at the window: positivity forces a dense positive support, not only a correct mean.

What this does not say about `ζ`: the bounds hold for cone points; `Λ` is one only under RH. They are uniform in
`c` only through the cone, which is empty off RH.
-/

open MeasureTheory Filter Topology Set
open scoped Nat Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.RHTower.WeilOneSided
open _root_.RHTower.WeilPoleWeight _root_.RHTower.OddSector _root_.RHTower.EvenSector
open _root_.RHTower.ResonatorProfile _root_.Zeta23

/-! ### The Toeplitz inequality on the cone -/

/-- The Toeplitz constant at conductor `s`. -/
def coneToeplitzConst (s : ℝ) : ℝ := Real.log 2 + 9 / 2 + oddProfileRatio / 2 + |s|

theorem coneToeplitzConst_pos (s : ℝ) : 0 < coneToeplitzConst s := by
  unfold coneToeplitzConst
  have := oddProfileRatio_nonneg
  have := Real.log_two_gt_d9
  have := abs_nonneg s
  linarith

/-- **The multiplicative Toeplitz inequality on every datum cone**, for real coefficients of any sign. -/
theorem cone_toeplitz_bound {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) {N : ℕ}
    (hN : 1 ≤ N) (hNc : Real.log N / 2 + 1 ≤ c) (cf : ℕ → ℝ) (hcf : ∀ m, N < m → cf m = 0) :
    2 * ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n * ∑ m ∈ Finset.Icc 1 N, cf (n * m) * cf m ≤
      (Real.log N + coneToeplitzConst s) * ∑ m ∈ Finset.Icc 1 N, cf m ^ 2 := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  set w : ℝ := 1 / ((N : ℝ) + 1) with hw_def
  have hw : 0 < w := by positivity
  have hw1 : w ≤ 1 := by
    rw [hw_def, div_le_one hN1]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hcC : ∀ m, N < m → (cf m : ℂ) = 0 := fun m hm => by rw [hcf m hm, Complex.ofReal_zero]
  have hq0 : 0 < ∫ u, gR' w u ^ 2 :=
    lt_of_lt_of_le (div_pos integral_d3_sq_pos (by positivity)) (integral_gR'_sq_ge hw)
  have hK : w ^ 2 * ∫ u, deriv (gR' w) u ^ 2 ≤ oddProfileRatio * ∫ u, gR' w u ^ 2 := by
    rw [deriv_gR']; exact sq_mul_integral_gR''_le hw hw1
  have hW := integral_weilAtomSymbol_resonator_ge h (L := N) (by linarith) (fun m => (cf m : ℂ))
  have hb := toeplitz_bound_of_profile_slack hN (fun m => (cf m : ℂ)) hcC (contDiff_gR' w 3)
    (fun u hu => gR'_eq_zero hw hu) hq0 hK hW
  have hl : ∀ n, (∑ m ∈ Finset.Icc 1 N, (cf (n * m) : ℂ) * conj (cf m : ℂ)).re =
      ∑ m ∈ Finset.Icc 1 N, cf (n * m) * cf m := fun n => by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hr : ∑ m ∈ Finset.Icc 1 N, ‖(cf m : ℂ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, cf m ^ 2 :=
    Finset.sum_congr rfl fun m _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hl, hr] at hb
  have e : Real.log N + (Real.log 2 + 9 / 2 + oddProfileRatio / 2) + |s| =
      Real.log N + coneToeplitzConst s := by unfold coneToeplitzConst; ring
  rw [e] at hb
  exact hb

/-! ### The second moment -/

/-- **The cone bounds the weights in mean square on primitive sets.** -/
theorem sum_sq_div_le_of_primitive {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) {N : ℕ}
    (hN : 1 ≤ N) (hNc : Real.log N / 2 + 1 ≤ c) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 2 N)
    (hprim : IsPrimitiveSet S) :
    ∑ n ∈ S, lam n ^ 2 / n ≤ (Real.log N + coneToeplitzConst s) ^ 2 := by
  set B := Real.log N + coneToeplitzConst s with hBdef
  have hB : 0 < B := by
    have := Real.log_natCast_nonneg N; have := coneToeplitzConst_pos s; rw [hBdef]; linarith
  set Q := ∑ n ∈ S, lam n ^ 2 / n with hQ
  have key : ∀ t : ℝ, 2 * t * Q ≤ B * (1 + t ^ 2 * Q) := by
    intro t
    set cf : ℕ → ℝ := fun m => if m = 1 then 1 else if m ∈ S then t * lam m / Real.sqrt m else 0
      with hc
    have hcN : ∀ m, N < m → cf m = 0 := by
      intro m hm
      have h1 : m ≠ 1 := by omega
      have h2 : m ∉ S := fun h' => by have := (Finset.mem_Icc.mp (hS h')).2; omega
      simp [hc, h1, h2]
    have hb := cone_toeplitz_bound h hN hNc cf hcN
    have hinner : ∀ n ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 1 N, cf (n * m) * cf m = if n ∈ S then t * lam n / Real.sqrt n else 0 := by
      intro n hn
      obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hrest : ∑ m ∈ (Finset.Icc 1 N).erase 1, cf (n * m) * cf m = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        obtain ⟨hm1, hmI⟩ := Finset.mem_erase.mp hm
        by_cases hmS : m ∈ S
        · have hnm1 : n * m ≠ 1 := by
            have := (Finset.mem_Icc.mp hmI).1; nlinarith
          have hnmS : n * m ∉ S := fun h' => hprim _ h' m hmS n hn2 rfl
          simp [hc, hnm1, hnmS]
        · simp [hc, hm1, hmS]
      rw [hrest, add_zero, mul_one]
      have hn1 : n ≠ 1 := by omega
      by_cases hnS : n ∈ S
      · simp [hc, hn1, hnS]
      · simp [hc, hn1, hnS]
    have hmass : ∑ m ∈ Finset.Icc 1 N, cf m ^ 2 = 1 + t ^ 2 * Q := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      have hS' : S ⊆ (Finset.Icc 1 N).erase 1 := fun n hn => by
        have := Finset.mem_Icc.mp (hS hn)
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, this.2⟩⟩
      rw [← Finset.sum_subset hS' (fun m hm hmS => by
        have hm1 := (Finset.mem_erase.mp hm).1
        simp [hc, hm1, hmS]), hQ, Finset.mul_sum]
      congr 1
      · simp [hc]
      · refine Finset.sum_congr rfl fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp (hS hn)).1
        have hn1 : n ≠ 1 := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        simp only [hc, hn1, hn, if_false, if_true, div_pow, mul_pow, Real.sq_sqrt hn0.le]
        ring
    have hlhs : ∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        ∑ m ∈ Finset.Icc 1 N, cf (n * m) * cf m = t * Q := by
      rw [Finset.sum_congr rfl fun n hn => by rw [hinner n hn], hQ, Finset.mul_sum]
      rw [← Finset.sum_subset hS (fun n _ hnS => by simp [hnS])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 := (Finset.mem_Icc.mp (hS hn)).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      rw [if_pos hn, show lam n / Real.sqrt n * (t * lam n / Real.sqrt n) =
        t * (lam n ^ 2 / (Real.sqrt n * Real.sqrt n)) by ring, hsq]
    rw [hlhs, hmass] at hb
    linarith
  have h1 := key (1 / B)
  have e1 : B * (2 * (1 / B) * Q) = 2 * Q := by field_simp
  have e2 : B * (B * (1 + (1 / B) ^ 2 * Q)) = B ^ 2 + Q := by field_simp
  have h2 := mul_le_mul_of_nonneg_left h1 hB.le
  rw [e1, e2] at h2
  linarith

/-- **The second moment on dyadic blocks.** `Σ_{N < n ≤ 2N} λ(n)² ≤ 2N (log 2N + C_s)²`. -/
theorem sum_sq_Ioc_le {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) {N : ℕ} (hN : 1 ≤ N)
    (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) :
    ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 ≤
      (2 * N : ℕ) * (Real.log (2 * N : ℕ) + coneToeplitzConst s) ^ 2 := by
  have hsub : Finset.Ioc N (2 * N) ⊆ Finset.Icc 2 (2 * N) := fun n hn => by
    rw [Finset.mem_Ioc] at hn; rw [Finset.mem_Icc]; omega
  have hprim : IsPrimitiveSet (Finset.Ioc N (2 * N)) := by
    intro m hm m' hm' k hk heq
    rw [Finset.mem_Ioc] at hm hm'
    have : k * m' ≥ 2 * (N + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hQ := sum_sq_div_le_of_primitive h (N := 2 * N) (by omega) hNc hsub hprim
  have h2N : (0 : ℝ) < (2 * N : ℕ) := by exact_mod_cast (show 0 < 2 * N by omega)
  calc ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2
      = (2 * N : ℕ) * ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / (2 * N : ℕ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by field_simp
    _ ≤ (2 * N : ℕ) * ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 / n := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) h2N.le
        rw [Finset.mem_Ioc] at hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hn0 (by exact_mod_cast hn.2)
    _ ≤ _ := mul_le_mul_of_nonneg_left hQ h2N.le

/-- **The first moment on dyadic blocks.** -/
theorem sum_abs_Ioc_le {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) {N : ℕ} (hN : 1 ≤ N)
    (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) :
    ∑ n ∈ Finset.Ioc N (2 * N), |lam n| ≤
      3 / 2 * N * (Real.log (2 * N : ℕ) + coneToeplitzConst s + 1) := by
  have hL : 0 ≤ Real.log (2 * N : ℕ) + coneToeplitzConst s := by
    have := Real.log_natCast_nonneg (2 * N); have := coneToeplitzConst_pos s; linarith
  exact sum_abs_Ioc_le_of_sum_sq hL (sum_sq_Ioc_le h hN hNc)

/-- **Large weights are sparse.** At most `2N (log 2N + C_s)²/T²` integers of `(N, 2N]` carry `|λ(n)| ≥ T`. -/
theorem card_large_le {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) {N : ℕ} (hN : 1 ≤ N)
    (hNc : Real.log (2 * N : ℕ) / 2 + 1 ≤ c) {T : ℝ} (hT : 0 < T) :
    (((Finset.Ioc N (2 * N)).filter fun n => T ≤ |lam n|).card : ℝ) * T ^ 2 ≤
      (2 * N : ℕ) * (Real.log (2 * N : ℕ) + coneToeplitzConst s) ^ 2 := by
  refine le_trans ?_ (sum_sq_Ioc_le h hN hNc)
  calc (((Finset.Ioc N (2 * N)).filter fun n => T ≤ |lam n|).card : ℝ) * T ^ 2
      = ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => T ≤ |lam n|), T ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.Ioc N (2 * N)).filter (fun n => T ≤ |lam n|), lam n ^ 2 := by
        refine Finset.sum_le_sum fun n hn => ?_
        have := (Finset.mem_filter.mp hn).2
        rw [← sq_abs (lam n)]
        exact pow_le_pow_left₀ hT.le this 2
    _ ≤ ∑ n ∈ Finset.Ioc N (2 * N), lam n ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun n _ _ => sq_nonneg _

/-! ### Positive support density -/

/-- The positive support of `λ` in the log-window `|log n − 2a| < r₀`, inside `[2, M]`. -/
def posSupport (lam : ℕ → ℝ) (a : ℝ) (M : ℕ) : Finset ℕ :=
  (Finset.Icc 2 M).filter fun n => |Real.log n - 2 * a| < kerRad ∧ 0 < lam n

theorem isPrimitiveSet_posSupport (lam : ℕ → ℝ) (a : ℝ) (M : ℕ) :
    IsPrimitiveSet (posSupport lam a M) := by
  intro m hm m' hm' k hk heq
  rw [posSupport, Finset.mem_filter, Finset.mem_Icc] at hm hm'
  have hm0 : (0 : ℝ) < m' := by exact_mod_cast (show 0 < m' by omega)
  have hk2 : (2 : ℝ) * m' ≤ m := by rw [heq]; push_cast; exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast hk) hm0.le
  have hlog : Real.log 2 + Real.log m' ≤ Real.log m := by
    rw [← Real.log_mul (by norm_num) hm0.ne']
    exact Real.log_le_log (by positivity) hk2
  have h1 := (abs_lt.mp hm.2.1)
  have h2 := (abs_lt.mp hm'.2.1)
  have hk := two_mul_kerRad_lt_log_two
  linarith [h1.2, h2.1]

/-- **The local floor against the positive support.** On the cone of `(β, s)`, `β ≥ 0`, for `0 ≤ a`, `a + 2 ≤ c`
and `M = ⌈2e^{2a}⌉`, `βJ²(e^a − 2) − D_s ≤ e^{1/6} ∫φ · √#P · (log M + C_s)` with `P = posSupport λ a M`. -/
theorem local_floor_le_card_mul {β s c : ℝ} {lam : ℕ → ℝ} (h : lam ∈ datumCone β s c) (hβ : 0 ≤ β)
    {a : ℝ} (ha : 0 ≤ a) (hac : a + 2 ≤ c) :
    β * farJ ^ 2 * (Real.exp a - 2) - localDensityConst s ≤
      Real.exp (1 / 6) * farMass * Real.sqrt ((posSupport lam a ⌈2 * Real.exp (2 * a)⌉₊).card) *
        (Real.log ⌈2 * Real.exp (2 * a)⌉₊ + coneToeplitzConst s) := by
  set M : ℕ := ⌈2 * Real.exp (2 * a)⌉₊ with hM
  set P := posSupport lam a M with hP
  have hE1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hMge : 2 * Real.exp (2 * a) ≤ M := Nat.le_ceil _
  have hMlt : (M : ℝ) < 2 * Real.exp (2 * a) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hM1 : 1 ≤ M := by exact_mod_cast (show (1 : ℝ) ≤ M by linarith)
  have hM0 : (0 : ℝ) < M := by linarith
  have hk0 := kerRad_pos
  have hk6 := kerRad_le
  -- the window condition for the second moment
  have hMc : Real.log M / 2 + 1 ≤ c := by
    have h3 : (M : ℝ) ≤ Real.exp (2 * a + 2) := by
      have : Real.exp (2 * a + 2) = Real.exp (2 * a) * Real.exp 2 := Real.exp_add _ _
      have he2 : (7 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        have he := Real.exp_one_gt_d9
        nlinarith
      rw [this]; nlinarith
    have := (Real.log_le_iff_le_exp hM0).mpr h3
    linarith
  -- the floor
  obtain ⟨hlow, -⟩ := farSum_mem_Icc_of_mem_datumCone h ha (by linarith)
  rw [exp_half_sub_sq] at hlow
  have hfloor : β * farJ ^ 2 * (Real.exp a - 2) - localDensityConst s ≤ farSum lam a := by
    have : 0 ≤ β * farJ ^ 2 * Real.exp (-a) := by have := farJ_sq_pos; positivity
    nlinarith
  rw [farSum_eq_finset_sum lam le_rfl hMge] at hfloor
  -- only the positive support contributes positively
  have hle1 : ∑ n ∈ Finset.Icc 2 M, lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
      ∑ n ∈ P, lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) := by
    rw [hP, posSupport, Finset.sum_filter]
    refine Finset.sum_le_sum fun n hn => ?_
    split_ifs with hc
    · exact le_rfl
    · rw [not_and_or, not_lt, not_lt] at hc
      rcases hc with hc | hc
      · rw [farKernel_eq_zero_of_le hc, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc
          (Real.sqrt_nonneg _)) (farKernel_nonneg _)
  -- each term of the positive support
  have hterm : ∀ n ∈ P, lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
      Real.exp (-a) * (Real.exp (1 / 12) * farMass) * lam n := by
    intro n hn
    rw [hP, posSupport, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn2, -⟩, hlog, hpos⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : Real.exp (a - 1 / 12) ≤ Real.sqrt n := by
      rw [show a - 1 / 12 = (2 * a - 1 / 6) / 2 by ring, Real.exp_half]
      refine Real.sqrt_le_sqrt ?_
      rw [← Real.exp_log hn0]
      exact Real.exp_le_exp.mpr (by linarith [(abs_lt.mp hlog).1])
    have hinv : 1 / Real.sqrt n ≤ Real.exp (-a) * Real.exp (1 / 12) := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hn0), ← Real.exp_add]
      calc (1 : ℝ) = Real.exp (-a + 1 / 12) * Real.exp (a - 1 / 12) := by
            rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
        _ ≤ Real.exp (-a + 1 / 12) * Real.sqrt n :=
            mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    have hk := farKernel_le (Real.log n - 2 * a)
    have hk0' := farKernel_nonneg (Real.log n - 2 * a)
    calc lam n / Real.sqrt n * farKernel (Real.log n - 2 * a)
        = lam n * (1 / Real.sqrt n) * farKernel (Real.log n - 2 * a) := by ring
      _ ≤ lam n * (Real.exp (-a) * Real.exp (1 / 12)) * farMass := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hinv hpos.le) hk hk0' ?_
          positivity
      _ = _ := by ring
  have hsum : ∑ n ∈ P, lam n / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
      Real.exp (-a) * (Real.exp (1 / 12) * farMass) * ∑ n ∈ P, lam n := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
  -- Cauchy–Schwarz and the second moment on the primitive set `P`
  have hPsub : P ⊆ Finset.Icc 2 M := Finset.filter_subset _ _
  have hQ := sum_sq_div_le_of_primitive h hM1 hMc hPsub (isPrimitiveSet_posSupport lam a M)
  have hsq2 : ∑ n ∈ P, lam n ^ 2 ≤ Real.exp (2 * a + 1 / 6) * ∑ n ∈ P, lam n ^ 2 / n := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [hP, posSupport, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn2, -⟩, hlog, -⟩ := hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnle : (n : ℝ) ≤ Real.exp (2 * a + 1 / 6) := by
      rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr (by linarith [(abs_lt.mp hlog).2])
    rw [mul_div_assoc', le_div_iff₀ hn0]
    exact mul_le_mul_of_nonneg_left hnle (sq_nonneg _)
  have hCS : (∑ n ∈ P, lam n) ^ 2 ≤ (P.card : ℝ) * ∑ n ∈ P, lam n ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq P (fun _ => (1 : ℝ)) lam
    simpa using this
  set B := Real.log M + coneToeplitzConst s with hB
  have hB0 : 0 ≤ B := by have := Real.log_natCast_nonneg M; have := coneToeplitzConst_pos s; linarith
  have hsumP : ∑ n ∈ P, lam n ≤ Real.sqrt P.card * (Real.exp (a + 1 / 12) * B) := by
    have h1 : (∑ n ∈ P, lam n) ^ 2 ≤ (Real.sqrt P.card * (Real.exp (a + 1 / 12) * B)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (a + 1 / 12) = 2 * a + 1 / 6 := by push_cast; ring
      rw [e]
      calc (∑ n ∈ P, lam n) ^ 2 ≤ (P.card : ℝ) * ∑ n ∈ P, lam n ^ 2 := hCS
        _ ≤ (P.card : ℝ) * (Real.exp (2 * a + 1 / 6) * B ^ 2) := by
            refine mul_le_mul_of_nonneg_left (hsq2.trans ?_) (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le
        _ = _ := by ring
    have h2 : 0 ≤ Real.sqrt P.card * (Real.exp (a + 1 / 12) * B) := by positivity
    exact abs_le_of_sq_le_sq' h1 h2 |>.2
  have hfin : Real.exp (-a) * (Real.exp (1 / 12) * farMass) *
      (Real.sqrt P.card * (Real.exp (a + 1 / 12) * B)) =
      Real.exp (1 / 6) * farMass * Real.sqrt P.card * B := by
    have e : Real.exp (-a) * Real.exp (1 / 12) * Real.exp (a + 1 / 12) = Real.exp (1 / 6) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    calc _ = (Real.exp (-a) * Real.exp (1 / 12) * Real.exp (a + 1 / 12)) * farMass *
          Real.sqrt P.card * B := by ring
      _ = _ := by rw [e]
  have hm0 := farMass_nonneg
  have hmono : Real.exp (-a) * (Real.exp (1 / 12) * farMass) * ∑ n ∈ P, lam n ≤
      Real.exp (-a) * (Real.exp (1 / 12) * farMass) *
        (Real.sqrt P.card * (Real.exp (a + 1 / 12) * B)) :=
    mul_le_mul_of_nonneg_left hsumP (by positivity)
  linarith

theorem farMass_pos : 0 < farMass :=
  lt_of_lt_of_le (nodeBump 2).rIn_pos ((farKernel_ge (t := 0) (by
    rw [abs_zero]; exact (half_pos (nodeBump 2).rIn_pos).le)).trans (farKernel_le 0))

theorem log_ceil_two_exp_le {a : ℝ} (ha : 0 ≤ a) :
    Real.log ⌈2 * Real.exp (2 * a)⌉₊ ≤ 2 * a + 2 := by
  have hE1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  have hMlt : ((⌈2 * Real.exp (2 * a)⌉₊ : ℕ) : ℝ) < 2 * Real.exp (2 * a) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hMge : 2 * Real.exp (2 * a) ≤ ⌈2 * Real.exp (2 * a)⌉₊ := Nat.le_ceil _
  have hM0 : (0 : ℝ) < ⌈2 * Real.exp (2 * a)⌉₊ := by linarith
  have h3 : ((⌈2 * Real.exp (2 * a)⌉₊ : ℕ) : ℝ) ≤ Real.exp (2 * a + 2) := by
    have : Real.exp (2 * a + 2) = Real.exp (2 * a) * Real.exp 2 := Real.exp_add _ _
    have he2 : (7 : ℝ) ≤ Real.exp 2 := by
      have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have he := Real.exp_one_gt_d9
      nlinarith
    rw [this]; nlinarith
  exact (Real.log_le_iff_le_exp hM0).mpr h3

/-- **Positive support density.** There are `κ > 0` and `a₀` such that every point of `𝒜(c)` is positive on at
least `κ e^{2a}/(a + 1)²` integers `n` with `|log n − 2a| < r₀`, for `a₀ ≤ a ≤ c − 2`. -/
theorem exists_card_pos_ge :
    ∃ κ a₀ : ℝ, 0 < κ ∧ ∀ c a : ℝ, ∀ lam ∈ windowCone c, a₀ ≤ a → a + 2 ≤ c →
      κ * Real.exp (2 * a) / (a + 1) ^ 2 ≤ ((posSupport lam a ⌈2 * Real.exp (2 * a)⌉₊).card : ℝ) := by
  set J := farJ ^ 2 with hJ
  have hJ0 : 0 < J := farJ_sq_pos
  set D := localDensityConst 0 with hD
  have hD0 : 0 ≤ D := localDensityConst_nonneg 0
  set m := farMass with hm
  have hm0 : 0 < m := farMass_pos
  set K : ℝ := 2 + coneToeplitzConst 0 with hK
  have hK0 : 0 < K := by have := coneToeplitzConst_pos 0; rw [hK]; linarith
  set Y : ℝ := Real.exp (1 / 6) * m * K with hY
  have hY0 : 0 < Y := by positivity
  refine ⟨(J / 2 / Y) ^ 2, max 0 (Real.log (4 + 2 * D / J)), by positivity,
    fun c a lam hlam ha hac => ?_⟩
  have ha0 : 0 ≤ a := (le_max_left _ _).trans ha
  have hea : 4 + 2 * D / J ≤ Real.exp a := by
    have h1 : Real.log (4 + 2 * D / J) ≤ a := (le_max_right _ _).trans ha
    have h2 : 0 < 4 + 2 * D / J := by positivity
    calc 4 + 2 * D / J = Real.exp (Real.log (4 + 2 * D / J)) := (Real.exp_log h2).symm
      _ ≤ Real.exp a := Real.exp_le_exp.mpr h1
  have hmain := local_floor_le_card_mul (mem_datumCone_one_zero_of_mem_windowCone hlam) zero_le_one
    ha0 hac
  rw [one_mul, ← hJ, ← hD, ← hm] at hmain
  set P : ℝ := ((posSupport lam a ⌈2 * Real.exp (2 * a)⌉₊).card : ℝ) with hP
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hX : J * Real.exp a / 2 ≤ J * (Real.exp a - 2) - D := by
    have : 2 * D ≤ J * (Real.exp a - 4) := by
      have := mul_le_mul_of_nonneg_left (show 2 * D / J ≤ Real.exp a - 4 by linarith) hJ0.le
      rwa [mul_div_cancel₀ _ hJ0.ne'] at this
    linarith
  have hB : Real.log ⌈2 * Real.exp (2 * a)⌉₊ + coneToeplitzConst 0 ≤ K * (a + 1) := by
    have := log_ceil_two_exp_le ha0
    have := coneToeplitzConst_pos 0
    rw [hK]; nlinarith
  have hsP := Real.sqrt_nonneg P
  have h1 : J * Real.exp a / 2 ≤ Y * (a + 1) * Real.sqrt P := by
    calc J * Real.exp a / 2 ≤ Real.exp (1 / 6) * m * Real.sqrt P *
          (Real.log ⌈2 * Real.exp (2 * a)⌉₊ + coneToeplitzConst 0) := hX.trans hmain
      _ ≤ Real.exp (1 / 6) * m * Real.sqrt P * (K * (a + 1)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = Y * (a + 1) * Real.sqrt P := by rw [hY]; ring
  have ha1 : 0 < a + 1 := by linarith
  have h2 : J / 2 / Y * Real.exp a / (a + 1) ≤ Real.sqrt P := by
    have e : J / 2 / Y * Real.exp a / (a + 1) = (J * Real.exp a / 2) / (Y * (a + 1)) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have h3 : 0 ≤ J / 2 / Y * Real.exp a / (a + 1) := by positivity
  have h4 := pow_le_pow_left₀ h3 h2 2
  rw [Real.sq_sqrt hP0] at h4
  calc (J / 2 / Y) ^ 2 * Real.exp (2 * a) / (a + 1) ^ 2
      = (J / 2 / Y * Real.exp a / (a + 1)) ^ 2 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ P := h4

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
