import GaloisForLFunctions.RHTower.JointAncestryShellArithmeticCriterion

/-!
# Loud zeros of a shell and an RH criterion without attainment

For the shell `P_N = primes in (N, 2N]` let `U_ρ(N) = Σ_{N<p≤2N} p^{ρ−3/2}` and
`A_k(N) = Σ_ρ U_ρ(N)^k/(ρ(1−ρ))`, the prime-side shell power sum of
`JointAncestryShellArithmeticCriterion`.

**Absorbed Turán bound** (`exists_norm_tsum_pow_ge_of_finite_loud`).  Let `B` be any function on the
zeros with summable power sums.  If only finitely many zeros have `|B(ρ)| > L` and at least one does,
then for every `M₀` some `k > M₀` satisfies

`|Σ_ρ B(ρ)^k/(ρ(1−ρ))| ≥ 2 W L^k`,   `W = Σ_ρ |1/(ρ(1−ρ))|`.

Turán's second main theorem on the loud set loses a factor `D(n, M)` polynomial in the window start
`M`.  The quiet zeros have ratio `L/Z < 1` to the loudest value `Z`, so their contribution decays
geometrically in `M`.  Choosing `M` large absorbs `D(n, M)`, the minimal weight and the angle
constant, and leaves the universal factor `2W`.

**Loud-set finiteness.** `JasShellLoudFinite` says that for every `ε > 0` and every large `N` only
finitely many zeros have `|U_ρ(N)| > N^ε`.  The zeros approaching the line imply it
(`jasShellLoudFinite_of_zerosApproachLine`).  Loud-set finiteness only constrains the values of one
Dirichlet polynomial per shell.  It allows infinitely many zeros at a fixed distance from the line
as long as each shell hears finitely many of them.

**Theorem** (`riemannHypothesis_iff_shellLoudFinite_and_shellArithmetic_growth`).

`RH ⟺ JasShellLoudFinite ∧ ∀ ε > 0, ∃ᶠ N, ∀ k ≥ 1, |A_k(N)| ≤ N^{εk}`.

No maximal off-line zero is needed: any zero right of the line is loud on every large shell
(`eventually_lt_norm_jasShellUniformSum`), and the absorbed bound on that single shell already
contradicts the growth condition.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-! ## The absorbed Turán bound -/

/-- The Turán window inequality holds beyond any prescribed start. -/
theorem exists_turan_window_ge (n M₀ : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (A : ℝ) {B : ℝ}
    (hB : 0 < B) : ∃ M : ℕ, M₀ ≤ M ∧ A * ρ ^ (M + 1) * (2 * (Real.exp 1 * n *
      (6 * (n + 1) * ((M : ℝ) + 2 * n + 2)) ^ n)) ≤ B := by
  have h1 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one n
    (show |ρ| < 1 by rw [abs_of_pos hρ0]; exact hρ1)).comp
    (tendsto_add_atTop_nat (2 * n + 2))
  have h2 := h1.const_mul (A * ρ ^ (1 : ℕ) / ρ ^ (2 * n + 2) * (2 * (Real.exp 1 * n * 6 ^ n *
    ((n : ℝ) + 1) ^ n)))
  rw [mul_zero] at h2
  obtain ⟨M, hM, hM₀⟩ := ((h2.eventually (ge_mem_nhds hB)).and (eventually_ge_atTop M₀)).exists
  refine ⟨M, hM₀, le_of_eq_of_le ?_ hM⟩
  simp only [Function.comp]
  have hρn : ρ ^ (2 * n + 2) ≠ 0 := pow_ne_zero _ hρ0.ne'
  have e1 : (6 * ((n : ℝ) + 1) * ((M : ℝ) + 2 * n + 2)) ^ n =
      6 ^ n * ((n : ℝ) + 1) ^ n * ((M : ℝ) + 2 * n + 2) ^ n := by rw [mul_pow, mul_pow]
  have e2 : ρ ^ (M + (2 * n + 2)) = ρ ^ (M + 1) * ρ ^ (2 * n + 1) := by
    rw [← pow_add]; congr 1; omega
  have e3 : ρ ^ (2 * n + 2) = ρ ^ 1 * ρ ^ (2 * n + 1) := by rw [← pow_add]; congr 1; omega
  push_cast
  rw [e1, e2, e3]
  have hρ1' : ρ ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hρ0.ne'
  field_simp
  ring

theorem inv_mul_one_sub_ne_zero (q : XiZeroCopy) : 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) ≠ 0 := by
  refine one_div_ne_zero (mul_ne_zero ?_ ?_)
  · intro h
    have := xiZeroCopy_re_pos q
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  · intro h
    have := xiZeroCopy_re_lt_one q
    have h' : (q.1 : ℂ) = 1 := by linear_combination -h
    rw [h', Complex.one_re] at this
    exact lt_irrefl _ this

/-- **Turán's constant is absorbed by a free exponent.**  If finitely many zeros, and at least one,
have `|B(ρ)| > L`, then beyond any `M₀` some power `k` has
`|Σ_ρ B(ρ)^k/(ρ(1−ρ))| ≥ 2 (Σ_ρ |1/(ρ(1−ρ))|) L^k`. -/
theorem exists_norm_tsum_pow_ge_of_finite_loud (B : XiZeroCopy → ℂ)
    (hsumm : ∀ ν : ℕ, Summable fun q : XiZeroCopy => B q ^ ν * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))))
    {L : ℝ} (hL : 0 < L) (hfin : {q : XiZeroCopy | L < ‖B q‖}.Finite)
    (hne : ∃ q : XiZeroCopy, L < ‖B q‖) (M₀ : ℕ) :
    ∃ ν : ℕ, M₀ < ν ∧ 2 * (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) * L ^ ν ≤
      ‖∑' q : XiZeroCopy, B q ^ ν * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))‖ := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Finset XiZeroCopy, G = hfin.toFinset := ⟨_, rfl⟩
  have hmemG : ∀ q, q ∈ G ↔ L < ‖B q‖ := fun q => by
    rw [hG, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  obtain ⟨q₁, hq₁⟩ := hne
  have hGne : G.Nonempty := ⟨q₁, (hmemG q₁).mpr hq₁⟩
  -- the loudest value
  obtain ⟨qm, hqmG, hqmax⟩ := G.exists_max_image (fun q => ‖B q‖) hGne
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ‖B qm‖ := ⟨_, rfl⟩
  have hLZ : L < Z := hZ ▸ (hmemG qm).mp hqmG
  have hZ0 : 0 < Z := hL.trans hLZ
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = L / Z := ⟨_, rfl⟩
  have hρ₂0 : 0 < ρ₂ := hρ₂ ▸ div_pos hL hZ0
  have hρ₂1 : ρ₂ < 1 := hρ₂ ▸ (div_lt_one hZ0).mpr hLZ
  have hρ₂Z : ρ₂ * Z = L := by rw [hρ₂]; field_simp
  -- the angle of the weights on the loud set
  obtain ⟨qd, -, hqdmax⟩ := G.exists_max_image (fun q => |(q.1 : ℂ).re - 1 / 2|) hGne
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(qd.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  have hδ1 : δ < 1 / 2 := hδ ▸ abs_re_sub_half_lt_half_xiZeroCopy qd
  have hδ0 : 0 ≤ δ := hδ ▸ abs_nonneg _
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 - δ ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; nlinarith
  have hcw : ∀ q ∈ G, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := fun q hq =>
    hc ▸ quarter_sub_sq_mul_norm_le_re_one_div hδ1 (hδ ▸ hqdmax q hq)
  -- the minimal weight on the loud set
  obtain ⟨qw, -, hqwmin⟩ :=
    G.exists_min_image (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) hGne
  obtain ⟨wmin, hwmin⟩ : ∃ wmin : ℝ, wmin = ‖1 / ((qw.1 : ℂ) * (1 - (qw.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwmin0 : 0 < wmin := hwmin ▸ norm_pos_iff.mpr (inv_mul_one_sub_ne_zero qw)
  have hwminG : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := fun q hq =>
    hwmin ▸ hqwmin q hq
  -- the total weight
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  have hW0 : 0 ≤ W := hW ▸ tsum_nonneg fun _ => norm_nonneg _
  -- the window start
  obtain ⟨M, hM₀M, hM⟩ :=
    exists_turan_window_ge G.card M₀ hρ₂0 hρ₂1 W (show 0 < c * wmin / 4 by positivity)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (Real.exp 1 * G.card *
      (6 * (G.card + 1) * ((M : ℝ) + 2 * G.card + 2)) ^ G.card) := ⟨_, rfl⟩
  rw [← hD] at hM
  have hn1 : (1 : ℝ) ≤ G.card := by exact_mod_cast Finset.card_pos.mpr hGne
  have hD0 : 0 < D := by rw [hD]; positivity
  have hWρ : W * ρ₂ ^ (M + 1) ≤ c * wmin / (4 * D) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  -- the finite set and its tail
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = c * wmin / (4 * D) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨F, hFtail, hGF⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) ≤ T ∧ G ⊆ F := by
    have h1 := (tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)).eventually (ge_mem_nhds hT0)
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, G ⊆ F := eventually_ge_atTop G
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    exact ⟨F, hF1, hF2⟩
  have hW₁ : ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W :=
    hW ▸ summable_inv_mul_one_sub.norm.sum_le_tsum F fun _ _ => norm_nonneg _
  have hquiet : ∀ q, q ∉ G → ‖B q‖ ≤ L := fun q hq => by
    by_contra h
    exact hq ((hmemG q).mpr (not_le.mp h))
  have hcomp : ∀ q ∈ F, q ∉ G → ‖B q‖ ≤ ρ₂ * Z := fun q _ hq => hρ₂Z ▸ hquiet q hq
  have htail : ∀ q : XiZeroCopy, q ∉ F → ‖B q‖ ≤ 1 * Z := fun q hq => by
    rw [one_mul]; exact (hquiet q fun h => hq (hGF h)).trans hLZ.le
  have hMT : W * ρ₂ ^ (M + 1) + T * 1 ^ (M + G.card) ≤ c * wmin / (2 * D) := by
    have h2 : c * wmin / (4 * D) + c * wmin / (4 * D) = c * wmin / (2 * D) := by
      field_simp; ring
    rw [one_pow, mul_one, hT]
    linarith
  obtain ⟨ν, hν1, -, hν⟩ := exists_norm_tsum_pow_mul_ge B M hsumm hGF hqmG hZ hZ0 hcomp
    hρ₂0.le hρ₂1.le htail le_rfl hc0 hcw hwminG hwmin0 hW₁ hFtail (by rw [← hD]; exact hMT)
  rw [← hD] at hν
  refine ⟨ν, by omega, le_trans ?_ hν⟩
  rw [← hW]
  have hkey : 2 * W * ρ₂ ^ (M + 1) ≤ c * wmin / (2 * D) := by
    have h2 : c * wmin / (4 * D) + c * wmin / (4 * D) = c * wmin / (2 * D) := by
      field_simp; ring
    linarith
  have hLν : L ^ ν ≤ ρ₂ ^ (M + 1) * Z ^ ν := by
    rw [← hρ₂Z, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hρ₂0.le hρ₂1.le hν1) (by positivity)
  calc 2 * W * L ^ ν ≤ 2 * W * (ρ₂ ^ (M + 1) * Z ^ ν) :=
        mul_le_mul_of_nonneg_left hLν (by positivity)
    _ = 2 * W * ρ₂ ^ (M + 1) * Z ^ ν := by ring
    _ ≤ c * wmin / (2 * D) * Z ^ ν := mul_le_mul_of_nonneg_right hkey (by positivity)

/-! ## Loud zeros of a shell -/

/-- The zeros whose shell sum on `(N, 2N]` exceeds `N^ε`. -/
def jasShellLoudSet (N : ℕ) (ε : ℝ) : Set XiZeroCopy :=
  {q | (N : ℝ) ^ ε < ‖jasShellUniformSum N (q.1 : ℂ)‖}

/-- Every large shell hears only finitely many zeros above every level `N^ε`. -/
def JasShellLoudFinite : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (jasShellLoudSet N ε).Finite

/-- A zero right of the line is loud on every large shell, at every level below its distance. -/
theorem eventually_lt_norm_jasShellUniformSum (q : XiZeroCopy) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < (q.1 : ℂ).re - 1 / 2) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ε < ‖jasShellUniformSum N (q.1 : ℂ)‖ := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 3 / 2 - (q.1 : ℂ).re := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith [xiZeroCopy_re_lt_one q]
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α - ε := by rw [hα]; linarith
  obtain ⟨f, hf⟩ : ∃ f : ℝ, f = jasShellFactor α (q.1 : ℂ).im := ⟨_, rfl⟩
  have hf0 : 0 < f := hf ▸ jasShellFactor_pos hα1 _
  have hz : (3 / 2 : ℂ) - (q.1 : ℂ) = (α : ℂ) - (((q.1 : ℂ).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [hα]
  have hlim := tendsto_natLog_div_rpow_atTop h1α
  filter_upwards [eventually_abs_norm_shell_sub_le hα0 hα1 (q.1 : ℂ).im (show 0 < f / 2 by
    positivity), hlim.eventually (gt_mem_nhds (show (0 : ℝ) < f / 2 by positivity)),
    eventually_ge_atTop 2] with N hN hlog hN2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN := Real.log_pos hN1
  rw [← hf] at hN
  have hU : ‖jasShellUniformSum N (q.1 : ℂ)‖ =
      ‖jasWindowSum N (2 * N) ((α : ℂ) - (((q.1 : ℂ).im : ℝ) : ℂ) * I)‖ := by
    rw [jasShellUniformSum, hz, jasWindowSum_eq_jasCpowSum]
  rw [hU]
  have hlow := (abs_le.mp hN).1
  have hE : jasMainScale α N = (N : ℝ) ^ (1 - α) / Real.log N := rfl
  have hpow : (N : ℝ) ^ (1 - α) = (N : ℝ) ^ (1 - α - ε) * (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hpe : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
  have hpd : 0 < (N : ℝ) ^ (1 - α - ε) := Real.rpow_pos_of_pos hNpos _
  have hkey : Real.log N < f / 2 * (N : ℝ) ^ (1 - α - ε) := by
    rwa [div_lt_iff₀ hpd] at hlog
  have hmain : (N : ℝ) ^ ε < f / 2 * jasMainScale α N := by
    have hgt : 1 < f / 2 * (N : ℝ) ^ (1 - α - ε) / Real.log N := by
      rw [lt_div_iff₀ hlogN]; linarith
    have e : f / 2 * ((N : ℝ) ^ (1 - α - ε) * (N : ℝ) ^ ε / Real.log N) =
        (f / 2 * (N : ℝ) ^ (1 - α - ε) / Real.log N) * (N : ℝ) ^ ε := by ring
    rw [hE, hpow, e]
    nlinarith
  linarith

/-- **The zeros approaching the line make every shell loud set finite.** -/
theorem jasShellLoudFinite_of_zerosApproachLine (hZ : BacklundConverse.ZerosApproachLine) :
    JasShellLoudFinite := by
  intro ε hε
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = min (ε / 2) (1 / 4) := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; exact lt_min (by linarith) (by norm_num)
  have hhε : h < ε := by rw [hh]; exact (min_le_left _ _).trans_lt (by linarith)
  have hh4 : h ≤ 1 / 4 := by rw [hh]; exact min_le_right _ _
  have hfin := BacklundConverse.finite_abs_im_gt_of_zerosApproachLine hZ hh0
  have hα0 : 0 < 1 - h := by linarith
  have hα1 : 1 - h < 1 := by linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 / (1 - (1 - h)) + 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hC]
    have : 0 < 1 - (1 - h) := by linarith
    positivity
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ (ε - h)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos),
    hgrow.eventually (eventually_gt_atTop (C * 2 ^ h)), eventually_ge_atTop 2] with N hN hg hN2
  refine hfin.subset fun q hq => ?_
  simp only [jasShellLoudSet, Set.mem_setOf_eq] at hq
  simp only [Set.mem_setOf_eq]
  by_contra hqn
  push Not at hqn
  rw [LindelofSparse.spectral_im_eq, abs_sub_comm] at hqn
  have hre : (q.1 : ℂ).re - 1 / 2 ≤ h := (le_abs_self _).trans hqn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2N : (2 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by push_cast; linarith [(show (1 : ℝ) ≤ N by
    exact_mod_cast (show 1 ≤ N by omega))]
  -- the shell sum is at most the prime power sum at exponent `1 − h`
  have h1 := norm_jasShellUniformSum_le N (q.1 : ℂ)
  have h2 : ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(3 / 2 - (q.1 : ℂ).re) * Real.log p) ≤
      ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(1 - h) * Real.log p) :=
    Finset.sum_le_sum fun p _ => exp_neg_mul_log_prime_anti (by linarith) p
  have h3 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) (1 - h)
  -- the main scale at `2N` is at most `2^h N^h`
  have hlog2N : 1 ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    have : Real.exp 1 ≤ ((2 * N : ℕ) : ℝ) := by
      have he := Real.exp_one_lt_d9
      have : (4 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
        push_cast; linarith [(show (2 : ℝ) ≤ N by exact_mod_cast hN2)]
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  have hscale : jasMainScale (1 - h) (2 * N) ≤ 2 ^ h * (N : ℝ) ^ h := by
    have e : jasMainScale (1 - h) (2 * N) = ((2 * N : ℕ) : ℝ) ^ h / Real.log ((2 * N : ℕ) : ℝ) := by
      simp only [jasMainScale]; ring_nf
    rw [e, div_le_iff₀ (by linarith)]
    have : ((2 * N : ℕ) : ℝ) ^ h = 2 ^ h * (N : ℝ) ^ h := by
      push_cast; rw [Real.mul_rpow (by norm_num) hNpos.le]
    rw [this]
    have : 0 ≤ 2 ^ h * (N : ℝ) ^ h := by positivity
    nlinarith
  have hpow : (N : ℝ) ^ ε = (N : ℝ) ^ (ε - h) * (N : ℝ) ^ h := by
    rw [← Real.rpow_add hNpos]; ring_nf
  have hNh : 0 < (N : ℝ) ^ h := Real.rpow_pos_of_pos hNpos _
  have hfinal : C * (2 ^ h * (N : ℝ) ^ h) < (N : ℝ) ^ ε := by
    rw [hpow]; nlinarith
  rw [← hC] at hN
  have hCs := mul_le_mul_of_nonneg_left hscale hC0.le
  linarith

/-! ## The capstone -/

/-- **RH ⟺ finite shell loud sets ∧ subexponential growth of the prime-side shell power sums.** -/
theorem riemannHypothesis_iff_shellLoudFinite_and_shellArithmetic_growth :
    RiemannHypothesis ↔ JasShellLoudFinite ∧ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellArithmeticSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  constructor
  · intro hRH
    exact ⟨jasShellLoudFinite_of_zerosApproachLine (zerosApproachLine_of_riemannHypothesis hRH),
      (riemannHypothesis_iff_zerosApproachLine_and_shellArithmetic_growth.mp hRH).2⟩
  · rintro ⟨hloud, hfr⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (q₁.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
      ⟨_, rfl⟩
    have hW0 : 0 < W := hW ▸ Summable.tsum_pos summable_inv_mul_one_sub.norm
      (fun _ => norm_nonneg _) q₁ (norm_pos_iff.mpr (inv_mul_one_sub_ne_zero q₁))
    have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ (δ / 4)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have hev := (eventually_lt_norm_jasShellUniformSum q₁ (ε := 3 * δ / 4) (by linarith)
      (by rw [← hδ]; linarith)).and ((hloud (3 * δ / 4) (by linarith)).and
        ((hgrow.eventually (eventually_gt_atTop (1 / (2 * W)))).and (eventually_ge_atTop 1)))
    obtain ⟨N, hN, hloudN, hfinN, hbig, hN1⟩ := ((hfr (δ / 2) (by linarith)).and_eventually hev).exists
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    obtain ⟨ν, hν0, hν⟩ := exists_norm_tsum_pow_ge_of_finite_loud
      (fun q => jasShellUniformSum N (q.1 : ℂ)) (summable_jasShellUniformPowerSum_terms N)
      (Real.rpow_pos_of_pos hNpos (3 * δ / 4)) hfinN ⟨q₁, hloudN⟩ 0
    have hν1 : 1 ≤ ν := hν0
    rw [← hW] at hν
    have hA := hN ν hν1
    rw [← jasShellUniformPowerSum_eq_arithmeticSum N hν1] at hA
    have hνr : (1 : ℝ) ≤ ν := by exact_mod_cast hν1
    -- `2W N^{3δν/4} > N^{δν/2}`
    have hpowL : ((N : ℝ) ^ (3 * δ / 4)) ^ ν = (N : ℝ) ^ (3 * δ / 4 * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    have hsplit : (N : ℝ) ^ (3 * δ / 4 * ν) =
        (N : ℝ) ^ (δ / 4 * ν) * (N : ℝ) ^ (δ / 2 * ν) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hge : (N : ℝ) ^ (δ / 4) ≤ (N : ℝ) ^ (δ / 4 * ν) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by nlinarith)
    have hb : 1 < 2 * W * (N : ℝ) ^ (δ / 4) := by
      rw [div_lt_iff₀ (by positivity)] at hbig; linarith
    have hpos : 0 < (N : ℝ) ^ (δ / 2 * ν) := Real.rpow_pos_of_pos hNpos _
    have hlt : (N : ℝ) ^ (δ / 2 * ν) < 2 * W * ((N : ℝ) ^ (3 * δ / 4)) ^ ν := by
      rw [hpowL, hsplit]
      have : 1 < 2 * W * (N : ℝ) ^ (δ / 4 * ν) :=
        lt_of_lt_of_le hb (mul_le_mul_of_nonneg_left hge (by positivity))
      nlinarith
    have hA' : ‖jasShellUniformPowerSum N ν‖ ≤ (N : ℝ) ^ (δ / 2 * ν) := hA
    have hν' : 2 * W * ((N : ℝ) ^ (3 * δ / 4)) ^ ν ≤ ‖jasShellUniformPowerSum N ν‖ := hν
    linarith

end

end RHTower
