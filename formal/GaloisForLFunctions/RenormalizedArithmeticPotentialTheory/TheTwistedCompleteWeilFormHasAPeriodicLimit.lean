import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.NoFixedOverlapSeesEveryFlip

/-!
# The twisted complete Weil form has an explicit limit on periodic packets

Replacing `Λ` by a real twist `λ` changes Weil's form by the lag sum
`Q_λ(f) − Q(f) = Σ_k d_λ(k) pairing_k(f)`, `d_λ(k) = (Λ(k) − λ(k))/√k` (`weilQuadTw_eq`). On the
atomic test of width `c/N` with coefficients `x_n = y(n)/√(n log N)`, `y` periodic, every lag
splits into its exact ratios `b = ka`, read at the atom mass `‖g‖²`, and an off-ratio window of
cost `O(c ‖g‖²/log N)` (`abs_flipInner_le`). The exact ratios are harmonic averages of the periodic
sequence `y(a) y(ka)`. Hence, whenever `Σ_k |d_λ(k)| < ∞`,

`(Q_λ − Q)(f_N)/‖g‖² → 2 Σ_k d_λ(k) k^{−1/2} M(y · y(k·))`

(`tendsto_twistedGap_packet`), where `M` is the period mean. The limit sees the twist only through
its defect and the multiplicative correlations of the profile with its dilates; the overlap `c`
drops out.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticLorentzianGeometry
  RenormalizedBiarithmeticGeometry
open _root_.RHTower (vonMangoldtAtom)

/-! ### The twist defect and the limit energy -/

/-- The **twist defect** `d_λ(k) = Λ(k)/√k − λ(k)/√k` on `k ≥ 2`: the lag weight by which the
twisted form exceeds Weil's. -/
def twistDefect (lam : ℕ → ℝ) (k : ℕ) : ℝ := vonMangoldtAtom k - twistCoeff lam k

theorem twistDefect_of_lt_two (lam : ℕ → ℝ) {k : ℕ} (hk : k < 2) : twistDefect lam k = 0 := by
  simp [twistDefect, vonMangoldtAtom, twistCoeff, show ¬ 2 ≤ k by omega]

/-- The period mean `M(y · y(k·))` of a `P`-periodic sequence against its `k`-dilate. -/
def shiftMean (y : ℕ → ℝ) (P k : ℕ) : ℝ := periodMean (fun a => y a * y (k * a)) P

/-- The **limit twist energy** `2 Σ_k d_λ(k) k^{−1/2} M(y · y(k·))` of a periodic profile. -/
def twistLimitEnergy (lam y : ℕ → ℝ) (P : ℕ) : ℝ :=
  2 * ∑' k : ℕ, twistDefect lam k / Real.sqrt k * shiftMean y P k

/-- The atomic coefficients `y(n)/√(n log N)` of a profile at horizon `N`. -/
def packetCoeff (y : ℕ → ℝ) (N n : ℕ) : ℝ := y n / Real.sqrt n / Real.sqrt (Real.log N)

/-! ### Harmonic averages of periodic sequences -/

theorem periodic_dilate_mul {y : ℕ → ℝ} {P : ℕ} (hy : Function.Periodic y P) (k : ℕ) :
    Function.Periodic (fun a => y a * y (k * a)) P := by
  intro a
  simp only
  rw [hy a, show k * (a + P) = k * a + k * P by ring]
  have := (hy.nat_mul k) (k * a)
  simpa only [Nat.cast_id] using congrArg (y a * ·) this

/-- Cutting a harmonic average at `N/k` changes it by at most `k` times the sup norm. -/
theorem abs_sum_Ioc_div_inv_le {g : ℕ → ℝ} {G : ℝ} (hG : ∀ a, |g a| ≤ G) {k N : ℕ} (hk : 1 ≤ k) :
    |∑ a ∈ Ioc (N / k) N, g a / (a : ℝ)| ≤ G * k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
    simp only [Nat.zero_div, Ioc_self, sum_empty, abs_zero]
    positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hG 0)
  have hterm : ∀ a ∈ Ioc (N / k) N, |g a / (a : ℝ)| ≤ G * k / N := by
    intro a ha
    have h1 : N / k < a := (mem_Ioc.mp ha).1
    have ha0 : (0 : ℝ) < a := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) h1
    have hlt : N < a * k := by
      have := Nat.lt_mul_div_succ N hk
      calc N < k * (N / k + 1) := this
        _ ≤ k * a := Nat.mul_le_mul_left k h1
        _ = a * k := Nat.mul_comm _ _
    have hlt' : (N : ℝ) < a * k := by exact_mod_cast hlt
    rw [abs_div, abs_of_pos ha0, div_le_div_iff₀ ha0 hN0]
    calc |g a| * N ≤ G * N := mul_le_mul_of_nonneg_right (hG a) hN0.le
      _ ≤ G * (a * k) := mul_le_mul_of_nonneg_left hlt'.le hG0
      _ = G * k * a := by ring
  calc |∑ a ∈ Ioc (N / k) N, g a / (a : ℝ)| ≤ ∑ a ∈ Ioc (N / k) N, G * k / N :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = (Ioc (N / k) N).card * (G * k / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ N * (G * k / N) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : (Ioc (N / k) N).card ≤ N := by
          rw [Nat.card_Ioc]; exact Nat.sub_le _ _
        exact_mod_cast this
    _ = G * k := by rw [mul_comm]; exact div_mul_cancel₀ (G * k) hN0.ne'

/-- **Harmonic averages up to `N/k`.** A periodic sequence keeps its period mean when the
logarithmic average is cut at `N/k`. -/
theorem tendsto_harmonic_mean_div {g : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hg : Function.Periodic g P)
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => (∑ a ∈ Icc 1 (N / k), g a / (a : ℝ)) / Real.log N) atTop
      (𝓝 (periodMean g P)) := by
  have hfull := tendsto_periodic_harmonic_mean hP hg
  set G := ∑ j ∈ range P, |g j|
  have hG : ∀ a : ℕ, |g a| ≤ G := fun a => abs_le_of_periodic hP hg a
  have htail : Tendsto (fun N : ℕ => (∑ a ∈ Ioc (N / k) N, g a / (a : ℝ)) / Real.log N) atTop
      (𝓝 0) := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hb : Tendsto (fun N : ℕ => G * k / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog0]
    refine div_le_div_of_nonneg_right ?_ hlog0.le
    exact abs_sum_Ioc_div_inv_le hG hk
  have hsplit : ∀ N : ℕ, (∑ a ∈ Icc 1 (N / k), g a / (a : ℝ)) / Real.log N =
      (∑ a ∈ Icc 1 N, g a / (a : ℝ)) / Real.log N -
        (∑ a ∈ Ioc (N / k) N, g a / (a : ℝ)) / Real.log N := by
    intro N
    rw [← sub_div]
    congr 1
    have hsub : Icc 1 N = Icc 1 (N / k) ∪ Ioc (N / k) N := by
      ext a
      simp only [mem_Icc, mem_union, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : a ≤ N / k
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨not_le.mp h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1, h2.trans (Nat.div_le_self N k)⟩
        · exact ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) h1, h2⟩
    have hdisj : Disjoint (Icc 1 (N / k)) (Ioc (N / k) N) := by
      rw [Finset.disjoint_left]
      intro a h1 h2
      exact Nat.lt_irrefl _ (lt_of_le_of_lt (mem_Icc.mp h1).2 (mem_Ioc.mp h2).1)
    rw [hsub, sum_union hdisj]
    ring
  simpa only [hsplit, sub_zero] using hfull.sub htail

/-! ### Exact ratios and the off-ratio window -/

section Lags

variable {g : ℝ → ℝ}

/-- The exact-ratio count of one lag: `2 Σ_{a,b} x_a x_b [b = ka]`. -/
def ratioPairs (N k : ℕ) (x : ℕ → ℝ) : ℝ :=
  2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0)

/-- The off-ratio window of one lag. -/
def offRatioPairs (g : ℝ → ℝ) (N k : ℕ) (x : ℕ → ℝ) : ℝ :=
  2 * ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b *
    (if b = k * a then 0 else bumpCorr g (Real.log k - (Real.log b - Real.log a)))

/-- A lag pairing of an atomic test is its exact ratios at the atom mass plus its window. -/
theorem pairing_atomicTest_eq_ratio_add (hg : Continuous g) (hgc : HasCompactSupport g) (N k : ℕ)
    (x : ℕ → ℝ) :
    pairing (atomicTest N x g) k =
      (∫ u, g u ^ 2) * ratioPairs N k x + offRatioPairs g N k x := by
  have hterm : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      x a * x b * bumpCorr g (Real.log k - (Real.log b - Real.log a)) =
        (∫ u, g u ^ 2) * (x a * x b * (if b = k * a then 1 else 0)) +
          x a * x b * (if b = k * a then 0 else
            bumpCorr g (Real.log k - (Real.log b - Real.log a))) := by
    intro a ha b hb
    by_cases hab : b = k * a
    · have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
      have hk0 : k ≠ 0 := by
        rintro rfl
        have := (mem_Icc.mp hb).1
        simp only [zero_mul] at hab
        omega
      have hk0' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      rw [if_pos hab, if_pos hab, hab, Nat.cast_mul, Real.log_mul hk0'.ne' ha0.ne',
        show Real.log k - (Real.log k + Real.log a - Real.log a) = 0 by ring, bumpCorr_zero]
      ring
    · rw [if_neg hab, if_neg hab]
      ring
  rw [pairing_atomicTest hg hgc, ratioPairs, offRatioPairs,
    Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hterm a ha b hb]
  simp only [sum_add_distrib, ← mul_sum]
  ring

theorem ratioPairs_eq_zero_of_lt {N k : ℕ} (hk : N < k) (x : ℕ → ℝ) : ratioPairs N k x = 0 := by
  unfold ratioPairs
  rw [mul_eq_zero]
  refine Or.inr (sum_eq_zero fun a ha => sum_eq_zero fun b hb => ?_)
  have ha1 := (mem_Icc.mp ha).1
  have hb2 := (mem_Icc.mp hb).2
  have : b ≠ k * a := fun h => by nlinarith
  rw [if_neg this, mul_zero]

theorem ratioPairs_zero (N : ℕ) (x : ℕ → ℝ) : ratioPairs N 0 x = 0 := by
  unfold ratioPairs
  rw [mul_eq_zero]
  refine Or.inr (sum_eq_zero fun a _ => sum_eq_zero fun b hb => ?_)
  have : b ≠ 0 * a := by have := (mem_Icc.mp hb).1; omega
  rw [if_neg this, mul_zero]

/-- The exact ratios of the lag `k ≥ 1` pair `a` with `ka` below the horizon. -/
theorem ratioPairs_eq {N k : ℕ} (hk : 1 ≤ k) (x : ℕ → ℝ) :
    ratioPairs N k x = 2 * ∑ a ∈ Icc 1 (N / k), x a * x (k * a) := by
  unfold ratioPairs
  congr 1
  have hinner : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0) =
      if a ∈ Icc 1 (N / k) then x a * x (k * a) else 0 := by
    intro a ha
    have hsel : ∑ b ∈ Icc 1 N, x a * x b * (if b = k * a then 1 else 0) =
        if k * a ∈ Icc 1 N then x a * x (k * a) else 0 := by
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq']
    rw [hsel]
    have ha1 := (mem_Icc.mp ha).1
    have hiff : k * a ∈ Icc 1 N ↔ a ∈ Icc 1 (N / k) := by
      simp only [mem_Icc]
      constructor
      · rintro ⟨-, h2⟩
        exact ⟨ha1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [Nat.mul_comm k a])⟩
      · rintro ⟨-, h2⟩
        refine ⟨Nat.mul_pos (by omega) ha1, ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega)).mp h2
        linarith [Nat.mul_comm k a]
    by_cases h : a ∈ Icc 1 (N / k)
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  rw [sum_congr rfl hinner, ← sum_filter]
  congr 1
  ext a
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans (Nat.div_le_self N k)⟩, h1, h2⟩

/-- **The twisted gap of an atomic test** is the exact-ratio sum at the atom mass plus the lag
windows. -/
theorem weilQuadTw_sub_eq_ratio_add {w : ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (lam : ℕ → ℝ) (N : ℕ)
    (x : ℕ → ℝ) :
    weilQuadTw lam (atomicTest N x g) - weilQuad (atomicTest N x g) =
      (∫ u, g u ^ 2) * ∑' k : ℕ, twistDefect lam k * ratioPairs N k x +
        ∑ k ∈ range (lagRange (Real.log N + w + 1)),
          twistDefect lam k * offRatioPairs g N k x := by
  set K := lagRange (Real.log N + w + 1) with hK
  have hKN : N < K := by
    rw [hK, lagRange]
    have hN : (N : ℝ) < Real.exp (2 * (Real.log N + w + 1)) := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0; simp only [Nat.cast_zero]; exact Real.exp_pos _
      · have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
        calc (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hN0).symm
          _ < Real.exp (2 * (Real.log N + w + 1)) := by
            rw [Real.exp_lt_exp]
            have := Real.log_natCast_nonneg N
            linarith
    have := (Nat.lt_ceil.mpr hN)
    omega
  have htsum : ∑' k : ℕ, twistDefect lam k * ratioPairs N k x =
      ∑ k ∈ range K, twistDefect lam k * ratioPairs N k x := by
    refine tsum_eq_sum fun k hk => ?_
    have hkK : K ≤ k := not_lt.mp (mem_range.not.mp hk)
    rw [ratioPairs_eq_zero_of_lt (hKN.trans_le hkK) x, mul_zero]
  rw [weilQuadTw_eq _ (supportedIn_atomicTest hgsupp hw N x), add_sub_cancel_left, htsum,
    mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [twistDefect, pairing_atomicTest_eq_ratio_add hg.continuous hgc]
  ring

end Lags

/-! ### The limit on periodic packets -/

theorem packetCoeff_mul_dilate (y : ℕ → ℝ) (N k a : ℕ) :
    packetCoeff y N a * packetCoeff y N (k * a) =
      (y a * y (k * a)) / (a : ℝ) / Real.sqrt k / Real.log N := by
  unfold packetCoeff
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg k), div_div, div_div, div_mul_div_comm,
    div_div, div_div]
  congr 1
  rw [show Real.sqrt a * Real.sqrt (Real.log N) *
      (Real.sqrt k * Real.sqrt a * Real.sqrt (Real.log N)) =
      (Real.sqrt a * Real.sqrt a) * Real.sqrt k *
        (Real.sqrt (Real.log N) * Real.sqrt (Real.log N)) by ring,
    Real.mul_self_sqrt (Nat.cast_nonneg a), Real.mul_self_sqrt (Real.log_natCast_nonneg N)]
  ring

/-- **The exact ratios of a periodic packet** converge to `2 k^{−1/2} M(y · y(k·))`. -/
theorem tendsto_ratioPairs_packet {y : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hy : Function.Periodic y P)
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun N : ℕ => ratioPairs N k (packetCoeff y N)) atTop
      (𝓝 (2 / Real.sqrt k * shiftMean y P k)) := by
  have h := (tendsto_harmonic_mean_div hP (periodic_dilate_mul hy k) hk).const_mul
    (2 / Real.sqrt k)
  refine h.congr fun N => ?_
  rw [ratioPairs_eq hk, sum_div, mul_sum, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [packetCoeff_mul_dilate]
  ring

/-- A uniform bound for the exact ratios of a bounded packet. -/
theorem abs_ratioPairs_packet_le {y : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |y n| ≤ B) {N k : ℕ}
    (hN : 3 ≤ N) (hk : 1 ≤ k) : |ratioPairs N k (packetCoeff y N)| ≤ 4 * B ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hlog1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog0 : 0 < Real.log N := by linarith
  have hk0 : (1 : ℝ) ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hharm : ∑ a ∈ Icc 1 N, 1 / (a : ℝ) ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa [one_div] using h
  rw [ratioPairs_eq hk]
  have hterm : ∀ a ∈ Icc 1 (N / k), |packetCoeff y N a * packetCoeff y N (k * a)| ≤
      B ^ 2 / Real.log N * (1 / (a : ℝ)) := by
    intro a ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
    rw [packetCoeff_mul_dilate, abs_div, abs_div, abs_div, abs_of_pos ha0,
      abs_of_pos (by linarith : (0 : ℝ) < Real.sqrt k), abs_of_pos hlog0, abs_mul]
    have hyy : |y a| * |y (k * a)| ≤ B ^ 2 := by
      rw [sq]; exact mul_le_mul (hB a) (hB _) (abs_nonneg _) hB0
    calc |y a| * |y (k * a)| / a / Real.sqrt k / Real.log N ≤ |y a| * |y (k * a)| / a / 1 /
          Real.log N := by
          gcongr
      _ ≤ B ^ 2 / a / 1 / Real.log N := by gcongr
      _ = B ^ 2 / Real.log N * (1 / (a : ℝ)) := by ring
  calc |2 * ∑ a ∈ Icc 1 (N / k), packetCoeff y N a * packetCoeff y N (k * a)|
      ≤ 2 * ∑ a ∈ Icc 1 (N / k), B ^ 2 / Real.log N * (1 / (a : ℝ)) := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm))
          (by norm_num)
    _ ≤ 2 * ∑ a ∈ Icc 1 N, B ^ 2 / Real.log N * (1 / (a : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
        · intro a ha
          simp only [mem_Icc] at ha ⊢
          exact ⟨ha.1, ha.2.trans (Nat.div_le_self N k)⟩
        · intro a _ _
          positivity
    _ = 2 * (B ^ 2 / Real.log N) * ∑ a ∈ Icc 1 N, 1 / (a : ℝ) := by rw [← mul_sum]; ring
    _ ≤ 2 * (B ^ 2 / Real.log N) * (2 * Real.log N) := by
        refine mul_le_mul_of_nonneg_left (hharm.trans (by linarith)) (by positivity)
    _ = 4 * B ^ 2 := by
        have hL : Real.log N ≠ 0 := hlog0.ne'
        field_simp
        ring

/-- The off-ratio windows of a bounded packet cost `O(c/log N)` per unit atom mass. -/
theorem abs_offRatio_packet_le {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1)
    {y : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |y n| ≤ B) (hB0 : 0 < B) {N : ℕ} (hN : 2 ≤ N) {k : ℕ}
    (hk : 1 ≤ k) :
    |offRatioPairs g N k (packetCoeff y N)| ≤
      B ^ 2 / Real.log N * (72 * (w * N) * ∫ u, g u ^ 2) := by
  have hlog0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  set s := B / Real.sqrt (Real.log N) with hs
  have hs0 : 0 < s := div_pos hB0 (Real.sqrt_pos.mpr hlog0)
  set z : ℕ → ℝ := fun n => packetCoeff y N n / s with hz
  have hzbound : ∀ n ∈ Icc 1 N, |z n| ≤ 1 / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    simp only [hz, packetCoeff, hs]
    rw [abs_div, abs_div, abs_div, abs_of_pos hsn, abs_of_pos (Real.sqrt_pos.mpr hlog0),
      abs_of_pos (div_pos hB0 (Real.sqrt_pos.mpr hlog0))]
    have hsl : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog0
    rw [div_div_div_cancel_right₀ hsl.ne', div_right_comm]
    exact div_le_div_of_nonneg_right ((div_le_one hB0).mpr (hB n)) hsn.le
  have hsne : s ≠ 0 := hs0.ne'
  have hscale : offRatioPairs g N k (packetCoeff y N) = s ^ 2 * offRatioPairs g N k z := by
    unfold offRatioPairs
    have hpz : ∀ a b, packetCoeff y N a * packetCoeff y N b = s ^ 2 * (z a * z b) := by
      intro a b
      simp only [hz]
      field_simp
    simp only [hpz, mul_assoc, ← mul_sum]
    ring
  have hwin := abs_flipInner_le hg hgc hgsupp hw0 hw1 hk hzbound
  have hk1 : (1 : ℝ) ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hG0 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hs2 : s ^ 2 = B ^ 2 / Real.log N := by
    rw [hs, div_pow, Real.sq_sqrt hlog0.le]
  rw [hscale, abs_mul, abs_of_nonneg (sq_nonneg s), hs2]
  refine mul_le_mul_of_nonneg_left (hwin.trans ?_) (by positivity)
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ 72 * (w * N) * ∫ u, g u ^ 2 := by positivity
  nlinarith

/-- **The limit of the twisted gap on periodic packets.** For a real twist with summable defect
and a periodic profile `y`, the normalized twisted gap of the atomic test with coefficients
`y(n)/√(n log N)` at width `c/N` tends to `2 Σ_k d_λ(k) k^{−1/2} M(y · y(k·))`. -/
theorem tendsto_twistedGap_packet {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {lam : ℕ → ℝ} (hlam : Summable fun k => |twistDefect lam k|)
    {y : ℕ → ℝ} {P : ℕ} (hP : 0 < P) (hy : Function.Periodic y P) :
    Tendsto (fun N : ℕ =>
      (weilQuadTw lam (atomicTest N (packetCoeff y N) (atomDilate φ (c / N))) -
        weilQuad (atomicTest N (packetCoeff y N) (atomDilate φ (c / N)))) /
          ∫ u, atomDilate φ (c / N) u ^ 2) atTop (𝓝 (twistLimitEnergy lam y P)) := by
  set B := 1 + ∑ j ∈ range P, |y j| with hBdef
  have hB0 : 0 < B := by positivity
  have hB : ∀ n, |y n| ≤ B := fun n => (abs_le_of_periodic hP hy n).trans (by linarith)
  -- the exact-ratio part, by dominated convergence over the lags
  have hratio : Tendsto (fun N : ℕ => ∑' k : ℕ, twistDefect lam k * ratioPairs N k (packetCoeff y N))
      atTop (𝓝 (∑' k : ℕ, twistDefect lam k * (2 / Real.sqrt k * shiftMean y P k))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => |twistDefect lam k| * (4 * B ^ 2))
      (hlam.mul_right _) (fun k => ?_) ?_
    · rcases Nat.lt_or_ge k 1 with hk | hk
      · have hk0 : k = 0 := by omega
        subst hk0
        simp only [ratioPairs_zero, mul_zero, twistDefect_of_lt_two lam (show 0 < 2 by norm_num),
          zero_mul]
        exact tendsto_const_nhds
      · exact (tendsto_ratioPairs_packet hP hy hk).const_mul _
    · filter_upwards [eventually_ge_atTop 3] with N hN k
      rw [Real.norm_eq_abs, abs_mul]
      rcases Nat.lt_or_ge k 1 with hk | hk
      · have hk0 : k = 0 := by omega
        subst hk0
        rw [ratioPairs_zero, abs_zero, mul_zero]
        positivity
      · exact mul_le_mul_of_nonneg_left (abs_ratioPairs_packet_le hB hN hk) (abs_nonneg _)
  -- the windows vanish
  have hwin : Tendsto (fun N : ℕ =>
      (∑ k ∈ range (lagRange (Real.log N + c / N + 1)),
        twistDefect lam k * offRatioPairs (atomDilate φ (c / N)) N k (packetCoeff y N)) /
          ∫ u, atomDilate φ (c / N) u ^ 2) atTop (𝓝 0) := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hb : Tendsto (fun N : ℕ => B ^ 2 * (72 * c) * (∑' k, |twistDefect lam k|) / Real.log N)
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop ⌈c⌉₊] with N hN hNc
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hw0 : 0 < c / N := div_pos hc hN0
    have hw1 : c / N ≤ 1 := by
      rw [div_le_one hN0]
      exact (Nat.le_ceil c).trans (by exact_mod_cast hNc)
    obtain ⟨hgd, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw0
    have hG0 : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
      rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
    have hwN : c / N * N = c := div_mul_cancel₀ c hN0.ne'
    have hterm : ∀ k ∈ range (lagRange (Real.log N + c / N + 1)),
        |twistDefect lam k * offRatioPairs (atomDilate φ (c / N)) N k (packetCoeff y N)| ≤
          |twistDefect lam k| * (B ^ 2 / Real.log N * (72 * c * ∫ u, atomDilate φ (c / N) u ^ 2)) := by
      intro k _
      rw [abs_mul]
      rcases Nat.lt_or_ge k 2 with hk | hk
      · rw [twistDefect_of_lt_two lam hk, abs_zero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h := abs_offRatio_packet_le hgd.continuous hgc hgsupp hw0 hw1 hB hB0 hN
          (show 1 ≤ k by omega)
        rwa [hwN] at h
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hG0, div_le_iff₀ hG0]
    calc |∑ k ∈ range (lagRange (Real.log N + c / N + 1)),
          twistDefect lam k * offRatioPairs (atomDilate φ (c / N)) N k (packetCoeff y N)|
        ≤ ∑ k ∈ range (lagRange (Real.log N + c / N + 1)), |twistDefect lam k| *
            (B ^ 2 / Real.log N * (72 * c * ∫ u, atomDilate φ (c / N) u ^ 2)) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ = (∑ k ∈ range (lagRange (Real.log N + c / N + 1)), |twistDefect lam k|) *
            (B ^ 2 / Real.log N * (72 * c * ∫ u, atomDilate φ (c / N) u ^ 2)) := by
          rw [sum_mul]
      _ ≤ (∑' k, |twistDefect lam k|) *
            (B ^ 2 / Real.log N * (72 * c * ∫ u, atomDilate φ (c / N) u ^ 2)) :=
          mul_le_mul_of_nonneg_right (hlam.sum_le_tsum _ fun k _ => abs_nonneg _)
            (by positivity)
      _ = B ^ 2 * (72 * c) * (∑' k, |twistDefect lam k|) / Real.log N *
            ∫ u, atomDilate φ (c / N) u ^ 2 := by ring
  have hlim := (hratio.add hwin)
  have hval : ∑' k : ℕ, twistDefect lam k * (2 / Real.sqrt k * shiftMean y P k) + 0 =
      twistLimitEnergy lam y P := by
    rw [add_zero, twistLimitEnergy, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc hN0
  obtain ⟨hgd, hgsupp, hgc⟩ := atomDilate_facts hφ hsupp hw0
  have hG0 : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw0]; exact mul_pos hw0 hM
  rw [weilQuadTw_sub_eq_ratio_add hgd hgc hgsupp hw0.le lam N, add_div,
    mul_div_cancel_left₀ _ hG0.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
