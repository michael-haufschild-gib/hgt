import GaloisForLFunctions.RHTower.ThetaDerivativePacketDivisor
import GaloisForLFunctions.RHTower.ThetaSourceTailRatioCalculus

/-!
# Theta derivative packets: positivity, strong log-concavity and relative growth

For `k_t = k + t k^{(4m)}` the log-concavity numerator satisfies, with `a = k^{(4m)}/k`,
`k_t'' k_t - (k_t')² = k² [(1+ta)² (log k)'' + t(1+ta) a''  - t² a'²]`. On the positive tail
`(log k)'' = -4π e^{2x} + o(1)` while `a''/a → (8m)²`, so far out `(log k_t)'' ≤ -1` uniformly in
`t ≥ 0`; evenness gives the negative tail. On the remaining compact interval the strictly negative
numerator of `k` and bounded derivatives survive a small perturbation. Hence for all small `t ≥ 0`,
`k_t > 0` and `(log k_t)'' ≤ -δ` on `ℝ` with one `δ > 0`.

Also: `k_t` is a Schwartz function converging to `k` as `t → 0`, has every exponential moment,
every exponentially weighted derivative seminorm of `k_t - k` is `O(|t|)`, and
`(k_t - k)/k ~ t (2π e^{2x})^{4m} → +∞` as `x → +∞`.
-/
open Filter Topology MeasureTheory Set Polynomial
open scoped ContDiff

namespace RHTower

noncomputable section

/-! ## Derivatives of the deformed source -/

theorem contDiff_iteratedDeriv_thetaCuspFullSource (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n thetaCuspFullSource) := by
  rw [iteratedDeriv_eq_iterate]
  exact contDiff_thetaCuspFullSource.iterate_deriv n

theorem hasDerivAt_thetaDerivativePacket_iteratedDeriv (m : ℕ) (t : ℝ) (i : ℕ) (x : ℝ) :
    HasDerivAt (fun y => iteratedDeriv i thetaCuspFullSource y +
        t * iteratedDeriv (i + 4 * m) thetaCuspFullSource y)
      (iteratedDeriv (i + 1) thetaCuspFullSource x +
        t * iteratedDeriv (i + 1 + 4 * m) thetaCuspFullSource x) x := by
  have h1 := hasDerivAt_iteratedDeriv_thetaCuspFullSource i x
  have h2 := (hasDerivAt_iteratedDeriv_thetaCuspFullSource (i + 4 * m) x).const_mul t
  rw [show i + 1 + 4 * m = i + 4 * m + 1 by ring]
  exact h1.add h2

/-- `k_t^{(i)} = k^{(i)} + t k^{(i+4m)}`. -/
theorem iteratedDeriv_thetaDerivativePacket (m : ℕ) (t : ℝ) (i : ℕ) :
    iteratedDeriv i (thetaDerivativePacket m t) = fun x =>
      iteratedDeriv i thetaCuspFullSource x + t * iteratedDeriv (i + 4 * m) thetaCuspFullSource x := by
  induction i with
  | zero =>
      funext x
      simp [thetaDerivativePacket]
  | succ i ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_thetaDerivativePacket_iteratedDeriv m t i x).deriv

theorem hasDerivAt_iteratedDeriv_thetaDerivativePacket (m : ℕ) (t : ℝ) (i : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv i (thetaDerivativePacket m t))
      (iteratedDeriv (i + 1) (thetaDerivativePacket m t) x) x := by
  rw [iteratedDeriv_thetaDerivativePacket, iteratedDeriv_thetaDerivativePacket]
  exact hasDerivAt_thetaDerivativePacket_iteratedDeriv m t i x

theorem iteratedDeriv_thetaDerivativePacket_neg (m : ℕ) (t : ℝ) (i : ℕ) (x : ℝ) :
    iteratedDeriv i (thetaDerivativePacket m t) (-x) =
      (-1) ^ i * iteratedDeriv i (thetaDerivativePacket m t) x := by
  rw [iteratedDeriv_thetaDerivativePacket]
  simp only
  rw [iteratedDeriv_thetaCuspFullSource_neg, iteratedDeriv_thetaCuspFullSource_neg, pow_add,
    show 4 * m = 2 * (2 * m) by ring, pow_mul]
  norm_num
  ring

theorem contDiff_thetaDerivativePacket (m : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (thetaDerivativePacket m t) :=
  contDiff_thetaCuspFullSource.add
    (contDiff_const.mul (contDiff_iteratedDeriv_thetaCuspFullSource (4 * m)))

/-! ## The logarithmic curvature numerator -/

/-- The log-concavity numerator `k_t'' k_t - (k_t')²`. -/
def thetaDerivativePacketNumerator (m : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv 2 (thetaDerivativePacket m t) x * thetaDerivativePacket m t x -
    iteratedDeriv 1 (thetaDerivativePacket m t) x ^ 2

theorem thetaDerivativePacketNumerator_neg (m : ℕ) (t x : ℝ) :
    thetaDerivativePacketNumerator m t (-x) = thetaDerivativePacketNumerator m t x := by
  unfold thetaDerivativePacketNumerator
  rw [iteratedDeriv_thetaDerivativePacket_neg, iteratedDeriv_thetaDerivativePacket_neg,
    thetaDerivativePacket_neg]
  ring

/-- The pointwise algebra behind the tail curvature bound: with `a = σ_r`,
`A = σ_{r+1}/σ_r - σ_1` and `M = a''/a`,
`(σ₂ + tσ_{r+2})(1 + ta) - (σ₁ + tσ_{r+1})² = (1+ta)² ℓ + t(1+ta) a M - t² a² A²`. -/
theorem thetaPacket_numerator_algebra (a s1 s2 u v t : ℝ) (ha : a ≠ 0) :
    (s2 + t * v) * (1 + t * a) - (s1 + t * u) ^ 2 =
      (1 + t * a) ^ 2 * (s2 - s1 ^ 2) +
        t * (1 + t * a) * a * ((v / a - (u / a) ^ 2 - (s2 - s1 ^ 2)) + (u / a - s1) ^ 2) -
          t ^ 2 * a ^ 2 * (u / a - s1) ^ 2 := by
  field_simp
  ring

theorem thetaPacket_numerator_le {a s1 s2 u v t c : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hM : (v / a - (u / a) ^ 2 - (s2 - s1 ^ 2)) + (u / a - s1) ^ 2 ≤ c)
    (hℓ : s2 - s1 ^ 2 ≤ -c - 1) :
    (s2 + t * v) * (1 + t * a) - (s1 + t * u) ^ 2 ≤ -(1 + t * a) ^ 2 := by
  rw [thetaPacket_numerator_algebra a s1 s2 u v t ha.ne']
  set M := (v / a - (u / a) ^ 2 - (s2 - s1 ^ 2)) + (u / a - s1) ^ 2
  set ℓ := s2 - s1 ^ 2
  have hta : 0 ≤ t * a := mul_nonneg ht ha.le
  have h1 : t * (1 + t * a) * a * M ≤ t * (1 + t * a) * a * c :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have h2 : t * (1 + t * a) * a * c ≤ (1 + t * a) ^ 2 * c := by
    have h3 : (1 + t * a) ^ 2 * c - t * (1 + t * a) * a * c = (1 + t * a) * c := by ring
    have h4 : 0 ≤ (1 + t * a) * c := mul_nonneg (by positivity) hc
    linarith
  have h4 : (1 + t * a) ^ 2 * ℓ ≤ (1 + t * a) ^ 2 * (-c - 1) :=
    mul_le_mul_of_nonneg_left hℓ (by positivity)
  nlinarith [sq_nonneg (t * a * (u / a - s1)), sq_nonneg (1 + t * a)]

/-- **Uniform tail curvature.** Far out on the positive tail, uniformly in `t ≥ 0`,
`k_t > 0` and `k_t'' k_t - (k_t')² ≤ -k_t²`, i.e. `(log k_t)'' ≤ -1`. -/
theorem eventually_thetaDerivativePacketNumerator_le (m : ℕ) (hm : 0 < m) :
    ∀ᶠ x in atTop, ∀ t : ℝ, 0 ≤ t →
      0 < thetaDerivativePacket m t x ∧
        thetaDerivativePacketNumerator m t x ≤ -thetaDerivativePacket m t x ^ 2 := by
  set r := 4 * m
  set c : ℝ := (2 * (r : ℕ) : ℝ) ^ 2 + 1
  have hc : 0 ≤ c := by positivity
  have hA := tendsto_thetaSourceRatio_logSlope m hm
  have hB := tendsto_thetaSourceRatio_logCurvature m hm
  have hM := hB.add (hA.pow 2)
  rw [zero_add] at hM
  have hMev := hM.eventually_lt_const (show ((2 * (r : ℕ) : ℝ)) ^ 2 < c by simp [c])
  have hℓ := tendsto_thetaSourceRatio_curvature_add_scale
  have hℓev := hℓ.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  have hq := tendsto_thetaTailScale.eventually_ge_atTop ((c + 2) / 4)
  filter_upwards [hMev, hℓev, hq, eventually_half_le_thetaSourceRatio m hm] with x hMx hℓx hqx ha
  intro t ht
  set K := thetaCuspFullSource x
  have hK : 0 < K := thetaCuspFullSource_pos_all x
  have ha0 : 0 < thetaSourceRatio r x := by linarith
  have hσ : ∀ i, iteratedDeriv i thetaCuspFullSource x = K * thetaSourceRatio i x := by
    intro i
    have hk0 : thetaCuspFullSource x ≠ 0 := hK.ne'
    simp only [thetaSourceRatio, K]
    field_simp
  have hkt : thetaDerivativePacket m t x = K * (1 + t * thetaSourceRatio r x) := by
    simp only [thetaDerivativePacket]
    rw [hσ r]
    ring
  have hpos : 0 < thetaDerivativePacket m t x := by
    rw [hkt]
    have : 0 ≤ t * thetaSourceRatio r x := mul_nonneg ht ha0.le
    positivity
  refine ⟨hpos, ?_⟩
  have hN : thetaDerivativePacketNumerator m t x =
      K ^ 2 * ((thetaSourceRatio 2 x + t * thetaSourceRatio (r + 2) x) *
        (1 + t * thetaSourceRatio r x) -
          (thetaSourceRatio 1 x + t * thetaSourceRatio (r + 1) x) ^ 2) := by
    unfold thetaDerivativePacketNumerator
    rw [iteratedDeriv_thetaDerivativePacket, iteratedDeriv_thetaDerivativePacket]
    simp only
    rw [hkt, hσ 2, hσ 1, show 2 + 4 * m = r + 2 by ring, show 1 + 4 * m = r + 1 by ring,
      hσ (r + 2), hσ (r + 1)]
    ring
  have hbound := thetaPacket_numerator_le (a := thetaSourceRatio r x)
    (s1 := thetaSourceRatio 1 x) (s2 := thetaSourceRatio 2 x) (u := thetaSourceRatio (r + 1) x)
    (v := thetaSourceRatio (r + 2) x) ha0 ht hc (by simpa [add_comm] using hMx.le)
    (by nlinarith)
  rw [hN, hkt, mul_pow]
  have hK2 : 0 < K ^ 2 := by positivity
  nlinarith

theorem continuous_iteratedDeriv_thetaCuspFullSource (n : ℕ) :
    Continuous (iteratedDeriv n thetaCuspFullSource) :=
  (contDiff_iteratedDeriv_thetaCuspFullSource n).continuous

/-- The compact-interval arithmetic: a strictly negative numerator and bounded derivatives
survive a small perturbation of size `t`. -/
theorem thetaPacket_compact_numerator_le {k0 k1 k2 d0 d1 d2 t B η κ : ℝ}
    (hk0 : |k0| ≤ B) (hk1 : |k1| ≤ B) (hk2 : |k2| ≤ B) (hd0 : |d0| ≤ B) (hd1 : |d1| ≤ B)
    (hd2 : |d2| ≤ B) (hB : 1 ≤ B) (hN0 : k2 * k0 - k1 ^ 2 ≤ -η) (hκk : κ ≤ k0) (hκ : 0 < κ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (htη : t * (12 * B ^ 2 + 1) ≤ η) (htκ : t * (2 * B) ≤ κ) :
    0 < k0 + t * d0 ∧ (k2 + t * d2) * (k0 + t * d0) - (k1 + t * d1) ^ 2 ≤
      -(η / (2 * (4 * B ^ 2 + 1))) * (k0 + t * d0) ^ 2 := by
  have hB0 : 0 ≤ B := by linarith
  have hη : 0 ≤ η := le_trans (by positivity) htη
  have prod : ∀ {a b : ℝ}, |a| ≤ B → |b| ≤ B → -(B * B) ≤ a * b ∧ a * b ≤ B * B := by
    intro a b ha hb
    have h : |a * b| ≤ B * B := by
      rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hB0
    exact abs_le.1 h
  have p1 := prod hk2 hd0
  have p2 := prod hd2 hk0
  have p3 := prod hk1 hd1
  have p4 := prod hd2 hd0
  have p5 := prod hd1 hd1
  have hM1 : k2 * d0 + d2 * k0 - 2 * k1 * d1 ≤ 4 * (B * B) := by linarith [p1.2, p2.2, p3.1]
  have hM2 : d2 * d0 - d1 ^ 2 ≤ 2 * (B * B) := by
    have : d1 ^ 2 = d1 * d1 := sq d1
    linarith [p4.2, p5.1]
  obtain ⟨hd0l, hd0u⟩ := abs_le.1 hd0
  obtain ⟨hk0l, hk0u⟩ := abs_le.1 hk0
  have htd1 : t * d0 ≤ t * B := mul_le_mul_of_nonneg_left hd0u ht
  have htd2 : t * -B ≤ t * d0 := mul_le_mul_of_nonneg_left hd0l ht
  have htB : t * B ≤ B := by
    have := mul_le_mul_of_nonneg_right ht1 hB0
    linarith
  have hpos : 0 < k0 + t * d0 := by
    have : t * -B = -(t * B) := by ring
    linarith
  refine ⟨hpos, ?_⟩
  have a1 : t * (k2 * d0 + d2 * k0 - 2 * k1 * d1) ≤ t * (4 * (B * B)) :=
    mul_le_mul_of_nonneg_left hM1 ht
  have ht2 : t ^ 2 ≤ t := by
    calc t ^ 2 = t * t := sq t
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right ht1 ht
      _ = t := one_mul t
  have a2 : t ^ 2 * (d2 * d0 - d1 ^ 2) ≤ t * (2 * (B * B)) := by
    have hM2' : 0 ≤ 2 * (B * B) := by positivity
    calc t ^ 2 * (d2 * d0 - d1 ^ 2) ≤ t ^ 2 * (2 * (B * B)) :=
          mul_le_mul_of_nonneg_left hM2 (sq_nonneg t)
      _ ≤ t * (2 * (B * B)) := mul_le_mul_of_nonneg_right ht2 hM2'
  have hexp : (k2 + t * d2) * (k0 + t * d0) - (k1 + t * d1) ^ 2 =
      (k2 * k0 - k1 ^ 2) + t * (k2 * d0 + d2 * k0 - 2 * k1 * d1) + t ^ 2 * (d2 * d0 - d1 ^ 2) := by
    ring
  have hmove : (k2 + t * d2) * (k0 + t * d0) - (k1 + t * d1) ^ 2 ≤ -(η / 2) := by
    rw [hexp]
    have h6 : t * (4 * (B * B)) + t * (2 * (B * B)) ≤ η / 2 := by
      have e : t * (12 * B ^ 2 + 1) = 2 * (t * (4 * (B * B)) + t * (2 * (B * B))) + t := by ring
      linarith
    linarith
  have hsq : (k0 + t * d0) ^ 2 ≤ 4 * B ^ 2 := by
    have hup : k0 + t * d0 ≤ 2 * B := by linarith
    have hlo : -(2 * B) ≤ k0 + t * d0 := by
      have : t * -B = -(t * B) := by ring
      linarith
    calc (k0 + t * d0) ^ 2 ≤ (2 * B) ^ 2 := sq_le_sq' hlo hup
      _ = 4 * B ^ 2 := by ring
  have hδ : η / (2 * (4 * B ^ 2 + 1)) * (k0 + t * d0) ^ 2 ≤ η / 2 := by
    have hfrac : η / (2 * (4 * B ^ 2 + 1)) * (4 * B ^ 2) ≤ η / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ η * 2 := by positivity
      nlinarith
    calc η / (2 * (4 * B ^ 2 + 1)) * (k0 + t * d0) ^ 2
        ≤ η / (2 * (4 * B ^ 2 + 1)) * (4 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ η / 2 := hfrac
  linarith

/-- **Global positivity and uniform strong log-concavity for small `t`.** There are `ε, δ > 0`
such that for every `0 ≤ t < ε`, `k_t > 0` on `ℝ` and `k_t'' k_t - (k_t')² ≤ -δ k_t²`. -/
theorem exists_thetaDerivativePacket_numerator_le (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < ε → ∀ x : ℝ,
      0 < thetaDerivativePacket m t x ∧
        thetaDerivativePacketNumerator m t x ≤ -δ * thetaDerivativePacket m t x ^ 2 := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_thetaDerivativePacketNumerator_le m hm)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = max X₀ 0 := ⟨_, rfl⟩
  have hK : IsCompact (Icc (-L) L) := isCompact_Icc
  have hL0 : 0 ≤ L := hL ▸ le_max_right _ _
  have hKne : (Icc (-L) L).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨x₀, -, hx₀⟩ := hK.exists_isMaxOn hKne
    continuous_thetaCuspLogConcavityNumerator.continuousOn
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = -thetaCuspLogConcavityNumerator x₀ := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; linarith [thetaCuspLogConcavityNumerator_neg_all x₀]
  obtain ⟨x₁, -, hx₁⟩ := hK.exists_isMinOn hKne contDiff_thetaCuspFullSource.continuous.continuousOn
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = thetaCuspFullSource x₁ := ⟨_, rfl⟩
  have hκ : 0 < κ := hκdef ▸ thetaCuspFullSource_pos_all x₁
  have hg : Continuous fun x => |thetaCuspFullSource x| + |iteratedDeriv 1 thetaCuspFullSource x| +
      |iteratedDeriv 2 thetaCuspFullSource x| + |iteratedDeriv (4 * m) thetaCuspFullSource x| +
      |iteratedDeriv (1 + 4 * m) thetaCuspFullSource x| +
      |iteratedDeriv (2 + 4 * m) thetaCuspFullSource x| := by
    have c0 := contDiff_thetaCuspFullSource.continuous
    have c1 := continuous_iteratedDeriv_thetaCuspFullSource 1
    have c2 := continuous_iteratedDeriv_thetaCuspFullSource 2
    have c3 := continuous_iteratedDeriv_thetaCuspFullSource (4 * m)
    have c4 := continuous_iteratedDeriv_thetaCuspFullSource (1 + 4 * m)
    have c5 := continuous_iteratedDeriv_thetaCuspFullSource (2 + 4 * m)
    fun_prop
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max B₀ 1 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := hBdef ▸ le_max_right _ _
  have hBd : ∀ x ∈ Icc (-L) L, |thetaCuspFullSource x| + |iteratedDeriv 1 thetaCuspFullSource x| +
      |iteratedDeriv 2 thetaCuspFullSource x| + |iteratedDeriv (4 * m) thetaCuspFullSource x| +
      |iteratedDeriv (1 + 4 * m) thetaCuspFullSource x| +
      |iteratedDeriv (2 + 4 * m) thetaCuspFullSource x| ≤ B := fun x hx =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB₀ x hx)).trans
      (hBdef ▸ le_max_left _ _)
  have hB0 : 0 < B := by linarith
  refine ⟨min 1 (min (η / (12 * B ^ 2 + 1)) (κ / (2 * B))), by positivity,
    min 1 (η / (2 * (4 * B ^ 2 + 1))), by positivity, ?_⟩
  intro t ht htε
  have ht1 : t ≤ 1 := htε.le.trans (min_le_left _ _)
  have htη : t * (12 * B ^ 2 + 1) ≤ η :=
    (le_div_iff₀ (by positivity)).1 (htε.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htκ : t * (2 * B) ≤ κ :=
    (le_div_iff₀ (by positivity)).1 (htε.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hnum : ∀ x, thetaDerivativePacketNumerator m t x =
      (iteratedDeriv 2 thetaCuspFullSource x + t * iteratedDeriv (2 + 4 * m) thetaCuspFullSource x) *
        (thetaCuspFullSource x + t * iteratedDeriv (4 * m) thetaCuspFullSource x) -
      (iteratedDeriv 1 thetaCuspFullSource x + t * iteratedDeriv (1 + 4 * m) thetaCuspFullSource x) ^ 2 := by
    intro x
    unfold thetaDerivativePacketNumerator
    rw [iteratedDeriv_thetaDerivativePacket, iteratedDeriv_thetaDerivativePacket]
    rfl
  have hcompact : ∀ x ∈ Icc (-L) L, 0 < thetaDerivativePacket m t x ∧
      thetaDerivativePacketNumerator m t x ≤
        -(η / (2 * (4 * B ^ 2 + 1))) * thetaDerivativePacket m t x ^ 2 := by
    intro x hx
    have hb := hBd x hx
    have hN0 : iteratedDeriv 2 thetaCuspFullSource x * thetaCuspFullSource x -
        iteratedDeriv 1 thetaCuspFullSource x ^ 2 ≤ -η := by
      rw [hηdef, neg_neg]; exact hx₀ hx
    have hκx : κ ≤ thetaCuspFullSource x := hκdef ▸ hx₁ hx
    have a0 := abs_nonneg (thetaCuspFullSource x)
    have a1 := abs_nonneg (iteratedDeriv 1 thetaCuspFullSource x)
    have a2 := abs_nonneg (iteratedDeriv 2 thetaCuspFullSource x)
    have a3 := abs_nonneg (iteratedDeriv (4 * m) thetaCuspFullSource x)
    have a4 := abs_nonneg (iteratedDeriv (1 + 4 * m) thetaCuspFullSource x)
    have a5 := abs_nonneg (iteratedDeriv (2 + 4 * m) thetaCuspFullSource x)
    have h := thetaPacket_compact_numerator_le (k0 := thetaCuspFullSource x)
      (k1 := iteratedDeriv 1 thetaCuspFullSource x) (k2 := iteratedDeriv 2 thetaCuspFullSource x)
      (d0 := iteratedDeriv (4 * m) thetaCuspFullSource x)
      (d1 := iteratedDeriv (1 + 4 * m) thetaCuspFullSource x)
      (d2 := iteratedDeriv (2 + 4 * m) thetaCuspFullSource x) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) hB1 hN0 hκx hκ ht ht1 htη htκ
    rw [hnum x]
    exact h
  intro x
  rcases le_or_gt |x| L with hx | hx
  · have hmem : x ∈ Icc (-L) L := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    obtain ⟨h1, h2⟩ := hcompact x hmem
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)
  · have htail : ∀ y, L < y → 0 < thetaDerivativePacket m t y ∧
        thetaDerivativePacketNumerator m t y ≤
          -(min 1 (η / (2 * (4 * B ^ 2 + 1)))) * thetaDerivativePacket m t y ^ 2 := by
      intro y hy
      have hy' : X₀ ≤ y := le_of_lt (lt_of_le_of_lt (hL ▸ le_max_left _ _) hy)
      obtain ⟨h1, h2⟩ := hX₀ y hy' t ht
      refine ⟨h1, h2.trans ?_⟩
      have := mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left 1 (η / (2 * (4 * B ^ 2 + 1)))))
        (sq_nonneg (thetaDerivativePacket m t y))
      linarith
    rcases le_or_gt 0 x with hx0 | hx0
    · exact htail x (by rwa [abs_of_nonneg hx0] at hx)
    · have := htail (-x) (by rwa [abs_of_neg hx0] at hx)
      rwa [thetaDerivativePacket_neg, thetaDerivativePacketNumerator_neg] at this

/-- The second logarithmic derivative of a positive `k_t` is its normalized numerator. -/
theorem iteratedDeriv_two_log_thetaDerivativePacket (m : ℕ) (t : ℝ)
    (hpos : ∀ y, 0 < thetaDerivativePacket m t y) (x : ℝ) :
    iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x =
      thetaDerivativePacketNumerator m t x / thetaDerivativePacket m t x ^ 2 := by
  have h0 : ∀ y, HasDerivAt (thetaDerivativePacket m t)
      (iteratedDeriv 1 (thetaDerivativePacket m t) y) y := by
    intro y
    have h := hasDerivAt_iteratedDeriv_thetaDerivativePacket m t 0 y
    rwa [iteratedDeriv_zero] at h
  have h1 : ∀ y, HasDerivAt (iteratedDeriv 1 (thetaDerivativePacket m t))
      (iteratedDeriv 2 (thetaDerivativePacket m t) y) y :=
    hasDerivAt_iteratedDeriv_thetaDerivativePacket m t 1
  have hderiv : deriv (fun y => Real.log (thetaDerivativePacket m t y)) =
      fun y => iteratedDeriv 1 (thetaDerivativePacket m t) y / thetaDerivativePacket m t y := by
    funext y
    exact ((h0 y).log (hpos y).ne').deriv
  rw [show iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x =
      deriv (deriv (fun y => Real.log (thetaDerivativePacket m t y))) x by
    simp [iteratedDeriv_succ], hderiv]
  unfold thetaDerivativePacketNumerator
  show deriv (iteratedDeriv 1 (thetaDerivativePacket m t) / thetaDerivativePacket m t) x = _
  rw [((h1 x).div (h0 x) (hpos x).ne').deriv]
  ring

/-- **Positivity and global strong log-concavity (1).** For all sufficiently small `t ≥ 0`,
`k_t > 0` on `ℝ` and `(log k_t)'' ≤ -δ` for one `δ > 0` independent of `t`. -/
theorem exists_thetaDerivativePacket_stronglyLogConcave (m : ℕ) (hm : 0 < m) :
    ∃ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → t < ε →
      (∀ x, 0 < thetaDerivativePacket m t x) ∧
        ∀ x, iteratedDeriv 2 (fun y => Real.log (thetaDerivativePacket m t y)) x ≤ -δ := by
  obtain ⟨ε, hε, δ, hδ, h⟩ := exists_thetaDerivativePacket_numerator_le m hm
  refine ⟨ε, hε, δ, hδ, fun t ht htε => ⟨fun x => (h t ht htε x).1, fun x => ?_⟩⟩
  have hpos : ∀ y, 0 < thetaDerivativePacket m t y := fun y => (h t ht htε y).1
  rw [iteratedDeriv_two_log_thetaDerivativePacket m t hpos, div_le_iff₀ (by positivity [hpos x])]
  exact (h t ht htε x).2

/-! ## Schwartz regularity, exponential moments and convergence -/

theorem iterate_derivCLM_apply (n : ℕ) (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    ((SchwartzMap.derivCLM ℝ ℝ)^[n] f) x = iteratedDeriv n f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', SchwartzMap.derivCLM_apply, iteratedDeriv_succ]
      congr 1
      funext y
      exact ih y

/-- `k_t` as a real Schwartz function. -/
def thetaDerivativePacketSchwartz (m : ℕ) (t : ℝ) : SchwartzMap ℝ ℝ :=
  thetaCuspSchwartzReal + t • ((SchwartzMap.derivCLM ℝ ℝ)^[4 * m] thetaCuspSchwartzReal)

@[simp] theorem thetaDerivativePacketSchwartz_apply (m : ℕ) (t x : ℝ) :
    thetaDerivativePacketSchwartz m t x = thetaDerivativePacket m t x := by
  have hco : (⇑thetaCuspSchwartzReal : ℝ → ℝ) = thetaCuspFullSource := rfl
  simp [thetaDerivativePacketSchwartz, iterate_derivCLM_apply, thetaDerivativePacket, hco]

/-- `k_t → k` in the Schwartz topology as `t → 0`. -/
theorem tendsto_thetaDerivativePacketSchwartz (m : ℕ) :
    Tendsto (thetaDerivativePacketSchwartz m) (𝓝 0) (𝓝 thetaCuspSchwartzReal) := by
  have h : Tendsto (fun t : ℝ => thetaCuspSchwartzReal +
      t • ((SchwartzMap.derivCLM ℝ ℝ)^[4 * m] thetaCuspSchwartzReal)) (𝓝 0)
      (𝓝 (thetaCuspSchwartzReal + (0 : ℝ) • ((SchwartzMap.derivCLM ℝ ℝ)^[4 * m]
        thetaCuspSchwartzReal))) :=
    tendsto_const_nhds.add (tendsto_id.smul tendsto_const_nhds)
  rwa [zero_smul, add_zero] at h

/-- `k_t` has every exponential moment. -/
theorem integrable_exp_abs_mul_abs_thetaDerivativePacket (m : ℕ) (t c : ℝ) :
    Integrable (fun x => Real.exp (c * |x|) * |thetaDerivativePacket m t x|) := by
  have h := (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 0 c).add
    ((integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource (4 * m) c).const_mul |t|)
  refine h.mono' (by
    have := contDiff_thetaDerivativePacket m t
    exact (by fun_prop : Continuous fun x =>
      Real.exp (c * |x|) * |thetaDerivativePacket m t x|).aestronglyMeasurable) ?_
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply, iteratedDeriv_zero, thetaDerivativePacket]
  have := abs_add_le (thetaCuspFullSource x) (t * iteratedDeriv (4 * m) thetaCuspFullSource x)
  rw [abs_mul] at this
  have he := Real.exp_pos (c * |x|)
  nlinarith

/-- Every exponentially weighted derivative seminorm of `k_t - k` is `O(|t|)`. -/
theorem exists_expWeighted_iteratedDeriv_thetaDerivativePacket_sub_le (m : ℕ) (A : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ t x : ℝ, Real.exp (A * |x|) *
      |iteratedDeriv n (fun y => thetaDerivativePacket m t y - thetaCuspFullSource y) x| ≤ |t| * C := by
  obtain ⟨C, hC⟩ := thetaCuspFullSource_derivative_exp_bound A (n + 4 * m)
  refine ⟨C, fun t x => ?_⟩
  have hfun : (fun y => thetaDerivativePacket m t y - thetaCuspFullSource y) =
      fun y => t * iteratedDeriv (4 * m) thetaCuspFullSource y := by
    funext y; simp [thetaDerivativePacket]
  rw [hfun, iteratedDeriv_const_mul t ((contDiff_iteratedDeriv_thetaCuspFullSource _).contDiffAt.of_le
    (by exact_mod_cast le_top)), iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply, ← iteratedDeriv_eq_iterate, abs_mul]
  have := hC x
  have hx := Real.exp_pos (A * |x|)
  nlinarith [abs_nonneg t, abs_nonneg (iteratedDeriv (n + 4 * m) thetaCuspFullSource x)]

/-! ## The relative tail growth (5) -/

theorem tendsto_thetaAtomRatio_div_scale_pow (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x => thetaAtomRatio (4 * m) x /
      (2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m)) atTop (𝓝 1) := by
  set r := 4 * m
  set P : ℝ[X] := thetaCuspSeedPolynomial * (C (2 * Real.pi) * X ^ 2) ^ r
  have hlc0 : thetaCuspSeedPolynomial.leadingCoeff = 4 * Real.pi ^ 2 := by
    have := (thetaCuspLogDerivativePolynomial_degree_leading 0).2
    rw [show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl] at this
    rw [this, pow_zero, mul_one]
  have hseed0 : thetaCuspSeedPolynomial ≠ 0 := by
    intro h
    rw [h, leadingCoeff_zero] at hlc0
    have : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
    linarith
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hmono : (C (2 * Real.pi) * X ^ 2 : ℝ[X]) ≠ 0 := by
    rw [Ne, mul_eq_zero, not_or]; exact ⟨by simp, pow_ne_zero _ X_ne_zero⟩
  have hnat : P.natDegree = 4 + 2 * r := by
    rw [natDegree_mul hseed0 (pow_ne_zero _ hmono), natDegree_pow, natDegree_C_mul_X_pow 2 _ hπ]
    have := natDegree_thetaCuspLogDerivativePolynomial 0
    rw [show thetaCuspLogDerivativePolynomial 0 = thetaCuspSeedPolynomial from rfl] at this
    rw [this]
    ring
  have hlc : P.leadingCoeff = 4 * Real.pi ^ 2 * (2 * Real.pi) ^ r := by
    rw [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C_mul_X_pow, hlc0]
  have hdeg : 0 < P.degree := by
    rw [degree_eq_natDegree (by intro h; rw [h, natDegree_zero] at hnat; omega), hnat]
    exact_mod_cast (by omega : 0 < 4 + 2 * r)
  have hQ := natDegree_thetaCuspLogDerivativePolynomial r
  have hlim := tendsto_eval_div_eval_of_natDegree_le P (thetaCuspLogDerivativePolynomial r) hdeg
    (by rw [hQ, hnat])
  have hcoeff : (thetaCuspLogDerivativePolynomial r).coeff P.natDegree =
      4 * Real.pi ^ 2 * (-(2 * Real.pi)) ^ r := by
    rw [hnat, ← hQ, coeff_natDegree, (thetaCuspLogDerivativePolynomial_degree_leading r).2]
  rw [hcoeff, hlc] at hlim
  have hval : 4 * Real.pi ^ 2 * (-(2 * Real.pi)) ^ r / (4 * Real.pi ^ 2 * (2 * Real.pi) ^ r) = 1 := by
    rw [Even.neg_pow ⟨2 * m, by ring⟩]
    field_simp
  rw [hval] at hlim
  refine (hlim.comp Real.tendsto_exp_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp, thetaAtomRatio, P, eval_mul, eval_pow, eval_C, eval_X, thetaTailScale_eq]
  rw [div_div]
  congr 1
  ring

theorem tendsto_thetaSourceRatio_div_scale_pow (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x => thetaSourceRatio (4 * m) x /
      (2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m)) atTop (𝓝 1) := by
  have hinv : ThetaTailModerate (fun x =>
      ((2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m))⁻¹) := by
    refine ThetaTailModerate.inv_of_ge one_pos ?_
    filter_upwards [eventually_one_le_thetaTailScale] with x hx
    exact one_le_pow₀ (by linarith)
  have hc : ThetaTailClose (fun x => thetaSourceRatio (4 * m) x /
      (2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m))
      (fun x => thetaAtomRatio (4 * m) x /
        (2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m)) :=
    (ThetaTailNegligible.mul_moderate (thetaSourceRatio_close (4 * m)) hinv).congr'
      (Eventually.of_forall fun x => by simp only; rw [div_eq_mul_inv, div_eq_mul_inv]; ring)
  exact hc.tendsto (tendsto_thetaAtomRatio_div_scale_pow m hm)

/-- **Relative tail growth (5).** `(k_t - k)/k ~ t (2π e^{2x})^{4m}` as `x → +∞`. -/
theorem tendsto_thetaDerivativePacket_relative_div (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun x => ((thetaDerivativePacket m t x - thetaCuspFullSource x) /
      thetaCuspFullSource x) / (t * (2 * Real.pi * Real.exp (2 * x)) ^ (4 * m))) atTop (𝓝 1) := by
  refine (tendsto_thetaSourceRatio_div_scale_pow m hm).congr fun x => ?_
  have hq : 2 * thetaCuspSingleAtomReflectionScale 1 x = 2 * Real.pi * Real.exp (2 * x) := by
    unfold thetaCuspSingleAtomReflectionScale; simp; ring
  rw [hq, thetaSourceRatio]
  simp only [thetaDerivativePacket, add_sub_cancel_left]
  field_simp

/-- For fixed `t > 0` the relative perturbation `(k_t - k)/k` tends to `+∞`. -/
theorem tendsto_thetaDerivativePacket_relative_atTop (m : ℕ) (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x => (thetaDerivativePacket m t x - thetaCuspFullSource x) /
      thetaCuspFullSource x) atTop atTop := by
  have hscale : Tendsto (fun x => t * (2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m))
      atTop atTop :=
    ((tendsto_pow_atTop (by omega)).comp
      (tendsto_thetaTailScale.const_mul_atTop two_pos)).const_mul_atTop ht
  have hratio := (tendsto_thetaSourceRatio_div_scale_pow m hm)
  have hprod := hratio.pos_mul_atTop one_pos hscale
  refine hprod.congr' ?_
  filter_upwards with x
  have hpos : 0 < (2 * thetaCuspSingleAtomReflectionScale 1 x) ^ (4 * m) := by
    have := thetaTailScale_pos x; positivity
  simp only [thetaSourceRatio, thetaDerivativePacket, add_sub_cancel_left]
  field_simp

end

end RHTower
