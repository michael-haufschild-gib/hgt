import GaloisForLFunctions.RHTower.HerglotzProducerAtomDomination
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitCounting

/-!
# Herglotz producers whose quotient by `ξ` is singular only on a sparse set of zeros are `Λ`

Keep the setting of `HerglotzProducerAtomDomination`: `Re Φ ≥ 0` on `Re s > ½`,
`Φ = Γ̃ + 1/(s − 1) − Σ_{n≥2} lam(n)n^{−s}` on `Re s > 1`, `G' = ΦG`, and
`G = s(s−1)Γ_ℝ(s)ζ(s)A(s)` on `Re s > ½` (`s ≠ 1`) with `A` holomorphic there.

**Theorem** (`eq_vonMangoldt_of_quotient_sparseRays`).  Let `S` be a set of ordinates.  Suppose `A`
is bounded on `½ + ε + iγ`, `0 < ε < 1`, at every zero `½ + iγ` of `ξ` with `γ ∉ S`, and that the
zeros with ordinate in `S`, counted with multiplicity, have lower density zero:
`#{zeros in S with 0 < γ ≤ T} ≤ ηT` along arbitrarily large `T`, for every `η > 0`.  Then
`lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds.

In phase language: a Herglotz producer whose boundary phase falls short of `ξ`'s jump only at a
density-zero set of zeros (fractional atoms, step phases) is the true producer.  The sparse part of
the twin door is closed.

**Proof.**
* The zeros off `S` carry full atoms of the Poisson representation of `Re Φ` (`atom_of_rayBounded`),
  so on `σ > 1` the weighted atom domination gives
  `Re Φ − Re ξ'/ξ ≥ −Σ_{γ_q ∈ S} A_q(σ, t)`.
* The left side is the cosine series of the deviation `Λ − lam`.  The right side is a weighted
  Poisson envelope; each copy has `t`-mass at most `π`, and far copies are dominated by
  `Re ξ'/ξ(√T + it) = O(log T)` (`integral_rayEnvelope_le`, the counting step of the corpus deficit
  law for an arbitrary weight `0 ≤ c ≤ 1`).
* The Cesàro mean of the envelope tends to `0` along a sequence, and the Bohr envelope bound kills
  every coefficient.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

namespace RHTower.AtomDomination

open GaloisForLFunctions.HTGeometry RHTower.IntegerMassRigidity RHTower.WeilSpectral

/-! ## Weighted Poisson envelopes and their counting bound -/

/-- The weighted Poisson envelope `Σ_q c(q) A_q(σ, t)`. -/
def rayEnvelope (c : XiZeroCopy → ℝ) (σ t : ℝ) : ℝ := ∑' q, c q * copyPoisson σ t q

/-- The weight `c(q)` on copies with ordinate in `(0, T]`, and `0` otherwise. -/
def rayWindowWeight (c : XiZeroCopy → ℝ) (T : ℝ) (q : XiZeroCopy) : ℝ :=
  if 0 < ((q.1 : ℂ)).im ∧ ((q.1 : ℂ)).im ≤ T then c q else 0

/-- The weighted count `Σ_{0 < γ_q ≤ T} c(q)`. -/
def rayWindowCount (c : XiZeroCopy → ℝ) (T : ℝ) : ℝ := ∑' q, rayWindowWeight c T q

theorem rayWindowWeight_nonneg {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) (T : ℝ)
    (q : XiZeroCopy) : 0 ≤ rayWindowWeight c T q := by
  unfold rayWindowWeight
  split_ifs
  · exact hc0 q
  · exact le_rfl

theorem rayWindowWeight_le_one {c : XiZeroCopy → ℝ} (hc1 : ∀ q, c q ≤ 1) (T : ℝ)
    (q : XiZeroCopy) : rayWindowWeight c T q ≤ 1 := by
  unfold rayWindowWeight
  split_ifs
  · exact hc1 q
  · exact zero_le_one

theorem rayEnvelope_nonneg {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) : 0 ≤ rayEnvelope c σ t :=
  tsum_nonneg fun q => mul_nonneg (hc0 q) (copyPoisson_pos hσ.le t q).le

theorem continuous_rayEnvelope {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) (hc1 : ∀ q, c q ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) : Continuous (rayEnvelope c σ) :=
  continuous_weighted_copyPoisson hσ hc0 hc1

theorem rayEnvelope_le_re_logDeriv_xi {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q)
    (hc1 : ∀ q, c q ≤ 1) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    rayEnvelope c σ t ≤ (logDeriv xi ((σ : ℂ) + t * I)).re := by
  rw [re_logDeriv_xi_eq_tsum_copyPoisson hσ t]
  refine (summable_deficit_mul_copyPoisson hσ t hc0 hc1).tsum_le_tsum (fun q => ?_)
    (summable_copyPoisson hσ t)
  have := mul_le_mul_of_nonneg_right (hc1 q) (copyPoisson_pos hσ.le t q).le
  linarith

/-- **Splitting off the window.**  For `H ≤ t ≤ T − H`, the envelope is at most its window part
plus `(2σ/(H − 1)) Re ξ'/ξ(H + it)`. -/
theorem rayEnvelope_le_window {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) (hc1 : ∀ q, c q ≤ 1)
    {σ H T t : ℝ} (hσ : 1 < σ) (hH : 1 < H) (htH : H ≤ t) (htT : t ≤ T - H) :
    rayEnvelope c σ t ≤ ∑' q, rayWindowWeight c T q * copyPoisson σ t q +
      2 * σ / (H - 1) * ∑' q, copyPoisson H t q := by
  have hk : 0 ≤ 2 * σ / (H - 1) := div_nonneg (by linarith) (by linarith)
  have hs1 := summable_deficit_mul_copyPoisson hσ t (rayWindowWeight_nonneg hc0 T)
    (rayWindowWeight_le_one hc1 T)
  have hs2 := (summable_copyPoisson hH t).mul_left (2 * σ / (H - 1))
  rw [rayEnvelope, ← tsum_mul_left, ← hs1.tsum_add hs2]
  refine (summable_deficit_mul_copyPoisson hσ t hc0 hc1).tsum_le_tsum (fun q => ?_)
    (hs1.add hs2)
  have hA := (copyPoisson_pos hσ.le t q).le
  have hAH := (copyPoisson_pos hH.le t q).le
  by_cases hw : 0 < ((q.1 : ℂ)).im ∧ ((q.1 : ℂ)).im ≤ T
  · rw [rayWindowWeight, if_pos hw]
    have := mul_nonneg hk hAH
    linarith
  · rw [rayWindowWeight, if_neg hw, zero_mul, zero_add]
    have hfar : H ≤ |t - ((q.1 : ℂ)).im| := by
      rcases not_and_or.mp hw with h | h
      · push Not at h
        rw [abs_of_nonneg (by linarith)]
        linarith
      · push Not at h
        rw [abs_of_neg (by linarith)]
        linarith
    calc c q * copyPoisson σ t q ≤ 1 * copyPoisson σ t q :=
          mul_le_mul_of_nonneg_right (hc1 q) hA
      _ ≤ _ := by rw [one_mul]; exact copyPoisson_le_shift hσ.le hH q hfar

/-- The window part has total mass at most `π D_c(T)` on every interval. -/
theorem integral_rayWindow_le {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) {σ T : ℝ} (hσ : 1 < σ)
    (hT : 0 ≤ T) (a b : ℝ) :
    ∫ t in a..b, ∑' q, rayWindowWeight c T q * copyPoisson σ t q ≤ π * rayWindowCount c T := by
  have hfin := finite_xiZeroCopy_band (T / 2) (by linarith : (0 : ℝ) ≤ T / 2)
  set S := hfin.toFinset
  have hzero : ∀ q ∉ S, rayWindowWeight c T q = 0 := by
    intro q hq
    rw [rayWindowWeight, if_neg]
    intro h
    apply hq
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, abs_le]
    constructor <;> linarith [h.1, h.2]
  have hsum : ∀ t, ∑' q, rayWindowWeight c T q * copyPoisson σ t q =
      ∑ q ∈ S, rayWindowWeight c T q * copyPoisson σ t q :=
    fun t => tsum_eq_sum fun q hq => by rw [hzero q hq, zero_mul]
  have hD : rayWindowCount c T = ∑ q ∈ S, rayWindowWeight c T q :=
    tsum_eq_sum fun q hq => hzero q hq
  simp_rw [hsum]
  rw [intervalIntegral.integral_finsetSum
    (f := fun q t => rayWindowWeight c T q * copyPoisson σ t q)
    fun q _ => ((continuous_copyPoisson hσ.le q).const_mul _).intervalIntegrable _ _,
    hD, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [intervalIntegral.integral_const_mul, mul_comm π]
  exact mul_le_mul_of_nonneg_left (integral_copyPoisson_le_pi hσ.le q a b)
    (rayWindowWeight_nonneg hc0 T q)

/-- **The counting bound.**  For `T ≥ 64` and `σ ≤ √T`,
`∫_8^T Σ_q c(q) A_q(σ, ·) ≤ π D_c(T) + (2 + 4σ)√T (½ log T + C_σ)`. -/
theorem integral_rayEnvelope_le {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q) (hc1 : ∀ q, c q ≤ 1)
    {σ T : ℝ} (hσ : 1 < σ) (hT : 64 ≤ T) (hσT : σ ≤ √T) :
    ∫ t in (8 : ℝ)..T, rayEnvelope c σ t ≤
      π * rayWindowCount c T + (2 + 4 * σ) * √T * (Real.log T / 2 + envelopeConst σ) := by
  set H := √T with hHdef
  have hH8 : 8 ≤ H := by
    rw [hHdef, show (8 : ℝ) = √64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have hHsq : H * H = T := Real.mul_self_sqrt (by linarith)
  have h2H : 2 * H ≤ T := by nlinarith
  have hHT : H ≤ T := by nlinarith
  set B := Real.log T / 2 + envelopeConst σ with hB
  have hB0 : 0 ≤ B := by
    have h1 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ 1 / σ := by positivity
    have h3 : 0 ≤ 1 / (σ - 1) := one_div_nonneg.mpr (by linarith)
    have h4 := vonMangoldtMajorant_nonneg σ
    rw [hB, envelopeConst]
    linarith
  have hcε := continuous_rayEnvelope hc0 hc1 hσ
  have hi : ∀ a b, IntervalIntegrable (rayEnvelope c σ) volume a b :=
    fun a b => hcε.intervalIntegrable a b
  have hP : ∀ t, 8 ≤ t → t ≤ T → rayEnvelope c σ t ≤ B := fun t ht htT =>
    (rayEnvelope_le_re_logDeriv_xi hc0 hc1 hσ t).trans
      (re_logDeriv_xi_le_log hσ le_rfl (by linarith) ht htT)
  have hPH : ∀ t, 8 ≤ t → t ≤ T → ∑' q, copyPoisson H t q ≤ B := fun t ht htT => by
    rw [← re_logDeriv_xi_eq_tsum_copyPoisson (by linarith) t]
    exact re_logDeriv_xi_le_log hσ hσT hHT ht htT
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 8 H) (hi H T),
    ← intervalIntegral.integral_add_adjacent_intervals (hi H (T - H)) (hi (T - H) T)]
  have hend1 : ∫ t in (8 : ℝ)..H, rayEnvelope c σ t ≤ H * B := by
    calc _ ≤ ∫ _ in (8 : ℝ)..H, B :=
          intervalIntegral.integral_mono_on hH8 (hi _ _) intervalIntegrable_const
            fun t ht => hP t ht.1 (by linarith [ht.2])
      _ = (H - 8) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ H * B := by nlinarith
  have hend2 : ∫ t in (T - H)..T, rayEnvelope c σ t ≤ H * B := by
    calc _ ≤ ∫ _ in (T - H)..T, B :=
          intervalIntegral.integral_mono_on (by linarith) (hi _ _) intervalIntegrable_const
            fun t ht => hP t (by linarith [ht.1]) ht.2
      _ = H * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hk : 0 ≤ 2 * σ / (H - 1) := div_nonneg (by linarith) (by linarith)
  have hW1 : Continuous fun t => ∑' q, rayWindowWeight c T q * copyPoisson σ t q :=
    continuous_weighted_copyPoisson hσ (rayWindowWeight_nonneg hc0 T)
      (rayWindowWeight_le_one hc1 T)
  have hP1 : Continuous fun t => ∑' q, copyPoisson H t q :=
    continuous_tsum_copyPoisson (by linarith)
  have hmidP : ∫ t in H..(T - H), ∑' q, copyPoisson H t q ≤ (T - 2 * H) * B := by
    calc _ ≤ ∫ _ in H..(T - H), B :=
          intervalIntegral.integral_mono_on (by linarith) (hP1.intervalIntegrable _ _)
            intervalIntegrable_const fun t ht => hPH t (by linarith [ht.1]) (by linarith [ht.2])
      _ = (T - 2 * H) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hmid : ∫ t in H..(T - H), rayEnvelope c σ t ≤
      π * rayWindowCount c T + 2 * σ / (H - 1) * ((T - 2 * H) * B) := by
    calc ∫ t in H..(T - H), rayEnvelope c σ t
        ≤ ∫ t in H..(T - H), (∑' q, rayWindowWeight c T q * copyPoisson σ t q +
            2 * σ / (H - 1) * ∑' q, copyPoisson H t q) :=
          intervalIntegral.integral_mono_on (by linarith) (hi _ _)
            ((hW1.add (hP1.const_mul _)).intervalIntegrable _ _)
            fun t ht => rayEnvelope_le_window hc0 hc1 hσ (by linarith) ht.1 ht.2
      _ = (∫ t in H..(T - H), ∑' q, rayWindowWeight c T q * copyPoisson σ t q) +
            2 * σ / (H - 1) * ∫ t in H..(T - H), ∑' q, copyPoisson H t q := by
          rw [intervalIntegral.integral_add (hW1.intervalIntegrable _ _)
            ((hP1.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
      _ ≤ π * rayWindowCount c T + 2 * σ / (H - 1) * ((T - 2 * H) * B) :=
          add_le_add (integral_rayWindow_le hc0 hσ (by linarith) _ _)
            (mul_le_mul_of_nonneg_left hmidP hk)
  have hkT : 2 * σ / (H - 1) * T ≤ 4 * σ * H := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hkB : 2 * σ / (H - 1) * ((T - 2 * H) * B) ≤ 4 * σ * H * B := by
    calc 2 * σ / (H - 1) * ((T - 2 * H) * B) ≤ 2 * σ / (H - 1) * (T * B) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hk
      _ = (2 * σ / (H - 1) * T) * B := by ring
      _ ≤ 4 * σ * H * B := mul_le_mul_of_nonneg_right hkT hB0
  have hexp : (2 + 4 * σ) * H * B = 2 * (H * B) + 4 * σ * H * B := by ring
  linarith

/-- **Sparse envelopes have mean zero.**  If `D_c(T) ≤ ηT` along arbitrarily large `T` for every
`η > 0`, the Cesàro means of `Σ_q c(q) A_q(σ, ·)` are `≤ η` along arbitrarily large `T`. -/
theorem frequently_mean_rayEnvelope_le {c : XiZeroCopy → ℝ} (hc0 : ∀ q, 0 ≤ c q)
    (hc1 : ∀ q, c q ≤ 1) {σ : ℝ} (hσ : 1 < σ)
    (hsparse : ∀ η > 0, ∃ᶠ T in atTop, rayWindowCount c T ≤ η * T) :
    ∀ η > 0, ∃ᶠ T in atTop, (∫ t in (8 : ℝ)..T, rayEnvelope c σ t) / T ≤ 0 + η := by
  intro η hη
  have hev : ∀ᶠ T in atTop, 64 ≤ T ∧ σ ^ 2 ≤ T ∧
      (2 + 4 * σ) * (Real.log T / 2 + envelopeConst σ) / √T ≤ η / 2 :=
    (eventually_ge_atTop 64).and ((eventually_ge_atTop (σ ^ 2)).and
      ((tendsto_envelopeError σ).eventually (ge_mem_nhds (by linarith))))
  refine (hev.and_frequently (hsparse (η / (2 * π)) (by positivity))).mono fun T hT' => ?_
  obtain ⟨⟨hT, hσT, herr⟩, hD⟩ := hT'
  have hT0 : 0 < T := by linarith
  have hσT' : σ ≤ √T := by
    rw [show σ = √(σ ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt hσT
  have hI := integral_rayEnvelope_le hc0 hc1 hσ hT hσT'
  have hsq : √T * √T = T := Real.mul_self_sqrt hT0.le
  have hsqpos : 0 < √T := Real.sqrt_pos.mpr hT0
  rw [zero_add, div_le_iff₀ hT0]
  have h1 : π * rayWindowCount c T ≤ π * (η / (2 * π) * T) :=
    mul_le_mul_of_nonneg_left hD Real.pi_pos.le
  have h2 : (2 + 4 * σ) * √T * (Real.log T / 2 + envelopeConst σ) ≤ η / 2 * T := by
    have := mul_le_mul_of_nonneg_right herr hsqpos.le
    rw [div_mul_eq_mul_div, div_le_iff₀ hsqpos] at this
    calc (2 + 4 * σ) * √T * (Real.log T / 2 + envelopeConst σ)
        = (2 + 4 * σ) * (Real.log T / 2 + envelopeConst σ) * √T := by ring
      _ ≤ η / 2 * √T * √T := this
      _ = η / 2 * T := by rw [mul_assoc, hsq]
  have h3 : π * (η / (2 * π) * T) = η / 2 * T := by
    field_simp
  linarith

/-! ## The theorem -/

/-- The indicator weight of the zero copies whose ordinate lies in `S`. -/
def ordinateSetWeight (S : Set ℝ) (q : XiZeroCopy) : ℝ := by
  classical
  exact if ((q.1 : ℂ)).im ∈ S then 1 else 0

theorem ordinateSetWeight_nonneg (S : Set ℝ) (q : XiZeroCopy) : 0 ≤ ordinateSetWeight S q := by
  unfold ordinateSetWeight
  split_ifs <;> norm_num

theorem ordinateSetWeight_le_one (S : Set ℝ) (q : XiZeroCopy) : ordinateSetWeight S q ≤ 1 := by
  unfold ordinateSetWeight
  split_ifs <;> norm_num

/-- **A Herglotz producer whose quotient by `ξ` is singular only on a sparse set of zeros is `Λ`.**
Keep the hypotheses of `eq_vonMangoldt_of_quotient_rayBounded`, but require the ray bound only at
the zeros `½ + iγ` with `γ ∉ S`, where the zeros with ordinate in `S` (with multiplicity) have
lower density zero.  Then `lam(n) = Λ(n)` for `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem eq_vonMangoldt_of_quotient_sparseRays {lam : ℕ → ℝ} {Φ G A : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    {S : Set ℝ}
    (hray : ∀ γ : ℝ, γ ∉ S → xi (1 / 2 + γ * I) = 0 →
      ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ‖A (1 / 2 + ε + γ * I)‖ ≤ C)
    (hsparse : ∀ η > 0, ∃ᶠ T in atTop, rayWindowCount (ordinateSetWeight S) T ≤ η * T) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  classical
  obtain ⟨hRHxi, hA0, hlogA⟩ := quotient_facts hΦd hGd hG2 hAd hGK
  obtain ⟨ν, hfin, hrep⟩ := exists_poissonRepresentation_halfPlane hΦd hΦre
  -- full atoms off `S`, no requirement on `S`
  set w : XiDivisorSupport → ℝ := fun ρ => if ((ρ : ℂ)).im ∈ S then 0 else 1 with hwdef
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ => by simp only [hwdef]; split_ifs <;> norm_num
  have hw1 : ∀ ρ, w ρ ≤ 1 := fun ρ => by simp only [hwdef]; split_ifs <;> norm_num
  have hatom : ∀ ρ : XiDivisorSupport,
      w ρ * (xiDivisorMult ρ : ℝ) ≤ (1 + ((ρ : ℂ)).im ^ 2) * ν.real (atomSet ((ρ : ℂ)).im) := by
    intro ρ
    by_cases hS : ((ρ : ℂ)).im ∈ S
    · simp only [hwdef, if_pos hS, zero_mul]
      exact mul_nonneg (by positivity) measureReal_nonneg
    · simp only [hwdef, if_neg hS, one_mul]
      refine atom_of_rayBounded hrep hRHxi hAd hA0 hlogA ρ (hray _ hS ?_)
      have hxiρ := xi_eq_zero_of_divisorSupport ρ
      have hρeq : (ρ : ℂ) = 1 / 2 + ((ρ : ℂ)).im * I :=
        Complex.ext (by simp [hRHxi _ hxiρ]) (by simp)
      rwa [← hρeq]
  have hc : ∀ q : XiZeroCopy, 1 - w q.1 = ordinateSetWeight S q := fun q => by
    simp only [hwdef, ordinateSetWeight]
    split_ifs <;> norm_num
  -- the cosine series of the deviation lies above the sparse envelope
  have hlow : ∀ t : ℝ, -rayEnvelope (ordinateSetWeight S) 2 t ≤
      logCosSeries (deviationCoeff lam 2) t := by
    intro t
    have hdom := tsum_weighted_copyPoisson_le_re hrep hΦre hRHxi hw0 hw1 hatom
      (σ := 2) (by norm_num) t
    have hs1 : Summable fun q : XiZeroCopy => w q.1 * copyPoisson 2 t q :=
      summable_deficit_mul_copyPoisson (by norm_num) t (c := fun q => w q.1)
        (fun q => hw0 q.1) (fun q => hw1 q.1)
    have hs2 := summable_copyPoisson (σ := 2) (by norm_num) t
    have henv : rayEnvelope (ordinateSetWeight S) 2 t =
        ∑' q, copyPoisson 2 t q - ∑' q : XiZeroCopy, w q.1 * copyPoisson 2 t q := by
      rw [rayEnvelope, ← hs2.tsum_sub hs1]
      refine tsum_congr fun q => ?_
      rw [← hc q]
      ring
    rw [← re_sub_re_logDeriv_xi_eq hsl hid (by norm_num) t, henv,
      ← re_logDeriv_xi_eq_tsum_copyPoisson (by norm_num) t]
    push_cast at hdom ⊢
    linarith
  have hcoeff : ∀ m : ℕ, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
    intro m hm
    have h := abs_le_four_mul_of_logCosSeries_envelope_frequently
      (summable_abs_deviationCoeff_of_summable hsl (σ := 2) (by norm_num))
      (by simp [deviationCoeff]) (by simp [deviationCoeff])
      (rayEnvelope_nonneg (ordinateSetWeight_nonneg S) (σ := 2) (by norm_num))
      (continuous_rayEnvelope (ordinateSetWeight_nonneg S) (ordinateSetWeight_le_one S)
        (σ := 2) (by norm_num))
      (frequently_mean_rayEnvelope_le (ordinateSetWeight_nonneg S)
        (ordinateSetWeight_le_one S) (σ := 2) (by norm_num) hsparse)
      (fun t _ => hlow t) hm
    rw [abs_deviationCoeff hm, mul_zero] at h
    have hpos : (0 : ℝ) < (m : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < m)) _
    have h0 : |lam m - ArithmeticFunction.vonMangoldt m| = 0 := by
      have := mul_nonneg (abs_nonneg (lam m - ArithmeticFunction.vonMangoldt m)) hpos.le
      nlinarith
    rw [abs_eq_zero, sub_eq_zero] at h0
    exact h0
  exact ⟨hcoeff, riemannHypothesis_iff_xi_zero_re_eq_half.mpr hRHxi⟩

end RHTower.AtomDomination
