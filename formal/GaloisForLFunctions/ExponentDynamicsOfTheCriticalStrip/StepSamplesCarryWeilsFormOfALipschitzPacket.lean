import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.WeilsFormIsContinuousInTheLogarithmicEnergy

/-!
# Step samples carry Weil's form of a Lipschitz packet

A window matrix is Weil's form on the step packets of the window `(R, R + J]`. This module
compares the form of a Lipschitz packet `F` inside the window with the form of its step sample
`g = Σ_j σ_j · flat_j`, the projection of `F` on the cells, `σ_j = ∫ F · flat_j`. The error
decays like `log R / R` in the block size `R`, with a constant polynomial in the ratio `Q` of the
window (`L` the Lipschitz constant and `M` the bound of `F`):

* `abs_stepSample_sub_le`: `|g − F| ≤ (L + M)/R` everywhere;
* `integral_stepSample_sub_sq`: `∫ (g − F)² = ∫ F² − Σ σ_j²`, so the sample does not gain mass;
* `packetLogEnergy_stepSample_sub_le`: the logarithmic energy of `g − F` is at most
  `8 (L + M)² (log Q + 1) log(1 + 4 (R + J) R²) / R²`;
* `abs_packetForm_stepSample_sub_le`, `abs_neutralForm_stepSample_sub_le`: Weil's form and its
  neutral part on the sample differ from those of `F` by at most `(L + M)² · sampleError Q R J`.

The energy estimate uses two moduli of `d = g − F`: it is small in the mean,
`‖d(· + t) − d‖² ≤ 4 (L + M)² (log Q + 1)/R²`, and it is Lipschitz in the mean at the scale of
the cells, `‖d(· + t) − d‖² ≲ (R + J) t`. The logarithm of the ratio of the two scales is the
price. The form is then transferred by the continuity of Weil's form in the logarithmic energy at
the weight `s = 1/R`; no hypothesis on the zeros enters.
-/

open Finset Filter Topology MeasureTheory
open scoped Real
open Zeta23
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth)
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. Integrals of bounded functions of bounded support -/

/-- A function bounded by `B` and supported in `[l, r]` has integral at most `B (r − l)` in
absolute value. -/
theorem abs_integral_le_of_support {ψ : ℝ → ℝ} {B l r : ℝ} (hlr : l ≤ r)
    (hb : ∀ u, |ψ u| ≤ B) (hs : ∀ u, ψ u ≠ 0 → l ≤ u ∧ u ≤ r) : |∫ u, ψ u| ≤ B * (r - l) := by
  have h0 : ∀ u, u ∉ Set.Icc l r → ψ u = 0 := fun u hu => by
    by_contra h
    exact hu (hs u h)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0, ← Real.norm_eq_abs]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc l r) (C := B)
    measure_Icc_lt_top (fun u _ => by rw [Real.norm_eq_abs]; exact hb u)
  rwa [Real.volume_real_Icc_of_le hlr] at h

/-- The first charge of a bounded function supported in `[l, r]`. -/
theorem abs_integral_mul_exp_neg_le {ψ : ℝ → ℝ} {b l r : ℝ} (hlr : l ≤ r)
    (hb : ∀ u, |ψ u| ≤ b) (hs : ∀ u, ψ u ≠ 0 → l ≤ u ∧ u ≤ r) :
    |∫ u, ψ u * Real.exp (-u / 2)| ≤ b * Real.exp (-l / 2) * (r - l) := by
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
  refine abs_integral_le_of_support hlr (fun u => ?_) fun u hu => hs u (left_ne_zero_of_mul hu)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases h0 : ψ u = 0
  · rw [h0, abs_zero, zero_mul]
    exact mul_nonneg hb0 (Real.exp_pos _).le
  · exact mul_le_mul (hb u) (Real.exp_le_exp.mpr (by linarith [(hs u h0).1])) (Real.exp_pos _).le
      hb0

/-- The second charge of a bounded function supported in `[l, r]`. -/
theorem abs_integral_mul_exp_le {ψ : ℝ → ℝ} {b l r : ℝ} (hlr : l ≤ r)
    (hb : ∀ u, |ψ u| ≤ b) (hs : ∀ u, ψ u ≠ 0 → l ≤ u ∧ u ≤ r) :
    |∫ u, ψ u * Real.exp (u / 2)| ≤ b * Real.exp (r / 2) * (r - l) := by
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0)
  refine abs_integral_le_of_support hlr (fun u => ?_) fun u hu => hs u (left_ne_zero_of_mul hu)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases h0 : ψ u = 0
  · rw [h0, abs_zero, zero_mul]
    exact mul_nonneg hb0 (Real.exp_pos _).le
  · exact mul_le_mul (hb u) (Real.exp_le_exp.mpr (by linarith [(hs u h0).2])) (Real.exp_pos _).le
      hb0

/-- The mass of a packet is its autocorrelation at zero. -/
theorem packetAutocorr_zero_eq (g : ℝ → ℝ) : packetAutocorr g 0 = ∫ u, g u ^ 2 := by
  unfold packetAutocorr
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show g u * g (u + 0) = g u ^ 2
  rw [add_zero, sq]

/-! ### 2. The logarithmic energy from two moduli -/

/-- **The logarithmic energy from two bounds on the modulus.** If `‖g(· + t) − g‖² ≤ β` and
`‖g(· + t) − g‖² ≤ β N t` for `0 ≤ t ≤ 1`, the density of the logarithmic energy is integrable
and `E(g) ≤ 2 β log(1 + N)`. -/
theorem packetLogEnergy_le_of_drop_le {g : ℝ → ℝ} (hgm : Measurable g) {β N : ℝ} (hN : 0 ≤ N)
    (hnn : ∀ t : ℝ, 0 ≤ 2 * (packetAutocorr g 0 - packetAutocorr g t))
    (h1 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 2 * (packetAutocorr g 0 - packetAutocorr g t) ≤ β)
    (h2 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      2 * (packetAutocorr g 0 - packetAutocorr g t) ≤ β * N * t) :
    IntervalIntegrable (fun t => 2 * (packetAutocorr g 0 - packetAutocorr g t) / t) volume 0 1 ∧
      packetLogEnergy g ≤ 2 * β * Real.log (1 + N) := by
  have hβ : 0 ≤ β := (hnn 0).trans (h1 0 le_rfl zero_le_one)
  have hpt : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      2 * (packetAutocorr g 0 - packetAutocorr g t) / t ≤ 2 * β * (N / (1 + N * t)) := by
    intro t ht0 ht1
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 2 * (packetAutocorr g 0 - packetAutocorr g t) := ⟨_, rfl⟩
    have hD1 : D ≤ β := by rw [hD]; exact h1 t ht0 ht1
    have hD2 : D ≤ β * N * t := by rw [hD]; exact h2 t ht0 ht1
    rw [← hD]
    have hNt : 0 ≤ N * t := mul_nonneg hN ht0
    have hpos : 0 < 1 + N * t := by linarith
    rcases eq_or_lt_of_le ht0 with h0 | ht
    · rw [← h0, div_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hβ) (div_nonneg hN hpos.le)
    · rw [div_le_iff₀ ht, show 2 * β * (N / (1 + N * t)) * t = 2 * β * N * t / (1 + N * t) by ring,
        le_div_iff₀ hpos]
      have h3 := mul_le_mul_of_nonneg_right hD1 hNt
      linarith
  have hint : IntervalIntegrable
      (fun t => 2 * (packetAutocorr g 0 - packetAutocorr g t) / t) volume 0 1 := by
    refine ((intervalIntegrable_div_one_add_mul hN).const_mul (2 * β)).mono_fun' ?_ ?_
    · exact (((measurable_const.sub (measurable_packetAutocorr_of_measurable hgm)).const_mul
        2).div measurable_id).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le zero_le_one] at ht
      show ‖2 * (packetAutocorr g 0 - packetAutocorr g t) / t‖ ≤ 2 * β * (N / (1 + N * t))
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnn t) ht.1.le)]
      exact hpt t ht.1.le ht.2
  refine ⟨hint, ?_⟩
  calc packetLogEnergy g ≤ ∫ t in (0:ℝ)..1, 2 * β * (N / (1 + N * t)) := by
        unfold packetLogEnergy
        exact intervalIntegral.integral_mono_on zero_le_one hint
          ((intervalIntegrable_div_one_add_mul hN).const_mul _) fun t ht => hpt t ht.1 ht.2
    _ = 2 * β * Real.log (1 + N) := by
        rw [intervalIntegral.integral_const_mul, integral_div_one_add_mul hN]

/-! ### 3. Three moduli -/

section Moduli

variable {g F : ℝ → ℝ} {B M L l r : ℝ}

/-- The modulus of a bounded packet: `‖g(· + t) − g‖² ≤ 4 B² (r − l + 1)` for `0 ≤ t ≤ 1`. -/
theorem bounded_drop_le (hgm : Measurable g) (hlr : l ≤ r) (hgb : ∀ u, |g u| ≤ B)
    (hgs : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * (packetAutocorr g 0 - packetAutocorr g t) ≤ 4 * B ^ 2 * (r - l + 1) := by
  rw [two_mul_packetAutocorr_drop hgm hgb hgs t]
  have hb : ∀ u, |(g (u + t) - g u) ^ 2| ≤ 4 * B ^ 2 := fun u => by
    have h : |g (u + t) - g u| ≤ 2 * B :=
      (abs_sub _ _).trans (by linarith [hgb (u + t), hgb u])
    rw [abs_pow]
    calc |g (u + t) - g u| ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 4 * B ^ 2 := by ring
  have hs : ∀ u, (g (u + t) - g u) ^ 2 ≠ 0 → l - 1 ≤ u ∧ u ≤ r := fun u hu => by
    by_cases h1 : g u = 0
    · have h2 : g (u + t) ≠ 0 := fun h2 => hu (by rw [h1, h2]; norm_num)
      obtain ⟨h3, h4⟩ := hgs _ h2
      constructor <;> linarith
    · obtain ⟨h3, h4⟩ := hgs _ h1
      constructor <;> linarith
  have h := (le_abs_self _).trans (abs_integral_le_of_support (by linarith) hb hs)
  have e : r - (l - 1) = r - l + 1 := by ring
  rwa [e] at h

/-- The modulus of a Lipschitz packet: `‖F(· + t) − F‖² ≤ L² (r − l + 1) t` for `0 ≤ t ≤ 1`. -/
theorem lipschitz_drop_le (hFm : Measurable F) (hlr : l ≤ r) (hFb : ∀ u, |F u| ≤ M)
    (hFL : ∀ u v, |F u - F v| ≤ L * |u - v|) (hFs : ∀ u, F u ≠ 0 → l ≤ u ∧ u ≤ r) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * (packetAutocorr F 0 - packetAutocorr F t) ≤ L ^ 2 * (r - l + 1) * t := by
  rw [two_mul_packetAutocorr_drop hFm hFb hFs t]
  have hb : ∀ u, |(F (u + t) - F u) ^ 2| ≤ L ^ 2 * t ^ 2 := fun u => by
    have h := hFL (u + t) u
    rw [add_sub_cancel_left, abs_of_nonneg ht0] at h
    rw [abs_pow, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hs : ∀ u, (F (u + t) - F u) ^ 2 ≠ 0 → l - 1 ≤ u ∧ u ≤ r := fun u hu => by
    by_cases h1 : F u = 0
    · have h2 : F (u + t) ≠ 0 := fun h2 => hu (by rw [h1, h2]; norm_num)
      obtain ⟨h3, h4⟩ := hFs _ h2
      constructor <;> linarith
    · obtain ⟨h3, h4⟩ := hFs _ h1
      constructor <;> linarith
  have h := (le_abs_self _).trans (abs_integral_le_of_support (by linarith) hb hs)
  have ht2 : t ^ 2 ≤ t := by nlinarith
  calc ∫ u, (F (u + t) - F u) ^ 2 ≤ L ^ 2 * t ^ 2 * (r - (l - 1)) := h
    _ = L ^ 2 * (r - l + 1) * t ^ 2 := by ring
    _ ≤ L ^ 2 * (r - l + 1) * t :=
        mul_le_mul_of_nonneg_left ht2 (mul_nonneg (sq_nonneg _) (by linarith))

/-- The modulus of a difference is at most twice the sum of the moduli. -/
theorem sub_drop_le (hgm : Measurable g) (hFm : Measurable F) (hgb : ∀ u, |g u| ≤ B)
    (hFb : ∀ u, |F u| ≤ M) (hgs : ∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r)
    (hFs : ∀ u, F u ≠ 0 → l ≤ u ∧ u ≤ r) (t : ℝ) :
    2 * (packetAutocorr (fun u => g u - F u) 0 - packetAutocorr (fun u => g u - F u) t) ≤
      2 * (2 * (packetAutocorr g 0 - packetAutocorr g t)) +
        2 * (2 * (packetAutocorr F 0 - packetAutocorr F t)) := by
  have hdm : Measurable fun u => g u - F u := hgm.sub hFm
  have hdb : ∀ u, |g u - F u| ≤ B + M := fun u =>
    (abs_sub _ _).trans (add_le_add (hgb u) (hFb u))
  have hds := support_sub hgs hFs
  have hi1 := integrable_packet_shift_sub_sq hgm hgb hgs t
  have hi2 := integrable_packet_shift_sub_sq hFm hFb hFs t
  have hi3 := integrable_packet_shift_sub_sq hdm hdb hds t
  have hmono : ∫ u, ((g (u + t) - F (u + t)) - (g u - F u)) ^ 2 ≤
      ∫ u, (2 * (g (u + t) - g u) ^ 2 + 2 * (F (u + t) - F u) ^ 2) :=
    integral_mono hi3 ((hi1.const_mul 2).add (hi2.const_mul 2)) fun u => by
      show ((g (u + t) - F (u + t)) - (g u - F u)) ^ 2 ≤
        2 * (g (u + t) - g u) ^ 2 + 2 * (F (u + t) - F u) ^ 2
      nlinarith [sq_nonneg ((g (u + t) - g u) + (F (u + t) - F u))]
  have hsplit : ∫ u, (2 * (g (u + t) - g u) ^ 2 + 2 * (F (u + t) - F u) ^ 2) =
      2 * (∫ u, (g (u + t) - g u) ^ 2) + 2 * ∫ u, (F (u + t) - F u) ^ 2 := by
    rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
      integral_const_mul]
  rw [two_mul_packetAutocorr_drop hdm hdb hds t, two_mul_packetAutocorr_drop hgm hgb hgs t,
    two_mul_packetAutocorr_drop hFm hFb hFs t]
  exact hmono.trans hsplit.le

/-- **The logarithmic energy of a Lipschitz packet** supported in `[l, r]` is at most
`2 L² (r − l + 1)`, and its density is integrable. -/
theorem packetLogEnergy_lipschitz_le (hFm : Measurable F) (hlr : l ≤ r) (hFb : ∀ u, |F u| ≤ M)
    (hFL : ∀ u v, |F u - F v| ≤ L * |u - v|) (hFs : ∀ u, F u ≠ 0 → l ≤ u ∧ u ≤ r) :
    IntervalIntegrable (fun t => 2 * (packetAutocorr F 0 - packetAutocorr F t) / t) volume 0 1 ∧
      packetLogEnergy F ≤ 2 * (L ^ 2 * (r - l + 1)) := by
  have hβ : 0 ≤ L ^ 2 * (r - l + 1) := mul_nonneg (sq_nonneg _) (by linarith)
  obtain ⟨hint, hE⟩ := packetLogEnergy_le_of_drop_le hFm (β := L ^ 2 * (r - l + 1)) (N := 1)
    zero_le_one (fun t => packetAutocorr_drop_nonneg hFm hFb hFs t)
    (fun t ht0 ht1 => (lipschitz_drop_le hFm hlr hFb hFL hFs ht0 ht1).trans
      (mul_le_of_le_one_right hβ ht1))
    (fun t ht0 ht1 => by
      rw [mul_one]
      exact lipschitz_drop_le hFm hlr hFb hFL hFs ht0 ht1)
  refine ⟨hint, hE.trans ?_⟩
  have hlog : Real.log (1 + 1) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 by norm_num)
    linarith
  have h := mul_le_mul_of_nonneg_left hlog (by linarith : (0 : ℝ) ≤ 2 * (L ^ 2 * (r - l + 1)))
  linarith

end Moduli

/-- The jump density of a Lipschitz packet of compact support is integrable. -/
theorem integrableOn_levyJump_of_lipschitz {F : ℝ → ℝ} (hFc : Continuous F)
    (hcs : HasCompactSupport F) {M L : ℝ} (hFb : ∀ u, |F u| ≤ M)
    (hFL : ∀ u v, |F u - F v| ≤ L * |u - v|) : IntegrableOn (levyJump F) (Set.Ioi 0) := by
  obtain ⟨R₀, hsupp⟩ := exists_natCast_le_abs_imp_eq_zero hcs
  have hsupp' : ∀ u : ℝ, ((R₀ + 1 : ℕ) : ℝ) ≤ |u| → F u = 0 := fun u hu =>
    hsupp u (le_trans (by push_cast; linarith) hu)
  have hX : (0 : ℝ) < 2 * ((R₀ + 1 : ℕ) : ℝ) := by positivity
  have hI1 := integrableOn_levyJump_Ioc hFc hsupp' hFb hFL (2 * ((R₀ + 1 : ℕ) : ℝ))
  have heq : Set.EqOn (levyJump F)
      (fun x => 2 * packetAutocorr F 0 * _root_.RHTower.archLevyDensity x)
      (Set.Ioi (2 * ((R₀ + 1 : ℕ) : ℝ))) := fun x hx => levyJump_of_le hsupp' (le_of_lt hx)
  have hI0 : IntegrableOn (fun x => 2 * packetAutocorr F 0 * _root_.RHTower.archLevyDensity x)
      (Set.Ioi (2 * ((R₀ + 1 : ℕ) : ℝ))) :=
    Integrable.const_mul
      (_root_.RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hX) _
  have hI2 : IntegrableOn (levyJump F) (Set.Ioi (2 * ((R₀ + 1 : ℕ) : ℝ))) :=
    hI0.congr_fun heq.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hX.le]
  exact hI1.union hI2

/-! ### 4. Cells and step samples -/

/-- The coefficient of a packet on the cell `(R + j, R + j + 1]`: its inner product with the
flat packet of the cell, which has unit mass. -/
def cellCoeff (F : ℝ → ℝ) (R j : ℕ) : ℝ :=
  ∫ u, flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * F u

/-- The step sample of a packet on the cells of `(R, R + J]`: its projection on the step
packets of the window. -/
def stepSample (F : ℝ → ℝ) (R J : ℕ) : ℝ → ℝ := stepPacket R J (cellCoeff F R)

/-- The coefficients are additive. -/
theorem cellCoeff_add {G H : ℝ → ℝ} (hG : Continuous G) (hH : Continuous H) (R j : ℕ) :
    cellCoeff (fun u => G u + H u) R j = cellCoeff G R j + cellCoeff H R j := by
  unfold cellCoeff
  rw [← integral_add (integrable_flatPacket_mul _ _ hG) (integrable_flatPacket_mul _ _ hH)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  exact mul_add _ _ _

/-- The length of a window of ratio at most `Q`. -/
theorem log_window_le {R J Q : ℕ} (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q) (hRJ : R + J ≤ Q * R) :
    Real.log ((R + J : ℕ) : ℝ) ≤ Real.log R + Real.log Q := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ₀
  have hmul : Real.log ((Q : ℝ) * R) = Real.log Q + Real.log R := Real.log_mul hQ'.ne' hR'.ne'
  have hle : Real.log ((R + J : ℕ) : ℝ) ≤ Real.log ((Q : ℝ) * R) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < R + J)) (by exact_mod_cast hRJ)
  linarith

/-- A point of `(log R, log(R + J)]` lies in one of the cells. -/
theorem exists_cell {R J : ℕ} (hR : 1 ≤ R) {u : ℝ} (h1 : Real.log R < u)
    (h2 : u ≤ Real.log ((R + J : ℕ) : ℝ)) :
    ∃ j, j < J ∧ u ∈ Set.Ioc (Real.log ((R + j : ℕ) : ℝ)) (Real.log ((R + (j + 1) : ℕ) : ℝ)) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have he1 : (R : ℝ) < Real.exp u := (Real.log_lt_iff_lt_exp hR').mp h1
  have hRJ : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have he2 : Real.exp u ≤ ((R + J : ℕ) : ℝ) := (Real.le_log_iff_exp_le hRJ).mp h2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈Real.exp u⌉₊ := ⟨_, rfl⟩
  have hn1 : R < n := by rw [hn]; exact Nat.lt_ceil.mpr he1
  have hn2 : n ≤ R + J := by rw [hn]; exact Nat.ceil_le.mpr he2
  have hn3 : Real.exp u ≤ n := by rw [hn]; exact Nat.le_ceil _
  have hn4 : (n : ℝ) < Real.exp u + 1 := by rw [hn]; exact Nat.ceil_lt_add_one (Real.exp_pos u).le
  have hn5 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  refine ⟨n - R - 1, by omega, ?_, ?_⟩
  · have hc : ((R + (n - R - 1) : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h : R + (n - R - 1) = n - 1 := by omega
      rw [h, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hc, Real.log_lt_iff_lt_exp (by linarith)]
    linarith
  · have hc : ((R + (n - R - 1 + 1) : ℕ) : ℝ) = (n : ℝ) := by
      have h : R + (n - R - 1 + 1) = n := by omega
      rw [h]
    rw [hc, Real.le_log_iff_exp_le (by linarith)]
    exact hn3

/-- On a cell a step packet is its coefficient times `e^{u/2}`. -/
theorem stepPacket_eq_of_mem_cell {R J : ℕ} (hR : 1 ≤ R) (σ : ℕ → ℝ) {j : ℕ} (hj : j < J) {u : ℝ}
    (hu : u ∈ Set.Ioc (Real.log ((R + j : ℕ) : ℝ)) (Real.log ((R + (j + 1) : ℕ) : ℝ))) :
    stepPacket R J σ u = σ j * Real.exp (u / 2) := by
  have hfj : flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u = Real.exp (u / 2) := by
    unfold flatPacket
    exact Set.indicator_of_mem hu _
  have hz : ∀ i ∈ range J, i ≠ j →
      σ i * flatPacket ((R + i : ℕ) : ℝ) ((R + (i + 1) : ℕ) : ℝ) u = 0 := fun i _ hij => by
    rcases flatPacket_cell_eq_zero_or hR hij u with h | h
    · rw [h, mul_zero]
    · exact absurd h (by rw [hfj]; exact (Real.exp_pos _).ne')
  unfold stepPacket
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj) hz, hfj]

/-- Off the cells a step packet vanishes. -/
theorem stepPacket_eq_zero_of_notMem {R J : ℕ} (σ : ℕ → ℝ) {u : ℝ}
    (hu : ∀ j, j < J →
      u ∉ Set.Ioc (Real.log ((R + j : ℕ) : ℝ)) (Real.log ((R + (j + 1) : ℕ) : ℝ))) :
    stepPacket R J σ u = 0 := by
  unfold stepPacket
  refine Finset.sum_eq_zero fun j hj => ?_
  have h : flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u = 0 := by
    unfold flatPacket
    exact Set.indicator_of_notMem (hu j (Finset.mem_range.mp hj)) _
  rw [h, mul_zero]

/-- **A Lipschitz packet is within `(L + M)/R` of its coefficient on a cell**:
`|F(u) − σ_j e^{u/2}| ≤ (L + M)/R` for `u` in the cell `(R + j, R + j + 1]`. The cell has length
at most `1/R`, the flat packet has unit charge against `e^{s/2}`, and
`F(u) e^{s/2} − F(s) e^{u/2} = e^{s/2} ((F(u) − F(s)) − F(s)(e^{(u−s)/2} − 1))`. -/
theorem abs_sub_cellCoeff_mul_exp_le {F : ℝ → ℝ} (hFc : Continuous F) {M L : ℝ}
    (hFb : ∀ u, |F u| ≤ M) (hFL : ∀ u v, |F u - F v| ≤ L * |u - v|) {R : ℕ} (hR : 1 ≤ R) (j : ℕ)
    {u : ℝ} (hu : u ∈ Set.Ioc (Real.log ((R + j : ℕ) : ℝ)) (Real.log ((R + (j + 1) : ℕ) : ℝ))) :
    |F u - cellCoeff F R j * Real.exp (u / 2)| ≤ (L + M) / R := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((R + j : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((R + (j + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  have hab1 : b = a + 1 := by rw [ha, hb]; push_cast; ring
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hRa : (R : ℝ) ≤ a := by rw [ha]; exact_mod_cast (by omega : R ≤ R + j)
  have ha0 : 0 < a := hR'.trans_le hRa
  have ha1 : 1 ≤ a := le_trans (by exact_mod_cast hR) hRa
  have hab : a ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hFb 0)
  have hL0 : 0 ≤ L := by
    have h := (abs_nonneg _).trans (hFL 1 0)
    rwa [sub_zero, abs_one, mul_one] at h
  have hcoef : cellCoeff F R j = ∫ s, flatPacket a b s * F s := by rw [ha, hb]; rfl
  rw [← ha, ← hb] at hu
  rw [hcoef]
  -- the length of the cell
  have hlen : Real.log b - Real.log a ≤ 1 / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have e : b / a - 1 = 1 / a := by
      rw [hab1]
      field_simp
      ring
    linarith
  have h1a : 1 / a ≤ 1 := by rw [div_le_one ha0]; exact ha1
  -- the representation
  have hone : ∫ s, flatPacket a b s * Real.exp (s / 2) = 1 := by
    rw [integral_flatPacket_mul_exp ha0 hab, hab1]
    ring
  have hi1 : Integrable fun s => flatPacket a b s * Real.exp (s / 2) :=
    integrable_flatPacket_mul a b (by fun_prop)
  have hi2 : Integrable fun s => flatPacket a b s * F s := integrable_flatPacket_mul a b hFc
  have hrep : F u - (∫ s, flatPacket a b s * F s) * Real.exp (u / 2) =
      ∫ s, flatPacket a b s * (F u * Real.exp (s / 2) - F s * Real.exp (u / 2)) := by
    have e : (fun s => flatPacket a b s * (F u * Real.exp (s / 2) - F s * Real.exp (u / 2))) =
        fun s => F u * (flatPacket a b s * Real.exp (s / 2)) -
          Real.exp (u / 2) * (flatPacket a b s * F s) := by
      funext s
      ring
    rw [e, integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
      integral_const_mul, hone]
    ring
  have hbound : ∀ s, ‖flatPacket a b s * (F u * Real.exp (s / 2) - F s * Real.exp (u / 2))‖ ≤
      (L + M) / R * (flatPacket a b s * Real.exp (s / 2)) := by
    intro s
    by_cases hs : s ∈ Set.Ioc (Real.log a) (Real.log b)
    · have hf : flatPacket a b s = Real.exp (s / 2) := by
        unfold flatPacket
        exact Set.indicator_of_mem hs _
      have hus : |u - s| ≤ 1 / a := by
        rw [abs_le]
        constructor <;> linarith [hu.1, hu.2, hs.1, hs.2]
      have hx : |(u - s) / 2| ≤ 1 := by
        rw [abs_div, abs_two]
        linarith
      have hexp := Real.abs_exp_sub_one_le hx
      have hsplit : F u * Real.exp (s / 2) - F s * Real.exp (u / 2) =
          Real.exp (s / 2) * ((F u - F s) - F s * (Real.exp ((u - s) / 2) - 1)) := by
        have he : Real.exp (u / 2) = Real.exp (s / 2) * Real.exp ((u - s) / 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he]
        ring
      have hin : |(F u - F s) - F s * (Real.exp ((u - s) / 2) - 1)| ≤ (L + M) / R := by
        have h1 := hFL u s
        have h2 : |F s * (Real.exp ((u - s) / 2) - 1)| ≤ M * (2 * |(u - s) / 2|) := by
          rw [abs_mul]
          exact mul_le_mul (hFb s) hexp (abs_nonneg _) hM0
        have h3 : |(u - s) / 2| = |u - s| / 2 := by rw [abs_div, abs_two]
        have h4 : (L + M) * |u - s| ≤ (L + M) * (1 / a) :=
          mul_le_mul_of_nonneg_left hus (by linarith)
        have h5 : (L + M) * (1 / a) ≤ (L + M) / R := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left (by linarith) hR' hRa
        calc |(F u - F s) - F s * (Real.exp ((u - s) / 2) - 1)|
            ≤ |F u - F s| + |F s * (Real.exp ((u - s) / 2) - 1)| := abs_sub _ _
          _ ≤ L * |u - s| + M * (2 * |(u - s) / 2|) := add_le_add h1 h2
          _ = (L + M) * |u - s| := by rw [h3]; ring
          _ ≤ (L + M) / R := h4.trans h5
      have hee : 0 ≤ Real.exp (s / 2) * Real.exp (s / 2) :=
        mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
      have hmul := mul_le_mul_of_nonneg_left hin hee
      rw [hf, hsplit, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      linarith
    · have hf : flatPacket a b s = 0 := by
        unfold flatPacket
        exact Set.indicator_of_notMem hs _
      rw [hf, zero_mul, zero_mul, mul_zero, norm_zero]
  rw [hrep, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hi1.const_mul _) (Eventually.of_forall hbound)).trans
    (le_of_eq ?_)
  rw [integral_const_mul, hone, mul_one]

/-- A Lipschitz packet inside the window `(R, R + J]`: continuous, bounded by `M`, Lipschitz
with constant `L`, supported in `(log R, log(R + J)]`. -/
structure WindowPacket (R J : ℕ) (M L : ℝ) (F : ℝ → ℝ) : Prop where
  continuous : Continuous F
  bound : ∀ u, |F u| ≤ M
  lipschitz : ∀ u v, |F u - F v| ≤ L * |u - v|
  support : ∀ u, F u ≠ 0 → Real.log R < u ∧ u ≤ Real.log ((R + J : ℕ) : ℝ)

section Sample

variable {R J Q : ℕ} {M L : ℝ} {F : ℝ → ℝ}

theorem WindowPacket.bound_nonneg (hF : WindowPacket R J M L F) : 0 ≤ M :=
  (abs_nonneg _).trans (hF.bound 0)

theorem WindowPacket.lipschitz_nonneg (hF : WindowPacket R J M L F) : 0 ≤ L := by
  have h := (abs_nonneg _).trans (hF.lipschitz 1 0)
  rwa [sub_zero, abs_one, mul_one] at h

theorem WindowPacket.measurable (hF : WindowPacket R J M L F) : Measurable F :=
  hF.continuous.measurable

/-- The support of a packet inside a window of ratio at most `Q`. -/
theorem WindowPacket.support_window (hF : WindowPacket R J M L F) (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q)
    (hRJ : R + J ≤ Q * R) : ∀ u, F u ≠ 0 → Real.log R ≤ u ∧ u ≤ Real.log R + Real.log Q :=
  fun u hu => ⟨(hF.support u hu).1.le, (hF.support u hu).2.trans (log_window_le hR hQ₀ hRJ)⟩

/-- The support of a step sample in a window of ratio at most `Q`. -/
theorem stepSample_support (F : ℝ → ℝ) (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q) (hRJ : R + J ≤ Q * R) :
    ∀ u, stepSample F R J u ≠ 0 → Real.log R ≤ u ∧ u ≤ Real.log R + Real.log Q := fun u hu =>
  ⟨(stepPacket_ne_zero hR J _ hu).1,
    (stepPacket_ne_zero hR J _ hu).2.trans (log_window_le hR hQ₀ hRJ)⟩

/-- **A Lipschitz packet inside the window is uniformly close to its step sample**:
`|g − F| ≤ (L + M)/R`. -/
theorem abs_stepSample_sub_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R) (u : ℝ) :
    |stepSample F R J u - F u| ≤ (L + M) / R := by
  by_cases hcell : ∃ j, j < J ∧
      u ∈ Set.Ioc (Real.log ((R + j : ℕ) : ℝ)) (Real.log ((R + (j + 1) : ℕ) : ℝ))
  · obtain ⟨j, hj, hu⟩ := hcell
    have hg : stepSample F R J u = cellCoeff F R j * Real.exp (u / 2) :=
      stepPacket_eq_of_mem_cell hR _ hj hu
    rw [hg, abs_sub_comm]
    exact abs_sub_cellCoeff_mul_exp_le hF.continuous hF.bound hF.lipschitz hR j hu
  · have hF0 : F u = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := hF.support u hne
      exact hcell (exists_cell hR h1 h2)
    have hg0 : stepSample F R J u = 0 :=
      stepPacket_eq_zero_of_notMem _ fun j hj hu => hcell ⟨j, hj, hu⟩
    rw [hF0, hg0, sub_zero, abs_zero]
    exact div_nonneg (add_nonneg hF.lipschitz_nonneg hF.bound_nonneg) (Nat.cast_nonneg R)

/-! ### 5. The mass of the sample -/

/-- **The step sample is the projection on the cells**: `∫ (g − F)² = ∫ F² − Σ σ_j²`. -/
theorem integral_stepSample_sub_sq (hF : WindowPacket R J M L F) (hR : 1 ≤ R) :
    ∫ u, (stepSample F R J u - F u) ^ 2 =
      (∫ u, F u ^ 2) - ∑ j ∈ range J, cellCoeff F R j ^ 2 := by
  have hsF : ∀ u, F u ≠ 0 → Real.log R ≤ u ∧ u ≤ Real.log ((R + J : ℕ) : ℝ) := fun u hu =>
    ⟨(hF.support u hu).1.le, (hF.support u hu).2⟩
  have hiF2 : Integrable fun u => F u ^ 2 := integrable_packet_sq hF.measurable hF.bound hsF
  have hig2 : Integrable fun u => stepSample F R J u ^ 2 :=
    integrable_packet_sq (measurable_stepPacket R J _) (abs_stepPacket_le R J _)
      (fun u hu => stepPacket_ne_zero hR J _ hu)
  have hint : ∀ j ∈ range J, Integrable fun u =>
      cellCoeff F R j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * F u) :=
    fun j _ => (integrable_flatPacket_mul _ _ hF.continuous).const_mul _
  have e : (fun u => F u * stepSample F R J u) = fun u => ∑ j ∈ range J,
      cellCoeff F R j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * F u) := by
    funext u
    unfold stepSample stepPacket
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hiFg : Integrable fun u => F u * stepSample F R J u := by
    rw [e]
    exact integrable_finsetSum _ hint
  have hFg : ∫ u, F u * stepSample F R J u = ∑ j ∈ range J, cellCoeff F R j ^ 2 := by
    rw [e, integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, sq]
    rfl
  have hg2 : ∫ u, stepSample F R J u ^ 2 = ∑ j ∈ range J, cellCoeff F R j ^ 2 := by
    rw [← packetAutocorr_stepPacket_zero hR J (cellCoeff F R)]
    exact (packetAutocorr_zero_eq _).symm
  have e2 : (fun u => (stepSample F R J u - F u) ^ 2) = fun u =>
      stepSample F R J u ^ 2 - 2 * (F u * stepSample F R J u) + F u ^ 2 := by
    funext u
    ring
  rw [e2, integral_add (hig2.sub (hiFg.const_mul 2)) hiF2, integral_sub hig2 (hiFg.const_mul 2),
    integral_const_mul, hg2, hFg]
  ring

/-- The sample does not gain mass: `Σ σ_j² ≤ ∫ F²`. -/
theorem sum_cellCoeff_sq_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R) :
    ∑ j ∈ range J, cellCoeff F R j ^ 2 ≤ ∫ u, F u ^ 2 := by
  have h := integral_stepSample_sub_sq hF hR
  have h0 : 0 ≤ ∫ u, (stepSample F R J u - F u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  linarith

/-- The mass of a packet inside a window of ratio at most `Q`. -/
theorem integral_sq_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q)
    (hRJ : R + J ≤ Q * R) : ∫ u, F u ^ 2 ≤ M ^ 2 * Real.log Q := by
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ₀)
  have hb : ∀ u, |F u ^ 2| ≤ M ^ 2 := fun u => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF.bound u) 2
  have hs : ∀ u, F u ^ 2 ≠ 0 → Real.log R ≤ u ∧ u ≤ Real.log R + Real.log Q := fun u hu =>
    hF.support_window hR hQ₀ hRJ u fun h => hu (by rw [h]; norm_num)
  have h := (le_abs_self _).trans (abs_integral_le_of_support (by linarith) hb hs)
  rwa [add_sub_cancel_left] at h

/-- The mass of the difference: `∫ (g − F)² ≤ ((L + M)/R)² log Q`. -/
theorem integral_stepSample_sub_sq_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q)
    (hRJ : R + J ≤ Q * R) :
    ∫ u, (stepSample F R J u - F u) ^ 2 ≤ ((L + M) / R) ^ 2 * Real.log Q := by
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ₀)
  have hb : ∀ u, |(stepSample F R J u - F u) ^ 2| ≤ ((L + M) / R) ^ 2 := fun u => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_stepSample_sub_le hF hR u) 2
  have hs : ∀ u, (stepSample F R J u - F u) ^ 2 ≠ 0 →
      Real.log R ≤ u ∧ u ≤ Real.log R + Real.log Q := fun u hu =>
    support_sub (stepSample_support F hR hQ₀ hRJ) (hF.support_window hR hQ₀ hRJ) u
      fun h => hu (by rw [h]; norm_num)
  have h := (le_abs_self _).trans (abs_integral_le_of_support (by linarith) hb hs)
  rwa [add_sub_cancel_left] at h

/-- The masses of a packet and of its sample differ by at most `((L + M)/R)² log Q`. -/
theorem abs_sum_cellCoeff_sq_sub_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R) (hQ₀ : 1 ≤ Q)
    (hRJ : R + J ≤ Q * R) :
    |∑ j ∈ range J, cellCoeff F R j ^ 2 - ∫ u, F u ^ 2| ≤ ((L + M) / R) ^ 2 * Real.log Q := by
  have h1 := integral_stepSample_sub_sq hF hR
  have h2 := integral_stepSample_sub_sq_le hF hR hQ₀ hRJ
  have h3 := sum_cellCoeff_sq_le hF hR
  rw [abs_le]
  constructor <;> linarith

/-! ### 6. The logarithmic energy of the difference -/

/-- **The logarithmic energy of `g − F`** is at most
`8 (L + M)² (log Q + 1) log(1 + 4 (R + J) R²) / R²`, and its density is integrable. -/
theorem packetLogEnergy_stepSample_sub_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R)
    (hQ₀ : 1 ≤ Q) (hRJ : R + J ≤ Q * R) :
    IntervalIntegrable (fun t => 2 * (packetAutocorr (fun u => stepSample F R J u - F u) 0 -
        packetAutocorr (fun u => stepSample F R J u - F u) t) / t) volume 0 1 ∧
      packetLogEnergy (fun u => stepSample F R J u - F u) ≤
        8 * ((L + M) ^ 2 * (Real.log Q + 1)) / (R : ℝ) ^ 2 *
          Real.log (1 + 4 * ((R + J : ℕ) : ℝ) * (R : ℝ) ^ 2) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hRne : (R : ℝ) ≠ 0 := hR'.ne'
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ₀)
  have hM0 := hF.bound_nonneg
  have hL0 := hF.lipschitz_nonneg
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((R + J : ℕ) : ℝ) := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast (by omega : 1 ≤ R + J)
  have hn0 : 0 ≤ n := by linarith
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (L + M) ^ 2 * (Real.log Q + 1) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg (sq_nonneg _) (by linarith)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j ∈ range J, cellCoeff F R j ^ 2 := ⟨_, rfl⟩
  have hgm : Measurable (stepSample F R J) := measurable_stepPacket R J (cellCoeff F R)
  have hgb : ∀ u, |stepSample F R J u| ≤
      ∑ j ∈ range J, |cellCoeff F R j| * Real.exp (Real.log ((R + (j + 1) : ℕ) : ℝ) / 2) :=
    abs_stepPacket_le R J (cellCoeff F R)
  have hgs := stepSample_support F hR hQ₀ hRJ
  have hFs := hF.support_window hR hQ₀ hRJ
  have hdm : Measurable fun u => stepSample F R J u - F u := hgm.sub hF.measurable
  have hdb : ∀ u, |stepSample F R J u - F u| ≤ (L + M) / R := abs_stepSample_sub_le hF hR
  have hds := support_sub hgs hFs
  have hlr : Real.log R ≤ Real.log R + Real.log Q := by linarith
  have hSP : S ≤ P := by
    have h1 : S ≤ ∫ u, F u ^ 2 := by rw [hS]; exact sum_cellCoeff_sq_le hF hR
    have h2 := integral_sq_le hF hR hQ₀ hRJ
    have h3 : M ^ 2 * Real.log Q ≤ (L + M) ^ 2 * (Real.log Q + 1) :=
      mul_le_mul (pow_le_pow_left₀ hM0 (by linarith) 2) (by linarith) hlogQ (sq_nonneg _)
    rw [hP]
    linarith
  have hLP : L ^ 2 * (Real.log Q + 1) ≤ P := by
    rw [hP]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL0 (by linarith) 2) (by linarith)
  have hβN : 4 * P / (R : ℝ) ^ 2 * (4 * n * (R : ℝ) ^ 2) = 16 * n * P := by
    field_simp
    ring
  have key := packetLogEnergy_le_of_drop_le hdm (β := 4 * P / (R : ℝ) ^ 2)
    (N := 4 * n * (R : ℝ) ^ 2) (mul_nonneg (mul_nonneg (by norm_num) hn0) (sq_nonneg _))
    (fun t => packetAutocorr_drop_nonneg hdm hdb hds t)
    (fun t ht0 ht1 => by
      have h := bounded_drop_le hdm hlr hdb hds ht0 ht1
      rw [add_sub_cancel_left] at h
      have e : 4 * ((L + M) / (R : ℝ)) ^ 2 * (Real.log Q + 1) = 4 * P / (R : ℝ) ^ 2 := by
        rw [hP]
        ring
      rw [← e]
      exact h)
    (fun t ht0 ht1 => by
      rw [hβN]
      have h1 := sub_drop_le hgm hF.measurable hgb hF.bound hgs hFs t
      have h2 : 2 * (packetAutocorr (stepSample F R J) 0 - packetAutocorr (stepSample F R J) t) ≤
          6 * n * t * S := by
        rw [hn, hS]
        exact (stepPacket_drop_le hR J (cellCoeff F R) ht0 ht1).2
      have h3 := lipschitz_drop_le hF.measurable hlr hF.bound hF.lipschitz hFs ht0 ht1
      rw [add_sub_cancel_left] at h3
      have h4 : 6 * n * t * S ≤ 6 * n * t * P :=
        mul_le_mul_of_nonneg_left hSP (mul_nonneg (mul_nonneg (by norm_num) hn0) ht0)
      have h5 : L ^ 2 * (Real.log Q + 1) * t ≤ P * t := mul_le_mul_of_nonneg_right hLP ht0
      have h6 : 1 * (P * t) ≤ n * (P * t) :=
        mul_le_mul_of_nonneg_right hn1 (mul_nonneg hP0 ht0)
      have h7 : 0 ≤ n * (P * t) := mul_nonneg hn0 (mul_nonneg hP0 ht0)
      linarith)
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  rw [hP, hn]
  ring

/-! ### 7. Weil's form of the sample -/

/-- **Weil's form of the step sample of a Lipschitz packet** inside a window of ratio at most
`Q` differs from the form of the packet by at most
`(L + M)² (log Q + 1)/R · 160 · L(A, w) (16 log(1 + 4 (R + J) R²) + 5)`, `A = (log Q + 1)/2`. -/
theorem abs_packetForm_stepSample_sub_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R)
    (hQ₀ : 1 ≤ Q) (hRJ : R + J ≤ Q * R) :
    |packetForm Q (stepSample F R J) - packetForm Q F| ≤
      (L + M) ^ 2 * ((Real.log Q + 1) / R *
        (160 * (logSamplingConst ((Real.log Q + 1) / 2) zetaZeroWidth *
          (16 * Real.log (1 + 4 * ((R + J : ℕ) : ℝ) * (R : ℝ) ^ 2) + 5)))) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRne : (R : ℝ) ≠ 0 := hR'.ne'
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ₀
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ₀)
  have hM0 := hF.bound_nonneg
  have hL0 := hF.lipschitz_nonneg
  obtain ⟨A, hA⟩ : ∃ A : _root_.RHTower.SuzukiPositiveAperture, A.1 = (Real.log Q + 1) / 2 :=
    ⟨⟨(Real.log Q + 1) / 2, by positivity⟩, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (L + M) ^ 2 * (Real.log Q + 1) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg (sq_nonneg _) (by linarith)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log (1 + 4 * ((R + J : ℕ) : ℝ) * (R : ℝ) ^ 2) :=
    ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by
    rw [hT]
    have h : (0 : ℝ) ≤ 4 * ((R + J : ℕ) : ℝ) * (R : ℝ) ^ 2 := by positivity
    exact Real.log_nonneg (by linarith)
  have hgs := stepSample_support F hR hQ₀ hRJ
  have hFs := hF.support_window hR hQ₀ hRJ
  have hlr : Real.log R ≤ Real.log R + Real.log Q := by linarith
  obtain ⟨hEd, hEdle⟩ := packetLogEnergy_stepSample_sub_le hF hR hQ₀ hRJ
  obtain ⟨hE₂, hE₂le⟩ := packetLogEnergy_lipschitz_le hF.measurable hlr hF.bound hF.lipschitz hFs
  rw [add_sub_cancel_left] at hE₂le
  rw [← hT, ← hP] at hEdle
  have h := abs_packetForm_sub_le (g₁ := stepSample F R J) (g₂ := F)
    (measurable_stepPacket R J _) hF.measurable (abs_stepPacket_le R J _) hF.bound hgs hFs
    (A := A) (by rw [hA, add_sub_cancel_left]; linarith) (Q := Q)
    (by rw [add_sub_cancel_left]; exact Real.log_lt_log hQ' (by linarith))
    (integrableOn_levyJump_stepPacket hR J _)
    (integrableOn_levyJump_of_lipschitz hF.continuous (hasCompactSupport_of_support_le hFs)
      hF.bound hF.lipschitz)
    hEd hE₂ (s := 1 / (R : ℝ)) (by positivity)
  rw [hA, one_div_one_div] at h
  refine h.trans ?_
  -- the masses and the energy of the packet
  have hmd : packetAutocorr (fun u => stepSample F R J u - F u) 0 ≤ P / (R : ℝ) ^ 2 := by
    have h1 : packetAutocorr (fun u => stepSample F R J u - F u) 0 =
        ∫ u, (stepSample F R J u - F u) ^ 2 := packetAutocorr_zero_eq _
    have h2 := integral_stepSample_sub_sq_le hF hR hQ₀ hRJ
    have h3 : ((L + M) / (R : ℝ)) ^ 2 * Real.log Q ≤ P / (R : ℝ) ^ 2 := by
      rw [hP, div_pow, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)) (sq_nonneg _)
    linarith
  have hmF : packetAutocorr F 0 ≤ P := by
    have h1 : packetAutocorr F 0 = ∫ u, F u ^ 2 := packetAutocorr_zero_eq _
    have h2 := integral_sq_le hF hR hQ₀ hRJ
    have h3 : M ^ 2 * Real.log Q ≤ (L + M) ^ 2 * (Real.log Q + 1) :=
      mul_le_mul (pow_le_pow_left₀ hM0 (by linarith) 2) (by linarith) hlogQ (sq_nonneg _)
    rw [hP]
    linarith
  have hEF : packetLogEnergy F ≤ 2 * P := by
    have h1 : L ^ 2 * (Real.log Q + 1) ≤ P := by
      rw [hP]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL0 (by linarith) 2) (by linarith)
    linarith
  have hLc := logSamplingConst_nonneg (σ := zetaZeroWidth) (a := (Real.log Q + 1) / 2)
    (by positivity)
  have hX : (1 + (R : ℝ)) * (packetLogEnergy (fun u => stepSample F R J u - F u) +
        packetAutocorr (fun u => stepSample F R J u - F u) 0) +
      1 / (R : ℝ) * (packetLogEnergy F + packetAutocorr F 0) ≤ P * (16 * T + 5) / R := by
    have h1 : packetLogEnergy (fun u => stepSample F R J u - F u) +
        packetAutocorr (fun u => stepSample F R J u - F u) 0 ≤ P * (8 * T + 1) / (R : ℝ) ^ 2 := by
      have e : 8 * P / (R : ℝ) ^ 2 * T + P / (R : ℝ) ^ 2 = P * (8 * T + 1) / (R : ℝ) ^ 2 := by
        ring
      linarith
    have hY0 : 0 ≤ P * (8 * T + 1) / (R : ℝ) ^ 2 :=
      div_nonneg (mul_nonneg hP0 (by linarith)) (sq_nonneg _)
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + R)
    have h4 := mul_le_mul_of_nonneg_right (by linarith : 1 + (R : ℝ) ≤ 2 * R) hY0
    have h5 : 2 * (R : ℝ) * (P * (8 * T + 1) / (R : ℝ) ^ 2) = 2 * P * (8 * T + 1) / R := by
      field_simp
    have h6 := mul_le_mul_of_nonneg_left (by linarith : packetLogEnergy F + packetAutocorr F 0 ≤
      3 * P) (by positivity : (0 : ℝ) ≤ 1 / (R : ℝ))
    have h7 : 2 * P * (8 * T + 1) / R + 1 / (R : ℝ) * (3 * P) = P * (16 * T + 5) / R := by
      ring
    linarith
  have hfin := mul_le_mul_of_nonneg_left hX hLc
  have e : (L + M) ^ 2 * ((Real.log Q + 1) / R *
      (160 * (logSamplingConst ((Real.log Q + 1) / 2) zetaZeroWidth * (16 * T + 5)))) =
      160 * (logSamplingConst ((Real.log Q + 1) / 2) zetaZeroWidth *
        (P * (16 * T + 5) / R)) := by
    rw [hP]
    ring
  rw [← hT, e]
  linarith

/-! ### 8. The neutral part of the sample -/

/-- Step packets against continuous weights are integrable. -/
theorem integrable_stepPacket_mul (R J : ℕ) (σ : ℕ → ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Integrable fun u => stepPacket R J σ u * w u := by
  have h : (fun u => stepPacket R J σ u * w u) = fun u => ∑ j ∈ range J,
      σ j * (flatPacket ((R + j : ℕ) : ℝ) ((R + (j + 1) : ℕ) : ℝ) u * w u) := by
    funext u
    rw [stepPacket, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h]
  exact integrable_finsetSum _ fun j _ => (integrable_flatPacket_mul _ _ hw).const_mul (σ j)

/-- The error of the step sample of a window of ratio `Q` at block size `R`, for a packet with
`L + M = 1`: the error of Weil's form and the error of the product of the two charges. -/
def sampleError (Q R J : ℕ) : ℝ :=
  (Real.log Q + 1) / R *
    (160 * (logSamplingConst ((Real.log Q + 1) / 2) zetaZeroWidth *
        (16 * Real.log (1 + 4 * ((R + J : ℕ) : ℝ) * (R : ℝ) ^ 2) + 5)) +
      6 * (Real.log Q * Q))

/-- **The neutral part of Weil's form on the step sample of a Lipschitz packet** differs from
the neutral part on the packet by at most `(L + M)² · sampleError Q R J`. The charges of
`g − F` are at most `(L + M)/R` times those of the window. -/
theorem abs_neutralForm_stepSample_sub_le (hF : WindowPacket R J M L F) (hR : 1 ≤ R)
    (hQ₀ : 1 ≤ Q) (hRJ : R + J ≤ Q * R) :
    |neutralForm Q (stepSample F R J) - neutralForm Q F| ≤ (L + M) ^ 2 * sampleError Q R J := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ₀
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ₀)
  have hM0 := hF.bound_nonneg
  have hL0 := hF.lipschitz_nonneg
  have hc0 : 0 ≤ L + M := by linarith
  have hgs := stepSample_support F hR hQ₀ hRJ
  have hFs := hF.support_window hR hQ₀ hRJ
  have hds := support_sub hgs hFs
  have hdb : ∀ u, |stepSample F R J u - F u| ≤ (L + M) / R := abs_stepSample_sub_le hF hR
  have hlr : Real.log R ≤ Real.log R + Real.log Q := by linarith
  have hpf := abs_packetForm_stepSample_sub_le hF hR hQ₀ hRJ
  have hw1 : Continuous fun u : ℝ => Real.exp (-u / 2) := by fun_prop
  have hw2 : Continuous fun u : ℝ => Real.exp (u / 2) := by fun_prop
  have hiF : ∀ {w : ℝ → ℝ}, Continuous w → Integrable fun u => F u * w u := fun hw =>
    (hF.continuous.mul hw).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_le hFs).mul_right
  -- the four charges
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∫ u, stepSample F R J u * Real.exp (-u / 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ∫ u, stepSample F R J u * Real.exp (u / 2) := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = ∫ u, F u * Real.exp (-u / 2) := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b' = ∫ u, F u * Real.exp (u / 2) := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Real.exp (-Real.log R / 2) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = Real.exp ((Real.log R + Real.log Q) / 2) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; exact (Real.exp_pos _).le
  have hβ0 : 0 ≤ β := by rw [hβ]; exact (Real.exp_pos _).le
  have hαβ : α * β ≤ Q := by
    rw [hα, hβ, ← Real.exp_add,
      show -Real.log R / 2 + (Real.log R + Real.log Q) / 2 = Real.log Q / 2 by ring]
    calc Real.exp (Real.log Q / 2) ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr (by linarith)
      _ = Q := Real.exp_log hQ'
  have hda : |a - a'| ≤ (L + M) / R * α * Real.log Q := by
    have e : a - a' = ∫ u, (stepSample F R J u - F u) * Real.exp (-u / 2) := by
      rw [ha, ha', ← integral_sub (integrable_stepPacket_mul R J _ hw1) (hiF hw1)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      exact (sub_mul _ _ _).symm
    have h := abs_integral_mul_exp_neg_le hlr hdb hds
    rw [add_sub_cancel_left, ← hα] at h
    rw [e]
    exact h
  have hdb' : |b - b'| ≤ (L + M) / R * β * Real.log Q := by
    have e : b - b' = ∫ u, (stepSample F R J u - F u) * Real.exp (u / 2) := by
      rw [hb, hb', ← integral_sub (integrable_stepPacket_mul R J _ hw2) (hiF hw2)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      exact (sub_mul _ _ _).symm
    have h := abs_integral_mul_exp_le hlr hdb hds
    rw [add_sub_cancel_left, ← hβ] at h
    rw [e]
    exact h
  have hba' : |a'| ≤ M * α * Real.log Q := by
    have h := abs_integral_mul_exp_neg_le hlr hF.bound hFs
    rw [add_sub_cancel_left, ← hα] at h
    rw [ha']
    exact h
  have hbb' : |b'| ≤ M * β * Real.log Q := by
    have h := abs_integral_mul_exp_le hlr hF.bound hFs
    rw [add_sub_cancel_left, ← hβ] at h
    rw [hb']
    exact h
  -- the product of the charges
  have hprod : |a * b - a' * b'| ≤ 3 * (L + M) ^ 2 * Real.log Q ^ 2 * Q / R := by
    have e : a * b - a' * b' = (a - a') * b' + a' * (b - b') + (a - a') * (b - b') := by ring
    have h1 : |(a - a') * b'| ≤ ((L + M) / R * α * Real.log Q) * (M * β * Real.log Q) := by
      rw [abs_mul]
      exact mul_le_mul hda hbb' (abs_nonneg _) ((abs_nonneg _).trans hda)
    have h2 : |a' * (b - b')| ≤ (M * α * Real.log Q) * ((L + M) / R * β * Real.log Q) := by
      rw [abs_mul]
      exact mul_le_mul hba' hdb' (abs_nonneg _) ((abs_nonneg _).trans hba')
    have h3 : |(a - a') * (b - b')| ≤
        ((L + M) / R * α * Real.log Q) * ((L + M) / R * β * Real.log Q) := by
      rw [abs_mul]
      exact mul_le_mul hda hdb' (abs_nonneg _) ((abs_nonneg _).trans hda)
    have h4 : |a * b - a' * b'| ≤ (α * β) * (Real.log Q ^ 2 *
        (2 * ((L + M) / R * M) + ((L + M) / R) ^ 2)) := by
      rw [e]
      refine (abs_add_three _ _ _).trans (le_of_le_of_eq (add_le_add (add_le_add h1 h2) h3) ?_)
      ring
    have hcR : 0 ≤ (L + M) / R := div_nonneg hc0 hR'.le
    have h5 : (L + M) / R * M ≤ (L + M) ^ 2 / R := by
      have h := mul_le_mul_of_nonneg_left (by linarith : M ≤ L + M) hcR
      have e1 : (L + M) / R * (L + M) = (L + M) ^ 2 / R := by ring
      linarith
    have h6 : ((L + M) / R) ^ 2 ≤ (L + M) ^ 2 / R := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hR' (by nlinarith)
    have h7 : 2 * ((L + M) / R * M) + ((L + M) / R) ^ 2 ≤ 3 * ((L + M) ^ 2 / R) := by linarith
    have h8 : 0 ≤ Real.log Q ^ 2 * (2 * ((L + M) / R * M) + ((L + M) / R) ^ 2) :=
      mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcR hM0))
        (sq_nonneg _))
    calc |a * b - a' * b'| ≤ (α * β) * (Real.log Q ^ 2 *
          (2 * ((L + M) / R * M) + ((L + M) / R) ^ 2)) := h4
      _ ≤ Q * (Real.log Q ^ 2 * (3 * ((L + M) ^ 2 / R))) :=
          mul_le_mul hαβ (mul_le_mul_of_nonneg_left h7 (sq_nonneg _)) h8 (Nat.cast_nonneg Q)
      _ = 3 * (L + M) ^ 2 * Real.log Q ^ 2 * Q / R := by ring
  have hN : neutralForm Q (stepSample F R J) - neutralForm Q F =
      (packetForm Q (stepSample F R J) - packetForm Q F) - 2 * (a * b - a' * b') := by
    unfold neutralForm
    rw [ha, hb, ha', hb']
    ring
  have habs : |(packetForm Q (stepSample F R J) - packetForm Q F) - 2 * (a * b - a' * b')| ≤
      |packetForm Q (stepSample F R J) - packetForm Q F| + 2 * |a * b - a' * b'| := by
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_two]
  have h9 : 3 * (L + M) ^ 2 * Real.log Q ^ 2 * Q / R ≤
      3 * (L + M) ^ 2 * ((Real.log Q + 1) * Real.log Q) * Q / R := by
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (by norm_num) (sq_nonneg _)))
      (Nat.cast_nonneg Q)) hR'.le
  have e : (L + M) ^ 2 * sampleError Q R J =
      (L + M) ^ 2 * ((Real.log Q + 1) / R *
        (160 * (logSamplingConst ((Real.log Q + 1) / 2) zetaZeroWidth *
          (16 * Real.log (1 + 4 * ((R + J : ℕ) : ℝ) * (R : ℝ) ^ 2) + 5)))) +
        2 * (3 * (L + M) ^ 2 * ((Real.log Q + 1) * Real.log Q) * Q / R) := by
    unfold sampleError
    ring
  rw [hN, e]
  linarith

end Sample

#print axioms abs_neutralForm_stepSample_sub_le

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
