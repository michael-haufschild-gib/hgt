import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateCombinationFailure

/-!
# The collar integral of the shifted ground states as a half-line integral against the collar mass

For `u` continuous with compact support and `a > 0`,

    ∫_{t>0} ω(t) ∫_0^t m_a(x) m_a(t−x) u(x)² dx dt
      + Σ_n Λ(n) n^{−1/2} ∫_0^{log n} m_a(x) m_a(log n − x) u(x)² dx
      = ∫_{x>0} u(x)² m_a(x) C_a(x) dx,

where `C_a` is the reflected collar mass. On `0 < x < t` the factor `m_a(t−x)` is its own positive
part and it vanishes for `x ≥ t`, so each inner integral is a half-line integral of
`m_a(x) m_a(t−x)⁺ u(x)²`. The exchange of the two integrations is justified by the bound
`m_a(x) m_a(t−x)⁺ ≤ Φ(0) max(L, Φ(0)) t` on the support of `u` (`L` a Lipschitz constant of `m_a`)
together with `∫_0^∞ ω(t) t dt < ∞`, and by the decay `m_a(y − x)⁺ ≤ (Φ(0)/Φ(R+a)) Φ(y − R − a)`
together with `Σ Λ(n) n^{−1/2} Φ(log n − c) < ∞`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Sign and positive part of the shift difference -/

theorem shiftDifference_apply_zero (a : ℝ) : shiftDifference a 0 = 0 := by
  have h := shiftDifference_neg a 0
  rw [neg_zero] at h
  linarith

theorem shiftDifference_nonpos_of_nonpos {a y : ℝ} (ha : 0 ≤ a) (hy : y ≤ 0) :
    shiftDifference a y ≤ 0 := by
  have h := shiftDifference_nonneg_of_nonneg ha (neg_nonneg.mpr hy)
  rw [shiftDifference_neg] at h
  linarith

theorem max_shiftDifference_eq_of_lt {a t x : ℝ} (ha : 0 ≤ a) (h : x < t) :
    max (shiftDifference a (t - x)) 0 = shiftDifference a (t - x) :=
  max_eq_left (shiftDifference_nonneg_of_nonneg ha (by linarith))

theorem max_shiftDifference_eq_zero_of_le {a t x : ℝ} (ha : 0 ≤ a) (h : t ≤ x) :
    max (shiftDifference a (t - x)) 0 = 0 :=
  max_eq_right (shiftDifference_nonpos_of_nonpos ha (by linarith))

/-- The collar integral on `(0, t)` is the half-line integral of the positive-part integrand. -/
theorem integral_Ioo_collar_eq_integral_Ioi_max {a : ℝ} (ha : 0 ≤ a) (u : ℝ → ℝ) (t : ℝ) :
    (∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) =
      ∫ x in Ioi (0 : ℝ), shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2 := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
    (fun x hx => ?_)]
  · exact (setIntegral_congr_fun measurableSet_Ioo fun x hx => by
      rw [max_shiftDifference_eq_of_lt ha hx.2]).symm
  · obtain ⟨hx0, hxt⟩ := hx
    have htx : t ≤ x := by
      by_contra h
      rw [not_le] at h
      exact hxt ⟨hx0, h⟩
    rw [max_shiftDifference_eq_zero_of_le ha htx]
    ring

/-- Decay of the positive part of `m_a(y − x)` in `y`, uniformly for `0 < x ≤ R`. -/
theorem max_shiftDifference_le_decay {a R x y : ℝ} (ha : 0 < a) (hxR : x ≤ R) (hy : 0 ≤ y) :
    max (shiftDifference a (y - x)) 0 ≤
      riemannKernelReal 0 / riemannKernelReal (R + a) * riemannKernelReal (y - R - a) := by
  have hΘ0 := riemannKernelReal_pos 0
  have hRa := riemannKernelReal_pos (R + a)
  have hK := (riemannKernelReal_pos (y - R - a)).le
  have hratio : 1 ≤ riemannKernelReal 0 / riemannKernelReal (R + a) := by
    rw [le_div_iff₀ hRa, one_mul]
    exact riemannKernelReal_le_zero_point _
  rcases le_or_gt (R + a) y with h | h
  · have hc0 : 0 ≤ y - R - a := by linarith
    have h1 : shiftDifference a (y - x) ≤ riemannKernelReal (y - R - a) := by
      have := abs_shiftDifference_le_kernel_of_nonneg ha.le (show 0 ≤ y - x by linarith)
      refine (le_abs_self _).trans (this.trans ?_)
      exact riemannKernelReal_antitone_of_nonneg hc0 (by linarith)
    calc max (shiftDifference a (y - x)) 0 ≤ riemannKernelReal (y - R - a) := max_le h1 hK
      _ = 1 * riemannKernelReal (y - R - a) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio hK
  · have h1 : max (shiftDifference a (y - x)) 0 ≤ riemannKernelReal 0 :=
      max_le (abs_le.mp (abs_shiftDifference_le a (y - x))).2 hΘ0.le
    have h2 : riemannKernelReal (R + a) ≤ riemannKernelReal (y - R - a) := by
      have := riemannKernelReal_sub_ge_of_le hy h.le
      rwa [← sub_sub] at this
    calc max (shiftDifference a (y - x)) 0 ≤ riemannKernelReal 0 := h1
      _ = riemannKernelReal 0 / riemannKernelReal (R + a) * riemannKernelReal (R + a) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (div_nonneg hΘ0.le hRa.le)

/-! ### The archimedean collar: product integrability and Fubini -/

theorem integrable_archLevy_collar_prod {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    Integrable (Function.uncurry fun t x =>
        archLevyDensity t * (shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  obtain ⟨Lm, hLm0, hLm⟩ :=
    exists_lipschitz_bound_on_Icc (contDiff_shiftDifference a) (-R - 1) (R + 1)
  have hΘ0 := (riemannKernelReal_pos 0).le
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = riemannKernelReal 0 * max Lm (riemannKernelReal 0) := ⟨_, rfl⟩
  have hint : Integrable (fun x => C * u x ^ 2) (volume.restrict (Ioi 0)) :=
    integrableOn_continuous_mul_sq continuous_const hu huc _
  have hdom : Integrable (fun z : ℝ × ℝ => (archLevyDensity z.1 * z.1) * (C * u z.2 ^ 2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Integrable.mul_prod integrableOn_archLevyDensity_mul_id hint
  have hmeas : Measurable fun z : ℝ × ℝ =>
      archLevyDensity z.1 *
        (shiftDifference a z.2 * max (shiftDifference a (z.1 - z.2)) 0 * u z.2 ^ 2) :=
    (measurable_archLevyDensity.comp measurable_fst).mul
      ((((continuous_shiftDifference a).comp continuous_snd).mul
        (((continuous_shiftDifference a).comp (continuous_fst.sub continuous_snd)).max
          continuous_const)).mul ((hu.comp continuous_snd).pow 2)).measurable
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun z hz => ?_
  have ht : 0 < z.1 := hz.1
  have hx : 0 < z.2 := hz.2
  have hL := archLevyDensity_pos ht
  show ‖archLevyDensity z.1 *
      (shiftDifference a z.2 * max (shiftDifference a (z.1 - z.2)) 0 * u z.2 ^ 2)‖ ≤
    (archLevyDensity z.1 * z.1) * (C * u z.2 ^ 2)
  by_cases hxR : z.2 ≤ R
  · have hmx : shiftDifference a z.2 ≤ riemannKernelReal 0 :=
      (abs_le.mp (abs_shiftDifference_le a z.2)).2
    have hmx0 : 0 ≤ shiftDifference a z.2 := shiftDifference_nonneg_of_nonneg ha.le hx.le
    have hmax : max (shiftDifference a (z.1 - z.2)) 0 ≤ max Lm (riemannKernelReal 0) * z.1 := by
      rcases le_or_gt z.1 1 with h1 | h1
      · rcases le_or_gt (z.1 - z.2) 0 with h0 | h0
        · rw [max_eq_right (shiftDifference_nonpos_of_nonpos ha.le h0)]
          exact mul_nonneg (le_max_of_le_left hLm0) ht.le
        · rw [max_eq_left (shiftDifference_nonneg_of_nonneg ha.le h0.le)]
          have hmem1 : z.1 - z.2 ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
          have hmem0 : (0 : ℝ) ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
          have hlip := hLm 0 hmem0 (z.1 - z.2) hmem1
          rw [shiftDifference_apply_zero, sub_zero, sub_zero, abs_of_pos h0] at hlip
          calc shiftDifference a (z.1 - z.2) ≤ Lm * (z.1 - z.2) := (abs_le.mp hlip).2
            _ ≤ Lm * z.1 := mul_le_mul_of_nonneg_left (by linarith) hLm0
            _ ≤ max Lm (riemannKernelReal 0) * z.1 :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le
      · calc max (shiftDifference a (z.1 - z.2)) 0 ≤ riemannKernelReal 0 :=
              max_le (abs_le.mp (abs_shiftDifference_le a (z.1 - z.2))).2 hΘ0
          _ ≤ riemannKernelReal 0 * z.1 := le_mul_of_one_le_right hΘ0 h1.le
          _ ≤ max Lm (riemannKernelReal 0) * z.1 :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le
    have hkey : shiftDifference a z.2 * max (shiftDifference a (z.1 - z.2)) 0 ≤ C * z.1 := by
      calc shiftDifference a z.2 * max (shiftDifference a (z.1 - z.2)) 0
          ≤ riemannKernelReal 0 * (max Lm (riemannKernelReal 0) * z.1) :=
            mul_le_mul hmx hmax (le_max_right _ _) hΘ0
        _ = C * z.1 := by rw [hC]; ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hL, abs_mul, abs_of_nonneg (sq_nonneg (u z.2)),
      abs_of_nonneg (mul_nonneg hmx0 (le_max_right (shiftDifference a (z.1 - z.2)) 0))]
    calc archLevyDensity z.1 *
          (shiftDifference a z.2 * max (shiftDifference a (z.1 - z.2)) 0 * u z.2 ^ 2)
        ≤ archLevyDensity z.1 * (C * z.1 * u z.2 ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey (sq_nonneg _)) hL.le
      _ = (archLevyDensity z.1 * z.1) * (C * u z.2 ^ 2) := by ring
  · rw [not_le] at hxR
    rw [hsupp z.2 (by rw [abs_of_pos hx]; exact hxR)]
    simp

/-- Fubini for the archimedean collar. -/
theorem integral_archLevy_collar_eq_integral_collarMassArch {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0 := by
  have hswap := integral_integral_swap (integrable_archLevy_collar_prod ha hu huc)
  calc (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2)
      = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
          archLevyDensity t *
            (shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [integral_Ioo_collar_eq_integral_Ioi_max ha.le, integral_const_mul]
    _ = ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
          archLevyDensity t *
            (shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2) := hswap
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        ring

/-- The archimedean part of `u² m_a C_a` is integrable on the half line. -/
theorem integrableOn_sq_mul_shiftDifference_mul_archCollar {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x *
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0) (Ioi 0) := by
  have h := (integrable_archLevy_collar_prod ha hu huc).integral_prod_right
  refine h.congr (Eventually.of_forall fun x => ?_)
  show (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      (shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2)) =
    u x ^ 2 * shiftDifference a x *
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * max (shiftDifference a (t - x)) 0
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring

/-! ### The prime collar: summability and Fubini -/

theorem integrable_atom_collar_term {a : ℝ} {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (y : ℝ) :
    Integrable (fun x => shiftDifference a x * max (shiftDifference a (y - x)) 0 * u x ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
  integrableOn_continuous_mul_sq ((continuous_shiftDifference a).mul
    (((continuous_shiftDifference a).comp (continuous_const.sub continuous_id)).max
      continuous_const)) hu huc _

theorem summable_integral_norm_atom_collar {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖vonMangoldtAtom n *
      (shiftDifference a x * max (shiftDifference a (Real.log n - x)) 0 * u x ^ 2)‖ := by
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  obtain ⟨Mu, hMu'⟩ := hu.bounded_above_of_compact_support huc
  have hMu : ∀ x, |u x| ≤ Mu := fun x => by
    rw [← Real.norm_eq_abs]
    exact hMu' x
  have hR0 : 0 ≤ R := by linarith
  have hΘ0 := (riemannKernelReal_pos 0).le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = riemannKernelReal 0 / riemannKernelReal (R + a) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact div_nonneg hΘ0 (riemannKernelReal_pos _).le
  have hbig : Summable fun n : ℕ => (riemannKernelReal 0 * D * Mu ^ 2 * R) *
      (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by
    refine ((summable_atom_riemannKernelReal_log_sub (R + a)).mul_left
      (riemannKernelReal 0 * D * Mu ^ 2 * R)).congr fun n => ?_
    rw [sub_sub]
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
    (fun n => ?_) hbig
  have hΛ := vonMangoldtAtom_nonneg n
  have hK := (riemannKernelReal_pos (Real.log n - R - a)).le
  have hb : ∀ x, 0 < x → |vonMangoldtAtom n *
      (shiftDifference a x * max (shiftDifference a (Real.log n - x)) 0 * u x ^ 2)| ≤
      (vonMangoldtAtom n * riemannKernelReal 0 * D * riemannKernelReal (Real.log n - R - a) *
        Mu ^ 2) * (if x ≤ R then 1 else 0) := by
    intro x hx
    split_ifs with hxR
    · rw [mul_one, abs_mul, abs_of_nonneg hΛ, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (u x)),
        abs_of_nonneg (le_max_right (shiftDifference a (Real.log n - x)) 0)]
      have h1 := abs_shiftDifference_le a x
      have h2 := max_shiftDifference_le_decay ha hxR (Real.log_natCast_nonneg n)
      rw [← hD] at h2
      have hu2 : u x ^ 2 ≤ Mu ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hMu x) 2
      calc vonMangoldtAtom n *
            (|shiftDifference a x| * max (shiftDifference a (Real.log n - x)) 0 * u x ^ 2)
          ≤ vonMangoldtAtom n *
            (riemannKernelReal 0 * (D * riemannKernelReal (Real.log n - R - a)) * Mu ^ 2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul h1 h2 (le_max_right _ _) hΘ0) hu2 (sq_nonneg _)
                (mul_nonneg hΘ0 (mul_nonneg hD0 hK))) hΛ
        _ = _ := by ring
    · rw [not_le] at hxR
      rw [hsupp x (by rw [abs_of_pos hx]; exact hxR)]
      simp
  refine (integral_Ioi_norm_le_of_le_indicator hR0 hb).trans (le_of_eq ?_)
  ring

/-- Fubini for the prime collar. -/
theorem tsum_atom_collar_eq_integral_collarMassPrime {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        shiftDifference a x * shiftDifference a (Real.log n - x) * u x ^ 2) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
        ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 := by
  have h1 : ∀ n : ℕ, vonMangoldtAtom n * (∫ x in Ioo (0 : ℝ) (Real.log n),
      shiftDifference a x * shiftDifference a (Real.log n - x) * u x ^ 2) =
      ∫ x in Ioi (0 : ℝ), vonMangoldtAtom n *
        (shiftDifference a x * max (shiftDifference a (Real.log n - x)) 0 * u x ^ 2) := by
    intro n
    rw [integral_Ioo_collar_eq_integral_Ioi_max ha.le, integral_const_mul]
  rw [tsum_congr h1, integral_tsum_of_summable_integral_norm
    (F := fun n : ℕ => fun x => vonMangoldtAtom n *
      (shiftDifference a x * max (shiftDifference a (Real.log n - x)) 0 * u x ^ 2))
    (fun n => (integrable_atom_collar_term hu huc (Real.log n)).const_mul _)
    (summable_integral_norm_atom_collar ha hu huc)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- The prime part of `u² m_a C_a` is integrable on the half line. -/
theorem integrableOn_sq_mul_shiftDifference_mul_primeCollar {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x *
      ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0) (Ioi 0) := by
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  obtain ⟨Mu, hMu'⟩ := hu.bounded_above_of_compact_support huc
  have hMu : ∀ x, |u x| ≤ Mu := fun x => by
    rw [← Real.norm_eq_abs]
    exact hMu' x
  have hR0 : 0 ≤ R := by linarith
  have hΘ0 := (riemannKernelReal_pos 0).le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = riemannKernelReal 0 / riemannKernelReal (R + a) := ⟨_, rfl⟩
  have hB : Summable fun n : ℕ =>
      D * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by
    refine ((summable_atom_riemannKernelReal_log_sub (R + a)).mul_left D).congr fun n => ?_
    rw [sub_sub]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = ∑' n : ℕ, D * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := ⟨_, rfl⟩
  have hpt : ∀ x, 0 < x → x ≤ R →
      |u x ^ 2 * shiftDifference a x *
        ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0| ≤
        Mu ^ 2 * riemannKernelReal 0 * B := by
    intro x hx hxR
    have hterm : ∀ n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 ≤
        D * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := fun n => by
      have h := max_shiftDifference_le_decay ha hxR (Real.log_natCast_nonneg n)
      rw [← hD] at h
      calc vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0
          ≤ vonMangoldtAtom n * (D * riemannKernelReal (Real.log n - R - a)) :=
            mul_le_mul_of_nonneg_left h (vonMangoldtAtom_nonneg n)
        _ = D * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by ring
    have hsum := summable_atom_max_shiftDifference a x
    have htsum : (∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0) ≤ B := by
      rw [hBdef]
      exact Summable.tsum_le_tsum hterm hsum hB
    have htsum0 : 0 ≤ ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 :=
      tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (le_max_right _ _)
    have hmx0 := shiftDifference_nonneg_of_nonneg ha.le hx.le
    have hmx := (abs_le.mp (abs_shiftDifference_le a x)).2
    have hu2 : u x ^ 2 ≤ Mu ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hMu x) 2
    have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (u x)), abs_of_nonneg hmx0, abs_of_nonneg htsum0]
    exact mul_le_mul (mul_le_mul hu2 hmx hmx0 (sq_nonneg _)) htsum htsum0 (by positivity)
  have hg0 : IntegrableOn (fun _ : ℝ => Mu ^ 2 * riemannKernelReal 0 * B) (Ioc (0 : ℝ) R) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hg : Integrable ((Ioc (0 : ℝ) R).indicator fun _ => Mu ^ 2 * riemannKernelReal 0 * B)
      (volume.restrict (Ioi 0)) :=
    (hg0.integrable_indicator measurableSet_Ioc).integrableOn
  have hmeas : AEStronglyMeasurable (fun x => u x ^ 2 * shiftDifference a x *
      ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0)
      (volume.restrict (Ioi 0)) := by
    refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => u x ^ 2 * shiftDifference a x *
      ∑ n ∈ Finset.range N, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0)
      atTop (fun N => ?_) ?_
    · refine Continuous.aestronglyMeasurable (((hu.pow 2).mul (continuous_shiftDifference a)).mul ?_)
      exact continuous_finsetSum _ fun n _ => continuous_const.mul
        (((continuous_shiftDifference a).comp (continuous_const.sub continuous_id)).max
          continuous_const)
    · exact Eventually.of_forall fun x =>
        ((summable_atom_max_shiftDifference a x).hasSum.tendsto_sum_nat).const_mul _
  refine hg.mono' hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  rw [Real.norm_eq_abs, Set.indicator_apply]
  by_cases hxR : x ≤ R
  · rw [if_pos ⟨hx, hxR⟩]
    exact hpt x hx hxR
  · rw [if_neg fun hm => hxR hm.2]
    rw [not_le] at hxR
    rw [hsupp x (by rw [abs_of_pos hx]; exact hxR)]
    simp

/-! ### The collar Fubini identity -/

/-- `u² m_a C_a` is integrable on the half line. -/
theorem integrableOn_sq_mul_shiftDifference_mul_collarMass {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * shiftedCollarMass a x) (Ioi 0) := by
  have h := (integrableOn_sq_mul_shiftDifference_mul_archCollar ha hu huc).add
    (integrableOn_sq_mul_shiftDifference_mul_primeCollar ha hu huc)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  unfold shiftedCollarMass
  simp only [Pi.add_apply]
  ring

/-- **Collar Fubini.** The shift integral of the collar integrals of `u² m_a ⊗ m_a` is the half-line
integral of `u² m_a` against the reflected collar mass. -/
theorem integral_dm_collar_eq_integral_sq_mul_collarMass {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) +
      (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        shiftDifference a x * shiftDifference a (Real.log n - x) * u x ^ 2) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x := by
  rw [integral_archLevy_collar_eq_integral_collarMassArch ha hu huc,
    tsum_atom_collar_eq_integral_collarMassPrime ha hu huc,
    ← integral_add (integrableOn_sq_mul_shiftDifference_mul_archCollar ha hu huc)
      (integrableOn_sq_mul_shiftDifference_mul_primeCollar ha hu huc)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  unfold shiftedCollarMass
  ring

/-- Integrability in the shift of the archimedean collar integral. -/
theorem integrableOn_archLevy_mul_collarIntegral {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun t => archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) (Ioi 0) := by
  have h := (integrable_archLevy_collar_prod ha hu huc).integral_prod_left
  refine h.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_)
  show (∫ x in Ioi (0 : ℝ), archLevyDensity t *
      (shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2)) =
    archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2
  rw [integral_Ioo_collar_eq_integral_Ioi_max ha.le, integral_const_mul]

/-- Summability in the prime of the prime collar integrals. -/
theorem summable_atom_mul_collarIntegral {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    Summable fun n : ℕ => vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      shiftDifference a x * shiftDifference a (Real.log n - x) * u x ^ 2 := by
  have hs := summable_integral_norm_atom_collar ha hu huc
  refine hs.of_norm_bounded fun n => ?_
  rw [integral_Ioo_collar_eq_integral_Ioi_max ha.le, ← integral_const_mul]
  exact norm_integral_le_integral_norm _

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
