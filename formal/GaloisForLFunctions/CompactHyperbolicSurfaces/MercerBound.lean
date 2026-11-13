import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerRepresentatives
import GaloisForLFunctions.HTGeometry.SchurKernelComposition

/-!
# A uniform bound for the continuous eigenfunctions

The rows of the singular kernel `K_a(w, ·) = Σ_γ k_a(u(w, γ·))` lie in `L²(F)` with a bound
independent of `w` (`exists_rowEnergy_le`): near the diagonal at most `N₀` translates contribute
and `k_a(u) ≤ C u^{−1/8}` is square integrable; away from it the kernel is bounded.  Bessel's
inequality for these rows, `⟨e_j, K_a(w, ·)⟩ = μ_j \overline{ẽ_j(w)}`, gives
`Σ_j μ_j² |ẽ_j(w)|² ≤ B`, and `ν_j ≤ (b(b−1) − a(a−1)) μ_j²` turns it into

  `Σ_{j ∈ S} ν_j |ẽ_j(w)|² ≤ B'`  for every finite `S` and every `w` (`exists_sum_nu_specRep_le`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real Metric
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- **Local size, sharper.**  `k_s(u) ≤ C u^{−1/8}` for `u > 0`. -/
theorem exists_resKernel_le_rpow_eighth {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → resKernel s u ≤ ENNReal.ofReal (C * u ^ (-(1 / 8 : ℝ))) := by
  set I : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)
  have hI : IntegrableOn (fun t : ℝ => t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) (Ioi 0) :=
    integrableOn_rpow_mul_one_add_rpow (by norm_num) (by linarith)
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0:ℝ) < t := ht; positivity
  refine ⟨1 / (4 * π) * I, by positivity, fun u hu => ?_⟩
  rw [resKernel_eq_lintegral_Ioi]
  have hb : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹) ≤
      ENNReal.ofReal (u ^ (-(1 / 8 : ℝ))) * ENNReal.ofReal (t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := greenDensity_le hs (show 0 < u + t by linarith)
    have h2 : (u + t) ^ (-(1 / 2 : ℝ)) ≤ u ^ (-(1 / 8 : ℝ)) * t ^ (-(3 / 8 : ℝ)) := by
      have hA : u ^ (1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) ≤ (u + t) ^ (1 / 2 : ℝ) := by
        calc u ^ (1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) ≤ (u + t) ^ (1 / 8 : ℝ) * (u + t) ^ (3 / 8 : ℝ) :=
              mul_le_mul (Real.rpow_le_rpow hu.le (by linarith) (by norm_num))
                (Real.rpow_le_rpow ht0.le (by linarith) (by norm_num)) (by positivity) (by positivity)
          _ = (u + t) ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add (by linarith)]; norm_num
      have hpos : 0 < u ^ (1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) := by positivity
      rw [Real.rpow_neg (by linarith), Real.rpow_neg hu.le, Real.rpow_neg ht0.le, ← mul_inv]
      exact inv_anti₀ hpos hA
    have h3 : (1 + (u + t)) ^ (-s) ≤ (1 + t) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h4 : (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht0.le]
    rw [h4]
    calc greenDensity s (u + t) * t ^ (-(1 / 2 : ℝ))
        ≤ (u + t) ^ (-(1 / 2 : ℝ)) * (1 + (u + t)) ^ (-s) * t ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (u ^ (-(1 / 8 : ℝ)) * t ^ (-(3 / 8 : ℝ))) * (1 + t) ^ (-s) * t ^ (-(1 / 2 : ℝ)) := by
          gcongr
      _ = u ^ (-(1 / 8 : ℝ)) * (t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) := by
          rw [show t ^ (-(7 / 8 : ℝ)) = t ^ (-(3 / 8 : ℝ)) * t ^ (-(1 / 2 : ℝ)) by
            rw [← Real.rpow_add ht0]; norm_num]
          ring
  calc ENNReal.ofReal (1 / (4 * π)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹)
      ≤ ENNReal.ofReal (1 / (4 * π)) * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(1 / 8 : ℝ))) * ENNReal.ofReal (t ^ (-(7 / 8 : ℝ)) * (1 + t) ^ (-s)) :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hb) _
    _ = ENNReal.ofReal (1 / (4 * π)) * (ENNReal.ofReal (u ^ (-(1 / 8 : ℝ))) * ENNReal.ofReal I) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal hI
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => by
            have : (0:ℝ) < r := hr; positivity))]
    _ = ENNReal.ofReal (1 / (4 * π) * I * u ^ (-(1 / 8 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- The singular profile `u ↦ u^{−¼}` on `(0, 1]`. -/
def quarterProfile (u : ℝ) : ℝ := if 0 < u ∧ u ≤ 1 then u ^ (-(1 / 4 : ℝ)) else 0

theorem quarterProfile_nonneg (u : ℝ) : 0 ≤ quarterProfile u := by
  unfold quarterProfile; split_ifs with h
  · exact Real.rpow_nonneg h.1.le _
  · exact le_rfl

theorem measurable_quarterProfile : Measurable quarterProfile := by
  unfold quarterProfile
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact (measurableSet_lt measurable_const measurable_id).inter (measurableSet_le measurable_id
    measurable_const)

/-- **Layer cake.**  `∫_ℍ u(i, w)^{−¼} 1_{u ≤ 1} dμ(w) < ∞`. -/
theorem lintegral_quarterProfile_lt_top :
    ∫⁻ w : ℍ, ENNReal.ofReal (quarterProfile (pairU I w)) < ∞ := by
  have hm : Measurable fun w : ℍ => quarterProfile (pairU I w) :=
    measurable_quarterProfile.comp (continuous_pairU.comp
      (continuous_const.prodMk continuous_id)).measurable
  rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall fun w => quarterProfile_nonneg _)
    hm.aemeasurable]
  have hb : ∀ t ∈ Ioi (0 : ℝ), volume {w : ℍ | t < quarterProfile (pairU I w)} ≤
      ENNReal.ofReal (32 * min 1 (t ^ (-(4 : ℝ)))) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hmin : 0 ≤ min 1 (t ^ (-(4 : ℝ))) := le_min zero_le_one (by positivity)
    refine (measure_mono fun w hw => ?_).trans (volume_pairU_I_le hmin)
    simp only [mem_setOf_eq] at hw ⊢
    unfold quarterProfile at hw
    split_ifs at hw with h
    · refine le_min h.2 ?_
      have hu : 0 < pairU I w := h.1
      -- `t < u^{−¼}` gives `u < t^{−4}`
      have h2 : pairU I w = (pairU I w ^ (-(1 / 4 : ℝ))) ^ (-(4 : ℝ)) := by
        rw [← Real.rpow_mul hu.le]; norm_num
      rw [h2]
      exact (Real.rpow_le_rpow_of_nonpos ht0 hw.le (by norm_num))
    · exact absurd hw (not_lt.mpr ht0.le)
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hb) ?_
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (32 * min 1 (t ^ (-(4 : ℝ)))) ≤
      (Ioc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal 32) t +
        (Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (32 * t ^ (-(4 : ℝ)))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases le_or_gt t 1 with h | h
    · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, h⟩)]
      exact le_add_right (ENNReal.ofReal_le_ofReal (by
        have := min_le_left (1 : ℝ) (t ^ (-(4 : ℝ))); linarith))
    · rw [indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h)]
      exact le_add_left (ENNReal.ofReal_le_ofReal (by
        have := min_le_right (1 : ℝ) (t ^ (-(4 : ℝ))); nlinarith))
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hsplit) ?_
  rw [lintegral_add_left' ((measurable_const.indicator measurableSet_Ioc).aemeasurable)]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
    rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
    rw [lintegral_indicator measurableSet_Ioi]
    exact ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 32).lintegral_lt_top

/-- `(Σ_s f)² ≤ 2 |s| Σ_s f²`. -/
theorem sq_sum_le_two_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ 2 * s.card * ∑ i ∈ s, f i ^ 2 := by
  have hpair : ∀ x y : ℝ≥0∞, x * y ≤ x ^ 2 + y ^ 2 := by
    intro x y
    calc x * y ≤ max x y * max x y := mul_le_mul' (le_max_left _ _) (le_max_right _ _)
      _ = max (x ^ 2) (y ^ 2) := by
          rcases le_total x y with h | h
          · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ bot_le h 2), sq]
          · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ bot_le h 2), sq]
      _ ≤ x ^ 2 + y ^ 2 := max_le le_self_add le_add_self
  calc (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i * f j := by rw [sq, Finset.sum_mul_sum]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (f i ^ 2 + f j ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair _ _
    _ = 2 * s.card * ∑ i ∈ s, f i ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum]
        ring

theorem add_sq_le_four (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2) := by
  calc (x + y) ^ 2 ≤ (2 * max x y) ^ 2 := by
        refine pow_le_pow_left₀ bot_le ?_ 2
        rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
    _ = 4 * (max x y) ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (x ^ 2 + y ^ 2) := by
        refine mul_le_mul_right ?_ _
        rcases le_total x y with h | h
        · rw [max_eq_right h]; exact le_add_self
        · rw [max_eq_left h]; exact le_self_add

/-- The near part `k_a · 1_{u ≤ 1}`. -/
def nearRes (a : ℝ) : ℝ → ℝ≥0∞ := (Iic (1 : ℝ)).indicator (resKernel a)

/-- The far part `k_a · 1_{u > 1}`. -/
def farRes (a : ℝ) : ℝ → ℝ≥0∞ := (Ioi (1 : ℝ)).indicator (resKernel a)

namespace CompactQuotient

variable (X : CompactQuotient)

/-- **Uniform row energy of `K_a`.** -/
theorem exists_rowEnergy_le {a : ℝ} (ha : 1 < a) : ∃ R : ℝ≥0∞, R < ∞ ∧ ∀ w : ℍ,
    ∫⁻ ξ in X.F, (autK X.Γ (resKernel a) w ξ) ^ 2 ≤ R := by
  have ha' : 1 / 2 < a := by linarith
  obtain ⟨C₈, hC₈, hC₈le⟩ := exists_resKernel_le_rpow_eighth ha'
  obtain ⟨C₁, hC₁, hC₁le⟩ := exists_resKernel_le_rpow_neg ha'
  obtain ⟨M, hM, hMle⟩ := X.cocompactFree.exists_autK_le ha
  obtain ⟨Ccnt, hCcnt, hcount⟩ := X.cocompactFree.exists_card_le
  have hsplit : ∀ u, resKernel a u = nearRes a u + farRes a u := by
    intro u
    rw [nearRes, farRes]
    rcases le_or_gt u 1 with h | h
    · rw [indicator_of_mem (show u ∈ Iic (1 : ℝ) from h),
        indicator_of_notMem (show u ∉ Ioi (1 : ℝ) from not_lt.mpr h), add_zero]
    · rw [indicator_of_notMem (show u ∉ Iic (1 : ℝ) from not_le.mpr h),
        indicator_of_mem (show u ∈ Ioi (1 : ℝ) from h), zero_add]
  have hfar : ∀ u, 0 ≤ u → farRes a u ≤ ENNReal.ofReal (C₁ * 2 ^ a * (1 + u) ^ (-a)) := by
    intro u hu
    rw [farRes]
    by_cases h : 1 < u
    · rw [indicator_of_mem (show u ∈ Ioi (1 : ℝ) from h)]
      refine (hC₁le u (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      have h3 := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < 1 + u)
        (show 1 + u ≤ 2 * u by linarith) (show -a ≤ 0 by linarith)
      rw [Real.mul_rpow (by norm_num) (by linarith)] at h3
      have h4 : (2 : ℝ) ^ a * 2 ^ (-a) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
      calc C₁ * u ^ (-a) = C₁ * 2 ^ a * (2 ^ (-a) * u ^ (-a)) := by
            rw [mul_assoc C₁, ← mul_assoc (2 ^ a), h4, one_mul]
        _ ≤ C₁ * 2 ^ a * (1 + u) ^ (-a) := mul_le_mul_of_nonneg_left h3 (by positivity)
    · rw [indicator_of_notMem (show u ∉ Ioi (1 : ℝ) from h)]; exact bot_le
  have hnear_sq : ∀ u, 0 < u → nearRes a u ^ 2 ≤
      ENNReal.ofReal (C₈ ^ 2) * ENNReal.ofReal (quarterProfile u) := by
    intro u hu
    rw [nearRes]
    by_cases h : u ≤ 1
    · rw [indicator_of_mem (show u ∈ Iic (1 : ℝ) from h)]
      have h1 := hC₈le u hu
      calc resKernel a u ^ 2 ≤ ENNReal.ofReal (C₈ * u ^ (-(1 / 8 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ bot_le h1 2
        _ = ENNReal.ofReal (C₈ ^ 2) * ENNReal.ofReal (quarterProfile u) := by
            rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have hq : (u ^ (-(1 / 8 : ℝ))) ^ 2 = u ^ (-(1 / 4 : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num
            unfold quarterProfile
            rw [if_pos ⟨hu, h⟩, mul_pow, hq]
    · rw [indicator_of_notMem (show u ∉ Iic (1 : ℝ) from h)]; simp
  set L := ∫⁻ w : ℍ, ENNReal.ofReal (quarterProfile (pairU I w))
  have hL : L < ∞ := lintegral_quarterProfile_lt_top
  set N₀ : ℝ≥0∞ := ENNReal.ofReal (Ccnt * 2)
  refine ⟨4 * (2 * N₀ * (ENNReal.ofReal (C₈ ^ 2) * L) +
      (ENNReal.ofReal (C₁ * 2 ^ a) * M) ^ 2 * volume X.F), ?_, fun w => ?_⟩
  · refine ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hL)
    · exact ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM))
        X.volume_F_lt_top
  -- pointwise split of the kernel
  have hpt : ∀ ξ : ℍ, (autK X.Γ (resKernel a) w ξ) ^ 2 ≤
      4 * (2 * N₀ * autK X.Γ (fun u => nearRes a u ^ 2) w ξ + (ENNReal.ofReal (C₁ * 2 ^ a) * M) ^ 2) := by
    intro ξ
    have hsum : autK X.Γ (resKernel a) w ξ = autK X.Γ (nearRes a) w ξ + autK X.Γ (farRes a) w ξ := by
      rw [autK, autK, autK, ← ENNReal.tsum_add]; exact tsum_congr fun γ => hsplit _
    have hF : autK X.Γ (farRes a) w ξ ≤ ENNReal.ofReal (C₁ * 2 ^ a) * M := hMle hfar w ξ
    obtain ⟨hfin, hcard⟩ := hcount w ξ 1 zero_le_one
    set S := {γ : X.Γ | pairU w ((γ : SL(2, ℝ)) • ξ) ≤ 1}
    have hnear_eq : autK X.Γ (nearRes a) w ξ = ∑ γ ∈ hfin.toFinset, nearRes a (pairU w ((γ : SL(2, ℝ)) • ξ)) := by
      rw [autK]
      refine tsum_eq_sum fun γ hγ => ?_
      have : ¬ pairU w ((γ : SL(2, ℝ)) • ξ) ≤ 1 := fun h => hγ (hfin.mem_toFinset.mpr h)
      rw [nearRes]
      exact indicator_of_notMem (show pairU w ((γ : SL(2, ℝ)) • ξ) ∉ Iic (1 : ℝ) from this) _
    have hnear_sq_eq : ∑ γ ∈ hfin.toFinset, nearRes a (pairU w ((γ : SL(2, ℝ)) • ξ)) ^ 2 =
        autK X.Γ (fun u => nearRes a u ^ 2) w ξ := by
      rw [autK]
      refine (tsum_eq_sum fun γ hγ => ?_).symm
      have : ¬ pairU w ((γ : SL(2, ℝ)) • ξ) ≤ 1 := fun h => hγ (hfin.mem_toFinset.mpr h)
      rw [nearRes, indicator_of_notMem (show pairU w ((γ : SL(2, ℝ)) • ξ) ∉ Iic (1 : ℝ) from this)]
      simp
    have hcardle : (hfin.toFinset.card : ℝ≥0∞) ≤ N₀ := by
      rw [← Set.ncard_eq_toFinset_card S hfin, ← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (S.ncard : ℝ) ≤ Ccnt * (1 + 1) := hcard
        _ = Ccnt * 2 := by ring
    have hN : (autK X.Γ (nearRes a) w ξ) ^ 2 ≤ 2 * N₀ * autK X.Γ (fun u => nearRes a u ^ 2) w ξ := by
      rw [hnear_eq, ← hnear_sq_eq]
      refine (sq_sum_le_two_card_mul _ _).trans ?_
      exact mul_le_mul_left (mul_le_mul_right hcardle _) _
    rw [hsum]
    refine (add_sq_le_four _ _).trans (mul_le_mul_right (add_le_add hN ?_) _)
    exact pow_le_pow_left₀ bot_le hF 2
  calc ∫⁻ ξ in X.F, (autK X.Γ (resKernel a) w ξ) ^ 2
      ≤ ∫⁻ ξ in X.F, 4 * (2 * N₀ * autK X.Γ (fun u => nearRes a u ^ 2) w ξ +
          (ENNReal.ofReal (C₁ * 2 ^ a) * M) ^ 2) := lintegral_mono hpt
    _ = 4 * (2 * N₀ * (∫⁻ ξ in X.F, autK X.Γ (fun u => nearRes a u ^ 2) w ξ) +
          (ENNReal.ofReal (C₁ * 2 ^ a) * M) ^ 2 * volume X.F) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top),
          setLIntegral_const, mul_comm ((ENNReal.ofReal (C₁ * 2 ^ a) * M) ^ 2)]
    _ ≤ 4 * (2 * N₀ * (ENNReal.ofReal (C₈ ^ 2) * L) +
          (ENNReal.ofReal (C₁ * 2 ^ a) * M) ^ 2 * volume X.F) := by
        refine mul_le_mul_right (add_le_add (mul_le_mul_right ?_ _) le_rfl) _
        have hmeas : Measurable fun u => nearRes a u ^ 2 :=
          ((measurable_resKernel a).indicator measurableSet_Iic).pow_const 2
        rw [setLIntegral_autK X.isFundamentalDomain hmeas, lintegral_pairU_eq_I (fun u => nearRes a u ^ 2) w,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_singleton I)] with ξ hξ
        have hne : I ≠ ξ := fun h => hξ (by rw [h]; rfl)
        have hpos : 0 < pairU I ξ := by
          rw [pairU_eq_cosh]
          have := Real.one_lt_cosh.mpr (dist_pos.mpr hne).ne'
          linarith
        exact hnear_sq _ hpos

/-- `ν_j ≤ (b(b − 1) − a(a − 1)) μ_j²`. -/
theorem nu_le_sq {a b : ℝ} (ha : 1 < a) (hab : a < b) (j : X.SpecIndex ha) :
    X.nu ha (b := b) j ≤ (b * (b - 1) - a * (a - 1)) * X.specMu ha j ^ 2 := by
  have hl := X.spectralParam_nonneg ha j
  have hA : 0 < a * (a - 1) := by nlinarith
  have hAB : a * (a - 1) < b * (b - 1) := by nlinarith
  rw [nu_def, X.specMu_eq ha j]
  set l := X.spectralParam ha j
  have h1 : 0 < l + a * (a - 1) := by linarith
  have h2 : l + a * (a - 1) ≤ l + b * (b - 1) := by linarith
  calc 1 / (l + a * (a - 1)) - 1 / (l + b * (b - 1))
      = (b * (b - 1) - a * (a - 1)) / ((l + a * (a - 1)) * (l + b * (b - 1))) := by
        rw [div_sub_div _ _ h1.ne' (by linarith)]; ring
    _ ≤ (b * (b - 1) - a * (a - 1)) / ((l + a * (a - 1)) * (l + a * (a - 1))) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity)
          (mul_le_mul_of_nonneg_left h2 h1.le)
    _ = (b * (b - 1) - a * (a - 1)) * (1 / (l + a * (a - 1))) ^ 2 := by
        rw [one_div, inv_pow, ← div_eq_mul_inv, sq]

/-- **Bessel's inequality for the continuous eigenfunctions.**
`Σ_{j ∈ S} ν_j |ẽ_j(w)|² ≤ B` for every finite `S` and every `w`: almost everywhere
`μ_j ẽ_j(w) = ⟨K_a(w, ·), e_j⟩`, the rows have energy at most `R`, and the bound passes from
almost every `w` to every `w` by continuity and `Γ`-invariance. -/
theorem exists_sum_nu_specRep_le {a b : ℝ} (ha : 1 < a) (hab : a < b) : ∃ B : ℝ,
    ∀ (S : Finset (X.SpecIndex ha)) (w : ℍ),
      ∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 ≤ B := by
  obtain ⟨R, hR, hRle⟩ := X.exists_rowEnergy_le ha
  set k := X.profileKernel (measurable_resKernel a) (lintegral_resKernel_mass_lt_top ha)
  have hto : ∀ w ξ, k.toFun w ξ = ((autK X.Γ (resKernel a) w ξ).toReal : ℂ) := fun _ _ => rfl
  have hrow : ∀ w, ∫⁻ ξ, ‖k.toFun w ξ‖ₑ ^ 2 ∂X.μ ≤ R := by
    intro w
    refine le_trans (lintegral_mono fun ξ => ?_) (hRle w)
    rw [hto, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact pow_le_pow_left₀ bot_le ENNReal.ofReal_toReal_le 2
  have hk2 : ∫⁻ y, ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂X.μ ∂X.μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono hrow) ?_
    rw [lintegral_const]
    exact ENNReal.mul_lt_top hR (measure_lt_top _ _)
  have hnorm : ∀ w, ‖k.rowVec w‖ ^ 2 ≤ R.toReal := by
    intro w
    have hw := lt_of_le_of_lt (hrow w) hR
    rw [Lp.norm_def, eLpNorm_congr_ae (k.rowVec_coeFn hw), ← ENNReal.toReal_pow, eLpNorm_two_sq]
    simp only [RCLike.enorm_conj]
    exact ENNReal.toReal_mono hR.ne (hrow w)
  have hC : 0 ≤ b * (b - 1) - a * (a - 1) := by nlinarith
  have hon := orthonormal_eigenVec (X.isSymmetric_resOp ha)
  refine ⟨(b * (b - 1) - a * (a - 1)) * R.toReal, fun S w => ?_⟩
  have hae : ∀ᵐ w ∂X.μ, ∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 ≤
      (b * (b - 1) - a * (a - 1)) * R.toReal := by
    have hj : ∀ᵐ w ∂X.μ, ∀ j ∈ S, ((X.specMu ha j : ℝ) : ℂ) * X.specRep ha (b := b) j w =
        ⟪k.rowVec w, X.specVec ha j⟫_ℂ := by
      refine (eventually_all_finset S).mpr fun j _ => ?_
      filter_upwards [k.op_apply_eq_inner_rowVec hk2 (X.specVec ha j),
        Lp.coeFn_smul ((X.specMu ha j : ℝ) : ℂ) (X.specVec ha j), X.ae_eq_specRep ha hab j]
        with w h1 h2 h3
      have h1' := h1
      rw [show k.op (X.specVec ha j) = X.resOp ha (X.specVec ha j) from rfl,
        X.resOp_specVec ha j, h2, Pi.smul_apply, smul_eq_mul, h3] at h1'
      exact h1'
    filter_upwards [hj] with w hw
    calc ∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2
        ≤ ∑ j ∈ S, (b * (b - 1) - a * (a - 1)) * ‖⟪X.specVec ha j, k.rowVec w⟫_ℂ‖ ^ 2 := by
          refine Finset.sum_le_sum fun j hjS => ?_
          rw [norm_inner_symm (X.specVec ha j) (k.rowVec w), ← hw j hjS, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (X.specMu_pos ha j), mul_pow,
            ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (X.nu_le_sq ha hab j) (sq_nonneg _)
      _ = (b * (b - 1) - a * (a - 1)) * ∑ j ∈ S, ‖⟪X.specVec ha j, k.rowVec w⟫_ℂ‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (b * (b - 1) - a * (a - 1)) * R.toReal :=
          mul_le_mul_of_nonneg_left ((Orthonormal.sum_inner_products_le (k.rowVec w) hon).trans (hnorm w)) hC
  -- from almost every `w` to every `w`
  have hfc : Continuous fun w => ∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 :=
    continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((X.continuous_specRep ha hab j).norm.pow 2)
  have hg := X.eq_zero_of_ae_eq_zero
    (g := fun w => ((max (∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 -
      (b * (b - 1) - a * (a - 1)) * R.toReal) 0 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((hfc.sub continuous_const).max continuous_const))
    (fun γ w => by simp only [X.specRep_smul ha hab])
    (by
      filter_upwards [hae] with w hw
      show ((max _ 0 : ℝ) : ℂ) = 0
      rw [max_eq_right (sub_nonpos.mpr hw), Complex.ofReal_zero])
  have h0 : ((max (∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 -
      (b * (b - 1) - a * (a - 1)) * R.toReal) 0 : ℝ) : ℂ) = 0 := congrFun hg w
  rw [Complex.ofReal_eq_zero] at h0
  linarith [le_max_left (∑ j ∈ S, X.nu ha (b := b) j * ‖X.specRep ha (b := b) j w‖ ^ 2 -
      (b * (b - 1) - a * (a - 1)) * R.toReal) 0]

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
