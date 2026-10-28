import GaloisForLFunctions.ShallowCauchyPrimeEnergy.ShallowCauchyEnergyBound
import GaloisForLFunctions.RHTower.XiReciprocalSlicePositiveDensity
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensityLong

/-!
# Unconditional implications of the prime-side shallow Cauchy energy bound

From the unconditional prime-side shallow Cauchy energy theorem (`ShallowCauchyEnergyBound`), this
module establishes four unconditional consequences for off-line zeros of `ζ` and `ξ` in `[T, 2T]`:

1. **Normalization by the Riemann–von Mangoldt zero count `N(T, 2T)`:**
   `(1 / log T) · xiShallowCauchyEnergy (1 / log T) T ≤ C_N · N(T, 2T)`.
2. **Critical-scale energy saturation (`h = α / log T`):**
   Uniformly for all `κ₂ / 2 ≤ α ≤ (log T) / 64`,
   `xiShallowCauchyEnergy (α / log T) T ≤ 2 C · T (log T)²` with a constant independent of `α`.
3. **Unconditional anti-clustering and squared-multiplicity control of shallow off-line zeros:**
   For any distinct strict-right `ζ`-zeros `ρ_j` in `[T, 2T]` within `1 / log T` of the critical
   line with exact multiplicities `m_j = ord_{ρ_j}(ζ)`:
   - `Σ_j m_j² ≤ C · T log T`, and
   - `Σ_{|γ_j − γ_k| ≤ K / log T} m_j m_k ≤ (C / 8) (16 + K²) · T log T` for every `K ≥ 0`.
4. **Joint shallow-energy + exponential-deep-tail Ward budget:**
   Combining the uniform shallow energy bound with Selberg's long two-length Barban–Vehov
   exponential near-line density (`exists_selberg_exponential_nearLine_zeroDensity_long`, rate
   `e^{−α/28} / α`) bounds the deep strict-right multiplicity in `[T, 2T]` exponentially in `α`
   while keeping `(α / log T) E_{α / log T} + R_deep = O_α(N(T, 2T))`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

/-! ## Implication 1: Normalization by `Zeta23.Ncount T (2 * T)` -/

/-- Eventual linear comparison `T log T ≤ 8π · N(T, 2T)` from the Riemann–von Mangoldt formula. -/
theorem eventually_T_mul_log_le_eight_pi_mul_Ncount :
    ∀ᶠ T : ℝ in atTop, T * Real.log T ≤ 8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ) := by
  obtain ⟨CR, T₁, hRvM⟩ := Zeta23.riemannVonMangoldt_zeta.main
  filter_upwards [eventually_ge_atTop
    (max (max T₁ (8 * Real.pi * (|CR| + 1))) (2 * Real.pi * Real.exp 5))] with T hT
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTCR : 8 * Real.pi * (|CR| + 1) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTexp : 2 * Real.pi * Real.exp (max 5 5) ≤ T := by
    rw [max_self]
    exact le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hTCR
  obtain ⟨hL5, -, hlogT, -⟩ := density_scale_bounds hTexp
  have hN := le_Ncount_of_large (hRvM T hT₁) hTCR (by linarith) hlogT
  calc T * Real.log T
      ≤ T * (2 * Zeta23.l T) := mul_le_mul_of_nonneg_left hlogT hT0.le
    _ = 8 * Real.pi * (T / (4 * Real.pi) * Zeta23.l T) := by
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp
        norm_num
    _ ≤ 8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ) :=
        mul_le_mul_of_nonneg_left hN (by positivity)

/-- **Normalized shallow Cauchy energy bound at depth `1 / log T`.**
Unconditionally, `(1 / log T) · xiShallowCauchyEnergy (1 / log T) T ≤ C_N · N(T, 2T)` for all
sufficiently large `T`. -/
theorem exists_xiShallowCauchyEnergy_one_div_log_le_mul_Ncount :
    ∃ C_N : ℝ, 0 < C_N ∧ ∀ᶠ T : ℝ in atTop,
      (1 / Real.log T) * xiShallowCauchyEnergy (1 / Real.log T) T ≤
        C_N * (Zeta23.Ncount T (2 * T) : ℝ) := by
  obtain ⟨C, hC, hev⟩ := exists_xiShallowCauchyEnergy_one_div_log_le
  refine ⟨8 * Real.pi * C, by positivity, ?_⟩
  filter_upwards [hev, eventually_T_mul_log_le_eight_pi_mul_Ncount] with T hE hN
  calc (1 / Real.log T) * xiShallowCauchyEnergy (1 / Real.log T) T
      ≤ C * (T * Real.log T) := by
        linarith [hE.2.1, show C * T * Real.log T = C * (T * Real.log T) by ring]
    _ ≤ C * (8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ)) :=
        mul_le_mul_of_nonneg_left hN hC.le
    _ = (8 * Real.pi * C) * (Zeta23.Ncount T (2 * T) : ℝ) := by ring

/-! ## Implication 2: Critical-scale saturation (`h = α / log T`) -/

/-- **Uniform critical-scale shallow Cauchy energy saturation.**
Widening the shallow layer from `1 / log T` to `α / log T` for any `κ₂ / 2 ≤ α ≤ (log T) / 64`
keeps `xiShallowCauchyEnergy (α / log T) T ≤ 2 C · T (log T)²` with a bound completely independent
of `α`. -/
theorem exists_criticalScale_xiShallowCauchyEnergy_saturation :
    ∃ C κ₂ : ℝ, 0 < C ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T : ℝ in atTop,
      ∀ α : ℝ, κ₂ / 2 ≤ α → α ≤ Real.log T / 64 →
        xiShallowCauchyEnergy (α / Real.log T) T ≤ 2 * C * T * (Real.log T) ^ (2 : ℕ) := by
  obtain ⟨C, κ₂, hC, hκ₂, hev⟩ := exists_uniform_xiShallowCauchyEnergy_le
  refine ⟨C, κ₂, hC, hκ₂, ?_⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with T hunif hL1 α hα_lo hα_hi
  have hL0 : 0 < Real.log T := by linarith
  have hα0 : 0 < α := by linarith
  have hh0 : 0 < α / Real.log T := div_pos hα0 hL0
  have hh64 : α / Real.log T ≤ 1 / 64 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  have hb := hunif (α / Real.log T) hh0 hh64
  have h2α : 2 * (α / Real.log T) * Real.log T = 2 * α := by field_simp
  rw [h2α, max_eq_right (by linarith)] at hb
  have hmul := mul_le_mul_of_nonneg_right hb (div_nonneg hL0.le hα0.le)
  have hlhs : (α / Real.log T) * xiShallowCauchyEnergy (α / Real.log T) T * (Real.log T / α) =
      xiShallowCauchyEnergy (α / Real.log T) T := by
    have hLne : Real.log T ≠ 0 := hL0.ne'
    have hαne : α ≠ 0 := hα0.ne'
    field_simp
  have hrhs : C * (2 * α) * (T * Real.log T) * (Real.log T / α) =
      2 * C * T * (Real.log T) ^ (2 : ℕ) := by
    have hαne : α ≠ 0 := hα0.ne'
    field_simp
  linarith

/-! ## Implication 3: Anti-clustering and squared-multiplicity bounds for shallow zeros -/

/-- Squared multiplicities of `h`-shallow modes are bounded by `h · finiteOfflineCauchyEnergy`. -/
theorem sum_sq_multiplicity_le_shift_mul_finiteOfflineCauchyEnergy
    {n : ℕ} {h : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hale : ∀ j, a j ≤ h) :
    (∑ j, (m j : ℝ) ^ (2 : ℕ)) ≤
      h * finiteOfflineCauchyEnergy (fun j => h + a j) gamma m := by
  have hshift : ∀ j, 0 < h + a j := fun j => add_pos hh (ha j)
  have hbase := finiteOfflineCauchyEnergy_ge_two_mul_sum_sq_div (gamma := gamma) m hshift
  have hterm : ∀ j : Fin n,
      (m j : ℝ) ^ (2 : ℕ) / h ≤ 2 * ((m j : ℝ) ^ (2 : ℕ) / (h + a j)) := by
    intro j
    have hden : 0 < h + a j := hshift j
    rw [← mul_div_assoc, div_le_div_iff₀ hh hden]
    have h1 : h + a j ≤ 2 * h := by linarith [hale j]
    have hm := mul_le_mul_of_nonneg_left h1 (sq_nonneg (m j : ℝ))
    linarith [show (m j : ℝ) ^ (2 : ℕ) * (2 * h) = 2 * (m j : ℝ) ^ (2 : ℕ) * h by ring]
  have hdiv_le : (∑ j, (m j : ℝ) ^ (2 : ℕ)) / h ≤
      finiteOfflineCauchyEnergy (fun j => h + a j) gamma m := by
    calc (∑ j, (m j : ℝ) ^ (2 : ℕ)) / h
        = ∑ j, (m j : ℝ) ^ (2 : ℕ) / h := Finset.sum_div _ _ _
      _ ≤ ∑ j, 2 * ((m j : ℝ) ^ (2 : ℕ) / (h + a j)) := Finset.sum_le_sum fun j _ => hterm j
      _ = 2 * ∑ j, (m j : ℝ) ^ (2 : ℕ) / (h + a j) := (Finset.mul_sum _ _ _).symm
      _ ≤ finiteOfflineCauchyEnergy (fun j => h + a j) gamma m := hbase
  rw [div_le_iff₀ hh] at hdiv_le
  linarith [show h * finiteOfflineCauchyEnergy (fun j => h + a j) gamma m =
    finiteOfflineCauchyEnergy (fun j => h + a j) gamma m * h by ring]

/-- Close-pair multiplicity correlation (`|γ_j − γ_k| ≤ K h`) of `h`-shallow modes is bounded by
`((16 + K²) / 8) · h · finiteOfflineCauchyEnergy`. -/
theorem sum_closePairs_le_shift_mul_finiteOfflineCauchyEnergy
    {n : ℕ} {h K : ℝ} (hh : 0 < h)
    {a gamma : Fin n → ℝ} (m : Fin n → ℕ)
    (ha : ∀ j, 0 < a j) (hale : ∀ j, a j ≤ h) :
    (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin n × Fin n => |gamma p.1 - gamma p.2| ≤ K * h),
        (m p.1 : ℝ) * (m p.2 : ℝ)) ≤
      ((16 + K ^ (2 : ℕ)) / 8) * h *
        finiteOfflineCauchyEnergy (fun j => h + a j) gamma m := by
  classical
  let P := (Finset.univ ×ˢ Finset.univ).filter
    (fun p : Fin n × Fin n => |gamma p.1 - gamma p.2| ≤ K * h)
  have hpt : ∀ p ∈ P,
      8 / ((16 + K ^ (2 : ℕ)) * h) ≤
        4 * transverseCauchyKernel (h + a p.1) (h + a p.2) (gamma p.1 - gamma p.2) := by
    intro p hp
    have hdist : |gamma p.1 - gamma p.2| ≤ K * h := (Finset.mem_filter.mp hp).2
    have hs_lo : 2 * h ≤ h + a p.1 + (h + a p.2) := by linarith [ha p.1, ha p.2]
    have hs_hi : h + a p.1 + (h + a p.2) ≤ 4 * h := by linarith [hale p.1, hale p.2]
    have hs_pos : 0 < h + a p.1 + (h + a p.2) := by linarith
    have hsq_s : (h + a p.1 + (h + a p.2)) ^ (2 : ℕ) ≤ 16 * h ^ (2 : ℕ) := by
      calc (h + a p.1 + (h + a p.2)) ^ (2 : ℕ)
          ≤ (4 * h) ^ (2 : ℕ) := pow_le_pow_left₀ hs_pos.le hs_hi 2
        _ = 16 * h ^ (2 : ℕ) := by ring
    have hsq_d : (gamma p.1 - gamma p.2) ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * h ^ (2 : ℕ) := by
      calc (gamma p.1 - gamma p.2) ^ (2 : ℕ)
          = |gamma p.1 - gamma p.2| ^ (2 : ℕ) := (sq_abs _).symm
        _ ≤ (K * h) ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hdist 2
        _ = K ^ (2 : ℕ) * h ^ (2 : ℕ) := by ring
    unfold transverseCauchyKernel
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hden_le : (h + a p.1 + (h + a p.2)) ^ (2 : ℕ) + (gamma p.1 - gamma p.2) ^ (2 : ℕ) ≤
        (16 + K ^ (2 : ℕ)) * h ^ (2 : ℕ) := by
      linarith [show 16 * h ^ (2 : ℕ) + K ^ (2 : ℕ) * h ^ (2 : ℕ) =
        (16 + K ^ (2 : ℕ)) * h ^ (2 : ℕ) by ring]
    have h1 : 8 * ((h + a p.1 + (h + a p.2)) ^ (2 : ℕ) + (gamma p.1 - gamma p.2) ^ (2 : ℕ)) ≤
        8 * ((16 + K ^ (2 : ℕ)) * h ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hden_le (by norm_num)
    have h2 : 4 * (2 * h) * ((16 + K ^ (2 : ℕ)) * h) ≤
        4 * (h + a p.1 + (h + a p.2)) * ((16 + K ^ (2 : ℕ)) * h) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs_lo (by norm_num)) (by positivity)
    linarith [show 8 * ((16 + K ^ (2 : ℕ)) * h ^ (2 : ℕ)) =
      4 * (2 * h) * ((16 + K ^ (2 : ℕ)) * h) by ring]
  have hnn_all : ∀ p : Fin n × Fin n,
      0 ≤ (m p.1 : ℝ) * (m p.2 : ℝ) *
        (4 * transverseCauchyKernel (h + a p.1) (h + a p.2) (gamma p.1 - gamma p.2)) := fun p =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num)
        (transverseCauchyKernel_pos (add_pos hh (ha p.1)) (add_pos hh (ha p.2)) _).le)
  have hsum_le :
      (8 / ((16 + K ^ (2 : ℕ)) * h)) * (∑ p ∈ P, (m p.1 : ℝ) * (m p.2 : ℝ)) ≤
        finiteOfflineCauchyEnergy (fun j => h + a j) gamma m := by
    calc (8 / ((16 + K ^ (2 : ℕ)) * h)) * (∑ p ∈ P, (m p.1 : ℝ) * (m p.2 : ℝ))
        = ∑ p ∈ P, (m p.1 : ℝ) * (m p.2 : ℝ) * (8 / ((16 + K ^ (2 : ℕ)) * h)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ p ∈ P, (m p.1 : ℝ) * (m p.2 : ℝ) *
            (4 * transverseCauchyKernel (h + a p.1) (h + a p.2) (gamma p.1 - gamma p.2)) :=
          Finset.sum_le_sum fun p hp =>
            mul_le_mul_of_nonneg_left (hpt p hp) (by positivity)
      _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)),
            (m p.1 : ℝ) * (m p.2 : ℝ) *
              (4 * transverseCauchyKernel (h + a p.1) (h + a p.2) (gamma p.1 - gamma p.2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => hnn_all p
      _ = finiteOfflineCauchyEnergy (fun j => h + a j) gamma m := by
          unfold finiteOfflineCauchyEnergy
          rw [Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
  have hmul := mul_le_mul_of_nonneg_left hsum_le
    (show 0 ≤ ((16 + K ^ (2 : ℕ)) / 8) * h by positivity)
  have hlhs : ((16 + K ^ (2 : ℕ)) / 8) * h *
      ((8 / ((16 + K ^ (2 : ℕ)) * h)) * (∑ p ∈ P, (m p.1 : ℝ) * (m p.2 : ℝ))) =
        ∑ p ∈ P, (m p.1 : ℝ) * (m p.2 : ℝ) := by
    have hhne : h ≠ 0 := hh.ne'
    have hKne : 16 + K ^ (2 : ℕ) ≠ 0 := by positivity
    field_simp
  linarith

/-- **Unconditional squared-multiplicity and critical-spacing close-pair bounds for shallow
strict-right `ζ`-zeros in `[T, 2T]`.** -/
theorem exists_shallow_zetaZeros_sq_multiplicity_and_closePairs_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (n : ℕ) (ρ : Fin n → ℂ), Function.Injective ρ →
        (∀ j, riemannZeta (ρ j) = 0) →
        (∀ j, 1 / 2 < (ρ j).re) →
        (∀ j, (ρ j).re - 1 / 2 ≤ 1 / Real.log T) →
        (∀ j, T ≤ (ρ j).im) →
        (∀ j, (ρ j).im ≤ 2 * T) →
          (∑ j, ((analyticOrderAt riemannZeta (ρ j)).toNat : ℝ) ^ (2 : ℕ)) ≤
              C * T * Real.log T ∧
          ∀ K : ℝ, 0 ≤ K →
            (∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
                (fun p : Fin n × Fin n => |(ρ p.1).im - (ρ p.2).im| ≤ K / Real.log T),
                ((analyticOrderAt riemannZeta (ρ p.1)).toNat : ℝ) *
                  ((analyticOrderAt riemannZeta (ρ p.2)).toNat : ℝ)) ≤
              (C / 8) * (16 + K ^ (2 : ℕ)) * T * Real.log T := by
  obtain ⟨C, hC, hev⟩ := exists_finiteOfflineCauchyEnergy_zetaZeros_one_div_log_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)]
    with T hE hT4 hL4 n ρ hρ_inj hzeta hre_gt hre_le him_lo him_hi
  have hL0 : 0 < Real.log T := by linarith
  have hh0 : 0 < 1 / Real.log T := div_pos one_pos hL0
  have ha0 : ∀ j : Fin n, 0 < (ρ j).re - 1 / 2 := fun j => sub_pos.mpr (hre_gt j)
  have hE_bd := hE n ρ hρ_inj hzeta hre_gt hre_le him_lo him_hi
  have hscaled : (1 / Real.log T) * finiteOfflineCauchyEnergy
      (fun j => 1 / Real.log T + ((ρ j).re - 1 / 2))
      (fun j => (ρ j).im)
      (fun j => (analyticOrderAt riemannZeta (ρ j)).toNat) ≤ C * T * Real.log T := by
    have hm := mul_le_mul_of_nonneg_left hE_bd hh0.le
    have hrhs : (1 / Real.log T) * (C * T * (Real.log T) ^ (2 : ℕ)) = C * T * Real.log T := by
      have hLne : Real.log T ≠ 0 := hL0.ne'
      field_simp
    linarith
  refine ⟨(sum_sq_multiplicity_le_shift_mul_finiteOfflineCauchyEnergy hh0 _ ha0 hre_le).trans
    hscaled, fun K _ => ?_⟩
  have hfilt : (Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin n × Fin n => |(ρ p.1).im - (ρ p.2).im| ≤ K / Real.log T) =
    (Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin n × Fin n => |(ρ p.1).im - (ρ p.2).im| ≤ K * (1 / Real.log T)) := by
    refine Finset.filter_congr fun p _ => ?_
    rw [mul_one_div]
  rw [hfilt]
  have hcp := sum_closePairs_le_shift_mul_finiteOfflineCauchyEnergy (K := K) hh0
    (a := fun j => (ρ j).re - 1 / 2) (gamma := fun j => (ρ j).im)
    (fun j => (analyticOrderAt riemannZeta (ρ j)).toNat) ha0 hre_le
  have hm := mul_le_mul_of_nonneg_left hscaled
    (show 0 ≤ (16 + K ^ (2 : ℕ)) / 8 by positivity)
  linarith [show ((16 + K ^ (2 : ℕ)) / 8) * (1 / Real.log T) *
      finiteOfflineCauchyEnergy (fun j => 1 / Real.log T + ((ρ j).re - 1 / 2))
        (fun j => (ρ j).im) (fun j => (analyticOrderAt riemannZeta (ρ j)).toNat) =
      ((16 + K ^ (2 : ℕ)) / 8) * ((1 / Real.log T) *
        finiteOfflineCauchyEnergy (fun j => 1 / Real.log T + ((ρ j).re - 1 / 2))
          (fun j => (ρ j).im) (fun j => (analyticOrderAt riemannZeta (ρ j)).toNat)) by ring,
    show ((16 + K ^ (2 : ℕ)) / 8) * (C * T * Real.log T) =
      (C / 8) * (16 + K ^ (2 : ℕ)) * T * Real.log T by ring]

/-! ## Implication 4: Joint shallow-energy + exponential-deep-tail Ward budget -/

/-- Any finite set of `XiZeroCopy` within unit ordinate distance of `t` has cardinality at most
`16 (xiLineTwoLogDerivConstant + log(|t| + 4))`. -/
theorem card_xiZeroCopy_unitStrip_le (t : ℝ) (F : Finset XiZeroCopy)
    (hF : ∀ c ∈ F, |(c.1 : ℂ).im - t| ≤ 1) :
    (F.card : ℝ) ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by
  have hterm : ∀ c ∈ F, (1 / 2 : ℝ) ≤ lorentzMassTerm t c := by
    intro c hc
    have hsq : (t - (c.1 : ℂ).im) ^ (2 : ℕ) ≤ 1 := by
      have habs : (t - (c.1 : ℂ).im) ^ (2 : ℕ) = |(c.1 : ℂ).im - t| ^ (2 : ℕ) := by
        rw [sq_abs]; ring
      rw [habs]
      exact pow_le_one₀ (abs_nonneg _) (hF c hc)
    unfold lorentzMassTerm
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hsum : (F.card : ℝ) * (1 / 2 : ℝ) ≤ lorentzMass t := by
    calc (F.card : ℝ) * (1 / 2 : ℝ)
        = ∑ _c ∈ F, (1 / 2 : ℝ) := by simp
      _ ≤ ∑ c ∈ F, lorentzMassTerm t c := Finset.sum_le_sum hterm
      _ ≤ lorentzMass t :=
          (summable_lorentzMassTerm t).sum_le_tsum F fun _ _ => by
            unfold lorentzMassTerm; positivity
  linarith [lorentzMass_le_log t]

/-- **Unconditional exponential deep-layer multiplicity bound on `[T, 2T]`.**
By Selberg's long two-length Barban–Vehov near-line density bound (`e^{−a/14}`) and the Lorentzian
unit-strip bound at the endpoints `T` and `2T`, all strict-right `ξ`-zero copies in `[T, 2T]` at
horizontal depth `> α / log T` satisfy

`(# xiDeepRightUpperWindow (α / log T) T) ≤ C_deep · (T log T · e^{−α/28} / α + (log T)²)`

uniformly for `4 ≤ α ≤ (log T) / 64`. -/
theorem exists_card_xiDeepRightUpperWindow_exponential_le :
    ∃ C_deep : ℝ, 0 < C_deep ∧ ∀ᶠ T : ℝ in atTop,
      ∀ α : ℝ, 4 ≤ α → α ≤ Real.log T / 64 →
        ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
          C_deep * (T * Real.log T * Real.exp (-(α / 28)) / α + (Real.log T) ^ (2 : ℕ)) := by
  classical
  obtain ⟨A, K, hA, hK, hdens⟩ := exists_selberg_exponential_nearLine_zeroDensity_long
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hdens
  refine ⟨A / Real.pi + 2 * K / Real.pi + 64, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max (U₀ / 4) 20),
    Real.tendsto_log_atTop.eventually_ge_atTop (|xiLineTwoLogDerivConstant| + 256)]
    with T hTbig hLbig α hα4 hα64
  have hT20 : 20 ≤ T := (le_max_right _ _).trans hTbig
  have hT0 : 0 < T := by linarith
  have hTU : U₀ ≤ 4 * T := by
    have := (le_max_left _ _).trans hTbig; linarith
  have hL_T_pos : 0 < Real.log T := by linarith [abs_nonneg xiLineTwoLogDerivConstant]
  have hL_T_1 : 1 ≤ Real.log T := by linarith [abs_nonneg xiLineTwoLogDerivConstant]
  obtain ⟨T₁', hT₁', T₂', hT₂', hcount⟩ := hU₀ (4 * T) hTU
  have hT₁_lo : T < T₁' := by have := hT₁'.1; linarith
  have hT₁_hi : T₁' < T + 1 := by have := hT₁'.2; linarith
  have hT₂_lo : 2 * T - 1 < T₂' := by have := hT₂'.1; linarith
  have hT₂_hi : T₂' < 2 * T := by have := hT₂'.2; linarith
  have hT12 : T₁' < T₂' := by linarith
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset (by linarith) hT12
  let L := Real.log (4 * T)
  have hL_ge : Real.log T ≤ L := Real.log_le_log hT0 (by linarith)
  have hL_le : L ≤ 2 * Real.log T := by
    have hsq : 4 * T ≤ T ^ (2 : ℕ) := by
      have : 0 ≤ T * (T - 4) := mul_nonneg hT0.le (by linarith)
      linarith [show T ^ (2 : ℕ) - 4 * T = T * (T - 4) by ring]
    have h1 := Real.log_le_log (by positivity) hsq
    rw [Real.log_pow] at h1
    simpa [L] using h1
  have hL_pos : 0 < L := hL_T_pos.trans_le hL_ge
  let a := α * L / (2 * Real.log T)
  have ha_ge_half : α / 2 ≤ a := by
    have hdiv1 : 1 ≤ L / Real.log T := (one_le_div hL_T_pos).mpr hL_ge
    have hm := mul_le_mul_of_nonneg_left hdiv1 (show 0 ≤ α / 2 by linarith)
    linarith [show (α / 2) * (L / Real.log T) = a by dsimp [a]; ring]
  have ha1 : 1 ≤ a := by linarith
  have haL : 2 * a + 2 ≤ L := by
    have h2a : 2 * a = (α / Real.log T) * L := by
      dsimp [a]
      have hLne : Real.log T ≠ 0 := hL_T_pos.ne'
      field_simp
    have h64 : (α / Real.log T) * L ≤ (1 / 64) * L := by
      refine mul_le_mul_of_nonneg_right ?_ hL_pos.le
      rw [div_le_div_iff₀ hL_T_pos (by norm_num)]
      linarith
    have hL256 : 256 ≤ L := by linarith [abs_nonneg xiLineTwoLogDerivConstant]
    linarith
  have hshift_eq : 2 * a / L = α / Real.log T := by
    dsimp [a]
    have hLne : L ≠ 0 := hL_pos.ne'
    have hLTne : Real.log T ≠ 0 := hL_T_pos.ne'
    field_simp
  have hmid_selberg := hcount a ha1 haL Z hZ
  rw [hshift_eq] at hmid_selberg
  let Z_deep := Z.filter (fun w => 1 / 2 + α / Real.log T ≤ w.re)
  have hS_mid_le :
      (∑ w ∈ Z_deep, ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
        (A / Real.pi) * (T * Real.log T * Real.exp (-(α / 28)) / α) +
          (2 * K / Real.pi) * (Real.log T) ^ (2 : ℕ) := by
    have ha_div_L : a / L = α / (2 * Real.log T) := by
      dsimp [a]
      have hLne : L ≠ 0 := hL_pos.ne'
      field_simp
    rw [ha_div_L] at hmid_selberg
    have hexp_le : Real.exp (-(a / 14)) ≤ Real.exp (-(α / 28)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hrhs_le : (T₂' - T₁') * (A * Real.exp (-(a / 14))) + K * L ≤
        A * T * Real.exp (-(α / 28)) + 2 * K * Real.log T := by
      have h1 : (T₂' - T₁') * (A * Real.exp (-(a / 14))) ≤
          T * (A * Real.exp (-(α / 28))) :=
        mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hexp_le hA.le)
          (by positivity) hT0.le
      have h2 : K * L ≤ K * (2 * Real.log T) := mul_le_mul_of_nonneg_left hL_le hK
      linarith [show T * (A * Real.exp (-(α / 28))) = A * T * Real.exp (-(α / 28)) by ring]
    have hcomb := hmid_selberg.trans hrhs_le
    have hfac : 0 ≤ Real.log T / (Real.pi * α) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcomb hfac
    have hlhs : 2 * Real.pi * (α / (2 * Real.log T) *
        ∑ w ∈ Z_deep, ((analyticOrderAt riemannZeta w).toNat : ℝ)) *
          (Real.log T / (Real.pi * α)) =
        ∑ w ∈ Z_deep, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      have hαne : α ≠ 0 := by linarith
      have hLTne : Real.log T ≠ 0 := hL_T_pos.ne'
      field_simp
    have hrhs_id : (A * T * Real.exp (-(α / 28)) + 2 * K * Real.log T) *
          (Real.log T / (Real.pi * α)) =
        (A / Real.pi) * (T * Real.log T * Real.exp (-(α / 28)) / α) +
          (2 * K / Real.pi) * ((Real.log T) ^ (2 : ℕ) / α) := by
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      have hαne : α ≠ 0 := by linarith
      field_simp
    have hK_drop : (2 * K / Real.pi) * ((Real.log T) ^ (2 : ℕ) / α) ≤
        (2 * K / Real.pi) * (Real.log T) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left (div_le_self (sq_nonneg _) (by linarith)) (by positivity)
    linarith
  let D := (xiDeepRightUpperWindow (α / Real.log T) T).map xiRightUpperZeroCopyEmbedding
  let D_bot := D.filter (fun c => (c.1 : ℂ).im ≤ T₁')
  let D_mid := D.filter (fun c => T₁' < (c.1 : ℂ).im ∧ (c.1 : ℂ).im < T₂')
  let D_top := D.filter (fun c => T₂' ≤ (c.1 : ℂ).im)
  have hD_sub : D ⊆ (D_bot ∪ D_mid) ∪ D_top := by
    intro c hc
    by_cases h1 : (c.1 : ℂ).im ≤ T₁'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc, h1⟩))
    · by_cases h2 : T₂' ≤ (c.1 : ℂ).im
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc, h2⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hc, lt_of_not_ge h1, lt_of_not_ge h2⟩))
  have hlog_end : xiLineTwoLogDerivConstant + Real.log (|2 * T| + 4) ≤ 2 * Real.log T := by
    rw [abs_of_pos (by positivity)]
    have h2T4 : Real.log (2 * T + 4) ≤ Real.log (3 * T) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3T : Real.log (3 * T) = Real.log 3 + Real.log T :=
      Real.log_mul (by norm_num) hT0.ne'
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hCabs : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
    linarith
  have hbot_le : (D_bot.card : ℝ) ≤ 32 * Real.log T := by
    have hc := card_xiZeroCopy_unitStrip_le T D_bot fun c hc => by
      obtain ⟨hcD, hhi⟩ := Finset.mem_filter.mp hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hcD
      have hp_mem := (mem_xiDeepRightUpperWindow hT0).mp hp
      rw [im_xiRightUpperZeroCopyEmbedding] at hhi ⊢
      rw [abs_le]
      exact ⟨by linarith [hp_mem.1], by linarith⟩
    have hlogT4 : Real.log (|T| + 4) ≤ Real.log (|2 * T| + 4) := by
      rw [abs_of_pos hT0, abs_of_pos (by positivity)]
      exact Real.log_le_log (by linarith) (by linarith)
    linarith
  have htop_le : (D_top.card : ℝ) ≤ 32 * Real.log T := by
    have hc := card_xiZeroCopy_unitStrip_le (2 * T) D_top fun c hc => by
      obtain ⟨hcD, hlo⟩ := Finset.mem_filter.mp hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hcD
      have hp_mem := (mem_xiDeepRightUpperWindow hT0).mp hp
      rw [im_xiRightUpperZeroCopyEmbedding] at hlo ⊢
      rw [abs_le]
      exact ⟨by linarith, by linarith [hp_mem.2.1]⟩
    linarith
  have hmid_card : (D_mid.card : ℝ) ≤
      ∑ w ∈ Z_deep, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    let fibZ : ℂ → Finset XiZeroCopy := fun w =>
      if hw : xi w = 0 then xiZeroCopyFiber ⟨w, mem_xi_divisor_support_of_eq_zero hw⟩ else ∅
    have hsub_fib : D_mid ⊆ Z_deep.biUnion fibZ := by
      intro c hc
      obtain ⟨hcD, hlo, hhi⟩ := Finset.mem_filter.mp hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hcD
      have hp_mem := (mem_xiDeepRightUpperWindow hT0).mp hp
      let w : ℂ := ((xiRightUpperZeroCopyEmbedding p).1 : ℂ)
      have hw_nontriv := isNontrivialZero_xiZeroCopy (xiRightUpperZeroCopyEmbedding p)
      have hw_re_gt : 1 / 2 + α / Real.log T ≤ w.re := by
        have hre := xiRightCenteredZero_re p.1
        have := hp_mem.2.2
        change 1 / 2 + α / Real.log T ≤ (p.1.1.1 : ℂ).re
        linarith
      have hw_Z : w ∈ Z_deep := by
        refine Finset.mem_filter.mpr ⟨(hZ w).mpr ⟨?_, hw_nontriv.1⟩, hw_re_gt⟩
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · rw [uIcc_of_le (by norm_num)]
          exact ⟨by linarith [div_pos (by linarith : (0 : ℝ) < α) hL_T_pos],
            by linarith [hw_nontriv.2.2]⟩
        · rw [uIcc_of_le hT12.le]
          exact ⟨hlo.le, hhi.le⟩
      have hw_xi : xi w = 0 := xi_eq_zero_of_mem_divisor_support (xiRightUpperZeroCopyEmbedding p).1
      refine Finset.mem_biUnion.mpr ⟨w, hw_Z, ?_⟩
      dsimp [fibZ]
      rw [dif_pos hw_xi, mem_xiZeroCopyFiber]
    have hcard_nat : D_mid.card ≤ ∑ w ∈ Z_deep, (analyticOrderAt riemannZeta w).toNat := by
      calc D_mid.card
          ≤ (Z_deep.biUnion fibZ).card := Finset.card_le_card hsub_fib
        _ ≤ ∑ w ∈ Z_deep, (fibZ w).card := Finset.card_biUnion_le
        _ ≤ ∑ w ∈ Z_deep, (analyticOrderAt riemannZeta w).toNat := by
            refine Finset.sum_le_sum fun w hw => ?_
            obtain ⟨hwZ, hw_re⟩ := Finset.mem_filter.mp hw
            obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
            have hre_lt_one : w.re < 1 := by
              by_contra hge
              exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hw0
            have hre_pos : 0 < w.re := by
              linarith [div_pos (by linarith : (0 : ℝ) < α) hL_T_pos]
            have hw_xi : xi w = 0 :=
              (xi_zero_iff_zeta_zero_of_mem_strip hre_pos hre_lt_one).mpr hw0
            dsimp [fibZ]
            rw [dif_pos hw_xi, card_xiZeroCopyFiber_eq_order_toNat,
              xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre_pos, hre_lt_one⟩]
    exact_mod_cast hcard_nat
  have hD_card_le : ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
      (D_bot.card : ℝ) + (D_mid.card : ℝ) + (D_top.card : ℝ) := by
    have hmap : (xiDeepRightUpperWindow (α / Real.log T) T).card = D.card :=
      (Finset.card_map _).symm
    have hunion : D.card ≤ D_bot.card + D_mid.card + D_top.card := by
      calc D.card ≤ ((D_bot ∪ D_mid) ∪ D_top).card := Finset.card_le_card hD_sub
        _ ≤ (D_bot ∪ D_mid).card + D_top.card := Finset.card_union_le _ _
        _ ≤ D_bot.card + D_mid.card + D_top.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    rw [hmap]
    exact_mod_cast hunion
  have h64_sq : 64 * Real.log T ≤ 64 * (Real.log T) ^ (2 : ℕ) := by
    have hsq : Real.log T ≤ (Real.log T) ^ (2 : ℕ) := by
      calc Real.log T = Real.log T * 1 := (mul_one _).symm
        _ ≤ Real.log T * Real.log T := mul_le_mul_of_nonneg_left hL_T_1 hL_T_pos.le
        _ = (Real.log T) ^ (2 : ℕ) := (sq _).symm
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  let X := T * Real.log T * Real.exp (-(α / 28)) / α
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hp1 : 0 ≤ (A / Real.pi) * (Real.log T) ^ (2 : ℕ) := by positivity
  have hp2 : 0 ≤ (2 * K / Real.pi + 64) * X := by positivity
  have hexpand :
      (A / Real.pi + 2 * K / Real.pi + 64) * (X + (Real.log T) ^ (2 : ℕ)) =
        (A / Real.pi) * X + (A / Real.pi) * (Real.log T) ^ (2 : ℕ) +
          (2 * K / Real.pi) * (Real.log T) ^ (2 : ℕ) +
          64 * (Real.log T) ^ (2 : ℕ) + (2 * K / Real.pi + 64) * X := by ring
  linarith [hD_card_le, hbot_le, htop_le, hmid_card.trans hS_mid_le, h64_sq, hexpand]

/-- **Unconditional joint shallow-energy and exponential-deep-tail Ward budget on `[T, 2T]`.**
Simultaneously for all `4 ≤ α ≤ (log T) / 64`:
1. Exact strict-right census split `R = R_shallow(α) + R_deep(α)`,
2. Diagonal shallow count bound `R_shallow(α) ≤ (α / log T) · E_{α / log T}`,
3. Prime-side shallow energy bound `(α / log T) · E_{α / log T} ≤ C_sh · max(κ₂, 2α) · N(T, 2T)`,
4. Exponential deep-tail bound `R_deep(α) ≤ C_deep · (T log T · e^{−α/28} / α + (log T)²)`. -/
theorem exists_shallowCauchyEnergy_and_exponential_deepWindow_le :
    ∃ C_sh C_deep κ₂ : ℝ, 0 < C_sh ∧ 0 < C_deep ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T : ℝ in atTop,
      ∀ α : ℝ, 4 ≤ α → α ≤ Real.log T / 64 →
        (xiRightUpperWindow T).card =
          (xiShallowRightUpperWindow (α / Real.log T) T).card +
            (xiDeepRightUpperWindow (α / Real.log T) T).card ∧
        ((xiShallowRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
          (α / Real.log T) * xiShallowCauchyEnergy (α / Real.log T) T ∧
        (α / Real.log T) * xiShallowCauchyEnergy (α / Real.log T) T ≤
          C_sh * max κ₂ (2 * α) * (Zeta23.Ncount T (2 * T) : ℝ) ∧
        ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
          C_deep * (T * Real.log T * Real.exp (-(α / 28)) / α + (Real.log T) ^ (2 : ℕ)) := by
  obtain ⟨C₀, κ₂, hC₀, hκ₂, hev_sh⟩ := exists_uniform_xiShallowCauchyEnergy_le
  obtain ⟨C_deep, hCd, hev_dp⟩ := exists_card_xiDeepRightUpperWindow_exponential_le
  refine ⟨8 * Real.pi * C₀, C_deep, κ₂, by positivity, hCd, hκ₂, ?_⟩
  filter_upwards [hev_sh, hev_dp, eventually_T_mul_log_le_eight_pi_mul_Ncount,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with T hsh hdp hN hL1 α hα4 hα64
  have hL0 : 0 < Real.log T := by linarith
  have hh0 : 0 < α / Real.log T := div_pos (by linarith) hL0
  have hh64 : α / Real.log T ≤ 1 / 64 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    linarith
  refine ⟨card_xiRightUpperWindow_eq_shallow_add_deep _ _,
    card_xiShallowRightUpperWindow_le_shift_mul_energy hh0 T, ?_, hdp α hα4 hα64⟩
  have hb := hsh (α / Real.log T) hh0 hh64
  have h2α : 2 * (α / Real.log T) * Real.log T = 2 * α := by
    have hLne : Real.log T ≠ 0 := hL0.ne'
    field_simp
  rw [h2α] at hb
  calc (α / Real.log T) * xiShallowCauchyEnergy (α / Real.log T) T
      ≤ C₀ * max κ₂ (2 * α) * (T * Real.log T) := hb
    _ ≤ C₀ * max κ₂ (2 * α) * (8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ)) :=
        mul_le_mul_of_nonneg_left hN
          (mul_nonneg hC₀.le (le_trans (by linarith) (le_max_left _ _)))
    _ = (8 * Real.pi * C₀) * max κ₂ (2 * α) * (Zeta23.Ncount T (2 * T) : ℝ) := by ring

/-- **Arbitrarily small deep fraction with `O(N(T, 2T))` shallow Ward energy.**
For every `ε > 0`, there exist a critical-scale depth multiplier `α ≥ 4` and a constant `B > 0`
such that eventually for large `T`:
1. `(# xiDeepRightUpperWindow (α / log T) T) ≤ ε · N(T, 2T)`,
2. `(α / log T) · xiShallowCauchyEnergy (α / log T) T + (# xiDeepRightUpperWindow (α / log T) T) ≤ B · N(T, 2T)`,
3. `xiShallowCauchyEnergy (α / log T) T ≤ B · T (log T)²`. -/
theorem exists_arbitrary_deepFraction_with_linear_shallowEnergy_budget :
    ∀ ε > 0, ∃ α B : ℝ, 4 ≤ α ∧ 0 < B ∧ ∀ᶠ T : ℝ in atTop,
      ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
          ε * (Zeta23.Ncount T (2 * T) : ℝ) ∧
      (α / Real.log T) * xiShallowCauchyEnergy (α / Real.log T) T +
          ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
        B * (Zeta23.Ncount T (2 * T) : ℝ) ∧
      xiShallowCauchyEnergy (α / Real.log T) T ≤ B * T * (Real.log T) ^ (2 : ℕ) := by
  intro ε hε
  obtain ⟨C_sh, C_deep, κ₂, hCsh, hCd, hκ₂, hev_joint⟩ :=
    exists_shallowCauchyEnergy_and_exponential_deepWindow_le
  obtain ⟨C_sat, κ₂', hCsat, hκ₂', hev_sat⟩ :=
    exists_criticalScale_xiShallowCauchyEnergy_saturation
  let α := max (max (κ₂ / 2) (κ₂' / 2)) (28 * (16 * Real.pi * C_deep / ε + 1))
  have hα_ge_κ : κ₂ / 2 ≤ α := le_trans (le_max_left _ _) (le_max_left _ _)
  have hα_ge_κ' : κ₂' / 2 ≤ α := le_trans (le_max_right _ _) (le_max_left _ _)
  have hα_ge_eps : 28 * (16 * Real.pi * C_deep / ε + 1) ≤ α := le_max_right _ _
  have hα4 : 4 ≤ α := by linarith
  have hexp_small : 8 * Real.pi * C_deep * Real.exp (-(α / 28)) / α ≤ ε / 2 := by
    have hexp_le : Real.exp (-(α / 28)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hα_lb : 16 * Real.pi * C_deep / ε ≤ α := by
      have : 0 < 16 * Real.pi * C_deep / ε := by positivity
      linarith
    rw [div_le_iff₀ (by linarith)]
    calc 8 * Real.pi * C_deep * Real.exp (-(α / 28))
        ≤ 8 * Real.pi * C_deep * 1 := mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = (ε / 2) * (16 * Real.pi * C_deep / ε) := by
          have hεne : ε ≠ 0 := hε.ne'
          field_simp
          norm_num
      _ ≤ (ε / 2) * α := mul_le_mul_of_nonneg_left hα_lb (by positivity)
  have hlog_sub : ∀ᶠ T : ℝ in atTop,
      8 * Real.pi * C_deep * Real.log T ≤ (ε / 2) * T := by
    have h1 := Real.isLittleO_log_id_atTop.bound
      (show (0 : ℝ) < (ε / 2) / (8 * Real.pi * C_deep) by positivity)
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with T hT hT1
    have hT0 : 0 < T := by linarith
    have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    simp only [Real.norm_eq_abs, id] at hT
    rw [abs_of_nonneg hL0, abs_of_nonneg hT0.le] at hT
    have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ 8 * Real.pi * C_deep by positivity)
    have hid : 8 * Real.pi * C_deep * ((ε / 2) / (8 * Real.pi * C_deep) * T) = (ε / 2) * T := by
      have hne : 8 * Real.pi * C_deep ≠ 0 := by positivity
      field_simp
    linarith
  refine ⟨α, max (C_sh * (2 * α) + ε) (2 * C_sat), hα4, by positivity, ?_⟩
  filter_upwards [hev_joint, hev_sat, eventually_T_mul_log_le_eight_pi_mul_Ncount,
    hlog_sub, Real.tendsto_log_atTop.eventually_ge_atTop (64 * α),
    eventually_ge_atTop (4 : ℝ)]
    with T hjoint hsat hN hlog_T hL64 hT4
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hα64 : α ≤ Real.log T / 64 := by linarith
  obtain ⟨-, -, hsh_bd, hdp_bd⟩ := hjoint α hα4 hα64
  have hmax_α : max κ₂ (2 * α) = 2 * α := max_eq_right (by linarith)
  rw [hmax_α] at hsh_bd
  have hdp_eps : ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ) ≤
      ε * (Zeta23.Ncount T (2 * T) : ℝ) := by
    have hterm1 : C_deep * (T * Real.log T * Real.exp (-(α / 28)) / α) ≤
        (ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ) := by
      calc C_deep * (T * Real.log T * Real.exp (-(α / 28)) / α)
          = (C_deep * Real.exp (-(α / 28)) / α) * (T * Real.log T) := by ring
        _ ≤ (C_deep * Real.exp (-(α / 28)) / α) *
              (8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ)) :=
            mul_le_mul_of_nonneg_left hN (by positivity)
        _ = (8 * Real.pi * C_deep * Real.exp (-(α / 28)) / α) *
              (Zeta23.Ncount T (2 * T) : ℝ) := by ring
        _ ≤ (ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ) :=
            mul_le_mul_of_nonneg_right hexp_small (Nat.cast_nonneg _)
    have hterm2 : C_deep * (Real.log T) ^ (2 : ℕ) ≤
        (ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ) := by
      have h1 : 8 * Real.pi * C_deep * (Real.log T) ^ (2 : ℕ) ≤
          (ε / 2) * (T * Real.log T) := by
        have hm := mul_le_mul_of_nonneg_right hlog_T hL0.le
        linarith [show 8 * Real.pi * C_deep * Real.log T * Real.log T =
            8 * Real.pi * C_deep * (Real.log T) ^ (2 : ℕ) by ring,
          show (ε / 2) * T * Real.log T = (ε / 2) * (T * Real.log T) by ring]
      have h2 : (ε / 2) * (T * Real.log T) ≤
          (ε / 2) * (8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ)) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      have h3 := (h1.trans h2)
      have hdiv := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 1 / (8 * Real.pi) by positivity)
      have hl : (1 / (8 * Real.pi)) * (8 * Real.pi * C_deep * (Real.log T) ^ (2 : ℕ)) =
          C_deep * (Real.log T) ^ (2 : ℕ) := by
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp
      have hr : (1 / (8 * Real.pi)) * ((ε / 2) * (8 * Real.pi * (Zeta23.Ncount T (2 * T) : ℝ))) =
          (ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ) := by
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp
      linarith
    linarith [show C_deep * (T * Real.log T * Real.exp (-(α / 28)) / α + (Real.log T) ^ (2 : ℕ)) =
      C_deep * (T * Real.log T * Real.exp (-(α / 28)) / α) +
        C_deep * (Real.log T) ^ (2 : ℕ) by ring]
  have hB1 : C_sh * (2 * α) + ε ≤ max (C_sh * (2 * α) + ε) (2 * C_sat) := le_max_left _ _
  have hB2 : 2 * C_sat ≤ max (C_sh * (2 * α) + ε) (2 * C_sat) := le_max_right _ _
  refine ⟨hdp_eps, ?_, ?_⟩
  · calc (α / Real.log T) * xiShallowCauchyEnergy (α / Real.log T) T +
          ((xiDeepRightUpperWindow (α / Real.log T) T).card : ℝ)
        ≤ (C_sh * (2 * α) + ε) * (Zeta23.Ncount T (2 * T) : ℝ) := by linarith
      _ ≤ max (C_sh * (2 * α) + ε) (2 * C_sat) * (Zeta23.Ncount T (2 * T) : ℝ) :=
          mul_le_mul_of_nonneg_right hB1 (Nat.cast_nonneg _)
  · calc xiShallowCauchyEnergy (α / Real.log T) T
        ≤ 2 * C_sat * T * (Real.log T) ^ (2 : ℕ) := hsat α hα_ge_κ' hα64
      _ ≤ max (C_sh * (2 * α) + ε) (2 * C_sat) * T * (Real.log T) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hB2 hT0.le) (sq_nonneg _)

end RHTower

end
