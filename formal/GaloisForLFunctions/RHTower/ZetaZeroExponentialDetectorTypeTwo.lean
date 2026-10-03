import GaloisForLFunctions.RHTower.ZetaZeroExponentialDetectorDichotomy
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalErrorMomentPolylog
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Counting Type II zeros with the critical fourth moment

Let `W ⊆ [T, 2T]` be `1`-separated and suppose `∫_{-L}^{L} |ζ(1/2 + i(γ + y))| dy ≥ V` for every
`γ ∈ W`, with `0 ≤ L ≤ T`.  Then

`#W · V⁴ ≤ (2L)³ (2L + 1) ∫_{-3T}^{3T} |ζ(1/2 + iu)|⁴ du`.

Mechanism: Cauchy–Schwarz twice gives `(∫_I g)⁴ ≤ |I|³ ∫_I g⁴` on each window `I = [γ - L, γ + L]`;
a point lies in at most `2L + 1` windows, because a `1`-separated set in an interval of length `ℓ`
has at most `ℓ + 1` points (`card_le_of_separated_subset_Icc`); every window lies in `[-3T, 3T]`.
With the critical fourth moment `∫_{-N}^{N} |ζ|⁴ ≪ N (log N)⁴` this gives
`#W ≪ L⁴ T (log T)⁴ V^{-4}` (`exists_card_typeTwo_le`).
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set

/-- **A `1`-separated set in an interval of length `ℓ` has at most `ℓ + 1` points.** -/
theorem card_le_of_separated_subset_Icc {S : Finset ℝ} {a ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hS : ∀ s ∈ S, a ≤ s ∧ s ≤ a + ℓ) (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 1 ≤ |s - s'|) :
    (S.card : ℝ) ≤ ℓ + 1 := by
  classical
  have hmaps : ∀ s ∈ S, ⌊s - a⌋₊ ∈ Finset.range (⌊ℓ⌋₊ + 1) := by
    intro s hs
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (by linarith [(hS s hs).2])
  have hinj : Set.InjOn (fun s => ⌊s - a⌋₊) S := by
    intro s hs s' hs' heq
    by_contra hne
    have h1 := hsep s hs s' hs' hne
    have hs0 : 0 ≤ s - a := by linarith [(hS s hs).1]
    have hs0' : 0 ≤ s' - a := by linarith [(hS s' hs').1]
    have ha := Nat.floor_le hs0
    have hb := Nat.lt_floor_add_one (s - a)
    have ha' := Nat.floor_le hs0'
    have hb' := Nat.lt_floor_add_one (s' - a)
    simp only at heq
    rw [heq] at ha hb
    have : |s - s'| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  have hfl : (⌊ℓ⌋₊ : ℝ) ≤ ℓ := Nat.floor_le hℓ
  have : (S.card : ℝ) ≤ (⌊ℓ⌋₊ + 1 : ℕ) := by exact_mod_cast hcard
  push_cast at this
  linarith

/-- **Hölder on an interval:** `(∫_a^b g)⁴ ≤ (b - a)³ ∫_a^b g⁴` for continuous `g`. -/
theorem intervalIntegral_pow_four_le {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ 4 ≤ (b - a) ^ 3 * ∫ x in a..b, g x ^ 4 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hconv : ∀ f : ℝ → ℝ, (∫ x in a..b, f x) = ∫ x, f x ∂μ := fun f => by
    rw [intervalIntegral.integral_of_le hab]
  have hint : ∀ f : ℝ → ℝ, Continuous f → Integrable f μ := fun f hf =>
    (hf.continuousOn.integrableOn_Icc (μ := volume)).mono_set Set.Ioc_subset_Icc_self
  have hlen : ∫ _x : ℝ, (1 : ℝ) ^ 2 ∂μ = b - a := by simp [μ, hab]
  have hcs1 := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := μ) (f := g)
    (g := fun _ => (1 : ℝ)) hg.aestronglyMeasurable aestronglyMeasurable_const
    (hint _ (hg.pow 2)) (hint _ continuous_const)
  have hcs2 := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := μ) (f := fun x => g x ^ 2)
    (g := fun _ => (1 : ℝ)) (hg.pow 2).aestronglyMeasurable aestronglyMeasurable_const
    (hint _ ((hg.pow 2).pow 2)) (hint _ continuous_const)
  simp only [mul_one] at hcs1 hcs2
  rw [hlen] at hcs1 hcs2
  have hpow4 : (fun x => (g x ^ 2) ^ 2) = fun x => g x ^ 4 := by funext x; ring
  rw [hpow4] at hcs2
  rw [hconv, hconv]
  have hI2 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hba : 0 ≤ b - a := by linarith
  calc (∫ x, g x ∂μ) ^ 4 = ((∫ x, g x ∂μ) ^ 2) ^ 2 := by ring
    _ ≤ ((∫ x, g x ^ 2 ∂μ) * (b - a)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hcs1 2
    _ = (∫ x, g x ^ 2 ∂μ) ^ 2 * (b - a) ^ 2 := by ring
    _ ≤ ((∫ x, g x ^ 4 ∂μ) * (b - a)) * (b - a) ^ 2 :=
        mul_le_mul_of_nonneg_right hcs2 (sq_nonneg _)
    _ = (b - a) ^ 3 * ∫ x, g x ^ 4 ∂μ := by ring

theorem continuous_norm_riemannZeta_half :
    Continuous fun u : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ := by
  have h := continuous_norm_riemannZeta_half_shift 0
  simpa using h

/-- **The Type II count.** -/
theorem card_mul_pow_four_le_typeTwo {W : Finset ℝ} {T L V : ℝ} (hL : 0 ≤ L) (hLT : L ≤ T)
    (hW : ∀ γ ∈ W, T ≤ γ ∧ γ ≤ 2 * T) (hsep : ∀ γ ∈ W, ∀ γ' ∈ W, γ ≠ γ' → 1 ≤ |γ - γ'|)
    (hV : 0 ≤ V)
    (hbig : ∀ γ ∈ W, V ≤ ∫ y in (-L)..L,
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I)‖) :
    (W.card : ℝ) * V ^ 4 ≤
      (2 * L) ^ 3 * (2 * L + 1) *
        ∫ u in (-(3 * T))..(3 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4 := by
  classical
  set g : ℝ → ℝ := fun u => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ with hgdef
  have hg : Continuous g := continuous_norm_riemannZeta_half
  have hT0 : 0 ≤ T := le_trans hL hLT
  -- each window
  have hwin : ∀ γ ∈ W, V ^ 4 ≤ (2 * L) ^ 3 * ∫ u in (γ - L)..(γ + L), g u ^ 4 := by
    intro γ hγ
    have h1 : (∫ y in (-L)..L, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + ((γ + y : ℝ) : ℂ) * I)‖) =
        ∫ u in (γ - L)..(γ + L), g u := by
      have := intervalIntegral.integral_comp_add_left g γ (a := -L) (b := L)
      simp only [hgdef] at this ⊢
      rw [show γ - L = γ + -L by ring]
      simpa using this
    have h2 := intervalIntegral_pow_four_le hg (a := γ - L) (b := γ + L) (by linarith)
    rw [show γ + L - (γ - L) = 2 * L by ring] at h2
    have h3 := hbig γ hγ
    rw [h1] at h3
    exact le_trans (pow_le_pow_left₀ hV h3 4) h2
  -- the windows as indicator integrals over `[-3T, 3T]`
  set J : Set ℝ := Icc (-(3 * T)) (3 * T) with hJ
  have hg4int : IntegrableOn (fun u => g u ^ 4) J :=
    (hg.pow 4).continuousOn.integrableOn_compact isCompact_Icc
  have hwinJ : ∀ γ ∈ W, (∫ u in (γ - L)..(γ + L), g u ^ 4) =
      ∫ u in J, (Icc (γ - L) (γ + L)).indicator (fun u => g u ^ 4) u := by
    intro γ hγ
    have hsub : Icc (γ - L) (γ + L) ⊆ J := by
      intro u hu
      have := hW γ hγ
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub,
      intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
  have hsum : (∑ γ ∈ W, ∫ u in (γ - L)..(γ + L), g u ^ 4) =
      ∫ u in J, ∑ γ ∈ W, (Icc (γ - L) (γ + L)).indicator (fun u => g u ^ 4) u := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl hwinJ
    · intro γ _
      exact hg4int.indicator measurableSet_Icc
  -- pointwise overlap
  have hover : ∀ u : ℝ, (∑ γ ∈ W, (Icc (γ - L) (γ + L)).indicator (fun u => g u ^ 4) u) ≤
      (2 * L + 1) * g u ^ 4 := by
    intro u
    have heq : (∑ γ ∈ W, (Icc (γ - L) (γ + L)).indicator (fun u => g u ^ 4) u) =
        ((W.filter fun γ => u ∈ Icc (γ - L) (γ + L)).card : ℝ) * g u ^ 4 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Set.indicator_apply]
      split_ifs <;> simp
    rw [heq]
    have hcard : ((W.filter fun γ => u ∈ Icc (γ - L) (γ + L)).card : ℝ) ≤ 2 * L + 1 := by
      refine card_le_of_separated_subset_Icc (a := u - L) (by linarith) ?_ ?_
      · intro γ hγ
        have := (Finset.mem_filter.mp hγ).2
        exact ⟨by linarith [this.2], by linarith [this.1]⟩
      · intro γ hγ γ' hγ' hne
        exact hsep γ (Finset.mem_filter.mp hγ).1 γ' (Finset.mem_filter.mp hγ').1 hne
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have hmono : (∫ u in J, ∑ γ ∈ W, (Icc (γ - L) (γ + L)).indicator (fun u => g u ^ 4) u) ≤
      ∫ u in J, (2 * L + 1) * g u ^ 4 := by
    refine setIntegral_mono_on ?_ (hg4int.const_mul _) measurableSet_Icc fun u _ => hover u
    exact integrable_finsetSum _ fun γ _ => hg4int.indicator measurableSet_Icc
  have hJint : (∫ u in J, (2 * L + 1) * g u ^ 4) =
      (2 * L + 1) * ∫ u in (-(3 * T))..(3 * T), g u ^ 4 := by
    rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc]
  -- assemble
  have hL3 : 0 ≤ (2 * L) ^ 3 := by positivity
  calc (W.card : ℝ) * V ^ 4 = ∑ γ ∈ W, V ^ 4 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ γ ∈ W, (2 * L) ^ 3 * ∫ u in (γ - L)..(γ + L), g u ^ 4 :=
        Finset.sum_le_sum hwin
    _ = (2 * L) ^ 3 * ∑ γ ∈ W, ∫ u in (γ - L)..(γ + L), g u ^ 4 := by rw [Finset.mul_sum]
    _ ≤ (2 * L) ^ 3 * ((2 * L + 1) * ∫ u in (-(3 * T))..(3 * T), g u ^ 4) := by
        rw [hsum, ← hJint]
        exact mul_le_mul_of_nonneg_left hmono hL3
    _ = (2 * L) ^ 3 * (2 * L + 1) * ∫ u in (-(3 * T))..(3 * T), g u ^ 4 := by ring

/-- The critical fourth moment on `[-3T, 3T]` is `≤ D T (1 + log T)⁴`. -/
theorem exists_integral_norm_riemannZeta_half_pow_four_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {T : ℝ}, 2 ≤ T →
      ∫ u in (-(3 * T))..(3 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4 ≤
        D * T * (1 + Real.log T) ^ 4 := by
  obtain ⟨D, hD, hbound⟩ := Sieve.exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_polylog
  refine ⟨D * 4 * 4 ^ 4, by positivity, fun {T} hT => ?_⟩
  have hT0 : 0 < T := by linarith
  set N : ℕ := ⌈3 * T⌉₊ with hN
  have hN1 : 3 * T ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < 3 * T + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hb := hbound hN4
  have heq : Sieve.inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ) =
      ∫ t in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 4 := by
    unfold Sieve.inghamCriticalZetaFourthMoment
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hpt : Sieve.inghamCriticalPoint t = ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I := by
      unfold Sieve.inghamCriticalPoint; push_cast; ring
    simp only [hpt]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [heq] at hb
  have hmono : (∫ u in (-(3 * T))..(3 * T),
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4) ≤
      ∫ u in (-(N : ℝ))..(N : ℝ), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 4 := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) hN1
      (Eventually.of_forall fun u => by positivity) ?_
    exact ((continuous_norm_riemannZeta_half.pow 4).intervalIntegrable _ _)
  refine le_trans hmono (le_trans hb ?_)
  have hlogN : 1 + Real.log N ≤ 4 * (1 + Real.log T) := by
    have hNpos : (0 : ℝ) < N := by linarith
    have h1 : Real.log N ≤ Real.log (4 * T) := Real.log_le_log hNpos (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h1
    have h4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    have := Real.log_nonneg (show (1 : ℝ) ≤ T by linarith)
    linarith
  have hlogN0 : 0 ≤ 1 + Real.log N := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N))
    linarith
  calc D * (N : ℝ) * (1 + Real.log N) ^ 4 ≤ D * (4 * T) * (4 * (1 + Real.log T)) ^ 4 := by
        gcongr
        linarith
    _ = D * 4 * 4 ^ 4 * T * (1 + Real.log T) ^ 4 := by ring

end RHTower
