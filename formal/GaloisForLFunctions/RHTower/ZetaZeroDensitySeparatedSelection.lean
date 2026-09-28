import GaloisForLFunctions.RHTower.ZetaZeroDetectionBlockTaylor
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.XiLogDerivZeroFreePositive
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Zeros in a height box become separated large values of one explicit polynomial

Fix `T ≥ 2^{120}`, the mollifier length `y = ⌊T^{1/40}⌋`, the block length `N = ⌈T^{61/50}⌉`, and
put `J = ⌊log₂(Ny)⌋ + 1`, `Λ = log(Ny)`, `M = ⌊Λ⌋ + 1`.  Every zero copy of the box
`σ ≤ Re ρ`, `T ≤ Im ρ ≤ 2T` (with `1/2 ≤ σ ≤ 1`) is detected, lies in one of the `M` slabs
`[σ + m/Λ, σ + (m+1)/Λ)`, and so has a class `(j, i, m)` for which the Taylor companion polynomial of
the `j`-th dyadic block is at least `1/(12J)` at `σ + m/Λ + i Im ρ`.

The most populated class, thinned to a `1`-separated set of ordinates, carries the whole box count
up to the explicit factor `J(J+8)M · 16(|C| + log(2T+5))`.  That factor is the number of classes times
the local zero-count capacity `ncard_xiOrdinateWindow_one_le_log`.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve

/-! ## Two finite selection principles -/

/-- **Maximal separated subsets.**  If every unit window around every real number contains at most
`K` points of `Z` (measured by `f`), then `Z` has a `1`-separated subset `S` with `#Z ≤ K·#S`. -/
theorem exists_separated_subset_card_le {α : Type*} [DecidableEq α] (Z : Finset α) (f : α → ℝ)
    {K : ℝ} (hK : ∀ t : ℝ, ((Z.filter (fun z => |f z - t| ≤ 1)).card : ℝ) ≤ K) :
    ∃ S ⊆ Z, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ |f a - f b|) ∧ (Z.card : ℝ) ≤ K * S.card := by
  set P := Z.powerset.filter (fun S => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ |f a - f b|) with hP
  have hne : P.Nonempty := ⟨∅, by simp [hP]⟩
  obtain ⟨S, hSP, hmax⟩ := P.exists_max_image Finset.card hne
  rw [hP, Finset.mem_filter, Finset.mem_powerset] at hSP
  refine ⟨S, hSP.1, hSP.2, ?_⟩
  have hcover : ∀ z ∈ Z, ∃ s ∈ S, |f z - f s| ≤ 1 := by
    intro z hz
    by_contra hcon
    push Not at hcon
    have hzS : z ∉ S := fun h => by
      have := hcon z h
      rw [sub_self, abs_zero] at this
      linarith
    have hins : insert z S ∈ P := by
      rw [hP, mem_filter, mem_powerset]
      refine ⟨insert_subset hz hSP.1, ?_⟩
      intro a ha b hb hab
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact (hcon b hb).le
      · rw [abs_sub_comm]
        exact (hcon a ha).le
      · exact hSP.2 a ha b hb hab
    have h := hmax _ hins
    rw [card_insert_of_notMem hzS] at h
    omega
  have hsub : Z ⊆ S.biUnion (fun s => Z.filter (fun z => |f z - f s| ≤ 1)) := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := hcover z hz
    exact mem_biUnion.mpr ⟨s, hs, mem_filter.mpr ⟨hz, hzs⟩⟩
  calc (Z.card : ℝ) ≤ (S.biUnion (fun s => Z.filter (fun z => |f z - f s| ≤ 1))).card := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ s ∈ S, ((Z.filter (fun z => |f z - f s| ≤ 1)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _s ∈ S, K := sum_le_sum fun s _ => hK (f s)
    _ = K * S.card := by rw [sum_const, nsmul_eq_mul]; ring

/-- **Pigeonhole with a real ratio.**  Some fiber of a map into `t` carries a `1/#t` share. -/
theorem exists_fiber_card_ge {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → β) (hf : ∀ a ∈ s, f a ∈ t) (ht : t.Nonempty) :
    ∃ b ∈ t, (s.card : ℝ) ≤ t.card * (s.filter (fun a => f a = b)).card := by
  obtain ⟨b, hb, hmax⟩ := t.exists_max_image (fun b => (s.filter (fun a => f a = b)).card) ht
  refine ⟨b, hb, ?_⟩
  have hsum := Finset.card_eq_sum_card_fiberwise hf
  calc (s.card : ℝ) = ∑ c ∈ t, ((s.filter (fun a => f a = c)).card : ℝ) := by
        exact_mod_cast hsum
    _ ≤ ∑ _c ∈ t, ((s.filter (fun a => f a = b)).card : ℝ) :=
        sum_le_sum fun c hc => by exact_mod_cast hmax c hc
    _ = t.card * (s.filter (fun a => f a = b)).card := by rw [sum_const, nsmul_eq_mul]

/-! ## The parameters -/

/-- The mollifier length `⌊T^{1/40}⌋`. -/
def densityMollifierLength (T : ℝ) : ℕ := ⌊T ^ (1 / 40 : ℝ)⌋₊

/-- The block length `⌈T^{61/50}⌉`. -/
def densityBlockLength (T : ℝ) : ℕ := ⌈T ^ (61 / 50 : ℝ)⌉₊

/-- The zero copies with `σ ≤ Re ρ` and `T ≤ Im ρ ≤ 2T`. -/
def zeroHeightBox (σ T : ℝ) : Set XiZeroCopy :=
  {q | σ ≤ (q.1 : ℂ).re ∧ T ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T}

theorem zeroHeightBox_finite (σ T : ℝ) : (zeroHeightBox σ T).Finite := by
  refine (finite_xiOrdinateWindow (T / 2) (3 * T / 2)).subset ?_
  intro q hq
  rw [mem_xiOrdinateWindow_iff, abs_le]
  exact ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩

/-- The local capacity `16(|C| + log(2T+5))` of a unit ordinate window meeting the box. -/
def densityWindowCapacity (T : ℝ) : ℝ := 16 * (|xiLineTwoLogDerivConstant| + Real.log (2 * T + 5))

theorem densityParameters {T : ℝ} (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T) :
    1 ≤ densityMollifierLength T ∧
    ((densityMollifierLength T : ℕ) : ℝ) ≤ T ^ (1 / 40 : ℝ) ∧
    T ^ (61 / 50 : ℝ) ≤ (densityBlockLength T : ℝ) ∧
    (densityBlockLength T : ℝ) ≤ 2 * T ^ (61 / 50 : ℝ) ∧
    2 ≤ densityBlockLength T * densityMollifierLength T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ (by norm_num)) hT
  have h8 : (8 : ℝ) ≤ T ^ (1 / 40 : ℝ) := by
    calc (8 : ℝ) = ((2 : ℝ) ^ (120 : ℕ)) ^ (1 / 40 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ T ^ (1 / 40 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
  have hA1 : (2 : ℝ) ≤ T ^ (61 / 50 : ℝ) := by
    calc (2 : ℝ) ≤ 8 := by norm_num
      _ ≤ T ^ (1 / 40 : ℝ) := h8
      _ ≤ T ^ (61 / 50 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hy1 : 1 ≤ densityMollifierLength T := by
    unfold densityMollifierLength
    exact Nat.le_floor (by push_cast; linarith)
  refine ⟨hy1, Nat.floor_le (by positivity), Nat.le_ceil _, ?_, ?_⟩
  · have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ T ^ (61 / 50 : ℝ) by positivity)
    unfold densityBlockLength
    linarith
  · have hN : 2 ≤ densityBlockLength T := by
      unfold densityBlockLength
      exact_mod_cast (le_trans hA1 (Nat.le_ceil _))
    calc 2 ≤ densityBlockLength T := hN
      _ = densityBlockLength T * 1 := (mul_one _).symm
      _ ≤ densityBlockLength T * densityMollifierLength T := Nat.mul_le_mul_left _ hy1

/-! ## The class of a detected zero -/

/-- **Every zero copy of the box has a class.** -/
theorem exists_class_of_mem_zeroHeightBox {σ T : ℝ} (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T)
    (hσ : 1 / 2 ≤ σ) {q : XiZeroCopy} (hq : q ∈ zeroHeightBox σ T) :
    let N := densityBlockLength T
    let y := densityMollifierLength T
    let Λ := Real.log (N * y : ℕ)
    ∃ j < detBlockCount N y, ∃ i < detBlockCount N y + 8, ∃ m < ⌊Λ⌋₊ + 1,
      1 / (12 * detBlockCount N y) ≤
        ‖abscissaTaylorPoly (detDyadicBlock N y j) (detCoeffC N y) Λ i (σ + m / Λ)
          (q.1 : ℂ).im‖ := by
  intro N y Λ
  obtain ⟨hy1, hyT, hN1, hN2, hNy⟩ := densityParameters hT
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hre := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
  have hzero := riemannZeta_eq_zero_of_xiZeroCopy q
  have hγpos : 0 < (q.1 : ℂ).im := lt_of_lt_of_le hT0 hq.2.1
  have hdet := half_le_norm_detPolyC_of_height hT hy1 hyT hN1 hN2 (le_trans hσ hq.1) hre.2.le
    (by rw [abs_of_pos hγpos]; exact hq.2.1) (by rw [abs_of_pos hγpos]; exact hq.2.2) hzero
  have hNy' : 1 < N * y := by
    change 1 < densityBlockLength T * densityMollifierLength T
    omega
  have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast hNy')
  set x : ℝ := ((q.1 : ℂ).re - σ) * Λ with hx
  have hx0 : 0 ≤ x := mul_nonneg (by linarith [hq.1]) hΛ0.le
  set m : ℕ := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  have hmM : m < ⌊Λ⌋₊ + 1 := by
    have hxΛ : x ≤ Λ := by
      rw [hx]
      have : (q.1 : ℂ).re - σ ≤ 1 := by linarith [hre.2]
      nlinarith
    exact Nat.lt_succ_of_le (Nat.floor_le_floor hxΛ)
  set δ : ℝ := (q.1 : ℂ).re - (σ + m / Λ) with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    have : (m : ℝ) / Λ ≤ (q.1 : ℂ).re - σ := by
      rw [div_le_iff₀ hΛ0]
      linarith
    linarith
  have hδΛ : δ * Λ ≤ 1 := by
    rw [hδ, sub_mul, add_mul, div_mul_cancel₀ _ hΛ0.ne']
    linarith
  have hσm : 0 ≤ σ + m / Λ := by positivity
  have hpt : (q.1 : ℂ) = (((σ + m / Λ + δ : ℝ) : ℂ) + ((q.1 : ℂ).im : ℂ) * I) := by
    rw [hδ]
    apply Complex.ext <;> simp
  rw [hpt] at hdet
  obtain ⟨j, hj, i, hi, hlarge⟩ := exists_detBlock_taylor_large hNy hσm hδ0 hδΛ hdet
  exact ⟨j, hj, i, hi, m, hmM, hlarge⟩

/-! ## The separated class -/

/-- **Zeros of a height box become separated large values.**  For `T ≥ 2^{120}` and
`1/2 ≤ σ`, there are a class `(j, i, m)` and a `1`-separated set `W ⊆ [T, 2T]` of ordinates at which
the companion polynomial of that class is at least `1/(12J)` on the line `σ + m/Λ`, such that the box
count is at most `J(J+8)(⌊Λ⌋+1) · 16(|C| + log(2T+5)) · #W`. -/
theorem exists_separated_class_of_zeroHeightBox {σ T : ℝ} (hT : (2 : ℝ) ^ (120 : ℕ) ≤ T)
    (hσ : 1 / 2 ≤ σ) :
    let N := densityBlockLength T
    let y := densityMollifierLength T
    let Λ := Real.log (N * y : ℕ)
    let J := detBlockCount N y
    ∃ j < J, ∃ i < J + 8, ∃ m < ⌊Λ⌋₊ + 1, ∃ W : Finset ℝ,
      (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) ∧
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) ∧
      (∀ t ∈ W, 1 / (12 * J) ≤
        ‖abscissaTaylorPoly (detDyadicBlock N y j) (detCoeffC N y) Λ i (σ + m / Λ) t‖) ∧
      ((zeroHeightBox σ T).ncard : ℝ) ≤
        (J * (J + 8) * (⌊Λ⌋₊ + 1) : ℕ) * densityWindowCapacity T * W.card := by
  intro N y Λ J
  classical
  set Z : Finset XiZeroCopy := (zeroHeightBox_finite σ T).toFinset with hZ
  set C : Finset (ℕ × ℕ × ℕ) := range J ×ˢ range (J + 8) ×ˢ range (⌊Λ⌋₊ + 1) with hC
  let good : XiZeroCopy → ℕ × ℕ × ℕ → Prop := fun q c =>
    c ∈ C ∧ 1 / (12 * J) ≤
      ‖abscissaTaylorPoly (detDyadicBlock N y c.1) (detCoeffC N y) Λ c.2.1 (σ + c.2.2 / Λ)
        (q.1 : ℂ).im‖
  have hex : ∀ q ∈ Z, ∃ c, good q c := by
    intro q hqZ
    rw [hZ, Set.Finite.mem_toFinset] at hqZ
    obtain ⟨j, hj, i, hi, m, hm, hlarge⟩ := exists_class_of_mem_zeroHeightBox hT hσ hqZ
    refine ⟨(j, i, m), ?_, hlarge⟩
    rw [hC]
    simp only [mem_product, mem_range]
    exact ⟨hj, hi, hm⟩
  let cls : XiZeroCopy → ℕ × ℕ × ℕ := fun q =>
    if h : q ∈ Z then Classical.choose (hex q h) else (0, 0, 0)
  have hcls : ∀ q ∈ Z, good q (cls q) := by
    intro q hq
    simp only [cls, dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hCne : C.Nonempty := by
    refine ⟨(0, 0, 0), ?_⟩
    simp only [hC, mem_product, mem_range]
    exact ⟨by simp [J, detBlockCount], by omega, by omega⟩
  obtain ⟨c, hcC, hfib⟩ := exists_fiber_card_ge Z C cls (fun q hq => (hcls q hq).1) hCne
  set Zc := Z.filter (fun q => cls q = c) with hZc
  have hcap : ∀ t : ℝ, ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).card : ℝ)
      ≤ densityWindowCapacity T := by
    intro t
    by_cases hne : (Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).Nonempty
    · obtain ⟨q, hq⟩ := hne
      rw [mem_filter, hZc, mem_filter, hZ, Set.Finite.mem_toFinset] at hq
      have ht : |t| ≤ 2 * T + 1 := by
        have h1 := hq.2
        rw [abs_le] at h1 ⊢
        have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
        constructor <;> linarith [hq.1.1.2.1, hq.1.1.2.2]
      have hsub : ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)) : Set XiZeroCopy)
          ⊆ xiOrdinateWindow 1 t := by
        intro z hz
        rw [mem_coe, mem_filter] at hz
        exact hz.2
      have hle := Set.ncard_le_ncard hsub (finite_xiOrdinateWindow 1 t)
      rw [Set.ncard_coe_finset] at hle
      have hwin := ncard_xiOrdinateWindow_one_le_log t
      have hlog : Real.log (|t| + 4) ≤ Real.log (2 * T + 5) :=
        Real.log_le_log (by positivity) (by linarith)
      unfold densityWindowCapacity
      have habsC := le_abs_self xiLineTwoLogDerivConstant
      calc ((Zc.filter (fun z => |(z.1 : ℂ).im - t| ≤ 1)).card : ℝ)
          ≤ ((xiOrdinateWindow 1 t).ncard : ℝ) := by exact_mod_cast hle
        _ ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := hwin
        _ ≤ 16 * (|xiLineTwoLogDerivConstant| + Real.log (2 * T + 5)) := by linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, card_empty, Nat.cast_zero]
      unfold densityWindowCapacity
      have hT1 : (1 : ℝ) ≤ 2 * T + 5 := by
        have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
        linarith
      have := Real.log_nonneg hT1
      positivity
  obtain ⟨S, hSZ, hSsep, hScard⟩ :=
    exists_separated_subset_card_le Zc (fun q => (q.1 : ℂ).im) hcap
  refine ⟨c.1, ?_, c.2.1, ?_, c.2.2, ?_, S.image (fun q => (q.1 : ℂ).im), ?_, ?_, ?_, ?_⟩
  · simp only [hC, mem_product, mem_range] at hcC
    exact hcC.1
  · simp only [hC, mem_product, mem_range] at hcC
    exact hcC.2.1
  · simp only [hC, mem_product, mem_range] at hcC
    exact hcC.2.2
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    have hq' := hSZ hq
    rw [hZc, mem_filter, hZ, Set.Finite.mem_toFinset] at hq'
    exact ⟨hq'.1.2.1, hq'.1.2.2⟩
  · intro t ht t' ht' htt'
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    obtain ⟨q', hq', rfl⟩ := mem_image.mp ht'
    have hqq : q ≠ q' := fun h => htt' (by rw [h])
    exact hSsep q hq q' hq' hqq
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    have hq' := hSZ hq
    rw [hZc, mem_filter] at hq'
    have hg := hcls q hq'.1
    rw [hq'.2] at hg
    exact hg.2
  · have hinj : Set.InjOn (fun q : XiZeroCopy => (q.1 : ℂ).im) S := by
      intro a ha b hb hab
      by_contra hne
      have h := hSsep a ha b hb hne
      simp only at hab
      rw [hab, sub_self, abs_zero] at h
      linarith
    rw [card_image_of_injOn hinj]
    have hbox : (zeroHeightBox σ T).ncard = Z.card := by
      rw [hZ, Set.ncard_eq_toFinset_card _ (zeroHeightBox_finite σ T)]
    have hCcard : (C.card : ℝ) = ((J * (J + 8) * (⌊Λ⌋₊ + 1) : ℕ) : ℝ) := by
      rw [hC]
      simp [card_product]
      ring
    rw [hbox]
    have hcap0 : 0 ≤ densityWindowCapacity T := le_trans (by positivity) (hcap 0)
    calc (Z.card : ℝ) ≤ C.card * (Z.filter (fun a => cls a = c)).card := hfib
      _ = C.card * (Zc.card : ℝ) := by rw [hZc]
      _ ≤ C.card * (densityWindowCapacity T * S.card) :=
          mul_le_mul_of_nonneg_left hScard (Nat.cast_nonneg _)
      _ = ((J * (J + 8) * (⌊Λ⌋₊ + 1) : ℕ) : ℝ) * densityWindowCapacity T * S.card := by
          rw [hCcard]
          ring

end

end RHTower
