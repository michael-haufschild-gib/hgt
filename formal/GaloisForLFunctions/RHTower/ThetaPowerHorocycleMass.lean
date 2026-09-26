import GaloisForLFunctions.RHTower.ThetaPowerModularTwoSidedBound

/-!
# Horocycle mass of the theta-power family

For `0 ≤ a ≤ 1/2` and `0 < y ≤ 1`, the horizontal horocycle `x ↦ x + iy`, `0 ≤ x ≤ 2`, carries
`L²`-mass `∫₀² |F_a(x+iy)|² dx ≥ L_K² (2 - 6/K) y^{-1/2}`.

If the reduction `g` of `τ = x + iy` into the fundamental domain has `Im gτ > K`, then its bottom row
`(c, d)` satisfies `(cx+d)² + c²y² < y/K`, so `1 ≤ |c| < (Ky)^{-1/2}` and `|cx+d| < (y/K)^{1/2}`.  These `x`
lie in at most `2c+1` intervals of length `2(y/K)^{1/2}/c` for each `c`, of total length `≤ 6/K` in `[0,2]`.
Everywhere else `|F_a(τ)| (Im τ)^{1/4} ≥ L_K` (`thetaPowerLowerConstant_le`).
-/

open Complex UpperHalfPlane ModularGroup MeasureTheory Set
open scoped MatrixGroups Real

namespace RHTower

noncomputable section

open Bottcher

/-- The horocycle points close to a cusp of small denominator. -/
def horoBad (K y : ℝ) : Set ℝ :=
  ⋃ (c : ℕ) (_ : 1 ≤ c ∧ (c : ℝ) ^ 2 * (K * y) < 1) (d : ℤ),
    {x : ℝ | |(c : ℝ) * x + d| < Real.sqrt (y / K)}

theorem isOpen_horoBad (K y : ℝ) : IsOpen (horoBad K y) := by
  unfold horoBad
  refine isOpen_iUnion fun c => isOpen_iUnion fun _ => isOpen_iUnion fun d => ?_
  exact isOpen_lt (by fun_prop) continuous_const

theorem measurableSet_horoBad (K y : ℝ) : MeasurableSet (horoBad K y) :=
  (isOpen_horoBad K y).measurableSet

/-- **Measure of the bad set.** -/
theorem volume_Icc_inter_horoBad_le {K y : ℝ} (hK : 1 ≤ K) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    volume (Icc (0 : ℝ) 2 ∩ horoBad K y) ≤ ENNReal.ofReal (6 / K) := by
  set ρ : ℝ := Real.sqrt (y / K) with hρ
  have hK0 : 0 < K := by linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, Real.sqrt_le_one]
    rw [div_le_one hK0]; linarith
  set s : ℝ := Real.sqrt (K * y) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set C : ℕ := ⌊1 / s⌋₊ with hC
  have hρs : ρ * s = y := by
    rw [hρ, hs, ← Real.sqrt_mul (by positivity)]
    rw [show y / K * (K * y) = y ^ 2 by field_simp]
    exact Real.sqrt_sq hy0.le
  have hsub : Icc (0 : ℝ) 2 ∩ horoBad K y ⊆
      ⋃ c ∈ Finset.Icc 1 C, ⋃ d ∈ Finset.Icc (-2 * (c : ℤ)) 0,
        Ioo ((-(d : ℝ) - ρ) / c) ((-(d : ℝ) + ρ) / c) := by
    rintro x ⟨⟨hx0, hx2⟩, hx⟩
    simp only [horoBad, mem_iUnion, mem_setOf_eq] at hx
    obtain ⟨c, ⟨hc1, hcK⟩, d, hd⟩ := hx
    have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
    refine ⟨c, ⟨hc1, ?_⟩, d, ⟨?_, ?_⟩, ?_⟩
    · apply Nat.le_floor
      have hcs : (c : ℝ) * s < 1 := by
        have h1 : ((c : ℝ) * s) ^ 2 < 1 := by
          rw [mul_pow, hs, Real.sq_sqrt (by positivity)]; linarith
        nlinarith [mul_pos hcpos hs0]
      rw [le_div_iff₀ hs0]; linarith
    · have h := (abs_lt.mp hd).1
      have : (-(2 * c : ℝ)) - 1 < d := by nlinarith
      have : (-(2 * c : ℤ)) - 1 < d := by exact_mod_cast this
      omega
    · have h := (abs_lt.mp hd).2
      have : (d : ℝ) < 1 := by nlinarith
      have : d < 1 := by exact_mod_cast this
      omega
    · rw [mem_Ioo, div_lt_iff₀ hcpos, lt_div_iff₀ hcpos]
      have h := abs_lt.mp hd
      constructor <;> linarith [h.1, h.2]
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hc_term : ∀ c ∈ Finset.Icc 1 C,
      volume (⋃ d ∈ Finset.Icc (-2 * (c : ℤ)) 0, Ioo ((-(d : ℝ) - ρ) / c) ((-(d : ℝ) + ρ) / c)) ≤
        ENNReal.ofReal (6 * ρ) := by
    intro c hc
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hlen : ∀ d ∈ Finset.Icc (-2 * (c : ℤ)) 0,
        volume (Ioo ((-(d : ℝ) - ρ) / c) ((-(d : ℝ) + ρ) / c)) = ENNReal.ofReal (2 * ρ / c) := by
      intro d _
      rw [Real.volume_Ioo]; congr 1; field_simp; ring
    rw [Finset.sum_congr rfl hlen, Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
    rw [show (0 : ℤ) + 1 - -2 * (c : ℤ) = ((2 * c + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    rw [show ((2 : ℝ) * c + 1) * (2 * ρ / c) = 4 * ρ + 2 * ρ / c by field_simp; ring]
    have : 2 * ρ / c ≤ 2 * ρ := div_le_self (by positivity) (by exact_mod_cast hc1)
    linarith
  refine le_trans (Finset.sum_le_sum hc_term) ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hCs : (C : ℝ) ≤ 1 / s := Nat.floor_le (by positivity)
  have hρy : ρ / y = 1 / s := by field_simp; linarith [hρs]
  have hρK : ρ * (1 / s) = 1 / K := by
    rw [← hρy]
    have hyK : ρ * (ρ / y) = ρ ^ 2 / y := by ring
    rw [hyK, hρ, Real.sq_sqrt (by positivity)]
    field_simp
  calc (C : ℝ) * (6 * ρ) ≤ (1 / s) * (6 * ρ) := by gcongr
    _ = 6 * (ρ * (1 / s)) := by ring
    _ = 6 / K := by rw [hρK]; ring

/-- **Good horocycle points.** Outside the bad set the reduction lands in `Im ≤ K`, so the compact
part lower bound applies. -/
theorem thetaPowerLowerConstant_le_horocycle {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) {K y x : ℝ}
    (hK : 1 ≤ K) (hy0 : 0 < y) (hy1 : y ≤ 1) (hx : x ∉ horoBad K y) :
    thetaPowerLowerConstant K ≤ ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ * y ^ (1 / 4 : ℝ) := by
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy0]
  set τ : ℍ := ⟨(x : ℂ) + y * Complex.I, him⟩ with hτ
  have hτim : τ.im = y := by simp [hτ, UpperHalfPlane.im]
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have hK' : (g • τ).im ≤ K := by
    by_contra hgt
    rw [not_le] at hgt
    apply hx
    have hform := ModularGroup.im_smul_eq_div_normSq g τ
    rw [ModularGroup.denom_apply] at hform
    set c : ℤ := g 1 0
    set d : ℤ := g 1 1
    have hns : Complex.normSq ((c : ℂ) * (τ : ℂ) + d) = ((c : ℝ) * x + d) ^ 2 + ((c : ℝ) * y) ^ 2 := by
      simp [Complex.normSq_apply, hτ]; ring
    rw [hns, hτim] at hform
    have hpos : 0 < ((c : ℝ) * x + d) ^ 2 + ((c : ℝ) * y) ^ 2 := by
      have := (g • τ).im_pos; rw [hform] at this
      exact (div_pos_iff.mp this).elim (fun h => h.2) (fun h => absurd h.1 (not_lt.mpr hy0.le))
    have hlt : ((c : ℝ) * x + d) ^ 2 + ((c : ℝ) * y) ^ 2 < y / K := by
      rw [hform, lt_div_iff₀ hpos] at hgt
      rw [lt_div_iff₀ (by linarith : (0 : ℝ) < K)]; linarith
    have hc0 : c ≠ 0 := by
      intro hc
      have hdet := Matrix.SpecialLinearGroup.det_coe g
      rw [Matrix.det_fin_two] at hdet
      have hc' : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := hc
      rw [hc', mul_zero, sub_zero] at hdet
      have hd1 : d = 1 ∨ d = -1 := Int.eq_one_or_neg_one_of_mul_eq_one' hdet |>.elim
        (fun h => Or.inl h.2) (fun h => Or.inr h.2)
      have hsq : ((d : ℝ)) ^ 2 = 1 := by rcases hd1 with h | h <;> simp [h]
      rw [hc] at hlt; simp only [Int.cast_zero, zero_mul, zero_add] at hlt
      rw [hsq] at hlt
      have : y / K ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    simp only [horoBad, mem_iUnion, mem_setOf_eq]
    have hcabs : (0 : ℝ) < |(c : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
    refine ⟨c.natAbs, ⟨?_, ?_⟩, if 0 < c then d else -d, ?_⟩
    · exact Int.natAbs_pos.mpr hc0
    · have hcast : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hcast, sq_abs]
      have h1 : ((c : ℝ) * y) ^ 2 < y / K := by nlinarith [sq_nonneg ((c : ℝ) * x + d)]
      have hK0 : 0 < K := by linarith
      rw [lt_div_iff₀ hK0] at h1
      nlinarith
    · have hcast : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hkey : |((c.natAbs : ℕ) : ℝ) * x + ((if 0 < c then d else -d : ℤ) : ℝ)| =
          |(c : ℝ) * x + d| := by
        rw [hcast]
        split_ifs with hcp
        · rw [abs_of_pos (by exact_mod_cast hcp : (0 : ℝ) < c)]
        · have hcn : (c : ℝ) < 0 := by
            have : c < 0 := lt_of_le_of_ne (not_lt.mp hcp) hc0
            exact_mod_cast this
          rw [abs_of_neg hcn, Int.cast_neg, ← abs_neg]; congr 1; ring
      rw [hkey]
      have h1 : ((c : ℝ) * x + d) ^ 2 < y / K := by nlinarith [sq_nonneg ((c : ℝ) * y)]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) h1
  have h := thetaPowerLowerConstant_le ha0 ha1 τ g hg hK'
  rwa [hτim] at h

theorem continuous_thetaPowerForm_horizontal (a y : ℝ) (hy : 0 < y) :
    Continuous fun x : ℝ => thetaPowerForm a ((x : ℂ) + y * Complex.I) := by
  have hd := differentiableOn_thetaPowerForm a
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : ((x : ℂ) + y * Complex.I) ∈ modUpperSet := by show 0 < ((x : ℂ) + y * Complex.I).im; simp [hy]
  have hat := (hd.differentiableAt (isOpen_modUpperSet.mem_nhds hmem)).continuousAt
  exact ContinuousAt.comp (g := thetaPowerForm a) hat
    (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + y * Complex.I) x)

/-- **Horocycle mass.** -/
theorem thetaPowerHorocycleMass {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) {K y : ℝ} (hK : 6 ≤ K)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    thetaPowerLowerConstant K ^ 2 * (2 - 6 / K) * y ^ (-(1 / 2 : ℝ)) ≤
      ∫ x in (0 : ℝ)..2, ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2 := by
  have hK1 : 1 ≤ K := by linarith
  set L := thetaPowerLowerConstant K with hL
  have hL0 : 0 < L := thetaPowerLowerConstant_pos K
  set B := horoBad K y
  set f : ℝ → ℝ := fun x => ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2 with hf
  have hfc : Continuous f := (continuous_thetaPowerForm_horizontal a y hy0).norm.pow 2
  set c0 : ℝ := L ^ 2 * y ^ (-(1 / 2 : ℝ)) with hc0
  have hc0pos : 0 ≤ c0 := by positivity
  have hpt : ∀ x, Bᶜ.indicator (fun _ => c0) x ≤ f x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_notMem (by simpa using hx)]; exact sq_nonneg _
    · rw [Set.indicator_of_mem (by simpa using hx)]
      have h := thetaPowerLowerConstant_le_horocycle ha0 ha1 hK1 hy0 hy1 hx
      have hy4 : 0 < y ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy0 _
      have hsq : L ^ 2 ≤ (‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ * y ^ (1 / 4 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hL0.le h 2
      have hyy : (y ^ (1 / 4 : ℝ)) ^ 2 * y ^ (-(1 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]; norm_num
      calc c0 = L ^ 2 * y ^ (-(1 / 2 : ℝ)) := rfl
        _ ≤ (‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ * y ^ (1 / 4 : ℝ)) ^ 2 * y ^ (-(1 / 2 : ℝ)) := by
            gcongr
        _ = f x * ((y ^ (1 / 4 : ℝ)) ^ 2 * y ^ (-(1 / 2 : ℝ))) := by rw [hf]; ring
        _ = f x := by rw [hyy, mul_one]
  have hmeasB : MeasurableSet Bᶜ := (measurableSet_horoBad K y).compl
  rw [intervalIntegral.integral_of_le (by norm_num)]
  have hint_ind : IntegrableOn (Bᶜ.indicator fun _ => c0) (Ioc (0 : ℝ) 2) :=
    (integrableOn_const (by simp) ).indicator hmeasB
  have hmono := setIntegral_mono_on hint_ind (hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    measurableSet_Ioc (fun x _ => hpt x)
  refine le_trans ?_ hmono
  rw [setIntegral_indicator hmeasB, setIntegral_const, smul_eq_mul]
  have hvol : 2 - 6 / K ≤ volume.real (Ioc (0 : ℝ) 2 ∩ Bᶜ) := by
    have hbad := volume_Icc_inter_horoBad_le hK1 hy0 hy1
    have hIoc : volume (Ioc (0 : ℝ) 2) ≤ volume (Ioc (0 : ℝ) 2 ∩ Bᶜ) + volume (Icc (0 : ℝ) 2 ∩ B) := by
      calc volume (Ioc (0 : ℝ) 2) ≤ volume ((Ioc (0 : ℝ) 2 ∩ Bᶜ) ∪ (Icc (0 : ℝ) 2 ∩ B)) := by
            apply measure_mono
            intro x hx
            by_cases hxB : x ∈ B
            · exact Or.inr ⟨Ioc_subset_Icc_self hx, hxB⟩
            · exact Or.inl ⟨hx, hxB⟩
        _ ≤ _ := measure_union_le _ _
    rw [Real.volume_Ioc] at hIoc
    have hfin : volume (Ioc (0 : ℝ) 2 ∩ Bᶜ) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.inter_subset_left)
    have h2 : ENNReal.ofReal (2 - 0) ≤ volume (Ioc (0 : ℝ) 2 ∩ Bᶜ) + ENNReal.ofReal (6 / K) :=
      le_trans hIoc (add_le_add le_rfl hbad)
    rw [measureReal_def]
    have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) h2
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by norm_num),
      ENNReal.toReal_ofReal (by positivity)] at h3
    linarith
  have hK6 : 0 ≤ 2 - 6 / K := by
    rw [sub_nonneg, div_le_iff₀ (by linarith)]; linarith
  calc L ^ 2 * (2 - 6 / K) * y ^ (-(1 / 2 : ℝ)) = (2 - 6 / K) * c0 := by rw [hc0]; ring
    _ ≤ volume.real (Ioc (0 : ℝ) 2 ∩ Bᶜ) * c0 := mul_le_mul_of_nonneg_right hvol hc0pos

end

end RHTower
