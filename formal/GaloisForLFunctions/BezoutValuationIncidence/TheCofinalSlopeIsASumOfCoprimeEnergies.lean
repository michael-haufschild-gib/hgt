import GaloisForLFunctions.BezoutValuationIncidence.TheCofinalMobiusProfileIsAsymptoticallyLinear

/-!
# The cofinal slope is a signed sum of coprime energies

The cofinal Möbius slope `κ = ρ Σ_j S(j) log(1 + 1/j)`, with `S(X) = Σ_{a,b ≤ X, (a,b)=1} w(a)w(b)`
and `w = μ/σ`, is the logarithmic integral of the step function `u ↦ S(⌊e^u⌋)`. The coprimality
sieve `S(X) = Σ_{δ ≤ X} μ(δ)(w(δ) T_δ(X/δ))²` splits that step function into translates of the
**coprime profiles** `g_δ(v) = T_δ(⌊e^v⌋₊)`, `T_δ(Y) = Σ_{a ≤ Y, (a,δ)=1} w(a)`:

  `S(⌊e^u⌋) = Σ_{δ ≥ 1} μ(δ) w(δ)² g_δ(u − log δ)²`.

Integrating and translating gives

  `κ = ρ Σ_{δ ≥ 1} μ(δ) w(δ)² ∫ g_δ²`   (`cofinalMobiusSlope_eq_tsum_coprimeEnergy`),

absolutely convergent by the coprime decay `|T_δ(Y)| ≤ C δ^{1/4} (1 + log Y)^{−2}`: the profile
energies grow at most like `δ^{1/2}` against the weight `w(δ)² ≤ δ^{−2}`.
-/

open MeasureTheory Set Filter ArithmeticFunction Function

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The coprime profile `g_δ(v) = T_δ(⌊e^v⌋₊)`. -/
def coprimeProfile (δ : ℕ) (v : ℝ) : ℝ := coprimeMoebiusSigmaSum δ ⌊Real.exp v⌋₊

/-- The coprime energy `∫ g_δ²`. -/
def coprimeEnergy (δ : ℕ) : ℝ := ∫ v, coprimeProfile δ v ^ 2

theorem coprimeMoebiusSigmaSum_zero (δ : ℕ) : coprimeMoebiusSigmaSum δ 0 = 0 := by
  simp [coprimeMoebiusSigmaSum]

theorem coprimeProfile_of_neg (δ : ℕ) {v : ℝ} (hv : v < 0) : coprimeProfile δ v = 0 := by
  have : ⌊Real.exp v⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hv)
  simp [coprimeProfile, this, coprimeMoebiusSigmaSum_zero]

theorem measurable_coprimeProfile (δ : ℕ) : Measurable (coprimeProfile δ) :=
  (measurable_from_nat (f := coprimeMoebiusSigmaSum δ)).comp Real.measurable_exp.nat_floor

/-- `1 + log ⌊e^v⌋₊ ≥ (3/10)(1 + v)` for `v ≥ 0`. -/
theorem three_tenths_mul_le_one_add_log_floor_exp {v : ℝ} (hv : 0 ≤ v) :
    3 / 10 * (1 + v) ≤ 1 + Real.log ⌊Real.exp v⌋₊ := by
  set X := ⌊Real.exp v⌋₊ with hX
  have hX1 : 1 ≤ X := Nat.le_floor (by simpa using Real.one_le_exp hv)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hhalf : Real.exp v / 2 ≤ X := by
    have hlt := Nat.lt_floor_add_one (Real.exp v)
    rw [← hX] at hlt
    by_cases h2 : Real.exp v ≤ 2
    · linarith
    · linarith [not_le.mp h2]
  have hlog : v - Real.log 2 ≤ Real.log X := by
    have := Real.log_le_log (by positivity) hhalf
    rwa [Real.log_div (Real.exp_pos v).ne' two_ne_zero, Real.log_exp] at this
  have h2 := Real.log_two_lt_d9
  linarith

/-- **Profile decay.** `|g_δ(v)| ≤ C δ^{1/4} (1 + v)^{−2}` for `v ≥ 0`. -/
theorem exists_abs_coprimeProfile_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℕ, δ ≠ 0 → ∀ v : ℝ, 0 ≤ v →
      |coprimeProfile δ v| ≤ C * (δ : ℝ) ^ (1 / 4 : ℝ) * ((1 + v) ^ 2)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_abs_coprimeMoebiusSigmaSum_le
  have hC0 : 0 ≤ C := by
    have h := hC 1 one_ne_zero 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one, Real.log_one, add_zero, one_pow,
      div_one] at h
    exact (abs_nonneg _).trans h
  refine ⟨100 / 9 * C, by positivity, fun δ hδ v hv => ?_⟩
  have hX1 : 1 ≤ ⌊Real.exp v⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp hv)
  have h := hC δ hδ _ hX1
  have hl := three_tenths_mul_le_one_add_log_floor_exp hv
  have hpos : 0 < 3 / 10 * (1 + v) := by positivity
  have hsq : (3 / 10 * (1 + v)) ^ 2 ≤ (1 + Real.log ⌊Real.exp v⌋₊) ^ 2 :=
    pow_le_pow_left₀ hpos.le hl 2
  have hd : 0 ≤ C * (δ : ℝ) ^ (1 / 4 : ℝ) := by positivity
  calc |coprimeProfile δ v| ≤ C * (δ : ℝ) ^ (1 / 4 : ℝ) / (1 + Real.log ⌊Real.exp v⌋₊) ^ 2 := h
    _ ≤ C * (δ : ℝ) ^ (1 / 4 : ℝ) / (3 / 10 * (1 + v)) ^ 2 :=
        div_le_div_of_nonneg_left hd (by positivity) hsq
    _ = 100 / 9 * C * (δ : ℝ) ^ (1 / 4 : ℝ) * ((1 + v) ^ 2)⁻¹ := by
        rw [mul_pow]; field_simp; ring

/-- `(1 + v)^{−2}` is integrable on `(0, ∞)`. -/
theorem integrableOn_inv_one_add_sq : IntegrableOn (fun v : ℝ => ((1 + v) ^ 2)⁻¹) (Ioi 0) := by
  have h := integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num) (by norm_num)
  refine h.congr_fun (fun v hv => ?_) measurableSet_Ioi
  have hv' : 0 < v + 1 := by simp only [Set.mem_Ioi] at hv; linarith
  show (v + 1) ^ (-2 : ℝ) = ((1 + v) ^ 2)⁻¹
  rw [Real.rpow_neg hv'.le, add_comm v 1, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- `(1 + v)^{−4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_inv_one_add_pow_four :
    IntegrableOn (fun v : ℝ => ((1 + v) ^ 2)⁻¹ ^ 2) (Ioi 0) := by
  refine Integrable.mono' integrableOn_inv_one_add_sq ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    simp only [Set.mem_Ioi] at hv
    have h1 : 0 < (1 + v) ^ 2 := by positivity
    have h2 : 1 ≤ (1 + v) ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ((1 + v) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
    calc ((1 + v) ^ 2)⁻¹ ^ 2 = ((1 + v) ^ 2)⁻¹ * ((1 + v) ^ 2)⁻¹ := sq _
      _ ≤ 1 * ((1 + v) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right this (by positivity)
      _ = ((1 + v) ^ 2)⁻¹ := one_mul _

/-- The profile vanishes off `[0, ∞)`, so its square is supported on `Ioi 0` up to a point. -/
theorem integral_coprimeProfile_sq_eq_setIntegral (δ : ℕ) :
    coprimeEnergy δ = ∫ v in Ioi 0, coprimeProfile δ v ^ 2 := by
  rw [coprimeEnergy, ← integral_Ici_eq_integral_Ioi]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
  simp only [Set.mem_Ici, not_le] at hv
  rw [coprimeProfile_of_neg δ hv]; ring

/-- The squared profile is integrable, with `∫ g_δ² ≤ C² δ^{1/2} K`. -/
theorem exists_integrable_coprimeProfile_sq :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℕ, δ ≠ 0 →
      Integrable (fun v => coprimeProfile δ v ^ 2) ∧ coprimeEnergy δ ≤ K * (δ : ℝ) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_coprimeProfile_le
  set I := ∫ v in Ioi (0 : ℝ), ((1 + v) ^ 2)⁻¹ ^ 2 with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun v _ => by positivity
  refine ⟨C ^ 2 * I, by positivity, fun δ hδ => ?_⟩
  have hδq : ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (δ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hbound : ∀ v ∈ Ioi (0 : ℝ), ‖coprimeProfile δ v ^ 2‖ ≤
      C ^ 2 * (δ : ℝ) ^ (1 / 2 : ℝ) * ((1 + v) ^ 2)⁻¹ ^ 2 := by
    intro v hv
    have h := hC δ hδ v (le_of_lt hv)
    rw [Real.norm_eq_abs, abs_pow, ← hδq]
    have : |coprimeProfile δ v| ^ 2 ≤ (C * (δ : ℝ) ^ (1 / 4 : ℝ) * ((1 + v) ^ 2)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    calc |coprimeProfile δ v| ^ 2 ≤ (C * (δ : ℝ) ^ (1 / 4 : ℝ) * ((1 + v) ^ 2)⁻¹) ^ 2 := this
      _ = C ^ 2 * ((δ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * ((1 + v) ^ 2)⁻¹ ^ 2 := by ring
  have hmeas : AEStronglyMeasurable (fun v => coprimeProfile δ v ^ 2) (volume.restrict (Ioi 0)) :=
    ((measurable_coprimeProfile δ).pow_const 2).aestronglyMeasurable
  have hintOn : IntegrableOn (fun v => coprimeProfile δ v ^ 2) (Ioi 0) :=
    (integrableOn_inv_one_add_pow_four.const_mul (C ^ 2 * (δ : ℝ) ^ (1 / 2 : ℝ))).mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  have hint : Integrable (fun v => coprimeProfile δ v ^ 2) := by
    rw [← integrableOn_univ, ← Ioi_union_Iic (a := (0 : ℝ))]
    refine hintOn.union ?_
    have hae : (fun v => coprimeProfile δ v ^ 2) =ᵐ[volume.restrict (Iic 0)] 0 := by
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Iic]
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with v hv hv'
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
      simp only [Set.mem_Iic] at hv'
      simp [coprimeProfile_of_neg δ (lt_of_le_of_ne hv' hv)]
    exact (integrable_zero _ _ _).congr hae.symm
  refine ⟨hint, ?_⟩
  rw [integral_coprimeProfile_sq_eq_setIntegral]
  calc ∫ v in Ioi 0, coprimeProfile δ v ^ 2
      ≤ ∫ v in Ioi 0, C ^ 2 * (δ : ℝ) ^ (1 / 2 : ℝ) * ((1 + v) ^ 2)⁻¹ ^ 2 := by
        refine setIntegral_mono_on hintOn
          (integrableOn_inv_one_add_pow_four.const_mul _) measurableSet_Ioi fun v hv => ?_
        have := hbound v hv
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
    _ = C ^ 2 * I * (δ : ℝ) ^ (1 / 2 : ℝ) := by
        rw [integral_const_mul, hI]; ring

/-! ### The logarithmic integral of a step function -/

/-- The pieces `[log(k+1), log(k+2))` on which `⌊e^u⌋₊ = k + 1`. -/
theorem natFloor_exp_eq_of_mem {k : ℕ} {u : ℝ}
    (hu : u ∈ Ico (Real.log (k + 1)) (Real.log ((k + 1 : ℕ) + 1))) : ⌊Real.exp u⌋₊ = k + 1 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hk2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
  obtain ⟨h1, h2⟩ := hu
  rw [Nat.floor_eq_iff (Real.exp_pos u).le]
  constructor
  · push_cast
    calc (k : ℝ) + 1 = Real.exp (Real.log (k + 1)) := (Real.exp_log hk).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr h1
  · calc Real.exp u < Real.exp (Real.log ((k + 1 : ℕ) + 1)) := Real.exp_lt_exp.mpr h2
      _ = ((k + 1 : ℕ) : ℝ) + 1 := Real.exp_log hk2

theorem iUnion_Ico_log_succ :
    (⋃ k : ℕ, Ico (Real.log (k + 1)) (Real.log ((k + 1 : ℕ) + 1))) = Ici 0 := by
  ext u
  simp only [mem_iUnion, Set.mem_Ici]
  constructor
  · rintro ⟨k, h1, -⟩
    exact (Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).trans h1
  · intro hu
    set X := ⌊Real.exp u⌋₊ with hX
    have hX1 : 1 ≤ X := Nat.le_floor (by simpa using Real.one_le_exp hu)
    refine ⟨X - 1, ?_, ?_⟩
    · have hcast : ((X - 1 : ℕ) : ℝ) + 1 = X := by
        rw [Nat.cast_sub hX1]; push_cast; ring
      rw [hcast]
      have := Nat.floor_le (Real.exp_pos u).le
      rw [← hX] at this
      calc Real.log X ≤ Real.log (Real.exp u) :=
            Real.log_le_log (by exact_mod_cast hX1) this
        _ = u := Real.log_exp u
    · have hcast : ((X - 1 + 1 : ℕ) : ℝ) + 1 = X + 1 := by
        rw [Nat.sub_add_cancel hX1]
      rw [hcast]
      have := Nat.lt_floor_add_one (Real.exp u)
      rw [← hX] at this
      calc u = Real.log (Real.exp u) := (Real.log_exp u).symm
        _ < Real.log (X + 1) := Real.log_lt_log (Real.exp_pos u) this

theorem log_succ_sub_log (k : ℕ) :
    Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1) = Real.log (1 + 1 / ((k + 1 : ℕ) : ℝ)) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [← Real.log_div (by positivity) hk.ne']
  congr 1
  push_cast
  field_simp

theorem log_one_add_one_div_nonneg (j : ℕ) : 0 ≤ Real.log (1 + 1 / (j : ℝ)) :=
  Real.log_nonneg (by have : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
                      linarith)

/-- **Logarithmic integral of a step function.** If `Σ |a(j)| log(1 + 1/j) < ∞`, then
`∫_{(0,∞)} a(⌊e^u⌋₊) du = Σ_j a(j) log(1 + 1/j)`. -/
theorem integral_Ioi_natFloor_exp {a : ℕ → ℝ}
    (ha : Summable fun j : ℕ => |a j| * Real.log (1 + 1 / (j : ℝ))) :
    ∫ u in Ioi 0, a ⌊Real.exp u⌋₊ = ∑' j : ℕ, a j * Real.log (1 + 1 / (j : ℝ)) := by
  set s : ℕ → Set ℝ := fun k => Ico (Real.log (k + 1)) (Real.log ((k + 1 : ℕ) + 1)) with hs
  have hmono : Monotone fun k : ℕ => Real.log (k + 1) := fun i j hij =>
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  have hdisj : Pairwise (Disjoint on s) := by
    have key : ∀ i j : ℕ, i < j → ∀ u, u ∈ s i → u ∉ s j := by
      intro i j hij u hu hu'
      have hle : Real.log (((i + 1 : ℕ) : ℝ) + 1) ≤ Real.log (j + 1) := by
        have := hmono (Nat.succ_le_of_lt hij)
        simpa using this
      linarith [hu.2, hu'.1]
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro u hu hu'
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h u hu hu'
    · exact key j i h u hu' hu
  have hpiece : ∀ k : ℕ, ∫ u in s k, a ⌊Real.exp u⌋₊ =
      a (k + 1) * Real.log (1 + 1 / ((k + 1 : ℕ) : ℝ)) := by
    intro k
    rw [setIntegral_congr_fun measurableSet_Ico (fun u hu => by
      rw [natFloor_exp_eq_of_mem hu]), setIntegral_const, smul_eq_mul,
      Real.volume_real_Ico_of_le (by linarith [hmono (Nat.le_succ k)]), log_succ_sub_log, mul_comm]
  have hnorm : ∀ k : ℕ, ∫ u in s k, ‖a ⌊Real.exp u⌋₊‖ =
      |a (k + 1)| * Real.log (1 + 1 / ((k + 1 : ℕ) : ℝ)) := by
    intro k
    rw [setIntegral_congr_fun measurableSet_Ico (fun u hu => by
      rw [natFloor_exp_eq_of_mem hu]), setIntegral_const, smul_eq_mul,
      Real.volume_real_Ico_of_le (by linarith [hmono (Nat.le_succ k)]), log_succ_sub_log, mul_comm,
      Real.norm_eq_abs]
  have hint : IntegrableOn (fun u => a ⌊Real.exp u⌋₊) (⋃ k, s k) := by
    refine integrableOn_iUnion_of_summable_integral_norm (fun k => ?_) ?_
    · refine (integrableOn_const (C := a (k + 1)) (by simp [hs, Real.volume_Ico])).congr_fun
        (fun u hu => by rw [natFloor_exp_eq_of_mem hu]) measurableSet_Ico
    · simp_rw [hnorm]
      exact (summable_nat_add_iff 1).mpr ha
  rw [← integral_Ici_eq_integral_Ioi, ← iUnion_Ico_log_succ]
  refine (integral_iUnion (fun k => measurableSet_Ico) hdisj hint).trans ?_
  refine (tsum_congr hpiece).trans ?_
  have hsum : Summable fun j : ℕ => a j * Real.log (1 + 1 / (j : ℝ)) := by
    refine ha.of_norm_bounded fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (log_one_add_one_div_nonneg j)]
  rw [hsum.tsum_eq_zero_add, Nat.cast_zero, div_zero, add_zero, Real.log_one, mul_zero, zero_add]

/-! ### The coprimality sieve along the logarithmic scale -/

/-- `g_δ(u − log δ) = T_δ(⌊e^u⌋₊ / δ)`. -/
theorem coprimeProfile_sub_log {δ : ℕ} (hδ : δ ≠ 0) (u : ℝ) :
    coprimeProfile δ (u - Real.log δ) = coprimeMoebiusSigmaSum δ (⌊Real.exp u⌋₊ / δ) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  rw [coprimeProfile, Real.exp_sub, Real.exp_log hδR, Nat.floor_div_natCast]

/-- The `δ`-th term of the sieve along the logarithmic scale. -/
def sieveTerm (δ : ℕ) (u : ℝ) : ℝ :=
  if δ = 0 then 0 else (moebius δ : ℝ) * moebiusSigma δ ^ 2 * coprimeProfile δ (u - Real.log δ) ^ 2

/-- **The sieve along the logarithmic scale.**
`S(⌊e^u⌋₊) = Σ_{δ ≥ 1} μ(δ) w(δ)² g_δ(u − log δ)²`. -/
theorem coprimePairMoebiusSigmaSum_natFloor_exp (u : ℝ) :
    coprimePairMoebiusSigmaSum ⌊Real.exp u⌋₊ = ∑' δ : ℕ, sieveTerm δ u := by
  set X := ⌊Real.exp u⌋₊ with hX
  rw [coprimePairMoebiusSigmaSum_eq, tsum_eq_sum (s := Finset.Icc 1 X)]
  · refine Finset.sum_congr rfl fun δ hδ => ?_
    have hδ0 : δ ≠ 0 := by have := (Finset.mem_Icc.mp hδ).1; omega
    rw [sieveTerm, if_neg hδ0, coprimeProfile_sub_log hδ0, ← hX]
    ring
  · intro δ hδ
    rw [sieveTerm]
    split_ifs with h0
    · rfl
    · have hlt : X < δ := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hδ
        omega
      rw [coprimeProfile_sub_log h0, ← hX, Nat.div_eq_of_lt hlt, coprimeMoebiusSigmaSum_zero]
      ring

theorem sieveTerm_eq_zero_of_neg (δ : ℕ) {u : ℝ} (hu : u < 0) : sieveTerm δ u = 0 := by
  rw [sieveTerm]
  split_ifs with h0
  · rfl
  · have hlog : 0 ≤ Real.log δ := Real.log_natCast_nonneg δ
    rw [coprimeProfile_of_neg δ (by linarith)]; ring

theorem measurable_sieveTerm (δ : ℕ) : Measurable (sieveTerm δ) := by
  unfold sieveTerm
  split_ifs
  · exact measurable_const
  · exact measurable_const.mul
      (((measurable_coprimeProfile δ).comp (measurable_id.sub_const _)).pow_const 2)

/-- `∫_{(0,∞)} μ(δ) w(δ)² g_δ(u − log δ)² du = μ(δ) w(δ)² ∫ g_δ²`. -/
theorem setIntegral_sieveTerm {δ : ℕ} (hδ : δ ≠ 0) :
    ∫ u in Ioi 0, sieveTerm δ u = (moebius δ : ℝ) * moebiusSigma δ ^ 2 * coprimeEnergy δ := by
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
  · simp only [sieveTerm, if_neg hδ]
    rw [integral_const_mul, coprimeEnergy,
      integral_sub_right_eq_self (fun v => coprimeProfile δ v ^ 2) (Real.log δ)]
  · filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu hu'
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
    simp only [Set.mem_Ioi, not_lt] at hu'
    exact sieveTerm_eq_zero_of_neg δ (lt_of_le_of_ne hu' hu)

theorem integrable_sieveTerm {δ : ℕ} (hint : δ ≠ 0 → Integrable fun v => coprimeProfile δ v ^ 2) :
    Integrable (sieveTerm δ) := by
  unfold sieveTerm
  split_ifs with h0
  · exact integrable_zero _ _ _
  · exact ((hint h0).comp_sub_right (Real.log δ)).const_mul _

/-! ### The slope as a signed sum of energies -/

/-- `|w(δ)|² ≤ δ^{−2}`. -/
theorem moebiusSigma_sq_le (δ : ℕ) : moebiusSigma δ ^ 2 ≤ ((δ : ℝ) ^ 2)⁻¹ := by
  have h := abs_moebiusSigma_le δ
  rw [← sq_abs]
  exact (pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (inv_pow _ _)

theorem summable_abs_coprimePairMoebiusSigmaSum_mul_log :
    Summable fun j : ℕ => |coprimePairMoebiusSigmaSum j| * Real.log (1 + 1 / (j : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_abs_coprimePairMoebiusSigmaSum_le
  refine (summable_inv_mul_one_add_log_sq.mul_left C).of_nonneg_of_le
    (fun j => mul_nonneg (abs_nonneg _) (log_one_add_one_div_nonneg j)) fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hl0 := Real.log_nonneg hjR
    have hlog : Real.log (1 + 1 / (j : ℝ)) ≤ 1 / j := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / j by positivity)
      linarith
    have hA := hC j hj
    have h4 : (1 + Real.log j) ^ 2 ≤ (1 + Real.log j) ^ 4 := by
      have : 1 ≤ 1 + Real.log j := by linarith
      exact pow_le_pow_right₀ this (by norm_num)
    have hA' : |coprimePairMoebiusSigmaSum j| ≤ C / (1 + Real.log j) ^ 2 := by
      have hC0 : 0 ≤ C := by
        have h1 := hC 1 le_rfl
        simp only [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
        exact (abs_nonneg _).trans h1
      exact hA.trans (div_le_div_of_nonneg_left hC0 (by positivity) h4)
    calc |coprimePairMoebiusSigmaSum j| * Real.log (1 + 1 / (j : ℝ))
        ≤ C / (1 + Real.log j) ^ 2 * (1 / j) :=
          mul_le_mul hA' hlog (log_one_add_one_div_nonneg j) ((abs_nonneg _).trans hA')
      _ = C * ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ := by field_simp

/-- **The cofinal slope is a signed sum of coprime energies.**
`κ = ρ Σ_{δ ≥ 1} μ(δ) w(δ)² ∫ g_δ²`, absolutely convergent. -/
theorem cofinalMobiusSlope_eq_tsum_coprimeEnergy :
    (Summable fun δ : ℕ => |moebiusSigma δ ^ 2 * coprimeEnergy δ|) ∧
      cofinalMobiusSlope = RHTower.Sieve.squarefreeDensity *
        ∑' δ : ℕ, (if δ = 0 then 0 else (moebius δ : ℝ) * moebiusSigma δ ^ 2 * coprimeEnergy δ) := by
  obtain ⟨K, hK0, hK⟩ := exists_integrable_coprimeProfile_sq
  -- the energies against the weights `w(δ)² ≤ δ^{−2}` are summable
  have hE0 : ∀ δ, 0 ≤ coprimeEnergy δ := fun δ => integral_nonneg fun v => sq_nonneg _
  have hdom : ∀ δ : ℕ, |moebiusSigma δ ^ 2 * coprimeEnergy δ| ≤ K * (δ : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro δ
    rcases Nat.eq_zero_or_pos δ with rfl | hδ
    · simp [moebiusSigma]
    · have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hE0 δ))]
      calc moebiusSigma δ ^ 2 * coprimeEnergy δ ≤ ((δ : ℝ) ^ 2)⁻¹ * (K * (δ : ℝ) ^ (1 / 2 : ℝ)) :=
            mul_le_mul (moebiusSigma_sq_le δ) (hK δ hδ.ne').2 (hE0 δ) (by positivity)
        _ = K * (δ : ℝ) ^ (-(3 / 2 : ℝ)) := by
            rw [show (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) - 2 by norm_num, Real.rpow_sub hδR,
              Real.rpow_two]
            ring
  have hsumE : Summable fun δ : ℕ => |moebiusSigma δ ^ 2 * coprimeEnergy δ| :=
    ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left K).of_nonneg_of_le (fun _ => abs_nonneg _) hdom
  refine ⟨hsumE, ?_⟩
  rw [cofinalMobiusSlope, ← integral_Ioi_natFloor_exp summable_abs_coprimePairMoebiusSigmaSum_mul_log]
  congr 1
  simp_rw [coprimePairMoebiusSigmaSum_natFloor_exp]
  have hint : ∀ δ : ℕ, Integrable (sieveTerm δ) (volume.restrict (Ioi 0)) :=
    fun δ => (integrable_sieveTerm fun h => (hK δ h).1).restrict
  have hnorm : ∀ δ : ℕ, ∫ u in Ioi 0, ‖sieveTerm δ u‖ ≤ |moebiusSigma δ ^ 2 * coprimeEnergy δ| := by
    intro δ
    rcases Nat.eq_zero_or_pos δ with rfl | hδ
    · have h0 : ∀ u, sieveTerm 0 u = 0 := fun u => by simp [sieveTerm]
      simp only [h0, norm_zero, integral_zero]
      exact abs_nonneg _
    · have hδ0 : δ ≠ 0 := hδ.ne'
      have hle : ∀ u, ‖sieveTerm δ u‖ = moebiusSigma δ ^ 2 * |(moebius δ : ℝ)| *
          coprimeProfile δ (u - Real.log δ) ^ 2 := by
        intro u
        rw [sieveTerm, if_neg hδ0, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_nonneg (sq_nonneg (moebiusSigma δ)),
          abs_of_nonneg (sq_nonneg (coprimeProfile δ (u - Real.log δ)))]
        ring
      have hμ : |(moebius δ : ℝ)| ≤ 1 := by
        have := abs_moebius_le_one (n := δ)
        exact_mod_cast this
      simp_rw [hle]
      calc ∫ u in Ioi 0, moebiusSigma δ ^ 2 * |(moebius δ : ℝ)| *
            coprimeProfile δ (u - Real.log δ) ^ 2
          ≤ ∫ u, moebiusSigma δ ^ 2 * |(moebius δ : ℝ)| * coprimeProfile δ (u - Real.log δ) ^ 2 :=
            setIntegral_le_integral (((hK δ hδ0).1.comp_sub_right _).const_mul _)
              (Eventually.of_forall fun u => by positivity)
        _ = moebiusSigma δ ^ 2 * |(moebius δ : ℝ)| * coprimeEnergy δ := by
            rw [integral_const_mul, coprimeEnergy,
              integral_sub_right_eq_self (fun v => coprimeProfile δ v ^ 2) (Real.log δ)]
        _ ≤ |moebiusSigma δ ^ 2 * coprimeEnergy δ| := by
            rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hE0 δ))]
            have := mul_nonneg (sq_nonneg (moebiusSigma δ)) (hE0 δ)
            nlinarith [abs_nonneg (moebius δ : ℝ)]
  have hsumN : Summable fun δ : ℕ => ∫ u in Ioi 0, ‖sieveTerm δ u‖ :=
    hsumE.of_nonneg_of_le (fun δ => integral_nonneg fun _ => norm_nonneg _) hnorm
  rw [← integral_tsum_of_summable_integral_norm hint hsumN]
  refine tsum_congr fun δ => ?_
  rcases Nat.eq_zero_or_pos δ with rfl | hδ
  · simp [sieveTerm]
  · rw [if_neg hδ.ne', setIntegral_sieveTerm hδ.ne']

end GaloisForLFunctions.BezoutValuationIncidence
