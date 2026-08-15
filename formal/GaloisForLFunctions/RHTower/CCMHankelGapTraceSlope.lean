import GaloisForLFunctions.RHTower.CCMTransverseIndexTraceSlopeCoercivity

/-!
# The residue energy is an initial Hankel gap-trace slope

For an anti-causal residue profile `ℓ` on the half-line, the Hilbert–Schmidt energy of the shifted
Hankel operator with kernel `ℓ(u + x + y)` is the first-moment tail

`F_ℓ(u) = ∫_u^∞ (t − u) |ℓ(t)|² dt`.

Splitting the tail at `u + h` gives the exact decomposition
`F_ℓ(u) − F_ℓ(u+h) = h T_ℓ(u+h) + ∫_{(u,u+h]} (t−u)|ℓ|²`, whose remainder is squeezed between `0`
and `h (T_ℓ(u) − T_ℓ(u+h))`.  Hence the difference quotient is sandwiched between the two tail
energies, and right continuity of the tail energy identifies the initial slope with `−‖ℓ‖₂²`.

No boundary value `ℓ(0)` and no derivative of `ℓ` enters.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-- The leakage density of a residue profile. -/
def leakDensity (ℓ : ℝ → ℂ) (t : ℝ) : ℝ := ‖ℓ t‖ ^ 2

theorem leakDensity_nonneg (ℓ : ℝ → ℂ) (t : ℝ) : 0 ≤ leakDensity ℓ t := by
  unfold leakDensity; positivity

/-- The tail leakage energy `T_ℓ(u) = ∫_u^∞ |ℓ|²`. -/
def tailLeakEnergy (ℓ : ℝ → ℂ) (u : ℝ) : ℝ := ∫ t in Ioi u, leakDensity ℓ t

/-- The shifted Hankel gap profile `F_ℓ(u) = ∫_u^∞ (t − u) |ℓ|²`. -/
def hankelGapProfile (ℓ : ℝ → ℂ) (u : ℝ) : ℝ := ∫ t in Ioi u, (t - u) * leakDensity ℓ t

/-- The admissible class of residue profiles: measurable on the half-line and with finite first
leakage moment.  This is hypothesis `(1)` of the card. -/
structure LeakProfile (ℓ : ℝ → ℂ) : Prop where
  meas : AEStronglyMeasurable ℓ (volume.restrict (Ioi (0 : ℝ)))
  moment : IntegrableOn (fun t => (1 + t) * leakDensity ℓ t) (Ioi (0 : ℝ)) volume

variable {ℓ : ℝ → ℂ}

theorem LeakProfile.densityMeas (h : LeakProfile ℓ) :
    AEStronglyMeasurable (leakDensity ℓ) (volume.restrict (Ioi (0 : ℝ))) := by
  unfold leakDensity
  exact (h.meas.norm.pow 2)

theorem LeakProfile.integrable (h : LeakProfile ℓ) :
    IntegrableOn (leakDensity ℓ) (Ioi (0 : ℝ)) volume := by
  refine Integrable.mono' h.moment h.densityMeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (leakDensity_nonneg ℓ t)]
  nlinarith [leakDensity_nonneg ℓ t]

theorem integrableOn_shifted (h : LeakProfile ℓ) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (fun t => (t - u) * leakDensity ℓ t) (Ioi u) volume := by
  refine Integrable.mono' (h.moment.mono_set (Ioi_subset_Ioi hu)) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop : Continuous fun t : ℝ => t - u)).mul
      (h.densityMeas.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi hu) le_rfl))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htu : u < t := ht
    have hd := leakDensity_nonneg ℓ t
    rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith

theorem integrableOn_tail (h : LeakProfile ℓ) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (leakDensity ℓ) (Ioi u) volume :=
  h.integrable.mono_set (Ioi_subset_Ioi hu)

/-! ## The exact splitting identity -/

theorem hankelGapProfile_sub (h : LeakProfile ℓ) {u k : ℝ} (hu : 0 ≤ u) (huk : u < k) :
    hankelGapProfile ℓ u - hankelGapProfile ℓ k
      = (k - u) * tailLeakEnergy ℓ k + ∫ t in Ioc u k, (t - u) * leakDensity ℓ t := by
  have hk : 0 ≤ k := le_trans hu (le_of_lt huk)
  have hsplit : Ioi u = Ioc u k ∪ Ioi k := (Ioc_union_Ioi_eq_Ioi (le_of_lt huk)).symm
  have hdisj : Disjoint (Ioc u k) (Ioi k) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn (fun t => (t - u) * leakDensity ℓ t) (Ioc u k) volume :=
    (integrableOn_shifted h hu).mono_set Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (fun t => (t - u) * leakDensity ℓ t) (Ioi k) volume :=
    (integrableOn_shifted h hu).mono_set (Ioi_subset_Ioi (le_of_lt huk))
  have hsum : hankelGapProfile ℓ u
      = (∫ t in Ioc u k, (t - u) * leakDensity ℓ t) + ∫ t in Ioi k, (t - u) * leakDensity ℓ t := by
    unfold hankelGapProfile
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hint1 hint2]
  have hshift : (∫ t in Ioi k, (t - u) * leakDensity ℓ t)
      = hankelGapProfile ℓ k + (k - u) * tailLeakEnergy ℓ k := by
    unfold hankelGapProfile tailLeakEnergy
    have hcongr : ∀ t : ℝ, (t - u) * leakDensity ℓ t
        = (t - k) * leakDensity ℓ t + (k - u) * leakDensity ℓ t := by
      intro t; ring
    rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => hcongr t]
    rw [integral_add (integrableOn_shifted h hk)
      ((integrableOn_tail h hk).const_mul _)]
    rw [integral_const_mul]
  rw [hsum, hshift]
  ring

/-! ## The difference-quotient sandwich -/

theorem tailLeakEnergy_sub (h : LeakProfile ℓ) {u k : ℝ} (hu : 0 ≤ u) (huk : u < k) :
    tailLeakEnergy ℓ u - tailLeakEnergy ℓ k = ∫ t in Ioc u k, leakDensity ℓ t := by
  have hsplit : Ioi u = Ioc u k ∪ Ioi k := (Ioc_union_Ioi_eq_Ioi (le_of_lt huk)).symm
  have hdisj : Disjoint (Ioc u k) (Ioi k) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn (leakDensity ℓ) (Ioc u k) volume :=
    (integrableOn_tail h hu).mono_set Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (leakDensity ℓ) (Ioi k) volume :=
    (integrableOn_tail h hu).mono_set (Ioi_subset_Ioi (le_of_lt huk))
  unfold tailLeakEnergy
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hint1 hint2]
  ring

theorem remainder_nonneg (ℓ : ℝ → ℂ) (u k : ℝ) :
    0 ≤ ∫ t in Ioc u k, (t - u) * leakDensity ℓ t := by
  refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
  have h1 : u ≤ t := le_of_lt ht.1
  have := leakDensity_nonneg ℓ t
  nlinarith

theorem remainder_le (h : LeakProfile ℓ) {u k : ℝ} (hu : 0 ≤ u) :
    (∫ t in Ioc u k, (t - u) * leakDensity ℓ t)
      ≤ (k - u) * ∫ t in Ioc u k, leakDensity ℓ t := by
  have hint1 : IntegrableOn (fun t => (t - u) * leakDensity ℓ t) (Ioc u k) volume :=
    (integrableOn_shifted h hu).mono_set Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (leakDensity ℓ) (Ioc u k) volume :=
    (integrableOn_tail h hu).mono_set Ioc_subset_Ioi_self
  rw [← integral_const_mul]
  refine setIntegral_mono_on hint1 (hint2.const_mul _) measurableSet_Ioc fun t ht => ?_
  have h2 : t ≤ k := ht.2
  have := leakDensity_nonneg ℓ t
  nlinarith

/-- **The sandwich.**  The backward difference quotient of the gap profile lies between the two tail
energies. -/
theorem tailLeakEnergy_le_diff_quotient (h : LeakProfile ℓ) {u k : ℝ} (hu : 0 ≤ u) (huk : u < k) :
    tailLeakEnergy ℓ k ≤ (hankelGapProfile ℓ u - hankelGapProfile ℓ k) / (k - u) ∧
      (hankelGapProfile ℓ u - hankelGapProfile ℓ k) / (k - u) ≤ tailLeakEnergy ℓ u := by
  have hpos : 0 < k - u := by linarith
  have hid := hankelGapProfile_sub h hu huk
  have hrem0 := remainder_nonneg ℓ u k
  have hrem1 := remainder_le (k := k) h hu
  have hts := tailLeakEnergy_sub h hu huk
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith
  · rw [div_le_iff₀ hpos]
    nlinarith

/-! ## Right continuity of the tail energy -/

theorem tendsto_tailLeakEnergy_right (h : LeakProfile ℓ) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun k : ℝ => tailLeakEnergy ℓ k) (𝓝[>] u) (𝓝 (tailLeakEnergy ℓ u)) := by
  have hmeas : Tendsto (fun k : ℝ => (volume.restrict (Ioi (0 : ℝ))) (Ioc u k)) (𝓝[>] u)
      (𝓝 0) := by
    have hle : ∀ k : ℝ, (volume.restrict (Ioi (0 : ℝ))) (Ioc u k) ≤ ENNReal.ofReal (k - u) := by
      intro k
      calc (volume.restrict (Ioi (0 : ℝ))) (Ioc u k)
          ≤ volume (Ioc u k) := Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal (k - u) := Real.volume_Ioc
    have hzero : Tendsto (fun k : ℝ => ENNReal.ofReal (k - u)) (𝓝[>] u) (𝓝 0) := by
      have hcont : Tendsto (fun k : ℝ => k - u) (𝓝[>] u) (𝓝 0) := by
        have h0 : Tendsto (fun k : ℝ => k - u) (𝓝 u) (𝓝 (u - u)) :=
          (continuous_sub_right u).tendsto u
        rw [sub_self] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have hcomp := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hcont
      simpa [Function.comp_def] using hcomp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall hle)
  have habs := h.integrable.tendsto_setIntegral_nhds_zero (l := 𝓝[>] u) hmeas
  have hset : ∀ k : ℝ, u < k → (∫ t in Ioc u k, leakDensity ℓ t ∂(volume.restrict (Ioi (0 : ℝ))))
      = ∫ t in Ioc u k, leakDensity ℓ t := by
    intro k hk
    have hsub : Ioc u k ⊆ Ioi (0 : ℝ) := fun t ht => lt_of_le_of_lt hu ht.1
    rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub]
  have hdiff : Tendsto (fun k : ℝ => tailLeakEnergy ℓ u - tailLeakEnergy ℓ k) (𝓝[>] u) (𝓝 0) := by
    refine habs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with k hk
    rw [hset k hk, ← tailLeakEnergy_sub h hu hk]
  have := (tendsto_const_nhds (x := tailLeakEnergy ℓ u) (f := 𝓝[>] u)).sub hdiff
  simpa using this

/-- **Equations (5)–(6).**  The backward difference quotient of the gap profile converges to the tail
energy: the initial trace slope is the residue energy. -/
theorem tendsto_diff_quotient_hankelGapProfile (h : LeakProfile ℓ) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun k : ℝ => (hankelGapProfile ℓ u - hankelGapProfile ℓ k) / (k - u)) (𝓝[>] u)
      (𝓝 (tailLeakEnergy ℓ u)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_tailLeakEnergy_right h hu)
    tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (tailLeakEnergy_le_diff_quotient h hu hk).1
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (tailLeakEnergy_le_diff_quotient h hu hk).2

/-- **Equation (6) at the origin.**  The negative initial slope of the gap profile is `‖ℓ‖₂²`. -/
theorem tendsto_initial_slope (h : LeakProfile ℓ) :
    Tendsto (fun k : ℝ => (hankelGapProfile ℓ 0 - hankelGapProfile ℓ k) / k) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Ioi (0 : ℝ), leakDensity ℓ t)) := by
  have := tendsto_diff_quotient_hankelGapProfile h (le_refl (0 : ℝ))
  simpa [tailLeakEnergy] using this

/-! ## Monotonicity of the gap profile -/

theorem hankelGapProfile_antitone (h : LeakProfile ℓ) {u k : ℝ} (hu : 0 ≤ u) (huk : u ≤ k) :
    hankelGapProfile ℓ k ≤ hankelGapProfile ℓ u := by
  rcases eq_or_lt_of_le huk with rfl | hlt
  · exact le_rfl
  · have hid := hankelGapProfile_sub h hu hlt
    have hrem0 := remainder_nonneg ℓ u k
    have htail : 0 ≤ tailLeakEnergy ℓ k :=
      setIntegral_nonneg measurableSet_Ioi fun t _ => leakDensity_nonneg ℓ t
    nlinarith

/-! ## The divisor and pole profiles -/

theorem exists_uniform_re_bound {r : ℕ} {lam : Fin r → ℂ} (hlam : ∀ j, 0 < (lam j).re) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, c ≤ (lam j).re := by
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact ⟨1, one_pos, fun j => absurd j.2 (by omega)⟩
  · obtain ⟨j₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin r))
      (fun j => (lam j).re) ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨(lam j₀).re, hlam j₀, fun j => hmin j (Finset.mem_univ j)⟩

theorem integrableOn_one_add_mul_exp_neg {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (1 + t) * Real.exp (-b * t)) (Ioi (0 : ℝ)) volume := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Ioi (0 : ℝ)) volume :=
    exp_neg_integrableOn_Ioi 0 hb
  have h2 : IntegrableOn (fun t : ℝ => t * Real.exp (-b * t)) (Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := b)
      (by norm_num) (le_refl (1 : ℝ)) hb
    refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro t _
    simp only [Real.rpow_one]
  refine MeasureTheory.IntegrableOn.congr_fun (h1.add h2) ?_ measurableSet_Ioi
  intro t _
  simp only [Pi.add_apply]
  ring

theorem norm_divisorPacketProfile_le {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ} {c : ℝ}
    (hc : ∀ j, c ≤ (lam j).re) {t : ℝ} (ht : 0 ≤ t) :
    ‖divisorPacketProfile lam m t‖ ≤ 2 * (∑ j, (m j : ℝ)) * Real.exp (-c * t) := by
  unfold divisorPacketProfile
  rw [norm_mul]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  have hbound : ‖∑ j, (m j : ℂ) * Complex.exp (-(lam j * (t : ℂ)))‖
      ≤ (∑ j, (m j : ℝ)) * Real.exp (-c * t) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(lam j * (t : ℂ))).re = -((lam j).re * t) := by
      simp [Complex.mul_re]
    rw [hre]
    have hexp : Real.exp (-((lam j).re * t)) ≤ Real.exp (-c * t) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hc j]
    have hm : ‖(m j : ℂ)‖ = (m j : ℝ) := by
      rw [Complex.norm_natCast]
    rw [hm]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  nlinarith [hbound, Real.exp_pos (-c * t),
    Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (Nat.cast_nonneg (m j) : (0:ℝ) ≤ (m j : ℝ)))]

theorem leakProfile_divisorPacket {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) : LeakProfile (divisorPacketProfile lam m) := by
  obtain ⟨c, hc0, hc⟩ := exists_uniform_re_bound hlam
  set M : ℝ := 2 * ∑ j, (m j : ℝ) with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (0:ℝ) ≤ ∑ j, (m j : ℝ) :=
      Finset.sum_nonneg fun j _ => Nat.cast_nonneg (m j)
    linarith
  refine ⟨?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ?_
    unfold divisorPacketProfile
    fun_prop
  · refine Integrable.mono' ((integrableOn_one_add_mul_exp_neg
      (b := 2 * c) (by linarith)).const_mul (M ^ 2)) ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_)
      unfold leakDensity divisorPacketProfile
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have hb := norm_divisorPacketProfile_le (m := m) hc ht0
      have hnn : 0 ≤ ‖divisorPacketProfile lam m t‖ := norm_nonneg _
      have hsq : leakDensity (divisorPacketProfile lam m) t ≤ M ^ 2 * Real.exp (-c * t) ^ 2 := by
        unfold leakDensity
        nlinarith [Real.exp_pos (-c * t)]
      have hexp2 : Real.exp (-c * t) ^ 2 = Real.exp (-(2 * c) * t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      have hd := leakDensity_nonneg (divisorPacketProfile lam m) t
      have h1t : (0 : ℝ) < 1 + t := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1t.le hd)]
      rw [hexp2] at hsq
      nlinarith [hsq, h1t, sq_nonneg M]

theorem tailLeakEnergy_divisorPacket_zero {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) :
    tailLeakEnergy (divisorPacketProfile lam m) 0 = divisorPacketEnergy lam m := rfl

/-- **Equation (10).**  The initial trace slope of a finite divisor packet is its residue energy. -/
theorem tendsto_initial_slope_divisorPacket {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) :
    Tendsto (fun k : ℝ => (hankelGapProfile (divisorPacketProfile lam m) 0
        - hankelGapProfile (divisorPacketProfile lam m) k) / k)
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorPacketEnergy lam m)) := by
  have h := tendsto_initial_slope (leakProfile_divisorPacket (m := m) hlam)
  simpa [divisorPacketEnergy, leakDensity] using h

theorem leakProfile_polePacket : LeakProfile polePacketProfile := by
  have hdens : ∀ t : ℝ, leakDensity polePacketProfile t = 4 * Real.exp (-(1 : ℝ) * t) := by
    intro t
    unfold leakDensity polePacketProfile
    rw [norm_mul, Complex.norm_exp]
    have hre : (-((1 / 2 : ℂ) * (t : ℂ))).re = -((1 / 2 : ℝ) * t) := by
      simp [Complex.mul_re]
    rw [hre]
    have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hnorm2, mul_pow]
    have : Real.exp (-((1 / 2 : ℝ) * t)) ^ 2 = Real.exp (-(1 : ℝ) * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [this]
    norm_num
  refine ⟨?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ?_
    unfold polePacketProfile
    fun_prop
  · refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_one_add_mul_exp_neg (b := 1) one_pos).const_mul 4) ?_ measurableSet_Ioi
    intro t _
    show (4 : ℝ) * ((1 + t) * Real.exp (-1 * t)) = (1 + t) * leakDensity polePacketProfile t
    rw [hdens t]
    ring

theorem tailLeakEnergy_polePacket_zero : tailLeakEnergy polePacketProfile 0 = 4 := by
  have : tailLeakEnergy polePacketProfile 0 = polePacketEnergy := rfl
  rw [this, polePacketEnergy_eq_four]

/-- **Equation (14).**  The incoming pole has initial trace slope exactly `-4`. -/
theorem tendsto_initial_slope_polePacket :
    Tendsto (fun k : ℝ => (hankelGapProfile polePacketProfile 0
        - hankelGapProfile polePacketProfile k) / k) (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  have h := tendsto_initial_slope leakProfile_polePacket
  rw [show (∫ t in Ioi (0 : ℝ), leakDensity polePacketProfile t)
      = tailLeakEnergy polePacketProfile 0 from rfl, tailLeakEnergy_polePacket_zero] at h
  exact h

/-- **Equations (16)–(17), packet form.**  A right-half divisor packet has initial trace loss at most
the pole value exactly when it is empty. -/
theorem divisorPacketEnergy_le_four_iff {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) (hstrip : ∀ j, (lam j).re < 1 / 2) (hm : ∀ j, 0 < m j) :
    divisorPacketEnergy lam m ≤ 4 ↔ r = 0 := by
  constructor
  · intro hle
    refine divisorPacket_isEmpty_of_energy_le_pole hlam hstrip hm ?_
    rw [polePacketEnergy_eq_four]
    exact hle
  · intro hr
    subst hr
    have hzero : ∀ t : ℝ, divisorPacketProfile lam m t = 0 := by
      intro t
      unfold divisorPacketProfile
      simp
    have hval : (∫ t in Ioi (0 : ℝ), ‖divisorPacketProfile lam m t‖ ^ 2) = 0 := by
      have hc : ∀ t : ℝ, ‖divisorPacketProfile lam m t‖ ^ 2 = 0 := by
        intro t
        rw [hzero t]
        simp
      simp [hc]
    unfold divisorPacketEnergy
    rw [hval]
    norm_num

/-! ## The closed form of the gap profile of a divisor packet -/

theorem integrableOn_sub_mul_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn (fun t : ℝ => ((t : ℂ) - (u : ℂ)) * Complex.exp (-(b * (t : ℂ))))
      (Ioi u) volume := by
  refine Integrable.mono' (((integrableOn_one_add_mul_exp_neg hb).mono_set
    (Ioi_subset_Ioi hu)).const_mul 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htu : u < t := ht
    have ht0 : (0 : ℝ) ≤ t := le_trans hu (le_of_lt htu)
    rw [norm_mul, Complex.norm_exp, re_neg_mul_ofReal]
    have hnorm : ‖((t : ℂ) - (u : ℂ))‖ = t - u := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
    rw [hnorm, one_mul, show -(b.re * t) = -b.re * t from by ring]
    have hexp : (0 : ℝ) < Real.exp (-b.re * t) := Real.exp_pos _
    nlinarith

theorem tendsto_linear_mul_exp_neg {c : ℝ} (hc : 0 < c) :
    Tendsto (fun s : ℝ => s * Real.exp (-(c * s))) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hcs : Tendsto (fun s : ℝ => c * s) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hcomp := (h.comp hcs).const_mul (1 / c)
  rw [mul_zero] at hcomp
  refine hcomp.congr fun s => ?_
  simp only [Function.comp_apply, pow_one]
  field_simp

/-- The exact first-moment Laplace integral on a shifted half-line. -/
theorem integral_Ioi_sub_mul_cexp_neg_mul {b : ℂ} (hb : 0 < b.re) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in Ioi u, ((t : ℂ) - (u : ℂ)) * Complex.exp (-(b * (t : ℂ))))
      = Complex.exp (-(b * (u : ℂ))) * b⁻¹ ^ 2 := by
  have hbne : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  set G : ℝ → ℂ := fun s => (((u : ℂ) - (s : ℂ)) * b⁻¹ - b⁻¹ ^ 2) *
    Complex.exp (-(b * (s : ℂ))) with hG
  have hderiv : ∀ t : ℝ, HasDerivAt G (((t : ℂ) - (u : ℂ)) * Complex.exp (-(b * (t : ℂ)))) t := by
    intro t
    have h0 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id t)
    have hf : HasDerivAt (fun s : ℝ => (((u : ℂ) - (s : ℂ)) * b⁻¹ - b⁻¹ ^ 2)) (-1 * b⁻¹) t :=
      ((h0.const_sub ((u : ℝ) : ℂ)).mul_const b⁻¹).sub_const (b⁻¹ ^ 2)
    have h1 : HasDerivAt (fun s : ℝ => -(b * ((s : ℝ) : ℂ))) (-(b * 1)) t :=
      HasDerivAt.neg (HasDerivAt.const_mul b h0)
    have hg := HasDerivAt.cexp h1
    have hmul := hf.mul hg
    have hval : -1 * b⁻¹ * Complex.exp (-(b * (t : ℂ)))
        + (((u : ℂ) - (t : ℂ)) * b⁻¹ - b⁻¹ ^ 2) * (Complex.exp (-(b * (t : ℂ))) * -(b * 1))
        = ((t : ℂ) - (u : ℂ)) * Complex.exp (-(b * (t : ℂ))) := by
      field_simp
      ring
    rw [hval] at hmul
    exact hmul
  have hlim : Tendsto G atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ s : ℝ, ‖G s‖
        ≤ ((‖b⁻¹‖ * |u| + ‖b⁻¹ ^ 2‖) + ‖b⁻¹‖ * |s|) * Real.exp (-(b.re * s)) := by
      intro s
      rw [hG]
      simp only [norm_mul, Complex.norm_exp, re_neg_mul_ofReal]
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (Real.exp_pos _))
      refine le_trans (norm_sub_le _ _) ?_
      have h1 : ‖((u : ℂ) - (s : ℂ)) * b⁻¹‖ ≤ ‖b⁻¹‖ * (|u| + |s|) := by
        rw [norm_mul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine le_trans (norm_sub_le _ _) ?_
        simp [Complex.norm_real, Real.norm_eq_abs]
      have h2 : ‖b⁻¹‖ * (|u| + |s|) = ‖b⁻¹‖ * |u| + ‖b⁻¹‖ * |s| := by ring
      rw [h2] at h1
      linarith
    have hmaj : Tendsto
        (fun s : ℝ => ((‖b⁻¹‖ * |u| + ‖b⁻¹ ^ 2‖) + ‖b⁻¹‖ * |s|) * Real.exp (-(b.re * s)))
        atTop (𝓝 0) := by
      have hexp0 : Tendsto (fun s : ℝ => Real.exp (-(b.re * s))) atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        exact tendsto_neg_atBot_iff.mpr (Filter.Tendsto.const_mul_atTop hb tendsto_id)
      have hexp1 : Tendsto (fun s : ℝ => s * Real.exp (-(b.re * s))) atTop (𝓝 0) :=
        tendsto_linear_mul_exp_neg hb
      have hsum := (hexp0.const_mul (‖b⁻¹‖ * |u| + ‖b⁻¹ ^ 2‖)).add (hexp1.const_mul ‖b⁻¹‖)
      rw [mul_zero, mul_zero, add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      rw [abs_of_nonneg hs]
      ring
    exact squeeze_zero (fun s => norm_nonneg _) hbound hmaj
  have hcont : ContinuousWithinAt G (Ici u) u := (hderiv u).continuousAt.continuousWithinAt
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t _ => hderiv t)
    (integrableOn_sub_mul_cexp_neg_mul hb hu) hlim
  rw [hmain, hG]
  simp
  ring

/-- The leakage density of a divisor packet as a double exponential sum. -/
theorem ofReal_leakDensity_divisorPacket {r : ℕ} (lam : Fin r → ℂ) (m : Fin r → ℕ) (t : ℝ) :
    ((leakDensity (divisorPacketProfile lam m) t : ℝ) : ℂ)
      = ∑ j, ∑ k, 4 * (m j : ℂ) * (m k : ℂ)
          * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))) := by
  have hconj : (starRingEnd ℂ) (divisorPacketProfile lam m t)
      = 2 * ∑ k, (m k : ℂ) * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ))) := by
    unfold divisorPacketProfile
    rw [map_mul, map_sum, complexConj_two]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    · simp
    · rw [map_neg, map_mul, Complex.conj_ofReal]
  have hsq : ((leakDensity (divisorPacketProfile lam m) t : ℝ) : ℂ)
      = divisorPacketProfile lam m t * (starRingEnd ℂ) (divisorPacketProfile lam m t) := by
    unfold leakDensity
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hsq, hconj]
  unfold divisorPacketProfile
  rw [show (2 * ∑ j, (m j : ℂ) * Complex.exp (-(lam j * (t : ℂ))))
      * (2 * ∑ k, (m k : ℂ) * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ))))
      = 4 * ((∑ j, (m j : ℂ) * Complex.exp (-(lam j * (t : ℂ))))
        * ∑ k, (m k : ℂ) * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ)))) from by ring]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hexp : Complex.exp (-(lam j * (t : ℂ)))
      * Complex.exp (-((starRingEnd ℂ) (lam k) * (t : ℂ)))
      = Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ))) := by
    rw [← Complex.exp_add]
    ring_nf
  linear_combination (4 * (m j : ℂ) * (m k : ℂ)) * hexp

/-- **Equation (9).**  The closed form of the gap profile of a finite divisor packet. -/
theorem hankelGapProfile_divisorPacket {r : ℕ} {lam : Fin r → ℂ} {m : Fin r → ℕ}
    (hlam : ∀ j, 0 < (lam j).re) {u : ℝ} (hu : 0 ≤ u) :
    ((hankelGapProfile (divisorPacketProfile lam m) u : ℝ) : ℂ)
      = ∑ j, ∑ k, (4 * (m j : ℂ) * (m k : ℂ))
          * (Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (u : ℂ)))
            * (lam j + (starRingEnd ℂ) (lam k))⁻¹ ^ 2) := by
  have hre : ∀ j k : Fin r, 0 < (lam j + (starRingEnd ℂ) (lam k)).re := by
    intro j k
    simp only [Complex.add_re, Complex.conj_re]
    have := hlam j
    have := hlam k
    linarith
  have hpt : ∀ t : ℝ, (((t - u) * leakDensity (divisorPacketProfile lam m) t : ℝ) : ℂ)
      = ∑ j, ∑ k, (4 * (m j : ℂ) * (m k : ℂ))
          * (((t : ℂ) - (u : ℂ)) * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ)))) := by
    intro t
    have hdens := ofReal_leakDensity_divisorPacket (lam := lam) (m := m) t
    push_cast
    rw [hdens, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hint : ∀ j k : Fin r, IntegrableOn
      (fun t : ℝ => (4 * (m j : ℂ) * (m k : ℂ))
        * (((t : ℂ) - (u : ℂ)) * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ)))))
      (Ioi u) volume :=
    fun j k => (integrableOn_sub_mul_cexp_neg_mul (hre j k) hu).const_mul _
  calc ((hankelGapProfile (divisorPacketProfile lam m) u : ℝ) : ℂ)
      = ∫ t in Ioi u, (((t - u) * leakDensity (divisorPacketProfile lam m) t : ℝ) : ℂ) :=
        (integral_complex_ofReal).symm
    _ = ∫ t in Ioi u, ∑ j, ∑ k, (4 * (m j : ℂ) * (m k : ℂ))
          * (((t : ℂ) - (u : ℂ))
            * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ)))) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t
    _ = ∑ j, ∑ k, ∫ t in Ioi u, (4 * (m j : ℂ) * (m k : ℂ))
          * (((t : ℂ) - (u : ℂ))
            * Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (t : ℂ)))) := by
        rw [integral_finsetSum _ fun j _ => (integrable_finsetSum _ fun k _ => hint j k)]
        exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hint j k
    _ = ∑ j, ∑ k, (4 * (m j : ℂ) * (m k : ℂ))
          * (Complex.exp (-((lam j + (starRingEnd ℂ) (lam k)) * (u : ℂ)))
            * (lam j + (starRingEnd ℂ) (lam k))⁻¹ ^ 2) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, integral_Ioi_sub_mul_cexp_neg_mul (hre j k) hu]

end

end GaloisForLFunctions.RHTower
