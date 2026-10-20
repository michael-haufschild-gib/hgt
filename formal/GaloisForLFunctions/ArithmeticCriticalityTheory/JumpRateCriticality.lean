import GaloisForLFunctions.ArithmeticCriticalityTheory.OddFormCriticality
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateMonotoneFoldDomination

/-!
# The odd arithmetic form has no slack in its jump rates

The odd Markov form is `Q(v) = ∫ dm(t) J_t(v) − ∫ ρ v²` with the single-length Doob jump energies

    J_ℓ(v) = ∫ Φ(x) Φ(x + ℓ) (v(x) − v(x + ℓ))² dx.

Lowering the jump measure `dm` by `ε δ_ℓ` lowers the form by `ε J_ℓ`. The theorem
(`exists_odd_markovEnergy_lt_shiftJumpEnergy`): for every jump length `ℓ > 0` and every `ε > 0`
there is an odd `v ∈ C²_c(ℝ)` with

    markovEnergy(Φ v) < ε J_ℓ(v).

So no jump rate can be lowered at any length, by any amount, without the odd form taking a negative
value: at `ℓ = log n` the rate `Λ(n) n^{−1/2}` of every prime power is needed in full
(`exists_odd_markovEnergy_lt_primeRate_shiftJumpEnergy`), and RH is the statement that it is the least
admissible rate (`riemannHypothesis_iff_isLeast_primeRate`). The archimedean density cannot be
lowered on any interval either (`exists_odd_markovEnergy_lt_integral_shiftJumpEnergy`). Together with the absence of Hardy
weights, the odd form is critical both against raising the potential and against lowering the jump
measure (`riemannHypothesis_iff_nonneg_and_rateCritical`).

Proof. Pick a pole-free pair `ω = sinh(n/2) ω_1 − sinh(1/2) ω_n` with `ω(ℓ/2) ≠ 0`; it is odd, so
`ω(−ℓ/2) − ω(ℓ/2) = −2ω(ℓ/2) ≠ 0` and the ℓ-jump energy of `ω` on the window `[−ℓ, 0]` is a
positive constant `κ`. Its plateau truncations `ω u_L` keep that window energy for `L ≥ ℓ`, while
their Markov energy is `O(e^{−8L})` by the span plateau law with `σ = 0`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The Doob jump energy at the single length `ℓ`: `∫ Φ(x)Φ(x+ℓ)(v(x) − v(x+ℓ))² dx`. -/
def shiftJumpEnergy (ℓ : ℝ) (v : ℝ → ℝ) : ℝ :=
  ∫ x, riemannKernelReal x * riemannKernelReal (x + ℓ) * (v x - v (x + ℓ)) ^ 2

theorem shiftJumpEnergy_nonneg (ℓ : ℝ) (v : ℝ → ℝ) : 0 ≤ shiftJumpEnergy ℓ v :=
  integral_nonneg fun _ => mul_nonneg (mul_nonneg (riemannKernelReal_pos _).le
    (riemannKernelReal_pos _).le) (sq_nonneg _)

theorem spanGroundState_neg {ι : Type*} (s : Finset ι) (c a : ι → ℝ) (y : ℝ) :
    spanGroundState s c a (-y) = -spanGroundState s c a y := by
  unfold spanGroundState
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [shiftedGroundState_neg]
  ring

/-- **No slack in the jump rates.** For every jump length `ℓ > 0` and every `ε > 0` some odd
`v ∈ C²_c(ℝ)` has `markovEnergy(Φ v) < ε J_ℓ(v)`. -/
theorem exists_odd_markovEnergy_lt_shiftJumpEnergy {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ (∀ x, v (-x) = -v x) ∧
      markovEnergy (fun x => (phiDoobTest v x : ℂ)) < ε * shiftJumpEnergy ℓ v := by
  obtain ⟨n, hn⟩ := exists_nat_nullPair_ne_zero (x := ℓ / 2) (by positivity)
  set c := nullPairCoeff (n : ℝ)
  set a := nullPairShift (n : ℝ)
  set ω := spanGroundState Finset.univ c a with hω_def
  have hωc : Continuous ω := continuous_spanGroundState _ _ _
  have hω0 : ω (ℓ / 2) ≠ 0 := by
    intro h0
    have h := riemannKernelReal_mul_spanGroundState Finset.univ c a (ℓ / 2)
    rw [← hω_def, h0, mul_zero] at h
    exact hn h.symm
  -- the window energy of the pole-free pair
  set g : ℝ → ℝ := fun x =>
    riemannKernelReal x * riemannKernelReal (x + ℓ) * (ω x - ω (x + ℓ)) ^ 2 with hg_def
  have hgc : Continuous g :=
    (continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
      (continuous_id.add continuous_const))).mul
      ((hωc.sub (hωc.comp (continuous_id.add continuous_const))).pow 2)
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (mul_nonneg (riemannKernelReal_pos _).le
    (riemannKernelReal_pos _).le) (sq_nonneg _)
  have hgpos : 0 < g (-(ℓ / 2)) := by
    have hd : ω (-(ℓ / 2)) - ω (-(ℓ / 2) + ℓ) = -2 * ω (ℓ / 2) := by
      rw [show -(ℓ / 2) + ℓ = ℓ / 2 by ring, hω_def, spanGroundState_neg]
      ring
    show 0 < riemannKernelReal (-(ℓ / 2)) * riemannKernelReal (-(ℓ / 2) + ℓ) *
      (ω (-(ℓ / 2)) - ω (-(ℓ / 2) + ℓ)) ^ 2
    rw [hd]
    exact mul_pos (mul_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _))
      (sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hω0))
  have hκ : 0 < ∫ x in Icc (-ℓ) 0, g x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hg0) hgc.integrableOn_Icc]
    have hopen : IsOpen ({x | 0 < g x} ∩ Ioo (-ℓ) 0) :=
      (isOpen_lt continuous_const hgc).inter isOpen_Ioo
    have hmem : -(ℓ / 2) ∈ {x | 0 < g x} ∩ Ioo (-ℓ) 0 :=
      ⟨hgpos, by constructor <;> linarith⟩
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨_, hmem⟩) (measure_mono ?_)
    exact fun x hx => ⟨ne_of_gt hx.1, Ioo_subset_Icc_self hx.2⟩
  -- the null sequence
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_spanPlateauProfile_le_of_poleFree
    (s := Finset.univ) (c := c) (a := a) (spanSourceCoefficient_nullPair n)
  obtain ⟨L, hLℓ, hLK⟩ : ∃ L : ℝ, ℓ ≤ L ∧
      K * Real.exp (-(8 * L)) < ε * ∫ x in Icc (-ℓ) 0, g x := by
    have h0 : Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
      simpa [Function.comp_def, neg_mul] using this
    obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds (mul_pos hε hκ)))
    exact ⟨max L₁ ℓ, le_max_right _ _, hL₁ _ (le_max_left _ _)⟩
  set v := spanPlateauProfile Finset.univ c a L with hv_def
  refine ⟨v, contDiff_spanPlateauProfile _ _ _ L, hasCompactSupport_spanPlateauProfile _ _ _ L,
    spanPlateauProfile_neg _ _ _ L, ?_⟩
  have hvc : Continuous v := (contDiff_spanPlateauProfile _ _ _ L).continuous
  have hJint : Integrable fun x =>
      riemannKernelReal x * riemannKernelReal (x + ℓ) * (v x - v (x + ℓ)) ^ 2 := by
    refine Continuous.integrable_of_hasCompactSupport ?_
      (hasCompactSupport_shift_sub_sq (hasCompactSupport_spanPlateauProfile _ _ _ L) ℓ).mul_left
    exact (continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
      (continuous_id.add continuous_const))).mul
      ((hvc.sub (hvc.comp (continuous_id.add continuous_const))).pow 2)
  have hJ : (∫ x in Icc (-ℓ) 0, g x) ≤ shiftJumpEnergy ℓ v := by
    unfold shiftJumpEnergy
    calc (∫ x in Icc (-ℓ) 0, g x)
        = ∫ x in Icc (-ℓ) 0,
            riemannKernelReal x * riemannKernelReal (x + ℓ) * (v x - v (x + ℓ)) ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
          have h1 : |x| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
          have h2 : |x + ℓ| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
          simp only [hg_def, hv_def, hω_def, spanPlateauProfile, smoothPlateau_eq_one h1,
            smoothPlateau_eq_one h2, mul_one]
      _ ≤ _ := setIntegral_le_integral hJint (ae_of_all _ fun x => mul_nonneg (mul_nonneg
          (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le) (sq_nonneg _))
  calc markovEnergy (fun x => (phiDoobTest v x : ℂ))
      ≤ K * Real.exp (-(8 * L)) := (le_abs_self _).trans (hK L)
    _ < ε * ∫ x in Icc (-ℓ) 0, g x := hLK
    _ ≤ ε * shiftJumpEnergy ℓ v := mul_le_mul_of_nonneg_left hJ hε.le

/-- **Every prime-power rate is needed in full.** If `Λ(n) > 0`, then for every `ε > 0` some odd
`v ∈ C²_c(ℝ)` has `markovEnergy(Φ v) < ε Λ(n) n^{−1/2} J_{log n}(v)`: lowering the rate of the
prime power `n` by any fraction makes the odd form negative. -/
theorem exists_odd_markovEnergy_lt_primeRate_shiftJumpEnergy {n : ℕ} (hn : 2 ≤ n)
    (hΛ : 0 < vonMangoldtAtom n) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ (∀ x, v (-x) = -v x) ∧
      markovEnergy (fun x => (phiDoobTest v x : ℂ)) <
        ε * (vonMangoldtAtom n * shiftJumpEnergy (Real.log n) v) := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  obtain ⟨v, hv, hvc, hodd, hlt⟩ := exists_odd_markovEnergy_lt_shiftJumpEnergy hlog (mul_pos hε hΛ)
  exact ⟨v, hv, hvc, hodd, by rwa [← mul_assoc]⟩

/-- **RH is criticality against the jump measure.** RH holds if and only if the odd Markov form is
nonnegative and no single jump rate can be lowered; the second condition holds unconditionally. -/
theorem riemannHypothesis_iff_nonneg_and_rateCritical :
    RiemannHypothesis ↔
      (∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
          0 ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ))) ∧
        ∀ ℓ ε : ℝ, 0 < ℓ → 0 < ε →
          ¬ ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
            ε * shiftJumpEnergy ℓ v ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ)) := by
  rw [← riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg]
  refine ⟨fun hRH => ⟨hRH, fun ℓ ε hℓ hε hslack => ?_⟩, fun h => h.1⟩
  obtain ⟨v, hv, hvc, hodd, hlt⟩ := exists_odd_markovEnergy_lt_shiftJumpEnergy hℓ hε
  exact absurd (hslack v hv hvc hodd) (not_le.mpr hlt)

/-- **The von Mangoldt rate is the critical rate.** For every `n ≥ 2`, RH holds if and only if
`Λ(n) n^{−1/2}` is the least rate `c` at the length `log n` for which the odd form, with that one rate
replaced by `c`, is nonnegative. -/
theorem riemannHypothesis_iff_isLeast_primeRate {n : ℕ} (hn : 2 ≤ n) :
    RiemannHypothesis ↔
      IsLeast {c : ℝ | ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
          0 ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ)) +
            (c - vonMangoldtAtom n) * shiftJumpEnergy (Real.log n) v} (vonMangoldtAtom n) := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg]
  constructor
  · intro hRH
    refine ⟨fun v hv hvc hodd => by simpa using hRH v hv hvc hodd, fun c hc => ?_⟩
    by_contra hlt
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    obtain ⟨v, hv, hvc, hodd, hQ⟩ := exists_odd_markovEnergy_lt_shiftJumpEnergy hlog
      (sub_pos.mpr (not_le.mp hlt))
    have := hc v hv hvc hodd
    linarith
  · intro h v hv hvc hodd
    simpa using h.1 v hv hvc hodd

/-! ### The archimedean density -/

theorem continuous_shiftJumpEnergy {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Continuous fun t => shiftJumpEnergy t v := by
  obtain ⟨Z, hZ⟩ := hvc.exists_bound_of_continuous hv
  have hZ' : ∀ x, |v x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  unfold shiftJumpEnergy
  refine continuous_of_dominated (bound := fun x => riemannKernelReal x * (riemannKernelReal 0 *
    (2 * Z) ^ 2)) (fun t => ?_) (fun t => Eventually.of_forall fun x => ?_)
    (integrable_riemannKernelReal.mul_const _) (Eventually.of_forall fun x => ?_)
  · exact ((continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
      (continuous_id.add continuous_const))).mul
      ((hv.sub (hv.comp (continuous_id.add continuous_const))).pow 2)).aestronglyMeasurable
  · have hd : |v x - v (x + t)| ≤ 2 * Z := by
      have := abs_sub (v x) (v (x + t))
      linarith [hZ' x, hZ' (x + t)]
    have hd2 : (v x - v (x + t)) ^ 2 ≤ (2 * Z) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (riemannKernelReal_pos _).le
      (riemannKernelReal_pos _).le) (sq_nonneg _))]
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (riemannKernelReal_le_zero_point _)
      (riemannKernelReal_pos _).le) hd2 (sq_nonneg _)
      (mul_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)
  · exact continuous_const.mul (continuous_riemannKernelReal.comp
      (continuous_const.add continuous_id)) |>.mul
      ((continuous_const.sub (hv.comp (continuous_const.add continuous_id))).pow 2)

/-- **No slack in the archimedean density.** For every interval `[t₁, t₂] ⊂ (0, ∞)` and `ε > 0`
some odd `v ∈ C²_c(ℝ)` has `markovEnergy(Φ v) < ε ∫_{t₁}^{t₂} J_t(v) dt`: lowering the jump density
on any interval, by any amount, makes the odd form negative. -/
theorem exists_odd_markovEnergy_lt_integral_shiftJumpEnergy {t₁ t₂ ε : ℝ} (h₁ : 0 < t₁)
    (h₁₂ : t₁ < t₂) (hε : 0 < ε) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧ (∀ x, v (-x) = -v x) ∧
      markovEnergy (fun x => (phiDoobTest v x : ℂ)) <
        ε * ∫ t in Icc t₁ t₂, shiftJumpEnergy t v := by
  set ℓ₀ := (t₁ + t₂) / 2 with hℓ₀
  have hℓ₀0 : 0 < ℓ₀ := by rw [hℓ₀]; linarith
  obtain ⟨n, hn⟩ := exists_nat_nullPair_ne_zero (x := ℓ₀ / 2) (by positivity)
  set c := nullPairCoeff (n : ℝ)
  set a := nullPairShift (n : ℝ)
  set ω := spanGroundState Finset.univ c a with hω_def
  have hωc : Continuous ω := continuous_spanGroundState _ _ _
  have hω0 : ω (ℓ₀ / 2) ≠ 0 := by
    intro h0
    have h := riemannKernelReal_mul_spanGroundState Finset.univ c a (ℓ₀ / 2)
    rw [← hω_def, h0, mul_zero] at h
    exact hn h.symm
  -- the window energy of the pole-free pair, jointly continuous in the length
  set G : ℝ → ℝ → ℝ := fun t x =>
    riemannKernelReal x * riemannKernelReal (x + t) * (ω x - ω (x + t)) ^ 2 with hG_def
  have hGc : Continuous (Function.uncurry G) :=
    (continuous_riemannKernelReal.comp continuous_snd |>.mul (continuous_riemannKernelReal.comp
      (continuous_snd.add continuous_fst))).mul
      (((hωc.comp continuous_snd).sub (hωc.comp (continuous_snd.add continuous_fst))).pow 2)
  have hG0 : ∀ t x, 0 ≤ G t x := fun t x => mul_nonneg (mul_nonneg (riemannKernelReal_pos _).le
    (riemannKernelReal_pos _).le) (sq_nonneg _)
  set h : ℝ → ℝ := fun t => ∫ x in Icc (-t₂) 0, G t x with hh_def
  have hhc : Continuous h := continuous_parametric_integral_of_continuous hGc isCompact_Icc
  have hh0 : ∀ t, 0 ≤ h t := fun t => setIntegral_nonneg measurableSet_Icc fun x _ => hG0 t x
  have hhpos : 0 < h ℓ₀ := by
    have hGx : Continuous (G ℓ₀) := hGc.comp (continuous_const.prodMk continuous_id)
    have hpt : 0 < G ℓ₀ (-(ℓ₀ / 2)) := by
      have hd : ω (-(ℓ₀ / 2)) - ω (-(ℓ₀ / 2) + ℓ₀) = -2 * ω (ℓ₀ / 2) := by
        rw [show -(ℓ₀ / 2) + ℓ₀ = ℓ₀ / 2 by ring, hω_def, spanGroundState_neg]
        ring
      show 0 < riemannKernelReal (-(ℓ₀ / 2)) * riemannKernelReal (-(ℓ₀ / 2) + ℓ₀) *
        (ω (-(ℓ₀ / 2)) - ω (-(ℓ₀ / 2) + ℓ₀)) ^ 2
      rw [hd]
      exact mul_pos (mul_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _))
        (sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hω0))
    show 0 < ∫ x in Icc (-t₂) 0, G ℓ₀ x
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (hG0 ℓ₀)) hGx.integrableOn_Icc]
    have hopen : IsOpen ({x | 0 < G ℓ₀ x} ∩ Ioo (-t₂) 0) :=
      (isOpen_lt continuous_const hGx).inter isOpen_Ioo
    have hmem : -(ℓ₀ / 2) ∈ {x | 0 < G ℓ₀ x} ∩ Ioo (-t₂) 0 :=
      ⟨hpt, by constructor <;> linarith⟩
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨_, hmem⟩) (measure_mono ?_)
    exact fun x hx => ⟨ne_of_gt hx.1, Ioo_subset_Icc_self hx.2⟩
  have hκ : 0 < ∫ t in Icc t₁ t₂, h t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hh0) hhc.integrableOn_Icc]
    have hopen : IsOpen ({t | 0 < h t} ∩ Ioo t₁ t₂) :=
      (isOpen_lt continuous_const hhc).inter isOpen_Ioo
    have hmem : ℓ₀ ∈ {t | 0 < h t} ∩ Ioo t₁ t₂ := ⟨hhpos, by constructor <;> linarith⟩
    refine lt_of_lt_of_le (hopen.measure_pos volume ⟨_, hmem⟩) (measure_mono ?_)
    exact fun t ht => ⟨ne_of_gt ht.1, Ioo_subset_Icc_self ht.2⟩
  -- the null sequence
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_spanPlateauProfile_le_of_poleFree
    (s := Finset.univ) (c := c) (a := a) (spanSourceCoefficient_nullPair n)
  obtain ⟨L, hLt, hLK⟩ : ∃ L : ℝ, t₂ ≤ L ∧
      K * Real.exp (-(8 * L)) < ε * ∫ t in Icc t₁ t₂, h t := by
    have h0 : Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
      simpa [Function.comp_def, neg_mul] using this
    obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds (mul_pos hε hκ)))
    exact ⟨max L₁ t₂, le_max_right _ _, hL₁ _ (le_max_left _ _)⟩
  set v := spanPlateauProfile Finset.univ c a L with hv_def
  refine ⟨v, contDiff_spanPlateauProfile _ _ _ L, hasCompactSupport_spanPlateauProfile _ _ _ L,
    spanPlateauProfile_neg _ _ _ L, ?_⟩
  have hvc : Continuous v := (contDiff_spanPlateauProfile _ _ _ L).continuous
  have hvs : HasCompactSupport v := hasCompactSupport_spanPlateauProfile _ _ _ L
  have hJ : ∀ t ∈ Icc t₁ t₂, h t ≤ shiftJumpEnergy t v := fun t ht => by
    have hJint : Integrable fun x =>
        riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2 := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hasCompactSupport_shift_sub_sq hvs t).mul_left
      exact (continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
        (continuous_id.add continuous_const))).mul
        ((hvc.sub (hvc.comp (continuous_id.add continuous_const))).pow 2)
    unfold shiftJumpEnergy
    calc h t = ∫ x in Icc (-t₂) 0,
            riemannKernelReal x * riemannKernelReal (x + t) * (v x - v (x + t)) ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
          have h1 : |x| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
          have h2 : |x + t| ≤ L := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, ht.1, ht.2]
          simp only [hG_def, hv_def, hω_def, spanPlateauProfile, smoothPlateau_eq_one h1,
            smoothPlateau_eq_one h2, mul_one]
      _ ≤ _ := setIntegral_le_integral hJint (ae_of_all _ fun x => mul_nonneg (mul_nonneg
          (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le) (sq_nonneg _))
  have hmono : (∫ t in Icc t₁ t₂, h t) ≤ ∫ t in Icc t₁ t₂, shiftJumpEnergy t v :=
    setIntegral_mono_on hhc.integrableOn_Icc (continuous_shiftJumpEnergy hvc hvs).integrableOn_Icc
      measurableSet_Icc hJ
  calc markovEnergy (fun x => (phiDoobTest v x : ℂ))
      ≤ K * Real.exp (-(8 * L)) := (le_abs_self _).trans (hK L)
    _ < ε * ∫ t in Icc t₁ t₂, h t := hLK
    _ ≤ ε * ∫ t in Icc t₁ t₂, shiftJumpEnergy t v := mul_le_mul_of_nonneg_left hmono hε.le

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
