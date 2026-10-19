import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateRemainderBounds

/-!
# Admissibility of the shifted ground states in the folded ground-state representation

For every `a > 0` and every `C¹` compactly supported `u`, the pair `(ω_a, u)` is folded-admissible:
the archimedean remainder and potential are integrable, the prime remainder and potential are
summable, and the prime part of the folded generator is integrable against `u² ω_a` on the half
line. Consequently the remainder-dominates-defect identity for the Markov energy of `Φ(ω_a u)`
holds for every even `u ∈ C²_c(ℝ)` without any integrability hypothesis.

The bounds behind this are the linear and `Φ(t − R − a)`-decay bounds of the potential kernel and
of the ground remainder, integrated against the Lévy density (`ω(t) t` is integrable on `(0, ∞)`)
and summed against the von Mangoldt atoms (`Σ Λ(n) n^{−1/2} Φ(log n − R − a) < ∞`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem vonMangoldtAtom_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : vonMangoldtAtom n = 0 := by
  unfold vonMangoldtAtom
  rw [if_neg (by omega)]

/-- The prime shift sum against `Φ(log n − c)`. -/
theorem summable_atom_riemannKernelReal_log_sub (c : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * riemannKernelReal (Real.log n - c) := by
  refine (summable_primeShift_left c).congr fun n => ?_
  rw [show Real.log n - c = -(c - Real.log n) by ring, riemannKernelReal_neg']

/-- **Admissibility of the shifted ground states.** For `a > 0` and `u ∈ C¹_c(ℝ)` the pair
`(ω_a, u)` satisfies all integrability requirements of the folded ground-state representation. -/
theorem foldedAdmissible_shiftedGroundState {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    FoldedAdmissible (shiftedGroundState a) u := by
  obtain ⟨R, hR1, hsupp⟩ := exists_support_radius huc
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨Mu, hMu'⟩ := hu.continuous.bounded_above_of_compact_support huc
  have hMu : ∀ x, |u x| ≤ Mu := fun x => by
    rw [← Real.norm_eq_abs]
    exact hMu' x
  have hMu0 : 0 ≤ Mu := le_trans (abs_nonneg _) (hMu 0)
  obtain ⟨Lu, hLu0, hLu⟩ := exists_lipschitz_bound_of_compactSupport hu huc
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have huc' : Continuous u := hu.continuous
  obtain ⟨Mω, hMω'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hωc.continuousOn : ContinuousOn (shiftedGroundState a) (Icc (-R - 1) (R + 1)))
  have hMω : ∀ y ∈ Icc (-R - 1) (R + 1), |shiftedGroundState a y| ≤ Mω := fun y hy => by
    rw [← Real.norm_eq_abs]
    exact hMω' y hy
  have hMω0 : 0 ≤ Mω := le_trans (abs_nonneg _) (hMω 0 ⟨by linarith, by linarith⟩)
  obtain ⟨LΦ, -, hLΦ⟩ :=
    exists_lipschitz_bound_on_Icc contDiff_riemannKernelReal_one (-R - 1) (R + 1)
  obtain ⟨Lm, -, hLm⟩ := exists_lipschitz_bound_on_Icc (contDiff_shiftDifference a) (-R - 1) (R + 1)
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hωpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  set Kl := max (riemannKernelReal 0 * (2 * Mω * LΦ + 2 * Lm))
    (riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0)) with hKl
  have hKl0 : 0 ≤ Kl := le_max_of_le_right (by positivity)
  set Kd := max (riemannKernelReal 0 * (2 * Mω + 2))
    (riemannKernelReal 0 * (2 * Mω * riemannKernelReal 0 + 2 * riemannKernelReal 0) /
      riemannKernelReal (R + a)) with hKd
  have hKd0 : 0 ≤ Kd := le_max_of_le_left (by positivity)
  have hKlin : ∀ t x, 0 < x → x ≤ R → 0 < t → |shiftedPotentialKernel a t x| ≤ Kl * t :=
    fun t x hx hxR ht => shiftedPotentialKernel_abs_le_linear_all hR1 hMω hLΦ hLm hx hxR ht
  have hKdec : ∀ t x, 0 < x → x ≤ R → 0 ≤ t →
      |shiftedPotentialKernel a t x| ≤ Kd * riemannKernelReal (t - R - a) :=
    fun t x hx hxR ht => shiftedPotentialKernel_abs_le_decay_all ha hMω hx hxR ht
  set Cl := 2 * (riemannKernelReal 0 ^ 2 * (Lu ^ 2 + 4 * Mu ^ 2) * R) +
    4 * riemannKernelReal 0 ^ 2 * Mu ^ 2 with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  have hrlin : ∀ t, 0 < t → |groundRemainderShift (shiftedGroundState a) u t| ≤ Cl * t :=
    fun t ht => abs_groundRemainderShift_shiftedGroundState_le_linear hR1 hsupp hMu hLu ht
  have hrdec : ∀ t, R + a ≤ t → |groundRemainderShift (shiftedGroundState a) u t| ≤
      (16 * riemannKernelReal 0 * Mu ^ 2 * R) * riemannKernelReal (t - R - a) :=
    fun t ht => abs_groundRemainderShift_shiftedGroundState_le_decay ha hR1 hsupp hMu ht
  set Cd := max (16 * riemannKernelReal 0 * Mu ^ 2 * R) (Cl * (R + a) / riemannKernelReal (R + a))
    with hCd
  have hrall : ∀ t, 0 < t → |groundRemainderShift (shiftedGroundState a) u t| ≤
      Cd * riemannKernelReal (t - R - a) :=
    fun t ht => abs_le_decay_of_linear_of_decay ha hR0 hCl0 hrlin hrdec ht
  have hrem_meas := measurable_groundRemainderShift hωc huc'
  have hu2 : ∀ x, u x ^ 2 ≤ Mu ^ 2 := fun x => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMu x) 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- archimedean remainder
    have hdom : Integrable (fun t => Cl * (archLevyDensity t * t)) (volume.restrict (Ioi 0)) :=
      integrableOn_archLevyDensity_mul_id.const_mul Cl
    refine hdom.mono' (measurable_archLevyDensity.mul hrem_meas).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have hL := archLevyDensity_pos (mem_Ioi.mp ht)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hL]
    calc archLevyDensity t * |groundRemainderShift (shiftedGroundState a) u t|
        ≤ archLevyDensity t * (Cl * t) := mul_le_mul_of_nonneg_left (hrlin t ht) hL.le
      _ = Cl * (archLevyDensity t * t) := by ring
  · -- archimedean potential
    have hcs : HasCompactSupport fun x => Kl * u x ^ 2 :=
      huc.comp_left (g := fun y => Kl * y ^ 2) (by simp)
    have hint : Integrable (fun x => Kl * u x ^ 2) (volume.restrict (Ioi 0)) :=
      ((continuous_const.mul (huc'.pow 2)).integrable_of_hasCompactSupport hcs).integrableOn
    have hdom : Integrable (fun z : ℝ × ℝ => (archLevyDensity z.1 * z.1) * (Kl * u z.2 ^ 2))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      Integrable.mul_prod integrableOn_archLevyDensity_mul_id hint
    have hmeas : Measurable fun z : ℝ × ℝ =>
        archLevyDensity z.1 * groundPotentialDensity (shiftedGroundState a) u z.1 z.2 :=
      (measurable_archLevyDensity.comp measurable_fst).mul
        (continuous_groundPotentialDensity_uncurry hωc huc').measurable
    refine hdom.mono' hmeas.aestronglyMeasurable ?_
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun z hz => ?_
    have ht : 0 < z.1 := hz.1
    have hx : 0 < z.2 := hz.2
    have hL := archLevyDensity_pos ht
    show ‖archLevyDensity z.1 * groundPotentialDensity (shiftedGroundState a) u z.1 z.2‖ ≤
      (archLevyDensity z.1 * z.1) * (Kl * u z.2 ^ 2)
    rw [groundPotentialDensity_shiftedGroundState, Real.norm_eq_abs, abs_mul, abs_of_pos hL,
      abs_mul, abs_of_nonneg (sq_nonneg _)]
    by_cases hxR : z.2 ≤ R
    · have hk := hKlin z.1 z.2 hx hxR ht
      calc archLevyDensity z.1 * (u z.2 ^ 2 * |shiftedPotentialKernel a z.1 z.2|)
          ≤ archLevyDensity z.1 * (u z.2 ^ 2 * (Kl * z.1)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (sq_nonneg _)) hL.le
        _ = (archLevyDensity z.1 * z.1) * (Kl * u z.2 ^ 2) := by ring
    · rw [not_le] at hxR
      rw [hsupp z.2 (by rw [abs_of_pos hx]; exact hxR)]
      simp
  · -- prime remainder
    have hbig : Summable fun n : ℕ =>
        Cd * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by
      refine ((summable_atom_riemannKernelReal_log_sub (R + a)).mul_left Cd).congr fun n => ?_
      rw [sub_sub]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbig
    · exact mul_nonneg (vonMangoldtAtom_nonneg n)
        (groundRemainderShift_nonneg hωpos (Real.log_natCast_nonneg n))
    · rcases lt_or_ge n 2 with hn | hn
      · rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
        simp
      · have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        have hlog : 0 < Real.log n := Real.log_pos h1
        have hb := hrall (Real.log n) hlog
        have hΛ := vonMangoldtAtom_nonneg n
        calc vonMangoldtAtom n * groundRemainderShift (shiftedGroundState a) u (Real.log n)
            ≤ vonMangoldtAtom n * |groundRemainderShift (shiftedGroundState a) u (Real.log n)| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hΛ
          _ ≤ vonMangoldtAtom n * (Cd * riemannKernelReal (Real.log n - R - a)) :=
              mul_le_mul_of_nonneg_left hb hΛ
          _ = Cd * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by ring
  · -- prime potential
    have hbig : Summable fun n : ℕ =>
        (Mu ^ 2 * Kd * R) * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by
      refine ((summable_atom_riemannKernelReal_log_sub (R + a)).mul_left
        (Mu ^ 2 * Kd * R)).congr fun n => ?_
      rw [sub_sub]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) hbig
    have hΛ := vonMangoldtAtom_nonneg n
    have hlog := Real.log_natCast_nonneg n
    have hb : ∀ x, 0 < x →
        |vonMangoldtAtom n * groundPotentialDensity (shiftedGroundState a) u (Real.log n) x| ≤
          (vonMangoldtAtom n * Mu ^ 2 * Kd * riemannKernelReal (Real.log n - R - a)) *
            (if x ≤ R then 1 else 0) := by
      intro x hx
      rw [groundPotentialDensity_shiftedGroundState, abs_mul, abs_of_nonneg hΛ, abs_mul,
        abs_of_nonneg (sq_nonneg _)]
      split_ifs with hxR
      · rw [mul_one]
        have hk := hKdec (Real.log n) x hx hxR hlog
        calc vonMangoldtAtom n * (u x ^ 2 * |shiftedPotentialKernel a (Real.log n) x|)
            ≤ vonMangoldtAtom n * (Mu ^ 2 * (Kd * riemannKernelReal (Real.log n - R - a))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hu2 x) hk (abs_nonneg _) (sq_nonneg _)) hΛ
          _ = _ := by ring
      · rw [not_le] at hxR
        rw [hsupp x (by rw [abs_of_pos hx]; exact hxR)]
        simp
    refine (integral_Ioi_norm_le_of_le_indicator hR0 hb).trans (le_of_eq ?_)
    ring
  · -- prime generator
    have hB : Summable fun n : ℕ =>
        (Mu ^ 2 * Kd) * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by
      refine ((summable_atom_riemannKernelReal_log_sub (R + a)).mul_left (Mu ^ 2 * Kd)).congr
        fun n => ?_
      rw [sub_sub]
    set B := ∑' n : ℕ, (Mu ^ 2 * Kd) * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a))
      with hBdef
    have hpt : ∀ x, 0 < x → x ≤ R →
        |u x ^ 2 * shiftedGroundState a x *
          ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x|
          ≤ B := by
      intro x hx hxR
      have hterm : ∀ n : ℕ, ‖u x ^ 2 * shiftedGroundState a x *
          (vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x)‖ ≤
          (Mu ^ 2 * Kd) * (vonMangoldtAtom n * riemannKernelReal (Real.log n - R - a)) := by
        intro n
        have hΛ := vonMangoldtAtom_nonneg n
        have e : u x ^ 2 * shiftedGroundState a x *
            (vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x) =
            vonMangoldtAtom n * (u x ^ 2 * shiftedPotentialKernel a (Real.log n) x) := by
          rw [← groundPotentialDensity_shiftedGroundState]
          unfold groundPotentialDensity
          ring
        rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ, abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hk := hKdec (Real.log n) x hx hxR (Real.log_natCast_nonneg n)
        calc vonMangoldtAtom n * (u x ^ 2 * |shiftedPotentialKernel a (Real.log n) x|)
            ≤ vonMangoldtAtom n * (Mu ^ 2 * (Kd * riemannKernelReal (Real.log n - R - a))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul (hu2 x) hk (abs_nonneg _) (sq_nonneg _)) hΛ
          _ = _ := by ring
      have hnorm : Summable fun n : ℕ => ‖u x ^ 2 * shiftedGroundState a x *
          (vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x)‖ :=
        hB.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      rw [← tsum_mul_left, ← Real.norm_eq_abs]
      exact (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hterm hnorm hB)
    have hg0 : IntegrableOn (fun _ : ℝ => B) (Ioc (0 : ℝ) R) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hg : Integrable ((Ioc (0 : ℝ) R).indicator fun _ => B) (volume.restrict (Ioi 0)) :=
      (hg0.integrable_indicator measurableSet_Ioc).integrableOn
    have hmeas : AEStronglyMeasurable (fun x => u x ^ 2 * shiftedGroundState a x *
        ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x)
        (volume.restrict (Ioi 0)) := by
      refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => u x ^ 2 * shiftedGroundState a x *
        ∑ n ∈ Finset.range N,
          vonMangoldtAtom n * foldedShiftGenerator (shiftedGroundState a) (Real.log n) x)
        atTop (fun N => ?_) ?_
      · refine Continuous.aestronglyMeasurable (((huc'.pow 2).mul hωc).mul ?_)
        exact continuous_finsetSum _ fun n _ =>
          continuous_const.mul (continuous_foldedShiftGenerator hωc _)
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_
        exact ((summable_atom_foldedShiftGenerator_shiftedGroundState ha x).hasSum.tendsto_sum_nat).const_mul _
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

/-- **Remainder-dominates-defect identity, unconditional form.** For every `a > 0` and every even
`u ∈ C²_c(ℝ)`,

    markovEnergy (Φ(ω_a u)) = groundRemainder − 4 ∫_{x>0} u² ω_a Φ (C_a(x) − sinh(a/2) sinh(x/2)). -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq_of_contDiff {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      groundRemainder (shiftedGroundState a) u -
        4 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
          (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2)) :=
  markovEnergy_phiDoob_shiftedGroundState_eq ha hu huc heven
    (foldedAdmissible_shiftedGroundState ha (hu.of_le (by norm_num)) huc)

/-- Nonnegativity of the Markov energy on `Φ(ω_a u)`, `u ∈ C²_c` even, is exactly the domination
of the weighted collar excess by the nonnegative ground remainder. -/
theorem markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_of_contDiff {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) ↔
      4 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
          (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2))) ≤
        groundRemainder (shiftedGroundState a) u :=
  markovEnergy_phiDoob_shiftedGroundState_nonneg_iff ha hu huc heven
    (foldedAdmissible_shiftedGroundState ha (hu.of_le (by norm_num)) huc)

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
