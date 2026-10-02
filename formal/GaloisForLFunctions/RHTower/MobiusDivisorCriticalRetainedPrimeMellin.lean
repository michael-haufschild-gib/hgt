import GaloisForLFunctions.RHTower.MobiusDivisorCriticalRetainedPrimeProduct

/-!
# Mellin identification of the actual retained old-prime head

Each prime dilation preserves the admitted source integral and its norm
integral. Absolute product admission then identifies the finite moving
old-prime head with the boundary transform, including its right slope.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- The literal old-prime head, with the cutoff `p² ≤ x` retained in each atom. -/
def criticalRetainedPrimeHead (x : ℝ) : ℝ :=
  ∑' p : ℕ, criticalRetainedPrimeHeadAtom p x

/-- The countable notation is exactly a finite prime sum at every positive
source cutoff; each summand still enforces `p² ≤ x`. -/
theorem criticalRetainedPrimeHead_eq_finite {x : ℝ} (hx : 1 < x) :
    criticalRetainedPrimeHead x =
      ∑ p ∈ retainedPrimeCutoff x, criticalRetainedPrimeHeadAtom p x := by
  apply tsum_eq_sum
  intro p hp
  by_cases hc : p.Prime ∧ (p : ℝ) ^ (2 : ℕ) ≤ x
  · exfalso
    apply hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hc.1.two_le
    have hpx : (p : ℝ) ≤ x := by nlinarith [hc.2]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by have := hc.1.two_le; omega, ?_⟩, hc.1⟩
    exact (Nat.le_floor_iff (le_of_lt (lt_trans zero_lt_one hx))).mpr hpx
  · simp [criticalRetainedPrimeHeadAtom, hc]

private theorem sourceAtom_zero_le_one (δ : ℝ) (p : ℕ) {y : ℝ} (hy : y ≤ 1) :
    criticalRetainedPrimeSourceAtom δ p y = 0 := by
  have hn : ¬(p.Prime ∧ (p : ℝ) ≤ y) := by
    rintro ⟨hp, hpy⟩
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  simp [criticalRetainedPrimeSourceAtom, hn]

private theorem headAtom_zero_le_one (p : ℕ) {x : ℝ} (hx : x ≤ 1) :
    criticalRetainedPrimeHeadAtom p x = 0 := by
  have hn : ¬(p.Prime ∧ (p : ℝ) ^ (2 : ℕ) ≤ x) := by
    rintro ⟨hp, hpx⟩
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  simp [criticalRetainedPrimeHeadAtom, hn]

private theorem ray_indicator_eq {f : ℝ → ℝ} (hf : ∀ x, x ≤ 1 → f x = 0) :
    (Ioi (1 : ℝ)).indicator f = f := by
  funext x
  by_cases hx : 1 < x
  · simp [hx]
  · simp [hx, hf x (le_of_not_gt hx)]

private theorem ray_integral_eq {f : ℝ → ℝ} (hf : ∀ x, x ≤ 1 → f x = 0) :
    (∫ x in Ioi (1 : ℝ), f x) = ∫ x, f x := by
  rw [← integral_indicator measurableSet_Ioi, ray_indicator_eq hf]

private theorem ray_integrable {f : ℝ → ℝ} (hf : ∀ x, x ≤ 1 → f x = 0)
    (hi : IntegrableOn f (Ioi (1 : ℝ))) : Integrable f := by
  have h := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  rwa [ray_indicator_eq hf] at h

private def retainedHeadMellinAtom (δ : ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHeadAtom p x

private theorem sourceAtom_integrable {δ : ℝ} (hδ : 0 ≤ δ) (p : ℕ) :
    Integrable (criticalRetainedPrimeSourceAtom δ p) := by
  have hi := Measure.ae_count_iff.mp
    (integrable_criticalRetainedPrimeSource_product hδ).prod_right_ae p
  exact ray_integrable (fun _ hx => sourceAtom_zero_le_one δ p hx) hi

private theorem retainedHeadMellinAtom_integrable {δ : ℝ} (hδ : 0 ≤ δ) (p : ℕ) :
    Integrable (retainedHeadMellinAtom δ p) := by
  change Integrable (fun x : ℝ => retainedHeadMellinAtom δ p x)
  by_cases hp : p.Prime
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hc : Integrable (fun y : ℝ => retainedHeadMellinAtom δ p ((p : ℝ) * y)) := by
      have hi := (sourceAtom_integrable hδ p).const_mul (p : ℝ)⁻¹
      convert hi using 1
      funext y
      rw [criticalRetainedPrimeSourceAtom_dilation]
      dsimp [retainedHeadMellinAtom]
      field_simp [hp0.ne']
    exact (integrable_comp_mul_left_iff _ hp0.ne').mp hc
  · simp only [retainedHeadMellinAtom, criticalRetainedPrimeHeadAtom, hp,
      false_and, if_false, mul_zero]
    exact integrable_zero ℝ ℝ volume

private theorem sourceAtom_integral_eq_headAtom (δ : ℝ) (p : ℕ) :
    (∫ y in Ioi (1 : ℝ), criticalRetainedPrimeSourceAtom δ p y) =
      ∫ x, retainedHeadMellinAtom δ p x := by
  rw [ray_integral_eq (fun _ hx => sourceAtom_zero_le_one δ p hx)]
  by_cases hp : p.Prime
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have he : criticalRetainedPrimeSourceAtom δ p =
        fun y : ℝ => (p : ℝ) * retainedHeadMellinAtom δ p ((p : ℝ) * y) := by
      funext y
      rw [criticalRetainedPrimeSourceAtom_dilation]
      dsimp [retainedHeadMellinAtom]
      ring
    rw [he, integral_const_mul, Measure.integral_comp_mul_left,
      smul_eq_mul, abs_of_pos (inv_pos.mpr hp0)]
    field_simp [hp0.ne']
  · simp [criticalRetainedPrimeSourceAtom, retainedHeadMellinAtom,
      criticalRetainedPrimeHeadAtom, hp]

private theorem sourceAtom_norm_integral_eq_headAtom (δ : ℝ) (p : ℕ) :
    (∫ y in Ioi (1 : ℝ), ‖criticalRetainedPrimeSourceAtom δ p y‖) =
      ∫ x, ‖retainedHeadMellinAtom δ p x‖ := by
  rw [ray_integral_eq (fun _ hx => by rw [sourceAtom_zero_le_one δ p hx, norm_zero])]
  by_cases hp : p.Prime
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have he : (fun y : ℝ => ‖criticalRetainedPrimeSourceAtom δ p y‖) =
        fun y : ℝ => (p : ℝ) * ‖retainedHeadMellinAtom δ p ((p : ℝ) * y)‖ := by
      funext y
      rw [criticalRetainedPrimeSourceAtom_dilation]
      dsimp [retainedHeadMellinAtom]
      rw [show (p : ℝ) * ((p : ℝ) * y) ^ (-(5 / 2 : ℝ) - δ) *
          criticalRetainedPrimeHeadAtom p ((p : ℝ) * y) =
        (p : ℝ) * (((p : ℝ) * y) ^ (-(5 / 2 : ℝ) - δ) *
          criticalRetainedPrimeHeadAtom p ((p : ℝ) * y)) by ring]
      simp only [abs_mul, abs_of_pos hp0]
    rw [he, integral_const_mul,
      Measure.integral_comp_mul_left (fun x => ‖retainedHeadMellinAtom δ p x‖) (p : ℝ),
      smul_eq_mul, abs_of_pos (inv_pos.mpr hp0)]
    field_simp [hp0.ne']
  · simp [criticalRetainedPrimeSourceAtom, retainedHeadMellinAtom,
      criticalRetainedPrimeHeadAtom, hp]

private theorem measurable_retainedHeadMellinAtom (δ : ℝ) (p : ℕ) :
    Measurable (retainedHeadMellinAtom δ p) := by
  apply (measurable_id.pow_const (-(5 / 2 : ℝ) - δ)).mul
  change Measurable (fun x : ℝ => criticalRetainedPrimeHeadAtom p x)
  by_cases hp : p.Prime
  · simp only [criticalRetainedPrimeHeadAtom, hp, true_and]
    exact Measurable.ite measurableSet_Ici
      (measurable_const.mul (measurable_criticalContinuousAbel.comp
        (measurable_id.div measurable_const))) measurable_const
  · simp only [criticalRetainedPrimeHeadAtom, hp, false_and, if_false]
    exact measurable_const

private theorem retainedHeadMellinAtom_product_integrable {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun z : ℕ × ℝ => retainedHeadMellinAtom δ z.1 z.2)
      (Measure.count.prod volume) := by
  have hm : Measurable (fun z : ℕ × ℝ => retainedHeadMellinAtom δ z.1 z.2) :=
    measurable_from_prod_countable_right (measurable_retainedHeadMellinAtom δ)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (retainedHeadMellinAtom_integrable hδ), ?_⟩
  have hi := (integrable_criticalRetainedPrimeSource_product hδ).integral_norm_prod_left
  convert hi using 1
  funext p
  exact (sourceAtom_norm_integral_eq_headAtom δ p).symm

private theorem retainedHead_count_integral_ae {δ : ℝ} (hδ : 0 ≤ δ) :
    (fun x : ℝ => ∫ p : ℕ, retainedHeadMellinAtom δ p x ∂Measure.count) =ᵐ[volume]
      fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHead x := by
  filter_upwards [(retainedHeadMellinAtom_product_integrable hδ).prod_left_ae] with x hx
  rw [integral_countable hx]
  simp only [count_real_singleton, one_smul, retainedHeadMellinAtom, criticalRetainedPrimeHead]
  rw [tsum_mul_left]

/-- The retained old-prime head is admitted absolutely at the critical
Mellin boundary. No prime-cutoff term is discarded. -/
theorem integrableOn_criticalRetainedPrimeHead {δ : ℝ} (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHead x)
      (Ioi (1 : ℝ)) := by
  have hi := (retainedHeadMellinAtom_product_integrable hδ).integral_prod_right
  exact (hi.congr (retainedHead_count_integral_ae hδ)).integrableOn

/-- Exact Mellin identification of the complete omitted old-prime term,
including at the critical endpoint. -/
theorem criticalRetainedPrimeHead_transform_eq {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHead x) =
      criticalRetainedPrimeBoundaryTransform δ := by
  have hi := retainedHeadMellinAtom_product_integrable hδ
  have hz : ∀ x : ℝ, x ≤ 1 → x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHead x = 0 := by
    intro x hx
    have ha : ∀ p : ℕ, criticalRetainedPrimeHeadAtom p x = 0 :=
      fun p => headAtom_zero_le_one p hx
    simp [criticalRetainedPrimeHead, ha]
  rw [ray_integral_eq hz, ← integral_congr_ae (retainedHead_count_integral_ae hδ)]
  rw [← integral_integral_swap hi, integral_countable hi.integral_prod_left]
  simp only [count_real_singleton, one_smul]
  rw [criticalRetainedPrimeBoundaryTransform_eq_prime_integrals hδ]
  apply tsum_congr
  intro p
  exact (sourceAtom_integral_eq_headAtom δ p).symm

/-- The full retained old-prime head has a finite right Mellin slope. Thus
this actual moving-cutoff term cannot supply a logarithmically divergent
first boundary slope. -/
theorem criticalRetainedPrimeHead_right_slope :
    Tendsto (fun δ : ℝ =>
      ((∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ) - δ) * criticalRetainedPrimeHead x) -
        (∫ x in Ioi (1 : ℝ), x ^ (-(5 / 2 : ℝ)) * criticalRetainedPrimeHead x)) / δ)
      (𝓝[>] 0)
      (𝓝 (-(∫ y in Ioi (1 : ℝ), criticalContinuousAbel y / y ^ (5 / 2 : ℝ) *
        retainedPrimeBoundaryMoment y))) := by
  apply criticalRetainedPrimeBoundaryTransform_right_slope.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  rw [criticalRetainedPrimeHead_transform_eq hδ.le]
  have hzero := criticalRetainedPrimeHead_transform_eq (δ := 0) le_rfl
  simp only [sub_zero] at hzero
  rw [hzero]

end RHTower
