import GaloisForLFunctions.RHTower.CHMDTranslatedPrimitiveSource

/-!
# Primitive cusp escape in the complete original Doob graph

The translated double-primitive profile is normalized in the actual theta-cosh mass.
Its complete signed source energy tends to zero, its full jump energy tends to one,
and its Hilbert graph norm squared tends to two. All vectors belong to the compact core.
No sign of the unnormalized Markov energy is assumed.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDEscape
open CHMDDoobGraph CHMDClosedJump CHMDTranslation

def source (p : SourceGraph) : Lp ℝ 2 massMeasure := p.val.fst

theorem source_smul (c : ℝ) (p : SourceGraph) : source (c • p) = c • source p := rfl

/-- The primitive hyperplane is the actual mass-orthogonal complement of the constant ground. -/
def Primitive (p : SourceGraph) : Prop := ⟪source p, source (constantLift 1)⟫_ℝ = 0

def test (t : ℝ) : ℝ → ℝ := phiDoobInv (translate profile t)

theorem test_contDiff (t : ℝ) : ContDiff ℝ 2 (test t) :=
  contDiff_phiDoobInv (contDiff_translate profile_contDiff t)

theorem test_compact (t : ℝ) : HasCompactSupport (test t) :=
  hasCompactSupport_phiDoobInv (compact_translate profile_compact t)

def lift (t : ℝ) : SourceGraph := compactLift (test t) (test_contDiff t) (test_compact t)

theorem lift_mem_core (t : ℝ) : lift t ∈ compactCore :=
  compactLift_mem_core (test t) (test_contDiff t) (test_compact t)

theorem lift_source_ae (t : ℝ) : source (lift t) =ᵐ[massMeasure] test t :=
  (compact_memLp_mass (test_contDiff t).continuous (test_compact t)).coeFn_toLp

theorem lift_energy (t : ℝ) :
    sourceEnergy (lift t) = markovEnergy (fun x => (profile x : ℂ)) := by
  rw [lift, sourceEnergy_compactLift]
  simp only [test, phiDoobTest_phiDoobInv, markovEnergy_translate]

theorem lift_mass (t : ℝ) : ‖source (lift t)‖ ^ 2 = inverseMass (translate profile t) := by
  change ‖(compact_memLp_mass (test_contDiff t).continuous (test_compact t)).toLp _‖ ^ 2 = _
  rw [norm_toLp_sq, integral_mass_sq]
  unfold phiDoobCoshMass phiDoobTest test phiDoobInv inverseMass inverseWeight
  congr 1
  funext x
  field_simp [(riemannKernelReal_pos x).ne']

theorem translated_profile_ne_zero (t : ℝ) : translate profile t ≠ 0 := by
  intro h
  apply profile_ne_zero
  funext x
  have he := congrFun h (x + t)
  simpa only [CHMDTranslation.translate, add_sub_cancel_right, Pi.zero_apply] using he

theorem lift_source_norm_pos (t : ℝ) : 0 < ‖source (lift t)‖ := by
  have hm := inverseMass_pos (continuous_translate profile_contDiff.continuous t)
    (compact_translate profile_compact t) (translated_profile_ne_zero t)
  rw [← lift_mass] at hm
  nlinarith [norm_nonneg (source (lift t))]

theorem lift_primitive (t : ℝ) : Primitive (lift t) := by
  unfold Primitive
  rw [L2.inner_def]
  have hc : source (constantLift 1) =ᵐ[massMeasure] (fun _ => (1 : ℝ)) :=
    (memLp_const 1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
  calc
    (∫ x, ⟪source (lift t) x, source (constantLift 1) x⟫_ℝ ∂massMeasure) =
        ∫ x, test t x ∂massMeasure := by
      apply integral_congr_ae
      filter_upwards [lift_source_ae t, hc] with x hx hc'
      simp [hx, hc']
    _ = coshHalfMoment (translate profile t) := by
      rw [massMeasure, integral_weighted volume continuous_massDensity.measurable
        (Eventually.of_forall fun x => (massDensity_pos x).le)]
      unfold coshHalfMoment
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [massDensity, test, phiDoobInv]
      field_simp [(riemannKernelReal_pos x).ne']
    _ = 0 := profile_translate_primitive t

theorem energy_smul (c : ℝ) (p : SourceGraph) : sourceEnergy (c • p) = c ^ 2 * sourceEnergy p := by
  unfold sourceEnergy energy
  simp only [Submodule.coe_smul, WithLp.smul_fst, WithLp.smul_snd, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

def normalized (t : ℝ) : SourceGraph := ‖source (lift t)‖⁻¹ • lift t

theorem normalized_mem_core (t : ℝ) : normalized t ∈ compactCore :=
  compactCore.smul_mem _ (lift_mem_core t)

theorem normalized_primitive (t : ℝ) : Primitive (normalized t) := by
  unfold Primitive normalized
  rw [source_smul, real_inner_smul_left]
  have hp := lift_primitive t
  change ⟪source (lift t), source (constantLift 1)⟫_ℝ = 0 at hp
  rw [hp, mul_zero]

theorem normalized_source_norm (t : ℝ) : ‖source (normalized t)‖ = 1 := by
  rw [normalized, source_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (lift_source_norm_pos t)), inv_mul_cancel₀ (lift_source_norm_pos t).ne']

theorem normalized_energy (t : ℝ) :
    sourceEnergy (normalized t) =
      markovEnergy (fun x => (profile x : ℂ)) / inverseMass (translate profile t) := by
  rw [normalized, energy_smul, inv_pow, lift_mass, lift_energy]
  ring

theorem normalized_energy_zero : Tendsto (fun t => sourceEnergy (normalized t)) atTop (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp
    (inverseMass_translate_atTop profile_contDiff.continuous profile_compact profile_ne_zero)
  have h := hi.const_mul (markovEnergy (fun x => (profile x : ℂ)))
  simpa only [normalized_energy, div_eq_mul_inv, mul_zero, Function.comp_def] using h

theorem normalized_jump (t : ℝ) :
    ‖(normalized t).val.snd‖ ^ 2 = sourceEnergy (normalized t) + 1 := by
  have hm : ‖(normalized t).val.fst‖ = 1 := normalized_source_norm t
  simp only [sourceEnergy, energy, hm, one_pow]
  ring

theorem normalized_jump_one :
    Tendsto (fun t => ‖(normalized t).val.snd‖ ^ 2) atTop (𝓝 1) := by
  simpa only [normalized_jump, zero_add] using normalized_energy_zero.add_const 1

theorem normalized_graph_norm_sq (t : ℝ) :
    ‖normalized t‖ ^ 2 = sourceEnergy (normalized t) + 2 := by
  have h := sourceEnergy_add_two_mass (normalized t)
  have hm : ‖(normalized t).val.fst‖ = 1 := normalized_source_norm t
  simpa only [hm, one_pow, mul_one] using h.symm

theorem normalized_graph_norm_sq_two :
    Tendsto (fun t => ‖normalized t‖ ^ 2) atTop (𝓝 2) := by
  simpa only [normalized_graph_norm_sq, zero_add] using normalized_energy_zero.add_const 2

theorem eventually_normalized_bounded : ∀ᶠ t in atTop, ‖normalized t‖ ≤ 2 := by
  filter_upwards [normalized_energy_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with t ht
  have hg := normalized_graph_norm_sq t
  nlinarith [norm_nonneg (normalized t)]

theorem separated_test_product {R s t : ℝ}
    (hR : ∀ x, profile x ≠ 0 → -R ≤ x ∧ x ≤ R) (hst : s + 2 * R < t) (x : ℝ) :
    test s x * test t x = 0 := by
  by_cases hs : profile (x - s) = 0
  · simp [test, phiDoobInv, CHMDTranslation.translate, hs]
  · have ht : profile (x - t) = 0 := by
      by_contra ht
      have h1 := (hR (x - s) hs).2
      have h2 := (hR (x - t) ht).1
      linarith
    simp [test, phiDoobInv, CHMDTranslation.translate, ht]

theorem separated_lift_inner {R s t : ℝ}
    (hR : ∀ x, profile x ≠ 0 → -R ≤ x ∧ x ≤ R) (hst : s + 2 * R < t) :
    ⟪source (lift s), source (lift t)⟫_ℝ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [lift_source_ae s, lift_source_ae t] with x hx hy
  rw [hx, hy]
  simpa [RCLike.inner_apply, mul_comm] using separated_test_product hR hst x

theorem separated_normalized_inner {R s t : ℝ}
    (hR : ∀ x, profile x ≠ 0 → -R ≤ x ∧ x ≤ R) (hst : s + 2 * R < t) :
    ⟪source (normalized s), source (normalized t)⟫_ℝ = 0 := by
  rw [normalized, normalized, source_smul, source_smul,
    real_inner_smul_left, real_inner_smul_right, separated_lift_inner hR hst]
  ring

/-- Unconditional primitive escape for the actual complete source and its compact core. -/
theorem exists_primitive_escape :
    ∃ p : ℕ → SourceGraph,
      (∀ n, p n ∈ compactCore) ∧
      (∀ n, Primitive (p n)) ∧
      (∀ n, ‖source (p n)‖ = 1) ∧
      (∀ n, ‖p n‖ ≤ 2) ∧
      (∀ n m, n ≠ m → ⟪source (p n), source (p m)⟫_ℝ = 0) ∧
      Tendsto (fun n => sourceEnergy (p n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(p n).val.snd‖ ^ 2) atTop (𝓝 1) ∧
      Tendsto (fun n => ‖p n‖ ^ 2) atTop (𝓝 2) := by
  obtain ⟨R, hRpos, hR⟩ := support_interval profile_compact
  obtain ⟨A, hA⟩ := eventually_atTop.1 eventually_normalized_bounded
  let time : ℕ → ℝ := fun n => A + (2 * R + 1) * n
  have hD : 0 < 2 * R + 1 := by linarith
  have htime : Tendsto time atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hcast.eventually (eventually_ge_atTop ((b - A) / (2 * R + 1)))] with n hn
    have hmul := (div_le_iff₀ hD).mp hn
    dsimp only [time]
    nlinarith
  have hsep {n m : ℕ} (hnm : n < m) : time n + 2 * R < time m := by
    have hn : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hnm
    have hmul := mul_le_mul_of_nonneg_left hn hD.le
    dsimp only [time]
    nlinarith
  refine ⟨fun n => normalized (time n), (fun _ => normalized_mem_core _),
    (fun _ => normalized_primitive _), (fun _ => normalized_source_norm _), ?_, ?_,
    normalized_energy_zero.comp htime, normalized_jump_one.comp htime,
    normalized_graph_norm_sq_two.comp htime⟩
  · intro n
    exact hA (time n) (by
      dsimp only [time]
      exact le_add_of_nonneg_right (mul_nonneg hD.le (Nat.cast_nonneg n)))
  · intro n m hnm
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · exact separated_normalized_inner hR (hsep hlt)
    · rw [real_inner_comm]
      exact separated_normalized_inner hR (hsep hgt)

theorem no_cauchy_subsequence {p : ℕ → SourceGraph}
    (hu : ∀ n, ‖source (p n)‖ = 1)
    (ho : ∀ n m, n ≠ m → ⟪source (p n), source (p m)⟫_ℝ = 0)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : ¬ CauchySeq (fun n => source (p (φ n))) := by
  intro hC
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC 1 (by norm_num)
  have hd := hN N le_rfl (N + 1) (by omega)
  have hne : φ N ≠ φ (N + 1) := (hφ (by omega : N < N + 1)).ne
  have he : dist (source (p (φ N))) (source (p (φ (N + 1)))) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hu, hu, ho _ _ hne]
    norm_num
  nlinarith [dist_nonneg (x := source (p (φ N))) (y := source (p (φ (N + 1))))]

def primitiveBallImage : Set (Lp ℝ 2 massMeasure) :=
  source '' {p : SourceGraph | p ∈ compactCore ∧ Primitive p ∧ ‖p‖ ≤ 2}

/-- The primitive compact-core graph has a noncompact source projection. -/
theorem not_isCompact_primitiveBallImage : ¬ IsCompact primitiveBallImage := by
  intro hcpt
  obtain ⟨p, hc, hp, hu, hb, ho, _hE, _hJ, _hG⟩ := exists_primitive_escape
  have hmem (n : ℕ) : source (p n) ∈ primitiveBallImage :=
    ⟨p n, ⟨hc n, hp n, hb n⟩, rfl⟩
  obtain ⟨a, _ha, φ, hφ, hconv⟩ := hcpt.tendsto_subseq hmem
  exact no_cauchy_subsequence hu ho hφ hconv.cauchySeq

/-- No strictly positive uniform signed margin is compatible with the original primitive core. -/
theorem no_positive_primitive_margin :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ p : SourceGraph,
      p ∈ compactCore → Primitive p → ε * ‖source p‖ ^ 2 ≤ sourceEnergy p := by
  rintro ⟨ε, hε, hgap⟩
  obtain ⟨p, hc, hp, hu, _hb, _ho, hE, _hJ, _hG⟩ := exists_primitive_escape
  obtain ⟨n, hn⟩ := (hE.eventually_lt_const hε).exists
  have hl := hgap (p n) (hc n) (hp n)
  rw [hu, one_pow, mul_one] at hl
  exact hl.not_gt hn

end RHTower.CHMDEscape
