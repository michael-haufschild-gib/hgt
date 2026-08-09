import GaloisForLFunctions.RHTower.DiagonalMultiplierSpectrum
import GaloisForLFunctions.RHTower.TwoPrimeKummerPrecisionHorizon

/-!
# The two-prime Kummer essential spectrum and the compact-repair no-go

The bounded Kummer phase transform on the full two-prime frequency lattice has

* point spectrum exactly the bounded phase values `β(μ)` of the nonzero modes;
* spectrum the whole interval `[-1, 1]`;
* a singular Weyl sequence at every point of `[-1, 1]`, built from an injective family of
  coordinate modes;

and consequently no compact perturbation of it is injective with closed range.
-/

open Filter
open scoped Topology InnerProductSpace ENNReal

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The nonzero modes of the two-prime frequency lattice. -/
def NonzeroKummerMode := {p : ℤ × ℤ // p ≠ (0, 0)}

instance : DecidableEq NonzeroKummerMode := Subtype.instDecidableEq

instance : Nonempty NonzeroKummerMode :=
  ⟨⟨(1, 0), by
    intro hcon
    have := congrArg Prod.fst hcon
    simp at this⟩⟩

/-- The bounded Kummer phase symbol of a nonzero mode. -/
noncomputable def kummerFullSymbol (p : NonzeroKummerMode) : ℂ :=
  ((kummerBeta (kummerFreq p.1) : ℝ) : ℂ)

theorem norm_kummerFullSymbol (p : NonzeroKummerMode) :
    ‖kummerFullSymbol p‖ = |kummerFreq p.1| / (1 + |kummerFreq p.1|) := by
  rw [kummerFullSymbol, Complex.norm_real, Real.norm_eq_abs, abs_kummerBeta]

theorem norm_kummerFullSymbol_le_one (p : NonzeroKummerMode) : ‖kummerFullSymbol p‖ ≤ 1 := by
  rw [norm_kummerFullSymbol]
  rw [div_le_one (by positivity)]
  linarith [abs_nonneg (kummerFreq p.1)]

/-- The bounded Kummer phase transform on the full two-prime lattice. -/
noncomputable def kummerTransform :
    lp (fun _ : NonzeroKummerMode => ℂ) 2 →L[ℂ] lp (fun _ : NonzeroKummerMode => ℂ) 2 :=
  deningerMultiplier norm_kummerFullSymbol_le_one

/-! ## Point spectrum -/

/-- Every bounded phase value is an eigenvalue with coordinate eigenvector. -/
theorem kummerTransform_eigen (p : NonzeroKummerMode) :
    kummerTransform (lp.single 2 p (1 : ℂ)) = kummerFullSymbol p • lp.single 2 p (1 : ℂ) :=
  hasEigenvalue_deningerMultiplier norm_kummerFullSymbol_le_one p

/-- Conversely every eigenvalue is a bounded phase value. -/
theorem kummerTransform_eigenvalue_mem {lam : ℂ} {x : lp (fun _ : NonzeroKummerMode => ℂ) 2}
    (hx : x ≠ 0) (heig : kummerTransform x = lam • x) :
    lam ∈ Set.range kummerFullSymbol :=
  mem_range_of_eigenvalue norm_kummerFullSymbol_le_one hx heig

/-! ## The bounded phase profile -/

theorem continuous_kummerBeta : Continuous kummerBeta := by
  have hfun : kummerBeta = fun t : ℝ => t / (1 + |t|) := rfl
  rw [hfun]
  refine Continuous.div continuous_id (continuous_const.add continuous_abs) fun t => ?_
  positivity

theorem kummerBeta_inverse {t : ℝ} (ht : |t| < 1) : kummerBeta (t / (1 - |t|)) = t := by
  have hden : (0 : ℝ) < 1 - |t| := by linarith
  have habs : |t / (1 - |t|)| = |t| / (1 - |t|) := by
    rw [abs_div, abs_of_pos hden]
  rw [kummerBeta, habs]
  have h1 : 1 + |t| / (1 - |t|) = 1 / (1 - |t|) := by
    field_simp
    ring
  rw [h1]
  field_simp

theorem abs_kummerBeta_lt_one (t : ℝ) : |kummerBeta t| < 1 := by
  rw [abs_kummerBeta, div_lt_one (by positivity)]
  linarith

/-! ## The spectrum -/

theorem closure_range_kummerFullSymbol :
    closure (Set.range kummerFullSymbol) = (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1 := by
  have hclosed : IsClosed ((fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1) :=
    (isCompact_Icc.image Complex.continuous_ofReal).isClosed
  refine le_antisymm ?_ ?_
  · refine closure_minimal ?_ hclosed
    rintro _ ⟨p, rfl⟩
    refine ⟨kummerBeta (kummerFreq p.1), ?_, rfl⟩
    have := abs_kummerBeta_lt_one (kummerFreq p.1)
    rw [abs_lt] at this
    exact ⟨this.1.le, this.2.le⟩
  · have hIoo : (fun t : ℝ => (t : ℂ)) '' Set.Ioo (-1 : ℝ) 1
        ⊆ closure (Set.range kummerFullSymbol) := by
      rintro _ ⟨t, ht, rfl⟩
      have habs : |t| < 1 := abs_lt.mpr ⟨ht.1, ht.2⟩
      set s : ℝ := t / (1 - |t|) with hs
      obtain ⟨q, hqinj, hq0, hqlim⟩ := exists_injective_modes_tendsto s
      have hmodes : ∀ n, kummerFullSymbol ⟨q n, hq0 n⟩
          = ((kummerBeta (kummerFreq (q n)) : ℝ) : ℂ) := fun n => rfl
      have hlim : Tendsto (fun n => kummerFullSymbol ⟨q n, hq0 n⟩) atTop (𝓝 ((t : ℝ) : ℂ)) := by
        have hbeta : Tendsto (fun n => kummerBeta (kummerFreq (q n))) atTop
            (𝓝 (kummerBeta s)) := (continuous_kummerBeta.tendsto s).comp hqlim
        rw [kummerBeta_inverse habs] at hbeta
        have := (Complex.continuous_ofReal.tendsto t).comp hbeta
        simpa [hmodes, Function.comp_def] using this
      refine mem_closure_of_tendsto hlim ?_
      exact Eventually.of_forall fun n => ⟨⟨q n, hq0 n⟩, rfl⟩
    have hIcc : (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1
        ⊆ closure (Set.range kummerFullSymbol) := by
      have hcl : Set.Icc (-1 : ℝ) 1 = closure (Set.Ioo (-1 : ℝ) 1) :=
        (closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)).symm
      calc (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1
          = (fun t : ℝ => (t : ℂ)) '' closure (Set.Ioo (-1 : ℝ) 1) := by rw [hcl]
        _ ⊆ closure ((fun t : ℝ => (t : ℂ)) '' Set.Ioo (-1 : ℝ) 1) :=
            image_closure_subset_closure_image Complex.continuous_ofReal
        _ ⊆ closure (closure (Set.range kummerFullSymbol)) := closure_mono hIoo
        _ = closure (Set.range kummerFullSymbol) := closure_closure
    exact hIcc

/-- **The two-prime Kummer spectrum.**  The bounded phase transform has spectrum the full
interval `[-1, 1]`. -/
theorem spectrum_kummerTransform :
    spectrum ℂ kummerTransform = (fun t : ℝ => (t : ℂ)) '' Set.Icc (-1 : ℝ) 1 := by
  rw [kummerTransform, spectrum_deningerMultiplier, closure_range_kummerFullSymbol]

/-! ## Singular Weyl sequences -/

theorem tendsto_kummerBeta_atTop : Tendsto kummerBeta atTop (𝓝 1) := by
  have hinv : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hmain : Tendsto (fun x : ℝ => 1 - (1 + x)⁻¹) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have := hc.sub hinv
    simpa using this
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [kummerBeta, abs_of_nonneg hx]
  field_simp
  ring

theorem kummerBeta_neg (t : ℝ) : kummerBeta (-t) = -kummerBeta t := by
  rw [kummerBeta, kummerBeta, abs_neg]
  ring

/-- Every point of `[-1, 1]` is the limit of the bounded phase values along an injective family of
nonzero modes. -/
theorem exists_injective_modes_symbol_tendsto {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ q : ℕ → NonzeroKummerMode, Function.Injective q ∧
      Tendsto (fun n => kummerFullSymbol (q n)) atTop (𝓝 ((t : ℝ) : ℂ)) := by
  have hlogpos : 0 < Real.log 2 := log_two_pos
  have hlift : ∀ (f : ℕ → ℝ) (q : ℕ → NonzeroKummerMode),
      (∀ n, kummerFreq (q n).1 = f n) →
      Tendsto (fun n => kummerBeta (f n)) atTop (𝓝 t) →
      Tendsto (fun n => kummerFullSymbol (q n)) atTop (𝓝 ((t : ℝ) : ℂ)) := by
    intro f q hf hlim
    have hcast := (Complex.continuous_ofReal.tendsto t).comp hlim
    refine hcast.congr fun n => ?_
    rw [Function.comp_apply, kummerFullSymbol, hf n]
  rcases lt_trichotomy t (-1) with hlt | heq | hgt
  · exact absurd ht.1 (not_le.mpr hlt)
  · -- the lower endpoint
    refine ⟨fun n => ⟨(-(n + 1 : ℤ), 0), ?_⟩, ?_, ?_⟩
    · intro hcon
      have := congrArg Prod.fst hcon
      simp only at this
      omega
    · intro n m hnm
      have := congrArg (fun r : NonzeroKummerMode => r.1.1) hnm
      simp only at this
      omega
    · refine hlift (fun n => -(((n : ℝ) + 1) * Real.log 2)) _ (fun n => ?_) ?_
      · rw [kummerFreq]
        push_cast
        ring
      · have hpos : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log 2) atTop atTop := by
          apply Filter.Tendsto.atTop_mul_const hlogpos
          exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
        have hbeta := tendsto_kummerBeta_atTop.comp hpos
        have hneg : Tendsto (fun n : ℕ => -kummerBeta (((n : ℝ) + 1) * Real.log 2))
            atTop (𝓝 (-1)) := by
          simpa [Function.comp_def] using hbeta.neg
        rw [heq]
        refine hneg.congr fun n => ?_
        rw [kummerBeta_neg]
  rcases lt_trichotomy t 1 with hlt1 | heq1 | hgt1
  · -- the interior
    have habs : |t| < 1 := abs_lt.mpr ⟨hgt, hlt1⟩
    set s : ℝ := t / (1 - |t|) with hs
    obtain ⟨q, hqinj, hq0, hqlim⟩ := exists_injective_modes_tendsto s
    refine ⟨fun n => ⟨q n, hq0 n⟩, ?_, ?_⟩
    · intro n m hnm
      have := congrArg (fun r : NonzeroKummerMode => r.1) hnm
      exact hqinj this
    · refine hlift (fun n => kummerFreq (q n)) _ (fun n => rfl) ?_
      have hbeta : Tendsto (fun n => kummerBeta (kummerFreq (q n))) atTop (𝓝 (kummerBeta s)) :=
        (continuous_kummerBeta.tendsto s).comp hqlim
      rwa [kummerBeta_inverse habs] at hbeta
  · -- the upper endpoint
    refine ⟨fun n => ⟨((n + 1 : ℤ), 0), ?_⟩, ?_, ?_⟩
    · intro hcon
      have := congrArg Prod.fst hcon
      simp only at this
      omega
    · intro n m hnm
      have := congrArg (fun r : NonzeroKummerMode => r.1.1) hnm
      simp only at this
      omega
    · refine hlift (fun n => ((n : ℝ) + 1) * Real.log 2) _ (fun n => ?_) ?_
      · rw [kummerFreq]
        push_cast
        ring
      · have hpos : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log 2) atTop atTop := by
          apply Filter.Tendsto.atTop_mul_const hlogpos
          exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
        have hbeta := tendsto_kummerBeta_atTop.comp hpos
        rw [heq1]
        simpa [Function.comp_def] using hbeta
  · exact absurd ht.2 (not_le.mpr hgt1)

/-- **The essential spectrum.**  Every point of `[-1, 1]` carries a singular Weyl sequence built
from an injective family of coordinate modes. -/
theorem exists_singular_weylSequence {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ q : ℕ → NonzeroKummerMode, Function.Injective q ∧
      (∀ n, ‖(lp.single 2 (q n) (1 : ℂ) : lp (fun _ : NonzeroKummerMode => ℂ) 2)‖ = 1) ∧
      (∀ z : lp (fun _ : NonzeroKummerMode => ℂ) 2,
        Tendsto (fun n => ⟪z, (lp.single 2 (q n) (1 : ℂ)
          : lp (fun _ : NonzeroKummerMode => ℂ) 2)⟫_ℂ) atTop (𝓝 0)) ∧
      Tendsto (fun n => ‖kummerTransform (lp.single 2 (q n) (1 : ℂ))
        - ((t : ℝ) : ℂ) • lp.single 2 (q n) (1 : ℂ)‖) atTop (𝓝 0) := by
  obtain ⟨q, hqinj, hqlim⟩ := exists_injective_modes_symbol_tendsto ht
  refine ⟨q, hqinj, fun n => norm_lp_single_one (q n), fun z => ?_, ?_⟩
  · exact tendsto_inner_lp_single_zero hqinj z
  · exact tendsto_weylSequence norm_kummerFullSymbol_le_one q hqlim

/-! ## The compact-repair no-go -/

/-- **Compact corrections cannot close the Kummer horizon.**  No compact perturbation of the
bounded two-prime Kummer transform is injective with closed range. -/
theorem not_injective_and_isClosed_range_kummerTransform_add_compact
    (K : lp (fun _ : NonzeroKummerMode => ℂ) 2 →L[ℂ] lp (fun _ : NonzeroKummerMode => ℂ) 2)
    (hK : IsCompactOperator K) :
    ¬ (Function.Injective (kummerTransform + K) ∧
      IsClosed (Set.range (kummerTransform + K))) := by
  obtain ⟨q, hqinj, hnorm, hweak, hdefect⟩ :=
    exists_singular_weylSequence (t := 0) (by norm_num)
  have hzero : Tendsto (fun n => kummerTransform (lp.single 2 (q n) (1 : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hdefect.congr fun n => ?_
    norm_num
  exact GaloisForLFunctions.HTGeometry.not_injective_and_isClosed_range_of_weaklyNull
    kummerTransform K hK (fun n => lp.single 2 (q n) (1 : ℂ)) hnorm hweak hzero

end GaloisForLFunctions.RHTower
