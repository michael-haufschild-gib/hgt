import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# Height truncations carry the index to the limit

The transfer theorem at work on truncated families. Cutting a zero configuration at height `T`
(`heightConfig`) leaves finitely many zeros, so the truncated orbit kernel `K_T` is Krein–Langer
(`isKreinLanger_orbitKernel_height`), with one hyperbolic pair per seen right zero of height `≤ T`.

**Pointwise convergence** (`tendsto_orbitKernel_height`). `K_T → K` pointwise as `T → ∞`, by
dominated convergence of the zero sum: the summands are absolutely summable on a tempered
configuration.

**The index of the limit is the supremum of the truncated indices**
(`negIndex_orbitKernel_eq_iSup_height`). One inequality is the monotonicity of the seen right
zeros; the other is the closedness of bounded index under pointwise limits. So the index, and in
particular positivity, passes from the finite Krein–Langer truncations to the full kernel in the
kernel topology (`isPosDefKernel_orbitKernel_iff_height`): RH is the positivity of every height
truncation of the Weil kernel of `ζ` (`riemannHypothesis_iff_height_truncations_posDef`).
-/

open Complex Finset Filter Topology
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests rightZeros
  summable_norm_Wsummand cx_contDiff cx_hasCompactSupport translate_contDiff
  translate_hasCompactSupport)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros seenRightZeros_cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- The zeros of height at most `T`. -/
def heightConfig (Z : ZeroConfig) (T : ℝ) : ZeroConfig where
  carrier := {ρ ∈ Z.carrier | |ρ.im| ≤ T}
  mult := Z.mult
  one_le_mult ρ hρ := Z.one_le_mult ρ hρ.1
  strip ρ hρ := Z.strip ρ hρ.1
  reflect_mem ρ hρ := ⟨Z.reflect_mem ρ hρ.1, by
    rw [show (reflect ρ).im = ρ.im by simp [reflect]]; exact hρ.2⟩
  mult_reflect ρ hρ := Z.mult_reflect ρ hρ.1
  finite_window T₁ T₂ := (Z.finite_window T₁ T₂).subset fun _ hρ => ⟨hρ.1.1, hρ.2⟩

theorem temperedConfig_heightConfig {Z : ZeroConfig} (hZ : TemperedConfig Z) (T : ℝ) :
    TemperedConfig (heightConfig Z T) :=
  (hZ.comp_injective (Set.inclusion_injective (fun _ h => h.1 :
    (heightConfig Z T).carrier ⊆ Z.carrier))).congr fun _ => rfl

theorem finite_heightConfig (Z : ZeroConfig) (T : ℝ) : (heightConfig Z T).carrier.Finite :=
  (Z.finite_window (-T - 1) T).subset fun ρ hρ =>
    ⟨hρ.1, by have := abs_le.mp hρ.2; constructor <;> linarith⟩

/-- **The height truncations are Krein–Langer.** -/
theorem isKreinLanger_orbitKernel_height {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (T : ℝ) : IsKreinLanger (orbitKernel (heightConfig Z T) f) :=
  (isKreinLanger_orbitKernel_iff (temperedConfig_heightConfig hZ T) hf).mpr
    ((finite_heightConfig Z T).subset fun _ h => h.1)

/-- The summand of the orbit kernel is a Weil summand of a test and its translate. -/
theorem orbitTerm_eq_Wsummand (Z : ZeroConfig) (f : ℝ → ℝ) (u : HeckeLattice) (ρ : ℂ) :
    orbitTerm Z f u ρ = Z.Wsummand (cx f) (shiftTest (scale heckeLogScale u) (cx f)) ρ := by
  have h := ArithmeticOrientationGeometry.Wsummand_scaleShift Z 0 (scale heckeLogScale u) f f ρ
  rw [ArithmeticCastelnuovoSeveri.scaleShift_zero] at h
  rw [← ArithmeticOrientationGeometry.cx_scaleShift_eq_translate, h, orbitTerm, logChar_apply]
  congr 2
  simp only [Complex.ofReal_zero]
  ring

theorem summable_norm_orbitTerm {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (u : HeckeLattice) :
    Summable fun ρ : Z.carrier => ‖orbitTerm Z f u ρ‖ := by
  simp only [orbitTerm_eq_Wsummand]
  exact summable_norm_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (translate_contDiff (cx_contDiff hf.1) _) (translate_hasCompactSupport (cx_hasCompactSupport hf.2) _)

/-- The truncated kernel as a sum over the whole carrier. -/
theorem orbitKernel_height_eq_tsum (Z : ZeroConfig) (f : ℝ → ℝ) (T : ℝ) (u : HeckeLattice) :
    orbitKernel (heightConfig Z T) f u =
      ∑' ρ : Z.carrier, if |(ρ : ℂ).im| ≤ T then orbitTerm Z f u ρ else 0 := by
  rw [orbitKernel_eq_tsum, show orbitTerm (heightConfig Z T) f u = orbitTerm Z f u from rfl,
    _root_.tsum_subtype, _root_.tsum_subtype (Z.carrier)
      (fun ρ => if |ρ.im| ≤ T then orbitTerm Z f u ρ else 0)]
  refine tsum_congr fun ρ => ?_
  by_cases hc : ρ ∈ Z.carrier
  · by_cases hT : |ρ.im| ≤ T
    · rw [Set.indicator_of_mem (show ρ ∈ (heightConfig Z T).carrier from ⟨hc, hT⟩),
        Set.indicator_of_mem hc, if_pos hT]
    · rw [Set.indicator_of_notMem (fun h => hT h.2), Set.indicator_of_mem hc, if_neg hT]
  · rw [Set.indicator_of_notMem (fun h => hc h.1), Set.indicator_of_notMem hc]

/-- **The truncated kernels converge pointwise to the orbit kernel.** -/
theorem tendsto_orbitKernel_height {Z : ZeroConfig} (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (u : HeckeLattice) :
    Tendsto (fun T : ℕ => orbitKernel (heightConfig Z T) f u) atTop (𝓝 (orbitKernel Z f u)) := by
  simp only [orbitKernel_height_eq_tsum]
  rw [orbitKernel_eq_tsum]
  refine tendsto_tsum_of_dominated_convergence (summable_norm_orbitTerm hZ hf u) (fun ρ => ?_)
    (Eventually.of_forall fun T ρ => ?_)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|(ρ : ℂ).im|⌉₊] with T hT
    rw [if_pos ((Nat.le_ceil _).trans (by exact_mod_cast hT))]
  · split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _

/-- **The index of the orbit kernel is the supremum of the indices of its height truncations.** -/
theorem negIndex_orbitKernel_eq_iSup_height {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {f : ℝ → ℝ} (hf : f ∈ realTests) :
    negIndex (orbitKernel Z f) = ⨆ T : ℕ, negIndex (orbitKernel (heightConfig Z T) f) := by
  refine le_antisymm ?_ (iSup_le fun T => ?_)
  · exact negIndex_le_of_tendsto (fun u => tendsto_orbitKernel_height hZ hf u)
      (Eventually.of_forall fun _ => isHermKernel_orbitKernel _ _)
      (Eventually.of_forall fun T => le_iSup (fun T : ℕ => negIndex (orbitKernel
        (heightConfig Z T) f)) T)
  · rw [negIndex_orbitKernel _ (temperedConfig_heightConfig hZ T) hf, negIndex_orbitKernel Z hZ hf]
    exact Set.encard_le_encard fun ρ hρ => ⟨hρ.1.1, hρ.2⟩

/-- Positivity of the orbit kernel is positivity of every height truncation. -/
theorem isPosDefKernel_orbitKernel_iff_height {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {f : ℝ → ℝ} (hf : f ∈ realTests) :
    IsPosDefKernel (orbitKernel Z f) ↔ ∀ T : ℕ, IsPosDefKernel (orbitKernel (heightConfig Z T) f) := by
  simp only [isPosDefKernel_iff (isHermKernel_orbitKernel _ _),
    negIndex_orbitKernel_eq_iSup_height hZ hf, ENat.iSup_eq_zero]

/-- **RH is positivity of every height truncation of the Weil kernel of `ζ`.** -/
theorem riemannHypothesis_iff_height_truncations_posDef :
    RiemannHypothesis ↔
      ∀ T : ℕ, IsPosDefKernel (orbitKernel (heightConfig zetaZeroConfig T)
        BiScaleUncertainty.ChebyshevGauge.cubicSpline) := by
  refine ((riemannHypothesis_tfae_zetaKernel Nat.prime_two Nat.prime_three
    (by norm_num)).out 0 1).trans ?_
  exact isPosDefKernel_orbitKernel_iff_height temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests

end GaloisForLFunctions.HeckeKreinToeplitz
