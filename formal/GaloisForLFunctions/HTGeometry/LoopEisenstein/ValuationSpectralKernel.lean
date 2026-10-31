import GaloisForLFunctions.HTGeometry.LoopEisenstein.DiscreteHaarMagnitude
import GaloisForLFunctions.HTGeometry.LocalRankOneIntegral

/-!
# Local spherical integrals in normalized valuation coordinates

A normalized uniformizer identifies each valuation shell by its exact radius.
The residue-normalized Iwasawa magnitude is a residue-cardinality power there,
so the radial spectral character equals the integrable spherical shell kernel.
-/

open scoped WithZero WithZeroMulInt NNReal
open GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable (L : Type*) [Field L] [Valued L ℤᵐ⁰]
variable (π : Integer L) (hπ : Irreducible π)
variable (hπv : Valued.v (π : L) = WithZero.exp (-1 : ℤ))
include hπv

/-- Normalized inverse-uniformizer balls are exactly valuation sublevel sets. -/
theorem mem_integralDilate_iff_valuation_le_exp (n : ℕ) (x : L) :
    x ∈ integralDilate L π hπ n ↔ Valued.v x ≤ WithZero.exp (n : ℤ) := by
  rw [mem_integralDilate]
  change Valued.v ((π : L) ^ n * x) ≤ 1 ↔ Valued.v x ≤ WithZero.exp (n : ℤ)
  by_cases hx : x = 0
  · simp only [hx, mul_zero, map_zero, zero_le, iff_self]
  · let m : ℤ := WithZero.log (Valued.v x)
    have he : Valued.v x = WithZero.exp m :=
      (WithZero.exp_log ((Valued.v : Valuation L ℤᵐ⁰).ne_zero_iff.mpr hx)).symm
    rw [map_mul, map_pow, hπv, he, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    change WithZero.exp (n • (-1 : ℤ) + m) ≤ WithZero.exp (0 : ℤ) ↔
      WithZero.exp m ≤ WithZero.exp (n : ℤ)
    rw [WithZero.exp_le_exp, WithZero.exp_le_exp]
    simp only [nsmul_eq_mul, mul_neg, mul_one]
    omega

/-- Shell zero is the integer ball; every later shell has its exact integer radius. -/
theorem valuationShell_max_valuation (n : ℕ) {x : L}
    (hx : x ∈ valuationShell L π hπ n) :
    max 1 (Valued.v x) = WithZero.exp (n : ℤ) := by
  cases n with
  | zero =>
    have h : x ∈ integralDilate L π hπ 0 := by
      simpa only [valuationShell, disjointed_zero] using hx
    have hv := (mem_integralDilate_iff_valuation_le_exp L π hπ hπv 0 x).mp h
    change Valued.v x ≤ 1 at hv
    exact max_eq_left hv
  | succ n =>
    rw [valuationShell, (integralDilate_monotone L π hπ).disjointed_add_one] at hx
    have hhi := (mem_integralDilate_iff_valuation_le_exp L π hπ hπv (n + 1) x).mp hx.1
    have hlo : WithZero.exp (n : ℤ) < Valued.v x :=
      lt_of_not_ge (fun h => hx.2 ((mem_integralDilate_iff_valuation_le_exp L π hπ hπv n x).mpr h))
    have hxv : Valued.v x ≠ 0 := by
      intro hz
      rw [hz] at hlo
      exact not_lt_zero hlo
    let m : ℤ := WithZero.log (Valued.v x)
    have he : Valued.v x = WithZero.exp m := (WithZero.exp_log hxv).symm
    rw [he, WithZero.exp_lt_exp] at hlo
    rw [he, WithZero.exp_le_exp] at hhi
    have hm : m = (n + 1 : ℕ) := by omega
    rw [he, hm, max_eq_right]
    change WithZero.exp (0 : ℤ) ≤ WithZero.exp ((n + 1 : ℕ) : ℤ)
    exact WithZero.exp_le_exp.mpr (by omega)

/-- Any order-preserving exponential normalization reads radius `n` as `q^n`. -/
theorem valuationShell_normalizedMagnitude {q : ℝ≥0} (hq : 1 < q) (n : ℕ) {x : L}
    (hx : x ∈ valuationShell L π hπ n) :
    max 1 (WithZeroMulInt.toNNReal hq.ne_zero (Valued.v x)) = q ^ n := by
  let f := WithZeroMulInt.toNNReal hq.ne_zero
  have hm : Monotone f := (WithZeroMulInt.toNNReal_strictMono hq).monotone
  calc
    max 1 (f (Valued.v x)) = max (f 1) (f (Valued.v x)) := by rw [map_one]
    _ = f (max 1 (Valued.v x)) := hm.map_max.symm
    _ = q ^ n := by
      rw [valuationShell_max_valuation L π hπ hπv n hx]
      change WithZeroMulInt.toNNReal hq.ne_zero (WithZero.exp (n : ℤ)) = q ^ n
      rw [WithZeroMulInt.toNNReal_neg_apply hq.ne_zero WithZero.exp_ne_zero]
      change q ^ (n : ℤ) = q ^ n
      exact zpow_natCast q n

omit hπv in
/-- Spectral parameter corresponding to residue cardinality `q`. -/
def localSpectralParameter (q : ℝ≥0) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (q : ℝ) : ℂ))

omit hπv in
/-- The radial character written directly in the normalized valuation. -/
def valuationSpectralKernel (q : ℝ≥0) (hq : 1 < q) (s : ℂ) (x : L) : ℂ :=
  Complex.exp (-(s + 1) *
    (Real.log (max 1 (WithZeroMulInt.toNNReal hq.ne_zero (Valued.v x) : ℝ)) : ℂ))

omit hπv in
private theorem spectral_base (q : ℝ≥0) (hq : 1 < q) (s : ℂ) :
    ((q : ℝ) : ℂ)⁻¹ * localSpectralParameter q s =
      Complex.exp (-(s + 1) * (Real.log (q : ℝ) : ℂ)) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (zero_lt_one.trans hq)
  have he : Complex.exp (-(Real.log (q : ℝ) : ℂ)) = ((q : ℝ) : ℂ)⁻¹ := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hqpos]
  rw [← he, localSpectralParameter, ← Complex.exp_add]
  congr 1
  ring

omit hπv in
/-- The right half-plane maps into the local spherical convergence disk. -/
theorem localSpectralParameter_norm_lt_one (q : ℝ≥0) (hq : 1 < q) (s : ℂ)
    (hs : 0 < s.re) : ‖localSpectralParameter q s‖ < 1 := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  rw [localSpectralParameter, Complex.norm_exp, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith only [mul_pos hs hlog]

variable [(Valued.v : Valuation L ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer L)]
local instance : (Valued.v : Valuation L ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)
local instance : NormedField L := Valued.toNormedField L ℤᵐ⁰
local instance : ProperSpace L :=
  Valued.integer.properSpace_iff_compactSpace_integer.mpr inferInstance
local instance : MeasurableSpace L := borel L
local instance : BorelSpace L := ⟨rfl⟩

omit hπv in
private theorem residue_card_nnreal_gt_one : (1 : ℝ≥0) < Nat.card (Residue L) := by
  exact_mod_cast residue_card_gt_one L

/-- The independently defined normalized valuation character is the actual shell kernel. -/
theorem sphericalKernel_eq_valuationSpectralKernel (s : ℂ) (x : L) :
    sphericalKernel L π hπ (localSpectralParameter (Nat.card (Residue L)) s) x =
      valuationSpectralKernel L (Nat.card (Residue L)) (residue_card_nnreal_gt_one L) s x := by
  have hx : x ∈ ⋃ n, valuationShell L π hπ n := by
    rw [iUnion_valuationShell]
    exact Set.mem_univ _
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  rw [sphericalKernel_on_shell L π hπ _ n hn, valuationSpectralKernel]
  have hmag := valuationShell_normalizedMagnitude L π hπ hπv
    (residue_card_nnreal_gt_one L) n hn
  have hreal : max 1
      (WithZeroMulInt.toNNReal (residue_card_nnreal_gt_one L).ne_zero (Valued.v x) : ℝ) =
      (Nat.card (Residue L) : ℝ) ^ n := by exact_mod_cast hmag
  rw [hreal, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hb := spectral_base (Nat.card (Residue L)) (residue_card_nnreal_gt_one L) s
  simp only [NNReal.coe_natCast, Complex.ofReal_natCast] at hb
  rw [hb, ← Complex.exp_nat_mul]
  congr 1
  ring

open MeasureTheory

include hπ

/-- The normalized radial character is absolutely integrable for positive real spectral part. -/
theorem valuationSpectralKernel_integrable_of_uniformizer (s : ℂ) (hs : 0 < s.re) :
    Integrable
      (valuationSpectralKernel L (Nat.card (Residue L)) (residue_card_nnreal_gt_one L) s)
      (normalizedHaar L) := by
  have he := funext (sphericalKernel_eq_valuationSpectralKernel L π hπ hπv s)
  rw [← he]
  exact sphericalKernel_integrable L π hπ
    (localSpectralParameter_norm_lt_one _ (residue_card_nnreal_gt_one L) s hs)

/-- Exact local intertwining factor for the normalized valuation character. -/
theorem integral_valuationSpectralKernel_of_uniformizer (s : ℂ) (hs : 0 < s.re) :
    (∫ x, valuationSpectralKernel L (Nat.card (Residue L))
        (residue_card_nnreal_gt_one L) s x ∂normalizedHaar L) =
      (1 - (Nat.card (Residue L) : ℂ)⁻¹ * localSpectralParameter (Nat.card (Residue L)) s) /
        (1 - localSpectralParameter (Nat.card (Residue L)) s) := by
  have he := funext (sphericalKernel_eq_valuationSpectralKernel L π hπ hπv s)
  rw [← he]
  exact integral_sphericalKernel L π hπ
    (localSpectralParameter_norm_lt_one _ (residue_card_nnreal_gt_one L) s hs)

omit hπ hπv in
/-- Valuations attaining `exp(-1)` need no chosen uniformizer in the integrability statement. -/
theorem valuationSpectralKernel_integrable
    (hrange : WithZero.exp (-1 : ℤ) ∈ Set.range (Valued.v : Valuation L ℤᵐ⁰))
    (s : ℂ) (hs : 0 < s.re) :
    Integrable
      (valuationSpectralKernel L (Nat.card (Residue L)) (residue_card_nnreal_gt_one L) s)
      (normalizedHaar L) := by
  obtain ⟨π, hπ, hπv⟩ := exists_irreducible_valuation_exp_neg_one L hrange
  exact valuationSpectralKernel_integrable_of_uniformizer L π hπ hπv s hs

omit hπ hπv in
/-- The actual local factor depends only on the residue field and normalized valuation. -/
theorem integral_valuationSpectralKernel
    (hrange : WithZero.exp (-1 : ℤ) ∈ Set.range (Valued.v : Valuation L ℤᵐ⁰))
    (s : ℂ) (hs : 0 < s.re) :
    (∫ x, valuationSpectralKernel L (Nat.card (Residue L))
        (residue_card_nnreal_gt_one L) s x ∂normalizedHaar L) =
      (1 - (Nat.card (Residue L) : ℂ)⁻¹ * localSpectralParameter (Nat.card (Residue L)) s) /
        (1 - localSpectralParameter (Nat.card (Residue L)) s) := by
  obtain ⟨π, hπ, hπv⟩ := exists_irreducible_valuation_exp_neg_one L hrange
  exact integral_valuationSpectralKernel_of_uniformizer L π hπ hπv s hs

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.valuationShell_normalizedMagnitude
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.valuationSpectralKernel_integrable
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.integral_valuationSpectralKernel
