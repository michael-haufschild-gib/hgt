import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierL2
import GaloisForLFunctions.RHTower.FieldOnePadicSoninSigma
import GaloisForLFunctions.RHTower.FieldOnePadicValuationUnitDecomposition

/-!
# Local p-adic Sonin space in Haar L²

Literal gap projections, valuation shells, and the Connes--Consani--Moscovici
generator in the whole `L²(ℚ_p)` Fourier theory.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance (q : Prop) : Decidable q := Classical.propDecidable q

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Pointwise ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

def fieldOnePadicSoninBallSet (m : ℤ) : Set ℚ_[p] :=
  {x | (((fieldOnePadicPrimeUnit p) ^ m : ℚ_[p]ˣ) * x) ∈
    fieldOnePadicUnitBall p}

theorem fieldOnePadicSoninBallSet_isClopen (m : ℤ) :
    IsClopen (fieldOnePadicSoninBallSet p m) := by
  let h : ℚ_[p] ≃ₜ ℚ_[p] :=
    Homeomorph.smul ((fieldOnePadicPrimeUnit p) ^ m)
  change IsClopen (h ⁻¹' fieldOnePadicUnitBall p)
  exact (fieldOnePadicUnitBall_isClopen p).preimage h.continuous

theorem fieldOnePadicSoninUnitBall_apply (x : ℚ_[p]) :
    (fieldOnePadicSoninUnitBall p).1 x =
      if x ∈ fieldOnePadicUnitBall p then 1 else 0 := by
  classical
  by_cases hx : x ∈ fieldOnePadicUnitBall p
  · obtain ⟨u, rfl⟩ := hx
    have hu : ((u : ℤ_[p]) : ℚ_[p]) ∈ fieldOnePadicUnitBall p :=
      ⟨u, rfl⟩
    rw [if_pos hu]
    exact fieldOnePadicSoninUnitBall_apply_coe p u
  · rw [if_neg hx]
    exact fieldOnePadicSoninUnitBall_apply_eq_zero_of_notMem p hx

@[simp] theorem fieldOnePadicSoninBall_apply_eq_indicator
    (m : ℤ) (x : ℚ_[p]) :
    (fieldOnePadicSoninBall p m).1 x =
      if x ∈ fieldOnePadicSoninBallSet p m then 1 else 0 := by
  classical
  rw [fieldOnePadicSoninBall_apply,
    fieldOnePadicSoninUnitBall_apply]
  rfl

theorem fieldOnePadicSoninBallSet_mem_iff_valuation
    (m : ℤ) {x : ℚ_[p]} (hx : x ≠ 0) :
    x ∈ fieldOnePadicSoninBallSet p m ↔
      0 ≤ m + Padic.valuation x := by
  rw [show x ∈ fieldOnePadicSoninBallSet p m ↔
    ‖(((fieldOnePadicPrimeUnit p) ^ m : ℚ_[p]ˣ) : ℚ_[p]) *
      x‖ ≤ 1 by
    constructor
    · rintro ⟨z, hz⟩
      rw [← hz]
      exact z.property
    · intro hz
      exact ⟨⟨_, hz⟩, rfl⟩]
  rw [Padic.norm_le_one_iff_val_nonneg]
  rw [Padic.valuation_mul]
  · rw [show (((fieldOnePadicPrimeUnit p) ^ m : ℚ_[p]ˣ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ m by simp [fieldOnePadicPrimeUnit]]
    rw [Padic.valuation_zpow, Padic.valuation_p]
    simp
  · exact Units.ne_zero ((fieldOnePadicPrimeUnit p) ^ m)
  · exact hx

theorem fieldOnePadicSoninBallSet_mem_forward_iff
    (m k : ℤ) (u : ℤ_[p]ˣ) :
    ((fieldOnePadicValuationUnitForward p
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) ∈
      fieldOnePadicSoninBallSet p m ↔ 0 ≤ m + k := by
  rw [fieldOnePadicSoninBallSet_mem_iff_valuation p m (Units.ne_zero _),
    fieldOnePadic_valuation_forward]
  simp

@[simp] theorem fieldOnePadicSoninShell_apply_forward
    (n k : ℤ) (u : ℤ_[p]ˣ) :
    (fieldOnePadicSoninShell p n).1
        ((fieldOnePadicValuationUnitForward p
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) =
      if k = -n then 1 else 0 := by
  rw [fieldOnePadicSoninShell]
  change (fieldOnePadicSoninBall p n).1 _ -
    (fieldOnePadicSoninBall p (n - 1)).1 _ = _
  rw [fieldOnePadicSoninBall_apply_eq_indicator,
    fieldOnePadicSoninBall_apply_eq_indicator,
    fieldOnePadicSoninBallSet_mem_forward_iff,
    fieldOnePadicSoninBallSet_mem_forward_iff]
  by_cases hk : k = -n
  · subst k
    simp
  · have hiff : (0 ≤ n + k ↔ 0 ≤ n - 1 + k) := by omega
    split <;> split <;> simp_all

@[simp] theorem fieldOnePadicSoninShell_apply_zero (n : ℤ) :
    (fieldOnePadicSoninShell p n).1 0 = 0 := by
  rw [fieldOnePadicSoninShell]
  change (fieldOnePadicSoninUnitBall p).1
      (((fieldOnePadicPrimeUnit p) ^ n : ℚ_[p]ˣ) * 0) -
    (fieldOnePadicSoninUnitBall p).1
      (((fieldOnePadicPrimeUnit p) ^ (n - 1) : ℚ_[p]ˣ) * 0) = 0
  simp

def fieldOnePadicL2SetProjection
    (s : Set ℚ_[p]) (hs : MeasurableSet s) :
    FieldOnePadicL2 p →L[ℂ] FieldOnePadicL2 p :=
  let T : FieldOnePadicL2 p →ₗ[ℂ] FieldOnePadicL2 p := {
    toFun := fun f => ((Lp.memLp f).indicator hs).toLp
      (s.indicator fun x => f x)
    map_add' := by
      intro f g
      let hf := (Lp.memLp f).indicator hs
      let hg := (Lp.memLp g).indicator hs
      calc
        ((Lp.memLp (f + g)).indicator hs).toLp
            (s.indicator fun x => (f + g) x) =
            (hf.add hg).toLp
              ((s.indicator fun x => f x) +
                (s.indicator fun x => g x)) := by
          apply MemLp.toLp_congr
          exact (Lp.coeFn_add f g).mono fun x hx => by
            by_cases hxs : x ∈ s
            · rw [Set.indicator_of_mem hxs, Pi.add_apply,
                Set.indicator_of_mem hxs, Set.indicator_of_mem hxs]
              simpa only [Pi.add_apply] using hx
            · rw [Set.indicator_of_notMem hxs, Pi.add_apply,
                Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs,
                add_zero]
        _ = hf.toLp (s.indicator fun x => f x) +
              hg.toLp (s.indicator fun x => g x) :=
          hf.toLp_add hg
    map_smul' := by
      intro c f
      let hf := (Lp.memLp f).indicator hs
      calc
        ((Lp.memLp (c • f)).indicator hs).toLp
            (s.indicator fun x => (c • f) x) =
            (hf.const_smul c).toLp
              (c • (s.indicator fun x => f x)) := by
          apply MemLp.toLp_congr
          filter_upwards [Lp.coeFn_smul c f] with x hx
          by_cases hxs : x ∈ s <;>
            simp [Set.indicator, hxs, hx]
        _ = c • hf.toLp (s.indicator fun x => f x) :=
          hf.toLp_const_smul c }
  T.mkContinuous 1 fun f => by
    change ‖((Lp.memLp f).indicator hs).toLp
      (s.indicator fun x => f x)‖ ≤ 1 * ‖f‖
    rw [one_mul, Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_indicator_le fun x => f x)

theorem fieldOnePadicL2SetProjection_ae
    (s : Set ℚ_[p]) (hs : MeasurableSet s) (f : FieldOnePadicL2 p) :
    (fieldOnePadicL2SetProjection p s hs f : ℚ_[p] → ℂ) =ᵐ[
      fieldOnePadicUnitBallNormalizedHaar p]
      s.indicator fun x => f x :=
  ((Lp.memLp f).indicator hs).coeFn_toLp

def fieldOnePadicSoninInnerBall : Set ℚ_[p] :=
  fieldOnePadicSoninBallSet p (-1)

def fieldOnePadicSoninOuterFourierBall : Set ℚ_[p] :=
  fieldOnePadicSoninBallSet p 1

theorem fieldOnePadicSoninInnerBall_measurable :
    MeasurableSet (fieldOnePadicSoninInnerBall p) :=
  (fieldOnePadicSoninBallSet_isClopen p (-1)).isOpen.measurableSet

def FieldOnePadicSoninL2 : Submodule ℂ (FieldOnePadicL2 p) :=
  LinearMap.ker (fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)).toLinearMap ⊓
    LinearMap.ker ((fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)).comp
        (fieldOnePadicL2Fourier p).toLinearIsometry.toContinuousLinearMap).toLinearMap

def fieldOnePadicSoninSigmaL2 : FieldOnePadicL2 p :=
  fieldOnePadicBruhatToL2Linear p (fieldOnePadicSoninSigma p)

@[simp] theorem fieldOnePadicL2Fourier_soninSigma :
    fieldOnePadicL2Fourier p (fieldOnePadicSoninSigmaL2 p) =
      fieldOnePadicSoninSigmaL2 p := by
  rw [fieldOnePadicSoninSigmaL2, fieldOnePadicL2Fourier_bruhat]
  rw [show fieldOnePadicBruhatFourierLinearEquiv p
      (fieldOnePadicSoninSigma p) = fieldOnePadicSoninSigma p by
    exact fieldOnePadicBruhatFourier_soninSigma p]

theorem fieldOnePadicSoninSigma_apply_eq_zero_on_inner
    {x : ℚ_[p]} (hx : x ∈ fieldOnePadicSoninInnerBall p) :
    (fieldOnePadicSoninSigma p).1 x = 0 := by
  classical
  change x ∈ fieldOnePadicSoninBallSet p (-1) at hx
  rw [fieldOnePadicSoninSigma, fieldOnePadicSoninShell]
  change ((fieldOnePadicSoninBall p 0).1 x -
      (fieldOnePadicSoninBall p (0 - 1)).1 x) -
    (p : ℂ)⁻¹ * ((fieldOnePadicSoninBall p 1).1 x -
      (fieldOnePadicSoninBall p (1 - 1)).1 x) = 0
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hv : 0 ≤ (-1 : ℤ) + Padic.valuation x :=
    (fieldOnePadicSoninBallSet_mem_iff_valuation p (-1) hx0).mp hx
  have h0mem : x ∈ fieldOnePadicSoninBallSet p 0 :=
    (fieldOnePadicSoninBallSet_mem_iff_valuation p 0 hx0).mpr (by omega)
  have h1mem : x ∈ fieldOnePadicSoninBallSet p 1 :=
    (fieldOnePadicSoninBallSet_mem_iff_valuation p 1 hx0).mpr (by omega)
  rw [fieldOnePadicSoninBall_apply_eq_indicator,
    fieldOnePadicSoninBall_apply_eq_indicator,
    fieldOnePadicSoninBall_apply_eq_indicator,
    fieldOnePadicSoninBall_apply_eq_indicator]
  simp [hx, h0mem, h1mem]

theorem fieldOnePadicL2SetProjection_soninSigma_eq_zero :
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)
      (fieldOnePadicSoninSigmaL2 p) = 0 := by
  apply Lp.ext
  filter_upwards [fieldOnePadicL2SetProjection_ae p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)
      (fieldOnePadicSoninSigmaL2 p),
    fieldOnePadicBruhatToL2_ae p (fieldOnePadicSoninSigma p),
    Lp.coeFn_zero ℂ 2 (fieldOnePadicUnitBallNormalizedHaar p)]
    with x hproj hsigma hzero
  rw [hproj, hzero]
  by_cases hx : x ∈ fieldOnePadicSoninInnerBall p
  · rw [Set.indicator_of_mem hx]
    rw [show (fieldOnePadicSoninSigmaL2 p : ℚ_[p] → ℂ) x =
        (fieldOnePadicSoninSigma p).1 x by
      change (fieldOnePadicBruhatToL2 p
        (fieldOnePadicSoninSigma p) : ℚ_[p] → ℂ) x = _
      exact hsigma]
    exact fieldOnePadicSoninSigma_apply_eq_zero_on_inner p hx
  · rw [Set.indicator_of_notMem hx]
    rfl

theorem fieldOnePadicSoninSigmaL2_mem :
    fieldOnePadicSoninSigmaL2 p ∈ FieldOnePadicSoninL2 p := by
  change fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)
      (fieldOnePadicSoninSigmaL2 p) = 0 ∧
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)
      (fieldOnePadicL2Fourier p (fieldOnePadicSoninSigmaL2 p)) = 0
  constructor
  · exact fieldOnePadicL2SetProjection_soninSigma_eq_zero p
  · rw [fieldOnePadicL2Fourier_soninSigma]
    exact fieldOnePadicL2SetProjection_soninSigma_eq_zero p

end

end GaloisForLFunctions.RHTower
