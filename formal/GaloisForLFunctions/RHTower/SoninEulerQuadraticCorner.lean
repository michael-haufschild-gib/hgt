import GaloisForLFunctions.RHTower.FiniteEulerCalkinIndependence
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Quadratic Sonin Euler corners

Two dilation corners across the actual even Sonin projection cannot acquire a compact product.
The proof uses two exterior shell sequences which are inverse dilates of one common interior shell;
their crossed images converge to that same interior vector.
-/

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

theorem dilation_comp_apply (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (f : SoninL2) :
    dilation r hr (dilation s hs f) = dilation (r * s) (mul_pos hr hs) f := by
  apply Lp.ext
  have hinner := (dilation_ae s hs f).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [dilation_ae r hr (dilation s hs f), hinner,
    dilation_ae (r * s) (mul_pos hr hs) f] with x hout hin htarget
  rw [hout, htarget]
  have hin' : dilation s hs f (r * x) =
      (Real.sqrt s : ℂ) * f (s * (r * x)) := by
    simpa only [Function.comp_apply] using hin
  rw [hin']
  have hsqrt : Real.sqrt (r * s) = Real.sqrt r * Real.sqrt s :=
    Real.sqrt_mul hr.le s
  rw [hsqrt]
  push_cast
  ring_nf

theorem inverseDilation_evenShellCell_subset_closedEvenShell
    {c d r : ℝ} (hc : 0 < c) (hcd : c < d) (hr : 0 < r) (n : ℕ) :
    (fun x : ℝ => r⁻¹ * x) ⁻¹' evenShellCell c d n ⊆
      closedEvenShell (r * c) (r * d) := by
  intro x hx
  have hinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hlower : c < |r⁻¹ * x| := (lt_shellLeft hcd n).trans hx.1
  have hupper : |r⁻¹ * x| < d := hx.2.trans_lt (shellRight_lt hcd n)
  rw [abs_mul, abs_of_pos hinv] at hlower hupper
  have hxlower : r * c < |x| := by
    calc
      r * c < r * (r⁻¹ * |x|) := mul_lt_mul_of_pos_left hlower hr
      _ = |x| := by field_simp
  have hxupper : |x| < r * d := by
    calc
      |x| = r * (r⁻¹ * |x|) := by field_simp
      _ < r * d := mul_lt_mul_of_pos_left hupper hr
  by_cases hx0 : 0 ≤ x
  · right
    constructor
    · simpa [abs_of_nonneg hx0] using hxlower.le
    · simpa [abs_of_nonneg hx0] using hxupper.le
  · left
    have hxneg : x < 0 := lt_of_not_ge hx0
    constructor
    · have : -x ≤ r * d := by simpa [abs_of_neg hxneg] using hxupper.le
      linarith
    · have : r * c ≤ -x := by simpa [abs_of_neg hxneg] using hxlower.le
      linarith

theorem centralInterval_disjoint_inverseDilation_evenShellCell
    {a c d r : ℝ} (hc : 0 < c) (hcd : c < d) (hr : 0 < r)
    (harc : a < r * c) (n : ℕ) :
    Disjoint (centralInterval a)
      ((fun x : ℝ => r⁻¹ * x) ⁻¹' evenShellCell c d n) := by
  rw [Set.disjoint_left]
  intro x hxa hxs
  have hxa' : |x| ≤ a := by
    rw [centralInterval] at hxa
    exact abs_le.mpr hxa
  have hinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hscaled : c < |r⁻¹ * x| := (lt_shellLeft hcd n).trans hxs.1
  rw [abs_mul, abs_of_pos hinv] at hscaled
  have : r * c < |x| := by
    calc
      r * c < r * (r⁻¹ * |x|) := mul_lt_mul_of_pos_left hscaled hr
      _ = |x| := by field_simp
  linarith

theorem centralSoninProjection_tendsto_of_orthonormal_boundedExterior
    (a c d : ℝ) (ha : 0 < a) (hc : 0 < c)
    (g : ℕ → SoninL2) (hg : Orthonormal ℂ g)
    (hphysical : ∀ n, indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) (g n) = 0)
    (hshell : ∀ n, indicatorCutoff (closedEvenShell c d)
      (measurableSet_closedEvenShell c d) (g n) = g n) :
    Tendsto (fun n => ‖centralSoninProjection a (g n) - g n‖) atTop (𝓝 0) := by
  let A : Submodule ℂ SoninL2 := centralPhysicalForbidden a
  let B : Submodule ℂ SoninL2 := centralFourierForbidden a
  letI : (Aᗮ ⊓ Bᗮ).HasOrthogonalProjection := by
    dsimp [A, B]
    infer_instance
  have hblock : ‖soninAlternatingBlock A B‖ < 1 := by
    simpa [A, B] using norm_centralSoninAlternatingBlock_lt_one a ha
  have hgA : ∀ n, g n ∈ Aᗮ := by
    intro n
    apply (Submodule.starProjection_apply_eq_zero_iff (K := A)).mp
    change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) (g n) = 0
    exact hphysical n
  have hcompact : IsCompactOperator (shellCutoffFourierCutoff c d) :=
    isCompactOperator_shellCutoffFourierCutoff c d hc
  have hnull := RHTower.IsCompactOperator.norm_apply_tendsto_zero_of_orthonormal
    (shellCutoffFourierCutoff c d) hcompact hg
  have hBnull : Tendsto (fun n => ‖B.starProjection (g n)‖) atTop (𝓝 0) := by
    apply hnull.congr'
    exact Filter.Eventually.of_forall fun n => by
      rw [← fourierCutoff_eq_fourierForbidden_starProjection]
      change ‖indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
          (fourierUnitary
            (indicatorCutoff (closedEvenShell c d) (measurableSet_closedEvenShell c d)
              (g n)))‖ =
        ‖fourierUnitary.symm
          (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
            (fourierUnitary (g n)))‖
      rw [fourierUnitary.symm.norm_map, hshell n]
  have h := soninIntersectionProjection_tendsto_shell A B hblock g hgA hBnull
  rw [centralSoninProjection_eq_soninIntersectionProjection]
  simpa [A, B] using h

theorem centralSoninProjection_inverseDilatedShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (harc : a < r * c) :
    Tendsto (fun n =>
      ‖centralSoninProjection a
          (dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
            (evenShellVector c d hc hcd n)) -
        dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (evenShellVector c d hc hcd n)‖) atTop (𝓝 0) := by
  let g : ℕ → SoninL2 := fun n =>
    dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
      (evenShellVector c d hc hcd n)
  have hg : Orthonormal ℂ g := by
    have hbase := evenShellVector_orthonormal c d hc hcd
    have hmap := hbase.comp_linearIsometryEquiv
      (dilationUnitary r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)))
    simpa [g, Function.comp_def] using hmap
  have hphysical : ∀ n, indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) (g n) = 0 := by
    intro n
    apply indicatorCutoff_dilation_normalizedIndicator_eq_zero
    exact centralInterval_disjoint_inverseDilation_evenShellCell hc hcd
      (zero_lt_one.trans hr) harc n
  have hshell : ∀ n, indicatorCutoff (closedEvenShell (r * c) (r * d))
      (measurableSet_closedEvenShell (r * c) (r * d)) (g n) = g n := by
    intro n
    apply indicatorCutoff_dilation_normalizedIndicator_eq_self
    exact inverseDilation_evenShellCell_subset_closedEvenShell hc hcd
      (zero_lt_one.trans hr) n
  exact centralSoninProjection_tendsto_of_orthonormal_boundedExterior
    a (r * c) (r * d) ha (mul_pos (zero_lt_one.trans hr) hc) g hg hphysical hshell

end RHTower
