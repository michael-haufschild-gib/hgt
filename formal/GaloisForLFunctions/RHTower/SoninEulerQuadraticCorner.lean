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
    {c d r : ℝ} (hcd : c < d) (hr : 0 < r) (n : ℕ) :
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
    {a c d r : ℝ} (hcd : c < d) (hr : 0 < r)
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

/-- Fourier observation on a bounded exterior shell, with the Fourier cutoff allowed to differ
from the shell's inner radius. -/
def boundedShellFourierCutoff (a c d : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc ∘L
    fourierUnitary.toLinearIsometry.toContinuousLinearMap ∘L
    indicatorCutoff (closedEvenShell c d) (measurableSet_closedEvenShell c d)

theorem boundedShellFourierCutoff_eq_add (a c d : ℝ) (hc : 0 < c) :
    boundedShellFourierCutoff a c d =
      cutoffFourierCutoff (-a) a (-d) (-c) + cutoffFourierCutoff (-a) a c d := by
  rw [boundedShellFourierCutoff, indicatorCutoff_closedEvenShell_eq_add c d hc]
  ext f
  simp [cutoffFourierCutoff]

theorem boundedShellFourierCutoff_isCompactOperator
    (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IsCompactOperator (boundedShellFourierCutoff a c d) := by
  rw [boundedShellFourierCutoff_eq_add a c d hc]
  exact (isCompactOperator_cutoffFourierCutoff (-a) a (-d) (-c) (by linarith)).add
    (isCompactOperator_cutoffFourierCutoff (-a) a c d (by linarith))

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
    dsimp [A]
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := centralPhysicalForbidden a)).mp
    change (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection (g n) = 0
    rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
    simpa [centralInterval] using hphysical n
  have hcompact : IsCompactOperator (boundedShellFourierCutoff a c d) :=
    boundedShellFourierCutoff_isCompactOperator a c d ha hc
  have hnull := RHTower.IsCompactOperator.norm_apply_tendsto_zero_of_orthonormal
    (boundedShellFourierCutoff a c d) hcompact hg
  have hBnull : Tendsto (fun n => ‖B.starProjection (g n)‖) atTop (𝓝 0) := by
    apply hnull.congr'
    exact Filter.Eventually.of_forall fun n => by
      dsimp [B, centralFourierForbidden]
      rw [← fourierCutoff_eq_fourierForbidden_starProjection]
      change ‖indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
          (fourierUnitary
            (indicatorCutoff (closedEvenShell c d) (measurableSet_closedEvenShell c d)
              (g n)))‖ =
        ‖fourierUnitary.symm
          (indicatorCutoff (Set.Icc (-a) a) measurableSet_Icc
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
            (evenShellVector c d hcd n)) -
        dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (evenShellVector c d hcd n)‖) atTop (𝓝 0) := by
  let g : ℕ → SoninL2 := fun n =>
    dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
      (evenShellVector c d hcd n)
  have hg : Orthonormal ℂ g := by
    have hbase := evenShellVector_orthonormal c d hc hcd
    have hmap := hbase.comp_linearIsometryEquiv
      (dilationUnitary r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)))
    simpa [g, Function.comp_def] using hmap
  have hphysical : ∀ n, indicatorCutoff (centralInterval a)
      (measurableSet_centralInterval a) (g n) = 0 := by
    intro n
    apply indicatorCutoff_dilation_normalizedIndicator_eq_zero
    exact centralInterval_disjoint_inverseDilation_evenShellCell hcd
      (zero_lt_one.trans hr) harc n
  have hshell : ∀ n, indicatorCutoff (closedEvenShell (r * c) (r * d))
      (measurableSet_closedEvenShell (r * c) (r * d)) (g n) = g n := by
    intro n
    apply indicatorCutoff_dilation_normalizedIndicator_eq_self
    exact inverseDilation_evenShellCell_subset_closedEvenShell hcd
      (zero_lt_one.trans hr) n
  exact centralSoninProjection_tendsto_of_orthonormal_boundedExterior
    a (r * c) (r * d) ha (mul_pos (zero_lt_one.trans hr) hc) g hg hphysical hshell

end RHTower

namespace RHTower

 theorem centralPhysicalCutoff_evenShellVector_eq_self
    (a c d : ℝ) (hcd : c < d) (hda : d < a) (n : ℕ) :
    indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (evenShellVector c d hcd n) = evenShellVector c d hcd n := by
  apply Lp.ext
  filter_upwards [
    indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a)
      (evenShellVector c d hcd n),
    normalizedIndicator_ae (evenShellCell c d n)
      (measurableSet_evenShellCell c d n)
      (evenShellCell_measure_ne_top hcd n)
  ] with x hcut hshell
  rw [hcut]
  by_cases hx : x ∈ evenShellCell c d n
  · have hxd : x ∈ Set.Icc (-d) d := evenShellCell_subset_Icc hcd n hx
    have hxa : x ∈ centralInterval a := by
      rw [centralInterval]
      constructor <;> linarith [hxd.1, hxd.2]
    rw [Set.indicator_of_mem hxa]
  · have hvzero : (evenShellVector c d hcd n : ℝ → ℂ) x = 0 := by
      change normalizedIndicator (evenShellCell c d n)
        (measurableSet_evenShellCell c d n) (evenShellCell_measure_ne_top hcd n) x = 0
      rw [hshell, Set.indicator_of_notMem hx]
      simp
    by_cases hxa : x ∈ centralInterval a
    · rw [Set.indicator_of_mem hxa]
    · rw [Set.indicator_of_notMem hxa]
      exact hvzero.symm

 theorem evenShellVector_mem_centralPhysicalForbidden
    (a c d : ℝ) (hcd : c < d) (hda : d < a) (n : ℕ) :
    evenShellVector c d hcd n ∈ centralPhysicalForbidden a := by
  rw [centralPhysicalForbidden]
  apply (physicalForbidden (Set.Icc (-a) a) measurableSet_Icc).starProjection_eq_self_iff.mp
  rw [← indicatorCutoff_eq_physicalForbidden_starProjection]
  simpa [centralInterval] using
    centralPhysicalCutoff_evenShellVector_eq_self a c d hcd hda n

theorem centralSoninProjection_eq_zero_of_mem_physicalForbidden
    (a : ℝ) {f : SoninL2} (hf : f ∈ centralPhysicalForbidden a) :
    centralSoninProjection a f = 0 := by
  rw [centralSoninProjection_eq_soninIntersectionProjection]
  apply ((centralPhysicalForbidden a)ᗮ ⊓
    (centralFourierForbidden a)ᗮ).starProjection_apply_eq_zero_iff.mpr
  rw [Submodule.mem_orthogonal']
  intro w hw
  exact Submodule.inner_right_of_mem_orthogonal hf hw.1

end RHTower

namespace RHTower

/-- Exterior shell vectors obtained by inverse dilation of one fixed interior shell. -/
def inverseDilatedEvenShell
    (c d r : ℝ) (hcd : c < d) (hr : 1 < r) (n : ℕ) : SoninL2 :=
  dilation r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)) (evenShellVector c d hcd n)

 theorem inverseDilatedEvenShell_orthonormal
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) :
    Orthonormal ℂ (inverseDilatedEvenShell c d r hcd hr) := by
  have hbase := evenShellVector_orthonormal c d hc hcd
  have hmap := hbase.comp_linearIsometryEquiv
    (dilationUnitary r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)))
  simpa [inverseDilatedEvenShell, Function.comp_def] using hmap

 theorem centralSoninProjection_inverseDilatedEvenShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (harc : a < r * c) :
    Tendsto (fun n =>
      ‖centralSoninProjection a (inverseDilatedEvenShell c d r hcd hr n) -
        inverseDilatedEvenShell c d r hcd hr n‖) atTop (𝓝 0) := by
  simpa [inverseDilatedEvenShell] using
    centralSoninProjection_inverseDilatedShell_tendsto a c d r ha hc hcd hr harc

 theorem centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (hr : 1 < r) (harc : a < r * c) :
    Tendsto (fun n =>
      ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) :
          SoninL2 →L[ℂ] SoninL2)
          (centralSoninProjection a (inverseDilatedEvenShell c d r hcd hr n)) -
        evenShellVector c d hcd n‖) atTop (𝓝 0) := by
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  let D : SoninL2 →L[ℂ] SoninL2 := dilationSum r hr
  let B : SoninL2 →L[ℂ] SoninL2 := 1 - Q
  let v : ℕ → SoninL2 := evenShellVector c d hcd
  let g : ℕ → SoninL2 := inverseDilatedEvenShell c d r hcd hr
  let e : ℕ → SoninL2 := fun n => Q (g n)
  let w : ℕ → SoninL2 := fun n =>
    dilation (r * r)⁻¹ (inv_pos.mpr (mul_pos (zero_lt_one.trans hr) (zero_lt_one.trans hr)))
      (v n)
  have hgeNorm : Tendsto (fun n => ‖e n - g n‖) atTop (𝓝 0) := by
    simpa [e, g, Q] using
      centralSoninProjection_inverseDilatedEvenShell_tendsto a c d r ha hc hcd hr harc
  have hge : Tendsto (fun n => e n - g n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hgeNorm
  have hrr : 1 < r * r := by nlinarith [hr]
  have harrc : a < (r * r) * c := by
    have hr0 : 0 < r := zero_lt_one.trans hr
    have hc0 : 0 < c := hc
    nlinarith [harc]
  have hqwNorm : Tendsto (fun n => ‖Q (w n) - w n‖) atTop (𝓝 0) := by
    simpa [Q, w, v, inverseDilatedEvenShell] using
      centralSoninProjection_inverseDilatedShell_tendsto
        a c d (r * r) ha hc hcd hrr harrc
  have hw : Tendsto (fun n => w n - Q (w n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert hqwNorm using 1
    funext n
    rw [← norm_neg]
    congr 2
    module
  have hfirst : Tendsto (fun n => B (D (e n - g n))) atTop (𝓝 0) := by
    simpa only [map_zero] using
      (B ∘L D).continuous.continuousAt.tendsto.comp hge
  have hsum : Tendsto (fun n => B (D (e n - g n)) + (w n - Q (w n)))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hfirst.add hw
  have hQe : ∀ n, Q (e n) = e n := by
    intro n
    dsimp [e, Q]
    rw [centralSoninProjection_eq_soninIntersectionProjection]
    apply ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_eq_self_iff.mpr
    exact ((centralPhysicalForbidden a)ᗮ ⊓
      (centralFourierForbidden a)ᗮ).starProjection_apply_mem _
  have hQv : ∀ n, Q (v n) = 0 := by
    intro n
    exact centralSoninProjection_eq_zero_of_mem_physicalForbidden a
      (evenShellVector_mem_centralPhysicalForbidden a c d hcd hda n)
  have hDg : ∀ n, D (g n) = v n + w n := by
    intro n
    dsimp [D, g, v, w, inverseDilatedEvenShell]
    rw [dilationSum_apply, dilation_dilation_inv]
    rw [dilation_comp_apply]
    congr 2
    field_simp
  have hvec : Tendsto (fun n =>
      (crossBoundary Q D : SoninL2 →L[ℂ] SoninL2) (e n) - v n)
      atTop (𝓝 0) := by
    convert hsum using 1
    funext n
    simp only [crossBoundary, mul_apply_eq_comp,
      one_apply_eq_self, _root_.sub_apply]
    rw [hQe n]
    have hDe : D (e n) = D (e n - g n) + D (g n) := by
      rw [map_sub, sub_add_cancel]
    rw [hDe, hDg n, map_add, map_add, hQv n]
    dsimp [B]
    module
  exact tendsto_zero_iff_norm_tendsto_zero.mp hvec

end RHTower

namespace RHTower

 theorem norm_inner_tendsto_one_of_paired_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x y v : ℕ → H} (hv : ∀ n, ‖v n‖ = 1)
    (hx : Tendsto (fun n => ‖x n - v n‖) atTop (𝓝 0))
    (hy : Tendsto (fun n => ‖y n - v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => ‖inner ℂ (x n) (y n)‖) atTop (𝓝 1) := by
  let ex : ℕ → ℝ := fun n => ‖x n - v n‖
  let ey : ℕ → ℝ := fun n => ‖y n - v n‖
  have hyNorm : ∀ n, ‖y n‖ ≤ ey n + 1 := by
    intro n
    calc
      ‖y n‖ = ‖(y n - v n) + v n‖ := by rw [sub_add_cancel]
      _ ≤ ‖y n - v n‖ + ‖v n‖ := norm_add_le _ _
      _ = ey n + 1 := by rw [hv n]
  have herr : ∀ n,
      ‖inner ℂ (x n) (y n) - inner ℂ (v n) (v n)‖ ≤
        ex n * (ey n + 1) + ey n := by
    intro n
    have hid : inner ℂ (x n) (y n) - inner ℂ (v n) (v n) =
        inner ℂ (x n - v n) (y n) + inner ℂ (v n) (y n - v n) := by
      rw [inner_sub_left, inner_sub_right]
      module
    rw [hid]
    calc
      ‖inner ℂ (x n - v n) (y n) + inner ℂ (v n) (y n - v n)‖
          ≤ ‖inner ℂ (x n - v n) (y n)‖ +
              ‖inner ℂ (v n) (y n - v n)‖ := norm_add_le _ _
      _ ≤ ‖x n - v n‖ * ‖y n‖ + ‖v n‖ * ‖y n - v n‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ex n * (ey n + 1) + ey n := by
        rw [hv n, one_mul]
        dsimp [ex, ey]
        nlinarith [hyNorm n, norm_nonneg (x n - v n)]
  have hupper : Tendsto (fun n => ex n * (ey n + 1) + ey n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hey1 : Tendsto (fun n => ‖y n - v n‖ + 1) atTop (𝓝 (0 + 1)) := hy.add h1
    have hprod : Tendsto (fun n => ‖x n - v n‖ * (‖y n - v n‖ + 1))
        atTop (𝓝 (0 * (0 + 1))) := hx.mul hey1
    have h := hprod.add hy
    simpa [ex, ey] using h
  have herr0 : Tendsto (fun n =>
      ‖inner ℂ (x n) (y n) - inner ℂ (v n) (v n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) herr hupper
  have hinner0 : Tendsto (fun n => inner ℂ (x n) (y n) - 1) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    convert herr0 using 1
    funext n
    rw [inner_self_eq_norm_sq_to_K, hv n]
    norm_num
  have hinner : Tendsto (fun n => inner ℂ (x n) (y n)) atTop (𝓝 1) := by
    have h := hinner0.add_const 1
    simpa only [sub_add_cancel, zero_add] using h
  simpa using hinner.norm

theorem adjointComp_not_isCompactOperator_of_paired_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Lp Lq : H →L[ℂ] H) (f k v : ℕ → H)
    (hf_bound : ∀ n, ‖f n‖ ≤ 1) (hk_bound : ∀ n, ‖k n‖ ≤ 1)
    (hf_weak : ∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0))
    (hv : ∀ n, ‖v n‖ = 1)
    (hq : Tendsto (fun n => ‖Lq (f n) - v n‖) atTop (𝓝 0))
    (hp : Tendsto (fun n => ‖Lp (k n) - v n‖) atTop (𝓝 0)) :
    ¬ IsCompactOperator (Lp† ∘L Lq) := by
  have hinner := norm_inner_tendsto_one_of_paired_approx hv hq hp
  have hinnerLower : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ ‖inner ℂ (Lq (f n)) (Lp (k n))‖ := by
    have hlt : ∀ᶠ n in atTop,
        (1 / 2 : ℝ) < ‖inner ℂ (Lq (f n)) (Lp (k n))‖ :=
      (tendsto_order.1 hinner).1 (1 / 2) (by norm_num)
    exact hlt.mono fun _ hn => hn.le
  have hTLower : ∀ᶠ n in atTop, (1 / 2 : ℝ) ≤ ‖(Lp† ∘L Lq) (f n)‖ :=
    hinnerLower.mono fun n hn => by
      have hadj : inner ℂ ((Lp† ∘L Lq) (f n)) (k n) =
          inner ℂ (Lq (f n)) (Lp (k n)) := by
        simpa using Lp.adjoint_inner_left (k n) (Lq (f n))
      calc
        (1 / 2 : ℝ) ≤ ‖inner ℂ (Lq (f n)) (Lp (k n))‖ := hn
        _ = ‖inner ℂ ((Lp† ∘L Lq) (f n)) (k n)‖ := by rw [hadj]
        _ ≤ ‖(Lp† ∘L Lq) (f n)‖ * ‖k n‖ := norm_inner_le_norm _ _
        _ ≤ ‖(Lp† ∘L Lq) (f n)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hk_bound n) (norm_nonneg _)
        _ = ‖(Lp† ∘L Lq) (f n)‖ := mul_one _
  exact not_isCompactOperator_of_weakly_tendsto_zero_of_eventually_image_norm_ge
    (Lp† ∘L Lq) f 1 (1 / 2) hf_bound hf_weak (by norm_num) hTLower

/-- A compact operator sends a bounded weakly-null sequence to a norm-null sequence. -/
theorem IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (K : E →L[ℂ] F) (hK : IsCompactOperator K) (f : ℕ → E) (R : ℝ)
    (hf_bound : ∀ n, ‖f n‖ ≤ R)
    (hf_weak : ∀ ℓ : E →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖K (f n)‖) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    exact Eventually.of_forall fun n => hb.trans_le (norm_nonneg (K (f n)))
  · intro b hb
    by_contra hsmall
    have hfreq : ∃ᶠ n in atTop, b ≤ ‖K (f n)‖ :=
      (not_eventually.mp hsmall).mono fun _ hn => le_of_not_gt hn
    obtain ⟨φ, hφ, hφlower⟩ := extraction_of_frequently_atTop hfreq
    have hnot := not_isCompactOperator_of_weakly_tendsto_zero_of_image_norm_ge
      K (f ∘ φ) R b (fun n => by simpa [Function.comp_apply] using hf_bound (φ n))
      (fun ℓ => by
        simpa [Function.comp_apply] using (hf_weak ℓ).comp hφ.tendsto_atTop)
      hb hφlower
    exact hnot hK

/-- A normalized strong image limit gives the sharp lower distance from every compact
perturbation. -/
theorem one_le_norm_sub_compact_of_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (f v : ℕ → H)
    (hf_bound : ∀ n, ‖f n‖ ≤ 1)
    (hf_weak : ∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0))
    (hv : ∀ n, ‖v n‖ = 1)
    (hT : Tendsto (fun n => ‖T (f n) - v n‖) atTop (𝓝 0))
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    1 ≤ ‖T - K‖ := by
  have hTnorm : Tendsto (fun n => ‖T (f n)‖) atTop (𝓝 1) :=
    tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq hT hv
  have hKzero : Tendsto (fun n => ‖K (f n)‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK f 1 hf_bound hf_weak
  have hupper : Tendsto (fun n => ‖T - K‖ + ‖K (f n)‖) atTop (𝓝 (‖T - K‖ + 0)) :=
    tendsto_const_nhds.add hKzero
  have hle : ∀ n, ‖T (f n)‖ ≤ ‖T - K‖ + ‖K (f n)‖ := by
    intro n
    have hdecomp : T (f n) = (T - K) (f n) + K (f n) := by simp
    calc
      ‖T (f n)‖ = ‖(T - K) (f n) + K (f n)‖ := by rw [hdecomp]
      _ ≤ ‖(T - K) (f n)‖ + ‖K (f n)‖ := norm_add_le _ _
      _ ≤ (‖T - K‖ * ‖f n‖) + ‖K (f n)‖ := by
        linarith [(T - K).le_opNorm (f n)]
      _ ≤ ‖T - K‖ + ‖K (f n)‖ := by
        have hm : ‖T - K‖ * ‖f n‖ ≤ ‖T - K‖ * 1 :=
          mul_le_mul_of_nonneg_left (hf_bound n) (norm_nonneg _)
        simpa using add_le_add_right hm ‖K (f n)‖
  have := le_of_tendsto_of_tendsto hTnorm hupper (Eventually.of_forall hle)
  simpa using this

/-- A nonzero scalar transports a sharp unit lower distance from compact operators to the
corresponding scalar multiple. -/
theorem norm_smul_le_norm_smul_sub_compact_of_one_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : ℂ) (hb : b ≠ 0) (T K : H →L[ℂ] H)
    (hdist : ∀ C : H →L[ℂ] H, IsCompactOperator C → 1 ≤ ‖T - C‖)
    (hK : IsCompactOperator K) :
    ‖b‖ ≤ ‖b • T - K‖ := by
  let C : H →L[ℂ] H := b⁻¹ • K
  have hC : IsCompactOperator C := by
    dsimp [C]
    exact hK.smul b⁻¹
  have hbase : 1 ≤ ‖T - C‖ := hdist C hC
  have hscale : ‖b‖ * 1 ≤ ‖b‖ * ‖T - C‖ :=
    mul_le_mul_of_nonneg_left hbase (norm_nonneg b)
  have heq : b • (T - C) = b • T - K := by
    dsimp [C]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hb, one_smul]
  calc
    ‖b‖ = ‖b‖ * 1 := by ring
    _ ≤ ‖b‖ * ‖T - C‖ := hscale
    _ = ‖b • (T - C)‖ := (norm_smul b (T - C)).symm
    _ = ‖b • T - K‖ := by rw [heq]

/-- The paired-shell certificate is sharp at the level of distance from compact operators: every
compact perturbation of the ordered Gram entry still has operator norm at least one. -/
theorem one_le_norm_adjointComp_sub_compact_of_paired_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Lp Lq : H →L[ℂ] H) (f k v : ℕ → H)
    (hf_bound : ∀ n, ‖f n‖ ≤ 1) (hk_bound : ∀ n, ‖k n‖ ≤ 1)
    (hf_weak : ∀ ℓ : H →L[ℂ] ℂ, Tendsto (fun n => ℓ (f n)) atTop (𝓝 0))
    (hv : ∀ n, ‖v n‖ = 1)
    (hq : Tendsto (fun n => ‖Lq (f n) - v n‖) atTop (𝓝 0))
    (hp : Tendsto (fun n => ‖Lp (k n) - v n‖) atTop (𝓝 0))
    (K : H →L[ℂ] H) (hK : IsCompactOperator K) :
    1 ≤ ‖Lp† ∘L Lq - K‖ := by
  let T : H →L[ℂ] H := Lp† ∘L Lq
  have hinner : Tendsto (fun n => ‖inner ℂ (Lq (f n)) (Lp (k n))‖)
      atTop (𝓝 1) := norm_inner_tendsto_one_of_paired_approx hv hq hp
  have hKzero : Tendsto (fun n => ‖K (f n)‖) atTop (𝓝 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK f 1 hf_bound hf_weak
  have hupper : Tendsto (fun n => ‖T - K‖ + ‖K (f n)‖) atTop (𝓝 (‖T - K‖ + 0)) :=
    tendsto_const_nhds.add hKzero
  have hle : ∀ n,
      ‖inner ℂ (Lq (f n)) (Lp (k n))‖ ≤ ‖T - K‖ + ‖K (f n)‖ := by
    intro n
    have hadj : inner ℂ (T (f n)) (k n) =
        inner ℂ (Lq (f n)) (Lp (k n)) := by
      dsimp [T]
      simpa using Lp.adjoint_inner_left (k n) (Lq (f n))
    have hdecomp : T (f n) = (T - K) (f n) + K (f n) := by
      simp
    calc
      ‖inner ℂ (Lq (f n)) (Lp (k n))‖ = ‖inner ℂ (T (f n)) (k n)‖ := by
        rw [hadj]
      _ = ‖inner ℂ ((T - K) (f n) + K (f n)) (k n)‖ := by rw [hdecomp]
      _ ≤ ‖inner ℂ ((T - K) (f n)) (k n)‖ +
          ‖inner ℂ (K (f n)) (k n)‖ := by
        rw [inner_add_left]
        exact norm_add_le _ _
      _ ≤ ‖(T - K) (f n)‖ * ‖k n‖ + ‖K (f n)‖ * ‖k n‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖T - K‖ + ‖K (f n)‖ := by
        have hTf := (T - K).le_opNorm (f n)
        have hfn := hf_bound n
        have hkn := hk_bound n
        have hTK : 0 ≤ ‖T - K‖ := norm_nonneg _
        have hKfn : 0 ≤ ‖K (f n)‖ := norm_nonneg _
        have hfn0 : 0 ≤ ‖f n‖ := norm_nonneg _
        have hkn0 : 0 ≤ ‖k n‖ := norm_nonneg _
        have hfirst : ‖(T - K) (f n)‖ * ‖k n‖ ≤ ‖T - K‖ := by
          calc
            ‖(T - K) (f n)‖ * ‖k n‖
                ≤ (‖T - K‖ * ‖f n‖) * ‖k n‖ :=
              mul_le_mul_of_nonneg_right hTf hkn0
            _ ≤ (‖T - K‖ * 1) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hfn hTK) hkn
                hkn0 (mul_nonneg hTK zero_le_one)
            _ = ‖T - K‖ := by ring
        have hsecond : ‖K (f n)‖ * ‖k n‖ ≤ ‖K (f n)‖ := by
          calc
            ‖K (f n)‖ * ‖k n‖ ≤ ‖K (f n)‖ * 1 :=
              mul_le_mul_of_nonneg_left hkn hKfn
            _ = ‖K (f n)‖ := mul_one _
        exact add_le_add hfirst hsecond
  have := le_of_tendsto_of_tendsto hinner hupper (Eventually.of_forall hle)
  simpa [T] using this

end RHTower

namespace RHTower

/-- The inverse-dilated shell sequence inside the even Hilbert carrier. -/
def inverseDilatedEvenShellEven
    (c d r : ℝ) (hcd : c < d) (hr : 1 < r) (n : ℕ) : evenSubspace :=
  (evenDilationUnitary r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)))
    (evenShellVectorEven c d hcd n)

@[simp] theorem coe_inverseDilatedEvenShellEven
    (c d r : ℝ) (hcd : c < d) (hr : 1 < r) (n : ℕ) :
    ((inverseDilatedEvenShellEven c d r hcd hr n : evenSubspace) : SoninL2) =
      inverseDilatedEvenShell c d r hcd hr n := rfl

 theorem inverseDilatedEvenShellEven_orthonormal
    (c d r : ℝ) (hc : 0 < c) (hcd : c < d) (hr : 1 < r) :
    Orthonormal ℂ (inverseDilatedEvenShellEven c d r hcd hr) := by
  have hbase := evenShellVectorEven_orthonormal c d hc hcd
  have hmap := hbase.comp_linearIsometryEquiv
    (evenDilationUnitary r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr)))
  simpa [inverseDilatedEvenShellEven, Function.comp_def] using hmap

 theorem evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hr : 1 < r)
    (harc : a < r * c) :
    Tendsto (fun n =>
      ‖evenCentralSoninProjection a (inverseDilatedEvenShellEven c d r hcd hr n) -
        inverseDilatedEvenShellEven c d r hcd hr n‖) atTop (𝓝 0) := by
  change Tendsto (fun n =>
    ‖centralSoninProjection a (inverseDilatedEvenShell c d r hcd hr n) -
      inverseDilatedEvenShell c d r hcd hr n‖) atTop (𝓝 0)
  exact centralSoninProjection_inverseDilatedEvenShell_tendsto
    a c d r ha hc hcd hr harc

 theorem evenCentralSoninDilationCorner_pairedShell_tendsto
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (hr : 1 < r) (harc : a < r * c) :
    Tendsto (fun n =>
      ‖evenCentralSoninDilationCorner a r hr
          (evenCentralSoninProjection a
            (inverseDilatedEvenShellEven c d r hcd hr n)) -
        evenShellVectorEven c d hcd n‖) atTop (𝓝 0) := by
  change Tendsto (fun n =>
    ‖(crossBoundary (centralSoninProjection a) (dilationSum r hr) :
        SoninL2 →L[ℂ] SoninL2)
        (centralSoninProjection a (inverseDilatedEvenShell c d r hcd hr n)) -
      evenShellVector c d hcd n‖) atTop (𝓝 0)
  exact centralSoninDilationCorner_inverseDilatedEvenShell_tendsto
    a c d r ha hc hcd hda hr harc

/-- The ordered two-scale Calkin Gram entry of the actual even Sonin dilation corners. -/
def evenCentralSoninQuadraticCorner
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) : evenSubspace →L[ℂ] evenSubspace :=
  (evenCentralSoninDilationCorner a p hp)† ∘L evenCentralSoninDilationCorner a q hq

/-- The ordered two-scale Gram entry of the positive Euler corners. -/
def evenCentralPositiveEulerQuadraticCorner
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) : evenSubspace →L[ℂ] evenSubspace :=
  (evenCentralPositiveEulerCorner a p hp)† ∘L evenCentralPositiveEulerCorner a q hq

/-- The positive Euler Gram entry is the explicit nonzero Euler scalar times the dilation
Gram entry. -/
theorem evenCentralPositiveEulerQuadraticCorner_eq_smul
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenCentralPositiveEulerQuadraticCorner a p q hp hq =
      (star (-((Real.sqrt p : ℂ)⁻¹)) * (-((Real.sqrt q : ℂ)⁻¹))) •
        evenCentralSoninQuadraticCorner a p q hp hq := by
  let bp : ℂ := -((Real.sqrt p : ℂ)⁻¹)
  let bq : ℂ := -((Real.sqrt q : ℂ)⁻¹)
  have hadj : (bp • evenCentralSoninDilationCorner a p hp)† =
      star bp • (evenCentralSoninDilationCorner a p hp)† := by
    change star (bp • evenCentralSoninDilationCorner a p hp) =
      star bp • star (evenCentralSoninDilationCorner a p hp)
    rw [star_smul]
  rw [evenCentralPositiveEulerQuadraticCorner, evenCentralPositiveEulerCorner_eq_smul,
    evenCentralPositiveEulerCorner_eq_smul]
  change (bp • evenCentralSoninDilationCorner a p hp)† ∘L
      (bq • evenCentralSoninDilationCorner a q hq) = _
  rw [hadj]
  apply ContinuousLinearMap.ext
  intro x
  change star bp • (((evenCentralSoninDilationCorner a p hp)†)
      (bq • evenCentralSoninDilationCorner a q hq x)) =
    (star bp * bq) • (((evenCentralSoninDilationCorner a p hp)†)
      (evenCentralSoninDilationCorner a q hq x))
  rw [map_smul, smul_smul]

/-- The literal ordered two-scale Euler Gram entry on the concrete archimedean
Hardy--Titchmarsh line. -/
def archimedeanPrimeEulerQuadraticCorner
    (a p q : ℝ) : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  (archimedeanPrimeEulerCorner a p)† ∘L archimedeanPrimeEulerCorner a q

/-- The concrete Hardy--Titchmarsh quadratic entry is the unitary push of the actual even Sonin
positive Euler quadratic entry. -/
theorem archimedeanPrimeEulerQuadraticCorner_eq_unitaryPush
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    archimedeanPrimeEulerQuadraticCorner a p q =
      unitaryPush archimedeanDualHardyTitchmarshUnitary
        (evenCentralPositiveEulerQuadraticCorner a p q hp hq) := by
  rw [archimedeanPrimeEulerQuadraticCorner,
    archimedeanPrimeEulerCorner_eq_sourceCorner (hp := hp),
    archimedeanPrimeEulerCorner_eq_sourceCorner (hp := hq),
    hardyTitchmarshEulerCorner_eq_unitaryPush,
    hardyTitchmarshEulerCorner_eq_unitaryPush,
    adjoint_unitaryPush]
  change unitaryPush archimedeanDualHardyTitchmarshUnitary
      ((evenCentralPositiveEulerCorner a p hp)†) *
        unitaryPush archimedeanDualHardyTitchmarshUnitary
          (evenCentralPositiveEulerCorner a q hq) =
    unitaryPush archimedeanDualHardyTitchmarshUnitary
      ((evenCentralPositiveEulerCorner a p hp)† *
        evenCentralPositiveEulerCorner a q hq)
  rw [← unitaryPush_mul]

/-- One interior shell gives the sharp lower distance from compact operators for a single even
Sonin dilation corner. -/
theorem one_le_norm_evenCentralSoninDilationCorner_sub_compact_of_shell
    (a c d p : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (hp : 1 < p) (hapc : a < p * c)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    1 ≤ ‖evenCentralSoninDilationCorner a p hp - K‖ := by
  let Q : evenSubspace →L[ℂ] evenSubspace := evenCentralSoninProjection a
  let g : ℕ → evenSubspace := inverseDilatedEvenShellEven c d p hcd hp
  let f : ℕ → evenSubspace := fun n => Q (g n)
  let v : ℕ → evenSubspace := evenShellVectorEven c d hcd
  have hg : Orthonormal ℂ g := by
    simpa [g] using inverseDilatedEvenShellEven_orthonormal c d p hc hcd hp
  have hf_approx : Tendsto (fun n => ‖f n - g n‖) atTop (𝓝 0) := by
    simpa [f, g, Q] using
      evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d p ha hc hcd hp hapc
  have hf_weak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun n => ℓ (f n)) atTop (𝓝 0) :=
    weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hg) hf_approx
  have hf_bound : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    calc
      ‖f n‖ ≤ ‖g n‖ := by
        change ‖evenCentralSoninProjection a (g n)‖ ≤ ‖g n‖
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le (g n)
      _ = 1 := hg.norm_eq_one n
  have hv : ∀ n, ‖v n‖ = 1 := by
    intro n
    exact (evenShellVectorEven_orthonormal c d hc hcd).norm_eq_one n
  have hcross : Tendsto (fun n =>
      ‖evenCentralSoninDilationCorner a p hp (f n) - v n‖) atTop (𝓝 0) := by
    simpa [f, g, v, Q] using
      evenCentralSoninDilationCorner_pairedShell_tendsto
        a c d p ha hc hcd hda hp hapc
  exact one_le_norm_sub_compact_of_approx
    (evenCentralSoninDilationCorner a p hp) f v hf_bound hf_weak hv hcross K hK

/-- Every compact perturbation of a one-scale even Sonin dilation corner has norm at least one. -/
theorem one_le_norm_evenCentralSoninDilationCorner_sub_compact
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ∀ K : evenSubspace →L[ℂ] evenSubspace, IsCompactOperator K →
      1 ≤ ‖evenCentralSoninDilationCorner a p hp - K‖ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hap : a / p < a := by
    rw [div_lt_iff₀ hp0]
    nlinarith
  let c : ℝ := (a / p + a) / 2
  let d : ℝ := (c + a) / 2
  have hc_lower : a / p < c := by
    dsimp [c]
    linarith
  have hc : 0 < c := lt_trans (div_pos ha hp0) hc_lower
  have hca : c < a := by
    dsimp [c]
    linarith
  have hcd : c < d := by
    dsimp [d]
    linarith
  have hda : d < a := by
    dsimp [d]
    linarith
  have hapc : a < p * c := by
    simpa [mul_comm] using (div_lt_iff₀ hp0).mp hc_lower
  intro K hK
  exact one_le_norm_evenCentralSoninDilationCorner_sub_compact_of_shell
    a c d p ha hc hcd hda hp hapc K hK

/-- The positive Euler coefficient is a lower bound for the distance of its one-scale corner from
every compact operator. -/
theorem norm_eulerCoefficient_le_norm_evenCentralPositiveEulerCorner_sub_compact
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    ‖-((Real.sqrt p : ℂ)⁻¹)‖ ≤ ‖evenCentralPositiveEulerCorner a p hp - K‖ := by
  rw [evenCentralPositiveEulerCorner_eq_smul]
  apply norm_smul_le_norm_smul_sub_compact_of_one_le
  · simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hp)]
  · exact one_le_norm_evenCentralSoninDilationCorner_sub_compact a p ha hp
  · exact hK

/-- A common interior shell gives the sharp lower distance from every compact operator for any
two scales which both move that shell across the physical Sonin boundary. -/
theorem one_le_norm_evenCentralSoninQuadraticCorner_sub_compact_of_shell
    (a c d p q : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (hp : 1 < p) (hq : 1 < q) (hapc : a < p * c) (haqc : a < q * c)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    1 ≤ ‖evenCentralSoninQuadraticCorner a p q hp hq - K‖ := by
  let Q : evenSubspace →L[ℂ] evenSubspace := evenCentralSoninProjection a
  let gp : ℕ → evenSubspace := inverseDilatedEvenShellEven c d p hcd hp
  let gq : ℕ → evenSubspace := inverseDilatedEvenShellEven c d q hcd hq
  let fp : ℕ → evenSubspace := fun n => Q (gp n)
  let fq : ℕ → evenSubspace := fun n => Q (gq n)
  let v : ℕ → evenSubspace := evenShellVectorEven c d hcd
  have hgp : Orthonormal ℂ gp := by
    simpa [gp] using inverseDilatedEvenShellEven_orthonormal c d p hc hcd hp
  have hgq : Orthonormal ℂ gq := by
    simpa [gq] using inverseDilatedEvenShellEven_orthonormal c d q hc hcd hq
  have hfp_approx : Tendsto (fun n => ‖fp n - gp n‖) atTop (𝓝 0) := by
    simpa [fp, gp, Q] using
      evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d p ha hc hcd hp hapc
  have hfq_approx : Tendsto (fun n => ‖fq n - gq n‖) atTop (𝓝 0) := by
    simpa [fq, gq, Q] using
      evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
        a c d q ha hc hcd hq haqc
  have hfq_weak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun n => ℓ (fq n)) atTop (𝓝 0) :=
    weakly_tendsto_zero_of_norm_sub_tendsto_zero
      (Orthonormal.weakly_tendsto_zero hgq) hfq_approx
  have hfp_bound : ∀ n, ‖fp n‖ ≤ 1 := by
    intro n
    calc
      ‖fp n‖ ≤ ‖gp n‖ := by
        change ‖evenCentralSoninProjection a (gp n)‖ ≤ ‖gp n‖
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le (gp n)
      _ = 1 := hgp.norm_eq_one n
  have hfq_bound : ∀ n, ‖fq n‖ ≤ 1 := by
    intro n
    calc
      ‖fq n‖ ≤ ‖gq n‖ := by
        change ‖evenCentralSoninProjection a (gq n)‖ ≤ ‖gq n‖
        rw [evenCentralSoninProjection_eq_starProjection]
        exact (evenCentralSoninCarrier a).norm_starProjection_apply_le (gq n)
      _ = 1 := hgq.norm_eq_one n
  have hv : ∀ n, ‖v n‖ = 1 := by
    intro n
    exact (evenShellVectorEven_orthonormal c d hc hcd).norm_eq_one n
  have hp_cross : Tendsto (fun n =>
      ‖evenCentralSoninDilationCorner a p hp (fp n) - v n‖) atTop (𝓝 0) := by
    simpa [fp, gp, v, Q] using
      evenCentralSoninDilationCorner_pairedShell_tendsto
        a c d p ha hc hcd hda hp hapc
  have hq_cross : Tendsto (fun n =>
      ‖evenCentralSoninDilationCorner a q hq (fq n) - v n‖) atTop (𝓝 0) := by
    simpa [fq, gq, v, Q] using
      evenCentralSoninDilationCorner_pairedShell_tendsto
        a c d q ha hc hcd hda hq haqc
  simpa [evenCentralSoninQuadraticCorner] using
    one_le_norm_adjointComp_sub_compact_of_paired_approx
      (evenCentralSoninDilationCorner a p hp)
      (evenCentralSoninDilationCorner a q hq) fq fp v
      hfq_bound hfp_bound hfq_weak hv hq_cross hp_cross K hK

/-- A common interior shell gives a noncompact ordered Gram entry for any two scales which
both move that shell across the physical Sonin boundary. -/
theorem evenCentralSoninQuadraticCorner_not_isCompactOperator_of_shell
    (a c d p q : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (hp : 1 < p) (hq : 1 < q) (hapc : a < p * c) (haqc : a < q * c) :
    ¬ IsCompactOperator (evenCentralSoninQuadraticCorner a p q hp hq) := by
  intro hcompact
  let T := evenCentralSoninQuadraticCorner a p q hp hq
  have hdist := one_le_norm_evenCentralSoninQuadraticCorner_sub_compact_of_shell
    a c d p q ha hc hcd hda hp hq hapc haqc T hcompact
  have hzero : ‖T - T‖ ≤ 0 := (T - T).opNorm_le_bound (by norm_num) (fun x => by simp)
  have : (1 : ℝ) ≤ 0 := hdist.trans hzero
  norm_num at this

/-- Every compact perturbation of an ordered two-scale Sonin Gram entry has norm at least one.
Equivalently, its essential norm is at least one, uniformly in both real scales. -/
theorem one_le_norm_evenCentralSoninQuadraticCorner_sub_compact
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    ∀ K : evenSubspace →L[ℂ] evenSubspace, IsCompactOperator K →
      1 ≤ ‖evenCentralSoninQuadraticCorner a p q hp hq - K‖ := by
  let m : ℝ := min p q
  have hm : 1 < m := by
    dsimp [m]
    exact lt_min hp hq
  have hm0 : 0 < m := zero_lt_one.trans hm
  have ham : a / m < a := by
    rw [div_lt_iff₀ hm0]
    nlinarith
  let c : ℝ := (a / m + a) / 2
  let d : ℝ := (c + a) / 2
  have hc_lower : a / m < c := by
    dsimp [c]
    linarith
  have hc : 0 < c := lt_trans (div_pos ha hm0) hc_lower
  have hca : c < a := by
    dsimp [c]
    linarith
  have hcd : c < d := by
    dsimp [d]
    linarith
  have hda : d < a := by
    dsimp [d]
    linarith
  have hamc : a < m * c := by
    simpa [mul_comm] using (div_lt_iff₀ hm0).mp hc_lower
  have hapc : a < p * c := by
    exact hamc.trans_le (mul_le_mul_of_nonneg_right (min_le_left p q) hc.le)
  have haqc : a < q * c := by
    exact hamc.trans_le (mul_le_mul_of_nonneg_right (min_le_right p q) hc.le)
  intro K hK
  exact one_le_norm_evenCentralSoninQuadraticCorner_sub_compact_of_shell
    a c d p q ha hc hcd hda hp hq hapc haqc K hK

/-- The product of the two Euler coefficients is a lower bound for the distance of the ordered
positive Euler Gram entry from every compact operator. -/
theorem norm_eulerCoefficientProduct_le_norm_evenCentralPositiveEulerQuadraticCorner_sub_compact
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    ‖star (-((Real.sqrt p : ℂ)⁻¹)) * (-((Real.sqrt q : ℂ)⁻¹))‖ ≤
      ‖evenCentralPositiveEulerQuadraticCorner a p q hp hq - K‖ := by
  rw [evenCentralPositiveEulerQuadraticCorner_eq_smul]
  apply norm_smul_le_norm_smul_sub_compact_of_one_le
  · apply mul_ne_zero
    · simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hp)]
    · simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hq)]
  · exact one_le_norm_evenCentralSoninQuadraticCorner_sub_compact a p q ha hp hq
  · exact hK

/-- **Two-scale Sonin Gram theorem.** Every ordered quadratic product of two fixed-cutoff
even Sonin dilation corners is noncompact, with no arithmetic relation required between the
two real scales. -/
theorem evenCentralSoninQuadraticCorner_not_isCompactOperator
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    ¬ IsCompactOperator (evenCentralSoninQuadraticCorner a p q hp hq) := by
  intro hcompact
  let T := evenCentralSoninQuadraticCorner a p q hp hq
  have hdist := one_le_norm_evenCentralSoninQuadraticCorner_sub_compact
    a p q ha hp hq T hcompact
  have hzero : ‖T - T‖ ≤ 0 := (T - T).opNorm_le_bound (by norm_num) (fun x => by simp)
  have : (1 : ℝ) ≤ 0 := hdist.trans hzero
  norm_num at this

/-- Every ordered quadratic product of two positive Euler corners is noncompact on the actual
even Sonin carrier. -/
theorem evenCentralPositiveEulerQuadraticCorner_not_isCompactOperator
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    ¬ IsCompactOperator (evenCentralPositiveEulerQuadraticCorner a p q hp hq) := by
  rw [evenCentralPositiveEulerQuadraticCorner_eq_smul]
  intro hcompact
  let b : ℂ := star (-((Real.sqrt p : ℂ)⁻¹)) * (-((Real.sqrt q : ℂ)⁻¹))
  let T : evenSubspace →L[ℂ] evenSubspace :=
    evenCentralSoninQuadraticCorner a p q hp hq
  have hb : b ≠ 0 := by
    dsimp [b]
    apply mul_ne_zero
    · simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hp)]
    · simp [Real.sqrt_ne_zero'.mpr (zero_lt_one.trans hq)]
  have hcompact' : IsCompactOperator (b • T) := by
    simpa [b, T] using hcompact
  have hunscaled : IsCompactOperator (b⁻¹ • (b • T)) := hcompact'.smul b⁻¹
  have heq : b⁻¹ • (b • T) = T := by
    rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
  apply evenCentralSoninQuadraticCorner_not_isCompactOperator a p q ha hp hq
  change IsCompactOperator T
  rw [← heq]
  exact hunscaled

/-- Every literal two-scale Euler Gram entry on the concrete archimedean Hardy--Titchmarsh carrier
is noncompact. -/
theorem archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    ¬ IsCompactOperator (archimedeanPrimeEulerQuadraticCorner a p q) := by
  rw [archimedeanPrimeEulerQuadraticCorner_eq_unitaryPush a p q hp hq]
  intro hcompact
  have hpull' : IsCompactOperator
      (evenCentralPositiveEulerQuadraticCorner a p q hp hq) := by
    have h := (hcompact.comp_clm
      (archimedeanDualHardyTitchmarshUnitary :
        evenSubspace →L[ℂ] ArchimedeanWeightedL2)).clm_comp
      (archimedeanDualHardyTitchmarshUnitary.symm :
        ArchimedeanWeightedL2 →L[ℂ] evenSubspace)
    simpa [unitaryPush, Function.comp_def] using h
  exact evenCentralPositiveEulerQuadraticCorner_not_isCompactOperator
    a p q ha hp hq hpull'

end RHTower
