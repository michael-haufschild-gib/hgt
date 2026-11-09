import GaloisForLFunctions.ExceptionalLayerTheory.RotatedContoursForFiniteDivisorFilters
import GaloisForLFunctions.ExceptionalLayerTheory.VinogradovKorobovBoundsForDampingFilters

/-!
# Zero-free contours for boundary-angle damping

The angular margin is reciprocal height. Polynomial vertical weights can
be absorbed at a polynomial height cost, leaving an exponential tail on
the rescaled vertical coordinate. Pole cancellation permits a full
zero-free rectangle including bounded zeta heights.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A weighted boundary kernel retains exponential decay at scale `t`,
with a polynomial cost uniform on each positive Mellin strip. -/
theorem exists_boundaryGaussianKernel_strip_envelope {l u : ℝ}
    (hl : 0 < l) (n : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ y t x v : ℝ,
      0 < y → 1 ≤ t → l ≤ x → x ≤ u →
      ‖rotatedGaussianKernel y (boundaryDampingAngle t) ((x : ℂ) + v * I)‖ *
        (1 + |v|) ^ n ≤ C * t ^ N * y ^ (-(x / 2)) * Real.exp (-(|v| / (4 * t))) := by
  obtain ⟨A, M, hA, hb⟩ :=
    GaloisForLFunctions.RHTower.DeckPointPair.exists_bound_norm_Gamma_strip_all
      (a := l / 2) (b := u / 2) (by positivity)
  let q := M + n
  let D : ℝ := Real.exp (1 / 4) * (q.factorial : ℝ) / (1 / 4 : ℝ) ^ q
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨A / 2 * D + 1, q, by positivity, ?_⟩
  intro y t x v hy ht hx hx1
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hg := hb (x / 2) (v / 2) (by linarith only [hx]) (by linarith only [hx1])
  have hv : |v / 2| ≤ |v| := by rw [abs_div, abs_two]; linarith only [abs_nonneg v]
  have hg' : ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ ≤
      A * (1 + |v|) ^ M * Real.exp (-(Real.pi / 4 * |v|)) := by
    rw [show -(Real.pi * |v / 2| / 2) = -(Real.pi / 4 * |v|) by
      rw [abs_div, abs_two]; ring] at hg
    exact hg.trans (by gcongr)
  have hphase : boundaryDampingAngle t * v / 2 ≤
      (Real.pi / 2 - 1 / t) * |v| / 2 := by
    have hh := le_abs_self (boundaryDampingAngle t * v)
    rw [abs_mul, abs_boundaryDampingAngle ht] at hh
    linarith only [hh]
  have hraw : ‖rotatedGaussianKernel y (boundaryDampingAngle t) ((x : ℂ) + v * I)‖ *
      (1 + |v|) ^ n ≤ A / 2 * y ^ (-(x / 2)) *
        ((1 + |v|) ^ q * Real.exp (-(|v| / (2 * t)))) := by
    rw [norm_rotatedGaussianKernel, norm_gaussianMBKernel_line hy]
    have him : ((x : ℂ) + v * I).im = v := by simp
    rw [him]
    calc
      _ ≤ Real.exp ((Real.pi / 2 - 1 / t) * |v| / 2) *
          (1 / 2 * (A * (1 + |v|) ^ M * Real.exp (-(Real.pi / 4 * |v|))) *
            y ^ (-(x / 2))) * (1 + |v|) ^ n := by gcongr
      _ = _ := by
        rw [show -(|v| / (2 * t)) =
          (Real.pi / 2 - 1 / t) * |v| / 2 + -(Real.pi / 4 * |v|) by ring,
          Real.exp_add]
        dsimp only [q]
        rw [pow_add]
        ring
  let z := |v| / t
  have hz : 0 ≤ z := by dsimp only [z]; positivity
  have hp : (1 + |v|) ^ q ≤ t ^ q * (1 + z) ^ q := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have he : t * (1 + z) = t + |v| := by
      dsimp only [z]
      field_simp [ht0.ne'] <;> ring
    rw [he]
    linarith only [ht]
  have hdom : (1 + z) ^ q * Real.exp (-(z / 4)) ≤ D := by
    have hh := HTGeometry.pow_mul_exp_neg_le (by norm_num : (0 : ℝ) < 1 / 4)
      q (by positivity : 0 ≤ 1 + z)
    calc
      _ = Real.exp (1 / 4) * ((1 + z) ^ q * Real.exp (-((1 / 4) * (1 + z)))) := by
        rw [show -(z / 4) = 1 / 4 + -((1 / 4) * (1 + z)) by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (1 / 4) * ((q.factorial : ℝ) / (1 / 4 : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ = D := by dsimp only [D]; ring
  have hpoly : (1 + |v|) ^ q * Real.exp (-(|v| / (2 * t))) ≤
      t ^ q * D * Real.exp (-(|v| / (4 * t))) := by
    have he : -(|v| / (2 * t)) = -(z / 4) + -(|v| / (4 * t)) := by
      dsimp only [z]
      ring
    rw [he, Real.exp_add]
    calc
      _ ≤ (t ^ q * (1 + z) ^ q) *
          (Real.exp (-(z / 4)) * Real.exp (-(|v| / (4 * t)))) := by gcongr
      _ = t ^ q * ((1 + z) ^ q * Real.exp (-(z / 4))) *
          Real.exp (-(|v| / (4 * t))) := by ring
      _ ≤ _ := by gcongr
  refine hraw.trans ?_
  calc
    _ ≤ A / 2 * y ^ (-(x / 2)) *
        (t ^ q * D * Real.exp (-(|v| / (4 * t)))) := by gcongr
    _ = (A / 2 * D) * t ^ q * y ^ (-(x / 2)) * Real.exp (-(|v| / (4 * t))) := by ring
    _ ≤ _ := by gcongr; linarith

/-- The full filter retains every spacing factor on an absolute zeta strip.
Translation from the observation height costs only a constant. -/
theorem exists_boundaryFilteredWeight_strip_envelope (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β l u : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, ∃ N : ℕ, 0 < C ∧ ∀ y h t x v : ℝ,
      0 < y → 0 ≤ h → h ≤ 1 → 1 ≤ t → l ≤ x → x ≤ u →
      ‖rotatedDivisorFilteredMellinWeight F ρ σ β h y (boundaryDampingAngle t) t
        (((σ + x : ℝ) : ℂ) + v * I)‖ ≤
      C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) * t ^ N *
        y ^ (-(x / 2)) * Real.exp (-(|v| / (4 * t))) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨B, hB, hb⟩ := exists_divisorDampingFilter_strip_bound F ρ β (|σ| + |u|)
  obtain ⟨A, N, hA, hK⟩ := exists_boundaryGaussianKernel_strip_envelope (u := u) hl d
  refine ⟨B ^ d * A * 2 ^ d * Real.exp (1 / 4), N + d, by positivity, ?_⟩
  intro y h t x v hy hh hh1 ht hx hx1
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hx0 : 0 ≤ x := hl.le.trans hx
  have hr : |σ + x| ≤ |σ| + |u| := by
    calc
      _ ≤ |σ| + |x| := abs_add_le _ _
      _ = |σ| + x := by rw [abs_of_nonneg hx0]
      _ ≤ _ := add_le_add le_rfl (hx1.trans (le_abs_self u))
  have hp := hb (σ + x) h t (v - t) hr hh hh1
  have hcoord : (((σ + x : ℝ) : ℂ) + v * I) - ((σ : ℂ) + t * I) =
      (x : ℂ) + ((v - t : ℝ) : ℂ) * I := by push_cast; ring
  have hsum : (t : ℂ) + ((v - t : ℝ) : ℂ) = v := by push_cast; ring
  rw [hsum, abs_of_pos ht0] at hp
  have htpoly : (1 + t) ^ d ≤ (2 : ℝ) ^ d * t ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [ht]) d
  have he : Real.exp (-(|v - t| / (4 * t))) ≤
      Real.exp (1 / 4) * Real.exp (-(|v| / (4 * t))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htri := abs_add_le (v - t) t
    rw [sub_add_cancel, abs_of_pos ht0] at htri
    have hd := div_le_div_of_nonneg_right htri (by positivity : 0 ≤ 4 * t)
    have hcancel : t / (4 * t) = 1 / 4 := by field_simp [ht0.ne']
    rw [add_div, hcancel] at hd
    linarith only [hd]
  rw [rotatedDivisorFilteredMellinWeight, norm_mul, hcoord]
  calc
    _ ≤ (h * B * (1 + t) * (1 + |v - t|)) ^ d *
        ‖rotatedGaussianKernel y (boundaryDampingAngle t) ((x : ℂ) + ((v - t : ℝ) : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = B ^ d * h ^ d * (1 + t) ^ d *
        (‖rotatedGaussianKernel y (boundaryDampingAngle t) ((x : ℂ) + ((v - t : ℝ) : ℂ) * I)‖ *
          (1 + |v - t|) ^ d) := by simp only [mul_pow]; ring
    _ ≤ B ^ d * h ^ d * ((2 : ℝ) ^ d * t ^ d) *
        (A * t ^ N * y ^ (-(x / 2)) *
          (Real.exp (1 / 4) * Real.exp (-(|v| / (4 * t))))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left htpoly (by positivity)
      · exact (hK y t x (v - t) hy ht hx hx1).trans
          (mul_le_mul_of_nonneg_left he (by positivity))
      · positivity
      · positivity
    _ = _ := by rw [pow_add]; ring

/-- Truncation under a variable exponential rate retains half of the decay
and the full integral of the other half. -/
theorem norm_integral_sub_intervalIntegral_le_scaled {g : ℝ → ℂ}
    (hg : Integrable g) {B H δ : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hb : ∀ v : ℝ, ‖g v‖ ≤ B * Real.exp (-(δ * |v|))) :
    ‖(∫ v : ℝ, g v) - ∫ v in (-H)..H, g v‖ ≤
      B * Real.exp (-(δ * H / 2)) * ∫ v : ℝ, Real.exp (-(δ / 2 * |v|)) := by
  have hS : MeasurableSet (Ioc (-H) H) := measurableSet_Ioc
  rw [intervalIntegral.integral_of_le (by linarith only [hH]),
    ← integral_add_compl hS hg, add_sub_cancel_left]
  have hi : Integrable (fun v : ℝ =>
      B * Real.exp (-(δ * H / 2)) * Real.exp (-(δ / 2 * |v|))) :=
    (integrable_exp_neg_mul_abs' (by positivity : 0 < δ / 2)).const_mul _
  have hp : ∀ v ∈ (Ioc (-H) H)ᶜ,
      ‖g v‖ ≤ B * Real.exp (-(δ * H / 2)) * Real.exp (-(δ / 2 * |v|)) := by
    intro v hv
    have hHv : H ≤ |v| := by
      simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_nonpos (by linarith only [hv, hH])]; linarith only [hv]
      · rw [abs_of_pos (by linarith only [hv, hH])]; exact hv.le
    calc
      _ ≤ B * Real.exp (-(δ * |v|)) := hb v
      _ = B * (Real.exp (-(δ * |v| / 2)) * Real.exp (-(δ / 2 * |v|))) := by
        rw [← Real.exp_add]; congr 2; ring
      _ ≤ B * (Real.exp (-(δ * H / 2)) * Real.exp (-(δ / 2 * |v|))) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫ v in (Ioc (-H) H)ᶜ,
        B * Real.exp (-(δ * H / 2)) * Real.exp (-(δ / 2 * |v|)) :=
      norm_integral_le_of_norm_le hi.integrableOn
        ((ae_restrict_iff' hS.compl).mpr (Eventually.of_forall hp))
    _ ≤ ∫ v : ℝ, B * Real.exp (-(δ * H / 2)) * Real.exp (-(δ / 2 * |v|)) :=
      setIntegral_le_integral hi (Eventually.of_forall fun _ => by positivity)
    _ = _ := integral_const_mul _ _

/-- The actual zero-free rectangle controls the logarithmic derivative away
from the pole by a polynomial in its height. -/
theorem eventually_zeta_vk_full_rectangle :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ H : ℝ in atTop, ∀ z : ℂ,
      |z.im| ≤ H → 1 - vkHadamardWidth (H + 1) / 2 ≤ z.re → z.re ≤ 9 / 8 →
      zetaResidueUnit z ≠ 0 ∧
        (vkHadamardWidth (H + 1) / 2 ≤ ‖z - 1‖ →
          ‖logDeriv riemannZeta z‖ ≤ D * (1 + H) ^ 4) := by
  obtain ⟨C, δ, H₀, hC, hδ, hH₀, hH₀E, hnz, hreg⟩ :=
    Sieve.exists_bound_zetaLogDerivReg_vk_uniform
  refine ⟨(C + 2) * 10 ^ 8, by positivity, ?_⟩
  have hwlim : Tendsto (fun H : ℝ => vkHadamardWidth (H + 1)) atTop (𝓝 0) :=
    tendsto_vkHadamardWidth_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  filter_upwards [eventually_ge_atTop H₀,
    hwlim.eventually (gt_mem_nhds hδ)] with H hH hwδ
  intro z hzH hzlo hzhi
  have hH3 : 3 ≤ H := hH₀.trans hH
  have hHE : Real.exp (Real.exp 1) ≤ H + 1 := by linarith only [hH₀E.trans hH]
  have hw : 0 < vkHadamardWidth (H + 1) := vkHadamardWidth_pos hHE
  have hwidth : Sieve.vkUniformRegWidth δ H = vkHadamardWidth (H + 1) / 2 := by
    rw [Sieve.vkUniformRegWidth, min_eq_right hwδ.le]
  have hzlo' : 1 - Sieve.vkUniformRegWidth δ H ≤ z.re := by rwa [hwidth]
  have hunit : zetaResidueUnit z ≠ 0 := by
    by_cases hz1 : z = 1
    · rw [hz1, zetaResidueUnit_one]; exact one_ne_zero
    · exact (zetaResidueUnit_ne_zero_iff hz1).mpr (hnz z H hH hzH hzlo' hz1)
  refine ⟨hunit, ?_⟩
  intro hdist
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, sub_self, norm_zero] at hdist
    linarith only [hdist, hw]
  have hinv : ‖(z - 1)⁻¹‖ ≤ 2 / vkHadamardWidth (H + 1) := by
    rw [norm_inv, inv_eq_one_div]
    calc
      _ ≤ 1 / (vkHadamardWidth (H + 1) / 2) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity) hdist
      _ = _ := by ring
  have hlog1 : 1 ≤ Real.log (H + 1) := by
    apply (Real.le_log_iff_exp_le (by linarith only [hH3] : 0 < H + 1)).mpr
    exact (Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num))).trans hHE
  have hlogH : Real.log H ≤ Real.log (H + 1) :=
    Real.log_le_log (by linarith only [hH3]) (by linarith)
  have hlogupper : Real.log (H + 1) ≤ 1 + H := by
    simpa only [add_comm] using Real.log_le_self (by linarith only [hH3] : 0 ≤ H + 1)
  have hr := hreg z H hH hzH hzlo' hzhi
  rw [← norm_neg, Sieve.neg_logDeriv_riemannZeta_eq hz1 hunit]
  calc
    _ ≤ ‖(z - 1)⁻¹‖ + ‖Sieve.zetaLogDerivReg z‖ := norm_add_le _ _
    _ ≤ 2 / vkHadamardWidth (H + 1) + C * Real.log H / vkHadamardWidth (H + 1) :=
      add_le_add hinv hr
    _ ≤ (C + 2) * Real.log (H + 1) / vkHadamardWidth (H + 1) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hw.le
      nlinarith only [hlog1, mul_le_mul_of_nonneg_left hlogH hC.le]
    _ ≤ (C + 2) * Real.log (H + 1) * (10 ^ 8 * Real.log (H + 1) ^ 3) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_vkHadamardWidth_le_log_cube hHE) (by positivity)
    _ = ((C + 2) * 10 ^ 8) * Real.log (H + 1) ^ 4 := by ring
    _ ≤ _ := by gcongr

/-- A zero-free rectangle contributes no residue to the pole-killing filter. -/
theorem boundaryFilteredWeight_zero_free_rectangle (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β h φ t : ℝ) {y c r H : ℝ} (hy : 0 < y)
    (hσc : σ < c) (hc1 : c < 1) (hr1 : 1 < r) (hH : 0 < H)
    (hnz : ∀ x v : ℝ, c ≤ x → x ≤ r → |v| ≤ H →
      zetaResidueUnit ((x : ℂ) + v * I) ≠ 0) :
    rectIntegral (fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
      (-logDeriv riemannZeta z)) ((c : ℂ) + (-H : ℝ) * I) ((r : ℂ) + H * I) = 0 := by
  classical
  let z₁ : ℂ := (c : ℂ) + (-H : ℝ) * I
  let z₂ : ℂ := (r : ℂ) + H * I
  let g := rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t
  have hcr : c ≤ r := (hc1.trans hr1).le
  have hcoords (z : ℂ) (hz : z ∈ uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) :
      c ≤ z.re ∧ z.re ≤ r ∧ |z.im| ≤ H := by
    have hz' : z.re ∈ Icc c r ∧ z.im ∈ Icc (-H) H := by
      simpa [z₁, z₂, uIcc_of_le hcr, uIcc_of_le (by linarith only [hH] : -H ≤ H)] using
        Complex.mem_reProdIm.mp hz
    exact ⟨hz'.1.1, hz'.1.2, abs_le.mpr hz'.2⟩
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ {z : ℂ | σ < z.re} := by
    intro z hz
    exact hσc.trans_le (hcoords z hz).1
  have hsum : (∑ z ∈ Sieve.zetaResidueUnitClosedRectangleZeros z₁ z₂,
      ((analyticOrderAt zetaResidueUnit z).toNat : ℂ) * g z) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    obtain ⟨hzK, hz0⟩ := Sieve.mem_zetaResidueUnitClosedRectangleZeros.mp hz
    obtain ⟨hx, hxr, hv⟩ := hcoords z hzK
    have hh := hnz z.re z.im hx hxr hv
    rw [Complex.re_add_im] at hh
    exact (hh hz0).elim
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc c r := by simpa [z₁, z₂, uIcc_of_le hcr] using hx
    simpa [z₁] using hnz x (-H) hx'.1 hx'.2 (by rw [abs_neg, abs_of_pos hH])
  have htop : ∀ x ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc c r := by simpa [z₁, z₂, uIcc_of_le hcr] using hx
    simpa [z₂] using hnz x H hx'.1 hx'.2 (le_of_eq (abs_of_pos hH))
  have hright : ∀ v ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₂.re : ℂ) + v * I) ≠ 0 := by
    intro v hv
    have hv' : v ∈ Icc (-H) H := by
      simpa [z₁, z₂, uIcc_of_le (by linarith only [hH] : -H ≤ H)] using hv
    simpa [z₂] using hnz r v hcr le_rfl (abs_le.mpr hv')
  have hleft : ∀ v ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₁.re : ℂ) + v * I) ≠ 0 := by
    intro v hv
    have hv' : v ∈ Icc (-H) H := by
      simpa [z₁, z₂, uIcc_of_le (by linarith only [hH] : -H ≤ H)] using hv
    simpa [z₁] using hnz c v le_rfl hcr (abs_le.mpr hv')
  have hid := rectIntegral_weighted_neg_logDeriv_zeta
    (isOpen_lt continuous_const Complex.continuous_re)
    (analyticOnNhd_rotatedDivisorFilteredMellinWeight F ρ σ β h φ t hy) hsub
    (by simpa [z₁] using hc1) (by simpa [z₂] using hr1)
    (by simpa [z₁] using neg_neg_of_pos hH) (by simpa [z₂] using hH)
    hbot htop hright hleft
  have hpole : g 1 = 0 := by
    dsimp only [g, rotatedDivisorFilteredMellinWeight]
    rw [divisorDampingFilter_pole, zero_mul]
  simpa only [hsum, sub_zero, hpole, mul_zero] using hid

/-- Only the vanishing boundary integral is needed to compare vertical edges;
the integrand may have removable singularities inside the rectangle. -/
theorem norm_vertical_integral_le_of_rectIntegral_zero {G : ℂ → ℂ} {c r H : ℝ}
    (hrect : rectIntegral G ((c : ℂ) + (-H : ℝ) * I) ((r : ℂ) + H * I) = 0) :
    ‖∫ v in (-H)..H, G ((r : ℂ) + v * I)‖ ≤
      ‖∫ v in (-H)..H, G ((c : ℂ) + v * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + (-H : ℝ) * I)‖ +
      ‖∫ x in c..r, G ((x : ℂ) + H * I)‖ := by
  let R := ∫ v in (-H)..H, G ((r : ℂ) + v * I)
  let L := ∫ v in (-H)..H, G ((c : ℂ) + v * I)
  let B := ∫ x in c..r, G ((x : ℂ) + (-H : ℝ) * I)
  let T := ∫ x in c..r, G ((x : ℂ) + H * I)
  have he : I • R = I • L - B + T := by
    have hh : B - T + I • R - I • L = 0 := by simpa [rectIntegral, R, L, B, T] using hrect
    linear_combination hh
  have hn : ‖R‖ = ‖I • R‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  change ‖R‖ ≤ ‖L‖ + ‖B‖ + ‖T‖
  rw [hn, he]
  calc
    _ ≤ ‖I • L - B‖ + ‖T‖ := norm_add_le _ _
    _ ≤ ‖I • L‖ + ‖B‖ + ‖T‖ := by gcongr; exact norm_sub_le _ _
    _ = _ := by rw [norm_smul, Complex.norm_I, one_mul]

/-- Literal prime inversion on an absolute Euler line, with the observation
height absorbed by translation of the integration coordinate. -/
theorem rotatedPrimeDampingFilter_eq_absolute_euler_integral
    (F : Finset XiZeroCopy) (ρ : ℂ) (σ β a h φ t r : ℝ)
    (hφ : |φ| < Real.pi / 2) (hr : 1 < r) (hσr : σ < r) :
    rotatedPrimeDampingFilter (divisorDampingFilter F ρ β h) σ β a h φ t =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, rotatedDivisorFilteredMellinWeight F ρ σ β h (Real.exp (-a * t)) φ t
          ((r : ℂ) + v * I) * (-logDeriv riemannZeta ((r : ℂ) + v * I)) := by
  let y := Real.exp (-a * t)
  let G : ℂ → ℂ := fun z => rotatedDivisorFilteredMellinWeight F ρ σ β h y φ t z *
    (-logDeriv riemannZeta z)
  rw [rotatedPrimeDampingFilter_eq_euler_integral _ σ β a h φ t (r - σ)
    (sub_pos.mpr hσr) hφ (by linarith only [hr])]
  have hfun : (fun v : ℝ =>
      (divisorDampingFilter F ρ β h).eval
        (Complex.exp ((h : ℂ) * (((σ : ℂ) + t * I +
          (((r - σ : ℝ) : ℂ) + v * I)) - β))) *
        rotatedGaussianKernel y φ (((r - σ : ℝ) : ℂ) + v * I) *
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            ((σ : ℂ) + t * I + (((r - σ : ℝ) : ℂ) + v * I))) =
      (fun v : ℝ => G ((r : ℂ) + ((v + t : ℝ) : ℂ) * I)) := by
    funext v
    have hz : (σ : ℂ) + t * I + (((r - σ : ℝ) : ℂ) + v * I) =
        (r : ℂ) + (t + v) * I := by push_cast; ring
    have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        ((r : ℂ) + (t + v) * I) = -logDeriv riemannZeta ((r : ℂ) + (t + v) * I) := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hr),
        logDeriv_apply, neg_div]
    rw [hz, he]
    have hvt : ((v + t : ℝ) : ℂ) = (t : ℂ) + v := by push_cast; ring
    rw [hvt]
    dsimp only [G, rotatedDivisorFilteredMellinWeight]
    have harg : (r : ℂ) + (t + v) * I - ((σ : ℂ) + t * I) =
        (((r - σ : ℝ) : ℂ) + v * I) := by push_cast; ring
    rw [harg]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, _ = _
  rw [hfun, integral_add_right_eq_self (fun v : ℝ => G ((r : ℂ) + v * I)) t]

#print axioms exists_boundaryGaussianKernel_strip_envelope
#print axioms exists_boundaryFilteredWeight_strip_envelope
#print axioms eventually_zeta_vk_full_rectangle
#print axioms boundaryFilteredWeight_zero_free_rectangle
#print axioms rotatedPrimeDampingFilter_eq_absolute_euler_integral

end GaloisForLFunctions.ExceptionalLayerTheory
