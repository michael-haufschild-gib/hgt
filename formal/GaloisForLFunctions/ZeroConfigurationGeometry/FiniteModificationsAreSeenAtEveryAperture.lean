import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw
import GaloisForLFunctions.SquareRootThreshold.WeilFormDeterminesTheConfiguration
import GaloisForLFunctions.RHTower.BakerGeneralProof.ExponentialPolynomial
import GaloisForLFunctions.RHTower.CosDilationBlindGoldenSupportVanishing
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt

/-!
# Finite modifications are seen at every aperture

Two tempered configurations `Z, Z'` are compared through their images, the Weil forms
`W(f, f) = Σ_ρ m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)` on windows supported in `[−r, r]`. No sign is used:
the question is only whether the images agree.

**Theorem** (`eq_of_weil_eq_on_aperture_of_finite`). If `Z` and `Z'` differ in finitely many points
(the signed multiplicity `m_Z − m_{Z'}` has finite support) and their images agree on every `C²`
window supported in `[−r, r]`, for one `r > 0`, then `Z = Z'`.

So a cancelling cluster is always infinite (`infinite_modification_of_mimic`): finitely many points
can never be rearranged, added or removed without changing the image at every aperture. This is
the sign-free counterpart of `finiteOffLine_visible`, where a finite off-line set produces a
*negative* Weil form only beyond a logarithmic aperture; identification needs no aperture at all.
For `ζ` (`zeta_finite_modification_seen`): every configuration that differs from the zeros of `ζ`
in finitely many points has a different image on windows of any aperture, hence on the prime side
`p ≤ e^{2r}` of the explicit formula.

**Proof.**
* The image difference is the image of the signed modification `c = m_Z − m_{Z'}`, a finite sum
  `Σ_z c_z f̂(γ_z) conj ĝ(conj γ_z)` (`W_sub_W_eq_sum`). Polarization in the window recovers the
  off-diagonal images from the diagonal ones (`modImage_eq_zero_of_diag`).
* For a fixed `g`, the functional `f ↦ Σ_z a_z f̂(γ_z) = ∫ f(u) E(u) du` with the exponential
  polynomial `E(u) = Σ_z a_z e^{iγ_z u}` vanishes on all smooth windows in `(−r, r)`, so `E = 0` on
  `(−r, r)` (fundamental lemma), hence on `ℂ` (identity theorem), hence `a_z = 0` (distinct
  frequencies are independent, `expPoly_finset_eq_zero`).
* A window `g = b·e^{−iw̄u}` with a normalized bump `b` has `ĝ(w̄) = 1`, which forces `c_z = 0`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The image of a single point `z` on the window pair `(f, g)`. -/
def pointImage (f g : ℝ → ℂ) (z : ℂ) : ℂ :=
  paperFT f (gammaOf z) * conj (paperFT g (conj (gammaOf z)))

theorem paperFT_add_smul {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (c z : ℂ) :
    paperFT (fun u => f u + c * g u) z = paperFT f z + c * paperFT g z := by
  have h1 : Integrable fun u : ℝ => f u * cexp (I * z * u) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have h2 : Integrable fun u : ℝ => g u * cexp (I * z * u) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  rw [paperFT_def, paperFT_def, paperFT_def, ← integral_const_mul, ← integral_add h1 (h2.const_mul c)]
  congr 1 with u; ring

/-! ### The image of the signed modification -/

theorem Wsummand_eq_mul (Z : ZeroConfig) (f g : ℝ → ℂ) (ρ : ℂ) :
    Z.Wsummand f g ρ = (Z.mult ρ : ℂ) * pointImage f g ρ := by
  simp only [ZeroConfig.Wsummand, pointImage, mul_assoc]

theorem W_eq_tsum_indicator (Z : ZeroConfig) (f g : ℝ → ℂ) :
    Z.W f g = ∑' z : ℂ, Z.carrier.indicator (fun z => (Z.mult z : ℂ)) z * pointImage f g z := by
  rw [ZeroConfig.W, tsum_congr fun ρ : Z.carrier => Wsummand_eq_mul Z f g ρ]
  exact (tsum_subtype Z.carrier fun z => (Z.mult z : ℂ) * pointImage f g z).trans
    (tsum_congr fun z => Set.indicator_mul_left _ _ _)

theorem summable_indicator_pointImage (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Summable fun z : ℂ => Z.carrier.indicator (fun z => (Z.mult z : ℂ)) z * pointImage f g z := by
  have hs' : Summable ((fun z => (Z.mult z : ℂ) * pointImage f g z) ∘ Subtype.val :
      Z.carrier → ℂ) :=
    (ArithmeticCastelnuovoSeveri.summable_Wsummand Z hZ hf hfc hg hgc).congr fun ρ =>
      Wsummand_eq_mul Z f g ρ
  exact (summable_subtype_iff_indicator.mp hs').congr fun z => Set.indicator_mul_left _ _ _

/-- **The image difference is the image of the signed modification**, a finite sum when the
modification is finite. -/
theorem W_sub_W_eq_sum {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {S : Finset ℂ} (hS : ∀ z ∉ S, multDiff Z Z' z = 0) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Z.W f g - Z'.W f g = ∑ z ∈ S, multDiff Z Z' z * pointImage f g z := by
  rw [W_eq_tsum_indicator, W_eq_tsum_indicator,
    ← (summable_indicator_pointImage Z hZ hf hfc hg hgc).tsum_sub
      (summable_indicator_pointImage Z' hZ' hf hfc hg hgc)]
  rw [tsum_eq_sum (s := S) fun z hz => by rw [← sub_mul, ← multDiff, hS z hz, zero_mul]]
  exact Finset.sum_congr rfl fun z _ => by rw [multDiff, sub_mul]

/-! ### Polarization -/

/-- The image of a finite signed modification `c` on `(f, g)`. -/
def modImage (S : Finset ℂ) (c : ℂ → ℂ) (f g : ℝ → ℂ) : ℂ :=
  ∑ z ∈ S, c z * pointImage f g z

theorem pointImage_add_smul {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (c z : ℂ) :
    pointImage (fun u => f u + c * g u) (fun u => f u + c * g u) z =
      pointImage f f z + c * pointImage g f z + conj c * pointImage f g z +
        c * conj c * pointImage g g z := by
  simp only [pointImage, paperFT_add_smul hf hfc hg hgc, map_add, map_mul]
  ring

theorem modImage_add_smul (S : Finset ℂ) (c : ℂ → ℂ) {f g : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (a : ℂ) :
    modImage S c (fun u => f u + a * g u) (fun u => f u + a * g u) =
      modImage S c f f + a * modImage S c g f + conj a * modImage S c f g +
        a * conj a * modImage S c g g := by
  simp only [modImage, pointImage_add_smul hf hfc hg hgc, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1; congr 1; congr 1
  all_goals exact Finset.sum_congr rfl fun z _ => by ring

/-- **Polarization.** Diagonal images determine the off-diagonal ones. -/
theorem modImage_eq_zero_of_diag {S : Finset ℂ} {c : ℂ → ℂ} {r : ℝ}
    (h : ∀ f, ApertureWindow r f → modImage S c f f = 0) {f g : ℝ → ℂ}
    (hf : ApertureWindow r f) (hg : ApertureWindow r g) : modImage S c f g = 0 := by
  have hfc := hf.hasCompactSupport
  have hgc := hg.hasCompactSupport
  have e1 := modImage_add_smul S c hf.1.continuous hfc hg.1.continuous hgc 1
  have eI := modImage_add_smul S c hf.1.continuous hfc hg.1.continuous hgc I
  rw [h _ (hf.add_smul hg 1), h f hf, h g hg] at e1
  rw [h _ (hf.add_smul hg I), h f hf, h g hg] at eI
  simp only [map_one, Complex.conj_I, zero_add, add_zero, one_mul, mul_zero] at e1 eI
  have h2 : modImage S c g f - modImage S c f g = 0 := by
    have : I * (modImage S c g f - modImage S c f g) = 0 := by linear_combination -eI
    exact (mul_eq_zero.mp this).resolve_left Complex.I_ne_zero
  linear_combination (-1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * h2

/-! ### Exponential sums vanishing on an interval -/

/-- A smooth bump of unit mass supported in `[−r, r]`. -/
theorem exists_unit_bump {r : ℝ} (hr : 0 < r) :
    ∃ b : ℝ → ℝ, ContDiff ℝ 2 b ∧ tsupport b ⊆ Icc (-r) r ∧ ∫ u, b u = 1 := by
  let B : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by linarith, by linarith⟩
  refine ⟨B.normed volume, B.contDiff_normed, ?_, B.integral_normed⟩
  rw [B.tsupport_normed_eq]
  intro u hu
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, show B.rOut = r from rfl] at hu
  exact abs_le.mp hu

/-- A window whose transform equals `1` at a prescribed point `w`. -/
theorem exists_window_paperFT_eq_one {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ∃ g : ℝ → ℂ, ApertureWindow r g ∧ paperFT g w = 1 := by
  obtain ⟨b, hb, hbs, hbi⟩ := exists_unit_bump hr
  refine ⟨fun u => (b u : ℂ) * cexp (-(I * w * u)), ⟨?_, ?_⟩, ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hb).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)
  · refine (tsupport_mul_subset_left).trans ?_
    exact (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero b).trans hbs
  · rw [paperFT_def]
    have : ∀ u : ℝ, (b u : ℂ) * cexp (-(I * w * u)) * cexp (I * w * u) = (b u : ℂ) := fun u => by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    simp_rw [this]
    rw [integral_complex_ofReal, hbi, Complex.ofReal_one]

/-- **Exponential sums do not vanish against all windows.** If `Σ_z a_z f̂(γ_z) = 0` for every
window of aperture `r`, the coefficients vanish. -/
theorem coeff_eq_zero_of_forall_window {S : Finset ℂ} {a : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ f, ApertureWindow r f → ∑ z ∈ S, a z * paperFT f (gammaOf z) = 0) :
    ∀ z ∈ S, a z = 0 := by
  set E : ℝ → ℂ := fun u => ∑ z ∈ S, a z * cexp (I * gammaOf z * u) with hE
  have hEc : Continuous E := by fun_prop
  -- `E` vanishes on `(−r, r)`
  have hae : ∀ᵐ x : ℝ, x ∈ Ioo (-r) r → E x = 0 := by
    refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hEc.locallyIntegrable (μ := volume)).locallyIntegrableOn _)
      fun ψ hψ hψc hψs => ?_
    have hw : ApertureWindow r fun u => (ψ u : ℂ) :=
      ⟨Complex.ofRealCLM.contDiff.comp (hψ.of_le (by norm_cast)),
        (tsupport_comp_subset (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero ψ).trans
          (hψs.trans Ioo_subset_Icc_self)⟩
    have h0 := h _ hw
    have hint : ∀ z ∈ S, Integrable fun u : ℝ => a z * ((ψ u : ℂ) * cexp (I * gammaOf z * u)) :=
      fun z _ => (((Complex.continuous_ofReal.comp hψ.continuous).mul
        (by fun_prop)).integrable_of_hasCompactSupport
        ((hψc.comp_left Complex.ofReal_zero).mul_right)).const_mul _
    simp only [paperFT_def, ← integral_const_mul] at h0
    rw [← integral_finsetSum S hint] at h0
    rw [← h0]
    congr 1 with u
    simp only [hE, Finset.smul_sum, Complex.real_smul]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hzero : ∀ x : ℝ, -r < x → x < r → E x = 0 := by
    intro x hx1 hx2
    by_contra hne
    set V : Set ℝ := Ioo (-r) r ∩ {x | E x ≠ 0}
    have hVo : IsOpen V := isOpen_Ioo.inter (isOpen_ne_fun hEc continuous_const)
    have hV0 : volume V = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae] with y hy hyV
      exact hyV.2 (hy hyV.1)
    have := (hVo.measure_eq_zero_iff volume).mp hV0
    exact (Set.eq_empty_iff_forall_notMem.mp this) x ⟨⟨hx1, hx2⟩, hne⟩
  -- analytic continuation of `E` to `ℂ`
  set G : ℂ → ℂ := fun w => ∑ z ∈ S, Polynomial.eval w (Polynomial.C (a z)) *
    cexp (I * gammaOf z * w) with hG
  have hGd : Differentiable ℂ G := by
    simp only [hG, Polynomial.eval_C]; fun_prop
  have hG0 : EqOn G 0 univ := RHTower.eqOn_zero_of_real_interval
    (hGd.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (neg_lt_self hr)
    (mem_univ _) fun x hx1 hx2 => by
      simpa only [hG, Polynomial.eval_C] using hzero x hx1 hx2
  have hinj : Set.InjOn (fun z => I * gammaOf z) S := fun z _ z' _ hzz => by
    have h1 : gammaOf z = gammaOf z' := mul_left_cancel₀ Complex.I_ne_zero hzz
    simpa [gammaOf, div_left_inj' Complex.I_ne_zero, sub_left_inj] using h1
  have hall := RHTower.BakerGeneralProof.expPoly_finset_eq_zero S (fun z => I * gammaOf z)
    (fun z => Polynomial.C (a z)) hinj (funext fun w => hG0 (mem_univ w))
  exact fun z hz => Polynomial.C_eq_zero.mp (hall z hz)

/-! ### The theorem -/

/-- **Finite modifications are seen at every aperture.** Two tempered configurations that differ
in finitely many points and have equal images on every window of one aperture `r > 0` are equal. -/
theorem eq_of_weil_eq_on_aperture_of_finite {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') (hfin : {z | multDiff Z Z' z ≠ 0}.Finite) {r : ℝ} (hr : 0 < r)
    (hW : ∀ f, ApertureWindow r f → Z.W f f = Z'.W f f) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  set S := hfin.toFinset
  have hS : ∀ z ∉ S, multDiff Z Z' z = 0 := fun z hz => by
    by_contra h; exact hz (hfin.mem_toFinset.mpr h)
  have hdiag : ∀ f, ApertureWindow r f → modImage S (multDiff Z Z') f f = 0 := fun f hf => by
    have hfc := hf.hasCompactSupport
    rw [modImage, ← W_sub_W_eq_sum hZ hZ' hS hf.1 hfc hf.1 hfc, hW f hf, sub_self]
  refine eq_of_multDiff_eq_zero fun z₀ => ?_
  by_cases hz₀ : z₀ ∈ S
  · obtain ⟨g, hg, hg1⟩ := exists_window_paperFT_eq_one hr (conj (gammaOf z₀))
    have hcoef := coeff_eq_zero_of_forall_window (a := fun z =>
        multDiff Z Z' z * conj (paperFT g (conj (gammaOf z)))) hr (fun f hf => by
      have := modImage_eq_zero_of_diag hdiag hf hg
      rw [modImage] at this
      rw [← this]
      exact Finset.sum_congr rfl fun z _ => by simp only [pointImage]; ring) z₀ hz₀
    simpa [hg1] using hcoef
  · exact hS z₀ hz₀

/-- **Cancelling clusters are infinite.** Distinct tempered mimics at any aperture differ in
infinitely many points. -/
theorem infinite_modification_of_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {r : ℝ} (hr : 0 < r)
    (hW : ∀ f, ApertureWindow r f → Z.W f f = Z'.W f f) (hne : Z.carrier ≠ Z'.carrier) :
    {z | multDiff Z Z' z ≠ 0}.Infinite :=
  fun hfin => hne (eq_of_weil_eq_on_aperture_of_finite hZ hZ' hfin hr hW).1

/-- **The zeros of `ζ` admit no finite rearrangement with the same image.** A tempered
configuration that differs from the zeros of `ζ` in finitely many points and has the image of `ζ`
on windows of some aperture `r > 0` is the configuration of `ζ`. -/
theorem zeta_finite_modification_seen {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hfin : {z | multDiff Z zetaZeroConfig z ≠ 0}.Finite) {r : ℝ} (hr : 0 < r)
    (hW : ∀ f, ApertureWindow r f → Z.W f f = zetaZeroConfig.W f f) :
    Z.carrier = zetaZeroConfig.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = zetaZeroConfig.mult ρ :=
  eq_of_weil_eq_on_aperture_of_finite hZ temperedConfig_zetaZeroConfig hfin hr hW

end GaloisForLFunctions.ZeroConfigurationGeometry
