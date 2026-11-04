import GaloisForLFunctions.SignedWindowCriticality.OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount
import GaloisForLFunctions.SignedWindowCriticality.ACriticalWindowIsAPoleChargedSolution

/-!
# The zero mode of a tight band is a reflection pair

Let the window `S = (b, c)` be symmetric about `m` and `R(v) = 2m − v`. On a collar test `f`
vanishing off `S` and beyond `m`, Weil's form on the reflection pair is
`W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`, `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`
(`OnReflectionPairsTheCouplingIsTheSmoothedPrimeCount`).

* **The band on a nonnegative window** (`abs_coupling_le_weilQuad_of_window`). If `W ≥ 0` on
  `C²_c` tests vanishing off `S`, then `|𝒞_m(f)| ≤ W(f)` for every such collar test.
* **A tight band has a reflection-pair zero mode** (`zeroMode_of_tight_band_even`,
  `zeroMode_of_tight_band_odd`, `zeroMode_of_tight_band`). If moreover `|𝒞_m(f)| = W(f)`, then
  `F₀ = f + εf∘R` with `ε = ±1` (the sign of `−𝒞_m(f)`) is a zero of the window form, it is
  `R`-symmetric up to the sign, `F₀∘R = εF₀`, and its gauge `F₀/Φ` is a pole-charged harmonic
  gauge on `S`: its Weil source vanishes there (`ACriticalWindowIsAPoleChargedSolution`).

So the first failure of the band on a nonnegative window is carried by two sites, the collar piece
and its mirror image, and one sign; at the failure the collar shape of the zero mode is the mirror
image of the collar piece, and the mode solves the pole-charged source equation with its own
charges. The bridge between Weil's form on real tests and ACT's full zero form is
`fullZeroForm_eq_weilQuad`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower _root_.RHTower _root_.RHTower.CHMDPolar
open SpacingScaleHarmonicAnalysis Zeta23 GaloisForLFunctions.ArithmeticCriticalityTheory

/-- Weil's form on a real test is ACT's full zero form. -/
theorem fullZeroForm_eq_weilQuad {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    fullZeroForm F = weilQuad F := by
  have h1 : markovEnergy (fun u => (F u : ℂ)) = weilQuad F -
      (weilPoleTerm (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re := by
    unfold markovEnergy weilQuad
    rw [Complex.sub_re]
  have h2 := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hF hFc
  unfold fullZeroForm
  rw [h1, h2]
  unfold oddPoleMoment evenPoleMoment coshHalfMoment sinhHalfMoment
  ring

/-! ### The gauge of a test -/

/-- The gauge `F/Φ` of a test `F`. -/
def testGauge (F : ℝ → ℝ) (x : ℝ) : ℝ := F x / riemannKernelReal x

theorem phiDoobTest_testGauge (F : ℝ → ℝ) : phiDoobTest (testGauge F) = F := by
  funext x
  unfold phiDoobTest testGauge
  rw [mul_div_cancel₀ _ (riemannKernelReal_pos x).ne']

theorem contDiff_testGauge {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (testGauge F) :=
  hF.div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne'

variable {f : ℝ → ℝ} {m b c : ℝ}

theorem testGauge_eq_zero {F : ℝ → ℝ} (hF : ∀ x, x ∉ Ioo b c → F x = 0) :
    ∀ x, x ∉ Ioo b c → testGauge F x = 0 := fun x hx => by
  simp [testGauge, hF x hx]

theorem hasCompactSupport_testGauge {F : ℝ → ℝ} (hF : ∀ x, x ∉ Ioo b c → F x = 0) :
    HasCompactSupport (testGauge F) :=
  HasCompactSupport.intro isCompact_Icc fun x hx =>
    testGauge_eq_zero hF x fun h => hx (Ioo_subset_Icc_self h)

/-- Window positivity of Weil's form, read in the Doob gauge. -/
theorem fullZeroForm_phiDoob_nonneg_of_window
    (hW : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, x ∉ Ioo b c → G x = 0) →
      0 ≤ weilQuad G)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hvb : ∀ x, x ∉ Ioo b c → v x = 0) : 0 ≤ fullZeroForm (phiDoobTest v) := by
  have hG : ContDiff ℝ 2 (phiDoobTest v) := contDiff_riemannKernelReal.mul hv
  have hGc : HasCompactSupport (phiDoobTest v) := by
    unfold phiDoobTest
    exact hvc.mul_left
  rw [fullZeroForm_eq_weilQuad hG.continuous hGc]
  exact hW _ hG hGc fun x hx => by simp [phiDoobTest, hvb x hx]

/-- A zero of a nonnegative window form is a pole-charged harmonic gauge. -/
theorem weilSource_testGauge_eq_zero
    (hW : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, x ∉ Ioo b c → G x = 0) →
      0 ≤ weilQuad G)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFb : ∀ x, x ∉ Ioo b c → F x = 0)
    (h0 : weilQuad F = 0) : ∀ x ∈ Ioo b c, weilSource (testGauge F) x = 0 := by
  have hFc : HasCompactSupport F :=
    HasCompactSupport.intro isCompact_Icc fun x hx => hFb x fun h => hx (Ioo_subset_Icc_self h)
  refine weilSource_eq_zero_of_zeroMode (contDiff_testGauge hF) (hasCompactSupport_testGauge hFb)
    (testGauge_eq_zero hFb) (fun v hv hvc hvb => fullZeroForm_phiDoob_nonneg_of_window hW hv hvc hvb)
    ?_
  rw [phiDoobTest_testGauge, fullZeroForm_eq_weilQuad hF.continuous hFc, h0]

/-! ### Reflection pairs in a symmetric window -/

theorem collarReflect_eq_zero_of_window (hfS : ∀ x, x ∉ Ioo b c → f x = 0) (hbc : b + c = 2 * m) :
    ∀ x, x ∉ Ioo b c → collarReflect m f x = 0 := fun x hx => by
  unfold collarReflect
  exact hfS _ fun h => hx ⟨by linarith [h.2], by linarith [h.1]⟩

/-- **The band on a nonnegative window.** -/
theorem abs_coupling_le_weilQuad_of_window (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) (hfS : ∀ x, x ∉ Ioo b c → f x = 0) (hbc : b + c = 2 * m)
    (hW : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, x ∉ Ioo b c → G x = 0) →
      0 ≤ weilQuad G) :
    |collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)| ≤
      weilQuad f := by
  have hR := collarReflect_eq_zero_of_window hfS hbc
  have hRf := contDiff_collarReflect (m := m) hf
  have hRc := hasCompactSupport_collarReflect (m := m) hfc
  refine (abs_coupling_le_weilQuad_iff hf hfc hm).mpr ⟨?_, ?_⟩
  · exact hW _ (hf.add hRf) (hfc.add hRc) fun x hx => by simp [hfS x hx, hR x hx]
  · exact hW _ (hf.add hRf.neg) (hfc.add hRc.neg) fun x hx => by simp [hfS x hx, hR x hx]

/-- **Even tight band.** If `𝒞_m(f) = −W(f)`, the `R`-symmetric pair `f + f∘R` is a zero mode of
the window: a zero of Weil's form whose gauge is pole-charged harmonic on the window. -/
theorem zeroMode_of_tight_band_even (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) (hfS : ∀ x, x ∉ Ioo b c → f x = 0) (hbc : b + c = 2 * m)
    (hW : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, x ∉ Ioo b c → G x = 0) →
      0 ≤ weilQuad G)
    (htight : collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n) =
      -weilQuad f) :
    weilQuad (fun u => f u + collarReflect m f u) = 0 ∧
      collarReflect m (fun u => f u + collarReflect m f u) = (fun u => f u + collarReflect m f u) ∧
      ∀ x ∈ Ioo b c, weilSource (testGauge fun u => f u + collarReflect m f u) x = 0 := by
  have hR := collarReflect_eq_zero_of_window hfS hbc
  have h0 : weilQuad (fun u => f u + collarReflect m f u) = 0 := by
    rw [weilQuad_add_collarReflect hf hfc hm, htight]; ring
  refine ⟨h0, ?_, weilSource_testGauge_eq_zero hW (hf.add (contDiff_collarReflect hf))
    (fun x hx => by simp [hfS x hx, hR x hx]) h0⟩
  funext u
  simp only [collarReflect, sub_sub_cancel]
  ring

/-- **Odd tight band.** If `𝒞_m(f) = W(f)`, the `R`-antisymmetric pair `f − f∘R` is a zero mode of
the window. -/
theorem zeroMode_of_tight_band_odd (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) (hfS : ∀ x, x ∉ Ioo b c → f x = 0) (hbc : b + c = 2 * m)
    (hW : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, x ∉ Ioo b c → G x = 0) →
      0 ≤ weilQuad G)
    (htight : collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n) =
      weilQuad f) :
    weilQuad (fun u => f u + -collarReflect m f u) = 0 ∧
      collarReflect m (fun u => f u + -collarReflect m f u) =
        (fun u => -(f u + -collarReflect m f u)) ∧
      ∀ x ∈ Ioo b c, weilSource (testGauge fun u => f u + -collarReflect m f u) x = 0 := by
  have hR := collarReflect_eq_zero_of_window hfS hbc
  have h0 : weilQuad (fun u => f u + -collarReflect m f u) = 0 := by
    rw [weilQuad_sub_collarReflect hf hfc hm, htight]; ring
  refine ⟨h0, ?_, weilSource_testGauge_eq_zero hW (hf.add (contDiff_collarReflect hf).neg)
    (fun x hx => by simp [hfS x hx, hR x hx]) h0⟩
  funext u
  simp only [collarReflect, sub_sub_cancel]
  ring

/-- **A tight band has a reflection-pair zero mode.** On a nonnegative symmetric window, if the
two-site band is tight, `|𝒞_m(f)| = W(f)`, then for one sign `ε = ±1` the pair `f + εf∘R` is a zero
of Weil's form, satisfies `F₀∘R = εF₀`, and has a pole-charged harmonic gauge on the window. -/
theorem zeroMode_of_tight_band (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) (hfS : ∀ x, x ∉ Ioo b c → f x = 0) (hbc : b + c = 2 * m)
    (hW : ∀ G : ℝ → ℝ, ContDiff ℝ 2 G → HasCompactSupport G → (∀ x, x ∉ Ioo b c → G x = 0) →
      0 ≤ weilQuad G)
    (htight : |collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)| =
      weilQuad f) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ weilQuad (fun u => f u + ε * collarReflect m f u) = 0 ∧
      collarReflect m (fun u => f u + ε * collarReflect m f u) =
        (fun u => ε * (f u + ε * collarReflect m f u)) ∧
      ∀ x ∈ Ioo b c, weilSource (testGauge fun u => f u + ε * collarReflect m f u) x = 0 := by
  rcases abs_choice (collarHankel m f -
      ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)) with h | h
  · obtain ⟨h0, hsym, hsrc⟩ := zeroMode_of_tight_band_odd hf hfc hm hfS hbc hW (h ▸ htight)
    refine ⟨-1, Or.inr rfl, ?_, ?_, ?_⟩
    · simpa [neg_one_mul] using h0
    · simpa [neg_one_mul] using hsym
    · simpa [neg_one_mul] using hsrc
  · obtain ⟨h0, hsym, hsrc⟩ := zeroMode_of_tight_band_even hf hfc hm hfS hbc hW
      (by linarith [h ▸ htight])
    refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
    · simpa using h0
    · simpa using hsym
    · simpa using hsrc

end GaloisForLFunctions.SignedWindowCriticality

end
