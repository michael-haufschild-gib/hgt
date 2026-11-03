import GaloisForLFunctions.SignedWindowCriticality.TheCollarHankelForm
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum

/-!
# On reflection pairs the coupling is the smoothed prime count

Let `f` be a `C²_c` test vanishing right of `m`, and `f∘R`, `R(v) = 2m − v`, its reflection; the
pair is ordered at `m` (CSTW `OrderedAt`). Their cross-correlation is a self-convolution,
`c_{f, f∘R}(x) = (f⋆f)(2m − x)` (`crossCorr_collarReflect`), so CSTW's ordered coupling — the
archimedean place and the pole through the collar kernel, minus the primes — reads

    𝒞_m(f) = 𝓗_m(f) − Σ_n Λ(n) n^{−1/2} (f⋆f)(2m − log n)          (`orderedCoupling_collarReflect`),

with the collar Hankel form `𝓗_m(f) = e^m μ_{1/2}(f)² − Σ_k e^{2mσ_k} μ_{σ_k}(f)²`. The first term of
`𝓗_m` is the main term of the smoothed prime count at `t = 2m`, the trivial-zero squares are its
exponentially small corrections, and `𝒞_m(f)` is the error of the prime count against them.

* **Two-site identity** (`weilQuad_add_collarReflect`, `weilQuad_sub_collarReflect`).
  `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`: the window form of a reflection pair is the self-energy of one
  site plus or minus the prime-count error.
* **The band under RH** (`abs_coupling_le_weilQuad_of_riemannHypothesis`). Under RH,
  `|𝓗_m(f) − Σ_n Λ(n)n^{−1/2}(f⋆f)(2m − log n)| ≤ W(f)` for every such `f` and every `m`: the
  ψ⋆ψ-smoothed prime count matches its Hankel main term within the self-energy of the bump, at
  every scale. This is the classical square-root form of RH read through the pole square and the
  trivial-zero squares (review-0311 §1.1).
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower _root_.RHTower
open SpacingScaleHarmonicAnalysis

/-- The self-convolution `(f⋆f)(s) = ∫ f(u) f(s − u) du`. -/
def selfConv (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u, f u * f (s - u)

variable {f : ℝ → ℝ} {m : ℝ}

theorem crossCorr_collarReflect (f : ℝ → ℝ) (m x : ℝ) :
    crossCorr f (collarReflect m f) x = selfConv f (2 * m - x) := by
  unfold crossCorr collarReflect selfConv
  exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring_nf)

theorem orderedAt_collarReflect (hf : ∀ u, m < u → f u = 0) : OrderedAt m f (collarReflect m f) :=
  ⟨hf, fun u hu => hf _ (by linarith)⟩

theorem contDiff_collarReflect (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (collarReflect m f) :=
  hf.comp (contDiff_const.sub contDiff_id)

theorem hasCompactSupport_collarReflect (hfc : HasCompactSupport f) :
    HasCompactSupport (collarReflect m f) := by
  have h : collarReflect m f = fun v => (fun w => f (-w)) (v - 2 * m) := by
    funext v; simp only [collarReflect]; ring_nf
  rw [h]
  exact (hfc.comp_homeomorph (Homeomorph.neg ℝ)).comp_homeomorph (Homeomorph.subRight (2 * m))

/-- **The ordered coupling of a reflection pair.** -/
theorem orderedCoupling_collarReflect (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) :
    orderedCoupling f (collarReflect m f) =
      collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n) := by
  unfold orderedCoupling
  rw [(orderedAt_collarReflect hm).integral_collarKernel_mul_eq_moments hf hfc
    (contDiff_collarReflect hf) (hasCompactSupport_collarReflect hfc)]
  have h := momentPairing_collarReflect m f
  unfold momentPairing at h
  rw [h]
  simp_rw [crossCorr_collarReflect]

/-- Weil's form does not see the reflection `R(v) = 2m − v`. -/
theorem weilQuad_collarReflect (f : ℝ → ℝ) (m : ℝ) : weilQuad (collarReflect m f) = weilQuad f := by
  have h : collarReflect m f = fun v => (fun w => f (-w)) (v - 2 * m) := by
    funext v; simp only [collarReflect]; ring_nf
  rw [h, weilQuad_comp_sub (fun w => f (-w)) (2 * m),
    CohomologyOfWindowsOfSpecZ.weilQuad_comp_neg]

/-- Weil's form is even. -/
theorem weilQuad_neg (f : ℝ → ℝ) : weilQuad (fun u => -f u) = weilQuad f := by
  unfold weilQuad
  have hk : EF.weilTest (fun u => ((-f u : ℝ) : ℂ)) (fun u => ((-f u : ℝ) : ℂ)) =
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) := by
    funext y
    rw [RHTower.weilTest_ofReal_eq, RHTower.weilTest_ofReal_eq]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  rw [hk]

/-- **Two-site identity, even sign.** `W(f + f∘R) = 2W(f) + 2𝒞_m(f)`. -/
theorem weilQuad_add_collarReflect (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) :
    weilQuad (fun u => f u + collarReflect m f u) =
      2 * weilQuad f + 2 * (collarHankel m f -
        ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)) := by
  rw [weilQuad_add_of_ordered (orderedAt_collarReflect hm) hf hfc (contDiff_collarReflect hf)
    (hasCompactSupport_collarReflect hfc), weilQuad_collarReflect,
    orderedCoupling_collarReflect hf hfc hm]
  ring

/-- **Two-site identity, odd sign.** `W(f − f∘R) = 2W(f) − 2𝒞_m(f)`. -/
theorem weilQuad_sub_collarReflect (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) :
    weilQuad (fun u => f u + -collarReflect m f u) =
      2 * weilQuad f - 2 * (collarHankel m f -
        ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)) := by
  set g : ℝ → ℝ := fun v => -collarReflect m f v
  have hord : OrderedAt m f g := ⟨hm, fun u hu => by
    simp only [g, collarReflect, hm _ (by linarith : m < 2 * m - u), neg_zero]⟩
  have hg : ContDiff ℝ 2 g := (contDiff_collarReflect hf).neg
  have hgc : HasCompactSupport g := (hasCompactSupport_collarReflect hfc).neg
  have hneg : orderedCoupling f g = -orderedCoupling f (collarReflect m f) := by
    have hc : ∀ x, crossCorr f g x = -crossCorr f (collarReflect m f) x := fun x => by
      unfold crossCorr
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun u => by simp only [g]; ring)
    unfold orderedCoupling
    simp_rw [hc, mul_neg, tsum_neg]
    rw [integral_neg]
    ring
  rw [weilQuad_add_of_ordered hord hf hfc hg hgc, hneg, orderedCoupling_collarReflect hf hfc hm,
    show weilQuad g = weilQuad (collarReflect m f) from weilQuad_neg _, weilQuad_collarReflect]
  ring

/-- **The band under RH.** Under RH the reflection-pair coupling is bounded by the self-energy:
`|𝓗_m(f) − Σ_n Λ(n)n^{−1/2}(f⋆f)(2m − log n)| ≤ W(f)`. -/
theorem abs_coupling_le_weilQuad_of_riemannHypothesis (hRH : RiemannHypothesis)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hm : ∀ u, m < u → f u = 0) :
    |collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)| ≤
      weilQuad f := by
  have hW := ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg.mp hRH
  have h1 := hW _ (hf.add (contDiff_collarReflect hf))
    (hfc.add (hasCompactSupport_collarReflect hfc))
  have h2 := hW _ (hf.add (contDiff_collarReflect hf).neg)
    (hfc.add (hasCompactSupport_collarReflect hfc).neg)
  rw [weilQuad_add_collarReflect hf hfc hm] at h1
  rw [weilQuad_sub_collarReflect hf hfc hm] at h2
  rw [abs_le]
  constructor <;> linarith

end GaloisForLFunctions.SignedWindowCriticality

end
