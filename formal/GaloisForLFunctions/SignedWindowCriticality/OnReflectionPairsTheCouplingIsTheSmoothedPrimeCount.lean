import GaloisForLFunctions.SignedWindowCriticality.TheCollarHankelForm
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheEvolutionStartsPositive

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
* **The first prime stage opens positive on reflection pairs** (`abs_coupling_le_weilQuad_of_short`).
  For `f` supported in `[p, m]` with `2(m − p) ≤ 181/250` the band holds unconditionally (base
  positivity of SPATL/GWZ); for `2(m − p) ≥ log 2` the prime `2` is inside the sum.
* **The growth step on a reflection sector** (`weilQuad_stage_even`, `weilQuad_stage_odd`). For a
  collar piece `x_L` left of a cut `a ≤ m` and an interior piece `y` with `y∘R = ±y`,
  `W(x_L + y ± x_L∘R) = 2W(x_L + y) − W(y) ± 2𝒞_m(x_L)`: on each reflection sector the stage form
  reads only forms on the shorter window and the prime-count error of the collar piece.
* **The band is positivity on the pair** (`abs_coupling_le_weilQuad_iff`).
  `|𝓗_m(f) − Σ_n Λ(n)n^{−1/2}(f⋆f)(2m − log n)| ≤ W(f)` iff `W ≥ 0` on `f ± f∘R`: the ψ⋆ψ-smoothed
  prime count matches its Hankel main term within the self-energy of the bump exactly when the
  reflection pair is nonnegative. Across all scales this is the classical square-root form of RH
  read through the pole square and the trivial-zero squares (review-0311 §1.1).
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower _root_.RHTower
open SpacingScaleHarmonicAnalysis Zeta23

/-- The self-convolution `(f⋆f)(s) = ∫ f(u) f(s − u) du`. -/
def selfConv (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u, f u * f (s - u)

variable {f : ℝ → ℝ} {m : ℝ}

theorem crossCorr_collarReflect (f : ℝ → ℝ) (m x : ℝ) :
    CanonicalSystemOfTheWindowTower.crossCorr f (collarReflect m f) x = selfConv f (2 * m - x) := by
  unfold CanonicalSystemOfTheWindowTower.crossCorr collarReflect selfConv
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

/-- The coupling with the negated reflection is the negated coupling. -/
theorem orderedCoupling_neg_collarReflect (f : ℝ → ℝ) (m : ℝ) :
    orderedCoupling f (fun v => -collarReflect m f v) = -orderedCoupling f (collarReflect m f) := by
  have hc : ∀ x, CanonicalSystemOfTheWindowTower.crossCorr f (fun v => -collarReflect m f v) x =
      -CanonicalSystemOfTheWindowTower.crossCorr f (collarReflect m f) x := fun x => by
    unfold CanonicalSystemOfTheWindowTower.crossCorr
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)
  unfold orderedCoupling
  simp_rw [hc, mul_neg, tsum_neg]
  rw [integral_neg]
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
  have hneg : orderedCoupling f g = -orderedCoupling f (collarReflect m f) :=
    orderedCoupling_neg_collarReflect f m
  rw [weilQuad_add_of_ordered hord hf hfc hg hgc, hneg, orderedCoupling_collarReflect hf hfc hm,
    show weilQuad g = weilQuad (collarReflect m f) from weilQuad_neg _, weilQuad_collarReflect]
  ring

/-- **The band is positivity on the reflection pair.**
`|𝓗_m(f) − Σ_n Λ(n)n^{−1/2}(f⋆f)(2m − log n)| ≤ W(f)` iff `W(f + f∘R) ≥ 0` and `W(f − f∘R) ≥ 0`. -/
theorem abs_coupling_le_weilQuad_iff (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hm : ∀ u, m < u → f u = 0) :
    |collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)| ≤
        weilQuad f ↔
      0 ≤ weilQuad (fun u => f u + collarReflect m f u) ∧
        0 ≤ weilQuad (fun u => f u + -collarReflect m f u) := by
  rw [weilQuad_add_collarReflect hf hfc hm, weilQuad_sub_collarReflect hf hfc hm, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- `W ≥ 0` on every `C²_c` test supported in an interval of length at most `181/250` (SPATL, GWZ). -/
theorem weilQuad_nonneg_of_short {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hGc : HasCompactSupport G)
    {c L : ℝ} (hL : L ≤ 181 / 250) (hsupp : ∀ u, u ∉ Icc (c - L) c → G u = 0) :
    0 ≤ weilQuad G := by
  by_cases h0 : G = 0
  · subst h0
    rw [weilQuad_eq hG hGc]
    simp [levyEnergy, primeSum, coshHalfMoment, sinhHalfMoment]
  · exact (GrowingWindowsOfSpecZ.weilQuad_pos_of_short ⟨hG, hGc⟩ h0 hL hsupp).le

/-- **The first prime stage opens positive on reflection pairs.** For `f` supported in `[p, m]`
with `2(m − p) ≤ 181/250`, `|𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)| ≤ W(f)`. When
`2(m − p) ≥ log 2` the prime `2` is inside the sum. -/
theorem abs_coupling_le_weilQuad_of_short (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {p : ℝ} (hp : ∀ u, u < p → f u = 0) (hm : ∀ u, m < u → f u = 0)
    (hL : 2 * (m - p) ≤ 181 / 250) :
    |collarHankel m f - ∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * m - Real.log n)| ≤
      weilQuad f := by
  rw [abs_coupling_le_weilQuad_iff hf hfc hm]
  have hsupp : ∀ g : ℝ → ℝ, (∀ u, u ∉ Icc p m → g u = 0) →
      ∀ u, u ∉ Icc (2 * m - p - 2 * (m - p)) (2 * m - p) →
        g u + collarReflect m g u = 0 ∧ g u + -collarReflect m g u = 0 := by
    intro g hg u hu
    have hu' : u < p ∨ 2 * m - p < u := by
      by_contra h
      rcases not_or.mp h with ⟨h1, h2⟩
      exact hu ⟨by linarith [not_lt.mp h1], not_lt.mp h2⟩
    have h1 : g u = 0 := hg u fun h => by rcases hu' with h' | h' <;> linarith [h.1, h.2]
    have h2 : collarReflect m g u = 0 := by
      unfold collarReflect
      exact hg _ fun h => by rcases hu' with h' | h' <;> linarith [h.1, h.2]
    rw [h1, h2]; simp
  have hfs : ∀ u, u ∉ Icc p m → f u = 0 := fun u hu => by
    by_cases h : u < p
    · exact hp u h
    · exact hm u (by by_contra h'; exact hu ⟨not_lt.mp h, not_lt.mp h'⟩)
  refine ⟨weilQuad_nonneg_of_short (hf.add (contDiff_collarReflect hf))
      (hfc.add (hasCompactSupport_collarReflect hfc)) hL fun u hu => (hsupp f hfs u hu).1,
    weilQuad_nonneg_of_short (hf.add (contDiff_collarReflect hf).neg)
      (hfc.add (hasCompactSupport_collarReflect hfc).neg) hL fun u hu => (hsupp f hfs u hu).2⟩

/-! ### The growth step on a reflection sector -/

/-- **The growth step on the even reflection sector.** For a collar test `x_L` vanishing right of
`a ≤ m` and an interior test `y` vanishing left of `a` with `y∘R = y`:
`W(x_L + y + x_L∘R) = 2W(x_L + y) − W(y) + 2𝒞_m(x_L)`. -/
theorem weilQuad_stage_even {xL y : ℝ → ℝ} {a : ℝ} (hxL : ContDiff ℝ 2 xL)
    (hxLc : HasCompactSupport xL) (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
    (ham : a ≤ m) (hL : ∀ u, a < u → xL u = 0) (hI : ∀ u, u < a → y u = 0)
    (hsym : ∀ u, y (2 * m - u) = y u) :
    weilQuad (fun u => xL u + y u + collarReflect m xL u) =
      2 * weilQuad (fun u => xL u + y u) - weilQuad y +
        2 * (collarHankel m xL -
          ∑' n : ℕ, vonMangoldtAtom n * selfConv xL (2 * m - Real.log n)) := by
  have hm : ∀ u, m < u → xL u = 0 := fun u hu => hL u (by linarith)
  have hord1 : OrderedAt a xL y := ⟨hL, hI⟩
  have hord2 : OrderedAt (2 * m - a) y (collarReflect m xL) := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [← hsym u]; exact hI _ (by linarith)
    · exact hL _ (by linarith)
  have hchain := weilQuad_chain_three hord1 hord2 (by linarith) hxL hxLc hy hyc
    (contDiff_collarReflect hxL) (hasCompactSupport_collarReflect hxLc)
  have hrefl : weilQuad (fun u => y u + collarReflect m xL u) = weilQuad (fun u => xL u + y u) := by
    have h : (fun u => y u + collarReflect m xL u) =
        collarReflect m (fun u => xL u + y u) := by
      funext v; simp only [collarReflect]; rw [hsym v]; ring
    rw [h, weilQuad_collarReflect]
  rw [hchain, hrefl, orderedCoupling_collarReflect hxL hxLc hm]
  ring

/-- **The growth step on the odd reflection sector.** With `y∘R = −y`:
`W(x_L + y − x_L∘R) = 2W(x_L + y) − W(y) − 2𝒞_m(x_L)`. -/
theorem weilQuad_stage_odd {xL y : ℝ → ℝ} {a : ℝ} (hxL : ContDiff ℝ 2 xL)
    (hxLc : HasCompactSupport xL) (hy : ContDiff ℝ 2 y) (hyc : HasCompactSupport y)
    (ham : a ≤ m) (hL : ∀ u, a < u → xL u = 0) (hI : ∀ u, u < a → y u = 0)
    (hanti : ∀ u, y (2 * m - u) = -y u) :
    weilQuad (fun u => xL u + y u + -collarReflect m xL u) =
      2 * weilQuad (fun u => xL u + y u) - weilQuad y -
        2 * (collarHankel m xL -
          ∑' n : ℕ, vonMangoldtAtom n * selfConv xL (2 * m - Real.log n)) := by
  have hm : ∀ u, m < u → xL u = 0 := fun u hu => hL u (by linarith)
  have hord1 : OrderedAt a xL y := ⟨hL, hI⟩
  have hord2 : OrderedAt (2 * m - a) y (fun v => -collarReflect m xL v) := by
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · have := hanti (2 * m - u)
      rw [show 2 * m - (2 * m - u) = u by ring] at this
      rw [this, hI _ (by linarith), neg_zero]
    · simp only [collarReflect, hL _ (by linarith : a < 2 * m - u), neg_zero]
  have hchain := weilQuad_chain_three hord1 hord2 (by linarith) hxL hxLc hy hyc
    (contDiff_collarReflect hxL).neg (hasCompactSupport_collarReflect hxLc).neg
  have hrefl : weilQuad (fun u => y u + -collarReflect m xL u) =
      weilQuad (fun u => xL u + y u) := by
    have h : (fun u => y u + -collarReflect m xL u) =
        fun v => -collarReflect m (fun u => xL u + y u) v := by
      funext v; simp only [collarReflect]; rw [hanti v]; ring
    rw [h, weilQuad_neg, weilQuad_collarReflect]
  rw [hchain, hrefl, orderedCoupling_neg_collarReflect, orderedCoupling_collarReflect hxL hxLc hm]
  ring

end GaloisForLFunctions.SignedWindowCriticality

end
