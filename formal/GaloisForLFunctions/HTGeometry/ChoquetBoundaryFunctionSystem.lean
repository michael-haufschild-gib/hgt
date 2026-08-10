import GaloisForLFunctions.HTGeometry.BauerMaximumPrinciple
import GaloisForLFunctions.HTGeometry.MilmanExtremePoints
import GaloisForLFunctions.HTGeometry.ShilovCommutativeBoundary

/-!
# The Choquet boundary of a function system

For a subspace `S ⊆ C(X, ℂ)` on a compact Hausdorff space, the point evaluations `δₓ : s ↦ s x`
form a compact subset of the space of functions on `S`, and their closed convex hull — the *state
body* — is compact.  The **Choquet boundary** consists of the points whose evaluation is an extreme
point of the state body.

Bauer's maximum principle places the maximum of `‖·‖` over the state body at an extreme point, and
Milman's theorem identifies extreme points of the state body as point evaluations.  Together they
prove, with no hypothesis on `S` at all, that the Choquet boundary is a boundary set: every `s ∈ S`
attains its norm there.

This is the half of the Shilov boundary that the peak-point description leaves open, and unlike the
peak points the Choquet boundary is never too small.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set Metric

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Evaluation of the elements of `S` at a point of `X`. -/
noncomputable def evalPoint (S : Submodule ℂ C(X, ℂ)) (x : X) : ↥S → ℂ := fun s => (s : C(X, ℂ)) x

omit [CompactSpace X] [T2Space X] in
@[simp]
theorem evalPoint_apply (S : Submodule ℂ C(X, ℂ)) (x : X) (s : ↥S) :
    evalPoint S x s = (s : C(X, ℂ)) x := rfl

omit [CompactSpace X] [T2Space X] in
theorem continuous_evalPoint (S : Submodule ℂ C(X, ℂ)) : Continuous (evalPoint S) :=
  continuous_pi fun s => (s : C(X, ℂ)).continuous

omit [T2Space X] in
theorem isCompact_range_evalPoint (S : Submodule ℂ C(X, ℂ)) :
    IsCompact (Set.range (evalPoint S)) :=
  isCompact_range (continuous_evalPoint S)

/-- The closed convex hull of the point evaluations. -/
def stateBody (S : Submodule ℂ C(X, ℂ)) : Set (↥S → ℂ) :=
  closure (convexHull ℝ (Set.range (evalPoint S)))

omit [CompactSpace X] [T2Space X] in
theorem convex_stateBody (S : Submodule ℂ C(X, ℂ)) : Convex ℝ (stateBody S) :=
  (convex_convexHull ℝ _).closure

omit [CompactSpace X] [T2Space X] in
theorem range_evalPoint_subset_stateBody (S : Submodule ℂ C(X, ℂ)) :
    Set.range (evalPoint S) ⊆ stateBody S :=
  (subset_convexHull ℝ _).trans subset_closure

omit [T2Space X] in
/-- The state body sits inside a product of discs, hence is compact. -/
theorem isCompact_stateBody (S : Submodule ℂ C(X, ℂ)) : IsCompact (stateBody S) := by
  set B : Set (↥S → ℂ) := Set.pi univ fun s : ↥S => closedBall (0 : ℂ) ‖s‖ with hB
  have hBcomp : IsCompact B := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hBconv : Convex ℝ B := convex_pi fun _ _ => convex_closedBall _ _
  have hBclosed : IsClosed B := hBcomp.isClosed
  have hrange : Set.range (evalPoint S) ⊆ B := by
    rintro φ ⟨x, rfl⟩ s -
    simp only [evalPoint_apply, mem_closedBall, dist_zero_right]
    exact (s : C(X, ℂ)).norm_coe_le_norm x
  exact hBcomp.of_isClosed_subset isClosed_closure
    (closure_minimal (convexHull_min hrange hBconv) hBclosed)

/-- The **Choquet boundary**: the points whose evaluation is an extreme point of the state body. -/
def choquetBoundary (S : Submodule ℂ C(X, ℂ)) : Set X :=
  {x : X | evalPoint S x ∈ (stateBody S).extremePoints ℝ}

omit [T2Space X] in
/-- Every extreme point of the state body is a point evaluation, by Milman's theorem. -/
theorem exists_mem_choquetBoundary_of_extremePoint {S : Submodule ℂ C(X, ℂ)}
    {φ : ↥S → ℂ} (hφ : φ ∈ (stateBody S).extremePoints ℝ) :
    ∃ x ∈ choquetBoundary S, evalPoint S x = φ := by
  obtain ⟨x, hx⟩ := extremePoints_closure_convexHull_subset (isCompact_range_evalPoint S)
    (isCompact_stateBody S) hφ
  exact ⟨x, by rw [choquetBoundary, Set.mem_setOf_eq, hx]; exact hφ, hx⟩

omit [T2Space X] in
/-- **The Choquet boundary is a boundary set.**  Bauer's maximum principle puts the maximum of
`φ ↦ ‖φ s‖` over the state body at an extreme point, and Milman's theorem identifies that extreme
point as an evaluation. -/
theorem isBoundarySet_choquetBoundary (S : Submodule ℂ C(X, ℂ)) :
    IsBoundarySet S (choquetBoundary S) := by
  intro s hs r hr0 hr
  rcases isEmpty_or_nonempty X with hX | hX
  · have hzero : s = 0 := by
      ext x
      exact (hX.false x).elim
    rw [hzero, norm_zero]
    exact hr0
  · set t : ↥S := ⟨s, hs⟩ with ht
    set f : (↥S → ℂ) → ℝ := fun φ => ‖φ t‖ with hf
    have hfcont : Continuous f := (continuous_apply t).norm
    have hfconv : ConvexOn ℝ (stateBody S) f := by
      refine ⟨convex_stateBody S, fun φ _ ψ _ a b ha hb _ => ?_⟩
      have hval : (a • φ + b • ψ) t = a • φ t + b • ψ t := rfl
      simp only [hf, hval, smul_eq_mul]
      calc ‖(a : ℂ) • φ t + (b : ℂ) • ψ t‖ ≤ ‖(a : ℂ) • φ t‖ + ‖(b : ℂ) • ψ t‖ := norm_add_le _ _
        _ = a * ‖φ t‖ + b * ‖ψ t‖ := by
            rw [norm_smul, norm_smul]
            simp [abs_of_nonneg ha, abs_of_nonneg hb]
    have hne : (stateBody S).Nonempty :=
      ⟨evalPoint S (Classical.arbitrary X),
        range_evalPoint_subset_stateBody S ⟨Classical.arbitrary X, rfl⟩⟩
    obtain ⟨φ₀, hφ₀ext, hφ₀max⟩ :=
      exists_extremePoint_forall_le (isCompact_stateBody S) hne hfcont.continuousOn hfconv
    obtain ⟨x, hxbd, hxeq⟩ := exists_mem_choquetBoundary_of_extremePoint hφ₀ext
    have hxr : ‖(s : C(X, ℂ)) x‖ ≤ r := hr x hxbd
    rw [ContinuousMap.norm_le _ hr0]
    intro y
    have hy : f (evalPoint S y) ≤ f φ₀ :=
      hφ₀max _ (range_evalPoint_subset_stateBody S ⟨y, rfl⟩)
    rw [← hxeq] at hy
    have hcoe : ‖(s : C(X, ℂ)) y‖ ≤ ‖(s : C(X, ℂ)) x‖ := hy
    exact hcoe.trans hxr

/-! ## Real elements and the shifted boundary bound -/

/-- The real part of an element of `C(X, ℂ)`. -/
noncomputable def realPart (u : C(X, ℂ)) : C(X, ℂ) := (2 : ℂ)⁻¹ • (u + star u)

omit [CompactSpace X] [T2Space X] in
@[simp]
theorem realPart_apply (u : C(X, ℂ)) (y : X) : realPart u y = ((u y).re : ℂ) := by
  simp only [realPart, ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.star_apply,
    smul_eq_mul, Complex.star_def]
  rw [Complex.add_conj]
  push_cast
  ring

omit [CompactSpace X] [T2Space X] in
theorem realPart_mem {S : Submodule ℂ C(X, ℂ)} (hstar : ∀ s ∈ S, star s ∈ S) {u : C(X, ℂ)}
    (hu : u ∈ S) : realPart u ∈ S :=
  S.smul_mem _ (S.add_mem hu (hstar u hu))

omit [T2Space X] in
/-- **A boundary set controls real parts, not only moduli.**  Shifting a real element by its own
norm makes the modulus record the value, so the sup-norm boundary condition upgrades to a bound on
real parts. -/
theorem IsBoundarySet.re_le_of_forall_le {S : Submodule ℂ C(X, ℂ)}
    (hone : (1 : C(X, ℂ)) ∈ S) {F : Set X} (hF : IsBoundarySet S F) {u : C(X, ℂ)} (hu : u ∈ S)
    (hureal : ∀ y, (u y).im = 0) {c : ℝ} (hc : ∀ y ∈ F, (u y).re ≤ c) (x : X) :
    (u x).re ≤ c := by
  set v : C(X, ℂ) := u - (c : ℂ) • 1 with hv
  have hvS : v ∈ S := S.sub_mem hu (S.smul_mem _ hone)
  have hvval : ∀ y, v y = u y - (c : ℂ) := by
    intro y; simp [hv]
  have hvre : ∀ y, (v y).re = (u y).re - c := by
    intro y; rw [hvval y]; simp
  have hvim : ∀ y, (v y).im = 0 := by
    intro y; rw [hvval y]; simp [hureal y]
  have hvnorm : ∀ y, ‖v y‖ = |(v y).re| := by
    intro y
    have h : v y = ((v y).re : ℂ) := by
      apply Complex.ext <;> simp [hvim y]
    conv_lhs => rw [h]
    rw [Complex.norm_real, Real.norm_eq_abs]
  set b : ℝ := ‖v‖ with hb
  have hb0 : 0 ≤ b := norm_nonneg _
  have hvle : ∀ y, |(v y).re| ≤ b := by
    intro y
    rw [← hvnorm y]
    exact v.norm_coe_le_norm y
  set w : C(X, ℂ) := v + (b : ℂ) • 1 with hw
  have hwS : w ∈ S := S.add_mem hvS (S.smul_mem _ hone)
  have hwval : ∀ y, w y = v y + (b : ℂ) := by
    intro y; simp [hw]
  have hwre : ∀ y, (w y).re = (v y).re + b := by
    intro y; rw [hwval y]; simp
  have hwim : ∀ y, (w y).im = 0 := by
    intro y; rw [hwval y]; simp [hvim y]
  have hwnorm : ∀ y, ‖w y‖ = |(w y).re| := by
    intro y
    have h : w y = ((w y).re : ℂ) := by
      apply Complex.ext <;> simp [hwim y]
    conv_lhs => rw [h]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hbound : ∀ y ∈ F, ‖w y‖ ≤ b := by
    intro y hy
    rw [hwnorm y, hwre y]
    have h1 : (v y).re ≤ 0 := by
      have := hc y hy
      rw [hvre y]; linarith
    have h2 : -b ≤ (v y).re := by
      have := hvle y
      rw [abs_le] at this
      exact this.1
    rw [abs_le]
    constructor <;> linarith
  have hwle : ‖w‖ ≤ b := hF w hwS b hb0 hbound
  have hx : ‖w x‖ ≤ b := le_trans (w.norm_coe_le_norm x) hwle
  rw [hwnorm x, hwre x, abs_le] at hx
  have := hx.2
  rw [hvre x] at this
  linarith

/-! ## The Choquet boundary lies in every closed boundary -/

/-- The closed convex hull of the evaluations at the points of a subset. -/
def stateBodyOn (S : Submodule ℂ C(X, ℂ)) (F : Set X) : Set (↥S → ℂ) :=
  closure (convexHull ℝ (evalPoint S '' F))

omit [CompactSpace X] [T2Space X] in
theorem stateBodyOn_subset (S : Submodule ℂ C(X, ℂ)) (F : Set X) :
    stateBodyOn S F ⊆ stateBody S :=
  closure_mono (convexHull_mono (Set.image_subset_range _ _))

omit [CompactSpace X] [T2Space X] in
theorem evalPoint_mem_stateBodyOn_of_mem (S : Submodule ℂ C(X, ℂ)) {F : Set X} {y : X}
    (hy : y ∈ F) : evalPoint S y ∈ stateBodyOn S F :=
  subset_closure (subset_convexHull ℝ _ ⟨y, hy, rfl⟩)

omit [T2Space X] in
theorem isCompact_stateBodyOn (S : Submodule ℂ C(X, ℂ)) (F : Set X) :
    IsCompact (stateBodyOn S F) :=
  (isCompact_stateBody S).of_isClosed_subset isClosed_closure (stateBodyOn_subset S F)

omit [T2Space X] in
/-- **Every point evaluation lies in the state body of a boundary.**  Otherwise a basic
neighbourhood in the product topology separates it, and finite-dimensional Hahn–Banach produces an
element of `S` whose real part is larger at the point than anywhere on the boundary — impossible
once the boundary condition is upgraded to real parts. -/
theorem evalPoint_mem_stateBodyOn {S : Submodule ℂ C(X, ℂ)} (hone : (1 : C(X, ℂ)) ∈ S)
    (hstar : ∀ s ∈ S, star s ∈ S) {F : Set X} (hF : IsBoundarySet S F) (x : X) :
    evalPoint S x ∈ stateBodyOn S F := by
  classical
  by_contra hp
  have hopen : IsOpen (stateBodyOn S F)ᶜ := isClosed_closure.isOpen_compl
  rw [isOpen_pi_iff] at hopen
  obtain ⟨I, U, hU, hsub⟩ := hopen _ hp
  -- the finite coordinate projection
  set Ψ : (↥S → ℂ) → (↥I → ℂ) := fun φ i => φ (i : ↥S) with hΨ
  have hΨcont : Continuous Ψ := continuous_pi fun i => continuous_apply _
  have hΨlin : IsLinearMap ℝ Ψ := by
    constructor
    · intro φ ψ; rfl
    · intro a φ; rfl
  have hnot : Ψ (evalPoint S x) ∉ Ψ '' stateBodyOn S F := by
    rintro ⟨φ, hφ, hφeq⟩
    refine hsub (fun i hi => ?_) hφ
    have hiI : i ∈ I := Finset.mem_coe.mp hi
    have hval : φ i = evalPoint S x i := congrFun hφeq ⟨i, hiI⟩
    rw [hval]
    exact (hU i hiI).2
  have himgconv : Convex ℝ (Ψ '' stateBodyOn S F) :=
    ((convex_convexHull ℝ _).closure).is_linear_image hΨlin
  have himgcomp : IsCompact (Ψ '' stateBodyOn S F) := (isCompact_stateBodyOn S F).image hΨcont
  obtain ⟨l, r, hlt, hgt⟩ :=
    geometric_hahn_banach_closed_point himgconv himgcomp.isClosed hnot
  -- turn the functional into an element of `S`
  set a : ↥I → ℝ := fun i => l (Pi.single i (1 : ℂ) : ↥I → ℂ) with ha
  set b : ↥I → ℝ := fun i => l (Pi.single i Complex.I : ↥I → ℂ) with hb
  set c : ↥I → ℂ := fun i => (a i : ℂ) - (b i : ℂ) * Complex.I with hc
  set w : C(X, ℂ) := ∑ i : ↥I, c i • ((i : ↥S) : C(X, ℂ)) with hw
  have hwS : w ∈ S := Submodule.sum_mem _ fun i _ => S.smul_mem _ (i : ↥S).2
  have hlval : ∀ v : ↥I → ℂ, l v = ∑ i : ↥I, (c i * v i).re := by
    intro v
    have hsplit : v = ∑ i : ↥I, Pi.single i (v i) := (Finset.univ_sum_single v).symm
    have hterm : ∀ i : ↥I, l (Pi.single i (v i)) = (c i * v i).re := by
      intro i
      have hz : Pi.single i (v i)
          = (v i).re • (Pi.single i (1 : ℂ) : ↥I → ℂ)
            + (v i).im • (Pi.single i Complex.I : ↥I → ℂ) := by
        rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
        congr 1
        simp only [mul_one, Complex.real_smul]
        exact (Complex.re_add_im (v i)).symm
      rw [hz, map_add, map_smul, map_smul]
      simp only [smul_eq_mul, hc, ha, hb]
      simp [Complex.sub_re, Complex.mul_re, Complex.mul_im]
      ring
    calc l v = l (∑ i : ↥I, Pi.single i (v i)) := by rw [← hsplit]
      _ = ∑ i : ↥I, l (Pi.single i (v i)) := by rw [map_sum]
      _ = ∑ i : ↥I, (c i * v i).re := by exact Finset.sum_congr rfl fun i _ => hterm i
  have hlw : ∀ y : X, l (Ψ (evalPoint S y)) = (w y).re := by
    intro y
    rw [hlval]
    have : w y = ∑ i : ↥I, c i * ((i : ↥S) : C(X, ℂ)) y := by
      simp [hw, ContinuousMap.sum_apply]
    rw [this, Complex.re_sum]
    rfl
  have hFbound : ∀ y ∈ F, ((realPart w) y).re ≤ r := by
    intro y hy
    have h1 : l (Ψ (evalPoint S y)) < r :=
      hlt _ ⟨evalPoint S y, evalPoint_mem_stateBodyOn_of_mem S hy, rfl⟩
    rw [hlw y] at h1
    simp only [realPart_apply, Complex.ofReal_re]
    exact h1.le
  have hxre := (hF.re_le_of_forall_le hone (realPart_mem hstar hwS)
    (fun y => by simp [realPart_apply]) hFbound x)
  simp only [realPart_apply, Complex.ofReal_re] at hxre
  rw [← hlw x] at hxre
  exact absurd hxre (not_le.mpr hgt)

omit [T2Space X] in
/-- **The Choquet boundary is contained in every closed boundary.** -/
theorem choquetBoundary_subset_of_isBoundarySet {S : Submodule ℂ C(X, ℂ)}
    (hone : (1 : C(X, ℂ)) ∈ S) (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y)
    {F : Set X} (hFc : IsClosed F) (hF : IsBoundarySet S F) :
    choquetBoundary S ⊆ F := by
  intro x hx
  have hmem : evalPoint S x ∈ stateBodyOn S F := evalPoint_mem_stateBodyOn hone hstar hF x
  have hext : evalPoint S x ∈ (stateBodyOn S F).extremePoints ℝ := by
    refine ⟨hmem, fun y hy z hz hseg => ?_⟩
    exact hx.2 (stateBodyOn_subset S F hy) (stateBodyOn_subset S F hz) hseg
  have hFcomp : IsCompact (evalPoint S '' F) :=
    (hFc.isCompact).image (continuous_evalPoint S)
  obtain ⟨y, hyF, hyeq⟩ :=
    extremePoints_closure_convexHull_subset hFcomp (isCompact_stateBodyOn S F) hext
  by_cases hxy : x = y
  · exact hxy ▸ hyF
  · obtain ⟨s, hs, hne⟩ := hsep x y (fun h => hxy h)
    exact absurd (congrFun hyeq ⟨s, hs⟩) (by simpa [evalPoint] using hne.symm)

/-! ## Consequences for the Shilov boundary -/

omit [T2Space X] in
/-- Unconditionally, the Shilov boundary is contained in the closure of the Choquet boundary. -/
theorem shilovBoundary_subset_closure_choquetBoundary (S : Submodule ℂ C(X, ℂ)) :
    shilovBoundary S ⊆ closure (choquetBoundary S) :=
  shilovBoundary_subset isClosed_closure (isBoundarySet_choquetBoundary S).closure

omit [T2Space X] in
/-- **Closed boundaries of a function system are closed under intersection.**  Both contain the
Choquet boundary, which is itself a boundary. -/
theorem isBoundarySet_inter_of_functionSystem {S : Submodule ℂ C(X, ℂ)}
    (hone : (1 : C(X, ℂ)) ∈ S) (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y)
    {F G : Set X} (hFc : IsClosed F) (hFb : IsBoundarySet S F) (hGc : IsClosed G)
    (hGb : IsBoundarySet S G) : IsBoundarySet S (F ∩ G) :=
  (isBoundarySet_choquetBoundary S).mono
    (Set.subset_inter (choquetBoundary_subset_of_isBoundarySet hone hstar hsep hFc hFb)
      (choquetBoundary_subset_of_isBoundarySet hone hstar hsep hGc hGb))

omit [T2Space X] in
/-- **The Shilov boundary of a function system is its least closed boundary.**  This discharges the
intersection hypothesis of `isLeast_shilovBoundary`. -/
theorem isLeast_shilovBoundary_of_functionSystem (S : Submodule ℂ C(X, ℂ))
    (hone : (1 : C(X, ℂ)) ∈ S) (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) :
    IsLeast {F : Set X | IsClosed F ∧ IsBoundarySet S F} (shilovBoundary S) :=
  isLeast_shilovBoundary S fun _ _ hFc hFb hGc hGb =>
    isBoundarySet_inter_of_functionSystem hone hstar hsep hFc hFb hGc hGb

omit [T2Space X] in
/-- **The Shilov boundary is the closure of the Choquet boundary.** -/
theorem shilovBoundary_eq_closure_choquetBoundary (S : Submodule ℂ C(X, ℂ))
    (hone : (1 : C(X, ℂ)) ∈ S) (hstar : ∀ s ∈ S, star s ∈ S)
    (hsep : ∀ x y : X, x ≠ y → ∃ s ∈ S, (s : C(X, ℂ)) x ≠ s y) :
    shilovBoundary S = closure (choquetBoundary S) := by
  refine Set.Subset.antisymm (shilovBoundary_subset_closure_choquetBoundary S) ?_
  refine Set.subset_sInter fun F hF => ?_
  exact hF.1.closure_subset_iff.mpr
    (choquetBoundary_subset_of_isBoundarySet hone hstar hsep hF.1 hF.2)

end ShilovLocal

end GaloisForLFunctions.HTGeometry
