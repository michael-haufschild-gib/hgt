import GaloisForLFunctions.ArtinMertens.LatticePointsInADomainWithLipschitzBoundary

/-!
# The frontier of the norm ball in the fundamental cone is Lipschitz

`normLeOne K = {x ∈ fundamental cone : N(x) ≤ 1}` has its frontier covered by finitely many smooth
images of faces of the unit cube `[0,1]^ι`, `ι = InfinitePlace K ⊕ {complex places}`, so
`card ι = [K : ℚ]` (`frontier_normLeOne_subset`, `card_paramIndex`,
`exists_lipschitzOnWith_boundaryParam`).

The parametrization `Φ_σ(y)` (`boundaryParam`) reads `u = y(w₀) ∈ [0,1]`, unit exponents
`x_i = y(i) ∈ [0,1]` and angles `θ_w = y(w) ∈ [0,1]`, and returns the point with
`|Φ_w| = u Π_i |η_i|_w^{x_i}` (`radialPart`), sign `σ_w` at the real places and argument `2πθ_w`
at the complex places. Mathlib's description of `normLeOne` through `expMapBasis` places the
frontier over the boundary of the parameter box: closure points have `|x_w| = expMapBasis(p)_w`
with `p` in the closed box `(−∞, 0] × [0,1]^r` (or `x = 0`), interior points have `p` in the open
box. So a frontier point has `u = e^{p(w₀)} = 1` (norm one), some `x_i ∈ {0, 1}` (a wall of the
cone) or `u = 0` (the apex).
-/

noncomputable section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem Set
open scoped Classical NNReal

namespace GaloisForLFunctions.ArtinMertens

variable (K : Type*) [Field K] [NumberField K]

/-- Parameter coordinates: one per infinite place (the scale at `w₀`, unit exponents elsewhere)
and one per complex place (an angle). -/
abbrev paramIndex : Type _ := InfinitePlace K ⊕ {w : InfinitePlace K // IsComplex w}

theorem card_paramIndex : Fintype.card (paramIndex K) = Module.finrank ℝ (mixedSpace K) := by
  rw [Fintype.card_sum, mixedEmbedding.finrank, ← card_add_two_mul_card_eq_rank,
    card_eq_nrRealPlaces_add_nrComplexPlaces, nrComplexPlaces]
  ring

variable {K}

/-- The radial part `r_w(y) = u Π_i |η_i|_w^{x_i}`, `u = y(w₀)`, `x_i = y(i)`. -/
def radialPart (y : paramIndex K → ℝ) (w : InfinitePlace K) : ℝ :=
  y (Sum.inl w₀) * Real.exp (∑ i : {w : InfinitePlace K // w ≠ w₀},
    Real.log (w (algebraMap (𝓞 K) K (fundSystem K (fundamentalCone.equivFinRank.symm i)))) *
      y (Sum.inl i.1))

/-- The parametrization `Φ_σ`: signs `σ` at the real places, arguments `2πθ` at the complex
places. -/
def boundaryParam (σ : {w : InfinitePlace K // IsReal w} → Bool) (y : paramIndex K → ℝ) :
    mixedSpace K :=
  (fun w => (if σ w then 1 else -1) * radialPart y w.1,
    fun w => (radialPart y w.1 : ℂ) *
      Complex.exp (((2 * Real.pi * y (Sum.inr w) : ℝ) : ℂ) * Complex.I))

theorem contDiff_radialPart (w : InfinitePlace K) :
    ContDiff ℝ 1 fun y : paramIndex K → ℝ => radialPart y w := by
  unfold radialPart
  fun_prop

theorem contDiff_boundaryParam (σ : {w : InfinitePlace K // IsReal w} → Bool) :
    ContDiff ℝ 1 (boundaryParam σ) := by
  refine ContDiff.prodMk (contDiff_pi.mpr fun w => ?_) (contDiff_pi.mpr fun w => ?_)
  · exact contDiff_const.mul (contDiff_radialPart w.1)
  · refine (Complex.ofRealCLM.contDiff.comp (contDiff_radialPart w.1)).mul ?_
    refine (Complex.contDiff_exp.restrict_scalars ℝ).comp ?_
    refine ContDiff.mul (Complex.ofRealCLM.contDiff.comp ?_) contDiff_const
    exact contDiff_const.mul (contDiff_apply ℝ ℝ (Sum.inr w))

/-- A uniform Lipschitz constant for the finitely many parametrizations on the unit cube. -/
theorem exists_lipschitzOnWith_boundaryParam :
    ∃ M : ℝ≥0, ∀ σ, LipschitzOnWith M (boundaryParam (K := K) σ) (Icc 0 1) := by
  choose Mσ hMσ using fun σ => (contDiff_boundaryParam (K := K) σ).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_Icc 0 1) isCompact_Icc
  exact ⟨Finset.univ.sup Mσ, fun σ => (hMσ σ).weaken (Finset.le_sup (Finset.mem_univ σ))⟩

/-- On the parameters of a point `p` of the box, the radial part is `expMapBasis p`. -/
theorem radialPart_eq {p : realSpace K} {y : paramIndex K → ℝ}
    (h₀ : y (Sum.inl w₀) = Real.exp (p w₀))
    (h : ∀ i : {w : InfinitePlace K // w ≠ w₀}, y (Sum.inl i.1) = p i.1) (w : InfinitePlace K) :
    radialPart y w = expMapBasis p w := by
  rw [expMapBasis_apply', Pi.smul_apply, smul_eq_mul, radialPart, h₀, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h i, Real.rpow_def_of_pos (w.pos_iff.mpr (by simp))]

/-- The angle `θ ∈ [0, 1]` with `e^{2πiθ} = z/|z|`. -/
def unitAngle (z : ℂ) : ℝ :=
  if 0 ≤ z.arg then z.arg / (2 * Real.pi) else z.arg / (2 * Real.pi) + 1

theorem unitAngle_mem_Icc (z : ℂ) : unitAngle z ∈ Icc (0 : ℝ) 1 := by
  have hpi := Real.pi_pos
  have h₁ := Complex.neg_pi_lt_arg z
  have h₂ := Complex.arg_le_pi z
  unfold unitAngle
  split_ifs with h
  · constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith
  · constructor
    · have : -(1 / 2 : ℝ) < z.arg / (2 * Real.pi) := by
        rw [lt_div_iff₀ (by positivity)]
        linarith
      linarith
    · have : z.arg / (2 * Real.pi) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith)
        (by positivity)
      linarith

theorem norm_mul_exp_unitAngle (z : ℂ) :
    (‖z‖ : ℂ) * Complex.exp (((2 * Real.pi * unitAngle z : ℝ) : ℂ) * Complex.I) = z := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have harg : Complex.exp (((2 * Real.pi * unitAngle z : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((z.arg : ℂ) * Complex.I) := by
    unfold unitAngle
    split_ifs
    · congr 2
      push_cast
      field_simp
    · rw [show (((2 * Real.pi * (z.arg / (2 * Real.pi) + 1) : ℝ) : ℂ) * Complex.I) =
          (z.arg : ℂ) * Complex.I + 2 * Real.pi * Complex.I by push_cast; field_simp; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [harg, Complex.norm_mul_exp_arg_mul_I]

/-- **The frontier of the norm ball lies over the faces of the parameter box.** -/
theorem frontier_normLeOne_subset :
    frontier (normLeOne K) ⊆
      ⋃ j : ({w : InfinitePlace K // IsReal w} → Bool) × paramIndex K × Bool,
        boundaryParam j.1 '' cubeFace j.2.1 (if j.2.2 then 1 else 0) := by
  intro x hx
  have hcl : normAtAllPlaces x ∈ compactSet K := closure_normLeOne_subset K hx.1
  have hint : normAtAllPlaces x ∉ expMapBasis '' interior (paramSet K) := fun h =>
    hx.2 (subset_interior_normLeOne K h)
  rw [compactSet_eq_union, mem_union, mem_singleton_iff] at hcl
  rcases hcl with ⟨p, hp, hpx⟩ | h0
  · -- `|x_w| = expMapBasis(p)_w` with `p` on the boundary of the box
    have hpint : p ∉ interior (paramSet K) := fun h => hint ⟨p, h, hpx⟩
    rw [closure_paramSet, mem_univ_pi] at hp
    rw [interior_paramSet, mem_univ_pi] at hpint
    simp only [not_forall] at hpint
    obtain ⟨w₁, hw₁⟩ := hpint
    have hpw₀ : p w₀ ≤ 0 := by simpa using hp w₀
    have hpw : ∀ w, w ≠ w₀ → p w ∈ Icc (0 : ℝ) 1 := fun w hw => by simpa [hw] using hp w
    set y : paramIndex K → ℝ := Sum.elim (fun w => if w = w₀ then Real.exp (p w₀) else p w)
      (fun w => unitAngle (x.2 w)) with hydef
    have hyI : ∀ i, y i ∈ Icc (0 : ℝ) 1 := by
      rintro (w | w)
      · by_cases hw : w = w₀
        · simp only [hydef, Sum.elim_inl, if_pos hw]
          exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr hpw₀⟩
        · simp only [hydef, Sum.elim_inl, if_neg hw]
          exact hpw w hw
      · exact unitAngle_mem_Icc _
    have hrad : ∀ w, radialPart y w = normAtPlace w x := fun w => by
      rw [radialPart_eq (p := p) (by simp [hydef]) (fun i => by simp [hydef, i.2]),
        hpx, normAtAllPlaces_apply]
    -- the face carrying the boundary coordinate
    obtain ⟨i₁, b₁, hface⟩ : ∃ (i₁ : paramIndex K) (b₁ : Bool), y i₁ = if b₁ then 1 else 0 := by
      by_cases hw : w₁ = w₀
      · subst hw
        have : p w₀ = 0 := by
          simp only [if_pos rfl, mem_Iio, not_lt] at hw₁
          linarith
        exact ⟨Sum.inl w₀, true, by simp [hydef, this]⟩
      · have hI := hpw w₁ hw
        simp only [if_neg hw, mem_Ioo, not_and, not_lt] at hw₁
        rcases eq_or_lt_of_le hI.1 with h0 | h0
        · exact ⟨Sum.inl w₁, false, by simp [hydef, hw, ← h0]⟩
        · exact ⟨Sum.inl w₁, true, by simp [hydef, hw, le_antisymm hI.2 (hw₁ h0)]⟩
    refine mem_iUnion.mpr ⟨(fun w => decide (0 ≤ x.1 w), i₁, b₁), y,
      ⟨⟨fun i => (hyI i).1, fun i => (hyI i).2⟩, hface⟩, ?_⟩
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp only [boundaryParam]
      rw [hrad, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
      by_cases h : 0 ≤ x.1 w
      · simp [h, abs_of_nonneg h]
      · simp [h, abs_of_neg (not_le.mp h)]
    · simp only [boundaryParam]
      rw [hrad, normAtPlace_apply_of_isComplex w.2]
      exact norm_mul_exp_unitAngle (x.2 w)
  · -- the apex
    have hx0 : x = 0 := forall_normAtPlace_eq_zero_iff.mp (congrFun h0)
    refine mem_iUnion.mpr ⟨(fun _ => true, Sum.inl w₀, false), 0,
      ⟨⟨le_rfl, zero_le_one⟩, by simp⟩, ?_⟩
    rw [hx0]
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_) <;> simp [boundaryParam, radialPart]

end GaloisForLFunctions.ArtinMertens
