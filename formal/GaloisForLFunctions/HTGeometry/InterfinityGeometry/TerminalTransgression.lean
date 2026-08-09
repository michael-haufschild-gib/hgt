import Mathlib

/-!
# Terminal transgression and curvature flux

A *terminal datum* is a continuous representation `π` of a monoid `M` on a topological module `E`,
together with a one-parameter time ray `r : ℝ≥0 → M` and a subspace `H ≤ E` on which the ray acts
by forward annihilation: `π (r V) h → 0` for `h ∈ H`.

For an `H`-valued one-cochain `b` whose radial restriction is flat and converges, `η = −lim b(r V)`
is the unique stable radial primitive, and the remaining defect

`𝔎_b(g) = b g − (π g η − η)`

vanishes on the ray.  This file proves:

* the Bianchi identity for the curvature `ω_b(g,h) = b(gh) − b g − π g (b h)` and its invariance
  under subtracting a coboundary;
* the radial coboundary identity, forward annihilation of the primitive, and uniqueness of a stable
  radial primitive;
* the curved transgression law expressing `𝔎_b(g)` through the ordered commutator defect corrected
  by two bulk curvature faces, and its flat specialization
  `𝔎_b(g) = −lim (b(r(V) g) − b(g r(φ V)))`;
* vanishing of the flat residue at every element eventually normalized by the ray, and, in the
  curved case, the identification of the residue with the oriented difference of two curvature
  faces;
* the left/right future-ordering laws `𝔎_b(g r V) = 𝔎_b(g)` and `𝔎_b(r V g) = π(r V) 𝔎_b(g)`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open Filter Topology NNReal

/-- A continuous monoid representation together with a forward-stable time ray. -/
structure TerminalDatum (𝕜 : Type*) (M : Type*) (E : Type*) [Semiring 𝕜] [Monoid M]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] where
  /-- The representing linear maps. -/
  π : M → (E →ₗ[𝕜] E)
  /-- The unit acts trivially. -/
  π_one : π 1 = LinearMap.id
  /-- The action is multiplicative. -/
  π_mul : ∀ g h : M, π (g * h) = (π g).comp (π h)
  /-- Every representing map is continuous. -/
  π_continuous : ∀ g : M, Continuous (π g)
  /-- The future time ray. -/
  r : ℝ≥0 → M
  /-- The ray is a one-parameter semigroup. -/
  r_add : ∀ V W : ℝ≥0, r (V + W) = r V * r W
  /-- The subspace of vectors annihilated in the future. -/
  stableSpace : Submodule 𝕜 E
  /-- Forward annihilation on the stable subspace. -/
  tendsto_stable : ∀ h ∈ stableSpace, Tendsto (fun V => π (r V) h) atTop (𝓝 0)

namespace TerminalDatum

variable {𝕜 M E : Type*} [Semiring 𝕜] [Monoid M] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] (D : TerminalDatum 𝕜 M E)

/-- The coboundary of a vector. -/
def coboundary (η : E) (g : M) : E := D.π g η - η

/-- The one-cocycle law for the representation. -/
def IsCocycle (b : M → E) : Prop := ∀ g h : M, b (g * h) = b g + D.π g (b h)

/-- The curvature of a one-cochain. -/
def curvature (b : M → E) (g h : M) : E := b (g * h) - b g - D.π g (b h)

/-- The radial restriction of a cochain is flat. -/
def IsRadiallyFlat (b : M → E) : Prop := ∀ V W : ℝ≥0, D.curvature b (D.r V) (D.r W) = 0

/-- The terminal residue of a cochain relative to a radial primitive. -/
def residue (b : M → E) (η : E) (g : M) : E := b g - D.coboundary η g

@[simp] theorem coboundary_one (η : E) : D.coboundary η 1 = 0 := by
  simp [coboundary, D.π_one]

theorem isCocycle_coboundary (η : E) : D.IsCocycle (D.coboundary η) := by
  intro g h
  simp only [coboundary, D.π_mul, LinearMap.comp_apply, map_sub]
  abel

theorem isCocycle_iff_curvature_eq_zero (b : M → E) :
    D.IsCocycle b ↔ ∀ g h : M, D.curvature b g h = 0 := by
  constructor
  · intro hb g h
    rw [curvature, hb g h]
    abel
  · intro hb g h
    have := hb g h
    rw [curvature, sub_eq_zero, sub_eq_iff_eq_add] at this
    rw [this]
    abel

theorem IsCocycle.isRadiallyFlat {b : M → E} (hb : D.IsCocycle b) : D.IsRadiallyFlat b :=
  fun _ _ => (D.isCocycle_iff_curvature_eq_zero b).1 hb _ _

/-- Subtracting a coboundary does not change the curvature. -/
theorem curvature_residue (b : M → E) (η : E) :
    D.curvature (D.residue b η) = D.curvature b := by
  funext g h
  have hcob := D.isCocycle_coboundary η g h
  simp only [curvature, residue, map_sub, hcob]
  abel

theorem curvature_coboundary (η : E) : D.curvature (D.coboundary η) = fun _ _ => 0 := by
  funext g h
  rw [curvature, D.isCocycle_coboundary η g h]
  abel

/-- **Bianchi identity** for the curvature of an arbitrary one-cochain. -/
theorem bianchi (b : M → E) (g h k : M) :
    D.curvature b g h + D.curvature b (g * h) k =
      D.π g (D.curvature b h k) + D.curvature b g (h * k) := by
  simp only [curvature, map_sub, D.π_mul, LinearMap.comp_apply, mul_assoc]
  abel

theorem isCocycle_residue {b : M → E} (hb : D.IsCocycle b) (η : E) :
    D.IsCocycle (D.residue b η) :=
  (D.isCocycle_iff_curvature_eq_zero _).2 fun g h => by
    rw [D.curvature_residue b η]
    exact (D.isCocycle_iff_curvature_eq_zero b).1 hb g h

/-- The radial primitive trivializes the cochain exactly when every residue vanishes. -/
theorem eq_coboundary_iff_residue_eq_zero (b : M → E) (η : E) :
    b = D.coboundary η ↔ ∀ g : M, D.residue b η g = 0 := by
  constructor
  · intro h g
    rw [residue, h, sub_self]
  · intro h
    funext g
    have := h g
    rw [residue, sub_eq_zero] at this
    exact this

theorem tendsto_radial_shift {b : M → E} (W : ℝ≥0) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) :
    Tendsto (fun V => b (D.r (W + V))) atTop (𝓝 ℓ) :=
  hlim.comp (tendsto_atTop_mono (fun _ => le_add_self) tendsto_id)

/-! ## The curved transgression law -/

section Curved

variable [IsTopologicalAddGroup E]

/-- **The curved transgression law.**  The residue is the negative limit of the ordered commutator
defect corrected by the oriented difference of two bulk curvature faces. -/
theorem tendsto_residue_curved {b : M → E} (hmem : ∀ g, b g ∈ D.stableSpace) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (g : M) {φ : ℝ≥0 → ℝ≥0}
    (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun V => (b (D.r V * g) - b (g * D.r (φ V))) -
        (D.curvature b (D.r V) g - D.curvature b g (D.r (φ V)))) atTop
      (𝓝 (-D.residue b (-ℓ) g)) := by
  have hexp : ∀ V : ℝ≥0,
      (b (D.r V * g) - b (g * D.r (φ V))) -
          (D.curvature b (D.r V) g - D.curvature b g (D.r (φ V))) =
        b (D.r V) + D.π (D.r V) (b g) - b g - D.π g (b (D.r (φ V))) := by
    intro V
    simp only [curvature]
    abel
  have h2 : Tendsto (fun V : ℝ≥0 => D.π (D.r V) (b g)) atTop (𝓝 0) :=
    D.tendsto_stable _ (hmem g)
  have h3 : Tendsto (fun V : ℝ≥0 => D.π g (b (D.r (φ V)))) atTop (𝓝 (D.π g ℓ)) :=
    ((D.π_continuous g).tendsto ℓ).comp (hlim.comp hφ)
  have hsum : Tendsto (fun V : ℝ≥0 =>
      b (D.r V) + D.π (D.r V) (b g) - b g - D.π g (b (D.r (φ V)))) atTop
      (𝓝 (ℓ + 0 - b g - D.π g ℓ)) :=
    ((hlim.add h2).sub_const (b g)).sub h3
  have hval : ℓ + 0 - b g - D.π g ℓ = -D.residue b (-ℓ) g := by
    simp only [residue, coboundary, map_neg]
    abel
  rw [hval] at hsum
  exact hsum.congr fun V => (hexp V).symm

/-- **Flat terminal transgression.**  For a genuine cocycle the curvature faces vanish and the
residue is the negative limit of the ordered commutator defect. -/
theorem tendsto_residue_flat {b : M → E} (hmem : ∀ g, b g ∈ D.stableSpace)
    (hb : D.IsCocycle b) {ℓ : E} (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (g : M)
    {φ : ℝ≥0 → ℝ≥0} (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun V => b (D.r V * g) - b (g * D.r (φ V))) atTop
      (𝓝 (-D.residue b (-ℓ) g)) := by
  have hzero : ∀ g h : M, D.curvature b g h = 0 :=
    (D.isCocycle_iff_curvature_eq_zero b).1 hb
  refine (D.tendsto_residue_curved hmem hlim g hφ).congr fun V => ?_
  rw [hzero, hzero, sub_zero, sub_zero]

/-- **Curved bulk-boundary flux.**  If the ray eventually normalizes `g`, the residue is exactly
the oriented difference of two bulk curvature faces. -/
theorem tendsto_curvature_flux {b : M → E} (hmem : ∀ g, b g ∈ D.stableSpace) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (g : M) {φ : ℝ≥0 → ℝ≥0}
    (hφ : Tendsto φ atTop atTop) (hcomm : ∀ᶠ V in atTop, D.r V * g = g * D.r (φ V)) :
    Tendsto (fun V => D.curvature b (D.r V) g - D.curvature b g (D.r (φ V))) atTop
      (𝓝 (D.residue b (-ℓ) g)) := by
  have hneg : Tendsto (fun V => -((b (D.r V * g) - b (g * D.r (φ V))) -
      (D.curvature b (D.r V) g - D.curvature b g (D.r (φ V))))) atTop
      (𝓝 (D.residue b (-ℓ) g)) := by
    simpa using (D.tendsto_residue_curved hmem hlim g hφ).neg
  refine hneg.congr' ?_
  filter_upwards [hcomm] with V hV
  rw [hV, sub_self, zero_sub, neg_neg]

end Curved

/-! ## The stable radial primitive -/

section Radial

variable [IsTopologicalAddGroup E] [T2Space E]

/-- **The radial coboundary identity.**  A radially flat, radially convergent cochain is a
coboundary on the ray, with primitive `η = −ℓ`. -/
theorem radial_coboundary {b : M → E} (hflat : D.IsRadiallyFlat b) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (W : ℝ≥0) :
    b (D.r W) = D.coboundary (-ℓ) (D.r W) := by
  have hstep : ∀ V : ℝ≥0,
      b (D.r (W + V)) = b (D.r W) + D.π (D.r W) (b (D.r V)) := by
    intro V
    have := hflat W V
    rw [curvature, ← D.r_add W V, sub_sub, sub_eq_zero] at this
    rw [this]
  have h1 : Tendsto (fun V => b (D.r (W + V))) atTop (𝓝 ℓ) := D.tendsto_radial_shift W hlim
  have h2 : Tendsto (fun V => b (D.r W) + D.π (D.r W) (b (D.r V))) atTop
      (𝓝 (b (D.r W) + D.π (D.r W) ℓ)) :=
    (((D.π_continuous (D.r W)).tendsto ℓ).comp hlim).const_add _
  have h3 : ℓ = b (D.r W) + D.π (D.r W) ℓ :=
    tendsto_nhds_unique (h1.congr (fun V => hstep V)) h2
  have hb : b (D.r W) = ℓ - D.π (D.r W) ℓ := by
    rw [eq_sub_iff_add_eq]
    exact h3.symm
  rw [coboundary, map_neg, hb]
  abel

/-- The radial primitive is annihilated in the future. -/
theorem tendsto_radial_primitive {b : M → E} (hflat : D.IsRadiallyFlat b) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) :
    Tendsto (fun V => D.π (D.r V) (-ℓ)) atTop (𝓝 0) := by
  have hEq : ∀ V : ℝ≥0, D.π (D.r V) (-ℓ) = b (D.r V) + (-ℓ) := by
    intro V
    have := D.radial_coboundary hflat hlim V
    rw [coboundary] at this
    rw [this]
    abel
  have hsum : Tendsto (fun V => b (D.r V) + (-ℓ)) atTop (𝓝 (ℓ + -ℓ)) := hlim.add_const _
  rw [add_neg_cancel] at hsum
  exact hsum.congr fun V => (hEq V).symm

/-- **Uniqueness of the stable radial primitive.** -/
theorem stable_primitive_unique {η η' : E}
    (hEq : ∀ V : ℝ≥0, D.coboundary η (D.r V) = D.coboundary η' (D.r V))
    (hη : Tendsto (fun V => D.π (D.r V) η) atTop (𝓝 0))
    (hη' : Tendsto (fun V => D.π (D.r V) η') atTop (𝓝 0)) : η = η' := by
  have hconst : ∀ V : ℝ≥0, D.π (D.r V) η - D.π (D.r V) η' = η - η' := by
    intro V
    have h := hEq V
    simp only [coboundary] at h
    calc D.π (D.r V) η - D.π (D.r V) η'
        = (D.π (D.r V) η - η) - (D.π (D.r V) η' - η') + (η - η') := by abel
      _ = η - η' := by rw [h]; abel
  have hsub : Tendsto (fun V : ℝ≥0 => D.π (D.r V) η - D.π (D.r V) η') atTop (𝓝 0) := by
    simpa using hη.sub hη'
  have h0 : Tendsto (fun _ : ℝ≥0 => η - η') atTop (𝓝 0) := hsub.congr hconst
  have huniq : (0 : E) = η - η' := tendsto_nhds_unique h0 tendsto_const_nhds
  exact sub_eq_zero.1 huniq.symm

theorem residue_radial_eq_zero {b : M → E} (hflat : D.IsRadiallyFlat b) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (V : ℝ≥0) :
    D.residue b (-ℓ) (D.r V) = 0 := by
  rw [residue, D.radial_coboundary hflat hlim V, sub_self]

/-- **Cofinal-normalizer rigidity.**  If the ray eventually normalizes `g`, the flat residue
vanishes. -/
theorem residue_eq_zero_of_eventually_commutes {b : M → E} (hmem : ∀ g, b g ∈ D.stableSpace)
    (hb : D.IsCocycle b) {ℓ : E} (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (g : M)
    {φ : ℝ≥0 → ℝ≥0} (hφ : Tendsto φ atTop atTop)
    (hcomm : ∀ᶠ V in atTop, D.r V * g = g * D.r (φ V)) : D.residue b (-ℓ) g = 0 := by
  have hmain := D.tendsto_residue_flat hmem hb hlim g hφ
  have hzero : Tendsto (fun V => b (D.r V * g) - b (g * D.r (φ V))) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hcomm] with V hV
    rw [hV, sub_self]
  have huniq : (0 : E) = -D.residue b (-ℓ) g := tendsto_nhds_unique hzero hmain
  simpa using huniq.symm

/-! ## Future ordering -/

theorem residue_mul_radial {b : M → E} (hb : D.IsCocycle b) (hflat : D.IsRadiallyFlat b) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (g : M) (V : ℝ≥0) :
    D.residue b (-ℓ) (g * D.r V) = D.residue b (-ℓ) g := by
  rw [D.isCocycle_residue hb (-ℓ) g (D.r V), D.residue_radial_eq_zero hflat hlim V, map_zero,
    add_zero]

theorem residue_radial_mul {b : M → E} (hb : D.IsCocycle b) (hflat : D.IsRadiallyFlat b) {ℓ : E}
    (hlim : Tendsto (fun V => b (D.r V)) atTop (𝓝 ℓ)) (g : M) (V : ℝ≥0) :
    D.residue b (-ℓ) (D.r V * g) = D.π (D.r V) (D.residue b (-ℓ) g) := by
  rw [D.isCocycle_residue hb (-ℓ) (D.r V) g, D.residue_radial_eq_zero hflat hlim V, zero_add]

end Radial

end TerminalDatum

end GaloisForLFunctions.HTGeometry.Interfinity
