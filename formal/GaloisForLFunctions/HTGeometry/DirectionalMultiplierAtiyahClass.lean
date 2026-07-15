import GaloisForLFunctions.HTGeometry.DirectionalKaehlerWedge

/-!
# Directional multiplier cocycles and their Atiyah class

Equivariant derivations logarithmically differentiate a multiplicative group-action cocycle into
an additive cocycle.  This construction is linear in the derivation and therefore defines an
Atiyah-class map into additive first cohomology.  Under an exact fixed-field hypothesis, its
kernel consists exactly of directions in which the multiplier primitive satisfies a first-order
linear differential equation over the base field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {G k K L : Type*} [Group G] [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- The `k`-linear space of derivations commuting with a semilinear group action. -/
def equivariantDerivations
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c) :
    Submodule k (Derivation k K K) where
  carrier := {D | ∀ g y, D (ρ g y) = ρ g (D y)}
  zero_mem' := by simp
  add_mem' := by
    intro D E hD hE g y
    simp only [Derivation.add_apply]
    rw [hD g y, hE g y, map_add]
  smul_mem' := by
    intro c D hD g y
    simp only [Derivation.smul_apply, Algebra.smul_def]
    rw [hD g y, map_mul, hfix]

/-- Additive one-cocycles for the action `ρ`, as a `k`-linear space. -/
def additiveActionCocycles
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c) :
    Submodule k (G → K) where
  carrier := {β | ∀ g h, β (g * h) = ρ g (β h) + β g}
  zero_mem' := by simp
  add_mem' := by
    intro β γ hβ hγ g h
    simp only [Pi.add_apply]
    rw [hβ g h, hγ g h, map_add]
    abel
  smul_mem' := by
    intro c β hβ g h
    simp only [Pi.smul_apply, Algebra.smul_def]
    rw [hβ g h, mul_add, map_mul, hfix]

/-- The linear coboundary map `b ↦ (g ↦ g(b) - b)`. -/
def additiveCoboundaryMap
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c) :
    K →ₗ[k] additiveActionCocycles ρ hfix where
  toFun b := ⟨fun g => ρ g b - b, by
    intro g h
    change ρ (g * h) b - b = ρ g (ρ h b - b) + (ρ g b - b)
    rw [map_mul]
    change ρ g (ρ h b) - b = ρ g (ρ h b - b) + (ρ g b - b)
    rw [map_sub]
    abel⟩
  map_add' b c := by
    ext g
    simp
    abel
  map_smul' c b := by
    apply Subtype.ext
    funext g
    dsimp
    simp only [Algebra.smul_def]
    rw [map_mul, hfix]
    ring

/-- Additive first cohomology for the semilinear action. -/
abbrev AdditiveActionH1
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c) :=
  additiveActionCocycles ρ hfix ⧸ LinearMap.range (additiveCoboundaryMap ρ hfix)

/-- The logarithmic derivative of a multiplicative multiplier cocycle. -/
def multiplierLogCocycle (D : Derivation k K K) (a : G → Kˣ) (g : G) : K :=
  D (a g : K) / (a g : K)

/-- Logarithmic differentiation of a multiplicative cocycle is a linear map from equivariant
derivations to additive one-cocycles. -/
def multiplierLogCocycleLinearMap
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c)
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = ρ g (a h : K) * (a g : K)) :
    equivariantDerivations ρ hfix →ₗ[k] additiveActionCocycles ρ hfix where
  toFun D := ⟨multiplierLogCocycle D.1 a, by
    intro g h
    rw [multiplierLogCocycle, multiplierLogCocycle,
      multiplierLogCocycle, ha, Derivation.leibniz, D.2]
    rw [map_div₀]
    field_simp
    ring⟩
  map_add' D E := by
    ext g
    simp [multiplierLogCocycle, add_div]
  map_smul' c D := by
    ext g
    simp [multiplierLogCocycle, Algebra.smul_def]
    ring

/-- The directional multiplier Atiyah-class map. -/
def multiplierAtiyahClassMap
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c)
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = ρ g (a h : K) * (a g : K)) :
    equivariantDerivations ρ hfix →ₗ[k] AdditiveActionH1 ρ hfix :=
  (Submodule.mkQ (LinearMap.range (additiveCoboundaryMap ρ hfix))).comp
    (multiplierLogCocycleLinearMap ρ hfix a ha)

/-- Vanishing of the Atiyah class is exactly existence of an additive coboundary primitive. -/
theorem multiplierAtiyahClassMap_eq_zero_iff
    (ρ : G →* (K ≃+* K))
    (hfix : ∀ g c, ρ g (algebraMap k K c) = algebraMap k K c)
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = ρ g (a h : K) * (a g : K))
    (D : equivariantDerivations ρ hfix) :
    multiplierAtiyahClassMap ρ hfix a ha D = 0 ↔
      ∃ b : K, ∀ g, multiplierLogCocycle D.1 a g = ρ g b - b := by
  rw [multiplierAtiyahClassMap, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro g
    exact (congrArg (fun f : additiveActionCocycles ρ hfix => f.1 g) hb).symm
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    ext g
    exact (hb g).symm

omit [IsScalarTower k K L] in
/-- The logarithmic derivative of a multiplier primitive shifts by the logarithmically
differentiated multiplier. -/
theorem multiplier_logDeriv_boundary
    (ρL : G →* (L ≃+* L))
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hDcomp : ∀ y, D (algebraMap K L y) = algebraMap K L (D₀ y))
    (hDcomm : ∀ g y, D (ρL g y) = ρL g (D y))
    (a : G → Kˣ) (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, ρL g X = algebraMap K L (a g : K) * X)
    (g : G) :
    ρL g (D X / X) =
      D X / X + algebraMap K L (multiplierLogCocycle D₀ a g) := by
  rw [map_div₀, ← hDcomm, hmul, Derivation.leibniz, hDcomp]
  dsimp [multiplierLogCocycle]
  rw [map_div₀]
  field_simp [hX]

omit [IsScalarTower k K L] in
/-- A logarithmic multiplier cocycle is a coboundary exactly when the primitive's logarithmic
derivative lies in the base field. -/
theorem multiplierLogCocycle_isCoboundary_iff_logDeriv_mem_base
    (ρK : G →* (K ≃+* K)) (ρL : G →* (L ≃+* L))
    (hcomp : ∀ g y, ρL g (algebraMap K L y) = algebraMap K L (ρK g y))
    (hfixed : ∀ z : L, (∀ g, ρL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hDcomp : ∀ y, D (algebraMap K L y) = algebraMap K L (D₀ y))
    (hDcomm : ∀ g y, D (ρL g y) = ρL g (D y))
    (a : G → Kˣ) (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, ρL g X = algebraMap K L (a g : K) * X) :
    (∃ b : K, ∀ g, multiplierLogCocycle D₀ a g = ρK g b - b) ↔
      ∃ q : K, algebraMap K L q = D X / X := by
  constructor
  · rintro ⟨b, hb⟩
    let u : L := D X / X
    let z : L := u - algebraMap K L b
    have hzfix : ∀ g, ρL g z = z := by
      intro g
      dsimp [z, u]
      rw [map_sub, multiplier_logDeriv_boundary ρL D₀ D
        hDcomp hDcomm a X hX hmul g, hcomp, hb g, map_sub]
      ring
    obtain ⟨c, hc⟩ := hfixed z hzfix
    refine ⟨c + b, ?_⟩
    rw [map_add]
    dsimp [z, u] at hc
    linear_combination hc
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    intro g
    apply (algebraMap K L).injective
    rw [map_sub, ← hcomp, hq]
    have hboundary := multiplier_logDeriv_boundary ρL D₀ D
      hDcomp hDcomm a X hX hmul g
    rw [hboundary]
    ring

omit [IsScalarTower k K L] in
/-- Exact first-order interpretation of logarithmic-cocycle triviality. -/
theorem multiplierLogCocycle_isCoboundary_iff_exists_firstOrder
    (ρK : G →* (K ≃+* K)) (ρL : G →* (L ≃+* L))
    (hcomp : ∀ g y, ρL g (algebraMap K L y) = algebraMap K L (ρK g y))
    (hfixed : ∀ z : L, (∀ g, ρL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hDcomp : ∀ y, D (algebraMap K L y) = algebraMap K L (D₀ y))
    (hDcomm : ∀ g y, D (ρL g y) = ρL g (D y))
    (a : G → Kˣ) (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, ρL g X = algebraMap K L (a g : K) * X) :
    (∃ b : K, ∀ g, multiplierLogCocycle D₀ a g = ρK g b - b) ↔
      ∃ q : K, D X = algebraMap K L q * X := by
  rw [multiplierLogCocycle_isCoboundary_iff_logDeriv_mem_base
    ρK ρL hcomp hfixed D₀ D hDcomp hDcomm a X hX hmul]
  apply exists_congr
  intro q
  constructor
  · intro hq
    exact (div_eq_iff hX).mp hq.symm
  · intro hq
    exact ((div_eq_iff hX).mpr hq).symm

omit [IsScalarTower k K L] in
/-- **Directional Atiyah-kernel theorem.**  The class map vanishes exactly in the directions in
which the multiplier primitive obeys a first-order linear differential equation over `K`. -/
theorem multiplierAtiyahClassMap_eq_zero_iff_exists_firstOrder
    (ρK : G →* (K ≃+* K)) (ρL : G →* (L ≃+* L))
    (hfix : ∀ g c, ρK g (algebraMap k K c) = algebraMap k K c)
    (hcomp : ∀ g y, ρL g (algebraMap K L y) = algebraMap K L (ρK g y))
    (hfixed : ∀ z : L, (∀ g, ρL g z = z) → ∃ q : K, algebraMap K L q = z)
    (D₀ : equivariantDerivations ρK hfix) (D : Derivation k L L)
    (hDcomp : ∀ y, D (algebraMap K L y) = algebraMap K L (D₀.1 y))
    (hDcomm : ∀ g y, D (ρL g y) = ρL g (D y))
    (a : G → Kˣ)
    (ha : ∀ g h, (a (g * h) : K) = ρK g (a h : K) * (a g : K))
    (X : L) (hX : X ≠ 0)
    (hmul : ∀ g, ρL g X = algebraMap K L (a g : K) * X) :
    multiplierAtiyahClassMap ρK hfix a ha D₀ = 0 ↔
      ∃ q : K, D X = algebraMap K L q * X := by
  rw [multiplierAtiyahClassMap_eq_zero_iff]
  exact multiplierLogCocycle_isCoboundary_iff_exists_firstOrder
    ρK ρL hcomp hfixed D₀.1 D hDcomp hDcomm a X hX hmul

end

end GaloisForLFunctions.HTGeometry
