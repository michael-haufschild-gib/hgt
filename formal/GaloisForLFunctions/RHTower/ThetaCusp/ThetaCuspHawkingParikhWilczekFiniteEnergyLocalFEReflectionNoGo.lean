import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint

/-!
# Finite-energy local reflection no-go for Parikh--Wilczek

The open PW-B producer asks a physical closed-time-path reverse transition to realize the
functional-equation partner of the first-winding Mellin response before any Xi-divisor
specialization.  A source-local reverse is a fixed weighted pullback on physical energy.  If its
energy map is `tau` and its weight is `w`, implementing `s ↦ 1-s` on Mellin characters requires

`w(x) * tau(x)^(s-1) = x^(-s)`.

Only the two real grades `s=1,2` are needed.  Grade one forces `w(x)=x⁻¹`; grade two then forces
`tau(x)=x⁻¹`.  No finite physical interval `(0,X)` is closed under reciprocal energy: the canonical
interior point `x=X/(X²+1)` has reciprocal `X+X⁻¹>X`.

Consequently no spectrally independent local reverse on the literal finite Parikh--Wilczek energy
interval can produce functional-equation reflection.  This kills the local finite-energy producer
in the PW-B chain

`physical CTP reverse -> FE partner balance -> Deninger Ward cancellation -> RH`.

The sharp positive survivor is reciprocal-energy rigidity.  A successor must enlarge the energy
support and implement a nonlocal completed seam (or use a singular/spectral-dependent operation);
it is not a local reverse transition of the finite-mass source.

`[NEW] [CLASSIFICATION] [NO-GO] [PAPER-PROVED] [LEAN-PROVED] [PW-B ROUTE KILL]`
-/

namespace RHTower

noncomputable section

/-- A spectrally independent local weighted pullback on `(0,X)` which realizes the Mellin
functional-equation reflection at grades one and two.  These two equations are the specializations
of `w(x) * tau(x)^(s-1) = x^(-s)` at `s=1` and `s=2`. -/
structure PWFiniteEnergyLocalFEReflectionData (X : ℝ) where
  energyMap : ℝ → ℝ
  weight : ℝ → ℝ
  mapsPhysical : ∀ {x : ℝ}, 0 < x → x < X →
    0 < energyMap x ∧ energyMap x < X
  mellinGradeOne : ∀ {x : ℝ}, 0 < x → x < X →
    weight x = x⁻¹
  mellinGradeTwo : ∀ {x : ℝ}, 0 < x → x < X →
    weight x * energyMap x = x⁻¹ ^ 2

/-- **Two-grade reciprocal rigidity.**  Any local source map realizing FE reflection at Mellin
grades one and two is uniquely reciprocal energy on the whole physical interval. -/
theorem PWFiniteEnergyLocalFEReflectionData.energyMap_eq_inv
    {X x : ℝ} (D : PWFiniteEnergyLocalFEReflectionData X)
    (hx0 : 0 < x) (hxX : x < X) :
    D.energyMap x = x⁻¹ := by
  have h1 := D.mellinGradeOne hx0 hxX
  have h2 := D.mellinGradeTwo hx0 hxX
  rw [h1] at h2
  apply (mul_left_cancel₀ (inv_ne_zero hx0.ne'))
  simpa [pow_two] using h2

/-- No finite positive energy interval supports a local two-grade FE-reflection pullback. -/
theorem no_PWFiniteEnergyLocalFEReflectionData
    {X : ℝ} (hX : 0 < X) :
    IsEmpty (PWFiniteEnergyLocalFEReflectionData X) := by
  refine ⟨fun D => ?_⟩
  let x : ℝ := X / (X ^ 2 + 1)
  have hden : 0 < X ^ 2 + 1 := by positivity
  have hx0 : 0 < x := div_pos hX hden
  have hxX : x < X := by
    dsimp only [x]
    exact div_lt_self hX (by nlinarith [sq_pos_of_pos hX])
  have hmap := (D.mapsPhysical hx0 hxX).2
  have hrigid := D.energyMap_eq_inv hx0 hxX
  have hxinv : x⁻¹ = X + X⁻¹ := by
    dsimp only [x]
    field_simp [hX.ne']
  have hXlt : X < x⁻¹ := by
    rw [hxinv]
    exact lt_add_of_pos_right X (inv_pos.mpr hX)
  rw [hrigid] at hmap
  exact (not_lt_of_ge hXlt.le) hmap

/-- Physical specialization: the Parikh--Wilczek endpoint `X=1/(2 epsilon)` admits no local
functional-equation reverse at any positive finite backreaction scale. -/
theorem no_schwarzschildParikhWilczek_finiteEnergyLocalFEReflectionData
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    IsEmpty (PWFiniteEnergyLocalFEReflectionData
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon)) := by
  apply no_PWFiniteEnergyLocalFEReflectionData
  rw [schwarzschildParikhWilczekDimensionlessEnergyEndpoint]
  positivity

/-- Proposed local PW-B producer: at every positive finite-mass scale, one fixed physical-energy
pullback supplies the functional-equation reverse before divisor specialization. -/
def SchwarzschildParikhWilczekFiniteEnergyLocalFEReflectionProducer : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Nonempty (PWFiniteEnergyLocalFEReflectionData
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon))

/-- **PW-B local-producer route kill.**  Literal finite-energy local CTP dynamics cannot implement
the FE reflection needed for fixed-grade partner balance. -/
theorem not_schwarzschildParikhWilczekFiniteEnergyLocalFEReflectionProducer :
    ¬ SchwarzschildParikhWilczekFiniteEnergyLocalFEReflectionProducer := by
  intro h
  have hdata := h 1 (by norm_num)
  obtain ⟨D⟩ := hdata
  exact (no_schwarzschildParikhWilczek_finiteEnergyLocalFEReflectionData
    (by norm_num : (0 : ℝ) < 1)).false D

end

end RHTower
