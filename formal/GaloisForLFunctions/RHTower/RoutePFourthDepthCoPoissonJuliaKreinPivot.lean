import GaloisForLFunctions.RHTower.RoutePFourthDepthCoPoissonJuliaColligation

/-!
# Route P fourth-depth co-Poisson Julia--Krein pivot

P-G103 proved that repairing fourth-depth energy `w / 64` requires a negative pivot `-w`
and cross `(sqrt 63 / 8) w`.  P-G104 identified the cross coefficient with the Julia defect of
the normalized contraction `c = 1 / 8`; P-G105 realized that contraction and defect on Burnol's
actual even co-Poisson carrier.  This file constructs the missing pivot from those same data.

For `U` the unitary fourfold dilation and `d = sqrt (1 - c^(2 : ℕ))`, define

```text
child f = (c U f, 0),
pivot f = ((d / c) U f, (1 / c) f).
```

In the canonical signature `(+, -)` their Krein Gram block is exactly

```text
[[ ||f||^(2 : ℕ) / 64, (sqrt 63 / 8) ||f||^(2 : ℕ) ],
 [ (sqrt 63 / 8) ||f||^(2 : ℕ),              -||f||^(2 : ℕ) ]].
```

Thus P-G103's pivot, cross, determinant, and restored Schur energy are all forced by the same
Julia colligation; none is fitted independently.  The signature is also the diagonalization of
source/co-source exchange, matching the fundamental-symmetry geometry already present in the
joint-depth Euler landing.  Both pivot coordinates remain in Burnol's two-level source ladder.

This closes the local co-Poisson realization.  It does not yet identify the pivot with the
Gamma/Stokes co-source or assemble the cofinal prime incidence.
-/

open Complex MeasureTheory Set
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Diagonal Krein pairing on the two resolved co-Poisson channels. -/
def routePPrimitiveFourthDepthCoPoissonKreinPair
    (x y : evenSubspace × evenSubspace) : ℂ :=
  ⟪x.1, y.1⟫_ℂ - ⟪x.2, y.2⟫_ℂ

/-- Off-diagonal form selected by source/co-source exchange. -/
def routePPrimitiveFourthDepthCoPoissonSourceExchangePair
    (x y : evenSubspace × evenSubspace) : ℂ :=
  ⟪x.1, y.2⟫_ℂ + ⟪x.2, y.1⟫_ℂ

/-- Unnormalized Hadamard coordinates from polar channels to source/co-source channels. -/
def routePPrimitiveFourthDepthCoPoissonSourceCoSourceCoordinates
    (v : evenSubspace × evenSubspace) : evenSubspace × evenSubspace :=
  (v.1 + v.2, v.1 - v.2)

/-- Source/co-source exchange diagonalizes to twice the `(+, -)` Krein form.  Hence the negative
environment direction is forced by exchange symmetry rather than inserted as a scalar sign. -/
theorem routePPrimitiveFourthDepthCoPoisson_sourceExchange_diagonalizes
    (x y : evenSubspace × evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonSourceExchangePair
        (routePPrimitiveFourthDepthCoPoissonSourceCoSourceCoordinates x)
        (routePPrimitiveFourthDepthCoPoissonSourceCoSourceCoordinates y) =
      2 * routePPrimitiveFourthDepthCoPoissonKreinPair x y := by
  simp only [routePPrimitiveFourthDepthCoPoissonSourceExchangePair,
    routePPrimitiveFourthDepthCoPoissonSourceCoSourceCoordinates,
    routePPrimitiveFourthDepthCoPoissonKreinPair,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-- The diagonal co-Poisson Krein pairing is Hermitian. -/
theorem routePPrimitiveFourthDepthCoPoissonKreinPair_conj_symm
    (x y : evenSubspace × evenSubspace) :
    star (routePPrimitiveFourthDepthCoPoissonKreinPair y x) =
      routePPrimitiveFourthDepthCoPoissonKreinPair x y := by
  change (starRingEnd ℂ) (⟪y.1, x.1⟫_ℂ - ⟪y.2, x.2⟫_ℂ) = _
  rw [map_sub,
    @inner_conj_symm ℂ evenSubspace _ _ _ x.1 y.1,
    @inner_conj_symm ℂ evenSubspace _ _ _ x.2 y.2]
  rfl

/-- Contracted fourth-depth child placed in the positive channel. -/
def routePPrimitiveFourthDepthCoPoissonKreinChild
    (f : evenSubspace) : evenSubspace × evenSubspace :=
  (routePPrimitiveFourthDepthCoPoissonContraction f, 0)

/-- Canonical Julia co-graph pivot.  Its first coordinate is `(d / c) U₄ f`; defining it through
the already realized child keeps coefficient provenance literal. -/
def routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot
    (f : evenSubspace) : evenSubspace × evenSubspace :=
  let c : ℂ := routeEPCubicFourthDepthNormalizedContraction
  let d : ℂ := routeEPCubicFourthDepthJuliaDefect
  ((d / c ^ (2 : ℕ)) • routePPrimitiveFourthDepthCoPoissonContraction f,
    (1 / c) • f)

theorem routeEPCubicFourthDepthNormalizedContraction_ne_zero :
    routeEPCubicFourthDepthNormalizedContraction ≠ 0 := by
  norm_num [routeEPCubicFourthDepthNormalizedContraction]

/-- Julia's Pythagorean identity is precisely the Lorentz normalization of the pivot. -/
theorem routeEPCubicFourthDepthJulia_lorentzCoefficient :
    (routeEPCubicFourthDepthJuliaDefect /
          routeEPCubicFourthDepthNormalizedContraction) ^ (2 : ℕ) -
        (1 / routeEPCubicFourthDepthNormalizedContraction) ^ (2 : ℕ) = -1 := by
  have h := routeEPCubicFourthDepthJulia_pythagoras
  field_simp [routeEPCubicFourthDepthNormalizedContraction_ne_zero]
  nlinarith

/-- Literal co-graph formula for the positive coordinate of the Julia pivot. -/
theorem routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot_fst
    (f : evenSubspace) :
    (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f).1 =
      ((routeEPCubicFourthDepthJuliaDefect /
        routeEPCubicFourthDepthNormalizedContraction : ℝ) : ℂ) •
          evenDilationCLM 4 (by norm_num) f := by
  rw [routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot]
  dsimp only
  rw [routePPrimitiveFourthDepthCoPoissonContraction, smul_apply, smul_smul]
  congr 1
  push_cast
  field_simp [routeEPCubicFourthDepthNormalizedContraction_ne_zero]

/-- Both pivot coordinates remain actual co-Poisson sources at the child and parent apertures. -/
theorem routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot_mem_sourceSpaces
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) :
    (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f).1 ∈
        burnolCoPoissonSourceSpace ((4 : ℝ)⁻¹ * b) ∧
      (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f).2 ∈
        burnolCoPoissonSourceSpace b := by
  rw [routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot]
  dsimp only
  exact ⟨Submodule.smul_mem _ _
      (routePPrimitiveFourthDepthCoPoissonContraction_mem_sourceSpace hb hf),
    Submodule.smul_mem _ _ hf⟩

/-- Child diagonal entry is the literal fourth-depth energy `w / 64`. -/
theorem routePPrimitiveFourthDepthCoPoissonKreinPair_child_child
    (f : evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonKreinPair
        (routePPrimitiveFourthDepthCoPoissonKreinChild f)
        (routePPrimitiveFourthDepthCoPoissonKreinChild f) =
      ((‖f‖ ^ (2 : ℕ) / 64 : ℝ) : ℂ) := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair,
    routePPrimitiveFourthDepthCoPoissonKreinChild]
  simp only [sub_zero, inner_zero_left]
  change ⟪(routePPrimitiveFourthDepthCoPoissonContraction f : evenSubspace),
      (routePPrimitiveFourthDepthCoPoissonContraction f : evenSubspace)⟫_ℂ = _
  have hinner := inner_self_eq_norm_sq_to_K
    (𝕜 := ℂ) (routePPrimitiveFourthDepthCoPoissonContraction f)
  rw [hinner, norm_routePPrimitiveFourthDepthCoPoissonContraction]
  norm_num [routeEPCubicFourthDepthNormalizedContraction]
  ring

/-- Child--pivot entry is exactly the Julia defect times parent energy. -/
theorem routePPrimitiveFourthDepthCoPoissonKreinPair_child_pivot
    (f : evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonKreinPair
        (routePPrimitiveFourthDepthCoPoissonKreinChild f)
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f) =
      (routeEPCubicFourthDepthJuliaDefect : ℂ) * (‖f‖ : ℂ) ^ (2 : ℕ) := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair,
    routePPrimitiveFourthDepthCoPoissonKreinChild,
    routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot]
  dsimp only
  simp only [inner_zero_left, sub_zero]
  rw [@inner_smul_right ℂ evenSubspace _ _ _
    (routePPrimitiveFourthDepthCoPoissonContraction f)
    (routePPrimitiveFourthDepthCoPoissonContraction f)
    ((routeEPCubicFourthDepthJuliaDefect : ℂ) /
      (routeEPCubicFourthDepthNormalizedContraction : ℂ) ^ (2 : ℕ))]
  have hinner := inner_self_eq_norm_sq_to_K
    (𝕜 := ℂ) (routePPrimitiveFourthDepthCoPoissonContraction f)
  rw [hinner, norm_routePPrimitiveFourthDepthCoPoissonContraction]
  norm_num [routeEPCubicFourthDepthNormalizedContraction]
  field_simp
  ring

/-- Child--pivot entry is P-G103's uniquely required quantized cross. -/
theorem routePPrimitiveFourthDepthCoPoissonKreinPair_child_pivot_eq_quantized
    (f : evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonKreinPair
        (routePPrimitiveFourthDepthCoPoissonKreinChild f)
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f) =
      (routeEPCubicFourthDepthQuantizedPolarCross (‖f‖ ^ (2 : ℕ)) : ℂ) := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair_child_pivot,
    routeEPCubicFourthDepthQuantizedPolarCross,
    routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  norm_cast

/-- The Julia co-graph pivot has exactly parent-sized negative Krein energy. -/
theorem routePPrimitiveFourthDepthCoPoissonKreinPair_pivot_pivot
    (f : evenSubspace) :
    routePPrimitiveFourthDepthCoPoissonKreinPair
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f) =
      -((‖f‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair,
    routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot]
  dsimp only
  rw [@inner_smul_left ℂ evenSubspace _ _ _
    (routePPrimitiveFourthDepthCoPoissonContraction f)
    (((routeEPCubicFourthDepthJuliaDefect : ℂ) /
      (routeEPCubicFourthDepthNormalizedContraction : ℂ) ^ (2 : ℕ)) •
        routePPrimitiveFourthDepthCoPoissonContraction f)
    ((routeEPCubicFourthDepthJuliaDefect : ℂ) /
      (routeEPCubicFourthDepthNormalizedContraction : ℂ) ^ (2 : ℕ))]
  rw [@inner_smul_right ℂ evenSubspace _ _ _
    (routePPrimitiveFourthDepthCoPoissonContraction f)
    (routePPrimitiveFourthDepthCoPoissonContraction f)
    ((routeEPCubicFourthDepthJuliaDefect : ℂ) /
      (routeEPCubicFourthDepthNormalizedContraction : ℂ) ^ (2 : ℕ))]
  rw [@inner_smul_left ℂ evenSubspace _ _ _ f
    ((1 / (routeEPCubicFourthDepthNormalizedContraction : ℂ)) • f)
    (1 / (routeEPCubicFourthDepthNormalizedContraction : ℂ))]
  rw [@inner_smul_right ℂ evenSubspace _ _ _ f f
    (1 / (routeEPCubicFourthDepthNormalizedContraction : ℂ))]
  have hinnerU := inner_self_eq_norm_sq_to_K
    (𝕜 := ℂ) (routePPrimitiveFourthDepthCoPoissonContraction f)
  have hinnerf := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f
  rw [hinnerU, hinnerf, norm_routePPrimitiveFourthDepthCoPoissonContraction]
  simp only [map_div₀, map_pow, Complex.conj_ofReal, map_one]
  have hreal :
      (routeEPCubicFourthDepthJuliaDefect /
            routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ)) *
          (routeEPCubicFourthDepthJuliaDefect /
            routeEPCubicFourthDepthNormalizedContraction ^ (2 : ℕ)) *
          (routeEPCubicFourthDepthNormalizedContraction * ‖f‖) ^ (2 : ℕ) -
        (1 / routeEPCubicFourthDepthNormalizedContraction) *
          ((1 / routeEPCubicFourthDepthNormalizedContraction) * ‖f‖ ^ (2 : ℕ)) =
          -‖f‖ ^ (2 : ℕ) := by
    calc
      _ = ((routeEPCubicFourthDepthJuliaDefect /
              routeEPCubicFourthDepthNormalizedContraction) ^ (2 : ℕ) -
            (1 / routeEPCubicFourthDepthNormalizedContraction) ^ (2 : ℕ)) *
          ‖f‖ ^ (2 : ℕ) := by
            field_simp [routeEPCubicFourthDepthNormalizedContraction_ne_zero]
      _ = -‖f‖ ^ (2 : ℕ) := by
        rw [routeEPCubicFourthDepthJulia_lorentzCoefficient]
        ring
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
  push_cast at hcast
  convert hcast using 1
  · push_cast
    congr 1
    ac_rfl
  · push_cast
    ring

/-- Every nonzero co-Poisson pivot is a genuine negative direction. -/
theorem routePPrimitiveFourthDepthCoPoissonKreinPair_pivot_neg
    (f : evenSubspace) (hf : f ≠ 0) :
    (routePPrimitiveFourthDepthCoPoissonKreinPair
      (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)
      (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)).re < 0 := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair_pivot_pivot]
  change -‖(f : SoninL2)‖ ^ (2 : ℕ) < 0
  exact neg_lt_zero.mpr
    (sq_pos_of_pos (norm_pos_iff.mpr (Subtype.coe_ne_coe.mpr hf)))

/-- The realized two-channel block has determinant exactly `-||f||^(4 : ℕ)`. -/
theorem routePPrimitiveFourthDepthCoPoissonJuliaKreinBlock_det
    (f : evenSubspace) :
    (routePPrimitiveFourthDepthCoPoissonKreinPair
          (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)
          (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)).re *
        (routePPrimitiveFourthDepthCoPoissonKreinPair
          (routePPrimitiveFourthDepthCoPoissonKreinChild f)
          (routePPrimitiveFourthDepthCoPoissonKreinChild f)).re -
      (routePPrimitiveFourthDepthCoPoissonKreinPair
        (routePPrimitiveFourthDepthCoPoissonKreinChild f)
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)).re ^ (2 : ℕ) =
      -‖f‖ ^ (4 : ℕ) := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair_child_child,
    routePPrimitiveFourthDepthCoPoissonKreinPair_child_pivot_eq_quantized,
    routePPrimitiveFourthDepthCoPoissonKreinPair_pivot_pivot]
  change (-(‖(f : SoninL2)‖ ^ (2 : ℕ))) * (‖(f : SoninL2)‖ ^ (2 : ℕ) / 64) -
      routeEPCubicFourthDepthQuantizedPolarCross (‖(f : SoninL2)‖ ^ (2 : ℕ)) ^ (2 : ℕ) =
        -‖(f : SoninL2)‖ ^ (4 : ℕ)
  rw [routeEPCubicPolarBlockDet_quantized]
  ring

/-- Shorting the realized child through its realized Julia pivot restores full parent energy. -/
theorem routePPrimitiveFourthDepthCoPoissonJuliaKrein_shorting
    (f : evenSubspace) (hf : f ≠ 0) :
    routeEPCubicPolarPivotShortedFourthDepthEnergy (‖f‖ ^ (2 : ℕ))
        (routePPrimitiveFourthDepthCoPoissonKreinPair
          (routePPrimitiveFourthDepthCoPoissonKreinChild f)
          (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)).re =
      ‖f‖ ^ (2 : ℕ) := by
  rw [routePPrimitiveFourthDepthCoPoissonKreinPair_child_pivot_eq_quantized]
  norm_num
  exact routeEPCubicPolarPivotShortedFourthDepthEnergy_quantized _
    (sq_pos_of_pos (norm_pos_iff.mpr (Subtype.coe_ne_coe.mpr hf)))

/-- **P-G105B capstone.**  Every nonzero genuine co-Poisson source produces the complete
coefficient-faithful Julia--Krein shorting block inside the source ladder. -/
theorem routePPrimitiveFourthDepthCoPoisson_JuliaKreinPivot
    {b : ℝ} (hb : 0 < b) {f : evenSubspace}
    (hf : f ∈ burnolCoPoissonSourceSpace b) (hf0 : f ≠ 0) :
    (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f).1 ∈
        burnolCoPoissonSourceSpace ((4 : ℝ)⁻¹ * b) ∧
      (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f).2 ∈
        burnolCoPoissonSourceSpace b ∧
      routePPrimitiveFourthDepthCoPoissonKreinPair
          (routePPrimitiveFourthDepthCoPoissonKreinChild f)
          (routePPrimitiveFourthDepthCoPoissonKreinChild f) =
        ((‖f‖ ^ (2 : ℕ) / 64 : ℝ) : ℂ) ∧
      routePPrimitiveFourthDepthCoPoissonKreinPair
          (routePPrimitiveFourthDepthCoPoissonKreinChild f)
          (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f) =
        (routeEPCubicFourthDepthQuantizedPolarCross (‖f‖ ^ (2 : ℕ)) : ℂ) ∧
      routePPrimitiveFourthDepthCoPoissonKreinPair
          (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)
          (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f) =
        -((‖f‖ ^ (2 : ℕ) : ℝ) : ℂ) ∧
      (routePPrimitiveFourthDepthCoPoissonKreinPair
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)
        (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)).re < 0 ∧
      routeEPCubicPolarPivotShortedFourthDepthEnergy (‖f‖ ^ (2 : ℕ))
          (routePPrimitiveFourthDepthCoPoissonKreinPair
            (routePPrimitiveFourthDepthCoPoissonKreinChild f)
            (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot f)).re =
        ‖f‖ ^ (2 : ℕ) := by
  exact ⟨(routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot_mem_sourceSpaces hb hf).1,
    (routePPrimitiveFourthDepthCoPoissonJuliaKreinPivot_mem_sourceSpaces hb hf).2,
    routePPrimitiveFourthDepthCoPoissonKreinPair_child_child f,
    routePPrimitiveFourthDepthCoPoissonKreinPair_child_pivot_eq_quantized f,
    routePPrimitiveFourthDepthCoPoissonKreinPair_pivot_pivot f,
    routePPrimitiveFourthDepthCoPoissonKreinPair_pivot_neg f hf0,
    routePPrimitiveFourthDepthCoPoissonJuliaKrein_shorting f hf0⟩

end

end RHTower
