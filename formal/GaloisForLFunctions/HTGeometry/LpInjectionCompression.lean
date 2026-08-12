import GaloisForLFunctions.HTGeometry.RectangularVectorDiagonal

open scoped ENNReal

namespace RHTower

noncomputable section

variable {ι κ E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [InnerProductSpace ℂ E] in
/-- Coordinate pullback along an injection preserves square summability. -/
theorem lpCoordinatePullback_memℓp (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : κ => E) 2) :
    Memℓp (fun i => x (f i)) 2 := by
  refine memℓp_gen ?_
  exact ((lp.memℓp x).summable (by norm_num)).comp_injective hf

/-- Linear coordinate pullback along an injection. -/
def lpCoordinatePullbackLinear (f : ι → κ) (hf : Function.Injective f) :
    lp (fun _ : κ => E) 2 →ₗ[ℂ] lp (fun _ : ι => E) 2 where
  toFun x := ⟨fun i => x (f i), lpCoordinatePullback_memℓp f hf x⟩
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl

@[simp] theorem lpCoordinatePullbackLinear_apply
    (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : κ => E) 2) (i : ι) :
    lpCoordinatePullbackLinear f hf x i = x (f i) := rfl

theorem lpCoordinatePullbackLinear_norm_le
    (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : κ => E) 2) :
    ‖lpCoordinatePullbackLinear f hf x‖ ≤ ‖x‖ := by
  have hleft : 0 ≤ ‖lpCoordinatePullbackLinear f hf x‖ := norm_nonneg _
  have hright : 0 ≤ ‖x‖ := norm_nonneg _
  have hy : ‖lpCoordinatePullbackLinear f hf x‖ ^ (2 : ℝ) =
      ∑' i, ‖x (f i)‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => E)
      (by norm_num) (lpCoordinatePullbackLinear f hf x)
  have hx : ‖x‖ ^ (2 : ℝ) = ∑' k, ‖x k‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : κ => E)
      (by norm_num) x
  have hsumx : Summable fun k => ‖x k‖ ^ (2 : ℝ) :=
    (lp.memℓp x).summable (by norm_num)
  have hsumy : Summable fun i => ‖x (f i)‖ ^ (2 : ℝ) :=
    hsumx.comp_injective hf
  have htsum : (∑' i, ‖x (f i)‖ ^ (2 : ℝ)) ≤
      ∑' k, ‖x k‖ ^ (2 : ℝ) := by
    exact hsumy.tsum_le_tsum_of_inj f hf
      (fun k _hk => Real.rpow_nonneg (norm_nonneg _) 2)
      (fun i => le_rfl) hsumx
  have hpow : ‖lpCoordinatePullbackLinear f hf x‖ ^ (2 : ℝ) ≤
      ‖x‖ ^ (2 : ℝ) := by simpa [hy, hx] using htsum
  have hleft2 : ‖lpCoordinatePullbackLinear f hf x‖ ^ (2 : ℝ) =
      ‖lpCoordinatePullbackLinear f hf x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : ‖x‖ ^ (2 : ℝ) = ‖x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Bounded coordinate pullback along an injection, with norm at most one. -/
def lpCoordinatePullback (f : ι → κ) (hf : Function.Injective f) :
    lp (fun _ : κ => E) 2 →L[ℂ] lp (fun _ : ι => E) 2 :=
  LinearMap.mkContinuous (lpCoordinatePullbackLinear f hf) 1
    (fun x => by simpa using lpCoordinatePullbackLinear_norm_le f hf x)

@[simp] theorem lpCoordinatePullback_apply
    (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : κ => E) 2) (i : ι) :
    lpCoordinatePullback (E := E) f hf x i = x (f i) := rfl

variable [DecidableEq ι] [DecidableEq κ]

/-- Scalar coordinate vectors at the image of an injection. -/
def lpScalarInjectionBasis (f : ι → κ) (i : ι) :
    lp (fun _ : κ => ℂ) 2 := lp.single 2 (f i) 1

theorem lpScalarInjectionBasis_orthonormal
    (f : ι → κ) (hf : Function.Injective f) :
    Orthonormal ℂ (lpScalarInjectionBasis f) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lpScalarInjectionBasis, lpScalarInjectionBasis,
    lp.inner_single_left, lp.single_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hfij : f j ≠ f i := fun h => hij (hf h.symm)
    simp [hfij, hij]

/-- Canonical ℓ² isometry extending coordinates by zero along an injection. -/
def lpScalarInjection (f : ι → κ) (hf : Function.Injective f) :
    lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2 :=
  (lpScalarInjectionBasis_orthonormal f hf).orthogonalFamily.linearIsometry

@[simp] theorem lpScalarInjection_single
    (f : ι → κ) (hf : Function.Injective f) (i : ι) (c : ℂ) :
    lpScalarInjection f hf (lp.single 2 i c) = lp.single 2 (f i) c := by
  rw [lpScalarInjection, OrthogonalFamily.linearIsometry_apply_single]
  ext j
  by_cases hji : j = f i
  · subst j
    simp [lpScalarInjectionBasis]
  · simp [lpScalarInjectionBasis, hji]

theorem lpScalarInjection_coordinate
    (f : ι → κ) (hf : Function.Injective f)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpScalarInjection f hf x (f i) = x i := by
  let U := lpScalarInjection f hf
  have hsingle : U (lp.single 2 i 1) = lp.single 2 (f i) 1 := by
    exact lpScalarInjection_single f hf i 1
  calc
    U x (f i) = inner ℂ (lp.single 2 (f i) 1) (U x) := by
      rw [lp.inner_single_left]
      simp
    _ = inner ℂ (U (lp.single 2 i 1)) (U x) := by rw [hsingle]
    _ = inner ℂ (lp.single 2 i 1) x := U.inner_map_map _ x
    _ = x i := by rw [lp.inner_single_left]; simp

/-- On scalar ℓ², coordinate pullback is exactly the Hilbert adjoint of
zero-extension along the same injection. -/
theorem lpCoordinatePullback_eq_adjoint_lpScalarInjection
    (f : ι → κ) (hf : Function.Injective f) :
    lpCoordinatePullback (E := ℂ) f hf =
      (lpScalarInjection f hf).toContinuousLinearMap.adjoint := by
  apply ContinuousLinearMap.ext
  intro y
  apply lp.ext
  funext i
  have hadj := ContinuousLinearMap.adjoint_inner_right
    (lpScalarInjection f hf).toContinuousLinearMap
    (lp.single 2 i 1) y
  have hsingle :
      (lpScalarInjection f hf).toContinuousLinearMap (lp.single 2 i 1) =
        lp.single 2 (f i) 1 := lpScalarInjection_single f hf i 1
  rw [lp.inner_single_left, hsingle, lp.inner_single_left] at hadj
  rw [lpCoordinatePullback_apply]
  simpa using hadj.symm

end

end RHTower
