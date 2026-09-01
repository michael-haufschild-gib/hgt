import GaloisForLFunctions.HTGeometry.AlgebraSpectrumTopology
import GaloisForLFunctions.HTGeometry.ComplexPolynomialComplementPathConnected

/-!
# Complex points of a principal localization of a complex polynomial ring

For a nonzero `G : MvPolynomial ι ℂ`, the complex points of `Localization.Away G` are exactly the
tuples `v : ι → ℂ` with `eval v G ≠ 0`: evaluation extends uniquely across the localization, the
extension is continuous for pointwise convergence because a fixed localized element is a fixed
quotient of two polynomial evaluations with nowhere-vanishing denominator, and every complex point
arises this way because the inverted polynomial must take a unit value.

Together with `ComplexPolynomialComplementPathConnected` this proves that the complex-point space
of every principal open of a complex affine space is **path connected**, which is the global
connectivity input consumed by the block/étale covering argument on the critical horizon.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

namespace AlgSpec

variable {ι : Type*} (G : MvPolynomial ι ℂ)

theorem continuous_mvPolynomial_eval (p : MvPolynomial ι ℂ) :
    Continuous fun v : ι → ℂ => MvPolynomial.eval v p := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (continuous_const : Continuous fun _ : ι → ℂ => c)
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul (continuous_apply i)

/-- Evaluation of the polynomial ring at a complex point. -/
def awayAeval (v : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval v

theorem awayAeval_apply (v : ι → ℂ) (p : MvPolynomial ι ℂ) :
    awayAeval v p = MvPolynomial.eval v p := by
  simp [awayAeval, MvPolynomial.aeval_eq_eval]

theorem awayAeval_isUnit_powers {v : ι → ℂ} (hv : MvPolynomial.eval v G ≠ 0)
    (y : Submonoid.powers G) : IsUnit (awayAeval v (y : MvPolynomial ι ℂ)) := by
  obtain ⟨k, hk⟩ := y.property
  rw [← hk, map_pow]
  exact (IsUnit.pow k (by simpa [awayAeval_apply] using isUnit_iff_ne_zero.2 hv))

/-- The complex point of the principal localization determined by a nonvanishing point. -/
def awayAlgPoint {v : ι → ℂ} (hv : MvPolynomial.eval v G ≠ 0) :
    AlgSpec (Localization.Away G) :=
  AlgHom.mk (IsLocalization.lift (awayAeval_isUnit_powers G hv)) fun c => by
    change IsLocalization.lift (awayAeval_isUnit_powers G hv)
        (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (C c)) = c
    rw [IsLocalization.lift_eq]
    simp [awayAeval]

theorem awayAlgPoint_algebraMap {v : ι → ℂ} (hv : MvPolynomial.eval v G ≠ 0)
    (p : MvPolynomial ι ℂ) :
    awayAlgPoint G hv (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) p) =
      MvPolynomial.eval v p := by
  change IsLocalization.lift (awayAeval_isUnit_powers G hv)
      (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) p) = _
  rw [IsLocalization.lift_eq]
  exact awayAeval_apply v p

/-- On the image of the polynomial ring, every complex point of the localization is evaluation at
the tuple of coordinate values. -/
theorem apply_algebraMap_eq_eval (chi : AlgSpec (Localization.Away G))
    (p : MvPolynomial ι ℂ) :
    chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) p) =
      MvPolynomial.eval
        (fun i => chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))) p := by
  have h : (chi : Localization.Away G →ₐ[ℂ] ℂ).comp
      (IsScalarTower.toAlgHom ℂ (MvPolynomial ι ℂ) (Localization.Away G)) =
      MvPolynomial.aeval
        (fun i => chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  calc chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) p)
      = ((chi : Localization.Away G →ₐ[ℂ] ℂ).comp
          (IsScalarTower.toAlgHom ℂ (MvPolynomial ι ℂ) (Localization.Away G))) p := rfl
    _ = MvPolynomial.aeval
          (fun i => chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))) p := by
        rw [h]
    _ = MvPolynomial.eval
          (fun i => chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))) p := by
        simp [MvPolynomial.aeval_eq_eval]

theorem isUnit_algebraMap_away :
    IsUnit (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) G) :=
  IsLocalization.map_units (M := Submonoid.powers G) (Localization.Away G)
    (⟨G, ⟨1, pow_one G⟩⟩ : Submonoid.powers G)

theorem eval_ne_zero_of_algSpec (chi : AlgSpec (Localization.Away G)) :
    MvPolynomial.eval
      (fun i => chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))) G ≠ 0 := by
  rw [← apply_algebraMap_eq_eval]
  exact ((isUnit_algebraMap_away G).map (chi : Localization.Away G →ₐ[ℂ] ℂ)).ne_zero

theorem awayAlgPoint_surjective :
    Function.Surjective
      (fun v : {v : ι → ℂ // MvPolynomial.eval v G ≠ 0} => awayAlgPoint G v.2) := by
  intro chi
  have hv : MvPolynomial.eval
      (fun i => chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))) G ≠ 0 :=
    eval_ne_zero_of_algSpec G chi
  refine ⟨⟨_, hv⟩, ?_⟩
  show awayAlgPoint G hv = chi
  apply IsLocalization.algHom_ext (Submonoid.powers G)
  apply MvPolynomial.algHom_ext
  intro i
  show awayAlgPoint G hv (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i)) =
    chi (algebraMap (MvPolynomial ι ℂ) (Localization.Away G) (X i))
  rw [awayAlgPoint_algebraMap, MvPolynomial.eval_X]

theorem continuous_awayAlgPoint :
    Continuous fun v : {v : ι → ℂ // MvPolynomial.eval v G ≠ 0} => awayAlgPoint G v.2 := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  set s := IsLocalization.sec (Submonoid.powers G) b with hs
  have hden : Continuous fun v : {v : ι → ℂ // MvPolynomial.eval v G ≠ 0} =>
      MvPolynomial.eval (v : ι → ℂ) (s.2 : MvPolynomial ι ℂ) :=
    (continuous_mvPolynomial_eval _).comp continuous_subtype_val
  have hnum : Continuous fun v : {v : ι → ℂ // MvPolynomial.eval v G ≠ 0} =>
      MvPolynomial.eval (v : ι → ℂ) s.1 :=
    (continuous_mvPolynomial_eval _).comp continuous_subtype_val
  have hden_ne : ∀ v : {v : ι → ℂ // MvPolynomial.eval v G ≠ 0},
      MvPolynomial.eval (v : ι → ℂ) (s.2 : MvPolynomial ι ℂ) ≠ 0 := by
    intro v
    have h := awayAeval_isUnit_powers G v.2 s.2
    rw [awayAeval_apply] at h
    exact h.ne_zero
  have hvalue : ∀ v : {v : ι → ℂ // MvPolynomial.eval v G ≠ 0},
      awayAlgPoint G v.2 b =
        MvPolynomial.eval (v : ι → ℂ) s.1 /
          MvPolynomial.eval (v : ι → ℂ) (s.2 : MvPolynomial ι ℂ) := by
    intro v
    apply (eq_div_iff (hden_ne v)).2
    have h := congrArg (fun z => awayAlgPoint G v.2 z)
      (IsLocalization.sec_spec (Submonoid.powers G) b)
    simp only [map_mul] at h
    rw [awayAlgPoint_algebraMap, awayAlgPoint_algebraMap] at h
    exact h
  convert hnum.div₀ hden hden_ne using 1
  funext v
  exact hvalue v


/-- A continuous surjection out of a path-connected space has path-connected target. -/
theorem pathConnectedSpace_of_continuous_surjective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PathConnectedSpace X] {f : X → Y} (hf : Continuous f)
    (hsurj : Function.Surjective f) : PathConnectedSpace Y := by
  have hne : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
  refine ⟨hne, ?_⟩
  intro y z
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨w, rfl⟩ := hsurj z
  exact ⟨(PathConnectedSpace.somePath x w).map hf⟩

/-- **The complex points of a principal localization of a complex polynomial ring are path
connected.** -/
theorem pathConnectedSpace_algSpec_localizationAway (hG : G ≠ 0) :
    PathConnectedSpace (AlgSpec (Localization.Away G)) := by
  obtain ⟨v₀, hv₀⟩ : ∃ v : ι → ℂ, MvPolynomial.eval v G ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hG (MvPolynomial.funext (fun x => by simp [hcon x]))
  have hpc : IsPathConnected {v : ι → ℂ | MvPolynomial.eval v G ≠ 0} :=
    isPathConnected_complexMvPolynomial_nonzeroLocus G hv₀
  letI : PathConnectedSpace {v : ι → ℂ // MvPolynomial.eval v G ≠ 0} :=
    isPathConnected_iff_pathConnectedSpace.1 hpc
  exact pathConnectedSpace_of_continuous_surjective (continuous_awayAlgPoint G)
    (awayAlgPoint_surjective G)

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
