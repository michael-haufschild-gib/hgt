import GaloisForLFunctions.RHTower.RepPointPairLaplacian

/-!
# The coset representation of `SL(2,ℤ)` and the lift of `Γ`-invariant functions

For a finite-index subgroup `Γ ≤ SL(2,ℤ)` let `Q = SL(2,ℤ)/Γ` (left cosets) and `E = ℂ^Q` with the
Euclidean norm.

* `cosetRep Γ : SL(2,ℤ) →* (E ≃ₗᵢ[ℂ] E)` is the permutation representation
  `(ρ(B)v)(q) = v(B⁻¹q)` (`cosetRep_apply`). Its invariant vectors are constant, because the action on
  `Q` is transitive (`eq_of_forall_cosetRep_eq`).
* For `f : ℍ → ℂ` put `(F_f z)(q) = f(g_q⁻¹ z)` with `g_q` a representative of `q` (`cosetLift`).
  If `f` is `Γ`-invariant, then `(F_f z)(gΓ) = f(g⁻¹z)` for every representative (`cosetLift_mk`)
  and `F_f(Bz) = ρ(B) F_f(z)` (`cosetLift_equivariant`).
* Conversely, every `ρ`-equivariant `F : ℍ → E` is `F_f` for the `Γ`-invariant `f(z) = F(z)(Γ)`
  (`invariant_eval_one`, `eq_cosetLift_eval_one`).
* For real `C²` `f`, the lift is `C²` in the chart (`contDiffOn_cosetLift`) and the Laplace–Beltrami
  operator acts on it through `f`: `y²Δ F_f = F_{−Δ⁺ f}` (`hypLap_cosetLift`), where `Δ⁺` is the
  positive hyperbolic Laplacian.
-/

open UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.RepCoset

open GaloisForLFunctions.RHTower.DeckPointPair (hypLap)

noncomputable section

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- The cosets of a finite-index subgroup form a finite type. -/
noncomputable instance (priority := 100) fintypeCosets : Fintype (SL(2, ℤ) ⧸ Γ) :=
  Subgroup.fintypeQuotientOfFiniteIndex

theorem piLpCongrLeft_toPerm_apply (B : SL(2, ℤ)) (v : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ))
    (q : SL(2, ℤ) ⧸ Γ) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (MulAction.toPerm B) v q = v (B⁻¹ • q) := by
  show (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (MulAction.toPerm B) v).ofLp q = v.ofLp (B⁻¹ • q)
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  rfl

/-- **The coset (permutation) representation** `(ρ(B)v)(q) = v(B⁻¹q)`. -/
def cosetRep : SL(2, ℤ) →*
    (EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)) where
  toFun B := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (MulAction.toPerm B)
  map_one' := by
    refine LinearIsometryEquiv.ext fun v => PiLp.ext fun q => ?_
    rw [piLpCongrLeft_toPerm_apply, inv_one, one_smul]
    rfl
  map_mul' B₁ B₂ := by
    refine LinearIsometryEquiv.ext fun v => PiLp.ext fun q => ?_
    rw [piLpCongrLeft_toPerm_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      piLpCongrLeft_toPerm_apply, piLpCongrLeft_toPerm_apply, mul_inv_rev, mul_smul]

theorem cosetRep_apply (B : SL(2, ℤ)) (v : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)) (q : SL(2, ℤ) ⧸ Γ) :
    cosetRep Γ B v q = v (B⁻¹ • q) :=
  piLpCongrLeft_toPerm_apply Γ B v q

/-- **Invariant vectors are constant**: the action of `SL(2,ℤ)` on its cosets is transitive. -/
theorem eq_of_forall_cosetRep_eq {v : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)}
    (hv : ∀ B, cosetRep Γ B v = v) (q q' : SL(2, ℤ) ⧸ Γ) : v q = v q' := by
  obtain ⟨B, hB⟩ := MulAction.exists_smul_eq SL(2, ℤ) q q'
  have h := congrArg (fun w : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) => w q') (hv B)
  simp only [cosetRep_apply] at h
  rw [← hB, inv_smul_smul] at h
  rw [← hB, h]

variable {Γ}

/-- **The lift** `(F_f z)(q) = f(g_q⁻¹ z)`, `g_q` the chosen representative of `q`. -/
def cosetLift (f : ℍ → ℂ) (z : ℍ) : EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ) :=
  WithLp.toLp 2 fun q => f ((Quotient.out q)⁻¹ • z)

omit [Γ.FiniteIndex] in
theorem cosetLift_apply (f : ℍ → ℂ) (z : ℍ) (q : SL(2, ℤ) ⧸ Γ) :
    cosetLift f z q = f ((Quotient.out q)⁻¹ • z) := rfl

omit [Γ.FiniteIndex] in
/-- For `Γ`-invariant `f`, every representative computes the lift: `(F_f z)(gΓ) = f(g⁻¹z)`. -/
theorem cosetLift_mk {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ, ∀ z, f (γ • z) = f z) (z : ℍ) (g : SL(2, ℤ)) :
    cosetLift f z (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) = f (g⁻¹ • z) := by
  rw [cosetLift_apply]
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ g
  have e : Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) = g * γ := hγ
  rw [e, mul_inv_rev, mul_smul]
  exact hf _ (Γ.inv_mem γ.2) _

/-- **Equivariance of the lift**: `F_f(Bz) = ρ(B) F_f(z)` for `Γ`-invariant `f`. -/
theorem cosetLift_equivariant {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ, ∀ z, f (γ • z) = f z) (B : SL(2, ℤ))
    (z : ℍ) : cosetLift f (B • z) = cosetRep Γ B (cosetLift f z) := by
  refine PiLp.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetRep_apply, MulAction.Quotient.smul_mk, smul_eq_mul, cosetLift_mk hf, cosetLift_mk hf, mul_inv_rev,
      inv_inv, mul_smul]

theorem isEquivariant_cosetLift {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ, ∀ z, f (γ • z) = f z) :
    RepPointPair.IsEquivariant (cosetRep Γ) (cosetLift f) :=
  fun B z => cosetLift_equivariant hf B z

/-- **Converse, invariance**: for `ρ`-equivariant `F`, `z ↦ F(z)(Γ)` is `Γ`-invariant. -/
theorem invariant_eval_one {F : ℍ → EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)}
    (hF : RepPointPair.IsEquivariant (cosetRep Γ) F) :
    ∀ γ ∈ Γ, ∀ z, F (γ • z) (QuotientGroup.mk 1) = F z (QuotientGroup.mk 1) := by
  intro γ hγ z
  have hq : (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Γ) = QuotientGroup.mk 1 :=
    QuotientGroup.eq.2 (by rw [inv_inv, mul_one]; exact hγ)
  rw [hF γ z, cosetRep_apply, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hq]

/-- **Converse, representation**: every `ρ`-equivariant `F` is the lift of `z ↦ F(z)(Γ)`. -/
theorem eq_cosetLift_eval_one {F : ℍ → EuclideanSpace ℂ (SL(2, ℤ) ⧸ Γ)}
    (hF : RepPointPair.IsEquivariant (cosetRep Γ) F) :
    F = cosetLift fun z => F z (QuotientGroup.mk 1) := by
  funext z
  refine PiLp.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetLift_mk (invariant_eval_one hF), hF, cosetRep_apply, inv_inv,
      MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- **Chart regularity of the lift**: each coordinate is a Möbius pullback of `f`. -/
theorem contDiffOn_cosetLift {f : ℍ → ℂ} (hf : IsRealSmoothUpperHalfPlane f) :
    ContDiffOn ℝ 2 (fun ζ => cosetLift (Γ := Γ) f (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} := by
  rw [contDiffOn_piLp]
  intro q
  exact SelbergMaassCuspTransport.smooth_pullback (Quotient.out q)⁻¹ f hf

/-- **The Laplacian acts through the lift**: `y²Δ F_f = F_{−Δ⁺ f}` for real `C²` `f`. -/
theorem hypLap_cosetLift {f : ℍ → ℂ} (hf : IsRealSmoothUpperHalfPlane f) :
    hypLap (cosetLift (Γ := Γ) f) = cosetLift fun z => -positiveHyperbolicLaplacian f z := by
  funext w
  refine PiLp.ext fun q => ?_
  rw [RepPointPair.hypLap_apply (contDiffOn_cosetLift hf) w q, cosetLift_apply]
  congr 1
  exact SelbergMaassCuspTransport.positive_laplacian_pullback (Quotient.out q)⁻¹ f hf w

end

end GaloisForLFunctions.RHTower.RepCoset
