import GaloisForLFunctions.HTGeometry.ScaleMautnerFormation
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport

/-!
# The Stone generator of a scale-covariant unitary flow

For a strongly continuous unitary group `V_t = e^{itA}` the generator `A` is the partially defined
operator `A x = -i (d/dt)|_{t=0} V_t x` on the vectors with differentiable orbit.

* A transport `W_t T = T V_{ct}` between unitary flows intertwines the generators with transported
  domains: `B T = c T A` (`scaleIntertwining_flowGenerator`).  In particular the exact scale law
  `U V_t U⁻¹ = V_{qt}` gives **(SM.4)** `U A U⁻¹ = qA` as an identity of partially defined
  operators.
* A scale intertwining scales the spectrum: `σ(B) = c σ(A)` (**(SM.6)**, **(SM.12)**).
* The generator is symmetric, and a compact-resolvent clock diagonalizes it.  **Theorem 3.1** holds
  at the level of generators: `U A U⁻¹ = qA` with compact resolvent forces `A = 0` and
  `dim H < ∞`.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## The generator -/

/-- Vectors whose orbit `t ↦ V_t x` is differentiable at `0`. -/
def generatorDomain (V : UnitaryFlow ℂ H) : Submodule ℂ H where
  carrier := {x | DifferentiableAt ℝ (fun t => V.op t x) 0}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_add]
    exact hx.add hy
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact differentiableAt_const 0
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, LinearIsometryEquiv.map_smul]
    exact hx.const_smul c

/-- The **Stone generator** `A` of `V_t = e^{itA}`: `A x = -i (d/dt)|_{t=0} V_t x`, defined exactly
on the vectors with differentiable orbit. -/
def flowGenerator (V : UnitaryFlow ℂ H) : H →ₗ.[ℂ] H where
  domain := generatorDomain V
  toFun :=
    { toFun := fun x => -Complex.I • deriv (fun t => V.op t (x : H)) 0
      map_add' := fun x y => by
        have hx : DifferentiableAt ℝ (fun t => V.op t (x : H)) 0 := x.2
        have hy : DifferentiableAt ℝ (fun t => V.op t (y : H)) 0 := y.2
        simp only [Submodule.coe_add, map_add]
        rw [show (fun t => V.op t (x : H) + V.op t (y : H)) =
          (fun t => V.op t (x : H)) + (fun t => V.op t (y : H)) from rfl, deriv_add hx hy, smul_add]
      map_smul' := fun c x => by
        have hx : DifferentiableAt ℝ (fun t => V.op t (x : H)) 0 := x.2
        simp only [Submodule.coe_smul, LinearIsometryEquiv.map_smul, RingHom.id_apply]
        rw [show (fun t => c • V.op t (x : H)) = c • (fun t => V.op t (x : H)) from rfl,
          deriv_const_smul c hx, smul_comm] }

theorem mem_flowGenerator_domain {V : UnitaryFlow ℂ H} {x : H} :
    x ∈ (flowGenerator V).domain ↔ DifferentiableAt ℝ (fun t => V.op t x) 0 := Iff.rfl

/-- The orbit of a domain vector has derivative `i A x` at `0`. -/
theorem hasDerivAt_flowGenerator (V : UnitaryFlow ℂ H) (x : (flowGenerator V).domain) :
    HasDerivAt (fun t => V.op t (x : H)) (Complex.I • flowGenerator V x) 0 := by
  have hx : DifferentiableAt ℝ (fun t => V.op t (x : H)) 0 := x.2
  have h : Complex.I • flowGenerator V x = deriv (fun t => V.op t (x : H)) 0 := by
    change Complex.I • (-Complex.I • deriv (fun t => V.op t (x : H)) 0) = _
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  rw [h]
  exact hx.hasDerivAt

/-- A derivative `i y` of the orbit at `0` puts `x` in the domain with `A x = y`. -/
theorem flowGenerator_of_hasDerivAt {V : UnitaryFlow ℂ H} {x y : H}
    (h : HasDerivAt (fun t => V.op t x) (Complex.I • y) 0) :
    ∃ hx : x ∈ (flowGenerator V).domain, flowGenerator V ⟨x, hx⟩ = y := by
  refine ⟨h.differentiableAt, ?_⟩
  change -Complex.I • deriv (fun t => V.op t x) 0 = y
  rw [h.deriv, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

/-- **The generator is symmetric**: differentiate `⟪V_t x, y⟫ = ⟪x, V_{-t} y⟫` at `0`. -/
theorem flowGenerator_symmetric (V : UnitaryFlow ℂ H) (x y : (flowGenerator V).domain) :
    ⟪flowGenerator V x, (y : H)⟫_ℂ = ⟪(x : H), flowGenerator V y⟫_ℂ := by
  have hl := (hasDerivAt_flowGenerator V x).inner ℂ (hasDerivAt_const (0 : ℝ) (y : H))
  have hneg : HasDerivAt (fun t : ℝ => V.op (-t) (y : H)) ((-1 : ℝ) • Complex.I • flowGenerator V y) 0 :=
    HasDerivAt.scomp_of_eq 0 (hasDerivAt_flowGenerator V y) (hasDerivAt_neg 0) neg_zero.symm
  have hr := (hasDerivAt_const (0 : ℝ) (x : H)).inner ℂ hneg
  have heq : (fun t : ℝ => ⟪V.op t (x : H), (y : H)⟫_ℂ) = fun t => ⟪(x : H), V.op (-t) (y : H)⟫_ℂ :=
    funext fun t => inner_op_left V t x y
  rw [heq] at hl
  have h := hl.unique hr
  simp only [inner_zero_right, inner_zero_left, zero_add, add_zero, inner_smul_left, inner_smul_right,
    Complex.conj_I, neg_smul, one_smul, inner_neg_right] at h
  have h' : -Complex.I * (⟪flowGenerator V x, (y : H)⟫_ℂ - ⟪(x : H), flowGenerator V y⟫_ℂ) = 0 := by
    rw [mul_sub]
    rw [neg_mul, neg_mul] at *
    linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (neg_eq_zero.1 h0) Complex.I_ne_zero
  · exact sub_eq_zero.1 h0

/-- A trivial flow has generator `0` on the whole space. -/
theorem flowGenerator_of_trivial {V : UnitaryFlow ℂ H} (hV : ∀ t x, V.op t x = x) :
    (flowGenerator V).domain = ⊤ ∧ ∀ x : (flowGenerator V).domain, flowGenerator V x = 0 := by
  have hd : ∀ x : H, HasDerivAt (fun t => V.op t x) (Complex.I • (0 : H)) 0 := fun x => by
    simp only [hV, smul_zero]
    exact hasDerivAt_const 0 x
  refine ⟨eq_top_iff.2 fun x _ => (flowGenerator_of_hasDerivAt (hd x)).1, fun x => ?_⟩
  obtain ⟨_, h⟩ := flowGenerator_of_hasDerivAt (hd x)
  exact h

/-! ## Scale intertwining of partially defined operators -/

/-- `B T = c T A` with transported domains: `x ∈ dom A ↔ Tx ∈ dom B` and `B(Tx) = c T(Ax)`. -/
structure ScaleIntertwining (T : H ≃ₗᵢ[ℂ] K) (A : H →ₗ.[ℂ] H) (B : K →ₗ.[ℂ] K) (c : ℂ) : Prop where
  domain_iff : ∀ x, x ∈ A.domain ↔ T x ∈ B.domain
  apply_eq : ∀ x : A.domain, B ⟨T x, (domain_iff x).1 x.2⟩ = c • T (A x)

namespace ScaleIntertwining

variable {T : H ≃ₗᵢ[ℂ] K} {A : H →ₗ.[ℂ] H} {B : K →ₗ.[ℂ] K} {c : ℂ}

theorem apply_mk (h : ScaleIntertwining T A B c) {x : H} (hx : x ∈ A.domain) (hTx : T x ∈ B.domain) :
    B ⟨T x, hTx⟩ = c • T (A ⟨x, hx⟩) :=
  h.apply_eq ⟨x, hx⟩

/-- The inverse transport intertwines back with the inverse factor. -/
theorem symm (h : ScaleIntertwining T A B c) (hc : c ≠ 0) : ScaleIntertwining T.symm B A c⁻¹ where
  domain_iff y := by rw [h.domain_iff, LinearIsometryEquiv.apply_symm_apply]
  apply_eq y := by
    have hy : T (T.symm y) ∈ B.domain := by rw [LinearIsometryEquiv.apply_symm_apply]; exact y.2
    have hx : T.symm y ∈ A.domain := (h.domain_iff _).2 hy
    have h1 := h.apply_mk hx hy
    have h2 : B ⟨T (T.symm y), hy⟩ = B y := congrArg B (Subtype.ext (T.apply_symm_apply y))
    rw [h2] at h1
    rw [h1, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ hc, one_smul]

/-- Composition of transports multiplies the factors. -/
theorem trans {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] {T' : K ≃ₗᵢ[ℂ] L}
    {C : L →ₗ.[ℂ] L} {d : ℂ} (h : ScaleIntertwining T A B c) (h' : ScaleIntertwining T' B C d) :
    ScaleIntertwining (T.trans T') A C (d * c) where
  domain_iff x := by rw [h.domain_iff, h'.domain_iff]; rfl
  apply_eq x := by
    have hx : T x ∈ B.domain := (h.domain_iff x).1 x.2
    have h1 := h'.apply_mk hx ((h'.domain_iff _).1 hx)
    change C ⟨T' (T x), _⟩ = _
    rw [h1, h.apply_eq x, LinearIsometryEquiv.map_smul, smul_smul]
    rfl

/-- Rescaling both operators: `(bB) T = (bc/a) T (aA)`. -/
theorem smul (h : ScaleIntertwining T A B c) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ScaleIntertwining T (a • A) (b • B) (b * c / a) where
  domain_iff x := h.domain_iff x
  apply_eq x := by
    rw [LinearPMap.smul_apply, LinearPMap.smul_apply, LinearIsometryEquiv.map_smul, smul_smul]
    have h1 := h.apply_mk (x := (x : H)) x.2 ((h.domain_iff x).1 x.2)
    change b • B ⟨T x, _⟩ = _
    rw [h1, smul_smul]
    congr 1
    field_simp

/-- **The intertwining as an identity of partially defined operators**: `T⁻¹ B T = c A`. -/
theorem unitaryConjugate_eq (h : ScaleIntertwining T A B c) :
    unitaryConjugateLinearPMap T B = c • A := by
  refine LinearPMap.ext ?_ ?_
  · ext x
    rw [unitaryConjugateLinearPMap_domain, LinearPMap.smul_domain, Submodule.mem_comap]
    exact (h.domain_iff x).symm
  · intro x hx hy
    rw [unitaryConjugateLinearPMap_apply, LinearPMap.smul_apply]
    have hyA : x ∈ A.domain := hy
    change T.symm (B ⟨T x, (h.domain_iff x).1 hyA⟩) = c • A ⟨x, hyA⟩
    rw [h.apply_mk hyA, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.symm_apply_apply]

end ScaleIntertwining

/-! ## Spectrum of a partially defined operator -/

/-- `z` lies in the resolvent set of `A`: `A - z` has a bounded two-sided inverse
`R : H → dom A`. -/
def IsPMapResolvent (A : H →ₗ.[ℂ] H) (z : ℂ) : Prop :=
  ∃ R : H →L[ℂ] H, ∃ hR : ∀ y, R y ∈ A.domain,
    (∀ y, A ⟨R y, hR y⟩ - z • R y = y) ∧ ∀ x : A.domain, R (A x - z • (x : H)) = x

/-- The spectrum of a partially defined operator. -/
def pmapSpectrum (A : H →ₗ.[ℂ] H) : Set ℂ := {z | ¬ IsPMapResolvent A z}

namespace ScaleIntertwining

variable {T : H ≃ₗᵢ[ℂ] K} {A : H →ₗ.[ℂ] H} {B : K →ₗ.[ℂ] K} {c : ℂ}

/-- A resolvent of `A` at `z` transports to the resolvent `c⁻¹ T R T⁻¹` of `B` at `cz`. -/
theorem isPMapResolvent (h : ScaleIntertwining T A B c) (hc : c ≠ 0) {z : ℂ}
    (hz : IsPMapResolvent A z) : IsPMapResolvent B (c * z) := by
  obtain ⟨R, hR, hright, hleft⟩ := hz
  let Tc : H →L[ℂ] K := T.toContinuousLinearEquiv.toContinuousLinearMap
  let Ti : K →L[ℂ] H := T.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hRB : ∀ y, (c⁻¹ • (Tc ∘L R ∘L Ti)) y = c⁻¹ • T (R (T.symm y)) := fun y => rfl
  have hmem : ∀ y, T (R (T.symm y)) ∈ B.domain := fun y => (h.domain_iff _).1 (hR _)
  refine ⟨c⁻¹ • (Tc ∘L R ∘L Ti), fun y => ?_, fun y => ?_, fun x => ?_⟩
  · rw [hRB]
    exact B.domain.smul_mem _ (hmem y)
  · have e1 : (⟨(c⁻¹ • (Tc ∘L R ∘L Ti)) y, by rw [hRB]; exact B.domain.smul_mem _ (hmem y)⟩ :
        B.domain) = c⁻¹ • ⟨T (R (T.symm y)), hmem y⟩ := Subtype.ext (hRB y)
    rw [e1, LinearPMap.map_smul, h.apply_mk (hR _) (hmem y), hRB, smul_smul, inv_mul_cancel₀ hc,
      one_smul, smul_smul, mul_comm c z, mul_assoc, mul_inv_cancel₀ hc, mul_one,
      ← LinearIsometryEquiv.map_smul, ← map_sub, hright, LinearIsometryEquiv.apply_symm_apply]
  · have hx0 : T (T.symm (x : K)) ∈ B.domain := by
      rw [LinearIsometryEquiv.apply_symm_apply]; exact x.2
    have hxA : T.symm (x : K) ∈ A.domain := (h.domain_iff _).2 hx0
    have h1 : B x = c • T (A ⟨T.symm x, hxA⟩) := by
      rw [← h.apply_mk hxA hx0]
      exact congrArg B (Subtype.ext (T.apply_symm_apply x).symm)
    rw [hRB, h1]
    have h2 : T.symm (c • T (A ⟨T.symm x, hxA⟩) - (c * z) • (x : K)) =
        c • (A ⟨T.symm x, hxA⟩ - z • ((⟨T.symm x, hxA⟩ : A.domain) : H)) := by
      rw [map_sub, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.map_smul, smul_sub, smul_smul]
    rw [h2, map_smul, hleft, LinearIsometryEquiv.map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact T.apply_symm_apply x

/-- **Spectral scaling (SM.6), (SM.12).**  `σ(B) = c σ(A)`. -/
theorem pmapSpectrum_eq (h : ScaleIntertwining T A B c) (hc : c ≠ 0) :
    pmapSpectrum B = (fun z => c * z) '' pmapSpectrum A := by
  ext z
  simp only [pmapSpectrum, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hz
    refine ⟨c⁻¹ * z, fun hA => hz ?_, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
    have := h.isPMapResolvent hc hA
    rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at this
  · rintro ⟨w, hw, rfl⟩ hB
    apply hw
    have := (h.symm hc).isPMapResolvent (inv_ne_zero hc) hB
    rwa [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at this

end ScaleIntertwining

/-! ## Transport of generators -/

/-- A transport `W_t T = T V_{ct}` carries the generator domain into the generator domain with
`B(Tx) = c T(Ax)`: differentiate `t ↦ T V_{ct} x` at `0`. -/
theorem flowGenerator_transport {V : UnitaryFlow ℂ H} {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) (c : ℝ)
    (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (x : (flowGenerator V).domain) :
    ∃ hTx : T x ∈ (flowGenerator W).domain,
      flowGenerator W ⟨T x, hTx⟩ = (c : ℂ) • T (flowGenerator V x) := by
  apply flowGenerator_of_hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => V.op (c * t) (x : H)) (c • Complex.I • flowGenerator V x) 0 :=
    HasDerivAt.scomp_of_eq 0 (hasDerivAt_flowGenerator V x)
      ((hasDerivAt_id (0 : ℝ)).const_mul c |>.congr_deriv (mul_one c)) (mul_zero c).symm
  have h2 := (((T.toContinuousLinearEquiv : H →L[ℂ] K).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    (0 : ℝ) h1
  have heq : (fun t => W.op t (T x)) =
      (fun v : H => ((T.toContinuousLinearEquiv : H →L[ℂ] K).restrictScalars ℝ) v) ∘
        fun t : ℝ => V.op (c * t) (x : H) := funext fun t => hT t x
  rw [heq]
  convert h2 using 1
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_smul]
  rw [smul_comm, Complex.coe_smul]

/-- **Generators intertwine under a flow transport.**  If `W_t T = T V_{ct}` with `c ≠ 0`, then
`B T = c T A` with transported domains. -/
theorem scaleIntertwining_flowGenerator {V : UnitaryFlow ℂ H} {W : UnitaryFlow ℂ K}
    (T : H ≃ₗᵢ[ℂ] K) {c : ℝ} (hc : c ≠ 0) (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) :
    ScaleIntertwining T (flowGenerator V) (flowGenerator W) c where
  domain_iff x := by
    refine ⟨fun hx => (flowGenerator_transport T c hT ⟨x, hx⟩).1, fun hTx => ?_⟩
    have hT' : ∀ t y, V.op t (T.symm y) = T.symm (W.op (c⁻¹ * t) y) := by
      intro t y
      conv_rhs => rw [← T.apply_symm_apply y]
      rw [hT, mul_inv_cancel_left₀ hc, LinearIsometryEquiv.symm_apply_apply]
    obtain ⟨h, _⟩ := flowGenerator_transport T.symm c⁻¹ hT' ⟨T x, hTx⟩
    simpa using h
  apply_eq x := (flowGenerator_transport T c hT x).2

/-- **(SM.4)** The exact scale law at the level of generators: `U A U⁻¹ = qA`, domains included. -/
theorem IsScaleLaw.scaleIntertwining {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : q ≠ 0)
    (hS : IsScaleLaw U V q) : ScaleIntertwining U.symm (flowGenerator V) (flowGenerator V) q :=
  scaleIntertwining_flowGenerator U.symm hq fun t x => by rw [← hS t x, U.symm_apply_apply]

/-- **(SM.4)** as an identity of partially defined operators. -/
theorem IsScaleLaw.unitaryConjugate_flowGenerator {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ}
    (hq : q ≠ 0) (hS : IsScaleLaw U V q) :
    unitaryConjugateLinearPMap U.symm (flowGenerator V) = (q : ℂ) • flowGenerator V :=
  (hS.scaleIntertwining hq).unitaryConjugate_eq

/-- **(SM.6)** `σ(A) = q σ(A)` under the exact scale law. -/
theorem IsScaleLaw.pmapSpectrum_eq {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : q ≠ 0)
    (hS : IsScaleLaw U V q) :
    pmapSpectrum (flowGenerator V) = (fun z => (q : ℂ) * z) '' pmapSpectrum (flowGenerator V) :=
  (hS.scaleIntertwining hq).pmapSpectrum_eq (by exact_mod_cast hq)

/-! ## Theorem 3.1 at the level of generators -/

namespace CompactResolventClock

variable {V : UnitaryFlow ℂ H} {κ : Type*} (C : CompactResolventClock V κ)

/-- The clock basis lies in the generator domain and diagonalizes the generator. -/
theorem flowGenerator_basis (k : κ) :
    ∃ hk : C.basis k ∈ (flowGenerator V).domain,
      flowGenerator V ⟨C.basis k, hk⟩ = (C.freq k : ℂ) • C.basis k := by
  apply flowGenerator_of_hasDerivAt
  have h0 : HasDerivAt (fun t : ℝ => Complex.I * ((C.freq k : ℂ) * (t : ℂ)))
      (Complex.I * ((C.freq k : ℂ) * ((1 : ℝ) : ℂ))) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul _).const_mul _
  have hc : HasDerivAt (fun t : ℝ => flowCharacter (C.freq k) t) (Complex.I * C.freq k) 0 := by
    have := h0.cexp
    simpa [flowCharacter] using this
  have heq : (fun t => V.op t (C.basis k)) = fun t => flowCharacter (C.freq k) t • C.basis k :=
    funext fun t => C.eigen k t
  rw [heq, smul_smul]
  exact hc.smul_const (C.basis k)

/-- A generator eigenvector of eigenvalue `μ` has no component along clock vectors of other
frequencies: `⟪f_j, Ay⟫ = ⟪Af_j, y⟫ = λ_j ⟪f_j, y⟫`. -/
theorem inner_eq_zero_of_generatorEigen {y : (flowGenerator V).domain} {μ : ℂ}
    (hy : flowGenerator V y = μ • (y : H)) {j : κ} (hj : (C.freq j : ℂ) ≠ μ) :
    ⟪C.basis j, (y : H)⟫_ℂ = 0 := by
  obtain ⟨hb, hAb⟩ := C.flowGenerator_basis j
  have h := flowGenerator_symmetric V ⟨C.basis j, hb⟩ y
  rw [hAb, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  by_contra hne
  exact hj (mul_right_cancel₀ hne h)

/-- Every generator eigenvalue is a clock frequency. -/
theorem exists_freq_eq_of_generatorEigen {y : (flowGenerator V).domain} (hy0 : (y : H) ≠ 0)
    {μ : ℂ} (hy : flowGenerator V y = μ • (y : H)) : ∃ j, (C.freq j : ℂ) = μ := by
  by_contra hall
  push Not at hall
  apply hy0
  apply C.basis.repr.injective
  refine lp.ext (funext fun j => ?_)
  rw [HilbertBasis.repr_apply_apply, C.inner_eq_zero_of_generatorEigen hy (hall j), map_zero]
  rfl

end CompactResolventClock

/-- **Theorem 3.1 (SM.5) for generators.**  If `U A U⁻¹ = qA` with `q > 1` (domains included) and
`A` has compact resolvent, then `A = 0` on the whole space, `V ≡ 1`, and `dim H < ∞`: `U` maps
the eigenvalue `λ` to `λ/q`, and `λ/qⁿ` would accumulate in a finite sublevel set. -/
theorem compactResolvent_generator_scaleLaw {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ}
    (hq : 1 < q) (hS : ScaleIntertwining U.symm (flowGenerator V) (flowGenerator V) q) {κ : Type*}
    (C : CompactResolventClock V κ) :
    (∀ k, C.freq k = 0) ∧ (∀ t x, V.op t x = x) ∧ Finite κ ∧ FiniteDimensional ℂ H ∧
      (flowGenerator V).domain = ⊤ ∧ ∀ x : (flowGenerator V).domain, flowGenerator V x = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by linarith : q ≠ 0)
  have hS' := hS.symm hq0
  have hstep : ∀ k, ∃ j, C.freq j = C.freq k / q := by
    intro k
    obtain ⟨hb, hAb⟩ := C.flowGenerator_basis k
    have hUb : U.symm.symm (C.basis k) ∈ (flowGenerator V).domain := (hS'.domain_iff _).1 hb
    have h1 := hS'.apply_mk hb hUb
    rw [hAb, LinearIsometryEquiv.map_smul, smul_smul] at h1
    have hy0 : U.symm.symm (C.basis k) ≠ 0 := fun h => by
      have := C.basis.orthonormal.1 k
      rw [← LinearIsometryEquiv.norm_map U.symm.symm, h, norm_zero] at this
      exact zero_ne_one this
    obtain ⟨j, hj⟩ := C.exists_freq_eq_of_generatorEigen (y := ⟨_, hUb⟩) hy0 h1
    refine ⟨j, Complex.ofReal_injective ?_⟩
    rw [hj]
    push_cast
    ring
  obtain ⟨h1, h2, h3, h4⟩ := C.trivial_of_freq_div hq hstep
  exact ⟨h1, h2, h3, h4, flowGenerator_of_trivial h2⟩

end GaloisForLFunctions.HTGeometry
