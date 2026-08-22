import GaloisForLFunctions.RHTower.DeningerDynSysValuedPointsAffine
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Algebra.Monoid

/-!
# The topology on the character points of an affine scheme

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §7, Lemmas 7.1 and 7.3.

For an affine scheme `X = Spec R` the space `X̂ (C)` is the set of pointed multiplicative maps
`Q : R → C` whose zero set is additively closed, equipped with the topology of pointwise
convergence, i.e. the subspace topology of the product topology on `C^R`.

The projection `X̂ (C) → Spec R`, `Q ↦ Q⁻¹(0)`, is continuous: the preimage of the closed set
`V (t)` is the intersection over `r ∈ t` of the closed sets `{Q | Q r = 0}`.  The Frobenius
operators `Q ↦ Q^ν` and the action of a ring automorphism of `R` are continuous, and the
automorphism action is by homeomorphisms.
-/

namespace RHTower

variable {R C : Type*} [CommRing R] [CommRing C]

/-- **Deninger, §7.**  The space `X̂ (C)` for an affine scheme `Spec R`: the pointed multiplicative
maps `R → C` whose zero set is additively closed. -/
def DeningerAffinePoints (R C : Type*) [CommRing R] [CommRing C] : Type _ :=
  {Q : R →*₀ C // DeningerAdditiveOnZeros Q}

namespace DeningerAffinePoints

/-- The underlying pointed multiplicative map. -/
def toFun (Q : DeningerAffinePoints R C) : R → C := fun r => Q.1 r

@[ext] theorem ext {Q Q' : DeningerAffinePoints R C} (h : ∀ r, Q.1 r = Q'.1 r) : Q = Q' :=
  Subtype.ext (DFunLike.ext _ _ h)

end DeningerAffinePoints

variable [TopologicalSpace C]

/-- **Deninger, §7.**  The topology of pointwise convergence on `X̂ (C)`. -/
instance deningerAffinePointsTopology : TopologicalSpace (DeningerAffinePoints R C) :=
  TopologicalSpace.induced DeningerAffinePoints.toFun inferInstance

theorem deningerAffineEval_continuous (r : R) :
    Continuous fun Q : DeningerAffinePoints R C => Q.1 r :=
  (continuous_apply r).comp continuous_induced_dom

/-- The projection `X̂ (C) → Spec R`. -/
def deningerAffineProj [IsDomain C] (Q : DeningerAffinePoints R C) : PrimeSpectrum R :=
  ⟨deningerZeroIdeal Q.1 Q.2, deningerZeroIdeal_isPrime Q.1 Q.2⟩

omit [TopologicalSpace C] in
@[simp] theorem deningerAffineProj_mem [IsDomain C] (Q : DeningerAffinePoints R C) (r : R) :
    r ∈ (deningerAffineProj Q).asIdeal ↔ Q.1 r = 0 := Iff.rfl

/-- **Deninger, Lemma 7.1 (`t7`).**  For an affine scheme the projection to the underlying scheme
is continuous. -/
theorem deningerAffineProj_continuous [IsDomain C] [T1Space C] :
    Continuous (deningerAffineProj (R := R) (C := C)) := by
  rw [continuous_iff_isClosed]
  intro s hs
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).1 hs
  have hpre : deningerAffineProj ⁻¹' s
      = ⋂ r ∈ t, (fun Q : DeningerAffinePoints R C => Q.1 r) ⁻¹' {0} := by
    ext Q
    constructor
    · intro hQ
      refine Set.mem_iInter₂.2 fun r hr => ?_
      rw [ht] at hQ
      exact hQ hr
    · intro hQ
      rw [ht]
      intro r hr
      exact Set.mem_iInter₂.1 hQ r hr
  rw [hpre]
  exact isClosed_biInter fun r _ =>
    isClosed_singleton.preimage (deningerAffineEval_continuous r)

/-! ## The Frobenius operators and the automorphism action -/

/-- **Deninger, §7.**  The Frobenius operator `F_ν` on the points of an affine scheme. -/
def deningerAffineFrobenius [IsDomain C] {ν : ℕ} (hν : 0 < ν)
    (Q : DeningerAffinePoints R C) : DeningerAffinePoints R C :=
  ⟨{ toFun := fun r => Q.1 r ^ ν
     map_zero' := by simp [hν.ne']
     map_one' := by simp
     map_mul' := fun a b => by simp [mul_pow] },
   by
     intro f f' hf'
     have h0 : Q.1 f' = 0 := by
       have := pow_eq_zero_iff (n := ν) hν.ne' |>.1 hf'
       exact this
     show Q.1 (f + f') ^ ν = Q.1 f ^ ν
     rw [Q.2 f f' h0]⟩

omit [TopologicalSpace C] in
@[simp] theorem deningerAffineFrobenius_apply [IsDomain C] {ν : ℕ} (hν : 0 < ν)
    (Q : DeningerAffinePoints R C) (r : R) :
    (deningerAffineFrobenius hν Q).1 r = Q.1 r ^ ν := rfl

/-- **Deninger, Lemma 7.3 (`t9`), continuity of the Frobenius operators.** -/
theorem deningerAffineFrobenius_continuous [IsDomain C] [ContinuousMul C] {ν : ℕ} (hν : 0 < ν) :
    Continuous (deningerAffineFrobenius (R := R) (C := C) hν) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun r => ?_
  exact (continuous_pow ν).comp (deningerAffineEval_continuous r)

/-- The action of a ring automorphism of `R` on the points. -/
def deningerAffineAut (σ : R ≃+* R) (Q : DeningerAffinePoints R C) : DeningerAffinePoints R C :=
  ⟨Q.1.comp σ.toRingHom.toMonoidWithZeroHom, by
    intro f f' hf'
    show Q.1 (σ (f + f')) = Q.1 (σ f)
    rw [map_add]
    exact Q.2 (σ f) (σ f') hf'⟩

omit [TopologicalSpace C] in
@[simp] theorem deningerAffineAut_apply (σ : R ≃+* R) (Q : DeningerAffinePoints R C) (r : R) :
    (deningerAffineAut σ Q).1 r = Q.1 (σ r) := rfl

theorem deningerAffineAut_continuous (σ : R ≃+* R) :
    Continuous (deningerAffineAut (R := R) (C := C) σ) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun r => deningerAffineEval_continuous (σ r)

omit [TopologicalSpace C] in
@[simp] theorem deningerAffineAut_trans (σ τ : R ≃+* R) (Q : DeningerAffinePoints R C) :
    deningerAffineAut σ (deningerAffineAut τ Q) = deningerAffineAut (σ.trans τ) Q := rfl

omit [TopologicalSpace C] in
@[simp] theorem deningerAffineAut_refl (Q : DeningerAffinePoints R C) :
    deningerAffineAut (RingEquiv.refl R) Q = Q := rfl

/-- **Deninger, Lemma 7.3 (`t9`), the automorphism action is by homeomorphisms.** -/
def deningerAffineAutHomeomorph (σ : R ≃+* R) :
    DeningerAffinePoints R C ≃ₜ DeningerAffinePoints R C where
  toFun := deningerAffineAut σ
  invFun := deningerAffineAut σ.symm
  left_inv Q := by
    ext r
    simp
  right_inv Q := by
    ext r
    simp
  continuous_toFun := deningerAffineAut_continuous σ
  continuous_invFun := deningerAffineAut_continuous σ.symm

end RHTower

namespace RHTower

variable {R C : Type*} [CommRing R] [CommRing C] [TopologicalSpace C]
variable {G : Type*} [Group G] [MulSemiringAction G R] [TopologicalSpace G]

/-- **Deninger, §7.**  The right action of a group of ring automorphisms on the points of an affine
scheme. -/
def deningerAffineSMul (σ : G) (Q : DeningerAffinePoints R C) : DeningerAffinePoints R C :=
  ⟨{ toFun := fun r => Q.1 (σ • r)
     map_zero' := by simp
     map_one' := by simp
     map_mul' := fun a b => by simp [smul_mul'] },
   by
     intro f f' hf'
     show Q.1 (σ • (f + f')) = Q.1 (σ • f)
     rw [smul_add]
     exact Q.2 (σ • f) (σ • f') hf'⟩

omit [TopologicalSpace C] [TopologicalSpace G] in
@[simp] theorem deningerAffineSMul_apply (σ : G) (Q : DeningerAffinePoints R C) (r : R) :
    (deningerAffineSMul σ Q).1 r = Q.1 (σ • r) := rfl

/-- **Deninger, Proposition 7.5 (`t85`).**  If the group acts continuously on the discrete ring
`R` — i.e. every `σ ↦ σ • r` is locally constant — then the action map on the points of an affine
scheme is jointly continuous. -/
theorem deningerAffineSMul_continuous
    (hstab : ∀ (r : R) (σ₀ : G), ∀ᶠ σ in nhds σ₀, σ • r = σ₀ • r) :
    Continuous fun p : DeningerAffinePoints R C × G => deningerAffineSMul p.2 p.1 := by
  rw [continuous_induced_rng]
  refine continuous_pi fun r => ?_
  rw [continuous_iff_continuousAt]
  rintro ⟨Q₀, σ₀⟩
  have hcont : ContinuousAt
      (fun p : DeningerAffinePoints R C × G => p.1.1 (σ₀ • r)) (Q₀, σ₀) :=
    ((deningerAffineEval_continuous (C := C) (σ₀ • r)).comp continuous_fst).continuousAt
  refine hcont.congr ?_
  have hsnd : Filter.Tendsto (fun p : DeningerAffinePoints R C × G => p.2)
      (nhds (Q₀, σ₀)) (nhds σ₀) := continuous_snd.continuousAt
  filter_upwards [hsnd.eventually (hstab r σ₀)] with p hp
  show p.1.1 (σ₀ • r) = (DeningerAffinePoints.toFun ∘ fun p : DeningerAffinePoints R C × G =>
    deningerAffineSMul p.2 p.1) p r
  show p.1.1 (σ₀ • r) = p.1.1 (p.2 • r)
  rw [hp]

end RHTower
