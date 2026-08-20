/-
# The Schrödinger evolution is a phase point of the spectral bundle

The evolved state `e^{-isH}Ω` pairs with a target `v` exactly as the gauge-invariant cross-weight
vector `w_j = conj⟨e_j,v⟩⟨e_j,Ω⟩` pairs with the relative-phase point `s(λ_j-λ_{i₀})/2π`.  The
identity is exact, and both sides are free of any eigenvector gauge.

Main results:
* `unitaryEvolution_mulVec_eq_sum` — the evolved state in an eigenbasis.
* `evolvedPhasePoint` — the anchored relative-phase point of physical time `s`.
* `norm_finiteComplexInner_unitaryEvolution_eq` — **the pairing modulus is a bundle pairing**.
* `finitePureStateFidelity_unitaryEvolution_eq` — the same for the fidelity.
-/
import GaloisForLFunctions.HTGeometry.SpectralBundleCaptureTube
import GaloisForLFunctions.HTGeometry.ObserverInvisibleRayPreservation

open Matrix Complex UnitAddTorus ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem finiteComplexInner_sum_smul_left (a : α → ℂ) (e : α → α → ℂ) (v : α → ℂ) :
    finiteComplexInner (∑ j, a j • e j) v
      = ∑ j, conj (a j) * finiteComplexInner (e j) v := by
  classical
  have hlhs : finiteComplexInner (∑ j, a j • e j) v
      = ∑ x, ∑ j, conj (a j) * (conj (e j x) * v x) := by
    rw [finiteComplexInner]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (∑ j, a j • e j) x = ∑ j, a j * e j x := by
      simp [Finset.sum_apply]
    rw [hx, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring
  rw [hlhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finiteComplexInner, Finset.mul_sum]

/-- The evolved state, expanded in an orthonormal eigenbasis. -/
theorem unitaryEvolution_mulVec_eq_sum {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (Ω : α → ℂ) (s : ℝ) :
    unitaryEvolution H s *ᵥ Ω
      = ∑ j, (finiteComplexInner (e j) Ω * Complex.exp (-(Complex.I * (s * lam j)))) • e j := by
  conv_lhs => rw [← heb.complete Ω]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, QuantumAlg.unitaryEvolution_mulVec_of_eigenvector (heb.eigen j) s,
    smul_smul]

/-- The anchored relative-phase point carrying the Schrödinger evolution at physical time `s`. -/
def evolvedPhasePoint (lam : α → ℝ) (i₀ : α) (s : ℝ) : UnitAddTorus {i : α // i ≠ i₀} :=
  fun j => (((s / (2 * Real.pi)) * (lam j.1 - lam i₀) : ℝ) : UnitAddCircle)

theorem mFourier_torusSection_evolvedPhasePoint (lam : α → ℝ) (i₀ : α) (s : ℝ) (j : α) :
    UnitAddTorus.mFourier (Pi.single j 1) (torusSection i₀ (evolvedPhasePoint lam i₀ s))
      = Complex.exp (Complex.I * ((s : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ)))) := by
  rw [UnitAddTorus.mFourier_single]
  have hsec : torusSection i₀ (evolvedPhasePoint lam i₀ s) j
      = (((s / (2 * Real.pi)) * (lam j - lam i₀) : ℝ) : UnitAddCircle) := by
    by_cases hj : j ≠ i₀
    · rw [torusSection, dif_pos hj]
      rfl
    · rw [torusSection, dif_neg hj]
      have hji : j = i₀ := not_ne_iff.mp hj
      subst hji
      simp
  rw [hsec, fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **The evolved pairing modulus is the bundle pairing of the cross-weights.**  No eigenvector
gauge appears on either side. -/
theorem norm_finiteComplexInner_unitaryEvolution_eq {H : Matrix α α ℂ} {e : α → α → ℂ}
    {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    (Ω v : α → ℂ) (i₀ : α) (s : ℝ) :
    ‖finiteComplexInner (unitaryEvolution H s *ᵥ Ω) v‖
      = ‖bundlePairing (spectralCrossWeight lam H v Ω)
          (torusSection i₀ (evolvedPhasePoint lam i₀ s))‖ := by
  classical
  have hphase : ‖Complex.exp (-(Complex.I * ((s : ℂ) * (lam i₀ : ℂ))))‖ = 1 := by
    have hrw : -(Complex.I * ((s : ℂ) * (lam i₀ : ℂ))) = ((-(s * lam i₀) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hrw, Complex.norm_exp_ofReal_mul_I]
  have hexp : finiteComplexInner (unitaryEvolution H s *ᵥ Ω) v
      = conj (Complex.exp (-(Complex.I * ((s : ℂ) * (lam i₀ : ℂ))))) *
        ∑ j, conj (finiteComplexInner (e j) Ω) *
          Complex.exp (Complex.I * ((s : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ)))) *
          finiteComplexInner (e j) v := by
    rw [unitaryEvolution_mulVec_eq_sum heb Ω s, finiteComplexInner_sum_smul_left,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc1 : conj (-(Complex.I * ((s : ℂ) * (lam j : ℂ))))
        = Complex.I * ((s : ℂ) * (lam j : ℂ)) := by
      simp [Complex.conj_I]
    have hc2 : conj (-(Complex.I * ((s : ℂ) * (lam i₀ : ℂ))))
        = Complex.I * ((s : ℂ) * (lam i₀ : ℂ)) := by
      simp [Complex.conj_I]
    have key : Complex.exp (Complex.I * ((s : ℂ) * (lam j : ℂ)))
        = Complex.exp (Complex.I * ((s : ℂ) * (lam i₀ : ℂ))) *
          Complex.exp (Complex.I * ((s : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ)))) := by
      rw [← Complex.exp_add]
      ring_nf
    rw [map_mul, ← Complex.exp_conj, ← Complex.exp_conj, hc1, hc2, key]
    ring
  rw [hexp, norm_mul, Complex.norm_conj, hphase, one_mul, bundlePairing]
  rw [show (∑ j, conj (UnitAddTorus.mFourier (Pi.single j 1)
      (torusSection i₀ (evolvedPhasePoint lam i₀ s))) * spectralCrossWeight lam H v Ω j)
      = conj (∑ j, conj (finiteComplexInner (e j) Ω) *
          Complex.exp (Complex.I * ((s : ℂ) * ((lam j : ℂ) - (lam i₀ : ℂ)))) *
          finiteComplexInner (e j) v) from ?_]
  · rw [Complex.norm_conj]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mFourier_torusSection_evolvedPhasePoint, spectralCrossWeight_eq heb hinj v Ω j]
    rw [map_mul, map_mul, RingHomInvPair.comp_apply_eq]
    ring

/-- The fidelity form of the same identity. -/
theorem finitePureStateFidelity_unitaryEvolution_eq {H : Matrix α α ℂ} {e : α → α → ℂ}
    {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam) (hinj : Function.Injective lam)
    (Ω v : α → ℂ) (i₀ : α) (s : ℝ) :
    finitePureStateFidelity (unitaryEvolution H s *ᵥ Ω) v
      = ‖bundlePairing (spectralCrossWeight lam H v Ω)
          (torusSection i₀ (evolvedPhasePoint lam i₀ s))‖ ^ 2 := by
  rw [finitePureStateFidelity, norm_finiteComplexInner_unitaryEvolution_eq heb hinj Ω v i₀ s]

end GaloisForLFunctions.HTGeometry

end
