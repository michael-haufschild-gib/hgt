import GaloisForLFunctions.RHTower.DeningerCircleSeparating
import GaloisForLFunctions.RHTower.DeningerTomographyNotEmbedding

/-!
# The tomography into the topologised circle product

The map `𝒫_Q h = (Per_q h)_{q}` is assembled here between the spaces that carry their own
topologies: Meyer's source on the left, the countable product of the circle spaces on the right.  It
is continuous coordinatewise, injective on an infinite prime family, and the kernel of a single
periodization is stable under the damped translates, so the escape family that witnesses
non-strictness stays inside `K_p`.

* `deningerTomographyLM` : **`𝒫_Q` between the topologised spaces.**
* `deningerTomographyLM_continuous`
* `deningerTomographyLM_injective` : **`ker 𝒫_Q = 0` for an infinite prime family.**
* `deningerEscapeSource_mem_ker` : **the escape family stays in `K_p`.**
-/

namespace RHTower

open SchwartzMap Filter Topology

noncomputable section

/-- **`𝒫_Q` between the topologised spaces.** -/
def deningerTomographyLM {ι : Type*} (P : ι → {x : ℝ // 0 < x}) :
    DeningerMeyerSource →ₗ[ℂ] ((i : ι) → DeningerCircle (P i)) where
  toFun h i := deningerPeriodizationLM (P i) h
  map_add' h g := funext fun i => (deningerPeriodizationLM (P i)).map_add h g
  map_smul' c h := funext fun i => (deningerPeriodizationLM (P i)).map_smul c h

@[simp]
theorem deningerTomographyLM_apply {ι : Type*} (P : ι → {x : ℝ // 0 < x})
    (h : DeningerMeyerSource) (i : ι) :
    deningerTomographyLM P h i = deningerPeriodizationLM (P i) h := rfl

/-- **The tomography is continuous.** -/
theorem deningerTomographyLM_continuous {ι : Type*} (P : ι → {x : ℝ // 0 < x}) :
    Continuous (deningerTomographyLM P) :=
  continuous_pi fun i => deningerPeriodizationLM_continuous (P i)

/-! ## Membership in a single kernel is a pointwise vanishing statement -/

/-- Being in the kernel of a periodization means the lattice sum vanishes identically. -/
theorem deningerPeriodizationLM_eq_zero_iff (P : {x : ℝ // 0 < x}) (h : DeningerMeyerSource) :
    deningerPeriodizationLM P h = 0 ↔
      ∀ t : ℝ, deningerPeriodizationSum
        ((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) P.1 t = 0 := by
  constructor
  · intro hzero t
    have := congrArg
      (fun F : DeningerCircle P => ((DeningerCircle.toPeriodic F :
        ↥(DeningerSmoothPeriodic P.1)) : ℝ → ℂ) t) hzero
    simpa [deningerPeriodizationLM, deningerPeriodizationMap_apply] using this
  · intro hall
    refine (DeningerCircle.toPeriodic (P := P)).injective (Subtype.ext (funext fun t => ?_))
    show deningerPeriodizationSum
      ((DeningerMeyerSource.toSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) P.1 t = 0
    exact hall t

/-- The damped translate of a source cochain, as an element of the topologised source. -/
def deningerEscapeSource (a s : ℝ) (h : DeningerMeyerSource) : DeningerMeyerSource :=
  DeningerMeyerSource.toSource.symm
    (deningerEscapeFamily a s (DeningerMeyerSource.toSource h))

theorem deningerEscapeSource_toSource (a s : ℝ) (h : DeningerMeyerSource) :
    DeningerMeyerSource.toSource (deningerEscapeSource a s h)
      = deningerEscapeFamily a s (DeningerMeyerSource.toSource h) := rfl

/-- **The escape family stays in the kernel of every periodization.**  Periodization turns the
translation into a rotation and pulls the damping factor out, so an identically vanishing lattice
sum stays identically vanishing. -/
theorem deningerEscapeSource_mem_ker (P : {x : ℝ // 0 < x}) (a s : ℝ) {h : DeningerMeyerSource}
    (hh : deningerPeriodizationLM P h = 0) :
    deningerPeriodizationLM P (deningerEscapeSource a s h) = 0 := by
  rw [deningerPeriodizationLM_eq_zero_iff] at hh ⊢
  intro t
  rw [deningerEscapeSource_toSource, deningerEscapeFamily_periodizationSum, hh (t - s), mul_zero]

/-! ## Injectivity on an infinite prime family -/

/-- **The tomography of an infinite prime family is injective.** -/
theorem deningerTomographyLM_injective {Q : Set ℕ} (hQinf : Q.Infinite)
    (hQp : ∀ q ∈ Q, Nat.Prime q) (P : Q → {x : ℝ // 0 < x})
    (hP : ∀ q : Q, (P q).1 = Real.log (q : ℕ)) :
    Function.Injective (deningerTomographyLM P) := by
  intro a b hab
  have hfun : ∀ q ∈ Q, ∀ t : ℝ,
      deningerPeriodizationSum
        ((DeningerMeyerSource.toSource a : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t
        = deningerPeriodizationSum
          ((DeningerMeyerSource.toSource b : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t := by
    intro q hq t
    have hco := congrArg (fun u : (i : Q) → DeningerCircle (P i) =>
      ((DeningerCircle.toPeriodic (u ⟨q, hq⟩) :
        ↥(DeningerSmoothPeriodic (P ⟨q, hq⟩).1)) : ℝ → ℂ) t) hab
    simp only [deningerTomographyLM_apply] at hco
    have hval : deningerPeriodizationSum
        ((DeningerMeyerSource.toSource a : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
          (P ⟨q, hq⟩).1 t
        = deningerPeriodizationSum
          ((DeningerMeyerSource.toSource b : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
            (P ⟨q, hq⟩).1 t := by
      simpa [deningerPeriodizationLM, deningerPeriodizationMap_apply] using hco
    rwa [hP ⟨q, hq⟩] at hval
  have hsub : ((DeningerMeyerSource.toSource a : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
      = ((DeningerMeyerSource.toSource b : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) :=
    deningerCofinalPrimeTomography_eq (DeningerMeyerSource.toSource a).2
      (DeningerMeyerSource.toSource b).2 hQinf hQp hfun
  exact DeningerMeyerSource.toSource.injective (Subtype.ext hsub)

end

end RHTower
