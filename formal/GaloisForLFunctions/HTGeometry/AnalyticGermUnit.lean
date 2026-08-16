import GaloisForLFunctions.HTGeometry.AnalyticGermDomain

/-!
# Units of the ring of analytic germs, and the two structural germs of a split coordinate

A germ is a unit exactly when its value at the point is nonzero: the reciprocal of a function
analytic and nonvanishing at a point is analytic there.  This makes `AnalyticGerm p` a local ring
with maximal ideal the kernel of the value homomorphism.

Splitting off the first coordinate of `ℂ^(n+1)` gives two structural pieces of the germ ring at the
origin: the germ `germCoord` of the first coordinate, and the ring homomorphism `germTail` pulling
germs in the remaining variables back along the projection.  Together they present a distinguished
polynomial as an algebraic expression in the germ ring.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **A germ is a unit exactly when it does not vanish at the point.** -/
theorem isUnit_analyticGerm_iff {p : E} (a : AnalyticGerm p) :
    IsUnit a ↔ analyticGermValue p a ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    intro h
    have hmul : analyticGermValue p (u : AnalyticGerm p) * analyticGermValue p (↑u⁻¹) = 1 := by
      rw [← map_mul, u.mul_inv, map_one]
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  · intro h
    obtain ⟨f, hf, hfa⟩ := a.2
    have haeq : a = analyticGermOf hf := Subtype.ext hfa.symm
    have hval : f p ≠ 0 := by
      rw [haeq, analyticGermValue_of hf] at h
      exact h
    have hinv : AnalyticAt ℂ (fun x => (f x)⁻¹) p := hf.inv hval
    refine isUnit_iff_exists_inv.mpr ⟨analyticGermOf hinv, ?_⟩
    refine Subtype.ext ?_
    rw [Subring.coe_mul, ← hfa, analyticGermOf_val, ← Germ.coe_mul, OneMemClass.coe_one]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [hf.continuousAt.eventually_ne hval] with x hx
    simp [mul_inv_cancel₀ hx]

/-! ## The split coordinate -/

variable {n : ℕ}

theorem analyticAt_coordZero :
    AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ => w 0) (0 : Fin (n + 1) → ℂ) :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt _

theorem analyticAt_tail :
    AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ => (Fin.tail w : Fin n → ℂ))
      (0 : Fin (n + 1) → ℂ) := by
  have : AnalyticAt ℂ (fun w : Fin (n + 1) → ℂ =>
      ((ContinuousLinearMap.pi fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) i.succ) w))
      (0 : Fin (n + 1) → ℂ) :=
    (ContinuousLinearMap.pi fun i : Fin n =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) i.succ).analyticAt _
  exact this

/-- The germ of the distinguished coordinate at the origin. -/
noncomputable def germCoord (n : ℕ) : AnalyticGerm (0 : Fin (n + 1) → ℂ) :=
  analyticGermOf analyticAt_coordZero

/-- Pulling germs in the remaining variables back along the projection. -/
noncomputable def germTail (n : ℕ) :
    AnalyticGerm (0 : Fin n → ℂ) →+* AnalyticGerm (0 : Fin (n + 1) → ℂ) :=
  analyticGermPullback analyticAt_tail (by
    funext i
    simp [Fin.tail])

theorem germTail_analyticGermOf {a : (Fin n → ℂ) → ℂ} (ha : AnalyticAt ℂ a (0 : Fin n → ℂ)) :
    (germTail n (analyticGermOf ha) : Germ (𝓝 (0 : Fin (n + 1) → ℂ)) ℂ)
      = ((a ∘ fun w : Fin (n + 1) → ℂ => (Fin.tail w : Fin n → ℂ)) :
          (Fin (n + 1) → ℂ) → ℂ) :=
  analyticGermPullback_analyticGermOf analyticAt_tail _ ha

@[simp]
theorem analyticGermValue_germCoord :
    analyticGermValue (0 : Fin (n + 1) → ℂ) (germCoord n) = 0 := rfl

end GaloisForLFunctions.HTGeometry
