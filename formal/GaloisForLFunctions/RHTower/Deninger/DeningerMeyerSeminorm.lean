import GaloisForLFunctions.RHTower.Deninger.DeningerExpSchwartz
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The Meyer seminorms of the exponentially decreasing source

Meyer's cochain space is the projective limit of the exponentially weighted Schwartz spaces, and its
defining seminorms are

`q_{A,n}(h) = sup_t e^{A|t|} ‖h^{(n)}(t)‖`.

Each is finite exactly because membership in the source *is* the statement that this supremum is
bounded, so the supremum is an honest seminorm on the source — not merely on a dense subspace.

* `deningerMeyerWeight`, `deningerMeyerWeight_le` : the weight and its supremum bound.
* `deningerMeyerSeminorm` : **the Meyer seminorm `q_{A,n}`.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The Meyer weight of a source element at exponent `A` and derivative order `n`. -/
def deningerMeyerWeight (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) (t : ℝ) : ℝ :=
  Real.exp (A * |t|) *
    ‖iteratedFDeriv ℝ n (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖

theorem deningerMeyerWeight_nonneg (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) (t : ℝ) :
    0 ≤ deningerMeyerWeight A n h t := by
  rw [deningerMeyerWeight]
  positivity

/-- The Meyer weight is bounded, which is exactly membership in the source. -/
theorem deningerMeyerWeight_bddAbove (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) :
    BddAbove (Set.range (deningerMeyerWeight A n h)) := by
  obtain ⟨C, hC⟩ := h.2 A n
  refine ⟨C, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hC t

/-- **The Meyer seminorm** `q_{A,n}(h) = sup_t e^{A|t|} ‖h^{(n)}(t)‖`, as a function. -/
def deningerMeyerSeminormFun (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) : ℝ :=
  ⨆ t : ℝ, deningerMeyerWeight A n h t

theorem deningerMeyerSeminormFun_nonneg (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) :
    0 ≤ deningerMeyerSeminormFun A n h :=
  Real.iSup_nonneg fun t => deningerMeyerWeight_nonneg A n h t

/-- **The defining bound of the Meyer seminorm.** -/
theorem deningerMeyerWeight_le (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) (t : ℝ) :
    deningerMeyerWeight A n h t ≤ deningerMeyerSeminormFun A n h :=
  le_ciSup (deningerMeyerWeight_bddAbove A n h) t

theorem deningerMeyerSeminormFun_le {A : ℝ} {n : ℕ} {h : DeningerExpSchwartz} {C : ℝ}
    (hC : ∀ t : ℝ, deningerMeyerWeight A n h t ≤ C) : deningerMeyerSeminormFun A n h ≤ C :=
  ciSup_le hC

/-- The seminorm is additive-subadditive. -/
theorem deningerMeyerSeminormFun_add_le (A : ℝ) (n : ℕ) (f g : DeningerExpSchwartz) :
    deningerMeyerSeminormFun A n (f + g)
      ≤ deningerMeyerSeminormFun A n f + deningerMeyerSeminormFun A n g := by
  refine deningerMeyerSeminormFun_le fun t => ?_
  have hcoe : (((f + g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
        + (((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := rfl
  have hsplit : iteratedFDeriv ℝ n (((f + g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
      = iteratedFDeriv ℝ n (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
        + iteratedFDeriv ℝ n (((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t := by
    rw [hcoe]
    exact iteratedFDeriv_add_apply
      ((((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth n).contDiffAt)
      ((((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth n).contDiffAt)
  have hexp : (0 : ℝ) ≤ Real.exp (A * |t|) := (Real.exp_pos _).le
  calc deningerMeyerWeight A n (f + g) t
      = Real.exp (A * |t|) *
        ‖iteratedFDeriv ℝ n (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
          + iteratedFDeriv ℝ n (((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖ := by
        rw [deningerMeyerWeight, hsplit]
    _ ≤ Real.exp (A * |t|) *
        (‖iteratedFDeriv ℝ n (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖
          + ‖iteratedFDeriv ℝ n (((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hexp
    _ = deningerMeyerWeight A n f t + deningerMeyerWeight A n g t := by
        rw [deningerMeyerWeight, deningerMeyerWeight]
        ring
    _ ≤ deningerMeyerSeminormFun A n f + deningerMeyerSeminormFun A n g :=
        add_le_add (deningerMeyerWeight_le A n f t) (deningerMeyerWeight_le A n g t)

/-- The seminorm is absolutely homogeneous. -/
theorem deningerMeyerSeminormFun_smul (A : ℝ) (n : ℕ) (c : ℂ) (f : DeningerExpSchwartz) :
    deningerMeyerSeminormFun A n (c • f) = ‖c‖ * deningerMeyerSeminormFun A n f := by
  have hcoe : (((c • f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = c • (((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := rfl
  have hweight : ∀ t : ℝ,
      deningerMeyerWeight A n (c • f) t = ‖c‖ * deningerMeyerWeight A n f t := by
    intro t
    rw [deningerMeyerWeight, deningerMeyerWeight, hcoe,
      iteratedFDeriv_const_smul_apply
        ((((f : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth n).contDiffAt),
      norm_smul]
    ring
  rw [deningerMeyerSeminormFun, deningerMeyerSeminormFun,
    Real.mul_iSup_of_nonneg (norm_nonneg c)]
  exact iSup_congr hweight

/-- **The Meyer seminorm** `q_{A,n}` of the exponentially decreasing source. -/
def deningerMeyerSeminorm (A : ℝ) (n : ℕ) : Seminorm ℂ DeningerExpSchwartz :=
  Seminorm.of (deningerMeyerSeminormFun A n) (deningerMeyerSeminormFun_add_le A n)
    (deningerMeyerSeminormFun_smul A n)

@[simp]
theorem deningerMeyerSeminorm_apply (A : ℝ) (n : ℕ) (h : DeningerExpSchwartz) :
    deningerMeyerSeminorm A n h = deningerMeyerSeminormFun A n h := rfl

/-- The Meyer seminorm family, indexed by the exponent and the derivative order. -/
def deningerMeyerSeminormFamily : SeminormFamily ℂ DeningerExpSchwartz (ℕ × ℕ) :=
  fun m => deningerMeyerSeminorm (m.1 : ℝ) m.2

end

end RHTower
