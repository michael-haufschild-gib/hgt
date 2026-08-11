import GaloisForLFunctions.RHTower.DeningerExpWeightDeriv

/-!
# Multipliers with bounded derivatives

A smooth function all of whose derivatives are bounded multiplies the source into itself: the
Leibniz expansion turns every exponentially weighted bound of the factor into an exponentially
weighted bound of the product, with the multiplier contributing only constants.

* `deningerBddMultiplier` : the class of such multipliers.
* `deningerBddMul` : **multiplication by one, as a linear map of the source.**
-/

namespace RHTower

open SchwartzMap
open scoped ContDiff

noncomputable section

/-- A smooth function all of whose iterated derivatives are bounded. -/
structure DeningerBddMultiplier where
  /-- The underlying function. -/
  toFun : ℝ → ℂ
  /-- It is smooth. -/
  smooth : ContDiff ℝ ∞ toFun
  /-- Every iterated derivative is bounded. -/
  bounded : ∀ j : ℕ, ∃ D : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ j toFun t‖ ≤ D

instance : CoeFun DeningerBddMultiplier fun _ => ℝ → ℂ := ⟨DeningerBddMultiplier.toFun⟩

/-- **Multiplying by a bounded multiplier keeps the exponentially weighted bounds.** -/
theorem deningerBddMul_bounds (g : DeningerBddMultiplier) {h : 𝓢(ℝ, ℂ)}
    (hh : h ∈ DeningerExpSchwartz) (A : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, Real.exp (A * |x|)
      * ‖iteratedFDeriv ℝ n (fun t => (g : ℝ → ℂ) t * (h : ℝ → ℂ) t) x‖ ≤ C := by
  choose D hD using g.bounded
  choose C hC using fun m : ℕ => hh A m
  refine ⟨∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * |D j| * |C (n - j)|, fun x => ?_⟩
  have hleib : ‖iteratedFDeriv ℝ n (fun t => (g : ℝ → ℂ) t * (h : ℝ → ℂ) t) x‖
      ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * ‖iteratedFDeriv ℝ j (g : ℝ → ℂ) x‖
          * ‖iteratedFDeriv ℝ (n - j) (h : ℝ → ℂ) x‖ :=
    norm_iteratedFDeriv_mul_le g.smooth (h.smooth (⊤ : ℕ∞)) x (by exact_mod_cast le_top)
  have hstep : Real.exp (A * |x|)
      * ‖iteratedFDeriv ℝ n (fun t => (g : ℝ → ℂ) t * (h : ℝ → ℂ) t) x‖
      ≤ Real.exp (A * |x|) * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)
          * ‖iteratedFDeriv ℝ j (g : ℝ → ℂ) x‖
          * ‖iteratedFDeriv ℝ (n - j) (h : ℝ → ℂ) x‖ :=
    mul_le_mul_of_nonneg_left hleib (Real.exp_pos _).le
  refine le_trans hstep ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hg : ‖iteratedFDeriv ℝ j (g : ℝ → ℂ) x‖ ≤ |D j| := le_trans (hD j x) (le_abs_self _)
  have hh' : Real.exp (A * |x|) * ‖iteratedFDeriv ℝ (n - j) (h : ℝ → ℂ) x‖ ≤ |C (n - j)| :=
    le_trans (hC (n - j) x) (le_abs_self _)
  calc Real.exp (A * |x|) * ((n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (g : ℝ → ℂ) x‖
          * ‖iteratedFDeriv ℝ (n - j) (h : ℝ → ℂ) x‖)
      = (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j (g : ℝ → ℂ) x‖
          * (Real.exp (A * |x|) * ‖iteratedFDeriv ℝ (n - j) (h : ℝ → ℂ) x‖) := by ring
    _ ≤ (n.choose j : ℝ) * |D j| * |C (n - j)| := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity)) hh' (by positivity)
          (by positivity)

/-- **Multiplication by a bounded multiplier, as a linear map of the source.** -/
def deningerBddMul (g : DeningerBddMultiplier) : DeningerExpSchwartz →ₗ[ℂ] DeningerExpSchwartz where
  toFun h := ⟨deningerExpSchwartzOfBounds
      (fun t => (g : ℝ → ℂ) t * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
      (g.smooth.mul (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)))
      (deningerBddMul_bounds g h.2),
    deningerExpSchwartzOfBounds_mem _ _ _⟩
  map_add' h k := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    show (g : ℝ → ℂ) t * (((h + k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
      = (g : ℝ → ℂ) t * (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
        + (g : ℝ → ℂ) t * (((k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
    show (g : ℝ → ℂ) t * ((((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
        + (((k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t) = _
    ring
  map_smul' c h := by
    refine Subtype.ext (SchwartzMap.ext fun t => ?_)
    show (g : ℝ → ℂ) t * (((c • h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t
      = c * ((g : ℝ → ℂ) t * (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t)
    show (g : ℝ → ℂ) t * (c * (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) t) = _
    ring

@[simp]
theorem deningerBddMul_apply (g : DeningerBddMultiplier) (h : DeningerExpSchwartz) (t : ℝ) :
    ((deningerBddMul g h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t
      = (g : ℝ → ℂ) t * ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t := rfl

/-- **Two multipliers that are pointwise inverse give mutually inverse operations.** -/
theorem deningerBddMul_comp (g g' : DeningerBddMultiplier)
    (hinv : ∀ t : ℝ, (g : ℝ → ℂ) t * (g' : ℝ → ℂ) t = 1) (h : DeningerExpSchwartz) :
    deningerBddMul g (deningerBddMul g' h) = h := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerBddMul_apply, deningerBddMul_apply, ← mul_assoc, hinv t, one_mul]

/-- **A multiplier with a pointwise inverse acts surjectively on the source.** -/
theorem deningerBddMul_surjective (g g' : DeningerBddMultiplier)
    (hinv : ∀ t : ℝ, (g : ℝ → ℂ) t * (g' : ℝ → ℂ) t = 1) :
    Function.Surjective (deningerBddMul g) :=
  fun h => ⟨deningerBddMul g' h, deningerBddMul_comp g g' hinv h⟩

end

end RHTower
