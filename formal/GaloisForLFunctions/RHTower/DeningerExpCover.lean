import GaloisForLFunctions.RHTower.DeningerDlogPeriod

/-!
# The exponential covering of a character stage

The coordinatewise exponential maps the complex vector space onto a character stage, is holomorphic,
and identifies two points exactly when their coordinates differ by integer multiples of `2πi`.  A
function on the vector space that is `2πi`-periodic in every coordinate therefore descends to the
stage; this is what makes a primitive found on the convex covering space produce a function on the
stage.

* `deningerExpMap` : the coordinatewise exponential.
* `deningerExpMap_hasFDerivAt` : its derivative is the diagonal of its values.
* `deningerExpMap_periodic` : periodicity in each coordinate.
* `deningerPeriodic_descent` : a coordinatewise periodic function is constant on the fibres.
-/

namespace RHTower

open Complex

section ExpCover

variable {r : ℕ}

/-- **The exponential covering of a character stage**: the coordinatewise exponential. -/
noncomputable def deningerExpMap (r : ℕ) : (Fin r → ℂ) → (Fin r → ℂ) :=
  fun w j => Complex.exp (w j)

@[simp]
theorem deningerExpMap_apply (w : Fin r → ℂ) (j : Fin r) :
    deningerExpMap r w j = Complex.exp (w j) := rfl

/-- **The exponential covering lands in the stage.** -/
theorem deningerExpMap_mem (w : Fin r → ℂ) : deningerExpMap r w ∈ deningerStageTorus r :=
  fun _ => Complex.exp_ne_zero _

/-- The derivative of the exponential covering: the diagonal of its values. -/
noncomputable def deningerExpDeriv (w : Fin r → ℂ) : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    (Complex.exp (w j)) • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j)

@[simp]
theorem deningerExpDeriv_apply (w u : Fin r → ℂ) (j : Fin r) :
    deningerExpDeriv w u j = Complex.exp (w j) * u j := rfl

theorem deningerExpMap_hasFDerivAt (w : Fin r → ℂ) :
    HasFDerivAt (deningerExpMap r) (deningerExpDeriv w) w := by
  refine hasFDerivAt_pi.2 fun j => ?_
  have hproj : HasFDerivAt (fun y : Fin r → ℂ => y j)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j) w :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).hasFDerivAt
  have hexp : HasDerivAt Complex.exp (Complex.exp (w j)) (w j) := Complex.hasDerivAt_exp _
  have hcomp := hexp.hasFDerivAt.comp w hproj
  have heq : (ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (w j))).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j) =
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).comp
        (deningerExpDeriv w) := by
    refine ContinuousLinearMap.ext fun u => ?_
    show u j • Complex.exp (w j) = Complex.exp (w j) * u j
    rw [smul_eq_mul]
    ring
  rw [heq] at hcomp
  exact hcomp

theorem deningerExpMap_analyticAt (w : Fin r → ℂ) : AnalyticAt ℂ (deningerExpMap r) w := by
  refine AnalyticAt.pi fun j => ?_
  have hproj : AnalyticAt ℂ (fun y : Fin r → ℂ => y j) w :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).analyticAt w
  exact hproj.cexp'

/-- **The exponential covering is periodic in each coordinate.** -/
theorem deningerExpMap_periodic (j : Fin r) (w : Fin r → ℂ) :
    deningerExpMap r (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) =
      deningerExpMap r w := by
  funext l
  show Complex.exp (w l + (2 * Real.pi * Complex.I) * (Pi.single j (1 : ℂ) : Fin r → ℂ) l) =
    Complex.exp (w l)
  rcases eq_or_ne l j with rfl | hl
  · rw [Pi.single_eq_same, mul_one]
    exact Complex.exp_periodic (w l)
  · rw [Pi.single_eq_of_ne hl, mul_zero, add_zero]

/-- A function periodic in one coordinate is invariant under integer multiples of the period in
that coordinate. -/
theorem deningerPeriodic_int {G : (Fin r → ℂ) → ℂ}
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      G (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = G w)
    (j : Fin r) (w : Fin r → ℂ) (n : ℤ) :
    G (w + ((n : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = G w := by
  have hfun : Function.Periodic
      (fun t : ℂ => G (w + t • (Pi.single j (1 : ℂ) : Fin r → ℂ)))
      (2 * Real.pi * Complex.I) := by
    intro t
    have h := hper j (w + t • (Pi.single j (1 : ℂ) : Fin r → ℂ))
    rw [add_assoc, ← add_smul] at h
    exact h
  have h := (hfun.int_mul n) 0
  simpa using h

/-- **A coordinatewise periodic function is constant on the fibres of the exponential covering.** -/
theorem deningerPeriodic_descent {G : (Fin r → ℂ) → ℂ}
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      G (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = G w)
    {w₁ w₂ : Fin r → ℂ} (h : deningerExpMap r w₁ = deningerExpMap r w₂) : G w₁ = G w₂ := by
  classical
  have hcoord : ∀ j : Fin r, ∃ n : ℤ, w₁ j = w₂ j + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro j
    have hj : Complex.exp (w₁ j) = Complex.exp (w₂ j) := congrFun h j
    exact Complex.exp_eq_exp_iff_exists_int.1 hj
  choose n hn using hcoord
  have hstep : ∀ s : Finset (Fin r),
      G (w₂ + fun l => if l ∈ s then (n l : ℂ) * (2 * Real.pi * Complex.I) else 0) = G w₂ := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have hz : (fun l : Fin r =>
            if l ∈ (∅ : Finset (Fin r)) then (n l : ℂ) * (2 * Real.pi * Complex.I) else 0) = 0 := by
          funext l
          simp
        rw [hz, add_zero]
    | @insert a s ha ih =>
        have hsplit : (fun l => if l ∈ insert a s then
              (n l : ℂ) * (2 * Real.pi * Complex.I) else 0) =
            (fun l => if l ∈ s then (n l : ℂ) * (2 * Real.pi * Complex.I) else 0) +
              ((n a : ℂ) * (2 * Real.pi * Complex.I)) •
                (Pi.single a (1 : ℂ) : Fin r → ℂ) := by
          funext l
          by_cases hl : l = a
          · subst hl
            simp [ha]
          · simp [Finset.mem_insert, hl]
        rw [hsplit, ← add_assoc, deningerPeriodic_int hper a, ih]
  have hall : w₁ = w₂ + fun l => if l ∈ (Finset.univ : Finset (Fin r)) then
      (n l : ℂ) * (2 * Real.pi * Complex.I) else 0 := by
    funext l
    simp only [Finset.mem_univ, if_true, Pi.add_apply]
    exact hn l
  rw [hall]
  exact hstep Finset.univ

end ExpCover

end RHTower
