import GaloisForLFunctions.HTGeometry.EliminationOrderDescent

/-!
# A family whose orders collide, decided

Every realization so far had separated orders, so the elimination induction never ran.  Here is a
family that genuinely collides: two members of the same blow-up order whose difference drops the
order.  It is the model of the configuration that defeats every local invariant — `L²` against `L'`
for a Cauchy transform — with the remainder made exact by the pole model.

The span carries a valuation: a combination has order two unless its two coefficients cancel, in
which case it has order one.  Both the order and the leading coefficient are independent of the
point, so the elimination search runs and decides the box.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem periodicPoleModel_mul {w : ℂ} (hw : w ∈ upperHalfPlane) :
    periodicPoleModel w * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) - 1) = 1 :=
  inv_mul_cancel₀ (exp_two_pi_I_mul_sub_one_ne_zero hw)

/-- Two members of order two whose difference is the pole model itself, of order one. -/
noncomputable def collisionPair : Fin 2 → ℂ → ℂ :=
  ![poleSquare, fun w => poleSquare w + periodicPoleModel w]

/-- The order of a combination: two, unless the coefficients cancel the square. -/
noncomputable def collisionOrd : (Fin 2 → ℂ) → ℕ :=
  fun c => if c 0 + c 1 = 0 then 1 else 2

/-- The leading value of a combination. -/
noncomputable def collisionLead : (Fin 2 → ℂ) → ℂ :=
  fun c => if c 0 + c 1 = 0 then c 1 else c 0 + c 1

theorem collisionLead_ne_zero {c : Fin 2 → ℂ} (hc : c ≠ 0) : collisionLead c ≠ 0 := by
  rw [collisionLead]
  by_cases h : c 0 + c 1 = 0
  · rw [if_pos h]
    intro h1
    refine hc (funext fun j => ?_)
    have h0 : c 0 = 0 := by
      have : c 0 = -c 1 := by linear_combination h
      rw [this, h1, neg_zero]
    fin_cases j
    · exact h0
    · exact h1
  · rw [if_neg h]
    exact h

/-- **The colliding family carries a uniform valuation.**  Every nonzero combination is graded, with
order and leading value independent of the point. -/
theorem uniformSpanValuation_collisionPair :
    UniformSpanValuation upperHalfPlane collisionPair (Set.range fun m : ℤ => (m : ℂ))
      collisionOrd collisionLead := by
  refine ⟨Set.infinite_range_of_injective (fun x y h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨m, rfl⟩
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach m
  refine ⟨u, fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1,
    humem, hlim, hexp, ?_⟩
  intro c hc
  refine ⟨collisionLead_ne_zero hc, ?_⟩
  by_cases h : c 0 + c 1 = 0
  · have hord : collisionOrd c = 1 := by rw [collisionOrd, if_pos h]
    have hlead : collisionLead c = c 1 := by rw [collisionLead, if_pos h]
    rw [hord, hlead]
    have hval : ∀ j, (∑ a : Fin 2, c a * collisionPair a (u j)) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (1 : ℕ) = c 1 := by
      intro j
      have hpm := periodicPoleModel_mul (humem j)
      rw [Fin.sum_univ_two, pow_one]
      show (c 0 * poleSquare (u j) + c 1 * (poleSquare (u j) + periodicPoleModel (u j))) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) = c 1
      rw [poleSquare]
      have hc0 : c 0 = -c 1 := by linear_combination h
      rw [hc0]
      linear_combination c 1 * hpm
    exact tendsto_const_nhds.congr fun j => (hval j).symm
  · have hord : collisionOrd c = 2 := by rw [collisionOrd, if_neg h]
    have hlead : collisionLead c = c 0 + c 1 := by rw [collisionLead, if_neg h]
    rw [hord, hlead]
    have hval : ∀ j, (∑ a : Fin 2, c a * collisionPair a (u j)) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (2 : ℕ)
        = (c 0 + c 1) + c 1 * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) := by
      intro j
      have hpm := periodicPoleModel_mul (humem j)
      rw [Fin.sum_univ_two]
      show (c 0 * poleSquare (u j) + c 1 * (poleSquare (u j) + periodicPoleModel (u j))) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (2 : ℕ)
        = (c 0 + c 1) + c 1 * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1)
      rw [poleSquare]
      linear_combination
        ((c 0 + c 1) * (periodicPoleModel (u j) *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) + 1) + c 1 *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1)) * hpm
    refine Tendsto.congr (fun j => (hval j).symm) ?_
    have := (hexp.const_mul (c 1)).const_add (c 0 + c 1)
    simpa using this

/-- **The collision is real.**  Both members of the family have order two, so the graded law does
not apply to the family as given: the elimination step is not optional here. -/
theorem collisionOrd_identity_not_injective :
    ¬ Function.Injective (fun a : Fin 2 => collisionOrd ((1 : Matrix (Fin 2) (Fin 2) ℂ) a)) := by
  intro h
  have h0 : collisionOrd ((1 : Matrix (Fin 2) (Fin 2) ℂ) 0) = 2 := by
    rw [collisionOrd, if_neg]
    norm_num [Matrix.one_apply]
  have h1 : collisionOrd ((1 : Matrix (Fin 2) (Fin 2) ℂ) 1) = 2 := by
    rw [collisionOrd, if_neg]
    norm_num [Matrix.one_apply]
  exact Fin.zero_ne_one (h (h0.trans h1.symm))

/-- **The colliding box is independent.**  Its orders collide, so no graded criterion applies
directly; the elimination search separates them and decides it. -/
theorem linearIndependent_degreeBox_collisionPair (q : ℕ) :
    LinearIndependent ℂ (fun p : Fin 2 × Fin (q + 1) =>
      Set.restrict upperHalfPlane (fun w => w ^ (p.2 : ℕ) * collisionPair p.1 w)) :=
  linearIndependent_degreeBox_of_uniformSpanValuation uniformSpanValuation_collisionPair

end GaloisForLFunctions.HTGeometry
