import GaloisForLFunctions.HTGeometry.MultiJetBlowUpIndependence

/-!
# Leading and subleading blow-up data cannot decide the monomial box

When the blow-up rates separate the exponent family, the box is independent.  When they collide, the
natural repair is to refine the invariant: keep the rate, the leading value, and the subleading
value.  That repair cannot work.

Two jets can share their rate, their leading value **and** their subleading value while one pair
produces a dependent box and the other an independent one — take `P` and `P` against `P` and `P + 1`
for a function `P` that blows up at the boundary.  Adding a constant is invisible to every finite
order of the blow-up expansion, because the constant is swallowed by the vanishing scale, yet it is
exactly what turns two equal functions into two independent ones.

So the multi-jet gap is not closed by any finite-order refinement of the blow-up data; it needs an
invariant that sees the whole function, not its behaviour at the singularity.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## Two-term blow-up data -/

/-- Blow-up data recording the rate, the leading value and the subleading value of each jet. -/
def TwoTermBlowUpData {n : ℕ} (S : Set ℂ) (F : Fin n → ℂ → ℂ) (Z : Set ℂ) (d : Fin n → ℕ)
    (c c' : Fin n → ℂ) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u : ℕ → ℂ) (t : ℕ → ℂ),
    (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k, Tendsto (fun j => F k (u j) * t j ^ (d k)) atTop (𝓝 (c k))) ∧
      (∀ k, Tendsto (fun j => (F k (u j) * t j ^ (d k) - c k) / t j) atTop (𝓝 (c' k)))

/-! ## The two families -/

/-- The square of the pole model: a jet of rate two with leading value one. -/
noncomputable def poleSquare (w : ℂ) : ℂ := periodicPoleModel w ^ (2 : ℕ)

/-- The colliding pair: the same jet twice. -/
noncomputable def collidingPairEqual : Fin 2 → ℂ → ℂ := ![poleSquare, poleSquare]

/-- The colliding pair: the same jet, and the same jet shifted by a constant. -/
noncomputable def collidingPairShifted : Fin 2 → ℂ → ℂ :=
  ![poleSquare, fun w => poleSquare w + 1]

/-- The two-element monomial box: each jet to the first power. -/
noncomputable def boxExponent : Fin 2 → (Fin 2 →₀ ℕ) :=
  ![Finsupp.single 0 1, Finsupp.single 1 1]

theorem expandedMonomialFamily_boxExponent (F : Fin 2 → ℂ → ℂ) (p : Fin 2 × Fin 1) (w : ℂ) :
    expandedMonomialFamily F boxExponent 0 p w = F p.1 w := by
  rw [expandedMonomialFamily_apply]
  have hsupp : (boxExponent p.1).support = {p.1} := by
    fin_cases p <;> simp [boxExponent]
  have hval : (boxExponent p.1) p.1 = 1 := by
    fin_cases p <;> simp [boxExponent]
  rw [hsupp, Finset.prod_singleton, hval, pow_one]
  have h0 : (p.2 : ℕ) = 0 := Fin.val_eq_zero p.2
  rw [h0, pow_zero, one_mul]

/-! ## Both families carry the same data -/

theorem poleSquare_mul_sq (w : ℂ) (hw : w ∈ upperHalfPlane) :
    poleSquare w * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w) - 1) ^ (2 : ℕ) = 1 := by
  rw [poleSquare, periodicPoleModel, ← mul_pow,
    inv_mul_cancel₀ (exp_two_pi_I_mul_sub_one_ne_zero hw), one_pow]

theorem twoTermBlowUpData_collidingPairEqual :
    TwoTermBlowUpData upperHalfPlane collidingPairEqual (Set.range fun m : ℤ => (m : ℂ))
      ![2, 2] ![1, 1] ![0, 0] := by
  refine ⟨Set.infinite_range_of_injective (fun x y h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨m, rfl⟩
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach m
  refine ⟨u, fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1,
    humem, hne, hlim, hexp, ?_, ?_⟩
  · intro k
    have hone : ∀ j : ℕ,
        collidingPairEqual k (u j) *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (![2, 2] k) = 1 := by
      intro j
      fin_cases k <;>
        simpa [collidingPairEqual] using poleSquare_mul_sq (u j) (humem j)
    refine Tendsto.congr (fun j => (hone j).symm) ?_
    fin_cases k <;> simp
  · intro k
    have hzero : ∀ j : ℕ,
        (collidingPairEqual k (u j) *
            (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (![2, 2] k)
          - ![(1 : ℂ), 1] k) /
            (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) = 0 := by
      intro j
      have hone : collidingPairEqual k (u j) *
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1) ^ (![2, 2] k) = 1 := by
        fin_cases k <;>
          simpa [collidingPairEqual] using poleSquare_mul_sq (u j) (humem j)
      have hck : ![(1 : ℂ), 1] k = 1 := by fin_cases k <;> simp
      rw [hone, hck, sub_self, zero_div]
    refine Tendsto.congr (fun j => (hzero j).symm) ?_
    fin_cases k <;> simp


theorem twoTermBlowUpData_collidingPairShifted :
    TwoTermBlowUpData upperHalfPlane collidingPairShifted (Set.range fun m : ℤ => (m : ℂ))
      ![2, 2] ![1, 1] ![0, 0] := by
  refine ⟨Set.infinite_range_of_injective (fun x y h => by exact_mod_cast h), ?_⟩
  rintro ζ ⟨m, rfl⟩
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach m
  set T : ℕ → ℂ := fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1 with hT
  have hbase : ∀ j, poleSquare (u j) * T j ^ (2 : ℕ) = 1 := fun j => poleSquare_mul_sq (u j) (humem j)
  refine ⟨u, T, humem, hne, hlim, hexp, ?_, ?_⟩
  · intro k
    fin_cases k
    · refine Tendsto.congr (fun j => (hbase j).symm) ?_
      simp
    · have hval : ∀ j, collidingPairShifted 1 (u j) * T j ^ (![2, 2] (1 : Fin 2))
          = 1 + T j ^ (2 : ℕ) := by
        intro j
        have hF : collidingPairShifted 1 (u j) = poleSquare (u j) + 1 := rfl
        have hd : (![2, 2] : Fin 2 → ℕ) 1 = 2 := rfl
        rw [hF, hd, add_mul, hbase j, one_mul]
      refine Tendsto.congr (fun j => (hval j).symm) ?_
      have := (hexp.pow 2).const_add (1 : ℂ)
      simpa using this
  · intro k
    fin_cases k
    · have hz : ∀ j, (collidingPairShifted 0 (u j) * T j ^ (![2, 2] (0 : Fin 2))
          - ![(1 : ℂ), 1] 0) / T j = 0 := by
        intro j
        have hF : collidingPairShifted 0 (u j) = poleSquare (u j) := rfl
        have hd : (![2, 2] : Fin 2 → ℕ) 0 = 2 := rfl
        have hc : (![(1 : ℂ), 1] : Fin 2 → ℂ) 0 = 1 := rfl
        rw [hF, hd, hc, hbase j, sub_self, zero_div]
      refine Tendsto.congr (fun j => (hz j).symm) ?_
      simp
    · have hz : ∀ j, (collidingPairShifted 1 (u j) * T j ^ (![2, 2] (1 : Fin 2))
          - ![(1 : ℂ), 1] 1) / T j = T j := by
        intro j
        have hF : collidingPairShifted 1 (u j) = poleSquare (u j) + 1 := rfl
        have hd : (![2, 2] : Fin 2 → ℕ) 1 = 2 := rfl
        have hc : (![(1 : ℂ), 1] : Fin 2 → ℂ) 1 = 1 := rfl
        rw [hF, hd, hc, add_mul, hbase j, one_mul]
        have hsq : (1 : ℂ) + T j ^ (2 : ℕ) - 1 = T j * T j := by ring
        rw [hsq, mul_div_assoc, div_self (hne j), mul_one]
      refine Tendsto.congr (fun j => (hz j).symm) ?_
      simpa using hexp

/-! ## The boxes differ -/

/-- The square of the pole model is nonconstant on the upper half-plane: its product with the
vanishing scale is one, while the scale tends to zero. -/
theorem poleSquare_not_const (κ : ℂ) : ¬ ∀ w ∈ upperHalfPlane, poleSquare w = κ := by
  intro h
  obtain ⟨u, humem, hlim, hexp, hne⟩ := exists_vertical_approach 0
  set T : ℕ → ℂ := fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * u j) - 1 with hT
  have hone : ∀ j, κ * T j ^ (2 : ℕ) = 1 := by
    intro j
    rw [← h (u j) (humem j)]
    exact poleSquare_mul_sq (u j) (humem j)
  have hzero : Filter.Tendsto (fun j => κ * T j ^ (2 : ℕ)) Filter.atTop (𝓝 0) := by
    have := (hexp.pow 2).const_mul κ
    simpa using this
  have hone' : Filter.Tendsto (fun j => κ * T j ^ (2 : ℕ)) Filter.atTop (𝓝 1) := by
    simp only [hone]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hone' hzero)

/-- **The equal pair has a dependent box.**  Both monomials are the same function. -/
theorem not_linearIndependent_collidingPairEqual :
    ¬ LinearIndependent ℂ (fun p : Fin 2 × Fin 1 =>
        Set.restrict upperHalfPlane (expandedMonomialFamily collidingPairEqual boxExponent 0 p)) := by
  rw [Fintype.linearIndependent_iff]
  intro h
  have hcomb : ∑ p : Fin 2 × Fin 1,
      (if p.1 = 0 then (1 : ℂ) else -1) •
        Set.restrict upperHalfPlane (expandedMonomialFamily collidingPairEqual boxExponent 0 p)
      = 0 := by
    funext w
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Set.restrict_apply, Fin.sum_univ_two, Fin.sum_univ_one]
    rw [expandedMonomialFamily_boxExponent, expandedMonomialFamily_boxExponent]
    simp [collidingPairEqual]
  have := h _ hcomb (0, 0)
  simp at this

/-- **The shifted pair has an independent box.**  A constant separates the two monomials. -/
theorem linearIndependent_collidingPairShifted :
    LinearIndependent ℂ (fun p : Fin 2 × Fin 1 =>
      Set.restrict upperHalfPlane
        (expandedMonomialFamily collidingPairShifted boxExponent 0 p)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hpt : ∀ w ∈ upperHalfPlane,
      g (0, 0) * poleSquare w + g (1, 0) * (poleSquare w + 1) = 0 := by
    intro w hw
    have h := congrFun hg ⟨w, hw⟩
    rw [Fintype.sum_prod_type] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Set.restrict_apply, Fin.sum_univ_two, Fin.sum_univ_one] at h
    rw [expandedMonomialFamily_boxExponent, expandedMonomialFamily_boxExponent] at h
    simpa [collidingPairShifted] using h
  have hkey : ∀ w ∈ upperHalfPlane,
      (g (0, 0) + g (1, 0)) * poleSquare w + g (1, 0) = 0 := by
    intro w hw
    have h := hpt w hw
    linear_combination h
  have hsum : g (0, 0) + g (1, 0) = 0 := by
    by_contra hne0
    refine poleSquare_not_const (-g (1, 0) / (g (0, 0) + g (1, 0))) ?_
    intro w hw
    have h := hkey w hw
    field_simp
    linear_combination h
  have hone : g (1, 0) = 0 := by
    obtain ⟨u, humem, -, -, -⟩ := exists_vertical_approach 0
    have h := hkey (u 0) (humem 0)
    rw [hsum, zero_mul, zero_add] at h
    exact h
  have hzero : g (0, 0) = 0 := by
    have hz : g (0, 0) = -g (1, 0) := by linear_combination hsum
    rw [hz, hone, neg_zero]
  intro p
  fin_cases p
  · exact hzero
  · exact hone

/-! ## The no-go -/

/-- **Leading and subleading blow-up data cannot decide the monomial box.**  Two jet families share
their rates, leading values and subleading values, yet one box is dependent and the other is
independent. -/
theorem twoTermBlowUpData_cannot_decide_box :
    TwoTermBlowUpData upperHalfPlane collidingPairEqual (Set.range fun m : ℤ => (m : ℂ))
        ![2, 2] ![1, 1] ![0, 0] ∧
      TwoTermBlowUpData upperHalfPlane collidingPairShifted (Set.range fun m : ℤ => (m : ℂ))
        ![2, 2] ![1, 1] ![0, 0] ∧
      ¬ LinearIndependent ℂ (fun p : Fin 2 × Fin 1 =>
          Set.restrict upperHalfPlane
            (expandedMonomialFamily collidingPairEqual boxExponent 0 p)) ∧
      LinearIndependent ℂ (fun p : Fin 2 × Fin 1 =>
        Set.restrict upperHalfPlane
          (expandedMonomialFamily collidingPairShifted boxExponent 0 p)) :=
  ⟨twoTermBlowUpData_collidingPairEqual, twoTermBlowUpData_collidingPairShifted,
    not_linearIndependent_collidingPairEqual, linearIndependent_collidingPairShifted⟩

end GaloisForLFunctions.HTGeometry
