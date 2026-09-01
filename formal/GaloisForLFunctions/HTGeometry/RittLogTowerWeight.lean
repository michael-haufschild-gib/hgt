import GaloisForLFunctions.HTGeometry.RittLogTowerMvSubstitution

/-!
# The weight filtration of the affine tower

Give the variable indexing the `j`-th jet the weight `j + 1`.  The tower substitution moves each
variable to a base multiple of itself of the same weight plus terms of strictly smaller weight, so
it preserves the weight filtration and acts on the top layer by the scalar `ρ^{-W}` together with
the base map on coefficients.

The two predicates below record the filtration directly on supports; that is more convenient than
`weightedTotalDegree`, because the strict layer has to be available for the zero polynomial as
well.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The weight of the variable indexing the `j`-th jet. -/
def jetWeight (n : ℕ) : Fin n → ℕ := fun j => (j : ℕ) + 1

/-- Every monomial of `F` has weight at most `d`. -/
def WLe (n : ℕ) (F : MvPolynomial (Fin n) K) (d : ℕ) : Prop :=
  ∀ e ∈ F.support, Finsupp.weight (jetWeight n) e ≤ d

/-- Every monomial of `F` has weight less than `d`. -/
def WLt (n : ℕ) (F : MvPolynomial (Fin n) K) (d : ℕ) : Prop :=
  ∀ e ∈ F.support, Finsupp.weight (jetWeight n) e < d

variable {n : ℕ}

theorem WLe.mono {F : MvPolynomial (Fin n) K} {d d' : ℕ} (h : WLe n F d) (hd : d ≤ d') :
    WLe n F d' := fun e he => le_trans (h e he) hd

theorem WLt.mono {F : MvPolynomial (Fin n) K} {d d' : ℕ} (h : WLt n F d) (hd : d ≤ d') :
    WLt n F d' := fun e he => lt_of_lt_of_le (h e he) hd

theorem WLt.wLe {F : MvPolynomial (Fin n) K} {d : ℕ} (h : WLt n F d) : WLe n F d :=
  fun e he => le_of_lt (h e he)

theorem wLe_zero (d : ℕ) : WLe n (0 : MvPolynomial (Fin n) K) d := by
  intro e he
  simp at he

theorem wLt_zero (d : ℕ) : WLt n (0 : MvPolynomial (Fin n) K) d := by
  intro e he
  simp at he

theorem wLe_C (a : K) (d : ℕ) : WLe n (C a : MvPolynomial (Fin n) K) d := by
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at he
  by_cases h : (0 : Fin n →₀ ℕ) = e
  · rw [← h]
    simp
  · rw [if_neg h] at he
    exact absurd rfl he

theorem wLe_X (j : Fin n) : WLe n (X j : MvPolynomial (Fin n) K) (jetWeight n j) := by
  intro e he
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X'] at he
  by_cases h : Finsupp.single j 1 = e
  · rw [← h, Finsupp.weight_single]
    simp
  · rw [if_neg h] at he
    exact absurd rfl he

theorem WLe.add {F G : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLe n F d) (hG : WLe n G d) :
    WLe n (F + G) d := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hF e h
  · exact hG e h

theorem WLt.add {F G : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLt n F d) (hG : WLt n G d) :
    WLt n (F + G) d := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hF e h
  · exact hG e h

theorem WLe.neg {F : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLe n F d) : WLe n (-F) d := by
  intro e he
  exact hF e (by simpa using he)

theorem WLt.neg {F : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLt n F d) : WLt n (-F) d := by
  intro e he
  exact hF e (by simpa using he)

theorem WLe.sub {F G : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLe n F d) (hG : WLe n G d) :
    WLe n (F - G) d := by
  rw [sub_eq_add_neg]
  exact hF.add hG.neg

theorem WLt.sub {F G : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLt n F d) (hG : WLt n G d) :
    WLt n (F - G) d := by
  rw [sub_eq_add_neg]
  exact hF.add hG.neg

theorem WLe.mul {F G : MvPolynomial (Fin n) K} {d d' : ℕ} (hF : WLe n F d) (hG : WLe n G d') :
    WLe n (F * G) (d + d') := by
  intro e he
  obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
  rw [map_add]
  exact add_le_add (hF a ha) (hG c hc)

theorem WLt.mul {F G : MvPolynomial (Fin n) K} {d d' : ℕ} (hF : WLt n F d) (hG : WLe n G d') :
    WLt n (F * G) (d + d') := by
  intro e he
  obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
  rw [map_add]
  exact add_lt_add_of_lt_of_le (hF a ha) (hG c hc)

theorem WLe.pow {F : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLe n F d) :
    ∀ m : ℕ, WLe n (F ^ m) (m * d)
  | 0 => by
      simpa using wLe_C (n := n) (1 : K) 0
  | (m + 1) => by
      have h := (hF.pow m).mul hF
      have hrw : m * d + d = (m + 1) * d := by ring
      rw [pow_succ]
      exact hrw ▸ h

end RittFrame

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

theorem WLe.mul_wLt {F G : MvPolynomial (Fin n) K} {d d' : ℕ} (hF : WLe n F d)
    (hG : WLt n G d') : WLt n (F * G) (d + d') := by
  rw [mul_comm, add_comm]
  exact hG.mul hF

/-- The diagonal part of the tower substitution. -/
noncomputable def towerDiag (Fr : RittFrame K L) (n : ℕ) (j : Fin n) : MvPolynomial (Fin n) K :=
  C ((Fr.ρ ^ ((j : ℕ) + 1))⁻¹) * X j

/-- The diagonal substitution. -/
noncomputable def towerDiagShift (Fr : RittFrame K L) (n : ℕ) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom ((C : K →+* MvPolynomial (Fin n) K).comp Fr.ψ) (Fr.towerDiag n)

theorem wLe_towerDiag (Fr : RittFrame K L) (j : Fin n) :
    WLe n (Fr.towerDiag n j) (jetWeight n j) := by
  have h := (wLe_C (n := n) ((Fr.ρ ^ ((j : ℕ) + 1))⁻¹) 0).mul (wLe_X (n := n) j)
  simpa using h

theorem wLe_towerSub (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLe n (Fr.towerSub b n j) (jetWeight n j) := by
  refine WLe.add (fun e he => ?_) ((wLe_C (n := n) (Fr.logConst b (j : ℕ)) _))
  classical
  have hterm : ∀ i : Fin n, WLe n (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i : MvPolynomial (Fin n) K)
      (jetWeight n j) := by
    intro i
    rcases lt_or_ge (j : ℕ) (i : ℕ) with hij | hij
    · rw [Fr.logCoeff_eq_zero_of_lt _ _ hij, map_zero, zero_mul]
      exact wLe_zero _
    · have h := (wLe_C (n := n) (Fr.logCoeff (j : ℕ) (i : ℕ)) 0).mul (wLe_X (n := n) i)
      refine (by simpa using h).mono ?_
      simp only [jetWeight]
      omega
  refine Finset.sum_induction _ (fun F => WLe n F (jetWeight n j)) (fun _ _ => WLe.add)
    (wLe_zero _) (fun i _ => hterm i) e he

theorem wLt_towerSub_sub_towerDiag (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt n (Fr.towerSub b n j - Fr.towerDiag n j) (jetWeight n j) := by
  classical
  have hsplit : Fr.towerSub b n j - Fr.towerDiag n j
      = (∑ i ∈ Finset.univ.erase j, C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
        + C (Fr.logConst b (j : ℕ)) := by
    rw [towerSub, towerDiag, Fr.logCoeff_diag (j : ℕ)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    ring
  rw [hsplit]
  refine WLt.add (fun e he => ?_) (fun e he => ?_)
  · have hterm : ∀ i ∈ Finset.univ.erase j,
        WLt n (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i : MvPolynomial (Fin n) K)
          (jetWeight n j) := by
      intro i hi
      have hne : i ≠ j := Finset.ne_of_mem_erase hi
      rcases lt_or_ge (j : ℕ) (i : ℕ) with hij | hij
      · rw [Fr.logCoeff_eq_zero_of_lt _ _ hij, map_zero, zero_mul]
        exact wLt_zero _
      · have hlt : (i : ℕ) < (j : ℕ) := by
          rcases lt_or_eq_of_le hij with h | h
          · exact h
          · exact absurd (Fin.ext h) hne
        have h := (wLe_C (n := n) (Fr.logCoeff (j : ℕ) (i : ℕ)) 0).mul (wLe_X (n := n) i)
        refine ((by simpa using h : WLe n _ (jetWeight n i)).mono (le_refl _)).mono ?_ |>.imp ?_
        · exact le_refl _
        · exact fun _ => id
    exact Finset.sum_induction _ (fun F => WLt n F (jetWeight n j)) (fun _ _ => WLt.add)
      (wLt_zero _) hterm e he
  · exact ((wLe_C (n := n) (Fr.logConst b (j : ℕ)) 0).mono (Nat.zero_le _)) e he |>.trans_lt
      (by simp only [jetWeight]; omega)

end RittFrame

end GaloisForLFunctions.HTGeometry
