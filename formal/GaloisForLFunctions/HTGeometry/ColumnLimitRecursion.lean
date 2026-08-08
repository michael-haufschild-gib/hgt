import GaloisForLFunctions.HTGeometry.TopColumnLimits

/-!
# The lower columns of the logarithmic Jacobian at infinity

Away from the newest coordinate the shifted operator degenerates, as that coordinate goes to
infinity, to the same operator one level down plus a single correction carried by the newest
column's residue:

`lim (S u)_k = (S' L)_k + (Q_k'/Q_k)·(∏_{i<m}Q_i)·(lead v_m)·res`,   `res = lim X_m·u_m`.

The three ingredients are that everything below the newest level is free of the newest coordinate,
that the product law carries values at infinity — its defect is a degree statement, already proved —
and that the newest jet contributes `∏_{i<m}Q_i·(lead v_m)·res` because `v_m(X_m)/X_m → lead v_m`.

This is the step that turns the peel into an induction: the level drops, but the starting vector
acquires the correction.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Q v : ℕ → Polynomial ℂ}

/-! ## Everything below the newest level is free of it -/

/-- **The low subalgebra of a lower level is free of the newest coordinate.** -/
theorem topFree_of_mem_lowSub {m m' : ℕ} (hm : m' < m) {f : CascadeField}
    (hf : f ∈ lowSub Q v m') : TopFree m f := by
  classical
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
      rcases hx with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩
      · refine topFree_algebraMap ?_
        rw [MvPolynomial.degreeOf_X, if_neg (by omega : ¬ m = j)]
      · exact topFree_inv_fact (by omega) (Q j)
      · exact topFree_inv_fact (by omega) (v j)
  | algebraMap c =>
      have hc : (algebraMap ℂ CascadeField) c
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.C c) := rfl
      rw [hc]
      exact topFree_algebraMap (MvPolynomial.degreeOf_C c m)
  | add x y _ _ ihx ihy => exact TopFree.add ihx ihy
  | mul x y _ _ ihx ihy => exact TopFree.mul ihx ihy

/-- The jet responses below the newest level are free of the newest coordinate. -/
theorem topFree_jetResponse {m k l : ℕ} (hl : l < m) : TopFree m (jetResponse (Q := Q) v k l) :=
  topFree_of_mem_lowSub hl (fpderiv_mem_lowSub Q v (prodJet_mem_lowSub Q v (le_refl l)))

theorem topFree_algebraMap_complex (m : ℕ) (c : ℂ) :
    TopFree m (algebraMap ℂ CascadeField c) := by
  have hc : (algebraMap ℂ CascadeField) c
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.C c) := rfl
  rw [hc]
  exact topFree_algebraMap (MvPolynomial.degreeOf_C c m)

/-! ## The product law carries values at infinity -/

/-- **The product law carries a value at infinity.** -/
theorem TopLim.prodDerivation {m : ℕ} {u a : CascadeField} (hv : (v m).natDegree ≤ 1)
    (hmem : u - a ∈ lowSub Q v m) (h : TopLim m u a) :
    TopLim m (prodDerivation Q v u) (prodDerivation Q v a) := by
  rw [TopLim, ← map_sub]
  exact TopDegLE.prodDerivation hv hmem h

/-! ## The newest jet against the newest entry -/

theorem natDegree_le_one_of_linear {p : Polynomial ℂ} {α β : ℂ}
    (hp : p = Polynomial.C α * Polynomial.X + Polynomial.C β) : p.natDegree ≤ 1 := by
  rw [hp]
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · refine le_trans Polynomial.natDegree_mul_le ?_
    simp
  · simp

/-- **The newest jet times an entry of the newest column.**  Since `v_m(X_m)/X_m → lead v_m`, the
product picks up the residue of that entry. -/
theorem topLim_prodJet_mul {m : ℕ} {α β : ℂ} {u res : CascadeField}
    (hv : v m = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hresfree : TopFree m res) (hu : TopDegLE m (-1) u)
    (hres : TopLim m (fx m * u) res) :
    TopLim m (prodJet Q v m * u)
      (prodHead Q m * (algebraMap ℂ CascadeField α * res)) := by
  have hsplit : prodJet Q v m * u
      = prodHead Q m * (algebraMap ℂ CascadeField α * (fx m * u)
          + algebraMap ℂ CascadeField β * u) := by
    rw [prodJet_eq, fact_linear v hv]
    ring
  rw [hsplit]
  have hαfree : TopFree m (algebraMap ℂ CascadeField α) := topFree_algebraMap_complex m α
  have hβfree : TopFree m (algebraMap ℂ CascadeField β) := topFree_algebraMap_complex m β
  have hhead : TopFree m (prodHead (Q := Q) m) := topFree_prodHead (le_refl m)
  have h1 : TopLim m (algebraMap ℂ CascadeField α * (fx m * u))
      (algebraMap ℂ CascadeField α * res) :=
    TopLim.mul hαfree hresfree topLim_const hres
  have hu0 : TopLim m u 0 := by
    rw [TopLim, sub_zero]
    exact hu
  have h2 : TopLim m (algebraMap ℂ CascadeField β * u)
      (algebraMap ℂ CascadeField β * 0) :=
    TopLim.mul hβfree (topFree_zero m) topLim_const hu0
  have hsum := TopLim.add h1 h2
  rw [mul_zero, add_zero] at hsum
  exact TopLim.mul hhead (TopFree.mul hαfree hresfree) topLim_const hsum

/-! ## The recursion of a lower column -/

/-- **The lower columns at infinity.**  The level drops and the starting vector picks up the
residue correction. -/
theorem topLim_gradShift_lower {m' k : ℕ} (hk : k ≤ m') {α β : ℂ} (hQ : ∀ j, Q j ≠ 0)
    (hv : v (m' + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    {u L : ℕ → CascadeField} {res : CascadeField}
    (hsub : ∀ l, u l - L l ∈ lowSub Q v (m' + 1))
    (hLfree : ∀ l, TopFree (m' + 1) (L l))
    (hlim : ∀ l, TopLim (m' + 1) (u l) (L l))
    (hresfree : TopFree (m' + 1) res)
    (hutop : TopDegLE (m' + 1) (-1) (u (m' + 1)))
    (hres : TopLim (m' + 1) (fx (m' + 1) * u (m' + 1)) res) :
    TopLim (m' + 1) (gradShift Q v (m' + 1) u k)
      (gradShift Q v m' L k
        + logFactor (Q k) k
          * (prodHead Q (m' + 1) * (algebraMap ℂ CascadeField α * res))) := by
  have hvdeg : (v (m' + 1)).natDegree ≤ 1 := natDegree_le_one_of_linear hv
  have hsplit : gradShift Q v (m' + 1) u k
      = (prodDerivation Q v (u k)
          + ∑ l ∈ Finset.range (m' + 1), jetResponse Q v k l * u l)
        + jetResponse Q v k (m' + 1) * u (m' + 1) := by
    rw [gradShift, Finset.sum_range_succ]
    ring
  rw [hsplit, gradShift]
  refine TopLim.add (TopLim.add ?_ ?_) ?_
  · exact TopLim.prodDerivation hvdeg (hsub k) (hlim k)
  · refine topLim_sum _ _ _ fun l hl => ?_
    have hlm : l < m' + 1 := Finset.mem_range.mp hl
    exact TopLim.mul (topFree_jetResponse hlm) (hLfree l) topLim_const (hlim l)
  · rw [jetResponse_of_gt v hQ (show k < m' + 1 by omega), mul_assoc]
    refine TopLim.mul (topFree_logFactor (by omega) (Q k)) ?_ topLim_const ?_
    · exact TopFree.mul (topFree_prodHead (le_refl (m' + 1)))
        (TopFree.mul (topFree_algebraMap_complex (m' + 1) α) hresfree)
    · exact topLim_prodJet_mul hv hresfree hutop hres

end GaloisForLFunctions.HTGeometry
