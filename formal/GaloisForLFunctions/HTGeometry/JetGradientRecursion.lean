import GaloisForLFunctions.HTGeometry.TopCoordinateCommutator
import GaloisForLFunctions.HTGeometry.LogJetJacobian

/-!
# The logarithmic Jacobian is a single orbit

Every coordinate commutes with the product law up to a *finite* first-order correction: only the
jets of level at least the coordinate respond to it, and they respond by

`∂_k (δ X_l) = 0` for `l < k`,  `= A_k` for `l = k`,  `= (Q_k'/Q_k)(X_k)·δ X_l` for `l > k`.

The difference of `∂_k ∘ δ` and `δ ∘ ∂_k` is a commutator of derivations, hence a derivation, so it
is determined by its values on the coordinates.  Therefore the full gradient vector obeys the exact
recursion

`∂ (δ F) = δ (∂ F) + M · ∂ F`,   `M` upper triangular with diagonal `A_k`.

Consequently the whole logarithmic Jacobian is one orbit: its rows are the iterates
`w, Sw, S²w, …, Sⁿw` of the single operator `S : u ↦ δu + Mu` applied to the border row `w` of
logarithmic derivatives.  The nonvanishing of the determinant at every height is therefore a
statement about one operator and one vector, not about a family of unrelated rows.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-! ## The derivative of a logarithmic factor, for any derivation -/

/-- **Any derivation differentiates a logarithmic factor into a Wronskian**, weighted by its value
on the coordinate. -/
theorem derivation_logFactor (D : Derivation ℂ CascadeField CascadeField) (p : Polynomial ℂ)
    (k : ℕ) :
    D (logFactor p k) = fact (scaledLogWronskian p 1) k * D (fx k) / fact p k ^ (2 : ℕ) := by
  rcases eq_or_ne p 0 with rfl | hp
  · have h0 : fact (0 : Polynomial ℂ) k = 0 := by
      rw [fact, univFactor]
      simp
    rw [logFactor, h0]
    simp
  · have hne : fact p k ≠ 0 := fact_ne_zero hp k
    rw [logFactor, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      derivation_fact, derivation_fact]
    simp only [smul_eq_mul, scaledLogWronskian_one_right, fact_sub, fact_mul, fact_pow]
    field_simp
    ring

/-- The coordinate derivative of its own logarithmic factor. -/
theorem fpderiv_logFactor_self (p : Polynomial ℂ) (k : ℕ) :
    fpderiv k (logFactor p k) = fact (scaledLogWronskian p 1) k / fact p k ^ (2 : ℕ) := by
  rw [derivation_logFactor, fpderiv_fx_self, mul_one]

/-- A logarithmic factor at another coordinate is invisible. -/
theorem fpderiv_logFactor_of_ne {p : Polynomial ℂ} {k l : ℕ} (h : l ≠ k) :
    fpderiv k (logFactor p l) = 0 := by
  rw [derivation_logFactor, fpderiv_fx_of_ne h]
  simp

/-! ## The jet responses -/

/-- The response of the jet at level `l` to the coordinate `k`. -/
noncomputable def jetResponse (Q v : ℕ → Polynomial ℂ) (k l : ℕ) : CascadeField :=
  fpderiv k (prodJet Q v l)

theorem jetResponse_eq (k l : ℕ) : jetResponse Q v k l = fpderiv k (prodJet Q v l) := rfl

/-- Jets below the coordinate do not respond. -/
theorem jetResponse_of_lt {k l : ℕ} (h : l < k) : jetResponse Q v k l = 0 :=
  fpderiv_eq_zero_of_mem_lowSub Q v h (prodJet_mem_lowSub Q v (le_refl l))

/-- The jet at the coordinate responds by the terminal factor's derivative. -/
theorem jetResponse_self (k : ℕ) :
    jetResponse Q v k k = prodHead Q k * fact (v k).derivative k := topResponse_eq Q v k

/-- Jets above the coordinate respond logarithmically. -/
theorem jetResponse_of_gt {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ) (hQ : ∀ j, Q j ≠ 0)
    {k l : ℕ} (h : k < l) :
    jetResponse Q v k l = logFactor (Q k) k * prodJet Q v l := by
  rw [jetResponse, prodJet_eq, Derivation.leibniz, fpderiv_prodHead_eq hQ h,
    fpderiv_fact_of_ne (by omega : l ≠ k)]
  simp only [smul_eq_mul, mul_zero, zero_add]
  ring

/-! ## The mixing correction -/

/-- The first-order correction: the responses of all jets in range, weighted by the corresponding
coordinate derivatives. -/
noncomputable def jetMix (Q v : ℕ → Polynomial ℂ) (m k : ℕ) (F : CascadeField) : CascadeField :=
  ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * fpderiv l F

theorem jetMix_add (m k : ℕ) (a b : CascadeField) :
    jetMix Q v m k (a + b) = jetMix Q v m k a + jetMix Q v m k b := by
  rw [jetMix, jetMix, jetMix, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_add]
  ring

theorem jetMix_mul (m k : ℕ) (a b : CascadeField) :
    jetMix Q v m k (a * b) = a * jetMix Q v m k b + b * jetMix Q v m k a := by
  rw [jetMix, jetMix, jetMix, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem jetMix_algebraMap_mul (m k : ℕ) (c : ℂ) (a : CascadeField) :
    jetMix Q v m k (algebraMap ℂ CascadeField c * a)
      = algebraMap ℂ CascadeField c * jetMix Q v m k a := by
  rw [jetMix, jetMix, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : fpderiv l (algebraMap ℂ CascadeField c * a)
      = algebraMap ℂ CascadeField c * fpderiv l a := by
    rw [Derivation.leibniz, (fpderiv l).map_algebraMap]
    simp
  rw [h]
  ring

/-! ## The mixed commutator is a derivation, and it vanishes -/

/-- The commutator of a coordinate derivation with the product law, corrected by the mixing. -/
noncomputable def mixCommutatorLin (Q v : ℕ → Polynomial ℂ) (m k : ℕ) :
    CascadeField →ₗ[ℂ] CascadeField where
  toFun F := fpderiv k (prodDerivation Q v F) - prodDerivation Q v (fpderiv k F)
      - jetMix Q v m k F
  map_add' x y := by
    simp only [map_add, jetMix_add]
    ring
  map_smul' c x := by
    have key : ∀ (D : Derivation ℂ CascadeField CascadeField) (y : CascadeField),
        D (algebraMap ℂ CascadeField c * y) = algebraMap ℂ CascadeField c * D y := by
      intro D y
      rw [Derivation.leibniz, D.map_algebraMap]
      simp
    simp only [Algebra.smul_def, RingHom.id_apply]
    rw [key (prodDerivation Q v) x, key (fpderiv k) x,
      key (fpderiv k) (prodDerivation Q v x), key (prodDerivation Q v) (fpderiv k x),
      jetMix_algebraMap_mul]
    ring

theorem mixCommutatorLin_apply (m k : ℕ) (F : CascadeField) :
    mixCommutatorLin Q v m k F
      = fpderiv k (prodDerivation Q v F) - prodDerivation Q v (fpderiv k F)
        - jetMix Q v m k F := rfl

/-- **The mixed commutator is a derivation.** -/
noncomputable def mixCommutator (Q v : ℕ → Polynomial ℂ) (m k : ℕ) :
    Derivation ℂ CascadeField CascadeField :=
  Derivation.mk' (mixCommutatorLin Q v m k) (by
    intro a b
    simp only [mixCommutatorLin_apply, smul_eq_mul, Derivation.leibniz, map_add, smul_eq_mul,
      jetMix_mul]
    ring)

theorem mixCommutator_apply (m k : ℕ) (F : CascadeField) :
    mixCommutator Q v m k F
      = fpderiv k (prodDerivation Q v F) - prodDerivation Q v (fpderiv k F)
        - jetMix Q v m k F := rfl

theorem mixCommutator_fx {m k j : ℕ} (hj : j ≤ m) : mixCommutator Q v m k (fx j) = 0 := by
  classical
  have hD : prodDerivation Q v (fpderiv k (fx j)) = 0 := by
    rcases eq_or_ne j k with rfl | hne
    · rw [fpderiv_fx_self]
      simp
    · rw [fpderiv_fx_of_ne hne]
      simp
  have hmix : jetMix Q v m k (fx j) = jetResponse Q v k j := by
    rw [jetMix, Finset.sum_eq_single j]
    · rw [fpderiv_fx_self, mul_one]
    · intro l _ hlj
      rw [fpderiv_fx_of_ne (fun h => hlj h.symm), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega : j < m + 1)) hnot
  rw [mixCommutator_apply, prodDerivation_fx, hD, hmix, ← jetResponse]
  ring

theorem mixCommutator_fact {m k j : ℕ} (hj : j ≤ m) (p : Polynomial ℂ) :
    mixCommutator Q v m k (fact p j) = 0 := by
  rw [derivation_fact, mixCommutator_fx Q v hj]
  simp

theorem mixCommutator_inv_fact {m k j : ℕ} (hj : j ≤ m) (p : Polynomial ℂ) :
    mixCommutator Q v m k ((fact p j)⁻¹) = 0 := by
  rw [Derivation.leibniz_inv, mixCommutator_fact Q v hj]
  simp

/-- **The mixed commutator vanishes on the low subalgebra.** -/
theorem mixCommutator_eq_zero {m k : ℕ} {F : CascadeField} (h : F ∈ lowSub Q v m) :
    mixCommutator Q v m k F = 0 := by
  have hgen : Set.EqOn (⇑(mixCommutator Q v m k))
      (⇑(0 : Derivation ℂ CascadeField CascadeField))
      ({z : CascadeField | ∃ j, j ≤ m ∧ z = fx j}
        ∪ {z : CascadeField | ∃ j, j ≤ m ∧ z = (fact (Q j) j)⁻¹}
        ∪ {z : CascadeField | ∃ j, j ≤ m ∧ z = (fact (v j) j)⁻¹}) := by
    rintro x ((⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨j, hj, rfl⟩)
    · simpa using mixCommutator_fx Q v hj
    · simpa using mixCommutator_inv_fact Q v hj (Q j)
    · simpa using mixCommutator_inv_fact Q v hj (v j)
  have hmem : F ∈ (lowSub Q v m : Set CascadeField) := h
  rw [lowSub] at hmem
  simpa using Derivation.eqOn_adjoin hgen hmem

/-- **The exact mixed commutation law**, at every coordinate. -/
theorem fpderiv_prodDerivation_mixed {m k : ℕ} {F : CascadeField} (h : F ∈ lowSub Q v m) :
    fpderiv k (prodDerivation Q v F)
      = prodDerivation Q v (fpderiv k F) + jetMix Q v m k F := by
  have h0 := mixCommutator_eq_zero Q v (k := k) h
  rw [mixCommutator_apply] at h0
  linear_combination h0

/-! ## The gradient recursion -/

/-- The operator the product law induces on gradient vectors. -/
noncomputable def gradShift (Q v : ℕ → Polynomial ℂ) (m : ℕ) (u : ℕ → CascadeField) :
    ℕ → CascadeField :=
  fun k => prodDerivation Q v (u k) + ∑ l ∈ Finset.range (m + 1), jetResponse Q v k l * u l

/-- **The gradient of a derivative is the shifted gradient.** -/
theorem gradient_prodDerivation_eq {m : ℕ} {F : CascadeField} (h : F ∈ lowSub Q v m) :
    (fun l => fpderiv l (prodDerivation Q v F))
      = gradShift Q v m (fun l => fpderiv l F) := by
  funext k
  exact fpderiv_prodDerivation_mixed Q v h

/-- **The gradient of an iterate is an iterate of the shifted operator.** -/
theorem gradient_iterate_eq {m : ℕ} (r : ℕ) {F : CascadeField} (h : F ∈ lowSub Q v m) :
    (fun l => fpderiv l (((prodDerivation Q v : CascadeField → CascadeField)^[r]) F))
      = ((gradShift Q v m)^[r]) (fun l => fpderiv l F) := by
  induction r generalizing F with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, ih (prodDerivation_mem_lowSub Q v h),
        gradient_prodDerivation_eq Q v h, Function.iterate_succ_apply]

/-! ## The border row generates everything -/

/-- The border row: the logarithmic derivatives, truncated to the levels in range. -/
noncomputable def logBorder (Q : ℕ → Polynomial ℂ) (m : ℕ) : ℕ → CascadeField :=
  fun l => if l ≤ m then logFactor (Q l) l else 0

/-- **The gradient of the logarithmic sum is the shifted border row.**  The whole matrix therefore
starts from one vector. -/
theorem gradient_logSum_eq {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ) (m : ℕ) :
    (fun l => fpderiv l (logSum Q v (m + 1))) = gradShift Q v m (logBorder Q m) := by
  classical
  funext k
  rw [gradShift, logSum, map_sum]
  have hterm : ∀ l ∈ Finset.range (m + 1),
      fpderiv k (logFactor (Q l) l * prodJet Q v l)
        = (if l = k then prodDerivation Q v (logBorder Q m k) else 0)
          + jetResponse Q v k l * logBorder Q m l := by
    intro l hl
    have hlm : l ≤ m := by
      have := Finset.mem_range.mp hl
      omega
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    by_cases hlk : l = k
    · subst hlk
      rw [if_pos rfl, fpderiv_logFactor_self, logBorder, if_pos hlm,
        prodDerivation_logFactor Q v (Q l) l]
      simp only [jetResponse_eq]
      ring
    · rw [if_neg hlk, fpderiv_logFactor_of_ne hlk, logBorder, if_pos hlm]
      simp only [jetResponse_eq]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  by_cases hk : k ≤ m
  · rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k
      (fun _ => prodDerivation Q v (logBorder Q m k)),
      if_pos (Finset.mem_range.mpr (by omega : k < m + 1))]
  · rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k
      (fun _ => prodDerivation Q v (logBorder Q m k)),
      if_neg (fun hc => hk (by have := Finset.mem_range.mp hc; omega)),
      logBorder, if_neg hk]
    simp

/-! ## The Jacobian is the orbit of the border row -/

/-- **Every entry of the logarithmic Jacobian is an iterate of the shifted operator.** -/
theorem logJetJacobian_entry {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (n : ℕ) (i j : Fin (n + 1)) :
    logJetJacobian Q v n i j
      = ((gradShift Q v (n + 1))^[(i : ℕ)]) (logBorder Q (n + 1)) ((j : ℕ) + 1) := by
  refine Fin.cases ?_ (fun r => ?_) i
  · have hjle : ((j : ℕ) + 1) ≤ n + 1 := by
      have := j.isLt
      omega
    simp only [logJetJacobian, uniformBordered, Matrix.of_apply, Fin.cases_zero, logGradient,
      Fin.val_zero, Function.iterate_zero, id_eq, logBorder, if_pos hjle]
  · have hL : logSum Q v (n + 2) ∈ lowSub Q v (n + 1) :=
      logSum_mem_lowSub_succ Q v (le_refl (n + 2))
    have hstep := gradient_iterate_eq Q v (r : ℕ) hL
    have hbase := gradient_logSum_eq (Q := Q) v (n + 1)
    have hval : ((gradShift Q v (n + 1))^[(r : ℕ) + 1]) (logBorder Q (n + 1))
        = (fun l => fpderiv l
            (((prodDerivation Q v : CascadeField → CascadeField)^[(r : ℕ)])
              (logSum Q v (n + 2)))) := by
      rw [hstep, Function.iterate_succ_apply, ← hbase]
    have hentry : logJetJacobian Q v n r.succ j
        = fpderiv ((j : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(r : ℕ)])
              (logSum Q v (n + 2))) := by
      simp only [logJetJacobian, uniformBordered, Matrix.of_apply, Fin.cases_succ]
    rw [hentry, Fin.val_succ, hval]

/-- **The logarithmic Jacobian is the orbit matrix of the border row.**  Row `i` is the `i`-th
iterate of the shifted operator applied to the vector of logarithmic derivatives. -/
theorem logJetJacobian_eq_orbit {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ) (n : ℕ) :
    logJetJacobian Q v n
      = Matrix.of fun i j : Fin (n + 1) =>
          ((gradShift Q v (n + 1))^[(i : ℕ)]) (logBorder Q (n + 1)) ((j : ℕ) + 1) := by
  funext i j
  exact logJetJacobian_entry v n i j

end GaloisForLFunctions.HTGeometry
