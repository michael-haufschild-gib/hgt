import GaloisForLFunctions.HTGeometry.JetChainTerm

/-!
# The descent chain

Given a torus-invariant solution `w` of the shift relation at level `N + 1`, the chain

`chain t = w + ∑_{u < t} binom(N+1, u+1)·V_u·z_{N−u}`

strips the pinned coefficients one coordinate at a time.  Its relation has the same exponent and an
explicit defect, and the subdiagonal law together with the subset-of-a-subset identity computes the
descent of that defect as `binom(N+1, t+1)·Ê_t` — the level dependence is a single binomial factor.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- One correction of the descent chain. -/
def chainTerm (N u : ℕ) : JetField C Unit :=
  ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit) * invTower u
    * (jetRatio (N - u) : JetField C Unit)

/-- The stripped element at stage `t`. -/
def chain (N : ℕ) (w : JetField C Unit) (t : ℕ) : JetField C Unit :=
  w + ∑ u ∈ Finset.range t, chainTerm (C := C) N u

/-- The inhomogeneous term at stage `t`. -/
def chainDefect (R : RatFunc C) (N : ℕ) (t : ℕ) : JetField C Unit :=
  substitutionShiftRatio R (N + 1)
    - ∑ u ∈ Finset.range t, ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
        * chainDelta R u (N - u)

omit [CharZero C] in
theorem chain_succ (N : ℕ) (w : JetField C Unit) (t : ℕ) :
    chain (C := C) N w (t + 1) = chain (C := C) N w t + chainTerm (C := C) N t := by
  rw [chain, chain, Finset.sum_range_succ]
  ring

omit [CharZero C] in
theorem chainDefect_succ (R : RatFunc C) (N t : ℕ) :
    chainDefect R N (t + 1)
      = chainDefect R N t
        - ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * chainDelta R t (N - t) := by
  rw [chainDefect, chainDefect, Finset.sum_range_succ]
  ring

/-- **The chain relation.** -/
theorem chain_relation (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ}
    {w : JetField C Unit}
    (heq : substitutionDeriv R ^ (N + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1))
    {t : ℕ} (ht : t ≤ N + 1) :
    substitutionDeriv R ^ (N + 1) * jetSubstitution R hR (chain (C := C) N w t)
      = substitutionDeriv R * chain (C := C) N w t - chainDefect R N t := by
  have hterm : ∀ u ∈ Finset.range t,
      substitutionDeriv R ^ (N + 1) * jetSubstitution R hR (chainTerm (C := C) N u)
        = substitutionDeriv R * chainTerm (C := C) N u
          + ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit) * chainDelta R u (N - u) := by
    intro u hu
    have huN : u ≤ N := by
      have := Finset.mem_range.mp hu
      omega
    have hmul := jetSubstitution_invTower_mul R hR u (N - u)
    rw [show u + 1 + (N - u) = N + 1 from by omega] at hmul
    rw [chainTerm, mul_assoc, map_mul, map_natCast, mul_left_comm, hmul]
    ring
  rw [chain, chainDefect, map_add, map_sum, mul_add, Finset.mul_sum,
    Finset.sum_congr rfl hterm, Finset.sum_add_distrib, heq, mul_add, Finset.mul_sum]
  ring

/-- The defect recursion with the sum in the descent's own indexing. -/
theorem invTowerDefect_eq' (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (t : ℕ) :
    invTowerDefect R t
      = shiftTower R (t + 1)
        - ∑ u ∈ Finset.range t, ((((t + 1).choose (u + 1) : ℕ)) : JetField C Unit)
            * shiftTower R (t - u)
            * (invTower (C := C) u + invTowerDefect R u / substitutionDeriv R) := by
  rw [invTowerDefect_eq R hR t]
  congr 1
  rw [← Finset.sum_range_reflect (fun u => ((((t + 1).choose (u + 1) : ℕ)) : JetField C Unit)
      * shiftTower R (t - u)
      * (invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)) t]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j < t := Finset.mem_range.mp hj
  have hch : ((t + 1).choose (t - 1 - j + 1) : ℕ) = ((t + 1).choose (j + 1) : ℕ) := by
    have h := Nat.choose_symm (n := t + 1) (k := j + 1) (by omega)
    rw [show t + 1 - (j + 1) = t - j from by omega] at h
    rw [show t - 1 - j + 1 = t - j from by omega]
    exact h
  rw [hch, show t - (t - 1 - j) = j + 1 from by omega]

theorem choose_chain_identity {N t u : ℕ} (hut : u < t) (htN : t ≤ N) :
    (N + 1).choose (u + 1) * (N - u).choose (N - t)
      = (N + 1).choose (t + 1) * (t + 1).choose (u + 1) := by
  have h1 := Nat.choose_mul (n := N + 1) (k := t + 1) (s := u + 1) (by omega)
  rw [show N + 1 - (u + 1) = N - u from by omega,
    show t + 1 - (u + 1) = t - u from by omega] at h1
  have h2 : (N - u).choose (N - u - (t - u)) = (N - u).choose (t - u) :=
    Nat.choose_symm (by omega)
  rw [show N - u - (t - u) = N - t from by omega] at h2
  rw [h2]
  exact h1.symm

/-- **The descent of the chain defect.** -/
theorem topDescent_chainDefect (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N t : ℕ}
    (hN : 2 * t + 1 < N) :
    topDescent (N - t) (chainDefect R N t)
      = ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * invTowerDefect R t := by
  have hK2 : 2 ≤ N - t := by omega
  have hs := topDescent_substitutionShiftRatio_choose R hK2 (N + 1)
  rw [show N + 1 - (N - t) = t + 1 from by omega] at hs
  have hterm : ∀ u ∈ Finset.range t,
      topDescent (N - t) (((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
          * chainDelta R u (N - u))
        = ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
          * ((invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)
            * ((((N - u).choose (N - t) : ℕ)) : JetField C Unit)
            * shiftTower R (t - u)) := by
    intro u hu
    have hut : u < t := Finset.mem_range.mp hu
    have hVu : topDescent (N - t) (invTower (C := C) u) = 0 :=
      topDescent_eq_zero (pd_invTower_of_gt (by omega))
    have hEu : topDescent (N - t) (invTowerDefect R u) = 0 :=
      topDescent_eq_zero (pd_invTowerDefect_of_gt R (by omega))
    have hd := topDescent_chainDelta R (u := u) (k := N - u) hK2 hVu hEu (by omega)
    rw [show N - u - (N - t) = t - u from by omega] at hd
    rw [topDescent_mul_left (pd_natCast_eq_zero _ _), hd]
  rw [chainDefect, topDescent_sub, topDescent_sum, Finset.sum_congr rfl hterm, hs,
    invTowerDefect_eq' R hR t]
  have hsym : ((N + 1).choose (N - t) : ℕ) = ((N + 1).choose (t + 1) : ℕ) := by
    have h := Nat.choose_symm (n := N + 1) (k := t + 1) (by omega)
    rw [show N + 1 - (t + 1) = N - t from by omega] at h
    exact h
  rw [hsym, mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  have hut : u < t := Finset.mem_range.mp hu
  have hnat := choose_chain_identity (N := N) (t := t) (u := u) hut (by omega)
  have hnatJ := congrArg (fun n : ℕ => ((n : ℕ) : JetField C Unit)) hnat
  simp only [Nat.cast_mul] at hnatJ
  linear_combination ((invTower (C := C) u
      + invTowerDefect R u / substitutionDeriv R) * shiftTower R (t - u)) * hnatJ

theorem chain_isWeightZero (N : ℕ) {w : JetField C Unit} (hwz : IsWeightZero w) (t : ℕ) :
    IsWeightZero (chain (C := C) N w t) := by
  induction t with
  | zero => simpa [chain] using hwz
  | succ t ih =>
      rw [chain_succ]
      refine ih.add ?_
      rw [chainTerm]
      refine IsWeightZero.mul (IsWeightZero.mul ?_ (isWeightZero_invTower t))
        (isWeightZero_jetRatio (N - t))
      rw [show ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit)
          = algebraMap C (JetField C Unit) (((((N + 1).choose (t + 1) : ℕ)) : C)) from
        (map_natCast (algebraMap C (JetField C Unit)) _).symm]
      exact isWeightZero_algebraMap _

/-- **The pinned coefficient at stage `t`.** -/
theorem topDescent_chain (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N t : ℕ}
    (hN : 2 * t + 1 < N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (heq : substitutionDeriv R ^ (N + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1))
    (hordt : ∀ j : ℕ, N - t < j → JetField.pd ((), j) (chain (C := C) N w t) = 0) :
    topDescent (N - t) (chain (C := C) N w t)
      = -(((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * invTower (C := C) t) := by
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hrel := chain_relation R hR heq (t := t) (by omega)
  have hrelZ : substitutionDeriv R ^ (((N + 1 : ℕ)) : ℤ)
      * jetSubstitution R hR (chain (C := C) N w t)
      = substitutionDeriv R * chain (C := C) N w t - chainDefect R N t := by
    rw [zpow_natCast]
    exact hrel
  have hstep := jetSubstitution_topDescent R hR (show 1 ≤ N - t by omega) hordt hrelZ
  have hexp : ((N + 1 : ℕ) : ℤ) + 1 - ((N - t : ℕ) : ℤ) = ((t + 2 : ℕ) : ℤ) := by
    have hc : ((N - t : ℕ) : ℤ) = (N : ℤ) - (t : ℤ) := by
      have h := Nat.cast_sub (R := ℤ) (show t ≤ N by omega)
      simpa using h
    rw [hc]
    push_cast
    ring
  rw [hexp, zpow_natCast, topDescent_chainDefect R hR hN] at hstep
  -- the candidate solves the same relation
  have hV := jetSubstitution_invTower R hR t
  set X : JetField C Unit := topDescent (N - t) (chain (C := C) N w t) with hXdef
  set c : JetField C Unit := ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) with hcdef
  have hdiff : substitutionDeriv R ^ ((t + 1 : ℕ) : ℤ)
      * jetSubstitution R hR (X + c * invTower (C := C) t) = X + c * invTower (C := C) t := by
    refine mul_left_cancel₀ hρ0 ?_
    have hz : substitutionDeriv R * substitutionDeriv R ^ ((t + 1 : ℕ) : ℤ)
        = substitutionDeriv R ^ (t + 2 : ℕ) := by
      rw [zpow_natCast, ← pow_succ']
    rw [← mul_assoc, hz, map_add, map_mul, map_natCast, mul_add]
    rw [show substitutionDeriv R ^ (t + 2 : ℕ) * (c * jetSubstitution R hR (invTower (C := C) t))
        = c * (substitutionDeriv R ^ (t + 2 : ℕ)
          * jetSubstitution R hR (invTower (C := C) t)) from by ring, hV, hstep]
    ring
  have hwzX : IsWeightZero (X + c * invTower (C := C) t) := by
    refine IsWeightZero.add (isWeightZero_topDescent (chain_isWeightZero N hwz t)) ?_
    refine IsWeightZero.mul ?_ (isWeightZero_invTower t)
    rw [hcdef, show ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit)
        = algebraMap C (JetField C Unit) (((((N + 1).choose (t + 1) : ℕ)) : C)) from
      (map_natCast (algebraMap C (JetField C Unit)) _).symm]
    exact isWeightZero_algebraMap _
  have hordX : ∀ j : ℕ, N < j →
      JetField.pd ((), j) (X + c * invTower (C := C) t) = 0 := by
    intro j hj
    rw [map_add, hXdef,
      topDescent_order (show 1 ≤ N - t by omega) hordt j (by omega),
      pd_mul_eq_zero (pd_natCast_eq_zero _ _) (pd_invTower_of_gt (by omega)), add_zero]
  by_cases hzero : X + c * invTower (C := C) t = 0
  · rw [hXdef] at hzero ⊢
    linarith [hzero] <;> skip
  · exact absurd (exponent_eq_zero_of_weightZero_eigen R hR (K := N) (by omega) hfix
      hwzX hzero hordX hdiff) (by push_cast; omega)

end

end GaloisForLFunctions.HTGeometry
