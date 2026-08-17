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

theorem topDescent_chainDelta' (R : RatFunc C) {u k K : ℕ} (hK : 2 ≤ K)
    (hEu : topDescent K (invTowerDefect R u) = 0) (hne : K ≠ k) :
    topDescent K (chainDelta R u k)
      = (invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)
          * ((((k.choose K : ℕ))) : JetField C Unit) * shiftTower R (k - K)
        + substitutionShiftRatio R k * topDescent K (invTower (C := C) u) := by
  have hρpd : JetField.pd ((), K) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R (by omega)
  have hs := topDescent_substitutionShiftRatio_choose R hK k
  rw [chainDelta, topDescent_add, topDescent_add, topDescent_mul, topDescent_mul,
    topDescent_div_right hρpd, topDescent_mul, hEu,
    topDescent_jetRatio (show K ≠ 1 by omega), if_neg hne, hs]
  field_simp
  ring

/-- **The descent of the chain defect**, with the correction coming from the descents of the tower
entries already stripped. -/
theorem topDescent_chainDefect_gen (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N t : ℕ}
    (hN : 2 * t < N) (hK2 : 2 ≤ N - t) :
    topDescent (N - t) (chainDefect R N t)
      = ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * invTowerDefect R t
        - ∑ u ∈ Finset.range t, ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
            * substitutionShiftRatio R (N - u) * topDescent (N - t) (invTower (C := C) u) := by
  have hs := topDescent_substitutionShiftRatio_choose R hK2 (N + 1)
  rw [show N + 1 - (N - t) = t + 1 from by omega] at hs
  have hterm : ∀ u ∈ Finset.range t,
      topDescent (N - t) (((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
          * chainDelta R u (N - u))
        = ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
            * ((invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)
              * ((((N - u).choose (N - t) : ℕ)) : JetField C Unit)
              * shiftTower R (t - u))
          + ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
            * substitutionShiftRatio R (N - u) * topDescent (N - t) (invTower (C := C) u) := by
    intro u hu
    have hut : u < t := Finset.mem_range.mp hu
    have hEu : topDescent (N - t) (invTowerDefect R u) = 0 :=
      topDescent_eq_zero (pd_invTowerDefect_of_gt R (by omega))
    have hd := topDescent_chainDelta' R (u := u) (k := N - u) hK2 hEu (by omega)
    rw [show N - u - (N - t) = t - u from by omega] at hd
    rw [topDescent_mul_left (pd_natCast_eq_zero _ _), hd]
    ring
  rw [chainDefect, topDescent_sub, topDescent_sum, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, hs, invTowerDefect_eq' R hR t]
  have hsym : ((N + 1).choose (N - t) : ℕ) = ((N + 1).choose (t + 1) : ℕ) := by
    have h := Nat.choose_symm (n := N + 1) (k := t + 1) (by omega)
    rw [show N + 1 - (t + 1) = N - t from by omega] at h
    exact h
  rw [hsym, mul_sub, Finset.mul_sum]
  have hmatch : ∑ u ∈ Finset.range t, ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
        * ((invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)
          * ((((N - u).choose (N - t) : ℕ)) : JetField C Unit)
          * shiftTower R (t - u))
      = ∑ u ∈ Finset.range t, ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit)
        * (((((t + 1).choose (u + 1) : ℕ)) : JetField C Unit) * shiftTower R (t - u)
          * (invTower (C := C) u + invTowerDefect R u / substitutionDeriv R)) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hut : u < t := Finset.mem_range.mp hu
    have hnat := choose_chain_identity (N := N) (t := t) (u := u) hut (by omega)
    have hnatJ := congrArg (fun n : ℕ => ((n : ℕ) : JetField C Unit)) hnat
    simp only [Nat.cast_mul] at hnatJ
    linear_combination ((invTower (C := C) u
        + invTowerDefect R u / substitutionDeriv R) * shiftTower R (t - u)) * hnatJ
  rw [hmatch]
  ring

/-- **The descent of the chain defect in the clean range.** -/
theorem topDescent_chainDefect (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N t : ℕ}
    (hN : 2 * t + 1 < N) :
    topDescent (N - t) (chainDefect R N t)
      = ((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * invTowerDefect R t := by
  rw [topDescent_chainDefect_gen R hR (by omega) (by omega)]
  have hz : ∀ u ∈ Finset.range t, ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
      * substitutionShiftRatio R (N - u) * topDescent (N - t) (invTower (C := C) u) = 0 := by
    intro u hu
    have hut : u < t := Finset.mem_range.mp hu
    rw [topDescent_eq_zero (pd_invTower_of_gt (show u + 2 < N - t by omega)), mul_zero]
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, sub_zero]

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
theorem topDescent_chain (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N t Kf : ℕ}
    (hN : 2 * t + 1 < N) (hKf1 : N - t ≤ Kf) (hKf2 : t + 2 ≤ Kf)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, Kf < j → JetField.pd ((), j) g = 0) →
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
  have hordX : ∀ j : ℕ, Kf < j →
      JetField.pd ((), j) (X + c * invTower (C := C) t) = 0 := by
    intro j hj
    rw [map_add, hXdef,
      topDescent_order (show 1 ≤ N - t by omega) hordt j (by omega),
      pd_mul_eq_zero (pd_natCast_eq_zero _ _) (pd_invTower_of_gt (by omega)), add_zero]
  by_cases hzero : X + c * invTower (C := C) t = 0
  · linear_combination hzero
  · exact absurd (exponent_eq_zero_of_weightZero_eigen R hR (K := Kf) (by omega) hfix
      hwzX hzero hordX hdiff) (by push_cast; omega)

/-- **The chain stays inside its jet order.** -/
theorem chain_order (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N Kf : ℕ}
    (hKf : N - 1 ≤ Kf)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, Kf < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (heq : substitutionDeriv R ^ (N + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1))
    (hbase : ∀ j : ℕ, N - 1 < j → JetField.pd ((), j) (chain (C := C) N w 1) = 0) :
    ∀ t : ℕ, 1 ≤ t → 2 * t < N → t + 2 ≤ Kf →
      ∀ j : ℕ, N - t < j → JetField.pd ((), j) (chain (C := C) N w t) = 0 := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro _ _; exact hbase
  | succ t ht ih =>
      intro hlt hKt j hj
      have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
      have hordt := ih (by omega) (by omega)
      have htop := topDescent_chain R hR (show 2 * t + 1 < N by omega)
        (show N - t ≤ Kf by omega) (by omega) hfix hwz heq hordt
      rcases (by omega : j = N - t ∨ N - t < j) with heqj | hlt2
      · subst heqj
        have hVpd : JetField.pd ((), N - t) (invTower (C := C) t) = 0 :=
          pd_invTower_of_gt (by omega)
        have hpdc : JetField.pd ((), N - t) (chain (C := C) N w t)
            = -(((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * invTower (C := C) t)
              / (JetField.jet ((), 1) : JetField C Unit) ^ (N - t) := by
          rw [eq_div_iff (pow_ne_zero _ hy1)]
          rw [topDescent] at htop
          linear_combination htop
        have hzs : JetField.pd ((), N - t) (jetRatio (N - t) : JetField C Unit)
            = 1 / (JetField.jet ((), 1) : JetField C Unit) ^ (N - t) :=
          pd_jetRatio_self (by omega)
        have hleib := (JetField.pd ((), N - t) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (((((N + 1).choose (t + 1) : ℕ)) : JetField C Unit) * invTower (C := C) t)
            (jetRatio (N - t) : JetField C Unit)
        simp only [smul_eq_mul] at hleib
        rw [chain_succ, map_add, chainTerm, hleib,
          pd_mul_eq_zero (pd_natCast_eq_zero _ _) hVpd, mul_zero, add_zero, hzs, hpdc]
        field_simp
        ring
      · rw [chain_succ, map_add, hordt j hlt2, chainTerm,
          pd_mul_eq_zero (pd_mul_eq_zero (pd_natCast_eq_zero _ _)
            (pd_invTower_of_gt (by omega))) (pd_jetRatio_of_ne (by omega) (by omega)), zero_add]

/-- **No normalizing shift at level `2T + 2`.** -/
theorem no_zshift_of_odd (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {T Kf : ℕ} (hT : 1 ≤ T)
    (hKf : 2 * T ≤ Kf) (hKfT : T + 2 ≤ Kf)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, Kf < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (heq : substitutionDeriv R ^ (2 * T + 1 + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (2 * T + 1 + 1))
    (hbase : ∀ j : ℕ, 2 * T + 1 - 1 < j →
      JetField.pd ((), j) (chain (C := C) (2 * T + 1) w 1) = 0) : False := by
  set N : ℕ := 2 * T + 1 with hNdef
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hNT : N - T = T + 1 := by omega
  have hordT := chain_order R hR (show N - 1 ≤ Kf by omega) hfix hwz heq hbase T hT
    (by omega) (by omega)
  have hordT' : ∀ j : ℕ, T + 1 < j → JetField.pd ((), j) (chain (C := C) N w T) = 0 :=
    fun j hj => hordT j (by omega)
  have hgen := topDescent_chainDefect_gen R hR (N := N) (t := T) (by omega) (by omega)
  have hcorr : ∑ u ∈ Finset.range T, ((((N + 1).choose (u + 1) : ℕ)) : JetField C Unit)
        * substitutionShiftRatio R (N - u) * topDescent (N - T) (invTower (C := C) u)
      = ((((N + 1).choose T : ℕ)) : JetField C Unit)
        * substitutionShiftRatio R (T + 2) := by
    rw [Finset.sum_eq_single (T - 1)]
    · rw [show T - 1 + 1 = T from by omega, show N - (T - 1) = T + 2 from by omega, hNT,
        show T + 1 = T - 1 + 2 from by omega, topDescent_invTower, mul_one]
    · intro b hbmem hb
      have hbT : b < T := Finset.mem_range.mp hbmem
      rw [hNT, topDescent_eq_zero (pd_invTower_of_gt (show b + 2 < T + 1 by omega)), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.mpr (show T - 1 < T by omega)) hcon
  rw [hcorr, hNT] at hgen
  have hrel := chain_relation R hR heq (t := T) (by omega)
  have hrelZ : substitutionDeriv R ^ (((N + 1 : ℕ)) : ℤ)
      * jetSubstitution R hR (chain (C := C) N w T)
      = substitutionDeriv R * chain (C := C) N w T - chainDefect R N T := by
    rw [zpow_natCast]
    exact hrel
  have hstep := jetSubstitution_topDescent R hR (show 1 ≤ N - T by omega) hordT hrelZ
  have hNZ : ((N : ℕ) : ℤ) = 2 * (T : ℤ) + 1 := by
    rw [hNdef]
    push_cast
    ring
  have hexp : ((N + 1 : ℕ) : ℤ) + 1 - ((N - T : ℕ) : ℤ) = ((T + 2 : ℕ) : ℤ) := by
    rw [hNT]
    push_cast
    omega
  rw [hexp, zpow_natCast, hNT, hgen] at hstep
  have hV := jetSubstitution_invTower R hR T
  have hz := jetSubstitution_jetRatio R hR (T + 2)
  set X : JetField C Unit := topDescent (T + 1) (chain (C := C) N w T) with hXdef
  set a : JetField C Unit := ((((N + 1).choose (T + 1) : ℕ)) : JetField C Unit) with hadef
  set b : JetField C Unit := ((((N + 1).choose T : ℕ)) : JetField C Unit) with hbdef
  set Y : JetField C Unit := -(a * invTower (C := C) T)
    + b * (jetRatio (T + 2) : JetField C Unit) with hYdef
  have hdiff : substitutionDeriv R ^ ((T + 1 : ℕ) : ℤ)
      * jetSubstitution R hR (X - Y) = X - Y := by
    refine mul_left_cancel₀ hρ0 ?_
    have hzz : substitutionDeriv R * substitutionDeriv R ^ ((T + 1 : ℕ) : ℤ)
        = substitutionDeriv R ^ (T + 2 : ℕ) := by
      rw [zpow_natCast, ← pow_succ']
    rw [← mul_assoc, hzz, map_sub, hYdef, map_add, map_neg, map_mul, map_mul, hadef, hbdef,
      map_natCast, map_natCast, mul_sub, hstep]
    rw [show substitutionDeriv R ^ (T + 2 : ℕ)
        * (-(((((N + 1).choose (T + 1) : ℕ)) : JetField C Unit)
              * jetSubstitution R hR (invTower (C := C) T))
          + ((((N + 1).choose T : ℕ)) : JetField C Unit)
            * jetSubstitution R hR (jetRatio (T + 2) : JetField C Unit))
        = -(((((N + 1).choose (T + 1) : ℕ)) : JetField C Unit)
            * (substitutionDeriv R ^ (T + 2 : ℕ)
              * jetSubstitution R hR (invTower (C := C) T)))
          + ((((N + 1).choose T : ℕ)) : JetField C Unit)
            * (substitutionDeriv R ^ (T + 2 : ℕ)
              * jetSubstitution R hR (jetRatio (T + 2) : JetField C Unit)) from by ring,
      hV, hz]
    ring
  have hwzX : IsWeightZero (X - Y) := by
    refine IsWeightZero.sub (isWeightZero_topDescent (chain_isWeightZero N hwz T)) ?_
    rw [hYdef]
    refine IsWeightZero.add (IsWeightZero.neg (IsWeightZero.mul ?_ (isWeightZero_invTower T)))
      (IsWeightZero.mul ?_ (isWeightZero_jetRatio (T + 2)))
    · rw [hadef, show ((((N + 1).choose (T + 1) : ℕ)) : JetField C Unit)
          = algebraMap C (JetField C Unit) (((((N + 1).choose (T + 1) : ℕ)) : C)) from
        (map_natCast (algebraMap C (JetField C Unit)) _).symm]
      exact isWeightZero_algebraMap _
    · rw [hbdef, show ((((N + 1).choose T : ℕ)) : JetField C Unit)
          = algebraMap C (JetField C Unit) (((((N + 1).choose T : ℕ)) : C)) from
        (map_natCast (algebraMap C (JetField C Unit)) _).symm]
      exact isWeightZero_algebraMap _
  have hordX : ∀ j : ℕ, Kf < j → JetField.pd ((), j) (X - Y) = 0 := by
    intro j hj
    rw [map_sub, hXdef, topDescent_order (show 1 ≤ T + 1 by omega) hordT' j (by omega), hYdef,
      map_add, map_neg,
      pd_mul_eq_zero (pd_natCast_eq_zero _ _) (pd_invTower_of_gt (by omega)),
      pd_mul_eq_zero (pd_natCast_eq_zero _ _) (pd_jetRatio_of_ne (by omega) (by omega)),
      neg_zero, add_zero, sub_zero]
  have hXY : X = Y := by
    by_cases hzero : X - Y = 0
    · linear_combination hzero
    · exact absurd (exponent_eq_zero_of_weightZero_eigen R hR (K := Kf) (by omega) hfix
        hwzX hzero hordX hdiff) (by push_cast; omega)
  have hXtop : topDescent (T + 2) X = 0 := by
    rw [topDescent, hXdef,
      topDescent_order (show 1 ≤ T + 1 by omega) hordT' (T + 2) (by omega), mul_zero]
  have hYtop : topDescent (T + 2) Y = b - a := by
    have hVT : topDescent (T + 2) (invTower (C := C) T) = 1 := topDescent_invTower T
    have hzT : topDescent (T + 2) (jetRatio (T + 2) : JetField C Unit) = 1 := by
      rw [topDescent_jetRatio (show T + 2 ≠ 1 by omega), if_pos rfl]
    have hneg : topDescent (T + 2) (-(a * invTower (C := C) T))
        = -topDescent (T + 2) (a * invTower (C := C) T) := by
      rw [topDescent, topDescent, map_neg]
      ring
    rw [hYdef, topDescent_add, hneg, hadef, hbdef,
      topDescent_mul_left (pd_natCast_eq_zero _ _),
      topDescent_mul_left (pd_natCast_eq_zero _ _), hVT, hzT]
    ring
  rw [hXY, hYtop] at hXtop
  have hne : ((N + 1).choose T : ℕ) ≠ ((N + 1).choose (T + 1) : ℕ) := by
    intro hcon
    have hrec := Nat.choose_succ_right_eq (N + 1) T
    rw [hcon, show N + 1 - T = T + 2 from by omega] at hrec
    have hpos : 0 < ((N + 1).choose (T + 1) : ℕ) := Nat.choose_pos (by omega)
    have := Nat.eq_of_mul_eq_mul_left hpos hrec
    omega
  refine hne ?_
  have hb : b - a = 0 := hXtop
  have hcast : ((((N + 1).choose T : ℕ)) : JetField C Unit)
      = ((((N + 1).choose (T + 1) : ℕ)) : JetField C Unit) := by
    rw [hadef, hbdef] at hb
    linear_combination hb
  have hinj : Function.Injective (fun n : ℕ => ((n : ℕ) : JetField C Unit)) := by
    intro x y hxy
    have h1 : ((x : ℕ) : C) = ((y : ℕ) : C) := by
      refine (algebraMap C (JetField C Unit)).injective ?_
      rw [map_natCast, map_natCast]
      exact hxy
    exact Nat.cast_injective h1
  exact hinj hcast

end

end GaloisForLFunctions.HTGeometry
