import GaloisForLFunctions.HTGeometry.JetShiftTower

/-!
# The subdiagonal law for the shift

Every descent of the shift is a binomial multiple of the universal tower:

`topDescent_K(s_m) = binom(m, K)·T_{m−K}`   for `K ≥ 2`.

The proof is a strong induction on `m` through the tower expansion.  Descending the expansion in the
coordinate `z_K` produces three contributions: the diagonal term `z_K` itself, the term where the
tower entry is `T_K`, and the terms where the descent falls on a lower tower entry.  The tower is the
base derivative of the shift, so the last contribution is again a descent of a shift at a smaller
level, and the subset-of-a-subset identity `binom(n,k)·binom(k,s) = binom(n,s)·binom(n−s,k−s)`
matches it against the tower expansion at that level.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
theorem topDescent_sum {ι : Type*} (K : ℕ) (s : Finset ι) (f : ι → JetField C Unit) :
    topDescent K (∑ i ∈ s, f i) = ∑ i ∈ s, topDescent K (f i) := by
  rw [topDescent, map_sum, Finset.mul_sum]
  rfl

omit [CharZero C] in
theorem pd_zero_topDescent (K : ℕ) (v : JetField C Unit) :
    JetField.pd ((), 0) (topDescent K v) = topDescent K (JetField.pd ((), 0) v) := by
  rw [topDescent, topDescent]
  have hleib := (JetField.pd ((), 0) : Derivation C (JetField C Unit) (JetField C Unit)).leibniz
    ((JetField.jet ((), 1) : JetField C Unit) ^ K) (JetField.pd ((), K) v)
  simp only [smul_eq_mul] at hleib
  have hpow : JetField.pd ((), 0) ((JetField.jet ((), 1) : JetField C Unit) ^ K) = 0 :=
    pd_pow_eq_zero (JetField.pd_jet_of_ne (by simp)) K
  rw [hleib, hpow, mul_zero, add_zero, pd_comm]

theorem topDescent_jetRatio {K j : ℕ} (hK : K ≠ 1) :
    topDescent K (jetRatio j : JetField C Unit) = if K = j then 1 else 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  rw [topDescent]
  by_cases h : K = j
  · subst h
    rw [pd_jetRatio_self hK, if_pos rfl]
    field_simp
  · rw [pd_jetRatio_of_ne hK h, mul_zero, if_neg h]

omit [CharZero C] in
theorem pd_substitutionShift_eq_zero (R : RatFunc C) {K m : ℕ} (hK : 1 ≤ K) (h : m ≤ K) :
    JetField.pd ((), K) (substitutionShift R m) = 0 := by
  have hleib := (JetField.pd ((), K) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionDeriv R) (JetField.jet ((), m) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  rw [substitutionShift, map_sub, hleib, pd_substitutionDeriv_eq_zero R (by omega), mul_zero,
    add_zero]
  rcases eq_or_lt_of_le h with heq | hlt
  · subst heq
    rw [pd_substitutionJet_self, JetField.pd_jet_self, mul_one, sub_self]
  · rw [pd_substitutionJet_eq_zero_of_lt R hlt,
      JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega),
      mul_zero, sub_zero]

omit [CharZero C] in
theorem topDescent_substitutionShiftRatio_of_le (R : RatFunc C) {K m : ℕ} (hK : 2 ≤ K)
    (h : m ≤ K) : topDescent K (substitutionShiftRatio R m) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hmul : substitutionShiftRatio R m * (JetField.jet ((), 1) : JetField C Unit) ^ m
      = substitutionShift R m := by
    rw [substitutionShiftRatio]
    field_simp
  have hpow : JetField.pd ((), K) ((JetField.jet ((), 1) : JetField C Unit) ^ m) = 0 :=
    pd_pow_eq_zero (JetField.pd_jet_of_ne (by
      simp only [ne_eq, Prod.mk.injEq, true_and]; omega)) m
  have hleib := (JetField.pd ((), K) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionShiftRatio R m) ((JetField.jet ((), 1) : JetField C Unit) ^ m)
  simp only [smul_eq_mul] at hleib
  rw [hmul, hpow, mul_zero, zero_add, pd_substitutionShift_eq_zero R (by omega) h] at hleib
  rw [topDescent]
  have := (mul_eq_zero.mp hleib.symm).resolve_left (pow_ne_zero m hy1)
  rw [this, mul_zero]

omit [CharZero C] in
theorem topDescent_mul (K : ℕ) (a b : JetField C Unit) :
    topDescent K (a * b) = a * topDescent K b + b * topDescent K a := by
  have hleib := (JetField.pd ((), K) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz a b
  simp only [smul_eq_mul] at hleib
  rw [topDescent, topDescent, topDescent, hleib]
  ring

theorem topDescent_shiftTower_of (R : RatFunc C) {K r : ℕ} (hK : 2 ≤ K) (hr : 1 ≤ r)
    (ihr : topDescent K (substitutionShiftRatio R r)
      = (((r.choose K : ℕ)) : JetField C Unit) * shiftTower R (r - K)) :
    topDescent K (shiftTower R r)
      = (((r.choose K : ℕ)) : JetField C Unit)
          * JetField.pd ((), 0) (shiftTower R (r - K))
        + JetField.pd ((), 0) (substitutionDeriv R) * (if K = r then 1 else 0) := by
  have hρ1 : JetField.pd ((), K) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
    rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
  have hcomm := pd_zero_topDescent (C := C) K (substitutionShiftRatio R r)
  have hd : JetField.pd ((), 0) ((((r.choose K : ℕ)) : JetField C Unit) * shiftTower R (r - K))
      = (((r.choose K : ℕ)) : JetField C Unit)
        * JetField.pd ((), 0) (shiftTower R (r - K)) := by
    have hl := (JetField.pd ((), 0) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        ((((r.choose K : ℕ)) : JetField C Unit)) (shiftTower R (r - K))
    simp only [smul_eq_mul] at hl
    rw [hl, pd_natCast_eq_zero, mul_zero, add_zero]
  rw [shiftTower_eq R hr, topDescent_add, ← hcomm, ihr, hd,
    topDescent_mul_left hρ1, topDescent_jetRatio (show K ≠ 1 by omega)]

theorem choose_subdiagonal_identity {M K i : ℕ} (hK : 2 ≤ K) (hKM : K ≤ M) :
    (M + 1).choose (i + 1) * (M - i).choose K
      = (M + 1).choose K * (M + 1 - K).choose (i + 1) := by
  rcases (by omega : i + 1 ≤ M + 1 - K ∨ M + 1 - K < i + 1) with hle | hlt
  · have hiq : i ≤ M - K := by omega
    have h1 := Nat.choose_mul (n := M + 1) (k := M + 1 - K) (s := i + 1) hle
    have h2 : (M - i).choose (M - i - K) = (M - i).choose K :=
      Nat.choose_symm (by omega)
    have h3 : (M + 1).choose (M + 1 - K) = (M + 1).choose K :=
      Nat.choose_symm (by omega)
    rw [show M + 1 - (i + 1) = M - i from by omega,
      show M + 1 - K - (i + 1) = M - i - K from by omega] at h1
    rw [h2, h3] at h1
    omega
  · have h4 : (M - i).choose K = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h5 : (M + 1 - K).choose (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h4, h5]
    ring

/-- **The subdiagonal law.** -/
theorem topDescent_substitutionShiftRatio_choose (R : RatFunc C) {K : ℕ} (hK : 2 ≤ K) (m : ℕ) :
    topDescent K (substitutionShiftRatio R m)
      = (((m.choose K : ℕ)) : JetField C Unit) * shiftTower R (m - K) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases (by omega : m ≤ K ∨ K < m) with hle | hlt
    · rw [topDescent_substitutionShiftRatio_of_le R hK hle]
      rcases eq_or_lt_of_le hle with heq | hlt2
      · subst heq
        rw [Nat.choose_self, Nat.sub_self]
        rw [show shiftTower R 0 = (0 : JetField C Unit) from rfl]
        rw [mul_zero]
      · rw [Nat.choose_eq_zero_of_lt hlt2, Nat.cast_zero, zero_mul]
    · obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
      have hKM : K ≤ M := by omega
      have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
      have hMne : ((M + 1 : ℕ) : JetField C Unit) ≠ 0 := by
        rw [show ((M + 1 : ℕ) : JetField C Unit)
            = algebraMap C (JetField C Unit) (((M + 1 : ℕ) : C)) from
          (map_natCast (algebraMap C (JetField C Unit)) (M + 1)).symm]
        intro hh
        exact absurd ((algebraMap C (JetField C Unit)).injective (by rw [hh, map_zero]))
          (Nat.cast_ne_zero.mpr (by omega))
      refine mul_left_cancel₀ hMne ?_
      have hexp := substitutionShiftRatio_eq_shiftTower_sum R M
      have h1 : ((M + 1 : ℕ) : JetField C Unit)
            * topDescent K (substitutionShiftRatio R (M + 1))
          = topDescent K (((M + 1 : ℕ) : JetField C Unit)
              * substitutionShiftRatio R (M + 1)) :=
        (topDescent_mul_left (pd_natCast_eq_zero _ _)).symm
      rw [h1, hexp, topDescent_sum]
      have hterm : ∀ i ∈ Finset.range M,
          topDescent K (((i + 1 : ℕ) : JetField C Unit)
              * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
              * (jetRatio (i + 1) : JetField C Unit) * shiftTower R (M - i))
            = ((i + 1 : ℕ) : JetField C Unit)
                * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                * (shiftTower R (M - i) * (if K = i + 1 then (1 : JetField C Unit) else 0))
              + ((i + 1 : ℕ) : JetField C Unit)
                  * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                  * ((jetRatio (i + 1) : JetField C Unit)
                    * (((((M - i).choose K : ℕ)) : JetField C Unit)
                      * JetField.pd ((), 0) (shiftTower R (M - i - K))))
              + ((i + 1 : ℕ) : JetField C Unit)
                  * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                  * ((jetRatio (i + 1) : JetField C Unit)
                    * (JetField.pd ((), 0) (substitutionDeriv R)
                      * (if K = M - i then (1 : JetField C Unit) else 0))) := by
        intro i hi
        have hiM : i < M := Finset.mem_range.mp hi
        have hcpd : JetField.pd ((), K) (((i + 1 : ℕ) : JetField C Unit)
            * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)) = 0 :=
          pd_mul_eq_zero (pd_natCast_eq_zero _ _) (pd_natCast_eq_zero _ _)
        have hTD := topDescent_shiftTower_of R hK (show 1 ≤ M - i by omega)
          (ih (M - i) (by omega))
        rw [mul_assoc, topDescent_mul_left hcpd, topDescent_mul, hTD,
          topDescent_jetRatio (show K ≠ 1 by omega)]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
      -- the diagonal term
      have hA : ∑ i ∈ Finset.range M, (((i + 1 : ℕ) : JetField C Unit)
              * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
              * (shiftTower R (M - i) * (if K = i + 1 then (1 : JetField C Unit) else 0)))
          = ((K : ℕ) : JetField C Unit) * ((((M + 1).choose K : ℕ)) : JetField C Unit)
            * shiftTower R (M + 1 - K) := by
        rw [Finset.sum_eq_single (K - 1)]
        · rw [show K - 1 + 1 = K from by omega, if_pos rfl,
            show M - (K - 1) = M + 1 - K from by omega]
          ring
        · intro b _ hb
          rw [if_neg (by omega), mul_zero, mul_zero]
        · intro hcon
          exact absurd (Finset.mem_range.mpr (show K - 1 < M by omega)) hcon
      -- the coordinate term
      have hCsum : ∑ i ∈ Finset.range M, (((i + 1 : ℕ) : JetField C Unit)
              * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
              * ((jetRatio (i + 1) : JetField C Unit)
                * (JetField.pd ((), 0) (substitutionDeriv R)
                  * (if K = M - i then (1 : JetField C Unit) else 0))))
          = ((M + 1 - K : ℕ) : JetField C Unit)
            * ((((M + 1).choose (M + 1 - K) : ℕ)) : JetField C Unit)
            * ((jetRatio (M + 1 - K) : JetField C Unit)
              * JetField.pd ((), 0) (substitutionDeriv R)) := by
        rw [Finset.sum_eq_single (M - K)]
        · rw [show M - (M - K) = K from by omega, if_pos rfl,
            show M - K + 1 = M + 1 - K from by omega]
          ring
        · intro b hb hbne
          have hbM : b < M := Finset.mem_range.mp hb
          rw [if_neg (by omega), mul_zero, mul_zero, mul_zero]
        · intro hcon
          exact absurd (Finset.mem_range.mpr (show M - K < M by omega)) hcon
      -- the tower expansion one level down, differentiated in the base coordinate
      obtain ⟨q, hq⟩ : ∃ q, M + 1 - K = q + 1 := ⟨M - K, by omega⟩
      have hd0 : ((q + 1 : ℕ) : JetField C Unit)
            * JetField.pd ((), 0) (substitutionShiftRatio R (q + 1))
          = ∑ i ∈ Finset.range q, ((i + 1 : ℕ) : JetField C Unit)
              * ((((q + 1).choose (i + 1) : ℕ)) : JetField C Unit)
              * (jetRatio (i + 1) : JetField C Unit)
              * JetField.pd ((), 0) (shiftTower R (q - i)) := by
        have hlhs : JetField.pd ((), 0) (((q + 1 : ℕ) : JetField C Unit)
              * substitutionShiftRatio R (q + 1))
            = ((q + 1 : ℕ) : JetField C Unit)
              * JetField.pd ((), 0) (substitutionShiftRatio R (q + 1)) := by
          have hl := (JetField.pd ((), 0) :
            Derivation C (JetField C Unit) (JetField C Unit)).leibniz
              (((q + 1 : ℕ) : JetField C Unit)) (substitutionShiftRatio R (q + 1))
          simp only [smul_eq_mul] at hl
          rw [hl, pd_natCast_eq_zero, mul_zero, add_zero]
        have hrhs : ∀ i ∈ Finset.range q,
            JetField.pd ((), 0) (((i + 1 : ℕ) : JetField C Unit)
                * ((((q + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                * (jetRatio (i + 1) : JetField C Unit) * shiftTower R (q - i))
              = ((i + 1 : ℕ) : JetField C Unit)
                * ((((q + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                * (jetRatio (i + 1) : JetField C Unit)
                * JetField.pd ((), 0) (shiftTower R (q - i)) := by
          intro i _
          have hcpd : JetField.pd ((), 0) (((i + 1 : ℕ) : JetField C Unit)
              * ((((q + 1).choose (i + 1) : ℕ)) : JetField C Unit)
              * (jetRatio (i + 1) : JetField C Unit)) = 0 :=
            pd_mul_eq_zero (pd_mul_eq_zero (pd_natCast_eq_zero _ _) (pd_natCast_eq_zero _ _))
              (pd_jetRatio_of_ne (by omega) (by omega))
          have hl := (JetField.pd ((), 0) :
            Derivation C (JetField C Unit) (JetField C Unit)).leibniz
              (((i + 1 : ℕ) : JetField C Unit)
                * ((((q + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                * (jetRatio (i + 1) : JetField C Unit)) (shiftTower R (q - i))
          simp only [smul_eq_mul] at hl
          rw [hl, hcpd, mul_zero, add_zero]
        have h := congrArg (JetField.pd ((), 0))
          (substitutionShiftRatio_eq_shiftTower_sum R q)
        rw [map_sum, hlhs, Finset.sum_congr rfl hrhs] at h
        exact h
      have hB : ∑ i ∈ Finset.range M, (((i + 1 : ℕ) : JetField C Unit)
              * ((((M + 1).choose (i + 1) : ℕ)) : JetField C Unit)
              * ((jetRatio (i + 1) : JetField C Unit)
                * (((((M - i).choose K : ℕ)) : JetField C Unit)
                  * JetField.pd ((), 0) (shiftTower R (M - i - K)))))
          = ((((M + 1).choose K : ℕ)) : JetField C Unit)
            * (((q + 1 : ℕ) : JetField C Unit)
              * JetField.pd ((), 0) (substitutionShiftRatio R (q + 1))) := by
        rw [hd0, Finset.mul_sum]
        have hsub : ∀ i ∈ Finset.range M, i ∉ Finset.range q →
            ((((M + 1).choose K : ℕ)) : JetField C Unit)
              * (((i + 1 : ℕ) : JetField C Unit)
                * ((((q + 1).choose (i + 1) : ℕ)) : JetField C Unit)
                * (jetRatio (i + 1) : JetField C Unit)
                * JetField.pd ((), 0) (shiftTower R (q - i))) = 0 := by
          intro i _ hi
          have hiq : q ≤ i := by
            by_contra hcon
            exact hi (Finset.mem_range.mpr (by omega))
          rw [show q - i = 0 from by omega,
            show shiftTower R 0 = (0 : JetField C Unit) from rfl, map_zero]
          ring
        rw [Finset.sum_subset (show Finset.range q ⊆ Finset.range M from fun x hx =>
          Finset.mem_range.mpr (by
            have hx' := Finset.mem_range.mp hx
            omega)) hsub]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hidx : M - i - K = q - i := by omega
        have hnat := choose_subdiagonal_identity (M := M) (K := K) (i := i) hK hKM
        rw [hq] at hnat
        have hnatJ := congrArg (fun n : ℕ => ((n : ℕ) : JetField C Unit)) hnat
        simp only [Nat.cast_mul] at hnatJ
        rw [hidx]
        linear_combination (((i + 1 : ℕ) : JetField C Unit)
          * (jetRatio (i + 1) : JetField C Unit)
          * JetField.pd ((), 0) (shiftTower R (q - i))) * hnatJ
      rw [hA, hB, hCsum]
      -- assemble
      have hsym : ((M + 1).choose (M + 1 - K) : ℕ) = ((M + 1).choose K : ℕ) :=
        Nat.choose_symm (by omega)
      have hTr := shiftTower_eq R (show 1 ≤ M + 1 - K by omega)
      have hcast : ((K : ℕ) : JetField C Unit) + ((M + 1 - K : ℕ) : JetField C Unit)
          = ((M + 1 : ℕ) : JetField C Unit) := by
        rw [← Nat.cast_add, show K + (M + 1 - K) = M + 1 from by omega]
      rw [hsym, hq] at *
      rw [hTr]
      linear_combination (((M + 1).choose K : ℕ) : JetField C Unit)
        * (JetField.pd ((), 0) (substitutionShiftRatio R (q + 1))
          + JetField.pd ((), 0) (substitutionDeriv R)
            * (jetRatio (q + 1) : JetField C Unit)) * hcast

end

end GaloisForLFunctions.HTGeometry
