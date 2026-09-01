import GaloisForLFunctions.HTGeometry.RittLogTowerWeight

/-!
# The subdiagonal layer of the tower substitution

Below its diagonal part the tower substitution has one distinguished layer: the terms that drop the
weight by exactly one.  For the `j`-th variable with `j ≥ 1` that is the subdiagonal coefficient
times the previous variable, and for the bottom variable it is the base constant.  Everything else
drops the weight by at least two.

This is the layer that produces the *rational affine connection*: the weight `W − 1` comparison of a
tower relation has multiplier `ρ^{-1}` whatever the relation's own multiplier was.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- The non-diagonal part of the tower substitution. -/
noncomputable def towerRest (Fr : RittFrame K L) (b : K) (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K :=
  Fr.towerSub b n j - Fr.towerDiag n j

/-- The layer of the tower substitution that drops the weight by exactly one. -/
noncomputable def towerRest1 (Fr : RittFrame K L) (b : K) (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K :=
  (∑ i : Fin n, if (i : ℕ) + 1 = (j : ℕ) then C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i else 0)
    + (if (j : ℕ) = 0 then C (Fr.logConst b 0) else 0)

theorem towerRest_eq (Fr : RittFrame K L) (b : K) (j : Fin n) :
    Fr.towerRest b n j
      = (∑ i ∈ Finset.univ.erase j, C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
        + C (Fr.logConst b (j : ℕ)) := by
  classical
  rw [towerRest, towerSub, towerDiag,
    ← Finset.add_sum_erase Finset.univ
      (fun i : Fin n => C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i) (Finset.mem_univ j),
    Fr.logCoeff_diag (j : ℕ)]
  ring

theorem wLt_towerRest (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt n (Fr.towerRest b n j) (jetWeight n j) :=
  Fr.wLt_towerSub_sub_towerDiag b j

theorem wLe_towerRest1 (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLe n (Fr.towerRest1 b n j) ((j : ℕ)) := by
  classical
  refine WLe.add ?_ ?_
  · have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        WLe n (if (i : ℕ) + 1 = (j : ℕ) then C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i else 0
          : MvPolynomial (Fin n) K) ((j : ℕ)) := by
      intro i _
      by_cases h : (i : ℕ) + 1 = (j : ℕ)
      · rw [if_pos h]
        exact (Fr.wLe_coeff_mul_X j i).mono (by simp only [jetWeight]; omega)
      · rw [if_neg h]
        exact wLe_zero _
    exact Finset.sum_induction _ (fun F => WLe n F ((j : ℕ))) (fun _ _ => WLe.add)
      (wLe_zero _) hterm
  · by_cases h : (j : ℕ) = 0
    · rw [if_pos h]
      exact wLe_C (n := n) (Fr.logConst b 0) _
    · rw [if_neg h]
      exact wLe_zero _

/-- **Everything below the subdiagonal layer drops the weight by at least two.** -/
theorem wLt_towerRest_sub_towerRest1 (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt n (Fr.towerRest b n j - Fr.towerRest1 b n j) ((j : ℕ)) := by
  classical
  have hA : (∑ i ∈ Finset.univ.erase j, C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
      = ∑ i : Fin n, (if i = j then (0 : MvPolynomial (Fin n) K)
        else C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun i : Fin n => if i = j then (0 : MvPolynomial (Fin n) K)
        else C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i) (Finset.mem_univ j), if_pos rfl, zero_add]
    exact (Finset.sum_congr rfl (fun i hi => by
      rw [if_neg (Finset.ne_of_mem_erase hi)])).symm
  have hsum : Fr.towerRest b n j - Fr.towerRest1 b n j
      = (∑ i : Fin n, ((if i = j then (0 : MvPolynomial (Fin n) K)
          else C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
          - (if (i : ℕ) + 1 = (j : ℕ) then C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i else 0)))
        + (C (Fr.logConst b (j : ℕ))
          - (if (j : ℕ) = 0 then C (Fr.logConst b 0) else 0)) := by
    rw [Fr.towerRest_eq b j, towerRest1, hA, Finset.sum_sub_distrib]
    ring
  rw [hsum]
  refine WLt.add ?_ ?_
  · have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        WLt n ((if i = j then (0 : MvPolynomial (Fin n) K)
          else C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
          - (if (i : ℕ) + 1 = (j : ℕ) then C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i else 0))
          ((j : ℕ)) := by
      intro i _
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_neg (by omega), sub_zero]
        exact wLt_zero _
      · rw [if_neg hij]
        by_cases hsucc : (i : ℕ) + 1 = (j : ℕ)
        · rw [if_pos hsucc, sub_self]
          exact wLt_zero _
        · rw [if_neg hsucc, sub_zero]
          rcases lt_or_ge (j : ℕ) (i : ℕ) with hlt | hge
          · rw [Fr.logCoeff_eq_zero_of_lt _ _ hlt, map_zero, zero_mul]
            exact wLt_zero _
          · have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
            intro e he
            exact lt_of_le_of_lt (Fr.wLe_coeff_mul_X j i e he)
              (by simp only [jetWeight]; omega)
    exact Finset.sum_induction _ (fun F => WLt n F ((j : ℕ))) (fun _ _ => WLt.add)
      (wLt_zero _) hterm
  · by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj, hj, sub_self]
      exact wLt_zero _
    · rw [if_neg hj, sub_zero]
      intro e he
      have h := wLe_C (n := n) (Fr.logConst b (j : ℕ)) 0 e he
      omega

/-- Every monomial of `F` has weight at least two below `d`. -/
def WLt2 (n : ℕ) (F : MvPolynomial (Fin n) K) (d : ℕ) : Prop :=
  ∀ e ∈ F.support, Finsupp.weight (jetWeight n) e + 1 < d

theorem WLt2.wLt {F : MvPolynomial (Fin n) K} {d : ℕ} (h : WLt2 n F d) : WLt n F d := by
  intro e he
  have := h e he
  omega

theorem wLt2_zero (d : ℕ) : WLt2 n (0 : MvPolynomial (Fin n) K) d := by
  intro e he
  simp at he

theorem WLt2.add {F G : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLt2 n F d) (hG : WLt2 n G d) :
    WLt2 n (F + G) d := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
  · exact hF e h
  · exact hG e h

theorem WLt2.neg {F : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLt2 n F d) : WLt2 n (-F) d :=
  fun e he => hF e (by simpa using he)

theorem WLt2.sub {F G : MvPolynomial (Fin n) K} {d : ℕ} (hF : WLt2 n F d) (hG : WLt2 n G d) :
    WLt2 n (F - G) d := by
  rw [sub_eq_add_neg]
  exact hF.add hG.neg

theorem WLt2.mul_wLe {F G : MvPolynomial (Fin n) K} {d d' : ℕ} (hF : WLt2 n F d)
    (hG : WLe n G d') : WLt2 n (F * G) (d + d') := by
  intro e he
  obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
  have h1 := hF a ha
  have h2 := hG c hc
  rw [map_add]
  omega

theorem WLe.mul_wLt2 {F G : MvPolynomial (Fin n) K} {d d' : ℕ} (hF : WLe n F d)
    (hG : WLt2 n G d') : WLt2 n (F * G) (d + d') := by
  rw [mul_comm, add_comm]
  exact hG.mul_wLe hF

theorem WLt.mul_wLt {F G : MvPolynomial (Fin n) K} {d d' : ℕ} (hF : WLt n F d)
    (hG : WLt n G d') : WLt2 n (F * G) (d + d') := by
  intro e he
  obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
  have h1 := hF a ha
  have h2 := hG c hc
  rw [map_add]
  omega

theorem wLt2_pow_sub_pow {A B : MvPolynomial (Fin n) K} {d : ℕ}
    (hA : WLe n A d) (hB : WLe n B d) (hsub : WLt2 n (A - B) d) :
    ∀ m : ℕ, WLt2 n (A ^ m - B ^ m) (m * d)
  | 0 => by
      simpa using wLt2_zero (K := K) (n := n) 0
  | (m + 1) => by
      have hrw : A ^ (m + 1) - B ^ (m + 1) = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by ring
      have h1 : WLt2 n (A ^ m * (A - B)) (m * d + d) := (hA.pow m).mul_wLt2 hsub
      have h2 : WLt2 n ((A ^ m - B ^ m) * B) (m * d + d) :=
        (wLt2_pow_sub_pow hA hB hsub m).mul_wLe hB
      have hd : (m + 1) * d = m * d + d := by ring
      rw [hrw, hd]
      exact h1.add h2

theorem wLe_prod_of_wLe {A : Fin n → MvPolynomial (Fin n) K} {w : Fin n → ℕ}
    (hA : ∀ j, WLe n (A j) (w j)) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n), WLe n (∏ j ∈ t, A j ^ k j) (∑ j ∈ t, k j * w j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa using wLe_C (K := K) (n := n) 1 0
  | insert c s hc ihs =>
      rw [Finset.prod_insert hc, Finset.sum_insert hc]
      exact ((hA c).pow (k c)).mul ihs

theorem wLt2_prod_sub_prod {A B : Fin n → MvPolynomial (Fin n) K} {w : Fin n → ℕ}
    (hA : ∀ j, WLe n (A j) (w j)) (hB : ∀ j, WLe n (B j) (w j))
    (hsub : ∀ j, WLt2 n (A j - B j) (w j)) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n),
      WLt2 n ((∏ j ∈ t, A j ^ k j) - (∏ j ∈ t, B j ^ k j)) (∑ j ∈ t, k j * w j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa using wLt2_zero (K := K) (n := n) 0
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hrw : A a ^ k a * ∏ j ∈ t, A j ^ k j - B a ^ k a * ∏ j ∈ t, B j ^ k j
          = (A a ^ k a - B a ^ k a) * (∏ j ∈ t, A j ^ k j)
            + B a ^ k a * ((∏ j ∈ t, A j ^ k j) - (∏ j ∈ t, B j ^ k j)) := by ring
      have hprodA : WLe n (∏ j ∈ t, A j ^ k j) (∑ j ∈ t, k j * w j) :=
        wLe_prod_of_wLe hA k t
      rw [hrw]
      exact ((wLt2_pow_sub_pow (hA a) (hB a) (hsub a) (k a)).mul_wLe hprodA).add
        (((hB a).pow (k a)).mul_wLt2 ih)

theorem WLt2.mono {F : MvPolynomial (Fin n) K} {d d' : ℕ} (h : WLt2 n F d) (hd : d ≤ d') :
    WLt2 n F d' := fun e he => lt_of_lt_of_le (h e he) hd

/-- The first-order truncation of the tower substitution: its diagonal part together with the
layer that drops the weight by exactly one. -/
noncomputable def towerSub2 (Fr : RittFrame K L) (b : K) (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K :=
  Fr.towerDiag n j + Fr.towerRest1 b n j

/-- The first-order truncation of the tower shift. -/
noncomputable def towerShift2 (Fr : RittFrame K L) (b : K) (n : ℕ) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K :=
  eval₂Hom ((C : K →+* MvPolynomial (Fin n) K).comp Fr.ψ) (Fr.towerSub2 b n)

theorem wLe_towerSub2 (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLe n (Fr.towerSub2 b n j) (jetWeight n j) :=
  (Fr.wLe_towerDiag j).add ((Fr.wLe_towerRest1 b j).mono (by simp only [jetWeight]; omega))

theorem wLt2_towerSub_sub_towerSub2 (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt2 n (Fr.towerSub b n j - Fr.towerSub2 b n j) (jetWeight n j) := by
  have hrw : Fr.towerSub b n j - Fr.towerSub2 b n j
      = Fr.towerRest b n j - Fr.towerRest1 b n j := by
    rw [towerSub2, towerRest]
    ring
  intro e he
  rw [hrw] at he
  have := Fr.wLt_towerRest_sub_towerRest1 b j e he
  simp only [jetWeight]
  omega

theorem towerShift2_monomial (Fr : RittFrame K L) (b : K) (e : Fin n →₀ ℕ) (c : K) :
    Fr.towerShift2 b n (monomial e c)
      = C (Fr.ψ c) * ∏ j ∈ e.support, Fr.towerSub2 b n j ^ e j := by
  rw [towerShift2, eval₂Hom_monomial]
  rfl

/-- **The tower shift and its first-order truncation agree two weight layers below the top.** -/
theorem wLt2_towerShift_sub_towerShift2 (Fr : RittFrame K L) (b : K)
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W) :
    WLt2 n (Fr.towerShift b n F - Fr.towerShift2 b n F) W := by
  classical
  have hmono : ∀ e ∈ F.support,
      WLt2 n (Fr.towerShift b n (monomial e (coeff e F))
        - Fr.towerShift2 b n (monomial e (coeff e F))) W := by
    intro e he
    rw [Fr.towerShift_monomial b e (coeff e F), Fr.towerShift2_monomial b e (coeff e F),
      ← mul_sub]
    refine ((wLe_C (n := n) (Fr.ψ (coeff e F)) 0).mul_wLt2
      (wLt2_prod_sub_prod (A := Fr.towerSub b n) (B := Fr.towerSub2 b n)
        (w := jetWeight n) (Fr.wLe_towerSub b) (Fr.wLe_towerSub2 b)
        (Fr.wLt2_towerSub_sub_towerSub2 b) (fun j => e j) e.support)).mono ?_
    rw [zero_add, ← weight_eq_sum e]
    exact hF e he
  have hsum : Fr.towerShift b n F - Fr.towerShift2 b n F
      = ∑ e ∈ F.support, (Fr.towerShift b n (monomial e (coeff e F))
        - Fr.towerShift2 b n (monomial e (coeff e F))) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← MvPolynomial.as_sum F]
  rw [hsum]
  exact Finset.sum_induction _ (fun G => WLt2 n G W) (fun _ _ => WLt2.add) (wLt2_zero _) hmono

theorem wLt_pow_sub_pow_gen {A B : MvPolynomial (Fin n) K} {d : ℕ}
    (hA : WLe n A d) (hB : WLe n B d) (hsub : WLt n (A - B) d) :
    ∀ m : ℕ, WLt n (A ^ m - B ^ m) (m * d)
  | 0 => by
      simpa using wLt_zero (K := K) (n := n) 0
  | (m + 1) => by
      have hrw : A ^ (m + 1) - B ^ (m + 1) = A ^ m * (A - B) + (A ^ m - B ^ m) * B := by ring
      have h1 : WLt n (A ^ m * (A - B)) (m * d + d) := (hA.pow m).mul_wLt hsub
      have h2 : WLt n ((A ^ m - B ^ m) * B) (m * d + d) :=
        (wLt_pow_sub_pow_gen hA hB hsub m).mul hB
      have hd : (m + 1) * d = m * d + d := by ring
      rw [hrw, hd]
      exact h1.add h2

theorem wLt_prod_sub_prod_gen {A B : Fin n → MvPolynomial (Fin n) K} {w : Fin n → ℕ}
    (hA : ∀ j, WLe n (A j) (w j)) (hB : ∀ j, WLe n (B j) (w j))
    (hsub : ∀ j, WLt n (A j - B j) (w j)) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n),
      WLt n ((∏ j ∈ t, A j ^ k j) - (∏ j ∈ t, B j ^ k j)) (∑ j ∈ t, k j * w j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa using wLt_zero (K := K) (n := n) 0
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hrw : A a ^ k a * ∏ j ∈ t, A j ^ k j - B a ^ k a * ∏ j ∈ t, B j ^ k j
          = (A a ^ k a - B a ^ k a) * (∏ j ∈ t, A j ^ k j)
            + B a ^ k a * ((∏ j ∈ t, A j ^ k j) - (∏ j ∈ t, B j ^ k j)) := by ring
      rw [hrw]
      exact ((wLt_pow_sub_pow_gen (hA a) (hB a) (hsub a) (k a)).mul
        (wLe_prod_of_wLe hA k t)).add (((hB a).pow (k a)).mul_wLt ih)

theorem wLt_towerSub2_sub_towerDiag (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt n (Fr.towerSub2 b n j - Fr.towerDiag n j) (jetWeight n j) := by
  have hrw : Fr.towerSub2 b n j - Fr.towerDiag n j = Fr.towerRest1 b n j := by
    rw [towerSub2]; ring
  rw [hrw]
  intro e he
  have := Fr.wLe_towerRest1 b j e he
  simp only [jetWeight]
  omega

/-- The first-order truncation agrees with the diagonal one below the top weight layer. -/
theorem wLt_towerShift2_sub_towerDiagShift (Fr : RittFrame K L) (b : K)
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W) :
    WLt n (Fr.towerShift2 b n F - Fr.towerDiagShift n F) W := by
  classical
  have hmono : ∀ e ∈ F.support,
      WLt n (Fr.towerShift2 b n (monomial e (coeff e F))
        - Fr.towerDiagShift n (monomial e (coeff e F))) W := by
    intro e he
    rw [Fr.towerShift2_monomial b e (coeff e F), Fr.towerDiagShift_monomial e (coeff e F),
      ← mul_sub]
    refine ((wLe_C (n := n) (Fr.ψ (coeff e F)) 0).mul_wLt
      (wLt_prod_sub_prod_gen (A := Fr.towerSub2 b n) (B := Fr.towerDiag n)
        (w := jetWeight n) (Fr.wLe_towerSub2 b) (Fr.wLe_towerDiag)
        (Fr.wLt_towerSub2_sub_towerDiag b) (fun j => e j) e.support)).mono ?_
    rw [zero_add, ← weight_eq_sum e]
    exact hF e he
  have hsum : Fr.towerShift2 b n F - Fr.towerDiagShift n F
      = ∑ e ∈ F.support, (Fr.towerShift2 b n (monomial e (coeff e F))
        - Fr.towerDiagShift n (monomial e (coeff e F))) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← MvPolynomial.as_sum F]
  rw [hsum]
  exact Finset.sum_induction _ (fun G => WLt n G W) (fun _ _ => WLt.add) (wLt_zero _) hmono

theorem wLe_weightedHomogeneousComponent (W : ℕ) (F : MvPolynomial (Fin n) K) :
    WLe n (weightedHomogeneousComponent (jetWeight n) W F) W := by
  classical
  intro e he
  rw [MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at he
  by_cases h : Finsupp.weight (jetWeight n) e = W
  · omega
  · rw [if_neg h] at he
    exact absurd rfl he

theorem wLe_sub_weightedHomogeneousComponent {F : MvPolynomial (Fin n) K} {W : ℕ}
    (hF : WLe n F W) :
    WLe n (F - weightedHomogeneousComponent (jetWeight n) W F) (W - 1) := by
  classical
  intro e he
  rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_weightedHomogeneousComponent] at he
  by_cases h : Finsupp.weight (jetWeight n) e = W
  · rw [if_pos h, sub_self] at he
    exact absurd rfl he
  · rw [if_neg h, sub_zero] at he
    have := hF e (MvPolynomial.mem_support_iff.mpr he)
    omega

theorem coeff_sub_weightedHomogeneousComponent {F : MvPolynomial (Fin n) K} {W : ℕ}
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d ≠ W) :
    coeff d (F - weightedHomogeneousComponent (jetWeight n) W F) = coeff d F := by
  classical
  rw [coeff_sub, coeff_weightedHomogeneousComponent, if_neg hd, sub_zero]

/-- **The weight `W − 1` layer of the tower shift.**  Below the top the shift acts by the base map
scaled by `ρ^{-(W-1)}`, corrected by the first-order image of the top weight component. -/
theorem coeff_towerShift_of_second (Fr : RittFrame K L) (b : K)
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d + 1 = W) :
    coeff d (Fr.towerShift b n F)
      = Fr.ψ (coeff d F) * (Fr.ρ ^ (W - 1))⁻¹
        + coeff d (Fr.towerShift2 b n
            (weightedHomogeneousComponent (jetWeight n) W F)) := by
  classical
  set F1 : MvPolynomial (Fin n) K := weightedHomogeneousComponent (jetWeight n) W F with hF1
  set F0 : MvPolynomial (Fin n) K := F - F1 with hF0
  have hdW : Finsupp.weight (jetWeight n) d ≠ W := by omega
  have hFsum : F = F0 + F1 := by rw [hF0]; ring
  have h1 : coeff d (Fr.towerShift b n F - Fr.towerShift2 b n F) = 0 := by
    by_contra hne
    have := Fr.wLt2_towerShift_sub_towerShift2 b hF d (MvPolynomial.mem_support_iff.mpr hne)
    omega
  have h2 : coeff d (Fr.towerShift2 b n F0 - Fr.towerDiagShift n F0) = 0 := by
    by_contra hne
    have := Fr.wLt_towerShift2_sub_towerDiagShift b
      (wLe_sub_weightedHomogeneousComponent hF) d (MvPolynomial.mem_support_iff.mpr hne)
    omega
  have h3 : coeff d F0 = coeff d F := coeff_sub_weightedHomogeneousComponent hdW
  rw [coeff_sub, sub_eq_zero] at h1 h2
  rw [h1]
  conv_lhs => rw [hFsum]
  have hw : Finsupp.weight (jetWeight n) d = W - 1 := by omega
  rw [map_add, coeff_add, h2, Fr.coeff_towerDiagShift F0 d, h3, hw]

/-- **The weight `W − 1` layer of a tower relation is an affine transport equation.**  Its
multiplier is `ρ^{J+W-1}` — for a collapse at order `n`, where `J = -(n+1)` and `W = n+1`, that is
`ρ^{-1}`: the rational affine connection. -/
theorem second_base_relation_of_towerShift (Fr : RittFrame K L) (b : K)
    {F G : MvPolynomial (Fin n) K} {W : ℕ} {J : ℤ} (hF : WLe n F W)
    (hrel : Fr.towerShift b n F = C (Fr.ρ ^ J) * F + G)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d + 1 = W) :
    Fr.ψ (coeff d F) = Fr.ρ ^ J * Fr.ρ ^ (W - 1) * coeff d F
      + Fr.ρ ^ (W - 1) * (coeff d G
        - coeff d (Fr.towerShift2 b n (weightedHomogeneousComponent (jetWeight n) W F))) := by
  have h1 := Fr.coeff_towerShift_of_second b hF hd
  have h2 : coeff d (Fr.towerShift b n F) = Fr.ρ ^ J * coeff d F + coeff d G := by
    rw [hrel, coeff_add, coeff_C_mul]
  rw [h1] at h2
  have hpow : (Fr.ρ : K) ^ (W - 1) ≠ 0 := pow_ne_zero _ Fr.ρ_ne
  field_simp at h2
  linear_combination h2

end RittFrame

end GaloisForLFunctions.HTGeometry
