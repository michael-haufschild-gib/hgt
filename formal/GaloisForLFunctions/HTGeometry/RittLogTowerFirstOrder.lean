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

/-- **The first-order expansion of a power.** -/
theorem wLt2_pow_sub_firstOrder {D R : MvPolynomial (Fin n) K} {d : ℕ}
    (hD : WLe n D d) (hR : WLt n R d) :
    ∀ m : ℕ, WLt2 n ((D + R) ^ m - D ^ m - (m : MvPolynomial (Fin n) K) * R * D ^ (m - 1))
      (m * d)
  | 0 => by
      simpa using wLt2_zero (K := K) (n := n) 0
  | (m + 1) => by
      simp only [Nat.add_sub_cancel]
      have hrw : (D + R) ^ (m + 1) - D ^ (m + 1)
            - ((m + 1 : ℕ) : MvPolynomial (Fin n) K) * R * D ^ m
          = ((D + R) ^ m - D ^ m - (m : MvPolynomial (Fin n) K) * R * D ^ (m - 1)) * (D + R)
            + ((m : MvPolynomial (Fin n) K) * R * D ^ (m - 1)) * R
            + (D ^ m * R - ((m + 1 : ℕ) : MvPolynomial (Fin n) K) * R * D ^ m
              + (m : MvPolynomial (Fin n) K) * R * D ^ (m - 1) * D) := by
        push_cast
        ring
      have hlast : (D : MvPolynomial (Fin n) K) ^ m * R
            - ((m + 1 : ℕ) : MvPolynomial (Fin n) K) * R * D ^ m
            + (m : MvPolynomial (Fin n) K) * R * D ^ (m - 1) * D = 0 := by
        cases m with
        | zero => push_cast; ring
        | succ m =>
            have : (D : MvPolynomial (Fin n) K) ^ (m + 1 - 1) * D = D ^ (m + 1) := by
              simp [pow_succ]
            push_cast
            rw [show (m + 1 - 1) = m from rfl] at this
            linear_combination ((m : MvPolynomial (Fin n) K) + 1) * R * this
      have h1 : WLt2 n (((D + R) ^ m - D ^ m - (m : MvPolynomial (Fin n) K) * R * D ^ (m - 1))
          * (D + R)) (m * d + d) :=
        (wLt2_pow_sub_firstOrder hD hR m).mul_wLe (hD.add hR.wLe)
      have h2 : WLt2 n (((m : MvPolynomial (Fin n) K) * R * D ^ (m - 1)) * R) (m * d + d) := by
        cases m with
        | zero =>
            simpa using wLt2_zero (K := K) (n := n) (0 * d + d)
        | succ m' =>
            have hm : WLe n (((m' + 1 : ℕ) : MvPolynomial (Fin n) K)) 0 := by
              simpa using wLe_C (K := K) (n := n) ((m' + 1 : ℕ) : K) 0
            have hprod := ((hm.mul_wLt hR).mul (hD.pow m')).mul_wLt hR
            exact hprod.mono (le_of_eq (by ring))
      have hd : (m + 1) * d = m * d + d := by ring
      rw [hrw, hlast, add_zero, hd]
      exact h1.add h2

/-- The first-order term of a product expansion. -/
noncomputable def firstOrderTerm (D R : Fin n → MvPolynomial (Fin n) K) (k : Fin n → ℕ)
    (t : Finset (Fin n)) : MvPolynomial (Fin n) K :=
  ∑ j ∈ t, ((k j : MvPolynomial (Fin n) K) * R j * D j ^ (k j - 1)
    * ∏ i ∈ t.erase j, D i ^ k i)

theorem wLt_firstOrderTerm {D R : Fin n → MvPolynomial (Fin n) K} {w : Fin n → ℕ}
    (hD : ∀ j, WLe n (D j) (w j)) (hR : ∀ j, WLt n (R j) (w j)) (k : Fin n → ℕ)
    (t : Finset (Fin n)) :
    WLt n (firstOrderTerm D R k t) (∑ j ∈ t, k j * w j) := by
  classical
  refine Finset.sum_induction _ (fun F => WLt n F (∑ j ∈ t, k j * w j))
    (fun _ _ => WLt.add) (wLt_zero _) ?_
  intro j hj
  by_cases hkj : k j = 0
  · rw [hkj]
    simp only [Nat.cast_zero, zero_mul]
    exact wLt_zero _
  · have hm : WLe n ((k j : MvPolynomial (Fin n) K)) 0 := by
      simpa using wLe_C (K := K) (n := n) ((k j : ℕ) : K) 0
    have hprod : WLe n (∏ i ∈ t.erase j, D i ^ k i) (∑ i ∈ t.erase j, k i * w i) :=
      wLe_prod_of_wLe hD k (t.erase j)
    have h := ((hm.mul_wLt (hR j)).mul ((hD j).pow (k j - 1))).mul hprod
    refine h.mono ?_
    have hsum : ∑ i ∈ t.erase j, k i * w i + k j * w j = ∑ i ∈ t, k i * w i := by
      rw [add_comm]
      exact Finset.add_sum_erase t (fun i => k i * w i) hj
    have hle : (k j - 1) * w j + w j = k j * w j := by
      obtain ⟨m, hm'⟩ : ∃ m, k j = m + 1 := ⟨k j - 1, by omega⟩
      rw [hm']
      simp only [Nat.add_sub_cancel]
      ring
    omega

/-- The algebraic identity behind the first-order product expansion. -/
theorem firstOrder_algebra (X Y c P P' S : MvPolynomial (Fin n) K) :
    X * P' - Y * P - (c * P + Y * S)
      = Y * (P' - P - S) + c * (S + (P' - P - S))
        + (X - Y - c) * (P + S + (P' - P - S)) := by
  ring

/-- **The first-order expansion of a product.** -/
theorem wLt2_prod_sub_firstOrder {D R : Fin n → MvPolynomial (Fin n) K} {w : Fin n → ℕ}
    (hD : ∀ j, WLe n (D j) (w j)) (hR : ∀ j, WLt n (R j) (w j)) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n),
      WLt2 n ((∏ j ∈ t, (D j + R j) ^ k j) - (∏ j ∈ t, D j ^ k j)
        - firstOrderTerm D R k t) (∑ j ∈ t, k j * w j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa [firstOrderTerm] using wLt2_zero (K := K) (n := n) 0
  | insert a t ha ih =>
      have hne : ∀ j ∈ t, j ≠ a := fun j hj hc => ha (hc ▸ hj)
      have hterm : firstOrderTerm D R k (insert a t)
          = (k a : MvPolynomial (Fin n) K) * R a * D a ^ (k a - 1) * (∏ i ∈ t, D i ^ k i)
            + D a ^ k a * firstOrderTerm D R k t := by
        rw [firstOrderTerm, Finset.sum_insert ha, Finset.erase_insert ha, firstOrderTerm,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.erase_insert_of_ne (Ne.symm (hne j hj)),
          Finset.prod_insert (fun hc => ha (Finset.mem_of_mem_erase hc))]
        ring
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, hterm,
        firstOrder_algebra ((D a + R a) ^ k a) (D a ^ k a)
          ((k a : MvPolynomial (Fin n) K) * R a * D a ^ (k a - 1))
          (∏ i ∈ t, D i ^ k i) (∏ j ∈ t, (D j + R j) ^ k j) (firstOrderTerm D R k t)]
      have hPle : WLe n (∏ i ∈ t, D i ^ k i) (∑ j ∈ t, k j * w j) := wLe_prod_of_wLe hD k t
      have hSle : WLt n (firstOrderTerm D R k t) (∑ j ∈ t, k j * w j) :=
        wLt_firstOrderTerm hD hR k t
      have hBle : WLt2 n ((∏ j ∈ t, (D j + R j) ^ k j) - (∏ i ∈ t, D i ^ k i)
          - firstOrderTerm D R k t) (∑ j ∈ t, k j * w j) := ih
      have hAle : WLt2 n ((D a + R a) ^ k a - D a ^ k a
          - (k a : MvPolynomial (Fin n) K) * R a * D a ^ (k a - 1)) (k a * w a) :=
        wLt2_pow_sub_firstOrder (hD a) (hR a) (k a)
      have hlin : WLt n ((k a : MvPolynomial (Fin n) K) * R a * D a ^ (k a - 1))
          (k a * w a) := by
        by_cases hka : k a = 0
        · rw [hka]
          simp only [Nat.cast_zero, zero_mul]
          exact wLt_zero _
        · have hm : WLe n ((k a : MvPolynomial (Fin n) K)) 0 := by
            simpa using wLe_C (K := K) (n := n) ((k a : ℕ) : K) 0
          refine ((hm.mul_wLt (hR a)).mul ((hD a).pow (k a - 1))).mono ?_
          have hle : (k a - 1) * w a + w a = k a * w a := by
            obtain ⟨m, hm'⟩ : ∃ m, k a = m + 1 := ⟨k a - 1, by omega⟩
            rw [hm']
            simp only [Nat.add_sub_cancel]
            ring
          omega
      refine WLt2.add (WLt2.add ?_ ?_) ?_
      · exact ((hD a).pow (k a)).mul_wLt2 hBle
      · exact hlin.mul_wLt (hSle.add hBle.wLt)
      · exact hAle.mul_wLe ((hPle.add hSle.wLe).add hBle.wLt.wLe)

theorem wLt_towerRest1 (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt n (Fr.towerRest1 b n j) (jetWeight n j) := by
  intro e he
  have := Fr.wLe_towerRest1 b j e he
  simp only [jetWeight]
  omega

/-- **The tower shift of a monomial, expanded to first order.** -/
theorem wLt2_towerShift2_monomial (Fr : RittFrame K L) (b : K) (e : Fin n →₀ ℕ) (c : K) :
    WLt2 n (Fr.towerShift2 b n (monomial e c)
        - C (Fr.ψ c) * ((∏ j ∈ e.support, Fr.towerDiag n j ^ e j)
          + firstOrderTerm (Fr.towerDiag n) (Fr.towerRest1 b n) (⇑e) e.support))
      (Finsupp.weight (jetWeight n) e) := by
  have h := wLt2_prod_sub_firstOrder (D := Fr.towerDiag n) (R := Fr.towerRest1 b n)
    (w := jetWeight n) (fun j => Fr.wLe_towerDiag j) (fun j => Fr.wLt_towerRest1 b j)
    (⇑e) e.support
  rw [Fr.towerShift2_monomial b e c]
  have hrw : C (Fr.ψ c) * (∏ j ∈ e.support, Fr.towerSub2 b n j ^ e j)
      - C (Fr.ψ c) * ((∏ j ∈ e.support, Fr.towerDiag n j ^ e j)
        + firstOrderTerm (Fr.towerDiag n) (Fr.towerRest1 b n) (⇑e) e.support)
      = C (Fr.ψ c) * ((∏ j ∈ e.support, (Fr.towerDiag n j + Fr.towerRest1 b n j) ^ e j)
        - (∏ j ∈ e.support, Fr.towerDiag n j ^ e j)
        - firstOrderTerm (Fr.towerDiag n) (Fr.towerRest1 b n) (⇑e) e.support) := by
    simp only [towerSub2]
    ring
  rw [hrw]
  refine ((wLe_C (n := n) (Fr.ψ c) 0).mul_wLt2 h).mono ?_
  rw [weight_eq_sum e]
  omega

/-- **The weight `W − 1` coefficient of the truncated tower shift** is the first-order term alone:
the diagonal part lives entirely in the top layer. -/
theorem coeff_towerShift2_of_second (Fr : RittFrame K L) (b : K)
    {F : MvPolynomial (Fin n) K} {W : ℕ}
    (hF : ∀ e ∈ F.support, Finsupp.weight (jetWeight n) e = W)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d + 1 = W) :
    coeff d (Fr.towerShift2 b n F)
      = ∑ e ∈ F.support, Fr.ψ (coeff e F)
          * coeff d (firstOrderTerm (Fr.towerDiag n) (Fr.towerRest1 b n) (⇑e) e.support) := by
  classical
  have hmono : ∀ e ∈ F.support,
      coeff d (Fr.towerShift2 b n (monomial e (coeff e F)))
        = Fr.ψ (coeff e F)
          * coeff d (firstOrderTerm (Fr.towerDiag n) (Fr.towerRest1 b n) (⇑e) e.support) := by
    intro e he
    have hrem : coeff d (Fr.towerShift2 b n (monomial e (coeff e F))
        - C (Fr.ψ (coeff e F)) * ((∏ j ∈ e.support, Fr.towerDiag n j ^ e j)
          + firstOrderTerm (Fr.towerDiag n) (Fr.towerRest1 b n) (⇑e) e.support)) = 0 := by
      by_contra hne
      have := Fr.wLt2_towerShift2_monomial b e (coeff e F) d
        (MvPolynomial.mem_support_iff.mpr hne)
      rw [hF e he] at this
      omega
    rw [coeff_sub, sub_eq_zero] at hrem
    rw [hrem, mul_add, coeff_add, coeff_C_mul, coeff_C_mul, Fr.prod_towerDiag e]
    have hdiag : coeff d (C ((Fr.ρ ^ Finsupp.weight (jetWeight n) e)⁻¹) * monomial e (1 : K))
        = 0 := by
      rw [coeff_C_mul, coeff_monomial, if_neg, mul_zero]
      intro hc
      rw [← hc, hF e he] at hd
      omega
    rw [hdiag, mul_zero, zero_add]
  have hsum : Fr.towerShift2 b n F
      = ∑ e ∈ F.support, Fr.towerShift2 b n (monomial e (coeff e F)) := by
    rw [← map_sum, ← MvPolynomial.as_sum F]
  rw [hsum, coeff_sum]
  exact Finset.sum_congr rfl hmono

theorem prod_towerDiag_sub_single (Fr : RittFrame K L) (e : Fin n →₀ ℕ) (j : Fin n)
    (hj : j ∈ e.support) :
    Fr.towerDiag n j ^ (e j - 1) * ∏ i ∈ e.support.erase j, Fr.towerDiag n i ^ e i
      = C ((Fr.ρ ^ Finsupp.weight (jetWeight n) (e - Finsupp.single j 1))⁻¹)
        * monomial (e - Finsupp.single j 1) (1 : K) := by
  classical
  set g : Fin n →₀ ℕ := e - Finsupp.single j 1 with hg
  have hgval : ∀ i : Fin n, g i = if i = j then e j - 1 else e i := by
    intro i
    rw [hg, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg h, if_neg (fun hc => h hc.symm)]
      simp
  have hgsub : g.support ⊆ e.support := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi ⊢
    rw [hgval i] at hi
    by_cases h : i = j
    · subst h
      rw [if_pos rfl] at hi
      omega
    · rw [if_neg h] at hi
      exact hi
  have hsplit : (∏ i ∈ e.support, Fr.towerDiag n i ^ g i)
      = Fr.towerDiag n j ^ (e j - 1) * ∏ i ∈ e.support.erase j, Fr.towerDiag n i ^ e i := by
    rw [← Finset.mul_prod_erase _ _ hj, hgval j, if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hgval i, if_neg (Finset.ne_of_mem_erase hi)]
  have hshrink : (∏ i ∈ e.support, Fr.towerDiag n i ^ g i)
      = ∏ i ∈ g.support, Fr.towerDiag n i ^ g i := by
    refine (Finset.prod_subset hgsub ?_).symm
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
  rw [← hsplit, hshrink, Fr.prod_towerDiag g]

theorem towerRest1_of_zero (Fr : RittFrame K L) (b : K) {j : Fin n} (hj : (j : ℕ) = 0) :
    Fr.towerRest1 b n j = C (Fr.logConst b 0) := by
  classical
  rw [towerRest1, if_pos hj]
  have hterm : ∀ i : Fin n,
      (if (i : ℕ) + 1 = (j : ℕ) then C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i else 0)
        = (0 : MvPolynomial (Fin n) K) := by
    intro i
    rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const_zero, zero_add]

theorem towerRest1_of_succ (Fr : RittFrame K L) (b : K) {j i : Fin n}
    (hij : (i : ℕ) + 1 = (j : ℕ)) :
    Fr.towerRest1 b n j = C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i := by
  classical
  rw [towerRest1, if_neg (by omega), add_zero]
  have hsingle : ∀ i' ∈ (Finset.univ : Finset (Fin n)), i' ≠ i →
      (if (i' : ℕ) + 1 = (j : ℕ) then C (Fr.logCoeff (j : ℕ) (i' : ℕ)) * X i'
        else 0) = (0 : MvPolynomial (Fin n) K) := by
    intro i' _ hne
    rw [if_neg]
    intro hc
    exact hne (Fin.ext (by omega))
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hsingle, if_pos hij]

end RittFrame

end GaloisForLFunctions.HTGeometry
