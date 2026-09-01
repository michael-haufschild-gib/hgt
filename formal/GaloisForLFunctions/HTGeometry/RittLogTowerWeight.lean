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
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X] at he
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
  rw [towerDiag]
  have h := (wLe_C (n := n) ((Fr.ρ ^ ((j : ℕ) + 1))⁻¹) 0).mul (wLe_X (n := n) j)
  simpa using h

theorem wLe_coeff_mul_X (Fr : RittFrame K L) (j i : Fin n) :
    WLe n (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i : MvPolynomial (Fin n) K) (jetWeight n i) := by
  have h := (wLe_C (n := n) (Fr.logCoeff (j : ℕ) (i : ℕ)) 0).mul (wLe_X (n := n) i)
  simpa using h

theorem wLe_towerSub (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLe n (Fr.towerSub b n j) (jetWeight n j) := by
  classical
  refine WLe.add ?_ (wLe_C (n := n) (Fr.logConst b (j : ℕ)) _)
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      WLe n (C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i : MvPolynomial (Fin n) K)
        (jetWeight n j) := by
    intro i _
    rcases lt_or_ge (j : ℕ) (i : ℕ) with hij | hij
    · rw [Fr.logCoeff_eq_zero_of_lt _ _ hij, map_zero, zero_mul]
      exact wLe_zero _
    · exact (Fr.wLe_coeff_mul_X j i).mono (by simp only [jetWeight]; omega)
  exact Finset.sum_induction _ (fun F => WLe n F (jetWeight n j)) (fun _ _ => WLe.add)
    (wLe_zero _) hterm

theorem wLt_towerSub_sub_towerDiag (Fr : RittFrame K L) (b : K) (j : Fin n) :
    WLt n (Fr.towerSub b n j - Fr.towerDiag n j) (jetWeight n j) := by
  classical
  have hsplit : Fr.towerSub b n j - Fr.towerDiag n j
      = (∑ i ∈ Finset.univ.erase j, C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i)
        + C (Fr.logConst b (j : ℕ)) := by
    rw [towerSub, towerDiag,
      ← Finset.add_sum_erase Finset.univ
        (fun i : Fin n => C (Fr.logCoeff (j : ℕ) (i : ℕ)) * X i) (Finset.mem_univ j),
      Fr.logCoeff_diag (j : ℕ)]
    ring
  rw [hsplit]
  refine WLt.add ?_ (fun e he => ?_)
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
          · exact absurd (Fin.ext h.symm).symm hne
        intro e he
        exact lt_of_le_of_lt (Fr.wLe_coeff_mul_X j i e he) (by simp only [jetWeight]; omega)
    exact Finset.sum_induction _ (fun F => WLt n F (jetWeight n j)) (fun _ _ => WLt.add)
      (wLt_zero _) hterm
  · have h := wLe_C (n := n) (Fr.logConst b (j : ℕ)) 0 e he
    simp only [jetWeight]
    omega

/-- Powers of two polynomials that agree modulo a strictly lower layer agree modulo one. -/
theorem wLt_pow_sub_pow {A a : MvPolynomial (Fin n) K} {d : ℕ}
    (hA : WLe n A d) (ha : WLe n a d) (hsub : WLt n (A - a) d) :
    ∀ m : ℕ, WLt n (A ^ m - a ^ m) (m * d)
  | 0 => by
      simpa using wLt_zero (K := K) (n := n) 0
  | (m + 1) => by
      have hrw : A ^ (m + 1) - a ^ (m + 1) = A ^ m * (A - a) + (A ^ m - a ^ m) * a := by ring
      have h1 : WLt n (A ^ m * (A - a)) (m * d + d) := (hA.pow m).mul_wLt hsub
      have h2 : WLt n ((A ^ m - a ^ m) * a) (m * d + d) :=
        (wLt_pow_sub_pow hA ha hsub m).mul ha
      have hd : (m + 1) * d = m * d + d := by ring
      rw [hrw, hd]
      exact h1.add h2

theorem wLe_prod_towerSub (Fr : RittFrame K L) (b : K) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n),
      WLe n (∏ j ∈ t, Fr.towerSub b n j ^ k j) (∑ j ∈ t, k j * jetWeight n j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa using wLe_C (K := K) (n := n) 1 0
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact ((Fr.wLe_towerSub b a).pow (k a)).mul ih

theorem wLe_prod_towerDiag (Fr : RittFrame K L) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n),
      WLe n (∏ j ∈ t, Fr.towerDiag n j ^ k j) (∑ j ∈ t, k j * jetWeight n j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa using wLe_C (K := K) (n := n) 1 0
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact ((Fr.wLe_towerDiag a).pow (k a)).mul ih

/-- **The two substitutions agree modulo a strictly lower weight layer, monomial by monomial.** -/
theorem wLt_prod_sub_prod (Fr : RittFrame K L) (b : K) (k : Fin n → ℕ) :
    ∀ t : Finset (Fin n),
      WLt n ((∏ j ∈ t, Fr.towerSub b n j ^ k j) - (∏ j ∈ t, Fr.towerDiag n j ^ k j))
        (∑ j ∈ t, k j * jetWeight n j) := by
  classical
  intro t
  induction t using Finset.induction with
  | empty => simpa using wLt_zero (K := K) (n := n) 0
  | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hrw : Fr.towerSub b n a ^ k a * ∏ j ∈ t, Fr.towerSub b n j ^ k j
            - Fr.towerDiag n a ^ k a * ∏ j ∈ t, Fr.towerDiag n j ^ k j
          = (Fr.towerSub b n a ^ k a - Fr.towerDiag n a ^ k a)
              * (∏ j ∈ t, Fr.towerSub b n j ^ k j)
            + Fr.towerDiag n a ^ k a
              * ((∏ j ∈ t, Fr.towerSub b n j ^ k j)
                - (∏ j ∈ t, Fr.towerDiag n j ^ k j)) := by ring
      rw [hrw]
      refine WLt.add ?_ ?_
      · exact (wLt_pow_sub_pow (Fr.wLe_towerSub b a) (Fr.wLe_towerDiag a)
          (Fr.wLt_towerSub_sub_towerDiag b a) (k a)).mul (Fr.wLe_prod_towerSub b k t)
      · exact ((Fr.wLe_towerDiag a).pow (k a)).mul_wLt (ih)

theorem weight_eq_sum (e : Fin n →₀ ℕ) :
    Finsupp.weight (jetWeight n) e = ∑ j ∈ e.support, e j * jetWeight n j := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun j _ => smul_eq_mul _ _

theorem towerShift_monomial (Fr : RittFrame K L) (b : K) (e : Fin n →₀ ℕ) (c : K) :
    Fr.towerShift b n (monomial e c)
      = C (Fr.ψ c) * ∏ j ∈ e.support, Fr.towerSub b n j ^ e j := by
  rw [towerShift, eval₂Hom_monomial]
  rfl

theorem towerDiagShift_monomial (Fr : RittFrame K L) (e : Fin n →₀ ℕ) (c : K) :
    Fr.towerDiagShift n (monomial e c)
      = C (Fr.ψ c) * ∏ j ∈ e.support, Fr.towerDiag n j ^ e j := by
  rw [towerDiagShift, eval₂Hom_monomial]
  rfl

/-- **The tower substitution and its diagonal part agree modulo a strictly lower weight layer.** -/
theorem wLt_towerShift_sub_towerDiagShift (Fr : RittFrame K L) (b : K)
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W) :
    WLt n (Fr.towerShift b n F - Fr.towerDiagShift n F) W := by
  classical
  have hmono : ∀ e ∈ F.support,
      WLt n (Fr.towerShift b n (monomial e (coeff e F))
        - Fr.towerDiagShift n (monomial e (coeff e F))) W := by
    intro e he
    rw [Fr.towerShift_monomial b e (coeff e F), Fr.towerDiagShift_monomial e (coeff e F),
      ← mul_sub]
    refine ((wLe_C (n := n) (Fr.ψ (coeff e F)) 0).mul_wLt
      (Fr.wLt_prod_sub_prod b (fun j => e j) e.support)).mono ?_
    rw [zero_add, ← weight_eq_sum e]
    exact hF e he
  have hsum : Fr.towerShift b n F - Fr.towerDiagShift n F
      = ∑ e ∈ F.support, (Fr.towerShift b n (monomial e (coeff e F))
        - Fr.towerDiagShift n (monomial e (coeff e F))) := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← MvPolynomial.as_sum F]
  rw [hsum]
  exact Finset.sum_induction _ (fun G => WLt n G W) (fun _ _ => WLt.add) (wLt_zero _) hmono

theorem prod_towerDiag (Fr : RittFrame K L) (e : Fin n →₀ ℕ) :
    (∏ j ∈ e.support, Fr.towerDiag n j ^ e j)
      = C ((Fr.ρ ^ Finsupp.weight (jetWeight n) e)⁻¹) * monomial e (1 : K) := by
  classical
  have h1 : ∀ j : Fin n, Fr.towerDiag n j ^ e j
      = C (((Fr.ρ ^ ((j : ℕ) + 1))⁻¹) ^ e j) * X j ^ e j := by
    intro j
    rw [towerDiag, mul_pow, ← C_pow]
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_mul_distrib, ← map_prod]
  have hmon : (∏ j ∈ e.support, (X j : MvPolynomial (Fin n) K) ^ e j) = monomial e (1 : K) := by
    rw [MvPolynomial.monomial_eq, map_one, one_mul]
    rfl
  have hcoef : (∏ j ∈ e.support, ((Fr.ρ ^ ((j : ℕ) + 1))⁻¹) ^ e j)
      = (Fr.ρ ^ Finsupp.weight (jetWeight n) e)⁻¹ := by
    have h2 : ∀ j ∈ e.support, ((Fr.ρ ^ ((j : ℕ) + 1))⁻¹) ^ e j
        = (Fr.ρ⁻¹) ^ (e j * jetWeight n j) := by
      intro j _
      rw [jetWeight, ← inv_pow, ← pow_mul]
      congr 1
      ring
    rw [Finset.prod_congr rfl h2, Finset.prod_pow_eq_pow_sum, weight_eq_sum e, inv_pow]
  rw [hmon, hcoef]

theorem coeff_towerDiagShift (Fr : RittFrame K L) (F : MvPolynomial (Fin n) K)
    (d : Fin n →₀ ℕ) :
    coeff d (Fr.towerDiagShift n F)
      = Fr.ψ (coeff d F) * (Fr.ρ ^ Finsupp.weight (jetWeight n) d)⁻¹ := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial e c =>
      rw [Fr.towerDiagShift_monomial e c, Fr.prod_towerDiag e]
      have hrw : C (Fr.ψ c) * (C ((Fr.ρ ^ Finsupp.weight (jetWeight n) e)⁻¹)
            * monomial e (1 : K))
          = monomial e (Fr.ψ c * (Fr.ρ ^ Finsupp.weight (jetWeight n) e)⁻¹) := by
        rw [← mul_assoc, ← map_mul, C_mul_monomial, mul_one]
      rw [hrw, coeff_monomial, coeff_monomial]
      by_cases h : e = d
      · subst h
        simp
      · simp [h]
  | add p q hp hq =>
      rw [map_add, coeff_add, coeff_add, map_add, hp, hq]
      ring

/-- **The top weight layer of the tower substitution.**  At a monomial of maximal weight the
substitution acts by the base map on the coefficient, scaled by `ρ^{-W}`. -/
theorem coeff_towerShift_of_top (Fr : RittFrame K L) (b : K)
    {F : MvPolynomial (Fin n) K} {W : ℕ} (hF : WLe n F W)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = W) :
    coeff d (Fr.towerShift b n F) = Fr.ψ (coeff d F) * (Fr.ρ ^ W)⁻¹ := by
  have hlt := Fr.wLt_towerShift_sub_towerDiagShift b hF
  have hzero : coeff d (Fr.towerShift b n F - Fr.towerDiagShift n F) = 0 := by
    by_contra hne
    have hmem : d ∈ (Fr.towerShift b n F - Fr.towerDiagShift n F).support :=
      MvPolynomial.mem_support_iff.mpr hne
    exact absurd (hlt d hmem) (by rw [hd]; omega)
  rw [coeff_sub, sub_eq_zero] at hzero
  rw [hzero, Fr.coeff_towerDiagShift F d, hd]

/-- **The base relation carried by the top weight layer of a tower relation.**  Comparing the
coefficient at a monomial of maximal weight turns the relation `towerShift F = ρ^J·F + G` into an
affine relation in the base field, with multiplier `ρ^{J+W}` and inhomogeneity `ρ^W` times the
corresponding coefficient of `G`. -/
theorem base_relation_of_towerShift (Fr : RittFrame K L) (b : K)
    {F G : MvPolynomial (Fin n) K} {W : ℕ} {J : ℤ}
    (hF : WLe n F W)
    (hrel : Fr.towerShift b n F = C (Fr.ρ ^ J) * F + G)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = W) :
    Fr.ψ (coeff d F) = Fr.ρ ^ J * Fr.ρ ^ W * coeff d F + Fr.ρ ^ W * coeff d G := by
  have h1 := Fr.coeff_towerShift_of_top b hF hd
  have h2 : coeff d (Fr.towerShift b n F) = Fr.ρ ^ J * coeff d F + coeff d G := by
    rw [hrel, coeff_add, coeff_C_mul]
  rw [h1] at h2
  have hpow : (Fr.ρ : K) ^ W ≠ 0 := pow_ne_zero _ Fr.ρ_ne
  field_simp at h2
  linear_combination h2

/-- **Ritt's form from the top weight layer.**  If the inhomogeneity lives strictly below the top
weight, the top layer of a tower relation is a homogeneous base relation whose exponent is
`J + W`. -/
theorem homogeneous_base_relation_of_towerShift (Fr : RittFrame K L) (b : K)
    {F G : MvPolynomial (Fin n) K} {W : ℕ} {J : ℤ}
    (hF : WLe n F W) (hG : WLt n G W)
    (hrel : Fr.towerShift b n F = C (Fr.ρ ^ J) * F + G)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d = W) :
    Fr.ψ (coeff d F) = Fr.ρ ^ J * Fr.ρ ^ W * coeff d F := by
  have hGd : coeff d G = 0 := by
    by_contra hne
    exact absurd (hG d (MvPolynomial.mem_support_iff.mpr hne)) (by rw [hd]; omega)
  have h := Fr.base_relation_of_towerShift b hF hrel hd
  rw [hGd, mul_zero, add_zero] at h
  exact h

end RittFrame

end GaloisForLFunctions.HTGeometry
