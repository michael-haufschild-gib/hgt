import GaloisForLFunctions.HTGeometry.OneDepthHankelBound
import GaloisForLFunctions.HTGeometry.IteratedTotalDegree
import GaloisForLFunctions.HTGeometry.ResultantDegreeBound

/-!
# The Hankel curve of a base jet at depth two

At depth two the unknown jet is `a₀ + a₁ t` above the observed packet, so the product of a fixed
fibre point's jet with it is affine-linear in the pair `(a₀, a₁)`.  The Padé–Hankel matrix is linear
in the jet, so its entries are affine-linear in that pair and its determinant is a plane curve of
degree the second depth.

Every other point of the fibre lies on that curve, by the product obstruction.  Two fibre points
therefore confine all the others to the intersection of two plane curves of degree `n`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- **A matrix of affine-linear forms in two variables.** -/
noncomputable def affineCurveMatrix (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) ((K[X])[X]) :=
  Matrix.of fun r j =>
    Polynomial.C (Polynomial.C (H₀ r j) + Polynomial.C (H₁ r j) * Polynomial.X)
      + Polynomial.C (Polynomial.C (H₂ r j)) * Polynomial.X

/-- **The entries of a matrix of affine-linear forms have total degree one.** -/
theorem totalDegLE_affineCurveMatrix (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) K) (r j : Fin n) :
    TotalDegLE (affineCurveMatrix H₀ H₁ H₂ r j) 1 := by
  intro k
  rw [affineCurveMatrix, Matrix.of_apply, Polynomial.coeff_add, Polynomial.coeff_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_X]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = 0), mul_zero, add_zero, Nat.cast_zero,
      add_zero]
    refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans Polynomial.degree_C_le (by exact_mod_cast Nat.zero_le 1)
    · refine le_trans (Polynomial.degree_mul_le _ _) ?_
      refine le_trans (add_le_add Polynomial.degree_C_le Polynomial.degree_X_le) ?_
      exact le_of_eq (by norm_num)
  · rw [if_neg (by omega : ¬ k = 0)]
    rcases eq_or_ne k 1 with rfl | hk1
    · rw [if_pos rfl, mul_one, zero_add]
      calc (C (H₂ r j) : K[X]).degree + ((1 : ℕ) : WithBot ℕ)
          ≤ 0 + ((1 : ℕ) : WithBot ℕ) := by
            gcongr
            exact Polynomial.degree_C_le
        _ = ((1 : ℕ) : WithBot ℕ) := zero_add _
    · rw [if_neg (fun h => hk1 h.symm), mul_zero, zero_add, Polynomial.degree_zero,
        WithBot.bot_add]
      exact bot_le

theorem evalPairHom_X (x y : K) : evalPairHom x y (Polynomial.X : (K[X])[X]) = y := by
  rw [evalPairHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- **Specialising an affine-linear entry.** -/
theorem evalPairHom_affineCurveMatrix (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) K) (x y : K)
    (r j : Fin n) :
    evalPairHom x y (affineCurveMatrix H₀ H₁ H₂ r j) = H₀ r j + H₁ r j * x + H₂ r j * y := by
  rw [affineCurveMatrix, Matrix.of_apply, map_add, map_mul, evalPairHom_C, evalPairHom_C,
    evalPairHom_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]

/-- **The determinant of a matrix of affine-linear forms is a plane curve of the matrix size.** -/
theorem totalDegLE_det_affineCurveMatrix (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) K) :
    TotalDegLE (affineCurveMatrix H₀ H₁ H₂).det n := by
  have := TotalDegLE.det (affineCurveMatrix H₀ H₁ H₂) (totalDegLE_affineCurveMatrix H₀ H₁ H₂)
  rwa [mul_one] at this

/-- **Exchanging the two variables exchanges the two linear parts.** -/
theorem evalPairHom_det_affineCurveMatrix_swap (H₀ H₁ H₂ : Matrix (Fin n) (Fin n) K) (x y : K) :
    evalPairHom y x (affineCurveMatrix H₀ H₂ H₁).det
      = evalPairHom x y (affineCurveMatrix H₀ H₁ H₂).det := by
  have hmat : (affineCurveMatrix H₀ H₂ H₁).map (evalPairHom y x)
      = (affineCurveMatrix H₀ H₁ H₂).map (evalPairHom x y) := by
    ext r j
    rw [Matrix.map_apply, Matrix.map_apply, evalPairHom_affineCurveMatrix,
      evalPairHom_affineCurveMatrix]
    ring
  rw [RingHom.map_det, RingHom.mapMatrix_apply, RingHom.map_det, RingHom.mapMatrix_apply, hmat]

/-- **The universal Padé–Hankel matrix of a base jet at depth two.** -/
noncomputable def hankelCurveMatrix (P₀ U : K[X]) (n : ℕ) :
    Matrix (Fin n) (Fin n) ((K[X])[X]) :=
  affineCurveMatrix (padeHankel (P₀ * U) 2 n) (padeHankel P₀ 2 n) (padeHankel (X * P₀) 2 n)

/-- **The determinant of the Hankel curve matrix is a plane curve of degree the second depth.** -/
theorem totalDegLE_det_hankelCurveMatrix (P₀ U : K[X]) :
    TotalDegLE (hankelCurveMatrix P₀ U n).det n :=
  totalDegLE_det_affineCurveMatrix _ _ _

/-- **Specialising an entry at a point of the plane.** -/
theorem evalPairHom_hankelCurveMatrix (P₀ U : K[X]) (a₀ a₁ : K) (r j : Fin n) :
    evalPairHom a₀ a₁ (hankelCurveMatrix P₀ U n r j)
      = padeHankel (P₀ * (C a₀ + C a₁ * X + U)) 2 n r j := by
  have hexpand : P₀ * (C a₀ + C a₁ * X + U)
      = C a₀ * P₀ + (C a₁ * (X * P₀) + P₀ * U) := by ring
  rw [hexpand, padeHankel_C_mul_add, padeHankel_C_mul_add, hankelCurveMatrix,
    evalPairHom_affineCurveMatrix]
  simp [Matrix.add_apply, Matrix.smul_apply]
  ring

/-- **Specialising the curve at a point of the plane.** -/
theorem evalPairHom_det_hankelCurveMatrix (P₀ U : K[X]) (a₀ a₁ : K) :
    evalPairHom a₀ a₁ (hankelCurveMatrix P₀ U n).det
      = (padeHankel (P₀ * (C a₀ + C a₁ * X + U)) 2 n).det := by
  have hmat : (hankelCurveMatrix P₀ U n).map (evalPairHom a₀ a₁)
      = padeHankel (P₀ * (C a₀ + C a₁ * X + U)) 2 n := by
    ext r j
    rw [Matrix.map_apply]
    exact evalPairHom_hankelCurveMatrix P₀ U a₀ a₁ r j
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmat]

/-- **Every fibre point other than the base one lies on the base point's Hankel curve.** -/
theorem evalPairHom_det_hankelCurveMatrix_eq_zero {U V : K[X]}
    (hU : (X : K[X]) ^ 2 ∣ U) (hV : (X : K[X]) ^ n ∣ V) (hn : 0 < n)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (p q : criticalFibre K 2 n U V) (hpq : p ≠ q) :
    evalPairHom (q.1.1.coeff 0) (q.1.1.coeff 1)
        (hankelCurveMatrix (p.1.1 + U) U n).det = 0 := by
  have hq : q.1.1 = C (q.1.1.coeff 0) + C (q.1.1.coeff 1) * X := by
    refine Polynomial.ext fun i => ?_
    match i with
    | 0 => simp
    | 1 => simp
    | (k + 2) =>
      rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le q.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2)))]
      simp
  rw [evalPairHom_det_hankelCurveMatrix, ← hq]
  exact det_padeHankel_product_eq_zero (by omega) hn hU hV hU0 hV0 p q hpq


/-! ## The count at depth two -/

/-- The Hankel curve of a base jet. -/
noncomputable def hankelCurve (P₀ U : K[X]) (n : ℕ) : (K[X])[X] :=
  (hankelCurveMatrix P₀ U n).det

/-- The same curve with the two jet coordinates exchanged. -/
noncomputable def hankelCurveSwap (P₀ U : K[X]) (n : ℕ) : (K[X])[X] :=
  (affineCurveMatrix (padeHankel (P₀ * U) 2 n) (padeHankel (X * P₀) 2 n)
    (padeHankel P₀ 2 n)).det

theorem totalDegLE_hankelCurve (P₀ U : K[X]) : TotalDegLE (hankelCurve P₀ U n) n :=
  totalDegLE_det_affineCurveMatrix _ _ _

theorem totalDegLE_hankelCurveSwap (P₀ U : K[X]) : TotalDegLE (hankelCurveSwap P₀ U n) n :=
  totalDegLE_det_affineCurveMatrix _ _ _

theorem evalPairHom_hankelCurveSwap (P₀ U : K[X]) (x y : K) :
    evalPairHom y x (hankelCurveSwap P₀ U n) = evalPairHom x y (hankelCurve P₀ U n) :=
  evalPairHom_det_affineCurveMatrix_swap _ _ _ x y

/-- The degree of the eliminant of two plane curves of degree `n`. -/
theorem natDegree_resultant_hankel_le {F G : (K[X])[X]} (hF : TotalDegLE F n)
    (hG : TotalDegLE G n) (hres : Polynomial.resultant F G n n ≠ 0) :
    (Polynomial.resultant F G n n).natDegree ≤ n * n := by
  have h := natDegree_resultant_add_le hF hG n n hres
  omega

/-- **At depth two the fibre is finite, with an explicit bound, for every `n` and every observed
packet.**  Two fibre points confine all the others to the intersection of two plane curves of degree
`n`; the two eliminants then bound each coordinate. -/
theorem nat_card_criticalFibre_depth_two_le (hn : 0 < n) {U V : K[X]}
    (hU : (X : K[X]) ^ 2 ∣ U) (hV : (X : K[X]) ^ n ∣ V)
    (hU0 : U.coeff 0 = 0) (hV0 : V.coeff 0 = 0)
    (hgen : ∀ p q : criticalFibre K 2 n U V, p ≠ q →
      Polynomial.resultant (hankelCurve (p.1.1 + U) U n) (hankelCurve (q.1.1 + U) U n) n n ≠ 0 ∧
      Polynomial.resultant (hankelCurveSwap (p.1.1 + U) U n)
        (hankelCurveSwap (q.1.1 + U) U n) n n ≠ 0) :
    Nat.card (criticalFibre K 2 n U V) ≤ 2 + n * n * (n * n) := by
  classical
  rcases subsingleton_or_nontrivial (criticalFibre K 2 n U V) with hsub | hnt
  · have hone : Nat.card (criticalFibre K 2 n U V) ≤ 1 := by
      rcases isEmpty_or_nonempty (criticalFibre K 2 n U V) with hemp | hnem
      · rw [Nat.card_of_isEmpty]
        omega
      · obtain ⟨x⟩ := hnem
        haveI : Unique (criticalFibre K 2 n U V) := uniqueOfSubsingleton x
        rw [Nat.card_unique]
    omega
  obtain ⟨p₀, p₁, hne⟩ := exists_pair_ne (criticalFibre K 2 n U V)
  obtain ⟨hres1, hres2⟩ := hgen p₀ p₁ hne
  set F : (K[X])[X] := hankelCurve (p₀.1.1 + U) U n with hF
  set G : (K[X])[X] := hankelCurve (p₁.1.1 + U) U n with hG
  set F' : (K[X])[X] := hankelCurveSwap (p₀.1.1 + U) U n with hF'
  set G' : (K[X])[X] := hankelCurveSwap (p₁.1.1 + U) U n with hG'
  set R₁ : Finset K := (Polynomial.resultant F G n n).roots.toFinset with hR₁
  set R₂ : Finset K := (Polynomial.resultant F' G' n n).roots.toFinset with hR₂
  set T : Finset (K × K) :=
    insert (p₀.1.1.coeff 0, p₀.1.1.coeff 1)
      (insert (p₁.1.1.coeff 0, p₁.1.1.coeff 1) (R₁ ×ˢ R₂)) with hT
  have hmem : ∀ q : criticalFibre K 2 n U V, (q.1.1.coeff 0, q.1.1.coeff 1) ∈ T := by
    intro q
    rcases eq_or_ne q p₀ with rfl | h0
    · exact Finset.mem_insert_self _ _
    rcases eq_or_ne q p₁ with rfl | h1
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hFq : evalPairHom (q.1.1.coeff 0) (q.1.1.coeff 1) F = 0 :=
      evalPairHom_det_hankelCurveMatrix_eq_zero hU hV hn hU0 hV0 p₀ q (Ne.symm h0)
    have hGq : evalPairHom (q.1.1.coeff 0) (q.1.1.coeff 1) G = 0 :=
      evalPairHom_det_hankelCurveMatrix_eq_zero hU hV hn hU0 hV0 p₁ q (Ne.symm h1)
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_product.2 ⟨?_, ?_⟩))
    · exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hres1).2
        (eval_resultant_eq_zero_of_common_zero (totalDegLE_hankelCurve _ _).natDegree_le
          (totalDegLE_hankelCurve _ _).natDegree_le (Or.inl (by omega)) hFq hGq))
    · refine Multiset.mem_toFinset.2 ((Polynomial.mem_roots hres2).2
        (eval_resultant_eq_zero_of_common_zero (x := q.1.1.coeff 1) (y := q.1.1.coeff 0)
          (totalDegLE_hankelCurveSwap _ _).natDegree_le
          (totalDegLE_hankelCurveSwap _ _).natDegree_le (Or.inl (by omega)) ?_ ?_))
      · rw [evalPairHom_hankelCurveSwap]
        exact hFq
      · rw [evalPairHom_hankelCurveSwap]
        exact hGq
  have hinj : Function.Injective
      (fun q : criticalFibre K 2 n U V => (⟨(q.1.1.coeff 0, q.1.1.coeff 1), hmem q⟩ : T)) := by
    intro q r hqr
    have hpair : (q.1.1.coeff 0, q.1.1.coeff 1) = (r.1.1.coeff 0, r.1.1.coeff 1) :=
      congrArg Subtype.val hqr
    refine criticalFibre_fst_injective (by omega) hn hU0 hV0 ?_
    show q.1.1 = r.1.1
    refine Polynomial.ext fun i => ?_
    match i with
    | 0 => exact congrArg Prod.fst hpair
    | 1 => exact congrArg Prod.snd hpair
    | (k + 2) =>
      rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le q.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2))),
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le r.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2)))]
  have hR₁card : R₁.card ≤ n * n := by
    calc R₁.card ≤ Multiset.card (Polynomial.resultant F G n n).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.resultant F G n n).natDegree := Polynomial.card_roots' _
      _ ≤ n * n := natDegree_resultant_hankel_le (totalDegLE_hankelCurve _ _)
          (totalDegLE_hankelCurve _ _) hres1
  have hR₂card : R₂.card ≤ n * n := by
    calc R₂.card ≤ Multiset.card (Polynomial.resultant F' G' n n).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.resultant F' G' n n).natDegree := Polynomial.card_roots' _
      _ ≤ n * n := natDegree_resultant_hankel_le (totalDegLE_hankelCurveSwap _ _)
          (totalDegLE_hankelCurveSwap _ _) hres2
  have hTcard : T.card ≤ 2 + n * n * (n * n) := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 := Finset.card_insert_le (p₁.1.1.coeff 0, p₁.1.1.coeff 1) (R₁ ×ˢ R₂)
    have h3 : (R₁ ×ˢ R₂).card = R₁.card * R₂.card := Finset.card_product _ _
    have h4 : R₁.card * R₂.card ≤ n * n * (n * n) := Nat.mul_le_mul hR₁card hR₂card
    omega
  calc Nat.card (criticalFibre K 2 n U V)
      ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 + n * n * (n * n) := hTcard

end GaloisForLFunctions.HTGeometry
