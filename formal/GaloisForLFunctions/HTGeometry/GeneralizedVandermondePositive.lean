import GaloisForLFunctions.HTGeometry.SparsePolynomialPositiveRoots
import GaloisForLFunctions.HTGeometry.LocalizedPerturbationHyperbolicity

/-!
# Generalized Vandermonde determinants are positive

For strictly increasing **positive** nodes `0 < x_0 < … < x_{m-1}` and strictly increasing natural
exponents `r_0 < … < r_{m-1}`, the generalized Vandermonde determinant `det [x_l^{r_a}]` is strictly
positive.  mathlib has the classical Vandermonde determinant (`Matrix.det_vandermonde`, exponents
`0,1,…,m-1`) but not this.

The proof is the classical Descartes induction.  Letting the last node vary turns the determinant
into a real polynomial `genVandermondePoly` with at most `m` nonzero coefficients (Laplace expansion
along the varying column: each term is a signed minor times a single power `X^{r_a}`).  That
polynomial vanishes at the `m-1` smaller nodes, and by the sparse root bound
(`SparsePolynomialPositiveRoots`) it can have no further positive root; its leading coefficient is
the minor on the smaller nodes, positive by induction, so the polynomial is positive to the right of
the last known root — in particular at the last node.

## Main results

* `genVandermonde` — the matrix `[x_l ^ r_a]`;
* `det_genVandermonde_pos` — its determinant is strictly positive.
-/

namespace GaloisForLFunctions

open Polynomial Matrix

/-- The generalized Vandermonde matrix `[x_l ^ r_a]`: rows indexed by exponents, columns by
points. -/
noncomputable def genVandermonde {m : ℕ} (r : Fin m → ℕ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a l => (x l) ^ (r a)

/-- The polynomial obtained by letting the last point of a generalized Vandermonde matrix vary. -/
noncomputable def genVandermondePoly {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ) :
    ℝ[X] :=
  (Matrix.of fun (a l : Fin (m + 1)) =>
    if l = Fin.last m then (X : ℝ[X]) ^ (r a) else Polynomial.C ((x l) ^ (r a))).det

theorem eval_genVandermondePoly {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ) (t : ℝ) :
    (genVandermondePoly r x).eval t =
      (Matrix.of fun (a l : Fin (m + 1)) =>
        if l = Fin.last m then t ^ (r a) else (x l) ^ (r a)).det := by
  classical
  rw [genVandermondePoly]
  have h := RingHom.map_det (Polynomial.evalRingHom t)
    (Matrix.of fun (a l : Fin (m + 1)) =>
      if l = Fin.last m then (X : ℝ[X]) ^ (r a) else Polynomial.C ((x l) ^ (r a)))
  simp only [Polynomial.coe_evalRingHom] at h
  rw [h]
  congr 1
  ext a l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem genVandermondePoly_eval_last {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ) :
    (genVandermondePoly r x).eval (x (Fin.last m)) = (genVandermonde r x).det := by
  rw [eval_genVandermondePoly, genVandermonde]
  congr 1
  ext a l
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [h]
  · rfl

theorem genVandermondePoly_eval_castSucc {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ)
    (j : Fin m) : (genVandermondePoly r x).eval (x j.castSucc) = 0 := by
  classical
  rw [eval_genVandermondePoly]
  refine Matrix.det_zero_of_column_eq (i := j.castSucc) (j := Fin.last m)
    (Fin.castSucc_lt_last j).ne ?_
  intro a
  simp only [Matrix.of_apply]
  rw [if_neg (Fin.castSucc_lt_last j).ne]
  simp

/-- The minors of the varying-point Laplace expansion. -/
noncomputable def genVandermondeMinor {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ)
    (a : Fin (m + 1)) : ℝ :=
  (Matrix.of fun (i j : Fin m) => (x j.castSucc) ^ (r (a.succAbove i))).det

theorem genVandermondeMinor_last {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ) :
    genVandermondeMinor r x (Fin.last m)
      = (genVandermonde (fun a : Fin m => r a.castSucc) (fun l : Fin m => x l.castSucc)).det := by
  rw [genVandermondeMinor, genVandermonde]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Fin.succAbove_last]

theorem genVandermondePoly_eq {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ) :
    genVandermondePoly r x
      = ∑ a : Fin (m + 1),
        Polynomial.C ((-1 : ℝ) ^ ((a : ℕ) + m) * genVandermondeMinor r x a) * X ^ (r a) := by
  classical
  rw [genVandermondePoly, Matrix.det_succ_column _ (Fin.last m)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : (Matrix.of fun (a l : Fin (m + 1)) =>
      if l = Fin.last m then (X : ℝ[X]) ^ (r a) else Polynomial.C ((x l) ^ (r a))) a (Fin.last m)
      = (X : ℝ[X]) ^ (r a) := by simp
  have h2 : (Matrix.of fun (a l : Fin (m + 1)) =>
      if l = Fin.last m then (X : ℝ[X]) ^ (r a) else Polynomial.C ((x l) ^ (r a))).submatrix
        a.succAbove (Fin.last m).succAbove
      = (Matrix.of fun (i j : Fin m) => (x j.castSucc) ^ (r (a.succAbove i))).map Polynomial.C := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, Fin.succAbove_last]
    rw [if_neg (Fin.castSucc_lt_last j).ne]
  have h3 : ((Matrix.of fun (i j : Fin m) => (x j.castSucc) ^ (r (a.succAbove i))).map
      Polynomial.C).det = Polynomial.C (genVandermondeMinor r x a) := by
    rw [genVandermondeMinor]
    exact (RingHom.map_det (Polynomial.C : ℝ →+* ℝ[X]) _).symm
  rw [h1, h2, h3, Fin.val_last, map_mul, map_pow, map_neg, map_one]
  ring

theorem support_genVandermondePoly_subset {m : ℕ} (r : Fin (m + 1) → ℕ) (x : Fin (m + 1) → ℝ) :
    (genVandermondePoly r x).support ⊆ Finset.image r Finset.univ := by
  classical
  rw [genVandermondePoly_eq]
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  by_contra hcon
  refine hn ?_
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
  intro h
  exact hcon (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, h.symm⟩)

theorem coeff_genVandermondePoly_last {m : ℕ} {r : Fin (m + 1) → ℕ} (x : Fin (m + 1) → ℝ)
    (hr : StrictMono r) :
    (genVandermondePoly r x).coeff (r (Fin.last m)) = genVandermondeMinor r x (Fin.last m) := by
  classical
  rw [genVandermondePoly_eq, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single (Fin.last m)]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one, Fin.val_last]
    rw [Even.neg_one_pow ⟨m, by ring⟩, one_mul]
  · intro a _ hane
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro h
    exact hane (hr.injective h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem natDegree_genVandermondePoly_le {m : ℕ} {r : Fin (m + 1) → ℕ} (x : Fin (m + 1) → ℝ)
    (hr : StrictMono r) : (genVandermondePoly r x).natDegree ≤ r (Fin.last m) := by
  classical
  rw [genVandermondePoly_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_X_pow]
  exact hr.monotone (Fin.le_last a)

/-- **Generalized Vandermonde positivity.**  For strictly increasing positive nodes and strictly
increasing natural exponents, the generalized Vandermonde determinant is strictly positive. -/
theorem det_genVandermonde_pos : ∀ (m : ℕ) (r : Fin m → ℕ) (x : Fin m → ℝ),
    StrictMono r → StrictMono x → (∀ l, 0 < x l) → 0 < (genVandermonde r x).det := by
  intro m
  induction m with
  | zero =>
      intro r x _ _ _
      simp [genVandermonde]
  | succ m ih =>
      intro r x hr hx hxpos
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [genVandermonde, Matrix.det_fin_one]
        exact pow_pos (hxpos 0) _
      classical
      set y : Fin m → ℝ := fun l => x l.castSucc with hydef
      set s : Fin m → ℕ := fun a => r a.castSucc with hsdef
      have hymono : StrictMono y := fun i j hij => hx (Fin.castSucc_lt_castSucc_iff.mpr hij)
      have hsmono : StrictMono s := fun i j hij => hr (Fin.castSucc_lt_castSucc_iff.mpr hij)
      have hypos : ∀ l, 0 < y l := fun l => hxpos _
      have hminor : 0 < genVandermondeMinor r x (Fin.last m) := by
        rw [genVandermondeMinor_last]
        exact ih s y hsmono hymono hypos
      set P : ℝ[X] := genVandermondePoly r x with hPdef
      have hcoeff : P.coeff (r (Fin.last m)) = genVandermondeMinor r x (Fin.last m) :=
        coeff_genVandermondePoly_last x hr
      have hP0 : P ≠ 0 := by
        intro h
        rw [h, Polynomial.coeff_zero] at hcoeff
        exact absurd hcoeff.symm (ne_of_gt hminor)
      have hdeg : P.natDegree = r (Fin.last m) :=
        le_antisymm (natDegree_genVandermondePoly_le x hr)
          (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact ne_of_gt hminor))
      have hlead : 0 < P.leadingCoeff := by
        rw [Polynomial.leadingCoeff, hdeg, hcoeff]
        exact hminor
      have hdegpos : 0 < P.natDegree := by
        rw [hdeg]
        have : r ⟨0, by omega⟩ < r (Fin.last m) := hr (by
          simp only [Fin.lt_def, Fin.val_last]
          omega)
        omega
      -- the `m` known positive roots
      set S : Finset ℝ := Finset.image (fun j : Fin m => x j.castSucc) Finset.univ with hSdef
      have hScard : S.card = m := by
        rw [hSdef, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
        intro i j hij
        exact Fin.castSucc_injective m (hx.injective hij)
      have hSsub : S ⊆ posRoots P := by
        intro t ht
        rw [hSdef, Finset.mem_image] at ht
        obtain ⟨j, -, rfl⟩ := ht
        rw [mem_posRoots hP0]
        exact ⟨hxpos _, genVandermondePoly_eval_castSucc r x j⟩
      have hbound : (posRoots P).card ≤ m := by
        have h1 := card_posRoots_succ_le hP0
        have h2 : P.support.card ≤ m + 1 := by
          refine le_trans (Finset.card_le_card (support_genVandermondePoly_subset r x)) ?_
          refine le_trans Finset.card_image_le ?_
          simp
        omega
      have hSeq : posRoots P = S :=
        (Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hbound)).symm
      -- no root at or beyond the last node
      have hnotroot : ∀ t : ℝ, x (Fin.last m) ≤ t → P.eval t ≠ 0 := by
        intro t ht he
        have htpos : 0 < t := lt_of_lt_of_le (hxpos _) ht
        have hmem : t ∈ posRoots P := (mem_posRoots hP0).mpr ⟨htpos, he⟩
        rw [hSeq, hSdef, Finset.mem_image] at hmem
        obtain ⟨j, -, hjt⟩ := hmem
        have : x j.castSucc < x (Fin.last m) := hx (Fin.castSucc_lt_last j)
        linarith [hjt ▸ ht]
      -- positivity from the leading behaviour
      have hpos : 0 < P.eval (x (Fin.last m)) := by
        by_contra hcon
        push Not at hcon
        have hne := hnotroot _ le_rfl
        have hneg : P.eval (x (Fin.last m)) < 0 := lt_of_le_of_ne hcon hne
        obtain ⟨T, hT⟩ := (SignAlternation.eventually_pos_atTop_of_leadingCoeff_pos
          hdegpos hlead).exists_forall_of_atTop
        set T' : ℝ := max T (x (Fin.last m) + 1) with hT'
        have hT'pos : 0 < P.eval T' := hT T' (le_max_left _ _)
        have hlt : x (Fin.last m) < T' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        obtain ⟨z, hz, hz0⟩ := SignAlternation.exists_root_of_sign_change hlt
          (by nlinarith [hneg, hT'pos])
        exact hnotroot z hz.1.le hz0
      rw [← genVandermondePoly_eval_last r x]
      exact hpos

end GaloisForLFunctions
