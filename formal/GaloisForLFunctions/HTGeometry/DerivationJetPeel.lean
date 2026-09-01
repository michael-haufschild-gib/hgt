import GaloisForLFunctions.HTGeometry.DerivationBorderedJetReduction

/-!
# The general peel step for jet Jacobians

A jet Jacobian with `k` rows already replaced by fixed border rows and the remaining rows the
gradients of the jets of an output `W` obeying `δ W = V · W` peels one further row: the gradient of
`W` becomes the next border row, the remaining rows become the gradients of the jets of `V`, and the
determinant picks up exactly one factor of `W` for each row that moved.

Nothing is assumed about the coordinate derivations.  The Bell chain `δ^m W = W · B_m(V)` is exact,
subtracting the Bell multiple of the pivot row is a determinant-preserving shear, the common factor
`W` leaves every moved row, and the Bell gradients are a unitriangular combination of the gradients
of the jets of `V`.

Iterating from `k = 0` replaces the whole output-jet Jacobian by the determinant of the gradients of
the iterated logarithmic derivatives `W`, `δW/W`, `δ(δW/W)/(δW/W)`, ….
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-! ## Natural-number indexed Bell values -/

/-- The Bell value governing the `m`-th jet of a terminal-linear output. -/
def bellJet (δ : Derivation ℂ R R) (A : R) (m : ℕ) : R :=
  aeval (fun i : Fin m => ((δ : R → R)^[(i : ℕ)]) A) (bellCore m)

theorem derivation_iterate_eq_bellJet (δ : Derivation ℂ R R) (x A : R) (hδx : δ x = A * x)
    (m : ℕ) : ((δ : R → R)^[m]) x = x * bellJet δ A m :=
  derivation_iterate_terminalLinear_eq_bellCore δ x A hδx m

/-- The coefficient of the `t`-th jet of `A` in the gradient of the `(s+1)`-st Bell value. -/
def bellJetCoeff (δ : Derivation ℂ R R) (A : R) (s t : ℕ) : R :=
  if h : t < s + 1 then
    aeval (fun i : Fin (s + 1) => ((δ : R → R)^[(i : ℕ)]) A) (pderiv ⟨t, h⟩ (bellCore (s + 1)))
  else 0

theorem bellJetCoeff_of_lt (δ : Derivation ℂ R R) (A : R) {s t : ℕ} (h : s < t) :
    bellJetCoeff δ A s t = 0 := by
  rw [bellJetCoeff, dif_neg (by omega)]

theorem bellJetCoeff_self (δ : Derivation ℂ R R) (A : R) (s : ℕ) :
    bellJetCoeff δ A s s = 1 := by
  rw [bellJetCoeff, dif_pos (Nat.lt_succ_self s)]
  have hlast : (⟨s, Nat.lt_succ_self s⟩ : Fin (s + 1)) = Fin.last s := rfl
  rw [hlast, pderiv_last_bellCore, map_one]

/-- **The gradient of a Bell value is a finite combination of the gradients of the jets.** -/
theorem derivation_bellJet_succ (δ : Derivation ℂ R R) (D : Derivation ℂ R R) (A : R)
    (s M : ℕ) (hM : s < M) :
    D (bellJet δ A (s + 1))
      = ∑ t ∈ Finset.range M, bellJetCoeff δ A s t * D (((δ : R → R)^[t]) A) := by
  classical
  have hbase : D (bellJet δ A (s + 1))
      = ∑ t ∈ Finset.range (s + 1), bellJetCoeff δ A s t * D (((δ : R → R)^[t]) A) := by
    rw [bellJet, derivation_aeval_eq_sum_pderiv]
    rw [← Fin.sum_univ_eq_sum_range
      (fun t => bellJetCoeff δ A s t * D (((δ : R → R)^[t]) A)) (s + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bellJetCoeff, dif_pos i.isLt]
  rw [hbase]
  have hsub : Finset.range (s + 1) ⊆ Finset.range M := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  refine Finset.sum_subset hsub ?_
  intro t _ htn
  have hts : ¬ (t < s + 1) := fun hc => htn (Finset.mem_range.mpr hc)
  have hst : s < t := Nat.lt_of_not_le fun hc => hts (Nat.lt_succ_of_le hc)
  rw [bellJetCoeff_of_lt δ A hst, zero_mul]

/-! ## The peel matrix -/

/-- The Jacobian with `k` fixed border rows and the jets of `W` below them. -/
def peelMatrix {N : ℕ} (δ : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (a : ℕ → Fin N → R) (k : ℕ) (W : R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun (i : Fin N) (j : Fin N) =>
    if (i : ℕ) < k then a (i : ℕ) j else D j (((δ : R → R)^[(i : ℕ) - k]) W)

theorem peelMatrix_zero_apply {N : ℕ} (δ : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (a : ℕ → Fin N → R) (W : R) (i j : Fin N) :
    peelMatrix δ D a 0 W i j = D j (((δ : R → R)^[(i : ℕ)]) W) := by
  simp [peelMatrix]

/-- After the Bell shear: the pivot row is the gradient of `W`, every later row is `W` times the
gradient of a Bell value. -/
private def peelMid {N : ℕ} (δ : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (a : ℕ → Fin N → R) (k : ℕ) (W V : R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun (i : Fin N) (j : Fin N) =>
    if (i : ℕ) < k then a (i : ℕ) j
    else if (i : ℕ) = k then D j W
    else W * D j (bellJet δ V ((i : ℕ) - k))

/-- The same with the common factor removed. -/
private def peelBord {N : ℕ} (δ : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (a : ℕ → Fin N → R) (k : ℕ) (W V : R) : Matrix (Fin N) (Fin N) R :=
  Matrix.of fun (i : Fin N) (j : Fin N) =>
    if (i : ℕ) < k then a (i : ℕ) j
    else if (i : ℕ) = k then D j W
    else D j (bellJet δ V ((i : ℕ) - k))

/-- The unitriangular matrix expressing the Bell gradients through the jet gradients. -/
private def peelBellMatrix {N : ℕ} (δ : Derivation ℂ R R) (V : R) (k : ℕ) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun (i : Fin N) (i' : Fin N) =>
    if (i : ℕ) ≤ k then (if i' = i then (1 : R) else 0)
    else if k < (i' : ℕ) then bellJetCoeff δ V ((i : ℕ) - k - 1) ((i' : ℕ) - k - 1) else 0

private theorem peelMatrix_det_eq_mid {N k : ℕ} (hk : k < N) (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (a : ℕ → Fin N → R) (W V : R) (hW : δ W = V * W) :
    (peelMatrix δ D a k W).det = (peelMid δ D a k W V).det := by
  classical
  refine Matrix.det_eq_of_forall_row_eq_smul_add_const
    (c := fun i : Fin N => if k < (i : ℕ) then bellJet δ V ((i : ℕ) - k) else 0)
    (k := (⟨k, hk⟩ : Fin N)) (by simp) ?_
  intro i j
  have hpivot : peelMid δ D a k W V (⟨k, hk⟩ : Fin N) j = D j W := by
    simp [peelMid]
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · simp [peelMatrix, peelMid, h, Nat.not_lt.mpr h.le]
  · simp [peelMatrix, peelMid, h]
  · rw [hpivot]
    simp only [peelMatrix, peelMid, Matrix.of_apply, if_neg (Nat.not_lt.mpr h.le),
      if_neg (by omega : ¬ ((i : ℕ) = k)), if_pos h]
    rw [derivation_iterate_eq_bellJet δ W V hW ((i : ℕ) - k), Derivation.leibniz]
    simp [smul_eq_mul]

private theorem peelMid_det {N k : ℕ} (hk : k < N) (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (a : ℕ → Fin N → R) (W V : R) :
    (peelMid δ D a k W V).det = W ^ (N - (k + 1)) * (peelBord δ D a k W V).det := by
  classical
  have hcard : (Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ k)).card = k + 1 := by
    have himg : (Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ k)).image (Fin.val)
        = Finset.range (k + 1) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · intro hm; exact ⟨⟨m, by omega⟩, by simpa using by omega, rfl⟩
    have hc := Finset.card_image_of_injective
      (Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ k)) (Fin.val_injective (n := N))
    rw [himg, Finset.card_range] at hc
    exact hc.symm
  have hprod : ∏ i : Fin N, (if (i : ℕ) ≤ k then (1 : R) else W) = W ^ (N - (k + 1)) := by
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have h1 : (Finset.univ.filter (fun i : Fin N => (i : ℕ) ≤ k)).card
        + (Finset.univ.filter (fun i : Fin N => ¬ ((i : ℕ) ≤ k))).card = N := by
      rw [Finset.card_filter_add_card_filter_not]
      simp
    rw [hcard] at h1
    omega
  have hrow : peelMid δ D a k W V
      = Matrix.of fun (i : Fin N) (j : Fin N) =>
          (if (i : ℕ) ≤ k then (1 : R) else W) * peelBord δ D a k W V i j := by
    funext i j
    rcases lt_trichotomy (i : ℕ) k with h | h | h
    · simp only [peelMid, peelBord, Matrix.of_apply, if_pos h, if_pos h.le, one_mul]
    · simp only [peelMid, peelBord, Matrix.of_apply, if_neg (by omega : ¬ ((i : ℕ) < k)),
        if_pos h, if_pos (le_of_eq h), one_mul]
    · simp only [peelMid, peelBord, Matrix.of_apply, if_neg (Nat.not_lt.mpr h.le),
        if_neg (by omega : ¬ ((i : ℕ) = k)), if_neg (Nat.not_le.mpr h)]
  rw [hrow, Matrix.det_mul_column, hprod]

private theorem peelBellMatrix_det {N k : ℕ} (δ : Derivation ℂ R R) (V : R) :
    (peelBellMatrix (N := N) δ V k).det = 1 := by
  classical
  have htri : (peelBellMatrix (N := N) δ V k).BlockTriangular (⇑OrderDual.toDual) := by
    intro i i' hlt
    have hii : (i : ℕ) < (i' : ℕ) := OrderDual.toDual_lt_toDual.mp hlt
    by_cases hik : (i : ℕ) ≤ k
    · have hne : i' ≠ i := by
        intro h; rw [h] at hii; omega
      simp only [peelBellMatrix, Matrix.of_apply, if_pos hik, if_neg hne]
    · simp only [peelBellMatrix, Matrix.of_apply, if_neg hik,
        if_pos (by omega : k < (i' : ℕ))]
      exact bellJetCoeff_of_lt δ V (by omega)
  rw [Matrix.det_of_lowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hik : (i : ℕ) ≤ k
  · simp only [peelBellMatrix, Matrix.of_apply, if_pos hik]
    simp
  · simp only [peelBellMatrix, Matrix.of_apply, if_neg hik,
      if_pos (by omega : k < (i : ℕ))]
    exact bellJetCoeff_self δ V _

private theorem peelBord_det {N k : ℕ} (hk : k < N) (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (a : ℕ → Fin N → R) (W V : R) :
    (peelBord δ D a k W V).det
      = (peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V).det := by
  classical
  have hPapply : ∀ (i j : Fin N),
      peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V i j =
        if (i : ℕ) < k + 1 then Function.update a k (fun j => D j W) (i : ℕ) j
        else D j (((δ : R → R)^[(i : ℕ) - (k + 1)]) V) := fun i j => rfl
  have hprod : peelBord δ D a k W V
      = peelBellMatrix (N := N) δ V k
        * peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V := by
    funext i j
    rw [Matrix.mul_apply]
    by_cases hik : (i : ℕ) ≤ k
    · have hsum : ∑ i' : Fin N,
          peelBellMatrix (N := N) δ V k i i'
            * peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V i' j
          = peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V i j := by
        rw [Finset.sum_eq_single i]
        · simp only [peelBellMatrix, Matrix.of_apply, if_pos hik]
          simp
        · intro b _ hb
          simp only [peelBellMatrix, Matrix.of_apply, if_pos hik, if_neg hb, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hsum, hPapply]
      rcases lt_trichotomy (i : ℕ) k with h | h | h
      · rw [if_pos (by omega : (i : ℕ) < k + 1),
          Function.update_of_ne (by omega : (i : ℕ) ≠ k)]
        simp only [peelBord, Matrix.of_apply, if_pos h]
      · rw [if_pos (by omega : (i : ℕ) < k + 1), h, Function.update_self]
        simp only [peelBord, Matrix.of_apply, if_neg (by omega : ¬ ((i : ℕ) < k)), if_pos h]
      · omega
    · have hi1 : ¬ ((i : ℕ) < k) := by omega
      have hi2 : ¬ ((i : ℕ) = k) := by omega
      obtain ⟨s, hs⟩ : ∃ s, (i : ℕ) - k = s + 1 := ⟨(i : ℕ) - k - 1, by omega⟩
      have hsk : (i : ℕ) - k - 1 = s := by omega
      simp only [peelBord, Matrix.of_apply, if_neg hi1, if_neg hi2]
      rw [hs, derivation_bellJet_succ δ (D j) V s (N - (k + 1)) (by omega)]
      have hE' : ∀ i' : Fin N,
          peelBellMatrix (N := N) δ V k i i'
              * peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V i' j
            = if k < (i' : ℕ) then
                bellJetCoeff δ V s ((i' : ℕ) - k - 1)
                  * D j (((δ : R → R)^[(i' : ℕ) - (k + 1)]) V)
              else 0 := by
        intro i'
        by_cases h' : k < (i' : ℕ)
        · rw [if_pos h']
          simp only [peelBellMatrix, Matrix.of_apply, if_neg hik, if_pos h', hsk]
          rw [hPapply, if_neg (by omega)]
        · rw [if_neg h']
          simp only [peelBellMatrix, Matrix.of_apply, if_neg hik, if_neg h', zero_mul]
      rw [Finset.sum_congr rfl (fun i' _ => hE' i')]
      rw [Fin.sum_univ_eq_sum_range
        (fun n => if k < n then
          bellJetCoeff δ V s (n - k - 1)
            * D j (((δ : R → R)^[n - (k + 1)]) V) else 0) N]
      have hsub : Finset.Ico (k + 1) N ⊆ Finset.range N := by
        intro x hx
        rw [Finset.mem_Ico] at hx
        exact Finset.mem_range.mpr hx.2
      have hzero : ∀ x ∈ Finset.range N, x ∉ Finset.Ico (k + 1) N →
          (if k < x then
            bellJetCoeff δ V s (x - k - 1)
              * D j (((δ : R → R)^[x - (k + 1)]) V) else 0) = 0 := by
        intro x hx hnx
        rw [Finset.mem_range] at hx
        rw [Finset.mem_Ico] at hnx
        rw [if_neg (by omega)]
      rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [if_pos (by omega : k < k + 1 + t)]
      have e1 : k + 1 + t - k - 1 = t := by omega
      have e2 : k + 1 + t - (k + 1) = t := by omega
      rw [e1, e2]
  rw [hprod, Matrix.det_mul, peelBellMatrix_det, one_mul]

/-- **The peel step.**  One row of jets of `W` becomes the border row `∂_j W`, the rest become the
jets of the multiplier `V`, and the determinant gains one factor of `W` for every moved row. -/
theorem peelMatrix_det_succ {N k : ℕ} (hk : k < N) (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (a : ℕ → Fin N → R) (W V : R) (hW : δ W = V * W) :
    (peelMatrix δ D a k W).det
      = W ^ (N - (k + 1)) *
        (peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V).det := by
  rw [peelMatrix_det_eq_mid hk δ D a W V hW, peelMid_det hk δ D a W V,
    peelBord_det hk δ D a W V]

/-- Nonvanishing transfers along the peel step. -/
theorem peelMatrix_det_ne_zero_of_succ {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    {N k : ℕ} (hk : k < N) (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (a : ℕ → Fin N → R) (W V : R) (hW : δ W = V * W)
    (hWne : W ≠ 0)
    (hnext : (peelMatrix δ D (Function.update a k (fun j => D j W)) (k + 1) V).det ≠ 0) :
    (peelMatrix δ D a k W).det ≠ 0 := by
  rw [peelMatrix_det_succ hk δ D a W V hW]
  exact mul_ne_zero (pow_ne_zero _ hWne) hnext

/-! ## Peeling the whole Jacobian

Iterating the step along the chain of iterated logarithmic derivatives `Y_(m+1) = δY_m / Y_m`
replaces the output-jet Jacobian by the Jacobian of the gradients of the `Y_m` themselves.
-/

/-- The gradient rows of a family. -/
def gradientMatrix {N : ℕ} (D : Fin N → Derivation ℂ R R) (Y : ℕ → R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun (i : Fin N) (j : Fin N) => D j (Y (i : ℕ))

theorem peelMatrix_full {N : ℕ} (δ : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (Y : ℕ → R) (W : R) :
    peelMatrix δ D (fun m j => D j (Y m)) N W = gradientMatrix D Y := by
  funext i j
  simp [peelMatrix, gradientMatrix]

/-- **The chain peel.**  Every level of the logarithmic-derivative chain contributes one explicit
power, and what is left is the determinant of the gradients. -/
theorem peelMatrix_det_chain {N : ℕ} (δ : Derivation ℂ R R) (D : Fin N → Derivation ℂ R R)
    (Y : ℕ → R) (hchain : ∀ m, δ (Y m) = Y (m + 1) * Y m) :
    ∀ (d k : ℕ), k + d = N →
      (peelMatrix δ D (fun m j => D j (Y m)) k (Y k)).det
        = (∏ m ∈ Finset.Ico k N, Y m ^ (N - (m + 1))) * (gradientMatrix D Y).det := by
  classical
  intro d
  induction d with
  | zero =>
      intro k hkd
      have hk : k = N := by omega
      subst hk
      rw [peelMatrix_full, Finset.Ico_self, Finset.prod_empty, one_mul]
  | succ d ih =>
      intro k hkd
      have hk : k < N := by omega
      rw [peelMatrix_det_succ hk δ D (fun m j => D j (Y m)) (Y k) (Y (k + 1)) (hchain k)]
      have hupd : Function.update (fun m j => D j (Y m)) k (fun j => D j (Y k))
          = fun m j => D j (Y m) :=
        Function.update_eq_self (β := fun _ => Fin N → R) k (fun m j => D j (Y m))
      rw [hupd, ih (k + 1) (by omega),
        Finset.prod_eq_prod_Ico_succ_bot hk (fun m => Y m ^ (N - (m + 1))), mul_assoc]

/-- **The output-jet determinant in logarithmic form.**  For an output whose iterated logarithmic
derivatives are `Y_0 = W`, `Y_(m+1) = δY_m / Y_m`, the Jacobian of the first `N` jets of `W` against
`N` coordinate derivations is an explicit monomial in the `Y_m` times the determinant of their
gradients. -/
theorem outputJacobian_det_eq_gradientMatrix {N : ℕ} (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (Y : ℕ → R) (hchain : ∀ m, δ (Y m) = Y (m + 1) * Y m) :
    (Matrix.of fun (i : Fin N) (j : Fin N) => D j (((δ : R → R)^[(i : ℕ)]) (Y 0))).det
      = (∏ m ∈ Finset.range N, Y m ^ (N - (m + 1))) * (gradientMatrix D Y).det := by
  have h := peelMatrix_det_chain δ D Y hchain N 0 (by omega)
  have hmat : peelMatrix δ D (fun m j => D j (Y m)) 0 (Y 0)
      = Matrix.of fun (i : Fin N) (j : Fin N) => D j (((δ : R → R)^[(i : ℕ)]) (Y 0)) := by
    funext i j
    exact peelMatrix_zero_apply δ D (fun m j => D j (Y m)) (Y 0) i j
  rw [hmat] at h
  rw [h, Finset.range_eq_Ico]

/-- **Observability from the gradients of the logarithmic-derivative chain.**  If every member of
the chain is nonzero and their gradients are independent, the output jets are observable. -/
theorem outputJacobian_det_ne_zero_of_gradientMatrix
    {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R] {N : ℕ} (δ : Derivation ℂ R R)
    (D : Fin N → Derivation ℂ R R) (Y : ℕ → R) (hchain : ∀ m, δ (Y m) = Y (m + 1) * Y m)
    (hne : ∀ m, Y m ≠ 0) (hgrad : (gradientMatrix D Y).det ≠ 0) :
    (Matrix.of fun (i : Fin N) (j : Fin N) => D j (((δ : R → R)^[(i : ℕ)]) (Y 0))).det ≠ 0 := by
  rw [outputJacobian_det_eq_gradientMatrix δ D Y hchain]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun m _ => pow_ne_zero _ (hne m)) hgrad

end GaloisForLFunctions.HTGeometry

end
