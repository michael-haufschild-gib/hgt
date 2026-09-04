import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedPrefixComparison
import GaloisForLFunctions.HTGeometry.SiegelEntryBoundSiegel
import GaloisForLFunctions.HTGeometry.ComplexSiegelEntryBound

/-!
# Product-formula comparison for nonzero transition entries

At one infinite place a nonzero algebraic integer may be arbitrarily small, so the integer-entry
step in the classical Siegel finiteness proof cannot be applied placewise.  Instead, the real and
complex entry inequalities are summed over all infinite places.  The algebraic-integer product
formula removes the entry term globally; determinant-profile balance then returns a uniform
placewise comparison of the two Jacobi weights indexed by that nonzero transition entry.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Unified real/complex entry inequality for the transpose-frame convention of the number-field
cone action. -/
theorem exists_numberFieldArchimedean_transitionEntryBound
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K n)
      (J : NumberFieldArchimedeanJacobiData A)
      (g : Matrix.SpecialLinearGroup (Fin n) (RingOfIntegers K))
      (J' : NumberFieldArchimedeanJacobiData (g • A)),
      J.IsSiegel t u → J'.IsSiegel t u →
      ∀ (k i : Fin n) (w : InfinitePlace K),
        c * (numberFieldArchimedeanJacobiWeight J k w *
              (w (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
                RingOfIntegers K) : K)) ^ 2) ≤
          L * numberFieldArchimedeanJacobiWeight J' i w := by
  obtain ⟨c, hc, hreal, hcomplex⟩ :=
    exists_real_complex_siegel_quasiDiagonal n t u ht
  let L : ℝ := 1 + (n : ℝ) * u ^ 2 * t ^ n
  have hL : 0 < L := by
    have ht0 : 0 ≤ t ^ n := pow_nonneg (le_trans zero_le_one ht) n
    have : 0 ≤ (n : ℝ) * u ^ 2 * t ^ n := by positivity
    dsimp [L]
    linarith
  refine ⟨c, L, hc, hL, ?_⟩
  intro A J g J' hJ hJ' k i w
  rcases InfinitePlace.isReal_or_isComplex w with hw | hw
  · let wr : {w : InfinitePlace K // w.IsReal} := ⟨w, hw⟩
    let G := numberFieldRealOrderMatrixAt wr
      (g : Matrix (Fin n) (Fin n) (RingOfIntegers K))
    let γ := Matrix.transpose G
    have hform : (J'.realJacobiData wr).form =
        Matrix.transpose γ * (J.realJacobiData wr).form * γ := by
      rw [J'.realJacobiData_form, J.realJacobiData_form]
      change (G * (A.1.1 wr : Matrix (Fin n) (Fin n) ℝ) * Matrix.transpose G) = _
      simp [γ, Matrix.transpose_transpose]
    have hb := siegel_entry_bound_of_siegel ht hc (hJ'.1 wr) hform
      (hreal (J.realJacobiData wr) (hJ.1 wr)) k i
    have hweak :
        c * ((J.realJacobiData wr).d k * (γ k i) ^ 2) ≤
          L * (J'.realJacobiData wr).d i := by
      refine hb.trans (mul_le_mul_of_nonneg_right ?_ (J'.realPos wr i).le)
      dsimp [L]
      linarith
    have hz : |γ k i| =
        w (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
          RingOfIntegers K) : K) := by
      calc
        |γ k i| =
            ‖(wr.1.embedding_of_isReal wr.2)
              (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
                RingOfIntegers K) : K)‖ := by
          simp [γ, G, numberFieldRealOrderMatrixAt]
        _ = ‖((wr.1.embedding_of_isReal wr.2)
              (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
                RingOfIntegers K) : K) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ = ‖w.embedding
              (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
                RingOfIntegers K) : K)‖ := by
          exact congrArg (fun z : ℂ ↦ ‖z‖)
            (InfinitePlace.embedding_of_isReal_apply wr.2
              (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
                RingOfIntegers K) : K))
        _ = w (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
                RingOfIntegers K) : K) := InfinitePlace.norm_embedding_eq _ _
    rw [← sq_abs, hz] at hweak
    simpa [numberFieldArchimedeanJacobiWeight, hw, wr,
      NumberFieldArchimedeanJacobiData.realJacobiData] using hweak
  · let wc : {w : InfinitePlace K // w.IsComplex} := ⟨w, hw⟩
    have hnr : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
    let G := numberFieldComplexOrderMatrixAt wc
      (g : Matrix (Fin n) (Fin n) (RingOfIntegers K))
    let γ := Matrix.conjTranspose G
    have hform : (J'.complexJacobiData wc).form =
        Matrix.conjTranspose γ * (J.complexJacobiData wc).form * γ := by
      rw [J'.complexJacobiData_form, J.complexJacobiData_form]
      change (G * (A.1.2 wc : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.conjTranspose G) = _
      simp [γ]
    have hb := complex_siegel_entry_bound ht hc (hJ'.2 wc) hform
      (hcomplex (J.complexJacobiData wc) (hJ.2 wc)) k i
    have hweak :
        c * ((J.complexJacobiData wc).d k * ‖γ k i‖ ^ 2) ≤
          L * (J'.complexJacobiData wc).d i := by
      refine hb.trans (mul_le_mul_of_nonneg_right ?_
        ((J'.complexJacobiData wc).pos i).le)
      dsimp [L]
      linarith
    have hz : ‖γ k i‖ =
        w (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
          RingOfIntegers K) : K) := by
      have heval : γ k i = star (w.embedding
          (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i k :
            RingOfIntegers K) : K)) := by
        rfl
      rw [heval, norm_star, InfinitePlace.norm_embedding_eq]
    rw [hz] at hweak
    simpa [numberFieldArchimedeanJacobiWeight, hnr, wc,
      NumberFieldArchimedeanJacobiData.complexJacobiData] using hweak

/-- **A nonzero algebraic-integer transition entry forces a placewise weight comparison.**
The conclusion is uniform in the forms, orbit element, indices, and infinite place. -/
theorem exists_numberFieldArchimedean_nonzeroEntryWeightComparison
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (t u R : ℝ) (ht : 1 ≤ t) :
    ∃ Q : ℝ, 0 < Q ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K (m + 1))
      (J : NumberFieldArchimedeanJacobiData A)
      (g : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K))
      (J' : NumberFieldArchimedeanJacobiData (g • A)),
      J.IsSiegel t u → J'.IsSiegel t u →
      J.IsDetBalanced R → J'.IsDetBalanced R →
      ∀ (k i : Fin (m + 1)),
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K)) i k ≠ 0 →
      ∀ w : InfinitePlace K,
        numberFieldArchimedeanJacobiWeight J k w ≤
          Q * numberFieldArchimedeanJacobiWeight J' i w := by
  obtain ⟨c, L, hc, hL, hentry⟩ :=
    exists_numberFieldArchimedean_transitionEntryBound K (m + 1) t u ht
  let Q := Real.exp (Real.log L - Real.log c + 4 * R)
  refine ⟨Q, Real.exp_pos _, ?_⟩
  intro A J g J' hJ hJ' hbal hbal' k i hnonzero w
  let α : RingOfIntegers K :=
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K)) i k
  have hα : α ≠ 0 := hnonzero
  have hz (v : InfinitePlace K) : 0 < v (α : K) := by
    rw [← v.norm_embedding_eq, norm_pos_iff]
    exact (map_ne_zero v.embedding).2 (by exact_mod_cast hα)
  have hlocalLog (v : InfinitePlace K) :
      Real.log c +
          Real.log (numberFieldArchimedeanJacobiWeight J k v) +
            2 * Real.log (v (α : K)) ≤
        Real.log L +
          Real.log (numberFieldArchimedeanJacobiWeight J' i v) := by
    exact log_mul_sq_le_log_mul hc
      (numberFieldArchimedeanJacobiWeight_pos J k v) (hz v) hL
      (numberFieldArchimedeanJacobiWeight_pos J' i v)
      (by simpa [α, mul_assoc] using hentry A J g J' hJ hJ' k i v)
  have hsum :
      (∑ v : InfinitePlace K, (mult v : ℝ) *
          Real.log (numberFieldArchimedeanJacobiWeight J k v)) ≤
        numberFieldInfinitePlaceWeight (K := K) * (Real.log L - Real.log c) +
          ∑ v : InfinitePlace K, (mult v : ℝ) *
            Real.log (numberFieldArchimedeanJacobiWeight J' i v) := by
    exact weighted_log_sum_le (fun v : InfinitePlace K ↦ (mult v : ℝ))
      (fun v ↦ numberFieldArchimedeanJacobiWeight J k v)
      (fun v ↦ v (α : K))
      (fun v ↦ numberFieldArchimedeanJacobiWeight J' i v)
      (fun v ↦ by
        by_cases hv : v.IsReal <;> simp [InfinitePlace.mult, hv])
      hlocalLog (weightedSum_numberFieldIntegerPlaceLog_nonneg α hα)
  let M := numberFieldWeightedPlaceMean
    (fun v ↦ Real.log (numberFieldArchimedeanJacobiWeight J k v))
  let M' := numberFieldWeightedPlaceMean
    (fun v ↦ Real.log (numberFieldArchimedeanJacobiWeight J' i v))
  have hW : 0 < numberFieldInfinitePlaceWeight (K := K) :=
    numberFieldInfinitePlaceWeight_pos (K := K)
  have hmean : M - M' ≤ Real.log L - Real.log c := by
    have hM : numberFieldInfinitePlaceWeight (K := K) * M =
        ∑ v : InfinitePlace K, (mult v : ℝ) *
          Real.log (numberFieldArchimedeanJacobiWeight J k v) := by
      dsimp [M]
      rw [numberFieldWeightedPlaceMean]
      field_simp [ne_of_gt hW]
    have hM' : numberFieldInfinitePlaceWeight (K := K) * M' =
        ∑ v : InfinitePlace K, (mult v : ℝ) *
          Real.log (numberFieldArchimedeanJacobiWeight J' i v) := by
      dsimp [M']
      rw [numberFieldWeightedPlaceMean]
      field_simp [ne_of_gt hW]
    rw [← hM, ← hM'] at hsum
    nlinarith
  obtain ⟨a, ha⟩ := hbal
  obtain ⟨a', ha'⟩ := hbal'
  have hma := numberFieldArchimedeanDetBalanced_mean_sub_witness_le J R a ha k
  have hma' := numberFieldArchimedeanDetBalanced_mean_sub_witness_le J' R a' ha' i
  let p : InfinitePlace K → ℝ :=
    numberFieldCenteredPlaceProfileAverage
      (fun j v ↦ Real.log (numberFieldArchimedeanJacobiWeight J j v))
  have hp :
      numberFieldCenteredPlaceProfileAverage
          (fun j v ↦ Real.log (numberFieldArchimedeanJacobiWeight J' j v)) w = p w :=
    numberFieldCenteredJacobiProfile_smul J g J' w
  have hloc := ha k w
  have hloc' := ha' i w
  rw [hp] at hloc'
  change |M - a k| ≤ R at hma
  change |M' - a' i| ≤ R at hma'
  change
    |Real.log (numberFieldArchimedeanJacobiWeight J k w) - (a k + p w)| ≤ R at hloc
  change
    |Real.log (numberFieldArchimedeanJacobiWeight J' i w) - (a' i + p w)| ≤ R at hloc'
  have hlog :
      Real.log (numberFieldArchimedeanJacobiWeight J k w) -
          Real.log (numberFieldArchimedeanJacobiWeight J' i w) ≤
        Real.log L - Real.log c + 4 * R := by
    have hmaB := abs_le.mp hma
    have hmaB' := abs_le.mp hma'
    have hlocB := abs_le.mp hloc
    have hlocB' := abs_le.mp hloc'
    linarith
  have hd := numberFieldArchimedeanJacobiWeight_pos J k w
  have hd' := numberFieldArchimedeanJacobiWeight_pos J' i w
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log hd, Real.exp_log hd'] at hexp
  exact (div_le_iff₀ hd').mp hexp

private theorem jacobiData_cast_isSiegel
    {r : ℕ} {A B : numberFieldArchimedeanPositiveForms K r}
    (e : A = B) (J : NumberFieldArchimedeanJacobiData B)
    {t u : ℝ} (hJ : J.IsSiegel t u) :
    (e.symm ▸ J).IsSiegel t u := by
  subst B
  exact hJ

private theorem jacobiData_cast_isDetBalanced
    {r : ℕ} {A B : numberFieldArchimedeanPositiveForms K (r + 1)}
    (e : A = B) (J : NumberFieldArchimedeanJacobiData B)
    {R : ℝ} (hJ : J.IsDetBalanced R) :
    (e.symm ▸ J).IsDetBalanced R := by
  subst B
  exact hJ

private theorem jacobiData_cast_weight
    {r : ℕ} {A B : numberFieldArchimedeanPositiveForms K r}
    (e : A = B) (J : NumberFieldArchimedeanJacobiData B)
    (i : Fin r) (w : InfinitePlace K) :
    numberFieldArchimedeanJacobiWeight (e.symm ▸ J) i w =
      numberFieldArchimedeanJacobiWeight J i w := by
  subst B
  rfl

/-- Symmetric inverse-transition form of the nonzero-entry comparison. -/
theorem exists_numberFieldArchimedean_nonzeroInverseEntryWeightComparison
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (t u R : ℝ) (ht : 1 ≤ t) :
    ∃ Q : ℝ, 0 < Q ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K (m + 1))
      (J : NumberFieldArchimedeanJacobiData A)
      (g : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K))
      (J' : NumberFieldArchimedeanJacobiData (g • A)),
      J.IsSiegel t u → J'.IsSiegel t u →
      J.IsDetBalanced R → J'.IsDetBalanced R →
      ∀ (k i : Fin (m + 1)),
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K)) i k ≠ 0 →
      ∀ w : InfinitePlace K,
        numberFieldArchimedeanJacobiWeight J' k w ≤
          Q * numberFieldArchimedeanJacobiWeight J i w := by
  obtain ⟨Q, hQ, hforward⟩ :=
    exists_numberFieldArchimedean_nonzeroEntryWeightComparison K m t u R ht
  refine ⟨Q, hQ, ?_⟩
  intro A J g J' hJ hJ' hbal hbal' k i hentry w
  let heq : g⁻¹ • (g • A) = A := inv_smul_smul g A
  let Jback : NumberFieldArchimedeanJacobiData (g⁻¹ • (g • A)) := heq.symm ▸ J
  have hJback : Jback.IsSiegel t u := jacobiData_cast_isSiegel heq J hJ
  have hbalBack : Jback.IsDetBalanced R :=
    jacobiData_cast_isDetBalanced heq J hbal
  have h := hforward (g • A) J' g⁻¹ Jback hJ' hJback hbal' hbalBack
    k i hentry w
  have hweight : numberFieldArchimedeanJacobiWeight Jback i w =
      numberFieldArchimedeanJacobiWeight J i w :=
    jacobiData_cast_weight heq J i w
  rwa [hweight] at h

end

end GaloisForLFunctions.HTGeometry
