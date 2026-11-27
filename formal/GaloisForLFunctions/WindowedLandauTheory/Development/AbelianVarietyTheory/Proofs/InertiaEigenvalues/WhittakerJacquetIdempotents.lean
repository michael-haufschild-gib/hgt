import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterAlgebraAverages
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitriangularCoordinateCount

/-! The Whittaker and Jacquet averages are idempotents. Their identity
coefficients are the inverses of the corresponding unitriangular group sizes. -/

noncomputable section

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem isUniUp_one : IsUniUp (1 : Mt g n) :=
  mem_upperUnitriangular.mp (upperUnitriangular g n).one_mem

private theorem isUniUp_mul {A B : Mt g n} (hA : IsUniUp A) (hB : IsUniUp B) :
    IsUniUp (A * B) := by
  have h (M : Mt g n) (hM : IsUniUp M) : HTGeometry.IsUpperUnipotent M :=
    ⟨fun i j => (hM i j).1, fun i => (hM i i).2 rfl⟩
  have hAB := (h A hA).mul (h B hB)
  intro i j
  refine ⟨hAB.1 i j, ?_⟩
  rintro rfl
  exact hAB.2 i

private theorem entN_one_of_lt {i j : ℕ} (hij : i < j) : entN (1 : Mt g n) i j = 0 := by
  unfold entN
  split_ifs
  · exact Matrix.one_apply_ne (fun h => hij.ne (congrArg Fin.val h))
  · rfl

/-- An upper entry adds under multiplication when the entries strictly
between it and the diagonal in the right factor's column vanish. -/
private theorem entN_mul_of_zeroColumn {A B : Mt g n} (hA : IsUniUp A) (hB : IsUniUp B)
    {i j : ℕ} (hij : i < j) (hzero : ∀ b, i < b → b < j → entN B b j = 0) :
    entN (A * B) i j = entN A i j + entN B i j := by
  by_cases hj : j < n
  · have hi : i < n := hij.trans hj
    simp only [entN, hi, hj, and_self, ↓reduceDIte]
    rw [Matrix.mul_apply, Finset.sum_eq_add (⟨i, hi⟩ : Fin n) ⟨j, hj⟩]
    · rw [(hA _ _).2 rfl, (hB _ _).2 rfl, one_mul, mul_one, add_comm]
    · exact fun h => hij.ne (congrArg Fin.val h)
    · intro b _ ⟨hbi, hbj⟩
      obtain hlow | hmid := lt_or_gt_of_ne hbi
      · rw [(hA _ _).1 hlow, zero_mul]
      · obtain hmid' | hhigh := lt_or_gt_of_ne hbj
        · have hz := hzero b.val (Fin.lt_def.mp hmid) (Fin.lt_def.mp hmid')
          simp only [entN, b.isLt, hj, and_self, ↓reduceDIte, Fin.eta] at hz
          rw [hz, mul_zero]
        · rw [(hB _ _).1 hhigh, mul_zero]
    · simp
    · simp
  · simp [entN, hj]

private theorem entN_mul_superdiagonal {A B : Mt g n} (hA : IsUniUp A) (hB : IsUniUp B)
    (i : ℕ) : entN (A * B) i (i + 1) = entN A i (i + 1) + entN B i (i + 1) :=
  entN_mul_of_zeroColumn hA hB (Nat.lt_succ_self i) (fun _ hi hj => by omega)

private theorem superdiagonalSum_mul {A B : Mt g n} (hA : IsUniUp A) (hB : IsUniUp B)
    (t : ℕ) (a : ℕ → ℕ) :
    (∑ i ∈ Finset.range t, entN (A * B) (a i) (a i + 1)) =
      (∑ i ∈ Finset.range t, entN A (a i) (a i + 1)) +
      ∑ i ∈ Finset.range t, entN B (a i) (a i + 1) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => entN_mul_superdiagonal hA hB (a i)

private def zeroColumn (s k : ℕ) (M : Mt g n) : Prop :=
  IsUniUp M ∧ ∀ i, s ≤ i → i < s + k → entN M i (s + k) = 0

private theorem zeroColumn_one (s k : ℕ) : zeroColumn s k (1 : Mt g n) :=
  ⟨isUniUp_one, fun _ _ hi => entN_one_of_lt hi⟩

private theorem zeroColumn_mul {s k : ℕ} {A B : Mt g n}
    (hA : zeroColumn s k A) (hB : zeroColumn s k B) : zeroColumn s k (A * B) := by
  refine ⟨isUniUp_mul hA.1 hB.1, fun i hs hi => ?_⟩
  rw [entN_mul_of_zeroColumn hA.1 hB.1 hi
    (fun b hb => hB.2 b (hs.trans hb.le)), hA.2 i hs hi, hB.2 i hs hi, add_zero]

private theorem phiJ_mul {s k : ℕ} {A B : Mt g n}
    (hA : zeroColumn s k A) (hB : zeroColumn s k B) :
    phiJ k s (A * B) = phiJ k s A + phiJ k s B := by
  have hshift (i : ℕ) : s + k + 2 + i = s + k + 1 + i + 1 := by omega
  unfold phiJ
  simp only [hshift, superdiagonalSum_mul hA.1 hB.1]
  split_ifs with hs
  · rw [entN_mul_of_zeroColumn hA.1 hB.1 (show s - 1 < s + k by omega)
      (fun b hb => hB.2 b (by omega)), entN_mul_superdiagonal hA.1 hB.1]
    abel
  · abel

private theorem inv_card_zeroColumn (s k : ℕ) (hc : s + k < n) :
    let P (u : Gn g n) := zeroColumn s k u.val
    let U := @Finset.filter (Gn g n) P (fun u => Classical.propDecidable (P u)) Finset.univ
    (U.card : ℂ)⁻¹ = (g : ℂ) ^ k * ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  let P (u : Gn g n) := zeroColumn s k u.val
  let U := @Finset.filter (Gn g n) P (fun u => Classical.propDecidable (P u)) Finset.univ
  let S := Finset.univ.filter fun u : Gn g n => IsUniUp u.val ∧
    ∀ a, s ≤ a → a < s + k → entN u.val a (s + k) = 0
  change (U.card : ℂ)⁻¹ = _
  have he : U = S := by
    ext u
    simp only [U, P, S, zeroColumn, Finset.mem_filter]
  calc
    _ = (S.card : ℂ)⁻¹ := congrArg (fun T : Finset (Gn g n) => (T.card : ℂ)⁻¹) he
    _ = _ := inv_card_unitriangular_zeroColumn s k hc

/-- The Whittaker average projects to the Whittaker eigenspace. -/
theorem eU_mul_self_coeff_one (ψ : AddChar (ZMod g) ℂ) :
    eU g n ψ * eU g n ψ = eU g n ψ ∧
      (eU g n ψ).coeff 1 = ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  unfold eU
  obtain ⟨hid, hc⟩ := eDat_mul_self_coeff_one IsUniUp
    (fun M : Mt g n => ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)) ψ
    isUniUp_one (fun _ _ => isUniUp_mul) (fun _ _ hA hB =>
      superdiagonalSum_mul hA hB (n - 1) id)
  refine ⟨hid, hc.trans ?_⟩
  rw [card_unitriangular, Nat.cast_pow]

/-- The restricted Jacquet average has a normalization factor for each
forced zero in its distinguished column. -/
theorem eJ_mul_self_coeff_one (ψ : AddChar (ZMod g) ℂ) (k s : ℕ) (hc : s + k < n) :
    eJ g n k s ψ * eJ g n k s ψ = eJ g n k s ψ ∧
      (eJ g n k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  obtain ⟨hid, h⟩ := eDat_mul_self_coeff_one (zeroColumn s k) (phiJ k s) ψ
    (zeroColumn_one s k) (fun _ _ => zeroColumn_mul) (fun _ _ => phiJ_mul)
  exact ⟨hid, h.trans (inv_card_zeroColumn s k hc)⟩

/-- The Jacquet average using the full first superdiagonal is idempotent
with the same normalization as the corresponding restricted subgroup. -/
theorem eJ'_mul_self_coeff_one (ψ : AddChar (ZMod g) ℂ) (k : ℕ) (hk : k < n) :
    eJ' g n k ψ * eJ' g n k ψ = eJ' g n k ψ ∧
      (eJ' g n k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  have hp : zeroColumn 0 k =
      (fun M : Mt g n => IsUniUp M ∧ ∀ i, i < k → entN M i k = 0) := by
    funext M
    simp [zeroColumn]
  obtain ⟨hid, h⟩ := eDat_mul_self_coeff_one (zeroColumn 0 k)
    (fun M : Mt g n => ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)) ψ
    (zeroColumn_one 0 k) (fun _ _ => zeroColumn_mul)
    (fun _ _ hA hB => superdiagonalSum_mul hA.1 hB.1 (n - 1) id)
  have he : eDat g n (zeroColumn 0 k)
      (fun M => ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)) ψ = eJ' g n k ψ := by
    unfold eJ'
    rw [hp]
  rw [← he]
  exact ⟨hid, h.trans (inv_card_zeroColumn 0 k (by simpa using hk))⟩

end GlobalTheory.GLq
