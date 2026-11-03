import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckePositiveWordReduction
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWordHarmonicTransport

/-!
# Primitive boundary partitions of Hecke bases

Primitive row sums select a finite complete suffix partition of the positive word
tree. The remaining prime-determinant bases have equal row sums.
-/

set_option autoImplicit false
noncomputable section
open Matrix Finset
open GaloisForLFunctions RenormalizedIntersectionTheory MayerCoding
open HTGeometry.WordSeries

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


/-- The two row sums record the action on the positive root vector `(1,1)`. -/
def heckeRowPair (A : NatMatrix) : ℕ × ℕ :=
  (A 0 0 + A 0 1, A 1 0 + A 1 1)

private theorem hecke_matrix_diagonal_pos {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) : 0 < A 0 0 ∧ 0 < A 1 1 := by
  dsimp only [HasHeckeDeterminant] at hA
  constructor
  · by_contra h
    have hz : A 0 0 = 0 := by omega
    rw [hz, zero_mul] at hA
    omega
  · by_contra h
    have hz : A 1 1 = 0 := by omega
    rw [hz, mul_zero] at hA
    omega

/-- Positive determinant forces both row sums to be positive. -/
theorem heckeRowPair_pos {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) : 0 < (heckeRowPair A).1 ∧ 0 < (heckeRowPair A).2 := by
  have hp := hecke_matrix_diagonal_pos hn hA
  dsimp only [heckeRowPair]
  omega

private theorem hecke_row_determinant {n : ℕ} {A : NatMatrix}
    (hA : HasHeckeDeterminant n A) :
    A 0 0 * (heckeRowPair A).2 = A 1 0 * (heckeRowPair A).1 + n := by
  dsimp only [HasHeckeDeterminant] at hA
  dsimp only [heckeRowPair]
  nlinarith only [hA]

/-- Coprime positive row sums whose total exceeds the determinant admit a
nonnegative matrix of that determinant. -/
theorem heckeMatrix_exists_of_coprime_rows {n r t : ℕ} (hn : 0 < n)
    (hr : 0 < r) (ht : 0 < t) (hcop : Nat.Coprime r t) (hs : n < r + t) :
    ∃ A : NatMatrix, HasHeckeDeterminant n A ∧ heckeRowPair A = (r, t) := by
  obtain ⟨m, hm, hmod⟩ := Nat.exists_mul_mod_eq_of_coprime n hcop.symm hr.ne'
  let a := if m = 0 then r else m
  have ha0 : 0 < a := by dsimp only [a]; split_ifs <;> omega
  have har : a ≤ r := by dsimp only [a]; split_ifs <;> omega
  have hamod : a * t % r = n % r := by
    dsimp only [a]
    split_ifs with hz
    · subst m
      simpa only [mul_zero, Nat.zero_mod, Nat.mul_mod_right] using hmod
    · simpa only [mul_comm] using hmod
  let c : ℤ := ((a * t / r : ℕ) : ℤ) - ((n / r : ℕ) : ℤ)
  have he : (a : ℤ) * t = (n : ℤ) + (r : ℤ) * c := by
    have h1 : ((a * t % r : ℕ) : ℤ) + (r : ℤ) * ((a * t / r : ℕ) : ℤ) = (a : ℤ) * t := by
      exact_mod_cast Nat.mod_add_div (a * t) r
    have h2 : ((n % r : ℕ) : ℤ) + (r : ℤ) * ((n / r : ℕ) : ℤ) = (n : ℤ) := by
      exact_mod_cast Nat.mod_add_div n r
    rw [hamod] at h1
    dsimp only [c]
    linear_combination h2 - h1
  have hrI : (0 : ℤ) < r := by exact_mod_cast hr
  have htI : (0 : ℤ) < t := by exact_mod_cast ht
  have hnI : (0 : ℤ) < n := by exact_mod_cast hn
  have haI : (1 : ℤ) ≤ a := by exact_mod_cast (Nat.succ_le_iff.mpr ha0)
  have harI : (a : ℤ) ≤ r := by exact_mod_cast har
  have hsI : (n : ℤ) < r + t := by exact_mod_cast hs
  have hc0 : 0 ≤ c := by
    by_contra h
    have hc : c ≤ -1 := by omega
    have hcr := mul_le_mul_of_nonneg_left hc hrI.le
    have hat := mul_le_mul_of_nonneg_right haI htI.le
    nlinarith only [he, hcr, hat, hsI]
  have hct : c < t := by
    have hat := mul_le_mul_of_nonneg_right harI htI.le
    have hm' : (r : ℤ) * c < (r : ℤ) * t := by nlinarith only [he, hat, hnI]
    by_contra hct
    have hc : (t : ℤ) ≤ c := le_of_not_gt hct
    have hm := mul_le_mul_of_nonneg_left hc hrI.le
    omega
  have hcCast : (c.toNat : ℤ) = c := Int.toNat_of_nonneg hc0
  have hcN : c.toNat < t := by
    have h : (c.toNat : ℤ) < t := by simpa only [hcCast] using hct
    exact_mod_cast h
  have heN : a * t = n + r * c.toNat := by
    have h : (a : ℤ) * t = (n : ℤ) + (r : ℤ) * (c.toNat : ℤ) := by
      simpa only [hcCast] using he
    exact_mod_cast h
  let A : NatMatrix := !![a, r - a; c.toNat, t - c.toNat]
  refine ⟨A, ?_, ?_⟩
  · change a * (t - c.toNat) = (r - a) * c.toNat + n
    have hb := Nat.sub_add_cancel har
    have hd := Nat.sub_add_cancel hcN.le
    nlinarith only [heN, hb, hd]
  · change (a + (r - a), c.toNat + (t - c.toNat)) = (r, t)
    congr 1 <;> omega

#print axioms heckeMatrix_exists_of_coprime_rows


/-- Coprime row sums determine a nonnegative positive-determinant matrix uniquely. -/
theorem heckeMatrix_eq_of_coprime_rows {n : ℕ} (hn : 0 < n) {A B : NatMatrix}
    (hA : HasHeckeDeterminant n A) (hB : HasHeckeDeterminant n B)
    (hcop : Nat.Coprime (heckeRowPair A).1 (heckeRowPair A).2)
    (hrows : heckeRowPair A = heckeRowPair B) : A = B := by
  let r := (heckeRowPair A).1
  let t := (heckeRowPair A).2
  have hr : 0 < r := (heckeRowPair_pos hn hA).1
  have hpA := hecke_matrix_diagonal_pos hn hA
  have hpB := hecke_matrix_diagonal_pos hn hB
  have h0 := congrArg Prod.fst hrows
  have h1 := congrArg Prod.snd hrows
  dsimp only [heckeRowPair] at h0 h1
  have ha : A 0 0 ≤ r := by dsimp only [r, heckeRowPair]; omega
  have hb : B 0 0 ≤ r := by dsimp only [r, heckeRowPair]; omega
  have heA : A 0 0 * t = A 1 0 * r + n := hecke_row_determinant hA
  have heB : B 0 0 * t = B 1 0 * r + n := by
    simpa only [← hrows] using hecke_row_determinant hB
  have heAI : (A 0 0 : ℤ) * t = (A 1 0 : ℤ) * r + n := by exact_mod_cast heA
  have heBI : (B 0 0 : ℤ) * t = (B 1 0 : ℤ) * r + n := by exact_mod_cast heB
  have hd : ((A 0 0 : ℤ) - B 0 0) * t = ((A 1 0 : ℤ) - B 1 0) * r := by
    linear_combination heAI - heBI
  have hz : (1 : ℤ) = (r : ℤ) * Nat.gcdA r t + (t : ℤ) * Nat.gcdB r t := by
    have h := Nat.gcd_eq_gcd_ab r t
    have hg : Nat.gcd r t = 1 := hcop
    simpa only [hg, Int.natCast_one] using h
  let k : ℤ := ((A 0 0 : ℤ) - B 0 0) * Nat.gcdA r t +
    ((A 1 0 : ℤ) - B 1 0) * Nat.gcdB r t
  have hk : (A 0 0 : ℤ) - B 0 0 = (r : ℤ) * k := by
    dsimp only [k]
    linear_combination ((A 0 0 : ℤ) - B 0 0) * hz + Nat.gcdB r t * hd
  have hrI : (0 : ℤ) < r := by exact_mod_cast hr
  have hlo : -(r : ℤ) < (A 0 0 : ℤ) - B 0 0 := by omega
  have hhi : (A 0 0 : ℤ) - B 0 0 < (r : ℤ) := by omega
  have hk0 : k = 0 := by
    by_contra h
    rcases lt_or_gt_of_ne h with hl | hu
    · have hle : k ≤ -1 := by omega
      have hm := mul_le_mul_of_nonneg_left hle hrI.le
      nlinarith only [hm, hk, hlo]
    · have hle : 1 ≤ k := by omega
      have hm := mul_le_mul_of_nonneg_left hle hrI.le
      nlinarith only [hm, hk, hhi]
  have haa : A 0 0 = B 0 0 := by
    rw [hk0, mul_zero] at hk
    exact_mod_cast sub_eq_zero.mp hk
  have hcc : A 1 0 = B 1 0 := by
    rw [haa] at heA
    have hm : A 1 0 * r = B 1 0 * r := by omega
    exact mul_right_cancel₀ hr.ne' hm
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp <;> omega

/-- The greatest common divisor of the row sums divides the determinant. -/
theorem heckeRowPair_gcd_dvd {n : ℕ} {A : NatMatrix} (hA : HasHeckeDeterminant n A) :
    Nat.gcd (heckeRowPair A).1 (heckeRowPair A).2 ∣ n := by
  have h1 := dvd_mul_of_dvd_right
    (Nat.gcd_dvd_right (heckeRowPair A).1 (heckeRowPair A).2) (A 0 0)
  have h2 := dvd_mul_of_dvd_right
    (Nat.gcd_dvd_left (heckeRowPair A).1 (heckeRowPair A).2) (A 1 0)
  rw [hecke_row_determinant hA] at h1
  apply (Nat.dvd_add_iff_left h2).mpr
  simpa only [add_comm] using h1

/-- Determinant-one matrices have primitive row sums. -/
theorem heckeRowPair_coprime_of_unimodular {A : NatMatrix} (hA : Unimodular A) :
    Nat.Coprime (heckeRowPair A).1 (heckeRowPair A).2 := by
  have h : HasHeckeDeterminant 1 A := hA
  exact Nat.dvd_one.mp (heckeRowPair_gcd_dvd h)

/-- Every primitive positive pair is the root value of a positive modular word. -/
theorem exists_matrixWord_of_coprime_rows {r t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (hcop : Nat.Coprime r t) : ∃ u : List Bool, heckeRowPair (matrixWord u) = (r, t) := by
  obtain ⟨A, hA, hrows⟩ := heckeMatrix_exists_of_coprime_rows (by norm_num : 0 < 1)
    hr ht hcop (by omega)
  obtain ⟨u, hu⟩ := exists_matrixWord A hA
  exact ⟨u, by rw [hu]; exact hrows⟩

/-- A positive word is determined by its value at the root `(1,1)`. -/
theorem matrixWord_rowPair_injective : Function.Injective (fun u => heckeRowPair (matrixWord u)) := by
  intro u v h
  apply matrixWord_injective
  exact heckeMatrix_eq_of_coprime_rows (by norm_num : 0 < 1)
    (matrixWord_unimodular u) (matrixWord_unimodular v)
    (heckeRowPair_coprime_of_unimodular (matrixWord_unimodular u)) h

#print axioms heckeMatrix_eq_of_coprime_rows
#print axioms heckeRowPair_gcd_dvd
#print axioms exists_matrixWord_of_coprime_rows
#print axioms matrixWord_rowPair_injective


/-- Row sums transform by the literal left matrix action. -/
theorem heckeRowPair_mul (A B : NatMatrix) :
    heckeRowPair (A * B) =
      (A 0 0 * (heckeRowPair B).1 + A 0 1 * (heckeRowPair B).2,
        A 1 0 * (heckeRowPair B).1 + A 1 1 * (heckeRowPair B).2) := by
  apply Prod.ext <;> simp [heckeRowPair, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A primitive root value of a product forces the right factor's root value to be primitive. -/
theorem heckeRowPair_coprime_of_mul {A B : NatMatrix}
    (h : Nat.Coprime (heckeRowPair (A * B)).1 (heckeRowPair (A * B)).2) :
    Nat.Coprime (heckeRowPair B).1 (heckeRowPair B).2 := by
  let d := Nat.gcd (heckeRowPair B).1 (heckeRowPair B).2
  have hd0 : d ∣ (heckeRowPair (A * B)).1 := by
    rw [heckeRowPair_mul]
    exact dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _)
  have hd1 : d ∣ (heckeRowPair (A * B)).2 := by
    rw [heckeRowPair_mul]
    exact dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _)
  have hd := Nat.dvd_gcd hd0 hd1
  rw [h.gcd_eq_one] at hd
  exact Nat.dvd_one.mp hd

open Classical in
/-- Actual Hecke bases whose two row sums are coprime. -/
noncomputable def primitiveHeckeSet (n : ℕ) : Finset NatMatrix :=
  (naturalHeckeSet n).filter (fun A => Nat.Coprime (heckeRowPair A).1 (heckeRowPair A).2)

/-- Each primitive Hecke basis has a unique word with the same positive root value. -/
theorem primitiveHecke_word_exists {n : ℕ} (hn : 0 < n) {B : NatMatrix}
    (hB : B ∈ primitiveHeckeSet n) :
    ∃ u : List Bool, heckeRowPair (matrixWord u) = heckeRowPair B ∧ u.length ≤ 4 * n := by
  classical
  have hb := Finset.mem_filter.mp hB
  have hdet := (mem_naturalHeckeSet_iff.mp hb.1).1
  have hp := heckeRowPair_pos hn hdet
  obtain ⟨u, hu⟩ := exists_matrixWord_of_coprime_rows hp.1 hp.2 hb.2
  have hu' : heckeRowPair (matrixWord u) = heckeRowPair B := hu
  refine ⟨u, hu', ?_⟩
  have hi : HasHeckeDeterminant 1 (1 : NatMatrix) := by norm_num [HasHeckeDeterminant, Matrix.one_apply]
  have hg := heckeMatrixSize_word_growth (by norm_num : 0 < 1) hi u
  rw [mul_one] at hg
  have hs := heckeTerminal_size_le hdet (mem_naturalHeckeSet_iff.mp hb.1).2
  have hsz : heckeMatrixSize (matrixWord u) = heckeMatrixSize B := by
    have h0 := congrArg Prod.fst hu'
    have h1 := congrArg Prod.snd hu'
    dsimp only [heckeRowPair, heckeMatrixSize] at h0 h1 ⊢
    omega
  rw [hsz] at hg
  omega

/-- Long words end in a primitive Hecke root word, at every positive determinant. -/
theorem primitiveHecke_suffix_exists {n : ℕ} (hn : 0 < n) (W : List Bool)
    (hW : n < W.length) :
    ∃ B ∈ primitiveHeckeSet n, ∃ u v : List Bool,
      heckeRowPair (matrixWord u) = heckeRowPair B ∧ W = v ++ u ∧ u.length ≤ 4 * n := by
  classical
  have hword : HasHeckeDeterminant 1 (matrixWord W) := matrixWord_unimodular W
  have hp := heckeRowPair_pos (by norm_num : 0 < 1) hword
  have hcop := heckeRowPair_coprime_of_unimodular (matrixWord_unimodular W)
  have hi : HasHeckeDeterminant 1 (1 : NatMatrix) := by norm_num [HasHeckeDeterminant, Matrix.one_apply]
  have hg := heckeMatrixSize_word_growth (by norm_num : 0 < 1) hi W
  rw [mul_one] at hg
  have hsize : n < (heckeRowPair (matrixWord W)).1 + (heckeRowPair (matrixWord W)).2 := by
    dsimp only [heckeMatrixSize, heckeRowPair] at hg ⊢
    omega
  obtain ⟨A, hA, ha⟩ := heckeMatrix_exists_of_coprime_rows hn hp.1 hp.2 hcop hsize
  have ha' : heckeRowPair A = heckeRowPair (matrixWord W) := ha
  obtain ⟨v, B, hB, htB, hv⟩ := heckeWordNormalForm_exists hn A hA
  have hbprim : Nat.Coprime (heckeRowPair B).1 (heckeRowPair B).2 := by
    apply heckeRowPair_coprime_of_mul (A := matrixWord v)
    simpa only [hv, ha'] using hcop
  have hb : B ∈ primitiveHeckeSet n := Finset.mem_filter.mpr
    ⟨mem_naturalHeckeSet_iff.mpr ⟨hB, htB⟩, hbprim⟩
  obtain ⟨u, hu, hul⟩ := primitiveHecke_word_exists hn hb
  have he : heckeRowPair (matrixWord (v ++ u)) = heckeRowPair (matrixWord W) := by
    rw [matrixWord_append, heckeRowPair_mul, hu]
    rw [← heckeRowPair_mul, hv, ha']
  exact ⟨B, hb, u, v, hu, (matrixWord_rowPair_injective he).symm, hul⟩

/-- Primitive Hecke root words form a suffix code: labels and prefixes are unique. -/
theorem primitiveHecke_suffix_unique {n : ℕ} (hn : 0 < n) {B C : NatMatrix}
    (hB : B ∈ primitiveHeckeSet n) (hC : C ∈ primitiveHeckeSet n)
    (u u' v v' : List Bool)
    (hu : heckeRowPair (matrixWord u) = heckeRowPair B)
    (hu' : heckeRowPair (matrixWord u') = heckeRowPair C)
    (hw : v ++ u = v' ++ u') : B = C ∧ v = v' ∧ u = u' := by
  classical
  have hb := mem_naturalHeckeSet_iff.mp (Finset.mem_filter.mp hB).1
  have hc := mem_naturalHeckeSet_iff.mp (Finset.mem_filter.mp hC).1
  have hvB : heckeRowPair (matrixWord v * B) = heckeRowPair (matrixWord (v ++ u)) := by
    rw [matrixWord_append, heckeRowPair_mul, heckeRowPair_mul, hu]
  have hvC : heckeRowPair (matrixWord v' * C) = heckeRowPair (matrixWord (v' ++ u')) := by
    rw [matrixWord_append, heckeRowPair_mul, heckeRowPair_mul, hu']
  have hprim : Nat.Coprime (heckeRowPair (matrixWord v * B)).1
      (heckeRowPair (matrixWord v * B)).2 := by
    rw [hvB]
    exact heckeRowPair_coprime_of_unimodular (matrixWord_unimodular (v ++ u))
  have hpair : heckeRowPair (matrixWord v * B) = heckeRowPair (matrixWord v' * C) := by
    rw [hvB, hvC, hw]
  have he := heckeMatrix_eq_of_coprime_rows hn (hasHeckeDeterminant_word_mul hb.1 v)
    (hasHeckeDeterminant_word_mul hc.1 v') hprim hpair
  obtain ⟨hvv, hBC⟩ := heckeWordNormalForm_unique hn hb.1 hc.1 hb.2 hc.2 v v' he
  refine ⟨hBC, hvv, ?_⟩
  subst v'
  exact List.append_cancel_left hw

#print axioms primitiveHecke_word_exists
#print axioms primitiveHecke_suffix_exists
#print axioms primitiveHecke_suffix_unique


private noncomputable def primitiveHeckeWord {n : ℕ} (hn : 0 < n)
    (B : {B : NatMatrix // B ∈ primitiveHeckeSet n}) : List Bool :=
  Classical.choose (primitiveHecke_word_exists hn B.property)

private theorem primitiveHeckeWord_spec {n : ℕ} (hn : 0 < n)
    (B : {B : NatMatrix // B ∈ primitiveHeckeSet n}) :
    heckeRowPair (matrixWord (primitiveHeckeWord hn B)) = heckeRowPair B.val ∧
      (primitiveHeckeWord hn B).length ≤ 4 * n :=
  Classical.choose_spec (primitiveHecke_word_exists hn B.property)

/-- The primitive Hecke root values form a complete finite harmonic partition,
for every positive determinant. -/
theorem sum_primitiveHecke_of_harmonic {n : ℕ} (hn : 0 < n) (Φ : ℕ × ℕ → ℂ)
    (hΦ : ∀ r t : ℕ, 0 < r → 0 < t → Φ (r, t) = Φ (r + t, t) + Φ (r, r + t)) :
    (∑ B ∈ primitiveHeckeSet n, Φ (heckeRowPair B)) = Φ (1, 1) := by
  classical
  let H : NatMatrix → ℂ := fun A => Φ (heckeRowPair A)
  have hi : HasHeckeDeterminant 1 (1 : NatMatrix) := by norm_num [HasHeckeDeterminant, Matrix.one_apply]
  have hH : ∀ A, HasHeckeDeterminant 1 A →
      H A = H (generator true * A) + H (generator false * A) := by
    intro A hA
    have hp := heckeRowPair_pos (by norm_num : 0 < 1) hA
    dsimp only [H]
    rw [heckeRowPair_mul, heckeRowPair_mul]
    simpa [generator] using hΦ _ _ hp.1 hp.2
  let J := {B : NatMatrix // B ∈ primitiveHeckeSet n}
  let u : J → List Bool := primitiveHeckeWord hn
  have hb : ∀ B ∈ (Finset.univ : Finset J), (u B).length ≤ 4 * n + 1 := by
    intro B hB
    exact (primitiveHeckeWord_spec hn B).2.trans (Nat.le_succ _)
  have hcover : ∀ W : List Bool, W.length = 4 * n + 1 →
      ∃ B ∈ (Finset.univ : Finset J), ∃ v : List Bool, W = v ++ u B := by
    intro W hW
    obtain ⟨B, hB, u', v, hu', hw, _⟩ := primitiveHecke_suffix_exists hn W (by omega)
    let B' : J := ⟨B, hB⟩
    have hu : u' = u B' := matrixWord_rowPair_injective
      (hu'.trans (primitiveHeckeWord_spec hn B').1.symm)
    exact ⟨B', Finset.mem_univ _, v, by rw [← hu]; exact hw⟩
  have huniq : ∀ B ∈ (Finset.univ : Finset J), ∀ C ∈ (Finset.univ : Finset J),
      ∀ v v' : List Bool, v ++ u B = v' ++ u C → B = C ∧ v = v' := by
    intro B hB C hC v v' hw
    obtain ⟨hBC, hv, _⟩ := primitiveHecke_suffix_unique hn B.property C.property
      (u B) (u C) v v' (primitiveHeckeWord_spec hn B).1 (primitiveHeckeWord_spec hn C).1 hw
    exact ⟨Subtype.ext hBC, hv⟩
  have hs := sum_heckeSuffixPartition H hH hi (Finset.univ : Finset J) u (4 * n + 1) hb hcover huniq
  have hroot : H (1 : NatMatrix) = Φ (1, 1) := by
    norm_num [H, heckeRowPair, Matrix.one_apply]
  rw [hroot] at hs
  have he : (∑ B : J, Φ (heckeRowPair B.val)) = Φ (1, 1) := by
    calc
      (∑ B : J, Φ (heckeRowPair B.val)) = ∑ B : J, H (matrixWord (u B) * 1) := by
        apply Finset.sum_congr rfl
        intro B hB
        rw [mul_one]
        exact congrArg Φ (primitiveHeckeWord_spec hn B).1.symm
      _ = Φ (1, 1) := hs
  exact (Finset.sum_coe_sort (primitiveHeckeSet n) (fun B => Φ (heckeRowPair B))).symm.trans he

#print axioms sum_primitiveHecke_of_harmonic


/-- Each row sum of a terminal Hecke basis is at most its determinant. -/
theorem heckeRowPair_le {n : ℕ} {A : NatMatrix} (hA : A ∈ naturalHeckeSet n) :
    (heckeRowPair A).1 ≤ n ∧ (heckeRowPair A).2 ≤ n := by
  have h := mem_naturalHeckeSet_iff.mp hA
  have hd := h.1
  dsimp only [HasHeckeDeterminant] at hd
  have hca := Nat.succ_le_iff.mpr h.2.1
  have hbd := Nat.succ_le_iff.mpr h.2.2
  dsimp only [heckeRowPair]
  constructor
  · have h1 := Nat.mul_le_mul_left (A 0 0) hbd
    have h2 := Nat.mul_le_mul_left (A 0 1) hca
    nlinarith only [hd, h1, h2]
  · have h1 := Nat.mul_le_mul_left (A 1 1) hca
    have h2 := Nat.mul_le_mul_left (A 1 0) hbd
    nlinarith only [hd, h1, h2]

/-- At prime determinant, every Hecke root value is primitive or equals `(p,p)`. -/
theorem primeHecke_primitive_or_equal_rows {p : ℕ} (hp : p.Prime) {A : NatMatrix}
    (hA : A ∈ naturalHeckeSet p) : A ∈ primitiveHeckeSet p ∨ heckeRowPair A = (p, p) := by
  classical
  have hdet := (mem_naturalHeckeSet_iff.mp hA).1
  rcases hp.eq_one_or_self_of_dvd _ (heckeRowPair_gcd_dvd hdet) with hg | hg
  · exact Or.inl (Finset.mem_filter.mpr ⟨hA, hg⟩)
  · right
    have h0 : p ∣ (heckeRowPair A).1 := by rw [← hg]; exact Nat.gcd_dvd_left _ _
    have h1 : p ∣ (heckeRowPair A).2 := by rw [← hg]; exact Nat.gcd_dvd_right _ _
    have hpos := heckeRowPair_pos hp.pos hdet
    have hle := heckeRowPair_le hA
    exact Prod.ext (le_antisymm hle.1 (Nat.le_of_dvd hpos.1 h0))
      (le_antisymm hle.2 (Nat.le_of_dvd hpos.2 h1))

private def equalRowHeckeMatrix (n k : ℕ) : NatMatrix :=
  !![k, n - k; k - 1, n - k + 1]

private theorem equalRowHeckeMatrix_spec {n k : ℕ} (hk : 1 ≤ k ∧ k ≤ n) :
    equalRowHeckeMatrix n k ∈ naturalHeckeSet n ∧
      heckeRowPair (equalRowHeckeMatrix n k) = (n, n) := by
  have hkn := Nat.sub_add_cancel hk.2
  have hk1 := Nat.sub_add_cancel hk.1
  constructor
  · apply mem_naturalHeckeSet_iff.mpr
    constructor
    · change k * (n - k + 1) = (n - k) * (k - 1) + n
      nlinarith only [hkn, hk1]
    · change k - 1 < k ∧ n - k < n - k + 1
      omega
  · change (k + (n - k), k - 1 + (n - k + 1)) = (n, n)
    congr 1 <;> omega

private theorem equalRowHeckeMatrix_complete {n : ℕ} (hn : 0 < n) {A : NatMatrix}
    (hA : A ∈ naturalHeckeSet n) (hrows : heckeRowPair A = (n, n)) :
    1 ≤ A 0 0 ∧ A 0 0 ≤ n ∧ equalRowHeckeMatrix n (A 0 0) = A := by
  have hdet := (mem_naturalHeckeSet_iff.mp hA).1
  have hp := hecke_matrix_diagonal_pos hn hdet
  have h0 := congrArg Prod.fst hrows
  have h1 := congrArg Prod.snd hrows
  dsimp only [heckeRowPair] at h0 h1
  have hd := hecke_row_determinant hdet
  rw [hrows] at hd
  have hm : A 0 0 * n = (A 1 0 + 1) * n := by nlinarith only [hd]
  have hac : A 0 0 = A 1 0 + 1 := mul_right_cancel₀ hn.ne' hm
  refine ⟨by omega, by omega, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp [equalRowHeckeMatrix] <;> omega

open Classical in
/-- The Hecke bases with both row sums equal to the determinant. -/
noncomputable def equalRowHeckeSet (n : ℕ) : Finset NatMatrix :=
  (naturalHeckeSet n).filter (fun A => heckeRowPair A = (n, n))

/-- Exactly `n` terminal determinant-`n` matrices have row sums `(n,n)`. -/
theorem equalRowHeckeSet_card {n : ℕ} (hn : 0 < n) : (equalRowHeckeSet n).card = n := by
  classical
  have he : equalRowHeckeSet n = (Finset.Icc 1 n).image (equalRowHeckeMatrix n) := by
    ext A
    constructor
    · intro h
      have h' := Finset.mem_filter.mp h
      obtain ⟨hk0, hkn, he⟩ := equalRowHeckeMatrix_complete hn h'.1 h'.2
      exact Finset.mem_image.mpr ⟨A 0 0, Finset.mem_Icc.mpr ⟨hk0, hkn⟩, he⟩
    · intro h
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr (equalRowHeckeMatrix_spec (Finset.mem_Icc.mp hk))
  rw [he]
  have hinj : Set.InjOn (equalRowHeckeMatrix n) (↑(Finset.Icc 1 n) : Set ℕ) := by
    intro k hk l hl he
    have h := congrArg (fun A : NatMatrix => A 0 0) he
    exact h
  rw [Finset.card_image_iff.mpr hinj]
  simp

/-- Prime Hecke root sums split exactly into the primitive partition and `p`
copies of the equal-row value. -/
theorem sum_primeHecke_rows {p : ℕ} (hp : p.Prime) (Φ : ℕ × ℕ → ℂ) :
    (∑ A ∈ naturalHeckeSet p, Φ (heckeRowPair A)) =
      (∑ A ∈ primitiveHeckeSet p, Φ (heckeRowPair A)) + (p : ℂ) * Φ (p, p) := by
  classical
  have he : naturalHeckeSet p = primitiveHeckeSet p ∪ equalRowHeckeSet p := by
    ext A
    constructor
    · intro hA
      rcases primeHecke_primitive_or_equal_rows hp hA with h | h
      · exact Finset.mem_union.mpr (Or.inl h)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hA, h⟩))
    · intro h
      rcases Finset.mem_union.mp h with h | h <;> exact (Finset.mem_filter.mp h).1
  have hd : Disjoint (primitiveHeckeSet p) (equalRowHeckeSet p) := by
    apply Finset.disjoint_left.mpr
    intro A hA hE
    have hcop := (Finset.mem_filter.mp hA).2
    have hrow := (Finset.mem_filter.mp hE).2
    have hg : Nat.gcd (heckeRowPair A).1 (heckeRowPair A).2 = 1 := hcop
    rw [hrow, Nat.gcd_self] at hg
    exact hp.ne_one hg
  rw [he, Finset.sum_union hd]
  congr 1
  calc
    (∑ A ∈ equalRowHeckeSet p, Φ (heckeRowPair A)) = ∑ _A ∈ equalRowHeckeSet p, Φ (p, p) := by
      exact Finset.sum_congr rfl (fun A hA => congrArg Φ (Finset.mem_filter.mp hA).2)
    _ = (p : ℂ) * Φ (p, p) := by rw [Finset.sum_const, equalRowHeckeSet_card hp.pos, nsmul_eq_mul]

/-- Prime Hecke evaluation of a binary-harmonic root function has only its
primitive value and its homogeneous diagonal contribution. -/
theorem sum_primeHecke_of_harmonic {p : ℕ} (hp : p.Prime) (Φ : ℕ × ℕ → ℂ)
    (hΦ : ∀ r t : ℕ, 0 < r → 0 < t → Φ (r, t) = Φ (r + t, t) + Φ (r, r + t)) :
    (∑ A ∈ naturalHeckeSet p, Φ (heckeRowPair A)) = Φ (1, 1) + (p : ℂ) * Φ (p, p) := by
  rw [sum_primeHecke_rows hp, sum_primitiveHecke_of_harmonic hp.pos Φ hΦ]

#print axioms primeHecke_primitive_or_equal_rows
#print axioms equalRowHeckeSet_card
#print axioms sum_primeHecke_rows
#print axioms sum_primeHecke_of_harmonic

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
