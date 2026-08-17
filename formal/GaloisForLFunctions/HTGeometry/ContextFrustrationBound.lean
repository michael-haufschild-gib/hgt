import GaloisForLFunctions.HTGeometry.ContextOrderPSDHierarchy

/-!
# Exact context-frustration bound

If every restriction to at most `k` contexts is positive semidefinite, the total real
off-diagonal coherence is bounded below by `-n(n-1)/(2(k-1))`. The proof formalizes the exact
pair-incidence count across all `k`-subsets and proves equality for the uniform boundary kernel.
No enumeration or numerical computation is used.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Finset
open scoped ComplexOrder

noncomputable section

/-- Every ordered pair of distinct vertices occurs in exactly `choose (n-2) (k-2)` `k`-faces. -/
theorem sum_powersetCard_pair_weight {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} (hk : 2 ≤ k) {i j : I} (hij : i ≠ j) (x : ℝ) :
    ∑ S ∈ (Finset.univ : Finset I).powersetCard k,
        (if (i ∈ S) ∧ (j ∈ S) then x else 0) =
      (Nat.choose (Fintype.card I - 2) (k - 2) : ℝ) * x := by
  classical
  let p : Finset I := {i, j}
  have hp_card : p.card = 2 := by simp [p, hij]
  have hp_sub : p ⊆ (Finset.univ : Finset I) := Finset.subset_univ _
  calc
    ∑ S ∈ (Finset.univ : Finset I).powersetCard k,
        (if (i ∈ S) ∧ (j ∈ S) then x else 0) =
      ∑ S ∈ (Finset.univ : Finset I).powersetCard k,
        (if p ⊆ S then x else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          simp [p, Finset.insert_subset_iff]
    _ = ∑ S ∈ ((Finset.univ : Finset I).powersetCard k).filter (p ⊆ ·), x := by
      rw [Finset.sum_filter]
    _ = (((Finset.univ : Finset I).powersetCard k).filter (p ⊆ ·)).card * x := by
      simp
    _ = (Nat.choose (Fintype.card I - 2) (k - 2) : ℝ) * x := by
      rw [Finset.card_filter_powersetCard_subset p Finset.univ k hp_sub]
      · simp [hp_card]
      · simpa [hp_card] using hk

/-- Weighted sum over ordered distinct pairs contained in a finite context. -/
def orderedPairMass {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset I), ∑ j ∈ (Finset.univ : Finset I),
    (if (i ∈ S) ∧ (j ∈ S) ∧ i ≠ j then w i j else 0)

theorem orderedPairMass_eq {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → I → ℝ) (S : Finset I) :
    orderedPairMass w S = ∑ i ∈ S, ∑ j ∈ S.erase i, w i j := by
  classical
  have hinner (i : I) :
      ∑ j ∈ (Finset.univ : Finset I), (if (j ∈ S) ∧ i ≠ j then w i j else 0) =
        ∑ j ∈ S.erase i, w i j := by
    calc
      _ = ∑ j ∈ (Finset.univ : Finset I).filter (fun j => (j ∈ S) ∧ i ≠ j), w i j := by
        rw [Finset.sum_filter]
      _ = _ := by
        apply Finset.sum_congr
        · ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor <;> rintro ⟨h₁, h₂⟩
          · exact ⟨h₂.symm, h₁⟩
          · exact ⟨h₂, h₁.symm⟩
        · intros
          rfl
  rw [orderedPairMass]
  calc
    ∑ i ∈ (Finset.univ : Finset I), ∑ j ∈ (Finset.univ : Finset I),
        (if (i ∈ S) ∧ (j ∈ S) ∧ i ≠ j then w i j else 0) =
      ∑ i ∈ (Finset.univ : Finset I),
        (if i ∈ S then ∑ j ∈ S.erase i, w i j else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i ∈ S
          · simp only [hi, true_and, if_true]
            exact hinner i
          · simp [hi]
    _ = _ := by rw [← Finset.sum_filter]; simp

/-- Double-counting law for ordered-pair mass across all `k`-contexts. -/
theorem sum_orderedPairMass_powersetCard {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → I → ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∑ S ∈ (Finset.univ : Finset I).powersetCard k, orderedPairMass w S =
      (Nat.choose (Fintype.card I - 2) (k - 2) : ℝ) *
        orderedPairMass w Finset.univ := by
  classical
  let P := (Finset.univ : Finset I).powersetCard k
  calc
    ∑ S ∈ P, orderedPairMass w S =
        ∑ i ∈ (Finset.univ : Finset I), ∑ j ∈ (Finset.univ : Finset I),
          ∑ S ∈ P, (if (i ∈ S) ∧ (j ∈ S) ∧ i ≠ j then w i j else 0) := by
            simp only [orderedPairMass]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ = ∑ i ∈ (Finset.univ : Finset I), ∑ j ∈ (Finset.univ : Finset I),
          (Nat.choose (Fintype.card I - 2) (k - 2) : ℝ) *
            (if i ≠ j then w i j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · simpa [P, hij] using sum_powersetCard_pair_weight hk hij (w i j)
    _ = (Nat.choose (Fintype.card I - 2) (k - 2) : ℝ) *
          orderedPairMass w Finset.univ := by
      simp [orderedPairMass, Finset.mul_sum]

/-- Unit-diagonal kernel positive semidefinite on every context of size at most `k`. -/
structure KLocalCorrelation (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) where
  matrix : Matrix I I ℂ
  diagonal : ∀ i, matrix i i = 1
  localPSD : ∀ (S : Finset I), S.card ≤ k →
    (matrix.submatrix (fun x : S => x.1) (fun x : S => x.1)).PosSemidef

theorem contextOrderKernel_boundary_posSemidef
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {k : ℕ} (hk : 2 ≤ k) (hcard : Fintype.card I ≤ k) :
    (contextOrderKernel (ι := I) (1 / ((k : ℝ) - 1))).PosSemidef := by
  rw [contextOrderKernel_decomposition]
  apply Matrix.PosSemidef.add
  · apply _root_.HTGeometry.one_sub_simplexEffectiveHarmonicProjection_posSemidef.smul
    have hkR : (1 : ℝ) < k := by exact_mod_cast hk
    have hfrac : 0 ≤ 1 / ((k : ℝ) - 1) :=
      div_nonneg zero_le_one (sub_nonneg.mpr hkR.le)
    have hcoef : 0 ≤ 1 + 1 / ((k : ℝ) - 1) := add_nonneg zero_le_one hfrac
    exact_mod_cast hcoef
  · apply _root_.HTGeometry.simplexEffectiveHarmonicProjection_posSemidef.smul
    have hkR : (1 : ℝ) < k := by exact_mod_cast hk
    have hcardR : (Fintype.card I : ℝ) ≤ k := by exact_mod_cast hcard
    have hfracEq :
        ((Fintype.card I : ℝ) - 1) * (1 / ((k : ℝ) - 1)) =
          ((Fintype.card I : ℝ) - 1) / ((k : ℝ) - 1) := by
      simp [div_eq_mul_inv]
    have hquot : ((Fintype.card I : ℝ) - 1) / ((k : ℝ) - 1) ≤ 1 :=
      (div_le_iff₀ (sub_pos.mpr hkR)).mpr (by nlinarith)
    have hcoef :
        0 ≤ 1 - ((Fintype.card I : ℝ) - 1) * (1 / ((k : ℝ) - 1)) := by
      rw [hfracEq]
      exact sub_nonneg.mpr hquot
    exact_mod_cast hcoef

/-- Uniform correlation kernel saturating the `k`-context frustration bound. -/
def uniformBoundaryCorrelation {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (hk : 2 ≤ k) : KLocalCorrelation I k where
  matrix := contextOrderKernel (1 / ((k : ℝ) - 1))
  diagonal i := by simp [contextOrderKernel]
  localPSD S hSk := by
    let e : S ↪ I := ⟨fun x => x.1, fun _ _ h => Subtype.ext h⟩
    change ((contextOrderKernel (ι := I) (1 / ((k : ℝ) - 1))).submatrix e e).PosSemidef
    rw [show (contextOrderKernel (ι := I) (1 / ((k : ℝ) - 1))).submatrix e e =
        contextOrderKernel (ι := S) (1 / ((k : ℝ) - 1)) from
      contextOrderKernel_submatrix _ e]
    cases isEmpty_or_nonempty S with
    | inl hE =>
        have hzero : contextOrderKernel (ι := S) (1 / ((k : ℝ) - 1)) = 0 :=
          Subsingleton.elim _ _
        rw [hzero]
        exact Matrix.PosSemidef.zero
    | inr _ => exact contextOrderKernel_boundary_posSemidef hk (by simpa using hSk)

theorem KLocalCorrelation.local_orderedPairMass_lower
    {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (C : KLocalCorrelation I k) (S : Finset I) (hSk : S.card = k) :
    -(S.card : ℝ) ≤ orderedPairMass (fun i j => (C.matrix i j).re) S := by
  classical
  have hpsd := C.localPSD S hSk.le
  have hq := hpsd.dotProduct_mulVec_nonneg (fun _ : S => (1 : ℂ))
  have hqR := (Complex.nonneg_iff.mp hq).1
  have hattach :
      0 ≤ ∑ i ∈ S.attach, ∑ j ∈ S.attach, (C.matrix (i : I) (j : I)).re := by
    simpa [dotProduct, Matrix.mulVec] using hqR
  have hsum : 0 ≤ ∑ i ∈ S, ∑ j ∈ S, (C.matrix i j).re := by
    have hconv :
        (∑ i ∈ S.attach, ∑ j ∈ S.attach, (C.matrix (i : I) (j : I)).re) =
          ∑ i ∈ S, ∑ j ∈ S, (C.matrix i j).re := by
      calc
        _ = ∑ i ∈ S.attach, ∑ j ∈ S, (C.matrix (i : I) j).re := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_attach S (fun j => (C.matrix (i : I) j).re)
        _ = _ := Finset.sum_attach S (fun i => ∑ j ∈ S, (C.matrix i j).re)
    rw [← hconv]
    exact hattach
  have hsplit :
      ∑ i ∈ S, ∑ j ∈ S, (C.matrix i j).re =
        (S.card : ℝ) + orderedPairMass (fun i j => (C.matrix i j).re) S := by
    rw [orderedPairMass_eq]
    calc
      ∑ i ∈ S, ∑ j ∈ S, (C.matrix i j).re =
          ∑ i ∈ S, (1 + ∑ j ∈ S.erase i, (C.matrix i j).re) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              ∑ j ∈ S, (C.matrix i j).re =
                  (∑ j ∈ S.erase i, (C.matrix i j).re) + (C.matrix i i).re :=
                    (Finset.sum_erase_add S (fun j => (C.matrix i j).re) hi).symm
              _ = 1 + ∑ j ∈ S.erase i, (C.matrix i j).re := by
                rw [C.diagonal]
                norm_num
                ring
      _ = (S.card : ℝ) + ∑ i ∈ S, ∑ j ∈ S.erase i, (C.matrix i j).re := by
        simp [Finset.sum_add_distrib]
  rw [hsplit] at hsum
  linarith

theorem KLocalCorrelation.choose_weighted_frustration_bound
    {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (C : KLocalCorrelation I k) (hk : 2 ≤ k) :
    -((Nat.choose (Fintype.card I) k : ℝ) * (k : ℝ)) ≤
      (Nat.choose (Fintype.card I - 2) (k - 2) : ℝ) *
        orderedPairMass (fun i j => (C.matrix i j).re) Finset.univ := by
  classical
  let P := (Finset.univ : Finset I).powersetCard k
  have hlocal : ∀ S ∈ P,
      -(k : ℝ) ≤ orderedPairMass (fun i j => (C.matrix i j).re) S := by
    intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    simpa [hcard] using C.local_orderedPairMass_lower S hcard
  have hsum := Finset.sum_le_sum hlocal
  rw [sum_orderedPairMass_powersetCard (fun i j => (C.matrix i j).re) hk] at hsum
  have hPcard : P.card = Nat.choose (Fintype.card I) k := by
    simp [P]
  simpa [P, hPcard] using hsum

theorem choose_incidence_ratio_identity {n k : ℕ} (hk : 2 ≤ k) :
    (Nat.choose n k : ℝ) * (k : ℝ) * ((k : ℝ) - 1) =
      (n : ℝ) * ((n : ℝ) - 1) * (Nat.choose (n - 2) (k - 2) : ℝ) := by
  have hchoose := Nat.choose_mul (n := n) (k := k) hk
  have hchooseR :
      (Nat.choose n k : ℝ) * (Nat.choose k 2 : ℝ) =
        (Nat.choose n 2 : ℝ) * (Nat.choose (n - 2) (k - 2) : ℝ) := by
    exact_mod_cast hchoose
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hchooseR
  nlinarith

def contextFrustration {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℂ) : ℝ :=
  orderedPairMass (fun i j => (C i j).re) Finset.univ / 2

/-- **Exact `k`-context frustration bound.** Local PSD controls total global frustration. -/
theorem KLocalCorrelation.contextFrustration_lower
    {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (C : KLocalCorrelation I k) (hk : 2 ≤ k) (hkn : k ≤ Fintype.card I) :
    -((Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) /
        (2 * ((k : ℝ) - 1))) ≤ contextFrustration C.matrix := by
  have hweighted := C.choose_weighted_frustration_bound hk
  let B : ℝ := Nat.choose (Fintype.card I - 2) (k - 2)
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hkn 2)
  have hratio := choose_incidence_ratio_identity (n := Fintype.card I) hk
  have hkden : (k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hscaled :
      B * (-((Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) /
          (2 * ((k : ℝ) - 1)))) =
        -((Nat.choose (Fintype.card I) k : ℝ) * (k : ℝ) / 2) := by
    dsimp [B] at hratio ⊢
    field_simp
    nlinarith
  rw [contextFrustration]
  apply (mul_le_mul_iff_of_pos_left hB).mp
  rw [hscaled]
  have hhalf := (mul_le_mul_of_nonneg_right hweighted (by norm_num : (0 : ℝ) ≤ 1 / 2))
  convert hhalf using 1 <;> ring

/-- **Sharpness.** The uniform boundary correlation attains the lower bound exactly. -/
theorem uniformBoundaryCorrelation_contextFrustration
    {I : Type*} [Fintype I] [DecidableEq I]
    (k : ℕ) (hk : 2 ≤ k) :
    contextFrustration (uniformBoundaryCorrelation (I := I) k hk).matrix =
      -((Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) /
        (2 * ((k : ℝ) - 1))) := by
  have hinner (i : I) :
      ∑ j ∈ (Finset.univ : Finset I).erase i,
          ((uniformBoundaryCorrelation (I := I) k hk).matrix i j).re =
        -((Fintype.card I : ℝ) - 1) / ((k : ℝ) - 1) := by
    calc
      _ = ∑ _j ∈ (Finset.univ : Finset I).erase i,
          -(1 / ((k : ℝ) - 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            have hij : i ≠ j := hji.symm
            change (contextOrderKernel (ι := I) (1 / ((k : ℝ) - 1)) i j).re = _
            rw [contextOrderKernel, if_neg hij]
            simp only [Complex.neg_re, Complex.ofReal_re]
      _ = -((Fintype.card I : ℝ) - 1) / ((k : ℝ) - 1) := by
        have hcard : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp only [Finset.card_univ, nsmul_eq_mul]
        rw [Nat.cast_sub hcard]
        ring
  rw [contextFrustration, orderedPairMass_eq]
  simp_rw [hinner]
  simp
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
