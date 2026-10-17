import GaloisForLFunctions.BiScaleUncertainty.DivisorCellConstraints

/-!
# Canonical endpoints of arithmetic cell components

The first missing edge after a cell closes its finite component. Fibres of
this endpoint map count every finite component exactly once. Cells on an
infinite active tail use their own index as a total-function convention.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorCellHasEnd (d : ℕ) (D : Set ℕ) (k : ℕ) : Prop :=
  ∃ n, ¬ divisorGridActive d D (k+n)

def divisorCellEnd (d : ℕ) (D : Set ℕ) (k : ℕ) : ℕ :=
  if h : divisorCellHasEnd d D k then k + Nat.find h else k

theorem divisorCellEnd_of_hasEnd (d : ℕ) (D : Set ℕ) (k : ℕ)
    (h : divisorCellHasEnd d D k) : divisorCellEnd d D k = k + Nat.find h := by
  rw [divisorCellEnd, dif_pos h]

theorem divisorCellEnd_of_noEnd (d : ℕ) (D : Set ℕ) (k : ℕ)
    (h : ¬ divisorCellHasEnd d D k) : divisorCellEnd d D k = k := by
  rw [divisorCellEnd, dif_neg h]

theorem divisorCellEnd_ge (d : ℕ) (D : Set ℕ) (k : ℕ) : k ≤ divisorCellEnd d D k := by
  unfold divisorCellEnd
  split_ifs <;> omega

theorem not_active_divisorCellEnd (d : ℕ) (D : Set ℕ) (k : ℕ)
    (h : divisorCellHasEnd d D k) : ¬ divisorGridActive d D (divisorCellEnd d D k) := by
  rw [divisorCellEnd_of_hasEnd d D k h]
  exact Nat.find_spec h

theorem active_before_divisorCellEnd (d : ℕ) (D : Set ℕ) (k : ℕ)
    (h : divisorCellHasEnd d D k) (i : ℕ) (hki : k ≤ i) (hie : i < divisorCellEnd d D k) :
    divisorGridActive d D i := by
  by_contra hi
  have hw : ¬ divisorGridActive d D (k+(i-k)) := by
    simpa only [show k+(i-k)=i by omega] using hi
  have hm := Nat.find_min' h hw
  rw [divisorCellEnd_of_hasEnd d D k h] at hie
  omega

theorem divisorCellStart_add (d : ℕ) (D : Set ℕ) (k n : ℕ)
    (h : ∀ i < n, divisorGridActive d D (k+i)) :
    divisorCellStart d D (k+n) = divisorCellStart d D k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show k+(n+1)=(k+n)+1 by omega, divisorCellStart, if_pos (h n (by omega))]
      exact ih (fun i hi => h i (by omega))

theorem divisorCellStart_end (d : ℕ) (D : Set ℕ) (k : ℕ)
    (h : divisorCellHasEnd d D k) :
    divisorCellStart d D (divisorCellEnd d D k) = divisorCellStart d D k := by
  rw [divisorCellEnd_of_hasEnd d D k h]
  apply divisorCellStart_add
  intro i hi
  apply active_before_divisorCellEnd d D k h (k+i) (by omega)
  rw [divisorCellEnd_of_hasEnd d D k h]
  omega

theorem divisorCellEnd_component (d : ℕ) (D : Set ℕ) (k : ℕ)
    (h : divisorCellHasEnd d D k) :
    DivisorFiniteComponent d D (divisorCellStart d D k) (divisorCellEnd d D k+1) := by
  have hc := divisorCellStart_component d D (divisorCellEnd d D k)
    (not_active_divisorCellEnd d D k h)
  rwa [divisorCellStart_end d D k h] at hc

theorem divisorCellEnd_eq_iff (d : ℕ) (D : Set ℕ) (k j : ℕ)
    (hj : ¬ divisorGridActive d D j) :
    divisorCellEnd d D k = j ↔ divisorCellStart d D j ≤ k ∧ k < j+1 := by
  constructor
  · intro he
    by_cases h : divisorCellHasEnd d D k
    · have hs := divisorCellStart_end d D k h
      have hk := divisorCellStart_le d D k
      have hg := divisorCellEnd_ge d D k
      rw [he] at hs hg
      omega
    · have hk : k = j := (divisorCellEnd_of_noEnd d D k h).symm.trans he
      exact False.elim (h ⟨0, by simpa only [Nat.add_zero, hk] using hj⟩)
  · rintro ⟨hsk, hkj⟩
    have hw : ¬ divisorGridActive d D (k+(j-k)) := by
      simpa only [show k+(j-k)=j by omega] using hj
    have h : divisorCellHasEnd d D k := ⟨j-k, hw⟩
    have hm := Nat.find_min' h hw
    have he := divisorCellEnd_of_hasEnd d D k h
    have hg := divisorCellEnd_ge d D k
    have hne := not_active_divisorCellEnd d D k h
    by_contra hn
    have hlt : divisorCellEnd d D k < j := by omega
    exact hne (divisorCellStart_internal d D j (divisorCellEnd d D k) (by omega) hlt)

theorem divisorCellEnd_fibre (d : ℕ) (D : Set ℕ) (j : ℕ)
    (hj : ¬ divisorGridActive d D j) :
    divisorCellEnd d D ⁻¹' {j} = (Finset.Ico (divisorCellStart d D j) (j+1) : Set ℕ) := by
  ext k
  simp only [mem_preimage, mem_singleton_iff, Finset.mem_coe, Finset.mem_Ico]
  exact divisorCellEnd_eq_iff d D k j hj

theorem divisorCellEnd_active_noEnd (d : ℕ) (D : Set ℕ) (k j : ℕ)
    (hj : divisorGridActive d D j) (he : divisorCellEnd d D k = j) :
    ¬ divisorCellHasEnd d D k := by
  intro h
  apply not_active_divisorCellEnd d D k h
  rw [he]
  exact hj

def divisorComponentLength (d : ℕ) (D : Set ℕ) (j : ℕ) : ℕ :=
  j+1-divisorCellStart d D j

theorem divisorComponentLength_pos (d : ℕ) (D : Set ℕ) (j : ℕ) :
    0 < divisorComponentLength d D j := by
  have := divisorCellStart_le d D j
  unfold divisorComponentLength
  omega

theorem divisorCellEnd_zero (d : ℕ) (D : Set ℕ) : divisorCellEnd d D 0 = 0 := by
  apply (divisorCellEnd_eq_iff d D 0 0 (not_divisorGridActive_zero d D)).mpr
  simp [divisorCellStart]

theorem divisorCellHasEnd_univ_iff (d k : ℕ) : divisorCellHasEnd d Set.univ k ↔ k = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    by_contra hk
    exact hn (divisorGrid_univ_active d (k+n) (by omega))
  · rintro rfl
    exact ⟨0, not_divisorGridActive_zero d Set.univ⟩

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
