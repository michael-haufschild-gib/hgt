import GaloisForLFunctions.HTGeometry.RittAffineTowerDichotomy
import GaloisForLFunctions.HTGeometry.RittJetIndependence

/-!
# The affine exceptional datum drops a level

The affine exceptional datum is a relation `σ v = ρ^{−1}·v + h` with `h` a nonzero base constant.
Its linear coefficient in the top coordinate is zero, so the level dichotomy's first branch applies
whenever `v` already lies one level down, and its fourth branch — the only one needing a nonzero
linear coefficient — cannot fire.  What is left is:

* the datum itself one level down, unchanged;
* the affine connection of the coordinate, which is a seeded relation one level down whose top Faà di
  Bruno coefficient is nonzero;
* the degree-one branch, whose leading coefficient satisfies a homogeneous relation and whose
  constant coefficient satisfies the companion relation supplied by the constant-term identity — the
  homogeneous exceptional datum one level down.

The "no shift defect" branch is impossible above jet order one.  So above jet order two the affine
exceptional datum always drops a level, into one of the three shapes the induction tracks.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- The jet prefix fields increase with the order. -/
theorem jetPrefixField_mono (Fr : RittFrame K L) (τ : L) {a b : ℕ} (hab : a ≤ b) :
    Fr.jetPrefixField τ a ≤ Fr.jetPrefixField τ b := by
  rw [RittFrame.jetPrefixField, RittFrame.jetPrefixField]
  refine IntermediateField.adjoin.mono K _ _ ?_
  rintro x ⟨j, hj, rfl⟩
  exact ⟨j, by omega, rfl⟩

/-- **The affine exceptional datum drops a level.** -/
theorem excAff_descends (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) {m : ℕ} (hm : 3 ≤ m)
    (htr : ∀ j, j < m → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ))
    {v : L} {h : K} (hv0 : v ≠ 0) (hh0 : h ≠ 0) (hvmem : v ∈ Fr.jetPrefixField τ m)
    (hrel : Fr.σ v = algebraMap K L (Fr.ρ)⁻¹ * v + algebraMap K L h) :
    (∃ (w : L) (A : ℕ → K), w ≠ 0 ∧ w ∈ Fr.jetPrefixField τ (m - 1) ∧ A (m - 2) ≠ 0 ∧
      Fr.σ w = algebraMap K L (q / Fr.ρ ^ (m - 1)) * w
        + ∑ j ∈ Finset.range (m - 1), algebraMap K L (A j) * Fr.d^[j] τ) ∨
    (∃ v' : L, v' ≠ 0 ∧ v' ∈ Fr.jetPrefixField τ (m - 1) ∧
      Fr.σ v' = algebraMap K L (Fr.ρ)⁻¹ * v' + algebraMap K L h) ∨
    (∃ (v' y : L), v' ≠ 0 ∧ v' ∈ Fr.jetPrefixField τ (m - 1) ∧
      y ∈ Fr.jetPrefixField τ (m - 1) ∧
      Fr.σ v' = algebraMap K L (q⁻¹ * Fr.ρ ^ (m - 1 - 1)) * v' ∧
      Fr.σ y = algebraMap K L (q / Fr.ρ ^ (m - 1)) * y
        + algebraMap K L (q / Fr.ρ ^ (m - 1)) * algebraMap K L h
            / (algebraMap K L (Fr.ρ)⁻¹ * v')
        - (Fr.σ (Fr.d^[m - 1] τ)
            - algebraMap K L (q / Fr.ρ ^ (m - 1)) * Fr.d^[m - 1] τ)) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hpm : m - 1 = p := by omega
  have hp2 : 2 ≤ p := by omega
  have hvmem' : v ∈ Fr.jetPrefixField τ (p + 1) := by rw [← hp]; exact hvmem
  have hβmem : algebraMap K L h ∈ Fr.jetPrefixField τ p :=
    IntermediateField.algebraMap_mem _ _
  have hcinv : (Fr.ρ)⁻¹ ≠ 0 := inv_ne_zero hρ0
  have hrelp : Fr.σ v = algebraMap K L (Fr.ρ)⁻¹ * v
      + (algebraMap K L (0 : K) * Fr.d^[p] τ + algebraMap K L h) := by
    rw [map_zero, zero_mul, zero_add]
    exact hrel
  rcases affine_descent_dichotomy_gen Fr hqconst hshift hq (htr p (by omega)) hv0 hvmem'
      hcinv hβmem hrelp with
      ⟨-, hmem⟩ | hdiag | ⟨w, N, A', hw0, hwmem, hN, hAsh, hconn⟩ |
      ⟨-, -, -, -, -, -, -, hαne, -, -, -⟩ | h5
  · -- the datum drops a level unchanged
    refine Or.inr (Or.inl ⟨v, hv0, ?_, hrel⟩)
    rw [hpm]
    exact hmem
  · -- impossible: the shift defect does not vanish above jet order one
    exfalso
    obtain ⟨r, hr⟩ : ∃ r, p = r + 2 := ⟨p - 2, by omega⟩
    have hjet : Fr.d^[r + 1] τ ∉ Fr.jetPrefixField τ (r + 1) := by
      intro hmem
      exact htr (r + 1) (by omega)
        (isAlgebraic_algebraMap
          (⟨Fr.d^[r + 1] τ, hmem⟩ : ↥(Fr.jetPrefixField τ (r + 1))))
    refine jetDefect_ne_zero Fr hqconst hshift hq hdρ r hjet ?_
    rw [RittFrame.jetDefect, ← hr, hdiag, sub_self]
  · -- the affine connection: a seeded relation one level down
    have hAtop : A' (p - 1) = -(((p.choose 2 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (p + 1)) :=
      jetDefect_top_coeff Fr hqconst hshift hp2 (fun j hj => htr j (by omega)) hAsh
    have hlam0 : A' (p - 1) ≠ 0 := by
      rw [hAtop]
      refine neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero ?_ hq) hdρ)
        (pow_ne_zero _ hρ0))
      exact Nat.cast_ne_zero.mpr (by have := Nat.choose_pos (show 2 ≤ p from hp2); omega)
    refine Or.inl ⟨w, fun j => -(N : K) * A' j, hw0, ?_, ?_, ?_⟩
    · rw [hpm]; exact hwmem
    · rw [show m - 2 = p - 1 by omega]
      exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hlam0
    · rw [hpm]; exact hconn
  · exact absurd rfl hαne
  · -- the degree-one branch: the homogeneous exceptional datum one level down
    obtain ⟨v', hv'0, hv'mem, hv'eq, hlin⟩ := h5
    obtain ⟨y, hymem, hyeq⟩ := hlin rfl
    refine Or.inr (Or.inr ⟨v', y, hv'0, ?_, ?_, ?_, ?_⟩)
    · rw [hpm]; exact hv'mem
    · rw [hpm]; exact hymem
    · have hsc : (Fr.ρ)⁻¹ / (q / Fr.ρ ^ p) = q⁻¹ * Fr.ρ ^ (p - 1) := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
        subst hr
        rw [show r + 1 - 1 = r by omega]
        field_simp
        ring
      rw [show m - 1 - 1 = p - 1 by omega, ← hsc]
      rw [hv'eq, show (0 : K) / (q / Fr.ρ ^ p) = 0 by simp, map_zero, add_zero]
    · rw [hpm]
      exact hyeq

/-- **The homogeneous exceptional datum drops a level.**  Its leading element descends without drift
into the next prefix field, which makes its companion an affine relation there whose linear
coefficient is a nonzero multiple of the top Faà di Bruno coefficient. -/
theorem excHom_descends (Fr : RittFrame K L) {τ : L} {q : K}
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) {m : ℕ} (hm : 3 ≤ m)
    (htr : ∀ j, j < m → Transcendental ↥(Fr.jetPrefixField τ j) (Fr.d^[j] τ))
    {v z : L} {κ ν : K} (hv0 : v ≠ 0) (hκ0 : κ ≠ 0) (hν0 : ν ≠ 0)
    (hvmem : v ∈ Fr.jetPrefixField τ m) (hzmem : z ∈ Fr.jetPrefixField τ m)
    (hveq : Fr.σ v = algebraMap K L (q⁻¹ * Fr.ρ ^ (m - 1)) * v)
    (hzeq : Fr.σ z = algebraMap K L (q / Fr.ρ ^ m) * z + algebraMap K L κ / v
      - algebraMap K L ν * (Fr.σ (Fr.d^[m] τ)
          - algebraMap K L (q / Fr.ρ ^ m) * Fr.d^[m] τ)) :
    (∃ (w : L) (A : ℕ → K), w ≠ 0 ∧ w ∈ Fr.jetPrefixField τ (m - 1) ∧ A (m - 2) ≠ 0 ∧
      Fr.σ w = algebraMap K L (q / Fr.ρ ^ (m - 1)) * w
        + ∑ j ∈ Finset.range (m - 1), algebraMap K L (A j) * Fr.d^[j] τ) ∨
    (∃ (v' z' : L) (κ' ν' : K), v' ≠ 0 ∧ κ' ≠ 0 ∧ ν' ≠ 0 ∧
      v' ∈ Fr.jetPrefixField τ (m - 1) ∧ z' ∈ Fr.jetPrefixField τ (m - 1) ∧
      Fr.σ v' = algebraMap K L (q⁻¹ * Fr.ρ ^ (m - 1 - 1)) * v' ∧
      Fr.σ z' = algebraMap K L (q / Fr.ρ ^ (m - 1)) * z' + algebraMap K L κ' / v'
        - algebraMap K L ν' * (Fr.σ (Fr.d^[m - 1] τ)
            - algebraMap K L (q / Fr.ρ ^ (m - 1)) * Fr.d^[m - 1] τ)) ∨
    (∃ (v' : L) (h : K), v' ≠ 0 ∧ h ≠ 0 ∧ v' ∈ Fr.jetPrefixField τ (m - 1) ∧
      Fr.σ v' = algebraMap K L (Fr.ρ)⁻¹ * v' + algebraMap K L h) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  obtain ⟨p, hp⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have hpm : m - 1 = p := by omega
  have hp2 : 2 ≤ p := by omega
  have haK0 : q / Fr.ρ ^ p ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
  have hamK0 : q / Fr.ρ ^ m ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
  -- the defect at level `m`, with its top coefficient
  obtain ⟨A, hAsupp, hA⟩ := exists_shift_jet_coeffs Fr hshift m
  have hAtop : A (m - 1) = -(((m.choose 2 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (m + 1)) :=
    jetDefect_top_coeff Fr hqconst hshift (by omega) (fun j hj => htr j hj) hA
  have hAtop0 : A (m - 1) ≠ 0 := by
    rw [hAtop]
    refine neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero ?_ hq) hdρ)
      (pow_ne_zero _ hρ0))
    exact Nat.cast_ne_zero.mpr (by have := Nat.choose_pos (show 2 ≤ m by omega); omega)
  -- the leading element descends without drift
  have hc₁0 : q⁻¹ * Fr.ρ ^ (m - 1) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hq) (pow_ne_zero _ hρ0)
  rcases exists_floor_eigen_or_affine_connection_of_tower Fr hqconst hshift hq p m
      (fun j hj => htr j hj) v _ hv0 hvmem hc₁0 hveq with
      ⟨n', hn'F, -, hvn'⟩ | ⟨m', hFm', hm', hdiag⟩ | ⟨m', w, N, A', hFm', hm', hw0, hwmem, hN,
        hAsh, hconn⟩
  · -- the companion is now an affine relation one level down
    have hvp : v ∈ Fr.jetPrefixField τ p := jetPrefixField_mono Fr τ hn'F hvn'
    have hβmem : algebraMap K L κ / v
        - algebraMap K L ν * ∑ j ∈ Finset.range p, algebraMap K L (A j) * Fr.d^[j] τ
        ∈ Fr.jetPrefixField τ p := by
      refine sub_mem (div_mem (IntermediateField.algebraMap_mem _ _) hvp) (mul_mem
        (IntermediateField.algebraMap_mem _ _) (sum_mem ?_))
      intro j hj
      rw [Finset.mem_range] at hj
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (Fr.jet_mem_jetPrefixField hj)
    have hz0 : z ≠ 0 := by
      intro hzero
      have hdef : algebraMap K L ν * ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ
          = algebraMap K L κ / v := by
        rw [hzero, map_zero, mul_zero, zero_add] at hzeq
        rw [hA] at hzeq
        linear_combination hzeq
      have hνL : algebraMap K L ν ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hν0
      have hsum : ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ
          ∈ Fr.jetPrefixField τ p := by
        have hrhs : algebraMap K L κ / v ∈ Fr.jetPrefixField τ p :=
          div_mem (IntermediateField.algebraMap_mem _ _) hvp
        have := mul_mem (IntermediateField.algebraMap_mem (Fr.jetPrefixField τ p) ν⁻¹) hrhs
        rw [← hdef, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hν0, map_one, one_mul] at this
        exact this
      have htop : Fr.d^[p] τ ∈ Fr.jetPrefixField τ p := by
        have hlow : ∑ j ∈ Finset.range p, algebraMap K L (A j) * Fr.d^[j] τ
            ∈ Fr.jetPrefixField τ p := by
          refine sum_mem ?_
          intro j hj
          rw [Finset.mem_range] at hj
          exact mul_mem (IntermediateField.algebraMap_mem _ _) (Fr.jet_mem_jetPrefixField hj)
        have hApL : algebraMap K L (A p) ≠ 0 := by
          refine (map_ne_zero_iff _ (algebraMap K L).injective).mpr ?_
          rw [← hpm]
          exact hAtop0
        have hsplit : algebraMap K L (A p) * Fr.d^[p] τ
            = (∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ)
              - ∑ j ∈ Finset.range p, algebraMap K L (A j) * Fr.d^[j] τ := by
          rw [hp, Finset.sum_range_succ]
          ring
        have hmem2 : algebraMap K L (A p) * Fr.d^[p] τ ∈ Fr.jetPrefixField τ p := by
          rw [hsplit]
          exact sub_mem hsum hlow
        have := mul_mem (IntermediateField.algebraMap_mem (Fr.jetPrefixField τ p) (A p)⁻¹) hmem2
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (by
          rw [← hpm]; exact hAtop0), map_one, one_mul] at this
        exact this
      exact htr p (by omega)
        (isAlgebraic_algebraMap (⟨Fr.d^[p] τ, htop⟩ : ↥(Fr.jetPrefixField τ p)))
    have hzmem' : z ∈ Fr.jetPrefixField τ (p + 1) := by rw [← hp]; exact hzmem
    have hzrel : Fr.σ z = algebraMap K L (q / Fr.ρ ^ m) * z
        + (algebraMap K L (-(ν * A p)) * Fr.d^[p] τ
          + (algebraMap K L κ / v
            - algebraMap K L ν * ∑ j ∈ Finset.range p, algebraMap K L (A j) * Fr.d^[j] τ)) := by
      have hsplit : ∑ j ∈ Finset.range m, algebraMap K L (A j) * Fr.d^[j] τ
          = algebraMap K L (A p) * Fr.d^[p] τ
            + ∑ j ∈ Finset.range p, algebraMap K L (A j) * Fr.d^[j] τ := by
        rw [hp, Finset.sum_range_succ]
        ring
      rw [hzeq, hA, hsplit, map_neg, map_mul]
      ring
    have hαne : -(ν * A p) ≠ 0 := by
      refine neg_ne_zero.mpr (mul_ne_zero hν0 ?_)
      rw [← hpm] at *
      exact hAtop0
    rcases affine_descent_dichotomy_gen Fr hqconst hshift hq (htr p (by omega)) hz0 hzmem'
        hamK0 hβmem hzrel with
        ⟨hα0, -⟩ | hdiag | ⟨w, N, A', hw0, hwmem, hN, hAsh, hconn⟩ |
        ⟨v', z', -, hv'0, hv'mem, hz'mem, -, -, hv'eq, hz'eq, -⟩ |
        ⟨v', hv'0, hv'mem, hv'eq, -⟩
    · exact absurd hα0 hαne
    · exfalso
      obtain ⟨r, hr⟩ : ∃ r, p = r + 2 := ⟨p - 2, by omega⟩
      have hjet : Fr.d^[r + 1] τ ∉ Fr.jetPrefixField τ (r + 1) := by
        intro hmem
        exact htr (r + 1) (by omega)
          (isAlgebraic_algebraMap
            (⟨Fr.d^[r + 1] τ, hmem⟩ : ↥(Fr.jetPrefixField τ (r + 1))))
      refine jetDefect_ne_zero Fr hqconst hshift hq hdρ r hjet ?_
      rw [RittFrame.jetDefect, ← hr, hdiag, sub_self]
    · have hAtop' : A' (p - 1) = -(((p.choose 2 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (p + 1)) :=
        jetDefect_top_coeff Fr hqconst hshift hp2 (fun j hj => htr j (by omega)) hAsh
      have hlam0 : A' (p - 1) ≠ 0 := by
        rw [hAtop']
        refine neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero ?_ hq) hdρ)
          (pow_ne_zero _ hρ0))
        exact Nat.cast_ne_zero.mpr (by have := Nat.choose_pos (show 2 ≤ p from hp2); omega)
      refine Or.inl ⟨w, fun j => -(N : K) * A' j, hw0, by rw [hpm]; exact hwmem, ?_, ?_⟩
      · rw [show m - 2 = p - 1 by omega]
        exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hlam0
      · rw [hpm]; exact hconn
    · have hsc : q / Fr.ρ ^ m / (q / Fr.ρ ^ p) ^ 2 = q⁻¹ * Fr.ρ ^ (p - 1) := by
        obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
        subst hr
        rw [show r + 1 - 1 = r by omega, hp]
        field_simp
        ring
      refine Or.inr (Or.inl ⟨v', z',
        q / Fr.ρ ^ p * -(ν * A p) / (q / Fr.ρ ^ m), 2, hv'0, ?_, two_ne_zero, ?_, ?_, ?_, ?_⟩)
      · exact div_ne_zero (mul_ne_zero haK0 hαne) hamK0
      · rw [hpm]; exact hv'mem
      · rw [hpm]; exact hz'mem
      · rw [show m - 1 - 1 = p - 1 by omega, ← hsc]
        exact hv'eq
      · rw [hpm, map_ofNat]
        exact hz'eq
    · refine Or.inr (Or.inr ⟨v', -(ν * A p) / (q / Fr.ρ ^ p), hv'0,
        div_ne_zero hαne haK0, by rw [hpm]; exact hv'mem, ?_⟩)
      have hscal : q / Fr.ρ ^ m / (q / Fr.ρ ^ p) = (Fr.ρ)⁻¹ := by
        rw [hp, pow_succ]
        field_simp
      rw [hv'eq, hscal]
  · exfalso
    obtain ⟨r, hr⟩ : ∃ r, m' = r + 2 := ⟨m' - 2, by omega⟩
    have hjet : Fr.d^[r + 1] τ ∉ Fr.jetPrefixField τ (r + 1) := by
      intro hmem
      exact htr (r + 1) (by omega)
        (isAlgebraic_algebraMap
          (⟨Fr.d^[r + 1] τ, hmem⟩ : ↥(Fr.jetPrefixField τ (r + 1))))
    refine jetDefect_ne_zero Fr hqconst hshift hq hdρ r hjet ?_
    rw [RittFrame.jetDefect, ← hr, hdiag, sub_self]
  · have hm'p : m' = p := by omega
    subst hm'p
    have hAtop' : A' (m' - 1) = -(((m'.choose 2 : ℕ) : K) * q * Fr.dK Fr.ρ / Fr.ρ ^ (m' + 1)) :=
      jetDefect_top_coeff Fr hqconst hshift hp2 (fun j hj => htr j (by omega)) hAsh
    have hlam0 : A' (m' - 1) ≠ 0 := by
      rw [hAtop']
      refine neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (mul_ne_zero ?_ hq) hdρ)
        (pow_ne_zero _ hρ0))
      exact Nat.cast_ne_zero.mpr (by have := Nat.choose_pos (show 2 ≤ m' from hp2); omega)
    refine Or.inl ⟨w, fun j => -(N : K) * A' j, hw0, by rw [hpm]; exact hwmem, ?_, ?_⟩
    · rw [show m - 2 = m' - 1 by omega]
      exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hlam0
    · rw [hpm]; exact hconn

end GaloisForLFunctions.HTGeometry
