import Mathlib

/-!
# A hard cyclic polygon inside a prime-torsion group

At prime order every nonzero power map of a torsion group is a bijection, so the preimage of a small
"easy" set under each power has the same size as the set itself.  The union of the `k-1` preimages
is therefore still small, and its complement -- the points *all* of whose nonidentity powers avoid
the easy set -- is nonempty and large.

The counting core is stated for an arbitrary finite family of injections, and the bijectivity of the
power map is stated for an arbitrary abelian group of exponent dividing `k`: coprimality of the
exponent with `k` supplies a two-sided inverse directly, with no vector-space structure.  Together
they give the polygon count without any hypothesis on how the easy set was produced.
-/

namespace GaloisForLFunctions.HTGeometry

section HardPolygon

variable {Q : Type*} [Fintype Q] [DecidableEq Q] {ι : Type*}

/-- The points all of whose listed images avoid the easy set. -/
def hardPoints (s : Finset ι) (P : ι → Q → Q) (E : Finset Q) : Finset Q :=
  (Finset.univ : Finset Q).filter fun q => ∀ i ∈ s, P i q ∉ E

/-- **The counting core.**  Removing the preimages of a set under finitely many injections costs at
most the number of injections times the size of the set. -/
theorem card_hardPoints_add_ge (s : Finset ι) (P : ι → Q → Q)
    (hP : ∀ i ∈ s, Function.Injective (P i)) (E : Finset Q) :
    Fintype.card Q ≤ (hardPoints s P E).card + s.card * E.card := by
  classical
  set bad : Finset Q := (Finset.univ : Finset Q).filter fun q => ¬ ∀ i ∈ s, P i q ∉ E with hbad
  have hsplit : (hardPoints s P E).card + bad.card = Fintype.card Q := by
    rw [hardPoints, hbad, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hcover : bad ⊆ s.biUnion fun i => (Finset.univ : Finset Q).filter fun q => P i q ∈ E := by
    intro q hq
    rw [hbad, Finset.mem_filter] at hq
    push Not at hq
    obtain ⟨i, hi, hmem⟩ := hq.2
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hmem⟩⟩
  have hfiber : ∀ i ∈ s,
      ((Finset.univ : Finset Q).filter fun q => P i q ∈ E).card ≤ E.card := by
    intro i hi
    refine Finset.card_le_card_of_injOn (P i) ?_ ?_
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · intro a _ b _ hab
      exact hP i hi hab
  have hbadle : bad.card ≤ s.card * E.card := by
    calc bad.card ≤ (s.biUnion fun i => (Finset.univ : Finset Q).filter fun q => P i q ∈ E).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ i ∈ s, ((Finset.univ : Finset Q).filter fun q => P i q ∈ E).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ s, E.card := Finset.sum_le_sum hfiber
      _ = s.card * E.card := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- A hard point exists as soon as the easy set is small enough. -/
theorem exists_hardPoint (s : Finset ι) (P : ι → Q → Q)
    (hP : ∀ i ∈ s, Function.Injective (P i)) (E : Finset Q)
    (hsmall : s.card * E.card < Fintype.card Q) :
    ∃ q : Q, ∀ i ∈ s, P i q ∉ E := by
  classical
  have hcard := card_hardPoints_add_ge s P hP E
  have hpos : 0 < (hardPoints s P E).card := by omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  rw [hardPoints, Finset.mem_filter] at hq
  exact ⟨q, hq.2⟩

end HardPolygon

section TorsionPower

/-- **The power map of a torsion group is bijective at every coprime exponent.**  A Bézout
coefficient supplies the inverse directly. -/
theorem bijective_zsmul_of_isCoprime {Q : Type*} [AddCommGroup Q] {k j : ℤ}
    (hk : ∀ q : Q, k • q = 0) (hj : IsCoprime j k) :
    Function.Bijective (fun q : Q => j • q) := by
  obtain ⟨a, b, hab⟩ := hj
  have hinv : ∀ q : Q, a • (j • q) = q := by
    intro q
    have hkq : (b * k) • q = 0 := by
      rw [mul_smul, hk q, smul_zero]
    have h1 : (a * j) • q + (b * k) • q = q := by
      rw [← add_smul, hab, one_smul]
    rw [hkq, add_zero] at h1
    rw [← mul_smul]
    exact h1
  refine ⟨fun x y hxy => ?_, fun y => ⟨a • y, ?_⟩⟩
  · have := congrArg (fun z : Q => a • z) hxy
    simpa [hinv] using this
  · have hcomm : j • (a • y) = a • (j • y) := by
      rw [← mul_smul, ← mul_smul, mul_comm]
    show j • (a • y) = y
    rw [hcomm, hinv]

/-- Every exponent between `1` and `k-1` is coprime to a prime `k`. -/
theorem isCoprime_of_lt_prime {k j : ℕ} (hk : k.Prime) (h1 : 1 ≤ j) (h2 : j ≤ k - 1) :
    IsCoprime (j : ℤ) (k : ℤ) := by
  have hkpos : 2 ≤ k := hk.two_le
  have hjk : ¬ (k ∣ j) := by
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hcop : Nat.Coprime j k := ((Nat.Prime.coprime_iff_not_dvd hk).mpr hjk).symm
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact_mod_cast hcop

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [AddCommGroup Q]

/-- **Theorem A, the existence half.**  If the easy set of a prime-torsion group is small enough,
some point has *every* nonidentity power outside it. -/
theorem exists_hard_torsion_point {k : ℕ} (hk : k.Prime) (hexp : ∀ q : Q, (k : ℤ) • q = 0)
    (E : Finset Q) (hsmall : (k - 1) * E.card < Fintype.card Q) :
    ∃ q : Q, ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → (j : ℤ) • q ∉ E := by
  classical
  have hcard : (Finset.Icc 1 (k - 1)).card = k - 1 := by
    rw [Nat.card_Icc]
    omega
  have hP : ∀ j ∈ Finset.Icc 1 (k - 1), Function.Injective (fun q : Q => (j : ℤ) • q) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact (bijective_zsmul_of_isCoprime hexp (isCoprime_of_lt_prime hk hj.1 hj.2)).1
  obtain ⟨q, hq⟩ := exists_hardPoint (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) hP E
    (by rw [hcard]; exact hsmall)
  exact ⟨q, fun j h1 h2 => hq j (Finset.mem_Icc.mpr ⟨h1, h2⟩)⟩

/-- **`(14a)`, the counting half.**  The hard points are at least `|Q| - (k-1)|E|` in number. -/
theorem card_hard_torsion_add_ge {k : ℕ} (hk : k.Prime) (hexp : ∀ q : Q, (k : ℤ) • q = 0)
    (E : Finset Q) :
    Fintype.card Q
      ≤ (hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).card + (k - 1) * E.card := by
  classical
  have hcard : (Finset.Icc 1 (k - 1)).card = k - 1 := by
    rw [Nat.card_Icc]
    omega
  have hP : ∀ j ∈ Finset.Icc 1 (k - 1), Function.Injective (fun q : Q => (j : ℤ) • q) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact (bijective_zsmul_of_isCoprime hexp (isCoprime_of_lt_prime hk hj.1 hj.2)).1
  have h := card_hardPoints_add_ge (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) hP E
  rwa [hcard] at h

/-- **`(14a)` in fractional form.**  If the easy set occupies at most a `β` fraction, the hard points
occupy at least a `1 - (k-1)β` fraction. -/
theorem card_hard_torsion_ge_of_frac {k : ℕ} (hk : k.Prime) (hexp : ∀ q : Q, (k : ℤ) • q = 0)
    (E : Finset Q) {β : ℝ} (hβ : (E.card : ℝ) ≤ β * (Fintype.card Q : ℝ)) :
    (1 - ((k : ℝ) - 1) * β) * (Fintype.card Q : ℝ)
      ≤ ((hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).card : ℝ) := by
  have hk1 : 1 ≤ k := hk.one_lt.le
  have hbase := card_hard_torsion_add_ge hk hexp E
  have hbaseR : (Fintype.card Q : ℝ)
      ≤ ((hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).card : ℝ)
        + ((k : ℝ) - 1) * (E.card : ℝ) := by
    have hcast : (((k - 1) * E.card : ℕ) : ℝ) = ((k : ℝ) - 1) * (E.card : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hk1, Nat.cast_one]
    calc (Fintype.card Q : ℝ)
        ≤ (((hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).card
            + (k - 1) * E.card : ℕ) : ℝ) := by exact_mod_cast hbase
      _ = ((hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).card : ℝ)
            + ((k : ℝ) - 1) * (E.card : ℝ) := by rw [Nat.cast_add, hcast]
  have hknn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  nlinarith [hbaseR, hβ, hknn]

/-! ### Counting the cyclic subgroups the hard points generate -/

/-- In an abelian group of prime exponent every nonzero element has that exact order. -/
theorem addOrderOf_eq_of_prime_exponent {k : ℕ} (hk : k.Prime) (hexp : ∀ q : Q, (k : ℤ) • q = 0)
    {q : Q} (hq : q ≠ 0) : addOrderOf q = k := by
  have hnat : (k : ℕ) • q = 0 := by
    have := hexp q
    rwa [natCast_zsmul] at this
  have hdvd : addOrderOf q ∣ k := addOrderOf_dvd_of_nsmul_eq_zero hnat
  rcases (Nat.Prime.eq_one_or_self_of_dvd hk _ hdvd) with h | h
  · exact absurd (addOrderOf_eq_one_iff.mp h) hq
  · exact h

/-- The nonzero elements of the cyclic subgroup generated by a point of order `k`. -/
theorem card_erase_zmultiples {k : ℕ} (hk : k.Prime) (hexp : ∀ q : Q, (k : ℤ) • q = 0)
    {q₀ : Q} (hq₀ : q₀ ≠ 0) :
    (((Finset.univ : Finset Q).filter fun x => x ∈ AddSubgroup.zmultiples q₀).erase 0).card
      = k - 1 := by
  classical
  have hmem : (0 : Q) ∈ (Finset.univ : Finset Q).filter fun x => x ∈ AddSubgroup.zmultiples q₀ :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ 0, (AddSubgroup.zmultiples q₀).zero_mem⟩
  have hcard : ((Finset.univ : Finset Q).filter fun x => x ∈ AddSubgroup.zmultiples q₀).card
      = k := by
    have h1 : Fintype.card ↥(AddSubgroup.zmultiples q₀)
        = ((Finset.univ : Finset Q).filter fun x => x ∈ AddSubgroup.zmultiples q₀).card :=
      Fintype.card_subtype _
    have h2 : Nat.card ↥(AddSubgroup.zmultiples q₀) = addOrderOf q₀ := Nat.card_zmultiples q₀
    rw [Nat.card_eq_fintype_card, h1] at h2
    rw [h2, addOrderOf_eq_of_prime_exponent hk hexp hq₀]
  rw [Finset.card_erase_of_mem hmem, hcard]

/-- **`(14b)`.**  The hard points generate at least `|hard \ {0}|/(k-1)` distinct cyclic subgroups of
order `k`. -/
theorem card_hard_subgroups_ge [DecidableEq (AddSubgroup Q)] {k : ℕ} (hk : k.Prime)
    (hexp : ∀ q : Q, (k : ℤ) • q = 0) (E : Finset Q) :
    ((hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).erase 0).card
      ≤ (k - 1)
        * (((hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).erase 0).image
            fun q => AddSubgroup.zmultiples q).card := by
  classical
  set S : Finset Q :=
    (hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).erase 0 with hS
  refine Finset.card_le_mul_card_image S (k - 1) fun A hA => ?_
  obtain ⟨q₀, hq₀S, hq₀A⟩ := Finset.mem_image.mp hA
  have hq₀ne : q₀ ≠ 0 := (Finset.mem_erase.mp hq₀S).1
  have hsub : {q ∈ S | (fun q => AddSubgroup.zmultiples q) q = A}
      ⊆ ((Finset.univ : Finset Q).filter fun x => x ∈ AddSubgroup.zmultiples q₀).erase 0 := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hqS := hq.1
    have hqA : AddSubgroup.zmultiples q = A := hq.2
    have hqne : q ≠ 0 := (Finset.mem_erase.mp hqS).1
    refine Finset.mem_erase.mpr ⟨hqne, Finset.mem_filter.mpr ⟨Finset.mem_univ q, ?_⟩⟩
    have hself : q ∈ AddSubgroup.zmultiples q := AddSubgroup.mem_zmultiples q
    rw [hqA, ← hq₀A] at hself
    exact hself
  calc {q ∈ S | (fun q => AddSubgroup.zmultiples q) q = A}.card
      ≤ (((Finset.univ : Finset Q).filter fun x => x ∈ AddSubgroup.zmultiples q₀).erase 0).card :=
        Finset.card_le_card hsub
    _ = k - 1 := card_erase_zmultiples hk hexp hq₀ne

end TorsionPower

section ConcreteTorusModel

/-- The anchored model of the projective `k`-torsion group of a `D`-level system. -/
abbrev torsionModel (k D : ℕ) : Type := Fin (D - 1) → ZMod k

theorem zsmul_torsionModel_eq_zero {k D : ℕ} (q : torsionModel k D) : (k : ℤ) • q = 0 := by
  funext j
  show (k : ℤ) • q j = 0
  rw [zsmul_eq_mul]
  simp

theorem card_torsionModel {k D : ℕ} [NeZero k] :
    Fintype.card (torsionModel k D) = k ^ (D - 1) := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **`(14)` and `(14a)` on the projective torsion group.**  With `(k-1)|E| < k^{D-1}` some torsion
class has every nonidentity power outside the easy set, and the hard classes number at least
`k^{D-1} - (k-1)|E|`. -/
theorem exists_hard_torsionModel_point {k D : ℕ} [NeZero k] (hk : k.Prime)
    (E : Finset (torsionModel k D)) (hsmall : (k - 1) * E.card < k ^ (D - 1)) :
    ∃ q : torsionModel k D, ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → (j : ℤ) • q ∉ E := by
  refine exists_hard_torsion_point hk zsmul_torsionModel_eq_zero E ?_
  rw [card_torsionModel]
  exact hsmall

theorem card_hard_torsionModel_add_ge {k D : ℕ} [NeZero k] (hk : k.Prime)
    (E : Finset (torsionModel k D)) :
    k ^ (D - 1)
      ≤ (hardPoints (Finset.Icc 1 (k - 1)) (fun j q => (j : ℤ) • q) E).card + (k - 1) * E.card := by
  have h := card_hard_torsion_add_ge (Q := torsionModel k D) hk zsmul_torsionModel_eq_zero E
  rwa [card_torsionModel] at h

end ConcreteTorusModel

end GaloisForLFunctions.HTGeometry
