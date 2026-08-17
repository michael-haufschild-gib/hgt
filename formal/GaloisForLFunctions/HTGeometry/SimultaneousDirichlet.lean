import Mathlib

/-!
# Simultaneous Dirichlet approximation and the first-hit exponent

Among the first `Q^m + 1` multiples of a real vector, two land in the same box of the subdivision of
the unit cube into `Q^m` boxes of side `1/Q`; their difference is a multiple of size at most `Q^m`
that is within `1/Q` of the integer lattice in every coordinate.

Consequently the first multiple entering a ball of radius `r` around the lattice appears by time
`(1/r + 1)^m`, which is the upper half of the first-hit exponent.  The lower half is the
Diophantine hypothesis itself: if only finitely many `q` beat `q^{-1/m-eta}`, then the first hitting
time at radius `r` is at least `r^{-1/(1/m+eta)}`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## Distance to the integer lattice -/

/-- The distance from a real number to the nearest integer, as an infimum over integers. -/
def latticeClose (x r : ℝ) : Prop := ∃ p : ℤ, |x - p| < r

theorem latticeClose_mono {x r s : ℝ} (h : latticeClose x r) (hrs : r ≤ s) : latticeClose x s := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, lt_of_lt_of_le hp hrs⟩

/-! ## Simultaneous Dirichlet approximation -/

section Dirichlet

variable {m : ℕ}

/-- The box index of a real number in the subdivision of the unit interval into `Q` parts. -/
noncomputable def boxIndex (Q : ℕ) (x : ℝ) : ℕ := ⌊(Q : ℝ) * Int.fract x⌋.toNat

theorem boxIndex_lt {Q : ℕ} (hQ : 0 < Q) (x : ℝ) : boxIndex Q x < Q := by
  have hfract := Int.fract_lt_one x
  have hfract0 := Int.fract_nonneg x
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlt : (Q : ℝ) * Int.fract x < Q := by
    calc (Q : ℝ) * Int.fract x < (Q : ℝ) * 1 := by
          exact mul_lt_mul_of_pos_left hfract hQR
      _ = Q := by ring
  have hfloor : ⌊(Q : ℝ) * Int.fract x⌋ < (Q : ℤ) := by
    rw [Int.floor_lt]
    exact_mod_cast hlt
  have hnn : (0 : ℤ) ≤ ⌊(Q : ℝ) * Int.fract x⌋ := by
    refine Int.floor_nonneg.mpr ?_
    positivity
  rw [boxIndex]
  omega

/-- Two numbers in the same box are within `1/Q` in fractional part. -/
theorem abs_fract_sub_lt_of_boxIndex_eq {Q : ℕ} (hQ : 0 < Q) {x y : ℝ}
    (h : boxIndex Q x = boxIndex Q y) :
    |Int.fract x - Int.fract y| < 1 / Q := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hx : (⌊(Q : ℝ) * Int.fract x⌋ : ℝ) ≤ (Q : ℝ) * Int.fract x := Int.floor_le _
  have hy : (⌊(Q : ℝ) * Int.fract y⌋ : ℝ) ≤ (Q : ℝ) * Int.fract y := Int.floor_le _
  have hx' : (Q : ℝ) * Int.fract x < (⌊(Q : ℝ) * Int.fract x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hy' : (Q : ℝ) * Int.fract y < (⌊(Q : ℝ) * Int.fract y⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hnnx : (0 : ℤ) ≤ ⌊(Q : ℝ) * Int.fract x⌋ := by
    refine Int.floor_nonneg.mpr ?_
    have := Int.fract_nonneg x
    positivity
  have hnny : (0 : ℤ) ≤ ⌊(Q : ℝ) * Int.fract y⌋ := by
    refine Int.floor_nonneg.mpr ?_
    have := Int.fract_nonneg y
    positivity
  have hfloor : ⌊(Q : ℝ) * Int.fract x⌋ = ⌊(Q : ℝ) * Int.fract y⌋ := by
    have := h
    rw [boxIndex, boxIndex] at this
    omega
  rw [hfloor] at hx hx'
  have hd1 : (Int.fract x - Int.fract y) * Q < 1 := by nlinarith
  have hd2 : (Int.fract y - Int.fract x) * Q < 1 := by nlinarith
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · have h := (lt_div_iff₀ hQR).mpr hd2
    linarith
  · exact (lt_div_iff₀ hQR).mpr hd1

/-- **Simultaneous Dirichlet approximation.**  Some multiple of size at most `Q^m` is within `1/Q`
of the integer lattice in every coordinate. -/
theorem exists_simultaneous_dirichlet (β : Fin m → ℝ) {Q : ℕ} (hQ : 0 < Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ^ m ∧ ∀ i, latticeClose ((q : ℝ) * β i) (1 / Q) := by
  classical
  -- the box map on the first `Q^m + 1` multiples
  set f : Fin (Q ^ m + 1) → (Fin m → Fin Q) :=
    fun k i => ⟨boxIndex Q ((k : ℕ) * β i), boxIndex_lt hQ _⟩ with hf
  have hcard : Fintype.card (Fin m → Fin Q) < Fintype.card (Fin (Q ^ m + 1)) := by
    simp
  obtain ⟨k, l, hkl, hfkl⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- order the two indices
  rcases lt_or_gt_of_ne hkl with hlt | hlt
  · refine ⟨(l : ℕ) - (k : ℕ), ?_, ?_, ?_⟩
    · omega
    · have : (l : ℕ) ≤ Q ^ m := by omega
      omega
    · intro i
      have hbox : boxIndex Q ((l : ℕ) * β i) = boxIndex Q ((k : ℕ) * β i) :=
        (congrArg Fin.val (congrFun hfkl i)).symm
      have hclose := abs_fract_sub_lt_of_boxIndex_eq hQ hbox
      refine ⟨⌊((l : ℕ) : ℝ) * β i⌋ - ⌊((k : ℕ) : ℝ) * β i⌋, ?_⟩
      have hfr : Int.fract (((l : ℕ) : ℝ) * β i) - Int.fract (((k : ℕ) : ℝ) * β i)
          = (((l : ℕ) : ℝ) * β i - ((k : ℕ) : ℝ) * β i)
            - ((⌊((l : ℕ) : ℝ) * β i⌋ : ℝ) - (⌊((k : ℕ) : ℝ) * β i⌋ : ℝ)) := by
        rw [Int.fract, Int.fract]
        ring
      have hcast : (((l : ℕ) - (k : ℕ) : ℕ) : ℝ) = ((l : ℕ) : ℝ) - ((k : ℕ) : ℝ) := by
        have : (k : ℕ) ≤ (l : ℕ) := le_of_lt hlt
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      push_cast
      rw [hfr] at hclose
      calc |(((l : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * β i
              - ((⌊((l : ℕ) : ℝ) * β i⌋ : ℝ) - (⌊((k : ℕ) : ℝ) * β i⌋ : ℝ))|
          = |(((l : ℕ) : ℝ) * β i - ((k : ℕ) : ℝ) * β i)
              - ((⌊((l : ℕ) : ℝ) * β i⌋ : ℝ) - (⌊((k : ℕ) : ℝ) * β i⌋ : ℝ))| := by
            ring_nf
        _ < 1 / Q := hclose
  · refine ⟨(k : ℕ) - (l : ℕ), ?_, ?_, ?_⟩
    · omega
    · have : (k : ℕ) ≤ Q ^ m := by omega
      omega
    · intro i
      have hbox : boxIndex Q ((k : ℕ) * β i) = boxIndex Q ((l : ℕ) * β i) :=
        congrArg Fin.val (congrFun hfkl i)
      have hclose := abs_fract_sub_lt_of_boxIndex_eq hQ hbox
      refine ⟨⌊((k : ℕ) : ℝ) * β i⌋ - ⌊((l : ℕ) : ℝ) * β i⌋, ?_⟩
      have hfr : Int.fract (((k : ℕ) : ℝ) * β i) - Int.fract (((l : ℕ) : ℝ) * β i)
          = (((k : ℕ) : ℝ) * β i - ((l : ℕ) : ℝ) * β i)
            - ((⌊((k : ℕ) : ℝ) * β i⌋ : ℝ) - (⌊((l : ℕ) : ℝ) * β i⌋ : ℝ)) := by
        rw [Int.fract, Int.fract]
        ring
      have hcast : (((k : ℕ) - (l : ℕ) : ℕ) : ℝ) = ((k : ℕ) : ℝ) - ((l : ℕ) : ℝ) := by
        have : (l : ℕ) ≤ (k : ℕ) := le_of_lt hlt
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      push_cast
      rw [hfr] at hclose
      calc |(((k : ℕ) : ℝ) - ((l : ℕ) : ℝ)) * β i
              - ((⌊((k : ℕ) : ℝ) * β i⌋ : ℝ) - (⌊((l : ℕ) : ℝ) * β i⌋ : ℝ))|
          = |(((k : ℕ) : ℝ) * β i - ((l : ℕ) : ℝ) * β i)
              - ((⌊((k : ℕ) : ℝ) * β i⌋ : ℝ) - (⌊((l : ℕ) : ℝ) * β i⌋ : ℝ))| := by
            ring_nf
        _ < 1 / Q := hclose

end Dirichlet

/-! ## The first-hit exponent -/

section FirstHit

variable {m : ℕ}

/-- The first multiple of `β` entering the `r`-neighbourhood of the integer lattice. -/
noncomputable def firstHit (β : Fin m → ℝ) (r : ℝ) : ℕ :=
  sInf {q : ℕ | 1 ≤ q ∧ ∀ i, latticeClose ((q : ℝ) * β i) r}

/-- **The upper half of the first-hit exponent.**  Dirichlet approximation makes the first hit
appear by time `⌈1/r⌉^m`. -/
theorem firstHit_le (β : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    firstHit β r ≤ ⌈1 / r⌉₊ ^ m := by
  classical
  set Q : ℕ := ⌈1 / r⌉₊ with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact Nat.ceil_pos.mpr (by positivity)
  obtain ⟨q, hq1, hqQ, hclose⟩ := exists_simultaneous_dirichlet β hQpos
  have hle : (1 : ℝ) / Q ≤ r := by
    have hQR : (1 : ℝ) / r ≤ Q := Nat.le_ceil _
    have hQpos' : (0 : ℝ) < Q := by exact_mod_cast hQpos
    rw [div_le_iff₀ hQpos']
    rw [div_le_iff₀ hr] at hQR
    nlinarith [hQR, hr, hQpos']
  have hmem : q ∈ {q : ℕ | 1 ≤ q ∧ ∀ i, latticeClose ((q : ℝ) * β i) r} :=
    ⟨hq1, fun i => latticeClose_mono (hclose i) hle⟩
  exact le_trans (Nat.sInf_le hmem) hqQ

/-- **The lower half of the first-hit exponent.**  A multiple that misses the Diophantine radius but
enters the `r`-neighbourhood forces `r` above that radius. -/
theorem rpow_lt_of_hit {β : Fin m → ℝ} {c r : ℝ} {q : ℕ}
    (hfail : ∃ i, ∀ p : ℤ, (q : ℝ) ^ (-c) ≤ |(q : ℝ) * β i - p|)
    (hhit : ∀ i, latticeClose ((q : ℝ) * β i) r) :
    (q : ℝ) ^ (-c) < r := by
  obtain ⟨i, hi⟩ := hfail
  obtain ⟨p, hp⟩ := hhit i
  exact lt_of_le_of_lt (hi p) hp

/-- The exponent form: the hitting time is at least `r^{-1/c}`. -/
theorem rpow_lt_cast_of_hit {β : Fin m → ℝ} {c r : ℝ} {q : ℕ} (hc : 0 < c)
    (hq : 0 < q)
    (hfail : ∃ i, ∀ p : ℤ, (q : ℝ) ^ (-c) ≤ |(q : ℝ) * β i - p|)
    (hhit : ∀ i, latticeClose ((q : ℝ) * β i) r) :
    r ^ (-(1 / c)) < (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlt := rpow_lt_of_hit hfail hhit
  have hmono : (((q : ℝ) ^ (-c)) ^ (-(1 / c))) > r ^ (-(1 / c)) := by
    refine Real.rpow_lt_rpow_of_neg (by positivity) hlt ?_
    simpa using (by positivity : (0:ℝ) < 1 / c)
  have hcancel : (((q : ℝ) ^ (-c)) ^ (-(1 / c))) = (q : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hqR)]
    rw [show -c * -(1 / c) = 1 by field_simp]
    exact Real.rpow_one _
  rw [hcancel] at hmono
  exact hmono

end FirstHit

end GaloisForLFunctions.HTGeometry
