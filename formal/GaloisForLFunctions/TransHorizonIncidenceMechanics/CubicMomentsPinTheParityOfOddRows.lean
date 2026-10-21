import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityRowsAtEveryHorizon

/-!
# Cubic moments pin the parity of odd rows

For a horizon-`N` row `c` and a sign pattern `σ` (`σ(q)² = 1`), the twisted row
`c^σ = scaledSelbergRow N c σ` has Selberg coordinates `σ(q) Y_N(q)`. Every two-point translated moment
of `c^σ` equals that of `c` (two-point blindness), and the parity rows of the character `χ₄` show that
the trans-horizon receiver can still separate them.

At degree three the separation is complete. The zero-product triple `ζ_q · ζ_q · ζ_q^{q-2} = 1` of a
primitive `q`-th root of unity (`q` odd; `gcd(q - 2, q) = 1`) has coefficient
`Y(q)³ (1 - σ(q)³)` in the difference of the cubic moment arrays (the BVI sign visibility law). Hence
if `c` is supported on the odd moduli — `Y_N(q) = 0` for even `q`, `Y_N(q) ≠ 0` for odd `q` — and
`c^σ` has the same cubic translated moments at every shift, then `σ = 1` on every odd modulus and
`c^σ = c` on `[1, N]`: **no parity pair survives the cubic translated moments.** The separating
observable of the parity rows is exactly the cubic moment at a single modulus, and its loss at
degree three is zero.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The cubic moment reads the sign at every odd modulus: if the twisted row has the cubic translated
moments of `c` and `Y_N(q) ≠ 0` at an odd `q ≤ N`, then `σ(q)³ = 1`. -/
theorem sign_cube_eq_one_of_translatedMoment_three {N q : ℕ} (hq : q ∈ Icc 1 N) (hodd : Odd q)
    (c : ℕ → ℝ) (σ : ℕ → ℝ) (hY : selbergMultiplesCoord N c q ≠ 0)
    (hall : ∀ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c σ) v =
      SieveMoments.translatedMoment N c v) :
    σ q ^ 3 = 1 := by
  have hq' := mem_Icc.mp hq
  have hq0 : 0 < q := hq'.1
  have hζ := Complex.isPrimitiveRoot_exp q hq0.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑q)
  have hcop : Nat.Coprime (q - 2) q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · have : q = 1 := by omega
      subst this; simp
    · have hodd2 : Odd (q - 2) := by
        obtain ⟨t, ht⟩ := hodd
        exact ⟨t - 1, by omega⟩
      have h2 := Nat.coprime_two_right.mpr hodd2
      have hq2 : q = 2 + (q - 2) := by omega
      rw [Nat.Coprime]
      nth_rewrite 2 [hq2]
      rw [Nat.gcd_add_self_right]
      exact h2
  have hξ := hζ.pow_of_coprime (q - 2) hcop
  set τ : Fin 3 → ℂ := ![ζ, ζ, ζ ^ (q - 2)]
  have hτ : τ ∈ Fintype.piFinset (fun _ : Fin 3 => responseRoots N) := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i
    · exact primitiveRoot_mem_responseRoots hq hζ
    · exact primitiveRoot_mem_responseRoots hq hζ
    · exact primitiveRoot_mem_responseRoots hq hξ
  have hprod : ∏ i, τ i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rcases Nat.lt_or_ge q 2 with h | h
    · have : q = 1 := by omega
      subst this
      have h1 : ζ = 1 := by simpa using hζ.pow_eq_one
      simp [h1]
    · rw [← pow_two, ← pow_add, show 2 + (q - 2) = q by omega, hζ.pow_eq_one]
  have h := (translatedMoment_scaled_eq_iff N c σ 3).mp hall τ hτ hprod
  have hord : ∀ i, orderOf (τ i) = q := by
    intro i
    fin_cases i
    · exact hζ.eq_orderOf.symm
    · exact hζ.eq_orderOf.symm
    · exact hξ.eq_orderOf.symm
  simp only [hord, prod_const, card_univ, Fintype.card_fin] at h
  have hY3 : selbergMultiplesCoord N c q ^ 3 ≠ 0 := pow_ne_zero 3 hY
  have := (mul_eq_zero.mp h).resolve_left hY3
  linarith

/-- A sign with `σ² = 1` and `σ³ = 1` is `1`. -/
private theorem eq_one_of_sq_of_cube {s : ℝ} (h2 : s * s = 1) (h3 : s ^ 3 = 1) : s = 1 := by
  have : s ^ 3 = s := by rw [pow_succ, sq, h2, one_mul]
  linarith

/-- **Cubic moments pin the parity of odd rows.** If `c` is supported on the odd moduli at horizon
`N` and its twist by a sign pattern `σ` has the same cubic translated moments at every shift, then the
twisted row is `c` itself on `[1, N]`. -/
theorem scaledSelbergRow_eq_of_translatedMoment_three {N : ℕ} (c : ℕ → ℝ) (σ : ℕ → ℝ)
    (hσ : ∀ q, σ q * σ q = 1)
    (heven : ∀ q ∈ Icc 1 N, Even q → selbergMultiplesCoord N c q = 0)
    (hodd : ∀ q ∈ Icc 1 N, Odd q → selbergMultiplesCoord N c q ≠ 0)
    (hall : ∀ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c σ) v =
      SieveMoments.translatedMoment N c v) :
    ∀ d ∈ Icc 1 N, scaledSelbergRow N c σ d = c d := by
  have hfix : ∀ q ∈ Icc 1 N, σ q * selbergMultiplesCoord N c q = selbergMultiplesCoord N c q := by
    intro q hq
    rcases Nat.even_or_odd q with he | ho
    · rw [heven q hq he, mul_zero]
    · rw [eq_one_of_sq_of_cube (hσ q)
        (sign_cube_eq_one_of_translatedMoment_three hq ho c σ (hodd q hq ho) hall), one_mul]
  intro d hd
  rw [← ramanujan_inverse_selbergCoords_eq N c d hd]
  unfold scaledSelbergRow RHTower.pmRamanujanResidueCoeff
  congr 1
  refine sum_congr rfl fun m hm => ?_
  have hm1 := (mem_Icc.mp hm).1
  have hd1 := (mem_Icc.mp hd).1
  have hdm : d * m ∈ Icc 1 N := by
    refine mem_Icc.mpr ⟨Nat.mul_pos hd1 hm1, ?_⟩
    calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d (mem_Icc.mp hm).2
      _ ≤ N := Nat.mul_div_le N d
  dsimp only
  rw [hfix (d * m) hdm]

/-- The character rows are supported on the odd moduli at every horizon. -/
theorem selbergMultiplesCoord_chiFourRow_even (ε : ℝ) {N q : ℕ} (hq : q ∈ Icc 1 N) (he : Even q) :
    selbergMultiplesCoord N (chiFourRow ε N) q = 0 := by
  rw [selbergMultiplesCoord_chiFourRow ε (mem_Icc.mp hq).1]
  have : chiFour q = 0 := by rw [chiFour_eq, if_pos (Nat.even_iff.mp he)]
  simp [dampedSignWeight, this]

theorem selbergMultiplesCoord_chiFourRow_odd_ne {ε : ℝ} (hε : 0 < ε) {N q : ℕ} (hq : q ∈ Icc 1 N)
    (ho : Odd q) : selbergMultiplesCoord N (chiFourRow ε N) q ≠ 0 := by
  have hq' := mem_Icc.mp hq
  rw [selbergMultiplesCoord_chiFourRow ε hq'.1]
  have hX : 1 ≤ N / q := (Nat.le_div_iff_mul_le hq'.1).mpr (by simpa using hq'.2)
  have hL := chiFourPartialMass_pos hε hX
  have hχ : chiFour q ≠ 0 := by
    rw [chiFour_eq, if_neg (by have := Nat.odd_iff.mp ho; omega)]
    split_ifs <;> norm_num
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq'.1
  refine mul_ne_zero ?_ hL.ne'
  exact div_ne_zero (mul_ne_zero hχ (Real.rpow_pos_of_pos hq0 _).ne') hq0.ne'

/-- **No parity pair of the character rows survives the cubic moments.** At every horizon, a sign
twist of the character row with the cubic translated moments of the row is the row itself; the twist
`χ₄` of the parity rows is separated by them (`exists_translatedMoment_three_chiFourTwinRow_ne`). -/
theorem chiFourRow_eq_of_cubic_moments {ε : ℝ} (hε : 0 < ε) (N : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ q, σ q * σ q = 1)
    (hall : ∀ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N (chiFourRow ε N) σ) v
      = SieveMoments.translatedMoment N (chiFourRow ε N) v) :
    ∀ d ∈ Icc 1 N, scaledSelbergRow N (chiFourRow ε N) σ d = chiFourRow ε N d :=
  scaledSelbergRow_eq_of_translatedMoment_three _ σ hσ
    (fun _ hq he => selbergMultiplesCoord_chiFourRow_even ε hq he)
    (fun _ hq ho => selbergMultiplesCoord_chiFourRow_odd_ne hε hq ho) hall

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
