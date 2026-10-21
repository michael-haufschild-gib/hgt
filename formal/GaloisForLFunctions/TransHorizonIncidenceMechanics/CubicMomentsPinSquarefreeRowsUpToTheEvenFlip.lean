import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipIsTheFermiTransformOfTheEvenPart

/-!
# Cubic moments pin squarefree rows up to the even flip

Let `c` be a horizon-`N` row whose Selberg coordinates are nonzero exactly at the squarefree moduli —
for instance every actual PM cofactor row, `Y_{Q+1}(e) = w_ε(e) = ρ_ε μ(e)/D_ε(e)`. If a sign twist
`c^σ = scaledSelbergRow N c σ` has the cubic translated moments of `c` at every shift, then:

* at an odd squarefree modulus `q` the triple `ζ_q ζ_q ζ_q^{q-2} = 1` forces `σ(q) = 1`;
* at an even squarefree modulus `2q'` the triple of orders `(2, q', 2q')`, realised as
  `η^{q'} η² η^{q'-2} = 1` for a primitive `2q'`-th root `η`, forces `σ(2q') = σ(2)`.

Hence `c^σ` is `c` itself or its even flip `c^♭` on `[1, N]`. The even flip is invisible to every
translated moment and is the Fermi transform of the even part (previous module), so **cubic additive
data determine the receiver of a squarefree row up to the Fermi receiver of its even part**: no parity
pair of PM receiver rows survives the cubic moments except through the prime `2`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- At an even squarefree modulus `2q'` the cubic moments tie the sign to `σ(2)`:
`σ(2) σ(q') σ(2q') = 1` whenever the three coordinates are nonzero. -/
theorem sign_two_mul_eq_of_translatedMoment_three {N q : ℕ} (hq : 3 ≤ q) (hodd : Odd q)
    (h2q : 2 * q ≤ N) (c : ℕ → ℝ) (σ : ℕ → ℝ)
    (hY2 : selbergMultiplesCoord N c 2 ≠ 0) (hYq : selbergMultiplesCoord N c q ≠ 0)
    (hY2q : selbergMultiplesCoord N c (2 * q) ≠ 0)
    (hall : ∀ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c σ) v =
      SieveMoments.translatedMoment N c v) :
    σ 2 * σ q * σ (2 * q) = 1 := by
  have hn : 0 < 2 * q := by omega
  have hη := Complex.isPrimitiveRoot_exp (2 * q) hn.ne'
  set η := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(2 * q))
  -- the three frequencies and their orders
  have h1 : IsPrimitiveRoot (η ^ q) 2 := by
    have := hη.pow_of_dvd (show q ≠ 0 by omega) (dvd_mul_left q 2)
    rwa [Nat.mul_div_cancel _ (by omega : 0 < q)] at this
  have h2 : IsPrimitiveRoot (η ^ 2) q := by
    have := hη.pow_of_dvd (show (2 : ℕ) ≠ 0 by norm_num) (dvd_mul_right 2 q)
    rwa [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at this
  have hcop : Nat.Coprime (q - 2) (2 * q) := by
    have hodd2 : Odd (q - 2) := by obtain ⟨t, ht⟩ := hodd; exact ⟨t - 1, by omega⟩
    refine Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd2) ?_
    have hq2 : q = 2 + (q - 2) := by omega
    rw [Nat.Coprime]
    nth_rewrite 2 [hq2]
    rw [Nat.gcd_add_self_right]
    exact Nat.coprime_two_right.mpr hodd2
  have h3 : IsPrimitiveRoot (η ^ (q - 2)) (2 * q) := hη.pow_of_coprime _ hcop
  have hm2 : (2 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by norm_num, by omega⟩
  have hmq : q ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
  have hm2q : 2 * q ∈ Icc 1 N := mem_Icc.mpr ⟨hn, h2q⟩
  set τ : Fin 3 → ℂ := ![η ^ q, η ^ 2, η ^ (q - 2)]
  have hτ : τ ∈ Fintype.piFinset (fun _ : Fin 3 => responseRoots N) := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i
    · exact primitiveRoot_mem_responseRoots hm2 h1
    · exact primitiveRoot_mem_responseRoots hmq h2
    · exact primitiveRoot_mem_responseRoots hm2q h3
  have hprod : ∏ i, τ i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← pow_add, ← pow_add, show q + 2 + (q - 2) = 2 * q by omega, hη.pow_eq_one]
  have h := (translatedMoment_scaled_eq_iff N c σ 3).mp hall τ hτ hprod
  have ho0 : orderOf (τ 0) = 2 := h1.eq_orderOf.symm
  have ho1 : orderOf (τ 1) = q := h2.eq_orderOf.symm
  have ho2 : orderOf (τ 2) = 2 * q := h3.eq_orderOf.symm
  rw [Fin.prod_univ_three, Fin.prod_univ_three, ho0, ho1, ho2] at h
  have hY : selbergMultiplesCoord N c 2 * selbergMultiplesCoord N c q *
      selbergMultiplesCoord N c (2 * q) ≠ 0 := mul_ne_zero (mul_ne_zero hY2 hYq) hY2q
  have := (mul_eq_zero.mp h).resolve_left hY
  linarith

/-- A sign with `σ² = 1` and `σ³ = 1` is `1`. -/
private theorem eq_one_of_sq_of_cube' {s : ℝ} (h2 : s * s = 1) (h3 : s ^ 3 = 1) : s = 1 := by
  have : s ^ 3 = s := by rw [pow_succ, sq, h2, one_mul]
  linarith

/-- **Cubic moments pin squarefree rows up to the even flip.** If the coordinates of `c` vanish off
the squarefree moduli and are nonzero at every squarefree modulus `≤ N`, and the twist by `σ` has the
cubic translated moments of `c`, then the twist is `c` or its even flip on `[1, N]`. -/
theorem scaledSelbergRow_eq_or_evenFlip_of_translatedMoment_three {N : ℕ} (c : ℕ → ℝ) (σ : ℕ → ℝ)
    (hσ : ∀ q, σ q * σ q = 1)
    (hns : ∀ q ∈ Icc 1 N, ¬ Squarefree q → selbergMultiplesCoord N c q = 0)
    (hsq : ∀ q ∈ Icc 1 N, Squarefree q → selbergMultiplesCoord N c q ≠ 0)
    (hall : ∀ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (scaledSelbergRow N c σ) v =
      SieveMoments.translatedMoment N c v) :
    (∀ d ∈ Icc 1 N, scaledSelbergRow N c σ d = c d) ∨
      (∀ d ∈ Icc 1 N, scaledSelbergRow N c σ d = evenFlipRow N c d) := by
  -- odd squarefree moduli carry the sign `1`
  have hodd : ∀ q ∈ Icc 1 N, Odd q → Squarefree q → σ q = 1 := fun q hq ho hs =>
    eq_one_of_sq_of_cube' (hσ q) (sign_cube_eq_one_of_translatedMoment_three hq ho c σ (hsq q hq hs) hall)
  -- even squarefree moduli carry the sign of `2`
  have heven : ∀ q ∈ Icc 1 N, Even q → Squarefree q → σ q = σ 2 := by
    intro q hq he hs
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by obtain ⟨k, hk⟩ := he; omega⟩
    have hq'odd : Odd q' := by
      rcases Nat.even_or_odd q' with h | h
      · exfalso
        obtain ⟨g, rfl⟩ := h
        have : (2 * 2) ∣ 2 * (g + g) := ⟨g, by ring⟩
        exact absurd (hs 2 (by simpa [mul_comm, two_mul] using this)) (by decide)
      · exact h
    have hq' := mem_Icc.mp hq
    rcases Nat.lt_or_ge q' 3 with hlt | hge
    · -- `q' = 1`: the modulus is `2` itself
      have : q' = 1 := by obtain ⟨t, ht⟩ := hq'odd; omega
      subst this; rfl
    · have hm2 : (2 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by norm_num, by omega⟩
      have hmq : q' ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
      have hs' : Squarefree q' := Squarefree.of_mul_right hs
      have h3 := sign_two_mul_eq_of_translatedMoment_three hge hq'odd hq'.2 c σ
        (hsq 2 hm2 Nat.squarefree_two) (hsq q' hmq hs') (hsq _ hq hs) hall
      rw [hodd q' hmq hq'odd hs', mul_one] at h3
      have h22 := hσ 2
      have : σ (2 * q') = σ 2 * (σ 2 * σ (2 * q')) := by rw [← mul_assoc, h22, one_mul]
      rw [this, h3, mul_one]
  have hsign : ∀ q ∈ Icc 1 N, σ q * selbergMultiplesCoord N c q =
      (if σ 2 = 1 then 1 else evenSign q) * selbergMultiplesCoord N c q := by
    intro q hq
    by_cases hs : Squarefree q
    · rcases Nat.even_or_odd q with he | ho
      · rw [heven q hq he hs]
        split_ifs with h21
        · rw [h21]
        · have : σ 2 = -1 := (mul_self_eq_one_iff.mp (hσ 2)).resolve_left h21
          rw [this, evenSign, if_pos (even_iff_two_dvd.mp he)]
      · rw [hodd q hq ho hs]
        split_ifs
        · rfl
        · rw [evenSign, if_neg (fun h => by have := Nat.odd_iff.mp ho; omega)]
    · rw [hns q hq hs, mul_zero, mul_zero]
  have hrow : ∀ (τ : ℕ → ℝ), (∀ q ∈ Icc 1 N, σ q * selbergMultiplesCoord N c q =
      τ q * selbergMultiplesCoord N c q) →
      ∀ d ∈ Icc 1 N, scaledSelbergRow N c σ d = scaledSelbergRow N c τ d := by
    intro τ hτ d hd
    unfold scaledSelbergRow RHTower.pmRamanujanResidueCoeff
    congr 1
    refine sum_congr rfl fun m hm => ?_
    have hd1 := (mem_Icc.mp hd).1
    have hdm : d * m ∈ Icc 1 N := by
      refine mem_Icc.mpr ⟨Nat.mul_pos hd1 (mem_Icc.mp hm).1, ?_⟩
      calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d (mem_Icc.mp hm).2
        _ ≤ N := Nat.mul_div_le N d
    dsimp only
    rw [hτ (d * m) hdm]
  by_cases h21 : σ 2 = 1
  · left
    intro d hd
    rw [hrow (fun _ => 1) (fun q hq => by rw [hsign q hq, if_pos h21]) d hd]
    rw [← ramanujan_inverse_selbergCoords_eq N c d hd]
    unfold scaledSelbergRow
    simp only [one_mul]
  · right
    intro d hd
    rw [hrow evenSign (fun q hq => by rw [hsign q hq, if_neg h21]) d hd]
    rfl

/-! ### The PM receiver rows -/

/-- The PM cofactor rows have nonzero coordinates exactly at the squarefree moduli. -/
theorem selbergMultiplesCoord_pmCofactor_ne {ε : ℝ} (hε : 0 < ε) {Q q : ℕ}
    (hq : q ∈ Icc 1 (Q + 1)) (hs : Squarefree q) :
    selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) q ≠ 0 := by
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hq]
  change dampedRamanujanCoeff ε q ≠ 0
  rw [dampedRamanujanCoeff_eq_closed hε]
  have hμ : (moebius q : ℝ) ≠ 0 := by
    exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs
  exact div_ne_zero (mul_ne_zero (RHTower.pmPowerDampedDivisorDensity_re_pos hε).ne' hμ)
    (RHTower.pmPowerDampedRamanujanDenominator_pos hε q).ne'

theorem selbergMultiplesCoord_pmCofactor_eq_zero (ε : ℝ) {Q q : ℕ}
    (hq : q ∈ Icc 1 (Q + 1)) (hs : ¬ Squarefree q) :
    selbergMultiplesCoord (Q + 1) (pmCofactorDivisorWeight ε Q) q = 0 := by
  rw [selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε hq,
    RHTower.pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hs, Complex.zero_re]

/-- **No parity twist of a PM receiver row survives the cubic moments, except the even flip.** At
every level `Q`, a sign twist of the cofactor row with the row's cubic translated moments is the row
or its even flip on `[1, Q+1]`. -/
theorem pmCofactor_twist_eq_or_evenFlip {ε : ℝ} (hε : 0 < ε) (Q : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ q, σ q * σ q = 1)
    (hall : ∀ v : Fin 3 → ℕ, SieveMoments.translatedMoment (Q + 1)
      (scaledSelbergRow (Q + 1) (pmCofactorDivisorWeight ε Q) σ) v =
        SieveMoments.translatedMoment (Q + 1) (pmCofactorDivisorWeight ε Q) v) :
    (∀ d ∈ Icc 1 (Q + 1), scaledSelbergRow (Q + 1) (pmCofactorDivisorWeight ε Q) σ d =
        pmCofactorDivisorWeight ε Q d) ∨
      (∀ d ∈ Icc 1 (Q + 1), scaledSelbergRow (Q + 1) (pmCofactorDivisorWeight ε Q) σ d =
        evenFlipRow (Q + 1) (pmCofactorDivisorWeight ε Q) d) :=
  scaledSelbergRow_eq_or_evenFlip_of_translatedMoment_three _ σ hσ
    (fun _ hq hs => selbergMultiplesCoord_pmCofactor_eq_zero ε hq hs)
    (fun _ hq hs => selbergMultiplesCoord_pmCofactor_ne hε hq hs) hall

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
