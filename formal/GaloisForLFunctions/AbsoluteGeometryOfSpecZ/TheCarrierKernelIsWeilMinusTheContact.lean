import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsOffDiagonalIsContactsPlusJets
import GaloisForLFunctions.HyperbolicArakelovTheory.TheFinitePartOfTheCoupledAdelicOrbit
import GaloisForLFunctions.RHTower.HardyZ
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# The carrier kernel is Weil's pairing minus the contact

Three presentations of the off-diagonal of Weil's form exist in the corpus: the intersection
numbers `Γ_m · Γ_n` defined from Weil's form (`SurfaceOfSpecZ.frobeniusIntersection`), the contacts
of the Frobenius graphs in the arithmetic square (`graphIdeal`), and the product of the local
critical Green kernels on the rational torus orbit of the adelic carrier
(`HyperbolicArakelovTheory.CoupledOrbit.term`). On a reduced rational displacement `a/b < 1` the
last is `b⁻²/(1 − (a/b)⁴)`. This file relates the three by one identity.

* **The off-diagonal identity on the carrier** (`frobeniusIntersection_sq_eq_carrier_add_contact`):

    `Γ_{a²} · Γ_{b²} = (ab)² · b⁻²/(1 − (a/b)⁴) + log #(ℤ/J(a², b²))`.

  The coupled kernel of the carrier is Weil's pairing of the **square** degrees, normalized by the
  square of the height product, minus the contact of the arithmetic square; the contact is `Λ(b)` if
  `a = 1` and `0` otherwise (`log_card_quotient_graphIdeal_sq`). The product of local kernels
  carries the jets and not the primes.
* **Rows** (`geometricRow_eq_weilRow_sub`): the height row of the carrier is the row of Weil's
  pairing minus `Λ(n)/n²`.
* **Finite parts** (`tendsto_weilRow_finitePart`): Weil's pairing on the reduced square degrees has
  a finite part under the same two counterterms as the carrier orbit, the collision row and the
  density row, and the two finite parts differ by the convergent contact series `Σ Λ(n)/n²`.
* **The density constant** (`four_mul_regularMean_eq`): `4c₀ = −2γ₀ − (log 4π + γ)`, where
  `c₀ = log 2/4 + π/8` is the density mean of the carrier and `γ₀` the logarithmic derivative of the
  Gamma factor at the centre: the counterterm of the carrier is fixed by the two constants of
  Weil's archimedean diagonal.

What remains of the comparison is the diagonal itself: the self-pairing `Γ_n²`.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.SurfaceOfSpecZ GaloisForLFunctions.HyperbolicArakelovTheory.CoupledOrbit

/-! ### The off-diagonal identity -/

/-- The contact of the square degrees: `Λ(b)` if `a = 1`, and `0` otherwise. -/
theorem log_card_quotient_graphIdeal_sq {a b : ℕ+} (h : Nat.Coprime a b) (hab : a < b) :
    Real.log (Nat.card (ℤ ⧸ graphIdeal (a ^ 2) (b ^ 2))) = if a = 1 then Λ (b : ℕ) else 0 := by
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have hb1 : (1 : ℕ+) < b ^ 2 := by
    have h1 : (1 : ℕ) < (b : ℕ) := lt_of_le_of_lt a.pos hab'
    have : (1 : ℕ) < ((b ^ 2 : ℕ+) : ℕ) := by rw [PNat.pow_coe]; nlinarith
    exact this
  by_cases ha : a = 1
  · subst ha
    rw [if_pos rfl, one_pow, log_card_quotient_graphIdeal_one hb1, PNat.pow_coe,
      ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]
  · have ha1 : (1 : ℕ+) < a ^ 2 := by
      have hne : (a : ℕ) ≠ 1 := fun h1 => ha (PNat.eq (by simpa using h1))
      have hpos := a.pos
      have h2 : 2 ≤ (a : ℕ) := by omega
      have : (1 : ℕ) < ((a ^ 2 : ℕ+) : ℕ) := by rw [PNat.pow_coe]; nlinarith
      exact this
    have hcop : Nat.Coprime ((a ^ 2 : ℕ+) : ℕ) ((b ^ 2 : ℕ+) : ℕ) := by
      rw [PNat.pow_coe, PNat.pow_coe]; exact h.pow 2 2
    rw [if_neg ha, log_card_quotient_eq_zero_of_eq_top (graphIdeal_eq_top_of_coprime hcop ha1 hb1)]

/-- **The off-diagonal identity on the carrier.** Weil's pairing of the square degrees is the
coupled critical kernel of the adelic carrier, normalized by the square of the height product,
plus the contact of the arithmetic square. -/
theorem frobeniusIntersection_sq_eq_carrier_add_contact {a b : ℕ+} (h : Nat.Coprime a b)
    (hab : a < b) :
    frobeniusIntersection ((a : ℕ) ^ 2) ((b : ℕ) ^ 2) =
      (((a : ℕ) : ℝ) * (b : ℕ)) ^ 2 * term 2 ⟨((a : ℕ), (b : ℕ)), a.pos, hab, h⟩ +
        Real.log (Nat.card (ℤ ⧸ graphIdeal (a ^ 2) (b ^ 2))) := by
  have hab' : (a : ℕ) < (b : ℕ) := hab
  have hA : (0 : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast a.pos
  have hB : (0 : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast b.pos
  have hAB : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab'
  have hcop : Nat.Coprime ((a ^ 2 : ℕ+) : ℕ) ((b ^ 2 : ℕ+) : ℕ) := by
    rw [PNat.pow_coe, PNat.pow_coe]; exact h.pow 2 2
  have hlt : a ^ 2 < b ^ 2 := by
    have : ((a ^ 2 : ℕ+) : ℕ) < ((b ^ 2 : ℕ+) : ℕ) := by
      rw [PNat.pow_coe, PNat.pow_coe]; exact Nat.pow_lt_pow_left hab' two_ne_zero
    exact this
  have hW := frobeniusIntersection_reduced 1 hcop hlt
  rw [PNat.one_coe, one_mul, one_mul, Nat.cast_one, one_mul, one_mul, PNat.pow_coe,
    PNat.pow_coe] at hW
  rw [hW]
  congr 1
  -- `a²/(1 − (a²/b²)²) = (ab)² b⁻²/(1 − (a/b)⁴)`
  have hr : ((a : ℕ) : ℝ) / (b : ℕ) < 1 := (div_lt_one hB).mpr hAB
  have hr0 : (0 : ℝ) < ((a : ℕ) : ℝ) / (b : ℕ) := div_pos hA hB
  have hden : (1 : ℝ) - (((a : ℕ) : ℝ) / (b : ℕ)) ^ 4 ≠ 0 := by
    have : (((a : ℕ) : ℝ) / (b : ℕ)) ^ 4 < 1 := pow_lt_one₀ hr0.le hr (by norm_num)
    linarith
  have hsq : (((((a : ℕ) ^ 2 : ℕ) : ℝ)) / (((b : ℕ) ^ 2 : ℕ) : ℝ)) ^ 2 =
      (((a : ℕ) : ℝ) / (b : ℕ)) ^ 4 := by
    push_cast
    rw [← div_pow, ← pow_mul]
  rw [hsq, term, Real.rpow_neg hB.le, Real.rpow_two]
  push_cast
  field_simp

/-- The same identity for natural degrees, with the contact evaluated. -/
theorem frobeniusIntersection_sq_of_coprime {a n : ℕ} (ha : 0 < a) (han : a < n)
    (h : Nat.Coprime a n) :
    frobeniusIntersection (a ^ 2) (n ^ 2) =
      ((n : ℝ) ^ 2)⁻¹ * (1 / (1 - ((a : ℝ) / n) ^ 4)) * ((a : ℝ) * n) ^ 2 +
        if a = 1 then Λ n else 0 := by
  obtain ⟨A, rfl⟩ : ∃ A : ℕ+, (A : ℕ) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨B, rfl⟩ : ∃ B : ℕ+, (B : ℕ) = n := ⟨⟨n, ha.trans han⟩, rfl⟩
  have hAB : A < B := han
  have hB : (0 : ℝ) < ((B : ℕ) : ℝ) := by exact_mod_cast B.pos
  rw [frobeniusIntersection_sq_eq_carrier_add_contact h hAB,
    log_card_quotient_graphIdeal_sq h hAB, term, Real.rpow_neg hB.le, Real.rpow_two]
  have hA1 : (A = 1) ↔ ((A : ℕ) = 1) := ⟨fun h1 => by rw [h1]; rfl, fun h1 => PNat.eq h1⟩
  simp only [hA1]
  congr 1
  ring

/-! ### Rows and finite parts -/

/-- The row of Weil's pairing on the reduced square degrees at height `n`. -/
def weilRow (n : ℕ) : ℝ :=
  if 2 ≤ n then ∑ a ∈ Icc 1 n,
    if Nat.Coprime n a then frobeniusIntersection (a ^ 2) (n ^ 2) / ((a : ℝ) * n) ^ 2 else 0
  else 0

/-- **The height row of the carrier is the row of Weil's pairing minus the contact `Λ(n)/n²`.** -/
theorem geometricRow_eq_weilRow_sub (n : ℕ) :
    geometricRow n = weilRow n - Λ n / (n : ℝ) ^ 2 := by
  by_cases hn : 2 ≤ n
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have h1mem : (1 : ℕ) ∈ Icc 1 n := mem_Icc.mpr ⟨le_refl 1, by omega⟩
    -- the contact sits at `a = 1` only
    have hcontact : ∑ a ∈ Icc 1 n,
        (if Nat.Coprime n a then (if a = 1 then Λ n else 0) / ((a : ℝ) * n) ^ 2 else 0) =
        Λ n / (n : ℝ) ^ 2 := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro a _ ha1
        simp [ha1]
      · exact fun h => absurd h1mem h
    rw [geometricRow, weilRow, if_pos hn, if_pos hn, ← hcontact, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases hc : Nat.Coprime n a
    · have hapos : 0 < a := (mem_Icc.mp ha).1
      have hlt : a < n := by
        refine lt_of_le_of_ne (mem_Icc.mp ha).2 fun he => ?_
        subst he
        have : a = 1 := by simpa only [Nat.coprime_self] using hc
        omega
      have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
      rw [if_pos hc, if_pos hc, if_pos hc, frobeniusIntersection_sq_of_coprime hapos hlt hc.symm,
        ← sub_div, add_sub_cancel_right]
      field_simp
    · rw [if_neg hc, if_neg hc, if_neg hc, mul_zero, sub_zero]
  · have hΛ : Λ n = 0 := by
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> simp
    rw [geometricRow, weilRow, if_neg hn, if_neg hn, hΛ, zero_div, sub_zero]

/-- The contact series `Σ Λ(n)/n²` converges. -/
theorem summable_vonMangoldt_div_sq : Summable fun n : ℕ => Λ n / (n : ℝ) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sq_nonneg _)) (fun n => ?_)
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- `Λ(n) ≤ log n ≤ 2 √n`
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt n := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hn0)
    have h2 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt n) := by
      rw [Real.log_sqrt hn0.le]; ring
    linarith
  have hΛ : Λ n ≤ 2 * Real.sqrt n := ArithmeticFunction.vonMangoldt_le_log.trans hlog
  have hpow : ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ = Real.sqrt n / (n : ℝ) ^ 2 := by
    rw [Real.sqrt_eq_rpow, inv_eq_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul,
      ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]
    norm_num
  rw [hpow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hΛ (sq_nonneg _)

/-- **The finite part of Weil's pairing on the reduced square degrees.** Under the collision and
density counterterms of the carrier orbit, the rows of Weil's pairing converge, and their finite
part is the finite part of the carrier plus the contact series. -/
theorem tendsto_weilRow_finitePart :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, weilRow n) - (∑ n ∈ range N, collisionRow n) -
      (∑ n ∈ range N, densityRow n)) atTop
      (𝓝 (orbitFinitePart + ∑' n : ℕ, Λ n / (n : ℝ) ^ 2)) := by
  have h := tendsto_orbit_finitePart.add summable_vonMangoldt_div_sq.hasSum.tendsto_sum_nat
  refine h.congr fun N => ?_
  have hrow : ∑ n ∈ range N, geometricRow n =
      ∑ n ∈ range N, weilRow n - ∑ n ∈ range N, Λ n / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => geometricRow_eq_weilRow_sub n
  rw [hrow]
  ring

/-! ### The density constant -/

/-- **The density constant of the carrier is fixed by Weil's two archimedean constants**:
`4c₀ = −2γ₀ − (log 4π + γ)`, with `γ₀` the logarithmic derivative of the Gamma factor at the
centre. -/
theorem four_mul_regularMean_eq :
    4 * regularMean = -2 * _root_.RHTower.gammaHardyPhaseRate 0 -
      (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) := by
  have h14 : _root_.RHTower.linePt 0 / 2 = (1 / 4 : ℂ) := by
    simp only [_root_.RHTower.linePt, Complex.ofReal_zero, zero_mul, add_zero]
    push_cast
    norm_num
  have hlog : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [regularMean_eq, _root_.RHTower.gammaHardyPhaseRate, h14,
    GaloisForLFunctions.RHTower.digamma_quarter, hlog, Complex.neg_re, Complex.ofReal_re]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
