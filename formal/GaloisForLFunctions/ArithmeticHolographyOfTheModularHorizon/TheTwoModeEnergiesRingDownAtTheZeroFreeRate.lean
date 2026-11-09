import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheRingdownRateOfASeedIsTheZeroFreeRegion
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.ThePairEntriesAreRankinSelbergSeries
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheMaassFormsSeeEveryResonanceInPairs
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The two-mode energies ring down at the zero-free rate

A **two-mode state** of the cavity is `u + c v` for two Maass cusp forms `u, v` and `c ∈ ℂ`; its energy is
`|u + cv|²`. This module proves Zagier's dichotomy for the cavity: the horocycle ringdown rates of the two-mode
energies are exactly the zero-free regions of `ζ`.

**Pair energies decay.** For cusp forms `u, v` with Whittaker coefficients `ρ_u, ρ_v` the polar transform of
`u v̄` on `Re s = 5/4` is `2(s − 1) ξ(2s) G(s; ν_u, ν_v) (2π)^{−s} Σ ρ_u(n) ρ̄_v(n) |n|^{−s}`; in `ξ(2s) G` the
factor `Γ(s)` cancels (`xi_mul_pairGamma`), the four Gamma factors at `Re = 5/8` decay like `e^{−π|t|}` in total,
and the Rankin–Selberg series converges absolutely (`exists_pairPolar_right`). Phragmén–Lindelöf spreads the
bound to the strip (`exists_pairPolar_decay`).

**The rates.** By the ringdown theorem for seeds, a zero-free half-plane `Re z > Θ` makes every two-mode energy
ring down at `y^{1 − Θ/2 − ε}` (`twoMode_rate_of_zeroFree`); conversely a zero `ρ` with `Re ρ > ½` is seen by a
two-mode energy (pairwise visibility and polarization, `exists_twoMode_seeing`) and caps its rate at
`y^{1 − Re ρ/2}` (`re_le_of_twoMode_rate`). Hence

  **RH ⟺ every two-mode energy of the cavity rings down at `y^{3/4 − ε}` for every `ε > 0`**
  (`riemannHypothesis_iff_twoMode_rate`).

M4 (a universal positive decay rate) and M5 (rate `¼`) are thereby exact statements about two-mode cavity states:
a zero-free strip is a common rate `y^α`, `α > ½`, of all two-mode energies (`zeroFreeStrip_iff_twoMode_rate`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.RHTower.DeckPointPair (CuspEigenIndex)

variable {lam₁ lam₂ : ℝ} {u v : ℍ → ℂ} {ρ₁ ρ₂ : ℤ → ℂ}

/-! ### The pair energy on the line `Re s = 5/4` -/

/-- `ξ(2s) G(s; ν₁, ν₂) = s(2s − 1) π^{−s} ζ(2s) 2^{s−3} Π Γ((s ± ν₁ ± ν₂)/2)`: the `Γ(s)` cancels. -/
theorem xi_mul_pairGamma {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1 / 2) (ν₁ ν₂ : ℂ) :
    xi (2 * s) * pairGamma ν₁ ν₂ s = s * (2 * s - 1) * (Real.pi : ℂ) ^ (-s) * riemannZeta (2 * s) *
      (2 : ℂ) ^ (s - 3) * (Gamma ((s + ν₁ + ν₂) / 2) * Gamma ((s + ν₁ - ν₂) / 2) *
        Gamma ((s - ν₁ + ν₂) / 2) * Gamma ((s - ν₁ - ν₂) / 2)) := by
  have hΓs : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  rw [CuspHRate.xi_two_mul_eq_gamma hs h1]
  unfold pairGamma
  field_simp

/-- The Rankin–Selberg series of a pair on `Re s = 5/4` is bounded. -/
theorem exists_pair_series_bound (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    (hρ₁0 : ρ₁ 0 = 0) (hρ₁ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff u n y = ρ₁ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁))
    (hρ₂0 : ρ₂ 0 = 0) (hρ₂ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff v n y = ρ₂ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)) :
    ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ s : ℂ, s.re = 5 / 4 →
      ‖∑' n : ℤ, ρ₁ n * starRingEnd ℂ (ρ₂ n) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)‖ ≤ L₀ := by
  have h1 := CuspMS.summable_sq_all hu hρ₁0 hρ₁ (σ := 5 / 4) (by norm_num)
  have h2 := CuspMS.summable_sq_all hv hρ₂0 hρ₂ (σ := 5 / 4) (by norm_num)
  set g : ℤ → ℝ := fun n => (‖ρ₁ n‖ ^ 2 * |(n : ℝ)| ^ (-(5 / 4 : ℝ)) + ‖ρ₂ n‖ ^ 2 * |(n : ℝ)| ^ (-(5 / 4 : ℝ))) / 2
  have hg : Summable g := (h1.add h2).div_const 2
  refine ⟨∑' n, g n, tsum_nonneg fun n => by positivity, fun s hs => ?_⟩
  refine tsum_of_norm_bounded hg.hasSum fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [hρ₁0, g]
  · have hpos : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_cpow_eq_rpow_re_of_pos hpos, neg_re, hs]
    have hp := Real.rpow_nonneg hpos.le (-(5 / 4 : ℝ))
    simp only [g]
    nlinarith [sq_nonneg (‖ρ₁ n‖ - ‖ρ₂ n‖), mul_nonneg (sq_nonneg (‖ρ₁ n‖ - ‖ρ₂ n‖)) hp]

/-- **The pair energy on `Re s = 5/4` decays like `e^{−π|t|}`**, with an exponent fixed by the Gamma bound alone:
for every pair the bound is `D (1 + |t|)^{4N_Γ + 3} e^{−π|t|}`. -/
theorem pairPolar_right_bound {CΓ : ℝ} {NΓ : ℕ} (hCΓ : 0 ≤ CΓ)
    (hΓ : ∀ y : ℝ, ‖Gamma (((5 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      CΓ * (1 + |y|) ^ NΓ * Real.exp (-(Real.pi * |y| / 2)))
    (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    (hρ₁0 : ρ₁ 0 = 0) (hρ₁ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff u n y = ρ₁ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁))
    (hρ₂0 : ρ₂ 0 = 0) (hρ₂ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff v n y = ρ₂ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, s.re = 5 / 4 → 1 ≤ |s.im| →
      ‖polarTransform (fun z => u z * starRingEnd ℂ (v z)) s‖ ≤
        D * (1 + |s.im|) ^ (4 * NΓ + 3) * Real.exp (-(Real.pi * |s.im|)) := by
  obtain ⟨L₀, hL₀, hL⟩ := exists_pair_series_bound hu hv hρ₁0 hρ₁ hρ₂0 hρ₂
  set t₁ := Real.sqrt (lam₁ - 1 / 4)
  set t₂ := Real.sqrt (lam₂ - 1 / 4)
  set A := 1 + |t₁| + |t₂|
  have hA : 1 ≤ A := by simp only [A]; linarith [abs_nonneg t₁, abs_nonneg t₂]
  refine ⟨16 * L₀ * CΓ ^ 4 * A ^ (4 * NΓ), by positivity, fun s hs ht => ?_⟩
  set T := s.im
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 / 2 := fun h => by rw [h] at hs; norm_num at hs
  have hs2 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hsre : 1 < s.re := by rw [hs]; norm_num
  have him : s.im ≠ 0 := fun h => by simp only [T] at ht; rw [h] at ht; norm_num at ht
  have hseq : s = ((5 / 4 : ℝ) : ℂ) + (T : ℂ) * I := by apply Complex.ext <;> simp [hs, T]
  have hν₁ : CuspL.nu lam₁ = (t₁ : ℂ) * I := rfl
  have hν₂ : CuspL.nu lam₂ = (t₂ : ℂ) * I := rfl
  -- the identity on the line
  have hP : polarTransform (fun z => u z * starRingEnd ℂ (v z)) s =
      2 * (s - 1) * (xi (2 * s) * pairGamma (CuspL.nu lam₁) (CuspL.nu lam₂) s) *
        ((2 * Real.pi : ℂ) ^ (-s) * ∑' n : ℤ, ρ₁ n * starRingEnd ℂ (ρ₂ n) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) := by
    rw [polarTransform_eq_mul hs0 hs1 hs2,
      show seedTransform (fun z => u z * starRingEnd ℂ (v z)) s = pairing s u v from rfl,
      pairing_eq_rankinSelberg hu hv hρ₁0 hρ₁ hρ₂ hsre him]
    have h2s : 2 * s ≠ 0 := mul_ne_zero two_ne_zero hs0
    have h2s1 : 2 * s - 1 ≠ 0 := fun h => hs1 (by linear_combination h / 2)
    have key : 4 * s * (2 * s - 1) * (s - 1) * (xi (2 * s) / (2 * s * (2 * s - 1))) = 2 * (s - 1) * xi (2 * s) := by
      rw [mul_div_assoc', div_eq_iff (mul_ne_zero h2s h2s1)]; ring
    generalize (2 * Real.pi : ℂ) ^ (-s) = Q
    generalize ∑' n : ℤ, ρ₁ n * starRingEnd ℂ (ρ₂ n) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) = L
    generalize pairGamma (CuspL.nu lam₁) (CuspL.nu lam₂) s = G
    rw [show 4 * s * (2 * s - 1) * (s - 1) * (xi (2 * s) / (2 * s * (2 * s - 1)) * (Q * G * L)) =
      (4 * s * (2 * s - 1) * (s - 1) * (xi (2 * s) / (2 * s * (2 * s - 1)))) * (Q * G * L) by ring, key]
    ring
  rw [hP, xi_mul_pairGamma (by rw [hs]; norm_num) hs1]
  have ha : ∀ y : ℝ, ‖Gamma (((5 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      CΓ * (1 + |y|) ^ NΓ * Real.exp (-(Real.pi * |y| / 2)) := hΓ
  have e1 : (s + CuspL.nu lam₁ + CuspL.nu lam₂) / 2 = ((5 / 8 : ℝ) : ℂ) + (((T + t₁ + t₂) / 2 : ℝ) : ℂ) * I := by
    rw [hseq, hν₁, hν₂]; apply Complex.ext <;> simp; ring
  have e2 : (s + CuspL.nu lam₁ - CuspL.nu lam₂) / 2 = ((5 / 8 : ℝ) : ℂ) + (((T + t₁ - t₂) / 2 : ℝ) : ℂ) * I := by
    rw [hseq, hν₁, hν₂]; apply Complex.ext <;> simp; ring
  have e3 : (s - CuspL.nu lam₁ + CuspL.nu lam₂) / 2 = ((5 / 8 : ℝ) : ℂ) + (((T - t₁ + t₂) / 2 : ℝ) : ℂ) * I := by
    rw [hseq, hν₁, hν₂]; apply Complex.ext <;> simp; ring
  have e4 : (s - CuspL.nu lam₁ - CuspL.nu lam₂) / 2 = ((5 / 8 : ℝ) : ℂ) + (((T - t₁ - t₂) / 2 : ℝ) : ℂ) * I := by
    rw [hseq, hν₁, hν₂]; apply Complex.ext <;> simp; ring
  rw [e1, e2, e3, e4]
  set X := 1 + |T|
  have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg T]
  have hY : ∀ c : ℝ, |c| ≤ |t₁| + |t₂| → 1 + |(T + c) / 2| ≤ A * X := by
    intro c hc
    have h1 : |(T + c) / 2| ≤ |T| + |c| := by
      rw [abs_div, abs_two]; have := abs_add_le T c; linarith [abs_nonneg T, abs_nonneg c]
    simp only [A, X]; nlinarith [abs_nonneg T, abs_nonneg t₁, abs_nonneg t₂]
  have hc1 : |t₁ + t₂| ≤ |t₁| + |t₂| := abs_add_le _ _
  have hc2 : |t₁ - t₂| ≤ |t₁| + |t₂| := abs_sub _ _
  have hc3 : |-t₁ + t₂| ≤ |t₁| + |t₂| := by rw [neg_add_eq_sub, abs_sub_comm]; exact abs_sub _ _
  have hc4 : |-t₁ - t₂| ≤ |t₁| + |t₂| := by rw [← neg_add', abs_neg]; exact abs_add_le _ _
  have hexp : Real.exp (-(Real.pi * |(T + t₁ + t₂) / 2| / 2)) * Real.exp (-(Real.pi * |(T + t₁ - t₂) / 2| / 2)) *
      Real.exp (-(Real.pi * |(T - t₁ + t₂) / 2| / 2)) * Real.exp (-(Real.pi * |(T - t₁ - t₂) / 2| / 2)) ≤
      Real.exp (-(Real.pi * |T|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have k1 : 2 * |T| ≤ |T + t₁ + t₂| + |T - t₁ - t₂| := by
      calc 2 * |T| = |(T + t₁ + t₂) + (T - t₁ - t₂)| := by rw [show (T + t₁ + t₂) + (T - t₁ - t₂) = 2 * T by ring,
            abs_mul, abs_two]
        _ ≤ _ := abs_add_le _ _
    have k2 : 2 * |T| ≤ |T + t₁ - t₂| + |T - t₁ + t₂| := by
      calc 2 * |T| = |(T + t₁ - t₂) + (T - t₁ + t₂)| := by rw [show (T + t₁ - t₂) + (T - t₁ + t₂) = 2 * T by ring,
            abs_mul, abs_two]
        _ ≤ _ := abs_add_le _ _
    simp only [abs_div, abs_two]
    nlinarith [Real.pi_pos]
  have hgam : ‖Gamma (((5 / 8 : ℝ) : ℂ) + (((T + t₁ + t₂) / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + (((T + t₁ - t₂) / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + (((T - t₁ + t₂) / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + (((T - t₁ - t₂) / 2 : ℝ) : ℂ) * I)‖ ≤
      CΓ ^ 4 * A ^ (4 * NΓ) * X ^ (4 * NΓ) * Real.exp (-(Real.pi * |T|)) := by
    rw [norm_mul, norm_mul, norm_mul]
    have p1 : (1 + |(T + t₁ + t₂) / 2|) ^ NΓ ≤ (A * X) ^ NΓ :=
      pow_le_pow_left₀ (by positivity) (by rw [show T + t₁ + t₂ = T + (t₁ + t₂) by ring]; exact hY _ hc1) _
    have p2 : (1 + |(T + t₁ - t₂) / 2|) ^ NΓ ≤ (A * X) ^ NΓ :=
      pow_le_pow_left₀ (by positivity) (by rw [show T + t₁ - t₂ = T + (t₁ - t₂) by ring]; exact hY _ hc2) _
    have p3 : (1 + |(T - t₁ + t₂) / 2|) ^ NΓ ≤ (A * X) ^ NΓ :=
      pow_le_pow_left₀ (by positivity) (by rw [show T - t₁ + t₂ = T + (-t₁ + t₂) by ring]; exact hY _ hc3) _
    have p4 : (1 + |(T - t₁ - t₂) / 2|) ^ NΓ ≤ (A * X) ^ NΓ :=
      pow_le_pow_left₀ (by positivity) (by rw [show T - t₁ - t₂ = T + (-t₁ - t₂) by ring]; exact hY _ hc4) _
    calc _ ≤ (CΓ * (1 + |(T + t₁ + t₂) / 2|) ^ NΓ * Real.exp (-(Real.pi * |(T + t₁ + t₂) / 2| / 2))) *
          (CΓ * (1 + |(T + t₁ - t₂) / 2|) ^ NΓ * Real.exp (-(Real.pi * |(T + t₁ - t₂) / 2| / 2))) *
          (CΓ * (1 + |(T - t₁ + t₂) / 2|) ^ NΓ * Real.exp (-(Real.pi * |(T - t₁ + t₂) / 2| / 2))) *
          (CΓ * (1 + |(T - t₁ - t₂) / 2|) ^ NΓ * Real.exp (-(Real.pi * |(T - t₁ - t₂) / 2| / 2))) := by
          gcongr <;> exact ha _
      _ ≤ (CΓ * (A * X) ^ NΓ * Real.exp (-(Real.pi * |(T + t₁ + t₂) / 2| / 2))) *
          (CΓ * (A * X) ^ NΓ * Real.exp (-(Real.pi * |(T + t₁ - t₂) / 2| / 2))) *
          (CΓ * (A * X) ^ NΓ * Real.exp (-(Real.pi * |(T - t₁ + t₂) / 2| / 2))) *
          (CΓ * (A * X) ^ NΓ * Real.exp (-(Real.pi * |(T - t₁ - t₂) / 2| / 2))) := by gcongr
      _ = CΓ ^ 4 * A ^ (4 * NΓ) * X ^ (4 * NΓ) *
          (Real.exp (-(Real.pi * |(T + t₁ + t₂) / 2| / 2)) * Real.exp (-(Real.pi * |(T + t₁ - t₂) / 2| / 2)) *
            Real.exp (-(Real.pi * |(T - t₁ + t₂) / 2| / 2)) * Real.exp (-(Real.pi * |(T - t₁ - t₂) / 2| / 2))) := by
          rw [mul_pow]; ring
      _ ≤ _ := by gcongr
  have hsn : ‖s‖ ≤ 2 * X := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hs]; simp only [X, T]; norm_num; linarith [abs_nonneg s.im]
  have hs1n : ‖s - 1‖ ≤ X := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [hs, X, T]; norm_num
  have h2s1n : ‖2 * s - 1‖ ≤ 2 * X := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [hs, X, T, abs_mul]; norm_num; linarith [abs_nonneg s.im]
  have hpi : ‖(Real.pi : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, neg_re, hs]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have h2pi : ‖(2 * Real.pi : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re, hs]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have h2 : ‖(2 : ℂ) ^ (s - 3)‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num), sub_re, hs]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hζ : ‖riemannZeta (2 * s)‖ ≤ 2 := by
    have := _root_.RHTower.norm_riemannZeta_le_of_le_re (σ₁ := 5 / 2) (by norm_num)
      (s := 2 * s) (by simp [hs]; norm_num)
    norm_num at this ⊢; linarith
  have hLs := hL s hs
  generalize Gamma (((5 / 8 : ℝ) : ℂ) + (((T + t₁ + t₂) / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + (((T + t₁ - t₂) / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + (((T - t₁ + t₂) / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + (((T - t₁ - t₂) / 2 : ℝ) : ℂ) * I) = Gp at hgam ⊢
  simp only [norm_mul]
  have hgam0 : 0 ≤ CΓ ^ 4 * A ^ (4 * NΓ) * X ^ (4 * NΓ) * Real.exp (-(Real.pi * |T|)) := by positivity
  calc _ ≤ 2 * X * (2 * X * (2 * X) * 1 * 2 * 1 *
        (CΓ ^ 4 * A ^ (4 * NΓ) * X ^ (4 * NΓ) * Real.exp (-(Real.pi * |T|)))) * (1 * L₀) := by
        gcongr
        · norm_num
    _ = 16 * L₀ * CΓ ^ 4 * A ^ (4 * NΓ) * X ^ (4 * NΓ + 3) * Real.exp (-(Real.pi * |T|)) := by ring

theorem exists_pairPolar_right (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    (hρ₁0 : ρ₁ 0 = 0) (hρ₁ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff u n y = ρ₁ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₁))
    (hρ₂0 : ρ₂ 0 = 0) (hρ₂ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff v n y = ρ₂ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam₂)) :
    ∃ D : ℝ, ∃ N : ℕ, 0 ≤ D ∧ ∀ s : ℂ, s.re = 5 / 4 → 1 ≤ |s.im| →
      ‖polarTransform (fun z => u z * starRingEnd ℂ (v z)) s‖ ≤
        D * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := _root_.RHTower.exists_bound_norm_Gamma_vertical_line (5 / 8) (by norm_num)
  obtain ⟨D, hD, h⟩ := pairPolar_right_bound hCΓ hΓ hu hv hρ₁0 hρ₁ hρ₂0 hρ₂
  exact ⟨D, _, hD, h⟩

/-- **The polar transform of a pair energy decays like `e^{−π|t|}` on the strip.** -/
theorem exists_pairPolar_decay (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖polarTransform (fun z => u z * starRingEnd ℂ (v z)) s‖ ≤
        C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) := by
  obtain ⟨ρ₁, hρ₁0, hρ₁⟩ := CuspL.exists_whittaker hu
  obtain ⟨ρ₂, hρ₂0, hρ₂⟩ := CuspL.exists_whittaker hv
  exact exists_polarTransform_decay ((isSeed_of_mem_cuspSpace hu).mul (isSeed_of_mem_cuspSpace hv).star)
    (exists_pairPolar_right hu hv hρ₁0 hρ₁ hρ₂0 hρ₂)

theorem isSeed_pair (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂) :
    IsSeed (fun z => u z * starRingEnd ℂ (v z)) :=
  (isSeed_of_mem_cuspSpace hu).mul (isSeed_of_mem_cuspSpace hv).star

/-! ### Two-mode energies -/

/-- The energy `|u + c v|²` of a two-mode state. -/
def twoModeEnergy (u v : ℍ → ℂ) (c : ℂ) (z : ℍ) : ℂ := ((‖u z + c * v z‖ ^ 2 : ℝ) : ℂ)

theorem twoModeEnergy_eq (u v : ℍ → ℂ) (c : ℂ) (z : ℍ) :
    twoModeEnergy u v c z = u z * starRingEnd ℂ (u z) + starRingEnd ℂ c * (u z * starRingEnd ℂ (v z)) +
      c * (v z * starRingEnd ℂ (u z)) + c * starRingEnd ℂ c * (v z * starRingEnd ℂ (v z)) := by
  rw [twoModeEnergy, Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [map_add, map_mul]
  ring

theorem isSeed_twoModeEnergy (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂) (c : ℂ) :
    IsSeed (twoModeEnergy u v c) :=
  ((isSeed_of_mem_cuspSpace hu).add ((isSeed_of_mem_cuspSpace hv).const_mul c)).normSq

theorem continuous_horocycle {G : ℍ → ℂ} (hG : Continuous G) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => G (UpperHalfPlane.ofComplex ⟨x, y⟩) := by
  have hmk : Continuous fun t : ℝ => (⟨t, y⟩ : ℂ) := by
    have : (fun t : ℝ => (⟨t, y⟩ : ℂ)) = fun t : ℝ => (t : ℂ) + (y : ℂ) * Complex.I := by
      funext t; apply Complex.ext <;> simp
    rw [this]; fun_prop
  exact (continuousOn_comp_ofComplex hG).comp_continuous hmk fun _ => hy

theorem integrableOn_horocycle {G : ℍ → ℂ} (hG : Continuous G) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun x : ℝ => G (UpperHalfPlane.ofComplex ⟨x, y⟩)) (Ico 0 1) :=
  ((continuous_horocycle hG hy).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self

/-- The response of a two-mode energy is the Hermitian combination of the four pair responses. -/
theorem response_twoModeEnergy (hu : Continuous u) (hv : Continuous v) (c : ℂ) {y : ℝ} (hy : 0 < y) :
    response (twoModeEnergy u v c) y =
      response (fun z => u z * starRingEnd ℂ (u z)) y + starRingEnd ℂ c * response (fun z => u z * starRingEnd ℂ (v z)) y +
        c * response (fun z => v z * starRingEnd ℂ (u z)) y +
        c * starRingEnd ℂ c * response (fun z => v z * starRingEnd ℂ (v z)) y := by
  have hc : ∀ g h : ℍ → ℂ, Continuous g → Continuous h → Continuous fun z => g z * starRingEnd ℂ (h z) :=
    fun g h hg hh => hg.mul (Complex.continuous_conj.comp hh)
  have i1 := integrableOn_horocycle (hc u u hu hu) hy
  have i2 := (integrableOn_horocycle (hc u v hu hv) hy).const_mul (starRingEnd ℂ c)
  have i3 := (integrableOn_horocycle (hc v u hv hu) hy).const_mul c
  have i4 := (integrableOn_horocycle (hc v v hv hv) hy).const_mul (c * starRingEnd ℂ c)
  unfold response
  simp_rw [twoModeEnergy_eq]
  rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  all_goals first | exact (i1.add i2).add i3 | exact i1.add i2 | exact i1 | exact i2 | exact i3 | exact i4

/-! ### Rates -/

/-- **Pair energies ring down at the zero-free rate.** -/
theorem pair_rate_of_zeroFree (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ a : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response (fun z => u z * starRingEnd ℂ (v z)) y - a‖ ≤ C * y ^ (1 - Θ / 2 - ε) :=
  ⟨_, response_rate_of_zeroFree (isSeed_pair hu hv) (exists_pairPolar_decay hu hv) hΘ hΘ1 hzf hε hε1⟩

/-- **Two-mode energies ring down at the zero-free rate.** If `ζ` has no zeros with `Re z > Θ`, `½ ≤ Θ ≤ 1`, the
energy of every two-mode state `u + cv` converges on closed horocycles at rate `y^{1 − Θ/2 − ε}`. -/
theorem twoMode_rate_of_zeroFree (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    (c : ℂ) {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ ≤ 1) (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ a : ℂ, ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response (twoModeEnergy u v c) y - a‖ ≤ C * y ^ (1 - Θ / 2 - ε) := by
  obtain ⟨a₁, C₁, -, h₁⟩ := pair_rate_of_zeroFree hu hu hΘ hΘ1 hzf hε hε1
  obtain ⟨a₂, C₂, -, h₂⟩ := pair_rate_of_zeroFree hu hv hΘ hΘ1 hzf hε hε1
  obtain ⟨a₃, C₃, -, h₃⟩ := pair_rate_of_zeroFree hv hu hΘ hΘ1 hzf hε hε1
  obtain ⟨a₄, C₄, -, h₄⟩ := pair_rate_of_zeroFree hv hv hΘ hΘ1 hzf hε hε1
  have hcu := HeckeCusp.continuous_of_maass hu.2.1
  have hcv := HeckeCusp.continuous_of_maass hv.2.1
  refine ⟨a₁ + starRingEnd ℂ c * a₂ + c * a₃ + c * starRingEnd ℂ c * a₄,
    C₁ + ‖c‖ * C₂ + ‖c‖ * C₃ + ‖c‖ * ‖c‖ * C₄, fun y hy hy1 => ?_⟩
  rw [response_twoModeEnergy hcu hcv c hy]
  set P := y ^ (1 - Θ / 2 - ε)
  have e : response (fun z => u z * starRingEnd ℂ (u z)) y + starRingEnd ℂ c * response (fun z => u z * starRingEnd ℂ (v z)) y +
        c * response (fun z => v z * starRingEnd ℂ (u z)) y +
        c * starRingEnd ℂ c * response (fun z => v z * starRingEnd ℂ (v z)) y -
      (a₁ + starRingEnd ℂ c * a₂ + c * a₃ + c * starRingEnd ℂ c * a₄) =
      (response (fun z => u z * starRingEnd ℂ (u z)) y - a₁) +
        starRingEnd ℂ c * (response (fun z => u z * starRingEnd ℂ (v z)) y - a₂) +
        c * (response (fun z => v z * starRingEnd ℂ (u z)) y - a₃) +
        c * starRingEnd ℂ c * (response (fun z => v z * starRingEnd ℂ (v z)) y - a₄) := by ring
  rw [e]
  refine norm_add₄_le.trans ?_
  simp only [norm_mul, Complex.norm_conj]
  have := h₁ y hy hy1; have := h₂ y hy hy1; have := h₃ y hy hy1; have := h₄ y hy hy1
  have hc0 := norm_nonneg c
  calc _ ≤ C₁ * P + ‖c‖ * (C₂ * P) + ‖c‖ * (C₃ * P) + ‖c‖ * ‖c‖ * (C₄ * P) := by gcongr
    _ = (C₁ + ‖c‖ * C₂ + ‖c‖ * C₃ + ‖c‖ * ‖c‖ * C₄) * P := by ring

/-! ### Seeing by a two-mode energy -/

theorem integrableOn_pairIntegrand (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    IntegrableOn (pairIntegrand s u v) ModularGroup.fd := by
  obtain ⟨K, -, hK⟩ := exists_pairing_bound Real.pi_pos h0 h1 h2
  obtain ⟨Mu, -, hMu⟩ := exists_envelope_of_mem_cuspSpace hu
  obtain ⟨Mv, -, hMv⟩ := exists_envelope_of_mem_cuspSpace hv
  exact (hK u v Mu Mv (HeckeCusp.continuous_of_maass hu.2.1) (HeckeCusp.continuous_of_maass hv.2.1) hMu hMv).1

/-- The completed transform of a two-mode energy is the Hermitian combination of the pair entries. -/
theorem seedTransform_twoModeEnergy (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) (c : ℂ) :
    seedTransform (twoModeEnergy u v c) s = pairing s u u + starRingEnd ℂ c * pairing s u v +
      c * pairing s v u + c * starRingEnd ℂ c * pairing s v v := by
  have i1 := integrableOn_pairIntegrand hu hu h0 h1 h2
  have i2 := (integrableOn_pairIntegrand hu hv h0 h1 h2).const_mul (starRingEnd ℂ c)
  have i3 := (integrableOn_pairIntegrand hv hu h0 h1 h2).const_mul c
  have i4 := (integrableOn_pairIntegrand hv hv h0 h1 h2).const_mul (c * starRingEnd ℂ c)
  have hpt : ∀ z : ℍ, twoModeEnergy u v c z * EisAuto.completedEisenstein (s - 1 / 2) z.re z.im =
      pairIntegrand s u u z + starRingEnd ℂ c * pairIntegrand s u v z + c * pairIntegrand s v u z +
        c * starRingEnd ℂ c * pairIntegrand s v v z := by
    intro z; simp only [pairIntegrand, twoModeEnergy_eq]; ring
  unfold seedTransform
  simp_rw [hpt]
  rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  · rfl
  all_goals first | exact (i1.add i2).add i3 | exact i1.add i2 | exact i1 | exact i2 | exact i3 | exact i4

/-- **Polarization.** If a pair entry `b_s(u, v)` does not vanish, some two-mode energy `|u + cv|²`,
`c ∈ {1, −1, i}`, sees `s`. -/
theorem exists_twoMode_seeing (hu : u ∈ HeckeCusp.cuspSpace lam₁) (hv : v ∈ HeckeCusp.cuspSpace lam₂)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) (hb : pairing s u v ≠ 0) :
    ∃ c : ℂ, seedTransform (twoModeEnergy u v c) s ≠ 0 := by
  by_contra hno
  push Not at hno
  have e1 := hno 1
  have e2 := hno (-1)
  have e3 := hno I
  rw [seedTransform_twoModeEnergy hu hv h0 h1 h2] at e1 e2 e3
  simp only [map_one, map_neg, Complex.conj_I] at e1 e2 e3
  have hBB : pairing s u v + pairing s v u = 0 := by linear_combination (e1 - e2) / 2
  have hI : I * (pairing s v u - pairing s u v) = 0 := by
    linear_combination e3 - (e1 + e2) / 2 + pairing s v v * Complex.I_mul_I
  have hd : pairing s v u - pairing s u v = 0 := (mul_eq_zero.1 hI).resolve_left Complex.I_ne_zero
  exact hb (by linear_combination (hBB - hd) / 2)

/-- **A seen zero caps the two-mode rate.** If every two-mode energy of the cuspidal eigenbasis rings down at
`y^α`, every zero `ρ` of `ζ` with `Re ρ > ½` has `Re ρ ≤ 2 − 2α`. -/
theorem re_le_of_twoMode_rate {α : ℝ}
    (h : ∀ (i l : CuspEigenIndex 0) (c : ℂ), ∃ (a : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖response (twoModeEnergy (maassForm i) (maassForm l) c) y - a‖ ≤ C * y ^ α)
    {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) : ρ.re ≤ 2 - 2 * α := by
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ρ.re := by linarith
  have hre1 : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hs0 : ρ / 2 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : ρ / 2 ≠ 1 / 2 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs2 : ρ / 2 ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  obtain ⟨i, l, hil⟩ := exists_maass_pair_seeing hζ hpos
  obtain ⟨c, hc⟩ := exists_twoMode_seeing (maassForm_mem l) (maassForm_mem i) hs0 hs1 hs2 hil
  obtain ⟨a, C, hrate⟩ := h l i c
  exact not_rate_of_seen (isSeed_twoModeEnergy (maassForm_mem l) (maassForm_mem i) c) hζ hpos hc
    (by linarith) a C hrate

/-- **Zagier's theorem for the cavity.** The Riemann hypothesis holds iff the energy of every two-mode state
`v_i + c v_l` of the cuspidal eigenbasis converges on closed horocycles at rate `y^{3/4 − ε}` for every `ε > 0`. -/
theorem riemannHypothesis_iff_twoMode_rate :
    RiemannHypothesis ↔ ∀ (i l : CuspEigenIndex 0) (c : ℂ) (ε : ℝ), 0 < ε →
      ∃ (a : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖response (twoModeEnergy (maassForm i) (maassForm l) c) y - a‖ ≤ C * y ^ (3 / 4 - ε) := by
  constructor
  · intro hRH i l c ε hε
    have hzf : ∀ z : ℂ, 1 / 2 < z.re → riemannZeta z ≠ 0 :=
      riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.1 hRH
    set ε' := min ε (1 / 4)
    have hε' : 0 < ε' := lt_min hε (by norm_num)
    obtain ⟨a, C, h⟩ := twoMode_rate_of_zeroFree (maassForm_mem i) (maassForm_mem l) c le_rfl (by norm_num)
      hzf hε' (by linarith [min_le_right ε (1 / 4)])
    refine ⟨a, max C 0, fun y hy hy1 => ?_⟩
    have hmono : y ^ (1 - 1 / 2 / 2 - ε') ≤ y ^ (3 / 4 - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith [min_le_left ε (1 / 4)])
    calc _ ≤ C * y ^ (1 - 1 / 2 / 2 - ε') := h y hy hy1
      _ ≤ max C 0 * y ^ (1 - 1 / 2 / 2 - ε') :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)
      _ ≤ max C 0 * y ^ (3 / 4 - ε) := mul_le_mul_of_nonneg_left hmono (le_max_right _ _)
  · intro h
    refine riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.2 fun s hs hζ => ?_
    have hre := re_le_of_twoMode_rate (α := 3 / 4 - (s.re - 1 / 2) / 4)
      (fun i l c => h i l c _ (by linarith)) hζ hs
    linarith

/-- **M4 for the cavity: a zero-free strip is a universal ringdown rate.** `ζ` has a zero-free strip
`Re z > 1 − δ` iff all two-mode energies of the cuspidal eigenbasis ring down at a common rate `y^α` with
`α > ½`. -/
theorem zeroFreeStrip_iff_twoMode_rate :
    (∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, 1 - δ < z.re → riemannZeta z ≠ 0) ↔
      ∃ α : ℝ, 1 / 2 < α ∧ ∀ (i l : CuspEigenIndex 0) (c : ℂ), ∃ (a : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖response (twoModeEnergy (maassForm i) (maassForm l) c) y - a‖ ≤ C * y ^ α := by
  constructor
  · rintro ⟨δ, hδ, hzf⟩
    set Θ := max (1 - δ) (1 / 2)
    have hΘ : 1 / 2 ≤ Θ := le_max_right _ _
    have hΘ1 : Θ < 1 := max_lt (by linarith) (by norm_num)
    have hzfΘ : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz => hzf z (lt_of_le_of_lt (le_max_left _ _) hz)
    refine ⟨1 - Θ / 2 - (1 - Θ) / 4, by linarith, fun i l c => ?_⟩
    exact twoMode_rate_of_zeroFree (maassForm_mem i) (maassForm_mem l) c hΘ hΘ1.le hzfΘ (by linarith)
      (by linarith)
  · rintro ⟨α, hα, h⟩
    refine ⟨min (2 * α - 1) (1 / 2), lt_min (by linarith) (by norm_num), fun z hz hζ => ?_⟩
    have h1 : 1 / 2 < z.re := by linarith [min_le_right (2 * α - 1) (1 / 2)]
    have h2 := re_le_of_twoMode_rate h hζ h1
    linarith [min_le_left (2 * α - 1) (1 / 2)]

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
