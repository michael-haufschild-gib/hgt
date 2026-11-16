import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwoAdicCubicTwistHasTheDoublePoleOfTheThetaSquare

/-!
# The cubic twist at two of the theta square has a double pole

`T` are the Fourier coefficients of the projected cubic theta function, `G̃(−2)` the normalized cubic Gauss sum at the
primary prime `−2` (`|G̃(−2)| = 1`), and `χ(h) = (h/−2)₃` the cubic residue symbol modulo the inert prime `2`
(`cubicTwistCoeff_eq_symbol`).

1. **Patterson's relations at `2` turn the shifted square into the cubic twist.** Write `h = (−2)^k h'` with `h'` odd.
   By `T(h'(−2)) = χ(h')\overline{G̃(−2)}T(h')`, `T(h'(−2)^{3j}) = 2^jT(h')` and `T(h'(−2)^{3j+2}) = 0`, the product
   `T(h)T(−4h)` vanishes unless `k = 3j + 1`, where it is `2·4^j\overline{G̃(−2)}χ(h')T(h')²`. Summing over `j`:
   `D₄(s) = 2·2^{−s}\overline{G̃(−2)}(1 − 4·2^{−3s})^{−1} L_χ(s)` (`besselDirichlet_fourShiftCoeff`).
2. **The cubic twist at two has a double pole** (`cubicTwistAtTwo_double_pole`). With the Hecke-at-four identity,
   `c(s) M(s) L_χ(s)` has the double pole of the theta square, where
   `c(s) = 2^{−s}·2·2^{−s}\overline{G̃(−2)}(1 − 4·2^{−3s})^{−1} + 2^{s−2}` does not vanish on `Re s > 5/4` and
   `c(4/3) = 2^{−2/3}(1 + ⅔\overline{G̃(−2)})`. Hence `M(s)L_χ(s)` continues to `{5/4 < Re s < 13/3, Im s > 0}` and to a
   punctured neighbourhood of `4/3`, and `(s − 4/3)² M(s) L_χ(s) → 108π³r³ / c(4/3) ≠ 0`.

The 2-ramified cubic twist of the theta square keeps the double pole; its leading coefficient is the untwisted one
divided by the 2-adic factor `c(4/3)`.
-/

noncomputable section

open Filter Function
open scoped BigOperators Classical ComplexConjugate Topology

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource MetaplecticMobiusDescent.CubicJacobi

/-! ### Patterson's relations at the inert prime `2` -/

theorem negTwo_prime : Prime (-2 : O) := CanonicalRowCompletion.negative_two_prime

theorem norm_ringComplex_neg_two : ‖ringComplex (-2 : O)‖ = 2 := by
  simp [map_neg, map_ofNat]

/-- `T(x(−2)^{3j}) = 2^j T(x)`. -/
theorem coeff_mul_neg_two_cube_pow (x : O) (hx : x ≠ 0) (j : ℕ) :
    rationalSourceResidualFourierCoefficient (x * (-2) ^ (3 * j)) =
      2 ^ j * rationalSourceResidualFourierCoefficient x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hne : x * (-2 : O) ^ (3 * j) ≠ 0 := mul_ne_zero hx (pow_ne_zero _ negTwo_prime.ne_zero)
    rw [show x * (-2 : O) ^ (3 * (j + 1)) = (x * (-2) ^ (3 * j)) * (-2) ^ 3 by ring,
      rationalSourceResidualFourierCoefficient_primary_cube (-2) negTwo_prime.ne_zero primary_neg_two _ hne, ih,
      norm_ringComplex_neg_two]
    push_cast
    ring

/-- `T(x(−2)^k) = 0` for odd `x` and `k ≡ 2 mod 3`. -/
theorem coeff_mul_neg_two_pow_vanish (x : O) (hx : ¬ (-2 : O) ∣ x) (k : ℕ) (hk : k % 3 = 2) :
    rationalSourceResidualFourierCoefficient (x * (-2) ^ k) = 0 :=
  rationalSourceResidualFourierCoefficient_prime_power_vanish (-2) negTwo_prime primary_neg_two x hx k hk

theorem symbol_nine_mul_neg_two (x : O) : symbol (9 * x) (-2) = symbol x (-2) :=
  symbol_congr ⟨-4 * x, by ring⟩

theorem exists_uF_eq : ∀ p : F4, p ≠ 0 → ∃ k : Fin 3, uF k = p := by decide

theorem F4_add_self : ∀ p : F4, p + p = 0 := by decide

theorem cubeRootF_uF (k : Fin 3) : cubeRootF (uF k) = ringComplex (uO k) := by
  fin_cases k
  · rw [cubeRootF, if_pos (by decide)]
    simp [uO]
  · rw [cubeRootF, if_neg (by decide), if_pos (by decide)]
    simp [uO]
  · rw [cubeRootF, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    simp [uO]

/-- For odd `x`, `(x/−2)₃` is the cube root of unity congruent to `x` modulo `2`. -/
theorem symbol_neg_two_eq_cubeRootF (x : O) (hx : ¬ (-2 : O) ∣ x) :
    ringComplex (symbol x (-2)) = cubeRootF (red x) := by
  have hred : red x ≠ 0 := fun h0 => hx (neg_dvd.mpr ((two_dvd_iff x).mpr h0))
  obtain ⟨k, hk⟩ := exists_uF_eq (red x) hred
  have hdvd : (-2 : O) ∣ x - uO k := by
    rw [neg_dvd, two_dvd_iff, red_sub, red_uO, hk, F4_add_self]
  rw [symbol_congr hdvd, symbol_uO_neg_two, ← hk, cubeRootF_uF]

/-- `T(x(−2)) = χ(x)\overline{G̃(−2)}T(x)` for odd `x`. -/
theorem coeff_mul_neg_two (x : O) (hx : ¬ (-2 : O) ∣ x) :
    rationalSourceResidualFourierCoefficient (x * (-2)) =
      cubeRootF (red x) * star (normalizedCubicUnitGauss (-2)) * rationalSourceResidualFourierCoefficient x := by
  rw [rationalSourceResidualFourierCoefficient_prime_normalized (-2) negTwo_prime primary_neg_two x hx,
    symbol_nine_mul_neg_two, symbol_neg_two_eq_cubeRootF x hx]

/-- The 2-adic cubic twist is the twist by the cubic residue symbol modulo `−2`: `χ(h) = (h/−2)₃`. -/
theorem cubicTwistCoeff_eq_symbol (h : O) :
    cubicTwistCoeff h = ringComplex (symbol h (-2)) * rationalSourceResidualFourierCoefficient h ^ 2 := by
  by_cases hd : (-2 : O) ∣ h
  · have h0 : red h = 0 := (two_dvd_iff h).mp (neg_dvd.mp hd)
    haveI hmax : (Ideal.span {(-2 : O)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible negTwo_prime.irreducible
    have hgood : lambda ∉ Ideal.span {(-2 : O)} :=
      primary_maximal_divisor_good (-2) primary_neg_two _ (Ideal.subset_span rfl)
    have hs : symbol h (-2) = 0 := by
      rw [symbol_congr (show (-2 : O) ∣ h - 0 by simpa using hd),
        symbol_prime (-2) negTwo_prime primary_neg_two, primeValue_eq _ hgood, map_zero]
    rw [cubicTwistCoeff, h0, cubeRootF_zero, hs, map_zero]
  · rw [cubicTwistCoeff, symbol_neg_two_eq_cubeRootF h hd]

/-! ### The decomposition `h = (−2)^k h'` -/

theorem exists_neg_two_pow_mul (h : O) (hh : h ≠ 0) :
    ∃ k : ℕ, ∃ x : O, ¬ (-2 : O) ∣ x ∧ h = (-2) ^ k * x :=
  WfDvdMonoid.max_power_factor hh negTwo_prime.irreducible

theorem neg_two_pow_mul_inj {k l : ℕ} {a b : O} (ha : ¬ (-2 : O) ∣ a) (hb : ¬ (-2 : O) ∣ b)
    (he : (-2 : O) ^ k * a = (-2) ^ l * b) : k = l ∧ a = b := by
  have h2 : (-2 : O) ≠ 0 := negTwo_prime.ne_zero
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    have hab : a = (-2) ^ (d + 1) * b := by
      apply mul_left_cancel₀ (pow_ne_zero k h2)
      rw [he]
      ring
    rw [hab] at ha
    exact ha (dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero d)) b)
  · exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k h2) he⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    have hba : b = (-2) ^ (d + 1) * a := by
      apply mul_left_cancel₀ (pow_ne_zero l h2)
      rw [← he]
      ring
    rw [hba] at hb
    exact hb (dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero d)) a)

/-- Elements prime to `2`. -/
abbrev OddO := ↥{x : O | ¬ (-2 : O) ∣ x}

theorem OddO.ne_zero (x : OddO) : x.val ≠ 0 := fun h0 => x.2 (by rw [h0]; exact dvd_zero _)

/-- `(j, h') ↦ (−2)^{3j+1} h'`: the frequencies on which the shifted square lives. -/
def twoAdicIndex (p : ℕ × OddO) : O := (-2) ^ (3 * p.1 + 1) * p.2.val

theorem twoAdicIndex_injective : Function.Injective twoAdicIndex := by
  rintro ⟨j, a⟩ ⟨j', b⟩ he
  obtain ⟨hk, hab⟩ := neg_two_pow_mul_inj a.2 b.2 he
  simp only [Prod.mk.injEq]
  exact ⟨by omega, Subtype.ext hab⟩

/-- `T(h)T(−4h) = 0` unless `v₂(h) ≡ 1 mod 3`. -/
theorem fourShiftCoeff_eq_zero (k : ℕ) (x : O) (hx : ¬ (-2 : O) ∣ x) (hk : k % 3 ≠ 1) :
    fourShiftCoeff ((-2) ^ k * x) = 0 := by
  rw [fourShiftCoeff]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
  · rw [rationalSourceResidualFourierCoefficient_neg,
      show 4 * ((-2 : O) ^ k * x) = x * (-2) ^ (k + 2) by ring,
      coeff_mul_neg_two_pow_vanish x hx _ (by omega), mul_zero]
  · rw [mul_comm ((-2 : O) ^ k) x, coeff_mul_neg_two_pow_vanish x hx k h2, zero_mul]

/-- `T(h)T(−4h) = 2·4^j\overline{G̃(−2)}χ(h')T(h')²` at `h = (−2)^{3j+1}h'`. -/
theorem fourShiftCoeff_twoAdicIndex (j : ℕ) (x : O) (hx : ¬ (-2 : O) ∣ x) :
    fourShiftCoeff ((-2) ^ (3 * j + 1) * x) =
      2 * star (normalizedCubicUnitGauss (-2)) * (4 : ℂ) ^ j * cubicTwistCoeff x := by
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact dvd_zero _)
  have h1 : rationalSourceResidualFourierCoefficient ((-2) ^ (3 * j + 1) * x) =
      2 ^ j * (cubeRootF (red x) * star (normalizedCubicUnitGauss (-2)) *
        rationalSourceResidualFourierCoefficient x) := by
    rw [show (-2 : O) ^ (3 * j + 1) * x = (x * (-2)) * (-2) ^ (3 * j) by ring,
      coeff_mul_neg_two_cube_pow _ (mul_ne_zero hx0 negTwo_prime.ne_zero), coeff_mul_neg_two x hx]
  have h2 : rationalSourceResidualFourierCoefficient (-(4 * ((-2) ^ (3 * j + 1) * x))) =
      2 ^ (j + 1) * rationalSourceResidualFourierCoefficient x := by
    rw [rationalSourceResidualFourierCoefficient_neg,
      show 4 * ((-2 : O) ^ (3 * j + 1) * x) = x * (-2) ^ (3 * (j + 1)) by ring,
      coeff_mul_neg_two_cube_pow x hx0]
  have h4 : (4 : ℂ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  rw [fourShiftCoeff, h1, h2, cubicTwistCoeff, h4]
  ring

/-! ### Weights -/

theorem ofReal_two_pow_cpow (n : ℕ) (s : ℂ) : ((((2 : ℝ) ^ n : ℝ)) : ℂ) ^ (-s) = ((2 : ℂ) ^ (-s)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by norm_num), ih, pow_succ]
    norm_num

theorem weight_twoAdicIndex (s : ℂ) (j : ℕ) (x : O) :
    ((4 * Real.pi * ‖cuspFrequency ((-2) ^ (3 * j + 1) * x)‖ : ℝ) : ℂ) ^ (-s) =
      (2 : ℂ) ^ (-s) * ((2 : ℂ) ^ (-s)) ^ (3 * j) * ((4 * Real.pi * ‖cuspFrequency x‖ : ℝ) : ℂ) ^ (-s) := by
  have hn : ‖cuspFrequency ((-2) ^ (3 * j + 1) * x)‖ = ‖cuspFrequency x‖ * (2 : ℝ) ^ (3 * j + 1) := by
    rw [mul_comm, cuspFrequency_mul_right, norm_mul, map_pow, norm_pow, norm_ringComplex_neg_two]
  rw [hn, show 4 * Real.pi * (‖cuspFrequency x‖ * (2 : ℝ) ^ (3 * j + 1)) =
      (4 * Real.pi * ‖cuspFrequency x‖) * (2 : ℝ) ^ (3 * j + 1) by ring, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_two_pow_cpow, pow_succ]
  ring

theorem norm_two_cpow_neg (s : ℂ) : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.neg_re]

theorem norm_four_complex : ‖(4 : ℂ)‖ = 4 := by norm_num

/-- `‖4·2^{−3s}‖ = 4·2^{−3Re s}` -/
theorem norm_four_mul_cube (s : ℂ) : ‖4 * ((2 : ℂ) ^ (-s)) ^ 3‖ = 4 * (2 : ℝ) ^ (-s.re * 3) := by
  rw [norm_mul, norm_pow, norm_two_cpow_neg, norm_four_complex, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  norm_num

theorem norm_four_mul_cube_lt (s : ℂ) (hs : 2 / 3 < s.re) : ‖4 * ((2 : ℂ) ^ (-s)) ^ 3‖ < 1 := by
  rw [norm_four_mul_cube]
  have h : (2 : ℝ) ^ (-s.re * 3) < 2 ^ (-2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h4 : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h4] at h
  linarith

theorem one_sub_four_mul_cube_ne_zero (s : ℂ) (hs : 2 / 3 < s.re) : 1 - 4 * ((2 : ℂ) ^ (-s)) ^ 3 ≠ 0 := by
  intro h0
  have h := norm_four_mul_cube_lt s hs
  rw [show 4 * ((2 : ℂ) ^ (-s)) ^ 3 = 1 by linear_combination -h0, norm_one] at h
  exact lt_irrefl _ h

/-! ### The shifted square is the cubic twist -/

/-- **Patterson at two.** For `Re s > 4`:
`D₄(s) = 2·2^{−s}\overline{G̃(−2)}(1 − 4·2^{−3s})^{−1} L_χ(s)`. -/
theorem besselDirichlet_fourShiftCoeff (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet fourShiftCoeff s =
      2 * (2 : ℂ) ^ (-s) * star (normalizedCubicUnitGauss (-2)) * (1 - 4 * ((2 : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet cubicTwistCoeff s := by
  set G : ℂ := star (normalizedCubicUnitGauss (-2)) with hG
  let w : O → ℂ := fun h => ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let F : O → ℂ := fun h => if h = 0 then 0 else fourShiftCoeff h * w h
  let g : OddO → ℂ := fun x => cubicTwistCoeff x.val * w x.val
  have hq := norm_four_mul_cube_lt s (by linarith)
  have hsupp : Function.support F ⊆ Set.range twoAdicIndex := by
    intro h hF
    have hh : h ≠ 0 := fun h0 => hF (by simp [F, h0])
    obtain ⟨k, x, hx, rfl⟩ := exists_neg_two_pow_mul h hh
    by_cases hk : k % 3 = 1
    · refine ⟨(k / 3, ⟨x, hx⟩), ?_⟩
      simp only [twoAdicIndex]
      congr 2
      omega
    · exfalso
      apply hF
      simp [F, hh, fourShiftCoeff_eq_zero k x hx hk]
  have hterm : ∀ p : ℕ × OddO, F (twoAdicIndex p) =
      (2 * (2 : ℂ) ^ (-s) * G) * ((4 * ((2 : ℂ) ^ (-s)) ^ 3) ^ p.1 * g p.2) := by
    rintro ⟨j, x, hx⟩
    have hne : (-2 : O) ^ (3 * j + 1) * x ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ negTwo_prime.ne_zero) (fun h0 => hx (by rw [h0]; exact dvd_zero _))
    simp only [F, g, w, twoAdicIndex]
    rw [if_neg hne, fourShiftCoeff_twoAdicIndex j x hx, weight_twoAdicIndex, mul_pow, pow_mul]
    ring
  have hgsum : Summable (fun x : OddO => ‖g x‖) := by
    refine (((summable_cubicTwistCoeff hs).subtype {x : O | ¬ (-2 : O) ∣ x}).mul_left
      ((4 * Real.pi) ^ (-s.re))).congr fun x => ?_
    have hx0 := OddO.ne_zero x
    have hξ : 0 < ‖cuspFrequency x.val‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero _ hx0)
    simp only [Function.comp, if_neg hx0, g, w, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
      Real.mul_rpow (by positivity) hξ.le]
    ring
  have hqsum : Summable (fun j : ℕ => ‖(4 * ((2 : ℂ) ^ (-s)) ^ 3) ^ j‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hq
  have hLchi : ∑' x : OddO, g x = besselDirichlet cubicTwistCoeff s := by
    have hsub : Function.support (fun h : O => if h = 0 then 0 else
        cubicTwistCoeff h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) ⊆
          {x : O | ¬ (-2 : O) ∣ x} := by
      intro h hG hd
      apply hG
      have h0 : red h = 0 := (two_dvd_iff h).mp (neg_dvd.mp hd)
      simp [cubicTwistCoeff, h0, cubeRootF_zero]
    rw [besselDirichlet, ← tsum_subtype_eq_of_support_subset hsub]
    refine tsum_congr fun x => ?_
    simp only [g, w, if_neg (OddO.ne_zero x)]
  calc besselDirichlet fourShiftCoeff s = ∑' h, F h := rfl
    _ = ∑' p : ℕ × OddO, F (twoAdicIndex p) := (twoAdicIndex_injective.tsum_eq hsupp).symm
    _ = ∑' p : ℕ × OddO, (2 * (2 : ℂ) ^ (-s) * G) * ((4 * ((2 : ℂ) ^ (-s)) ^ 3) ^ p.1 * g p.2) :=
        tsum_congr hterm
    _ = (2 * (2 : ℂ) ^ (-s) * G) * ((∑' j : ℕ, (4 * ((2 : ℂ) ^ (-s)) ^ 3) ^ j) * ∑' x : OddO, g x) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hqsum hgsum]
    _ = _ := by
        rw [tsum_geometric_of_norm_lt_one hq, hLchi]
        ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
