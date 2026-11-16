import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtAPrimaryPrimeCarriesTheDoublePole

/-!
# The dilate correlation at every primary prime has a double pole

Patterson's relations at a primary prime `p` (`ρ = |p|`): for `p ∤ x`, `T(xp^{3j}) = ρ^jT(x)` and `T(xp^{3j+2}) = 0`.
Writing `h = p^kx` with `p ∤ x`, the shifted square `T(h)T(−p²h)` vanishes unless `k = 3j + 1`, where it is
`ρ^{2j+1}T(x)T(xp)`; summing over `j` (`besselDirichlet_shiftSqCoeff`):

`D_{p²}(s) = ρ·ρ^{−s}(1 − ρ²ρ^{−3s})^{−1} D_{dil}(s)`.

So the combination of `dilateCombination_double_pole` is `c_p(s)D_{dil}(s)` with
`c_p(s) = 2ρ^{1−2s}(1 − ρ^{2−3s})^{−1} + ρ^{s−1}`, and `c_p(s)·ρ^{1−s}(1 − ρ^{2−3s}) = 1 + ρ^{2−3s}` does not vanish on
`Re s > 2/3`. At `s = 4/3`, `c_p(4/3) = ρ^{1/3}(ρ² + 1)/(ρ² − 1)`, `ρ² = N(p)`. Hence (`dilateCorrelation_double_pole`)

`(s − 4/3)² M(s) D_{dil}(s) → 216π³r³ / c_p(4/3) = 108π³r³ · N(p)^{−1/6} · 2(N(p) − 1)/(N(p) + 1)`,

and, since `T(k)T(kp) = (9/p)₃\overline{G̃(p)}(k/p)₃T(k)²`, the cubic twist `L_{χ_p}(s) = Σ_k (k/p)₃T(k)²(4π|ξ_k|)^{−s}` has
the double pole with leading coefficient `((9/p)₃\overline{G̃(p)})^{−1}·216π³r³/c_p(4/3) ≠ 0` (`cubicTwistAtPrime_double_pole`):
**every cubic twist of the theta square keeps the double pole.**
-/

noncomputable section

open Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Patterson's relations at `p` -/

/-- `T(xp^{3j}) = ρ^jT(x)`. -/
theorem coeff_mul_cube_pow (x : O) (hx : x ≠ 0) (j : ℕ) :
    rationalSourceResidualFourierCoefficient (x * P.p ^ (3 * j)) =
      (‖ringComplex P.p‖ : ℂ) ^ j * rationalSourceResidualFourierCoefficient x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hne : x * P.p ^ (3 * j) ≠ 0 := mul_ne_zero hx (pow_ne_zero _ P.ne_zero)
    rw [show x * P.p ^ (3 * (j + 1)) = (x * P.p ^ (3 * j)) * P.p ^ 3 by ring,
      rationalSourceResidualFourierCoefficient_primary_cube P.p P.ne_zero P.primary _ hne, ih]
    ring

theorem shiftSqCoeff_eq_zero (k : ℕ) (x : O) (hx : ¬ P.p ∣ x) (hk : k % 3 ≠ 1) :
    P.shiftSqCoeff (P.p ^ k * x) = 0 := by
  rw [shiftSqCoeff]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
  · rw [show -(P.p ^ k * x * P.p) * P.p = -(x * P.p ^ (k + 2)) by ring, rationalSourceResidualFourierCoefficient_neg,
      rationalSourceResidualFourierCoefficient_prime_power_vanish P.p P.prime P.primary x hx _ (by omega), mul_zero]
  · rw [mul_comm (P.p ^ k) x,
      rationalSourceResidualFourierCoefficient_prime_power_vanish P.p P.prime P.primary x hx k h2, zero_mul]

theorem shiftSqCoeff_index (j : ℕ) (x : O) (hx : ¬ P.p ∣ x) :
    P.shiftSqCoeff (P.p ^ (3 * j + 1) * x) =
      (‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℂ) ^ 2) ^ j * P.dilateCoeff x := by
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact dvd_zero _)
  have h1 : rationalSourceResidualFourierCoefficient (P.p ^ (3 * j + 1) * x) =
      (‖ringComplex P.p‖ : ℂ) ^ j * rationalSourceResidualFourierCoefficient (x * P.p) := by
    rw [show P.p ^ (3 * j + 1) * x = (x * P.p) * P.p ^ (3 * j) by ring,
      P.coeff_mul_cube_pow _ (mul_ne_zero hx0 P.ne_zero)]
  have h2 : rationalSourceResidualFourierCoefficient (-(P.p ^ (3 * j + 1) * x * P.p) * P.p) =
      (‖ringComplex P.p‖ : ℂ) ^ (j + 1) * rationalSourceResidualFourierCoefficient x := by
    rw [show -(P.p ^ (3 * j + 1) * x * P.p) * P.p = -(x * P.p ^ (3 * (j + 1))) by ring,
      rationalSourceResidualFourierCoefficient_neg, P.coeff_mul_cube_pow x hx0]
  rw [shiftSqCoeff, h1, h2, dilateCoeff, if_neg hx]
  ring

/-! ### The decomposition `h = p^kx` -/

theorem pow_mul_inj {k l : ℕ} {a b : O} (ha : ¬ P.p ∣ a) (hb : ¬ P.p ∣ b)
    (he : P.p ^ k * a = P.p ^ l * b) : k = l ∧ a = b := by
  have h2 := P.ne_zero
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    have hab : a = P.p ^ (d + 1) * b := by
      apply mul_left_cancel₀ (pow_ne_zero k h2)
      rw [he]
      ring
    rw [hab] at ha
    exact ha (dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero d)) b)
  · exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero k h2) he⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    have hba : b = P.p ^ (d + 1) * a := by
      apply mul_left_cancel₀ (pow_ne_zero l h2)
      rw [← he]
      ring
    rw [hba] at hb
    exact hb (dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero d)) a)

/-- Elements prime to `p`. -/
abbrev Coprime := ↥{x : O | ¬ P.p ∣ x}

theorem Coprime.ne_zero {P : PrimaryPrime} (x : P.Coprime) : x.val ≠ 0 :=
  fun h0 => x.2 (by rw [h0]; exact dvd_zero _)

/-- `(j, x) ↦ p^{3j+1}x`. -/
def tripleIndex (q : ℕ × P.Coprime) : O := P.p ^ (3 * q.1 + 1) * q.2.val

theorem tripleIndex_injective : Function.Injective P.tripleIndex := by
  rintro ⟨j, a⟩ ⟨j', b⟩ he
  obtain ⟨hk, hab⟩ := P.pow_mul_inj a.2 b.2 he
  simp only [Prod.mk.injEq]
  exact ⟨by omega, Subtype.ext hab⟩

theorem ofReal_pow_cpow (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (s : ℂ) :
    (((ρ ^ n : ℝ)) : ℂ) ^ (-s) = ((ρ : ℂ) ^ (-s)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hρ, ih, pow_succ]

theorem weight_tripleIndex (s : ℂ) (j : ℕ) (x : O) :
    ((4 * Real.pi * ‖cuspFrequency (P.p ^ (3 * j + 1) * x)‖ : ℝ) : ℂ) ^ (-s) =
      ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ (3 * j) *
        ((4 * Real.pi * ‖cuspFrequency x‖ : ℝ) : ℂ) ^ (-s) := by
  have hn : ‖cuspFrequency (P.p ^ (3 * j + 1) * x)‖ = ‖cuspFrequency x‖ * ‖ringComplex P.p‖ ^ (3 * j + 1) := by
    rw [mul_comm, cuspFrequency_mul_right, norm_mul, map_pow, norm_pow]
  rw [hn, show 4 * Real.pi * (‖cuspFrequency x‖ * ‖ringComplex P.p‖ ^ (3 * j + 1)) =
      (4 * Real.pi * ‖cuspFrequency x‖) * ‖ringComplex P.p‖ ^ (3 * j + 1) by ring, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_pow_cpow _ (norm_nonneg _), pow_succ]
  ring

theorem norm_rho_cube_lt (s : ℂ) (hs : 2 / 3 < s.re) :
    ‖((‖ringComplex P.p‖ : ℂ) ^ 2) * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3‖ < 1 := by
  have hn := P.norm_pos
  have hρ2 : 1 < ‖ringComplex P.p‖ ^ 2 := by
    have h := ringComplex_norm_sq_eq_absNorm_span P.p
    have hne : Ideal.absNorm (Ideal.span {P.p}) ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]
      exact P.prime.not_unit
    have h1 : 1 ≤ ‖ringComplex P.p‖ ^ 2 := one_le_norm_sq_ringComplex P.ne_zero
    have h2 : (Ideal.absNorm (Ideal.span {P.p}) : ℝ) ≠ 1 := by exact_mod_cast hne
    rw [← h] at h2
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  set ρ := ‖ringComplex P.p‖
  have hρ1 : 1 < ρ := by nlinarith
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hn, Complex.neg_re, Complex.norm_real,
    Real.norm_of_nonneg hn.le, ← Real.rpow_natCast (ρ ^ (-s.re)), ← Real.rpow_mul hn.le, ← Real.rpow_natCast ρ 2,
    ← Real.rpow_add hn]
  apply Real.rpow_lt_one_of_one_lt_of_neg hρ1
  push_cast
  linarith

/-- **Patterson at `p`.** For `Re s > 4`: `D_{p²}(s) = ρ·ρ^{−s}(1 − ρ²ρ^{−3s})^{−1} D_{dil}(s)`. -/
theorem besselDirichlet_shiftSqCoeff (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet P.shiftSqCoeff s =
      (‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) *
        (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
          besselDirichlet P.dilateCoeff s := by
  set t : ℂ := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) with htdef
  set ρc : ℂ := (‖ringComplex P.p‖ : ℂ) with hρc
  let w : O → ℂ := fun h => ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let F : O → ℂ := fun h => if h = 0 then 0 else P.shiftSqCoeff h * w h
  let g : P.Coprime → ℂ := fun x => P.dilateCoeff x.val * w x.val
  have hq := P.norm_rho_cube_lt s (by linarith)
  have hsupp : Function.support F ⊆ Set.range P.tripleIndex := by
    intro h hF
    have hh : h ≠ 0 := fun h0 => hF (by simp [F, h0])
    obtain ⟨k, x, hx, rfl⟩ := WfDvdMonoid.max_power_factor hh P.prime.irreducible
    by_cases hk : k % 3 = 1
    · refine ⟨(k / 3, ⟨x, hx⟩), ?_⟩
      simp only [tripleIndex]
      congr 2
      omega
    · exfalso
      apply hF
      simp [F, hh, P.shiftSqCoeff_eq_zero k x hx hk]
  have hterm : ∀ q : ℕ × P.Coprime, F (P.tripleIndex q) = (ρc * t) * ((ρc ^ 2 * t ^ 3) ^ q.1 * g q.2) := by
    rintro ⟨j, x, hx⟩
    have hne : P.p ^ (3 * j + 1) * x ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.ne_zero) (fun h0 => hx (by rw [h0]; exact dvd_zero _))
    simp only [F, g, w, tripleIndex]
    rw [if_neg hne, P.shiftSqCoeff_index j x hx, P.weight_tripleIndex, mul_pow, pow_mul]
    ring
  have hgsum : Summable (fun x : P.Coprime => ‖g x‖) := by
    refine (((P.summable_dilateCoeff hs).subtype {x : O | ¬ P.p ∣ x}).mul_left
      ((4 * Real.pi) ^ (-s.re))).congr fun x => ?_
    have hx0 := Coprime.ne_zero x
    have hξ : 0 < ‖cuspFrequency x.val‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero _ hx0)
    simp only [Function.comp, if_neg hx0, g, w, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
      Real.mul_rpow (by positivity) hξ.le]
    ring
  have hqsum : Summable (fun j : ℕ => ‖(ρc ^ 2 * t ^ 3) ^ j‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hq
  have hD : ∑' x : P.Coprime, g x = besselDirichlet P.dilateCoeff s := by
    have hsub : Function.support (fun h : O => if h = 0 then 0 else
        P.dilateCoeff h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) ⊆ {x : O | ¬ P.p ∣ x} := by
      intro h hG hd
      apply hG
      simp [dilateCoeff, hd]
    rw [besselDirichlet, ← tsum_subtype_eq_of_support_subset hsub]
    refine tsum_congr fun x => ?_
    simp only [g, w, if_neg (Coprime.ne_zero x)]
  calc besselDirichlet P.shiftSqCoeff s = ∑' h, F h := rfl
    _ = ∑' q : ℕ × P.Coprime, F (P.tripleIndex q) := (P.tripleIndex_injective.tsum_eq hsupp).symm
    _ = ∑' q : ℕ × P.Coprime, (ρc * t) * ((ρc ^ 2 * t ^ 3) ^ q.1 * g q.2) := tsum_congr hterm
    _ = (ρc * t) * ((∑' j : ℕ, (ρc ^ 2 * t ^ 3) ^ j) * ∑' x : P.Coprime, g x) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hqsum hgsum]
    _ = _ := by
        rw [tsum_geometric_of_norm_lt_one hq, hD]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
