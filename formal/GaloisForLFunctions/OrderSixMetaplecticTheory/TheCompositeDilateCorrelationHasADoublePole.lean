import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeDilateCombinationCarriesTheDoublePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtEveryPrimaryPrimeHasADoublePole

/-!
# The composite dilate correlation has a double pole

Patterson's relations at `p` (`T(xp^{3j}) = ρ^jT(x)`, `T(xp^{3j+2}) = 0` for `p ∤ x`) peel one prime at a time
(`PrimaryPrime.besselDirichlet_peel`): a coefficient vanishing off `k ≡ 1 mod 3` with `F(p^{3j+1}x) = ρ^{2j+1}G(x)` has
`D_F = E_p(s)D_G`, `E_p(s) = ρρ^{−s}(1 − ρ²ρ^{−3s})^{−1}`. For `m = pq` this gives

`D_A = E_pE_qD_m`, `D_B = E_pE_qD_×`, `D_{UL} = E_pD_m`, `D_{LU} = E_qD_m`,

with `D_× = Σ T(kp)T(kq)` and `D_m = (q/p)₃D_×` (Patterson at both primes). By cubic reciprocity the factor `(p/q)₃`
of the mixed dilate cosets cancels `(q/p)₃`, so the composite combination is `c_p(s)c_q(s)D_m(s)`
(`combination_eq`), and (`mDilateCorrelation_double_pole`)

`(s − 4/3)²M(s)D_m(s) → (2 + 2(p/q)₃)·108π³r³/(c_p(4/3)c_q(4/3)) ≠ 0`.

The residue is the product of the local factors exactly when `(p/q)₃ = 1`; otherwise it carries `(1 + (p/q)₃)/2`,
of modulus `1/2`. Since `T(k)T(km) = (q/p)₃(9/p)₃(9/q)₃\overline{G̃(p)G̃(q)}(k/m)₃T(k)²`, the cubic twist
`L_{χ_m} = Σ (k/m)₃T(k)²(4π|ξ_k|)^{−s}` keeps the double pole (`cubicTwistAtPair_double_pole`).
-/

noncomputable section

open Filter Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- **Patterson peeling at `p`.** -/
theorem besselDirichlet_peel (F G : O → ℂ) (s : ℂ) (hs : 2 / 3 < s.re)
    (hF0 : ∀ (k : ℕ) (x : O), ¬ P.p ∣ x → k % 3 ≠ 1 → F (P.p ^ k * x) = 0)
    (hF1 : ∀ (j : ℕ) (x : O), ¬ P.p ∣ x →
      F (P.p ^ (3 * j + 1) * x) = (‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℂ) ^ 2) ^ j * G x)
    (hGp : ∀ x, P.p ∣ x → G x = 0)
    (hGs : Summable (fun h : O => if h = 0 then 0 else ‖G h‖ * ‖cuspFrequency h‖ ^ (-s.re))) :
    besselDirichlet F s =
      (‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) *
        (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ * besselDirichlet G s := by
  set t : ℂ := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) with htdef
  set ρc : ℂ := (‖ringComplex P.p‖ : ℂ) with hρc
  let w : O → ℂ := fun h => ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let F' : O → ℂ := fun h => if h = 0 then 0 else F h * w h
  let g : P.Coprime → ℂ := fun x => G x.val * w x.val
  have hq := P.norm_rho_cube_lt s hs
  have hsupp : Function.support F' ⊆ Set.range P.tripleIndex := by
    intro h hF
    have hh : h ≠ 0 := fun h0 => hF (by simp [F', h0])
    obtain ⟨k, x, hx, rfl⟩ := WfDvdMonoid.max_power_factor hh P.prime.irreducible
    by_cases hk : k % 3 = 1
    · refine ⟨(k / 3, ⟨x, hx⟩), ?_⟩
      simp only [tripleIndex]
      congr 2
      omega
    · exfalso
      apply hF
      simp [F', hh, hF0 k x hx hk]
  have hterm : ∀ q : ℕ × P.Coprime, F' (P.tripleIndex q) = (ρc * t) * ((ρc ^ 2 * t ^ 3) ^ q.1 * g q.2) := by
    rintro ⟨j, x, hx⟩
    have hne : P.p ^ (3 * j + 1) * x ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.ne_zero) (fun h0 => hx (by rw [h0]; exact dvd_zero _))
    simp only [F', g, w, tripleIndex]
    rw [if_neg hne, hF1 j x hx, P.weight_tripleIndex, mul_pow, pow_mul]
    ring
  have hgsum : Summable (fun x : P.Coprime => ‖g x‖) := by
    refine ((hGs.subtype {x : O | ¬ P.p ∣ x}).mul_left ((4 * Real.pi) ^ (-s.re))).congr fun x => ?_
    have hx0 := Coprime.ne_zero x
    have hξ : 0 < ‖cuspFrequency x.val‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero _ hx0)
    simp only [Function.comp, if_neg hx0, g, w, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
      Real.mul_rpow (by positivity) hξ.le]
    ring
  have hqsum : Summable (fun j : ℕ => ‖(ρc ^ 2 * t ^ 3) ^ j‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hq
  have hD : ∑' x : P.Coprime, g x = besselDirichlet G s := by
    have hsub : Function.support (fun h : O => if h = 0 then 0 else
        G h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) ⊆ {x : O | ¬ P.p ∣ x} := by
      intro h hG hd
      apply hG
      simp [hGp h hd]
    rw [besselDirichlet, ← tsum_subtype_eq_of_support_subset hsub]
    refine tsum_congr fun x => ?_
    simp only [g, w, if_neg (Coprime.ne_zero x)]
  calc besselDirichlet F s = ∑' h, F' h := rfl
    _ = ∑' q : ℕ × P.Coprime, F' (P.tripleIndex q) := (P.tripleIndex_injective.tsum_eq hsupp).symm
    _ = ∑' q : ℕ × P.Coprime, (ρc * t) * ((ρc ^ 2 * t ^ 3) ^ q.1 * g q.2) := tsum_congr hterm
    _ = (ρc * t) * ((∑' j : ℕ, (ρc ^ 2 * t ^ 3) ^ j) * ∑' x : P.Coprime, g x) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hqsum hgsum]
    _ = _ := by
        rw [tsum_geometric_of_norm_lt_one hq, hD]
        simp only [htdef, hρc]
        ring

/-- `T(xp^k) = 0` for `p ∤ x`, `k ≡ 2 mod 3`. -/
theorem coeff_vanish (x : O) (hx : ¬ P.p ∣ x) (k : ℕ) (hk : k % 3 = 2) : rationalSourceResidualFourierCoefficient (x * P.p ^ k) = 0 :=
  rationalSourceResidualFourierCoefficient_prime_power_vanish P.p P.prime P.primary x hx k hk

/-- `T(xp^{3j+1}) = ρ^jT(xp)`. -/
theorem coeff_cube_one (x : O) (hx : x ≠ 0) (j : ℕ) :
    rationalSourceResidualFourierCoefficient (x * P.p ^ (3 * j + 1)) = (‖ringComplex P.p‖ : ℂ) ^ j * rationalSourceResidualFourierCoefficient (x * P.p) := by
  rw [show x * P.p ^ (3 * j + 1) = (x * P.p) * P.p ^ (3 * j) by ring,
    P.coeff_mul_cube_pow _ (mul_ne_zero hx P.ne_zero)]

end PrimaryPrime

namespace PrimaryPair

variable (R : PrimaryPair)

theorem P_not_dvd_Q_pow_mul {y : O} (hy : ¬ R.P.p ∣ y) (a : ℕ) : ¬ R.P.p ∣ R.Q.p ^ a * y := fun h =>
  (R.P.prime.dvd_or_dvd h).elim (fun h1 => R.P_not_dvd_Q (R.P.prime.dvd_of_dvd_pow h1)) hy

theorem Q_not_dvd_P_pow_mul {y : O} (hy : ¬ R.Q.p ∣ y) (a : ℕ) : ¬ R.Q.p ∣ R.P.p ^ a * y := fun h =>
  (R.Q.prime.dvd_or_dvd h).elim (fun h1 => R.Q_not_dvd_P (R.Q.prime.dvd_of_dvd_pow h1)) hy

theorem P_not_dvd_mul_Q {y : O} (hy : ¬ R.P.p ∣ y) : ¬ R.P.p ∣ y * R.Q.p := fun h =>
  (R.P.prime.dvd_or_dvd h).elim hy R.P_not_dvd_Q

theorem Q_not_dvd_mul_P {y : O} (hy : ¬ R.Q.p ∣ y) : ¬ R.Q.p ∣ y * R.P.p := fun h =>
  (R.Q.prime.dvd_or_dvd h).elim hy R.Q_not_dvd_P

theorem ne_zero_of_not_dvd {π y : O} (hy : ¬ π ∣ y) : y ≠ 0 := fun h => hy (h ▸ dvd_zero π)

/-! ### Intermediate coefficients -/

/-- `T(xp)T(xq²)` for `p ∤ x`. -/
def shiftHalf (x : O) : ℂ := if R.P.p ∣ x then 0 else rationalSourceResidualFourierCoefficient (x * R.P.p) * rationalSourceResidualFourierCoefficient (x * R.Q.p * R.Q.p)

/-- `T(x)T(xq²p)` for `p ∤ x`. -/
def crossHalf (x : O) : ℂ := if R.P.p ∣ x then 0 else rationalSourceResidualFourierCoefficient x * rationalSourceResidualFourierCoefficient (x * R.Q.p * R.Q.p * R.P.p)

/-- `T(yq)T(yp)` for `y` prime to `m`. -/
def crossDilate (y : O) : ℂ := if R.P.p ∣ y ∨ R.Q.p ∣ y then 0 else rationalSourceResidualFourierCoefficient (y * R.Q.p) * rationalSourceResidualFourierCoefficient (y * R.P.p)

theorem summable_shiftHalf {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.shiftHalf h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine summable_coeff_of_le _ (fun x => x * R.P.p) (fun x => x * R.Q.p * R.Q.p) R.P.norm_pos
    (pow_pos R.Q.norm_pos 2) (injective_mul_const R.P.ne_zero)
    (fun a b hab => mul_right_cancel₀ R.QQ_ne_zero (by linear_combination hab)) (fun h => ?_) (fun h => ?_)
    (fun h => ?_) hσ
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · rw [shiftHalf]
    split_ifs
    · rw [norm_zero]
      positivity
    · rw [norm_mul]

theorem summable_crossHalf {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.crossHalf h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  have hc : R.Q.p * R.Q.p * R.P.p ≠ 0 := mul_ne_zero R.QQ_ne_zero R.P.ne_zero
  refine summable_coeff_of_le _ id (fun x => x * R.Q.p * R.Q.p * R.P.p) one_pos
    (mul_pos (pow_pos R.Q.norm_pos 2) R.P.norm_pos) Function.injective_id
    (fun a b hab => mul_right_cancel₀ hc (by linear_combination hab)) (fun h => (one_mul _).symm) (fun h => ?_)
    (fun h => ?_) hσ
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · rw [crossHalf]
    split_ifs
    · rw [norm_zero]
      positivity
    · rw [norm_mul]
      rfl

theorem summable_crossDilate {σ : ℝ} (hσ : 4 < σ) :
    Summable (fun h : O => if h = 0 then 0 else ‖R.crossDilate h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  refine summable_coeff_of_le _ (fun x => x * R.Q.p) (fun x => x * R.P.p) R.Q.norm_pos R.P.norm_pos
    (injective_mul_const R.Q.ne_zero) (injective_mul_const R.P.ne_zero) (fun h => ?_) (fun h => ?_) (fun h => ?_) hσ
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · simp only [cuspFrequency_mul_right, norm_mul]
    ring
  · rw [crossDilate]
    split_ifs
    · rw [norm_zero]
      positivity
    · rw [norm_mul]

/-! ### Peeling the five series -/

theorem shift_peel_P (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet R.shiftCoeff s = (‖ringComplex R.P.p‖ : ℂ) * ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex R.P.p‖ : ℂ) ^ 2 * (((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet R.shiftHalf s := by
  refine R.P.besselDirichlet_peel _ _ s (by linarith) (fun k x hx hk => ?_) (fun j x hx => ?_)
    (fun x hx => by rw [shiftHalf, if_pos hx]) (R.summable_shiftHalf hs)
  · rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
    · rw [shiftCoeff, show -(R.P.p ^ k * x * (R.P.p * R.Q.p)) * R.Q.p * R.P.p =
          -(x * R.Q.p * R.Q.p * R.P.p ^ (k + 2)) by ring, rationalSourceResidualFourierCoefficient_neg,
        R.P.coeff_vanish _ (R.P_not_dvd_mul_Q (R.P_not_dvd_mul_Q hx)) _ (by omega), mul_zero]
    · rw [shiftCoeff, mul_comm (R.P.p ^ k) x, R.P.coeff_vanish x hx k h2, zero_mul]
  · have hx0 := PrimaryPair.ne_zero_of_not_dvd hx
    rw [shiftCoeff, shiftHalf, if_neg hx, mul_comm (R.P.p ^ (3 * j + 1)) x, R.P.coeff_cube_one x hx0,
      show -(x * R.P.p ^ (3 * j + 1) * (R.P.p * R.Q.p)) * R.Q.p * R.P.p =
        -(x * R.Q.p * R.Q.p * R.P.p ^ (3 * (j + 1))) by ring, rationalSourceResidualFourierCoefficient_neg,
      R.P.coeff_mul_cube_pow _ (mul_ne_zero (mul_ne_zero hx0 R.Q.ne_zero) R.Q.ne_zero)]
    ring

theorem shiftHalf_peel_Q (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet R.shiftHalf s = (‖ringComplex R.Q.p‖ : ℂ) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex R.Q.p‖ : ℂ) ^ 2 * (((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet R.mDilateCoeff s := by
  refine R.Q.besselDirichlet_peel _ _ s (by linarith) (fun k y hy hk => ?_) (fun i y hy => ?_)
    (fun y hy => by rw [mDilateCoeff, if_pos (Or.inr hy)]) (R.summable_mDilateCoeff hs)
  · rw [shiftHalf]
    split_ifs with hp
    · rfl
    · have hp' : ¬ R.P.p ∣ y := fun h => hp (dvd_mul_of_dvd_right h _)
      rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
      · rw [show R.Q.p ^ k * y * R.Q.p * R.Q.p = y * R.Q.p ^ (k + 2) by ring,
          R.Q.coeff_vanish y hy _ (by omega), mul_zero]
      · rw [show R.Q.p ^ k * y * R.P.p = y * R.P.p * R.Q.p ^ k by ring,
          R.Q.coeff_vanish _ (R.Q_not_dvd_mul_P hy) k h2, zero_mul]
  · by_cases hp : R.P.p ∣ y
    · rw [shiftHalf, if_pos (dvd_mul_of_dvd_right hp _), mDilateCoeff, if_pos (Or.inl hp), mul_zero]
    · have hy0 := PrimaryPair.ne_zero_of_not_dvd hy
      rw [shiftHalf, if_neg (R.P_not_dvd_Q_pow_mul hp _), mDilateCoeff, if_neg (not_or.mpr ⟨hp, hy⟩),
        show R.Q.p ^ (3 * i + 1) * y * R.P.p = y * R.P.p * R.Q.p ^ (3 * i + 1) by ring,
        R.Q.coeff_cube_one _ (mul_ne_zero hy0 R.P.ne_zero),
        show R.Q.p ^ (3 * i + 1) * y * R.Q.p * R.Q.p = y * R.Q.p ^ (3 * (i + 1)) by ring,
        R.Q.coeff_mul_cube_pow _ hy0, show y * R.P.p * R.Q.p = y * (R.P.p * R.Q.p) by ring]
      ring

theorem cross_peel_P (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet R.crossCoeff s = (‖ringComplex R.P.p‖ : ℂ) * ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex R.P.p‖ : ℂ) ^ 2 * (((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet R.crossHalf s := by
  refine R.P.besselDirichlet_peel _ _ s (by linarith) (fun k x hx hk => ?_) (fun j x hx => ?_)
    (fun x hx => by rw [crossHalf, if_pos hx]) (R.summable_crossHalf hs)
  · rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
    · rw [crossCoeff, show -(R.P.p ^ k * x * R.P.p) * R.P.p = -(x * R.P.p ^ (k + 2)) by ring, rationalSourceResidualFourierCoefficient_neg,
        R.P.coeff_vanish x hx _ (by omega), mul_zero]
    · rw [crossCoeff, show R.P.p ^ k * x * R.Q.p * R.Q.p = x * R.Q.p * R.Q.p * R.P.p ^ k by ring,
        R.P.coeff_vanish _ (R.P_not_dvd_mul_Q (R.P_not_dvd_mul_Q hx)) k h2, zero_mul]
  · have hx0 := PrimaryPair.ne_zero_of_not_dvd hx
    rw [crossCoeff, crossHalf, if_neg hx,
      show R.P.p ^ (3 * j + 1) * x * R.Q.p * R.Q.p = x * R.Q.p * R.Q.p * R.P.p ^ (3 * j + 1) by ring,
      R.P.coeff_cube_one _ (mul_ne_zero (mul_ne_zero hx0 R.Q.ne_zero) R.Q.ne_zero),
      show -(R.P.p ^ (3 * j + 1) * x * R.P.p) * R.P.p = -(x * R.P.p ^ (3 * (j + 1))) by ring, rationalSourceResidualFourierCoefficient_neg,
      R.P.coeff_mul_cube_pow _ hx0]
    ring

theorem crossHalf_peel_Q (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet R.crossHalf s = (‖ringComplex R.Q.p‖ : ℂ) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex R.Q.p‖ : ℂ) ^ 2 * (((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet R.crossDilate s := by
  refine R.Q.besselDirichlet_peel _ _ s (by linarith) (fun k y hy hk => ?_) (fun i y hy => ?_)
    (fun y hy => by rw [crossDilate, if_pos (Or.inr hy)]) (R.summable_crossDilate hs)
  · rw [crossHalf]
    split_ifs with hp
    · rfl
    · rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
      · rw [show R.Q.p ^ k * y * R.Q.p * R.Q.p * R.P.p = y * R.P.p * R.Q.p ^ (k + 2) by ring,
          R.Q.coeff_vanish _ (R.Q_not_dvd_mul_P hy) _ (by omega), mul_zero]
      · rw [mul_comm (R.Q.p ^ k) y, R.Q.coeff_vanish y hy k h2, zero_mul]
  · by_cases hp : R.P.p ∣ y
    · rw [crossHalf, if_pos (dvd_mul_of_dvd_right hp _), crossDilate, if_pos (Or.inl hp), mul_zero]
    · have hy0 := PrimaryPair.ne_zero_of_not_dvd hy
      rw [crossHalf, if_neg (R.P_not_dvd_Q_pow_mul hp _), crossDilate, if_neg (not_or.mpr ⟨hp, hy⟩),
        mul_comm (R.Q.p ^ (3 * i + 1)) y, R.Q.coeff_cube_one y hy0,
        show y * R.Q.p ^ (3 * i + 1) * R.Q.p * R.Q.p * R.P.p = y * R.P.p * R.Q.p ^ (3 * (i + 1)) by ring,
        R.Q.coeff_mul_cube_pow _ (mul_ne_zero hy0 R.P.ne_zero)]
      ring

theorem ul_peel_P (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet R.ulCoeff s = (‖ringComplex R.P.p‖ : ℂ) * ((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex R.P.p‖ : ℂ) ^ 2 * (((‖ringComplex R.P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet R.mDilateCoeff s := by
  refine R.P.besselDirichlet_peel _ _ s (by linarith) (fun k x hx hk => ?_) (fun j x hx => ?_)
    (fun x hx => by rw [mDilateCoeff, if_pos (Or.inl hx)]) (R.summable_mDilateCoeff hs)
  · rw [ulCoeff]
    split_ifs with hq
    · rfl
    · have hq' : ¬ R.Q.p ∣ x := fun h => hq (dvd_mul_of_dvd_right h _)
      rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
      · rw [show -(R.P.p ^ k * x * (R.P.p * R.P.p)) = -(x * R.P.p ^ (k + 2)) by ring, rationalSourceResidualFourierCoefficient_neg,
          R.P.coeff_vanish x hx _ (by omega), mul_zero]
      · rw [show R.P.p ^ k * x * R.Q.p = x * R.Q.p * R.P.p ^ k by ring,
          R.P.coeff_vanish _ (R.P_not_dvd_mul_Q hx) k h2, zero_mul]
  · by_cases hq : R.Q.p ∣ x
    · rw [ulCoeff, if_pos (dvd_mul_of_dvd_right hq _), mDilateCoeff, if_pos (Or.inr hq), mul_zero]
    · have hx0 := PrimaryPair.ne_zero_of_not_dvd hx
      rw [ulCoeff, if_neg (R.Q_not_dvd_P_pow_mul hq _), mDilateCoeff, if_neg (not_or.mpr ⟨hx, hq⟩),
        show R.P.p ^ (3 * j + 1) * x * R.Q.p = x * R.Q.p * R.P.p ^ (3 * j + 1) by ring,
        R.P.coeff_cube_one _ (mul_ne_zero hx0 R.Q.ne_zero),
        show -(R.P.p ^ (3 * j + 1) * x * (R.P.p * R.P.p)) = -(x * R.P.p ^ (3 * (j + 1))) by ring, rationalSourceResidualFourierCoefficient_neg,
        R.P.coeff_mul_cube_pow _ hx0, show x * R.Q.p * R.P.p = x * (R.P.p * R.Q.p) by ring]
      ring

theorem lu_peel_Q (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet R.luCoeff s = (‖ringComplex R.Q.p‖ : ℂ) * ((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s) *
      (1 - (‖ringComplex R.Q.p‖ : ℂ) ^ 2 * (((‖ringComplex R.Q.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
        besselDirichlet R.mDilateCoeff s := by
  refine R.Q.besselDirichlet_peel _ _ s (by linarith) (fun k x hx hk => ?_) (fun j x hx => ?_)
    (fun x hx => by rw [mDilateCoeff, if_pos (Or.inr hx)]) (R.summable_mDilateCoeff hs)
  · rw [luCoeff]
    split_ifs with hp
    · rfl
    · rcases (by omega : k % 3 = 0 ∨ k % 3 = 2) with h0 | h2
      · rw [show -(R.Q.p ^ k * x * (R.Q.p * R.Q.p)) = -(x * R.Q.p ^ (k + 2)) by ring, rationalSourceResidualFourierCoefficient_neg,
          R.Q.coeff_vanish x hx _ (by omega), mul_zero]
      · rw [show R.Q.p ^ k * x * R.P.p = x * R.P.p * R.Q.p ^ k by ring,
          R.Q.coeff_vanish _ (R.Q_not_dvd_mul_P hx) k h2, zero_mul]
  · by_cases hp : R.P.p ∣ x
    · rw [luCoeff, if_pos (dvd_mul_of_dvd_right hp _), mDilateCoeff, if_pos (Or.inl hp), mul_zero]
    · have hx0 := PrimaryPair.ne_zero_of_not_dvd hx
      rw [luCoeff, if_neg (R.P_not_dvd_Q_pow_mul hp _), mDilateCoeff, if_neg (not_or.mpr ⟨hp, hx⟩),
        show R.Q.p ^ (3 * j + 1) * x * R.P.p = x * R.P.p * R.Q.p ^ (3 * j + 1) by ring,
        R.Q.coeff_cube_one _ (mul_ne_zero hx0 R.P.ne_zero),
        show -(R.Q.p ^ (3 * j + 1) * x * (R.Q.p * R.Q.p)) = -(x * R.Q.p ^ (3 * (j + 1))) by ring, rationalSourceResidualFourierCoefficient_neg,
        R.Q.coeff_mul_cube_pow _ hx0, show x * R.P.p * R.Q.p = x * (R.P.p * R.Q.p) by ring]
      ring

/-! ### Reciprocity and the product of the local factors -/

/-- `T(k)T(km) = (q/p)₃T(kq)T(kp)` (Patterson at `p` twice). -/
theorem mDilateCoeff_eq_cross (y : O) :
    R.mDilateCoeff y = ringComplex (symbol R.Q.p R.P.p) * R.crossDilate y := by
  rw [mDilateCoeff, crossDilate]
  split_ifs with h
  · ring
  · obtain ⟨hp, hq⟩ := not_or.mp h
    have n1 := rationalSourceResidualFourierCoefficient_prime_normalized R.P.p R.P.prime R.P.primary y hp
    have n3 := rationalSourceResidualFourierCoefficient_prime_normalized R.P.p R.P.prime R.P.primary _ (R.P_not_dvd_mul_Q hp)
    rw [show 9 * (y * R.Q.p) = 9 * y * R.Q.p by ring, symbol_mul_numerator, map_mul] at n3
    rw [show y * (R.P.p * R.Q.p) = y * R.Q.p * R.P.p by ring, n3, n1]
    ring

/-- **The composite combination is `c_p(s)c_q(s)D_m(s)`.** -/
theorem combination_eq (s : ℂ) (hs : 4 < s.re) :
    R.combination s = R.P.dilateFactor s * R.Q.dilateFactor s * besselDirichlet R.mDilateCoeff s := by
  have hB : besselDirichlet R.mDilateCoeff s = ringComplex (symbol R.Q.p R.P.p) * besselDirichlet R.crossDilate s := by
    rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    split_ifs
    · ring
    · rw [R.mDilateCoeff_eq_cross]
      ring
  rw [combination, R.shift_peel_P s hs, R.shiftHalf_peel_Q s hs, R.cross_peel_P s hs, R.crossHalf_peel_Q s hs,
    R.ul_peel_P s hs, R.lu_peel_Q s hs, PrimaryPrime.dilateFactor, PrimaryPrime.dilateFactor, hB,
    R.symbol_reciprocity_pair]
  ring

theorem two_add_two_symbol_ne_zero : 2 + 2 * ringComplex (symbol R.P.p R.Q.p) ≠ 0 := by
  intro h0
  have h3 := R.symbol_cube
  rw [← R.symbol_reciprocity_pair, show ringComplex (symbol R.P.p R.Q.p) = -1 by linear_combination h0 / 2] at h3
  norm_num at h3

/-- **The composite dilate correlation has a double pole.** For coprime primary primes `p, q`, `m = pq`,
`M(s)D_m(s)`, `D_m(s) = Σ_{(k,m)=1}T(k)T(km)(4π|ξ_k|)^{−s}`, continues to `{1 < Re s < 13/3, Im s > 0}` and to a
punctured neighbourhood of `4/3`, and `(s − 4/3)²M(s)D_m(s) → (2 + 2(p/q)₃)·108π³r³/(c_p(4/3)c_q(4/3)) ≠ 0`. -/
theorem mDilateCorrelation_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * besselDirichlet R.mDilateCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 ((2 + 2 * ringComplex (symbol R.P.p R.Q.p)) * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
          (R.P.dilateFactor (4 / 3) * R.Q.dilateFactor (4 / 3)))) ∧
      (2 + 2 * ringComplex (symbol R.P.p R.Q.p)) * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
          (R.P.dilateFactor (4 / 3) * R.Q.dilateFactor (4 / 3)) ≠ 0 := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl⟩ := R.combination_double_pole
  obtain ⟨-, -, -, -, -, hne⟩ := thetaSqDirichlet_double_pole
  have hre43 : (2 / 3 : ℝ) < (4 / 3 : ℂ).re := by norm_num
  have hc : ∀ s : ℂ, 2 / 3 < s.re → R.P.dilateFactor s * R.Q.dilateFactor s ≠ 0 := fun s hs =>
    mul_ne_zero (R.P.dilateFactor_ne_zero s hs) (R.Q.dilateFactor_ne_zero s hs)
  have hcd : ∀ s : ℂ, 2 / 3 < s.re → DifferentiableAt ℂ (fun s => R.P.dilateFactor s * R.Q.dilateFactor s) s :=
    fun s hs => (R.P.dilateFactor_differentiableAt s hs).mul (R.Q.dilateFactor_differentiableAt s hs)
  refine ⟨fun s => Λ s / (R.P.dilateFactor s * R.Q.dilateFactor s), fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_,
    div_ne_zero (mul_ne_zero R.two_add_two_symbol_ne_zero hne) (hc _ hre43)⟩
  · show Λ s / (R.P.dilateFactor s * R.Q.dilateFactor s) = _
    rw [hΛ s hs4 hs hi, R.combination_eq s hs4, div_eq_iff (hc s (by linarith))]
    ring
  · exact (hΛd s hs1 hs hi).div (hcd s (by linarith)) (hc s (by linarith))
  · have hre : ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), 2 / 3 < s.re :=
      eventually_nhdsWithin_of_eventually_nhds
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre43)
    filter_upwards [hΛn, hre] with s h1 h2
    exact h1.div (hcd s h2) (hc s h2)
  · have hcont : Tendsto (fun s => R.P.dilateFactor s * R.Q.dilateFactor s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (R.P.dilateFactor (4 / 3) * R.Q.dilateFactor (4 / 3))) :=
      (hcd _ hre43).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine (hΛl.div hcont (hc _ hre43)).congr' (Eventually.of_forall fun s => ?_)
    simp only [Pi.div_apply]
    ring

/-! ### The cubic twist at `m` -/

/-- The cubic twist `(k/m)₃T(k)²` of the theta square at `m = pq`. -/
def twistCoeff (k : O) : ℂ := ringComplex (symbol k (R.P.p * R.Q.p)) * rationalSourceResidualFourierCoefficient k ^ 2

/-- `κ_m = (q/p)₃(9/p)₃\overline{G̃(p)}(9/q)₃\overline{G̃(q)}`. -/
def twistFactor : ℂ := ringComplex (symbol R.Q.p R.P.p) *
  (ringComplex (symbol 9 R.P.p) * star (normalizedCubicUnitGauss R.P.p)) *
    (ringComplex (symbol 9 R.Q.p) * star (normalizedCubicUnitGauss R.Q.p))

/-- `T(k)T(km) = κ_m(k/m)₃T(k)²`. -/
theorem mDilateCoeff_eq_twist (k : O) : R.mDilateCoeff k = R.twistFactor * R.twistCoeff k := by
  rw [mDilateCoeff, twistCoeff, symbol_mul_denominator, map_mul]
  split_ifs with h
  · rcases h with hp | hq
    · rw [← R.P.chi_res, (R.P.res_eq_zero_iff k).mpr hp, MulChar.map_zero]
      ring
    · rw [← R.Q.chi_res k, (R.Q.res_eq_zero_iff k).mpr hq, MulChar.map_zero]
      ring
  · obtain ⟨hp, hq⟩ := not_or.mp h
    have n2 := rationalSourceResidualFourierCoefficient_prime_normalized R.Q.p R.Q.prime R.Q.primary k hq
    have n3 := rationalSourceResidualFourierCoefficient_prime_normalized R.P.p R.P.prime R.P.primary _ (R.P_not_dvd_mul_Q hp)
    rw [show 9 * (k * R.Q.p) = 9 * k * R.Q.p by ring, symbol_mul_numerator, map_mul, symbol_mul_numerator,
      map_mul] at n3
    rw [symbol_mul_numerator, map_mul] at n2
    rw [show k * (R.P.p * R.Q.p) = k * R.Q.p * R.P.p by ring, n3, n2, twistFactor]
    ring

theorem twistFactor_ne_zero : R.twistFactor ≠ 0 := by
  have ha : ringComplex (symbol R.Q.p R.P.p) ≠ 0 := fun h0 => by
    have h3 := R.symbol_cube
    rw [h0] at h3
    norm_num at h3
  exact mul_ne_zero (mul_ne_zero ha R.P.twistFactor_ne_zero) R.Q.twistFactor_ne_zero

/-- **Every cubic twist at a product of two primes keeps the double pole.** `M(s)L_{χ_m}(s)`,
`L_{χ_m}(s) = Σ_k (k/m)₃T(k)²(4π|ξ_k|)^{−s}`, continues as above, and
`(s − 4/3)²M(s)L_{χ_m}(s) → (2 + 2(p/q)₃)·108π³r³/(c_p(4/3)c_q(4/3)κ_m) ≠ 0`. -/
theorem cubicTwistAtPair_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * besselDirichlet R.twistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 ((2 + 2 * ringComplex (symbol R.P.p R.Q.p)) * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
          (R.P.dilateFactor (4 / 3) * R.Q.dilateFactor (4 / 3) * R.twistFactor))) ∧
      (2 + 2 * ringComplex (symbol R.P.p R.Q.p)) * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
          (R.P.dilateFactor (4 / 3) * R.Q.dilateFactor (4 / 3) * R.twistFactor) ≠ 0 := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, hne⟩ := R.mDilateCorrelation_double_pole
  have hκ := R.twistFactor_ne_zero
  have hD : ∀ s, besselDirichlet R.mDilateCoeff s = R.twistFactor * besselDirichlet R.twistCoeff s := by
    intro s
    rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    split_ifs
    · ring
    · rw [R.mDilateCoeff_eq_twist]
      ring
  refine ⟨fun s => Λ s / R.twistFactor, fun s hs4 hs hi => ?_, fun s hs1 hs hi => (hΛd s hs1 hs hi).div_const _,
    ?_, ?_, ?_⟩
  · show Λ s / R.twistFactor = _
    rw [hΛ s hs4 hs hi, hD, div_eq_iff hκ]
    ring
  · filter_upwards [hΛn] with s h1
    exact h1.div_const _
  · have h := hΛl.div_const R.twistFactor
    rw [div_div] at h
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only
    ring
  · rw [← div_div]
    exact div_ne_zero hne hκ

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
