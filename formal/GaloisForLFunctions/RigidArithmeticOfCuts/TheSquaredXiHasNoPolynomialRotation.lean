import GaloisForLFunctions.RigidArithmeticOfCuts.TheZeroOfMaximalAngle
import GaloisForLFunctions.RigidArithmeticOfCuts.RotatedRelationsWithPolynomialCoefficients
import GaloisForLFunctions.HTGeometry.EntireOrderTwoSeries
import GaloisForLFunctions.RHTower.XiCriticalGaussianNodes

/-!
# The squared Xi has no polynomial rotation

The Taylor coefficients of `Q` are `(−1)^k a_k`, with `ξ(½ + x) = Σ a_k x^{2k}`. The sequence `a_k` is a positive Turán
sequence, so `a_{k+1}/a_k` decreases, and since `Q` is entire its limit is `0`.

Therefore **no relation `T(w) Q(w) = A(w) Q(ϑ w) + B(w) Q(ϑ̄ w)` with polynomial coefficients exists**, for `ϑ` on the unit
circle off the real axis, except the trivial one. This settles the first test of the second-order mechanism in the
class of polynomial coefficients, and it extends the constant-coefficient obstruction to all degrees.

A rotated relation forcing RH must have coefficients of the size of `Q`. The vacuous `A = Q(ϑ̄ ·)`, `B = −Q(ϑ ·)` has that
size, and it satisfies `‖A‖ = ‖B‖` at the zeros exactly under RH. So all the content of such a relation lies in the
arithmetic source of its coefficients.
-/

open Complex Filter Topology RHTower Polynomial
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- `ξ(½ + x)` in the coordinates of the Turán property. -/
private def centreXi (x : ℂ) : ℂ := XiC (-(I * x))

private lemma turan_centreXi : TuranTaylorAtZero centreXi :=
  turanTaylorAtZero_XiC_neg_I_mul_of_cone sqrt3Cone_centre

/-- The even Taylor coefficient `a_k` of `ξ(½ + x)`. -/
def xiCoeff (k : ℕ) : ℝ := evenTaylorRe centreXi k

theorem xiCoeff_nonneg (k : ℕ) : 0 ≤ xiCoeff k := turan_centreXi.2.2.1 k

theorem xiCoeff_turan {i j : ℕ} (hij : i < j) :
    xiCoeff i * xiCoeff (j + 1) ≤ xiCoeff (i + 1) * xiCoeff j := turan_centreXi.2.2.2 i j hij

private lemma differentiable_centreXi : Differentiable ℂ centreXi := turan_centreXi.1.1

private lemma taylorCoeff_even (k : ℕ) : taylorCoeff centreXi (2 * k) = (xiCoeff k : ℂ) := by
  have him := im_factorial_inv_mul turan_centreXi.1 (2 * k)
  apply Complex.ext
  · simp only [taylorCoeff, xiCoeff, evenTaylorRe, Complex.ofReal_re]
  · simp only [taylorCoeff, Complex.ofReal_im]
    exact him

private lemma taylorCoeff_odd (k : ℕ) : taylorCoeff centreXi (2 * k + 1) = 0 := by
  rw [taylorCoeff, turan_centreXi.2.1 k, mul_zero]

/-- **The even Taylor series of `ξ(½ + x)`.** -/
theorem hasSum_centreXi (x : ℂ) : HasSum (fun k => (xiCoeff k : ℂ) * (x ^ 2) ^ k) (centreXi x) := by
  have h := hasSum_taylorCoeff differentiable_centreXi x
  have hinj : Function.Injective fun k : ℕ => 2 * k := fun _ _ he => by simpa using he
  have hf : ∀ n ∉ Set.range (fun k : ℕ => 2 * k), taylorCoeff centreXi n * x ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · exact absurd ⟨k, rfl⟩ hn
    · rw [taylorCoeff_odd, zero_mul]
  have h2 := (hinj.hasSum_iff hf).mpr h
  have hfun : ((fun n => taylorCoeff centreXi n * x ^ n) ∘ fun k : ℕ => 2 * k) =
      fun k => (xiCoeff k : ℂ) * (x ^ 2) ^ k := by
    funext k
    simp only [Function.comp]
    rw [taylorCoeff_even, pow_mul]
  rwa [hfun] at h2

/-- The Taylor coefficient of `Q`. -/
def squaredXiCoeff (k : ℕ) : ℂ := (-1) ^ k * (xiCoeff k : ℂ)

/-- **The Taylor series of `Q`.** -/
theorem hasSum_squaredXi (w : ℂ) : HasSum (fun k => squaredXiCoeff k * w ^ k) (squaredXi w) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-w) (n := 2) (by norm_num)
  have h := hasSum_centreXi x
  have hval : centreXi x = squaredXi w := by
    have hz : (-(I * x)) ^ 2 = w := by
      have : (-(I * x)) ^ 2 = I ^ 2 * x ^ 2 := by ring
      rw [this, Complex.I_sq, hx]
      ring
    rw [centreXi, ← squaredXi_sq, hz]
  rw [hval] at h
  have hfun : (fun k => (xiCoeff k : ℂ) * (x ^ 2) ^ k) = fun k => squaredXiCoeff k * w ^ k := by
    funext k
    rw [hx, squaredXiCoeff, neg_pow w]
    ring
  rwa [hfun] at h

private lemma xiCoeff_zero_pos : 0 < xiCoeff 0 := by
  refine lt_of_le_of_ne (xiCoeff_nonneg 0) fun h0 => ?_
  have h := (hasSum_squaredXi 0)
  have hval : squaredXi 0 = 0 := by
    have h1 : HasSum (fun k => squaredXiCoeff k * (0 : ℂ) ^ k) 0 := by
      have : (fun k => squaredXiCoeff k * (0 : ℂ) ^ k) = fun _ => 0 := by
        funext k
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [squaredXiCoeff, ← h0]
        · simp [zero_pow hk.ne']
      rw [this]
      exact hasSum_zero
    exact h.unique h1
  obtain ⟨q, hq⟩ := (squaredXi_eq_zero_iff 0).mp hval
  exact zeroSq_ne_zero q hq

/-- **Every coefficient is positive.** A vanishing coefficient makes all later ones vanish by Turán, so `Q` would be a
polynomial, while it has infinitely many zeros by Hardy. -/
theorem xiCoeff_pos (k : ℕ) : 0 < xiCoeff k := by
  classical
  by_contra hnot
  have hzero : ∃ k, xiCoeff k = 0 := ⟨k, le_antisymm (not_lt.mp hnot) (xiCoeff_nonneg k)⟩
  set k₀ := Nat.find hzero with hk₀
  have hk₀zero : xiCoeff k₀ = 0 := Nat.find_spec hzero
  have hk₀pos : 0 < k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h | h
    · rw [h] at hk₀zero
      exact absurd hk₀zero xiCoeff_zero_pos.ne'
    · exact h
  have hprev : 0 < xiCoeff (k₀ - 1) := by
    refine lt_of_le_of_ne (xiCoeff_nonneg _) fun h => ?_
    exact Nat.find_min hzero (by omega : k₀ - 1 < k₀) h.symm
  have hlater : ∀ j, k₀ ≤ j → xiCoeff j = 0 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hk₀zero
    | succ j hj ih =>
      have h := xiCoeff_turan (i := k₀ - 1) (j := j) (by omega)
      rw [ih, mul_zero] at h
      have h2 : xiCoeff (j + 1) ≤ 0 := by
        by_contra hpos
        have := mul_pos hprev (not_le.mp hpos)
        linarith
      exact le_antisymm h2 (xiCoeff_nonneg _)
  -- `Q` is a polynomial.
  set p : ℂ[X] := ∑ j ∈ Finset.range k₀, C (squaredXiCoeff j) * X ^ j with hp
  have hQp : ∀ w, squaredXi w = p.eval w := by
    intro w
    have hs : HasSum (fun j => squaredXiCoeff j * w ^ j)
        (∑ j ∈ Finset.range k₀, squaredXiCoeff j * w ^ j) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        have hle : k₀ ≤ j := by simpa using hj
        simp [squaredXiCoeff, hlater j hle]
    rw [(hasSum_squaredXi w).unique hs, hp, eval_finsetSum]
    simp
  have hp0 : p ≠ 0 := by
    intro h
    have := hQp 0
    rw [h, eval_zero] at this
    obtain ⟨q, hq⟩ := (squaredXi_eq_zero_iff 0).mp this
    exact zeroSq_ne_zero q hq
  have hinf := infinite_positive_real_XiC_zeros
  apply hinf
  have hfin : (p.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
  refine Set.Finite.of_finite_image (f := fun x : ℝ => ((x ^ 2 : ℝ) : ℂ))
    (hfin.subset ?_) ?_
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    have hval : squaredXi ((x ^ 2 : ℝ) : ℂ) = 0 := by
      have h := squaredXi_sq (x : ℂ)
      push_cast
      rw [h, hx]
    rw [hQp] at hval
    exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr hval))
  · intro a ha b hb hab
    have hab' : a ^ 2 = b ^ 2 := Complex.ofReal_injective hab
    have ha0 : 0 ≤ a := (show 0 < a ∧ _ from ha).1.le
    have hb0 : 0 ≤ b := (show 0 < b ∧ _ from hb).1.le
    exact (pow_left_inj₀ ha0 hb0 (by norm_num)).mp hab'

/-- The ratios `a_{k+1}/a_k` decrease. -/
private lemma ratio_antitone : Antitone fun k => xiCoeff (k + 1) / xiCoeff k := by
  refine antitone_nat_of_succ_le fun k => ?_
  have h1 := xiCoeff_pos k
  have h2 := xiCoeff_pos (k + 1)
  rw [div_le_div_iff₀ h2 h1]
  have h := xiCoeff_turan (i := k) (j := k + 1) (by omega)
  nlinarith

/-- **The ratios tend to zero.** A positive limit would give a finite radius of convergence. -/
theorem tendsto_ratio_xiCoeff : Tendsto (fun k => xiCoeff (k + 1) / xiCoeff k) atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range fun k => xiCoeff (k + 1) / xiCoeff k) :=
    ⟨0, by
      rintro _ ⟨k, rfl⟩
      exact div_nonneg (xiCoeff_nonneg _) (xiCoeff_nonneg _)⟩
  have hlim := tendsto_atTop_ciInf ratio_antitone hbdd
  set l := ⨅ k, xiCoeff (k + 1) / xiCoeff k with hl
  have hl0 : 0 ≤ l := le_ciInf fun k => div_nonneg (xiCoeff_nonneg _) (xiCoeff_nonneg _)
  rcases hl0.eq_or_lt with h | h
  · rwa [← h] at hlim
  · exfalso
    have hge : ∀ k, xiCoeff 0 * l ^ k ≤ xiCoeff k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : l ≤ xiCoeff (k + 1) / xiCoeff k := ciInf_le hbdd k
        rw [le_div_iff₀ (xiCoeff_pos k)] at h1
        calc xiCoeff 0 * l ^ (k + 1) = (xiCoeff 0 * l ^ k) * l := by ring
          _ ≤ xiCoeff k * l := mul_le_mul_of_nonneg_right ih hl0
          _ = l * xiCoeff k := mul_comm _ _
          _ ≤ _ := h1
    set w : ℂ := ((l⁻¹ : ℝ) : ℂ) with hw
    have hs := (hasSum_squaredXi w).summable.tendsto_atTop_zero
    have hn := hs.norm
    rw [norm_zero] at hn
    have hlow : ∀ k, xiCoeff 0 ≤ ‖squaredXiCoeff k * w ^ k‖ := by
      intro k
      rw [norm_mul, norm_pow, hw, Complex.norm_real, Real.norm_of_nonneg (by positivity), squaredXiCoeff,
        norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (xiCoeff_nonneg k)]
      have h1 := hge k
      have h2 : 0 < (l⁻¹) ^ k := by positivity
      calc xiCoeff 0 = xiCoeff 0 * l ^ k * (l⁻¹) ^ k := by
            rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ h.ne', one_pow, mul_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 h2.le
    have := ge_of_tendsto' hn hlow
    linarith [xiCoeff_zero_pos]

/-- **The squared Xi has no polynomial rotation.** A relation `T(w) Q(w) = A(w) Q(ϑ w) + B(w) Q(ϑ̄ w)`, `|ϑ| = 1`,
`Im ϑ ≠ 0`, with polynomial coefficients, is trivial. -/
theorem squaredXi_no_polynomial_rotation {ϑ : ℂ} (hn : ‖ϑ‖ = 1) (him : ϑ.im ≠ 0) {T A B : ℂ[X]}
    (hrel : ∀ w, T.eval w * squaredXi w =
      A.eval w * squaredXi (ϑ * w) + B.eval w * squaredXi (star ϑ * w)) :
    T = 0 ∧ A = 0 ∧ B = 0 := by
  have hf0 : ∀ k, squaredXiCoeff k ≠ 0 := by
    intro k
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact_mod_cast (xiCoeff_pos k).ne'
  have hnorm : ∀ k, ‖squaredXiCoeff k‖ = xiCoeff k := by
    intro k
    rw [squaredXiCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (xiCoeff_nonneg k)]
  have hratio : Tendsto (fun k => ‖squaredXiCoeff (k + 1) / squaredXiCoeff k‖) atTop (𝓝 0) := by
    simp only [norm_div, hnorm]
    exact tendsto_ratio_xiCoeff
  have h1 : ϑ ≠ 1 := fun h => him (by simp [h])
  have h2 : ϑ ≠ star ϑ := fun h => him (by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith)
  exact polynomial_rotated_relation_trivial hf0 hratio hasSum_squaredXi hn h1 h2 hrel

end GaloisForLFunctions.RigidArithmeticOfCuts
