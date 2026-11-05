import GaloisForLFunctions.FiniteFreeProbability.SzegoComposition
import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeDeBruijnNewman
import GaloisForLFunctions.RHTower.XiJensenHermiteIdentity
import GaloisForLFunctions.RHTower.LevinsonLittlewoodZeroCount

/-!
# The source-faithful Gamma ⊠ theta factorization of the shifted Jensen polynomials

The shifted Jensen coefficients of `Ξ` factor as `γ(n+j) = γ(n) · m(n+j)/m(n) · 1/(4^j (n+1/2)_j)`:
a theta moment ratio times a Gamma (Pochhammer) weight. In the multiplicative finite free
convolution this is an exact factorization

`J^{d,n} = (γ(n)/m(n)) · Γ_{n,d} ⊠_d Θ_{n,d}`,

with the Gamma piece `Γ_{n,d} = Σ_j C(d,j) X^j/(4^j (n+1/2)_j)` and the theta piece
`Θ_{n,d} = Σ_j C(d,j) m(n+j) X^j`, the Jensen polynomial of the theta moments.

**Theorem.** The theta piece is never real-rooted for `d ≥ 2`. Real-rootedness descends along the
Jensen ladder `(J^{d+1,n})' = (d+1) J^{d,n+1}` to the quadratic `J^{2,n+d-2}`, which would force the
Turán inequality `m(k+1)² ≥ m(k) m(k+2)`; but the theta moments are strictly log-convex,
`m(k) m(k+2) − m(k+1)² = m(k) ∫ x^{2k} Φ(x) (x² − c)² dx > 0`.

So Szegő's theorem never applies to the canonical source-faithful split: the reality of `J^{d,n}`
cannot come from the theta (Euler) side, only from the Gamma weights overpowering a strictly
positive theta dispersion.
-/

open Polynomial Filter Topology MeasureTheory
open GaloisForLFunctions.SignAlternation RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-! ## Theta moments as integrals over the line -/

theorem integrable_pow_mul_riemannKernel (k : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * k) * riemannKernelReal x) := by
  have h := (integrable_riemannKernel_mul_pow (2 * k)).norm
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_I,
    one_mul, abs_of_nonneg (riemannKernel_superExp.nonneg x)]
  rw [Even.pow_abs (even_two_mul k) x]; ring

theorem thetaCuspRawEvenMoment_eq_integral (k : ℕ) :
    thetaCuspRawEvenMoment k = ∫ x, x ^ (2 * k) * riemannKernelReal x := by
  rw [GaloisForLFunctions.HTGeometry.integral_even_eq_two_mul (integrable_pow_mul_riemannKernel k)
    (fun x => by rw [riemannKernel_superExp.even, Even.neg_pow (even_two_mul k)]),
    thetaCuspRawEvenMoment]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [thetaCuspFullSource_eq_riemannKernelReal]

/-- **Strict log-convexity of the theta moments.** -/
theorem thetaCuspRawEvenMoment_succ_sq_lt (k : ℕ) :
    thetaCuspRawEvenMoment (k + 1) ^ 2 < thetaCuspRawEvenMoment k * thetaCuspRawEvenMoment (k + 2) := by
  set M : ℕ → ℝ := fun j => ∫ x, x ^ (2 * j) * riemannKernelReal x
  have hM : ∀ j, thetaCuspRawEvenMoment j = M j := thetaCuspRawEvenMoment_eq_integral
  rw [hM, hM, hM]
  have hM0 : 0 < M k := by rw [← hM]; exact thetaCuspRawEvenMoment_pos k
  set c := M (k + 1) / M k
  set g : ℝ → ℝ := fun x => x ^ (2 * k) * riemannKernelReal x * (x ^ 2 - c) ^ 2
  have hint : ∀ j, Integrable (fun x : ℝ => x ^ (2 * j) * riemannKernelReal x) :=
    integrable_pow_mul_riemannKernel
  -- expand the variance integral
  have e : ∀ x, g x = x ^ (2 * (k + 2)) * riemannKernelReal x -
      2 * c * (x ^ (2 * (k + 1)) * riemannKernelReal x) + c ^ 2 * (x ^ (2 * k) *
        riemannKernelReal x) := fun x => by simp only [g]; ring
  have hexp : ∫ x, g x = M (k + 2) - 2 * c * M (k + 1) + c ^ 2 * M k := by
    simp_rw [e]
    have h1 : Integrable (fun x : ℝ => x ^ (2 * (k + 2)) * riemannKernelReal x -
        2 * c * (x ^ (2 * (k + 1)) * riemannKernelReal x)) := (hint _).sub ((hint _).const_mul _)
    have h2 : Integrable (fun x : ℝ => c ^ 2 * (x ^ (2 * k) * riemannKernelReal x)) :=
      (hint _).const_mul _
    have h3 : Integrable (fun x : ℝ => 2 * c * (x ^ (2 * (k + 1)) * riemannKernelReal x)) :=
      (hint _).const_mul _
    rw [integral_add h1 h2, integral_sub (hint _) h3, integral_const_mul, integral_const_mul]
  -- positivity of the variance integral
  have hcont : Continuous g := by
    simp only [g]
    exact ((continuous_pow _).mul riemannKernel_superExp.continuous).mul (by fun_prop)
  have hnonneg : ∀ x, 0 ≤ g x := fun x => by
    simp only [g]
    exact mul_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
      (riemannKernel_superExp.nonneg x)) (sq_nonneg _)
  set x₀ := Real.sqrt |c| + 1
  have hx₀ : 0 < x₀ := by positivity
  have hgx₀ : 0 < g x₀ := by
    have hsq : c < x₀ ^ 2 := by
      have h1 : Real.sqrt |c| ^ 2 = |c| := Real.sq_sqrt (abs_nonneg c)
      have h2 := le_abs_self c
      have h3 : 0 ≤ Real.sqrt |c| := Real.sqrt_nonneg _
      nlinarith
    simp only [g]
    exact mul_pos (mul_pos (pow_pos hx₀ _) (riemannKernelReal_pos x₀)) (by nlinarith)
  have hIpos : 0 < ∫ x in (x₀ - 1)..(x₀ + 1), g x :=
    intervalIntegral_pos_of_continuous_global_nonneg hcont hnonneg ⟨x₀, by constructor <;> linarith,
      hgx₀⟩
  have hgint : Integrable g :=
    (((hint _).sub ((hint _).const_mul _)).add ((hint _).const_mul _)).congr
      (Eventually.of_forall fun x => (e x).symm)
  have hle : ∫ x in (x₀ - 1)..(x₀ + 1), g x ≤ ∫ x, g x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral hgint (Eventually.of_forall hnonneg)
  have hpos : 0 < M (k + 2) - 2 * c * M (k + 1) + c ^ 2 * M k := by
    rw [← hexp]; exact hIpos.trans_le hle
  have hc : c * M k = M (k + 1) := div_mul_cancel₀ _ hM0.ne'
  nlinarith [hc, hpos, hM0]

/-! ## The Jensen ladder and the degree-two Turán obstruction -/

/-- Real-rootedness descends along the shifted Jensen ladder. -/
theorem splits_jensenPoly_succ_shift {a : ℕ → ℝ} {d n : ℕ}
    (h : (jensenPoly a (d + 1) n).Splits) : (jensenPoly a d (n + 1)).Splits := by
  have hder : (derivative (jensenPoly a (d + 1) n)).Splits := by
    have := GaloisForLFunctions.HTGeometry.splits_laguerreShift h 0
    simpa [GaloisForLFunctions.HTGeometry.laguerreShift] using this
  rw [derivative_jensenPoly] at hder
  exact (splits_mul_iff_right (C_ne_zero.2 (by positivity)) (Polynomial.Splits.C _)).1 hder

theorem splits_jensenPoly_shift_of_splits {a : ℕ → ℝ} (d : ℕ) :
    ∀ m n, (jensenPoly a (d + m) n).Splits → (jensenPoly a d (n + m)).Splits := by
  intro m
  induction m with
  | zero => intro n h; simpa using h
  | succ m ih =>
    intro n h
    have h1 : (jensenPoly a (d + m) (n + 1)).Splits :=
      splits_jensenPoly_succ_shift (by rwa [show d + m + 1 = d + (m + 1) by ring])
    have := ih (n + 1) h1
    rwa [show n + 1 + m = n + (m + 1) by ring] at this

theorem jensenPoly_two (a : ℕ → ℝ) (k : ℕ) :
    jensenPoly a 2 k = C (a (k + 2)) * X ^ 2 + C (2 * a (k + 1)) * X + C (a k) := by
  simp only [jensenPoly, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  norm_num [Nat.choose]
  ring

/-- **Turán obstruction.** A real-rooted quadratic Jensen polynomial with positive leading
coefficient forces `a(k) a(k+2) ≤ a(k+1)²`. -/
theorem turan_of_splits_jensenPoly_two {a : ℕ → ℝ} {k : ℕ} (ha : a (k + 2) ≠ 0)
    (h : (jensenPoly a 2 k).Splits) : a k * a (k + 2) ≤ a (k + 1) ^ 2 := by
  have hdeg : (jensenPoly a 2 k).degree ≠ 0 := by
    rw [jensenPoly_two, degree_quadratic ha]; decide
  obtain ⟨x, hx⟩ := h.exists_eval_eq_zero hdeg
  rw [jensenPoly_two] at hx
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hx
  have hq : a (k + 2) * (x * x) + 2 * a (k + 1) * x + a k = 0 := by linear_combination hx
  have hdisc := discrim_eq_sq_of_quadratic_eq_zero hq
  rw [discrim] at hdisc
  nlinarith [sq_nonneg (2 * a (k + 2) * x + 2 * a (k + 1))]

/-- **The theta piece is never real-rooted.** For every `d ≥ 2` and every shift `n`, the Jensen
polynomial of the theta moments has a non-real root. -/
theorem not_splits_jensenPoly_thetaMoment {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    ¬ (jensenPoly thetaCuspRawEvenMoment d n).Splits := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, d = 2 + m := ⟨d - 2, by omega⟩
  have h2 := splits_jensenPoly_shift_of_splits 2 m n h
  have ht := turan_of_splits_jensenPoly_two (thetaCuspRawEvenMoment_pos _).ne' h2
  have hs := thetaCuspRawEvenMoment_succ_sq_lt (n + m)
  linarith

/-! ## The factorization -/

/-- The Gamma piece `Γ_{n,d} = Σ_j C(d,j) X^j / (4^j (n+1/2)_j)`. -/
def gammaPiece (n d : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1),
    C ((d.choose j : ℝ) / (4 ^ j * ScaledHypergeometric.rising ((n : ℝ) + 1 / 2) j)) * X ^ j

theorem coeff_sum_range_C_mul_X_pow (f : ℕ → ℝ) {d k : ℕ} (hk : k ≤ d) :
    (∑ j ∈ Finset.range (d + 1), C (f j) * X ^ j).coeff k = f k := by
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; rw [coeff_C_mul_X_pow, if_neg (Ne.symm hj)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **The source-faithful factorization.** `J^{d,n} = (γ(n)/m(n)) · Γ_{n,d} ⊠_d Θ_{n,d}`. -/
theorem jensenPoly_xiJensenCoeff_eq_ffMul (d n : ℕ) :
    jensenPoly xiJensenCoeff d n = C (xiJensenCoeff n / thetaCuspRawEvenMoment n) *
      ffMul d (gammaPiece n d) (jensenPoly thetaCuspRawEvenMoment d n) := by
  rw [jensenPoly, ffMul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [gammaPiece, coeff_sum_range_C_mul_X_pow _ hk', jensenPoly,
    coeff_sum_range_C_mul_X_pow (fun j => (d.choose j : ℝ) * thetaCuspRawEvenMoment (n + j)) hk',
    ← mul_assoc, ← C_mul, xiJensenCoeff_add]
  congr 2
  have hm := thetaCuspRawEvenMoment_pos n
  have hr := ScaledHypergeometric.rising_pos (by positivity : 0 < (n : ℝ) + 1 / 2) k
  have hc : (d.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk').ne'
  field_simp

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.not_splits_jensenPoly_thetaMoment
#print axioms FiniteFreeProbability.jensenPoly_xiJensenCoeff_eq_ffMul
