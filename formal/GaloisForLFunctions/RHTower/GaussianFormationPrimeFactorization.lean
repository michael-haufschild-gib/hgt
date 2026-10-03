import GaloisForLFunctions.RHTower.GaussianEulerContinuumRelativeFormation
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# Prime factorization of the Gaussian formation phase

The Gaussian Euler logarithm `Lₓ(s) = ∑_{n ≥ 2} (Λ(n)/log n) e^{-πxn²} n^{-s}` is supported on
prime powers, so it is the convergent sum of the prime-local logarithms

`ℓ_{x,p}(s) = ∑_{k ≥ 1} (1/k) e^{-πx p^{2k}} p^{-ks}`,

and `exp(Lₓ) = ∏_p exp(ℓ_{x,p})`.  The normalized boundary phase of `Φₓ = h_∞ exp(Lₓ + Aₓ)` is

`Φₓ/|Φₓ| = (h_∞/|h_∞|) · exp(i Im Aₓ) · ∏_p exp(i Im ℓ_{x,p})`,

a single phase built from the complete prime sum.  Its displacement-kernel numerator
`\overline{u(z)} u(w) - 1` expands, for any finite set of prime-local factors, into the sum over
nonempty prime sets `S` of the products `∏_{p ∈ S} (\overline{u_p(z)} u_p(w) - 1)`: the kernel
carries mixed monomials from distinct primes before any Hardy compression.
-/

noncomputable section

open Complex Filter Topology Set

namespace RHTower

/-- The prime power `p^{k+1}` as a Gaussian index. -/
def gaussianPrimePowerIndex (z : Nat.Primes × ℕ) : GaussianEulerIndex :=
  ⟨eulerPrimePowerNat z, by
    have h : 2 ≤ z.1.1 := z.1.2.two_le
    calc 2 ≤ z.1.1 := h
      _ ≤ z.1.1 ^ (z.2 + 1) := Nat.le_self_pow (by omega) _⟩

theorem gaussianPrimePowerIndex_injective : Function.Injective gaussianPrimePowerIndex :=
  fun _ _ h => eulerPrimePowerNat_injective (congrArg Subtype.val h)

/-- The Dirichlet terms of the Gaussian Euler logarithm are absolutely summable. -/
theorem summable_norm_gaussianEulerTerm {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Summable fun n : GaussianEulerIndex => ‖gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-s)‖ := by
  have hraw := GaloisForLFunctions.HTGeometry.summable_rpow_mul_exp_neg_rpow
    (A := |s.re|) (c := Real.pi * x) (e := 2) (mul_pos Real.pi_pos hx) (by norm_num)
  have hbase := hraw.subtype (fun n : ℕ => 2 ≤ n)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hbase
  have hn1 : (1 : ℝ) ≤ n.1 := by exact_mod_cast le_trans (by norm_num) n.2
  change _ ≤ (n.1 : ℝ) ^ |s.re| * Real.exp (-(Real.pi * x * (n.1 : ℝ) ^ (2 : ℝ)))
  rw [norm_mul, gaussianEulerAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), show ((n.1 : ℕ) : ℂ) = ((n.1 : ℝ) : ℂ) from
      (Complex.ofReal_natCast _).symm,
    GaloisForLFunctions.norm_cpow_neg_eq_rpow_re (n.1 : ℝ) (by linarith) s]
  rw [Real.rpow_two]
  have hc := norm_eulerLogDirichletCoeff_le_one n.1
  have hr : (n.1 : ℝ) ^ (-s.re) ≤ (n.1 : ℝ) ^ |s.re| :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_abs _)
  have he : Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) =
      Real.exp (-(Real.pi * x * (n.1 : ℝ) ^ 2)) := by ring_nf
  rw [he]
  calc ‖eulerLogDirichletCoeff n.1‖ * Real.exp (-(Real.pi * x * (n.1 : ℝ) ^ 2)) *
        (n.1 : ℝ) ^ (-s.re)
      ≤ 1 * Real.exp (-(Real.pi * x * (n.1 : ℝ) ^ 2)) * (n.1 : ℝ) ^ |s.re| := by
        gcongr
    _ = _ := by ring

/-- `Lₓ(s)` is the sum of its prime-power terms. -/
theorem hasSum_gaussianEulerLog_primePowers {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasSum (fun z : Nat.Primes × ℕ => gaussianEulerAmplitude x (gaussianPrimePowerIndex z) *
      ((gaussianPrimePowerIndex z).1 : ℂ) ^ (-s)) (gaussianEulerLog x s) := by
  have hs := (summable_norm_gaussianEulerTerm hx s).of_norm
  have hsum : HasSum (fun n : GaussianEulerIndex => gaussianEulerAmplitude x n * (n.1 : ℂ) ^ (-s))
      (gaussianEulerLog x s) := by
    rw [gaussianEulerLog_eq_tsum_cpow]; exact hs.hasSum
  refine (gaussianPrimePowerIndex_injective.hasSum_iff fun n hn => ?_).2 hsum
  by_cases hpp : IsPrimePow n.1
  · exfalso
    obtain ⟨q, k, hq, hk, hqk⟩ := hpp
    apply hn
    refine ⟨(⟨q, Nat.prime_iff.mpr hq⟩, k - 1), Subtype.ext ?_⟩
    change q ^ (k - 1 + 1) = n.1
    rw [Nat.sub_add_cancel hk, hqk]
  · rw [gaussianEulerAmplitude, eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
    simp

/-- Prime-local Gaussian logarithm `ℓ_{x,p}(s) = ∑_{k ≥ 1} (1/k) e^{-πx p^{2k}} p^{-ks}`. -/
def gaussianPrimeLocalLog (x : ℝ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑' k : ℕ, gaussianEulerAmplitude x (gaussianPrimePowerIndex (p, k)) *
    ((gaussianPrimePowerIndex (p, k)).1 : ℂ) ^ (-s)

/-- **Prime factorization of the Euler logarithm**: `Lₓ(s) = ∑_p ℓ_{x,p}(s)`. -/
theorem hasSum_gaussianPrimeLocalLog {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasSum (fun p : Nat.Primes => gaussianPrimeLocalLog x p s) (gaussianEulerLog x s) := by
  have h := hasSum_gaussianEulerLog_primePowers hx s
  exact h.prod_fiberwise fun p => (h.summable.prod_factor p).hasSum

/-- `exp(Lₓ(s)) = ∏_p exp(ℓ_{x,p}(s))`. -/
theorem hasProd_exp_gaussianPrimeLocalLog {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasProd (fun p : Nat.Primes => Complex.exp (gaussianPrimeLocalLog x p s))
      (Complex.exp (gaussianEulerLog x s)) :=
  (hasSum_gaussianPrimeLocalLog hx s).cexp

/-- **Phase of the formation.**  `Φₓ/|Φₓ| = (h_∞/|h_∞|) · exp(i Im Aₓ) · exp(i Im Lₓ)`. -/
theorem gaussianEulerContinuumFormation_div_norm (x : ℝ) {s : ℂ} (hs : 0 < s.re) :
    gaussianEulerContinuumFormation x s / (‖gaussianEulerContinuumFormation x s‖ : ℂ) =
      gaussianArchimedeanHalfFactor s / (‖gaussianArchimedeanHalfFactor s‖ : ℂ) *
        Complex.exp (I * ((gaussianContinuumPrimitive x s).im : ℂ)) *
          Complex.exp (I * ((gaussianEulerLog x s).im : ℂ)) := by
  have hh := gaussianArchimedeanHalfFactor_ne_zero hs
  have hhn : (‖gaussianArchimedeanHalfFactor s‖ : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (norm_ne_zero_iff.2 hh)
  set w := gaussianRelativePotential x s
  have hsplit : Complex.exp w = (Real.exp w.re : ℂ) * Complex.exp (I * (w.im : ℂ)) := by
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [mul_comm I]
    exact (Complex.re_add_im w).symm
  have hnorm : (‖gaussianEulerContinuumFormation x s‖ : ℂ) =
      (‖gaussianArchimedeanHalfFactor s‖ : ℂ) * (Real.exp w.re : ℂ) := by
    rw [gaussianEulerContinuumFormation, norm_mul, Complex.norm_exp]
    push_cast
    rfl
  have hwim : w.im = (gaussianContinuumPrimitive x s).im + (gaussianEulerLog x s).im := by
    simp only [w, gaussianRelativePotential, add_im]
    ring
  rw [hnorm, gaussianEulerContinuumFormation, ← show Complex.exp w = Complex.exp
    (gaussianRelativePotential x s) from rfl, hsplit, hwim, ofReal_add, mul_add,
    Complex.exp_add]
  have hexp : (Real.exp w.re : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.exp_pos _).ne'
  field_simp

/-- **Prime factorization of the formation phase**: `exp(i Im Lₓ(s)) = ∏_p exp(i Im ℓ_{x,p}(s))`. -/
theorem hasProd_exp_im_gaussianPrimeLocalLog {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasProd (fun p : Nat.Primes => Complex.exp (I * ((gaussianPrimeLocalLog x p s).im : ℂ)))
      (Complex.exp (I * ((gaussianEulerLog x s).im : ℂ))) := by
  have him := (hasSum_gaussianPrimeLocalLog hx s).mapL Complex.imCLM
  have hof := him.mapL Complex.ofRealCLM
  have hI := hof.mul_left I
  exact hI.cexp

/-- **Mixed monomials in the kernel numerator.**  For finitely many factors,
`\overline{∏ v_p} ∏ w_p - 1 = ∑_{∅ ≠ S} ∏_{p ∈ S} (\overline{v_p} w_p - 1)`. -/
theorem conj_prod_mul_prod_sub_one {ι : Type*} [DecidableEq ι] (F : Finset ι) (v w : ι → ℂ) :
    starRingEnd ℂ (∏ p ∈ F, v p) * ∏ p ∈ F, w p - 1 =
      ∑ S ∈ F.powerset.erase ∅, ∏ p ∈ S, (starRingEnd ℂ (v p) * w p - 1) := by
  have h := Finset.prod_one_add (f := fun p => starRingEnd ℂ (v p) * w p - 1) F
  simp only [add_sub_cancel] at h
  rw [map_prod, ← Finset.prod_mul_distrib, h, ← Finset.sum_erase_add _ _ (Finset.empty_mem_powerset F),
    Finset.prod_empty, add_sub_cancel_right]

end RHTower
