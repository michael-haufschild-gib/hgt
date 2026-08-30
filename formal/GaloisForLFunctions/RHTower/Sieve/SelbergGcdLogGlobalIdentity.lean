import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogLocalIdentity

/-!
# The global gcd-logarithmic identity

`c·log(m,n) = corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫` for all `m, n`.

Both sides are Leibniz derivations of the original Selberg coefficient, so the local identity of
`SelbergGcdLogLocalIdentity` propagates by `BivariateDerivation.eq_of_prime_pow_eq`.
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- The zero function is a derivation of any bivariate multiplicative function. -/
theorem bivariateDerivation_zero (f : ℕ → ℕ → ℝ) :
    BivariateDerivation f (fun _ _ => 0) := by
  constructor
  · rfl
  · intro a b c d _
    ring

/-- On a pair-coprime splitting the diagonal support forces both components to be diagonal. -/
private theorem diag_pair_split {a b c d : ℕ}
    (h : Nat.Coprime (a * b) (c * d)) (hne : a * c = b * d) :
    a = b ∧ c = d := by
  have hac : Nat.Coprime a c :=
    (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_right c d)
  have had : Nat.Coprime a d :=
    (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_left d c)
  have hbc : Nat.Coprime b c :=
    (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_right c d)
  have hbd : Nat.Coprime b d :=
    (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_left d c)
  have hab : a ∣ b := by
    have hdvd : a ∣ b * d := ⟨c, by rw [← hne]⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right had hdvd)
  have hba : b ∣ a := by
    have hdvd : b ∣ a * c := ⟨d, by rw [hne]⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right hbc hdvd)
  have hab' : a = b := Nat.dvd_antisymm hab hba
  refine ⟨hab', ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb0 : b = 0 := hab'.symm
    subst hb0
    have hcd : Nat.Coprime 0 (c * d) := by simpa using h
    have : c * d = 1 := by simpa using hcd
    have hc1 : c = 1 := Nat.dvd_one.mp ⟨d, this.symm⟩
    have hd1 : d = 1 := Nat.dvd_one.mp ⟨c, by rw [Nat.mul_comm]; exact this.symm⟩
    rw [hc1, hd1]
  · have hpos : 0 < a := ha
    have : a * c = a * d := by rw [hne, hab']
    exact Nat.eq_of_mul_eq_mul_left hpos this

/-- **The logarithmic diagonal weight is a derivation of the reciprocal diagonal weight.** -/
theorem bivariateDerivation_selbergDiagonalLogReciprocalCoeff :
    BivariateDerivation selbergDiagonalReciprocalCoeff
      selbergDiagonalLogReciprocalCoeff := by
  constructor
  · rw [selbergDiagonalLogReciprocalCoeff, if_pos rfl]
    simp
  · intro a b c d h
    rw [selbergDiagonalLogReciprocalCoeff, selbergDiagonalLogReciprocalCoeff,
      selbergDiagonalLogReciprocalCoeff, selbergDiagonalReciprocalCoeff,
      selbergDiagonalReciprocalCoeff]
    by_cases hne : a * c = b * d
    · obtain ⟨hab, hcd⟩ := diag_pair_split h hne
      subst hab
      subst hcd
      rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp
      have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
      rw [reciprocalNatArithmetic_apply (by exact_mod_cast hc.ne'),
        reciprocalNatArithmetic_apply (by exact_mod_cast ha.ne')]
      push_cast
      rw [Real.log_mul haR.ne' hcR.ne']
      field_simp
    · rw [if_neg hne]
      by_cases hab : a = b
      · by_cases hcd : c = d
        · exact absurd (by rw [hab, hcd]) hne
        · rw [if_neg hcd, if_neg hcd]
          ring
      · rw [if_neg hab, if_neg hab]
        ring

/-- **`𝒫^{log}` is a derivation of the principal Selberg coefficient.** -/
theorem bivariateDerivation_selbergGcdLogPrincipalCoeff :
    BivariateDerivation selbergPrincipalCoeff selbergGcdLogPrincipalCoeff := by
  have hconv := BivariateDerivation.convolution
    bivariateMultiplicative_selbergDiagonalReciprocalCoeff
    bivariateMultiplicative_selbergMoebiusReciprocalPair
    bivariateDerivation_selbergDiagonalLogReciprocalCoeff
    (bivariateDerivation_zero selbergMoebiusReciprocalPair)
  have hzero : bivariateDirichletConvolution selbergDiagonalReciprocalCoeff
      (fun _ _ => (0 : ℝ)) = fun _ _ => 0 := by
    funext m n
    rw [bivariateDirichletConvolution]
    split_ifs with h
    · rfl
    · apply Finset.sum_eq_zero
      intro z _
      ring
  have hfun : (fun m n => bivariateDirichletConvolution
      selbergDiagonalLogReciprocalCoeff selbergMoebiusReciprocalPair m n +
      bivariateDirichletConvolution selbergDiagonalReciprocalCoeff
        (fun _ _ => (0 : ℝ)) m n) = selbergGcdLogPrincipalCoeff := by
    rw [hzero]
    funext m n
    rw [selbergGcdLogPrincipalCoeff]
    ring
  rw [hfun] at hconv
  rw [← selbergPrincipalCoeff] at hconv
  exact hconv

/-- The right-hand side of the gcd-logarithmic identity is a derivation of `c`. -/
theorem bivariateDerivation_gcdLogRightSide :
    BivariateDerivation selbergOriginalCoeff
      (fun m n => bivariateDirichletConvolution selbergEulerCorrectionLogCoeff
          selbergPrincipalCoeff m n +
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergGcdLogPrincipalCoeff m n) := by
  have hconv := BivariateDerivation.convolution
    bivariateMultiplicative_selbergEulerCorrectionCoeff
    bivariateMultiplicative_selbergPrincipalCoeff
    bivariateDerivation_selbergEulerCorrectionLogCoeff
    bivariateDerivation_selbergGcdLogPrincipalCoeff
  have hbase : bivariateDirichletConvolution selbergEulerCorrectionCoeff
      selbergPrincipalCoeff = selbergOriginalCoeff := by
    funext m n
    exact selbergEulerCorrection_convolution_principal m n
  rw [hbase] at hconv
  exact hconv

/-- **The global gcd-logarithmic identity.** -/
theorem selbergOriginalGcdLogCoeff_eq_convolution_sum
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    selbergOriginalGcdLogCoeff m n =
      bivariateDirichletConvolution selbergEulerCorrectionLogCoeff
          selbergPrincipalCoeff m n +
        bivariateDirichletConvolution selbergEulerCorrectionCoeff
          selbergGcdLogPrincipalCoeff m n := by
  refine BivariateDerivation.eq_of_prime_pow_eq
    bivariateDerivation_selbergOriginalGcdLogCoeff
    bivariateDerivation_gcdLogRightSide ?_ hm hn
  intro p hp i j
  have hlocal := congrFun (congrFun
    (additiveBivariateConvolution_localGcdLog_identity hp) i) j
  rw [bivariateDirichletConvolution_prime_pow _ _ hp,
    bivariateDirichletConvolution_prime_pow _ _ hp]
  have hcorrLog : (fun a b => selbergEulerCorrectionLogCoeff (p ^ a) (p ^ b)) =
      selbergCorrectionLogLocal p := by
    funext a b
    exact selbergEulerCorrectionLogCoeff_prime_pow hp a b
  have hprin : (fun a b => selbergPrincipalCoeff (p ^ a) (p ^ b)) =
      selbergLocalPrincipal p := rfl
  have hcorr : (fun a b => selbergEulerCorrectionCoeff (p ^ a) (p ^ b)) =
      selbergLocalCorrection p := rfl
  have hprinLog : (fun a b => selbergGcdLogPrincipalCoeff (p ^ a) (p ^ b)) =
      selbergLocalGcdLogPrincipal p := rfl
  rw [hcorrLog, hprin, hcorr, hprinLog]
  have hleft : selbergOriginalGcdLogCoeff (p ^ i) (p ^ j) =
      selbergLocalOriginalGcdLog p i j := rfl
  rw [hleft, ← hlocal]
  ring

end

end RHTower.Sieve
