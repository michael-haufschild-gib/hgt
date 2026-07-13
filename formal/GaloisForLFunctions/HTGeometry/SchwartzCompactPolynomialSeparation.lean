import GaloisForLFunctions.HTGeometry.SchwartzSpectralQuadraticSeparation
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UrysohnsLemma

/-!
# Compact polynomial spectral separation

Two disjoint compact real packets can be separated by one polynomial.  Applying the positive
polynomial `(1 + P²) / 2` to the spectral momentum gives a globally invertible symmetric Schwartz
multiplier whose powers contract the first packet and whose inverse powers contract the second.
This removes any interval or finite-partition hypothesis from spectral locality.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial

noncomputable section

namespace SchwartzMap

/-! ## Polynomial separation of compact packets -/

/-- Urysohn separation followed by Weierstrass approximation: one real polynomial is uniformly
near zero on the first compact set and uniformly near two on the second. -/
theorem exists_polynomial_zero_two_separating_compacts
    {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L) :
    ∃ P : ℝ[X],
      (∀ x ∈ K, |P.eval x| < (1 : ℝ) / 4) ∧
      (∀ x ∈ L, |P.eval x - 2| < (1 : ℝ) / 4) := by
  obtain ⟨u, huK, huL, _hu01⟩ :=
    exists_continuous_zero_one_of_isClosed hK.isClosed hL.isClosed hKL
  obtain ⟨R, hR⟩ := (hK.union hL).isBounded.exists_norm_le
  let T : ℝ := max R 0
  have hsub : K ∪ L ⊆ Icc (-T) T := by
    intro x hx
    have hxR : |x| ≤ R := by simpa [Real.norm_eq_abs] using hR x hx
    have hxT : |x| ≤ T := hxR.trans (le_max_left _ _)
    exact ⟨neg_le_of_abs_le hxT, le_of_abs_le hxT⟩
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn
    (-T) T (fun x => 2 * u x) (continuous_const.mul u.continuous).continuousOn
    ((1 : ℝ) / 4) (by norm_num)
  refine ⟨P, ?_, ?_⟩
  · intro x hx
    have hnear := hP x (hsub (Or.inl hx))
    rw [huK hx] at hnear
    simpa using hnear
  · intro x hx
    have hnear := hP x (hsub (Or.inr hx))
    rw [huL hx] at hnear
    norm_num at hnear
    exact hnear

/-! ## Polynomial functional calculus for spectral momentum -/

/-- Real polynomial functional calculus of the spectral momentum multiplier `2πt`. -/
def polynomialSpectralMomentumCLM (P : ℝ[X]) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  Polynomial.eval₂
    (algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ))
    spectralMomentumCLM P

theorem spectralMomentumCLM_pow_apply_pointwise
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (spectralMomentumCLM ^ n) f t = spectralMomentumMultiplier t ^ n * f t := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih, spectralMomentumCLM_apply]
      ring

@[simp] theorem polynomialSpectralMomentumCLM_apply
    (P : ℝ[X]) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    polynomialSpectralMomentumCLM P f t =
      ((P.eval (2 * Real.pi * t) : ℝ) : ℂ) * f t := by
  rw [polynomialSpectralMomentumCLM, Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  rw [ContinuousLinearMap.sum_apply]
  have heval :
      (∑ d ∈ P.support,
        ((algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)) (P.coeff d) *
          spectralMomentumCLM ^ d) f) t =
      ∑ d ∈ P.support,
        (((algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)) (P.coeff d) *
          spectralMomentumCLM ^ d) f) t := by
    induction P.support using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha]
  rw [heval]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _hn
  change ((algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)) (P.coeff n)
      (((⇑spectralMomentumCLM)^[n]) f)) t = _
  simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  change (P.coeff n : ℂ) * (((⇑spectralMomentumCLM)^[n]) f) t = _
  rw [show (((⇑spectralMomentumCLM)^[n]) f) t =
      spectralMomentumMultiplier t ^ n * f t by
        simpa using spectralMomentumCLM_pow_apply_pointwise n f t]
  simp [spectralMomentumMultiplier]
  ring

/-- Every real polynomial in spectral momentum is symmetric for the Fourier pullback of a
momentum-symmetric form. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_polynomialSpectralMomentum_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (P : ℝ[X]) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback (polynomialSpectralMomentumCLM P f) g =
      Q.fourierPullback f (polynomialSpectralMomentumCLM P g) := by
  have hterm (n : ℕ) (c : ℝ) (u v : SchwartzMap ℝ ℂ) :
      Q.fourierPullback
          (((algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)) c *
            spectralMomentumCLM ^ n) u) v =
        Q.fourierPullback u
          (((algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)) c *
            spectralMomentumCLM ^ n) v) := by
    change Q.fourierPullback (c • ((spectralMomentumCLM ^ n) u)) v =
      Q.fourierPullback u (c • ((spectralMomentumCLM ^ n) v))
    rw [Q.fourierPullback.apply_real_smul_left,
      Q.fourierPullback.apply_real_smul_right]
    congr 1
    exact Q.fourierPullback_spectralMomentum_pow_symmetric hQ n u v
  rw [polynomialSpectralMomentumCLM, Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum]
  let A : ℕ → (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ) := fun n =>
    (algebraMap ℝ (SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)) (P.coeff n) *
      spectralMomentumCLM ^ n
  have hs (s : Finset ℕ) :
      Q.fourierPullback ((∑ n ∈ s, A n) f) g =
        Q.fourierPullback f ((∑ n ∈ s, A n) g) := by
    induction s using Finset.induction_on with
    | empty =>
        have hzL : Q.fourierPullback (0 : SchwartzMap ℝ ℂ) g = 0 := by
          simpa using Q.fourierPullback.apply_smul_left 0 0 g
        have hzR : Q.fourierPullback f (0 : SchwartzMap ℝ ℂ) = 0 := by
          simpa using Q.fourierPullback.apply_smul_right 0 f 0
        exact hzL.trans hzR.symm
    | @insert n s hn ih =>
        simp only [Finset.sum_insert hn, ContinuousLinearMap.add_apply,
          Q.fourierPullback.apply_add_left, Q.fourierPullback.apply_add_right]
        rw [hterm n (P.coeff n), ih]
  exact hs P.support

/-! ## Positive polynomial separator and reciprocal -/

/-- Positive polynomial separator multiplier `(1 + P(2πt)²) / 2`. -/
def positivePolynomialSpectralSeparatorMultiplier (P : ℝ[X]) (t : ℝ) : ℝ :=
  (1 + (P.eval (2 * Real.pi * t)) ^ 2) / 2

/-- Its everywhere-defined reciprocal. -/
def inversePositivePolynomialSpectralSeparatorMultiplier (P : ℝ[X]) (t : ℝ) : ℝ :=
  2 / (1 + (P.eval (2 * Real.pi * t)) ^ 2)

theorem polynomialMomentum_hasTemperateGrowth (P : ℝ[X]) :
    Function.HasTemperateGrowth (fun t : ℝ => P.eval (2 * Real.pi * t)) := by
  have hx : Function.HasTemperateGrowth (fun t : ℝ => 2 * Real.pi * t) := by
    fun_prop
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa using hP.add hQ
  | monomial n a =>
      simpa [Polynomial.eval_monomial] using
        (Function.HasTemperateGrowth.const a).mul (hx.pow n)

theorem positivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth (P : ℝ[X]) :
    Function.HasTemperateGrowth (positivePolynomialSpectralSeparatorMultiplier P) := by
  have hP := polynomialMomentum_hasTemperateGrowth P
  have hone : Function.HasTemperateGrowth (fun _t : ℝ => (1 : ℝ)) := by fun_prop
  have hhalf : Function.HasTemperateGrowth (fun _t : ℝ => ((2 : ℝ)⁻¹)) := by fun_prop
  simpa [positivePolynomialSpectralSeparatorMultiplier, div_eq_mul_inv] using
    (hone.add (hP.pow 2)).mul hhalf

theorem inversePositivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth (P : ℝ[X]) :
    Function.HasTemperateGrowth (inversePositivePolynomialSpectralSeparatorMultiplier P) := by
  have hP := polynomialMomentum_hasTemperateGrowth P
  have hbase := (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1)).comp hP
  have hconst : Function.HasTemperateGrowth (fun _t : ℝ => (2 : ℝ)) := by fun_prop
  have hmul := hconst.mul hbase
  simpa [inversePositivePolynomialSpectralSeparatorMultiplier, Function.comp_apply,
    Real.norm_eq_abs, sq_abs, Real.rpow_neg_one, div_eq_mul_inv] using hmul

/-- Continuous Schwartz multiplier by the positive polynomial separator. -/
def positivePolynomialSpectralSeparatorCLM (P : ℝ[X]) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun t => (positivePolynomialSpectralSeparatorMultiplier P t : ℂ))

/-- Continuous Schwartz multiplier by the reciprocal separator. -/
def inversePositivePolynomialSpectralSeparatorCLM (P : ℝ[X]) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun t => (inversePositivePolynomialSpectralSeparatorMultiplier P t : ℂ))

@[simp] theorem positivePolynomialSpectralSeparatorCLM_apply
    (P : ℝ[X]) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    positivePolynomialSpectralSeparatorCLM P f t =
      (positivePolynomialSpectralSeparatorMultiplier P t : ℂ) * f t := by
  unfold positivePolynomialSpectralSeparatorCLM
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rfl
  · exact Complex.ofRealCLM.hasTemperateGrowth.comp
      (positivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth P)

@[simp] theorem inversePositivePolynomialSpectralSeparatorCLM_apply
    (P : ℝ[X]) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    inversePositivePolynomialSpectralSeparatorCLM P f t =
      (inversePositivePolynomialSpectralSeparatorMultiplier P t : ℂ) * f t := by
  unfold inversePositivePolynomialSpectralSeparatorCLM
  rw [SchwartzMap.smulLeftCLM_apply_apply]
  · rfl
  · exact Complex.ofRealCLM.hasTemperateGrowth.comp
      (inversePositivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth P)

/-- The polynomial whose momentum functional calculus is the positive separator. -/
def positiveSeparatorPolynomial (P : ℝ[X]) : ℝ[X] :=
  Polynomial.C ((2 : ℝ)⁻¹) * (Polynomial.C 1 + P ^ 2)

theorem positivePolynomialSpectralSeparatorCLM_eq_polynomialSpectralMomentumCLM
    (P : ℝ[X]) :
    positivePolynomialSpectralSeparatorCLM P =
      polynomialSpectralMomentumCLM (positiveSeparatorPolynomial P) := by
  ext f t
  rw [positivePolynomialSpectralSeparatorCLM_apply,
    polynomialSpectralMomentumCLM_apply]
  simp [positivePolynomialSpectralSeparatorMultiplier, positiveSeparatorPolynomial]
  ring_nf
  simp

/-- The globally positive polynomial separator is symmetric for every momentum-symmetric
Fourier-pullback form. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_positivePolynomialSeparator_symmetric
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (P : ℝ[X]) (f g : SchwartzMap ℝ ℂ) :
    Q.fourierPullback (positivePolynomialSpectralSeparatorCLM P f) g =
      Q.fourierPullback f (positivePolynomialSpectralSeparatorCLM P g) := by
  rw [positivePolynomialSpectralSeparatorCLM_eq_polynomialSpectralMomentumCLM]
  exact Q.fourierPullback_polynomialSpectralMomentum_symmetric hQ
    (positiveSeparatorPolynomial P) f g

/-- Powers of a real temperate scalar multiplier act pointwise by scalar powers. -/
theorem smulLeftCLM_ofReal_pow_apply
    (m : ℝ → ℝ) (hm : Function.HasTemperateGrowth m)
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (SchwartzMap.smulLeftCLM ℂ (fun x => (m x : ℂ)) ^ n) f t =
      (m t : ℂ) ^ n * f t := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, ih,
        SchwartzMap.smulLeftCLM_apply_apply]
      · ring
      · exact Complex.ofRealCLM.hasTemperateGrowth.comp hm

theorem positivePolynomialSpectralSeparatorCLM_pow_apply
    (P : ℝ[X]) (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (positivePolynomialSpectralSeparatorCLM P ^ n) f t =
      (positivePolynomialSpectralSeparatorMultiplier P t : ℂ) ^ n * f t := by
  exact smulLeftCLM_ofReal_pow_apply
    (positivePolynomialSpectralSeparatorMultiplier P)
    (positivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth P) n f t

theorem inversePositivePolynomialSpectralSeparatorCLM_pow_apply
    (P : ℝ[X]) (n : ℕ) (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (inversePositivePolynomialSpectralSeparatorCLM P ^ n) f t =
      (inversePositivePolynomialSpectralSeparatorMultiplier P t : ℂ) ^ n * f t := by
  exact smulLeftCLM_ofReal_pow_apply
    (inversePositivePolynomialSpectralSeparatorMultiplier P)
    (inversePositivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth P) n f t

theorem positivePolynomialSeparator_mul_inverse (P : ℝ[X]) (t : ℝ) :
    positivePolynomialSpectralSeparatorMultiplier P t *
      inversePositivePolynomialSpectralSeparatorMultiplier P t = 1 := by
  unfold positivePolynomialSpectralSeparatorMultiplier
    inversePositivePolynomialSpectralSeparatorMultiplier
  have hden : 1 + P.eval (2 * Real.pi * t) ^ 2 ≠ 0 := by positivity
  field_simp

/-- Reciprocal powers give an exact inverse factor for positive polynomial separator powers. -/
theorem positivePolynomialSeparator_pow_inverse_factor
    (P : ℝ[X]) (n : ℕ) (g : SchwartzMap ℝ ℂ) :
    (positivePolynomialSpectralSeparatorCLM P ^ n)
      ((inversePositivePolynomialSpectralSeparatorCLM P ^ n) g) = g := by
  ext t
  rw [positivePolynomialSpectralSeparatorCLM_pow_apply,
    inversePositivePolynomialSpectralSeparatorCLM_pow_apply]
  rw [← mul_assoc, ← mul_pow]
  have hab :
      (positivePolynomialSpectralSeparatorMultiplier P t : ℂ) *
        inversePositivePolynomialSpectralSeparatorMultiplier P t = 1 := by
    exact_mod_cast positivePolynomialSeparator_mul_inverse P t
  rw [hab, one_pow, one_mul]

theorem positivePolynomialSeparator_le_seventeen_thirtyTwo
    {P : ℝ[X]} {x : ℝ} (hx : |P.eval x| < (1 : ℝ) / 4) :
    (1 + (P.eval x) ^ 2) / 2 ≤ (17 : ℝ) / 32 := by
  have habs := (abs_lt.mp hx)
  have hsquare : (P.eval x) ^ 2 < (1 : ℝ) / 16 := by nlinarith
  linarith

theorem inversePositivePolynomialSeparator_le_thirtyTwo_sixtyFive
    {P : ℝ[X]} {x : ℝ} (hx : |P.eval x - 2| < (1 : ℝ) / 4) :
    2 / (1 + (P.eval x) ^ 2) ≤ (32 : ℝ) / 65 := by
  have habs := (abs_lt.mp hx)
  have hlower : (7 : ℝ) / 4 < P.eval x := by linarith
  have hden : 0 < 1 + (P.eval x) ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-- Direct powers contract a compact packet on which `P` is uniformly within `1/4` of zero. -/
theorem tendsto_positivePolynomialSpectralSeparator_pow_zero_of_compact_packet
    {K : Set ℝ} {P : ℝ[X]} (hP : ∀ x ∈ K, |P.eval x| < (1 : ℝ) / 4)
    (f : SchwartzMap ℝ ℂ) (hfCompact : IsCompact (tsupport f))
    (hfK : ∀ t ∈ tsupport f, 2 * Real.pi * t ∈ K) :
    Tendsto (fun n : ℕ => (positivePolynomialSpectralSeparatorCLM P ^ n) f)
      atTop (nhds 0) := by
  obtain ⟨T, hT, hbound⟩ := hfCompact.isBounded.exists_pos_norm_le
  have hsupp : tsupport f ⊆ {t : ℝ | |t| ≤ T} := by
    intro t ht
    simpa [Real.norm_eq_abs] using hbound t ht
  have hpacket : ∀ t ∈ tsupport f,
      0 ≤ positivePolynomialSpectralSeparatorMultiplier P t ∧
        positivePolynomialSpectralSeparatorMultiplier P t ≤ (17 : ℝ) / 32 := by
    intro t ht
    constructor
    · unfold positivePolynomialSpectralSeparatorMultiplier
      positivity
    · exact positivePolynomialSeparator_le_seventeen_thirtyTwo (hP _ (hfK t ht))
  simpa only [positivePolynomialSpectralSeparatorCLM] using
    tendsto_smulLeftCLM_pow_zero_of_compact_packet
      (positivePolynomialSpectralSeparatorMultiplier P)
      (positivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth P)
      f hT.le (by norm_num) (by norm_num) hsupp hpacket

/-- Reciprocal powers contract a compact packet on which `P` is uniformly within `1/4` of two. -/
theorem tendsto_inversePositivePolynomialSpectralSeparator_pow_zero_of_compact_packet
    {L : Set ℝ} {P : ℝ[X]} (hP : ∀ x ∈ L, |P.eval x - 2| < (1 : ℝ) / 4)
    (g : SchwartzMap ℝ ℂ) (hgCompact : IsCompact (tsupport g))
    (hgL : ∀ t ∈ tsupport g, 2 * Real.pi * t ∈ L) :
    Tendsto (fun n : ℕ => (inversePositivePolynomialSpectralSeparatorCLM P ^ n) g)
      atTop (nhds 0) := by
  obtain ⟨T, hT, hbound⟩ := hgCompact.isBounded.exists_pos_norm_le
  have hsupp : tsupport g ⊆ {t : ℝ | |t| ≤ T} := by
    intro t ht
    simpa [Real.norm_eq_abs] using hbound t ht
  have hpacket : ∀ t ∈ tsupport g,
      0 ≤ inversePositivePolynomialSpectralSeparatorMultiplier P t ∧
        inversePositivePolynomialSpectralSeparatorMultiplier P t ≤ (32 : ℝ) / 65 := by
    intro t ht
    constructor
    · unfold inversePositivePolynomialSpectralSeparatorMultiplier
      positivity
    · exact inversePositivePolynomialSeparator_le_thirtyTwo_sixtyFive (hP _ (hgL t ht))
  simpa only [inversePositivePolynomialSpectralSeparatorCLM] using
    tendsto_smulLeftCLM_pow_zero_of_compact_packet
      (inversePositivePolynomialSpectralSeparatorMultiplier P)
      (inversePositivePolynomialSpectralSeparatorMultiplier_hasTemperateGrowth P)
      g hT.le (by norm_num) (by norm_num) hsupp hpacket

/-! ## Arbitrary compact spectral locality -/

/-- **Compact polynomial spectral locality.** Momentum symmetry makes any two Schwartz maps with
disjoint compact spectral supports orthogonal for the Fourier-pullback form.  No interval geometry
or kernel representation is assumed. -/
theorem ContinuousSchwartzSesquilinearForm.fourierPullback_eq_zero_of_disjoint_compact_tsupport
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (f g : SchwartzMap ℝ ℂ)
    (hfCompact : IsCompact (tsupport f)) (hgCompact : IsCompact (tsupport g))
    (hfg : Disjoint (tsupport f) (tsupport g)) :
    Q.fourierPullback f g = 0 := by
  let c : ℝ → ℝ := fun t => 2 * Real.pi * t
  let K : Set ℝ := c '' tsupport f
  let L : Set ℝ := c '' tsupport g
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hcInjective : Function.Injective c := by
    intro x y hxy
    dsimp [c] at hxy
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    nlinarith
  have hK : IsCompact K := hfCompact.image hc
  have hL : IsCompact L := hgCompact.image hc
  have hKL : Disjoint K L := Set.disjoint_image_of_injective hcInjective hfg
  obtain ⟨P, hPK, hPL⟩ := exists_polynomial_zero_two_separating_compacts hK hL hKL
  apply Q.fourierPullback_eq_zero_of_clmPower_separation
    (positivePolynomialSpectralSeparatorCLM P)
    (Q.fourierPullback_positivePolynomialSeparator_symmetric hQ P)
    f g (fun n => (inversePositivePolynomialSpectralSeparatorCLM P ^ n) g)
  · intro n
    exact positivePolynomialSeparator_pow_inverse_factor P n g
  · exact tendsto_positivePolynomialSpectralSeparator_pow_zero_of_compact_packet
      hPK f hfCompact (fun t ht => mem_image_of_mem c ht)
  · exact tendsto_inversePositivePolynomialSpectralSeparator_pow_zero_of_compact_packet
      hPL g hgCompact (fun t ht => mem_image_of_mem c ht)

end SchwartzMap
