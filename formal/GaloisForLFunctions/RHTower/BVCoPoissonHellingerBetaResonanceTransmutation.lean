import GaloisForLFunctions.RHTower.BVCoPoissonHalfWeightResonance
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Hellinger--Beta/co-Poisson resonance transmutation

The critical co-Poisson Mellin vector

`F(s) = eta(s - 1/2) / (s - 1/2)`

does not acquire Burnol extended-property-S regularity after multiplication
by the scalar Hellinger--Hodge Beta column

`H(s) = -Gamma(s + 1/2) Gamma(3/2) / Gamma(s + 2)`.

After reflection, the old integer Gamma resonance is replaced by the common
half-integer pole lattice `3/2 + 2 n`.  This module computes every residue,
proves it nonzero, and proves that no nonzero polynomial can cancel the
infinite family.

The argument is unconditional.  In particular, nonvanishing of the eta
factor at the reflected points is reduced through the zeta functional
equation to the classical zero-free half-plane `re(s) > 1`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Recursive normalization of the Gamma residue at the negative integer
`-n`. -/
def gammaNegNatResidue : ℕ → ℂ
  | 0 => 1
  | n + 1 => gammaNegNatResidue n / (-(n + 1 : ℂ))

theorem gammaNegNatResidue_ne_zero (n : ℕ) :
    gammaNegNatResidue n ≠ 0 := by
  induction n with
  | zero => simp [gammaNegNatResidue]
  | succ n ih =>
      rw [gammaNegNatResidue]
      exact div_ne_zero ih (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n))

theorem gammaNegNatResidue_eq (n : ℕ) :
    gammaNegNatResidue n = (-1 : ℂ) ^ n / n.factorial := by
  induction n with
  | zero => simp [gammaNegNatResidue]
  | succ n ih =>
      rw [gammaNegNatResidue, ih, Nat.factorial_succ]
      push_cast
      have hn : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      have hsucc : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp [hn, hsucc]
      ring

/-- Exact residue limit of Gamma at every nonpositive integer. -/
theorem tendsto_add_nat_mul_Gamma_nhds_neg_nat (n : ℕ) :
    Tendsto (fun z : ℂ => (z + n) * Complex.Gamma z)
      (𝓝[≠] (-(n : ℂ))) (𝓝 (gammaNegNatResidue n)) := by
  induction n with
  | zero =>
      simpa [gammaNegNatResidue] using
        Complex.tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
      let a : ℂ := -(n + 1 : ℂ)
      have hshift :
          Tendsto (fun z : ℂ => z + 1)
            (𝓝[≠] a) (𝓝[≠] (-(n : ℂ))) := by
        have hderiv : HasDerivAt (fun z : ℂ => z + 1) 1 a :=
          hasDerivAt_id a |>.add_const 1
        have hmap := hderiv.tendsto_nhdsNE (by norm_num : (1 : ℂ) ≠ 0)
        convert hmap using 1
        all_goals simp [a]
      have hnum :
          Tendsto
            (fun z : ℂ => ((z + 1) + n) * Complex.Gamma (z + 1))
            (𝓝[≠] a) (𝓝 (gammaNegNatResidue n)) :=
        ih.comp hshift
      have hden : Tendsto (fun z : ℂ => z) (𝓝[≠] a) (𝓝 a) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hquot := hnum.div hden (by
        dsimp [a]
        exact neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n))
      have heq :
          ∀ᶠ z : ℂ in 𝓝[≠] a,
            ((z + 1) + n) * Complex.Gamma (z + 1) / z =
              (z + (n + 1)) * Complex.Gamma z := by
        have ha0 : a ≠ 0 := by
          dsimp [a]
          exact neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)
        have hneEventually : ∀ᶠ z : ℂ in 𝓝[≠] a, z ≠ 0 :=
          Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (isOpen_ne.mem_nhds ha0)
        filter_upwards [hneEventually] with z hz0
        rw [Complex.Gamma_add_one z hz0]
        field_simp [hz0]
        ring
      rw [show gammaNegNatResidue (n + 1) = gammaNegNatResidue n / a by
        simp [gammaNegNatResidue, a]]
      convert hquot.congr' heq using 1 <;> simp [a]

/-- Scalar Hellinger--Hodge Beta column in Mellin coordinates. -/
def hellingerHodgeBetaColumnComplex (s : ℂ) : ℂ :=
  -(Complex.Gamma (s + 1 / 2) * Complex.Gamma (3 / 2) /
      Complex.Gamma (s + 2))

/-- Source-forced Beta coface recurrence, valid at every point where the
two Gamma shift identities are regular. -/
theorem hellingerHodgeBetaColumnComplex_add_one
    {s : ℂ} (hshalf : s + 1 / 2 ≠ 0) (hstwo : s + 2 ≠ 0) :
    hellingerHodgeBetaColumnComplex (s + 1) =
      (s + 1 / 2) / (s + 2) * hellingerHodgeBetaColumnComplex s := by
  rw [hellingerHodgeBetaColumnComplex, hellingerHodgeBetaColumnComplex]
  have hnum := Complex.Gamma_add_one (s + 1 / 2) hshalf
  have hden := Complex.Gamma_add_one (s + 2) hstwo
  rw [show s + 1 + 1 / 2 = (s + 1 / 2) + 1 by ring,
    show s + 1 + 2 = (s + 2) + 1 by ring,
    hnum, hden]
  rw [div_eq_mul_inv, mul_inv_rev]
  field_simp [hstwo]

/-- Real-domain form of the Beta coface recurrence stated on the paper
card.  The hypothesis `-1/2 < a` keeps both shift denominators regular. -/
theorem hellingerHodgeBetaColumnComplex_real_add_one
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    hellingerHodgeBetaColumnComplex ((a + 1 : ℝ) : ℂ) =
      (((a + 1 / 2) / (a + 2) : ℝ) : ℂ) *
        hellingerHodgeBetaColumnComplex (a : ℂ) := by
  have hshalf : (a : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hstwo : (a : ℂ) + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  convert hellingerHodgeBetaColumnComplex_add_one hshalf hstwo using 1 <;>
    push_cast <;> ring

/-- Scalar Hellinger correction of the critical co-Poisson Mellin vector. -/
def hellingerBetaCoPoissonMellin (s : ℂ) : ℂ :=
  criticalEtaMellin s * hellingerHodgeBetaColumnComplex s

/-- Common reflected half-integer pole lattice created by the scalar Beta
column. -/
def hellingerBetaReflectedHalfPole (n : ℕ) : ℂ :=
  3 / 2 + 2 * n

/-- Exact residue of the reflected scalar Hellinger/co-Poisson product at
`3/2 + 2 n`. -/
def hellingerBetaReflectedResidue (n : ℕ) : ℂ :=
  criticalEtaMellin (-(1 / 2 : ℂ) - 2 * n) *
    (gammaNegNatResidue (2 * n) * Complex.Gamma (3 / 2) /
      Complex.Gamma (3 / 2 - 2 * n))

theorem continuousAt_criticalEtaMellin
    {s : ℂ} (hsHalf : s ≠ 1 / 2) (hsZeta : s - 1 / 2 ≠ 1) :
    ContinuousAt criticalEtaMellin s := by
  unfold criticalEtaMellin dirichletEta
  apply ContinuousAt.div
  · apply ContinuousAt.mul
    · fun_prop
    · have houter :
          Tendsto riemannZeta
            (𝓝 (s - 1 / 2)) (𝓝 (riemannZeta (s - 1 / 2))) :=
        (differentiableAt_riemannZeta hsZeta).continuousAt
      have hinner :
          Tendsto (fun z : ℂ => z - 1 / 2)
            (𝓝 s) (𝓝 (s - 1 / 2)) :=
        (continuous_id.sub continuous_const).tendsto s
      exact houter.comp hinner
  · fun_prop
  · simpa [sub_ne_zero] using hsHalf

/-- The reflected Beta column has the exact normalized Gamma residue at
every common half-lattice point. -/
theorem tendsto_reflected_hellingerHodgeBetaColumn_residue (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        (s - hellingerBetaReflectedHalfPole n) *
          hellingerHodgeBetaColumnComplex (1 - s))
      (𝓝[≠] (hellingerBetaReflectedHalfPole n))
      (𝓝 (gammaNegNatResidue (2 * n) * Complex.Gamma (3 / 2) /
        Complex.Gamma (3 / 2 - 2 * n))) := by
  let a := hellingerBetaReflectedHalfPole n
  have hmap :
      Tendsto (fun s : ℂ => 3 / 2 - s)
        (𝓝[≠] a) (𝓝[≠] (-(2 * n : ℕ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact
        ((continuous_const.sub continuous_id).tendsto' a
          (-(2 * n : ℕ) : ℂ) (by
            simp [a, hellingerBetaReflectedHalfPole])).mono_left
          nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      apply hs
      rw [Set.mem_singleton_iff]
      simp [a, hellingerBetaReflectedHalfPole] at h ⊢
      linear_combination -h
  have hgamma :=
    (tendsto_add_nat_mul_Gamma_nhds_neg_nat (2 * n)).comp hmap
  have hgamma' :
      Tendsto
        (fun s : ℂ =>
          (s - a) * (-(Complex.Gamma (3 / 2 - s))))
        (𝓝[≠] a) (𝓝 (gammaNegNatResidue (2 * n))) := by
    apply hgamma.congr'
    filter_upwards with s
    simp only [Function.comp_apply]
    simp [a, hellingerBetaReflectedHalfPole]
    ring
  have hdenCont :
      ContinuousAt (fun s : ℂ => Complex.Gamma (3 - s)) a := by
    apply (Complex.continuousAt_Gamma (3 - a) ?_).comp
    · fun_prop
    · intro m hm
      have hre := congrArg Complex.re hm
      simp [a, hellingerBetaReflectedHalfPole] at hre
      have hreal : (3 : ℝ) = 4 * n - 2 * m := by linarith
      have hint : (3 : ℤ) = 4 * (n : ℤ) - 2 * (m : ℤ) := by
        exact_mod_cast hreal
      omega
  have hdenNe : Complex.Gamma (3 - a) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp [a, hellingerBetaReflectedHalfPole] at hre
    have hreal : (3 : ℝ) = 4 * n - 2 * m := by linarith
    have hint : (3 : ℤ) = 4 * (n : ℤ) - 2 * (m : ℤ) := by
      exact_mod_cast hreal
    omega
  have hconst :
      Tendsto (fun _ : ℂ => Complex.Gamma (3 / 2))
        (𝓝[≠] a) (𝓝 (Complex.Gamma (3 / 2))) := tendsto_const_nhds
  have hden :
      Tendsto (fun s : ℂ => Complex.Gamma (3 - s))
        (𝓝[≠] a) (𝓝 (Complex.Gamma (3 - a))) :=
    hdenCont.mono_left nhdsWithin_le_nhds
  have hquot := (hgamma'.mul hconst).div hden hdenNe
  have hquot' :
      Tendsto
        (fun s : ℂ =>
          (s - a) * hellingerHodgeBetaColumnComplex (1 - s))
        (𝓝[≠] a)
        (𝓝 (gammaNegNatResidue (2 * n) * Complex.Gamma (3 / 2) /
          Complex.Gamma (3 - a))) := by
    apply hquot.congr'
    filter_upwards with s
    simp [hellingerHodgeBetaColumnComplex]
    ring
  have hdenPoint :
      (3 - a : ℂ) = 3 / 2 - 2 * n := by
    simp [a, hellingerBetaReflectedHalfPole]
    ring
  rw [hdenPoint] at hquot'
  simpa only [a] using hquot'

lemma cos_pi_mul_two_add_two_nat_div_two_ne_zero (n : ℕ) :
    Complex.cos ((Real.pi : ℂ) * ((2 : ℂ) + 2 * n) / 2) ≠ 0 := by
  rw [show (Real.pi : ℂ) * ((2 : ℂ) + 2 * n) / 2 =
      (((n + 1 : ℕ) * Real.pi : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_cos]
  norm_cast
  rw [Real.cos_nat_mul_pi]
  exact pow_ne_zero _ (by norm_num)

/-- Zeta has no zero at any negative odd integer.  The proof uses the
functional equation and the zero-free half-plane, rather than a table of
special values. -/
lemma riemannZeta_neg_one_sub_two_nat_ne_zero (n : ℕ) :
    riemannZeta (-(1 : ℂ) - 2 * n) ≠ 0 := by
  let s : ℂ := 2 + 2 * n
  have hsneg (m : ℕ) : s ≠ -m := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsone : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [s] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub (s := s) hsneg hsone
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hbase : (2 * (Real.pi : ℂ) : ℂ) ≠ 0 :=
    mul_ne_zero htwo (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hpow : (2 * (Real.pi : ℂ) : ℂ) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
  have hgamma : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    dsimp [s]
    norm_num
    positivity
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    dsimp [s]
    exact cos_pi_mul_two_add_two_nat_div_two_ne_zero n
  have hzeta : riemannZeta s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    dsimp [s]
    norm_num
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrhs : 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hpow) hgamma) hcos)
      hzeta
  rw [← hfe] at hrhs
  have harg : 1 - s = -(1 : ℂ) - 2 * n := by
    dsimp [s]
    ring
  simpa only [harg] using hrhs

lemma one_sub_two_cpow_two_add_two_nat_ne_zero (n : ℕ) :
    1 - (2 : ℂ) ^ ((2 : ℂ) + 2 * n) ≠ 0 := by
  have hrpos : 0 < (2 : ℝ) + 2 * n := by positivity
  have hgt : 1 < (2 : ℝ) ^ ((2 : ℝ) + 2 * n) :=
    Real.one_lt_rpow (by norm_num) hrpos
  intro h
  have hpow : (2 : ℂ) ^ ((2 : ℂ) + 2 * n) = 1 :=
    (sub_eq_zero.mp h).symm
  have hcast : (((2 : ℝ) ^ ((2 : ℝ) + 2 * n) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_cpow (by norm_num)]
    simpa only [ofReal_ofNat, ofReal_add, ofReal_natCast, ofReal_mul]
      using hpow
  have hre := congrArg Complex.re hcast
  norm_num at hre
  linarith

lemma dirichletEta_neg_one_sub_two_nat_ne_zero (n : ℕ) :
    dirichletEta (-(1 : ℂ) - 2 * n) ≠ 0 := by
  unfold dirichletEta
  apply mul_ne_zero
  · convert one_sub_two_cpow_two_add_two_nat_ne_zero n using 1
    all_goals ring_nf
  · exact riemannZeta_neg_one_sub_two_nat_ne_zero n

theorem criticalEtaMellin_neg_half_sub_two_nat_ne_zero (n : ℕ) :
    criticalEtaMellin (-(1 / 2 : ℂ) - 2 * n) ≠ 0 := by
  unfold criticalEtaMellin
  apply div_ne_zero
  · convert dirichletEta_neg_one_sub_two_nat_ne_zero n using 1
    all_goals ring_nf
  · norm_num
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

lemma Gamma_three_halves_sub_two_nat_ne_zero (n : ℕ) :
    Complex.Gamma ((3 / 2 : ℂ) - 2 * n) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  norm_num at hre
  have hreal : (3 : ℝ) = 4 * n - 2 * m := by linarith
  have hint : (3 : ℤ) = 4 * (n : ℤ) - 2 * (m : ℤ) := by
    exact_mod_cast hreal
  omega

theorem hellingerBetaReflectedResidue_ne_zero (n : ℕ) :
    hellingerBetaReflectedResidue n ≠ 0 := by
  unfold hellingerBetaReflectedResidue
  apply mul_ne_zero (criticalEtaMellin_neg_half_sub_two_nat_ne_zero n)
  apply div_ne_zero
  · exact mul_ne_zero (gammaNegNatResidue_ne_zero (2 * n))
      (Complex.Gamma_ne_zero_of_re_pos
        (by norm_num : 0 < (3 / 2 : ℂ).re))
  · exact Gamma_three_halves_sub_two_nat_ne_zero n

/-- Formula (6) on the paper card: the raw reflected residue written
directly with the eta value, factorial, and two finite Gamma values. -/
theorem hellingerBetaReflectedResidue_eq_card_formula (n : ℕ) :
    hellingerBetaReflectedResidue n =
      (dirichletEta (-(1 : ℂ) - 2 * n) / (-(1 : ℂ) - 2 * n)) *
        (Complex.Gamma (3 / 2) /
          (((2 * n).factorial : ℂ) *
            Complex.Gamma (3 / 2 - 2 * n))) := by
  rw [hellingerBetaReflectedResidue, criticalEtaMellin,
    gammaNegNatResidue_eq]
  have hsign : (-1 : ℂ) ^ (2 * n) = 1 := by simp
  rw [hsign]
  have hetaArg : -(1 / 2 : ℂ) - 2 * n - 1 / 2 = -(1 : ℂ) - 2 * n := by
    ring
  rw [hetaArg]
  have hfac : (((2 * n).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have hgamma := Gamma_three_halves_sub_two_nat_ne_zero n
  field_simp [hfac, hgamma]

/-- Every half-lattice point is a genuine simple pole of the reflected
scalar Hellinger/co-Poisson product, with the exact residue above. -/
theorem tendsto_reflected_hellingerBetaCoPoissonMellin_residue (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        (s - hellingerBetaReflectedHalfPole n) *
          hellingerBetaCoPoissonMellin (1 - s))
      (𝓝[≠] (hellingerBetaReflectedHalfPole n))
      (𝓝 (hellingerBetaReflectedResidue n)) := by
  let a := hellingerBetaReflectedHalfPole n
  let z : ℂ := -(1 / 2 : ℂ) - 2 * n
  have hzHalf : z ≠ 1 / 2 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzZeta : z - 1 / 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    norm_num at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmap :
      Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] a) (𝓝 z) := by
    have hmap' :
        Tendsto (fun s : ℂ => 1 - s) (𝓝 a) (𝓝 z) :=
      (continuous_const.sub continuous_id).tendsto' a z (by
        simp [a, z, hellingerBetaReflectedHalfPole]
        ring)
    exact hmap'.mono_left nhdsWithin_le_nhds
  have heta :
      Tendsto (fun s : ℂ => criticalEtaMellin (1 - s))
        (𝓝[≠] a) (𝓝 (criticalEtaMellin z)) := by
    have houter :
        Tendsto criticalEtaMellin
          (𝓝 z) (𝓝 (criticalEtaMellin z)) :=
      continuousAt_criticalEtaMellin hzHalf hzZeta
    exact houter.comp hmap
  have hbeta := tendsto_reflected_hellingerHodgeBetaColumn_residue n
  have hproduct := heta.mul hbeta
  have hproduct' :
      Tendsto
        (fun s : ℂ =>
          (s - a) * hellingerBetaCoPoissonMellin (1 - s))
        (𝓝[≠] a)
        (𝓝 (criticalEtaMellin z *
          (gammaNegNatResidue (2 * n) * Complex.Gamma (3 / 2) /
            Complex.Gamma (3 / 2 - 2 * n)))) := by
    apply hproduct.congr'
    filter_upwards with s
    unfold hellingerBetaCoPoissonMellin
    ring
  simpa only [a, z, hellingerBetaReflectedResidue] using hproduct'

theorem hellingerBetaReflectedHalfPole_injective :
    Function.Injective hellingerBetaReflectedHalfPole := by
  intro m n h
  unfold hellingerBetaReflectedHalfPole at h
  have hre := congrArg Complex.re h
  norm_num at hre
  exact_mod_cast hre

/-- No nonzero polynomial can cancel the full half-lattice residue family.
This is the exact algebraic obstruction to scalar extended-property-S
repair by the Hellinger Beta column. -/
theorem polynomial_eq_zero_of_cancels_hellingerBeta_half_residues
    (p : Polynomial ℂ)
    (hcancel : ∀ n : ℕ,
      p.eval (hellingerBetaReflectedHalfPole n) *
        hellingerBetaReflectedResidue n = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply
    (Set.infinite_range_of_injective
      hellingerBetaReflectedHalfPole_injective).mono
  rintro z ⟨n, rfl⟩
  change p.eval (hellingerBetaReflectedHalfPole n) = 0
  exact (mul_eq_zero.mp (hcancel n)).resolve_right
    (hellingerBetaReflectedResidue_ne_zero n)

/-- Even Fourier-reflection factor in Burnol's Mellin normalization. -/
def burnolEvenReflectionFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s - 1 / 2) *
    Complex.Gamma ((1 - s) / 2) / Complex.Gamma (s / 2)

/-- Odd Fourier-reflection factor in Burnol's Mellin normalization. -/
def burnolOddReflectionFactor (s : ℂ) : ℂ :=
  Complex.I * (Real.pi : ℂ) ^ (s - 1 / 2) *
    Complex.Gamma ((2 - s) / 2) / Complex.Gamma ((s + 1) / 2)

lemma burnolEvenHalfPoleNumerator_not_neg_nat (n m : ℕ) :
    (1 - hellingerBetaReflectedHalfPole n) / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaReflectedHalfPole] at hre
  have hreal : (4 : ℝ) * m = 4 * n + 1 := by linarith
  have hint : (4 : ℤ) * m = 4 * n + 1 := by
    exact_mod_cast hreal
  omega

lemma burnolEvenHalfPoleDenominator_not_neg_nat (n m : ℕ) :
    hellingerBetaReflectedHalfPole n / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaReflectedHalfPole] at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma burnolOddHalfPoleNumerator_not_neg_nat (n m : ℕ) :
    (2 - hellingerBetaReflectedHalfPole n) / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaReflectedHalfPole] at hre
  have hreal : (4 : ℝ) * n = 4 * m + 1 := by linarith
  have hint : (4 : ℤ) * n = 4 * m + 1 := by
    exact_mod_cast hreal
  omega

lemma burnolOddHalfPoleDenominator_not_neg_nat (n m : ℕ) :
    (hellingerBetaReflectedHalfPole n + 1) / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaReflectedHalfPole] at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem continuousAt_burnolEvenReflectionFactor_halfPole (n : ℕ) :
    ContinuousAt burnolEvenReflectionFactor
      (hellingerBetaReflectedHalfPole n) := by
  let a := hellingerBetaReflectedHalfPole n
  have hpow :
      ContinuousAt (fun s : ℂ => (Real.pi : ℂ) ^ (s - 1 / 2)) a :=
    (continuousAt_id.sub continuousAt_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hnum :
      ContinuousAt (fun s : ℂ => Complex.Gamma ((1 - s) / 2)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 ((1 - a) / 2)) (𝓝 (Complex.Gamma ((1 - a) / 2))) :=
      Complex.continuousAt_Gamma ((1 - a) / 2) (by
        intro m hm
        exact burnolEvenHalfPoleNumerator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => (1 - s) / 2)
          (𝓝 a) (𝓝 ((1 - a) / 2)) :=
      (continuous_const.sub continuous_id).div_const 2 |>.tendsto a
    exact houter.comp hinner
  have hden :
      ContinuousAt (fun s : ℂ => Complex.Gamma (s / 2)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 (a / 2)) (𝓝 (Complex.Gamma (a / 2))) :=
      Complex.continuousAt_Gamma (a / 2) (by
        intro m hm
        exact burnolEvenHalfPoleDenominator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => s / 2) (𝓝 a) (𝓝 (a / 2)) :=
      continuous_id.div_const 2 |>.tendsto a
    exact houter.comp hinner
  unfold burnolEvenReflectionFactor
  exact (hpow.mul hnum).div hden
    (Complex.Gamma_ne_zero
      (burnolEvenHalfPoleDenominator_not_neg_nat n))

theorem continuousAt_burnolOddReflectionFactor_halfPole (n : ℕ) :
    ContinuousAt burnolOddReflectionFactor
      (hellingerBetaReflectedHalfPole n) := by
  let a := hellingerBetaReflectedHalfPole n
  have hpow :
      ContinuousAt (fun s : ℂ => (Real.pi : ℂ) ^ (s - 1 / 2)) a :=
    (continuousAt_id.sub continuousAt_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hnum :
      ContinuousAt (fun s : ℂ => Complex.Gamma ((2 - s) / 2)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 ((2 - a) / 2)) (𝓝 (Complex.Gamma ((2 - a) / 2))) :=
      Complex.continuousAt_Gamma ((2 - a) / 2) (by
        intro m hm
        exact burnolOddHalfPoleNumerator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => (2 - s) / 2)
          (𝓝 a) (𝓝 ((2 - a) / 2)) :=
      (continuous_const.sub continuous_id).div_const 2 |>.tendsto a
    exact houter.comp hinner
  have hden :
      ContinuousAt (fun s : ℂ => Complex.Gamma ((s + 1) / 2)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 ((a + 1) / 2)) (𝓝 (Complex.Gamma ((a + 1) / 2))) :=
      Complex.continuousAt_Gamma ((a + 1) / 2) (by
        intro m hm
        exact burnolOddHalfPoleDenominator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => (s + 1) / 2)
          (𝓝 a) (𝓝 ((a + 1) / 2)) :=
      (continuous_id.add continuous_const).div_const 2 |>.tendsto a
    exact houter.comp hinner
  unfold burnolOddReflectionFactor
  exact ((continuousAt_const.mul hpow).mul hnum).div hden
    (Complex.Gamma_ne_zero
      (burnolOddHalfPoleDenominator_not_neg_nat n))

theorem burnolEvenReflectionFactor_halfPole_ne_zero (n : ℕ) :
    burnolEvenReflectionFactor (hellingerBetaReflectedHalfPole n) ≠ 0 := by
  unfold burnolEvenReflectionFactor
  apply div_ne_zero
  · apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · exact Complex.Gamma_ne_zero
        (burnolEvenHalfPoleNumerator_not_neg_nat n)
  · exact Complex.Gamma_ne_zero
      (burnolEvenHalfPoleDenominator_not_neg_nat n)

theorem burnolOddReflectionFactor_halfPole_ne_zero (n : ℕ) :
    burnolOddReflectionFactor (hellingerBetaReflectedHalfPole n) ≠ 0 := by
  unfold burnolOddReflectionFactor
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero Complex.I_ne_zero
        (Complex.cpow_ne_zero_iff.mpr
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
      (Complex.Gamma_ne_zero
        (burnolOddHalfPoleNumerator_not_neg_nat n))
  · exact Complex.Gamma_ne_zero
      (burnolOddHalfPoleDenominator_not_neg_nat n)

/-- Even reflected scalar transform. -/
def hellingerBetaEvenReflectedMellin (s : ℂ) : ℂ :=
  burnolEvenReflectionFactor s * hellingerBetaCoPoissonMellin (1 - s)

/-- Odd reflected scalar transform. -/
def hellingerBetaOddReflectedMellin (s : ℂ) : ℂ :=
  burnolOddReflectionFactor s * hellingerBetaCoPoissonMellin (1 - s)

def hellingerBetaEvenReflectedResidue (n : ℕ) : ℂ :=
  burnolEvenReflectionFactor (hellingerBetaReflectedHalfPole n) *
    hellingerBetaReflectedResidue n

def hellingerBetaOddReflectedResidue (n : ℕ) : ℂ :=
  burnolOddReflectionFactor (hellingerBetaReflectedHalfPole n) *
    hellingerBetaReflectedResidue n

theorem tendsto_hellingerBetaEvenReflectedMellin_residue (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        (s - hellingerBetaReflectedHalfPole n) *
          hellingerBetaEvenReflectedMellin s)
      (𝓝[≠] (hellingerBetaReflectedHalfPole n))
      (𝓝 (hellingerBetaEvenReflectedResidue n)) := by
  let a := hellingerBetaReflectedHalfPole n
  have hfactor :
      Tendsto burnolEvenReflectionFactor
        (𝓝[≠] a) (𝓝 (burnolEvenReflectionFactor a)) :=
    (continuousAt_burnolEvenReflectionFactor_halfPole n).mono_left
      nhdsWithin_le_nhds
  have hres := tendsto_reflected_hellingerBetaCoPoissonMellin_residue n
  have hmul := hfactor.mul hres
  have hmul' :
      Tendsto
        (fun s : ℂ =>
          (s - a) * hellingerBetaEvenReflectedMellin s)
        (𝓝[≠] a)
        (𝓝 (burnolEvenReflectionFactor a *
          hellingerBetaReflectedResidue n)) := by
    apply hmul.congr'
    filter_upwards with s
    unfold hellingerBetaEvenReflectedMellin
    ring
  simpa only [a, hellingerBetaEvenReflectedResidue] using hmul'

theorem tendsto_hellingerBetaOddReflectedMellin_residue (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        (s - hellingerBetaReflectedHalfPole n) *
          hellingerBetaOddReflectedMellin s)
      (𝓝[≠] (hellingerBetaReflectedHalfPole n))
      (𝓝 (hellingerBetaOddReflectedResidue n)) := by
  let a := hellingerBetaReflectedHalfPole n
  have hfactor :
      Tendsto burnolOddReflectionFactor
        (𝓝[≠] a) (𝓝 (burnolOddReflectionFactor a)) :=
    (continuousAt_burnolOddReflectionFactor_halfPole n).mono_left
      nhdsWithin_le_nhds
  have hres := tendsto_reflected_hellingerBetaCoPoissonMellin_residue n
  have hmul := hfactor.mul hres
  have hmul' :
      Tendsto
        (fun s : ℂ =>
          (s - a) * hellingerBetaOddReflectedMellin s)
        (𝓝[≠] a)
        (𝓝 (burnolOddReflectionFactor a *
          hellingerBetaReflectedResidue n)) := by
    apply hmul.congr'
    filter_upwards with s
    unfold hellingerBetaOddReflectedMellin
    ring
  simpa only [a, hellingerBetaOddReflectedResidue] using hmul'

theorem hellingerBetaEvenReflectedResidue_ne_zero (n : ℕ) :
    hellingerBetaEvenReflectedResidue n ≠ 0 :=
  mul_ne_zero (burnolEvenReflectionFactor_halfPole_ne_zero n)
    (hellingerBetaReflectedResidue_ne_zero n)

theorem hellingerBetaOddReflectedResidue_ne_zero (n : ℕ) :
    hellingerBetaOddReflectedResidue n ≠ 0 :=
  mul_ne_zero (burnolOddReflectionFactor_halfPole_ne_zero n)
    (hellingerBetaReflectedResidue_ne_zero n)

theorem polynomial_eq_zero_of_cancels_hellingerBeta_even_half_residues
    (p : Polynomial ℂ)
    (hcancel : ∀ n : ℕ,
      p.eval (hellingerBetaReflectedHalfPole n) *
        hellingerBetaEvenReflectedResidue n = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply
    (Set.infinite_range_of_injective
      hellingerBetaReflectedHalfPole_injective).mono
  rintro z ⟨n, rfl⟩
  change p.eval (hellingerBetaReflectedHalfPole n) = 0
  exact (mul_eq_zero.mp (hcancel n)).resolve_right
    (hellingerBetaEvenReflectedResidue_ne_zero n)

theorem polynomial_eq_zero_of_cancels_hellingerBeta_odd_half_residues
    (p : Polynomial ℂ)
    (hcancel : ∀ n : ℕ,
      p.eval (hellingerBetaReflectedHalfPole n) *
        hellingerBetaOddReflectedResidue n = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply
    (Set.infinite_range_of_injective
      hellingerBetaReflectedHalfPole_injective).mono
  rintro z ⟨n, rfl⟩
  change p.eval (hellingerBetaReflectedHalfPole n) = 0
  exact (mul_eq_zero.mp (hcancel n)).resolve_right
    (hellingerBetaOddReflectedResidue_ne_zero n)

/-- A polynomial cancelling every even reflected half-lattice residue
outside an arbitrary finite exceptional set is the zero polynomial. -/
theorem polynomial_eq_zero_of_cancels_hellingerBeta_even_half_residues_off_finset
    (p : Polynomial ℂ) (exceptional : Finset ℕ)
    (hcancel : ∀ n : ℕ, n ∉ exceptional →
      p.eval (hellingerBetaReflectedHalfPole n) *
        hellingerBetaEvenReflectedResidue n = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  let index : ℕ → ℕ := fun n => n + exceptional.sup id + 1
  have hindex : Function.Injective index := by
    intro m n h
    dsimp [index] at h
    omega
  have hpole : Function.Injective (fun n =>
      hellingerBetaReflectedHalfPole (index n)) :=
    hellingerBetaReflectedHalfPole_injective.comp hindex
  apply (Set.infinite_range_of_injective hpole).mono
  rintro z ⟨n, rfl⟩
  change p.eval (hellingerBetaReflectedHalfPole (index n)) = 0
  have hnot : index n ∉ exceptional := by
    intro hmem
    have hle : index n ≤ exceptional.sup id := Finset.le_sup (f := id) hmem
    dsimp [index] at hle
    omega
  exact (mul_eq_zero.mp (hcancel (index n) hnot)).resolve_right
    (hellingerBetaEvenReflectedResidue_ne_zero (index n))

/-- Odd counterpart of
`polynomial_eq_zero_of_cancels_hellingerBeta_even_half_residues_off_finset`. -/
theorem polynomial_eq_zero_of_cancels_hellingerBeta_odd_half_residues_off_finset
    (p : Polynomial ℂ) (exceptional : Finset ℕ)
    (hcancel : ∀ n : ℕ, n ∉ exceptional →
      p.eval (hellingerBetaReflectedHalfPole n) *
        hellingerBetaOddReflectedResidue n = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  let index : ℕ → ℕ := fun n => n + exceptional.sup id + 1
  have hindex : Function.Injective index := by
    intro m n h
    dsimp [index] at h
    omega
  have hpole : Function.Injective (fun n =>
      hellingerBetaReflectedHalfPole (index n)) :=
    hellingerBetaReflectedHalfPole_injective.comp hindex
  apply (Set.infinite_range_of_injective hpole).mono
  rintro z ⟨n, rfl⟩
  change p.eval (hellingerBetaReflectedHalfPole (index n)) = 0
  have hnot : index n ∉ exceptional := by
    intro hmem
    have hle : index n ≤ exceptional.sup id := Finset.le_sup (f := id) hmem
    dsimp [index] at hle
    omega
  exact (mul_eq_zero.mp (hcancel (index n) hnot)).resolve_right
    (hellingerBetaOddReflectedResidue_ne_zero (index n))

/-- An affine map with nonzero slope transports a punctured neighbourhood
to the corresponding punctured neighbourhood. -/
theorem const_sub_div_punctured_tendsto
    (a c d : ℂ) (hd : d ≠ 0) :
    Tendsto (fun s : ℂ => (c - s) / d)
      (𝓝[≠] a) (𝓝[≠] ((c - a) / d)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact
      ((continuous_const.sub continuous_id).div_const d |>.tendsto' a
        ((c - a) / d) rfl).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    apply hs
    rw [Set.mem_singleton_iff]
    have h' := congrArg (fun z : ℂ => z * d) h
    field_simp [hd] at h'
    linear_combination -h'

/-- Even integer poles beyond the initial point, parameterized as
`3 + 2 n`. -/
def hellingerBetaEvenOldPole (n : ℕ) : ℂ := 3 + 2 * n

/-- Odd integer poles beyond the initial point, parameterized as
`4 + 2 n`. -/
def hellingerBetaOddOldPole (n : ℕ) : ℂ := 4 + 2 * n

def burnolEvenGammaPoleRatioLimit (n : ℕ) : ℂ :=
  2 * (gammaNegNatResidue (n + 1) / gammaNegNatResidue (2 * n))

def burnolOddGammaPoleRatioLimit (n : ℕ) : ℂ :=
  2 * (gammaNegNatResidue (n + 1) /
    gammaNegNatResidue (2 * n + 1))

/-- At every noninitial even integer pole, the two singular Gamma factors
have a finite nonzero ratio.  Their affine pole coordinates differ by the
exact factor two. -/
theorem tendsto_burnolEvenGammaPoleRatio (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        Complex.Gamma ((1 - s) / 2) / Complex.Gamma (3 - s))
      (𝓝[≠] (hellingerBetaEvenOldPole n))
      (𝓝 (burnolEvenGammaPoleRatioLimit n)) := by
  let a := hellingerBetaEvenOldPole n
  have hnumMap :
      Tendsto (fun s : ℂ => (1 - s) / 2)
        (𝓝[≠] a) (𝓝[≠] (-(n + 1 : ℕ) : ℂ)) := by
    have h := const_sub_div_punctured_tendsto a 1 2 (by norm_num)
    have hpoint : ((1 - a) / 2 : ℂ) = -(n + 1 : ℕ) := by
      simp [a, hellingerBetaEvenOldPole]
      ring
    rw [hpoint] at h
    exact h
  have hdenMap :
      Tendsto (fun s : ℂ => 3 - s)
        (𝓝[≠] a) (𝓝[≠] (-(2 * n : ℕ) : ℂ)) := by
    have h := const_sub_div_punctured_tendsto a 3 1 (by norm_num)
    have hpoint : ((3 - a) / 1 : ℂ) = -(2 * n : ℕ) := by
      simp [a, hellingerBetaEvenOldPole]
    rw [hpoint] at h
    simpa using h
  have hnum :=
    (tendsto_add_nat_mul_Gamma_nhds_neg_nat (n + 1)).comp hnumMap
  have hden :=
    (tendsto_add_nat_mul_Gamma_nhds_neg_nat (2 * n)).comp hdenMap
  have hquot :=
    hnum.div hden (gammaNegNatResidue_ne_zero (2 * n))
  have htwo :
      Tendsto (fun _ : ℂ => (2 : ℂ))
        (𝓝[≠] a) (𝓝 (2 : ℂ)) := tendsto_const_nhds
  have hscaled := htwo.mul hquot
  have hdenEventually :=
    hden.eventually
      (isOpen_ne.mem_nhds (gammaNegNatResidue_ne_zero (2 * n)))
  have hscaled' :
      Tendsto
        (fun s : ℂ =>
          Complex.Gamma ((1 - s) / 2) / Complex.Gamma (3 - s))
        (𝓝[≠] a)
        (𝓝 (2 * (gammaNegNatResidue (n + 1) /
          gammaNegNatResidue (2 * n)))) := by
    apply hscaled.congr'
    filter_upwards [hdenEventually, self_mem_nhdsWithin] with s hdenNe hs
    simp only [Pi.div_apply, Function.comp_apply] at hdenNe ⊢
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    have hGammaNe : Complex.Gamma (3 - s) ≠ 0 :=
      (mul_ne_zero_iff.mp hdenNe).2
    have has : a - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have haff :
        (3 - s + (2 * n : ℕ) : ℂ) = a - s := by
      simp [a, hellingerBetaEvenOldPole]
      ring
    have haffNe : (3 - s + (2 * n : ℕ) : ℂ) ≠ 0 := by
      rw [haff]
      exact has
    have hnumAff :
        (1 - s) / 2 + (n + 1 : ℕ) = (a - s) / 2 := by
      simp [a, hellingerBetaEvenOldPole]
      ring
    have hprodNe : (a - s) * Complex.Gamma (3 - s) ≠ 0 := by
      rw [← haff]
      exact hdenNe
    rw [hnumAff, haff]
    field_simp [hprodNe, hGammaNe, has, haffNe]
  simpa only [a, burnolEvenGammaPoleRatioLimit] using hscaled'

/-- Odd counterpart of `tendsto_burnolEvenGammaPoleRatio`. -/
theorem tendsto_burnolOddGammaPoleRatio (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        Complex.Gamma ((2 - s) / 2) / Complex.Gamma (3 - s))
      (𝓝[≠] (hellingerBetaOddOldPole n))
      (𝓝 (burnolOddGammaPoleRatioLimit n)) := by
  let a := hellingerBetaOddOldPole n
  have hnumMap :
      Tendsto (fun s : ℂ => (2 - s) / 2)
        (𝓝[≠] a) (𝓝[≠] (-(n + 1 : ℕ) : ℂ)) := by
    have h := const_sub_div_punctured_tendsto a 2 2 (by norm_num)
    have hpoint : ((2 - a) / 2 : ℂ) = -(n + 1 : ℕ) := by
      simp [a, hellingerBetaOddOldPole]
      ring
    rw [hpoint] at h
    exact h
  have hdenMap :
      Tendsto (fun s : ℂ => 3 - s)
        (𝓝[≠] a) (𝓝[≠] (-(2 * n + 1 : ℕ) : ℂ)) := by
    have h := const_sub_div_punctured_tendsto a 3 1 (by norm_num)
    have hpoint : ((3 - a) / 1 : ℂ) = -(2 * n + 1 : ℕ) := by
      simp [a, hellingerBetaOddOldPole]
      ring
    rw [hpoint] at h
    simpa using h
  have hnum :=
    (tendsto_add_nat_mul_Gamma_nhds_neg_nat (n + 1)).comp hnumMap
  have hden :=
    (tendsto_add_nat_mul_Gamma_nhds_neg_nat (2 * n + 1)).comp hdenMap
  have hquot :=
    hnum.div hden (gammaNegNatResidue_ne_zero (2 * n + 1))
  have htwo :
      Tendsto (fun _ : ℂ => (2 : ℂ))
        (𝓝[≠] a) (𝓝 (2 : ℂ)) := tendsto_const_nhds
  have hscaled := htwo.mul hquot
  have hdenEventually :=
    hden.eventually
      (isOpen_ne.mem_nhds (gammaNegNatResidue_ne_zero (2 * n + 1)))
  have hscaled' :
      Tendsto
        (fun s : ℂ =>
          Complex.Gamma ((2 - s) / 2) / Complex.Gamma (3 - s))
        (𝓝[≠] a)
        (𝓝 (2 * (gammaNegNatResidue (n + 1) /
          gammaNegNatResidue (2 * n + 1)))) := by
    apply hscaled.congr'
    filter_upwards [hdenEventually, self_mem_nhdsWithin] with s hdenNe hs
    simp only [Pi.div_apply, Function.comp_apply] at hdenNe ⊢
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    have hGammaNe : Complex.Gamma (3 - s) ≠ 0 :=
      (mul_ne_zero_iff.mp hdenNe).2
    have has : a - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    have haff :
        (3 - s + (2 * n + 1 : ℕ) : ℂ) = a - s := by
      simp [a, hellingerBetaOddOldPole]
      ring
    have haffNe : (3 - s + (2 * n + 1 : ℕ) : ℂ) ≠ 0 := by
      rw [haff]
      exact has
    have hnumAff :
        (2 - s) / 2 + (n + 1 : ℕ) = (a - s) / 2 := by
      simp [a, hellingerBetaOddOldPole]
      ring
    have hprodNe : (a - s) * Complex.Gamma (3 - s) ≠ 0 := by
      rw [← haff]
      exact hdenNe
    rw [hnumAff, haff]
    field_simp [hprodNe, hGammaNe, has, haffNe]
  simpa only [a, burnolOddGammaPoleRatioLimit] using hscaled'

lemma burnolEvenOldPoleHellingerNumerator_not_neg_nat (n m : ℕ) :
    3 / 2 - hellingerBetaEvenOldPole n ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaEvenOldPole] at hre
  have hreal : (2 : ℝ) * m = 4 * n + 3 := by linarith
  have hint : (2 : ℤ) * m = 4 * n + 3 := by
    exact_mod_cast hreal
  omega

lemma burnolOddOldPoleHellingerNumerator_not_neg_nat (n m : ℕ) :
    3 / 2 - hellingerBetaOddOldPole n ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaOddOldPole] at hre
  have hreal : (2 : ℝ) * m = 4 * n + 5 := by linarith
  have hint : (2 : ℤ) * m = 4 * n + 5 := by
    exact_mod_cast hreal
  omega

lemma burnolEvenOldPoleDenominator_not_neg_nat (n m : ℕ) :
    hellingerBetaEvenOldPole n / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaEvenOldPole] at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma burnolOddOldPoleDenominator_not_neg_nat (n m : ℕ) :
    (hellingerBetaOddOldPole n + 1) / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [hellingerBetaOddOldPole] at hre
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Regular factor left after extracting the two cancelling even-parity
Gamma poles. -/
def burnolEvenHellingerCancellationRegularFactor (s : ℂ) : ℂ :=
  -((Real.pi : ℂ) ^ (s - 1 / 2) *
      Complex.Gamma (3 / 2 - s) * Complex.Gamma (3 / 2) /
        Complex.Gamma (s / 2))

/-- Odd counterpart of
`burnolEvenHellingerCancellationRegularFactor`. -/
def burnolOddHellingerCancellationRegularFactor (s : ℂ) : ℂ :=
  -(Complex.I * (Real.pi : ℂ) ^ (s - 1 / 2) *
      Complex.Gamma (3 / 2 - s) * Complex.Gamma (3 / 2) /
        Complex.Gamma ((s + 1) / 2))

theorem continuousAt_burnolEvenHellingerCancellationRegularFactor
    (n : ℕ) :
    ContinuousAt burnolEvenHellingerCancellationRegularFactor
      (hellingerBetaEvenOldPole n) := by
  let a := hellingerBetaEvenOldPole n
  have hpow :
      ContinuousAt (fun s : ℂ => (Real.pi : ℂ) ^ (s - 1 / 2)) a :=
    (continuousAt_id.sub continuousAt_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hnum :
      ContinuousAt (fun s : ℂ => Complex.Gamma (3 / 2 - s)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 (3 / 2 - a)) (𝓝 (Complex.Gamma (3 / 2 - a))) :=
      Complex.continuousAt_Gamma (3 / 2 - a) (by
        intro m hm
        exact burnolEvenOldPoleHellingerNumerator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => 3 / 2 - s)
          (𝓝 a) (𝓝 (3 / 2 - a)) :=
      (continuous_const.sub continuous_id).tendsto a
    exact houter.comp hinner
  have hden :
      ContinuousAt (fun s : ℂ => Complex.Gamma (s / 2)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 (a / 2)) (𝓝 (Complex.Gamma (a / 2))) :=
      Complex.continuousAt_Gamma (a / 2) (by
        intro m hm
        exact burnolEvenOldPoleDenominator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => s / 2) (𝓝 a) (𝓝 (a / 2)) :=
      continuous_id.div_const 2 |>.tendsto a
    exact houter.comp hinner
  unfold burnolEvenHellingerCancellationRegularFactor
  exact (((hpow.mul hnum).mul continuousAt_const).div hden
    (Complex.Gamma_ne_zero
      (burnolEvenOldPoleDenominator_not_neg_nat n))).neg

theorem continuousAt_burnolOddHellingerCancellationRegularFactor
    (n : ℕ) :
    ContinuousAt burnolOddHellingerCancellationRegularFactor
      (hellingerBetaOddOldPole n) := by
  let a := hellingerBetaOddOldPole n
  have hpow :
      ContinuousAt (fun s : ℂ => (Real.pi : ℂ) ^ (s - 1 / 2)) a :=
    (continuousAt_id.sub continuousAt_const).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hnum :
      ContinuousAt (fun s : ℂ => Complex.Gamma (3 / 2 - s)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 (3 / 2 - a)) (𝓝 (Complex.Gamma (3 / 2 - a))) :=
      Complex.continuousAt_Gamma (3 / 2 - a) (by
        intro m hm
        exact burnolOddOldPoleHellingerNumerator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => 3 / 2 - s)
          (𝓝 a) (𝓝 (3 / 2 - a)) :=
      (continuous_const.sub continuous_id).tendsto a
    exact houter.comp hinner
  have hden :
      ContinuousAt (fun s : ℂ => Complex.Gamma ((s + 1) / 2)) a := by
    have houter :
        Tendsto Complex.Gamma
          (𝓝 ((a + 1) / 2)) (𝓝 (Complex.Gamma ((a + 1) / 2))) :=
      Complex.continuousAt_Gamma ((a + 1) / 2) (by
        intro m hm
        exact burnolOddOldPoleDenominator_not_neg_nat n m (by
          simpa only [a] using hm))
    have hinner :
        Tendsto (fun s : ℂ => (s + 1) / 2)
          (𝓝 a) (𝓝 ((a + 1) / 2)) :=
      (continuous_id.add continuous_const).div_const 2 |>.tendsto a
    exact houter.comp hinner
  unfold burnolOddHellingerCancellationRegularFactor
  exact ((((continuousAt_const.mul hpow).mul hnum).mul continuousAt_const).div
    hden (Complex.Gamma_ne_zero
      (burnolOddOldPoleDenominator_not_neg_nat n))).neg

theorem burnolEvenHellingerCancellationRegularFactor_oldPole_ne_zero
    (n : ℕ) :
    burnolEvenHellingerCancellationRegularFactor
      (hellingerBetaEvenOldPole n) ≠ 0 := by
  unfold burnolEvenHellingerCancellationRegularFactor
  apply neg_ne_zero.mpr
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
        (Complex.Gamma_ne_zero
          (burnolEvenOldPoleHellingerNumerator_not_neg_nat n)))
      (Complex.Gamma_ne_zero_of_re_pos
        (by norm_num : 0 < (3 / 2 : ℂ).re))
  · exact Complex.Gamma_ne_zero
      (burnolEvenOldPoleDenominator_not_neg_nat n)

theorem burnolOddHellingerCancellationRegularFactor_oldPole_ne_zero
    (n : ℕ) :
    burnolOddHellingerCancellationRegularFactor
      (hellingerBetaOddOldPole n) ≠ 0 := by
  unfold burnolOddHellingerCancellationRegularFactor
  apply neg_ne_zero.mpr
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero Complex.I_ne_zero
          (Complex.cpow_ne_zero_iff.mpr
            (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
        (Complex.Gamma_ne_zero
          (burnolOddOldPoleHellingerNumerator_not_neg_nat n)))
      (Complex.Gamma_ne_zero_of_re_pos
        (by norm_num : 0 < (3 / 2 : ℂ).re))
  · exact Complex.Gamma_ne_zero
      (burnolOddOldPoleDenominator_not_neg_nat n)

theorem burnolEvenGammaPoleRatioLimit_ne_zero (n : ℕ) :
    burnolEvenGammaPoleRatioLimit n ≠ 0 := by
  unfold burnolEvenGammaPoleRatioLimit
  exact mul_ne_zero (by norm_num)
    (div_ne_zero (gammaNegNatResidue_ne_zero (n + 1))
      (gammaNegNatResidue_ne_zero (2 * n)))

theorem burnolOddGammaPoleRatioLimit_ne_zero (n : ℕ) :
    burnolOddGammaPoleRatioLimit n ≠ 0 := by
  unfold burnolOddGammaPoleRatioLimit
  exact mul_ne_zero (by norm_num)
    (div_ne_zero (gammaNegNatResidue_ne_zero (n + 1))
      (gammaNegNatResidue_ne_zero (2 * n + 1)))

def burnolEvenHellingerIntegerCancellationValue (n : ℕ) : ℂ :=
  burnolEvenHellingerCancellationRegularFactor
      (hellingerBetaEvenOldPole n) *
    burnolEvenGammaPoleRatioLimit n

def burnolOddHellingerIntegerCancellationValue (n : ℕ) : ℂ :=
  burnolOddHellingerCancellationRegularFactor
      (hellingerBetaOddOldPole n) *
    burnolOddGammaPoleRatioLimit n

/-- Every noninitial even integer pole of the Burnol reflection factor is
cancelled exactly by the Hellinger Beta zero, leaving a finite nonzero
limit. -/
theorem tendsto_burnolEven_mul_reflectedHellingerBeta_oldPole (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        burnolEvenReflectionFactor s *
          hellingerHodgeBetaColumnComplex (1 - s))
      (𝓝[≠] (hellingerBetaEvenOldPole n))
      (𝓝 (burnolEvenHellingerIntegerCancellationValue n)) := by
  let a := hellingerBetaEvenOldPole n
  have hregular :
      Tendsto burnolEvenHellingerCancellationRegularFactor
        (𝓝[≠] a)
        (𝓝 (burnolEvenHellingerCancellationRegularFactor a)) :=
    (continuousAt_burnolEvenHellingerCancellationRegularFactor n).mono_left
      nhdsWithin_le_nhds
  have hratio := tendsto_burnolEvenGammaPoleRatio n
  have hmul := hregular.mul hratio
  have hregularEventually :=
    hregular.eventually (isOpen_ne.mem_nhds
      (burnolEvenHellingerCancellationRegularFactor_oldPole_ne_zero n))
  have hratioEventually :=
    hratio.eventually (isOpen_ne.mem_nhds
      (burnolEvenGammaPoleRatioLimit_ne_zero n))
  have hmul' :
      Tendsto
        (fun s : ℂ =>
          burnolEvenReflectionFactor s *
            hellingerHodgeBetaColumnComplex (1 - s))
        (𝓝[≠] a)
        (𝓝 (burnolEvenHellingerCancellationRegularFactor a *
          burnolEvenGammaPoleRatioLimit n)) := by
    apply hmul.congr'
    filter_upwards [hregularEventually, hratioEventually] with s hregNe hratioNe
    have hratioParts :
        Complex.Gamma ((1 - s) / 2) ≠ 0 ∧
          Complex.Gamma (3 - s) ≠ 0 :=
      div_ne_zero_iff.mp hratioNe
    have hregDivNe :
        (Real.pi : ℂ) ^ (s - 1 / 2) *
            Complex.Gamma (3 / 2 - s) * Complex.Gamma (3 / 2) /
          Complex.Gamma (s / 2) ≠ 0 := by
      exact neg_ne_zero.mp (by
        simpa only [burnolEvenHellingerCancellationRegularFactor] using hregNe)
    have hdenNe : Complex.Gamma (s / 2) ≠ 0 :=
      (div_ne_zero_iff.mp hregDivNe).2
    unfold burnolEvenReflectionFactor hellingerHodgeBetaColumnComplex
      burnolEvenHellingerCancellationRegularFactor
    rw [show 1 - s + 1 / 2 = (3 / 2 : ℂ) - s by ring,
      show 1 - s + 2 = (3 : ℂ) - s by ring]
    field_simp [hratioParts.2, hdenNe]
  simpa only [a, burnolEvenHellingerIntegerCancellationValue] using hmul'

/-- Odd counterpart of
`tendsto_burnolEven_mul_reflectedHellingerBeta_oldPole`. -/
theorem tendsto_burnolOdd_mul_reflectedHellingerBeta_oldPole (n : ℕ) :
    Tendsto
      (fun s : ℂ =>
        burnolOddReflectionFactor s *
          hellingerHodgeBetaColumnComplex (1 - s))
      (𝓝[≠] (hellingerBetaOddOldPole n))
      (𝓝 (burnolOddHellingerIntegerCancellationValue n)) := by
  let a := hellingerBetaOddOldPole n
  have hregular :
      Tendsto burnolOddHellingerCancellationRegularFactor
        (𝓝[≠] a)
        (𝓝 (burnolOddHellingerCancellationRegularFactor a)) :=
    (continuousAt_burnolOddHellingerCancellationRegularFactor n).mono_left
      nhdsWithin_le_nhds
  have hratio := tendsto_burnolOddGammaPoleRatio n
  have hmul := hregular.mul hratio
  have hregularEventually :=
    hregular.eventually (isOpen_ne.mem_nhds
      (burnolOddHellingerCancellationRegularFactor_oldPole_ne_zero n))
  have hratioEventually :=
    hratio.eventually (isOpen_ne.mem_nhds
      (burnolOddGammaPoleRatioLimit_ne_zero n))
  have hmul' :
      Tendsto
        (fun s : ℂ =>
          burnolOddReflectionFactor s *
            hellingerHodgeBetaColumnComplex (1 - s))
        (𝓝[≠] a)
        (𝓝 (burnolOddHellingerCancellationRegularFactor a *
          burnolOddGammaPoleRatioLimit n)) := by
    apply hmul.congr'
    filter_upwards [hregularEventually, hratioEventually] with s hregNe hratioNe
    have hratioParts :
        Complex.Gamma ((2 - s) / 2) ≠ 0 ∧
          Complex.Gamma (3 - s) ≠ 0 :=
      div_ne_zero_iff.mp hratioNe
    have hregDivNe :
        Complex.I * (Real.pi : ℂ) ^ (s - 1 / 2) *
              Complex.Gamma (3 / 2 - s) * Complex.Gamma (3 / 2) /
          Complex.Gamma ((s + 1) / 2) ≠ 0 := by
      exact neg_ne_zero.mp (by
        simpa only [burnolOddHellingerCancellationRegularFactor] using hregNe)
    have hdenNe : Complex.Gamma ((s + 1) / 2) ≠ 0 :=
      (div_ne_zero_iff.mp hregDivNe).2
    unfold burnolOddReflectionFactor hellingerHodgeBetaColumnComplex
      burnolOddHellingerCancellationRegularFactor
    rw [show 1 - s + 1 / 2 = (3 / 2 : ℂ) - s by ring,
      show 1 - s + 2 = (3 : ℂ) - s by ring]
    field_simp [hratioParts.2, hdenNe]
  simpa only [a, burnolOddHellingerIntegerCancellationValue] using hmul'

theorem burnolEvenHellingerIntegerCancellationValue_ne_zero (n : ℕ) :
    burnolEvenHellingerIntegerCancellationValue n ≠ 0 :=
  mul_ne_zero
    (burnolEvenHellingerCancellationRegularFactor_oldPole_ne_zero n)
    (burnolEvenGammaPoleRatioLimit_ne_zero n)

theorem burnolOddHellingerIntegerCancellationValue_ne_zero (n : ℕ) :
    burnolOddHellingerIntegerCancellationValue n ≠ 0 :=
  mul_ne_zero
    (burnolOddHellingerCancellationRegularFactor_oldPole_ne_zero n)
    (burnolOddGammaPoleRatioLimit_ne_zero n)

theorem tendsto_criticalEtaMellin_one_sub_evenOldPole (n : ℕ) :
    Tendsto (fun s : ℂ => criticalEtaMellin (1 - s))
      (𝓝[≠] (hellingerBetaEvenOldPole n))
      (𝓝 (criticalEtaMellin (1 - hellingerBetaEvenOldPole n))) := by
  let a := hellingerBetaEvenOldPole n
  let z : ℂ := 1 - a
  have hzHalf : z ≠ 1 / 2 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z, a, hellingerBetaEvenOldPole] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzZeta : z - 1 / 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z, a, hellingerBetaEvenOldPole] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmap :
      Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] a) (𝓝 z) := by
    exact ((continuous_const.sub continuous_id).tendsto' a z (by
      simp [z])).mono_left nhdsWithin_le_nhds
  have houter :
      Tendsto criticalEtaMellin (𝓝 z) (𝓝 (criticalEtaMellin z)) :=
    continuousAt_criticalEtaMellin hzHalf hzZeta
  have hcomp := houter.comp hmap
  have hcomp' :
      Tendsto (fun s : ℂ => criticalEtaMellin (1 - s))
        (𝓝[≠] a) (𝓝 (criticalEtaMellin z)) := by
    apply hcomp.congr'
    filter_upwards with s
    rfl
  simpa only [a, z] using hcomp'

theorem tendsto_criticalEtaMellin_one_sub_oddOldPole (n : ℕ) :
    Tendsto (fun s : ℂ => criticalEtaMellin (1 - s))
      (𝓝[≠] (hellingerBetaOddOldPole n))
      (𝓝 (criticalEtaMellin (1 - hellingerBetaOddOldPole n))) := by
  let a := hellingerBetaOddOldPole n
  let z : ℂ := 1 - a
  have hzHalf : z ≠ 1 / 2 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z, a, hellingerBetaOddOldPole] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzZeta : z - 1 / 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z, a, hellingerBetaOddOldPole] at hre
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hmap :
      Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] a) (𝓝 z) := by
    exact ((continuous_const.sub continuous_id).tendsto' a z (by
      simp [z])).mono_left nhdsWithin_le_nhds
  have houter :
      Tendsto criticalEtaMellin (𝓝 z) (𝓝 (criticalEtaMellin z)) :=
    continuousAt_criticalEtaMellin hzHalf hzZeta
  have hcomp := houter.comp hmap
  have hcomp' :
      Tendsto (fun s : ℂ => criticalEtaMellin (1 - s))
        (𝓝[≠] a) (𝓝 (criticalEtaMellin z)) := by
    apply hcomp.congr'
    filter_upwards with s
    rfl
  simpa only [a, z] using hcomp'

theorem criticalEtaMellin_one_sub_evenOldPole_ne_zero (n : ℕ) :
    criticalEtaMellin (1 - hellingerBetaEvenOldPole n) ≠ 0 := by
  convert criticalEtaMellin_one_sub_positiveOddPole_ne_zero (n + 1) using 1
  unfold hellingerBetaEvenOldPole positiveOddPole
  push_cast
  ring

theorem criticalEtaMellin_one_sub_oddOldPole_ne_zero (n : ℕ) :
    criticalEtaMellin (1 - hellingerBetaOddOldPole n) ≠ 0 := by
  convert criticalEtaMellin_one_sub_positiveEvenPole_ne_zero (n + 1) using 1
  unfold hellingerBetaOddOldPole positiveEvenPole
  push_cast
  ring

def hellingerBetaEvenIntegerCancellationValue (n : ℕ) : ℂ :=
  criticalEtaMellin (1 - hellingerBetaEvenOldPole n) *
    burnolEvenHellingerIntegerCancellationValue n

def hellingerBetaOddIntegerCancellationValue (n : ℕ) : ℂ :=
  criticalEtaMellin (1 - hellingerBetaOddOldPole n) *
    burnolOddHellingerIntegerCancellationValue n

/-- The full even reflected Hellinger/co-Poisson transform is regular and
nonzero at every old even Gamma pole beyond the initial point. -/
theorem tendsto_hellingerBetaEvenReflectedMellin_oldPole (n : ℕ) :
    Tendsto hellingerBetaEvenReflectedMellin
      (𝓝[≠] (hellingerBetaEvenOldPole n))
      (𝓝 (hellingerBetaEvenIntegerCancellationValue n)) := by
  have heta := tendsto_criticalEtaMellin_one_sub_evenOldPole n
  have hcancel :=
    tendsto_burnolEven_mul_reflectedHellingerBeta_oldPole n
  have hmul := heta.mul hcancel
  have hmul' :
      Tendsto hellingerBetaEvenReflectedMellin
        (𝓝[≠] (hellingerBetaEvenOldPole n))
        (𝓝 (criticalEtaMellin (1 - hellingerBetaEvenOldPole n) *
          burnolEvenHellingerIntegerCancellationValue n)) := by
    apply hmul.congr'
    filter_upwards with s
    unfold hellingerBetaEvenReflectedMellin
      hellingerBetaCoPoissonMellin
    ring
  simpa only [hellingerBetaEvenIntegerCancellationValue] using hmul'

/-- Odd counterpart of
`tendsto_hellingerBetaEvenReflectedMellin_oldPole`. -/
theorem tendsto_hellingerBetaOddReflectedMellin_oldPole (n : ℕ) :
    Tendsto hellingerBetaOddReflectedMellin
      (𝓝[≠] (hellingerBetaOddOldPole n))
      (𝓝 (hellingerBetaOddIntegerCancellationValue n)) := by
  have heta := tendsto_criticalEtaMellin_one_sub_oddOldPole n
  have hcancel :=
    tendsto_burnolOdd_mul_reflectedHellingerBeta_oldPole n
  have hmul := heta.mul hcancel
  have hmul' :
      Tendsto hellingerBetaOddReflectedMellin
        (𝓝[≠] (hellingerBetaOddOldPole n))
        (𝓝 (criticalEtaMellin (1 - hellingerBetaOddOldPole n) *
          burnolOddHellingerIntegerCancellationValue n)) := by
    apply hmul.congr'
    filter_upwards with s
    unfold hellingerBetaOddReflectedMellin
      hellingerBetaCoPoissonMellin
    ring
  simpa only [hellingerBetaOddIntegerCancellationValue] using hmul'

theorem hellingerBetaEvenIntegerCancellationValue_ne_zero (n : ℕ) :
    hellingerBetaEvenIntegerCancellationValue n ≠ 0 :=
  mul_ne_zero (criticalEtaMellin_one_sub_evenOldPole_ne_zero n)
    (burnolEvenHellingerIntegerCancellationValue_ne_zero n)

theorem hellingerBetaOddIntegerCancellationValue_ne_zero (n : ℕ) :
    hellingerBetaOddIntegerCancellationValue n ≠ 0 :=
  mul_ne_zero (criticalEtaMellin_one_sub_oddOldPole_ne_zero n)
    (burnolOddHellingerIntegerCancellationValue_ne_zero n)

/-- Unconditional capstone for the exact scalar theorem on the card.

It packages the Beta recurrence, exact cancellation of every noninitial old
integer pole in both parities, exact nonzero residues at every new common
half-lattice pole, and the finite-exception polynomial no-go.  It does not
assert the separate vector-coface conjecture. -/
theorem hellingerBetaCoPoisson_resonanceTransmutation :
    (∀ a : ℝ, -(1 / 2 : ℝ) < a →
      hellingerHodgeBetaColumnComplex ((a + 1 : ℝ) : ℂ) =
        (((a + 1 / 2) / (a + 2) : ℝ) : ℂ) *
          hellingerHodgeBetaColumnComplex (a : ℂ)) ∧
    (∀ n : ℕ,
      Tendsto hellingerBetaEvenReflectedMellin
        (𝓝[≠] (hellingerBetaEvenOldPole n))
        (𝓝 (hellingerBetaEvenIntegerCancellationValue n)) ∧
      hellingerBetaEvenIntegerCancellationValue n ≠ 0) ∧
    (∀ n : ℕ,
      Tendsto hellingerBetaOddReflectedMellin
        (𝓝[≠] (hellingerBetaOddOldPole n))
        (𝓝 (hellingerBetaOddIntegerCancellationValue n)) ∧
      hellingerBetaOddIntegerCancellationValue n ≠ 0) ∧
    (∀ n : ℕ,
      hellingerBetaReflectedResidue n =
        (dirichletEta (-(1 : ℂ) - 2 * n) / (-(1 : ℂ) - 2 * n)) *
          (Complex.Gamma (3 / 2) /
            (((2 * n).factorial : ℂ) *
              Complex.Gamma (3 / 2 - 2 * n))) ∧
      Tendsto
        (fun s : ℂ =>
          (s - hellingerBetaReflectedHalfPole n) *
            hellingerBetaEvenReflectedMellin s)
        (𝓝[≠] (hellingerBetaReflectedHalfPole n))
        (𝓝 (hellingerBetaEvenReflectedResidue n)) ∧
      hellingerBetaEvenReflectedResidue n ≠ 0 ∧
      Tendsto
        (fun s : ℂ =>
          (s - hellingerBetaReflectedHalfPole n) *
            hellingerBetaOddReflectedMellin s)
        (𝓝[≠] (hellingerBetaReflectedHalfPole n))
        (𝓝 (hellingerBetaOddReflectedResidue n)) ∧
      hellingerBetaOddReflectedResidue n ≠ 0) ∧
    (∀ (p : Polynomial ℂ) (exceptional : Finset ℕ),
      (∀ n : ℕ, n ∉ exceptional →
        p.eval (hellingerBetaReflectedHalfPole n) *
          hellingerBetaEvenReflectedResidue n = 0) → p = 0) ∧
    (∀ (p : Polynomial ℂ) (exceptional : Finset ℕ),
      (∀ n : ℕ, n ∉ exceptional →
        p.eval (hellingerBetaReflectedHalfPole n) *
          hellingerBetaOddReflectedResidue n = 0) → p = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact hellingerHodgeBetaColumnComplex_real_add_one ha
  · intro n
    exact ⟨tendsto_hellingerBetaEvenReflectedMellin_oldPole n,
      hellingerBetaEvenIntegerCancellationValue_ne_zero n⟩
  · intro n
    exact ⟨tendsto_hellingerBetaOddReflectedMellin_oldPole n,
      hellingerBetaOddIntegerCancellationValue_ne_zero n⟩
  · intro n
    exact ⟨hellingerBetaReflectedResidue_eq_card_formula n,
      tendsto_hellingerBetaEvenReflectedMellin_residue n,
      hellingerBetaEvenReflectedResidue_ne_zero n,
      tendsto_hellingerBetaOddReflectedMellin_residue n,
      hellingerBetaOddReflectedResidue_ne_zero n⟩
  · intro p exceptional hcancel
    exact
      polynomial_eq_zero_of_cancels_hellingerBeta_even_half_residues_off_finset
        p exceptional hcancel
  · intro p exceptional hcancel
    exact
      polynomial_eq_zero_of_cancels_hellingerBeta_odd_half_residues_off_finset
        p exceptional hcancel

end

end RHTower
