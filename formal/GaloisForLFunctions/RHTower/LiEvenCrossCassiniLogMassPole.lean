import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniSource
import GaloisForLFunctions.RHTower.SquaredXiCompleteMonotonicity
import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic

/-!
# Retained Cassini poles in the even logarithmic-mass current

The fixed Cassini source defines the radial Euler response and its logarithmic-mass
current.  Exponential transport preserves a cubic pole at every actual squared Xi
node.  At each such pole the reflected mass is inside the source's zero-free disk,
so even reflection preserves the pole.  Every integer exponential translate retains
its intrinsic signed cubic coefficient.  Direct and reflected pole lattices are
disjoint, and positive real masses remain analytic.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Interior masses of the LI source window. -/
abbrev LiEvenCrossInteriorMass := {v : ℝ // 0 < v ∧ v ≤ 1 / 4}

/-- Literal complex continuation of the Cassini radial Euler response. -/
def liEvenCrossCassiniEulerDilation (z : ℂ) : ℂ :=
  2 * z * (z * deriv (logDeriv xiSquaredSeamCassiniSource) (1 - z) -
    logDeriv xiSquaredSeamCassiniSource (1 - z))

/-- Logarithmic-mass current, written in source derivatives. -/
def liEvenCrossCassiniLogMassCurrent (z : ℂ) : ℂ :=
  -4 * z ^ 3 * deriv (deriv (logDeriv xiSquaredSeamCassiniSource)) (1 - z) +
    12 * z ^ 2 * deriv (logDeriv xiSquaredSeamCassiniSource) (1 - z) -
      4 * z * logDeriv xiSquaredSeamCassiniSource (1 - z)

/-- Even logarithmic-mass germ of the first LI current. -/
def liEvenCrossCassiniEvenLogMassGerm (v : ℝ) (t : ℂ) : ℂ :=
  liEvenCrossCassiniLogMassCurrent ((v : ℂ) * Complex.exp t) +
    liEvenCrossCassiniLogMassCurrent ((v : ℂ) * Complex.exp (-t))

/-- Principal logarithmic coordinate of one actual squared Xi node. -/
def liEvenCrossCassiniLogMassPole (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) : ℂ :=
  Complex.log (-xiSquaredNode q / (v.val : ℂ))

/-- Intrinsic Xi multiplicity, preserved by the Cassini square coordinate. -/
def liEvenCrossCassiniPoleMultiplicity (q : XiZeroCopy) : ℕ :=
  Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1 : ℂ))

theorem liEvenCrossCassiniPoleMultiplicity_pos (q : XiZeroCopy) :
    0 < liEvenCrossCassiniPoleMultiplicity q := by
  have hpos := xi_divisor_pos_on_support q.1
  unfold liEvenCrossCassiniPoleMultiplicity
  omega

private theorem cassiniSource_one_sub_positive_ne_zero {y : ℝ} (hy : 0 < y) :
    xiSquaredSeamCassiniSource (1 - (y : ℂ)) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := (xiSquaredSeamCassiniSource_eq_zero_iff_exists_zeroCopy _).mp hzero
  have hnode : xiSquaredNode q = -(y : ℂ) := by
    unfold xiSquaredSeamCassiniZero at hq
    unfold xiSquaredNode
    linear_combination hq
  have hpos := xiSquaredNode_re_pos q
  rw [hnode] at hpos
  simp only [Complex.neg_re, Complex.ofReal_re] at hpos
  linarith

private theorem meromorphicAt_cassiniLogDeriv (u : ℂ) :
    MeromorphicAt (logDeriv xiSquaredSeamCassiniSource) u := by
  exact (differentiable_xiSquaredSeamCassiniSource.analyticAt u).deriv.meromorphicAt.div
    (differentiable_xiSquaredSeamCassiniSource.analyticAt u).meromorphicAt

theorem meromorphicAt_liEvenCrossCassiniLogMassCurrent (z : ℂ) :
    MeromorphicAt liEvenCrossCassiniLogMassCurrent z := by
  have h0 := (meromorphicAt_cassiniLogDeriv (1 - z)).comp_analyticAt
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z)
  have h1 := (meromorphicAt_cassiniLogDeriv (1 - z)).deriv.comp_analyticAt
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z)
  have h2 := (meromorphicAt_cassiniLogDeriv (1 - z)).deriv.deriv.comp_analyticAt
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z)
  exact ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => -4 * w ^ 3) z).meromorphicAt.mul h2).add
    ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => 12 * w ^ 2) z).meromorphicAt.mul h1) |>.sub
      ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => 4 * w) z).meromorphicAt.mul h0)

theorem meromorphicOn_liEvenCrossCassiniEvenLogMassGerm (v : ℝ) :
    MeromorphicOn (liEvenCrossCassiniEvenLogMassGerm v) Set.univ := by
  intro t _
  exact ((meromorphicAt_liEvenCrossCassiniLogMassCurrent _).comp_analyticAt
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (v : ℂ) * Complex.exp w) t)).add
      ((meromorphicAt_liEvenCrossCassiniLogMassCurrent _).comp_analyticAt
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => (v : ℂ) * Complex.exp (-w)) t))

theorem liEvenCrossCassiniEvenLogMassGerm_even (v : ℝ) :
    Function.Even (liEvenCrossCassiniEvenLogMassGerm v) := by
  intro t
  simp [liEvenCrossCassiniEvenLogMassGerm, add_comm]

theorem analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero
    {z : ℂ} (hz : xiSquaredSeamCassiniSource (1 - z) ≠ 0) :
    AnalyticAt ℂ liEvenCrossCassiniLogMassCurrent z := by
  have hL : AnalyticAt ℂ (logDeriv xiSquaredSeamCassiniSource) (1 - z) :=
    (differentiable_xiSquaredSeamCassiniSource.analyticAt _).deriv.div
      (differentiable_xiSquaredSeamCassiniSource.analyticAt _) hz
  have h0 := hL.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z)
  have h1 := hL.deriv.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z)
  have h2 := hL.deriv.deriv.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 1 - w) z)
  exact ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => -4 * w ^ 3) z).mul h2).add
    ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => 12 * w ^ 2) z).mul h1) |>.sub
      ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => 4 * w) z).mul h0)

theorem analyticAt_liEvenCrossCassiniEvenLogMassGerm_real
    {v : ℝ} (hv : 0 < v) (t : ℝ) :
    AnalyticAt ℂ (liEvenCrossCassiniEvenLogMassGerm v) (t : ℂ) := by
  have hp : 0 < v * Real.exp t := mul_pos hv (Real.exp_pos _)
  have hm : 0 < v * Real.exp (-t) := mul_pos hv (Real.exp_pos _)
  have h0 := analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero
    (cassiniSource_one_sub_positive_ne_zero hp)
  have h1 := analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero
    (cassiniSource_one_sub_positive_ne_zero hm)
  have he0 : (v : ℂ) * Complex.exp (t : ℂ) = (v * Real.exp t : ℝ) := by
    simp [Complex.ofReal_exp]
  have he1 : (v : ℂ) * Complex.exp (-(t : ℂ)) = (v * Real.exp (-t) : ℝ) := by
    simp [Complex.ofReal_exp]
  rw [← he0] at h0
  rw [← he1] at h1
  have h0c : AnalyticAt ℂ (fun w : ℂ =>
      liEvenCrossCassiniLogMassCurrent ((v : ℂ) * Complex.exp w)) (t : ℂ) :=
    h0.comp (f := fun w : ℂ => (v : ℂ) * Complex.exp w) (x := (t : ℂ))
      (by fun_prop)
  have h1c : AnalyticAt ℂ (fun w : ℂ =>
      liEvenCrossCassiniLogMassCurrent ((v : ℂ) * Complex.exp (-w))) (t : ℂ) :=
    h1.comp (f := fun w : ℂ => (v : ℂ) * Complex.exp (-w)) (x := (t : ℂ))
      (by fun_prop)
  exact h0c.add h1c

private theorem cassiniSource_one_add_sq (z : ℂ) :
    xiSquaredSeamCassiniSource (1 + z ^ 2) = XiC z := by
  simp only [xiSquaredSeamCassiniSource, add_sub_cancel_left]
  exact xiSquaredSeamEntireQuotient_sq z

theorem liEvenCrossCassiniSource_conj (u : ℂ) :
    xiSquaredSeamCassiniSource (conj u) = conj (xiSquaredSeamCassiniSource u) := by
  let a := Complex.sqrt (u - 1)
  have ha : a ^ 2 = u - 1 := GaloisForLFunctions.HTGeometry.complex_sqrt_sq _
  have hu : 1 + a ^ 2 = u := by rw [ha]; ring
  have huc : 1 + conj a ^ 2 = conj u := by
    simpa using congrArg conj hu
  rw [← huc, cassiniSource_one_add_sq, XiC_conj,
    ← cassiniSource_one_add_sq, hu]

private theorem deriv_conj_of_schwarz {f : ℂ → ℂ}
    (hs : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    deriv f (conj z) = conj (deriv f z) := by
  have hfun : conj ∘ f ∘ conj = f := by
    funext w
    simpa [Function.comp_apply] using (hs (conj w)).symm
  have hd := deriv_conj_conj (f := f)
  rw [hfun] at hd
  simpa [Function.comp_apply] using congrFun hd (conj z)

private theorem cassiniLogDeriv_conj (u : ℂ) :
    logDeriv xiSquaredSeamCassiniSource (conj u) =
      conj (logDeriv xiSquaredSeamCassiniSource u) := by
  simp only [logDeriv_apply, liEvenCrossCassiniSource_conj,
    deriv_conj_of_schwarz liEvenCrossCassiniSource_conj, map_div₀]

theorem liEvenCrossCassiniLogMassCurrent_conj (z : ℂ) :
    liEvenCrossCassiniLogMassCurrent (conj z) =
      conj (liEvenCrossCassiniLogMassCurrent z) := by
  have h1 := deriv_conj_of_schwarz cassiniLogDeriv_conj (1 - z)
  have h2 := deriv_conj_of_schwarz (deriv_conj_of_schwarz cassiniLogDeriv_conj) (1 - z)
  have h0 := cassiniLogDeriv_conj (1-z)
  simp only [map_sub, map_one] at h0 h1 h2
  simp only [liEvenCrossCassiniLogMassCurrent, map_sub, map_add, map_mul, map_pow,
    map_ofNat, map_neg, h0, h1, h2]

theorem liEvenCrossCassiniEvenLogMassGerm_conj (v : ℝ) (t : ℂ) :
    liEvenCrossCassiniEvenLogMassGerm v (conj t) =
      conj (liEvenCrossCassiniEvenLogMassGerm v t) := by
  have h0 := liEvenCrossCassiniLogMassCurrent_conj ((v : ℂ) * Complex.exp t)
  have h1 := liEvenCrossCassiniLogMassCurrent_conj ((v : ℂ) * Complex.exp (-t))
  simpa only [liEvenCrossCassiniEvenLogMassGerm, map_add, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, map_neg] using congrArg₂ (fun a b : ℂ => a+b) h0 h1

/-- The endpoint height gap gives a uniform distance of every squared node from zero. -/
theorem liEvenCross_squaredNode_norm_lower (q : XiZeroCopy) :
    (81 / 4 : ℝ) < ‖xiSquaredNode q‖ := by
  have h1 := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have h2 := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hre : (81 / 4 : ℝ) < (xiSquaredNode q).re := by
    rw [xiSquaredNode_re]
    linarith
  exact hre.trans_le (Complex.re_le_norm _)

private theorem cassiniSource_one_sub_small_ne_zero {z : ℂ} (hz : ‖z‖ < 1) :
    xiSquaredSeamCassiniSource (1 - z) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ := (xiSquaredSeamCassiniSource_eq_zero_iff_exists_zeroCopy _).mp hzero
  have hnode : xiSquaredNode q = -z := by
    unfold xiSquaredSeamCassiniZero at hq
    unfold xiSquaredNode
    linear_combination hq
  have hbig := liEvenCross_squaredNode_norm_lower q
  rw [hnode, norm_neg] at hbig
  linarith

private theorem logDeriv_order_neg_one {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hfinite : analyticOrderAt f c ≠ ⊤) (hzero : f c = 0) :
    meromorphicOrderAt (logDeriv f) c = ((-1 : ℤ) : WithTop ℤ) := by
  have hmne : (analyticOrderAt f c).toNat ≠ 0 := by
    intro h0
    have horder0 : analyticOrderAt f c = 0 := by
      rw [(ENat.coe_toNat hfinite).symm, h0]
      rfl
    rcases analyticOrderAt_eq_zero.mp horder0 with h | h
    · exact h hf
    · exact h hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have horder : analyticOrderAt f c = (k + 1 : ℕ) := by
    calc
      analyticOrderAt f c = ((analyticOrderAt f c).toNat : ℕ∞) :=
        (ENat.coe_toNat hfinite).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderiv : analyticOrderAt (deriv f) c = k :=
    analyticOrderAt_deriv_of_pos hf horder
  rw [show logDeriv f = deriv f / f by rfl]
  rw [meromorphicOrderAt_div hf.deriv.meromorphicAt hf.meromorphicAt,
    hf.deriv.meromorphicOrderAt_eq, hf.meromorphicOrderAt_eq,
    hderiv, horder, ENat.map_coe, ENat.map_coe]
  exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)

/-- The highest source derivative retains a cubic pole at every actual squared node. -/
theorem meromorphicOrderAt_liEvenCrossCassiniLogMassCurrent_node (q : XiZeroCopy) :
    meromorphicOrderAt liEvenCrossCassiniLogMassCurrent (-xiSquaredNode q) =
      ((-3 : ℤ) : WithTop ℤ) := by
  let p := -xiSquaredNode q
  let c := xiSquaredSeamCassiniZero q
  let L := logDeriv xiSquaredSeamCassiniSource
  have hpc : 1 - p = c := by
    simp [p, c, xiSquaredNode, xiSquaredSeamCassiniZero]
  have hpne : p ≠ 0 := neg_ne_zero.mpr (xiSquaredNode_ne_zero q)
  have hL : meromorphicOrderAt L c = ((-1 : ℤ) : WithTop ℤ) :=
    logDeriv_order_neg_one (differentiable_xiSquaredSeamCassiniSource.analyticAt _)
      (xiSquaredSeamCassiniSource_order_ne_top _) (xiSquaredSeamCassiniSource_zero q)
  have hL1 : meromorphicOrderAt (deriv L) c = ((-2 : ℤ) : WithTop ℤ) := by
    simpa using meromorphicOrderAt_deriv_eq_sub_one (by norm_num : ((-1 : ℤ) : ℂ) ≠ 0) hL
  have hL2 : meromorphicOrderAt (deriv (deriv L)) c = ((-3 : ℤ) : WithTop ℤ) := by
    simpa using meromorphicOrderAt_deriv_eq_sub_one (by norm_num : ((-2 : ℤ) : ℂ) ≠ 0) hL1
  have hshift : AnalyticAt ℂ (fun z : ℂ => 1 - z) p := by fun_prop
  have hshiftD : deriv (fun z : ℂ => 1 - z) p ≠ 0 := by simp
  have h0 : meromorphicOrderAt (fun z : ℂ => L (1 - z)) p = ((-1 : ℤ) : WithTop ℤ) := by
    rw [← Function.comp_def, meromorphicOrderAt_comp_of_deriv_ne_zero hshift hshiftD, hpc]
    exact hL
  have h1 : meromorphicOrderAt (fun z : ℂ => deriv L (1 - z)) p = ((-2 : ℤ) : WithTop ℤ) := by
    rw [← Function.comp_def, meromorphicOrderAt_comp_of_deriv_ne_zero hshift hshiftD, hpc]
    exact hL1
  have h2 : meromorphicOrderAt (fun z : ℂ => deriv (deriv L) (1 - z)) p =
      ((-3 : ℤ) : WithTop ℤ) := by
    rw [← Function.comp_def, meromorphicOrderAt_comp_of_deriv_ne_zero hshift hshiftD, hpc]
    exact hL2
  let A := fun z : ℂ => -4 * z ^ 3 * deriv (deriv L) (1 - z)
  let B := fun z : ℂ => 12 * z ^ 2 * deriv L (1 - z)
  let C := fun z : ℂ => -(4 * z * L (1 - z))
  have hA : meromorphicOrderAt A p = ((-3 : ℤ) : WithTop ℤ) := by
    rw [show A = (fun z : ℂ => -4 * z ^ 3) * (fun z : ℂ => deriv (deriv L) (1-z)) by rfl,
      meromorphicOrderAt_mul_of_ne_zero (by fun_prop) (by dsimp; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hpne))]
    exact h2
  have hB : meromorphicOrderAt B p = ((-2 : ℤ) : WithTop ℤ) := by
    rw [show B = (fun z : ℂ => 12 * z ^ 2) * (fun z : ℂ => deriv L (1-z)) by rfl,
      meromorphicOrderAt_mul_of_ne_zero (by fun_prop) (by dsimp; exact mul_ne_zero (by norm_num) (pow_ne_zero _ hpne))]
    exact h1
  have hC : meromorphicOrderAt C p = ((-1 : ℤ) : WithTop ℤ) := by
    rw [show C = -( (fun z : ℂ => 4 * z) * (fun z : ℂ => L (1-z))) by rfl,
      ← meromorphicOrderAt_neg,
      meromorphicOrderAt_mul_of_ne_zero (by fun_prop) (by dsimp; exact mul_ne_zero (by norm_num) hpne)]
    exact h0
  have hCM : MeromorphicAt C p := by
    have h := (meromorphicAt_cassiniLogDeriv (1-p)).comp_analyticAt hshift
    exact ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => 4*z) p).meromorphicAt.mul h).neg
  have hBM : MeromorphicAt B p := by
    have h := (meromorphicAt_cassiniLogDeriv (1-p)).deriv.comp_analyticAt hshift
    exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 12*z^2) p).meromorphicAt.mul h
  have hBC : meromorphicOrderAt (B+C) p = ((-2 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_add_eq_left_of_lt hCM (by
      rw [hB, hC]
      exact_mod_cast (show (-2 : ℤ) < -1 by norm_num))]
    exact hB
  have hABC : meromorphicOrderAt (A+(B+C)) p = ((-3 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_add_eq_left_of_lt (hBM.add hCM) (by
      rw [hA, hBC]
      exact_mod_cast (show (-3 : ℤ) < -2 by norm_num))]
    exact hA
  have hfun : liEvenCrossCassiniLogMassCurrent = A+(B+C) := by
    funext z
    simp only [liEvenCrossCassiniLogMassCurrent, A, B, C, L, Pi.add_apply]
    ring
  rw [hfun]
  exact hABC

theorem liEvenCrossCassiniLogMassPole_direct_mass (v : LiEvenCrossInteriorMass)
    (q : XiZeroCopy) :
    (v.val : ℂ) * Complex.exp (liEvenCrossCassiniLogMassPole v q) = -xiSquaredNode q := by
  have hvne : (v.val : ℂ) ≠ 0 := by exact_mod_cast v.property.1.ne'
  rw [liEvenCrossCassiniLogMassPole, Complex.exp_log
    (div_ne_zero (neg_ne_zero.mpr (xiSquaredNode_ne_zero q)) hvne)]
  field_simp

theorem liEvenCrossCassiniLogMassPole_reflected_mass (v : LiEvenCrossInteriorMass)
    (q : XiZeroCopy) :
    (v.val : ℂ) * Complex.exp (-liEvenCrossCassiniLogMassPole v q) =
      -(v.val : ℂ) ^ 2 / xiSquaredNode q := by
  have hvne : (v.val : ℂ) ≠ 0 := by exact_mod_cast v.property.1.ne'
  rw [Complex.exp_neg, liEvenCrossCassiniLogMassPole, Complex.exp_log
    (div_ne_zero (neg_ne_zero.mpr (xiSquaredNode_ne_zero q)) hvne)]
  field_simp

/-- The reflected mass is uniformly inside the zero-free source disk. -/
theorem liEvenCrossCassiniLogMassPole_reflected_mass_norm (v : LiEvenCrossInteriorMass)
    (q : XiZeroCopy) :
    ‖(v.val : ℂ) * Complex.exp (-liEvenCrossCassiniLogMassPole v q)‖ < (1 / 150 : ℝ) := by
  rw [liEvenCrossCassiniLogMassPole_reflected_mass, norm_div, norm_neg, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg v.property.1.le]
  have hbig := liEvenCross_squaredNode_norm_lower q
  have hnorm : 0 < ‖xiSquaredNode q‖ := norm_pos_iff.mpr (xiSquaredNode_ne_zero q)
  rw [div_lt_iff₀ hnorm]
  have hv2 : v.val ^ 2 ≤ 1 / 16 := by nlinarith [v.property.2, v.property.1]
  nlinarith

theorem meromorphicOrderAt_liEvenCrossCassiniLogMassCurrent_exp
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t))
      (liEvenCrossCassiniLogMassPole v q) = ((-3 : ℤ) : WithTop ℤ) := by
  have he := liEvenCrossCassiniLogMassPole_direct_mass v q
  have hd : deriv (fun t : ℂ => (v.val : ℂ) * Complex.exp t)
      (liEvenCrossCassiniLogMassPole v q) ≠ 0 := by
    rw [((Complex.hasDerivAt_exp _).const_mul (v.val : ℂ)).deriv, he]
    exact neg_ne_zero.mpr (xiSquaredNode_ne_zero q)
  rw [← Function.comp_def,
    meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) hd, he]
  exact meromorphicOrderAt_liEvenCrossCassiniLogMassCurrent_node q

theorem analyticAt_liEvenCrossCassiniLogMassCurrent_reflected_exp
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    AnalyticAt ℂ
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp (-t)))
      (liEvenCrossCassiniLogMassPole v q) := by
  have hsmall := liEvenCrossCassiniLogMassPole_reflected_mass_norm v q
  have hz := cassiniSource_one_sub_small_ne_zero
    (hsmall.trans (by norm_num : (1 / 150 : ℝ) < 1))
  exact (analyticAt_liEvenCrossCassiniLogMassCurrent_of_source_ne_zero hz).comp
    (f := fun t : ℂ => (v.val : ℂ) * Complex.exp (-t))
    (x := liEvenCrossCassiniLogMassPole v q) (by fun_prop)

/-- Every actual squared Xi node survives even logarithmic reflection as an exact cubic pole. -/
theorem meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_pole
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val)
      (liEvenCrossCassiniLogMassPole v q) = ((-3 : ℤ) : WithTop ℤ) := by
  have hD := meromorphicOrderAt_liEvenCrossCassiniLogMassCurrent_exp v q
  have hR := analyticAt_liEvenCrossCassiniLogMassCurrent_reflected_exp v q
  have hlt : meromorphicOrderAt
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t))
      (liEvenCrossCassiniLogMassPole v q) < meromorphicOrderAt
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp (-t)))
      (liEvenCrossCassiniLogMassPole v q) := by
    rw [hD]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-3 : ℤ) < 0 by norm_num)) hR.meromorphicOrderAt_nonneg
  change meromorphicOrderAt
    ((fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t)) +
      (fun t : ℂ => liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp (-t))))
    (liEvenCrossCassiniLogMassPole v q) = _
  rw [meromorphicOrderAt_add_eq_left_of_lt hR.meromorphicAt hlt]
  exact hD

theorem not_analyticAt_liEvenCrossCassiniEvenLogMassGerm_pole
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    ¬ AnalyticAt ℂ (liEvenCrossCassiniEvenLogMassGerm v.val)
      (liEvenCrossCassiniLogMassPole v q) := by
  intro h
  have hn := h.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_pole] at hn
  have hneg : ((-3 : ℤ) : WithTop ℤ) < 0 := by
    exact_mod_cast (show (-3 : ℤ) < 0 by norm_num)
  exact not_le_of_gt hneg hn

/-- Every interior mass has a genuine singularity of the literal even current germ. -/
theorem exists_liEvenCrossCassiniEvenLogMassGerm_cubic_pole (v : LiEvenCrossInteriorMass) :
    ∃ t : ℂ, meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val) t =
      ((-3 : ℤ) : WithTop ℤ) := by
  let q : XiZeroCopy := Classical.choice (inferInstance : Nonempty XiZeroCopy)
  exact ⟨liEvenCrossCassiniLogMassPole v q,
    meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_pole v q⟩

/-- The mass-coordinate cubic principal coefficient keeps the exact Xi multiplicity. -/
theorem liEvenCrossCassiniLogMassCurrent_cubic_coefficient_node (q : XiZeroCopy) :
    Tendsto (fun z : ℂ => (z + xiSquaredNode q) ^ 3 * liEvenCrossCassiniLogMassCurrent z)
      (𝓝[≠] (-xiSquaredNode q))
      (𝓝 (8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ) * (-xiSquaredNode q) ^ 3)) := by
  let p := -xiSquaredNode q
  let c := xiSquaredSeamCassiniZero q
  let m := liEvenCrossCassiniPoleMultiplicity q
  let L := logDeriv xiSquaredSeamCassiniSource
  have hpc : 1 - p = c := by
    simp [p, c, xiSquaredNode, xiSquaredSeamCassiniZero]
  have hs : Tendsto (fun z : ℂ => 1-z) (𝓝[≠] p) (𝓝[≠] c) := by
    rw [← hpc]
    exact ((hasDerivAt_id p).const_sub 1).tendsto_nhdsNE (by norm_num)
  have hsub (z : ℂ) : (1-z)-c = -(z-p) := by rw [← hpc]; ring
  have hm : (analyticOrderAt xiSquaredSeamCassiniSource c).toNat = m := by
    simp [c, m, liEvenCrossCassiniPoleMultiplicity,
      analyticOrderAt_xiSquaredSeamCassiniSource_cassiniZero_eq_multiplicity]
  have hr (j : ℕ) := (logDeriv_iteratedDeriv_residue_of_zero
    (differentiable_xiSquaredSeamCassiniSource.analyticAt c)
    (xiSquaredSeamCassiniSource_order_ne_top c) (xiSquaredSeamCassiniSource_zero q) j).comp hs
  have hfun : (fun t : ℂ => deriv xiSquaredSeamCassiniSource t /
      xiSquaredSeamCassiniSource t) = L := rfl
  rw [hfun] at hr
  have h0 : Tendsto (fun z : ℂ => (z-p) * L (1-z)) (𝓝[≠] p) (𝓝 (-(m : ℂ))) := by
    convert (hr 0).neg using 1 <;>
      simp [hsub, hm, iteratedDeriv_zero]
    funext z
    ring
  have h1 : Tendsto (fun z : ℂ => (z-p)^2 * deriv L (1-z)) (𝓝[≠] p) (𝓝 (-(m : ℂ))) := by
    convert hr 1 using 1 <;> simp [Function.comp_def, hsub, hm, iteratedDeriv_one]
    funext z
    ring
  have h2 : Tendsto (fun z : ℂ => (z-p)^3 * deriv (deriv L) (1-z))
      (𝓝[≠] p) (𝓝 (-2*(m : ℂ))) := by
    convert (hr 2).neg using 1 <;>
      simp [hsub, hm, iteratedDeriv_succ, iteratedDeriv_zero]
    · funext z
      ring
    · ring
  have hz : Tendsto (fun z : ℂ => z) (𝓝[≠] p) (𝓝 p) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun z : ℂ => z-p) (𝓝[≠] p) (𝓝 (0 : ℂ)) := by
    simpa using hz.sub (show Tendsto (fun _ : ℂ => p) (𝓝[≠] p) (𝓝 p) from tendsto_const_nhds)
  have hlim := ((hz.pow 3).mul h2).const_mul (-4) |>.add
    (((hz.pow 2).mul (hd.mul h1)).const_mul 12) |>.sub
      ((hz.mul ((hd.pow 2).mul h0)).const_mul 4)
  convert hlim using 1
  · funext z
    simp only [liEvenCrossCassiniLogMassCurrent, p, L]
    ring
  · dsimp only [p, m]
    congr 1
    ring

/-- Exponential transport cancels the mass scale in the cubic coefficient. -/
theorem liEvenCrossCassiniLogMassCurrent_cubic_coefficient_exp
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    Tendsto (fun t : ℂ => (t-liEvenCrossCassiniLogMassPole v q)^3 *
      liEvenCrossCassiniLogMassCurrent ((v.val : ℂ) * Complex.exp t))
      (𝓝[≠] liEvenCrossCassiniLogMassPole v q)
      (𝓝 (8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ))) := by
  let t0 := liEvenCrossCassiniLogMassPole v q
  let p := -xiSquaredNode q
  let g := fun t : ℂ => (v.val : ℂ) * Complex.exp t
  have hpne : p ≠ 0 := neg_ne_zero.mpr (xiSquaredNode_ne_zero q)
  have he : g t0 = p := liEvenCrossCassiniLogMassPole_direct_mass v q
  have hg : HasDerivAt g p t0 := by
    have h := (Complex.hasDerivAt_exp t0).const_mul (v.val : ℂ)
    change HasDerivAt g (g t0) t0 at h
    rw [he] at h
    exact h
  have hmap : Tendsto g (𝓝[≠] t0) (𝓝[≠] p) := by
    simpa only [he] using hg.tendsto_nhdsNE hpne
  have hmass : Tendsto (fun t : ℂ => (g t-p)^3 * liEvenCrossCassiniLogMassCurrent (g t))
      (𝓝[≠] t0) (𝓝 (8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ) * p^3)) := by
    simpa only [Function.comp_def, p, sub_neg_eq_add] using
      (liEvenCrossCassiniLogMassCurrent_cubic_coefficient_node q).comp hmap
  have hlim := hmass.div (hg.tendsto_slope.pow 3) (pow_ne_zero 3 hpne)
  have htarget : 8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ) * p^3 / p^3 =
      8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ) := by field_simp
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hmap.eventually self_mem_nhdsWithin] with t ht hgt
  have htne : t-t0 ≠ 0 := sub_ne_zero.mpr ht
  have hgne : g t-p ≠ 0 := sub_ne_zero.mpr hgt
  change (g t-p)^3 * liEvenCrossCassiniLogMassCurrent (g t) / (slope g t0 t)^3 =
    (t-t0)^3 * liEvenCrossCassiniLogMassCurrent (g t)
  rw [slope_def_field, he]
  field_simp [htne, hgne]

/-- Even reflection preserves the intrinsic multiplicity in the cubic principal coefficient. -/
theorem liEvenCrossCassiniEvenLogMassGerm_cubic_coefficient
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    Tendsto (fun t : ℂ => (t-liEvenCrossCassiniLogMassPole v q)^3 *
      liEvenCrossCassiniEvenLogMassGerm v.val t)
      (𝓝[≠] liEvenCrossCassiniLogMassPole v q)
      (𝓝 (8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ))) := by
  have hD := liEvenCrossCassiniLogMassCurrent_cubic_coefficient_exp v q
  have hR : Tendsto (fun t : ℂ => liEvenCrossCassiniLogMassCurrent
      ((v.val : ℂ) * Complex.exp (-t))) (𝓝[≠] liEvenCrossCassiniLogMassPole v q)
      (𝓝 (liEvenCrossCassiniLogMassCurrent
        ((v.val : ℂ) * Complex.exp (-liEvenCrossCassiniLogMassPole v q)))) :=
    (analyticAt_liEvenCrossCassiniLogMassCurrent_reflected_exp v q).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have h0 : Tendsto (fun t : ℂ => t-liEvenCrossCassiniLogMassPole v q)
      (𝓝[≠] liEvenCrossCassiniLogMassPole v q) (𝓝 (0 : ℂ)) := by
    have hi : Tendsto (fun t : ℂ => t) (𝓝[≠] liEvenCrossCassiniLogMassPole v q)
        (𝓝 (liEvenCrossCassiniLogMassPole v q)) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hi.sub (show Tendsto (fun _ : ℂ => liEvenCrossCassiniLogMassPole v q)
      (𝓝[≠] liEvenCrossCassiniLogMassPole v q) (𝓝 (liEvenCrossCassiniLogMassPole v q)) from
        tendsto_const_nhds)
  convert hD.add ((h0.pow 3).mul hR) using 1
  · funext t
    simp [liEvenCrossCassiniEvenLogMassGerm, mul_add]
  · simp

/-- Reflection reverses the oriented cubic coefficient while preserving its multiplicity. -/
theorem liEvenCrossCassiniEvenLogMassGerm_reflected_cubic_coefficient
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    Tendsto (fun t : ℂ => (t+liEvenCrossCassiniLogMassPole v q)^3 *
      liEvenCrossCassiniEvenLogMassGerm v.val t)
      (𝓝[≠] (-liEvenCrossCassiniLogMassPole v q))
      (𝓝 (-8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ))) := by
  have hmap : Tendsto (fun t : ℂ => -t)
      (𝓝[≠] (-liEvenCrossCassiniLogMassPole v q))
      (𝓝[≠] liEvenCrossCassiniLogMassPole v q) := by
    have hd : HasDerivAt (fun t : ℂ => -t) (-1 : ℂ)
        (-liEvenCrossCassiniLogMassPole v q) :=
      (hasDerivAt_id (-liEvenCrossCassiniLogMassPole v q)).neg
    simpa only [neg_neg] using hd.tendsto_nhdsNE (by norm_num : (-1 : ℂ) ≠ 0)
  convert ((liEvenCrossCassiniEvenLogMassGerm_cubic_coefficient v q).comp hmap).neg using 1
  · funext t
    simp only [Function.comp_apply, liEvenCrossCassiniEvenLogMassGerm_even v.val t]
    ring
  · congr 1
    ring

theorem meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_reflected_pole
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) :
    meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val)
      (-liEvenCrossCassiniLogMassPole v q) = ((-3 : ℤ) : WithTop ℤ) := by
  have hfun : liEvenCrossCassiniEvenLogMassGerm v.val ∘ (fun t : ℂ => -t) =
      liEvenCrossCassiniEvenLogMassGerm v.val := by
    funext t
    exact liEvenCrossCassiniEvenLogMassGerm_even v.val t
  rw [← hfun, meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp), neg_neg]
  exact meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_pole v q

/-- A direct pole and a reflected pole cannot collide, even for different Xi nodes. -/
theorem liEvenCrossCassiniLogMassPole_ne_reflected (v : LiEvenCrossInteriorMass)
    (q r : XiZeroCopy) :
    liEvenCrossCassiniLogMassPole v q ≠ -liEvenCrossCassiniLogMassPole v r := by
  intro h
  have he := congrArg (fun t : ℂ => ‖(v.val : ℂ) * Complex.exp t‖) h
  rw [liEvenCrossCassiniLogMassPole_direct_mass, norm_neg] at he
  have hsmall := liEvenCrossCassiniLogMassPole_reflected_mass_norm v r
  rw [← he] at hsmall
  have hbig := liEvenCross_squaredNode_norm_lower q
  linarith

/-- Integer periods of the exponential logarithmic-mass coordinate. -/
def liEvenCrossCassiniLogMassPeriod (k : ℤ) : ℂ :=
  (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

theorem liEvenCrossCassiniEvenLogMassGerm_periodic (v : ℝ) (k : ℤ) :
    Function.Periodic (liEvenCrossCassiniEvenLogMassGerm v)
      (liEvenCrossCassiniLogMassPeriod k) := by
  intro t
  have hp : Function.Periodic Complex.exp (liEvenCrossCassiniLogMassPeriod k) :=
    Complex.exp_periodic.int_mul k
  have hm : Complex.exp (-(t + liEvenCrossCassiniLogMassPeriod k)) =
      Complex.exp (-t) := by
    simpa only [neg_add, sub_eq_add_neg] using hp.sub_eq (-t)
  simp only [liEvenCrossCassiniEvenLogMassGerm, hp t, hm]

private theorem orderAt_periodic_translate (f : ℂ → ℂ) (a d : ℂ)
    (hper : Function.Periodic f d) :
    meromorphicOrderAt f (a + d) = meromorphicOrderAt f a := by
  have hfun : f ∘ (fun t : ℂ => t + d) = f := funext hper
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := f) (g := fun t : ℂ => t + d) (x := a) (by fun_prop) (by simp)
  rw [hfun] at ho
  exact ho.symm

private theorem cubicLimit_periodic_translate (f : ℂ → ℂ) (a d c : ℂ)
    (hper : Function.Periodic f d)
    (h : Tendsto (fun t : ℂ => (t - a) ^ 3 * f t) (𝓝[≠] a) (𝓝 c)) :
    Tendsto (fun t : ℂ => (t - (a + d)) ^ 3 * f t)
      (𝓝[≠] (a + d)) (𝓝 c) := by
  have hd : HasDerivAt (fun t : ℂ => t - d) 1 (a + d) :=
    (hasDerivAt_id (a + d)).sub_const d
  have hm : Tendsto (fun t : ℂ => t - d) (𝓝[≠] (a + d)) (𝓝[≠] a) := by
    simpa only [add_sub_cancel_right] using
      hd.tendsto_nhdsNE (by norm_num : (1 : ℂ) ≠ 0)
  convert h.comp hm using 1
  funext t
  simp only [Function.comp_apply, hper.sub_eq t]
  congr 1
  ring

theorem liEvenCrossCassiniLogMassPole_periodic_direct_mass
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) (k : ℤ) :
    (v.val : ℂ) * Complex.exp
      (liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k) =
        -xiSquaredNode q := by
  have hp : Function.Periodic Complex.exp (liEvenCrossCassiniLogMassPeriod k) :=
    Complex.exp_periodic.int_mul k
  rw [hp, liEvenCrossCassiniLogMassPole_direct_mass]

theorem liEvenCrossCassiniLogMassPole_periodic_reflected_mass
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) (k : ℤ) :
    (v.val : ℂ) * Complex.exp
      (-liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k) =
        -(v.val : ℂ) ^ 2 / xiSquaredNode q := by
  have hp : Function.Periodic Complex.exp (liEvenCrossCassiniLogMassPeriod k) :=
    Complex.exp_periodic.int_mul k
  rw [hp, liEvenCrossCassiniLogMassPole_reflected_mass]

/-- Every direct periodic pole retains order three. -/
theorem meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_periodic_pole
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) (k : ℤ) :
    meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val)
      (liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k) =
        ((-3 : ℤ) : WithTop ℤ) := by
  exact (orderAt_periodic_translate _ _ _
    (liEvenCrossCassiniEvenLogMassGerm_periodic v.val k)).trans
      (meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_pole v q)

/-- Every reflected periodic pole retains order three. -/
theorem meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_periodic_reflected_pole
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) (k : ℤ) :
    meromorphicOrderAt (liEvenCrossCassiniEvenLogMassGerm v.val)
      (-liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k) =
        ((-3 : ℤ) : WithTop ℤ) := by
  exact (orderAt_periodic_translate _ _ _
    (liEvenCrossCassiniEvenLogMassGerm_periodic v.val k)).trans
      (meromorphicOrderAt_liEvenCrossCassiniEvenLogMassGerm_reflected_pole v q)

/-- A direct pole lattice preserves the positive intrinsic multiplicity coefficient. -/
theorem liEvenCrossCassiniEvenLogMassGerm_periodic_cubic_coefficient
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) (k : ℤ) :
    Tendsto (fun t : ℂ =>
      (t - (liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k)) ^ 3 *
        liEvenCrossCassiniEvenLogMassGerm v.val t)
      (𝓝[≠] (liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k))
      (𝓝 (8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ))) :=
  cubicLimit_periodic_translate _ _ _ _
    (liEvenCrossCassiniEvenLogMassGerm_periodic v.val k)
    (liEvenCrossCassiniEvenLogMassGerm_cubic_coefficient v q)

/-- A reflected pole lattice preserves the negative intrinsic multiplicity coefficient. -/
theorem liEvenCrossCassiniEvenLogMassGerm_periodic_reflected_cubic_coefficient
    (v : LiEvenCrossInteriorMass) (q : XiZeroCopy) (k : ℤ) :
    Tendsto (fun t : ℂ =>
      (t - (-liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k)) ^ 3 *
        liEvenCrossCassiniEvenLogMassGerm v.val t)
      (𝓝[≠] (-liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k))
      (𝓝 (-8 * (liEvenCrossCassiniPoleMultiplicity q : ℂ))) := by
  apply cubicLimit_periodic_translate _ _ _ _
    (liEvenCrossCassiniEvenLogMassGerm_periodic v.val k)
  simpa only [sub_neg_eq_add] using
    liEvenCrossCassiniEvenLogMassGerm_reflected_cubic_coefficient v q

/-- Direct and reflected periodic pole families cannot collide across any Xi nodes. -/
theorem liEvenCrossCassiniLogMassPole_lattices_disjoint
    (v : LiEvenCrossInteriorMass) (q r : XiZeroCopy) (k l : ℤ) :
    liEvenCrossCassiniLogMassPole v q + liEvenCrossCassiniLogMassPeriod k ≠
      -liEvenCrossCassiniLogMassPole v r + liEvenCrossCassiniLogMassPeriod l := by
  intro h
  have he := congrArg (fun t : ℂ => ‖(v.val : ℂ) * Complex.exp t‖) h
  rw [liEvenCrossCassiniLogMassPole_periodic_direct_mass,
    liEvenCrossCassiniLogMassPole_periodic_reflected_mass, norm_neg] at he
  have hsmall := liEvenCrossCassiniLogMassPole_reflected_mass_norm v r
  rw [liEvenCrossCassiniLogMassPole_reflected_mass, ← he] at hsmall
  have hbig := liEvenCross_squaredNode_norm_lower q
  linarith

end

end RHTower
