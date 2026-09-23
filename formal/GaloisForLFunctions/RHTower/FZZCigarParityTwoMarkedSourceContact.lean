import GaloisForLFunctions.HTGeometry.FZZCigarReplicaBackreaction

/-!
# Two independently marked FZZ source insertions

The literal radial and winding weights give a bilinear two-insertion Wick exponent. Its first
same-winding tangent vanishes at an unmarked second insertion, but its mixed tangent is nonzero.
The resulting charge form splits exactly into winding and radial squares of opposite signs.

For the opposite-winding radial pair, compact integration retains an explicit scale term in the
logarithmic comparison of two annuli. Its mixed derivative ranges over all real values although
both compared integrals are strictly positive. This is a theorem about the relative response;
it does not infer the sign of the complete integrated torus response.

The two marks are distinct and varied independently. The coefficient named `Contact` below is a
direct mixed source coefficient, not a distribution supported on coincident points. No nonlinear
off-shell continuation of a single marked insertion, full neutral screening sum, meromorphic
continuation, external-momentum Ward identity, or RH conclusion is asserted.

Source: Halder--Jafferis, arXiv:2402.00932, §3.2.3, equations (3.29)--(3.33), and the literal
replica weights formalized in `FZZCigarReplicaBackreaction`.
-/

open GaloisForLFunctions.HTGeometry.FZZCigar

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- All physical cigar levels, parameterized without a level assumption. -/
def fzzTwoMarkedPhysicalLevel (u : ℝ) : ℝ := 2 + Real.exp u

theorem fzzTwoMarkedPhysicalLevel_gt_two (u : ℝ) :
    2 < fzzTwoMarkedPhysicalLevel u := by
  unfold fzzTwoMarkedPhysicalLevel
  linarith [Real.exp_pos u]

/-- Wick exponent for two independently marked insertions.  The charge product is `1` for
equal winding and `-1` for opposite winding. -/
def fzzTwoMarkedOPEExponent (k q δ ε : ℝ) : ℝ :=
  -((k - 2) / 2) * replicaRadialWeight (1 / k) δ *
      replicaRadialWeight (1 / k) ε +
    (k * q / 2) * replicaWindingWeight δ * replicaWindingWeight ε

/-- The mixed source coefficient before any position integration. -/
def fzzTwoMarkedContact (k q : ℝ) : ℝ :=
  k * q / 2 - k ^ (2 : ℕ) / (2 * (k - 2))

theorem fzzTwoMarkedOPEExponent_normalForm (u q δ ε : ℝ) :
    fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) q δ ε =
      -(fzzTwoMarkedPhysicalLevel u - 2) / 2 + fzzTwoMarkedPhysicalLevel u * q / 2 +
        fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) * (δ + ε) +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q * δ * ε := by
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hk0 : fzzTwoMarkedPhysicalLevel u ≠ 0 := by linarith
  have hk2 : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  have hd : 1 - 2 * (1 / fzzTwoMarkedPhysicalLevel u) ≠ 0 := by
    intro h
    field_simp [hk0] at h
    linarith
  unfold fzzTwoMarkedOPEExponent replicaRadialWeight replicaWindingWeight
    fzzTwoMarkedContact
  field_simp [hk0, hk2, hd]
  ring

theorem fzzTwoMarkedOPEExponent_same (u δ ε : ℝ) :
    fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) 1 δ ε =
      1 - fzzTwoMarkedPhysicalLevel u / (fzzTwoMarkedPhysicalLevel u - 2) * δ * ε := by
  rw [fzzTwoMarkedOPEExponent_normalForm]
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hd : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  unfold fzzTwoMarkedContact
  field_simp [hd]
  ring

theorem fzzTwoMarkedOPEExponent_opposite (u δ ε : ℝ) :
    fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) (-1) δ ε =
      1 - fzzTwoMarkedPhysicalLevel u + fzzTwoMarkedPhysicalLevel u * (δ + ε) -
        fzzTwoMarkedPhysicalLevel u * (fzzTwoMarkedPhysicalLevel u - 1) /
          (fzzTwoMarkedPhysicalLevel u - 2) * δ * ε := by
  rw [fzzTwoMarkedOPEExponent_normalForm]
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hd : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  unfold fzzTwoMarkedContact
  field_simp [hd]
  ring

theorem hasDerivAt_fzzTwoMarkedOPEExponent_left (u q δ ε : ℝ) :
    HasDerivAt (fun d => fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) q d ε)
      (fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q * ε) δ := by
  simp_rw [fzzTwoMarkedOPEExponent_normalForm]
  have heq : (fun d : ℝ =>
      -(fzzTwoMarkedPhysicalLevel u - 2) / 2 + fzzTwoMarkedPhysicalLevel u * q / 2 +
        fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) * (d + ε) +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q * d * ε) =
      fun d => (fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q * ε) * d +
        (-(fzzTwoMarkedPhysicalLevel u - 2) / 2 + fzzTwoMarkedPhysicalLevel u * q / 2 +
          fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) * ε) := by
    funext d
    ring
  rw [heq]
  simpa only [mul_one, id_eq] using ((hasDerivAt_id δ).const_mul
    (fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) +
      fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q * ε)).add_const
        (-(fzzTwoMarkedPhysicalLevel u - 2) / 2 + fzzTwoMarkedPhysicalLevel u * q / 2 +
          fzzTwoMarkedPhysicalLevel u / 2 * (1 - q) * ε)

/-- The mixed derivative is fixed by the two first-order marked insertions; it does not require
a choice of second-order continuation for an individual insertion. -/
theorem fzzTwoMarkedOPEExponent_mixedDeriv (u q δ ε : ℝ) :
    deriv (fun e => deriv
      (fun d => fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) q d e) δ) ε =
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q := by
  simp_rw [(hasDerivAt_fzzTwoMarkedOPEExponent_left u q δ _).deriv]
  simpa only [mul_one, id_eq] using (((hasDerivAt_id ε).const_mul
    (fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q)).const_add
      (fzzTwoMarkedPhysicalLevel u / 2 * (1 - q))).deriv

/-- The quadratic form on the two winding-charge channels of the mixed source coefficient. -/
def fzzTwoMarkedChargeForm (k x y : ℝ) : ℝ :=
  fzzTwoMarkedContact k 1 * (x ^ (2 : ℕ) + y ^ (2 : ℕ)) +
    2 * fzzTwoMarkedContact k (-1) * x * y

/-- Exact radial and winding decomposition of the double-insertion charge coefficient. -/
theorem fzzTwoMarkedChargeForm_split (k x y : ℝ) :
    fzzTwoMarkedChargeForm k x y =
      k / 2 * (x - y) ^ (2 : ℕ) - k ^ (2 : ℕ) / (2 * (k - 2)) * (x + y) ^ (2 : ℕ) := by
  unfold fzzTwoMarkedChargeForm fzzTwoMarkedContact
  ring

theorem fzzTwoMarkedChargeForm_radial (u x : ℝ) :
    fzzTwoMarkedChargeForm (fzzTwoMarkedPhysicalLevel u) x x =
      -(2 * fzzTwoMarkedPhysicalLevel u ^ (2 : ℕ) / (fzzTwoMarkedPhysicalLevel u - 2)) * x ^ (2 : ℕ) := by
  rw [fzzTwoMarkedChargeForm_split]
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hd : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  field_simp [hd]
  ring

theorem fzzTwoMarkedChargeForm_winding (k x : ℝ) :
    fzzTwoMarkedChargeForm k x (-x) = 2 * k * x ^ (2 : ℕ) := by
  rw [fzzTwoMarkedChargeForm_split]
  ring

/-- At every physical level the two-marked charge form has both signs. -/
theorem fzzTwoMarkedChargeForm_indefinite (u : ℝ) :
    fzzTwoMarkedChargeForm (fzzTwoMarkedPhysicalLevel u) 1 1 < 0 ∧
      0 < fzzTwoMarkedChargeForm (fzzTwoMarkedPhysicalLevel u) 1 (-1) := by
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  constructor
  · rw [fzzTwoMarkedChargeForm_radial]
    have hp : 0 < 2 * fzzTwoMarkedPhysicalLevel u ^ (2 : ℕ) /
        (fzzTwoMarkedPhysicalLevel u - 2) := by positivity
    simpa using neg_neg_of_pos hp
  · rw [fzzTwoMarkedChargeForm_winding]
    positivity

/-- Positive absolute-power pair kernel, with `L` the logarithm of the squared separation. -/
def fzzTwoMarkedPairKernel (u q L δ ε : ℝ) : ℝ :=
  Real.exp (L * fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) q δ ε)

theorem fzzTwoMarkedPairKernel_pos (u q L δ ε : ℝ) :
    0 < fzzTwoMarkedPairKernel u q L δ ε := Real.exp_pos _

/-- The connected mixed logarithmic response retains the direct two-marked source term. -/
theorem fzzTwoMarkedPairKernel_mixedLogDeriv (u q L δ ε : ℝ) :
    deriv (fun e => deriv (fun d => Real.log (fzzTwoMarkedPairKernel u q L d e)) δ) ε =
      L * fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q := by
  simp only [fzzTwoMarkedPairKernel, Real.log_exp]
  have hfirst (e : ℝ) :=
    ((hasDerivAt_fzzTwoMarkedOPEExponent_left u q δ e).const_mul L).deriv
  simp_rw [hfirst]
  simpa only [mul_one, id_eq] using ((((hasDerivAt_id ε).const_mul
    (fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) q)).const_add
      (fzzTwoMarkedPhysicalLevel u / 2 * (1 - q))).const_mul L).deriv


/-- Every prescribed real same-winding mixed logarithmic response occurs in a positive pair
kernel.  The separation is allowed to vary, while the physical level and charge are fixed. -/
theorem fzzTwoMarkedPairKernel_same_response_surjective (u target : ℝ) :
    ∃ L : ℝ, deriv (fun e => deriv
      (fun d => Real.log (fzzTwoMarkedPairKernel u 1 L d e)) 0) 0 = target := by
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hk0 : fzzTwoMarkedPhysicalLevel u ≠ 0 := by linarith
  have hd : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  refine ⟨-target * (fzzTwoMarkedPhysicalLevel u - 2) / fzzTwoMarkedPhysicalLevel u, ?_⟩
  rw [fzzTwoMarkedPairKernel_mixedLogDeriv]
  unfold fzzTwoMarkedContact
  field_simp [hk0, hd]
  ring

/-- Every real logarithmic squared separation is realized by a nonzero complex separation. -/
theorem fzzTwoMarked_logSeparation_realized (L : ℝ) :
    (Real.exp (L / 2) : ℂ) ≠ 0 ∧
      Real.log (Complex.normSq (Real.exp (L / 2) : ℂ)) = L := by
  constructor
  · exact_mod_cast (Real.exp_pos (L / 2)).ne'
  · rw [Complex.normSq_ofReal, ← Real.exp_add]
    rw [show L / 2 + L / 2 = L by ring, Real.log_exp]

/-- Opposite-winding radial pair integral on a compact annulus, expressed in logarithmic squared
radius.  The extra `1` in the exponent is the radial area Jacobian. -/
def fzzTwoMarkedAnnularIntegral (u L δ ε : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp
    ((1 + fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) (-1) δ ε) * (L + x))

theorem fzzTwoMarkedAnnularIntegral_pos (u L δ ε : ℝ) :
    0 < fzzTwoMarkedAnnularIntegral u L δ ε := by
  apply intervalIntegral.integral_pos (by norm_num)
    (by fun_prop) (fun x _ => (Real.exp_pos _).le)
  exact ⟨0, by simp, Real.exp_pos _⟩

theorem fzzTwoMarkedAnnularIntegral_scale (u L δ ε : ℝ) :
    fzzTwoMarkedAnnularIntegral u L δ ε =
      Real.exp ((1 + fzzTwoMarkedOPEExponent
        (fzzTwoMarkedPhysicalLevel u) (-1) δ ε) * L) *
          fzzTwoMarkedAnnularIntegral u 0 δ ε := by
  unfold fzzTwoMarkedAnnularIntegral
  simp only [zero_add]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact logarithmic comparison of two compact integrated sources. -/
theorem fzzTwoMarkedAnnularIntegral_logRatio (u L δ ε : ℝ) :
    Real.log (fzzTwoMarkedAnnularIntegral u L δ ε) -
      Real.log (fzzTwoMarkedAnnularIntegral u 0 δ ε) =
        (1 + fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) (-1) δ ε) * L := by
  rw [fzzTwoMarkedAnnularIntegral_scale, Real.log_mul (Real.exp_pos _).ne'
    (fzzTwoMarkedAnnularIntegral_pos u 0 δ ε).ne', Real.log_exp]
  ring

/-- The direct mixed replica source term survives compact position integration. -/
theorem fzzTwoMarkedAnnularIntegral_mixedLogRatio (u L δ ε : ℝ) :
    deriv (fun e => deriv (fun d =>
      Real.log (fzzTwoMarkedAnnularIntegral u L d e) -
        Real.log (fzzTwoMarkedAnnularIntegral u 0 d e)) δ) ε =
          fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * L := by
  simp_rw [fzzTwoMarkedAnnularIntegral_logRatio]
  have hfirst (e : ℝ) := (((hasDerivAt_fzzTwoMarkedOPEExponent_left
    u (-1) δ e).const_add 1).mul_const L).deriv
  simp_rw [hfirst]
  simpa only [mul_one, id_eq] using ((((hasDerivAt_id ε).const_mul
    (fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1))).const_add
      (fzzTwoMarkedPhysicalLevel u / 2 * (1 - (-1)))).mul_const L).deriv

/-- Moving the compact annulus realizes every real relative mixed replica response at any
fixed physical level; both compared position integrals remain strictly positive. -/
theorem fzzTwoMarkedAnnularIntegral_response_surjective (u target : ℝ) :
    ∃ L : ℝ, (∀ δ ε, 0 < fzzTwoMarkedAnnularIntegral u L δ ε) ∧
      deriv (fun e => deriv (fun d =>
        Real.log (fzzTwoMarkedAnnularIntegral u L d e) -
          Real.log (fzzTwoMarkedAnnularIntegral u 0 d e)) 0) 0 = target := by
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hk0 : fzzTwoMarkedPhysicalLevel u ≠ 0 := by linarith
  have hk1 : fzzTwoMarkedPhysicalLevel u - 1 ≠ 0 := by linarith
  have hd : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  refine ⟨-target * (fzzTwoMarkedPhysicalLevel u - 2) /
    (fzzTwoMarkedPhysicalLevel u * (fzzTwoMarkedPhysicalLevel u - 1)),
    fun δ ε => fzzTwoMarkedAnnularIntegral_pos u _ δ ε, ?_⟩
  rw [fzzTwoMarkedAnnularIntegral_mixedLogRatio]
  unfold fzzTwoMarkedContact
  field_simp [hk0, hk1, hd]
  ring

end

end GaloisForLFunctions.RHTower
