import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitPrimeCellParityFibreChiralityNoGo
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnBurnolHolonomyMassShell
import GaloisForLFunctions.RHTower.CothInfra

/-!
# Route P geometric information is a Burnol holonomy virial

The geometric-valuation KL chirality of the Route-P prime cell has an exact prime-power
expansion.  Its `n`th term is the positive Euler weight times

`V(u) = u cosh u - sinh u`.

At the physical prime center this is the renormalized scale derivative `t H'(t) - H(t)` of the
reciprocal holonomy `H(t) = 2 sinh(2(n+1)t log p)`.  At an actual right-half zeta zero, this `H`
is exactly the normalized Burnol co-Poisson holonomy at dilation `p^(n+1)`.  Hence information
chirality and co-Poisson holonomy are two presentations of one source virial, not independent
pressures.  The virial is strictly positive away from the critical wall.
-/

open Real Set Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Virial derivative of an oriented reciprocal holonomy. -/
def sourceHorizontalHolonomyVirial (u : ℝ) : ℝ :=
  u * Real.cosh u - Real.sinh u

/-- Prime-power term in geometric information chirality, before hyperbolic rewriting. -/
def sourceHorizontalGeometricKLPrimePowerTerm (c s : ℝ) (n : ℕ) : ℝ :=
  let k : ℝ := n + 1
  2 * s * (Real.exp ((c + s) * k) + Real.exp ((c - s) * k)) -
    2 * (Real.exp ((c + s) * k) / k - Real.exp ((c - s) * k) / k)

/-- Every information-chirality prime-power term is a weighted holonomy virial. -/
theorem sourceHorizontalGeometricKLPrimePowerTerm_eq_virial
    (c s : ℝ) (n : ℕ) :
    sourceHorizontalGeometricKLPrimePowerTerm c s n =
      4 * Real.exp (c * (n + 1)) / (n + 1) *
        sourceHorizontalHolonomyVirial (s * (n + 1)) := by
  have hk : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [sourceHorizontalGeometricKLPrimePowerTerm, sourceHorizontalHolonomyVirial]
  rw [show (c + s) * ((n : ℝ) + 1) =
        c * ((n : ℝ) + 1) + s * ((n : ℝ) + 1) by ring,
    show (c - s) * ((n : ℝ) + 1) =
        c * ((n : ℝ) + 1) - s * ((n : ℝ) + 1) by ring,
    Real.exp_add, Real.exp_sub, Real.cosh_eq, Real.sinh_eq]
  have he : Real.exp (s * ((n : ℝ) + 1)) ≠ 0 := Real.exp_ne_zero _
  rw [Real.exp_neg]
  field_simp [he, hk.ne']
  ring

private theorem hasSum_sourceHorizontalBoseMean_exp
    {x : ℝ} (hx : x < 0) :
    HasSum (fun n : ℕ => Real.exp (x * (n + 1)))
      (sourceHorizontalBoseMean x) := by
  let q := Real.exp x
  have hq0 : 0 ≤ q := (Real.exp_pos x).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr hx
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left q
  have hfun : (fun n : ℕ => q * q ^ n) =
      fun n : ℕ => Real.exp (x * (n + 1)) := by
    funext n
    rw [show q = Real.exp x by rfl, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hval : q * (1 - q)⁻¹ = sourceHorizontalBoseMean x := by
    rw [sourceHorizontalBoseMean]
    rfl
  rw [hfun, hval] at h
  exact h

private theorem hasSum_sourceHorizontalBoseLogPartition_exp
    {x : ℝ} (hx : x < 0) :
    HasSum (fun n : ℕ => Real.exp (x * (n + 1)) / (n + 1))
      (sourceHorizontalBoseLogPartition x) := by
  let q := Real.exp x
  have hq0 : 0 < q := Real.exp_pos x
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr hx
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := q) (by rw [abs_of_pos hq0]; exact hq1)
  have hfun : (fun n : ℕ => q ^ (n + 1) / (n + 1)) =
      fun n : ℕ => Real.exp (x * (n + 1)) / (n + 1) := by
    funext n
    congr 1
    rw [show q = Real.exp x by rfl, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hval : -Real.log (1 - q) = sourceHorizontalBoseLogPartition x := by
    rw [sourceHorizontalBoseLogPartition]
  rw [hfun, hval] at h
  exact h

/-- Exact prime-power expansion of geometric KL chirality. -/
theorem hasSum_sourceHorizontalGeometricKLPrimePowerTerm
    {c s : ℝ} (hplus : c + s < 0) (hminus : c - s < 0) :
    HasSum (sourceHorizontalGeometricKLPrimePowerTerm c s)
      (sourceHorizontalCenteredGeometricKLChirality c s) := by
  have hmp := hasSum_sourceHorizontalBoseMean_exp hplus
  have hmm := hasSum_sourceHorizontalBoseMean_exp hminus
  have hlp := hasSum_sourceHorizontalBoseLogPartition_exp hplus
  have hlm := hasSum_sourceHorizontalBoseLogPartition_exp hminus
  have h := ((hmp.add hmm).mul_left (2 * s)).sub
    ((hlp.sub hlm).mul_left 2)
  rw [sourceHorizontalCenteredGeometricKLChirality]
  refine h.congr_fun ?_
  intro n
  rw [sourceHorizontalGeometricKLPrimePowerTerm]

/-- Virial series form retaining reciprocal-holonomy geometry. -/
theorem hasSum_sourceHorizontalGeometricKLHolonomyVirial
    {c s : ℝ} (hplus : c + s < 0) (hminus : c - s < 0) :
    HasSum (fun n : ℕ =>
      4 * Real.exp (c * (n + 1)) / (n + 1) *
        sourceHorizontalHolonomyVirial (s * (n + 1)))
      (sourceHorizontalCenteredGeometricKLChirality c s) := by
  exact (hasSum_sourceHorizontalGeometricKLPrimePowerTerm hplus hminus).congr_fun
    (fun n => (sourceHorizontalGeometricKLPrimePowerTerm_eq_virial c s n).symm)

/-- Holonomy virial is strictly positive on positive displacement. -/
theorem sourceHorizontalHolonomyVirial_pos {u : ℝ} (hu : 0 < u) :
    0 < sourceHorizontalHolonomyVirial u := by
  rw [sourceHorizontalHolonomyVirial]
  exact sub_pos.mpr (RHTower.sinh_lt_mul_cosh hu)

/-- Reciprocal holonomy at one prime-power clock. -/
def sourceHorizontalPrimePowerHolonomy
    (p : Nat.Primes) (n : ℕ) (t : ℝ) : ℝ :=
  2 * Real.sinh (2 * (n + 1) * Real.log (p : ℝ) * t)

theorem hasDerivAt_sourceHorizontalPrimePowerHolonomy
    (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    HasDerivAt (sourceHorizontalPrimePowerHolonomy p n)
      (4 * (n + 1) * Real.log (p : ℝ) *
        Real.cosh (2 * (n + 1) * Real.log (p : ℝ) * t)) t := by
  unfold sourceHorizontalPrimePowerHolonomy
  have hlin : HasDerivAt
      (fun y : ℝ => 2 * (n + 1) * Real.log (p : ℝ) * y)
      (2 * (n + 1) * Real.log (p : ℝ)) t := by
    simpa using (hasDerivAt_id t).const_mul
      (2 * (n + 1) * Real.log (p : ℝ))
  have h := (Real.hasDerivAt_sinh _).comp t hlin |>.const_mul 2
  have hcoeff :
      2 * (Real.cosh (2 * (n + 1) * Real.log (p : ℝ) * t) *
        (2 * (n + 1) * Real.log (p : ℝ))) =
      4 * (n + 1) * Real.log (p : ℝ) *
        Real.cosh (2 * (n + 1) * Real.log (p : ℝ) * t) := by ring
  rw [hcoeff] at h
  simpa only [Function.comp_apply] using h

/-- Renormalized scale derivative of prime-power holonomy is twice its hyperbolic virial. -/
theorem sourceHorizontalPrimePowerHolonomy_scaleVirial
    (p : Nat.Primes) (n : ℕ) (t : ℝ) :
    t * deriv (sourceHorizontalPrimePowerHolonomy p n) t -
        sourceHorizontalPrimePowerHolonomy p n t =
      2 * sourceHorizontalHolonomyVirial
        (2 * (n + 1) * Real.log (p : ℝ) * t) := by
  rw [(hasDerivAt_sourceHorizontalPrimePowerHolonomy p n t).deriv,
    sourceHorizontalPrimePowerHolonomy, sourceHorizontalHolonomyVirial]
  ring

/-- Every physical prime-power scale virial is strictly positive off the critical wall. -/
theorem sourceHorizontalPrimePowerHolonomy_scaleVirial_pos
    (p : Nat.Primes) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < t * deriv (sourceHorizontalPrimePowerHolonomy p n) t -
        sourceHorizontalPrimePowerHolonomy p n t := by
  rw [sourceHorizontalPrimePowerHolonomy_scaleVirial]
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  apply sourceHorizontalHolonomyVirial_pos
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  positivity

/-- At physical prime center, geometric KL chirality is the prime-power sum of renormalized
reciprocal-holonomy scale virials. -/
theorem hasSum_sourceHorizontalPrimeGeometricKL_scaleVirial
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1 / 2) :
    HasSum (fun n : ℕ =>
      2 * Real.exp (-Real.log (p : ℝ) * (n + 1)) / (n + 1) *
        (t * deriv (sourceHorizontalPrimePowerHolonomy p n) t -
          sourceHorizontalPrimePowerHolonomy p n t))
      (sourceHorizontalCenteredGeometricKLChirality
        (-Real.log (p : ℝ)) (2 * t * Real.log (p : ℝ))) := by
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hplus : -Real.log (p : ℝ) + 2 * t * Real.log (p : ℝ) < 0 := by
    rcases abs_lt.mp ht with ⟨_, ht'⟩
    nlinarith
  have hminus : -Real.log (p : ℝ) - 2 * t * Real.log (p : ℝ) < 0 := by
    rcases abs_lt.mp ht with ⟨ht', _⟩
    nlinarith
  have h := hasSum_sourceHorizontalGeometricKLHolonomyVirial hplus hminus
  refine h.congr_fun ?_
  intro n
  rw [sourceHorizontalPrimePowerHolonomy_scaleVirial]
  have harg : 2 * ((n : ℝ) + 1) * Real.log (p : ℝ) * t =
      2 * t * Real.log (p : ℝ) * ((n : ℝ) + 1) := by ring
  rw [harg]
  ring

/-- Every prime-power member of a right-half zeta-zero co-Poisson ladder has exactly the
reciprocal holonomy used by the information-virial expansion. -/
theorem burnolCoPoissonNormalizedHolonomy_primePower_eq_sourceHorizontal
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (p : Nat.Primes) (n : ℕ) (hz : riemannZeta w = 0) :
    burnolCoPoissonNormalizedHolonomy
        (r := (p : ℝ) ^ (n + 1)) hlo hhi ha
        (one_lt_pow₀ (by exact_mod_cast p.prop.one_lt) (Nat.succ_ne_zero n)) =
      sourceHorizontalPrimePowerHolonomy p n (w.re - 1 / 2) := by
  let r : ℝ := (p : ℝ) ^ (n + 1)
  have hr0 : 0 < r := pow_pos (by exact_mod_cast p.prop.pos) _
  have hr1 : 1 < r := one_lt_pow₀ (by exact_mod_cast p.prop.one_lt) (Nat.succ_ne_zero n)
  let hb : 0 < r⁻¹ * a := mul_pos (inv_pos.mpr hr0) ha
  have hann : BurnolCoPoissonAnnihilatorPoint w (r⁻¹ * a) hlo hhi hb :=
    burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero hlo hhi hb hz
  have hk : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 :=
    burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1
  have h := burnolCoPoissonNormalizedHolonomy_eq_two_sinh_of_annihilator
    hlo hhi ha hr1 hann hk
  change burnolCoPoissonNormalizedHolonomy hlo hhi ha hr1 = _ at h
  rw [h, sourceHorizontalPrimePowerHolonomy]
  dsimp only [r]
  rw [Real.log_pow]
  push_cast
  congr 2
  ring

end

end RHTower.HedenmalmThetaSource
