import GaloisForLFunctions.RHTower.BornSectorExchange
import GaloisForLFunctions.RHTower.WeightOneInversion

/-!
# Poisson wiring: the even Hurwitz pair at `1/2` is the Born sector pair

Mathlib's even Hurwitz zeta development carries, for each point `a` of the unit circle, a
Poisson-dual pair: the shifted kernel `evenKernel a` and the twisted kernel `cosKernel a`,
exchanged by theta inversion, whose Mellin transforms `completedHurwitzZetaEven a` and
`completedCosZeta a` satisfy the functional equation
`completedHurwitzZetaEven a (1-s) = completedCosZeta a s`.

At the two-torsion point `a = 1/2` this pair **is** the Born sector pair:

* `completedCosZeta (1/2) s = -Λ₄(s)` — the twisted sector is the negative of the
  parity-graded order sector;
* `completedHurwitzZetaEven (1/2) s = Λ₂(s)` — the shifted sector is the half-integer
  disorder sector;
* hence mathlib's functional equation *is* the signed sector swap `Λ₂(1-s) = -Λ₄(s)`,
  now derived from genuine Poisson summation rather than from the scalar reflection
  identity of the completed zeta — the two independent proofs agree.

At the kernel level, the same wiring converts the theta inversion into the weight-one
inversion of scale profiles: the order profile `cosKernel (1/2) (t²)` and disorder profile
`evenKernel (1/2) (t²)` are exchanged by `J f(t) = t⁻¹ f(t⁻¹)`, and both are lattice sums
of dilated Gaussian seeds — parity-signed integer dilations for the order profile,
half-integer dilations for the disorder profile.
-/

noncomputable section

namespace RHTower

open Complex Filter HurwitzZeta

/-- The half point of the unit circle is not zero: the two-torsion twist is nontrivial. -/
theorem half_ne_zero_unitAddCircle : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  rw [Ne, AddCircle.coe_eq_zero_iff]
  rintro ⟨n, hn⟩
  rw [zsmul_eq_mul, mul_one] at hn
  have h2 : (2 * n : ℤ) = 1 := by
    have : (2 : ℝ) * n = 1 := by linarith
    exact_mod_cast this
  omega

/-! ## The Dirichlet-series identifications on `Re s > 1` -/

/-- On `Re s > 1`, the completed cosine zeta at the two-torsion point is the negative of the
parity-graded sector: the twisted Dirichlet series is the alternating series. -/
theorem completedCosZeta_one_half_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedCosZeta ((1 / 2 : ℝ) : UnitAddCircle) s = -lambdaParity s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  set e : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * (1 / (n : ℂ) ^ s) with he_def
  have hterm : ∀ n : ℕ,
      (if n = 0 then 0 else Complex.Gammaℝ s
        * ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * n) : ℝ) : ℂ) / (n : ℂ) ^ s)
      = Complex.Gammaℝ s * e n := by
    intro n
    show _ = Complex.Gammaℝ s * ((-1 : ℂ) ^ n * (1 / (n : ℂ) ^ s))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Complex.zero_cpow hs0]
    · rw [if_neg hn.ne']
      have hcos : Real.cos (2 * Real.pi * (1 / 2 : ℝ) * n) = (-1 : ℝ) ^ n := by
        rw [show 2 * Real.pi * (1 / 2 : ℝ) * n = ((n : ℤ) : ℝ) * Real.pi by push_cast; ring,
          Real.cos_int_mul_pi]
        norm_cast
      rw [hcos]
      push_cast
      ring
  have hsummable : Summable e := by
    refine (summable_mul_left_iff hΓ).mp ?_
    exact ((hasSum_nat_completedCosZeta (1 / 2 : ℝ) hs).summable).congr hterm
  have he : Summable fun k : ℕ => e (2 * k) :=
    hsummable.comp_injective fun a b hab => by omega
  have ho : Summable fun k : ℕ => e (2 * k + 1) :=
    hsummable.comp_injective fun a b hab => by omega
  have heo := tsum_even_add_odd he ho
  have heTerm : ∀ k : ℕ, e (2 * k) = (2 : ℂ) ^ (-s) * (1 / (k : ℂ) ^ s) := by
    intro k
    show (-1 : ℂ) ^ (2 * k) * (1 / ((2 * k : ℕ) : ℂ) ^ s) = _
    have hsq : (-1 : ℂ) ^ (2 * k) = 1 := by
      rw [pow_mul]
      norm_num
    have hcast : ((2 * k : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((k : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hsq, one_mul, hcast, natCast_mul_natCast_cpow, Complex.cpow_neg,
      show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num, one_div, mul_inv, one_div]
  have hoTerm : ∀ k : ℕ, e (2 * k + 1) = -((((2 * k : ℕ) : ℂ) + 1) ^ (-s)) := by
    intro k
    show (-1 : ℂ) ^ (2 * k + 1) * (1 / ((2 * k + 1 : ℕ) : ℂ) ^ s) = _
    have hsq : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have hcast : ((2 * k + 1 : ℕ) : ℂ) = ((2 * k : ℕ) : ℂ) + 1 := by
      push_cast
      ring
    rw [hsq, hcast, Complex.cpow_neg, one_div]
    ring
  have heSum : ∑' k : ℕ, e (2 * k) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [tsum_congr heTerm, tsum_mul_left, ← zeta_eq_tsum_one_div_nat_cpow hs]
  have hoSum : ∑' k : ℕ, e (2 * k + 1) = -oddLevelZeta s := by
    rw [tsum_congr hoTerm, tsum_neg, oddLevelZeta]
  have halt : ∑' n : ℕ, e n = (2 : ℂ) ^ (-s) * riemannZeta s - oddLevelZeta s := by
    rw [← heo, heSum, hoSum]
    ring
  have hΛ : completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp
  have h2s : (2 : ℂ) ^ ((1 : ℂ) - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, Complex.cpow_add _ _ two_ne_zero,
      Complex.cpow_one]
  calc completedCosZeta ((1 / 2 : ℝ) : UnitAddCircle) s
      = ∑' n : ℕ, (if n = 0 then 0 else Complex.Gammaℝ s
          * ((Real.cos (2 * Real.pi * (1 / 2 : ℝ) * n) : ℝ) : ℂ) / (n : ℂ) ^ s) :=
        (hasSum_nat_completedCosZeta (1 / 2 : ℝ) hs).tsum_eq.symm
    _ = ∑' n : ℕ, Complex.Gammaℝ s * e n := tsum_congr hterm
    _ = Complex.Gammaℝ s * ∑' n : ℕ, e n := tsum_mul_left
    _ = -lambdaParity s := by
        rw [halt, oddLevelZeta_eq hs]
        unfold lambdaParity
        rw [h2s]
        linear_combination (1 - 2 * (2 : ℂ) ^ (-s)) * hΛ

/-- On `Re s > 1`, the completed even Hurwitz zeta at the two-torsion point is the
half-integer disorder sector: the `ℤ`-lattice pairs `n ↔ -(n+1)` fold onto the displaced
levels `n + 1/2`. -/
theorem completedHurwitzZetaEven_one_half_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedHurwitzZetaEven ((1 / 2 : ℝ) : UnitAddCircle) s = lambdaHalfShift s := by
  have hpair := (hasSum_int_completedHurwitzZetaEven (1 / 2 : ℝ) hs).nat_add_neg_add_one
  have hterm : ∀ n : ℕ,
      (Complex.Gammaℝ s / ((|((n : ℤ) : ℝ) + (1 / 2 : ℝ)| : ℝ) : ℂ) ^ s / 2
        + Complex.Gammaℝ s / ((|((-((n : ℤ) + 1) : ℤ) : ℝ) + (1 / 2 : ℝ)| : ℝ) : ℂ) ^ s / 2)
      = Complex.Gammaℝ s * (((n : ℂ) + 1 / 2) ^ (-s)) := by
    intro n
    have habs1 : |((n : ℤ) : ℝ) + (1 / 2 : ℝ)| = (n : ℝ) + 1 / 2 := by
      rw [abs_of_pos (by positivity)]
      norm_num
    have habs2 : |((-((n : ℤ) + 1) : ℤ) : ℝ) + (1 / 2 : ℝ)| = (n : ℝ) + 1 / 2 := by
      rw [abs_of_neg (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])]
      push_cast
      ring
    rw [habs1, habs2]
    have hbne : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      positivity
    have hpne : ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hbne)
    rw [show (n : ℂ) + 1 / 2 = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.cpow_neg]
    field_simp
    ring
  calc completedHurwitzZetaEven ((1 / 2 : ℝ) : UnitAddCircle) s
      = ∑' n : ℕ, (Complex.Gammaℝ s / ((|((n : ℤ) : ℝ) + (1 / 2 : ℝ)| : ℝ) : ℂ) ^ s / 2
          + Complex.Gammaℝ s
            / ((|((-((n : ℤ) + 1) : ℤ) : ℝ) + (1 / 2 : ℝ)| : ℝ) : ℂ) ^ s / 2) :=
        hpair.tsum_eq.symm
    _ = ∑' n : ℕ, Complex.Gammaℝ s * (((n : ℂ) + 1 / 2) ^ (-s)) := tsum_congr hterm
    _ = Complex.Gammaℝ s * ∑' n : ℕ, ((n : ℂ) + 1 / 2) ^ (-s) := tsum_mul_left
    _ = Complex.Gammaℝ s * HurwitzZetaShift.hzeta s (1 / 2) := rfl
    _ = lambdaHalfShift s := (lambdaHalfShift_eq_halfLevels hs).symm

/-! ## Globalization off the exceptional points -/

private theorem eq_on_compl_pair {F G : ℂ → ℂ}
    (hF : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → DifferentiableAt ℂ F w)
    (hG : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → DifferentiableAt ℂ G w)
    (hEq : ∀ w : ℂ, 1 < w.re → F w = G w)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) : F s = G s := by
  set U : Set ℂ := ({0, 1} : Set ℂ)ᶜ with hU
  have hfin : ({0, 1} : Set ℂ).Finite := Set.toFinite _
  have hUopen : IsOpen U := hfin.isClosed.isOpen_compl
  have hmem : ∀ w : ℂ, w ∈ U → w ≠ 0 ∧ w ≠ 1 := by
    intro w hw
    simpa [hU, Set.mem_compl_iff, not_or] using hw
  have hUconn : IsPreconnected U := by
    refine (hfin.countable.isPathConnected_compl_of_one_lt_rank ?_).isConnected.isPreconnected
    rw [Complex.rank_real_complex]
    norm_num
  have hFan : AnalyticOnNhd ℂ F U :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (hF w (hmem w hw).1 (hmem w hw).2).differentiableWithinAt) hUopen
  have hGan : AnalyticOnNhd ℂ G U :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (hG w (hmem w hw).1 (hmem w hw).2).differentiableWithinAt) hUopen
  have h2U : (2 : ℂ) ∈ U := by
    simp only [hU, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    norm_num
  have heq2 : F =ᶠ[nhds 2] G :=
    Filter.eventuallyEq_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (1 : ℝ) < (2 : ℂ).re))
      fun w hw => hEq w hw
  have hEqOn := hFan.eqOn_of_preconnected_of_eventuallyEq hGan hUconn h2U heq2
  exact hEqOn (by simp [hU, hs0, hs1])

/-- **The twisted sector is the parity sector, globally**:
`completedCosZeta (1/2) = -Λ₄` away from the exceptional points. -/
theorem completedCosZeta_one_half {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedCosZeta ((1 / 2 : ℝ) : UnitAddCircle) s = -lambdaParity s := by
  refine eq_on_compl_pair
    (fun w hw0 _ => differentiableAt_completedCosZeta _ hw0
      (Or.inr half_ne_zero_unitAddCircle))
    (fun w hw0 hw1 => ?_)
    (fun w hw => completedCosZeta_one_half_of_one_lt_re hw) hs0 hs1
  have hcoup : DifferentiableAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) w := by
    apply DifferentiableAt.sub (differentiableAt_const _)
    exact DifferentiableAt.const_cpow
      ((differentiableAt_const _).sub differentiableAt_id) (Or.inl two_ne_zero)
  exact (hcoup.mul (differentiableAt_completedZeta hw0 hw1)).neg

/-- **The shifted sector is the disorder sector, globally**:
`completedHurwitzZetaEven (1/2) = Λ₂` away from the exceptional points. -/
theorem completedHurwitzZetaEven_one_half {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedHurwitzZetaEven ((1 / 2 : ℝ) : UnitAddCircle) s = lambdaHalfShift s := by
  refine eq_on_compl_pair
    (fun w hw0 hw1 => differentiableAt_completedHurwitzZetaEven _ (Or.inl hw0) hw1)
    (fun w hw0 hw1 => ?_)
    (fun w hw => completedHurwitzZetaEven_one_half_of_one_lt_re hw) hs0 hs1
  have hcoup : DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ z - 1) w := by
    apply DifferentiableAt.sub _ (differentiableAt_const _)
    exact DifferentiableAt.const_cpow differentiableAt_id (Or.inl two_ne_zero)
  exact hcoup.mul (differentiableAt_completedZeta hw0 hw1)

/-- **The sector swap from Poisson summation.**  Mathlib's even Hurwitz functional equation
— proven by theta inversion, i.e. genuine Poisson summation — specializes at the two-torsion
point to the signed sector swap, independently confirming the scalar reflection proof. -/
theorem lambdaHalfShift_one_sub_poisson {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    lambdaHalfShift (1 - s) = -lambdaParity s := by
  have h10 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h11 : (1 : ℂ) - s ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  rw [← completedHurwitzZetaEven_one_half h10 h11,
    completedHurwitzZetaEven_one_sub, completedCosZeta_one_half hs0 hs1]

/-! ## The kernel level: theta inversion is the weight-one inversion -/

/-- The order theta profile: the parity-signed Gaussian lattice sum, `cosKernel (1/2)` in
the scale variable. -/
def orderThetaProfile (t : ℝ) : ℝ := cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (t ^ 2)

/-- The disorder theta profile: the half-integer Gaussian lattice sum, `evenKernel (1/2)`
in the scale variable. -/
def disorderThetaProfile (t : ℝ) : ℝ := evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (t ^ 2)

/-- **Theta inversion is the weight-one inversion of the sector profiles**: the disorder
profile is the inverted order profile.  This is Poisson summation in the scale variable —
the operator source of the sector swap. -/
theorem disorderThetaProfile_eq_inversion {t : ℝ} (ht : 0 < t) :
    disorderThetaProfile t = weightOneInversion orderThetaProfile t := by
  unfold disorderThetaProfile orderThetaProfile weightOneInversion
  rw [evenKernel_functional_equation]
  congr 1
  · rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht.le]
    norm_num
  · congr 1
    rw [one_div, ← inv_pow]

/-- The converse direction: the order profile is the inverted disorder profile. -/
theorem orderThetaProfile_eq_inversion {t : ℝ} (ht : 0 < t) :
    orderThetaProfile t = weightOneInversion disorderThetaProfile t := by
  have h := disorderThetaProfile_eq_inversion (t := t⁻¹) (by positivity)
  unfold weightOneInversion at h ⊢
  rw [inv_inv] at h
  rw [h]
  field_simp

/-- The disorder profile is the half-integer lattice sum of dilated Gaussian seeds. -/
theorem disorderThetaProfile_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => thetaCuspGaussian ((n + 1 / 2) * t)) (disorderThetaProfile t) := by
  have h := hasSum_int_evenKernel (1 / 2 : ℝ) (t := t ^ 2) (by positivity)
  refine h.congr_fun fun n => ?_
  unfold thetaCuspGaussian
  congr 1
  ring

/-- The order profile is the parity-signed integer lattice sum of dilated Gaussian seeds:
the grading enters as the sign `(-1)^n` on the `n`-fold dilated seed. -/
theorem orderThetaProfile_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => ((-1 : ℝ) ^ n) * thetaCuspGaussian (n * t))
      (orderThetaProfile t) := by
  have h := hasSum_int_cosKernel (1 / 2 : ℝ) (t := t ^ 2) (by positivity)
  rw [← Complex.hasSum_ofReal]
  refine h.congr_fun fun n => ?_
  have hchar : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) * (n : ℂ))
      = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) * (n : ℂ)
        = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_int_mul, Complex.exp_pi_mul_I]
    push_cast
    ring
  rw [hchar, ← Complex.ofReal_mul]
  congr 1
  unfold thetaCuspGaussian
  congr 1
  ring

end RHTower
