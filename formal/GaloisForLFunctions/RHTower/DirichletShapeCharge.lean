/-
# The completed-Dirichlet-shape stratum carries off-line deck charge

A carrier lies in the **completed-Dirichlet shape** when, on some right half-plane, it factors as
the archimedean dressing `archFactor s = s(s−1)/2 · Γ_ℝ(s)` times an ordinary Dirichlet series
`∑ aₙ n^{−s}` with real coefficients.  This is a *shape* constraint only: no functional equation and
no Euler product is imposed — the coefficient sequence is arbitrary.

Two members exhibit the range of the class.  The completed zeta `ξ = archFactor · ζ` belongs to it
(constant coefficients `aₙ = 1`).  The `η`-completion `s ↦ (1 − 2^{1−s})·ξ(s)` also belongs to it: the
Dirichlet-shape multiplier `1 − 2^{1−s}` turns the constant coefficients into the alternating ones
`aₙ = (−1)^{n+1}`, the Dirichlet eta coefficients, since `(1 − 2^{1−s})ζ(s) = ∑ (−1)^{n+1} n^{−s}` on
`Re s > 1`.

The multiplier `1 − 2^{1−s}` vanishes to first order at `s₀ = 1 + (2π/log 2)·i`, where `2^{1−s₀} = 1`,
while `ξ(s₀) ≠ 0` (because `Re s₀ = 1`).  Hence the `η`-completion has a simple zero at `s₀`, an
off-line point with `Re s₀ = 1 ≠ 1/2`, so its base-level deck charge there is `(−1)¹ = −1 ≠ 1`.

The class therefore **carries off-line charge** at an explicit point on `Re s = 1`.  By the trichotomy
identity `ForcesRHParity ↔ IsCategorical` (parity-forcing is exactly the charge-free cell), it
**cannot force RH-grade parity**: the deck charge stays blind below functional-equation pinning even
inside the Dirichlet-shape stratum.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

namespace RHTower

open Complex

/-! ### §1 The completed-Dirichlet shape class -/

/-- A carrier has **completed-Dirichlet shape** if on some right half-plane it is the archimedean
dressing `archFactor` times an ordinary Dirichlet series with real coefficients.  No functional
equation and no Euler product is required — only the shape. -/
def CompletedDirichletShape (f : ℂ → ℂ) : Prop :=
  ∃ (a : ℕ → ℝ) (σ₀ : ℝ), ∀ s : ℂ, σ₀ < s.re →
    f s = archFactor s * LSeries (fun n => ((a n : ℝ) : ℂ)) s

/-! ### §2 ξ lies in the class (constant coefficients) -/

/-- **ξ has completed-Dirichlet shape.**  On `Re s > 1`, `ξ = archFactor · ζ` and `ζ` is the Dirichlet
series with constant coefficients `aₙ = 1`. -/
theorem xi_completedDirichletShape : CompletedDirichletShape xi := by
  refine ⟨fun _ => (1 : ℝ), 1, fun s hs => ?_⟩
  have hspos : 0 < s.re := by linarith
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hspos; exact lt_irrefl 0 hspos
  have h1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  congr 1
  rw [← LSeries_one_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} _ => by simp) s

/-! ### §3 The Dirichlet eta identity -/

/-- The indicator of the even naturals, as a complex coefficient sequence. -/
private noncomputable def dirEvenIndicator : ℕ → ℂ := fun n => if 2 ∣ n then 1 else 0

/-- On `Re s > 1` the even-supported Dirichlet series sums to `2^{−s}·ζ(s)`: reindexing the zeta
series by `k ↦ 2k` scales each term by `2^{−s}`. -/
private theorem hasSum_dirEvenIndicator (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term dirEvenIndicator s) ((2 : ℂ) ^ (-s) * riemannZeta s) := by
  have hz : HasSum (LSeries.term (1 : ℕ → ℂ) s) (riemannZeta s) := LSeriesHasSum_one hs
  have hz2 : HasSum (fun k => (2 : ℂ) ^ (-s) * LSeries.term (1 : ℕ → ℂ) s k)
      ((2 : ℂ) ^ (-s) * riemannZeta s) := hz.mul_left _
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by intro a b h; simpa using h
  have hrange : ∀ n ∉ Set.range (fun k : ℕ => 2 * k), LSeries.term dirEvenIndicator s n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · rw [LSeries.term_of_ne_zero hpos.ne' dirEvenIndicator s]
      have hnd : ¬ 2 ∣ n := fun ⟨m, hm⟩ => hn ⟨m, by rw [hm]⟩
      simp [dirEvenIndicator, hnd]
  rw [← hinj.hasSum_iff hrange]
  refine HasSum.congr_fun hz2 ?_
  intro k
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · simp [Function.comp, h0]
  · have h2k : 2 * k ≠ 0 := by positivity
    simp only [Function.comp]
    rw [LSeries.term_of_ne_zero h2k dirEvenIndicator s, LSeries.term_of_ne_zero hpos.ne' (1 : ℕ → ℂ) s]
    have hcp : ((2 * k : ℕ) : ℂ) ^ s = (2 : ℂ) ^ s * (k : ℂ) ^ s := by
      have h : ((2 * k : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * ((k : ℝ) : ℂ) := by push_cast; ring
      rw [h, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity),
        Complex.ofReal_ofNat, Complex.ofReal_natCast]
    have hdvd : (2 : ℕ) ∣ 2 * k := ⟨k, rfl⟩
    have hks : (k : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hpos.ne'))
    simp only [dirEvenIndicator, hdvd, if_true, Pi.one_apply]
    rw [hcp, Complex.cpow_neg]
    field_simp

/-- **The Dirichlet eta identity.**  On `Re s > 1` the alternating Dirichlet series equals
`(1 − 2^{1−s})·ζ(s)`.  Splitting the constant coefficients into odd (`+1`) and even (`−1`) via
`(−1)^{n+1} = 1 − 2·[2 ∣ n]` and summing the even part gives `ζ(s) − 2·2^{−s}·ζ(s)`. -/
private theorem lseries_alt_eq (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hz : HasSum (LSeries.term (1 : ℕ → ℂ) s) (riemannZeta s) := LSeriesHasSum_one hs
  have hE := hasSum_dirEvenIndicator s hs
  have hsub : HasSum (fun n => LSeries.term (1 : ℕ → ℂ) s n - 2 * LSeries.term dirEvenIndicator s n)
      (riemannZeta s - 2 * ((2 : ℂ) ^ (-s) * riemannZeta s)) := hz.sub (hE.mul_left 2)
  have hfun : (fun n => LSeries.term (1 : ℕ → ℂ) s n - 2 * LSeries.term dirEvenIndicator s n)
      = LSeries.term (fun n => (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) s := by
    funext n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · rw [LSeries.term_of_ne_zero hpos.ne' (1 : ℕ → ℂ) s,
        LSeries.term_of_ne_zero hpos.ne' dirEvenIndicator s,
        LSeries.term_of_ne_zero hpos.ne' _ s]
      rcases Nat.even_or_odd n with he | ho
      · have hdvd : (2 : ℕ) ∣ n := he.two_dvd
        have hpow : (-1 : ℂ) ^ (n + 1) = -1 := (he.add_one).neg_one_pow
        simp only [dirEvenIndicator, hdvd, if_true, Pi.one_apply]
        push_cast [hpow]
        ring
      · have hnd : ¬ (2 : ℕ) ∣ n := by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff]
        have hpow : (-1 : ℂ) ^ (n + 1) = 1 := (ho.add_one).neg_one_pow
        simp only [dirEvenIndicator, hnd, if_false, Pi.one_apply]
        push_cast [hpow]
        ring
  rw [hfun] at hsub
  rw [show LSeries (fun n => (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) s
        = ∑' n, LSeries.term (fun n => (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) s n from rfl, hsub.tsum_eq]
  have h21s : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [h21s]; ring

/-! ### §4 The η-completion lies in the class (alternating coefficients) -/

/-- The `η`-completion `s ↦ (1 − 2^{1−s})·ξ(s)`: the completed zeta multiplied by the Dirichlet-shape
multiplier that converts `ζ` into the Dirichlet eta series. -/
noncomputable def etaCompletion : ℂ → ℂ := fun s => (1 - (2 : ℂ) ^ ((1 : ℂ) - s)) * xi s

/-- **The η-completion has completed-Dirichlet shape.**  On `Re s > 1`,
`(1 − 2^{1−s})·ξ(s) = archFactor s · ∑ (−1)^{n+1} n^{−s}`. -/
theorem etaCompletion_completedDirichletShape : CompletedDirichletShape etaCompletion := by
  refine ⟨fun n => (-1 : ℝ) ^ (n + 1), 1, fun s hs => ?_⟩
  have hspos : 0 < s.re := by linarith
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hspos; exact lt_irrefl 0 hspos
  have h1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  unfold etaCompletion
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG, lseries_alt_eq s hs]
  ring

/-! ### §5 The explicit off-line witness point -/

/-- The witness point `s₀ = 1 + (2π/log 2)·i` on the line `Re s = 1`, where `2^{1−s₀} = 1`. -/
noncomputable def s₀ : ℂ := 1 + ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I

theorem s₀_re : s₀.re = 1 := by
  simp only [s₀, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring

/-- At `s₀` the eta multiplier's exponential factor is trivial: `2^{1−s₀} = 1`, because
`log 2 · (1 − s₀) = −2π i` and `exp(−2π i) = 1`. -/
theorem two_cpow_one_sub_s₀ : (2 : ℂ) ^ ((1 : ℂ) - s₀) = 1 := by
  have hne : (Real.log 2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  have h1s : (1 : ℂ) - s₀ = - (((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) := by
    simp only [s₀]; ring
  rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog2, h1s, Complex.exp_eq_one_iff]
  refine ⟨-1, ?_⟩
  have hc : (Real.log 2) * (2 * Real.pi / Real.log 2) = 2 * Real.pi := by field_simp
  have hstep : ((Real.log 2 : ℝ) : ℂ) * -(((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I)
      = -((((Real.log 2) * (2 * Real.pi / Real.log 2) : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hstep, hc]; push_cast; ring

/-! ### §6 The η-completion has a simple zero at s₀ -/

/-- The eta multiplier `s ↦ 1 − 2^{1−s}` is entire. -/
private theorem etaFactor_analyticAt (z : ℂ) :
    AnalyticAt ℂ (fun s => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)) z := by
  have hne2 : (2 : ℂ) ≠ 0 := by norm_num
  have hwe : (fun s => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s))
      = (fun s => (1 : ℂ) - Complex.exp (Complex.log 2 * ((1 : ℂ) - s))) := by
    funext s; rw [Complex.cpow_def_of_ne_zero hne2]
  rw [hwe]
  have hdiff : Differentiable ℂ (fun s => (1 : ℂ) - Complex.exp (Complex.log 2 * ((1 : ℂ) - s))) :=
    (((differentiable_id.const_sub 1).const_mul (Complex.log 2)).cexp).const_sub 1
  exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)

/-- **The eta multiplier vanishes to first order at `s₀`.**  It is entire, vanishes at `s₀`
(`2^{1−s₀} = 1`), and its derivative there is `log 2 ≠ 0`. -/
private theorem etaFactor_order_s₀ :
    analyticOrderAt (fun s => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)) s₀ = 1 := by
  have hne2 : (2 : ℂ) ≠ 0 := by norm_num
  set L := Complex.log 2 with hL
  have hLne : L ≠ 0 := by
    rw [hL, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have hwe : (fun s => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s))
      = (fun s => (1 : ℂ) - Complex.exp (L * ((1 : ℂ) - s))) := by
    funext s; rw [hL, Complex.cpow_def_of_ne_zero hne2]
  rw [hwe]
  have hexp1 : Complex.exp (L * ((1 : ℂ) - s₀)) = 1 := by
    rw [hL, ← Complex.cpow_def_of_ne_zero hne2]; exact two_cpow_one_sub_s₀
  have hd : HasDerivAt (fun s => (1 : ℂ) - Complex.exp (L * ((1 : ℂ) - s)))
      (- (Complex.exp (L * ((1 : ℂ) - s₀)) * (L * (-1)))) s₀ := by
    have h1 : HasDerivAt (fun s : ℂ => (1 : ℂ) - s) (-1) s₀ := by
      simpa using (hasDerivAt_id s₀).const_sub 1
    exact ((h1.const_mul L).cexp).const_sub 1
  have hzero : (fun s => (1 : ℂ) - Complex.exp (L * ((1 : ℂ) - s))) s₀ = 0 := by
    simp only; rw [hexp1]; ring
  have hderiv : deriv (fun s => (1 : ℂ) - Complex.exp (L * ((1 : ℂ) - s))) s₀ = L := by
    rw [hd.deriv, hexp1]; ring
  have han : AnalyticAt ℂ (fun s => (1 : ℂ) - Complex.exp (L * ((1 : ℂ) - s))) s₀ := by
    have hdiff : Differentiable ℂ (fun s => (1 : ℂ) - Complex.exp (L * ((1 : ℂ) - s))) :=
      (((differentiable_id.const_sub 1).const_mul L).cexp).const_sub 1
    exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) s₀ (Set.mem_univ s₀)
  refine han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero ?_
  rw [hderiv]; exact hLne

/-- **The η-completion has a simple zero at `s₀`.**  The order is `1 + 0`: the eta multiplier
contributes a simple zero and `ξ(s₀) ≠ 0` contributes order `0`. -/
theorem etaCompletion_order_s₀ : analyticOrderAt etaCompletion s₀ = 1 := by
  have hxine : xi s₀ ≠ 0 := xi_ne_zero_of_one_le_re (by rw [s₀_re])
  have hxi0 : analyticOrderAt xi s₀ = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hxine)
  have hmul : etaCompletion = (fun s => (1 : ℂ) - (2 : ℂ) ^ ((1 : ℂ) - s)) * xi := rfl
  rw [hmul, analyticOrderAt_mul (etaFactor_analyticAt s₀)
      (xi_analyticOnNhd_univ s₀ (Set.mem_univ s₀)), etaFactor_order_s₀, hxi0, add_zero]

/-! ### §7 Off-line charge, hence no RH-grade parity -/

/-- **The class carries nontrivial charge at `s₀`.**  The `η`-completion is in the class and has a
simple (odd) zero at `s₀`, so its base-level deck charge there is `(−1)¹ = −1 ≠ 1`. -/
theorem carriesChargeAt_completedDirichletShape :
    CarriesChargeAt CompletedDirichletShape s₀ := by
  refine ⟨etaCompletion, etaCompletion_completedDirichletShape, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow, etaCompletion_order_s₀, ENat.toNat_one]
  norm_num

/-- **The class carries off-line charge.**  The witness point `s₀` has `Re s₀ = 1 ≠ 1/2`. -/
theorem carriesOffLineCharge_completedDirichletShape :
    CarriesOffLineCharge CompletedDirichletShape :=
  ⟨s₀, by rw [s₀_re]; norm_num, carriesChargeAt_completedDirichletShape⟩

/-- **The completed-Dirichlet shape cannot force RH-grade parity.**  Parity-forcing by charge is
exactly the charge-free (categorical) cell (`forcesRHParity_iff_categorical`); this class carries
off-line charge, so it is not categorical.  The shape constraint — arch factor times an ordinary
Dirichlet series, with no functional equation and no Euler product — is blind to off-line parity. -/
theorem not_forcesRHParity_completedDirichletShape :
    ¬ ForcesRHParity CompletedDirichletShape := by
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat carriesOffLineCharge_completedDirichletShape

/-! ### §8 Integral multiplicativity does not repair the shape class -/

/-- Ordinary integral multiplicativity for a real Dirichlet coefficient sequence.  The value at
zero is immaterial to `LSeries`; multiplicativity is imposed on every coprime pair. -/
def IntegralMultiplicativeDirichletCoefficient (a : ℕ → ℝ) : Prop :=
  (∀ n, ∃ z : ℤ, a n = z) ∧
    a 1 = 1 ∧
      ∀ ⦃m n : ℕ⦄, m.Coprime n → a (m * n) = a m * a n

/-- Completed Dirichlet shape with one and the same coefficient sequence both integral and
multiplicative.  No functional equation is included. -/
def CompletedIntegralMultiplicativeDirichletShape (f : ℂ → ℂ) : Prop :=
  ∃ (a : ℕ → ℝ) (σ₀ : ℝ), IntegralMultiplicativeDirichletCoefficient a ∧
    ∀ s : ℂ, σ₀ < s.re →
      f s = archFactor s * LSeries (fun n => ((a n : ℝ) : ℂ)) s

/-- Alternating eta coefficients, now exposed as an integral multiplicative sequence. -/
def alternatingDirichletCoefficient (n : ℕ) : ℝ := (-1 : ℝ) ^ (n + 1)

theorem alternatingDirichletCoefficient_integralMultiplicative :
    IntegralMultiplicativeDirichletCoefficient alternatingDirichletCoefficient := by
  refine ⟨fun n => ⟨(-1 : ℤ) ^ (n + 1), ?_⟩, ?_, ?_⟩
  · simp [alternatingDirichletCoefficient]
  · norm_num [alternatingDirichletCoefficient]
  · intro m n hcop
    rcases Nat.even_or_odd m with hm | hm <;>
      rcases Nat.even_or_odd n with hn | hn
    · exfalso
      have htwo : 2 ∣ Nat.gcd m n := Nat.dvd_gcd hm.two_dvd hn.two_dvd
      rw [hcop.gcd_eq_one] at htwo
      norm_num at htwo
    · simp only [alternatingDirichletCoefficient]
      rw [(hm.mul_right n).add_one.neg_one_pow,
        hm.add_one.neg_one_pow, hn.add_one.neg_one_pow]
      ring
    · simp only [alternatingDirichletCoefficient]
      rw [(hn.mul_left m).add_one.neg_one_pow,
        hm.add_one.neg_one_pow, hn.add_one.neg_one_pow]
      ring
    · simp only [alternatingDirichletCoefficient]
      rw [(hm.mul hn).add_one.neg_one_pow,
        hm.add_one.neg_one_pow, hn.add_one.neg_one_pow]
      ring

/-- The eta completion belongs to the strictly smaller class whose actual Dirichlet coefficients
are simultaneously integral and multiplicative. -/
theorem etaCompletion_completedIntegralMultiplicativeDirichletShape :
    CompletedIntegralMultiplicativeDirichletShape etaCompletion := by
  refine ⟨alternatingDirichletCoefficient, 1,
    alternatingDirichletCoefficient_integralMultiplicative, fun s hs => ?_⟩
  have hspos : 0 < s.re := by linarith
  have h0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hspos; exact lt_irrefl 0 hspos
  have h1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl 1 hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  unfold etaCompletion
  simp only [alternatingDirichletCoefficient]
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG, lseries_alt_eq s hs]
  ring

/-- **Completed integral-multiplicative shape blindness law.**  Even after integrality and
multiplicativity are imposed on the very coefficients in the completed Dirichlet presentation,
the class carries a simple off-line charge and cannot force RH-grade parity. -/
theorem completedIntegralMultiplicativeDirichletShape_blindnessUniversality :
    CarriesOffLineCharge CompletedIntegralMultiplicativeDirichletShape ∧
      ¬ ForcesRHParity CompletedIntegralMultiplicativeDirichletShape := by
  have hcharge : CarriesChargeAt CompletedIntegralMultiplicativeDirichletShape s₀ := by
    refine ⟨etaCompletion,
      etaCompletion_completedIntegralMultiplicativeDirichletShape, ?_⟩
    rw [carrierCharge_one_eq_neg_one_pow, etaCompletion_order_s₀, ENat.toNat_one]
    norm_num
  have hoff : CarriesOffLineCharge CompletedIntegralMultiplicativeDirichletShape :=
    ⟨s₀, by rw [s₀_re]; norm_num, hcharge⟩
  refine ⟨hoff, ?_⟩
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat hoff

/-- **The Euler contrast: multiplicativity empties all charge beyond the wall.**  ξ — whose
Dirichlet coefficients carry the Euler product — is zero-free on `re ≥ 1`, so every window beyond
the wall is vacuum and carries zero deck charge at every level, while the η-completion, a member
of the same completed integral-multiplicative shape class but WITHOUT a functional equation,
carries charge `−1` at a point ON the wall.  The Euler product kills charge wherever it applies;
the open frontier is the reach of that kill across the strip. -/
theorem xi_chargeFree_beyond_wall (k : ℕ) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hball : ∀ z ∈ Metric.closedBall c r, 1 ≤ z.re) :
    boxCharge k xi c r = 0 :=
  boxCharge_eq_zero_of_vacuum k hr xi_differentiable.continuous.continuousOn
    fun z hz => xi_ne_zero_of_one_le_re (hball z hz)

end RHTower
