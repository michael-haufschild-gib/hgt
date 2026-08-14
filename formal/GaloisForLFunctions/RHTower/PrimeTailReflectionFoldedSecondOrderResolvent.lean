import GaloisForLFunctions.RHTower.CriticalHalfDensityPrimeTailResolventLaw

/-!
# Reflection-folded second-order prime-tail resolvent

The first-order ordinary-prime transport equation

`(∂_L - lam) H_lam = -Π₀`,   `Π₀ = Σ_{n ≥ 2} Λ(n)/(√n log n) δ_{log n}`,

is folded across the reflection `lam ↦ -lam` before any zero of the completed Xi function is
selected.  A completed branch is a homogeneous datum plus the causal accumulation of the literal
prime measure,

`H_lam(L) = e^{lam L} P(lam) - Σ_{log n < L} Λ(n)/(√n log n) e^{lam (L - log n)}`.

The causal part is single-valued and carries the whole forcing; the datum `P` carries the whole
homogeneous freedom.  Hence the half-sum and the divided difference

`C_lam = (H_lam + H_{-lam})/2`,  `S_lam = (H_lam - H_{-lam})/(2 lam)`

satisfy the parameter-independent second-order equations

`(∂_L² - lam²) S_lam = -Π₀`,  `(∂_L² - lam²) C_lam = -∂_L Π₀`,

with Cauchy data at the source point `L = 0` given by `P` alone.  A monodromy increment of `P` by
`2πi m` produces exactly the two global modes `2πi m cosh(lam L)` and `2πi m sinh(lam L)/lam`,
both solutions of `u'' = mu u` with `mu = lam²`; `mu` is invariant under the functional equation
`ρ ↦ 1 - ρ`, and reality of `mu` forces the critical line on every nonreal point.

Every statement is unconditional: the homogeneous datum `P` is an arbitrary function of the folded
parameter, and no zero, branch, or spectral realization is assumed.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions ENNReal

namespace RHTower

noncomputable section

/-! ## Locally finite causal prime accumulation -/

/-- Only finitely many positive-integer logarithms lie strictly below a cut. -/
theorem primeFoldBelow_finite (B : ℝ) :
    {n : DeningerPrimePowerIndex | deningerPrimePowerTime n < B}.Finite := by
  refine (deningerPrimeActiveSet_finite ⟨Icc 0 B, isCompact_Icc⟩).subset ?_
  intro n hn
  exact ⟨(deningerPrimePowerTime_pos n).le, le_of_lt hn⟩

/-- The finite set of prime-power indices seated strictly below a cut. -/
def primeFoldBelowFinset (B : ℝ) : Finset DeningerPrimePowerIndex :=
  (primeFoldBelow_finite B).toFinset

@[simp]
theorem mem_primeFoldBelowFinset (B : ℝ) (n : DeningerPrimePowerIndex) :
    n ∈ primeFoldBelowFinset B ↔ deningerPrimePowerTime n < B := by
  simp [primeFoldBelowFinset]

/-- One causal Green atom of `∂_L - lam` seated at the logarithmic time of `n`. -/
def primeFoldCausalAtom (lam : ℂ) (n : DeningerPrimePowerIndex) (L : ℝ) : ℂ :=
  if deningerPrimePowerTime n < L then
    (criticalPrimeTailAtomWeight n : ℂ) *
      Complex.exp (lam * ((L - deningerPrimePowerTime n : ℝ) : ℂ))
  else 0

theorem primeFoldCausalAtom_eq_indicator (lam : ℂ) (n : DeningerPrimePowerIndex) :
    primeFoldCausalAtom lam n =
      Set.indicator (Ioi (deningerPrimePowerTime n))
        (fun L : ℝ => (criticalPrimeTailAtomWeight n : ℂ) *
          Complex.exp (lam * ((L - deningerPrimePowerTime n : ℝ) : ℂ))) := by
  funext L
  by_cases hL : deningerPrimePowerTime n < L <;>
    simp [primeFoldCausalAtom, Set.indicator, hL]

theorem primeFoldCausalAtom_eq_zero_of_le
    (lam : ℂ) (n : DeningerPrimePowerIndex) {L : ℝ}
    (hL : L ≤ deningerPrimePowerTime n) :
    primeFoldCausalAtom lam n L = 0 := by
  simp [primeFoldCausalAtom, not_lt.mpr hL]

/-- Every ordinary-prime atom is seated at or after `log 2`. -/
theorem log_two_le_deningerPrimePowerTime (n : DeningerPrimePowerIndex) :
    Real.log 2 ≤ deningerPrimePowerTime n := by
  rw [deningerPrimePowerTime]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast n.property)

/-- The accumulated ordinary-prime source at rate `lam`.  For each time the sum is finite. -/
def primeFoldCausalTail (lam : ℂ) (L : ℝ) : ℂ :=
  ∑' n : DeningerPrimePowerIndex, primeFoldCausalAtom lam n L

/-- Below a cut the accumulation is the explicit finite sum over the active indices. -/
theorem primeFoldCausalTail_eq_sum (lam : ℂ) {B L : ℝ} (hLB : L ≤ B) :
    primeFoldCausalTail lam L =
      ∑ n ∈ primeFoldBelowFinset B, primeFoldCausalAtom lam n L := by
  refine tsum_eq_sum ?_
  intro n hn
  have hnB : ¬ deningerPrimePowerTime n < B := by
    simpa using hn
  exact primeFoldCausalAtom_eq_zero_of_le lam n (hLB.trans (not_lt.mp hnB))

/-- No ordinary-prime atom is seated before `log 2`. -/
theorem primeFoldCausalTail_eq_zero (lam : ℂ) {L : ℝ} (hL : L ≤ Real.log 2) :
    primeFoldCausalTail lam L = 0 := by
  have hzero : ∀ n : DeningerPrimePowerIndex, primeFoldCausalAtom lam n L = 0 := fun n =>
    primeFoldCausalAtom_eq_zero_of_le lam n (hL.trans (log_two_le_deningerPrimePowerTime n))
  simp [primeFoldCausalTail, hzero]

/-! ## The completed branch -/

/-- A completed prime-tail branch: a homogeneous datum in the folded parameter minus the causal
accumulation of the literal ordinary-prime measure. -/
def primeFoldBranch (P : ℂ → ℂ) (lam : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (lam * (L : ℂ)) * P lam - primeFoldCausalTail lam L

/-- Increasing the homogeneous datum by a constant shifts the branch by a pure homogeneous
solution; the ordinary-prime accumulation is single-valued. -/
theorem primeFoldBranch_add_const (P : ℂ → ℂ) (c : ℂ) (lam : ℂ) (L : ℝ) :
    primeFoldBranch (fun w => P w + c) lam L - primeFoldBranch P lam L =
      c * Complex.exp (lam * (L : ℂ)) := by
  simp only [primeFoldBranch]
  ring

/-- The source point carries no prime atom: the branch value there is the datum. -/
theorem primeFoldBranch_zero (P : ℂ → ℂ) (lam : ℂ) :
    primeFoldBranch P lam 0 = P lam := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  simp [primeFoldBranch, primeFoldCausalTail_eq_zero lam hlog]

/-- Near the source point the branch is purely homogeneous, so its Cauchy derivative there is
`lam` times the datum. -/
theorem primeFoldBranch_hasDerivAt_zero (P : ℂ → ℂ) (lam : ℂ) :
    HasDerivAt (primeFoldBranch P lam) (lam * P lam) 0 := by
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlin : HasDerivAt (fun x : ℝ => lam * (x : ℂ)) lam 0 := by
    simpa [mul_comm] using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul lam)
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (lam * (x : ℂ)))
      (Complex.exp (lam * ((0 : ℝ) : ℂ)) * lam) 0 := hlin.cexp
  have hhom : HasDerivAt (fun x : ℝ => Complex.exp (lam * (x : ℂ)) * P lam)
      (lam * P lam) 0 := by
    have := hexp.mul_const (P lam)
    simpa using this
  refine hhom.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hlogpos] with x hx
  simp [primeFoldBranch, primeFoldCausalTail_eq_zero lam (le_of_lt hx)]

/-! ## Forcing functional on compactly supported functions -/

/-- Action of the literal ordinary-prime forcing measure on a function of logarithmic time. -/
def primeFoldForcing (f : ℝ → ℂ) : ℂ :=
  ∑' n : DeningerPrimePowerIndex,
    (criticalPrimeTailAtomWeight n : ℂ) * f (deningerPrimePowerTime n)

theorem primeFoldForcing_eq_sum {f : ℝ → ℂ} {B : ℝ}
    (hf : ∀ L, B ≤ L → f L = 0) :
    primeFoldForcing f =
      ∑ n ∈ primeFoldBelowFinset B,
        (criticalPrimeTailAtomWeight n : ℂ) * f (deningerPrimePowerTime n) := by
  refine tsum_eq_sum ?_
  intro n hn
  have hnB : ¬ deningerPrimePowerTime n < B := by simpa using hn
  simp [hf _ (not_lt.mp hnB)]

theorem summable_primeFoldForcing {f : ℝ → ℂ} {B : ℝ}
    (hf : ∀ L, B ≤ L → f L = 0) :
    Summable (fun n : DeningerPrimePowerIndex =>
      (criticalPrimeTailAtomWeight n : ℂ) * f (deningerPrimePowerTime n)) := by
  refine summable_of_ne_finset_zero (s := primeFoldBelowFinset B) ?_
  intro n hn
  have hnB : ¬ deningerPrimePowerTime n < B := by simpa using hn
  simp [hf _ (not_lt.mp hnB)]

/-- A compactly supported function vanishes beyond some cut. -/
theorem exists_vanishing_bound {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ B : ℝ, ∀ L : ℝ, B ≤ L → f L = 0 := by
  obtain ⟨B₀, hB₀⟩ := bddAbove_def.mp hf.bddAbove
  refine ⟨B₀ + 1, fun L hL => ?_⟩
  by_contra hne
  have hmem : L ∈ tsupport f := subset_tsupport _ (by simpa [Function.mem_support] using hne)
  have := hB₀ L hmem
  linarith

theorem primeFoldForcing_sub {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    primeFoldForcing (fun L => f L - g L) =
      primeFoldForcing f - primeFoldForcing g := by
  obtain ⟨B₁, h₁⟩ := exists_vanishing_bound hf
  obtain ⟨B₂, h₂⟩ := exists_vanishing_bound hg
  have hs₁ := summable_primeFoldForcing (B := max B₁ B₂) (f := f)
    (fun L hL => h₁ L ((le_max_left B₁ B₂).trans hL))
  have hs₂ := summable_primeFoldForcing (B := max B₁ B₂) (f := g)
    (fun L hL => h₂ L ((le_max_right B₁ B₂).trans hL))
  rw [primeFoldForcing, primeFoldForcing, primeFoldForcing, ← hs₁.tsum_sub hs₂]
  exact tsum_congr fun n => by ring

theorem primeFoldForcing_add {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    primeFoldForcing (fun L => f L + g L) =
      primeFoldForcing f + primeFoldForcing g := by
  obtain ⟨B₁, h₁⟩ := exists_vanishing_bound hf
  obtain ⟨B₂, h₂⟩ := exists_vanishing_bound hg
  have hs₁ := summable_primeFoldForcing (B := max B₁ B₂) (f := f)
    (fun L hL => h₁ L ((le_max_left B₁ B₂).trans hL))
  have hs₂ := summable_primeFoldForcing (B := max B₁ B₂) (f := g)
    (fun L hL => h₂ L ((le_max_right B₁ B₂).trans hL))
  rw [primeFoldForcing, primeFoldForcing, primeFoldForcing, ← hs₁.tsum_add hs₂]
  exact tsum_congr fun n => by ring

theorem primeFoldForcing_const_mul (c : ℂ) (f : ℝ → ℂ) :
    primeFoldForcing (fun L => c * f L) = c * primeFoldForcing f := by
  rw [primeFoldForcing, primeFoldForcing, ← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-! ## The first-order transport law -/

/-- Whole-line integral of the derivative of a compactly supported `C¹` function. -/
theorem integral_deriv_primeFold_eq_zero_of_hasCompactSupport
    {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hsupp : HasCompactSupport g) :
    (∫ L : ℝ, deriv g L) = 0 := by
  have hint : Integrable fun L : ℝ => deriv g L :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hsupp.deriv
  have hsplit :=
    MeasureTheory.integral_add_compl (μ := (volume : Measure ℝ))
      (measurableSet_Iic (a := (0 : ℝ))) hint
  have hIic : (∫ L : ℝ in Iic (0 : ℝ), deriv g L) = g 0 :=
    HasCompactSupport.integral_Iic_deriv_eq hg hsupp 0
  have hIoi : (∫ L : ℝ in Ioi (0 : ℝ), deriv g L) = -g 0 :=
    HasCompactSupport.integral_Ioi_deriv_eq hg hsupp 0
  rw [compl_Iic] at hsplit
  rw [hIic, hIoi] at hsplit
  simpa using hsplit.symm

/-- Pointwise decomposition of a compactly supported pairing into the homogeneous term and the
finitely many active causal atoms. -/
theorem mul_primeFoldBranch_eq_sub_sum
    (P : ℂ → ℂ) (lam : ℂ) {g : ℝ → ℂ} {B : ℝ}
    (hgzero : ∀ L : ℝ, B ≤ L → g L = 0) (L : ℝ) :
    g L * primeFoldBranch P lam L =
      g L * (Complex.exp (lam * (L : ℂ)) * P lam) -
        ∑ n ∈ primeFoldBelowFinset B, g L * primeFoldCausalAtom lam n L := by
  by_cases hL : L ≤ B
  · rw [primeFoldBranch, primeFoldCausalTail_eq_sum lam hL, mul_sub, Finset.mul_sum]
  · have hgL : g L = 0 := hgzero L (le_of_lt (not_le.mp hL))
    simp [hgL]

theorem integrable_mul_primeFoldCausalAtom
    (lam : ℂ) (n : DeningerPrimePowerIndex) {g : ℝ → ℂ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun L : ℝ => g L * primeFoldCausalAtom lam n L) := by
  classical
  have hcont : Continuous (fun L : ℝ => (criticalPrimeTailAtomWeight n : ℂ) *
      Complex.exp (lam * ((L - deningerPrimePowerTime n : ℝ) : ℂ))) := by fun_prop
  have hbase : Integrable (fun L : ℝ => g L * ((criticalPrimeTailAtomWeight n : ℂ) *
      Complex.exp (lam * ((L - deningerPrimePowerTime n : ℝ) : ℂ)))) :=
    (hgc.mul hcont).integrable_of_hasCompactSupport hgs.mul_right
  have hind := hbase.indicator (measurableSet_Ioi (a := deningerPrimePowerTime n))
  refine hind.congr ?_
  filter_upwards [] with L
  by_cases hL : deningerPrimePowerTime n < L <;>
    simp [primeFoldCausalAtom, Set.indicator, hL]

theorem integrable_mul_primeFoldHomogeneous
    (P : ℂ → ℂ) (lam : ℂ) {g : ℝ → ℂ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun L : ℝ => g L * (Complex.exp (lam * (L : ℂ)) * P lam)) := by
  have hcont : Continuous (fun L : ℝ => Complex.exp (lam * (L : ℂ)) * P lam) := by fun_prop
  exact (hgc.mul hcont).integrable_of_hasCompactSupport hgs.mul_right

/-- Every compactly supported continuous pairing with a completed branch is integrable. -/
theorem integrable_mul_primeFoldBranch
    (P : ℂ → ℂ) (lam : ℂ) {g : ℝ → ℂ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun L : ℝ => g L * primeFoldBranch P lam L) := by
  classical
  obtain ⟨B, hB⟩ := exists_vanishing_bound hgs
  have hsum : Integrable (fun L : ℝ =>
      ∑ n ∈ primeFoldBelowFinset B, g L * primeFoldCausalAtom lam n L) :=
    integrable_finsetSum _ fun n _ => integrable_mul_primeFoldCausalAtom lam n hgc hgs
  have := (integrable_mul_primeFoldHomogeneous P lam hgc hgs).sub hsum
  refine this.congr ?_
  filter_upwards [] with L
  exact (mul_primeFoldBranch_eq_sub_sum P lam hB L).symm

/-- One causal atom absorbs exactly its own prime mass under the transport operator. -/
theorem integral_primeFoldCausalAtom_transport
    (lam : ℂ) (n : DeningerPrimePowerIndex) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    (∫ L : ℝ, (deriv ψ L + lam * ψ L) * primeFoldCausalAtom lam n L) =
      -((criticalPrimeTailAtomWeight n : ℂ) * ψ (deningerPrimePowerTime n)) := by
  set t : ℝ := deningerPrimePowerTime n with ht
  set G : ℝ → ℂ := fun L => ψ L * Complex.exp (lam * ((L - t : ℝ) : ℂ)) with hG
  have hexpCD : ContDiff ℝ 1 (fun L : ℝ => Complex.exp (lam * ((L - t : ℝ) : ℂ))) := by
    have hlin : ContDiff ℝ 1 (fun L : ℝ => lam * ((L - t : ℝ) : ℂ)) := by
      have : ContDiff ℝ 1 (fun L : ℝ => ((L - t : ℝ) : ℂ)) := by
        simpa [Function.comp_def] using
          (Complex.ofRealCLM.contDiff.comp
            ((contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ)).sub contDiff_const))
      exact contDiff_const.mul this
    exact hlin.cexp
  have hGCD : ContDiff ℝ 1 G := hψ.mul hexpCD
  have hGsupp : HasCompactSupport G := hsupp.mul_right
  have hderivG : ∀ L : ℝ,
      HasDerivAt G ((deriv ψ L + lam * ψ L) *
        Complex.exp (lam * ((L - t : ℝ) : ℂ))) L := by
    intro L
    have h1 : HasDerivAt ψ (deriv ψ L) L :=
      (hψ.differentiable (by simp)).differentiableAt.hasDerivAt
    have hlin : HasDerivAt (fun x : ℝ => lam * ((x - t : ℝ) : ℂ)) lam L := by
      simpa [mul_comm] using
        (((hasDerivAt_id L).sub_const t).ofReal_comp.const_mul lam)
    have h2 : HasDerivAt (fun x : ℝ => Complex.exp (lam * ((x - t : ℝ) : ℂ)))
        (Complex.exp (lam * ((L - t : ℝ) : ℂ)) * lam) L := hlin.cexp
    rw [hG, show (deriv ψ L + lam * ψ L) * Complex.exp (lam * ((L - t : ℝ) : ℂ)) =
        deriv ψ L * Complex.exp (lam * ((L - t : ℝ) : ℂ)) +
          ψ L * (Complex.exp (lam * ((L - t : ℝ) : ℂ)) * lam) from by ring]
    exact h1.mul h2
  have hderivEq : (fun L : ℝ => deriv G L) =
      fun L : ℝ => (deriv ψ L + lam * ψ L) * Complex.exp (lam * ((L - t : ℝ) : ℂ)) := by
    funext L
    exact (hderivG L).deriv
  have hIoi := HasCompactSupport.integral_Ioi_deriv_eq hGCD hGsupp t
  rw [hderivEq] at hIoi
  have hGt : G t = ψ t := by simp [hG]
  rw [hGt] at hIoi
  have hpoint : (fun L : ℝ => (deriv ψ L + lam * ψ L) * primeFoldCausalAtom lam n L) =
      Set.indicator (Ioi t)
        (fun L : ℝ => (criticalPrimeTailAtomWeight n : ℂ) *
          ((deriv ψ L + lam * ψ L) * Complex.exp (lam * ((L - t : ℝ) : ℂ)))) := by
    funext L
    by_cases hL : t < L
    · simp only [primeFoldCausalAtom, ← ht, if_pos hL,
        Set.indicator_of_mem (mem_Ioi.mpr hL)]
      ring
    · simp [primeFoldCausalAtom, ← ht, Set.indicator, hL]
  rw [hpoint, integral_indicator measurableSet_Ioi, integral_const_mul, hIoi]
  ring

/-- **First-order ordinary-prime transport law.**  Against every compactly supported `C¹`
function the completed branch reproduces exactly the literal prime forcing, for every homogeneous
datum and every value of the folded parameter.  This is `(∂_L - lam) H_lam = -Π₀`. -/
theorem integral_primeFoldBranch_transport
    (P : ℂ → ℂ) (lam : ℂ) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hsupp : HasCompactSupport ψ) :
    (∫ L : ℝ, (deriv ψ L + lam * ψ L) * primeFoldBranch P lam L) =
      primeFoldForcing ψ := by
  classical
  obtain ⟨B, hψzero⟩ := exists_vanishing_bound hsupp
  obtain ⟨B', hderivzero⟩ := exists_vanishing_bound hsupp.deriv
  set C : ℝ := max B B' with hC
  have hψzeroC : ∀ L : ℝ, C ≤ L → ψ L = 0 :=
    fun L hL => hψzero L ((le_max_left B B').trans hL)
  have hderivzeroC : ∀ L : ℝ, C ≤ L → deriv ψ L = 0 :=
    fun L hL => hderivzero L ((le_max_right B B').trans hL)
  set g : ℝ → ℂ := fun L => deriv ψ L + lam * ψ L with hg
  have hgzero : ∀ L : ℝ, C ≤ L → g L = 0 := by
    intro L hL
    simp [hg, hψzeroC L hL, hderivzeroC L hL]
  have hgCont : Continuous g :=
    (hψ.continuous_deriv le_rfl).add (continuous_const.mul hψ.continuous)
  have hgSupp : HasCompactSupport g :=
    HasCompactSupport.add hsupp.deriv hsupp.mul_left
  have hhomInt : (∫ L : ℝ, g L * (Complex.exp (lam * (L : ℂ)) * P lam)) = 0 := by
    have hhomCD : ContDiff ℝ 1 (fun L : ℝ => ψ L * (Complex.exp (lam * (L : ℂ)) * P lam)) := by
      have hexpCD : ContDiff ℝ 1 (fun L : ℝ => Complex.exp (lam * (L : ℂ))) := by
        have hlin : ContDiff ℝ 1 (fun L : ℝ => lam * (L : ℂ)) := by
          have : ContDiff ℝ 1 (fun L : ℝ => (L : ℂ)) := Complex.ofRealCLM.contDiff
          exact contDiff_const.mul this
        exact hlin.cexp
      exact hψ.mul (hexpCD.mul contDiff_const)
    have hhomSupp : HasCompactSupport
        (fun L : ℝ => ψ L * (Complex.exp (lam * (L : ℂ)) * P lam)) := hsupp.mul_right
    have hhomDeriv : (fun L : ℝ =>
        deriv (fun x : ℝ => ψ x * (Complex.exp (lam * (x : ℂ)) * P lam)) L) =
        fun L : ℝ => g L * (Complex.exp (lam * (L : ℂ)) * P lam) := by
      funext L
      have h1 : HasDerivAt ψ (deriv ψ L) L :=
        (hψ.differentiable (by simp)).differentiableAt.hasDerivAt
      have hlin : HasDerivAt (fun x : ℝ => lam * (x : ℂ)) lam L := by
        simpa [mul_comm] using ((hasDerivAt_id L).ofReal_comp.const_mul lam)
      have h2 : HasDerivAt (fun x : ℝ => Complex.exp (lam * (x : ℂ)))
          (Complex.exp (lam * (L : ℂ)) * lam) L := hlin.cexp
      have h3 : HasDerivAt (fun x : ℝ => Complex.exp (lam * (x : ℂ)) * P lam)
          (Complex.exp (lam * (L : ℂ)) * lam * P lam) L := h2.mul_const (P lam)
      have hmul : HasDerivAt (fun x : ℝ => ψ x * (Complex.exp (lam * (x : ℂ)) * P lam))
          (deriv ψ L * (Complex.exp (lam * (L : ℂ)) * P lam) +
            ψ L * (Complex.exp (lam * (L : ℂ)) * lam * P lam)) L := h1.mul h3
      rw [hmul.deriv]
      simp only [hg]
      ring
    rw [← hhomDeriv]
    exact integral_deriv_primeFold_eq_zero_of_hasCompactSupport hhomCD hhomSupp
  have hpoint := mul_primeFoldBranch_eq_sub_sum P lam hgzero
  rw [show (fun L : ℝ => (deriv ψ L + lam * ψ L) * primeFoldBranch P lam L) =
      fun L : ℝ => g L * primeFoldBranch P lam L from rfl]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_sub
    (integrable_mul_primeFoldHomogeneous P lam hgCont hgSupp)
    (integrable_finsetSum _ fun n _ => integrable_mul_primeFoldCausalAtom lam n hgCont hgSupp)]
  rw [hhomInt, integral_finsetSum _ (fun n _ =>
    integrable_mul_primeFoldCausalAtom lam n hgCont hgSupp)]
  have hatom : ∀ n : DeningerPrimePowerIndex,
      (∫ L : ℝ, g L * primeFoldCausalAtom lam n L) =
        -((criticalPrimeTailAtomWeight n : ℂ) * ψ (deningerPrimePowerTime n)) :=
    fun n => integral_primeFoldCausalAtom_transport lam n hψ hsupp
  simp only [hatom]
  rw [primeFoldForcing_eq_sum hψzeroC]
  simp

/-! ## The reflection fold -/

/-- Even reflection fold of the completed branch. -/
def primeFoldEven (P : ℂ → ℂ) (lam : ℂ) (L : ℝ) : ℂ :=
  (primeFoldBranch P lam L + primeFoldBranch P (-lam) L) / 2

/-- Odd reflection fold: the resolvent divided difference in the folded parameter. -/
def primeFoldOdd (P : ℂ → ℂ) (lam : ℂ) (L : ℝ) : ℂ :=
  (primeFoldBranch P lam L - primeFoldBranch P (-lam) L) / (2 * lam)

theorem contDiff_deriv_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (deriv φ) := by
  have h : ContDiff ℝ (1 + 1 : ℕ) φ := by norm_num; exact hφ
  simpa using ContDiff.deriv' h

/-- Second-order pairing of the branch at rate `lam`. -/
theorem integral_primeFoldBranch_secondOrder
    (P : ℂ → ℂ) (lam : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : HasCompactSupport φ) :
    (∫ L : ℝ, (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P lam L) =
      primeFoldForcing (fun L => deriv φ L - lam * φ L) := by
  have hderivCD : ContDiff ℝ 1 (deriv φ) := contDiff_deriv_of_contDiff_two hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hψCD : ContDiff ℝ 1 (fun L : ℝ => deriv φ L - lam * φ L) :=
    hderivCD.sub (contDiff_const.mul hφ1)
  have hψsupp : HasCompactSupport (fun L : ℝ => deriv φ L - lam * φ L) :=
    HasCompactSupport.sub hsupp.deriv hsupp.mul_left
  have hderivψ : ∀ L : ℝ,
      deriv (fun x : ℝ => deriv φ x - lam * φ x) L =
        deriv (deriv φ) L - lam * deriv φ L := by
    intro L
    have h1 : DifferentiableAt ℝ (deriv φ) L :=
      (hderivCD.differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ φ L := (hφ1.differentiable (by simp)).differentiableAt
    have hd : HasDerivAt (fun x : ℝ => deriv φ x - lam * φ x)
        (deriv (deriv φ) L - lam * deriv φ L) L :=
      h1.hasDerivAt.sub (h2.hasDerivAt.const_mul lam)
    exact hd.deriv
  have hmain := integral_primeFoldBranch_transport P lam hψCD hψsupp
  rw [show (fun L : ℝ =>
      (deriv (fun x : ℝ => deriv φ x - lam * φ x) L +
        lam * (deriv φ L - lam * φ L)) * primeFoldBranch P lam L) =
      fun L : ℝ => (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P lam L from by
    funext L; rw [hderivψ L]; ring] at hmain
  exact hmain

/-- Second-order pairing of the branch at the reflected rate `-lam`. -/
theorem integral_primeFoldBranch_secondOrder_reflected
    (P : ℂ → ℂ) (lam : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : HasCompactSupport φ) :
    (∫ L : ℝ, (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P (-lam) L) =
      primeFoldForcing (fun L => deriv φ L + lam * φ L) := by
  have h := integral_primeFoldBranch_secondOrder P (-lam) hφ hsupp
  simpa [sub_neg_eq_add, neg_mul] using h

theorem continuous_secondOrderSymbol {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (lam : ℂ) :
    Continuous (fun L : ℝ => deriv (deriv φ) L - lam ^ 2 * φ L) :=
  ((contDiff_deriv_of_contDiff_two hφ).continuous_deriv le_rfl).sub
    (continuous_const.mul hφ.continuous)

theorem hasCompactSupport_secondOrderSymbol {φ : ℝ → ℂ}
    (hsupp : HasCompactSupport φ) (lam : ℂ) :
    HasCompactSupport (fun L : ℝ => deriv (deriv φ) L - lam ^ 2 * φ L) :=
  HasCompactSupport.sub hsupp.deriv.deriv hsupp.mul_left

/-- **Reflection fold, odd part.**  The divided difference obeys the parameter-independent
second-order equation `(∂_L² - lam²) S_lam = -Π₀`. -/
theorem integral_primeFoldOdd_secondOrder
    (P : ℂ → ℂ) {lam : ℂ} (hlam : lam ≠ 0) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : HasCompactSupport φ) :
    (∫ L : ℝ, (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldOdd P lam L) =
      -primeFoldForcing φ := by
  have hgCont := continuous_secondOrderSymbol hφ lam
  have hgSupp := hasCompactSupport_secondOrderSymbol hsupp lam
  have hu := integrable_mul_primeFoldBranch P lam hgCont hgSupp
  have hv := integrable_mul_primeFoldBranch P (-lam) hgCont hgSupp
  have hsplit : (fun L : ℝ =>
      (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldOdd P lam L) =
      fun L : ℝ =>
        ((deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P lam L -
          (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P (-lam) L) / (2 * lam) := by
    funext L
    rw [primeFoldOdd]
    ring
  rw [hsplit, integral_div, integral_sub hu hv,
    integral_primeFoldBranch_secondOrder P lam hφ hsupp,
    integral_primeFoldBranch_secondOrder_reflected P lam hφ hsupp]
  have hminus : HasCompactSupport (fun L : ℝ => deriv φ L - lam * φ L) :=
    HasCompactSupport.sub hsupp.deriv hsupp.mul_left
  have hplus : HasCompactSupport (fun L : ℝ => deriv φ L + lam * φ L) :=
    HasCompactSupport.add hsupp.deriv hsupp.mul_left
  rw [← primeFoldForcing_sub hminus hplus]
  have hrw : (fun L : ℝ => (deriv φ L - lam * φ L) - (deriv φ L + lam * φ L)) =
      fun L : ℝ => (-(2 * lam)) * φ L := by
    funext L; ring
  rw [hrw, primeFoldForcing_const_mul]
  field_simp

/-- **Reflection fold, even part.**  The half-sum obeys `(∂_L² - lam²) C_lam = -∂_L Π₀`, whose
right-hand side is the prime forcing evaluated on the derivative of the test function. -/
theorem integral_primeFoldEven_secondOrder
    (P : ℂ → ℂ) (lam : ℂ) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : HasCompactSupport φ) :
    (∫ L : ℝ, (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldEven P lam L) =
      primeFoldForcing (deriv φ) := by
  have hgCont := continuous_secondOrderSymbol hφ lam
  have hgSupp := hasCompactSupport_secondOrderSymbol hsupp lam
  have hu := integrable_mul_primeFoldBranch P lam hgCont hgSupp
  have hv := integrable_mul_primeFoldBranch P (-lam) hgCont hgSupp
  have hsplit : (fun L : ℝ =>
      (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldEven P lam L) =
      fun L : ℝ =>
        ((deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P lam L +
          (deriv (deriv φ) L - lam ^ 2 * φ L) * primeFoldBranch P (-lam) L) / 2 := by
    funext L
    rw [primeFoldEven]
    ring
  rw [hsplit, integral_div, integral_add hu hv,
    integral_primeFoldBranch_secondOrder P lam hφ hsupp,
    integral_primeFoldBranch_secondOrder_reflected P lam hφ hsupp]
  have hminus : HasCompactSupport (fun L : ℝ => deriv φ L - lam * φ L) :=
    HasCompactSupport.sub hsupp.deriv hsupp.mul_left
  have hplus : HasCompactSupport (fun L : ℝ => deriv φ L + lam * φ L) :=
    HasCompactSupport.add hsupp.deriv hsupp.mul_left
  have hcombine := primeFoldForcing_add hminus hplus
  have hrw : (fun L : ℝ => (deriv φ L - lam * φ L) + (deriv φ L + lam * φ L)) =
      fun L : ℝ => (2 : ℂ) * deriv φ L := by funext L; ring
  rw [hrw, primeFoldForcing_const_mul] at hcombine
  rw [← hcombine]
  ring

/-! ## Cauchy data of the folds at the source point -/

theorem primeFoldEven_zero (P : ℂ → ℂ) (lam : ℂ) :
    primeFoldEven P lam 0 = (P lam + P (-lam)) / 2 := by
  simp [primeFoldEven, primeFoldBranch_zero]

theorem primeFoldOdd_zero (P : ℂ → ℂ) (lam : ℂ) :
    primeFoldOdd P lam 0 = (P lam - P (-lam)) / (2 * lam) := by
  simp [primeFoldOdd, primeFoldBranch_zero]

theorem primeFoldEven_hasDerivAt_zero (P : ℂ → ℂ) (lam : ℂ) :
    HasDerivAt (primeFoldEven P lam) ((lam * P lam - lam * P (-lam)) / 2) 0 := by
  have h1 := primeFoldBranch_hasDerivAt_zero P lam
  have h2 := primeFoldBranch_hasDerivAt_zero P (-lam)
  have h := (h1.add h2).div_const 2
  refine h.congr_deriv ?_
  ring

theorem primeFoldOdd_hasDerivAt_zero (P : ℂ → ℂ) (lam : ℂ) :
    HasDerivAt (primeFoldOdd P lam) ((lam * P lam + lam * P (-lam)) / (2 * lam)) 0 := by
  have h1 := primeFoldBranch_hasDerivAt_zero P lam
  have h2 := primeFoldBranch_hasDerivAt_zero P (-lam)
  have h := (h1.sub h2).div_const (2 * lam)
  refine h.congr_deriv ?_
  ring

/-- **Source Cauchy data of the even fold.**  For an even datum the half-sum has Dirichlet value
`P lam` and vanishing Neumann datum. -/
theorem primeFoldEven_cauchy_data_of_even
    (P : ℂ → ℂ) (lam : ℂ) (heven : P (-lam) = P lam) :
    primeFoldEven P lam 0 = P lam ∧ HasDerivAt (primeFoldEven P lam) 0 0 := by
  refine ⟨?_, ?_⟩
  · rw [primeFoldEven_zero, heven]; ring
  · have h := primeFoldEven_hasDerivAt_zero P lam
    rw [heven] at h
    exact h.congr_deriv (by ring)

/-- **Source Cauchy data of the odd fold.**  For an even datum the divided difference has
vanishing Dirichlet value and Neumann datum `P lam`. -/
theorem primeFoldOdd_cauchy_data_of_even
    (P : ℂ → ℂ) {lam : ℂ} (hlam : lam ≠ 0) (heven : P (-lam) = P lam) :
    primeFoldOdd P lam 0 = 0 ∧ HasDerivAt (primeFoldOdd P lam) (P lam) 0 := by
  refine ⟨?_, ?_⟩
  · rw [primeFoldOdd_zero, heven]; simp
  · have h := primeFoldOdd_hasDerivAt_zero P lam
    rw [heven] at h
    refine h.congr_deriv ?_
    rw [show lam * P lam + lam * P lam = 2 * lam * P lam from by ring]
    exact mul_div_cancel_left₀ (P lam) (mul_ne_zero two_ne_zero hlam)

/-! ## Source-pointed global modes created by one monodromy increment -/

/-- `sinh a / a`, extended by its removable value `1` at the origin. -/
def sinhDiv (a : ℂ) : ℂ := if a = 0 then 1 else Complex.sinh a / a

@[simp]
theorem sinhDiv_zero : sinhDiv 0 = 1 := by simp [sinhDiv]

theorem sinhDiv_of_ne_zero {a : ℂ} (h : a ≠ 0) : sinhDiv a = Complex.sinh a / a := by
  simp [sinhDiv, h]

/-- Positive monodromy coefficient of a zero of multiplicity `m`. -/
def primeFoldMonodromyCoefficient (m : ℕ) : ℂ := 2 * Real.pi * Complex.I * m

theorem primeFoldMonodromyCoefficient_ne_zero {m : ℕ} (hm : m ≠ 0) :
    primeFoldMonodromyCoefficient m ≠ 0 := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hm' : ((m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hm
  simp [primeFoldMonodromyCoefficient, hpi, hm', Complex.I_ne_zero]

/-- Even global mode created by one monodromy increment. -/
def primeFoldEvenMode (lam : ℂ) (m : ℕ) (L : ℝ) : ℂ :=
  primeFoldMonodromyCoefficient m * Complex.cosh (lam * (L : ℂ))

/-- Odd global mode created by one monodromy increment, with its removable value at `lam = 0`. -/
def primeFoldOddMode (lam : ℂ) (m : ℕ) (L : ℝ) : ℂ :=
  primeFoldMonodromyCoefficient m * ((L : ℂ) * sinhDiv (lam * (L : ℂ)))

theorem primeFoldOddMode_eq_of_ne_zero {lam : ℂ} (hlam : lam ≠ 0) (m : ℕ) (L : ℝ) :
    primeFoldOddMode lam m L =
      primeFoldMonodromyCoefficient m * (Complex.sinh (lam * (L : ℂ)) / lam) := by
  rcases eq_or_ne ((L : ℝ) : ℂ) 0 with hL | hL
  · simp [primeFoldOddMode, hL]
  · have hne : lam * ((L : ℝ) : ℂ) ≠ 0 := mul_ne_zero hlam hL
    rw [primeFoldOddMode, sinhDiv_of_ne_zero hne]
    field_simp

theorem primeFoldOddMode_eq_of_zero (m : ℕ) (L : ℝ) :
    primeFoldOddMode 0 m L = primeFoldMonodromyCoefficient m * (L : ℂ) := by
  simp [primeFoldOddMode]

@[simp]
theorem primeFoldEvenMode_zero (lam : ℂ) (m : ℕ) :
    primeFoldEvenMode lam m 0 = primeFoldMonodromyCoefficient m := by
  simp [primeFoldEvenMode]

@[simp]
theorem primeFoldOddMode_zero (lam : ℂ) (m : ℕ) :
    primeFoldOddMode lam m 0 = 0 := by
  simp [primeFoldOddMode]

theorem primeFoldOddMode_hasDerivAt (lam : ℂ) (m : ℕ) (L : ℝ) :
    HasDerivAt (primeFoldOddMode lam m) (primeFoldEvenMode lam m L) L := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · have hbase : HasDerivAt (fun x : ℝ => primeFoldMonodromyCoefficient m * (x : ℂ))
        (primeFoldMonodromyCoefficient m) L := by
      simpa using ((hasDerivAt_id L).ofReal_comp.const_mul (primeFoldMonodromyCoefficient m))
    have hEq : (fun x : ℝ => primeFoldMonodromyCoefficient m * (x : ℂ)) =
        primeFoldOddMode 0 m := by
      funext x
      rw [primeFoldOddMode_eq_of_zero]
    rw [hEq] at hbase
    simpa [primeFoldEvenMode] using hbase
  · have hlin : HasDerivAt (fun x : ℝ => lam * (x : ℂ)) lam L := by
      simpa [mul_comm] using ((hasDerivAt_id L).ofReal_comp.const_mul lam)
    have hsinh : HasDerivAt (fun x : ℝ => Complex.sinh (lam * (x : ℂ)))
        (Complex.cosh (lam * (L : ℂ)) * lam) L := by
      have h := (Complex.hasDerivAt_sinh (lam * ((L : ℝ) : ℂ))).scomp L hlin
      simpa [Function.comp_def, smul_eq_mul, mul_comm] using h
    have hscaled := (hsinh.div_const lam).const_mul (primeFoldMonodromyCoefficient m)
    have hEq : (fun x : ℝ =>
        primeFoldMonodromyCoefficient m * (Complex.sinh (lam * (x : ℂ)) / lam)) =
        primeFoldOddMode lam m := by
      funext x
      rw [primeFoldOddMode_eq_of_ne_zero hlam]
    rw [hEq] at hscaled
    refine hscaled.congr_deriv ?_
    rw [primeFoldEvenMode]
    field_simp

theorem primeFoldEvenMode_hasDerivAt (lam : ℂ) (m : ℕ) (L : ℝ) :
    HasDerivAt (primeFoldEvenMode lam m) (lam ^ 2 * primeFoldOddMode lam m L) L := by
  have hlin : HasDerivAt (fun x : ℝ => lam * (x : ℂ)) lam L := by
    simpa [mul_comm] using ((hasDerivAt_id L).ofReal_comp.const_mul lam)
  have hcosh : HasDerivAt (fun x : ℝ => Complex.cosh (lam * (x : ℂ)))
      (Complex.sinh (lam * (L : ℂ)) * lam) L := by
    have h := (Complex.hasDerivAt_cosh (lam * ((L : ℝ) : ℂ))).scomp L hlin
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using h
  have hscaled := hcosh.const_mul (primeFoldMonodromyCoefficient m)
  refine hscaled.congr_deriv ?_
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp
  · rw [primeFoldOddMode_eq_of_ne_zero hlam]
    field_simp

/-- The odd monodromy mode solves the homogeneous folded equation `u'' = mu u`, `mu = lam²`. -/
theorem primeFoldOddMode_secondDeriv (lam : ℂ) (m : ℕ) (L : ℝ) :
    deriv (deriv (primeFoldOddMode lam m)) L = lam ^ 2 * primeFoldOddMode lam m L := by
  have h1 : deriv (primeFoldOddMode lam m) = primeFoldEvenMode lam m := by
    funext x
    exact (primeFoldOddMode_hasDerivAt lam m x).deriv
  rw [h1]
  exact (primeFoldEvenMode_hasDerivAt lam m L).deriv

/-- The even monodromy mode solves the same homogeneous folded equation. -/
theorem primeFoldEvenMode_secondDeriv (lam : ℂ) (m : ℕ) (L : ℝ) :
    deriv (deriv (primeFoldEvenMode lam m)) L = lam ^ 2 * primeFoldEvenMode lam m L := by
  have h1 : deriv (primeFoldEvenMode lam m) =
      fun x : ℝ => lam ^ 2 * primeFoldOddMode lam m x := by
    funext x
    exact (primeFoldEvenMode_hasDerivAt lam m x).deriv
  rw [h1]
  have h2 : HasDerivAt (fun x : ℝ => lam ^ 2 * primeFoldOddMode lam m x)
      (lam ^ 2 * primeFoldEvenMode lam m L) L :=
    (primeFoldOddMode_hasDerivAt lam m L).const_mul (lam ^ 2)
  exact h2.deriv

/-- Neumann datum of the even mode vanishes; its Dirichlet datum is the exact multiplicity. -/
theorem primeFoldEvenMode_hasDerivAt_zero (lam : ℂ) (m : ℕ) :
    HasDerivAt (primeFoldEvenMode lam m) 0 0 := by
  simpa using primeFoldEvenMode_hasDerivAt lam m 0

/-- Neumann datum of the odd mode is the exact multiplicity; its Dirichlet datum vanishes. -/
theorem primeFoldOddMode_hasDerivAt_zero (lam : ℂ) (m : ℕ) :
    HasDerivAt (primeFoldOddMode lam m) (primeFoldMonodromyCoefficient m) 0 := by
  simpa using primeFoldOddMode_hasDerivAt lam m 0

theorem primeFoldEvenMode_ne_zero {m : ℕ} (hm : m ≠ 0) (lam : ℂ) :
    primeFoldEvenMode lam m ≠ 0 := by
  intro h
  have hval := congrFun h 0
  rw [primeFoldEvenMode_zero] at hval
  exact primeFoldMonodromyCoefficient_ne_zero hm hval

theorem primeFoldOddMode_ne_zero {m : ℕ} (hm : m ≠ 0) (lam : ℂ) :
    primeFoldOddMode lam m ≠ 0 := by
  intro h
  have hd : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (primeFoldMonodromyCoefficient m) 0 := by
    rw [show (fun _ : ℝ => (0 : ℂ)) = primeFoldOddMode lam m from h.symm]
    exact primeFoldOddMode_hasDerivAt_zero lam m
  have hval := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  exact primeFoldMonodromyCoefficient_ne_zero hm hval

/-! ## Monodromy increments of the folds -/

/-- The even fold of a monodromy increment is exactly the even global mode. -/
theorem primeFoldEven_monodromy (P : ℂ → ℂ) (m : ℕ) (lam : ℂ) (L : ℝ) :
    primeFoldEven (fun w => P w + primeFoldMonodromyCoefficient m) lam L -
        primeFoldEven P lam L =
      primeFoldEvenMode lam m L := by
  have h1 := primeFoldBranch_add_const P (primeFoldMonodromyCoefficient m) lam L
  have h2 := primeFoldBranch_add_const P (primeFoldMonodromyCoefficient m) (-lam) L
  have hcosh : Complex.cosh (lam * (L : ℂ)) =
      (Complex.exp (lam * (L : ℂ)) + Complex.exp (-lam * (L : ℂ))) / 2 := by
    rw [Complex.cosh]
    ring_nf
  rw [primeFoldEven, primeFoldEven, primeFoldEvenMode, hcosh,
    show (primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) lam L +
      primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) (-lam) L) / 2 -
      (primeFoldBranch P lam L + primeFoldBranch P (-lam) L) / 2 =
      ((primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) lam L -
        primeFoldBranch P lam L) +
       (primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) (-lam) L -
        primeFoldBranch P (-lam) L)) / 2 from by ring, h1, h2]
  ring

/-- The odd fold of a monodromy increment is exactly the odd global mode. -/
theorem primeFoldOdd_monodromy (P : ℂ → ℂ) (m : ℕ) {lam : ℂ} (hlam : lam ≠ 0) (L : ℝ) :
    primeFoldOdd (fun w => P w + primeFoldMonodromyCoefficient m) lam L -
        primeFoldOdd P lam L =
      primeFoldOddMode lam m L := by
  have h1 := primeFoldBranch_add_const P (primeFoldMonodromyCoefficient m) lam L
  have h2 := primeFoldBranch_add_const P (primeFoldMonodromyCoefficient m) (-lam) L
  have hsinh : Complex.sinh (lam * (L : ℂ)) =
      (Complex.exp (lam * (L : ℂ)) - Complex.exp (-lam * (L : ℂ))) / 2 := by
    rw [Complex.sinh]
    ring_nf
  rw [primeFoldOdd, primeFoldOdd, primeFoldOddMode_eq_of_ne_zero hlam, hsinh,
    show (primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) lam L -
      primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) (-lam) L) / (2 * lam) -
      (primeFoldBranch P lam L - primeFoldBranch P (-lam) L) / (2 * lam) =
      ((primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) lam L -
        primeFoldBranch P lam L) -
       (primeFoldBranch (fun w => P w + primeFoldMonodromyCoefficient m) (-lam) L -
        primeFoldBranch P (-lam) L)) / (2 * lam) from by ring, h1, h2]
  field_simp

/-! ## The folded spectral parameter -/

/-- Folded spectral parameter of a point of the critical strip. -/
def primeFoldMu (ρ : ℂ) : ℂ := (ρ - 1 / 2) ^ 2

/-- Functional-equation partners define the same folded parameter: reflection is internal. -/
theorem primeFoldMu_functional_equation (ρ : ℂ) :
    primeFoldMu (1 - ρ) = primeFoldMu ρ := by
  rw [primeFoldMu, primeFoldMu]
  ring

/-- Complex conjugation acts on the folded parameter by conjugation. -/
theorem primeFoldMu_conj (ρ : ℂ) :
    primeFoldMu (starRingEnd ℂ ρ) = starRingEnd ℂ (primeFoldMu ρ) := by
  have h : starRingEnd ℂ (ρ - 1 / 2) = starRingEnd ℂ ρ - 1 / 2 := by
    simp [Complex.ext_iff]
  rw [primeFoldMu, primeFoldMu, ← h, ← map_pow]

/-- **Reality consumer.**  A nonreal point whose folded parameter is real lies on the critical
line. -/
theorem re_eq_half_of_primeFoldMu_real {ρ : ℂ}
    (him : ρ.im ≠ 0) (hmu : (primeFoldMu ρ).im = 0) : ρ.re = 1 / 2 := by
  have hcast : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hexp : (primeFoldMu ρ).im = 2 * (ρ.re - 1 / 2) * ρ.im := by
    rw [primeFoldMu, hcast, pow_two, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hexp] at hmu
  have h2 : ρ.re - 1 / 2 = 0 := by
    rcases mul_eq_zero.mp hmu with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    · exact absurd h him
  linarith

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions ENNReal

/-! ## The transport law as an identity of positive-time distributions -/

theorem primeFoldBranch_locallyIntegrableOn (P : ℂ → ℂ) (lam : ℂ) :
    LocallyIntegrableOn (primeFoldBranch P lam) (Ioi 0) volume := by
  classical
  rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K _hKsub hK
  obtain ⟨B, hB⟩ := bddAbove_def.mp hK.bddAbove
  have hhom : IntegrableOn (fun L : ℝ => Complex.exp (lam * (L : ℂ)) * P lam) K volume :=
    ContinuousOn.integrableOn_compact hK (by fun_prop)
  have hatom : ∀ n : DeningerPrimePowerIndex,
      IntegrableOn (primeFoldCausalAtom lam n) K volume := by
    intro n
    have hcont : IntegrableOn (fun L : ℝ => (criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (lam * ((L - deningerPrimePowerTime n : ℝ) : ℂ))) K volume :=
      ContinuousOn.integrableOn_compact hK (by fun_prop)
    rw [primeFoldCausalAtom_eq_indicator]
    exact hcont.indicator measurableSet_Ioi
  have hsum : IntegrableOn
      (fun L : ℝ => ∑ n ∈ primeFoldBelowFinset B, primeFoldCausalAtom lam n L) K volume :=
    integrable_finsetSum _ fun n _ => hatom n
  refine (hhom.sub hsum).congr_fun ?_ hK.measurableSet
  intro L hLK
  simp only [Pi.sub_apply]
  rw [primeFoldBranch, primeFoldCausalTail_eq_sum lam (hB L hLK)]

/-- Regular distribution carried by a completed prime-tail branch on positive time. -/
def primeFoldBranchDistribution (P : ℂ → ℂ) (lam : ℂ) : DeningerTimeDistribution :=
  deningerRegularTimeDistribution (primeFoldBranch P lam)

@[simp]
theorem primeFoldBranchDistribution_apply (P : ℂ → ℂ) (lam : ℂ)
    (φ : DeningerTimeTestFunction) :
    primeFoldBranchDistribution P lam φ =
      ∫ L : ℝ, (φ L : ℂ) * primeFoldBranch P lam L :=
  deningerRegularTimeDistribution_apply (primeFoldBranch_locallyIntegrableOn P lam) φ

theorem deningerTimeDistributionDeriv_apply
    (T : DeningerTimeDistribution) (φ : DeningerTimeTestFunction) :
    deningerTimeDistributionDeriv T φ = -T (deningerTimeTestDerivative φ) := by
  rw [deningerTimeDistributionDeriv, Distribution.lineDerivCLM_apply]
  rfl

theorem contDiff_ofReal_testFunction (φ : DeningerTimeTestFunction) (k : ℕ) :
    ContDiff ℝ k (fun x : ℝ => (φ x : ℂ)) := by
  simpa [Function.comp_def] using
    (Complex.ofRealCLM.contDiff.comp (φ.contDiff.of_le (by exact_mod_cast le_top)))

theorem hasCompactSupport_ofReal_testFunction (φ : DeningerTimeTestFunction) :
    HasCompactSupport (fun x : ℝ => (φ x : ℂ)) := by
  simpa only [Function.comp_apply] using!
    (φ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl)

theorem continuous_ofReal_testFunction (φ : DeningerTimeTestFunction) :
    Continuous (fun x : ℝ => (φ x : ℂ)) :=
  Complex.continuous_ofReal.comp φ.continuous

theorem deriv_ofReal_testFunction (φ : DeningerTimeTestFunction) :
    deriv (fun x : ℝ => (φ x : ℂ)) =
      fun L : ℝ => ((deningerTimeTestDerivative φ L : ℝ) : ℂ) := by
  funext L
  have hφ : HasDerivAt (fun x : ℝ => φ x) (deriv (fun x : ℝ => φ x) L) L :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
  rw [hφ.ofReal_comp.deriv, deningerTimeTestDerivative_apply_eq_deriv]

theorem integral_ofReal_test_mul_primeFoldBranch_add
    (P : ℂ → ℂ) (lam : ℂ) (φ : DeningerTimeTestFunction) :
    (∫ L : ℝ, (((deningerTimeTestDerivative φ L : ℝ) : ℂ) + lam * (φ L : ℂ)) *
        primeFoldBranch P lam L) =
      (∫ L : ℝ, ((deningerTimeTestDerivative φ L : ℝ) : ℂ) * primeFoldBranch P lam L) +
        lam * ∫ L : ℝ, (φ L : ℂ) * primeFoldBranch P lam L := by
  have hd1 : Integrable (fun L : ℝ =>
      ((deningerTimeTestDerivative φ L : ℝ) : ℂ) * primeFoldBranch P lam L) :=
    integrable_mul_primeFoldBranch P lam
      (continuous_ofReal_testFunction (deningerTimeTestDerivative φ))
      (hasCompactSupport_ofReal_testFunction (deningerTimeTestDerivative φ))
  have hd2 : Integrable (fun L : ℝ => (lam * (φ L : ℂ)) * primeFoldBranch P lam L) :=
    integrable_mul_primeFoldBranch P lam
      (continuous_const.mul (continuous_ofReal_testFunction φ))
      (hasCompactSupport_ofReal_testFunction φ).mul_left
  rw [show (fun L : ℝ => (((deningerTimeTestDerivative φ L : ℝ) : ℂ) + lam * (φ L : ℂ)) *
      primeFoldBranch P lam L) =
      fun L : ℝ => ((deningerTimeTestDerivative φ L : ℝ) : ℂ) * primeFoldBranch P lam L +
        (lam * (φ L : ℂ)) * primeFoldBranch P lam L from by funext L; ring,
    integral_add hd1 hd2]
  congr 1
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun L => by ring))

/-- **Equation (6).**  On positive time the completed prime-tail branch transports the literal
ordinary-integer forcing measure, for every homogeneous datum and every folded parameter. -/
theorem primeFoldBranch_transport_distribution (P : ℂ → ℂ) (lam : ℂ) :
    deningerTimeDistributionDeriv (primeFoldBranchDistribution P lam) -
        lam • primeFoldBranchDistribution P lam =
      -criticalPrimeTailForcingDistribution := by
  ext φ
  have hmain := integral_primeFoldBranch_transport P lam
    (contDiff_ofReal_testFunction φ 1) (hasCompactSupport_ofReal_testFunction φ)
  rw [deriv_ofReal_testFunction φ, integral_ofReal_test_mul_primeFoldBranch_add P lam φ] at hmain
  have hderiv : deningerTimeDistributionDeriv (primeFoldBranchDistribution P lam) φ =
      -∫ L : ℝ, ((deningerTimeTestDerivative φ L : ℝ) : ℂ) * primeFoldBranch P lam L := by
    rw [deningerTimeDistributionDeriv_apply, primeFoldBranchDistribution_apply]
  have hsmul : (lam • primeFoldBranchDistribution P lam) φ =
      lam * ∫ L : ℝ, (φ L : ℂ) * primeFoldBranch P lam L := by
    rw [smul_apply, primeFoldBranchDistribution_apply, smul_eq_mul]
  rw [sub_apply, hderiv, hsmul, neg_apply,
    criticalPrimeTailForcingDistribution_apply]
  rw [show primeFoldForcing (fun x : ℝ => (φ x : ℂ)) =
      ∑' n : DeningerPrimePowerIndex,
        (criticalPrimeTailAtomWeight n : ℂ) * (φ (deningerPrimePowerTime n) : ℂ) from rfl] at hmain
  linear_combination -hmain

/-! ## The folded distributions -/

/-- Even reflection fold at the level of positive-time distributions. -/
def primeFoldEvenDistribution (P : ℂ → ℂ) (lam : ℂ) : DeningerTimeDistribution :=
  (2 : ℂ)⁻¹ • (primeFoldBranchDistribution P lam + primeFoldBranchDistribution P (-lam))

/-- Odd reflection fold at the level of positive-time distributions. -/
def primeFoldOddDistribution (P : ℂ → ℂ) (lam : ℂ) : DeningerTimeDistribution :=
  (2 * lam)⁻¹ • (primeFoldBranchDistribution P lam - primeFoldBranchDistribution P (-lam))

theorem primeFoldEvenDistribution_apply (P : ℂ → ℂ) (lam : ℂ)
    (φ : DeningerTimeTestFunction) :
    primeFoldEvenDistribution P lam φ =
      ∫ L : ℝ, (φ L : ℂ) * primeFoldEven P lam L := by
  have hu : Integrable (fun L : ℝ => (φ L : ℂ) * primeFoldBranch P lam L) :=
    integrable_mul_primeFoldBranch P lam
      (continuous_ofReal_testFunction φ) (hasCompactSupport_ofReal_testFunction φ)
  have hv : Integrable (fun L : ℝ => (φ L : ℂ) * primeFoldBranch P (-lam) L) :=
    integrable_mul_primeFoldBranch P (-lam)
      (continuous_ofReal_testFunction φ) (hasCompactSupport_ofReal_testFunction φ)
  rw [primeFoldEvenDistribution, smul_apply,
    add_apply, primeFoldBranchDistribution_apply,
    primeFoldBranchDistribution_apply, smul_eq_mul]
  rw [show (fun L : ℝ => (φ L : ℂ) * primeFoldEven P lam L) =
      fun L : ℝ => ((φ L : ℂ) * primeFoldBranch P lam L +
        (φ L : ℂ) * primeFoldBranch P (-lam) L) / 2 from by
    funext L; rw [primeFoldEven]; ring]
  rw [integral_div, integral_add hu hv]
  ring

theorem primeFoldOddDistribution_apply (P : ℂ → ℂ) (lam : ℂ)
    (φ : DeningerTimeTestFunction) :
    primeFoldOddDistribution P lam φ =
      ∫ L : ℝ, (φ L : ℂ) * primeFoldOdd P lam L := by
  have hu : Integrable (fun L : ℝ => (φ L : ℂ) * primeFoldBranch P lam L) :=
    integrable_mul_primeFoldBranch P lam
      (continuous_ofReal_testFunction φ) (hasCompactSupport_ofReal_testFunction φ)
  have hv : Integrable (fun L : ℝ => (φ L : ℂ) * primeFoldBranch P (-lam) L) :=
    integrable_mul_primeFoldBranch P (-lam)
      (continuous_ofReal_testFunction φ) (hasCompactSupport_ofReal_testFunction φ)
  rw [primeFoldOddDistribution, smul_apply,
    sub_apply, primeFoldBranchDistribution_apply,
    primeFoldBranchDistribution_apply, smul_eq_mul]
  rw [show (fun L : ℝ => (φ L : ℂ) * primeFoldOdd P lam L) =
      fun L : ℝ => ((φ L : ℂ) * primeFoldBranch P lam L -
        (φ L : ℂ) * primeFoldBranch P (-lam) L) / (2 * lam) from by
    funext L; rw [primeFoldOdd]; ring]
  rw [integral_div, integral_sub hu hv]
  ring

theorem deriv_deriv_ofReal_testFunction (φ : DeningerTimeTestFunction) :
    deriv (deriv (fun x : ℝ => (φ x : ℂ))) =
      fun L : ℝ =>
        ((deningerTimeTestDerivative (deningerTimeTestDerivative φ) L : ℝ) : ℂ) := by
  rw [deriv_ofReal_testFunction φ]
  exact deriv_ofReal_testFunction (deningerTimeTestDerivative φ)

theorem secondOrder_pairing_apply
    (T : DeningerTimeDistribution) (lam : ℂ) (φ : DeningerTimeTestFunction) :
    (deningerTimeDistributionDeriv (deningerTimeDistributionDeriv T) -
        (lam ^ 2) • T) φ =
      T (deningerTimeTestDerivative (deningerTimeTestDerivative φ)) - lam ^ 2 * T φ := by
  rw [sub_apply, deningerTimeDistributionDeriv_apply,
    deningerTimeDistributionDeriv_apply, smul_apply, smul_eq_mul]
  ring

/-- Pairings of a compactly supported continuous function with the folds are integrable. -/
theorem integrable_mul_primeFoldOdd (P : ℂ → ℂ) (lam : ℂ) {g : ℝ → ℂ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun L : ℝ => g L * primeFoldOdd P lam L) := by
  have hb := (integrable_mul_primeFoldBranch P lam hgc hgs).sub
    (integrable_mul_primeFoldBranch P (-lam) hgc hgs)
  refine (hb.div_const (2 * lam)).congr ?_
  filter_upwards [] with L
  simp only [Pi.sub_apply]
  rw [primeFoldOdd]
  ring

theorem integrable_mul_primeFoldEven (P : ℂ → ℂ) (lam : ℂ) {g : ℝ → ℂ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    Integrable (fun L : ℝ => g L * primeFoldEven P lam L) := by
  have hb := (integrable_mul_primeFoldBranch P lam hgc hgs).add
    (integrable_mul_primeFoldBranch P (-lam) hgc hgs)
  refine (hb.div_const 2).congr ?_
  filter_upwards [] with L
  simp only [Pi.add_apply]
  rw [primeFoldEven]
  ring

/-- Splitting the second-order symbol pairing against an arbitrary positive-time function. -/
theorem integral_secondOrderSymbol_split
    {u : ℝ → ℂ} (lam : ℂ) (φ : DeningerTimeTestFunction)
    (h1 : Integrable (fun L : ℝ =>
      ((deningerTimeTestDerivative (deningerTimeTestDerivative φ) L : ℝ) : ℂ) * u L))
    (h2 : Integrable (fun L : ℝ => (lam ^ 2 * (φ L : ℂ)) * u L)) :
    (∫ L : ℝ,
        (((deningerTimeTestDerivative (deningerTimeTestDerivative φ) L : ℝ) : ℂ) -
          lam ^ 2 * (φ L : ℂ)) * u L) =
      (∫ L : ℝ,
        ((deningerTimeTestDerivative (deningerTimeTestDerivative φ) L : ℝ) : ℂ) * u L) -
        lam ^ 2 * ∫ L : ℝ, (φ L : ℂ) * u L := by
  rw [show (fun L : ℝ =>
      (((deningerTimeTestDerivative (deningerTimeTestDerivative φ) L : ℝ) : ℂ) -
        lam ^ 2 * (φ L : ℂ)) * u L) =
      fun L : ℝ =>
        ((deningerTimeTestDerivative (deningerTimeTestDerivative φ) L : ℝ) : ℂ) * u L -
          (lam ^ 2 * (φ L : ℂ)) * u L from by funext L; ring,
    integral_sub h1 h2]
  congr 1
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun L => by ring))

/-- **Theorem 1, odd part.**  The divided difference of the two reflected branches obeys the
parameter-independent second-order equation `(∂_L² - lam²) S_lam = -Π₀`. -/
theorem primeFoldOdd_secondOrder_distribution
    (P : ℂ → ℂ) {lam : ℂ} (hlam : lam ≠ 0) :
    deningerTimeDistributionDeriv
        (deningerTimeDistributionDeriv (primeFoldOddDistribution P lam)) -
        (lam ^ 2) • primeFoldOddDistribution P lam =
      -criticalPrimeTailForcingDistribution := by
  ext φ
  have hsq : Continuous (fun L : ℝ => lam ^ 2 * (φ L : ℂ)) :=
    continuous_const.mul (continuous_ofReal_testFunction φ)
  have hsqSupp : HasCompactSupport (fun L : ℝ => lam ^ 2 * (φ L : ℂ)) :=
    (hasCompactSupport_ofReal_testFunction φ).mul_left
  have hmain := integral_primeFoldOdd_secondOrder P hlam
    (contDiff_ofReal_testFunction φ 2) (hasCompactSupport_ofReal_testFunction φ)
  rw [deriv_deriv_ofReal_testFunction φ,
    integral_secondOrderSymbol_split lam φ
      (integrable_mul_primeFoldOdd P lam
        (continuous_ofReal_testFunction
          (deningerTimeTestDerivative (deningerTimeTestDerivative φ)))
        (hasCompactSupport_ofReal_testFunction
          (deningerTimeTestDerivative (deningerTimeTestDerivative φ))))
      (integrable_mul_primeFoldOdd P lam hsq hsqSupp),
    ← primeFoldOddDistribution_apply, ← primeFoldOddDistribution_apply] at hmain
  rw [secondOrder_pairing_apply, neg_apply, criticalPrimeTailForcingDistribution_apply]
  rw [show primeFoldForcing (fun x : ℝ => (φ x : ℂ)) =
      ∑' n : DeningerPrimePowerIndex,
        (criticalPrimeTailAtomWeight n : ℂ) * (φ (deningerPrimePowerTime n) : ℂ) from rfl] at hmain
  exact hmain

/-- **Theorem 1, even part.**  The half-sum of the two reflected branches obeys
`(∂_L² - lam²) C_lam = -∂_L Π₀`. -/
theorem primeFoldEven_secondOrder_distribution (P : ℂ → ℂ) (lam : ℂ) :
    deningerTimeDistributionDeriv
        (deningerTimeDistributionDeriv (primeFoldEvenDistribution P lam)) -
        (lam ^ 2) • primeFoldEvenDistribution P lam =
      -deningerTimeDistributionDeriv criticalPrimeTailForcingDistribution := by
  ext φ
  have hsq : Continuous (fun L : ℝ => lam ^ 2 * (φ L : ℂ)) :=
    continuous_const.mul (continuous_ofReal_testFunction φ)
  have hsqSupp : HasCompactSupport (fun L : ℝ => lam ^ 2 * (φ L : ℂ)) :=
    (hasCompactSupport_ofReal_testFunction φ).mul_left
  have hmain := integral_primeFoldEven_secondOrder P lam
    (contDiff_ofReal_testFunction φ 2) (hasCompactSupport_ofReal_testFunction φ)
  rw [deriv_deriv_ofReal_testFunction φ, deriv_ofReal_testFunction φ,
    integral_secondOrderSymbol_split lam φ
      (integrable_mul_primeFoldEven P lam
        (continuous_ofReal_testFunction
          (deningerTimeTestDerivative (deningerTimeTestDerivative φ)))
        (hasCompactSupport_ofReal_testFunction
          (deningerTimeTestDerivative (deningerTimeTestDerivative φ))))
      (integrable_mul_primeFoldEven P lam hsq hsqSupp),
    ← primeFoldEvenDistribution_apply, ← primeFoldEvenDistribution_apply] at hmain
  rw [secondOrder_pairing_apply, neg_apply, deningerTimeDistributionDeriv_apply,
    criticalPrimeTailForcingDistribution_apply]
  rw [show primeFoldForcing
      (fun x : ℝ => ((deningerTimeTestDerivative φ x : ℝ) : ℂ)) =
      ∑' n : DeningerPrimePowerIndex,
        (criticalPrimeTailAtomWeight n : ℂ) *
          (deningerTimeTestDerivative φ (deningerPrimePowerTime n) : ℂ) from rfl] at hmain
  rw [hmain]
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions ENNReal

/-! ## Reflection invariance of the folded modes -/

/-- The even global mode depends on the folded parameter only through `mu = lam²`. -/
theorem primeFoldEvenMode_neg (lam : ℂ) (m : ℕ) :
    primeFoldEvenMode (-lam) m = primeFoldEvenMode lam m := by
  funext L
  rw [primeFoldEvenMode, primeFoldEvenMode, show (-lam) * (L : ℂ) = -(lam * (L : ℂ)) from by ring,
    Complex.cosh_neg]

/-- The odd global mode depends on the folded parameter only through `mu = lam²`. -/
theorem primeFoldOddMode_neg (lam : ℂ) (m : ℕ) :
    primeFoldOddMode (-lam) m = primeFoldOddMode lam m := by
  funext L
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp
  · rw [primeFoldOddMode_eq_of_ne_zero hlam, primeFoldOddMode_eq_of_ne_zero (neg_ne_zero.mpr hlam),
      show (-lam) * (L : ℂ) = -(lam * (L : ℂ)) from by ring, Complex.sinh_neg]
    field_simp

/-! ## The Xi monodromy datum -/

theorem continuous_xi : Continuous xi :=
  continuous_iff_continuousAt.mpr fun s => (xi_analyticOnNhd_univ s (Set.mem_univ s)).continuousAt

/-- Small circles about any point are nonvanishing `Xi`-loops. -/
theorem xi_circle_isLoop (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      IsLoop (fun θ : ℝ => xi (ρ₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        0 (2 * Real.pi) := by
  obtain ⟨R₀, hR₀, h, _hha, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, fun r hr hrR => ?_⟩
  have hmem : ∀ θ : ℝ, ρ₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈ Metric.ball ρ₀ R₀ := by
    intro θ
    have hnorm : ‖(r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        Complex.norm_exp]
      simp
    simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left, hnorm]
    exact hrR
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_xi.comp (by fun_prop)
  · intro θ
    rw [hfact _ (hmem θ)]
    refine mul_ne_zero (pow_ne_zero _ ?_) (hh0 _ (hmem θ))
    have hne : ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast ne_of_gt hr) (Complex.exp_ne_zero _)
    simpa using hne
  · have h0 : Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) = 1 := by simp
    have h2π : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I from by
        push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    rw [h0, h2π]

/-- **Equation (15).**  Any continuous logarithm of `Xi` along a small circle about a point
increases by exactly `2πi` times the vanishing order there. -/
theorem xi_logBranch_increment (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      ∀ Q : ℝ → ℂ, Continuous Q →
        (∀ θ : ℝ, Complex.exp (Q θ) =
          xi (ρ₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) →
        Q (2 * Real.pi) - Q 0 =
          primeFoldMonodromyCoefficient (analyticOrderAt xi ρ₀).toNat := by
  obtain ⟨R₁, hR₁, hloop⟩ := xi_circle_isLoop ρ₀
  obtain ⟨R₂, hR₂, hwind⟩ := windingNumber_xi_zero ρ₀
  refine ⟨min R₁ R₂, lt_min hR₁ hR₂, fun r hr hrR Q hQc hQe => ?_⟩
  have hr1 : r < R₁ := lt_of_lt_of_le hrR (min_le_left _ _)
  have hr2 : r < R₂ := lt_of_lt_of_le hrR (min_le_right _ _)
  have hincr := contLog_increment (hloop r hr hr1) hQc hQe
  rw [hwind r hr hr2] at hincr
  rw [hincr, primeFoldMonodromyCoefficient]
  push_cast
  ring

/-- **Equations (16)–(17), even part.**  Continuing the homogeneous datum once around a `Xi` zero
changes the even fold by exactly the even global mode of `mu = lam²`, with the multiplicity as
its exact coefficient. -/
theorem primeFoldEven_xi_monodromy (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      ∀ Q : ℝ → ℂ, Continuous Q →
        (∀ θ : ℝ, Complex.exp (Q θ) =
          xi (ρ₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) →
        ∀ (P : ℂ → ℂ) (lam : ℂ) (L : ℝ),
          primeFoldEven (fun w => P w + (Q (2 * Real.pi) - Q 0)) lam L -
              primeFoldEven P lam L =
            primeFoldEvenMode lam (analyticOrderAt xi ρ₀).toNat L := by
  obtain ⟨R₀, hR₀, hincr⟩ := xi_logBranch_increment ρ₀
  refine ⟨R₀, hR₀, fun r hr hrR Q hQc hQe P lam L => ?_⟩
  rw [hincr r hr hrR Q hQc hQe]
  exact primeFoldEven_monodromy P _ lam L

/-- **Equations (16)–(17), odd part.** -/
theorem primeFoldOdd_xi_monodromy (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      ∀ Q : ℝ → ℂ, Continuous Q →
        (∀ θ : ℝ, Complex.exp (Q θ) =
          xi (ρ₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) →
        ∀ (P : ℂ → ℂ) {lam : ℂ}, lam ≠ 0 → ∀ L : ℝ,
          primeFoldOdd (fun w => P w + (Q (2 * Real.pi) - Q 0)) lam L -
              primeFoldOdd P lam L =
            primeFoldOddMode lam (analyticOrderAt xi ρ₀).toNat L := by
  obtain ⟨R₀, hR₀, hincr⟩ := xi_logBranch_increment ρ₀
  refine ⟨R₀, hR₀, fun r hr hrR Q hQc hQe P lam hlam L => ?_⟩
  rw [hincr r hr hrR Q hQc hQe]
  exact primeFoldOdd_monodromy P _ hlam L

end

end RHTower
