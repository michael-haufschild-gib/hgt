import GaloisForLFunctions.RHTower.AnderssonTheoremOne
import GaloisForLFunctions.HTGeometry.HelsonCharacterLSeries
import GaloisForLFunctions.HTGeometry.HelsonPrescribedDivisor
import GaloisForLFunctions.HTGeometry.AnderssonLemmaOne
import GaloisForLFunctions.HTGeometry.WeierstrassProductMultiplicity

/-!
# Andersson's Theorem 2 and the divisor surjectivity of the Helson stratum

A function analytic and zero free on the closed half plane whose logarithmic derivative has a
Mellin representation with a vanishing bounded datum is a Helson zeta function times an entire
zero-free function.  The character comes from Theorem 1, the entire factor from an entire primitive
of the leftover, and the identification of the two logarithmic derivatives from the Euler product.
-/

noncomputable section

open MeasureTheory Filter Set Complex GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **Andersson's Theorem 2** for a function whose logarithmic derivative is a Mellin transform of
a bounded vanishing datum plus an entire function. -/
theorem helson_factorization_of_mellin_logDeriv {F : ℂ → ℂ}
    (hFan : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ F z) (hFne : ∀ z : ℂ, 1 ≤ z.re → F z ≠ 0)
    {q : ℝ → ℂ} {g₁ : ℂ → ℂ} (hg₁ : Differentiable ℂ g₁)
    (hqmeas : AEStronglyMeasurable q (volume.restrict (Set.Ioi (1:ℝ))))
    (hq0 : Tendsto q atTop (nhds 0)) {M : ℝ} (hqb : ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M)
    (hrep : ∀ s : ℂ, 1 < s.re →
      logDeriv F s = (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) + g₁ s) :
    ∃ (χ : PhaseTorus) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ z : ℂ, g z ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → F s = helsonZetaValue s χ * g s := by
  classical
  -- the character, from Theorem 1 applied to the negated datum
  have hnegmeas : AEStronglyMeasurable (fun x => -q x) (volume.restrict (Set.Ioi (1:ℝ))) :=
    hqmeas.neg
  have hneg0 : Tendsto (fun x => -q x) atTop (nhds 0) := by
    have := hq0.neg
    rw [neg_zero] at this
    exact this
  have hnegb : ∀ x : ℝ, 1 ≤ x → ‖-q x‖ ≤ M := by
    intro x hx
    rw [norm_neg]
    exact hqb x hx
  obtain ⟨u, g₀, hu1, hg₀, hthm1⟩ :=
    exists_character_entire_remainder (α := (8:ℝ)/10) (θ := (9:ℝ)/10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hnegmeas hneg0 hnegb
  set A₀ : ℝ := anderssonAbscissa ((9:ℝ)/10) 0 with hA₀def
  have hA₀ : A₀ = ((9:ℝ)/10 + (1 - (9:ℝ)/10) / 3) + 2 * ((9:ℝ)/10) := by
    rw [hA₀def, anderssonAbscissa_zero]
  have hA₀gt : 2 < A₀ := by
    rw [hA₀]
    norm_num
  -- the phase torus point
  set χ : PhaseTorus := fun p => ⟨u (p : ℕ), hu1 (p : ℕ)⟩ with hχdef
  have hχ : ∀ p : Nat.Primes, ((χ p : ℂ)) = u (p : ℕ) := fun p => rfl
  have hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1 := fun p _ => hu1 p
  -- the leftover entire function
  set G : ℂ → ℂ := fun z => g₁ z - g₀ z with hGdef
  have hGdiff : Differentiable ℂ G := hg₁.sub hg₀
  have hkey : ∀ s : ℂ, A₀ < s.re →
      logDeriv F s = logDeriv (fun z => helsonZetaValue z χ) s + G s := by
    intro s hs
    have hs1 : 1 < s.re := by linarith
    have hz := logDeriv_helsonZetaValue hu hχ hs1
    have hneg : (∫ x in Set.Ioi (1:ℝ), (-q x) * (x : ℂ) ^ (-s))
        = -(∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) := by
      rw [← MeasureTheory.integral_neg]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      ring
    have h1 := hthm1 s hs
    rw [hneg] at h1
    rw [hrep s hs1, hz, hGdef]
    have h2 : (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s))
        = -(LSeries (characterSource u) s + g₀ s) := by
      linear_combination -h1
    rw [h2]
    ring
  -- an entire primitive of the leftover
  obtain ⟨H, hH⟩ := hGdiff.isExactOn_univ
  have hHderiv : ∀ z : ℂ, HasDerivAt H (G z) z := fun z => hH z (Set.mem_univ z)
  have hHdiff : Differentiable ℂ H := fun z => (hHderiv z).differentiableAt
  -- the ratio is constant on the half plane
  set Ω : Set ℂ := {z : ℂ | A₀ < z.re} with hΩdef
  have hΩopen : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_re
  have hΩconv : Convex ℝ Ω := by
    refine convex_halfSpace_gt ?_ A₀
    exact { map_add := fun x y => Complex.add_re x y, map_smul := fun c x => by simp }
  set Φ : ℂ → ℂ := fun z => F z / (helsonZetaValue z χ * Complex.exp (H z)) with hΦdef
  have hZdiff : ∀ z ∈ Ω, DifferentiableAt ℂ (fun w => helsonZetaValue w χ) z := by
    intro z hz
    have hz1 : 1 < z.re := lt_trans (by linarith [hA₀gt] : (1:ℝ) < A₀) hz
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    exact (differentiableOn_helsonZetaValue χ).differentiableAt (hopen.mem_nhds hz1)
  have hZne : ∀ z ∈ Ω, helsonZetaValue z χ ≠ 0 := by
    intro z hz
    have hz1 : 1 < z.re := lt_trans (by linarith [hA₀gt] : (1:ℝ) < A₀) hz
    exact helsonZetaValue_ne_zero hz1 χ
  have hFdiff : ∀ z ∈ Ω, DifferentiableAt ℂ F z := by
    intro z hz
    have hz1 : (1:ℝ) ≤ z.re := le_of_lt (lt_trans (by linarith [hA₀gt] : (1:ℝ) < A₀) hz)
    exact (hFan z hz1).differentiableAt
  have hFne' : ∀ z ∈ Ω, F z ≠ 0 := by
    intro z hz
    have hz1 : (1:ℝ) ≤ z.re := le_of_lt (lt_trans (by linarith [hA₀gt] : (1:ℝ) < A₀) hz)
    exact hFne z hz1
  have hEdiff : ∀ z : ℂ, DifferentiableAt ℂ (fun w => Complex.exp (H w)) z := fun z =>
    (Complex.differentiable_exp.differentiableAt).comp z (hHdiff z)
  have hlogE : ∀ z : ℂ, logDeriv (fun w => Complex.exp (H w)) z = G z := by
    intro z
    rw [logDeriv_apply, deriv_cexp (hHdiff z), (hHderiv z).deriv]
    field_simp
  have hΦderiv : ∀ z ∈ Ω, deriv Φ z = 0 := by
    intro z hz
    have hZ := hZne z hz
    have hE : Complex.exp (H z) ≠ 0 := Complex.exp_ne_zero _
    have hden : helsonZetaValue z χ * Complex.exp (H z) ≠ 0 := mul_ne_zero hZ hE
    have hdivlem : logDeriv (fun w => F w / (helsonZetaValue w χ * Complex.exp (H w))) z
        = logDeriv F z - logDeriv (fun w => helsonZetaValue w χ * Complex.exp (H w)) z :=
      logDeriv_div z (hFne' z hz) hden (hFdiff z hz) ((hZdiff z hz).mul (hEdiff z))
    have hmullem : logDeriv (fun w => helsonZetaValue w χ * Complex.exp (H w)) z
        = logDeriv (fun w => helsonZetaValue w χ) z + logDeriv (fun w => Complex.exp (H w)) z :=
      logDeriv_mul z hZ hE (hZdiff z hz) (hEdiff z)
    have hlog : logDeriv Φ z = 0 := by
      rw [hΦdef, hdivlem, hmullem, hlogE z, hkey z hz]
      ring
    have hΦne : Φ z ≠ 0 := div_ne_zero (hFne' z hz) hden
    have hap := logDeriv_apply Φ z
    rw [hlog] at hap
    rcases div_eq_zero_iff.1 hap.symm with h | h
    · exact h
    · exact absurd h hΦne
  have hΦdiff : DifferentiableOn ℂ Φ Ω := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (hFdiff z hz).div ((hZdiff z hz).mul (hEdiff z))
      (mul_ne_zero (hZne z hz) (Complex.exp_ne_zero _))
  have hz₀ : ((A₀ + 1 : ℝ) : ℂ) ∈ Ω := by
    rw [hΩdef, Set.mem_setOf_eq, Complex.ofReal_re]
    linarith
  have hconst : ∀ z ∈ Ω, Φ z = Φ ((A₀ + 1 : ℝ) : ℂ) := by
    intro z hz
    refine Convex.is_const_of_fderivWithin_eq_zero hΩconv hΦdiff ?_ hz hz₀
    intro w hw
    rw [fderivWithin_of_isOpen hΩopen hw]
    have hd : deriv Φ w = 0 := hΦderiv w hw
    have : fderiv ℂ Φ w = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Φ w) := by
      rw [deriv]
      exact (ContinuousLinearMap.ext_ring (by simp)).symm
    rw [this, hd]
    simp
  set c : ℂ := Φ ((A₀ + 1 : ℝ) : ℂ) with hcdef
  have hcne : c ≠ 0 := by
    rw [hcdef, hΦdef]
    exact div_ne_zero (hFne' _ hz₀) (mul_ne_zero (hZne _ hz₀) (Complex.exp_ne_zero _))
  refine ⟨χ, fun z => c * Complex.exp (H z), ?_, ?_, ?_⟩
  · exact (differentiable_const c).mul (Complex.differentiable_exp.comp hHdiff)
  · intro z
    exact mul_ne_zero hcne (Complex.exp_ne_zero _)
  · -- the identity on the big half plane, then continued to `Re s > 1`
    have hbig : ∀ z ∈ Ω, F z = helsonZetaValue z χ * (c * Complex.exp (H z)) := by
      intro z hz
      have hval : F z / (helsonZetaValue z χ * Complex.exp (H z)) = c := hconst z hz
      have hden : helsonZetaValue z χ * Complex.exp (H z) ≠ 0 :=
        mul_ne_zero (hZne z hz) (Complex.exp_ne_zero _)
      have hEq := (div_eq_iff hden).1 hval
      rw [hEq]
      ring
    intro s hs
    set U : Set ℂ := {z : ℂ | 1 < z.re} with hUdef
    have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUconv : Convex ℝ U := by
      refine convex_halfSpace_gt ?_ 1
      exact { map_add := fun x y => Complex.add_re x y, map_smul := fun c x => by simp }
    have hUconn : IsPreconnected U := hUconv.isPreconnected
    have hFU : AnalyticOnNhd ℂ F U := by
      intro z hz
      exact hFan z (le_of_lt hz)
    have hRU : AnalyticOnNhd ℂ (fun z => helsonZetaValue z χ * (c * Complex.exp (H z))) U := by
      refine DifferentiableOn.analyticOnNhd ?_ hUopen
      intro z hz
      refine DifferentiableAt.differentiableWithinAt ?_
      refine DifferentiableAt.mul ?_ ?_
      · exact (differentiableOn_helsonZetaValue χ).differentiableAt (hUopen.mem_nhds hz)
      · exact (differentiableAt_const c).mul (hEdiff z)
    have hz₀U : ((A₀ + 1 : ℝ) : ℂ) ∈ U := by
      rw [hUdef, Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    have hev : F =ᶠ[nhds ((A₀ + 1 : ℝ) : ℂ)]
        fun z => helsonZetaValue z χ * (c * Complex.exp (H z)) := by
      filter_upwards [hΩopen.mem_nhds hz₀] with z hz
      exact hbig z hz
    exact hFU.eqOn_of_preconnected_of_eventuallyEq hRU hUconn hz₀U hev hs

/-- **The Helson realization of a divisor.**  Any meromorphic function that is analytic and zero
free on the closed half plane, and whose logarithmic derivative has a Mellin representation with a
bounded vanishing datum, has the same divisor as the continuation of a Helson zeta function. -/
theorem exists_continuable_phase_of_mellin_logDeriv {F : ℂ → ℂ}
    (hFmero : MeromorphicOn F Set.univ)
    (hFan : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ F z) (hFne : ∀ z : ℂ, 1 ≤ z.re → F z ≠ 0)
    {q : ℝ → ℂ} {g₁ : ℂ → ℂ} (hg₁ : Differentiable ℂ g₁)
    (hqmeas : AEStronglyMeasurable q (volume.restrict (Set.Ioi (1:ℝ))))
    (hq0 : Tendsto q atTop (nhds 0)) {M : ℝ} (hqb : ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M)
    (hrep : ∀ s : ℂ, 1 < s.re →
      logDeriv F s = (∫ x in Set.Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) + g₁ s) :
    ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
      ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (Z s)) ∧
        ∀ z : ℂ, meromorphicOrderAt Z z = meromorphicOrderAt F z := by
  classical
  obtain ⟨χ, g, hgdiff, hgne, hfact⟩ :=
    helson_factorization_of_mellin_logDeriv hFan hFne hg₁ hqmeas hq0 hqb hrep
  have hZmero : MeromorphicOn (fun s => F s / g s) Set.univ := by
    intro z _
    exact (hFmero z (Set.mem_univ z)).div ((hgdiff.analyticAt z).meromorphicAt)
  have hZval : ∀ s : ℂ, 1 < s.re → F s / g s = helsonZetaValue s χ := by
    intro s hs
    rw [hfact s hs, mul_div_assoc, div_self (hgne s), mul_one]
  refine ⟨χ, ⟨fun s => F s / g s, hZmero, ?_⟩, fun s => F s / g s, hZmero, ?_, ?_⟩
  · intro s hs
    show HasProd _ (F s / g s)
    rw [hZval s hs]
    exact (multipliable_helsonEuler (fun p => le_of_eq (χ p).2) hs).hasProd
  · intro s hs
    show HasProd _ (F s / g s)
    rw [hZval s hs]
    exact (multipliable_helsonEuler (fun p => le_of_eq (χ p).2) hs).hasProd
  · intro z
    have hgorder : meromorphicOrderAt g z = 0 := by
      rw [(hgdiff.analyticAt z).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr (hgne z))]
      rfl
    have hdiv := meromorphicOrderAt_div (hFmero z (Set.mem_univ z))
      ((hgdiff.analyticAt z).meromorphicAt)
    have hfun : (fun s => F s / g s) = F / g := rfl
    rw [hfun, hdiv, hgorder, sub_zero]

/-- **Andersson's Theorem 2 for a prescribed-divisor realization**, unconditionally. -/
theorem helson_factorization_divisorFunction {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    ∃ (χ : PhaseTorus) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ z : ℂ, g z ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re →
        GaloisForLFunctions.divisorFunction a b s = helsonZetaValue s χ * g s := by
  obtain ⟨q, g₁, hg₁, hqmeas, hq0, ⟨M, hqb⟩, hrep⟩ :=
    exists_mellin_add_entire_logDeriv_divisorFunction ha hane hb hbne hare hbre
  exact helson_factorization_of_mellin_logDeriv
    (fun z hz => divisorFunction_analyticAt_of_re_le ha hane hb hbne hbre hz)
    (fun z hz => divisorFunction_ne_zero_of_re_le ha hane hb hbne hare hbre hz)
    hg₁ hqmeas hq0 hqb hrep

/-- **Divisor surjectivity of the Helson continuation stratum**, unconditionally: every locally
finite signed divisor to the left of the line is the divisor of the meromorphic continuation of a
Helson zeta function. -/
theorem exists_continuable_phase_with_prescribed_divisor {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
      ∃ F : ℂ → ℂ, MeromorphicOn F Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (F s)) ∧
        ∀ z : ℂ, meromorphicOrderAt F z
          = meromorphicOrderAt (GaloisForLFunctions.divisorFunction a b) z := by
  classical
  obtain ⟨χ, g, hgdiff, hgne, hfact⟩ :=
    helson_factorization_divisorFunction ha hane hb hbne hare hbre
  refine ⟨χ, ?_, fun s => GaloisForLFunctions.divisorFunction a b s / g s, ?_, ?_, ?_⟩
  · refine ⟨fun s => GaloisForLFunctions.divisorFunction a b s / g s, ?_, ?_⟩
    · intro z _
      exact ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z
        (Set.mem_univ z)).div ((hgdiff.analyticAt z).meromorphicAt)
    · intro s hs
      have hval : GaloisForLFunctions.divisorFunction a b s / g s = helsonZetaValue s χ := by
        rw [hfact s hs, mul_div_assoc, div_self (hgne s), mul_one]
      show HasProd _ (GaloisForLFunctions.divisorFunction a b s / g s)
      rw [hval]
      exact (multipliable_helsonEuler (fun p => le_of_eq (χ p).2) hs).hasProd
  · intro z _
    exact ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z
      (Set.mem_univ z)).div ((hgdiff.analyticAt z).meromorphicAt)
  · intro s hs
    have hval : GaloisForLFunctions.divisorFunction a b s / g s = helsonZetaValue s χ := by
      rw [hfact s hs, mul_div_assoc, div_self (hgne s), mul_one]
    show HasProd _ (GaloisForLFunctions.divisorFunction a b s / g s)
    rw [hval]
    exact (multipliable_helsonEuler (fun p => le_of_eq (χ p).2) hs).hasProd
  · intro z
    have hgorder : meromorphicOrderAt g z = 0 := by
      rw [(hgdiff.analyticAt z).meromorphicOrderAt_eq,
        analyticOrderAt_eq_zero.mpr (Or.inr (hgne z))]
      rfl
    have hdiv := meromorphicOrderAt_div
      ((GaloisForLFunctions.meromorphicOn_divisorFunction ha hane hb hbne) z (Set.mem_univ z))
      ((hgdiff.analyticAt z).meromorphicAt)
    have hfun : (fun s => GaloisForLFunctions.divisorFunction a b s / g s)
        = GaloisForLFunctions.divisorFunction a b / g := rfl
    rw [hfun, hdiv, hgorder, sub_zero]

/-- **Divisor surjectivity with multiplicities.**  The continuation of the Helson zeta function
produced above has, at every point, exactly the order prescribed by the two sequences. -/
theorem exists_continuable_phase_with_prescribed_multiplicities {a b : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (hane : ∀ n, a n ≠ 0)
    (hb : Tendsto (fun n => ‖b n‖) atTop atTop) (hbne : ∀ n, b n ≠ 0)
    (hare : ∀ n, (a n).re < 1) (hbre : ∀ n, (b n).re < 1) :
    ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
      ∃ F : ℂ → ℂ, MeromorphicOn F Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (F s)) ∧
        ∀ z : ℂ, meromorphicOrderAt F z
          = ((GaloisForLFunctions.zeroMultiplicity a z : ℤ) : WithTop ℤ)
            - ((GaloisForLFunctions.zeroMultiplicity b z : ℤ) : WithTop ℤ) := by
  obtain ⟨χ, hχ, F, hFmero, hFprod, hFord⟩ :=
    exists_continuable_phase_with_prescribed_divisor ha hane hb hbne hare hbre
  refine ⟨χ, hχ, F, hFmero, hFprod, fun z => ?_⟩
  rw [hFord z]
  exact GaloisForLFunctions.meromorphicOrderAt_divisorFunction_eq_multiplicity ha hane hb hbne z

end RHTower

end
