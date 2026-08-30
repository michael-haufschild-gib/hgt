import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint
import GaloisForLFunctions.HTGeometry.GammaShiftCasoratian
import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit

/-!
# Parikh--Wilczek finite-band Borel reflection no-go

The first-winding Parikh--Wilczek Borel tower is

`B_k(s) = Gamma(s + 2k) / (k!)^2`.

Every fixed finite grade row therefore factors as `Gamma(s) P(s)`, where `P` is an even
ascending-Pochhammer polynomial.  If such a row produced the functional-equation-reflected
coefficient `B_0(1-s)` throughout the critical strip, applying the same source law at `1-s`
would force

`P(s) P(1-s) = 1`.

Polynomial rigidity makes `P` constant.  The source law would then make Gamma reflection-symmetric
near `s = 1/2`; differentiating there contradicts the nonzero exact logarithmic derivative
`digamma(1/2) = -gamma - 2 log 2`.

Thus no spectrally independent finite boundary row can generate the missing PW functional-equation
partner.  This includes the boundary row of an arbitrary finite-band non-diagonal grade mixer;
later rows may depend on grade and mix in either direction.  Any surviving PW-B producer must be
infinite-range/non-polynomial (for example fractional or singular), channel-coupled, or depend on
the spectral parameter itself.

`[NEW] [CLASSIFICATION] [NO-GO] [PW-B] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A fixed finite boundary row acting on the literal first-winding PW Borel grades. -/
def schwarzschildParikhWilczekFiniteBandBorelTransform {N : ℕ}
    (a : Fin (N + 1) → ℂ) (s : ℂ) : ℂ :=
  ∑ j, a j * schwarzschildParikhWilczekFirstWindingBorelCoefficient s (j : ℕ)

/-- Exact polynomial multiplier of a finite PW Borel boundary row after extracting `Gamma(s)`. -/
def schwarzschildParikhWilczekFiniteBandGammaMultiplier {N : ℕ}
    (a : Fin (N + 1) → ℂ) : ℂ[X] :=
  ∑ j, C (a j / (((j : ℕ).factorial : ℂ) ^ 2)) *
    ascPochhammer ℂ (2 * (j : ℕ))

/-- **Finite-row classification.**  Every finite PW Borel boundary row is Gamma times one finite
even ascending-Pochhammer polynomial. -/
theorem schwarzschildParikhWilczekFiniteBandBorelTransform_eq_eval_mul_Gamma
    {N : ℕ} (a : Fin (N + 1) → ℂ) (s : ℂ) (hs : 0 < s.re) :
    schwarzschildParikhWilczekFiniteBandBorelTransform a s =
      (schwarzschildParikhWilczekFiniteBandGammaMultiplier a).eval s *
        Complex.Gamma s := by
  rw [schwarzschildParikhWilczekFiniteBandBorelTransform]
  simp only [schwarzschildParikhWilczekFirstWindingBorelCoefficient]
  have hEval :
      (schwarzschildParikhWilczekFiniteBandGammaMultiplier a).eval s =
        ∑ j, (a j / (((j : ℕ).factorial : ℂ) ^ 2)) *
          (ascPochhammer ℂ (2 * (j : ℕ))).eval s := by
    rw [schwarzschildParikhWilczekFiniteBandGammaMultiplier]
    change (Polynomial.evalRingHom s)
      (∑ j, C (a j / (((j : ℕ).factorial : ℂ) ^ 2)) *
        ascPochhammer ℂ (2 * (j : ℕ))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [hEval, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hpole : ∀ k < 2 * (j : ℕ), s + k ≠ 0 := by
    intro k _ hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [show s + 2 * (j : ℂ) = s + ((2 * (j : ℕ) : ℕ) : ℂ) by push_cast; ring]
  rw [GaloisForLFunctions.Complex.Gamma_add_nat_eq_ascPochhammer_mul s
    (2 * (j : ℕ)) hpole]
  ring

/-- **PW-B finite-band reflection no-go.**  No fixed finite linear combination of forward
first-winding Borel grades produces the functional-equation-reflected grade-zero coefficient on
the open critical strip.  Since grade zero is the boundary row of every finite-band mixer on
`ℕ`, this kills all spectrally independent finite-band non-diagonal grade transport as the missing
PW-B source law. -/
theorem no_schwarzschildParikhWilczekFiniteBandBorelReflection :
    ¬ ∃ (N : ℕ) (a : Fin (N + 1) → ℂ),
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        schwarzschildParikhWilczekFiniteBandBorelTransform a s =
          schwarzschildParikhWilczekFirstWindingBorelCoefficient (1 - s) 0 := by
  rintro ⟨N, a, hreflect⟩
  let P : ℂ[X] := schwarzschildParikhWilczekFiniteBandGammaMultiplier a
  let PR : ℂ[X] := P.comp (C 1 - X)
  have hGamma_ne (s : ℂ) (hs : 0 < s.re) : Complex.Gamma s ≠ 0 :=
    GaloisForLFunctions.HTGeometry.gamma_ne_zero_of_re_pos hs
  have hsource (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
      P.eval s * Complex.Gamma s = Complex.Gamma (1 - s) := by
    rw [← schwarzschildParikhWilczekFiniteBandBorelTransform_eq_eval_mul_Gamma a s hs0]
    simpa [P, schwarzschildParikhWilczekFirstWindingBorelCoefficient] using
      hreflect s hs0 hs1
  have hproduct (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
      P.eval s * P.eval (1 - s) = 1 := by
    have hs0' : 0 < (1 - s).re := by simp; linarith
    have hs1' : (1 - s).re < 1 := by simp; linarith
    have hforward := hsource s hs0 hs1
    have hbackward := hsource (1 - s) hs0' hs1'
    have hGs : Complex.Gamma s ≠ 0 := hGamma_ne s hs0
    have hGr : Complex.Gamma (1 - s) ≠ 0 := hGamma_ne (1 - s) hs0'
    have hP : P.eval s = Complex.Gamma (1 - s) / Complex.Gamma s :=
      (eq_div_iff hGs).2 hforward
    have hPr : P.eval (1 - s) = Complex.Gamma s / Complex.Gamma (1 - s) := by
      apply (eq_div_iff hGr).2
      simpa only [sub_sub_cancel] using hbackward
    rw [hP, hPr]
    field_simp
  have hpoly : P * PR = 1 := by
    have hinj : Function.Injective
        (fun n : ℕ => (1 / 2 : ℂ) + (n : ℂ) * I) := by
      intro m n hmn
      have him := congrArg Complex.im hmn
      norm_num at him
      exact_mod_cast him
    have hrange :
        Set.range (fun n : ℕ => (1 / 2 : ℂ) + (n : ℂ) * I) ⊆
          {z : ℂ | (P * PR - 1).IsRoot z} := by
      intro z hz
      obtain ⟨n, rfl⟩ := hz
      change (P * PR - 1).IsRoot ((1 / 2 : ℂ) + (n : ℂ) * I)
      rw [Polynomial.IsRoot.def]
      have hs0 : 0 < ((1 / 2 : ℂ) + (n : ℂ) * I).re := by norm_num
      have hs1 : ((1 / 2 : ℂ) + (n : ℂ) * I).re < 1 := by norm_num
      rw [Polynomial.eval_sub, Polynomial.eval_mul]
      have hPR : PR.eval ((1 / 2 : ℂ) + (n : ℂ) * I) =
          P.eval (1 - ((1 / 2 : ℂ) + (n : ℂ) * I)) := by
        simp [PR]
      rw [hPR, hproduct _ hs0 hs1]
      simp
    have hinfinite : {z : ℂ | (P * PR - 1).IsRoot z}.Infinite :=
      (Set.infinite_range_of_injective hinj).mono hrange
    have hzero := Polynomial.eq_zero_of_infinite_isRoot (P * PR - 1) hinfinite
    exact sub_eq_zero.mp hzero
  have hPne : P ≠ 0 := by
    intro hP
    rw [hP, zero_mul] at hpoly
    exact zero_ne_one hpoly
  have hPRne : PR ≠ 0 := by
    intro hPR
    rw [hPR, mul_zero] at hpoly
    exact zero_ne_one hpoly
  have hdeg := Polynomial.natDegree_mul hPne hPRne
  rw [hpoly] at hdeg
  norm_num at hdeg
  have hPdeg : P.natDegree = 0 :=
    (Nat.eq_zero_of_add_eq_zero hdeg.symm).1
  let c : ℂ := P.coeff 0
  have hPconst : P = C c := Polynomial.eq_C_of_natDegree_eq_zero hPdeg
  have hscalar (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
      c * Complex.Gamma s = Complex.Gamma (1 - s) := by
    have h := hsource s hs0 hs1
    rw [hPconst, Polynomial.eval_C] at h
    exact h
  let center : ℂ := 1 / 2
  have hGcenter : Complex.Gamma center ≠ 0 :=
    hGamma_ne center (by norm_num [center])
  have hc : c = 1 := by
    have h := hscalar center (by norm_num [center]) (by norm_num [center])
    have hone : 1 - center = center := by norm_num [center]
    rw [hone] at h
    apply (mul_right_cancel₀ hGcenter)
    simpa using h
  have hlocal :
      (fun s : ℂ => c * Complex.Gamma s) =ᶠ[𝓝 center]
        (fun s : ℂ => Complex.Gamma (1 - s)) := by
    have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (by norm_num [center])] with s hs
    exact hscalar s hs.1 hs.2
  have hdiffCenter : DifferentiableAt ℂ Complex.Gamma center :=
    GaloisForLFunctions.HTGeometry.differentiableAt_gamma_of_re_pos
      (by norm_num [center])
  have hleft : deriv (fun s : ℂ => c * Complex.Gamma s) center =
      c * deriv Complex.Gamma center := deriv_const_mul c hdiffCenter
  have hinner : HasDerivAt (fun s : ℂ => 1 - s) (-1) center :=
    (hasDerivAt_id center).const_sub (1 : ℂ)
  have hright : deriv (fun s : ℂ => Complex.Gamma (1 - s)) center =
      -(deriv Complex.Gamma center) := by
    have hdiffRef : DifferentiableAt ℂ Complex.Gamma (1 - center) :=
      GaloisForLFunctions.HTGeometry.differentiableAt_gamma_of_re_pos
        (by norm_num [center])
    have hcomp := hdiffRef.hasDerivAt.comp center hinner
    change deriv (Complex.Gamma ∘ fun s : ℂ => 1 - s) center = _
    rw [show 1 - center = center by norm_num [center]] at hcomp
    simpa using hcomp.deriv
  have hderiv := hlocal.deriv_eq
  rw [hleft, hright, hc, one_mul] at hderiv
  have hderivZero : deriv Complex.Gamma center = 0 := by
    have htwo : 2 * deriv Complex.Gamma center = 0 := by
      linear_combination hderiv
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hpsi : Complex.digamma center ≠ 0 := by
    rw [GaloisForLFunctions.SeamSplit.digamma_half]
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.log_re] at hre
    have hgamma : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
      lt_trans Real.one_half_lt_eulerMascheroniSeq_six
        (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 6)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hderivNe : deriv Complex.Gamma center ≠ 0 := by
    rw [GaloisForLFunctions.HTGeometry.deriv_gamma_eq (by norm_num [center])]
    exact mul_ne_zero hGcenter hpsi
  exact hderivNe hderivZero

end

end RHTower
