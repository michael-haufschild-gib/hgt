import GaloisForLFunctions.RHTower.PhotonicCorotatingInterfaceSymbol
import GaloisForLFunctions.RHTower.PhotonicPrimeCyclicSlabParabolicRealization
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Frozen two-sided complex transmission excludes critical prime conormals

For the constant-coefficient two-sided elliptic collar, transfer from two fixed
interior slices and continuous normal flux forces an interface Fourier trace to
vanish when interior-slice coefficients have polynomial growth. This handles
complex decaying roots and thus the lossy principal symbol of PTR. It does not
assert the variable-coefficient Maxwell collar obeys these decoupled grade
relations; deriving that full source transmission law remains open.
-/

namespace RHTower

open Filter Topology

private def frozenInterfaceDenominator (kl kr x y : ℂ) : ℂ :=
  (kl + kr) + (kl - kr) * x ^ 2 + (kr - kl) * y ^ 2 -
    (kl + kr) * x ^ 2 * y ^ 2

private theorem frozen_complex_interface_identity
    (kl kr x y c dl dr L R : ℂ)
    (hflux : kl * dl = kr * dr)
    (hleft : 2 * x * L = c * (1 + x ^ 2) - dl * (1 - x ^ 2))
    (hright : 2 * y * R = c * (1 + y ^ 2) + dr * (1 - y ^ 2)) :
    frozenInterfaceDenominator kl kr x y * c =
      2 * kl * x * (1 - y ^ 2) * L +
        2 * kr * y * (1 - x ^ 2) * R := by
  unfold frozenInterfaceDenominator
  linear_combination
    -(kl * (1 - y ^ 2)) * hleft -
      (kr * (1 - x ^ 2)) * hright +
      ((1 - x ^ 2) * (1 - y ^ 2)) * hflux

private theorem frozen_complex_interface_trace_vanishes
    (kl kr : ℂ) (x y c dl dr L R : ℕ → ℂ)
    (hnonzero : kl + kr ≠ 0)
    (hx : Tendsto x atTop (nhds 0))
    (hy : Tendsto y atTop (nhds 0))
    (hxl : Tendsto (fun n => x n * L n) atTop (nhds 0))
    (hyr : Tendsto (fun n => y n * R n) atTop (nhds 0))
    (hflux : ∀ n, kl * dl n = kr * dr n)
    (hleft : ∀ n, 2 * x n * L n = c n * (1 + x n ^ 2) - dl n * (1 - x n ^ 2))
    (hright : ∀ n, 2 * y n * R n = c n * (1 + y n ^ 2) + dr n * (1 - y n ^ 2)) :
    Tendsto c atTop (nhds 0) := by
  let F : ℕ → ℂ := fun n => frozenInterfaceDenominator kl kr (x n) (y n)
  have hx2 : Tendsto (fun n => x n ^ 2) atTop (nhds 0) := by
    simpa using hx.pow 2
  have hy2 : Tendsto (fun n => y n ^ 2) atTop (nhds 0) := by
    simpa using hy.pow 2
  have hT1 : Tendsto (fun n => (kl - kr) * x n ^ 2) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hx2 (a := kl - kr))
  have hT2 : Tendsto (fun n => (kr - kl) * y n ^ 2) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hy2 (a := kr - kl))
  have hT3 : Tendsto (fun n => (kl + kr) * x n ^ 2 * y n ^ 2)
      atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul (hx2.mul hy2) (a := kl + kr)) using 1
      <;> simp [mul_assoc]
  have hF : Tendsto F atTop (nhds (kl + kr)) := by
    simpa [F, frozenInterfaceDenominator] using
      ((tendsto_const_nhds.add hT1).add hT2).sub hT3
  have hY1 : Tendsto (fun n => 1 - y n ^ 2) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hy2 (a := (1 : ℂ)))
  have hX1 : Tendsto (fun n => 1 - x n ^ 2) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hx2 (a := (1 : ℂ)))
  have hleftTerm : Tendsto (fun n => 2 * kl * x n * (1 - y n ^ 2) * L n)
      atTop (nhds 0) := by
    have h := (tendsto_const_nhds.mul hxl (a := 2 * kl)).mul hY1
    convert h using 1
    · funext n
      ring
    · simp
  have hrightTerm : Tendsto (fun n => 2 * kr * y n * (1 - x n ^ 2) * R n)
      atTop (nhds 0) := by
    have h := (tendsto_const_nhds.mul hyr (a := 2 * kr)).mul hX1
    convert h using 1
    · funext n
      ring
    · simp
  have hFc : Tendsto (fun n => F n * c n) atTop (nhds 0) := by
    convert hleftTerm.add hrightTerm using 1
    · funext n
      exact frozen_complex_interface_identity kl kr (x n) (y n) (c n)
        (dl n) (dr n) (L n) (R n) (hflux n) (hleft n) (hright n)
    · simp
  have heventual : ∀ᶠ n in atTop, F n ≠ 0 := hF.eventually_ne hnonzero
  have hratio : Tendsto (fun n => (F n * c n) / F n) atTop (nhds 0) := by
    convert hFc.div hF hnonzero using 1
    · rfl
    · simp
  apply hratio.congr'
  filter_upwards [heventual] with n hn
  simp [hn]

private theorem exp_damped_polynomial_slice_vanishes
    (a : ℝ) (P : Polynomial ℝ) (x L : ℕ → ℂ) (ha : 0 < a)
    (hx : ∀ n, ‖x n‖ ≤ Real.exp (-(a * (n : ℝ))))
    (hL : ∀ n, ‖L n‖ ≤ P.eval (a * (n : ℝ))) :
    Tendsto (fun n => x n * L n) atTop (nhds 0) := by
  have hAt : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ =>
      P.eval (a * (n : ℝ)) / Real.exp (a * (n : ℝ))) atTop (nhds 0) := by
    exact (Polynomial.tendsto_div_exp_atTop P).comp hAt
  have hnorm : Tendsto (fun n => ‖x n * L n‖) atTop (nhds 0) := by
    apply squeeze_zero (fun n => norm_nonneg (x n * L n))
      (fun n => ?_) hupper
    have hp : 0 ≤ P.eval (a * (n : ℝ)) :=
      (norm_nonneg (L n)).trans (hL n)
    calc
      ‖x n * L n‖ = ‖x n‖ * ‖L n‖ := norm_mul _ _
      _ ≤ ‖x n‖ * P.eval (a * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hL n) (norm_nonneg _)
      _ ≤ Real.exp (-(a * (n : ℝ))) * P.eval (a * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (hx n) hp
      _ = P.eval (a * (n : ℝ)) / Real.exp (a * (n : ℝ)) := by
        rw [Real.exp_neg]
        ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

private theorem frozen_complex_exponential_trace_vanishes
    (kl kr : ℂ) (PL PR : Polynomial ℝ) (c dl dr L R : ℕ → ℂ)
    (hkl : 0 < kl.re) (hkr : 0 < kr.re)
    (hLpoly : ∀ n, ‖L n‖ ≤ PL.eval (kl.re * (n : ℝ)))
    (hRpoly : ∀ n, ‖R n‖ ≤ PR.eval (kr.re * (n : ℝ)))
    (hflux : ∀ n, kl * dl n = kr * dr n)
    (hleft : ∀ n : ℕ,
      2 * Complex.exp (-(kl * (n : ℂ))) * L n =
        c n * (1 + Complex.exp (-(kl * (n : ℂ))) ^ 2) -
          dl n * (1 - Complex.exp (-(kl * (n : ℂ))) ^ 2))
    (hright : ∀ n : ℕ,
      2 * Complex.exp (-(kr * (n : ℂ))) * R n =
        c n * (1 + Complex.exp (-(kr * (n : ℂ))) ^ 2) +
          dr n * (1 - Complex.exp (-(kr * (n : ℂ))) ^ 2)) :
    Tendsto c atTop (nhds 0) := by
  let x : ℕ → ℂ := fun n => Complex.exp (-(kl * (n : ℂ)))
  let y : ℕ → ℂ := fun n => Complex.exp (-(kr * (n : ℂ)))
  have hxnorm (n : ℕ) : ‖x n‖ = Real.exp (-(kl.re * (n : ℝ))) := by
    simp [x, Complex.norm_exp, Complex.neg_re, Complex.mul_re]
  have hynorm (n : ℕ) : ‖y n‖ = Real.exp (-(kr.re * (n : ℝ))) := by
    simp [y, Complex.norm_exp, Complex.neg_re, Complex.mul_re]
  have hxreal : Tendsto (fun n : ℕ => Real.exp (-(kl.re * (n : ℝ))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hkl tendsto_natCast_atTop_atTop)
  have hyreal : Tendsto (fun n : ℕ => Real.exp (-(kr.re * (n : ℝ))))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hkr tendsto_natCast_atTop_atTop)
  have hx : Tendsto x atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hxnorm] using hxreal
  have hy : Tendsto y atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hynorm] using hyreal
  have hxl : Tendsto (fun n => x n * L n) atTop (nhds 0) := by
    apply exp_damped_polynomial_slice_vanishes kl.re PL x L hkl
    · intro n
      exact (hxnorm n).le
    · exact hLpoly
  have hyr : Tendsto (fun n => y n * R n) atTop (nhds 0) := by
    apply exp_damped_polynomial_slice_vanishes kr.re PR y R hkr
    · intro n
      exact (hynorm n).le
    · exact hRpoly
  have hnonzero : kl + kr ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.zero_re] at hre
    linarith
  exact frozen_complex_interface_trace_vanishes kl kr x y c dl dr L R
    hnonzero hx hy hxl hyr hflux hleft hright

theorem ptr_frozen_complex_prime_conormal_no_go
    (p : Nat.Primes) (s kl kr : ℂ) (PL PR : Polynomial ℝ)
    (dl dr L R : ℕ → ℂ) (hre : s.re = 1 / 2)
    (hkl : 0 < kl.re) (hkr : 0 < kr.re)
    (hLpoly : ∀ n, ‖L n‖ ≤ PL.eval (kl.re * (n : ℝ)))
    (hRpoly : ∀ n, ‖R n‖ ≤ PR.eval (kr.re * (n : ℝ)))
    (hflux : ∀ n, kl * dl n = kr * dr n)
    (hleft : ∀ n : ℕ,
      2 * Complex.exp (-(kl * (n : ℂ))) * L n =
        photonicPrimePCMConormalSideband p s (n : ℤ) *
          (1 + Complex.exp (-(kl * (n : ℂ))) ^ 2) -
          dl n * (1 - Complex.exp (-(kl * (n : ℂ))) ^ 2))
    (hright : ∀ n : ℕ,
      2 * Complex.exp (-(kr * (n : ℂ))) * R n =
        photonicPrimePCMConormalSideband p s (n : ℤ) *
          (1 + Complex.exp (-(kr * (n : ℂ))) ^ 2) +
          dr n * (1 - Complex.exp (-(kr * (n : ℂ))) ^ 2)) :
    False := by
  let c : ℕ → ℂ := fun n => photonicPrimePCMConormalSideband p s (n : ℤ)
  have hc : Tendsto c atTop (nhds 0) :=
    frozen_complex_exponential_trace_vanishes kl kr PL PR c dl dr L R
      hkl hkr hLpoly hRpoly hflux hleft hright
  have hchar : ‖bilateralHalfDensityCharacter (p : ℕ) s‖ = 1 :=
    (norm_bilateralHalfDensityCharacter_eq_one_iff p.property.two_le s).mpr hre
  have hnorm (n : ℕ) : ‖c n‖ = 1 := by
    dsimp [c]
    rw [photonicPrimePCMConormalSideband_eq_bilateralEigenFamily]
    simp [bilateralEigenFamily, hchar]
  have hnormlim : Tendsto (fun n => ‖c n‖) atTop (nhds (0 : ℝ)) := by
    simpa only [norm_zero, Function.comp_def] using
      (continuous_norm.tendsto (0 : ℂ)).comp hc
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (0 : ℝ)) := by
    simpa only [hnorm] using hnormlim
  have hbad : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
  exact one_ne_zero hbad

/-- Polynomial interior slices and the exact decoupled two-sided transfer law
for a fixed complex normal root pair. This is a frozen-collar model, not the
variable-coefficient Maxwell interface equation. -/
def ptrFrozenPrimeConormalAdmissible
    (p : Nat.Primes) (s kl kr : ℂ) : Prop :=
  ∃ (PL PR : Polynomial ℝ) (dl dr L R : ℕ → ℂ),
    (∀ n, ‖L n‖ ≤ PL.eval (kl.re * (n : ℝ))) ∧
    (∀ n, ‖R n‖ ≤ PR.eval (kr.re * (n : ℝ))) ∧
    (∀ n, kl * dl n = kr * dr n) ∧
    (∀ n : ℕ,
      2 * Complex.exp (-(kl * (n : ℂ))) * L n =
        photonicPrimePCMConormalSideband p s (n : ℤ) *
          (1 + Complex.exp (-(kl * (n : ℂ))) ^ 2) -
          dl n * (1 - Complex.exp (-(kl * (n : ℂ))) ^ 2)) ∧
    (∀ n : ℕ,
      2 * Complex.exp (-(kr * (n : ℂ))) * R n =
        photonicPrimePCMConormalSideband p s (n : ℤ) *
          (1 + Complex.exp (-(kr * (n : ℂ))) ^ 2) +
          dr n * (1 - Complex.exp (-(kr * (n : ℂ))) ^ 2))

/-- The source paper's actual complex dielectric and exterior-air principal
roots exclude any critical-line prime conormal in the frozen distributional
collar model. The remaining physical lift is variable-coefficient transfer. -/
theorem ptr_paper_frozen_complex_prime_conormal_no_go
    (φ : ℝ) (p : Nat.Primes) (s : ℂ) (hre : s.re = 1 / 2) :
    ∃ κin κout : ℂ,
      κin ^ 2 = ptrPaperInsideNormalSymbol φ ∧
      κout ^ 2 =
        (((299792458 : ℝ) / 100000000) ^ 2 -
          ((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ) ∧
      ¬ ptrFrozenPrimeConormalAdmissible p s κin κout := by
  obtain ⟨κin, κout, hkin, hkout, hkinpos, hkoutpos, _⟩ :=
    ptr_paper_complex_principal_transmission_complementing φ
  refine ⟨κin, κout, hkin, hkout, ?_⟩
  rintro ⟨PL, PR, dl, dr, L, R, hLpoly, hRpoly, hflux, hleft, hright⟩
  exact ptr_frozen_complex_prime_conormal_no_go p s κin κout PL PR dl dr L R
    hre hkinpos hkoutpos hLpoly hRpoly hflux hleft hright

end RHTower
