import GaloisForLFunctions.RHTower.DeningerGaussianEndpointCore
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The completed Mellin factor of the Gaussian power orbit

Summing a Gaussian probe over its Kummer power orbit and taking the Mellin transform produces the
completed Gamma factor times the zeta function: the orbit sum contributes the Dirichlet series and
the single probe contributes the Gamma factor.  Linearity then gives the completed Mellin transform
of every endpoint-corrected Gaussian combination, with the exponential polynomial of the
combination as its Dirichlet coefficient.

* `deningerGaussianRaySum` : the power orbit sum.
* `deningerGaussianRaySum_mellin` : the completed Mellin factor `(9)`.
* `deningerGaussianComboRay_mellin` : the same for a finite combination `(10)`.
-/

namespace RHTower

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

section RaySum

/-- The Gaussian power orbit sum in the squared variable. -/
noncomputable def deningerGaussianRayTheta (μ : ℝ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, ((Real.exp (-Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ)

/-- The Gaussian power orbit sum. -/
noncomputable def deningerGaussianRaySum (μ : ℝ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, deningerGaussianProbe (μ * ((n : ℝ) + 1)) x

/-- The orbit sum is the squared-variable orbit sum evaluated at the square. -/
theorem deningerGaussianRaySum_eq_theta (μ : ℝ) (x : ℝ) :
    deningerGaussianRaySum μ x = deningerGaussianRayTheta μ (x ^ 2) := by
  rw [deningerGaussianRaySum, deningerGaussianRayTheta]
  refine tsum_congr fun n => ?_
  rw [deningerGaussianProbe_apply]
  congr 2
  ring

/-- The Gaussian orbit terms are summable on the open ray. -/
theorem deningerRayTheta_summable {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    Summable fun n : ℕ => Real.exp (-Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t) := by
  set q : ℝ := Real.exp (-Real.pi * μ ^ 2 * t) with hq
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : 0 < Real.pi * μ ^ 2 * t := by positivity
    linarith
  have hgeom : Summable fun n : ℕ => q ^ (n + 1) := by
    have := summable_geometric_of_lt_one (le_of_lt hqpos) hqlt
    exact (this.mul_left q).congr fun n => by rw [pow_succ]; ring
  refine Summable.of_nonneg_of_le (fun n => le_of_lt (Real.exp_pos _)) (fun n => ?_) hgeom
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hle : -Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t
      ≤ (-Real.pi * μ ^ 2 * t) * ((n : ℝ) + 1) := by
    have hpos : 0 < Real.pi * μ ^ 2 * t := by positivity
    nlinarith [hsq, hpos]
  calc Real.exp (-Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t)
      ≤ Real.exp ((-Real.pi * μ ^ 2 * t) * ((n : ℝ) + 1)) := Real.exp_le_exp.mpr hle
    _ = q ^ (n + 1) := by
        rw [hq, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- The Gaussian orbit sum converges on the open ray. -/
theorem deningerRayTheta_hasSum {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) :
    HasSum (fun n : ℕ => (1 : ℂ) *
        ((Real.exp (-Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ))
      (deningerGaussianRayTheta μ t) := by
  have hreal := deningerRayTheta_summable hμ ht
  have hcx : Summable fun n : ℕ =>
      ((Real.exp (-Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ) := by
    exact Complex.ofRealCLM.summable hreal
  have h := hcx.hasSum
  rw [deningerGaussianRayTheta]
  exact h.congr_fun fun n => by rw [one_mul]

/-- The Dirichlet weights of the orbit are summable to the right of one. -/
theorem deningerRay_summable_weights {μ : ℝ} (hμ : 0 < μ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(1 : ℂ)‖ / |μ * ((n : ℝ) + 1)| ^ s.re := by
  have hshift : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s.re := by
    have h := (Real.summable_one_div_nat_rpow (p := s.re)).mpr hs
    have h2 := (summable_nat_add_iff 1).mpr h
    exact h2.congr fun n => by push_cast; ring_nf
  have hfun : ∀ n : ℕ, ‖(1 : ℂ)‖ / |μ * ((n : ℝ) + 1)| ^ s.re
      = (μ ^ s.re)⁻¹ * (1 / ((n : ℝ) + 1) ^ s.re) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [norm_one, abs_of_pos (by positivity : (0 : ℝ) < μ * ((n : ℝ) + 1)),
      Real.mul_rpow (le_of_lt hμ) hn]
    field_simp
  exact (hshift.mul_left _).congr fun n => (hfun n).symm

/-- **The completed Mellin factor of the power orbit.**  The Mellin transform of the Gaussian
orbit sum is half the completed Gamma factor times the width power times zeta. -/
theorem deningerGaussianRaySum_mellin {μ : ℝ} (hμ : 0 < μ) {s : ℂ} (hs : 1 < s.re) :
    mellin (deningerGaussianRaySum μ) s
      = (Complex.Gammaℝ s / 2) * ((μ : ℂ) ^ (-s) * riemannZeta s) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ =>
      if μ * ((n : ℝ) + 1) = 0 then 0
      else (1 : ℂ) * ((Real.exp (-Real.pi * (μ * ((n : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ))
      (deningerGaussianRayTheta μ t) := by
    intro t ht
    have hne : ∀ n : ℕ, μ * ((n : ℝ) + 1) ≠ 0 := by
      intro n
      positivity
    exact (deningerRayTheta_hasSum hμ ht).congr_fun fun n => if_neg (hne n)
  have hmain := hasSum_mellin_pi_mul_sq (a := fun _ : ℕ => (1 : ℂ))
    (r := fun n : ℕ => μ * ((n : ℝ) + 1)) (F := deningerGaussianRayTheta μ) hs0 hF
    (deningerRay_summable_weights hμ hs)
  have hterm : ∀ n : ℕ,
      Complex.Gammaℝ s * (1 : ℂ) / ((|μ * ((n : ℝ) + 1)| : ℝ) : ℂ) ^ s
        = (Complex.Gammaℝ s * (μ : ℂ) ^ (-s)) * (1 / ((n : ℂ) + 1) ^ s) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have habs : |μ * ((n : ℝ) + 1)| = μ * ((n : ℝ) + 1) :=
      abs_of_pos (by positivity)
    have hsplit : (((μ * ((n : ℝ) + 1) : ℝ)) : ℂ) ^ s
        = (μ : ℂ) ^ s * (((n : ℝ) + 1 : ℝ) : ℂ) ^ s := by
      rw [Complex.ofReal_mul]
      exact mul_cpow_ofReal_nonneg (le_of_lt hμ) hn s
    have hμne : ((μ : ℂ)) ^ s ≠ 0 := by
      refine fun hzero => ?_
      rw [Complex.cpow_eq_zero_iff] at hzero
      exact (ne_of_gt hμ) (by exact_mod_cast hzero.1)
    have hnne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ s ≠ 0 := by
      refine fun hzero => ?_
      rw [Complex.cpow_eq_zero_iff] at hzero
      have : ((n : ℝ) + 1 : ℝ) = 0 := by exact_mod_cast hzero.1
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [habs, hsplit, Complex.cpow_neg]
    have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
    rw [hcast] at hnne ⊢
    field_simp
  have htsum : mellin (deningerGaussianRayTheta μ) (s / 2)
      = (Complex.Gammaℝ s * (μ : ℂ) ^ (-s)) * riemannZeta s := by
    rw [← hmain.tsum_eq]
    rw [tsum_congr hterm, tsum_mul_left, ← zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hcomp := mellin_comp_rpow (deningerGaussianRayTheta μ) s 2
  have hfun : (fun t : ℝ => deningerGaussianRayTheta μ (t ^ (2 : ℝ)))
      = deningerGaussianRaySum μ := by
    funext t
    rw [deningerGaussianRaySum_eq_theta]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hfun, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, htsum] at hcomp
  rw [hcomp]
  rw [show |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ by norm_num, Complex.real_smul]
  push_cast
  ring

end RaySum

section ComboRay

variable {N : ℕ} {c : Fin N → ℂ} {μ : Fin N → ℝ}

/-- **A family indexed by a finite type and a summation index sums fibrewise.** -/
theorem deningerHasSum_fintypeProd {ι β M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {g : ι → β → M} {S : ι → M} (h : ∀ i, HasSum (g i) (S i)) :
    HasSum (fun p : ι × β => g p.1 p.2) (∑ i, S i) := by
  have hslice : ∀ i : ι, HasSum (fun p : ι × β => if p.1 = i then g i p.2 else 0) (S i) := by
    intro i
    have hinj : Function.Injective (fun b : β => (i, b)) := by
      intro a b hab
      exact (Prod.mk.injEq _ _ _ _ ▸ hab).2
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro p hp
      have hne : p.1 ≠ i := by
        intro hcon
        exact hp ⟨p.2, by rw [← hcon]⟩
      simp [hne]
    · exact (h i).congr_fun fun b => by simp
  have hsum := hasSum_sum (s := (Finset.univ : Finset ι)) (fun i _ => hslice i)
  refine hsum.congr_fun fun p => ?_
  simp

/-- The Dirichlet term of one Gaussian orbit. -/
theorem deningerRayTerm_split {ν : ℝ} (hν : 0 < ν) (a s : ℂ) (n : ℕ) :
    Complex.Gammaℝ s * a / ((|ν * ((n : ℝ) + 1)| : ℝ) : ℂ) ^ s
      = (Complex.Gammaℝ s * a * (ν : ℂ) ^ (-s)) * (1 / ((n : ℂ) + 1) ^ s) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have habs : |ν * ((n : ℝ) + 1)| = ν * ((n : ℝ) + 1) := abs_of_pos (by positivity)
  have hsplit : (((ν * ((n : ℝ) + 1) : ℝ)) : ℂ) ^ s
      = (ν : ℂ) ^ s * (((n : ℝ) + 1 : ℝ) : ℂ) ^ s := by
    rw [Complex.ofReal_mul]
    exact mul_cpow_ofReal_nonneg (le_of_lt hν) hn s
  have hνne : ((ν : ℂ)) ^ s ≠ 0 := by
    refine fun hzero => ?_
    rw [Complex.cpow_eq_zero_iff] at hzero
    exact (ne_of_gt hν) (by exact_mod_cast hzero.1)
  have hnne : ((((n : ℝ) + 1 : ℝ)) : ℂ) ^ s ≠ 0 := by
    refine fun hzero => ?_
    rw [Complex.cpow_eq_zero_iff] at hzero
    have hz : ((n : ℝ) + 1 : ℝ) = 0 := by exact_mod_cast hzero.1
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [habs, hsplit, Complex.cpow_neg]
  have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = ((n : ℂ) + 1) := by push_cast; ring
  rw [hcast] at hnne ⊢
  field_simp

/-- The zeta series to the right of one. -/
theorem deningerZeta_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
  have h := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  have h2 := (summable_nat_add_iff 1).mpr h
  have h3 : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s :=
    h2.congr fun n => by push_cast; ring_nf
  have h4 := h3.hasSum
  rwa [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at h4

/-- The zeta-type orbit sum of a finite Gaussian combination. -/
noncomputable def deningerGaussianComboRay (c : Fin N → ℂ) (μ : Fin N → ℝ) (x : ℝ) : ℂ :=
  ∑ j, c j * deningerGaussianRaySum (μ j) x

/-- Its partner in the squared variable. -/
noncomputable def deningerGaussianComboTheta (c : Fin N → ℂ) (μ : Fin N → ℝ) (t : ℝ) : ℂ :=
  ∑ j, c j * deningerGaussianRayTheta (μ j) t

theorem deningerComboRay_eq_theta (c : Fin N → ℂ) (μ : Fin N → ℝ) (x : ℝ) :
    deningerGaussianComboRay c μ x = deningerGaussianComboTheta c μ (x ^ 2) := by
  rw [deningerGaussianComboRay, deningerGaussianComboTheta]
  exact Finset.sum_congr rfl fun j _ => by rw [deningerGaussianRaySum_eq_theta]

/-- **The completed Mellin transform of an endpoint-corrected Gaussian combination.**  The Gamma
factor and zeta come from the orbit, and the exponential polynomial of the combination is the
remaining Dirichlet coefficient. -/
theorem deningerGaussianComboRay_mellin (hμ : ∀ j, 0 < μ j) {s : ℂ} (hs : 1 < s.re) :
    mellin (deningerGaussianComboRay c μ) s
      = (Complex.Gammaℝ s / 2) * riemannZeta s * deningerExpPoly c μ s := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun p : Fin N × ℕ =>
      if μ p.1 * ((p.2 : ℝ) + 1) = 0 then 0
      else c p.1 * ((Real.exp (-Real.pi * (μ p.1 * ((p.2 : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ))
      (deningerGaussianComboTheta c μ t) := by
    intro t ht
    have hfib : ∀ j : Fin N, HasSum (fun n : ℕ =>
        if μ j * ((n : ℝ) + 1) = 0 then 0
        else c j * ((Real.exp (-Real.pi * (μ j * ((n : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ))
        (c j * deningerGaussianRayTheta (μ j) t) := by
      intro j
      have hne : ∀ n : ℕ, μ j * ((n : ℝ) + 1) ≠ 0 := by
        intro n
        have := hμ j
        positivity
      have hbase := (deningerRayTheta_hasSum (hμ j) ht).mul_left (c j)
      refine hbase.congr_fun fun n => ?_
      rw [if_neg (hne n), one_mul]
    exact deningerHasSum_fintypeProd hfib
  have hweights : Summable fun p : Fin N × ℕ =>
      ‖c p.1‖ / |μ p.1 * ((p.2 : ℝ) + 1)| ^ s.re := by
    have hfib : ∀ j : Fin N, HasSum (fun n : ℕ => ‖c j‖ / |μ j * ((n : ℝ) + 1)| ^ s.re)
        (∑' n : ℕ, ‖c j‖ / |μ j * ((n : ℝ) + 1)| ^ s.re) := by
      intro j
      have hbase := deningerRay_summable_weights (hμ j) hs
      have hscaled : Summable fun n : ℕ => ‖c j‖ / |μ j * ((n : ℝ) + 1)| ^ s.re := by
        refine (hbase.mul_left ‖c j‖).congr fun n => ?_
        rw [norm_one]
        ring
      exact hscaled.hasSum
    exact (deningerHasSum_fintypeProd hfib).summable
  have hmain := hasSum_mellin_pi_mul_sq (a := fun p : Fin N × ℕ => c p.1)
    (r := fun p : Fin N × ℕ => μ p.1 * ((p.2 : ℝ) + 1))
    (F := deningerGaussianComboTheta c μ) hs0 hF hweights
  have htarget : HasSum (fun p : Fin N × ℕ =>
      Complex.Gammaℝ s * c p.1 / ((|μ p.1 * ((p.2 : ℝ) + 1)| : ℝ) : ℂ) ^ s)
      (∑ j, Complex.Gammaℝ s * c j * (μ j : ℂ) ^ (-s) * riemannZeta s) := by
    refine deningerHasSum_fintypeProd (g := fun (j : Fin N) (n : ℕ) =>
      Complex.Gammaℝ s * c j / ((|μ j * ((n : ℝ) + 1)| : ℝ) : ℂ) ^ s) fun j => ?_
    have hbase := (deningerZeta_hasSum hs).mul_left
      (Complex.Gammaℝ s * c j * (μ j : ℂ) ^ (-s))
    exact hbase.congr_fun fun n => deningerRayTerm_split (hμ j) (c j) s n
  have hval : mellin (deningerGaussianComboTheta c μ) (s / 2)
      = Complex.Gammaℝ s * riemannZeta s * deningerExpPoly c μ s := by
    rw [hmain.unique htarget, deningerExpPoly, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcomp := mellin_comp_rpow (deningerGaussianComboTheta c μ) s 2
  have hfun : (fun t : ℝ => deningerGaussianComboTheta c μ (t ^ (2 : ℝ)))
      = deningerGaussianComboRay c μ := by
    funext t
    rw [deningerComboRay_eq_theta]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hfun, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num, hval] at hcomp
  rw [hcomp, show |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ by norm_num, Complex.real_smul]
  push_cast
  ring

end ComboRay

end RHTower
