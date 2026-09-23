import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Convex.Contractible

/-!
# Holomorphic branches of the logarithm and the square root

On a simply connected open subset of the plane a nonvanishing holomorphic function has a
holomorphic logarithm, hence a holomorphic square root, and the square root can be normalised at any
point where the function is one.  Mathlib supplies the continuous branch; the upgrade to holomorphy
is local: near a point the continuous branch differs from the principal logarithm of the normalised
function by an element of `2πiℤ`, and a continuous function into that discrete set which vanishes at
the point vanishes nearby.
-/

open Set Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A convex nonempty subset of the plane is simply connected. -/
theorem isSimplyConnected_of_convex {s : Set ℂ} (hs : Convex ℝ s) (hne : s.Nonempty) :
    IsSimplyConnected s := by
  haveI : ContractibleSpace s := hs.contractibleSpace hne
  exact SimplyConnectedSpace.ofContractible _

/-- **A continuous logarithm of a holomorphic nonvanishing function is holomorphic.** -/
theorem differentiableAt_of_exp_comp {U : Set ℂ} (hU : IsOpen U) {g f : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hfc : ContinuousOn f U)
    (hexp : ∀ z ∈ U, Complex.exp (f z) = g z) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    DifferentiableAt ℂ f z₀ := by
  have hUnhds : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hgz₀ : g z₀ ≠ 0 := by
    rw [← hexp z₀ hz₀]
    exact Complex.exp_ne_zero _
  have hgat : DifferentiableAt ℂ g z₀ := hg.differentiableAt hUnhds
  have hqat : DifferentiableAt ℂ (fun z => g z / g z₀) z₀ := hgat.div_const _
  have hq₀ : g z₀ / g z₀ = 1 := div_self hgz₀
  have hqslit : ∀ᶠ z in nhds z₀, g z / g z₀ ∈ Complex.slitPlane := by
    refine hqat.continuousAt (Complex.isOpen_slitPlane.mem_nhds ?_)
    rw [hq₀]
    exact Complex.one_mem_slitPlane
  have hcomp : DifferentiableAt ℂ (fun z => Complex.log (g z / g z₀)) z₀ := by
    refine hqat.clog ?_
    rw [hq₀]
    exact Complex.one_mem_slitPlane
  have hhat : DifferentiableAt ℂ (fun z => f z₀ + Complex.log (g z / g z₀)) z₀ :=
    hcomp.const_add (f z₀)
  have hhz₀ : f z₀ + Complex.log (g z₀ / g z₀) = f z₀ := by
    rw [hq₀, Complex.log_one, add_zero]
  have hfat : ContinuousAt f z₀ := hfc.continuousAt hUnhds
  have hnormcont : ContinuousAt (fun z => ‖f z - (f z₀ + Complex.log (g z / g z₀))‖) z₀ :=
    (hfat.sub hhat.continuousAt).norm
  have hval0 : ‖f z₀ - (f z₀ + Complex.log (g z₀ / g z₀))‖ = 0 := by
    rw [hhz₀, sub_self, norm_zero]
  have hsmall : ∀ᶠ z in nhds z₀, ‖f z - (f z₀ + Complex.log (g z / g z₀))‖ < 2 * Real.pi := by
    have hlt : ‖f z₀ - (f z₀ + Complex.log (g z₀ / g z₀))‖ < 2 * Real.pi := by
      rw [hval0]
      positivity
    exact hnormcont.eventually (eventually_lt_nhds hlt)
  have heq : ∀ᶠ z in nhds z₀, f z = f z₀ + Complex.log (g z / g z₀) := by
    filter_upwards [hUnhds, hqslit, hsmall] with z hzU hzslit hzsmall
    have hqne : g z / g z₀ ≠ 0 := Complex.slitPlane_ne_zero hzslit
    have hexph : Complex.exp (f z₀ + Complex.log (g z / g z₀)) = g z := by
      rw [Complex.exp_add, Complex.exp_log hqne, hexp z₀ hz₀, mul_comm,
        div_mul_cancel₀ _ hgz₀]
    have hexpeq : Complex.exp (f z) = Complex.exp (f z₀ + Complex.log (g z / g z₀)) := by
      rw [hexp z hzU, hexph]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpeq
    have hsub : f z - (f z₀ + Complex.log (g z / g z₀)) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hn]; ring
    have hnorm : ‖f z - (f z₀ + Complex.log (g z / g z₀))‖ = |(n : ℝ)| * (2 * Real.pi) := by
      rw [hsub, norm_mul, norm_mul, norm_mul]
      simp [abs_of_nonneg Real.pi_pos.le]
    have hn0 : n = 0 := by
      by_contra hcon
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have hz1 : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hcon)
        have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hz1
        simpa using this
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [hnorm] at hzsmall
      nlinarith [hzsmall, h1, hpi]
    rw [hn0] at hn
    simpa using hn
  exact hhat.congr_of_eventuallyEq heq

/-- **A holomorphic logarithm on a simply connected domain.** -/
theorem exists_differentiableOn_exp_eq {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (h0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ ∀ z ∈ U, Complex.exp (f z) = g z := by
  have hnot : (0 : ℂ) ∉ g '' U := by
    rintro ⟨z, hz, hgz⟩
    exact h0 z hz hgz
  obtain ⟨f, hfc, hfe⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn hnot
  have hval : ∀ z ∈ U, Complex.exp (f z) = g z := fun z hz => hfe hz
  refine ⟨f, fun z hz => ?_, hval⟩
  exact (differentiableAt_of_exp_comp hUo hg hfc hval hz).differentiableWithinAt

/-- **A holomorphic square root on a simply connected domain**, normalised at a point where the
function is one. -/
theorem exists_differentiableOn_sq_eq {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (h0 : ∀ z ∈ U, g z ≠ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hg1 : g z₀ = 1) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ (∀ z ∈ U, f z ^ (2 : ℕ) = g z) ∧ f z₀ = 1
      ∧ ∀ z ∈ U, f z ≠ 0 := by
  obtain ⟨L, hL, hLe⟩ := exists_differentiableOn_exp_eq hUo hUc hg h0
  set e : ℂ → ℂ := fun z => Complex.exp (L z / 2) with he
  have hesq : ∀ z ∈ U, e z ^ (2 : ℕ) = g z := by
    intro z hz
    rw [he]
    have : Complex.exp (L z / 2) ^ (2 : ℕ) = Complex.exp (L z / 2 + L z / 2) := by
      rw [Complex.exp_add, sq]
    rw [this]
    have hhalf : L z / 2 + L z / 2 = L z := by ring
    rw [hhalf, hLe z hz]
  have hene : ∀ z, e z ≠ 0 := fun z => Complex.exp_ne_zero _
  have he₀sq : e z₀ ^ (2 : ℕ) = 1 := by rw [hesq z₀ hz₀, hg1]
  refine ⟨fun z => e z / e z₀, ?_, ?_, ?_, ?_⟩
  · exact (fun z hz => (((hL.differentiableAt (hUo.mem_nhds hz)).div_const 2).cexp.div_const
      (e z₀)).differentiableWithinAt)
  · intro z hz
    rw [div_pow, hesq z hz, he₀sq, div_one]
  · show e z₀ / e z₀ = 1
    exact div_self (hene z₀)
  · intro z _
    exact div_ne_zero (hene z) (hene z₀)

end

end GaloisForLFunctions.HTGeometry
