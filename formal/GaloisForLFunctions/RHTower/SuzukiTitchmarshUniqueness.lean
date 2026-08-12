import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity
import GaloisForLFunctions.RHTower.TitchmarshZeroGap
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

noncomputable section

/-!
# Suzuki's exponential-type uniqueness lemma

This file formalizes Suzuki (2022), Lemma 2.1.  Its cited density input is Titchmarsh,
*The Theory of the Riemann Zeta-function*, Theorem 9.12.  Shrinking zero windows around every
sufficiently high ordinate give arbitrarily dense finite packets of distinct zeros of
`xi (1/2 - I*z)`.  Jensen's linear divisor bound for a nonzero entire function of finite
exponential type then forces the function to vanish identically.
-/

open Complex Set Metric Filter Topology

namespace RHTower

theorem tendsto_titchmarshZeroGapWidth_atTop_zero :
    Tendsto titchmarshZeroGapWidth atTop (nhds 0) := by
  have hL1 : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hL2 : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL1
  have hL3 : Tendsto (fun T : ℝ => Real.log (Real.log (Real.log T))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL2
  change Tendsto (fun T : ℝ => 1000 / Real.log (Real.log (Real.log T))) atTop (nhds 0)
  exact tendsto_const_nhds.div_atTop hL3

/-- Uniform form of Titchmarsh's theorem with any prescribed positive window width. -/
theorem exists_uniform_riemannZeta_zero_window {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℝ, δ + 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ |ρ.im - T| < δ := by
  have hsmall : ∀ᶠ T : ℝ in atTop, titchmarshZeroGapWidth T < δ :=
    tendsto_titchmarshZeroGapWidth_atTop_zero (Iio_mem_nhds hδ)
  have hboth := eventually_exists_riemannZeta_zero_titchmarsh.and hsmall
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hboth
  refine ⟨max T₁ (δ + 1), le_max_right _ _, ?_⟩
  intro T hT
  obtain ⟨⟨ρ, hρzero, hρwidth⟩, hwidthδ⟩ := hT₁ T ((le_max_left _ _).trans hT)
  exact ⟨ρ, hρzero, hρwidth.trans hwidthδ⟩

/-- Original zeta coordinate transported to Suzuki's centered variable
`xi (1/2 - I*z)`. -/
def suzukiCenteredZeroCoordinate (ρ : ℂ) : ℂ :=
  I * (ρ - 1 / 2)

theorem suzukiCenteredZeroCoordinate_injective :
    Function.Injective suzukiCenteredZeroCoordinate := by
  intro ρ σ h
  unfold suzukiCenteredZeroCoordinate at h
  have h' : ρ - 1 / 2 = σ - 1 / 2 := by
    exact mul_left_cancel₀ I_ne_zero h
  exact sub_left_inj.mp h'

theorem one_half_sub_I_mul_suzukiCenteredZeroCoordinate (ρ : ℂ) :
    1 / 2 - I * suzukiCenteredZeroCoordinate ρ = ρ := by
  unfold suzukiCenteredZeroCoordinate
  rw [← mul_assoc, I_mul_I]
  ring

/-- `N` disjoint Titchmarsh windows produce `N` distinct Suzuki-centered Xi zeros, all in one
explicit linearly growing disc. -/
theorem exists_suzukiCentered_zero_packet
    {δ T₀ : ℝ} (hδ : 0 < δ) (hT₀ : δ + 1 ≤ T₀)
    (hwindow : ∀ T : ℝ, T₀ ≤ T →
      ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ |ρ.im - T| < δ)
    (N : ℕ) :
    ∃ z : Fin N → ℂ, Function.Injective z ∧
      (∀ i, xi (1 / 2 - I * z i) = 0) ∧
      ∀ i, ‖z i‖ ≤ T₀ + 3 * δ * N + δ + 2 := by
  let target : Fin N → ℝ := fun i => T₀ + 3 * δ * (i : ℝ)
  have htarget (i : Fin N) : T₀ ≤ target i := by
    dsimp only [target]
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hδi : 0 ≤ δ * (i : ℝ) := mul_nonneg hδ.le hi0
    nlinarith
  have hex (i : Fin N) :
      ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ |ρ.im - target i| < δ :=
    hwindow (target i) (htarget i)
  let ρ : Fin N → ℂ := fun i => Classical.choose (hex i)
  have hρzero (i : Fin N) : riemannZeta (ρ i) = 0 :=
    (Classical.choose_spec (hex i)).1
  have hρnear (i : Fin N) : |(ρ i).im - target i| < δ :=
    (Classical.choose_spec (hex i)).2
  let z : Fin N → ℂ := fun i => suzukiCenteredZeroCoordinate (ρ i)
  have hρinj : Function.Injective ρ := by
    intro i j hij
    by_contra hijFin
    rcases lt_or_gt_of_ne hijFin with hijlt | hjilt
    · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hijlt
      have hi := (abs_lt.mp (hρnear i)).2
      have hj := (abs_lt.mp (hρnear j)).1
      rw [hij] at hi
      dsimp only [target] at hi hj
      nlinarith
    · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hjilt
      have hj := (abs_lt.mp (hρnear j)).2
      have hi := (abs_lt.mp (hρnear i)).1
      rw [← hij] at hj
      dsimp only [target] at hi hj
      nlinarith
  have hzinj : Function.Injective z :=
    suzukiCenteredZeroCoordinate_injective.comp hρinj
  have hxi (i : Fin N) : xi (1 / 2 - I * z i) = 0 := by
    have himpos : 0 < (ρ i).im := by
      have hi := (abs_lt.mp (hρnear i)).1
      dsimp only [target] at hi
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
      have hterm : 0 ≤ 3 * δ * (i : ℝ) := by positivity
      linarith
    have htriv : ∀ n : ℕ, ρ i ≠ -(2 * ((n : ℂ) + 1)) := by
      intro n hn
      have him := congrArg Complex.im hn
      simp at him
      linarith
    have hxizero :=
      xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hρzero i, htriv⟩
    dsimp only [z]
    rw [one_half_sub_I_mul_suzukiCenteredZeroCoordinate]
    exact hxizero
  have hzbound (i : Fin N) : ‖z i‖ ≤ T₀ + 3 * δ * N + δ + 2 := by
    have himpos : 0 < (ρ i).im := by
      have hi := (abs_lt.mp (hρnear i)).1
      dsimp only [target] at hi
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
      have hterm : 0 ≤ 3 * δ * (i : ℝ) := by positivity
      linarith
    have htriv : ∀ n : ℕ, ρ i ≠ -(2 * ((n : ℂ) + 1)) := by
      intro n hn
      have him := congrArg Complex.im hn
      simp at him
      linarith
    obtain ⟨hre0, hre1⟩ := riemannZeta_zero_re_mem_Ioo (hρzero i) htriv
    have himUpper : (ρ i).im < T₀ + 3 * δ * N + δ := by
      have hi := (abs_lt.mp (hρnear i)).2
      have hindex : ((i : ℕ) : ℝ) ≤ N := by
        exact_mod_cast (Nat.le_of_lt i.isLt)
      dsimp only [target] at hi
      nlinarith
    have hρnorm : ‖ρ i‖ ≤ 1 + (ρ i).im := by
      have hdecomp : ρ i = (((ρ i).re : ℝ) : ℂ) + (((ρ i).im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      calc
        ‖ρ i‖ = ‖(((ρ i).re : ℝ) : ℂ) + (((ρ i).im : ℝ) : ℂ) * I‖ :=
          congrArg norm hdecomp
        ‖(((ρ i).re : ℝ) : ℂ) + (((ρ i).im : ℝ) : ℂ) * I‖
            ≤ ‖(((ρ i).re : ℝ) : ℂ)‖ + ‖(((ρ i).im : ℝ) : ℂ) * I‖ := norm_add_le _ _
        _ = |(ρ i).re| + |(ρ i).im| := by simp
        _ = (ρ i).re + (ρ i).im := by rw [abs_of_pos hre0, abs_of_pos himpos]
        _ ≤ 1 + (ρ i).im := by linarith
    have hcoord : ‖suzukiCenteredZeroCoordinate (ρ i)‖ ≤ ‖ρ i‖ + 1 / 2 := by
      rw [suzukiCenteredZeroCoordinate, norm_mul, norm_I, one_mul]
      calc
        ‖ρ i - 1 / 2‖ ≤ ‖ρ i‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
        _ = ‖ρ i‖ + 1 / 2 := by norm_num
    dsimp only [z]
    linarith
  exact ⟨z, hzinj, hxi, hzbound⟩

/-- Suzuki (2022), Lemma 2.1, in explicit finite-exponential-type form. -/
theorem suzuki_exponentialType_uniqueness
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖))
    (hvalues : ∀ z : ℂ, xi (1 / 2 - I * z) = 0 → F z = a) :
    F = fun _ => a := by
  let g : ℂ → ℂ := fun z => F z - a
  have hgdiff : Differentiable ℂ g := by
    dsimp only [g]
    fun_prop
  have hC' : 1 ≤ C + ‖a‖ := by linarith [norm_nonneg a]
  have hggrow : ∀ z : ℂ, ‖g z‖ ≤ (C + ‖a‖) * Real.exp (A * ‖z‖) := by
    intro z
    have hexp : 1 ≤ Real.exp (A * ‖z‖) := by
      rw [Real.one_le_exp_iff]
      positivity
    have haexp : ‖a‖ ≤ ‖a‖ * Real.exp (A * ‖z‖) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (norm_nonneg a)
    calc
      ‖g z‖ = ‖F z - a‖ := rfl
      _ ≤ ‖F z‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ C * Real.exp (A * ‖z‖) + ‖a‖ * Real.exp (A * ‖z‖) :=
        add_le_add (hgrow z) haexp
      _ = (C + ‖a‖) * Real.exp (A * ‖z‖) := by ring
  by_contra hFconst
  have hgne : g ≠ 0 := by
    intro hg
    apply hFconst
    funext z
    have hz := congrFun hg z
    dsimp only [g] at hz
    exact sub_eq_zero.mp hz
  have hgc : ∃ c : ℂ, g c ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hgne (funext hc)
  obtain ⟨c, hgc⟩ := hgc
  obtain ⟨K, hK, hcount⟩ :=
    exponentialType_zeroCount_linear hgdiff hgc hA hC' hggrow
  let δ : ℝ := 1 / (12 * (K + 1))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  obtain ⟨T₀, hT₀, hwindow⟩ := exists_uniform_riemannZeta_zero_window hδ
  let base : ℝ := 1 + ‖c‖ + T₀ + δ + 2
  have hbase : 0 < base := by
    dsimp only [base]
    have hT₀pos : 0 < T₀ := by linarith
    positivity
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (2 * K * base)
  have hNposReal : 0 < (N : ℝ) := by
    have : 0 < 2 * K * base := by positivity
    exact this.trans hN
  have hNpos : 0 < N := by exact_mod_cast hNposReal
  obtain ⟨z, hzinj, hxizero, hzbound⟩ :=
    exists_suzukiCentered_zero_packet hδ hT₀ hwindow N
  let r : ℝ := ‖c‖ + T₀ + 3 * δ * N + δ + 2
  have hr : 1 ≤ r := by
    dsimp only [r]
    have hT₀pos : 0 < T₀ := by linarith
    have hterm : 0 ≤ 3 * δ * (N : ℝ) := by positivity
    linarith [norm_nonneg c]
  have hball : ∀ i ∈ (Finset.univ : Finset (Fin N)), z i ∈ closedBall c r := by
    intro i _
    rw [mem_closedBall_iff_norm]
    calc
      ‖z i - c‖ ≤ ‖z i‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ (T₀ + 3 * δ * N + δ + 2) + ‖c‖ := by
        simpa [add_comm] using add_le_add_right (hzbound i) ‖c‖
      _ = r := by dsimp only [r]; ring
  have hgzero : ∀ i ∈ (Finset.univ : Finset (Fin N)), g (z i) = 0 := by
    intro i _
    dsimp only [g]
    rw [hvalues (z i) (hxizero i)]
    exact sub_self a
  have hdivInt := card_le_sum_divisor_of_finite_zeros hgdiff hgc
    (Finset.univ : Finset (Fin N)) z
    (fun _ _ _ _ hij => hzinj hij) hball hgzero
  have hdivReal : (N : ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor g (closedBall c r)) u) : ℝ) := by
    norm_num at hdivInt ⊢
    exact_mod_cast hdivInt
  have hupper := hcount r hr
  have hcoef : 3 * K * δ ≤ 1 / 4 := by
    have hden : 0 < 12 * (K + 1) := by positivity
    dsimp only [δ]
    rw [show 3 * K * (1 / (12 * (K + 1))) =
      (3 * K) / (12 * (K + 1)) by ring, div_le_iff₀ hden]
    nlinarith
  have hbasePart : K * base < (N : ℝ) / 2 := by nlinarith
  have hslopePart : K * (3 * δ * N) ≤ (N : ℝ) / 4 := by
    calc
      K * (3 * δ * N) = (3 * K * δ) * (N : ℝ) := by ring
      _ ≤ (1 / 4 : ℝ) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N)
      _ = (N : ℝ) / 4 := by ring
  have hrSplit : 1 + r = base + 3 * δ * N := by
    dsimp only [r, base]
    ring
  have htooSmall : K * (1 + r) < (N : ℝ) := by
    rw [hrSplit]
    nlinarith
  exact (not_lt_of_ge (hdivReal.trans hupper)) htooSmall

/-- Closed existential-growth formulation of Suzuki's Lemma 2.1. -/
theorem suzuki_lemma_two_one
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ)
    (hexponentialType : ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧
      ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (A * ‖z‖))
    (hvalues : ∀ z : ℂ, xi (1 / 2 - I * z) = 0 → F z = a) :
    F = fun _ => a := by
  obtain ⟨A, C, hA, hC, hgrow⟩ := hexponentialType
  exact suzuki_exponentialType_uniqueness hF a hA hC hgrow hvalues

end RHTower
