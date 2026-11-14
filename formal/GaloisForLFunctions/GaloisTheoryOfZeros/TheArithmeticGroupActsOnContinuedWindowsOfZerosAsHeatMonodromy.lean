import GaloisForLFunctions.GaloisTheoryOfZeros.TheArithmeticGroupIsAHeatMonodromyOnFiniteWindowsButNotOnAFibre
import GaloisForLFunctions.GaloisTheoryOfZeros.EveryTurnIsAnInvolutionThatFlipsAsManyPairsAsTheOrderOfTheCentreValue

/-!
# The arithmetic group acts on continued windows of zeros as heat monodromy

The zeros of ξ are the zeros of the heat family at the time `0`, in the centred coordinate
`z(ρ) = (ρ − ½)(−i)`. Every zero `z₀` of `H_0`, simple or not, is a collision of some order
`m ≥ 1`; a Hermite sheet `s ↦ Z(s)` through it gives zeros `Z(√t)` of `H_t` for small real
`t > 0`, tending to `z₀`. This module specializes the arithmetic group `G = Gal(E/B)` along these
continuations.

* **Continuation** (`exists_continuation_of_zero`). Every zero of `H_0` is the limit, as
  `t → 0⁺`, of zeros of `H_t`.
* **Specialization on a window** (`exists_forwardMonodromy_eq_on_continued_window`). For finitely
  many zeros `s_i` of ξ in distinct reflection pairs and `σ ∈ G` there are continuations
  `w_i(t) → z(s_i)`, `w'_i(t) → z(σ s_i)` as `t → 0⁺` and `t₀ > 0` such that at every real time
  `0 < t < t₀` off the branch times some `g ∈ G₊(t)` carries each `w_i(t)` to `w'_i(t)`.

So on every finite window of zeros the arithmetic action is the limit at the time `0` of forward
heat monodromies; the window, and with it `t₀`, may grow without bound, while on a whole fibre no
such identification exists.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower RHTower.DeBruijn Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local instance : IsGalois B E := ⟨⟩

/-- The centred coordinate of a zero of ξ is a zero of the heat family at the time `0`. -/
theorem complexHeat_zero_xiSpectralPointSupport (ρ : XiDivisorSupport) :
    complexHeat 0 (xiSpectralPointSupport ρ) = 0 := by
  have h0 := complexHeat_ofReal 0 (xiSpectralPointSupport ρ)
  rw [Complex.ofReal_zero] at h0
  rw [h0, riemannHeat_zero]
  have h : 1 / 2 + I * xiSpectralPointSupport ρ = (ρ : ℂ) := by
    rw [xiSpectralPointSupport]
    linear_combination ((1 : ℂ) / 2 - ρ) * Complex.I_sq
  rw [h]
  exact xi_divisorSupport_eq_zero ρ

theorem xiSpectralPointSupport_injective : Function.Injective xiSpectralPointSupport := by
  intro ρ ρ' h
  apply Subtype.ext
  unfold xiSpectralPointSupport at h
  linear_combination I * h + ((ρ : ℂ) - ρ') * Complex.I_sq

/-- **Continuation.** A zero of `H_0` is the limit of zeros of `H_t` as `t → 0⁺`: follow a Hermite
sheet of the collision at `(0, z₀)` along `s = √t`. -/
theorem exists_continuation_of_zero {z₀ : ℂ} (h0 : complexHeat 0 z₀ = 0) :
    ∃ w : ℝ → ℂ, Tendsto w (𝓝[>] 0) (𝓝 z₀) ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, complexHeat (t : ℂ) (w t) = 0 := by
  obtain ⟨m, hm, hc⟩ := exists_isCollision h0
  have hne : ({ρ : ℂ | heatModelFwd m ρ = 0}).ncard ≠ 0 := by
    rw [ncard_setOf_heatModelFwd_eq_zero]
    omega
  obtain ⟨ρ, hρ⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨ε, hε, hcont, hzero⟩ := hc.exists_ball_sheet hρ
  have hsq : Tendsto (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.comp Real.continuous_sqrt).tendsto (0 : ℝ)
    simp only [Function.comp, Real.sqrt_zero, Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hca : ContinuousAt (collisionZero 0 z₀ m ρ) 0 :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  refine ⟨fun t => collisionZero 0 z₀ m ρ (Real.sqrt t : ℂ), ?_, ?_⟩
  · have h := hca.tendsto.comp hsq
    rwa [collisionZero_zero] at h
  · filter_upwards [hsq (Metric.ball_mem_nhds 0 hε), self_mem_nhdsWithin] with t ht htpos
    have h := (hzero _ ht).1
    rwa [zero_add, ← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt htpos)] at h

/-- **Specialization on a window.** The action of an arithmetic automorphism on finitely many
zeros of ξ in distinct reflection pairs is realized, along continuations of the zeros from the
time `0`, by forward heat monodromies at all small real times off the branch times. -/
theorem exists_forwardMonodromy_eq_on_continued_window {ι : Type*} [Finite ι]
    (s : ι → XiDivisorSupport) (σ : G)
    (hs : ∀ i j, i ≠ j → s j ≠ s i ∧ s j ≠ xiZeroReflectEquiv (s i)) :
    ∃ w w' : ι → ℝ → ℂ, (∀ i, Tendsto (w i) (𝓝[>] 0) (𝓝 (xiSpectralPointSupport (s i)))) ∧
      (∀ i, Tendsto (w' i) (𝓝[>] 0)
        (𝓝 (xiSpectralPointSupport (primeTraceZeroMap σ (s i))))) ∧
      ∃ t₀ > 0, ∀ t : ℝ, ∀ ht : 0 < (t : ℂ).re, t < t₀ → ∀ hb : (t : ℂ) ∉ branchTimes,
        ∃ hw : ∀ i, complexHeat t (w i t) = 0, ∃ hw' : ∀ i, complexHeat t (w' i t) = 0,
          ∃ g ∈ forwardMonodromy (t : ℂ) ht hb, ∀ i, g ⟨w i t, hw i⟩ = ⟨w' i t, hw' i⟩ := by
  have hσ : Function.Injective (primeTraceZeroMap σ) := (primeTraceZeroPermutation σ).injective
  choose w hw hw0 using fun i =>
    exists_continuation_of_zero (complexHeat_zero_xiSpectralPointSupport (s i))
  choose w' hw' hw0' using fun i =>
    exists_continuation_of_zero
      (complexHeat_zero_xiSpectralPointSupport (primeTraceZeroMap σ (s i)))
  -- distinct points that are not opposite stay so for small times
  have hsep : ∀ (v : ι → ℝ → ℂ) (a : ι → XiDivisorSupport),
      (∀ i, Tendsto (v i) (𝓝[>] 0) (𝓝 (xiSpectralPointSupport (a i)))) →
      (∀ i j, i ≠ j → a j ≠ a i ∧ a j ≠ xiZeroReflectEquiv (a i)) →
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i j, i ≠ j → v j t ≠ v i t ∧ v j t ≠ -v i t := by
    intro v a hv ha
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    have hne1 : xiSpectralPointSupport (a j) - xiSpectralPointSupport (a i) ≠ 0 :=
      sub_ne_zero.2 fun e => (ha i j hij).1 (xiSpectralPointSupport_injective e)
    have hne2 : xiSpectralPointSupport (a j) + xiSpectralPointSupport (a i) ≠ 0 := by
      intro e
      apply (ha i j hij).2
      apply xiSpectralPointSupport_injective
      rw [xiSpectralPointSupport_reflect]
      linear_combination e
    have e1 := ((hv j).sub (hv i)).eventually_ne hne1
    have e2 := ((hv j).add (hv i)).eventually_ne hne2
    filter_upwards [e1, e2] with t ht1 ht2
    exact fun _ => ⟨fun e => ht1 (by rw [e, sub_self]), fun e => ht2 (by rw [e, neg_add_cancel])⟩
  have hs' : ∀ i j, i ≠ j → primeTraceZeroMap σ (s j) ≠ primeTraceZeroMap σ (s i) ∧
      primeTraceZeroMap σ (s j) ≠ xiZeroReflectEquiv (primeTraceZeroMap σ (s i)) := by
    intro i j hij
    rw [← primeTraceZeroMap_reflection]
    exact ⟨fun e => (hs i j hij).1 (hσ e), fun e => (hs i j hij).2 (hσ e)⟩
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ((∀ i, complexHeat (t : ℂ) (w i t) = 0) ∧
      ∀ i, complexHeat (t : ℂ) (w' i t) = 0) ∧
      (∀ i j, i ≠ j → w j t ≠ w i t ∧ w j t ≠ -w i t) ∧
      ∀ i j, i ≠ j → w' j t ≠ w' i t ∧ w' j t ≠ -w' i t :=
    ((eventually_all.2 hw0).and (eventually_all.2 hw0')).and
      ((hsep w s hw hs).and (hsep w' _ hw' hs'))
  obtain ⟨t₀, ht₀, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨w, w', hw, hw', t₀, ht₀, fun t ht htt hb => ?_⟩
  have htpos : 0 < t := by simpa using ht
  obtain ⟨⟨hz, hz'⟩, hd, hd'⟩ := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htt) (Set.mem_Ioi.2 htpos)
  refine ⟨hz, hz', exists_mem_forwardMonodromy_forall_apply_eq ht hb
    (p := fun i => ⟨w i t, hz i⟩) (q := fun i => ⟨w' i t, hz' i⟩)
    (fun i j hij => ⟨fun e => (hd i j hij).1 (congrArg Subtype.val e),
      fun e => (hd i j hij).2 (congrArg Subtype.val e)⟩)
    (fun i j hij => ⟨fun e => (hd' i j hij).1 (congrArg Subtype.val e),
      fun e => (hd' i j hij).2 (congrArg Subtype.val e)⟩)⟩

end GaloisForLFunctions.GaloisTheoryOfZeros
