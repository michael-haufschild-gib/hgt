import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks
import GaloisForLFunctions.RHTower.PhotonicLosslessProductPortRH
import GaloisForLFunctions.RHTower.XiOrderedPrimeDeterminantNormalForm
import GaloisForLFunctions.HTGeometry.PolyaClassPhaseRigidity

/-!
# The PTR producer crystallises above its zero depth

Write `A_h(x) = Re Ξ(x + ih) = cos(hD)Ξ(x)` for the PTR producer at depth `h`.

**Theorem** (`cosProducer_gap_rigidity`). Suppose every spectral point `γ` of `Ξ` has
`Im γ ≤ σ < h`. Then any three consecutive real zeros `a < b < c` of `A_h` satisfy
`c − b ≤ (b − a) e^{2(c − a)/(h − σ)}` and `b − a ≤ (c − b) e^{2(c − a)/(h − σ)}`.

**Proof.** The shift `G(z) = Ξ(z + iσ)` is a locally uniform limit of the ball truncations
`Ξ(0) ∏_{|γ| ≤ m}(1 − (z + iσ)/γ)`, whose roots `γ − iσ` lie in `Im ≤ 0`. So `G` is lower Pólya and
`A_h(x) = Re G(x + i(h − σ))`. The phase speed of `G` at depth `h − σ` is a positive Poisson sum,
log-Lipschitz with constant `2/(h − σ)` (`LowerPolyaClass.phaseSpeed_le_exp_mul`). It is positive
everywhere, since otherwise the phase is constant and `A_h` vanishes on an interval. Gap rigidity of
the phase (`gap_rigidity_of_phase`) concludes.

**Corollaries.**
- `cosProducer_gap_rigidity_of_half_lt`: unconditionally, for `h > 1/2`, at scale `h − 1/2`.
- `cosProducer_gap_rigidity_of_rh`: under RH, for every `h > 0`, at scale `h`.

With the critical-scale anti-crystal law (`exists_eventually_not_rigidWindow_critical`), this is a
melting law. Under RH the producer zeros are rigid at scale `≍ h` at every depth `h > 0`, while the
zeros of `Ξ = A_0` are not `C/log T`-rigid. The PTR producer family melts at depth `Θ(1/log T)`,
which is where PTR's open core sits.
-/

noncomputable section

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry (LowerPolyaClass phaseSpeed exists_phase_rep
  gap_rigidity_of_phase)

namespace RHTower

/-- **The shifted Xi function is lower Pólya** when all spectral points have `Im γ ≤ σ`. -/
theorem lowerPolyaClass_XiC_shift {σ : ℝ} (hσ : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≤ σ) :
    LowerPolyaClass (fun z => XiC (z + σ * I)) := by
  set p : ℕ → ℂ[X] := fun m =>
    C (XiC 0) * ∏ q ∈ xiZeroBall m, (1 - C (xiSpectralPoint q)⁻¹ * (X + C ((σ : ℂ) * I))) with hp
  have heval : ∀ m z, (p m).eval z =
      XiC 0 * ∏ q ∈ xiZeroBall m, (1 - (z + σ * I) / xiSpectralPoint q) := by
    intro m z
    simp only [hp, eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_add, eval_X]
    congr 1
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [div_eq_inv_mul]
  refine ⟨p, fun m r hr => ?_, ?_⟩
  · -- the roots are `γ − iσ`
    have hr0 : (p m).eval r = 0 := (Polynomial.isRoot_of_mem_roots hr).eq_zero
    rw [heval, mul_eq_zero, Finset.prod_eq_zero_iff] at hr0
    rcases hr0 with h0 | ⟨q, _, hq⟩
    · exact absurd h0 XiC_zero_ne_zero
    · have hγ := xiSpectralPoint_ne_zero q
      have : r + σ * I = xiSpectralPoint q := by
        rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hγ] at hq; exact hq
      have him := congrArg Complex.im this
      simp at him
      linarith [hσ q]
  · -- convergence
    have hconv := tendstoLocallyUniformly_prod_xiZeroBall
    have hshift : TendstoLocallyUniformly
        (fun (m : ℕ) (z : ℂ) => ∏ q ∈ xiZeroBall m, (1 - (z + σ * I) / xiSpectralPoint q))
        (fun z => xiCanonicalProduct (z + σ * I)) atTop :=
      hconv.comp (fun z => z + σ * I) (continuous_id.add continuous_const)
    have hc : TendstoLocallyUniformly (fun (_ : ℕ) (_ : ℂ) => XiC 0) (fun _ => XiC 0) atTop :=
      fun u hu x => ⟨univ, univ_mem, Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
    have hcont : Continuous fun z => xiCanonicalProduct (z + σ * I) :=
      hshift.continuous (Eventually.of_forall fun m => by fun_prop).frequently
    have hmul := hc.mul₀ hshift continuous_const hcont
    refine (hmul.congr_right ?_).congr fun m z => (heval m z).symm
    intro z
    have h := congrFun XiC_eq_constant_mul_canonicalProduct (z + σ * I)
    simp only [Pi.mul_apply] at h
    exact h.symm

/-- `A_h(x) = Re Ξ(x + ih)` is a real zero exactly when the producer vanishes. -/
theorem cosProducer_ofReal (h x : ℝ) :
    cosProducer h x = (((XiC ((x : ℂ) + h * I)).re : ℝ) : ℂ) := by
  unfold cosProducer
  have hconj : XiC ((x : ℂ) - h * I) = (starRingEnd ℂ) (XiC ((x : ℂ) + h * I)) := by
    rw [← XiC_conj']
    congr 1
    simp [map_add, Complex.conj_ofReal]
    ring
  rw [hconj, Complex.add_conj]
  push_cast
  ring

/-- **Gap rigidity of the producer zeros.** -/
theorem cosProducer_gap_rigidity {σ h : ℝ}
    (hσ : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≤ σ) (hσh : σ < h) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (ha : cosProducer h a = 0) (hb : cosProducer h b = 0)
    (hc : cosProducer h c = 0) (hno1 : ∀ x ∈ Ioo a b, cosProducer h x ≠ 0)
    (hno2 : ∀ x ∈ Ioo b c, cosProducer h x ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / (h - σ)) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / (h - σ)) := by
  set G : ℂ → ℂ := fun z => XiC (z + σ * I) with hG
  have hGc := lowerPolyaClass_XiC_shift hσ
  have hd : 0 < h - σ := by linarith
  have hshift : ∀ t : ℝ, G ((t : ℂ) + ((h - σ : ℝ) : ℂ) * I) = XiC ((t : ℂ) + h * I) := by
    intro t; simp only [hG]; congr 1; push_cast; ring
  have hne : ∀ t : ℝ, G ((t : ℂ) + ((h - σ : ℝ) : ℂ) * I) ≠ 0 := by
    intro t hz
    rw [hshift] at hz
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
    have him := congrArg Complex.im hq
    simp at him
    linarith [hσ q]
  have hGd := hGc.differentiable
  obtain ⟨A, φ, hA, hφ, hAφ⟩ := exists_phase_rep hGd hne
  have hrel : ∀ x : ℝ, cosProducer h x = 0 ↔ A x * Real.cos (φ x) = 0 := by
    intro x
    have e : (x : ℂ) + ((h - σ : ℝ) : ℂ) * I + σ * I = x + h * I := by push_cast; ring
    have := hAφ x
    simp only [e] at this
    rw [cosProducer_ofReal, ← this]
    simp
  have hLL := hGc.phaseSpeed_le_exp_mul hd hne
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  -- the phase speed is positive
  have hωpos : ∀ t, 0 < phaseSpeed G (h - σ) t := by
    intro t₀
    by_contra hle
    push Not at hle
    have h0 : phaseSpeed G (h - σ) t₀ = 0 := le_antisymm hle (hLL t₀ t₀).1
    have hz : ∀ s, phaseSpeed G (h - σ) s = 0 := fun s => by
      have := (hLL s t₀).2
      rw [h0, mul_zero] at this
      exact le_antisymm this (hLL s s).1
    have hconst : ∀ y, φ y = φ a := by
      intro y
      have hd' : ∀ x, HasDerivAt φ 0 x := fun x => by
        have := hφ x; rwa [hz x, neg_zero] at this
      exact is_const_of_deriv_eq_zero (fun x => (hd' x).differentiableAt)
        (fun x => (hd' x).deriv) y a
    have hcos : Real.cos (φ a) = 0 :=
      (mul_eq_zero.mp ((hrel a).mp ha)).resolve_left (hA a).ne'
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    apply hno1 _ hmid
    rw [hrel, hconst, hcos, mul_zero]
  exact gap_rigidity_of_phase hd hA hφ hωpos (fun s t => (hLL s t).2) hab hbc
    ((hrel a).mp ha) ((hrel b).mp hb) ((hrel c).mp hc)
    (fun x hx => fun h' => hno1 x hx ((hrel x).mpr h'))
    (fun x hx => fun h' => hno2 x hx ((hrel x).mpr h'))

/-- **Horizon producers are crystals:** unconditionally, for `h > 1/2`. -/
theorem cosProducer_gap_rigidity_of_half_lt {h : ℝ} (hh : 1 / 2 < h) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (ha : cosProducer h a = 0) (hb : cosProducer h b = 0)
    (hc : cosProducer h c = 0) (hno1 : ∀ x ∈ Ioo a b, cosProducer h x ≠ 0)
    (hno2 : ∀ x ∈ Ioo b c, cosProducer h x ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / (h - 1 / 2)) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / (h - 1 / 2)) :=
  cosProducer_gap_rigidity (fun q => (xiSpectralPoint_im_mem_openHalf q).2.le) hh hab hbc ha hb
    hc hno1 hno2

/-- **Under RH every producer is a crystal at its own depth.** -/
theorem cosProducer_gap_rigidity_of_rh (hRH : RiemannHypothesis) {h : ℝ} (hh : 0 < h)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (ha : cosProducer h a = 0)
    (hb : cosProducer h b = 0) (hc : cosProducer h c = 0)
    (hno1 : ∀ x ∈ Ioo a b, cosProducer h x ≠ 0) (hno2 : ∀ x ∈ Ioo b c, cosProducer h x ≠ 0) :
    c - b ≤ (b - a) * Real.exp (2 * (c - a) / h) ∧
      b - a ≤ (c - b) * Real.exp (2 * (c - a) / h) := by
  have := cosProducer_gap_rigidity (σ := 0)
    (fun q => (xiSpectralPoint_im_eq_zero_of_rh hRH q).le) hh hab hbc ha hb hc hno1 hno2
  simpa using this

end RHTower
