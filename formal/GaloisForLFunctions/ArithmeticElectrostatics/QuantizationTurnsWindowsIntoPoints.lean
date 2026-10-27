import GaloisForLFunctions.ArithmeticElectrostatics.TheTransverseEnergyOfTheZeroDivisor
import GaloisForLFunctions.ArithmeticElectrostatics.TheRenormalizedSquareIsSelbergsSource
import GaloisForLFunctions.RHTower.XiZeroBandFinite
import GaloisForLFunctions.ArithmeticElectrostatics.TheVirialLawsOfAFiniteConfiguration

/-!
# Quantization turns windows into points

Averages, proportions and almost-every statements place most zeros near the line and exclude none:
excluding an individual zero needs control below the zero spacing. A quantized quantity removes
that obstruction, because a window cannot carry a fraction of a quantum.

* **The energy of a window counts its off-line zeros** (`card_offLine_le_windowEnergy`): for the
  finite window `W(T, H)` of zeros with `|γ − T| ≤ H`, the number of off-line zeros in the window
  is at most its energy `Σ_{ρ ∈ W} E(ρ)`, `E` the angular energy. Off-line zeros come with their
  reflection partner at the same ordinate, so a window with an off-line zero has energy at least
  `2` (`two_le_windowEnergy`), and a window of energy below `2` is critical
  (`critical_of_windowEnergy_lt_two`), whatever its size — one zero spacing suffices.
  RH holds iff every unit window has energy below `2` (`riemannHypothesis_iff_windowEnergy_lt_two`).
* **Electrostatics is blind to the archimedean place** (`transverseEnergy_affine`,
  `fieldAt_affine`): the reflection-commuting affine maps `s ↦ ½ + λ(s − ½) + iκ` (dilations and the
  archimedean twist) preserve the transverse energy and scale the field by `λ⁻¹`. The first gauge
  charge, an archimedean twist, is invisible to every electrostatic quantity.
* **The renormalized source carries the gauge charge at every prime** (`selbergSource_twist`,
  `eq_one_of_twisted_selbergSource_nonneg`): for a completely multiplicative gauge `ω`, the source
  of the twin `ω Λ` is `ω Λ₂`, and its nonnegativity at a prime forces `ω(p) ≥ 0`; for sign gauges,
  `ω(p) = 1`. The charge enters through the arithmetic computation, not through the geometry of the
  charges.
-/

open Finset RHTower ArithmeticFunction
open scoped ENNReal

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-! ### Windows -/

/-- The window of zeros with ordinate within `H` of `T`. -/
def zeroWindow (T H : ℝ) : Set XiDivisorSupport := {ρ | |(ρ : ℂ).im - T| ≤ H}

theorem zeroWindow_finite (T : ℝ) {H : ℝ} (hH : 0 ≤ H) : (zeroWindow T H).Finite :=
  finite_xiDivisorSupport_band T hH

/-- The **energy of a window**: the total angular energy of its zeros. -/
def windowEnergy (T : ℝ) {H : ℝ} (hH : 0 ≤ H) : ℝ :=
  ∑ ρ ∈ (zeroWindow_finite T hH).toFinset, angularEnergy ρ

/-- **The energy of a window counts its off-line zeros.** -/
theorem card_offLine_le_windowEnergy (T : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (((zeroWindow_finite T hH).toFinset.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re ≠ 1 / 2).card : ℝ) ≤
      windowEnergy T hH := by
  rw [windowEnergy]
  calc (((zeroWindow_finite T hH).toFinset.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re ≠ 1 / 2).card : ℝ)
      = ∑ _ρ ∈ (zeroWindow_finite T hH).toFinset.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re ≠ 1 / 2, (1 : ℝ) := by
        simp
    _ ≤ ∑ ρ ∈ (zeroWindow_finite T hH).toFinset.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re ≠ 1 / 2,
          angularEnergy ρ := sum_le_sum fun ρ hρ => one_le_angularEnergy (mem_filter.mp hρ).2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun ρ _ _ => angularEnergy_nonneg ρ

/-- A window containing an off-line zero has energy at least `2`: the zero and its partner. -/
theorem two_le_windowEnergy (T : ℝ) {H : ℝ} (hH : 0 ≤ H) {ρ : XiDivisorSupport}
    (hρW : ρ ∈ zeroWindow T H) (hρ : (ρ : ℂ).re ≠ 1 / 2) : 2 ≤ windowEnergy T hH := by
  have hpW : supportPartner ρ ∈ zeroWindow T H := by
    simp only [zeroWindow, Set.mem_setOf_eq, supportPartner_coe, Complex.sub_im, Complex.one_im,
      Complex.conj_im, zero_sub, neg_neg] at hρW ⊢
    exact hρW
  have hpρ : (supportPartner ρ : ℂ).re ≠ 1 / 2 := by
    rw [supportPartner_re]; intro hc; exact hρ (by linarith)
  have hne : supportPartner ρ ≠ ρ := fun hc => hρ ((supportPartner_eq_self_iff ρ).mp hc)
  have hsub : ({ρ, supportPartner ρ} : Finset XiDivisorSupport) ⊆
      (zeroWindow_finite T hH).toFinset.filter fun ρ : XiDivisorSupport => (ρ : ℂ).re ≠ 1 / 2 := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_filter.mpr ⟨(zeroWindow_finite T hH).mem_toFinset.mpr hρW, hρ⟩
    · exact mem_filter.mpr ⟨(zeroWindow_finite T hH).mem_toFinset.mpr hpW, hpρ⟩
  have hcard := card_le_card hsub
  rw [card_pair hne.symm] at hcard
  have := card_offLine_le_windowEnergy T hH
  have h2 : (2 : ℝ) ≤ (((zeroWindow_finite T hH).toFinset.filter
      fun ρ : XiDivisorSupport => (ρ : ℂ).re ≠ 1 / 2).card : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Selection at any scale**: a window of energy below `2` has no off-line zero. -/
theorem critical_of_windowEnergy_lt_two (T : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (h : windowEnergy T hH < 2) : ∀ ρ ∈ zeroWindow T H, (ρ : ℂ).re = 1 / 2 := by
  intro ρ hρW
  by_contra hρ
  exact absurd (two_le_windowEnergy T hH hρW hρ) (not_le.mpr h)

/-- **RH is a window bound**: every unit window has energy below `2`. -/
theorem riemannHypothesis_iff_windowEnergy_lt_two :
    RiemannHypothesis ↔ ∀ T : ℝ, windowEnergy T zero_le_one < 2 := by
  constructor
  · intro h T
    have hzero : ∀ ρ, angularEnergy ρ = 0 := angularEnergy_eq_zero_of_riemannHypothesis h
    rw [windowEnergy, sum_eq_zero fun ρ _ => hzero ρ]
    norm_num
  · intro h
    refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
    exact critical_of_windowEnergy_lt_two ((ρ : ℂ).im) zero_le_one (h _) ρ (by
      simp [zeroWindow])

/-! ### Blindness to the archimedean place -/

section Affine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A reflection-commuting affine map `s ↦ ½ + λ(s − ½) + iκ`. -/
def affineMap (lam κ : ℝ) (s : ℂ) : ℂ := 1 / 2 + lam * (s - 1 / 2) + κ * Complex.I

theorem affineMap_sub (lam κ : ℝ) (s t : ℂ) : affineMap lam κ s - affineMap lam κ t = lam * (s - t) := by
  simp only [affineMap]; ring

/-- **The transverse energy is invariant under dilations and the archimedean twist.** -/
theorem transverseEnergy_affine (m : ι → ℝ) (z : ι → ℂ) {lam : ℝ} (hlam : lam ≠ 0) (κ : ℝ) :
    transverseEnergy m (fun j => affineMap lam κ (z j)) = transverseEnergy m z := by
  unfold transverseEnergy
  congr 1
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [show (affineMap lam κ (z j)).re - (affineMap lam κ (z k)).re = lam * ((z j).re - (z k).re) by
      rw [← Complex.sub_re, affineMap_sub, Complex.re_ofReal_mul, Complex.sub_re],
    affineMap_sub, Complex.normSq_mul, Complex.normSq_ofReal]
  by_cases hd : Complex.normSq (z j - z k) = 0
  · rw [hd]; simp
  · field_simp

/-- **The field scales by `λ⁻¹`**: equilibrium is invariant under the affine maps. -/
theorem fieldAt_affine (m : ι → ℂ) (z : ι → ℂ) (lam κ : ℝ) (j : ι) :
    ArithmeticCorrespondencePositivity.fieldAt m (fun k => affineMap lam κ (z k)) j =
      (lam : ℂ)⁻¹ * ArithmeticCorrespondencePositivity.fieldAt m z j := by
  simp only [ArithmeticCorrespondencePositivity.fieldAt, affineMap_sub, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [div_eq_mul_inv, mul_inv]
  ring

end Affine

/-! ### The gauge charge of the renormalized source -/

/-- Twisting by a completely multiplicative gauge commutes with Dirichlet convolution. -/
theorem pmul_mul_pmul {ω f g : ArithmeticFunction ℝ} (hω : ∀ a b, ω (a * b) = ω a * ω b) :
    (f.pmul ω) * (g.pmul ω) = (f * g).pmul ω := by
  ext n
  simp only [mul_apply, pmul_apply, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, hω]
  ring

/-- **The source of a twin is the twisted source**: `Λ₂^ω = ω Λ₂`. -/
theorem selbergSource_twist {ω : ArithmeticFunction ℝ} (hω : ∀ a b, ω (a * b) = ω a * ω b) :
    (vonMangoldt.pmul ω).pmul log + (vonMangoldt.pmul ω) * (vonMangoldt.pmul ω) =
      selbergSource.pmul ω := by
  rw [pmul_mul_pmul hω, selbergSource]
  ext n
  simp only [ArithmeticFunction.add_apply, pmul_apply]
  ring

/-- **Gauge selectivity at every prime**: if the source of the twin `ω Λ` is nonnegative, then
`ω(p) ≥ 0` at every prime; for a sign gauge `ω(p) = 1`. -/
theorem eq_one_of_twisted_selbergSource_nonneg {ω : ArithmeticFunction ℝ}
    (hpos : ∀ n, 0 ≤ (selbergSource.pmul ω) n)
    {p : ℕ} (hp : p.Prime) (hsign : ω p = 1 ∨ ω p = -1) : ω p = 1 := by
  have hval := selbergSource_prime_pow hp (le_refl 1)
  rw [pow_one, Nat.cast_one, show (2 * (1 : ℝ) - 1) = 1 by norm_num, one_mul] at hval
  have hlog : 0 < Real.log p ^ 2 := pow_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) 2
  have h := hpos p
  rw [pmul_apply, hval] at h
  rcases hsign with h1 | h1
  · exact h1
  · rw [h1] at h; nlinarith

end

end GaloisForLFunctions.ArithmeticElectrostatics
