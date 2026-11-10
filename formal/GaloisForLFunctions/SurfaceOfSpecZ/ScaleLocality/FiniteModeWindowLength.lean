import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.HalfPeriodSignResolution
import GaloisForLFunctions.HTGeometry.BohrTrigPolynomial
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Compactness.Compact

/-!
# Finite-mode windows without frequency separation

A nonzero trace with `n` distinct frequencies above `Γ>0` has a uniform
negative excursion on every interval longer than `nπ/Γ`. Half-period
deletion bounds the length; compactness of the phase torus makes the
excursion uniform. A remainder tending to zero preserves these windows.
-/

open Set Complex Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Positive and negative frequencies cannot cancel a nonzero real trace. -/
theorem finite_positive_spectrum_real_nonzero {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ)
    (hγ : ∀ j, 0 < γ j) (hinj : Function.Injective γ) (ha : ∃ j, a j ≠ 0) :
    ∃ t, (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re ≠ 0 := by
  classical
  by_contra h
  have hz (t : ℝ) : (∑ j, a j * bohrExp (γ j) t).re = 0 := by
    have hzero : (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re = 0 :=
      by_contra fun ht => h ⟨t, ht⟩
    simpa only [bohrExp, bohrChar, neg_mul, neg_neg] using hzero
  let b : Sum (Fin n) (Fin n) → ℂ := Sum.elim a (fun j => conj (a j))
  let μ : Sum (Fin n) (Fin n) → ℝ := Sum.elim γ (fun j => -γ j)
  have hsum : (fun t => ∑ i, b i * bohrExp (μ i) t) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    rw [Fintype.sum_sum_type]
    change (∑ j, a j * bohrExp (γ j) t) +
      (∑ j, conj (a j) * bohrExp (-γ j) t) = 0
    have he : (∑ j, conj (a j) * bohrExp (-γ j) t) =
        conj (∑ j, a j * bohrExp (γ j) t) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, conj_bohrExp]
      simp only [bohrExp, neg_neg]
    rw [he]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, hz, add_zero, Complex.zero_re]
    · simp only [Complex.add_im, Complex.conj_im, add_neg_cancel, Complex.zero_im]
  obtain ⟨j, hj⟩ := ha
  have hcoef := bohrCoefficient_trigPoly Finset.univ b μ (γ j)
  rw [hsum] at hcoef
  have hzero : bohrCoefficient (fun _ : ℝ => (0 : ℂ)) (γ j) = 0 := by
    simp only [bohrCoefficient, zero_mul]
    exact bohrMean_zero
  rw [hzero, Fintype.sum_sum_type] at hcoef
  change 0 = (∑ i, if γ i = γ j then a i else 0) +
    (∑ i, if -γ i = γ j then conj (a i) else 0) at hcoef
  have hneg (i : Fin n) : -γ i ≠ γ j := by linarith only [hγ i, hγ j]
  simp only [hinj.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hneg, if_false, Finset.sum_const_zero, add_zero] at hcoef
  exact hj hcoef.symm

/-- A compact family with a negative value in each member has a uniform negative excursion. -/
theorem compact_uniform_negative {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (S : Set ℝ) (F : X → ℝ → ℝ) (hc : ∀ t, Continuous (fun x => F x t))
    (hn : ∀ x, ∃ t ∈ S, F x t < 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ∃ t ∈ S, F x t < -ε := by
  let I := {ε : ℝ // 0 < ε}
  letI : Nonempty I := ⟨⟨1, zero_lt_one⟩⟩
  let U : I → Set X := fun ε => ⋃ t ∈ S, {x | F x t < -(ε : ℝ)}
  have hUo : ∀ ε, IsOpen (U ε) := fun ε =>
    isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_lt (hc t) continuous_const
  have hcover : (univ : Set X) ⊆ ⋃ ε, U ε := by
    intro x _
    obtain ⟨t, ht, hneg⟩ := hn x
    let ε : I := ⟨-F x t / 2, by linarith only [hneg]⟩
    refine mem_iUnion.mpr ⟨ε, mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, ?_⟩⟩⟩
    change F x t < -(-F x t / 2)
    linarith only [hneg]
  have hdir : Directed (· ⊆ ·) U := by
    intro ε δ
    refine ⟨⟨min (ε : ℝ) δ, lt_min ε.property δ.property⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨t, ht⟩ := mem_iUnion.mp hx
      obtain ⟨htS, hx⟩ := mem_iUnion.mp ht
      refine mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨htS, ?_⟩⟩
      change F x t < -(ε : ℝ) at hx
      change F x t < -min (ε : ℝ) δ
      exact hx.trans_le (neg_le_neg (min_le_left _ _))
    · intro x hx
      obtain ⟨t, ht⟩ := mem_iUnion.mp hx
      obtain ⟨htS, hx⟩ := mem_iUnion.mp ht
      refine mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨htS, ?_⟩⟩
      change F x t < -(δ : ℝ) at hx
      change F x t < -min (ε : ℝ) δ
      exact hx.trans_le (neg_le_neg (min_le_right _ _))
  obtain ⟨ε, hε⟩ := isCompact_univ.elim_directed_cover U hUo hcover hdir
  refine ⟨ε, ε.property, fun x => ?_⟩
  obtain ⟨t, ht⟩ := mem_iUnion.mp (hε (mem_univ x))
  obtain ⟨htS, hx⟩ := mem_iUnion.mp ht
  exact ⟨t, htS, hx⟩

/-- Every phase rotation has a negative excursion on the same interval, with a uniform margin. -/
theorem finite_spectrum_uniform_phase_negative {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ)
    {Γ L : ℝ} (hΓ : 0 < Γ) (hγ : ∀ j, Γ ≤ γ j)
    (hinj : Function.Injective γ) (ha : ∃ j, a j ≠ 0) (hL : n * Real.pi < Γ * L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : Fin n → Circle, ∃ t ∈ Icc 0 L,
      (∑ j, (a j * (q j : ℂ)) * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re < -ε := by
  let F : (Fin n → Circle) → ℝ → ℝ := fun q t =>
    (∑ j, (a j * (q j : ℂ)) * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re
  apply compact_uniform_negative (Icc 0 L) F
  · intro t
    unfold F
    fun_prop
  · intro q
    have hne := finite_positive_spectrum_real_nonzero (fun j => a j * (q j : ℂ)) γ
      (fun j => hΓ.trans_le (hγ j)) hinj
      (by obtain ⟨j, hj⟩ := ha; exact ⟨j, mul_ne_zero hj (Circle.coe_ne_zero _)⟩)
    by_contra hn
    have hpos : ∀ t ∈ Icc 0 (0 + L), 0 ≤ F q t := by
      intro t ht
      exact le_of_not_gt fun hneg => hn ⟨t, by simpa only [zero_add] using ht, hneg⟩
    have hbound := exponentialSum_sign_interval_resolution (fun j => a j * (q j : ℂ)) γ
      hΓ hγ hne hpos
    exact (not_le.mpr hL) hbound

/-- The window length depends on the number and the lowest frequency, without separation. -/
theorem finite_spectrum_negative_in_every_window {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ)
    {Γ L : ℝ} (hΓ : 0 < Γ) (hγ : ∀ j, Γ ≤ γ j)
    (hinj : Function.Injective γ) (ha : ∃ j, a j ≠ 0) (hL : n * Real.pi < Γ * L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : ℝ, ∃ u ∈ Icc T (T + L),
      (∑ j, a j * Complex.exp (((γ j * u : ℝ) : ℂ) * Complex.I)).re < -ε := by
  obtain ⟨ε, hε, hphase⟩ := finite_spectrum_uniform_phase_negative a γ hΓ hγ hinj ha hL
  refine ⟨ε, hε, fun T => ?_⟩
  obtain ⟨t, ht, hneg⟩ := hphase (fun j => Circle.exp (γ j * T))
  refine ⟨T + t, ⟨by linarith only [ht.1], by linarith only [ht.2]⟩, ?_⟩
  have he : (∑ j, (a j * (Circle.exp (γ j * T) : ℂ)) *
      Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)) =
      ∑ j, a j * Complex.exp (((γ j * (T + t) : ℝ) : ℂ) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Circle.coe_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rwa [he] at hneg

/-- A vanishing remainder preserves finite-mode negative windows with half the margin. -/
theorem finite_spectrum_negative_windows_of_remainder {n : ℕ}
    (a : Fin n → ℂ) (γ : Fin n → ℝ) {Γ L : ℝ} (hΓ : 0 < Γ)
    (hγ : ∀ j, Γ ≤ γ j) (hinj : Function.Injective γ) (ha : ∃ j, a j ≠ 0)
    (hL : n * Real.pi < Γ * L) {f : ℝ → ℝ}
    (hrem : Tendsto (fun u => f u -
      (∑ j, a j * Complex.exp (((γ j * u : ℝ) : ℂ) * Complex.I)).re) atTop (𝓝 0)) :
    ∃ ε U : ℝ, 0 < ε ∧ ∀ T : ℝ, U ≤ T → ∃ u ∈ Icc T (T + L), f u < -ε := by
  obtain ⟨ε, hε, hwin⟩ := finite_spectrum_negative_in_every_window a γ hΓ hγ hinj ha hL
  obtain ⟨U, hU⟩ := eventually_atTop.mp (hrem.eventually_lt_const (half_pos hε))
  refine ⟨ε / 2, U, half_pos hε, fun T hT => ?_⟩
  obtain ⟨u, hu, hneg⟩ := hwin T
  exact ⟨u, hu, by linarith only [hU u (hT.trans hu.1), hneg]⟩

#print axioms finite_spectrum_negative_in_every_window
#print axioms finite_spectrum_negative_windows_of_remainder

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
