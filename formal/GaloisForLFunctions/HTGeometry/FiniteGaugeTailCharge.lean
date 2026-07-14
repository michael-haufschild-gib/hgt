import GaloisForLFunctions.HTGeometry.DenseNullContinuationSeam
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-gauge tail charges

This file isolates the two general mechanisms behind the Helson critical-divisor law.

* A product invariant under finite coordinate modifications has dense nonempty fibers.  Its
  coinduced charge topology is therefore indiscrete, and every continuous separated readout
  constant on charge fibers collapses.
* A finite change of unimodular Euler phases is a holomorphic nonvanishing gauge on the positive
  half-plane.  Any divisor there is consequently a finite-modification tail charge.
-/

namespace GaloisForLFunctions

open Complex Set

/-- A finite-modification invariant on a product has a dense fiber through every point. -/
theorem dense_fiber_of_finiteModification_invariant
    {I Q : Type*} {A : I → Type*} [∀ i, TopologicalSpace (A i)]
    (q : (∀ i, A i) → Q)
    (hinvariant : ∀ x y, y ∈ finiteModification A x → q y = q x)
    (x : ∀ i, A i) :
    Dense (q ⁻¹' {q x}) := by
  apply (dense_finiteModification x).mono
  intro y hy
  simpa only [mem_preimage, mem_singleton_iff] using hinvariant x y hy

/-- If every fiber of a surjection is dense, its coinduced quotient topology is indiscrete. -/
theorem coinduced_eq_indiscrete_of_dense_fibers
    {X Q : Type*} [tX : TopologicalSpace X]
    (q : X → Q) (hq : Function.Surjective q)
    (hdense : ∀ a : Q, Dense (q ⁻¹' {a})) :
    TopologicalSpace.coinduced q tX = ⊤ := by
  apply TopologicalSpace.ext
  funext U
  rw [isOpen_coinduced, TopologicalSpace.isOpen_top_iff]
  apply propext
  constructor
  · intro hU
    by_cases hUempty : U = ∅
    · exact Or.inl hUempty
    · right
      apply eq_univ_of_forall
      intro a
      obtain ⟨u, huU⟩ := U.nonempty_iff_ne_empty.mpr hUempty
      obtain ⟨x, hx⟩ := hq u
      have hpreNonempty : (q ⁻¹' U).Nonempty := ⟨x, by simpa [hx] using huU⟩
      rcases (dense_iff_inter_open.mp (hdense a)) (q ⁻¹' U) hU hpreNonempty with
        ⟨z, hzU, hza⟩
      have hqza : q z = a := by
        simpa only [mem_preimage, mem_singleton_iff] using hza
      simpa only [mem_preimage, hqza] using hzU
  · rintro (rfl | rfl)
    · simp
    · simp

/-- If an invariant has dense fibers, continuity at one point into a `T₁` space forces its value
at that point to equal every other value. -/
theorem continuousAt_constant_of_dense_fibers
    {X Q Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (q : X → Q) (F : X → Y) (x : X) (hF : ContinuousAt F x)
    (hdense : ∀ y : X, Dense (q ⁻¹' {q y}))
    (hinvariant : ∀ y z, q y = q z → F y = F z) :
    ∀ y, F y = F x := by
  intro y
  apply specializes_iff_eq.mp
  apply specializes_iff_forall_open.mpr
  intro U hU hFxU
  have hpre : F ⁻¹' U ∈ nhds x := hF (hU.mem_nhds hFxU)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hpre
  rcases (dense_iff_inter_open.mp (hdense y)) V hVopen ⟨x, hxV⟩ with
    ⟨z, hzV, hzy⟩
  have hqzy : q z = q y := by
    simpa only [mem_preimage, mem_singleton_iff] using hzy
  have hzU : F z ∈ U := hVsub hzV
  exact hinvariant z y hqzy ▸ hzU

/-- A continuous `T₀` readout that is constant on dense charge fibers is constant globally. -/
theorem continuous_constant_of_dense_fibers
    {X Q Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space Y]
    (q : X → Q) (F : X → Y) (hF : Continuous F)
    (hdense : ∀ x : X, Dense (q ⁻¹' {q x}))
    (hinvariant : ∀ x y, q x = q y → F x = F y) :
    ∀ x y, F x = F y := by
  intro x y
  by_contra hxy
  obtain ⟨U, hUopen, hxor⟩ := exists_isOpen_xor_mem hxy
  have hpreOpen : IsOpen (F ⁻¹' U) := hUopen.preimage hF
  rcases hxor with hxyU | hyxU
  · have hpreNonempty : (F ⁻¹' U).Nonempty := ⟨x, hxyU.1⟩
    rcases (dense_iff_inter_open.mp (hdense y)) (F ⁻¹' U) hpreOpen hpreNonempty with
      ⟨z, hzU, hzy⟩
    have hqzy : q z = q y := by
      simpa only [mem_preimage, mem_singleton_iff] using hzy
    exact hxyU.2 (hinvariant z y hqzy ▸ hzU)
  · have hpreNonempty : (F ⁻¹' U).Nonempty := ⟨y, hyxU.1⟩
    rcases (dense_iff_inter_open.mp (hdense x)) (F ⁻¹' U) hpreOpen hpreNonempty with
      ⟨z, hzU, hzx⟩
    have hqzx : q z = q x := by
      simpa only [mem_preimage, mem_singleton_iff] using hzx
    exact hyxU.2 (hinvariant z x hqzx ▸ hzU)

/-- The positive half-plane, the divisor-protection region for finite unimodular Euler gauges. -/
def positiveHalfPlane : Set ℂ := {s | 0 < s.re}

/-- The analytic prime power `p⁻ˢ`, written without a branch ambiguity for a positive real base. -/
noncomputable def analyticPrimeDecay (p : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log p : ℂ))

theorem norm_analyticPrimeDecay (p : ℝ) (s : ℂ) :
    ‖analyticPrimeDecay p s‖ = Real.exp (-s.re * Real.log p) := by
  rw [analyticPrimeDecay, Complex.norm_exp]
  simp [Complex.mul_re]

theorem differentiable_analyticPrimeDecay (p : ℝ) :
    Differentiable ℂ (analyticPrimeDecay p) := by
  change Differentiable ℂ (fun s : ℂ => Complex.exp (-s * (Real.log p : ℂ)))
  fun_prop

theorem norm_analyticPrimeDecay_lt_one
    {p : ℝ} (hp : 1 < p) {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    ‖analyticPrimeDecay p s‖ < 1 := by
  rw [norm_analyticPrimeDecay, Real.exp_lt_one_iff]
  have hs' : 0 < s.re := hs
  nlinarith [Real.log_pos hp]

/-- A unimodular local Euler factor has no zero in the positive half-plane. -/
theorem one_sub_phase_mul_analyticPrimeDecay_ne_zero
    {p : ℝ} (hp : 1 < p) {omega : ℂ} (homega : ‖omega‖ = 1)
    {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    1 - omega * analyticPrimeDecay p s ≠ 0 := by
  intro hzero
  have hEq : omega * analyticPrimeDecay p s = 1 := (sub_eq_zero.mp hzero).symm
  have hlt : ‖omega * analyticPrimeDecay p s‖ < 1 := by
    rw [norm_mul, homega, one_mul]
    exact norm_analyticPrimeDecay_lt_one hp hs
  rw [hEq, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The one-prime meromorphic gauge associated with a phase change. -/
noncomputable def localEulerGaugeRatio
    (p : ℝ) (omega psi : ℂ) (s : ℂ) : ℂ :=
  (1 - omega * analyticPrimeDecay p s) /
    (1 - psi * analyticPrimeDecay p s)

/-- A one-prime unimodular phase change is nonzero on the positive half-plane. -/
theorem localEulerGaugeRatio_ne_zero
    {p : ℝ} (hp : 1 < p) {omega psi : ℂ}
    (homega : ‖omega‖ = 1) (hpsi : ‖psi‖ = 1)
    {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    localEulerGaugeRatio p omega psi s ≠ 0 := by
  rw [localEulerGaugeRatio]
  exact div_ne_zero
    (one_sub_phase_mul_analyticPrimeDecay_ne_zero hp homega hs)
    (one_sub_phase_mul_analyticPrimeDecay_ne_zero hp hpsi hs)

/-- A one-prime phase change is holomorphic on the positive half-plane. -/
theorem differentiableOn_localEulerGaugeRatio_positiveHalfPlane
    {p : ℝ} (hp : 1 < p) {omega psi : ℂ} (hpsi : ‖psi‖ = 1) :
    DifferentiableOn ℂ (localEulerGaugeRatio p omega psi) positiveHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ
    (fun z => (1 - omega * analyticPrimeDecay p z) /
      (1 - psi * analyticPrimeDecay p z)) s
  apply DifferentiableAt.div
  · exact (differentiable_analyticPrimeDecay p).differentiableAt.const_mul omega |>.const_sub 1
  · exact (differentiable_analyticPrimeDecay p).differentiableAt.const_mul psi |>.const_sub 1
  · exact one_sub_phase_mul_analyticPrimeDecay_ne_zero hp hpsi hs

/-- The finite meromorphic Euler gauge associated with finitely many phase changes. -/
noncomputable def finiteEulerGaugeRatio
    {I : Type*} (P : Finset I) (p : I → ℝ) (omega psi : I → ℂ) (s : ℂ) : ℂ :=
  ∏ i ∈ P, localEulerGaugeRatio (p i) (omega i) (psi i) s

/-- Every finite unimodular Euler gauge is nonzero in the positive half-plane. -/
theorem finiteEulerGaugeRatio_ne_zero
    {I : Type*} (P : Finset I) (p : I → ℝ) (hp : ∀ i ∈ P, 1 < p i)
    (omega psi : I → ℂ)
    (homega : ∀ i ∈ P, ‖omega i‖ = 1) (hpsi : ∀ i ∈ P, ‖psi i‖ = 1)
    {s : ℂ} (hs : s ∈ positiveHalfPlane) :
    finiteEulerGaugeRatio P p omega psi s ≠ 0 := by
  rw [finiteEulerGaugeRatio]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact localEulerGaugeRatio_ne_zero (hp i hi) (homega i hi) (hpsi i hi) hs

/-- Every finite unimodular Euler gauge is holomorphic on the positive half-plane. -/
theorem differentiableOn_finiteEulerGaugeRatio_positiveHalfPlane
    {I : Type*} (P : Finset I) (p : I → ℝ) (hp : ∀ i ∈ P, 1 < p i)
    (omega psi : I → ℂ) (hpsi : ∀ i ∈ P, ‖psi i‖ = 1) :
    DifferentiableOn ℂ (finiteEulerGaugeRatio P p omega psi) positiveHalfPlane := by
  classical
  change DifferentiableOn ℂ
    (fun s => ∏ i ∈ P, localEulerGaugeRatio (p i) (omega i) (psi i) s)
    positiveHalfPlane
  apply DifferentiableOn.fun_finsetProd
  intro i hi
  exact differentiableOn_localEulerGaugeRatio_positiveHalfPlane (hp i hi) (hpsi i hi)

end GaloisForLFunctions
