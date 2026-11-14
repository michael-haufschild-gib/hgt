import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta
import GaloisForLFunctions.RHTower.LegendreRootNumber
import GaloisForLFunctions.RHTower.DirichletLSubpolynomial
import GaloisForLFunctions.RHTower.DirichletLReciprocalRightOfTheOneLine
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownRateIsTheZeroFreeStrip
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion

/-!
# Bianchi Horizon Ringdown Equivalence (`SL₂(ℤ[ω])\ℍ³`)

For the third cyclotomic / Eisenstein field `K = ℚ(√−3) = ℚ(ζ₃)`, the Eisenstein lattice sum over
`ℤ[ω] \ {0}` factors as `6 ζ(s) L(s, χ₋₃)` (`EisensteinNorm.latticeSum_eq`), matching `6 ζ_K(s)` on
`Re s > 1` (`FamilyContinuationTheory.dedekindZeta_thirdCyclotomic`). Completing both factors gives
the completed Dedekind zeta function

`Λ_K(s) = 3^{s/2} Λ_ℚ(s) Λ(s, χ₋₃)`

and its entire pole-cleared completion

`ξ_K(s) = 3^{s/2} ξ(s) Λ(s, χ₋₃)`,

satisfying `ξ_K(1 - s) = ξ_K(s)` (`xiBianchi_one_sub`, because the Legendre root number of `χ₋₃` is
`+1`) and `ξ_K(s̄) = \overline{ξ_K(s)}` (`xiBianchi_conj`).

On the three-dimensional Bianchi modular quotient `SL₂(ℤ[ω])\ℍ³`, the spherical Eisenstein constant
term has scattering reflection coefficient

`φ_K(w) = Λ_K(2w) / Λ_K(1 + 2w) = ((1 + 2w) / (2w - 1)) · (ξ_K(2w) / ξ_K(1 + 2w))`

(`bianchiScatteringPhase`, `completedBianchiZeta_div_eq_bianchiScatteringPhase`), which is unitary
on the continuous-spectrum axis `Re w = 0` (`norm_bianchiScatteringPhase_axis`). Sending a smooth
compactly supported wavepacket `h` into the Bianchi cusp produces the reflected horizon wavepacket

`bianchiReflectedField h τ = ∫_{-∞}^∞ a_h(t) φ_K(it) e^{itτ} dt`.

Main theorem (`bianchi_zeroFreeStrip_iff_pulse_ringdown`): for every `0 < δ ≤ 1/4`,

`∀ ρ, ζ(ρ) L(ρ, χ₋₃) = 0 → 0 < Re ρ → Re ρ ≤ 1 - 2δ`
`⟺ ∀ ε > 0, ∀ h : CompactPulse, ∃ C, ∀ τ ≥ 0, ‖bianchiReflectedField h τ‖ ≤ C e^{-(δ - ε)τ}`.

Equivalently, for any third cyclotomic field `K`, the late-time ringdown rate `δ` of reflected
pulses on the Bianchi horizon equals half the zero-free strip width of the Dedekind / Hecke
`L`-function `heckeLFunction (trivialModulus K) 1` (`bianchi_hecke_zeroFreeStrip_iff_pulse_ringdown`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform

noncomputable section

namespace GaloisForLFunctions.RingdownOfTheCubicCover

open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.BlackHoleRingdown.RingdownRate
open _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-! ## 1. Completed Dedekind zeta and entire `ξ_K` for `ℚ(√−3)` -/

/-- `chi3D` is primitive of conductor `3`. -/
theorem isPrimitive_chi3D : chi3D.IsPrimitive := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact GaloisForLFunctions.RHTower.HalfWeight.isPrimitive_of_ne_one chi3D chi3D_ne_one

/-- `chi3D` agrees definitionally with `HalfWeight.legendreC 3`. -/
theorem chi3D_eq_legendreC : chi3D = GaloisForLFunctions.RHTower.HalfWeight.legendreC 3 := rfl

/-- Functional equation of `Λ(s, χ₋₃)`: `Λ(1 - s, χ₋₃) = 3^{s - 1/2} Λ(s, χ₋₃)`. -/
theorem completedLFunction_chi3D_one_sub (s : ℂ) :
    DirichletCharacter.completedLFunction chi3D (1 - s) =
      (3 : ℂ) ^ (s - 1 / 2) * DirichletCharacter.completedLFunction chi3D s := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact GaloisForLFunctions.RHTower.HalfWeight.completedLFunction_legendre_one_sub 3 (by decide) s

/-- Self-duality `χ₋₃⁻¹ = χ₋₃`. -/
theorem chi3D_inv : chi3D⁻¹ = chi3D := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact GaloisForLFunctions.RHTower.HalfWeight.legendreC_inv 3

/-- Completed Dedekind zeta function `Λ_K(s) = 3^{s/2} Λ_ℚ(s) Λ(s, χ₋₃)` of `K = ℚ(√−3)`. -/
def completedBianchiZeta (s : ℂ) : ℂ :=
  (3 : ℂ) ^ (s / 2) * completedRiemannZeta s * DirichletCharacter.completedLFunction chi3D s

/-- Entire pole-cleared Dedekind `ξ`-function `ξ_K(s) = 3^{s/2} ξ(s) Λ(s, χ₋₃)` of `K = ℚ(√−3)`. -/
def xiBianchi (s : ℂ) : ℂ :=
  (3 : ℂ) ^ (s / 2) * xi s * DirichletCharacter.completedLFunction chi3D s

/-- `ξ_K` is entire on `ℂ`. -/
theorem differentiable_xiBianchi : Differentiable ℂ xiBianchi := by
  have h3 : Differentiable ℂ fun s : ℂ => (3 : ℂ) ^ (s / 2) :=
    (differentiable_id.div_const (2 : ℂ)).const_cpow (Or.inl (by norm_num))
  exact (h3.mul xi_differentiable).mul (DirichletCharacter.differentiable_completedLFunction chi3D_ne_one)

/-- Functional equation `ξ_K(1 - s) = ξ_K(s)` on all of `ℂ`. -/
theorem xiBianchi_one_sub (s : ℂ) : xiBianchi (1 - s) = xiBianchi s := by
  unfold xiBianchi
  rw [xi_one_sub, completedLFunction_chi3D_one_sub]
  have hpow : (3 : ℂ) ^ ((1 - s) / 2) * (3 : ℂ) ^ (s - 1 / 2) = (3 : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0)]
    congr 1
    ring
  calc (3 : ℂ) ^ ((1 - s) / 2) * xi s *
        ((3 : ℂ) ^ (s - 1 / 2) * DirichletCharacter.completedLFunction chi3D s)
      = ((3 : ℂ) ^ ((1 - s) / 2) * (3 : ℂ) ^ (s - 1 / 2)) * xi s *
          DirichletCharacter.completedLFunction chi3D s := by ring
    _ = (3 : ℂ) ^ (s / 2) * xi s * DirichletCharacter.completedLFunction chi3D s := by rw [hpow]

/-- Conjugation symmetry `ξ_K(s̄) = \overline{ξ_K(s)}`. -/
theorem xiBianchi_conj (s : ℂ) :
    xiBianchi (starRingEnd ℂ s) = starRingEnd ℂ (xiBianchi s) := by
  unfold xiBianchi
  have harg : ((3 : ℂ)).arg ≠ Real.pi := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_ne_zero.symm
  have hpow : (3 : ℂ) ^ (starRingEnd ℂ s / 2) = starRingEnd ℂ ((3 : ℂ) ^ (s / 2)) := by
    have h2 : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by simp [conj_two]
    rw [h2, Complex.cpow_conj (x := (3 : ℂ)) (n := s / 2) harg]
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hL : DirichletCharacter.completedLFunction chi3D (starRingEnd ℂ s) =
      starRingEnd ℂ (DirichletCharacter.completedLFunction chi3D s) := by
    rw [conj_completedLFunction chi3D_ne_one s, chi3D_inv]
  rw [hpow, xi_conj, hL, map_mul, map_mul]

/-- Archimedean gamma factor of `χ₋₃` does not vanish on `Re s > 0`. -/
theorem gammaFactor_chi3D_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor chi3D s ≠ 0 := by
  obtain ⟨d, hd, hgf⟩ := gammaFactor_eq_Gammaℝ chi3D
  rw [hgf]
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- Archimedean gamma factor of `χ₋₃` does not vanish off the real axis. -/
theorem gammaFactor_chi3D_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) :
    DirichletCharacter.gammaFactor chi3D s ≠ 0 := by
  obtain ⟨d, _, hgf⟩ := gammaFactor_eq_Gammaℝ chi3D
  rw [hgf]
  exact gammaℝ_ne_zero_of_im (by simpa using hs)

/-- Factorization `Λ(s, χ₋₃) = L(s, χ₋₃) γ(s, χ₋₃)` when `s ≠ 0` and `γ(s, χ₋₃) ≠ 0`. -/
theorem completedLFunction_chi3D_eq_mul {s : ℂ} (hs : s ≠ 0)
    (hgf : DirichletCharacter.gammaFactor chi3D s ≠ 0) :
    DirichletCharacter.completedLFunction chi3D s =
      DirichletCharacter.LFunction chi3D s * DirichletCharacter.gammaFactor chi3D s := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi3D s (Or.inl hs),
    div_mul_cancel₀ _ hgf]

/-- On `Re s > 0`, `s ≠ 1`, zeros of `ξ_K(s)` coincide with zeros of `ζ(s) L(s, χ₋₃)`. -/
theorem xiBianchi_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (hne1 : s ≠ 1) :
    xiBianchi s = 0 ↔ riemannZeta s * DirichletCharacter.LFunction chi3D s = 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have h3 : (3 : ℂ) ^ (s / 2) ≠ 0 := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hgf := gammaFactor_chi3D_ne_zero_of_re_pos h0
  unfold xiBianchi
  rw [completedLFunction_chi3D_eq_mul hs0 hgf, mul_eq_zero, mul_eq_zero, mul_eq_zero]
  simp only [h3, false_or, hgf, or_false, xi_eq_zero_iff h0 hne1]
  exact mul_eq_zero.symm

/-- `ξ_K` has no zeros on `Re s ≥ 1`. -/
theorem xiBianchi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : xiBianchi s ≠ 0 := by
  have h0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have h3 : (3 : ℂ) ^ (s / 2) ≠ 0 := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hgf := gammaFactor_chi3D_ne_zero_of_re_pos h0
  unfold xiBianchi
  rw [completedLFunction_chi3D_eq_mul hs0 hgf]
  exact mul_ne_zero (mul_ne_zero h3 (xi_ne_zero_of_one_le_re hs))
    (mul_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hs) hgf)

/-- `ξ_K(2w) ≠ 0` for all `Re w ≤ 0` (by `ξ_K(2w) = ξ_K(1 - 2w)` and `Re(1 - 2w) ≥ 1`). -/
theorem xiBianchi_two_mul_ne_zero_of_re_nonpos {w : ℂ} (hw : w.re ≤ 0) : xiBianchi (2 * w) ≠ 0 := by
  rw [← xiBianchi_one_sub]
  exact xiBianchi_ne_zero_of_one_le_re (by simp; linarith)

/-- Every zero of `ξ_K` lies in the open critical strip `0 < Re s < 1`. -/
theorem zero_mem_openStrip_of_xiBianchi_eq_zero {s : ℂ} (hz : xiBianchi s = 0) :
    0 < s.re ∧ s.re < 1 := by
  have hlt1 : s.re < 1 := lt_of_not_ge fun h => xiBianchi_ne_zero_of_one_le_re h hz
  have hgt0 : 0 < s.re := by
    by_contra hle
    push Not at hle
    have h1 : 1 ≤ (1 - s).re := by simp; linarith
    exact xiBianchi_ne_zero_of_one_le_re h1 (by rw [xiBianchi_one_sub]; exact hz)
  exact ⟨hgt0, hlt1⟩

/-! ## 2. The Bianchi Eisenstein scattering phase and its strip bounds -/

/-- Scattering reflection phase `φ_K(w) = ((1 + 2w)/(2w - 1)) · (ξ_K(2w) / ξ_K(1 + 2w))` of the
Bianchi Eisenstein constant term on `SL₂(ℤ[ω])\ℍ³`. -/
def bianchiScatteringPhase (w : ℂ) : ℂ :=
  ((1 + 2 * w) / (2 * w - 1)) * (xiBianchi (2 * w) / xiBianchi (1 + 2 * w))

/-- Away from `{0, 1/2, -1/2}`, `bianchiScatteringPhase w` is the completed Dedekind zeta ratio
`Λ_K(2w) / Λ_K(1 + 2w)` of the Bianchi Eisenstein constant term. -/
theorem completedBianchiZeta_div_eq_bianchiScatteringPhase {w : ℂ}
    (hw0 : w ≠ 0) (hwhalf : 2 * w - 1 ≠ 0) (hwneg : 1 + 2 * w ≠ 0)
    (hwone : 2 * w ≠ 1) (hwm1 : 1 + 2 * w ≠ 1) :
    completedBianchiZeta (2 * w) / completedBianchiZeta (1 + 2 * w) =
      bianchiScatteringPhase w := by
  have h2w0 : 2 * w ≠ 0 := mul_ne_zero two_ne_zero hw0
  have hxi1 : xi (2 * w) = w * (2 * w - 1) * completedRiemannZeta (2 * w) := by
    rw [xi_eq_half_mul h2w0 hwone]
    ring
  have hxi2 : xi (1 + 2 * w) = w * (1 + 2 * w) * completedRiemannZeta (1 + 2 * w) := by
    rw [xi_eq_half_mul hwneg hwm1]
    ring
  unfold bianchiScatteringPhase xiBianchi completedBianchiZeta
  rw [hxi1, hxi2]
  have h1 : (3 : ℂ) ^ (2 * w / 2) * (w * (2 * w - 1) * completedRiemannZeta (2 * w)) *
      DirichletCharacter.completedLFunction chi3D (2 * w) =
      (w * (2 * w - 1)) * ((3 : ℂ) ^ (2 * w / 2) * completedRiemannZeta (2 * w) *
        DirichletCharacter.completedLFunction chi3D (2 * w)) := by ring
  have h2 : (3 : ℂ) ^ ((1 + 2 * w) / 2) * (w * (1 + 2 * w) * completedRiemannZeta (1 + 2 * w)) *
      DirichletCharacter.completedLFunction chi3D (1 + 2 * w) =
      (w * (1 + 2 * w)) * ((3 : ℂ) ^ ((1 + 2 * w) / 2) * completedRiemannZeta (1 + 2 * w) *
        DirichletCharacter.completedLFunction chi3D (1 + 2 * w)) := by ring
  rw [h1, h2]
  field_simp

/-- On `Re w > 1/2`, the Eisenstein lattice sum over `ℤ[ω] \ {0}` identifies the uncompleted
Dirichlet factor inside `Λ_K(1 + 2w)`. -/
theorem bianchiLatticeSum_eq_product {w : ℂ} (hw : 0 < w.re) :
    (∑' p : {p : ℤ × ℤ // p ≠ (0, 0)}, latTerm (1 + 2 * w) p) =
      6 * (riemannZeta (1 + 2 * w) * DirichletCharacter.LFunction chi3D (1 + 2 * w)) :=
  latticeSum_eq (by simp; linarith)

/-- Unitarity of the Bianchi scattering reflection phase on the continuous-spectrum axis `Re w = 0`:
`‖φ_K(it)‖ = 1` for every `t ∈ ℝ`. -/
theorem norm_bianchiScatteringPhase_axis (t : ℝ) :
    ‖bianchiScatteringPhase ((t : ℂ) * I)‖ = 1 := by
  set z : ℂ := 1 + 2 * ((t : ℂ) * I) with hz
  have hzre : z.re = 1 := by rw [hz]; simp
  have hzne : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre
  have hxine : xiBianchi z ≠ 0 := xiBianchi_ne_zero_of_one_le_re (by linarith)
  have hconjz : starRingEnd ℂ z = 1 - 2 * ((t : ℂ) * I) := by
    rw [hz]
    simp [conj_two]
    ring
  have hden : 2 * ((t : ℂ) * I) - 1 = -starRingEnd ℂ z := by
    rw [hconjz]
    ring
  have hxi_num : xiBianchi (2 * ((t : ℂ) * I)) = starRingEnd ℂ (xiBianchi z) := by
    have h1 : (2 : ℂ) * ((t : ℂ) * I) = 1 - starRingEnd ℂ z := by rw [hconjz]; ring
    rw [h1, xiBianchi_one_sub, xiBianchi_conj]
  unfold bianchiScatteringPhase
  rw [show 1 + 2 * ((t : ℂ) * I) = z from rfl, hden, hxi_num, norm_mul, norm_div, norm_div,
    norm_neg, Complex.norm_conj, Complex.norm_conj,
    div_self (norm_ne_zero_iff.mpr hzne), div_self (norm_ne_zero_iff.mpr hxine), mul_one]

/-- Holomorphicity of `bianchiScatteringPhase` away from `1/2` and zeros of `ξ_K(1 + 2u)`. -/
theorem differentiableAt_bianchiScatteringPhase {u : ℂ}
    (hne : u ≠ 1 / 2) (hxi : xiBianchi (1 + 2 * u) ≠ 0) :
    DifferentiableAt ℂ bianchiScatteringPhase u := by
  have hd : 2 * u - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) / (2 * v - 1)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).div (by fun_prop) hd
  have h2 : DifferentiableAt ℂ (fun v : ℂ => xiBianchi (2 * v)) u :=
    (differentiable_xiBianchi _).comp u (by fun_prop)
  have h3 : DifferentiableAt ℂ (fun v : ℂ => xiBianchi (1 + 2 * v)) u :=
    (differentiable_xiBianchi _).comp u (by fun_prop)
  exact h1.mul (h2.div h3 hxi)

/-- Off the real axis, `bianchiScatteringPhase u` factors into the `SL₂(ℤ)` scattering ratio
`scatterQ (u + 1/2)`, the `χ₋₃` `L`-ratio, and the `χ₋₃` Archimedean gamma ratio. -/
theorem bianchiScatteringPhase_eq_factors {u : ℂ} (him : u.im ≠ 0) :
    bianchiScatteringPhase u =
      ((3 : ℂ) ^ (2 * u / 2) / (3 : ℂ) ^ ((1 + 2 * u) / 2)) *
        (2 / (2 * u - 1)) * scatterQ (u + 1 / 2) *
        (DirichletCharacter.LFunction chi3D (2 * u) *
          (DirichletCharacter.LFunction chi3D (1 + 2 * u))⁻¹ *
          (DirichletCharacter.gammaFactor chi3D (2 * u) /
            DirichletCharacter.gammaFactor chi3D (1 + 2 * u))) := by
  have h2im : (2 * u).im ≠ 0 := by simp [him]
  have h1im : (1 + 2 * u).im ≠ 0 := by simp [him]
  have h2ne0 : 2 * u ≠ 0 := fun h => h2im (by simp [h])
  have h1ne0 : 1 + 2 * u ≠ 0 := fun h => h1im (by simp [h])
  have h2m1 : 2 * u - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp [him] at this
  have hgf2 := gammaFactor_chi3D_ne_zero_of_im_ne_zero h2im
  have hgf1 := gammaFactor_chi3D_ne_zero_of_im_ne_zero h1im
  have hQ : scatterQ (u + 1 / 2) = (u + 1 / 2) * xi (2 * u) / xi (1 + 2 * u) := by
    unfold scatterQ
    rw [show 2 * (u + 1 / 2) - 1 = 2 * u by ring, show 2 * (u + 1 / 2) = 1 + 2 * u by ring]
  unfold bianchiScatteringPhase xiBianchi
  rw [hQ, completedLFunction_chi3D_eq_mul h2ne0 hgf2, completedLFunction_chi3D_eq_mul h1ne0 hgf1]
  have hu12 : u + 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp [him] at this
  field_simp
  congr 1
  ring

/-- Polynomial strip bound on `‖bianchiScatteringPhase u‖` for `a ≤ Re u ≤ b` (`-1 ≤ a`, `b ≤ 1`),
`1 ≤ |Im u|`, whenever `1/ζ(1 + 2u)` and `1/L(1 + 2u, χ₋₃)` grow at most polynomially. -/
theorem exists_norm_bianchiScatteringPhase_strip_le {a b K₁ K₂ : ℝ} {N₁ N₂ : ℕ}
    (ha : -1 ≤ a) (hb : b ≤ 1) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hζ : ∀ u : ℂ, a ≤ u.re → u.re ≤ b → 1 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ K₁ * |u.im| ^ N₁)
    (hL : ∀ u : ℂ, a ≤ u.re → u.re ≤ b → 1 ≤ |u.im| →
      ‖(DirichletCharacter.LFunction chi3D (1 + 2 * u))⁻¹‖ ≤ K₂ * |u.im| ^ N₂) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ u : ℂ, a ≤ u.re → u.re ≤ b → 1 ≤ |u.im| →
      ‖bianchiScatteringPhase u‖ ≤ C * |u.im| ^ M := by
  have hζ_shift : ∀ s : ℂ, a + 1 / 2 ≤ s.re → s.re ≤ b + 1 / 2 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ K₁ * |s.im| ^ N₁ := by
    intro s hs1 hs2 hsim
    have hs_eq : (2 : ℂ) * s = 1 + 2 * (s - 1 / 2) := by ring
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    have him : (s - 1 / 2).im = s.im := by simp
    rw [hs_eq, ← him]
    exact hζ (s - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hsim)
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le hK₁ hζ_shift
  obtain ⟨EL, hEL, hdisc⟩ := exists_bound_LFunction_disc chi3D_ne_one isPrimitive_chi3D
    (a := 0) (R := 2) (by norm_num) (by norm_num)
  obtain ⟨d, hd, hgf⟩ := gammaFactor_eq_Gammaℝ chi3D
  have hd0 : 0 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hd1 : d ≤ 1 := by rcases hd with rfl | rfl <;> norm_num
  obtain ⟨CΓ₁, NΓ₁, hCΓ₁, hΓ₁⟩ :=
    exists_sharp_bound_norm_Gamma_strip (a + d / 2) (b + d / 2)
  obtain ⟨CΓ₂, NΓ₂, hCΓ₂, hΓ₂⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_inv_Gamma_strip
      (a + (1 + d) / 2) (b + (1 + d) / 2)
  set CΓ : ℝ := Real.pi ^ (1 / 2 : ℝ) * (CΓ₁ * CΓ₂)
  refine ⟨CQ * (64 * EL * K₂ * CΓ), NQ + (3 + N₂ + (NΓ₁ + NΓ₂)), by positivity,
    fun u hu1 hu2 hut => ?_⟩
  have huim : u.im ≠ 0 := fun h => by rw [h, abs_zero] at hut; linarith
  rw [bianchiScatteringPhase_eq_factors huim, norm_mul, norm_mul, norm_mul]
  -- Factor 1: `‖3^u / 3^{1/2 + u}‖ ≤ 1`
  have h3le : ‖(3 : ℂ) ^ (2 * u / 2) / (3 : ℂ) ^ ((1 + 2 * u) / 2)‖ ≤ 1 := by
    rw [norm_div, show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num),
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have hre1 : (2 * u / 2).re = u.re := by simp
    have hre2 : ((1 + 2 * u) / 2).re = 1 / 2 + u.re := by simp; ring
    rw [hre1, hre2, div_le_one (Real.rpow_pos_of_pos (by norm_num) _)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- Factor 2: `‖2 / (2u - 1)‖ ≤ 1` on `|Im u| ≥ 1`
  have h2le : ‖(2 : ℂ) / (2 * u - 1)‖ ≤ 1 := by
    have him2 : (2 : ℝ) ≤ |(2 * u - 1).im| := by simp; linarith
    have hn2 : (2 : ℝ) ≤ ‖2 * u - 1‖ := him2.trans (Complex.abs_im_le_norm _)
    rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
    exact hn2
  -- Factor 3: `‖scatterQ (u + 1/2)‖`
  have hQb : ‖scatterQ (u + 1 / 2)‖ ≤ CQ * |u.im| ^ NQ := by
    have hre : (u + 1 / 2).re = u.re + 1 / 2 := by simp
    have him : (u + 1 / 2).im = u.im := by simp
    have hb := hQ (u + 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hut)
    rwa [him] at hb
  -- Factor 4: `‖L(2u, χ₋₃)‖ ≤ 64 EL |Im u|³`
  have hL2 : ‖DirichletCharacter.LFunction chi3D (2 * u)‖ ≤ 64 * EL * |u.im| ^ 3 := by
    have hdisc_u : ‖2 * u - (((0 : ℝ) : ℂ) + ((2 * u.im : ℝ) : ℂ) * I)‖ ≤ 2 := by
      have heq : 2 * u - (((0 : ℝ) : ℂ) + ((2 * u.im : ℝ) : ℂ) * I) = ((2 * u.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith, by linarith⟩
    have hb := hdisc (2 * u.im) (2 * u) hdisc_u
    have habs : 2 + |2 * u.im| ≤ 4 * |u.im| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    calc ‖DirichletCharacter.LFunction chi3D (2 * u)‖
        ≤ EL * (2 + |2 * u.im|) ^ 3 := hb
      _ ≤ EL * (4 * |u.im|) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) habs 3) hEL.le
      _ = 64 * EL * |u.im| ^ 3 := by ring
  -- Factor 5: `‖γ(2u, χ₋₃) / γ(1 + 2u, χ₋₃)‖ ≤ CΓ |Im u|^{NΓ₁ + NΓ₂}`
  have hΓb : ‖DirichletCharacter.gammaFactor chi3D (2 * u) /
      DirichletCharacter.gammaFactor chi3D (1 + 2 * u)‖ ≤ CΓ * |u.im| ^ (NΓ₁ + NΓ₂) := by
    set sd : ℂ := u + ((1 + d : ℝ) : ℂ) / 2 with hsd
    have hgf1 : DirichletCharacter.gammaFactor chi3D (2 * u) = Complex.Gammaℝ (2 * sd - 1) := by
      rw [hgf]; congr 1; rw [hsd]; push_cast; ring
    have hgf2 : DirichletCharacter.gammaFactor chi3D (1 + 2 * u) = Complex.Gammaℝ (2 * sd) := by
      rw [hgf]; congr 1; rw [hsd]; push_cast; ring
    rw [hgf1, hgf2, norm_gammaℝ_div]
    have hre1 : (sd - 1 / 2).re = u.re + d / 2 := by rw [hsd]; simp; ring
    have him1 : (sd - 1 / 2).im = u.im := by rw [hsd]; simp
    have hre2 : sd.re = u.re + (1 + d) / 2 := by rw [hsd]; simp
    have him2 : sd.im = u.im := by rw [hsd]; simp
    have hb1 := hΓ₁ (sd - 1 / 2) (by rw [hre1]; linarith) (by rw [hre1]; linarith)
      (by rw [him1]; exact hut)
    have hb2 := hΓ₂ sd (by rw [hre2]; linarith) (by rw [hre2]; linarith)
      (by rw [him2]; exact hut)
    rw [him1] at hb1
    rw [him2] at hb2
    have hprod : ‖Complex.Gamma (sd - 1 / 2)‖ * ‖(Complex.Gamma sd)⁻¹‖ ≤
        CΓ₁ * CΓ₂ * |u.im| ^ (NΓ₁ + NΓ₂) := by
      calc ‖Complex.Gamma (sd - 1 / 2)‖ * ‖(Complex.Gamma sd)⁻¹‖
          ≤ (CΓ₁ * |u.im| ^ NΓ₁ * Real.exp (-(Real.pi * |u.im| / 2))) *
              (CΓ₂ * |u.im| ^ NΓ₂ * Real.exp (Real.pi * |u.im| / 2)) :=
            mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
        _ = CΓ₁ * CΓ₂ * |u.im| ^ (NΓ₁ + NΓ₂) := by
            rw [pow_add]
            have hexp : Real.exp (-(Real.pi * |u.im| / 2)) * Real.exp (Real.pi * |u.im| / 2) = 1 := by
              rw [← Real.exp_add]; simp
            linear_combination (CΓ₁ * CΓ₂ * |u.im| ^ NΓ₁ * |u.im| ^ NΓ₂) * hexp
    calc Real.pi ^ (1 / 2 : ℝ) * (‖Complex.Gamma (sd - 1 / 2)‖ * ‖(Complex.Gamma sd)⁻¹‖)
        ≤ Real.pi ^ (1 / 2 : ℝ) * (CΓ₁ * CΓ₂ * |u.im| ^ (NΓ₁ + NΓ₂)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = CΓ * |u.im| ^ (NΓ₁ + NΓ₂) := by simp only [CΓ]; ring
  have hLinv := hL u hu1 hu2 hut
  rw [norm_mul, norm_mul]
  calc ‖(3 : ℂ) ^ (2 * u / 2) / (3 : ℂ) ^ ((1 + 2 * u) / 2)‖ * ‖(2 : ℂ) / (2 * u - 1)‖ *
        ‖scatterQ (u + 1 / 2)‖ *
        (‖DirichletCharacter.LFunction chi3D (2 * u)‖ *
          ‖(DirichletCharacter.LFunction chi3D (1 + 2 * u))⁻¹‖ *
          ‖DirichletCharacter.gammaFactor chi3D (2 * u) /
            DirichletCharacter.gammaFactor chi3D (1 + 2 * u)‖)
      ≤ 1 * 1 * (CQ * |u.im| ^ NQ) *
          ((64 * EL * |u.im| ^ 3) * (K₂ * |u.im| ^ N₂) * (CΓ * |u.im| ^ (NΓ₁ + NΓ₂))) := by
        gcongr
    _ = CQ * (64 * EL * K₂ * CΓ) * |u.im| ^ (NQ + (3 + N₂ + (NΓ₁ + NΓ₂))) := by
        simp only [pow_add]
        ring

/-! ## 3. Reflected Bianchi wavepackets and right-strip shift (`0 ≤ Re u ≤ 3/8`) -/

/-- Reflected wavepacket on the Bianchi horizon `SL₂(ℤ[ω])\ℍ³` produced by a compact pulse `h`
scattered off the spherical Eisenstein reflection phase `φ_K(it) = Λ_K(2it)/Λ_K(1 + 2it)`. -/
def bianchiReflectedField (h : CompactPulse) (τ : ℝ) : ℂ :=
  ∫ t : ℝ, pulseAmplitude h (t : ℂ) * bianchiScatteringPhase ((t : ℂ) * I) *
    Complex.exp (I * (t : ℂ) * (τ : ℂ))

/-- Spectral integral of the Bianchi pulse along a vertical line `Re u = c`. -/
def bianchiLineField (h : CompactPulse) (c τ : ℝ) : ℂ :=
  ∫ t : ℝ, pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    bianchiScatteringPhase ((c : ℂ) + (t : ℂ) * I) *
    Complex.exp (((c : ℂ) + (t : ℂ) * I) * (τ : ℂ))

theorem bianchiLineField_zero (h : CompactPulse) (τ : ℝ) :
    bianchiLineField h 0 τ = bianchiReflectedField h τ := by
  unfold bianchiLineField bianchiReflectedField
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
  rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
  congr 2
  ring

/-- Uniform bound and continuity of `bianchiReflectedField h` on `ℝ`. -/
theorem continuous_bianchiReflectedField_and_bounded (h : CompactPulse) :
    Continuous (bianchiReflectedField h) ∧
      ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ τ : ℝ, ‖bianchiReflectedField h τ‖ ≤ M₀ := by
  have hint_a : Integrable fun t : ℝ => ‖pulseAmplitude h (t : ℂ)‖ := by
    have h0 := (h.integrable_amplitude_line 0).norm
    refine h0.congr (Eventually.of_forall fun t => ?_)
    simp
  have hpt : ∀ (τ t : ℝ),
      ‖pulseAmplitude h (t : ℂ) * bianchiScatteringPhase ((t : ℂ) * I) *
        Complex.exp (I * (t : ℂ) * (τ : ℂ))‖ = ‖pulseAmplitude h (t : ℂ)‖ := by
    intro τ t
    rw [norm_mul, norm_mul, norm_bianchiScatteringPhase_axis, mul_one, Complex.norm_exp]
    have hre : (I * (t : ℂ) * (τ : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
  have hcont : Continuous (bianchiReflectedField h) := by
    unfold bianchiReflectedField
    refine continuous_of_dominated (bound := fun t : ℝ => ‖pulseAmplitude h (t : ℂ)‖) ?_ ?_ hint_a ?_
    · intro τ
      have hc : Continuous fun t : ℝ => pulseAmplitude h (t : ℂ) *
          bianchiScatteringPhase ((t : ℂ) * I) * Complex.exp (I * (t : ℂ) * (τ : ℂ)) := by
        refine ((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).mul ?_).mul
          (by fun_prop)
        refine continuous_iff_continuousAt.mpr fun t => ?_
        have hne : ((t : ℂ) * I) ≠ 1 / 2 := fun he => by
          have := congrArg Complex.re he; simp at this
        have hxi : xiBianchi (1 + 2 * ((t : ℂ) * I)) ≠ 0 :=
          xiBianchi_ne_zero_of_one_le_re (by simp)
        exact ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) * I)
          (differentiableAt_bianchiScatteringPhase hne hxi).continuousAt (by fun_prop)
      exact hc.aestronglyMeasurable
    · exact fun τ => ae_of_all _ fun t => (hpt τ t).le
    · refine ae_of_all _ fun t => ?_
      fun_prop
  refine ⟨hcont, ∫ t : ℝ, ‖pulseAmplitude h (t : ℂ)‖,
    integral_nonneg fun _ => norm_nonneg _, fun τ => ?_⟩
  unfold bianchiReflectedField
  exact norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun t => (hpt τ t).le)

/-- On the pole-free right strip `0 ≤ Re u ≤ 3/8` (where `1 ≤ Re(1 + 2u) ≤ 7/4` and `u ≠ 1/2`),
`‖a_h(-iu) φ_K(u)‖ ≤ B / (1 + Im² u)`. -/
theorem exists_amplitude_bianchi_right_le (h : CompactPulse) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 8 →
      ‖pulseAmplitude h (-I * u) * bianchiScatteringPhase u‖ ≤ B / (1 + u.im ^ 2) := by
  obtain ⟨C₁, hC₁, hζ_log⟩ := exists_norm_inv_LFunction_le_log_pow (1 : DirichletCharacter ℂ 1)
  obtain ⟨C₂, hC₂, hL_log⟩ := exists_norm_inv_LFunction_le_log_pow chi3D
  -- Compact box `1 ≤ Re z ≤ 2`, `2 ≤ |Im z| ≤ 10` for `1/ζ(z)` and `1/L(z, χ₋₃)`
  set boxR : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ 2 ≤ |z.im| ∧ |z.im| ≤ 10}
  have hboxR_c : IsCompact boxR := by
    have heq : boxR = ((Icc (1 : ℝ) 2) ×ℂ (Icc (-10 : ℝ) 10)) ∩ {z : ℂ | 2 ≤ |z.im|} := by
      ext z
      simp only [boxR, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζ : ContinuousOn (fun z : ℂ => (riemannZeta z)⁻¹) boxR := by
    intro z hz
    have hne1 : z ≠ 1 := fun h1 => by have := hz.2.1; rw [h1] at this; simp at this; linarith
    have hz0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz.1.1
    exact ((differentiableAt_riemannZeta hne1).continuousAt.inv₀ hz0).continuousWithinAt
  have hcont_L : ContinuousOn (fun z : ℂ => (DirichletCharacter.LFunction chi3D z)⁻¹) boxR := by
    intro z hz
    have hL0 : DirichletCharacter.LFunction chi3D z ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hz.1.1
    exact (((DirichletCharacter.differentiable_LFunction chi3D_ne_one).continuous.continuousAt).inv₀
      hL0).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hboxR_c.exists_bound_of_continuousOn hcont_ζ
  obtain ⟨M₂, hM₂⟩ := hboxR_c.exists_bound_of_continuousOn hcont_L
  have hlog_le_id : ∀ t : ℝ, 9 ≤ |t| → Real.log |t| ≤ |t| := fun t ht =>
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hζ_strip : ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 8 → 1 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ (max (max M₁ 0) (C₁ * 2 ^ 7)) * |u.im| ^ 7 := by
    intro u hu1 hu2 hut
    set z : ℂ := 1 + 2 * u with hzdef
    have hzre1 : 1 ≤ z.re := by rw [hzdef]; simp; linarith
    have hzre2 : z.re ≤ 2 := by rw [hzdef]; simp; linarith
    have hzim : |z.im| = 2 * |u.im| := by
      have : z.im = 2 * u.im := by rw [hzdef]; simp
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 7 := one_le_pow₀ hut
    rcases le_or_gt |z.im| 10 with hsmall | hbig
    · have hmem : z ∈ boxR := ⟨⟨hzre1, hzre2⟩, by linarith, hsmall⟩
      calc ‖(riemannZeta z)⁻¹‖ ≤ M₁ := hM₁ z hmem
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * 1 := by
            rw [mul_one]; exact (le_max_left M₁ 0).trans (le_max_left _ _)
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |u.im| ^ 7 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp
      have hb := hζ_log z.re z.im hzre1 hzre2 (by linarith)
      rw [DirichletCharacter.LFunction_modOne_eq, ← hz_eq] at hb
      have hlog : Real.log |z.im| ^ 7 ≤ (2 * |u.im|) ^ 7 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith))
          (by rw [← hzim]; exact hlog_le_id z.im (by linarith)) 7
      calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * Real.log |z.im| ^ 7 := hb
        _ ≤ C₁ * (2 * |u.im|) ^ 7 := mul_le_mul_of_nonneg_left hlog hC₁.le
        _ = (C₁ * 2 ^ 7) * |u.im| ^ 7 := by ring
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |u.im| ^ 7 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hL_strip : ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 8 → 1 ≤ |u.im| →
      ‖(DirichletCharacter.LFunction chi3D (1 + 2 * u))⁻¹‖ ≤
        (max (max M₂ 0) (C₂ * 2 ^ 7)) * |u.im| ^ 7 := by
    intro u hu1 hu2 hut
    set z : ℂ := 1 + 2 * u with hzdef
    have hzre1 : 1 ≤ z.re := by rw [hzdef]; simp; linarith
    have hzre2 : z.re ≤ 2 := by rw [hzdef]; simp; linarith
    have hzim : |z.im| = 2 * |u.im| := by
      have : z.im = 2 * u.im := by rw [hzdef]; simp
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 7 := one_le_pow₀ hut
    rcases le_or_gt |z.im| 10 with hsmall | hbig
    · have hmem : z ∈ boxR := ⟨⟨hzre1, hzre2⟩, by linarith, hsmall⟩
      calc ‖(DirichletCharacter.LFunction chi3D z)⁻¹‖ ≤ M₂ := hM₂ z hmem
        _ ≤ max (max M₂ 0) (C₂ * 2 ^ 7) * 1 := by
            rw [mul_one]; exact (le_max_left M₂ 0).trans (le_max_left _ _)
        _ ≤ max (max M₂ 0) (C₂ * 2 ^ 7) * |u.im| ^ 7 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp
      have hb := hL_log z.re z.im hzre1 hzre2 (by linarith)
      rw [← hz_eq] at hb
      have hlog : Real.log |z.im| ^ 7 ≤ (2 * |u.im|) ^ 7 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith))
          (by rw [← hzim]; exact hlog_le_id z.im (by linarith)) 7
      calc ‖(DirichletCharacter.LFunction chi3D z)⁻¹‖ ≤ C₂ * Real.log |z.im| ^ 7 := hb
        _ ≤ C₂ * (2 * |u.im|) ^ 7 := mul_le_mul_of_nonneg_left hlog hC₂.le
        _ = (C₂ * 2 ^ 7) * |u.im| ^ 7 := by ring
        _ ≤ max (max M₂ 0) (C₂ * 2 ^ 7) * |u.im| ^ 7 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨Cφ, Mφ, hCφ, hφ⟩ := exists_norm_bianchiScatteringPhase_strip_le
    (a := 0) (b := 3 / 8) (by norm_num) (by norm_num) (by positivity) (by positivity)
    hζ_strip hL_strip
  obtain ⟨Ca, hCa, hrap⟩ := h.rapidAmplitude.decay (3 / 8) (Mφ + 2)
  set Kbox : Set ℂ := Icc (0 : ℝ) (3 / 8) ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun u => pulseAmplitude h (-I * u) * bianchiScatteringPhase u) Kbox := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have h1 : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) u :=
      (h.differentiable_amplitude _).comp u (by fun_prop)
    have hne : u ≠ 1 / 2 := fun he => by
      have := hu'.1.2; rw [he] at this; norm_num at this
    have hxi : xiBianchi (1 + 2 * u) ≠ 0 :=
      xiBianchi_ne_zero_of_one_le_re (by simp; linarith [hu'.1.1])
    exact (h1.mul (differentiableAt_bianchiScatteringPhase hne hxi)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  refine ⟨max (2 * max B₀ 0) (Cφ * Ca), by positivity, fun u hu1 hu2 => ?_⟩
  by_cases hut : 1 ≤ |u.im|
  · have hφu := hφ u hu1 hu2 hut
    have hw1 : (-I * u).re = u.im := by simp
    have hw2 : (-I * u).im = -u.re := by simp
    have ha := hrap (-I * u) (by rw [hw2, abs_neg, abs_le]; exact ⟨by linarith, hu2⟩)
    rw [hw1] at ha
    have ht1 : |u.im| ^ Mφ ≤ (1 + |u.im|) ^ Mφ :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) Mφ
    have ht2 : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
    rw [le_div_iff₀ (by positivity), norm_mul]
    calc ‖pulseAmplitude h (-I * u)‖ * ‖bianchiScatteringPhase u‖ * (1 + u.im ^ 2)
        ≤ ‖pulseAmplitude h (-I * u)‖ * (Cφ * (1 + |u.im|) ^ Mφ) * (1 + |u.im|) ^ 2 := by
          gcongr
          exact hφu.trans (mul_le_mul_of_nonneg_left ht1 hCφ)
      _ = Cφ * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ (Mφ + 2)) := by ring
      _ ≤ Cφ * Ca := mul_le_mul_of_nonneg_left ha hCφ
      _ ≤ max (2 * max B₀ 0) (Cφ * Ca) := le_max_right _ _
  · have hut' := abs_le.1 (not_le.1 hut).le
    have hb := hB₀ u (Complex.mem_reProdIm.2 ⟨⟨hu1, hu2⟩, hut'⟩)
    have hsq : u.im ^ 2 ≤ 1 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc ‖pulseAmplitude h (-I * u) * bianchiScatteringPhase u‖ * (1 + u.im ^ 2)
        ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
          (le_max_right _ _)
      _ ≤ max (2 * max B₀ 0) (Cφ * Ca) := by
          linarith [le_max_left (2 * max B₀ 0) (Cφ * Ca)]

/-- Holomorphic vertical line shift on the pole-free strip `0 ≤ c ≤ 3/8`:
`bianchiReflectedField h τ = bianchiLineField h c τ` for all `τ ∈ ℝ`. -/
theorem bianchiReflectedField_eq_lineField (h : CompactPulse) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 3 / 8) (τ : ℝ) :
    bianchiReflectedField h τ = bianchiLineField h c τ := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchi_right_le h
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * bianchiScatteringPhase u *
    Complex.exp (u * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c → 0 ≤ s.re ∧ s.re ≤ 3 / 8 := by
    intro s hs
    rw [uIcc_of_le hc0] at hs
    exact ⟨hs.1, hs.2.trans hc1⟩
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have ha : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) s :=
      (h.differentiable_amplitude _).comp s (by fun_prop)
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at h2; norm_num at h2
    have hxi : xiBianchi (1 + 2 * s) ≠ 0 := xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
    exact (ha.mul (differentiableAt_bianchiScatteringPhase hne hxi)).mul (by fun_prop)
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c →
      ‖Φ s‖ ≤ (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hexp : ‖Complex.exp (s * (τ : ℂ))‖ ≤ Real.exp ((3 / 8) * |τ|) := by
      rw [Complex.norm_exp]
      have hre : (s * (τ : ℂ)).re = s.re * τ := by simp
      have habs_re : |s.re| ≤ 3 / 8 := by rw [abs_of_nonneg h1]; exact h2
      rw [hre]
      refine Real.exp_le_exp.mpr ?_
      calc s.re * τ ≤ |s.re * τ| := le_abs_self _
        _ = |s.re| * |τ| := abs_mul _ _
        _ ≤ (3 / 8) * |τ| := mul_le_mul_of_nonneg_right habs_re (abs_nonneg _)
    simp only [hΦ]
    rw [norm_mul]
    calc ‖pulseAmplitude h (-I * s) * bianchiScatteringPhase s‖ * ‖Complex.exp (s * (τ : ℂ))‖
        ≤ (B / (1 + s.im ^ 2)) * Real.exp ((3 / 8) * |τ|) :=
          mul_le_mul (hB s h1 h2) hexp (norm_nonneg _) (by positivity)
      _ = (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by ring
  rw [← bianchiLineField_zero]
  exact integral_vertical_line_shift_of_decay hd hbΦ

/-- Early-time decay (`τ ≤ 0`): shifting to `Re u = 3/8` gives
`‖bianchiReflectedField h τ‖ ≤ C e^{(3/8)τ}` for all `τ ≤ 0`. -/
theorem exists_bianchiReflectedField_early_decay (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, τ ≤ 0 →
      ‖bianchiReflectedField h τ‖ ≤ C * Real.exp ((3 / 8) * τ) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchi_right_le h
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  rw [bianchiReflectedField_eq_lineField h (c := 3 / 8) (by norm_num) le_rfl τ]
  unfold bianchiLineField
  have hpt : ∀ t : ℝ,
      ‖pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
        bianchiScatteringPhase (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
        Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖ ≤
      B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) := by
    intro t
    set u : ℂ := ((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I
    have hre : u.re = 3 / 8 := by simp [u]
    have him : u.im = t := by simp [u]
    rw [norm_mul, Complex.norm_exp]
    have hre_exp : (u * (τ : ℂ)).re = (3 / 8) * τ := by simp [u]
    rw [hre_exp]
    have hb := hB u (by rw [hre]; norm_num) (by rw [hre])
    rw [him, div_eq_mul_inv] at hb
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hint : Integrable fun t : ℝ => B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
    (integrable_inv_one_add_sq.const_mul B).mul_const _
  calc ‖∫ t : ℝ, pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
          bianchiScatteringPhase (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp ((3 / 8) * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

/-! ## 4. Forward direction: zero-free strip implies Bianchi pulse ringdown -/

section Forward

variable {δ σ : ℝ} (hδ : δ ≤ 1 / 4) (hσ : 0 < σ) (hσδ : σ < δ)
  (hz : ∀ ρ : ℂ, riemannZeta ρ * DirichletCharacter.LFunction chi3D ρ = 0 →
    0 < ρ.re → ρ.re ≤ 1 - 2 * δ)

include hδ hσδ hz in
theorem xiBianchi_ne_zero_of_zeroFree {u : ℂ} (h1 : -σ ≤ u.re) :
    xiBianchi (1 + 2 * u) ≠ 0 := by
  have hre : (1 + 2 * u).re = 1 + 2 * u.re := by simp
  rcases lt_or_ge (1 + 2 * u).re 1 with h | h
  · have hne : 1 + 2 * u ≠ 1 := fun he => by rw [he, one_re] at h; exact lt_irrefl _ h
    have hpos : 0 < (1 + 2 * u).re := by rw [hre]; linarith
    rw [Ne, xiBianchi_eq_zero_iff hpos hne]
    intro h0
    have := hz _ h0 hpos
    rw [hre] at this
    linarith
  · exact xiBianchi_ne_zero_of_one_le_re h

include hδ hz in
theorem zeroAbscissa_chi3D_le_of_zeroFree : zeroAbscissa chi3D ≤ 1 - 2 * δ := by
  refine csSup_le (zeroReSet_nonempty chi3D_ne_one isPrimitive_chi3D) fun x hx => ?_
  obtain ⟨ρ, hL0, rfl⟩ := hx
  rcases le_or_gt ρ.re 0 with hle | hgt
  · linarith
  · exact hz ρ (by rw [hL0, mul_zero]) hgt

include hδ hσ hσδ hz in
/-- On `-σ ≤ Re u ≤ 0`, `0 < σ < δ ≤ 1/4`, `‖a_h(-iu) φ_K(u)‖ ≤ B / (1 + Im² u)` under the
Dedekind zero-free strip `Re ρ ≤ 1 - 2δ`. -/
theorem exists_amplitude_bianchi_left_le (h : CompactPulse) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖pulseAmplitude h (-I * u) * bianchiScatteringPhase u‖ ≤ B / (1 + u.im ^ 2) := by
  set Θ : ℝ := 1 - 2 * δ with hΘ
  have hzf_ζ : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz' h0 => by
    have := hz z (by rw [h0, zero_mul]) (by linarith)
    linarith
  obtain ⟨κ₁, hκ₁, hζ_lb⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree (Θ := Θ)
    (by linarith) (by linarith) hzf_ζ (δ := 2 * (δ - σ)) (by linarith) (by linarith)
    (ε := 1) one_pos
  have habs_L : zeroAbscissa chi3D ≤ Θ := zeroAbscissa_chi3D_le_of_zeroFree hδ hz
  obtain ⟨κ₂, hκ₂, hL_lb⟩ := exists_lower_bound_subpolynomial chi3D_ne_one isPrimitive_chi3D
    (δ := 2 * (δ - σ)) (by linarith) (by linarith) (ε := 1) one_pos
  -- Compact box `-σ ≤ Re u ≤ 0`, `1 ≤ |Im u| ≤ 3` for `1/ζ(1 + 2u)` to bridge `[1, 3]`
  set boxU : Set ℂ := {u : ℂ | (-σ ≤ u.re ∧ u.re ≤ 0) ∧ 1 ≤ |u.im| ∧ |u.im| ≤ 3}
  have hboxU_c : IsCompact boxU := by
    have heq : boxU = ((Icc (-σ) 0) ×ℂ (Icc (-3 : ℝ) 3)) ∩ {u : ℂ | 1 ≤ |u.im|} := by
      ext u
      simp only [boxU, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζU : ContinuousOn (fun u : ℂ => (riemannZeta (1 + 2 * u))⁻¹) boxU := by
    intro u hu
    have hne1 : 1 + 2 * u ≠ 1 := fun h1 => by
      have him0 := congrArg Complex.im h1
      simp at him0
      have huim := hu.2.1
      rw [him0, abs_zero] at huim
      linarith
    have hz0 : riemannZeta (1 + 2 * u) ≠ 0 := hzf_ζ _ (by simp; linarith [hu.1.1])
    have hc : ContinuousAt (fun v : ℂ => riemannZeta (1 + 2 * v)) u :=
      ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt (by fun_prop)
    exact (hc.inv₀ hz0).continuousWithinAt
  obtain ⟨Mζ, hMζ⟩ := hboxU_c.exists_bound_of_continuousOn hcont_ζU
  have hζ_strip : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 → 1 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ (max (max Mζ 0) (4 / κ₁)) * |u.im| ^ 1 := by
    intro u hu1 hu2 hut
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 1 := by simpa using hut
    rcases le_or_gt |u.im| 3 with hsmall | hbig
    · have hmem : u ∈ boxU := ⟨⟨hu1, hu2⟩, hut, hsmall⟩
      calc ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ Mζ := hMζ u hmem
        _ ≤ max (max Mζ 0) (4 / κ₁) * 1 := by
            rw [mul_one]; exact (le_max_left Mζ 0).trans (le_max_left _ _)
        _ ≤ max (max Mζ 0) (4 / κ₁) * |u.im| ^ 1 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have him : |(1 + 2 * u).im| = 2 * |u.im| := by
        have : (1 + 2 * u).im = 2 * u.im := by simp
        rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := hζ_lb (1 + 2 * u) (by simp; linarith) (by rw [him]; linarith)
      rw [Real.rpow_neg_one, him] at hb
      have hpos : 0 < ‖riemannZeta (1 + 2 * u)‖ := lt_of_lt_of_le (by positivity) hb
      rw [norm_inv, inv_le_comm₀ hpos (by positivity)]
      have h2t : 2 + 2 * |u.im| ≤ 4 * |u.im| := by linarith
      calc (max (max Mζ 0) (4 / κ₁) * |u.im| ^ 1)⁻¹
          ≤ ((4 / κ₁) * |u.im|)⁻¹ := by
            rw [pow_one]
            exact inv_anti₀ (by positivity)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        _ = κ₁ * (4 * |u.im|)⁻¹ := by field_simp
        _ ≤ κ₁ * (2 + 2 * |u.im|)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2t) hκ₁.le
        _ ≤ ‖riemannZeta (1 + 2 * u)‖ := hb
  have hL_strip : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 → 1 ≤ |u.im| →
      ‖(DirichletCharacter.LFunction chi3D (1 + 2 * u))⁻¹‖ ≤ (4 / κ₂) * |u.im| ^ 1 := by
    intro u hu1 _ hut
    have him : |(1 + 2 * u).im| = 2 * |u.im| := by
      have : (1 + 2 * u).im = 2 * u.im := by simp
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hb := hL_lb (1 + 2 * u) (by simp; linarith)
    rw [Real.rpow_neg_one, him] at hb
    have hpos : 0 < ‖DirichletCharacter.LFunction chi3D (1 + 2 * u)‖ :=
      lt_of_lt_of_le (by positivity) hb
    rw [norm_inv, pow_one, inv_le_comm₀ hpos (by positivity)]
    have h2t : 2 + 2 * |u.im| ≤ 4 * |u.im| := by linarith
    calc ((4 / κ₂) * |u.im|)⁻¹ = κ₂ * (4 * |u.im|)⁻¹ := by field_simp
      _ ≤ κ₂ * (2 + 2 * |u.im|)⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2t) hκ₂.le
      _ ≤ ‖DirichletCharacter.LFunction chi3D (1 + 2 * u)‖ := hb
  obtain ⟨Cφ, Mφ, hCφ, hφ⟩ := exists_norm_bianchiScatteringPhase_strip_le
    (a := -σ) (b := 0) (by linarith) (by norm_num) (by positivity) (by positivity)
    hζ_strip hL_strip
  obtain ⟨Ca, hCa, hrap⟩ := h.rapidAmplitude.decay σ (Mφ + 2)
  set Kbox : Set ℂ := Icc (-σ) 0 ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun u => pulseAmplitude h (-I * u) * bianchiScatteringPhase u) Kbox := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have h1 : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) u :=
      (h.differentiable_amplitude _).comp u (by fun_prop)
    have hne : u ≠ 1 / 2 := fun he => by
      have := hu'.1.2; rw [he] at this; norm_num at this
    have hxi := xiBianchi_ne_zero_of_zeroFree hδ hσδ hz hu'.1.1
    exact (h1.mul (differentiableAt_bianchiScatteringPhase hne hxi)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  refine ⟨max (2 * max B₀ 0) (Cφ * Ca), by positivity, fun u hu1 hu2 => ?_⟩
  by_cases hut : 1 ≤ |u.im|
  · have hφu := hφ u hu1 hu2 hut
    have hw1 : (-I * u).re = u.im := by simp
    have hw2 : (-I * u).im = -u.re := by simp
    have ha := hrap (-I * u) (by rw [hw2, abs_neg, abs_le]; constructor <;> linarith)
    rw [hw1] at ha
    have ht1 : |u.im| ^ Mφ ≤ (1 + |u.im|) ^ Mφ :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) Mφ
    have ht2 : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
    rw [le_div_iff₀ (by positivity), norm_mul]
    calc ‖pulseAmplitude h (-I * u)‖ * ‖bianchiScatteringPhase u‖ * (1 + u.im ^ 2)
        ≤ ‖pulseAmplitude h (-I * u)‖ * (Cφ * (1 + |u.im|) ^ Mφ) * (1 + |u.im|) ^ 2 := by
          gcongr
          exact hφu.trans (mul_le_mul_of_nonneg_left ht1 hCφ)
      _ = Cφ * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ (Mφ + 2)) := by ring
      _ ≤ Cφ * Ca := mul_le_mul_of_nonneg_left ha hCφ
      _ ≤ max (2 * max B₀ 0) (Cφ * Ca) := le_max_right _ _
  · have hut' := abs_le.1 (not_le.1 hut).le
    have hb := hB₀ u (Complex.mem_reProdIm.2 ⟨⟨hu1, hu2⟩, hut'⟩)
    have hsq : u.im ^ 2 ≤ 1 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc ‖pulseAmplitude h (-I * u) * bianchiScatteringPhase u‖ * (1 + u.im ^ 2)
        ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
          (le_max_right _ _)
      _ ≤ max (2 * max B₀ 0) (Cφ * Ca) := by
          linarith [le_max_left (2 * max B₀ 0) (Cφ * Ca)]

include hδ hσ hσδ hz in
/-- Forward direction: a zero-free strip `Re ρ ≤ 1 - 2δ` for `ζ(s) L(s, χ₋₃)` implies
`‖bianchiReflectedField h τ‖ ≤ C e^{-στ}` for every `0 < σ < δ` and `τ ≥ 0`. -/
theorem bianchiReflectedField_decay_of_zeroFree (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-σ * τ) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchi_left_le hδ hσ hσδ hz h
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * bianchiScatteringPhase u *
    Complex.exp (u * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → -σ ≤ s.re ∧ s.re ≤ 0 := by
    intro s hs
    rw [uIcc_of_ge (by linarith)] at hs
    exact hs
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have ha : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) s :=
      (h.differentiable_amplitude _).comp s (by fun_prop)
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at h2; norm_num at h2
    have hxi := xiBianchi_ne_zero_of_zeroFree hδ hσδ hz h1
    exact (ha.mul (differentiableAt_bianchiScatteringPhase hne hxi)).mul (by fun_prop)
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → ‖Φ s‖ ≤ B / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have he : ‖Complex.exp (s * (τ : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (s * (τ : ℂ)).re = s.re * τ := by simp
      rw [this]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg h2 hτ)
    simp only [hΦ]
    rw [norm_mul]
    calc ‖pulseAmplitude h (-I * s) * bianchiScatteringPhase s‖ * ‖Complex.exp (s * (τ : ℂ))‖
        ≤ B / (1 + s.im ^ 2) * 1 := mul_le_mul (hB s h1 h2) he (norm_nonneg _) (by positivity)
      _ = B / (1 + s.im ^ 2) := mul_one _
  have hshift := integral_vertical_line_shift_of_decay hd hbΦ
  have hpk : bianchiReflectedField h τ = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [← bianchiLineField_zero]
    rfl
  rw [hpk, hshift]
  have hpt : ∀ t : ℝ,
      ‖Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) := by
    intro t
    have hre : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).re = -σ := by simp
    have him : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
    simp only [hΦ]
    rw [norm_mul, Complex.norm_exp]
    have : ((((-σ : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ)).re = -σ * τ := by simp
    rw [this]
    have hb := hB _ (by rw [hre]) (by rw [hre]; linarith)
    rw [him, div_eq_mul_inv] at hb
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hint : Integrable fun t : ℝ => B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) :=
    (integrable_inv_one_add_sq.const_mul B).mul_const _
  calc ‖∫ t : ℝ, Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp (-σ * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

end Forward

/-! ## 5. Converse direction: bilateral Laplace–Fourier inversion and mode excitation -/

/-- Bilateral Laplace identity on `1/8 < Re w < 5/16`: the two half-line Laplace integrals of
`bianchiReflectedField h` sum to `2π a_h(-iw) φ_K(w)`. -/
theorem bianchi_bilateral_laplace_eq (h : CompactPulse) {w : ℂ}
    (hw1 : 1 / 8 < w.re) (hw2 : w.re < 5 / 16) :
    (∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * bianchiReflectedField h τ) +
      (∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * bianchiReflectedField h (-σ)) =
      2 * Real.pi * pulseAmplitude h (-I * w) * bianchiScatteringPhase w := by
  set c : ℝ := w.re
  set η : ℝ := w.im
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c ≤ 3 / 8 := by linarith
  have hw_eq : w = (c : ℂ) + (η : ℂ) * I := by apply Complex.ext <;> simp [c, η]
  obtain ⟨hGc, M₀, hM₀, hGb⟩ := continuous_bianchiReflectedField_and_bounded h
  obtain ⟨Ce, hCe, hGe⟩ := exists_bianchiReflectedField_early_decay h
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchi_right_le h
  -- Spectral profile `f(t) = a_h(-i(c + it)) φ_K(c + it)` on the line `Re u = c`
  set f : ℝ → ℂ := fun t => pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    bianchiScatteringPhase ((c : ℂ) + (t : ℂ) * I) with hf_def
  have hf_cont : Continuous f := by
    refine (h.differentiable_amplitude.continuous.comp (by fun_prop)).mul ?_
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : ((c : ℂ) + (t : ℂ) * I) ≠ 1 / 2 := fun he => by
      have := congrArg Complex.re he; simp at this; linarith
    have hxi : xiBianchi (1 + 2 * ((c : ℂ) + (t : ℂ) * I)) ≠ 0 :=
      xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
      (differentiableAt_bianchiScatteringPhase hne hxi).continuousAt (by fun_prop)
  have hf_int : Integrable f := by
    refine (integrable_inv_one_add_sq.const_mul B).mono' hf_cont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hb := hB ((c : ℂ) + (t : ℂ) * I) (by simp; exact hc0) (by simp; exact hc1)
    simpa [hf_def, div_eq_mul_inv] using hb
  -- Damped reflected field `g(τ) = e^{-cτ} G(τ)` is continuous and `L¹(ℝ)`
  set g : ℝ → ℂ := fun τ => Complex.exp (-(c : ℂ) * (τ : ℂ)) * bianchiReflectedField h τ with hg_def
  have hg_cont : Continuous g := (by fun_prop : Continuous fun τ : ℝ =>
    Complex.exp (-(c : ℂ) * (τ : ℂ))).mul hGc
  have hg_pos : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn (fun τ : ℝ => M₀ * Real.exp (-c * τ)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M₀
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ _ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(c : ℂ) * (τ : ℂ)).re = -c * τ := by simp
    rw [hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb τ) (Real.exp_pos _).le
  have hg_neg : IntegrableOn g (Iic (0 : ℝ)) := by
    have hdom_i : IntegrableOn (fun σ : ℝ => Ce * Real.exp (-(3 / 8 - c) * σ)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul Ce
    have hdom : IntegrableOn (fun τ : ℝ => Ce * Real.exp ((3 / 8 - c) * τ)) (Iic (0 : ℝ)) := by
      rw [← integrable_indicator_iff measurableSet_Iic]
      have h1 := (integrable_indicator_iff measurableSet_Ioi).mpr hdom_i
      refine (h1.comp_neg).congr ?_
      have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
        rw [ae_iff]
        have hset : {τ : ℝ | ¬τ ≠ 0} = ({0} : Set ℝ) := by ext τ; simp
        rw [hset]
        exact measure_singleton 0
      refine hae.mono fun τ hτ => ?_
      dsimp only
      rcases lt_or_gt_of_ne hτ with hlt | hgt
      · rw [indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_mem (show τ ∈ Iic (0 : ℝ) from hlt.le)]
        ring_nf
      · rw [indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_notMem (show τ ∉ Iic (0 : ℝ) by simp; linarith)]
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun τ hτ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(c : ℂ) * (τ : ℂ)).re = -c * τ := by simp
    rw [hre]
    calc Real.exp (-c * τ) * ‖bianchiReflectedField h τ‖
        ≤ Real.exp (-c * τ) * (Ce * Real.exp ((3 / 8) * τ)) :=
          mul_le_mul_of_nonneg_left (hGe τ hτ) (Real.exp_pos _).le
      _ = Ce * Real.exp ((3 / 8 - c) * τ) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hg_int : Integrable g := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hg_neg.union hg_pos
  -- Express `g = 𝓕⁻ F` with `F(v) = 2π f(2π v)` and invert via `Continuous.fourier_fourierInv_eq`
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
  set F : ℝ → ℂ := fun v => (2 * Real.pi : ℂ) * f (2 * Real.pi * v) with hF_def
  have hF_cont : Continuous F := continuous_const.mul (hf_cont.comp (by fun_prop))
  have hF_int : Integrable F := (hf_int.comp_mul_left' hpi0).const_mul (2 * Real.pi : ℂ)
  have hFinv_eq : 𝓕⁻ F = g := by
    funext τ
    rw [fourierInv_eq_integral_exp]
    have hg_sub := Measure.integral_comp_mul_left
      (fun y : ℝ => f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) (2 * Real.pi)
    have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
    rw [habs, Complex.real_smul] at hg_sub
    have hrw : ∀ v : ℝ, Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) • F v =
        (2 * Real.pi : ℂ) * (f (2 * Real.pi * v) *
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ))) := by
      intro v
      simp only [hF_def, smul_eq_mul]
      have he : Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) =
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ)) := by
        congr 1; push_cast; ring
      rw [he]; ring
    simp_rw [hrw]
    rw [integral_const_mul, hg_sub]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
    simp only [hg_def]
    rw [bianchiReflectedField_eq_lineField h hc0 hc1 τ]
    unfold bianchiLineField
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    have he : Complex.exp (((c : ℂ) + (y : ℂ) * I) * (τ : ℂ)) =
        Complex.exp ((c : ℂ) * (τ : ℂ)) * Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hc_cancel : Complex.exp (-(c : ℂ) * (τ : ℂ)) * Complex.exp ((c : ℂ) * (τ : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      have : -(c : ℂ) * (τ : ℂ) + (c : ℂ) * (τ : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [he]
    linear_combination (f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) * (-hc_cancel)
  have hFF_eq : 𝓕 F = fun x => g (-x) := by
    funext x
    have h1 := Real.fourierInv_eq_fourier_neg F (-x)
    rw [neg_neg, hFinv_eq] at h1
    exact h1.symm
  have hFF_int : Integrable (𝓕 F) := by
    rw [hFF_eq]
    exact hg_int.comp_neg
  have hinv := hF_cont.fourier_fourierInv_eq hF_int hFF_int
  rw [hFinv_eq] at hinv
  have hval := congrFun hinv (η / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul] at hval
  have hF_eval : F (η / (2 * Real.pi)) =
      2 * Real.pi * pulseAmplitude h (-I * w) * bianchiScatteringPhase w := by
    simp only [hF_def, hf_def]
    rw [mul_div_cancel₀ _ hpi0, ← hw_eq]
    ring
  -- Identify `𝓕 g (η / (2π))` with the sum of the two half-line Laplace integrals
  set H : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * bianchiReflectedField h τ with hH_def
  have hH_eq : ∀ τ : ℝ,
      Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ = H τ := by
    intro τ
    simp only [smul_eq_mul, hg_def, hH_def]
    have hexp : Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) *
        Complex.exp (-(c : ℂ) * (τ : ℂ)) = Complex.exp (-w * (τ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      have hdiv : -2 * Real.pi * τ * (η / (2 * Real.pi)) = -η * τ := by field_simp
      rw [hdiv, hw_eq]
      push_cast
      ring
    rw [← mul_assoc, hexp]
  have hH_int : Integrable H := by
    refine (hg_int.norm).mono' ((by fun_prop : Continuous fun τ : ℝ =>
      Complex.exp (-w * (τ : ℂ))).mul hGc).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [← hH_eq τ, smul_eq_mul, norm_mul, Complex.norm_exp]
    have hre : (((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) : ℂ) * I).re = 0 := by
      generalize -2 * Real.pi * τ * (η / (2 * Real.pi)) = r
      simp
    rw [hre, Real.exp_zero, one_mul]
  have hsplit : (∫ τ in Ioi (0 : ℝ), H τ) + (∫ τ in Iic (0 : ℝ), H τ) = ∫ τ : ℝ, H τ := by
    have h1 := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hH_int
    rwa [compl_Ioi] at h1
  have hneg_eq : (∫ τ in Iic (0 : ℝ), H τ) =
      ∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * bianchiReflectedField h (-σ) := by
    rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi,
      ← integral_neg_eq_self]
    have hae : ∀ᵐ σ : ℝ, σ ≠ 0 := by
      rw [ae_iff]
      have hset : {σ : ℝ | ¬σ ≠ 0} = ({0} : Set ℝ) := by ext σ; simp
      rw [hset]
      exact measure_singleton 0
    refine integral_congr_ae (hae.mono fun σ hσ => ?_)
    dsimp only
    rcases lt_or_gt_of_ne hσ with hlt | hgt
    · rw [indicator_of_notMem (show -σ ∉ Iic (0 : ℝ) by simp; linarith),
        indicator_of_notMem (show σ ∉ Ioi (0 : ℝ) by simp; linarith)]
    · rw [indicator_of_mem (show -σ ∈ Iic (0 : ℝ) by simp; linarith),
        indicator_of_mem (show σ ∈ Ioi (0 : ℝ) from hgt)]
      simp only [hH_def]
      push_cast
      ring_nf
  rw [← hneg_eq, hsplit]
  calc ∫ τ : ℝ, H τ
      = ∫ τ : ℝ, Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ :=
        integral_congr_ae (Eventually.of_forall fun τ => (hH_eq τ).symm)
    _ = F (η / (2 * Real.pi)) := hval
    _ = 2 * Real.pi * pulseAmplitude h (-I * w) * bianchiScatteringPhase w := hF_eval

/-- Converse direction: if every compact pulse scattered off the Bianchi horizon decays as
`O(e^{-δτ})` (`δ > 0`), then every zero of `ζ(s) L(s, χ₋₃)` with `Re ρ > 0` satisfies
`Re ρ ≤ 1 - 2δ`. -/
theorem re_le_of_bianchi_pulse_ringdown {δ : ℝ} (_hδ : 0 < δ)
    (hdecay : ∀ h : CompactPulse, ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-δ * τ))
    {ρ : ℂ} (hρ : riemannZeta ρ * DirichletCharacter.LFunction chi3D ρ = 0)
    (hρ0 : 0 < ρ.re) : ρ.re ≤ 1 - 2 * δ := by
  by_contra hlt
  push Not at hlt
  have hρ1 : ρ.re < 1 := by
    by_contra hge
    push Not at hge
    exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hge)
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hge) hρ
  have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  set p : ℂ := (ρ - 1) / 2 with hpdef
  have hp1 : 1 + 2 * p = ρ := by rw [hpdef]; ring
  have hpxi : xiBianchi (1 + 2 * p) = 0 := by rw [hp1]; exact (xiBianchi_eq_zero_iff hρ0 hne1).2 hρ
  have hpre : p.re = (ρ.re - 1) / 2 := by rw [hpdef]; simp
  have hp_neg : p.re < 0 := by rw [hpre]; linarith
  have hp_gt : -δ < p.re := by rw [hpre]; linarith
  set h := excitingPulse p
  obtain ⟨C₀, hC₀⟩ := hdecay h
  obtain ⟨hGc, -⟩ := continuous_bianchiReflectedField_and_bounded h
  obtain ⟨Ce, hCe, hGe⟩ := exists_bianchiReflectedField_early_decay h
  -- `L_+(w)` is holomorphic on `Re w > -δ`
  set Lpos : ℂ → ℂ := fun w => ∫ τ in Ioi (0 : ℝ),
    Complex.exp (-w * (τ : ℂ)) * bianchiReflectedField h τ with hLpos
  have hC₀' : ∀ τ : ℝ, -0 < τ → ‖bianchiReflectedField h τ‖ ≤ max C₀ 0 * Real.exp (-δ * τ) :=
    fun τ hτ => (hC₀ τ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hLpos_d : DifferentiableOn ℂ Lpos {w : ℂ | -δ < w.re} := by
    simpa [hLpos] using differentiableOn_laplace hGc (le_max_right C₀ 0) hC₀'
  -- `L_-(w)` is holomorphic on `Re w < 3/8`
  set Lneg₀ : ℂ → ℂ := fun z => ∫ σ in Ioi (0 : ℝ),
    Complex.exp (-z * (σ : ℂ)) * bianchiReflectedField h (-σ) with hLneg₀
  have hGe' : ∀ σ : ℝ, -(0 : ℝ) < σ →
      ‖bianchiReflectedField h (-σ)‖ ≤ Ce * Real.exp (-(3 / 8) * σ) := by
    intro σ hσ
    simpa [mul_neg, neg_mul] using hGe (-σ) (by linarith)
  have hLneg₀_d : DifferentiableOn ℂ Lneg₀ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by
    simpa [hLneg₀] using differentiableOn_laplace (hGc.comp continuous_neg) hCe hGe'
  set Lneg : ℂ → ℂ := fun w => Lneg₀ (-w) with hLneg
  have hLneg_d : DifferentiableOn ℂ Lneg {w : ℂ | w.re < 3 / 8} := by
    intro w hw
    have hw' : -w ∈ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by show -(3 / 8 : ℝ) < (-w).re; simp; exact hw
    have hopen : IsOpen {z : ℂ | -(3 / 8 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
    exact ((hLneg₀_d (-w) hw').differentiableAt (hopen.mem_nhds hw')).comp w differentiableAt_id.neg
      |>.differentiableWithinAt
  -- Analytic continuation across the open strip `S = {-δ < Re w < 3/8}`
  set S : Set ℂ := {w : ℂ | -δ < w.re ∧ w.re < 3 / 8} with hS
  have hSo : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hSconn : IsPreconnected S :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt (3 / 8))).isPreconnected
  set Φ₁ : ℂ → ℂ := fun w => (2 * w - 1) * xiBianchi (1 + 2 * w) * (Lpos w + Lneg w) with hΦ₁
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiBianchi (2 * w) with hΦ₂
  have hUpos : IsOpen {w : ℂ | -δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUneg : IsOpen {w : ℂ | w.re < 3 / 8} := isOpen_lt Complex.continuous_re continuous_const
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w hw
    have h1 := (hLpos_d w hw.1).differentiableAt (hUpos.mem_nhds hw.1)
    have h2 := (hLneg_d w hw.2).differentiableAt (hUneg.mem_nhds hw.2)
    have hxi : DifferentiableAt ℂ (fun v : ℂ => xiBianchi (1 + 2 * v)) w :=
      (differentiable_xiBianchi _).comp w (by fun_prop)
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul hxi).mul
      (h1.add h2)).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w _
    have ha : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) w :=
      (h.differentiable_amplitude _).comp w (by fun_prop)
    have hxi : DifferentiableAt ℂ (fun v : ℂ => xiBianchi (2 * v)) w :=
      (differentiable_xiBianchi _).comp w (by fun_prop)
    exact ((((differentiableAt_const _).mul ha).mul (by fun_prop)).mul hxi).differentiableWithinAt
  have hagree : ∀ w : ℂ, 1 / 8 < w.re → w.re < 5 / 16 → Φ₁ w = Φ₂ w := by
    intro w hw1 hw2
    have hlap : Lpos w + Lneg w =
        2 * Real.pi * pulseAmplitude h (-I * w) * bianchiScatteringPhase w := by
      have hneg_rw : Lneg w = ∫ σ in Ioi (0 : ℝ),
          Complex.exp (w * (σ : ℂ)) * bianchiReflectedField h (-σ) := by
        simp only [hLneg, hLneg₀, neg_neg]
      rw [hneg_rw]
      exact bianchi_bilateral_laplace_eq h hw1 hw2
    have h2w : 2 * w - 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hxi : xiBianchi (1 + 2 * w) ≠ 0 := xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
    simp only [hΦ₁, hΦ₂, hlap, bianchiScatteringPhase]
    field_simp
  have hEq : EqOn Φ₁ Φ₂ S := by
    refine hΦ₁a.eqOn_of_preconnected_of_eventuallyEq hΦ₂a hSconn
      (show (1 / 4 : ℂ) ∈ S from ⟨by simp; linarith, by norm_num⟩) ?_
    have hV : IsOpen {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hV.mem_nhds (show (1 / 4 : ℂ) ∈ {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} by
      norm_num)] with w hw
    exact hagree w hw.1 hw.2
  have hpS : p ∈ S := ⟨hp_gt, by linarith⟩
  have hp_eq := hEq hpS
  simp only [hΦ₁, hΦ₂, hpxi, mul_zero, zero_mul] at hp_eq
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have ha_ne : pulseAmplitude h (-I * p) ≠ 0 := pulseAmplitude_excitingPulse_ne_zero p
  have h12p : 1 + 2 * p ≠ 0 := by
    rw [hp1]
    exact fun h0 => by rw [h0] at hρ0; simp at hρ0
  have hxi2p : xiBianchi (2 * p) ≠ 0 := xiBianchi_two_mul_ne_zero_of_re_nonpos hp_neg.le
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi ha_ne) h12p) hxi2p hp_eq.symm

/-! ## 6. Main Equivalence Theorems on the Bianchi Horizon -/

/-- **Bianchi Horizon Ringdown Equivalence.** For `0 < δ ≤ 1/4`, `ζ(s) L(s, χ₋₃)` has no zeros in
`Re ρ > 1 - 2δ` (`Re ρ > 0`) if and only if every compact pulse reflected off the Bianchi
Eisenstein horizon `SL₂(ℤ[ω])\ℍ³` rings down at rate `O(e^{-(δ - ε)τ})` for every `ε > 0`. -/
theorem bianchi_zeroFreeStrip_iff_pulse_ringdown {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (∀ ρ : ℂ, riemannZeta ρ * DirichletCharacter.LFunction chi3D ρ = 0 →
      0 < ρ.re → ρ.re ≤ 1 - 2 * δ) ↔
      ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse, ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(δ - ε) * τ) := by
  constructor
  · intro hz ε hε h
    have hm0 : 0 < min ε (δ / 2) := lt_min hε (by linarith)
    have hm1 : min ε (δ / 2) ≤ δ / 2 := min_le_right _ _
    have hm2 : min ε (δ / 2) ≤ ε := min_le_left _ _
    obtain ⟨C, hC, hbd⟩ := bianchiReflectedField_decay_of_zeroFree
      (σ := δ - min ε (δ / 2)) hδ (by linarith) (by linarith) hz h
    refine ⟨C, fun τ hτ => (hbd τ hτ).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)⟩
    nlinarith
  · intro hr ρ hρ hρ0
    by_contra hlt
    push Not at hlt
    have hρ1 : ρ.re < 1 := by
      by_contra hge
      push Not at hge
      exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hge)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hge) hρ
    set ε : ℝ := (ρ.re - (1 - 2 * δ)) / 4 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hεδ : ε < δ := by rw [hε]; linarith
    have := re_le_of_bianchi_pulse_ringdown (δ := δ - ε) (by linarith) (hr ε hε0) hρ hρ0
    linarith

/-- Formulation of the Bianchi horizon ringdown equivalence directly in terms of the entire
Dedekind completion `xiBianchi`. -/
theorem bianchi_xi_zeroFreeStrip_iff_pulse_ringdown {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (∀ ρ : ℂ, xiBianchi ρ = 0 → ρ.re ≤ 1 - 2 * δ) ↔
      ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse, ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(δ - ε) * τ) := by
  rw [← bianchi_zeroFreeStrip_iff_pulse_ringdown hδ0 hδ]
  constructor
  · intro hxi ρ hprod hρ0
    have hρ1 : ρ.re < 1 := by
      by_contra hge
      push Not at hge
      exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hge)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hge) hprod
    have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
    exact hxi ρ ((xiBianchi_eq_zero_iff hρ0 hne1).2 hprod)
  · intro hz ρ hxi
    obtain ⟨h0, h1⟩ := zero_mem_openStrip_of_xiBianchi_eq_zero hxi
    have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl _ h1
    exact hz ρ ((xiBianchi_eq_zero_iff h0 hne1).1 hxi) h0

/-- Formulation for any third cyclotomic field `K` (`ℚ(ζ₃) = ℚ(√−3)`): late-time ringdown at rate
`O(e^{-(δ - ε)τ})` on `SL₂(ℤ[ω])\ℍ³` is equivalent to the zero-free strip `Re ρ ≤ 1 - 2δ` for the
Hecke `L`-function of the trivial character of `K` (the Dedekind zeta continuation `ζ_K(s)`). -/
theorem bianchi_hecke_zeroFreeStrip_iff_pulse_ringdown
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    (∀ ρ : ℂ, ρ ≠ 1 → HeckeLFunctions.heckeLFunction (HeckeLFunctions.trivialModulus K) 1 ρ = 0 →
      0 < ρ.re → ρ.re ≤ 1 - 2 * δ) ↔
      ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse, ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(δ - ε) * τ) := by
  rw [← bianchi_zeroFreeStrip_iff_pulse_ringdown hδ0 hδ]
  constructor
  · intro hK ρ hprod hρ0
    have hρ1 : ρ.re < 1 := by
      by_contra hge
      push Not at hge
      exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hge)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hge) hprod
    have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
    exact hK ρ hne1 (by rwa [heckeLFunction_thirdCyclotomic_trivial K hne1]) hρ0
  · intro hz ρ hne1 hK hρ0
    rw [heckeLFunction_thirdCyclotomic_trivial K hne1] at hK
    exact hz ρ hK hρ0

/-- Quarter-rate Bianchi pulse ringdown (`δ = 1/4`) is equivalent to GRH for `ζ_K(s) = ζ(s) L(s, χ₋₃)`
on `Re ρ > 0`, and in particular implies `RiemannHypothesis`. -/
theorem bianchi_quarter_ringdown_iff_dedekind_rh :
    (∀ ρ : ℂ, xiBianchi ρ = 0 → ρ.re = 1 / 2) ↔
      ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse, ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(1 / 4 - ε) * τ) := by
  rw [← bianchi_xi_zeroFreeStrip_iff_pulse_ringdown (by norm_num) le_rfl]
  constructor
  · intro hrh ρ hxi
    linarith [hrh ρ hxi]
  · intro hle ρ hxi
    have h1 : ρ.re ≤ 1 / 2 := by linarith [hle ρ hxi]
    have h2 : (1 - ρ).re ≤ 1 / 2 := by
      have := hle (1 - ρ) (by rw [xiBianchi_one_sub]; exact hxi)
      linarith
    simp at h2
    linarith

end GaloisForLFunctions.RingdownOfTheCubicCover

end
