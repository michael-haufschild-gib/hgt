import GaloisForLFunctions.RHTower.PhotonicHelicalInfiniteLadderCore
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Co-rotating principal symbol of the literal PTR cylinder

The exact material-locked Floquet/OAM grades become one angular Fourier series
in a co-rotating coordinate. The two-dimensional TE principal symbol is
elliptic at the cylinder interface for the real dielectric profile and drive
parameters displayed in the rotating-cylinder source paper. Its two-sided
principal transmission kernel is zero. These are symbol-level facts, not a
distributional Maxwell regularity or prime-conormal exclusion theorem.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

private theorem mcast_ne_zero {m : ℤ} (hm : m ≠ 0) : (m : ℝ) ≠ 0 := by
  exact_mod_cast hm

/-- The literal locked ladder is stationary in a co-rotating angular coordinate. -/
theorem ptr_locked_phase_corotating (ω Ω θ t : ℝ) (ℓ m n : ℤ) (hm : m ≠ 0) :
    (floquetSidebandAngularMomentum ℓ m n : ℝ) * θ -
        floquetSidebandFrequency ω Ω n * t =
      (floquetSidebandAngularMomentum ℓ m n : ℝ) *
          (θ - Ω / (m : ℝ) * t) -
        (ω - (ℓ : ℝ) * Ω / (m : ℝ)) * t := by
  simp only [GaloisForLFunctions.HTGeometry.floquetSidebandAngularMomentum,
    GaloisForLFunctions.HTGeometry.floquetSidebandFrequency]
  have hm' := mcast_ne_zero hm
  push_cast
  field_simp
  ring

/-- Positive scaling of the TE helical principal symbol at a cylinder wall. -/
def ptrScaledHelicalPrincipal (c ε Ω R : ℝ) (m : ℤ) (ξr ξφ : ℝ) : ℝ :=
  (c * (m : ℝ) * R * ξr) ^ 2 +
    (c ^ 2 * (m : ℝ) ^ 2 - ε * (Ω * R) ^ 2) * ξφ ^ 2

theorem ptrScaledHelicalPrincipal_pos_of_subluminal
    (c ε Ω R : ℝ) (m : ℤ) (ξr ξφ : ℝ)
    (hsub : ε * (Ω * R) ^ 2 < c ^ 2 * (m : ℝ) ^ 2)
    (hξ : ξφ ≠ 0) :
    0 < ptrScaledHelicalPrincipal c ε Ω R m ξr ξφ := by
  unfold ptrScaledHelicalPrincipal
  have h1 : 0 ≤ (c * (m : ℝ) * R * ξr) ^ 2 := sq_nonneg _
  have h2 : 0 < ξφ ^ 2 := sq_pos_of_ne_zero hξ
  have h3 : 0 < (c ^ 2 * (m : ℝ) ^ 2 - ε * (Ω * R) ^ 2) * ξφ ^ 2 :=
    mul_pos (sub_pos.mpr hsub) h2
  linarith

/-- Exact light-cylinder boundary for a real normal characteristic root. -/
theorem ptrScaledHelicalPrincipal_has_real_normal_root_iff
    (c ε Ω R : ℝ) (m : ℤ)
    (hcmR : c * (m : ℝ) * R ≠ 0) :
    (∃ ξr : ℝ, ptrScaledHelicalPrincipal c ε Ω R m ξr 1 = 0) ↔
      c ^ 2 * (m : ℝ) ^ 2 ≤ ε * (Ω * R) ^ 2 := by
  constructor
  · rintro ⟨ξr, hroot⟩
    by_contra h
    have hsub : ε * (Ω * R) ^ 2 < c ^ 2 * (m : ℝ) ^ 2 := lt_of_not_ge h
    have hp := ptrScaledHelicalPrincipal_pos_of_subluminal
      c ε Ω R m ξr 1 hsub (by norm_num)
    linarith
  · intro h
    let A : ℝ := ε * (Ω * R) ^ 2 - c ^ 2 * (m : ℝ) ^ 2
    have hA : 0 ≤ A := sub_nonneg.mpr h
    refine ⟨Real.sqrt A / (c * (m : ℝ) * R), ?_⟩
    have he : c * (m : ℝ) * R * (Real.sqrt A / (c * (m : ℝ) * R)) =
        Real.sqrt A := mul_div_cancel₀ _ hcmR
    simp only [ptrScaledHelicalPrincipal, he]
    rw [Real.sq_sqrt hA]
    dsimp [A]
    ring

/-- The all-grade centrifugal/temporal dispersion has the light-cylinder
coefficient as its quadratic term. -/
theorem ptr_scaled_dispersion_quadratic
    (c ε Ω R ω : ℝ) (ℓ m n : ℤ) :
    c ^ 2 * ((floquetSidebandAngularMomentum ℓ m n : ℝ)) ^ 2 -
      ε * R ^ 2 * (floquetSidebandFrequency ω Ω n) ^ 2 =
    (c ^ 2 * (m : ℝ) ^ 2 - ε * (Ω * R) ^ 2) * (n : ℝ) ^ 2 +
      2 * (c ^ 2 * (ℓ : ℝ) * (m : ℝ) - ε * R ^ 2 * ω * Ω) * (n : ℝ) +
      (c ^ 2 * (ℓ : ℝ) ^ 2 - ε * R ^ 2 * ω ^ 2) := by
  simp only [GaloisForLFunctions.HTGeometry.floquetSidebandAngularMomentum,
    GaloisForLFunctions.HTGeometry.floquetSidebandFrequency]
  push_cast
  ring

/-- Angular/Floquet charge sector extracted from an arbitrary two-index field.
No separable radial profile or global helical symmetry is imposed. -/
def ptrLocalHelicalSector {E : Type*} (m q : ℤ)
    (c : ℤ → ℤ → E) (n : ℤ) : E :=
  c n (q + m * n)

/-- General circular-collar coefficient equation. The angularly diagonal
operator `D` may contain arbitrary radial differential or interface dynamics;
the rotating material terms shift both indices together. -/
def ptrLocalHelicalEquation {E : Type*} [AddCommGroup E]
    (m : ℤ) (D : ℤ → ℤ → E → E)
    (M0 Mp Mm : ℤ → E → E) (c : ℤ → ℤ → E) : Prop :=
  ∀ n k : ℤ,
    D n k (c n k) =
      M0 n (c n k) + Mp n (c (n - 1) (k - m)) +
        Mm n (c (n + 1) (k + m))

/-- The full two-index circular-collar equation is exactly the product of
its helical-charge sectors. Other sectors and spatial profiles may be present;
they cannot feed a selected locked OAM diagonal in this local equation. -/
theorem ptrLocalHelicalEquation_iff_all_sectors
    {E : Type*} [AddCommGroup E]
    (m : ℤ) (D : ℤ → ℤ → E → E)
    (M0 Mp Mm : ℤ → E → E) (c : ℤ → ℤ → E) :
    ptrLocalHelicalEquation m D M0 Mp Mm c ↔
      ∀ q n : ℤ,
        D n (q + m * n) (ptrLocalHelicalSector m q c n) =
          M0 n (ptrLocalHelicalSector m q c n) +
            Mp n (ptrLocalHelicalSector m q c (n - 1)) +
            Mm n (ptrLocalHelicalSector m q c (n + 1)) := by
  constructor
  · intro h q n
    have hm : q + m * n - m = q + m * (n - 1) := by ring
    have hp : q + m * n + m = q + m * (n + 1) := by ring
    simpa only [ptrLocalHelicalSector, ← hm, ← hp] using h n (q + m * n)
  · intro h n k
    let q : ℤ := k - m * n
    have hk : q + m * n = k := by dsimp [q]; ring
    have hm : q + m * (n - 1) = k - m := by dsimp [q]; ring
    have hp : q + m * (n + 1) = k + m := by dsimp [q]; ring
    simpa only [ptrLocalHelicalSector, hk, hm, hp] using h q n

/-- With the source paper's largest displayed drive, the cylinder wall is
strictly inside the light surface even at maximal real permittivity. -/
theorem ptr_paper_cylinder_strictly_inside_light_surface :
    (15 : ℝ) * ((27 : ℝ) / 200 * Real.pi) ^ 2 <
      ((299792458 : ℝ) / 100000000) ^ 2 := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hv0 : 0 < (27 : ℝ) / 200 * Real.pi := by positivity
  have hv : (27 : ℝ) / 200 * Real.pi < 27 / 50 := by nlinarith
  have hc : (5 / 2 : ℝ) < (299792458 : ℝ) / 100000000 := by norm_num
  nlinarith [sq_nonneg ((27 : ℝ) / 200 * Real.pi),
    sq_nonneg ((299792458 : ℝ) / 100000000)]

/-- Exact nondimensionalization of `f=100 THz`, `R=270 nm`, and `m=4`. -/
theorem ptr_paper_drive_wall_speed :
    ((2 * Real.pi * (100 * 10 ^ 12 : ℝ)) *
        (270 / 10 ^ 9 : ℝ) / 4) / (10 ^ 8 : ℝ) =
      (27 : ℝ) / 200 * Real.pi := by
  norm_num
  ring

/-- Real part of the paper's angular dielectric profile. -/
noncomputable def ptrPaperDielectricReal (φ : ℝ) : ℝ :=
  (25 / 2) * (1 + (1 / 5) * Real.cos (4 * φ))

/-- The paper's formal complex material coefficient, including its displayed
constant imaginary loss. Its all-signed-frequency causal status is separate. -/
noncomputable def ptrPaperDielectricComplex (φ : ℝ) : ℂ :=
  (ptrPaperDielectricReal φ : ℂ) + Complex.I * (1 / 500 : ℂ)

theorem ptrPaperDielectricReal_le_fifteen (φ : ℝ) :
    ptrPaperDielectricReal φ ≤ 15 := by
  unfold ptrPaperDielectricReal
  nlinarith [Real.cos_le_one (4 * φ)]

/-- The decaying two-sided principal transmission system has zero kernel. -/
theorem ptr_elliptic_interface_principal_kernel_zero
    (αin αout : ℝ) (hin : 0 < αin) (hout : 0 < αout)
    (ain aout : ℂ) (hvalue : ain = aout)
    (hflux : ((Real.sqrt αin : ℝ) : ℂ) * ain +
      ((Real.sqrt αout : ℝ) : ℂ) * aout = 0) :
    ain = 0 ∧ aout = 0 := by
  have hs : 0 < Real.sqrt αin + Real.sqrt αout :=
    add_pos (Real.sqrt_pos.2 hin) (Real.sqrt_pos.2 hout)
  have hs0 : (((Real.sqrt αin + Real.sqrt αout : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hs
  rw [← hvalue] at hflux
  have hmul : (((Real.sqrt αin + Real.sqrt αout : ℝ) : ℂ)) * ain = 0 := by
    push_cast
    linear_combination hflux
  have ha := (mul_eq_zero.mp hmul).resolve_left hs0
  exact ⟨ha, hvalue.symm.trans ha⟩

/-- Uniform ellipticity for the actual angular profile at the interface. -/
theorem ptr_paper_dielectric_helical_principal_pos
    (φ ξr ξφ : ℝ) (hξ : ξφ ≠ 0) :
    0 < ((299792458 : ℝ) / 100000000 * ξr) ^ 2 +
      (((299792458 : ℝ) / 100000000) ^ 2 -
        ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2) * ξφ ^ 2 := by
  have hv2 : 0 ≤ ((27 : ℝ) / 200 * Real.pi) ^ 2 := sq_nonneg _
  have hsub : ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2 <
      ((299792458 : ℝ) / 100000000) ^ 2 := by
    have hmax := ptr_paper_cylinder_strictly_inside_light_surface
    have hε := ptrPaperDielectricReal_le_fifteen φ
    nlinarith [mul_nonneg (sub_nonneg.mpr hε) hv2]
  have hpos : 0 < ξφ ^ 2 := sq_pos_of_ne_zero hξ
  have hrad : 0 ≤ ((299792458 : ℝ) / 100000000 * ξr) ^ 2 := sq_nonneg _
  nlinarith [mul_pos (sub_pos.mpr hsub) hpos]

/-- The imaginary material term does not change the real part of the
source-faithful complex TE principal symbol. -/
theorem ptr_paper_complex_principal_re
    (φ ξr ξφ : ℝ) :
    (( (((299792458 : ℝ) / 100000000 * ξr : ℝ) : ℂ) ^ 2 +
      (((((299792458 : ℝ) / 100000000) ^ 2 : ℝ) : ℂ) -
        ptrPaperDielectricComplex φ *
          (((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ)) * (ξφ : ℂ) ^ 2)).re =
      ((299792458 : ℝ) / 100000000 * ξr) ^ 2 +
        (((299792458 : ℝ) / 100000000) ^ 2 -
          ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2) * ξφ ^ 2 := by
  have heq :
      ((((299792458 : ℝ) / 100000000 * ξr : ℝ) : ℂ) ^ 2 +
        (((((299792458 : ℝ) / 100000000) ^ 2 : ℝ) : ℂ) -
          ptrPaperDielectricComplex φ *
            (((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ)) * (ξφ : ℂ) ^ 2) =
        ((((299792458 : ℝ) / 100000000 * ξr) ^ 2 +
          (((299792458 : ℝ) / 100000000) ^ 2 -
            ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2) * ξφ ^ 2 : ℝ) : ℂ) -
          Complex.I * (((1 / 500 : ℝ) *
            ((27 : ℝ) / 200 * Real.pi) ^ 2 * ξφ ^ 2 : ℝ) : ℂ) := by
    unfold ptrPaperDielectricComplex
    push_cast
    ring
  have him :
      (Complex.I * (((1 / 500 : ℝ) *
        ((27 : ℝ) / 200 * Real.pi) ^ 2 * ξφ ^ 2 : ℝ) : ℂ)).re = 0 := by
    rw [Complex.I_mul_re, Complex.ofReal_im]
    ring
  exact (congrArg Complex.re heq).trans (by rw [Complex.sub_re, Complex.ofReal_re, him, sub_zero])

/-- The formal lossy source coefficient is strongly elliptic in every
nonzero tangential direction at the displayed cylinder wall. -/
theorem ptr_paper_complex_principal_ne_zero
    (φ ξr ξφ : ℝ) (hξ : ξφ ≠ 0) :
    ((((299792458 : ℝ) / 100000000 * ξr : ℝ) : ℂ) ^ 2 +
      (((((299792458 : ℝ) / 100000000) ^ 2 : ℝ) : ℂ) -
        ptrPaperDielectricComplex φ *
          (((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ)) * (ξφ : ℂ) ^ 2) ≠ 0 := by
  intro hzero
  have hre := ptr_paper_complex_principal_re φ ξr ξφ
  rw [hzero] at hre
  have hpos := ptr_paper_dielectric_helical_principal_pos φ ξr ξφ hξ
  simp at hre
  linarith

/-- Any two decaying complex normal roots have an invertible transmission
principal matrix. This applies equally to real and lossy dielectric roots. -/
theorem ptr_complex_interface_principal_kernel_zero
    (κin κout ain aout : ℂ)
    (hin : 0 < κin.re) (hout : 0 < κout.re)
    (hvalue : ain = aout) (hflux : κin * ain + κout * aout = 0) :
    ain = 0 ∧ aout = 0 := by
  have hsum : κin + κout ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.zero_re] at hre
    linarith
  rw [← hvalue] at hflux
  have hmul : (κin + κout) * ain = 0 := by
    linear_combination hflux
  have ha := (mul_eq_zero.mp hmul).resolve_left hsum
  exact ⟨ha, hvalue.symm.trans ha⟩

/-- A complex normal symbol with positive real part has a square root whose
real part is positive. -/
theorem ptr_exists_decaying_complex_normal_root (α : ℂ) (ha : 0 < α.re) :
    ∃ κ : ℂ, κ ^ 2 = α ∧ 0 < κ.re := by
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq α (n := 2) (by omega)
  have hre : α.re = κ.re ^ 2 - κ.im ^ 2 := by
    rw [← hκ, pow_two, Complex.mul_re]
    ring
  have hne : κ.re ≠ 0 := by
    intro hzero
    rw [hzero] at hre
    nlinarith [sq_nonneg κ.im]
  by_cases hpos : 0 < κ.re
  · exact ⟨κ, hκ, hpos⟩
  · have hneg : κ.re < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
    refine ⟨-κ, ?_, ?_⟩
    · simpa only [Even.neg_pow even_two] using hκ
    · simpa using (neg_pos.mpr hneg)

/-- Normal symbol of the paper's lossy dielectric at the cylinder wall. -/
noncomputable def ptrPaperInsideNormalSymbol (φ : ℝ) : ℂ :=
  ((((299792458 : ℝ) / 100000000) ^ 2 : ℝ) : ℂ) -
    ptrPaperDielectricComplex φ *
      (((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ)

/-- The source's complex loss does not destroy the strictly positive real
normal symbol on the displayed wall. -/
theorem ptrPaperInsideNormalSymbol_re_pos (φ : ℝ) :
    0 < (ptrPaperInsideNormalSymbol φ).re := by
  have hreal := ptr_paper_complex_principal_re φ 0 1
  have heq : (ptrPaperInsideNormalSymbol φ).re =
      ((299792458 : ℝ) / 100000000) ^ 2 -
        ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2 := by
    simpa [ptrPaperInsideNormalSymbol] using hreal
  have hv2 : 0 ≤ ((27 : ℝ) / 200 * Real.pi) ^ 2 := sq_nonneg _
  have hmax := ptr_paper_cylinder_strictly_inside_light_surface
  have hε := ptrPaperDielectricReal_le_fifteen φ
  rw [heq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hε) hv2]

/-- The literal complex dielectric and exterior air admit decaying roots,
and their principal source-free transmission system is complementing. -/
theorem ptr_paper_complex_principal_transmission_complementing (φ : ℝ) :
    ∃ κin κout : ℂ,
      κin ^ 2 = ptrPaperInsideNormalSymbol φ ∧
      κout ^ 2 =
        (((299792458 : ℝ) / 100000000) ^ 2 -
          ((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ) ∧
      0 < κin.re ∧ 0 < κout.re ∧
      ∀ ain aout : ℂ,
        ain = aout → κin * ain + κout * aout = 0 →
          ain = 0 ∧ aout = 0 := by
  obtain ⟨κin, hkin, hkinpos⟩ :=
    ptr_exists_decaying_complex_normal_root
      (ptrPaperInsideNormalSymbol φ) (ptrPaperInsideNormalSymbol_re_pos φ)
  have hout : 0 < ((299792458 : ℝ) / 100000000) ^ 2 -
      ((27 : ℝ) / 200 * Real.pi) ^ 2 := by
    have hmax := ptr_paper_cylinder_strictly_inside_light_surface
    nlinarith
  obtain ⟨κout, hkout, hkoutpos⟩ :=
    ptr_exists_decaying_complex_normal_root
      (((((299792458 : ℝ) / 100000000) ^ 2 -
        ((27 : ℝ) / 200 * Real.pi) ^ 2 : ℝ) : ℂ)) (by exact_mod_cast hout)
  exact ⟨κin, κout, hkin, hkout, hkinpos, hkoutpos,
    fun ain aout hvalue hflux =>
      ptr_complex_interface_principal_kernel_zero κin κout ain aout
        hkinpos hkoutpos hvalue hflux⟩

/-- Actual inside profile and exterior air have no common decaying
source-free principal boundary amplitude in a fixed locked sector. -/
theorem ptr_paper_dielectric_principal_transmission_kernel_zero
    (φ : ℝ) (ain aout : ℂ) (hvalue : ain = aout)
    (hflux : ((Real.sqrt
        (((299792458 : ℝ) / 100000000) ^ 2 -
          ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2) : ℝ) : ℂ) * ain +
      ((Real.sqrt
        (((299792458 : ℝ) / 100000000) ^ 2 -
          ((27 : ℝ) / 200 * Real.pi) ^ 2) : ℝ) : ℂ) * aout = 0) :
    ain = 0 ∧ aout = 0 := by
  have hv2 : 0 ≤ ((27 : ℝ) / 200 * Real.pi) ^ 2 := sq_nonneg _
  have hin : 0 < ((299792458 : ℝ) / 100000000) ^ 2 -
      ptrPaperDielectricReal φ * ((27 : ℝ) / 200 * Real.pi) ^ 2 := by
    have hmax := ptr_paper_cylinder_strictly_inside_light_surface
    have hε := ptrPaperDielectricReal_le_fifteen φ
    nlinarith [mul_nonneg (sub_nonneg.mpr hε) hv2]
  have hout : 0 < ((299792458 : ℝ) / 100000000) ^ 2 -
      ((27 : ℝ) / 200 * Real.pi) ^ 2 := by
    have hmax := ptr_paper_cylinder_strictly_inside_light_surface
    nlinarith
  exact ptr_elliptic_interface_principal_kernel_zero _ _ hin hout
    ain aout hvalue hflux

end RHTower
