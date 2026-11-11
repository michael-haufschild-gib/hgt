import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheRationalsContainsZeta
import GaloisForLFunctions.FamilyContinuationTheory.TheEisensteinLatticeSumIsZetaTimesAnLFunction

/-!
# The Hecke family of the third cyclotomic field contains `ζ`

Let `K = ℚ(ζ₃)`. Its ring of integers has the basis `1, η` with `η² + η + 1 = 0`; the norm of
`a + bη` is `a² − ab + b²` (`algebraNorm_eq_eisNorm`), every ideal is principal and there are six
units (`card_units_thirdCyclotomic`). So the number of ideals of norm `n ≥ 1` is
`Σ_{d ∣ n} χ₋₃(d)` (`card_ideals_thirdCyclotomic`) and

`ζ_K(s) = ζ(s) L(s, χ₋₃)`  for `Re s > 1`  (`dedekindZeta_thirdCyclotomic`).

Both sides continue off `1` and `L(s, χ₋₃)` is entire, so a zero of `ζ` is a zero of the Hecke
`L`-function of the trivial character of the unit modulus of `K`
(`heckeLFunction_thirdCyclotomic_trivial`). A zero-free half-plane for the Hecke family of `K` is
therefore a half-plane for `ζ` and for `L(s, χ₋₃)`
(`xiZeroHalfPlaneBound_of_heckeHalfPlane_thirdCyclotomic`), and it bounds the zero abscissa of `ζ`
(`zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic`).
-/

noncomputable section

open Complex NumberField IsDedekindDomain LSeries
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions _root_.RHTower EisensteinNorm

local notation "𝔼" => RHTower.BourgainEisensteinInt
local notation "N" => RHTower.BourgainEisensteinInt.norm

/-- Two functions holomorphic off `1` that agree on `Re s > 1` agree off `1`. -/
theorem eq_of_eqOn_one_lt_re {f g : ℂ → ℂ} (hf : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ f s)
    (hg : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ g s) (h : ∀ s : ℂ, 1 < s.re → f s = g s)
    {s : ℂ} (hs : s ≠ 1) : f s = g s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hfa : AnalyticOnNhd ℂ f ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hf z hz).differentiableWithinAt) hU
  have hga : AnalyticOnNhd ℂ g ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd (fun z hz => (hg z hz).differentiableWithinAt) hU
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hev : f =ᶠ[nhds (2 : ℂ)] g := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact h z hz
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hconn h2 hev hs

/-- The quadratic character of conductor `3` is not trivial. -/
theorem chi3D_ne_one : chi3D ≠ 1 := by
  intro h
  have h2 := chi3D_apply 2
  have hu : IsUnit ((2 : ℕ) : ZMod 3) := (ZMod.isUnit_iff_coprime 2 3).mpr (by decide)
  have h3 : chi3 2 = -1 := by decide
  rw [h, MulChar.one_apply hu, h3] at h2
  norm_num at h2

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-! ### The basis `1, η` and the norm form -/

/-- The cube root of unity `η` in the ring of integers. -/
def eisEta : 𝓞 K := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

theorem eisPowerBasis_dim :
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.dim = 2 := by
  rw [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime Nat.prime_three]

/-- The integral basis `1, η` of the ring of integers. -/
def eisBasis : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.basis.reindex
    (finCongr (eisPowerBasis_dim K))

theorem eisBasis_zero : eisBasis K 0 = 1 := by
  simp [eisBasis, PowerBasis.coe_basis]

theorem eisBasis_one : eisBasis K 1 = eisEta K := by
  simp [eisBasis, PowerBasis.coe_basis, IsPrimitiveRoot.integralPowerBasis_gen, eisEta]

/-- `η² = −η − 1`. -/
theorem eisEta_sq : eisEta K ^ 2 = -eisEta K - 1 := by
  have hprim := (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot
  have h3 : eisEta K ^ 3 = 1 := hprim.pow_eq_one
  have h1 : eisEta K ≠ 1 := hprim.ne_one (by norm_num)
  have hmul : (eisEta K - 1) * (eisEta K ^ 2 + eisEta K + 1) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · linear_combination h

theorem eisBasis_repr_combo (a b : ℤ) :
    (eisBasis K).repr (a • (1 : 𝓞 K) + b • eisEta K) =
      Finsupp.single 0 a + Finsupp.single 1 b := by
  rw [← eisBasis_zero K, ← eisBasis_one K, map_add, map_smul, map_smul,
    Module.Basis.repr_self, Module.Basis.repr_self]
  simp

theorem eisBasis_repr_combo_zero (a b : ℤ) :
    (eisBasis K).repr (a • (1 : 𝓞 K) + b • eisEta K) 0 = a := by
  rw [eisBasis_repr_combo]
  simp

theorem eisBasis_repr_combo_one (a b : ℤ) :
    (eisBasis K).repr (a • (1 : 𝓞 K) + b • eisEta K) 1 = b := by
  rw [eisBasis_repr_combo]
  simp

/-- The coordinates of an integer of `K` in the basis `1, η`, as an Eisenstein integer. -/
def eisCoord : 𝓞 K ≃ 𝔼 where
  toFun x := ⟨(eisBasis K).repr x 0, (eisBasis K).repr x 1⟩
  invFun z := z.re • (1 : 𝓞 K) + z.im • eisEta K
  left_inv x := by
    have h := (eisBasis K).sum_repr x
    rw [Fin.sum_univ_two, eisBasis_zero, eisBasis_one] at h
    exact h
  right_inv z := BourgainEisensteinInt.ext (eisBasis_repr_combo_zero K z.re z.im)
    (eisBasis_repr_combo_one K z.re z.im)

/-- `N(a + bη) = a² − ab + b²`: the determinant of multiplication by `a + bη` in the basis
`1, η`, whose columns are `(a, b)` and `(−b, a − b)`. -/
theorem algebraNorm_combo (a b : ℤ) :
    Algebra.norm ℤ (a • (1 : 𝓞 K) + b • eisEta K) = a ^ 2 - a * b + b ^ 2 := by
  have h1 : (a • (1 : 𝓞 K) + b • eisEta K) * eisEta K =
      (-b) • (1 : 𝓞 K) + (a - b) • eisEta K := by
    have hsq := eisEta_sq K
    simp only [zsmul_eq_mul, mul_one, Int.cast_neg, Int.cast_sub]
    linear_combination (b : 𝓞 K) * hsq
  rw [Algebra.norm_eq_matrix_det (eisBasis K), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  rw [eisBasis_zero, eisBasis_one, mul_one, h1]
  simp only [eisBasis_repr_combo_zero, eisBasis_repr_combo_one]
  ring

/-- **The norm of an integer of `K` is the norm form of its coordinates.** -/
theorem algebraNorm_eq_eisNorm (x : 𝓞 K) : Algebra.norm ℤ x = N (eisCoord K x) := by
  have hx : (eisCoord K x).re • (1 : 𝓞 K) + (eisCoord K x).im • eisEta K = x :=
    (eisCoord K).symm_apply_apply x
  conv_lhs => rw [← hx]
  rw [algebraNorm_combo, BourgainEisensteinInt.norm_def]

theorem algebraNorm_nonneg_thirdCyclotomic (x : 𝓞 K) : 0 ≤ Algebra.norm ℤ x := by
  rw [algebraNorm_eq_eisNorm]
  exact BourgainEisensteinInt.norm_nonneg _

/-- The integers of `K` of norm `n` are the Eisenstein integers of norm `n`. -/
theorem card_algebraNorm_eq (n : ℕ) :
    Nat.card {x : 𝓞 K // Algebra.norm ℤ x = n} = (normSet n).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((eisCoord K).subtypeEquiv fun x => by
    rw [mem_normSet, algebraNorm_eq_eisNorm])

/-! ### Ideals and units -/

theorem algebraNorm_eq_of_absNorm_span {x : 𝓞 K} {n : ℕ}
    (h : Ideal.absNorm (Ideal.span ({x} : Set (𝓞 K))) = n) : Algebra.norm ℤ x = n := by
  rw [Ideal.absNorm_span_singleton] at h
  rw [← h]
  exact (Int.natAbs_of_nonneg (algebraNorm_nonneg_thirdCyclotomic K x)).symm

/-- **Ideals and units.** For `n ≥ 1`, an ideal of norm `n` and a unit give an element of norm
`n`, a generator times the unit, and every element of norm `n` arises exactly once. -/
theorem card_ideals_mul_card_units {n : ℕ} (hn : 0 < n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} * Nat.card (𝓞 K)ˣ =
      Nat.card {x : 𝓞 K // Algebra.norm ℤ x = n} := by
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  have hspan : ∀ (I : Ideal (𝓞 K)) (u : (𝓞 K)ˣ),
      Ideal.span ({Submodule.IsPrincipal.generator I * (u : 𝓞 K)} : Set (𝓞 K)) = I :=
    fun I u => by
      rw [Ideal.span_singleton_mul_right_unit u.isUnit, Ideal.span_singleton_generator]
  obtain ⟨f, hf⟩ : ∃ f : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} × (𝓞 K)ˣ →
      {x : 𝓞 K // Algebra.norm ℤ x = n},
      ∀ p, (f p).1 = Submodule.IsPrincipal.generator p.1.1 * (p.2 : 𝓞 K) :=
    ⟨fun p => ⟨Submodule.IsPrincipal.generator p.1.1 * (p.2 : 𝓞 K),
      algebraNorm_eq_of_absNorm_span K (by rw [hspan]; exact p.1.2)⟩, fun _ => rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨I, hI⟩, u⟩ ⟨⟨J, hJ⟩, v⟩ h
    have h1 := hf (⟨I, hI⟩, u)
    have h2 := hf (⟨J, hJ⟩, v)
    rw [h] at h1
    have hval : Submodule.IsPrincipal.generator I * (u : 𝓞 K) =
        Submodule.IsPrincipal.generator J * (v : 𝓞 K) := h1.symm.trans h2
    have hIJ : I = J := by
      calc I = Ideal.span ({Submodule.IsPrincipal.generator I * (u : 𝓞 K)} : Set (𝓞 K)) :=
            (hspan I u).symm
        _ = Ideal.span ({Submodule.IsPrincipal.generator J * (v : 𝓞 K)} : Set (𝓞 K)) := by
            rw [hval]
        _ = J := hspan J v
    subst hIJ
    have hg : Submodule.IsPrincipal.generator I ≠ 0 := by
      intro h0
      have hbot : I = ⊥ := by
        rw [← Ideal.span_singleton_generator I, h0]
        simp
      rw [hbot, Ideal.absNorm_bot] at hI
      omega
    have huv : u = v := Units.ext (mul_left_cancel₀ hg hval)
    rw [huv]
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    have hIx : Ideal.absNorm (Ideal.span ({x} : Set (𝓞 K))) = n := by
      rw [Ideal.absNorm_span_singleton, hx, Int.natAbs_natCast]
    obtain ⟨u, hu⟩ : Associated
        (Submodule.IsPrincipal.generator (Ideal.span ({x} : Set (𝓞 K)))) x :=
      Ideal.span_singleton_eq_span_singleton.mp (Ideal.span_singleton_generator _)
    exact ⟨(⟨Ideal.span {x}, hIx⟩, u), Subtype.ext ((hf _).trans hu)⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

/-- **The third cyclotomic field has six units.** -/
theorem card_units_thirdCyclotomic : Nat.card (𝓞 K)ˣ = 6 := by
  have h := card_ideals_mul_card_units K (n := 1) one_pos
  have h1 : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun I J => Subtype.ext ((Ideal.absNorm_eq_one_iff.mp I.2).trans
      (Ideal.absNorm_eq_one_iff.mp J.2).symm)⟩, ⟨⟨⊤, Ideal.absNorm_top⟩⟩⟩
  rw [h1, one_mul, card_algebraNorm_eq, card_normSet_one] at h
  exact h

/-- **The number of ideals of norm `n ≥ 1`** is `Σ_{d ∣ n} χ₋₃(d)`. -/
theorem card_ideals_thirdCyclotomic {n : ℕ} (hn : 0 < n) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℤ) = divisorChar n := by
  have h := card_ideals_mul_card_units K hn
  rw [card_units_thirdCyclotomic, card_algebraNorm_eq] at h
  have h2 := card_normSet hn
  have h3 : (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℤ) * 6 =
      6 * divisorChar n := by
    rw [← h2]
    exact_mod_cast h
  linarith

/-! ### The zeta function -/

/-- **The zeta function of the third cyclotomic field**: `ζ_K(s) = ζ(s) L(s, χ₋₃)` on
`Re s > 1`. -/
theorem dedekindZeta_thirdCyclotomic {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction chi3D s := by
  have hconv : ∀ {n : ℕ}, n ≠ 0 →
      ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℕ) : ℂ) =
        (convolution 1 (fun n : ℕ => chi3D n)) n := by
    intro n hn
    have h := card_ideals_thirdCyclotomic K (Nat.pos_of_ne_zero hn)
    have h' : ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℕ) : ℂ) =
        ((divisorChar n : ℤ) : ℂ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h
    rw [h', LSeries.convolution_def]
    have hd := Nat.sum_divisorsAntidiagonal' (fun a b => (1 : ℕ → ℂ) a * chi3D b) (n := n)
    show _ = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chi3D p.2
    rw [hd, divisorChar]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Pi.one_apply, one_mul, chi3D_apply]
  unfold dedekindZeta
  rw [LSeries_congr hconv, LSeries_convolution' (LSeriesSummable_one_iff.mpr hs)
    (chi3D.LSeriesSummable_of_one_lt_re hs), LSeries_one_eq_riemannZeta hs,
    DirichletCharacter.LFunction_eq_LSeries chi3D hs]

/-- **Off `1` the Hecke `L`-function of the trivial character of the unit modulus of `K` is
`ζ(s) L(s, χ₋₃)`.** -/
theorem heckeLFunction_thirdCyclotomic_trivial {s : ℂ} (hs : s ≠ 1) :
    heckeLFunction (trivialModulus K) 1 s =
      riemannZeta s * DirichletCharacter.LFunction chi3D s :=
  eq_of_eqOn_one_lt_re (f := heckeLFunction (trivialModulus K) 1)
    (g := fun s => riemannZeta s * DirichletCharacter.LFunction chi3D s)
    (fun _ hz => differentiableAt_heckeLFunction (trivialModulus K) 1 hz)
    (fun z hz => (differentiableAt_riemannZeta hz).mul
      (DirichletCharacter.differentiable_LFunction chi3D_ne_one z))
    (fun z hz => by
      rw [heckeLFunction_eq_heckeL (trivialModulus K) 1 hz, heckeL_trivialModulus_one,
        dedekindZeta_thirdCyclotomic K hz]) hs

/-! ### The transfer to `ζ` -/

variable {K}

/-- A Hecke half-plane over `K` is a half-plane for `ζ`. -/
theorem riemannZeta_ne_zero_of_heckeHalfPlane_thirdCyclotomic {σ₀ : ℝ}
    (h : HeckeHalfPlane K σ₀) {ρ : ℂ} (hρ : σ₀ < ρ.re) (hρ1 : ρ ≠ 1) : riemannZeta ρ ≠ 0 := by
  intro h0
  apply h (trivialModulus K) 1 ρ hρ hρ1
  rw [heckeLFunction_thirdCyclotomic_trivial K hρ1, h0, zero_mul]

/-- A Hecke half-plane over `K` is a half-plane for `L(s, χ₋₃)`. -/
theorem LFunction_chi3D_ne_zero_of_heckeHalfPlane_thirdCyclotomic {σ₀ : ℝ}
    (h : HeckeHalfPlane K σ₀) {ρ : ℂ} (hρ : σ₀ < ρ.re) (hρ1 : ρ ≠ 1) :
    DirichletCharacter.LFunction chi3D ρ ≠ 0 := by
  intro h0
  apply h (trivialModulus K) 1 ρ hρ hρ1
  rw [heckeLFunction_thirdCyclotomic_trivial K hρ1, h0, mul_zero]

/-- **A Hecke half-plane over the third cyclotomic field bounds the zero abscissa of `ζ`.** -/
theorem zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic {σ₀ : ℝ}
    (h : HeckeHalfPlane K σ₀) : zetaZeroAbscissa ≤ σ₀ :=
  zetaZeroAbscissa_le_of_zeroFree fun _ hρ hρ1 =>
    riemannZeta_ne_zero_of_heckeHalfPlane_thirdCyclotomic h hρ hρ1

/-- **A Hecke half-plane over the third cyclotomic field bounds the zeros of `ξ`.** -/
theorem xiZeroHalfPlaneBound_of_heckeHalfPlane_thirdCyclotomic {σ₀ : ℝ}
    (hσ₀ : (1 : ℝ) / 2 ≤ σ₀) (h : HeckeHalfPlane K σ₀) : XiZeroHalfPlaneBound (σ₀ - 1 / 2) := by
  refine (suzukiZetaZeroFreeRightOf_iff_xiZeroHalfPlaneBound (by linarith)).mp ?_
  intro s hs hs1
  exact riemannZeta_ne_zero_of_heckeHalfPlane_thirdCyclotomic h (by linarith) hs1

/-- **The half-plane `Re s > ½` for the Hecke family of the third cyclotomic field gives the
Riemann hypothesis.** -/
theorem riemannHypothesis_of_heckeHalfPlane_thirdCyclotomic (h : HeckeHalfPlane K (1 / 2)) :
    RiemannHypothesis := by
  have hb := xiZeroHalfPlaneBound_of_heckeHalfPlane_thirdCyclotomic le_rfl h
  rw [sub_self] at hb
  exact riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr hb

/-- **The family step over the third cyclotomic field bounds the zeros of `ξ`.** If, whenever
all pole-cleared Hecke `L`-functions of `K` are zero-free in `Re s > β`, each ray class character
has a sum with a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with its signal, `a₁, a₂ < β`
the same for all characters, then the zeros of `ξ` lie in `Re ρ ≤ σ₀`. -/
theorem xiZeroHalfPlaneBound_of_family_common_signal_thirdCyclotomic {σ₀ : ℝ}
    (hσ₀ : (1 : ℝ) / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        heckePoleCleared η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (heckePoleClearedKernel η.1 η.2 c) 2 Z‖ ≤ C * Z ^ a₂)) :
    XiZeroHalfPlaneBound (σ₀ - 1 / 2) :=
  xiZeroHalfPlaneBound_of_heckeHalfPlane_thirdCyclotomic hσ₀
    (heckeHalfPlane_of_family_common_signal K hσ₀1 c hstep)

end GaloisForLFunctions.FamilyContinuationTheory
