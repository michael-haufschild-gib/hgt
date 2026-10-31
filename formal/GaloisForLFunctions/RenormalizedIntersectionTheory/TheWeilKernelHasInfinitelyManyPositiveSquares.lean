import GaloisForLFunctions.RenormalizedIntersectionTheory.TheHadamardPowersOfWeilsKernel
import GaloisForLFunctions.RHTower.XiCriticalZeroLinearNodes
import GaloisForLFunctions.RHTower.LaguerreInequality
import GaloisForLFunctions.RHTower.WeilDeletionTestKit
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexOfABohrSeries
import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw

/-!
# Weil's kernel has infinitely many positive squares

The critical zeros enter Weil's kernel `K_ζ` as unitary characters `u ↦ u^{−iγ}` with weights
`m_ρ |B̂(γ)|² ≥ 0`, `B̂(x) = (sin x/x)⁴` the transform of the cubic spline. So the on-line part is a
Bohr series with nonnegative coefficients, and its positive index is the number of critical zeros
the spline sees (`HeckeKreinToeplitz.negIndex_bohrSum`).

* **The spline sees infinitely many critical zeros** (`criticalSeen_infinite`). `B̂` vanishes on the
  real line only at `πℤ ∖ {0}`; a dyadic window `(T, 2T]` holds at most `T/π + 1` such points but at
  least `c₀ T log T` distinct critical ordinates (`RHTower.exists_many_critical_ordinates_dyadic`).
* **The critical zeros carry infinitely many positive squares**
  (`posIndex_orbitKernel_onLine_eq_top`): `κ₊(K_on) = ∞`, unconditionally.
* **On the finite stratum `K_ζ` has infinitely many positive squares**
  (`posIndex_zetaKernel_eq_top_of_finite`): the off-line pairs are a finite-rank perturbation.
* **The Künneth square is all-or-nothing** (`riemannHypothesis_or_negIndex_kunnethZeta_eq_top`):
  either RH holds and `K_ζ ⊠ K_ζ` is positive definite, or it has infinitely many negative squares.
  On the finite stratum a single off-line zero is multiplied by the infinitely many positive squares
  of the critical zeros; on the infinite stratum the Künneth square dominates `κ(K_ζ) = ∞`.
-/

open Complex Filter Finset
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx rightZeros summable_re_Wsummand)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)
open RHTower.WeilDeletion (upow)
open scoped Real
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-! ### The real zeros of the spline transform -/

/-- `B̂(x) = (sin x/x)⁴` vanishes on the real line only at `πℤ ∖ {0}`. -/
theorem paperFT_cubicSpline_ne_zero_of_real {x : ℝ} (hx0 : x ≠ 0) (hx : ∀ n : ℤ, x ≠ n * π) :
    paperFT (cx cubicSpline) (x : ℂ) ≠ 0 := by
  have hcx : cx cubicSpline = fun u => (upow 1 3 u : ℂ) := rfl
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  rw [hcx, RHTower.WeilDeletion.paperFT_upow, RHTower.WeilDeletion.paperFT_unif one_pos hx0']
  refine pow_ne_zero _ (div_ne_zero ?_ (by simp [hx0', I_ne_zero]))
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (sub_eq_zero.mp h)
  have him := congrArg Complex.im hn
  simp only [mul_one, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add,
    neg_im, add_im, mul_re, intCast_re, intCast_im, sub_zero, mul_zero, re_ofNat,
    im_ofNat] at him
  exact hx n (by linarith)

/-! ### Infinitely many critical zeros are seen -/

/-- The critical zeros seen by the cubic spline. -/
def criticalSeen : Set ℂ :=
  {ρ | ρ ∈ zetaZeroConfig.carrier ∧ ρ.re = 1 / 2 ∧ paperFT (cx cubicSpline) (ρ.im : ℂ) ≠ 0}

/-- An integer interval has at most `b + 1 − a` points. -/
theorem card_Icc_int_le (a b : ℤ) : ((Icc a b).card : ℝ) ≤ max 0 ((b : ℝ) + 1 - a) := by
  rw [Int.card_Icc]
  rcases le_or_gt 0 (b + 1 - a) with h | h
  · have : ((b + 1 - a).toNat : ℤ) = b + 1 - a := Int.toNat_of_nonneg h
    have hc : (((b + 1 - a).toNat : ℕ) : ℝ) = ((b + 1 - a : ℤ) : ℝ) := by exact_mod_cast this
    rw [hc]; push_cast; exact le_max_right _ _
  · rw [Int.toNat_of_nonpos h.le]; simp

open Classical in
/-- A window `(T, 2T]` contains at most `T/π + 1` multiples of `π`. -/
theorem card_filter_lattice_le {T : ℝ} (hT0 : 0 ≤ T) (τS : Finset ℝ)
    (hτS : ∀ τ ∈ τS, T < τ ∧ τ ≤ 2 * T) :
    ((τS.filter fun τ => ∃ n : ℤ, τ = n * π).card : ℝ) ≤ T / π + 1 := by
  classical
  set a := ⌈T / π⌉
  set b := ⌊2 * T / π⌋
  have hmaps : ∀ τ ∈ τS.filter (fun τ => ∃ n : ℤ, τ = n * π), ⌊τ / π⌋ ∈ Icc a b := by
    intro τ hτ
    obtain ⟨hτ, n, rfl⟩ := mem_filter.mp hτ
    obtain ⟨h1, h2⟩ := hτS _ hτ
    rw [mul_div_cancel_right₀ _ Real.pi_ne_zero, Int.floor_intCast, mem_Icc]
    constructor
    · exact Int.ceil_le.mpr ((div_le_iff₀ Real.pi_pos).mpr h1.le)
    · exact Int.le_floor.mpr ((le_div_iff₀ Real.pi_pos).mpr h2)
  have hinj : Set.InjOn (fun τ => ⌊τ / π⌋) (τS.filter fun τ => ∃ n : ℤ, τ = n * π) := by
    intro τ hτ τ' hτ' h
    obtain ⟨-, n, rfl⟩ := mem_filter.mp hτ
    obtain ⟨-, n', rfl⟩ := mem_filter.mp hτ'
    simp only [mul_div_cancel_right₀ _ Real.pi_ne_zero, Int.floor_intCast] at h
    rw [h]
  have hcard := card_le_card_of_injOn _ hmaps hinj
  have h1 := card_Icc_int_le a b
  have ha : T / π ≤ (a : ℝ) := Int.le_ceil _
  have hb : (b : ℝ) ≤ 2 * T / π := Int.floor_le _
  have hT : (2 * T / π) = 2 * (T / π) := by ring
  calc ((τS.filter fun τ => ∃ n : ℤ, τ = n * π).card : ℝ) ≤ (Icc a b).card := by
        exact_mod_cast hcard
    _ ≤ max 0 ((b : ℝ) + 1 - a) := h1
    _ ≤ T / π + 1 := max_le (by positivity) (by linarith)

open Classical in
/-- **The cubic spline sees infinitely many critical zeros.** -/
theorem criticalSeen_infinite : criticalSeen.Infinite := by
  classical
  intro hfin
  obtain ⟨c₀, hc₀, T₀, hT₀, hmany⟩ := RHTower.exists_many_critical_ordinates_dyadic
  set M : ℕ := hfin.toFinset.card
  -- a window large enough for the count to beat the lattice and the seen zeros
  set T : ℝ := max T₀ (max ((M : ℝ) + 2) (Real.exp ((1 / π + 1) / c₀ + 1)))
  have hTT₀ : T₀ ≤ T := le_max_left _ _
  have hTM : (M : ℝ) + 2 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTe : Real.exp ((1 / π + 1) / c₀ + 1) ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hT0 : 0 < T := by linarith [Real.exp_pos ((1 / π + 1) / c₀ + 1)]
  have hlog : (1 / π + 1) / c₀ + 1 ≤ Real.log T := by
    rw [← Real.log_exp ((1 / π + 1) / c₀ + 1)]
    exact Real.log_le_log (Real.exp_pos _) hTe
  have hclog : 1 / π + 1 < c₀ * Real.log T := by
    have : (1 / π + 1) / c₀ < Real.log T := by linarith
    rwa [div_lt_iff₀ hc₀, mul_comm] at this
  have hbig : T / π + 1 + M < c₀ * (T * Real.log T) := by
    have h1 : T * (1 / π + 1) < T * (c₀ * Real.log T) := mul_lt_mul_of_pos_left hclog hT0
    have h2 : T / π = T * (1 / π) := by ring
    nlinarith
  obtain ⟨τS, hτS, hcard⟩ := hmany T hTT₀
  have hL := card_filter_lattice_le hT0.le τS fun τ hτ => ⟨(hτS τ hτ).1, (hτS τ hτ).2.1⟩
  -- the ordinates off the lattice give distinct seen zeros
  have hR : (τS.filter fun τ => ¬ ∃ n : ℤ, τ = n * π).card ≤ M := by
    refine card_le_card_of_injOn (fun τ : ℝ => (1 / 2 : ℂ) + (τ : ℂ) * I) (fun τ hτ => ?_)
      (fun τ _ τ' _ h => by simpa using congrArg Complex.im h)
    obtain ⟨hτ, hlat⟩ := mem_filter.mp hτ
    obtain ⟨hT1, -, hXi⟩ := hτS τ hτ
    have hτ0 : τ ≠ 0 := by linarith
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    refine ⟨?_, by simp, ?_⟩
    · rw [RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip]
      refine ⟨?_, by norm_num, by norm_num⟩
      rw [RHTower.xiHalfLine_real, hXi, ofReal_zero]
    · have him : ((1 / 2 : ℂ) + (τ : ℂ) * I).im = τ := by simp
      rw [him]
      exact paperFT_cubicSpline_ne_zero_of_real hτ0 fun n hn => hlat ⟨n, hn⟩
  have hsplit := filter_card_add_filter_neg_card_eq_card (s := τS)
    (p := fun τ => ∃ n : ℤ, τ = n * π)
  have hRr : ((τS.filter fun τ => ¬ ∃ n : ℤ, τ = n * π).card : ℝ) ≤ M := by exact_mod_cast hR
  have hsum : (τS.card : ℝ) = (τS.filter fun τ => ∃ n : ℤ, τ = n * π).card +
      (τS.filter fun τ => ¬ ∃ n : ℤ, τ = n * π).card := by exact_mod_cast hsplit.symm
  linarith

/-! ### The on-line part is a Bohr series with nonnegative weights -/

/-- The configuration of the critical zeros of `ζ`. -/
abbrev zetaOnLine : ZeroConfig := onLineConfig zetaZeroConfig

theorem onLine_eq {ρ : ℂ} (hρ : ρ ∈ zetaOnLine.carrier) : ρ = 1 / 2 + (ρ.im : ℂ) * I :=
  Complex.ext (by simp [hρ.2]) (by simp)

/-- On the critical line the zero summand is `m_ρ |B̂(γ)|²`. -/
theorem Wsummand_onLine {ρ : ℂ} (hρ : ρ ∈ zetaOnLine.carrier) :
    zetaOnLine.Wsummand (cx cubicSpline) (cx cubicSpline) ρ =
      (((zetaOnLine.mult ρ : ℝ) * ‖paperFT (cx cubicSpline) (ρ.im : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have hγ : gammaOf ρ = (ρ.im : ℂ) := by
    rw [onLine_eq hρ, gammaOf]
    apply Complex.ext <;> simp
  simp only [ZeroConfig.Wsummand, hγ, conj_ofReal, mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem cx_cubicSpline_contDiff : ContDiff ℝ 2 (cx cubicSpline) :=
  Complex.ofRealCLM.contDiff.comp contDiff_cubicSpline

theorem cx_cubicSpline_hasCompactSupport : HasCompactSupport (cx cubicSpline) :=
  hasCompactSupport_cubicSpline.comp_left Complex.ofReal_zero

theorem criticalSeen_subset : criticalSeen ⊆ zetaOnLine.carrier := fun _ h => ⟨h.1, h.2.1⟩

/-- An enumeration of the critical zeros. -/
theorem exists_enum_onLine : Nonempty (ℕ ≃ zetaOnLine.carrier) := by
  haveI : Countable zetaOnLine.carrier :=
    ((SquareRootThreshold.countable_carrier zetaZeroConfig).mono fun _ h => h.1).to_subtype
  haveI : Infinite zetaOnLine.carrier :=
    (criticalSeen_infinite.mono criticalSeen_subset).to_subtype
  exact nonempty_equiv_of_countable

section Bohr

variable (e : ℕ ≃ zetaOnLine.carrier)

/-- The character of the `j`-th critical zero, `u ↦ u^{−iγ_j}`. -/
def onLineChar (j : ℕ) : HeckeLattice →* ℂ :=
  logChar heckeLogScale (((-((e j : ℂ).im) : ℝ) : ℂ) * I)

/-- The weight of the `j`-th critical zero, `m_ρ |B̂(γ_j)|²`. -/
def onLineWeight (j : ℕ) : ℝ := (zetaOnLine.Wsummand (cx cubicSpline) (cx cubicSpline) (e j)).re

theorem isUnitaryChar_onLineChar (j : ℕ) : IsUnitaryChar (onLineChar e j) :=
  isUnitaryChar_logChar_imag _

theorem summable_onLineWeight : Summable (onLineWeight e) :=
  (e.summable_iff.mpr (summable_re_Wsummand zetaOnLine
    (temperedConfig_onLineConfig temperedConfig_zetaZeroConfig) cx_cubicSpline_contDiff
    cx_cubicSpline_hasCompactSupport cx_cubicSpline_contDiff cx_cubicSpline_hasCompactSupport))

/-- Distinct critical zeros give distinct characters on `ℚ_{>0}`. -/
theorem onLineChar_injective : Function.Injective (onLineChar e) := by
  intro i j hij
  set γi := (e i : ℂ).im
  set γj := (e j : ℂ).im
  have hγ : γi = γj := by
    by_contra hne
    have hd : 0 < |γi - γj| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨u, hu0, hu1⟩ := heckeLogScale_small (π / |γi - γj|) (div_pos Real.pi_pos hd)
    have h := congrArg (fun χ : HeckeLattice →* ℂ => χ u) hij
    simp only [onLineChar, logChar_apply] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have him := congrArg Complex.im hn
    simp only [mul_im, mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_mul,
      mul_one, add_zero, zero_add, intCast_re, intCast_im, ofNat_re, ofNat_im, add_im,
      one_mul, neg_re, neg_im, neg_zero, re_ofNat, im_ofNat, ofReal_ofNat] at him
    set s := scale heckeLogScale u
    have hns : (γj - γi) * s = n * (2 * π) := by linarith
    have hsmall : |(γj - γi) * s| < π := by
      rw [abs_mul, abs_of_pos hu0, abs_sub_comm]
      calc |γi - γj| * s < |γi - γj| * (π / |γi - γj|) := mul_lt_mul_of_pos_left hu1 hd
        _ = π := by field_simp
    rw [hns] at hsmall
    have hn0 : n = 0 := by
      by_contra hn0
      have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hsmall
      nlinarith [Real.pi_pos]
    rw [hn0, Int.cast_zero, zero_mul] at hns
    exact hne (by
      have := (mul_eq_zero.mp hns).resolve_right hu0.ne'
      linarith)
  apply e.injective
  apply Subtype.ext
  apply Complex.ext
  · rw [(e i).2.2, (e j).2.2]
  · exact hγ

/-- **The on-line part of Weil's kernel is a Bohr series.** -/
theorem orbitKernel_onLine_eq_bohrSum :
    orbitKernel zetaOnLine cubicSpline = bohrSum (onLineChar e) (onLineWeight e) := by
  funext u
  rw [orbitKernel_eq_tsum, ← e.tsum_eq]
  unfold bohrSum
  refine tsum_congr fun j => ?_
  have hρ := (e j).2
  set ρ : ℂ := (e j : ℂ)
  have hW := Wsummand_onLine hρ
  have hre : (zetaOnLine.Wsummand (cx cubicSpline) (cx cubicSpline) ρ) =
      ((onLineWeight e j : ℝ) : ℂ) := by
    rw [onLineWeight, hW, ofReal_re]
  have hs : (1 / 2 - ρ : ℂ) = (((-(ρ.im)) : ℝ) : ℂ) * I := by
    conv_lhs => rw [onLine_eq hρ]
    push_cast; ring
  rw [orbitTerm, hre, hs, mul_comm]
  rfl

end Bohr

/-- **The critical zeros carry infinitely many positive squares**: `κ₊(K_on) = ∞`. -/
theorem posIndex_orbitKernel_onLine_eq_top :
    posIndex (orbitKernel zetaOnLine cubicSpline) = ⊤ := by
  classical
  obtain ⟨e⟩ := exists_enum_onLine
  have hneg : (fun g => -orbitKernel zetaOnLine cubicSpline g) =
      bohrSum (onLineChar e) (fun j => -onLineWeight e j) := by
    funext u
    rw [orbitKernel_onLine_eq_bohrSum e]
    simp only [bohrSum, ofReal_neg, neg_mul, tsum_neg]
  rw [posIndex, hneg, negIndex_bohrSum (isUnitaryChar_onLineChar e) (summable_onLineWeight e).neg
    (onLineChar_injective e), Set.Infinite.encard_eq]
  -- every seen critical zero is a positive weight
  set g : ℂ → ℕ := fun ρ => if h : ρ ∈ zetaOnLine.carrier then e.symm ⟨ρ, h⟩ else 0
  refine Set.infinite_of_injOn_mapsTo (f := g) (s := criticalSeen) ?_ ?_ criticalSeen_infinite
  · intro ρ hρ ρ' hρ' h
    simp only [g, dif_pos (criticalSeen_subset hρ), dif_pos (criticalSeen_subset hρ')] at h
    exact congrArg Subtype.val (e.symm.injective h)
  · intro ρ hρ
    have hs := criticalSeen_subset hρ
    simp only [g, dif_pos hs, Set.mem_setOf_eq, neg_lt_zero, onLineWeight,
      Equiv.apply_symm_apply, Wsummand_onLine hs, ofReal_re]
    have hm : (1 : ℝ) ≤ zetaOnLine.mult ρ := by exact_mod_cast zetaOnLine.one_le_mult ρ hs
    have hF : 0 < ‖paperFT (cx cubicSpline) (ρ.im : ℂ)‖ := norm_pos_iff.mpr hρ.2.2
    positivity

/-- **On the finite stratum Weil's kernel has infinitely many positive squares.** -/
theorem posIndex_zetaKernel_eq_top_of_finite (hR : (rightZeros zetaZeroConfig).Finite) :
    posIndex zetaKernel = ⊤ := by
  classical
  set R := hR.toFinset
  set W : ℂ → ℂ := fun ρ => zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ
  set P : HeckeLattice → ℂ := fun u => ∑ ρ ∈ R, pairKernel (zeroChar (conj ρ)) (conj (W ρ)) u
  have hdec : ∀ u, zetaKernel u = orbitKernel zetaOnLine cubicSpline u + P u := fun u =>
    orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig cubicSpline_mem_realTests hR u
  have hP : IsHermKernel P := fun u => by
    simp only [P, map_sum, isHermKernel_pairKernel _ _ u]
  have hζ : IsHermKernel fun u => -zetaKernel u := fun u => by
    simp only [isHermKernel_zetaKernel u, map_neg]
  -- `−K_on = −K_ζ + P`
  have hon : (fun u => -orbitKernel zetaOnLine cubicSpline u) =
      fun u => -zetaKernel u + P u := by
    funext u; rw [hdec u]; ring
  have h1 := negIndex_add_le hζ hP
  rw [← hon] at h1
  have h2 : negIndex P ≤ R.card := by
    have h := negIndex_add_sum_pairKernel_le (J := R) HeckeKreinToeplitz.isPosDefKernel_zero
      (fun ρ => zeroChar (conj (ρ : ℂ))) (fun ρ => conj (W ρ))
    simp only [zero_add, Fintype.card_coe] at h
    convert h using 2
    funext u
    exact (R.sum_coe_sort fun ρ => pairKernel (zeroChar (conj ρ)) (conj (W ρ)) u).symm
  have htop : posIndex (orbitKernel zetaOnLine cubicSpline) = ⊤ :=
    posIndex_orbitKernel_onLine_eq_top
  rw [posIndex] at htop
  rw [htop] at h1
  by_contra hne
  have : negIndex (fun u => -zetaKernel u) + negIndex P < ⊤ :=
    ENat.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hne, h2.trans_lt (ENat.coe_lt_top _)⟩
  exact absurd (top_le_iff.mp h1) this.ne

/-- **The Künneth square of Weil's kernel is all-or-nothing**: either RH holds, or
`K_ζ ⊠ K_ζ` has infinitely many negative squares. -/
theorem riemannHypothesis_or_negIndex_kunnethZeta_eq_top :
    RiemannHypothesis ∨ negIndex kunnethZeta = ⊤ := by
  rcases (rightZeros zetaZeroConfig).finite_or_infinite with hR | hR
  · rcases negIndex_tensorKernel_self_eq_zero_or_top isHermKernel_zetaKernel
      (posIndex_zetaKernel_eq_top_of_finite hR) with h | h
    · exact Or.inl (riemannHypothesis_iff_negIndex_kunnethZeta_eq_zero.mpr h)
    · exact Or.inr h
  · right
    have htop : negIndex zetaKernel = ⊤ := by
      rw [negIndex_zetaKernel]; exact Set.encard_eq_top_iff.mpr hR
    exact top_le_iff.mp (htop ▸ negIndex_zetaKernel_le_negIndex_kunnethZeta)

end GaloisForLFunctions.RenormalizedIntersectionTheory
