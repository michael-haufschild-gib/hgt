import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.RingTheory.Polynomial.Dickson
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Multipliers at fixed points of the special rational maps

The multiplier of a fixed point is invariant under any locally invertible conjugacy.  For the two
polynomial families on the Ritt list — the power maps and the normalized Chebyshev (Dickson) maps —
every finite fixed point has multiplier `0` or of modulus at least the degree.  Consequently a map
carrying a fixed point that is attracting but not superattracting, or parabolic, is conjugate to
neither family.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- **The multiplier is a conjugacy invariant.** -/
theorem multiplier_eq_of_conj {R S φ : ℂ → ℂ} {c dR dS dφ : ℂ}
    (hconj : ∀ z, φ (R z) = S (φ z))
    (hR : HasDerivAt R dR c) (hfix : R c = c)
    (hφ : HasDerivAt φ dφ c) (hφne : dφ ≠ 0)
    (hS : HasDerivAt S dS (φ c)) : dS = dR := by
  have hφR : HasDerivAt φ dφ (R c) := by rw [hfix]; exact hφ
  have h1 : HasDerivAt (fun z => φ (R z)) (dφ * dR) c := hφR.comp c hR
  have h2 : HasDerivAt (fun z => S (φ z)) (dS * dφ) c := hS.comp c hφ
  have hfun : (fun z => φ (R z)) = fun z => S (φ z) := funext hconj
  rw [hfun] at h1
  have heq : dS * dφ = dφ * dR := h2.unique h1
  have : dφ * dS = dφ * dR := by rw [← heq]; ring
  exact mul_left_cancel₀ hφne this

/-- The `n`-th power map. -/
def powerMap (n : ℕ) : ℂ → ℂ := fun z => z ^ n

theorem hasDerivAt_powerMap (n : ℕ) (c : ℂ) :
    HasDerivAt (powerMap n) ((n : ℂ) * c ^ (n - 1)) c := hasDerivAt_pow n c

/-- **Every finite fixed point of a power map is superattracting or repelling.** -/
theorem powerMap_multiplier {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hfix : powerMap n c = c) :
    (n : ℂ) * c ^ (n - 1) = 0 ∨ (n : ℂ) * c ^ (n - 1) = (n : ℂ) := by
  by_cases hc : c = 0
  · left
    subst hc
    have : (0 : ℂ) ^ (n - 1) = 0 := zero_pow (by omega)
    rw [this, mul_zero]
  · right
    have hpow : c ^ (n - 1) = 1 := by
      have hsplit : c ^ n = c ^ (n - 1) * c := by
        rw [← pow_succ]
        congr 1
        omega
      have := hfix
      rw [powerMap, hsplit] at this
      field_simp at this
      exact this
    rw [hpow, mul_one]

/-- A power map has no fixed point whose multiplier is nonzero of modulus at most one. -/
theorem powerMap_no_nonsuper_nonrepelling {n : ℕ} (hn : 2 ≤ n) {c : ℂ}
    (hfix : powerMap n c = c) (hne : (n : ℂ) * c ^ (n - 1) ≠ 0)
    (hle : ‖(n : ℂ) * c ^ (n - 1)‖ ≤ 1) : False := by
  rcases powerMap_multiplier hn hfix with h | h
  · exact hne h
  · rw [h] at hle
    have : (2 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast hn
    linarith

/-- **No map with an attracting-but-not-superattracting or parabolic fixed point is conjugate to a
power map.** -/
theorem not_conj_powerMap_of_nonsuper_nonrepelling {n : ℕ} (hn : 2 ≤ n)
    {R φ : ℂ → ℂ} {c dR dφ : ℂ}
    (hconj : ∀ z, φ (R z) = powerMap n (φ z))
    (hR : HasDerivAt R dR c) (hfix : R c = c)
    (hφ : HasDerivAt φ dφ c) (hφne : dφ ≠ 0)
    (hdR : dR ≠ 0) (hle : ‖dR‖ ≤ 1) : False := by
  have hfix' : powerMap n (φ c) = φ c := by
    have := hconj c
    rw [hfix] at this
    exact this.symm
  have hmul := multiplier_eq_of_conj hconj hR hfix hφ hφne (hasDerivAt_powerMap n (φ c))
  refine powerMap_no_nonsuper_nonrepelling hn hfix' ?_ ?_
  · rw [hmul]; exact hdR
  · rw [hmul]; exact hle

/-- The normalized Chebyshev (Dickson) map of degree `n`. -/
def dicksonMap (n : ℕ) : ℂ → ℂ := fun z => (Polynomial.dickson 1 1 n).eval z

theorem hasDerivAt_dicksonMap (n : ℕ) (c : ℂ) :
    HasDerivAt (dicksonMap n) ((Polynomial.derivative (Polynomial.dickson 1 1 n)).eval c) c :=
  Polynomial.hasDerivAt _ c

/-- Every complex number is a Joukowski image of a nonzero point. -/
theorem exists_joukowski (c : ℂ) : ∃ w : ℂ, w ≠ 0 ∧ w + w⁻¹ = c := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c ^ 2 - 4 : ℂ) (n := 2) (by norm_num)
  refine ⟨(c + s) / 2, ?_, ?_⟩
  · intro h
    have hq : ((c + s) / 2) ^ 2 - c * ((c + s) / 2) + 1 = 0 := by
      field_simp
      linear_combination hs
    rw [h] at hq
    simp at hq
  · have hq : ((c + s) / 2) ^ 2 - c * ((c + s) / 2) + 1 = 0 := by
      field_simp
      linear_combination hs
    have hne : ((c + s) / 2 : ℂ) ≠ 0 := by
      intro h
      rw [h] at hq
      simp at hq
    have hcs : (c + s : ℂ) ≠ 0 := by
      intro h
      apply hne
      rw [h]
      simp
    have h1 : ((c + s) / 2) * ((c + s) / 2 + ((c + s) / 2)⁻¹) = ((c + s) / 2) ^ 2 + 1 := by
      field_simp
    have h2 : ((c + s) / 2) ^ 2 + 1 = ((c + s) / 2) * c := by linear_combination hq
    rw [h2] at h1
    exact mul_left_cancel₀ hne h1

theorem dicksonMap_joukowski (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    dicksonMap n (w + w⁻¹) = w ^ n + (w ^ n)⁻¹ := by
  rw [dicksonMap, Polynomial.dickson_one_one_eval_add_inv w w⁻¹ (mul_inv_cancel₀ hw) n, inv_pow]

/-- Differentiating the Joukowski semiconjugacy. -/
theorem dicksonMap_deriv_joukowski (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (Polynomial.derivative (Polynomial.dickson 1 1 n)).eval (w + w⁻¹) * (1 + -(w ^ 2)⁻¹) =
      (n : ℂ) * w ^ (n - 1) + -((n : ℂ) * w ^ (n - 1)) / (w ^ n) ^ 2 := by
  have hjou := (hasDerivAt_id w).add (hasDerivAt_inv hw)
  have hf := (hasDerivAt_dicksonMap n (w + w⁻¹)).comp w hjou
  have hpow : HasDerivAt (fun t : ℂ => t ^ n) ((n : ℂ) * w ^ (n - 1)) w := hasDerivAt_pow n w
  have hwn : w ^ n ≠ 0 := pow_ne_zero n hw
  have hg : HasDerivAt (fun t : ℂ => t ^ n + (t ^ n)⁻¹)
      ((n : ℂ) * w ^ (n - 1) + -((n : ℂ) * w ^ (n - 1)) / (w ^ n) ^ 2) w :=
    hpow.add (hpow.inv hwn)
  have heq : (fun t : ℂ => t ^ n + (t ^ n)⁻¹) =ᶠ[nhds w] fun t : ℂ => dicksonMap n (t + t⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with t ht
    exact (dicksonMap_joukowski n ht).symm
  exact (hf.congr_of_eventuallyEq heq).unique hg

/-- The derivative of the Dickson map on the doubled Chebyshev variable. -/
theorem dickson_derivative_eval_two_mul (n : ℕ) (x : ℂ) :
    (Polynomial.derivative (Polynomial.dickson 1 1 n)).eval (2 * x) =
      (n : ℂ) * (Polynomial.Chebyshev.U ℂ ((n : ℤ) - 1)).eval x := by
  have hC : (Polynomial.Chebyshev.C ℂ (n : ℤ)).comp (2 * Polynomial.X) =
      2 * Polynomial.Chebyshev.T ℂ (n : ℤ) := Polynomial.Chebyshev.C_comp_two_mul_X ℂ _
  have hD := congrArg Polynomial.derivative hC
  simp only [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_X,
    Polynomial.derivative_ofNat, Polynomial.Chebyshev.T_derivative_eq_U, zero_mul, mul_one,
    zero_add] at hD
  have hDeval := congrArg (fun q : Polynomial ℂ => q.eval x) hD
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_ofNat, Polynomial.eval_X,
    Polynomial.eval_intCast] at hDeval
  rw [Polynomial.dickson_one_one_eq_chebyshev_C]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  field_simp at hDeval
  push_cast at hDeval ⊢
  linear_combination hDeval

/-- **Every finite fixed point of a Chebyshev map has multiplier of modulus at least the degree.** -/
theorem two_le_norm_dicksonMap_multiplier {n : ℕ} (hn : 2 ≤ n) {c : ℂ}
    (hfix : dicksonMap n c = c) :
    2 ≤ ‖(Polynomial.derivative (Polynomial.dickson 1 1 n)).eval c‖ := by
  obtain ⟨w, hw, rfl⟩ := exists_joukowski c
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases hw2 : w ^ 2 = 1
  · have hcases : w = 1 ∨ w = -1 := by
      have : (w - 1) * (w + 1) = 0 := by linear_combination hw2
      rcases mul_eq_zero.mp this with h | h
      · left
        exact sub_eq_zero.mp h
      · right
        linear_combination h
    rcases hcases with rfl | rfl
    · have hval : (1 : ℂ) + (1 : ℂ)⁻¹ = 2 * 1 := by norm_num
      rw [hval, dickson_derivative_eval_two_mul, Polynomial.Chebyshev.U_eval_one]
      push_cast
      rw [show ((n : ℂ) - 1 + 1) = (n : ℂ) by ring]
      simp only [Complex.norm_mul, Complex.norm_natCast]
      nlinarith
    · have hval : (-1 : ℂ) + (-1 : ℂ)⁻¹ = 2 * (-1) := by norm_num
      rw [hval, dickson_derivative_eval_two_mul, Polynomial.Chebyshev.U_eval_neg_one]
      have h1 : ‖(((((n : ℤ) - 1).negOnePow : ℤ) : ℂ))‖ = 1 := by
        rcases Int.units_eq_one_or ((n : ℤ) - 1).negOnePow with h | h <;> rw [h] <;> simp
      rw [Complex.norm_mul, Complex.norm_mul, h1]
      push_cast
      rw [show ‖((n : ℂ) - 1 + 1)‖ = ‖(n : ℂ)‖ by rw [show ((n : ℂ) - 1 + 1) = (n : ℂ) by ring]]
      simp only [Complex.norm_natCast, one_mul]
      nlinarith
  · have hfac : (1 : ℂ) - (w ^ 2)⁻¹ ≠ 0 := by
      intro h
      apply hw2
      have hw2ne : (w ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hw
      field_simp at h
      linear_combination h
    have hjfix : w ^ n + (w ^ n)⁻¹ = w + w⁻¹ := by
      rw [← dicksonMap_joukowski n hw]
      exact hfix
    have hwn : w ^ n ≠ 0 := pow_ne_zero n hw
    have hsplit : (w ^ n - w) * (w ^ n * w - 1) = 0 := by
      field_simp at hjfix
      linear_combination hjfix
    have hderiv := dicksonMap_deriv_joukowski n hw
    rcases mul_eq_zero.mp hsplit with h | h
    · have hwn_eq : w ^ n = w := sub_eq_zero.mp h
      have hwn1 : w ^ (n - 1) = 1 := by
        have hstep : w ^ (n - 1) * w = w ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hwn_eq] at hstep
        refine mul_right_cancel₀ hw ?_
        rw [hstep, one_mul]
      rw [hwn1, hwn_eq] at hderiv
      have hstep2 : (Polynomial.derivative (Polynomial.dickson 1 1 n)).eval (w + w⁻¹) *
          (1 + -(w ^ 2)⁻¹) = (n : ℂ) * (1 + -(w ^ 2)⁻¹) := by
        rw [hderiv]
        have hw2ne : (w ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hw
        field_simp
        try ring
      have hval := mul_right_cancel₀ hfac hstep2
      rw [hval, Complex.norm_natCast]
      exact hn'
    · have hwn_eq : w ^ n = w⁻¹ := by
        field_simp
        linear_combination h
      have hwn1 : w ^ (n - 1) = (w ^ 2)⁻¹ := by
        have hstep : w ^ (n - 1) * w = w ^ n := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hwn_eq] at hstep
        refine mul_right_cancel₀ hw ?_
        rw [hstep]
        field_simp
      rw [hwn1, hwn_eq] at hderiv
      have hstep2 : (Polynomial.derivative (Polynomial.dickson 1 1 n)).eval (w + w⁻¹) *
          (1 + -(w ^ 2)⁻¹) = -(n : ℂ) * (1 + -(w ^ 2)⁻¹) := by
        rw [hderiv]
        have hw2ne : (w ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hw
        field_simp
        try ring
      have hval := mul_right_cancel₀ hfac hstep2
      rw [hval, norm_neg, Complex.norm_natCast]
      exact hn'

/-- **No map with an attracting-but-not-superattracting or parabolic fixed point is conjugate to a
Chebyshev map.** -/
theorem not_conj_dicksonMap_of_nonrepelling {n : ℕ} (hn : 2 ≤ n)
    {R φ : ℂ → ℂ} {c dR dφ : ℂ}
    (hconj : ∀ z, φ (R z) = dicksonMap n (φ z))
    (hR : HasDerivAt R dR c) (hfix : R c = c)
    (hφ : HasDerivAt φ dφ c) (hφne : dφ ≠ 0)
    (hle : ‖dR‖ ≤ 1) : False := by
  have hfix' : dicksonMap n (φ c) = φ c := by
    have := hconj c
    rw [hfix] at this
    exact this.symm
  have hmul := multiplier_eq_of_conj hconj hR hfix hφ hφne (hasDerivAt_dicksonMap n (φ c))
  have := two_le_norm_dicksonMap_multiplier hn hfix'
  rw [hmul] at this
  linarith

/-- The inverse power map. -/
def invPowerMap (n : ℕ) : ℂ → ℂ := fun z => (z ^ n)⁻¹

theorem hasDerivAt_invPowerMap (n : ℕ) {c : ℂ} (hc : c ≠ 0) :
    HasDerivAt (invPowerMap n) (-((n : ℂ) * c ^ (n - 1)) / (c ^ n) ^ 2) c :=
  (hasDerivAt_pow n c).inv (pow_ne_zero n hc)

/-- **Every finite nonzero fixed point of an inverse power map is repelling.** -/
theorem invPowerMap_multiplier {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : c ≠ 0)
    (hfix : invPowerMap n c = c) :
    -((n : ℂ) * c ^ (n - 1)) / (c ^ n) ^ 2 = -(n : ℂ) := by
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  have hkey : c ^ (n + 1) = 1 := by
    have : (c ^ n)⁻¹ = c := hfix
    field_simp at this
    rw [pow_succ]
    linear_combination -this
  have hstep : c ^ (n - 1) = c ^ n * c ^ n := by
    have h1 : c ^ (n - 1) * c ^ (n + 1) = c ^ n * c ^ n := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hkey, mul_one] at h1
    exact h1
  rw [hstep]
  field_simp

/-- **No map with an attracting-but-not-superattracting or parabolic fixed point is conjugate to an
inverse power map.** -/
theorem not_conj_invPowerMap_of_nonrepelling {n : ℕ} (hn : 2 ≤ n)
    {R φ : ℂ → ℂ} {c dR dφ : ℂ}
    (hconj : ∀ z, φ (R z) = invPowerMap n (φ z))
    (hR : HasDerivAt R dR c) (hfix : R c = c)
    (hφ : HasDerivAt φ dφ c) (hφne : dφ ≠ 0) (hφc : φ c ≠ 0)
    (hle : ‖dR‖ ≤ 1) : False := by
  have hfix' : invPowerMap n (φ c) = φ c := by
    have := hconj c
    rw [hfix] at this
    exact this.symm
  have hmul := multiplier_eq_of_conj hconj hR hfix hφ hφne
    (hasDerivAt_invPowerMap n hφc)
  rw [invPowerMap_multiplier hn hφc hfix'] at hmul
  rw [← hmul, norm_neg, Complex.norm_natCast] at hle
  have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- **A linearizing semiconjugacy forces every fixed point to be repelling.**  If `R ∘ π = π ∘ (a ·)`
with `1 < ‖a‖`, then at every fixed point coming from a regular point of `π` whose orbit point has
the same `‖π'‖`, the multiplier has modulus `‖a‖`.  This is the mechanism common to the power,
Chebyshev and elliptic (Lattès) branches of the Ritt list. -/
theorem norm_multiplier_of_linearizingSemiconj {R π : ℂ → ℂ} {a z₀ dR dπ dπa : ℂ}
    (hsemi : ∀ z, R (π z) = π (a * z))
    (hπ : HasDerivAt π dπ z₀) (hπa : HasDerivAt π dπa (a * z₀)) (hπne : dπ ≠ 0)
    (hR : HasDerivAt R dR (π z₀))
    (hnorm : ‖dπa‖ = ‖dπ‖) :
    ‖dR‖ = ‖a‖ := by
  have hleft : HasDerivAt (fun z => R (π z)) (dR * dπ) z₀ := hR.comp z₀ hπ
  have hmul : HasDerivAt (fun z : ℂ => a * z) a z₀ := by
    simpa using (hasDerivAt_id z₀).const_mul a
  have hright : HasDerivAt (fun z => π (a * z)) (dπa * a) z₀ := hπa.comp z₀ hmul
  have hfun : (fun z => R (π z)) = fun z => π (a * z) := funext hsemi
  rw [hfun] at hleft
  have heq : dR * dπ = dπa * a := hleft.unique hright
  have hn : ‖dR‖ * ‖dπ‖ = ‖a‖ * ‖dπ‖ := by
    have := congrArg norm heq
    rw [norm_mul, norm_mul, hnorm] at this
    rw [this]
    ring
  have hdπpos : 0 < ‖dπ‖ := norm_pos_iff.mpr hπne
  exact mul_right_cancel₀ (ne_of_gt hdπpos) hn

/-! ## The elliptic (Lattès) branch -/

open PeriodPair

/-- The Weierstrass function is differentiable off the lattice, with derivative `℘'`. -/
theorem hasDerivAt_weierstrassP {L : PeriodPair} {z : ℂ} (hz : z ∉ (L.lattice : Set ℂ)) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hopen : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hda : DifferentiableAt ℂ L.weierstrassP z :=
    L.differentiableOn_weierstrassP.differentiableAt (hopen.mem_nhds hz)
  have h := hda.hasDerivAt
  rwa [L.deriv_weierstrassP] at h

/-- **Equal `℘`-values force equal `|℘'|`.**  Immediate from the Weierstrass differential
equation `℘'² = 4℘³ − g₂℘ − g₃`. -/
theorem norm_derivWeierstrassP_eq_of_weierstrassP_eq {L : PeriodPair} {u v : ℂ}
    (hu : u ∉ (L.lattice : Set ℂ)) (hv : v ∉ (L.lattice : Set ℂ))
    (h : L.weierstrassP u = L.weierstrassP v) :
    ‖L.derivWeierstrassP u‖ = ‖L.derivWeierstrassP v‖ := by
  have h1 := L.derivWeierstrassP_sq u hu
  have h2 := L.derivWeierstrassP_sq v hv
  rw [h] at h1
  have hsq : L.derivWeierstrassP u ^ 2 = L.derivWeierstrassP v ^ 2 := by rw [h1, ← h2]
  have hn : ‖L.derivWeierstrassP u‖ ^ 2 = ‖L.derivWeierstrassP v‖ ^ 2 := by
    rw [← norm_pow, ← norm_pow, hsq]
  have h0 : (0 : ℝ) ≤ ‖L.derivWeierstrassP u‖ := norm_nonneg _
  have h0' : (0 : ℝ) ≤ ‖L.derivWeierstrassP v‖ := norm_nonneg _
  nlinarith

/-- **The multiplier of a Lattès map at a regular fixed point.**  If `R ∘ ℘ = ℘ ∘ (a ·)`, then at a
fixed point coming from a point off the lattice where `℘' ≠ 0`, the multiplier has modulus `‖a‖`. -/
theorem norm_multiplier_lattes {L : PeriodPair} {a z₀ : ℂ} {R : ℂ → ℂ} {dR : ℂ}
    (hsemi : ∀ z, R (L.weierstrassP z) = L.weierstrassP (a * z))
    (hz₀ : z₀ ∉ (L.lattice : Set ℂ)) (haz₀ : a * z₀ ∉ (L.lattice : Set ℂ))
    (hne : L.derivWeierstrassP z₀ ≠ 0)
    (hR : HasDerivAt R dR (L.weierstrassP z₀))
    (hfix : R (L.weierstrassP z₀) = L.weierstrassP z₀) :
    ‖dR‖ = ‖a‖ := by
  have hpe : L.weierstrassP (a * z₀) = L.weierstrassP z₀ := by
    rw [← hsemi z₀, hfix]
  have hnorm : ‖L.derivWeierstrassP (a * z₀)‖ = ‖L.derivWeierstrassP z₀‖ :=
    norm_derivWeierstrassP_eq_of_weierstrassP_eq haz₀ hz₀ hpe
  exact norm_multiplier_of_linearizingSemiconj hsemi (hasDerivAt_weierstrassP hz₀)
    (hasDerivAt_weierstrassP haz₀) hne hR hnorm

/-- **A Lattès map has no attracting-but-not-superattracting or parabolic regular fixed point.** -/
theorem not_lattes_of_nonrepelling {L : PeriodPair} {a z₀ : ℂ} {R : ℂ → ℂ} {dR : ℂ}
    (ha : 1 < ‖a‖)
    (hsemi : ∀ z, R (L.weierstrassP z) = L.weierstrassP (a * z))
    (hz₀ : z₀ ∉ (L.lattice : Set ℂ)) (haz₀ : a * z₀ ∉ (L.lattice : Set ℂ))
    (hne : L.derivWeierstrassP z₀ ≠ 0)
    (hR : HasDerivAt R dR (L.weierstrassP z₀))
    (hfix : R (L.weierstrassP z₀) = L.weierstrassP z₀)
    (hle : ‖dR‖ ≤ 1) : False := by
  rw [norm_multiplier_lattes hsemi hz₀ haz₀ hne hR hfix] at hle
  linarith

end

end GaloisForLFunctions.HTGeometry
