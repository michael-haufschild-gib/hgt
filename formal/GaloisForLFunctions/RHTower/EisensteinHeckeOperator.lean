import GaloisForLFunctions.RHTower.EisensteinHeckeCoefficient
import GaloisForLFunctions.RHTower.EisensteinLineModelBounds
import GaloisForLFunctions.RHTower.HeckeOperatorBasic

/-!
# Hecke operators on the Eisenstein line model

The Hecke operator `T_p` acts on functions of `(x, y)` on the upper half-plane by
`(T_p F)(x, y) = p^{-1/2} (F(px, py) + Σ_{b < p} F((x + b)/p, y/p))`.  On the Fourier tail
`Σ_n W_u(n) e(±nx) √y K_u(2πny)` of the completed Eisenstein series the first term shifts the
frequency `n ↦ pn` and the residue sum over `b` keeps only the frequencies divisible by `p`, so the
`m`-th coefficient of `T_p tail` is `1_{p ∣ m} W_u(m/p) + W_u(pm)`.  By the Hecke relation of the
Whittaker coefficients this is `(p^u + p^{-u}) W_u(m)`.  Together with the same computation on the
two Weyl powers of the constant term this gives the Hecke eigen-equation
`T_p E_u = (p^u + p^{-u}) E_u` of the Eisenstein line model at every parameter `u`.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The Hecke operator on functions of `(x, y)` -/

theorem heckeOp_add (p : ℕ) (F G : ℝ → ℝ → ℂ) (x y : ℝ) :
    heckeOp p (fun x y => F x y + G x y) x y = heckeOp p F x y + heckeOp p G x y := by
  unfold heckeOp
  rw [Finset.sum_add_distrib]
  ring

theorem heckeOp_const_mul (p : ℕ) (c : ℂ) (F : ℝ → ℝ → ℂ) (x y : ℝ) :
    heckeOp p (fun x y => c * F x y) x y = c * heckeOp p F x y := by
  unfold heckeOp
  rw [← Finset.mul_sum]
  ring

/-! ## The base term of the Fourier tail -/

/-- The `M`-th base term `e(±(M+1)x) √y K_u(2π(M+1)y)` of the Fourier tail. -/
def baseTerm (negative : Bool) (x y : ℝ) (M : ℕ) (u : ℂ) : ℂ :=
  d4BMCompletedEisensteinFourierPhase negative M x * (Real.sqrt y : ℂ) *
    modifiedBesselKOrder (2 * Real.pi * ((M : ℝ) + 1) * y) u

theorem eisensteinTailTerm_eq_whittaker_mul_base (negative : Bool) (x y : ℝ) (M : ℕ) (u : ℂ) :
    eisensteinTailTerm negative x y M u = whittakerCoeff u (M + 1) * baseTerm negative x y M u := by
  unfold eisensteinTailTerm baseTerm
  rw [whittakerCoeff_eq]
  simp only [pow_zero, mul_one]
  ring

/-! ## The residue sum of the Fourier phases -/

theorem fourierPhase_div_split (negative : Bool) (N : ℕ) {p : ℕ} (hp : 0 < p) (x : ℝ) (b : ℕ) :
    d4BMCompletedEisensteinFourierPhase negative N ((x + b) / p) =
      Complex.exp (((d4BMFourierSign negative * (2 * Real.pi * ((N : ℝ) + 1) * x / p) : ℝ) : ℂ) * I) *
        Complex.exp (((d4BMFourierSign negative * (2 * Real.pi * ((N : ℝ) + 1) / p) : ℝ) : ℂ) * I) ^ b := by
  unfold d4BMCompletedEisensteinFourierPhase
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

theorem fourierSign_mul_self (negative : Bool) :
    d4BMFourierSign negative * d4BMFourierSign negative = 1 := by
  cases negative <;> simp [d4BMFourierSign]

/-- `Σ_{b<p} e(±(N+1)(x+b)/p) = p · e(±((N+1)/p) x)` if `p ∣ N + 1`, and `0` otherwise. -/
theorem sum_fourierPhase_div (negative : Bool) {p : ℕ} (hp : p.Prime) (N : ℕ) (x : ℝ) :
    ∑ b ∈ range p, d4BMCompletedEisensteinFourierPhase negative N ((x + b) / p) =
      if p ∣ N + 1 then
        (p : ℂ) * d4BMCompletedEisensteinFourierPhase negative ((N + 1) / p - 1) x
      else 0 := by
  have hp0 : 0 < p := hp.pos
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  simp_rw [fourierPhase_div_split negative N hp0 x]
  rw [← Finset.mul_sum]
  set σ : ℝ := d4BMFourierSign negative with hσ
  have hσσ : σ * σ = 1 := fourierSign_mul_self negative
  set ω : ℂ := Complex.exp (((σ * (2 * Real.pi * ((N : ℝ) + 1) / p) : ℝ) : ℂ) * I) with hω
  by_cases hdvd : p ∣ N + 1
  · rw [if_pos hdvd]
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hdiv : (N + 1) / p = m := by rw [hm, Nat.mul_div_cancel_left _ hp0]
    have hNm : ((N : ℝ) + 1) = p * m := by exact_mod_cast hm
    have hω1 : ω = 1 := by
      rw [hω, Complex.exp_eq_one_iff]
      cases negative
      · refine ⟨m, ?_⟩
        simp only [hσ, d4BMFourierSign, Bool.false_eq_true, if_false]
        rw [hNm]
        push_cast
        field_simp [hpC]
      · refine ⟨-(m : ℤ), ?_⟩
        simp only [hσ, d4BMFourierSign, if_true]
        rw [hNm]
        push_cast
        field_simp [hpC]
    rw [hω1]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hdiv, mul_comm]
    congr 1
    unfold d4BMCompletedEisensteinFourierPhase
    congr 2
    rw [Nat.cast_sub hm1, hNm]
    push_cast
    field_simp
    ring
  · rw [if_neg hdvd]
    have hω1 : ω ≠ 1 := by
      intro h1
      apply hdvd
      have hre := congrArg Complex.re h1
      rw [hω, Complex.exp_ofReal_mul_I_re, Complex.one_re, Real.cos_eq_one_iff] at hre
      obtain ⟨n, hn⟩ := hre
      -- `σ (N+1)/p = n`, hence `N + 1 = σ n p`
      have h2 : σ * (2 * Real.pi * ((N : ℝ) + 1) / p) = n * (2 * Real.pi) := hn.symm
      rw [mul_div_assoc', div_eq_iff hpR] at h2
      have h3 : σ * ((N : ℝ) + 1) = n * p := by
        apply mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0)
        linear_combination h2
      have h4 : σ * (σ * ((N : ℝ) + 1)) = σ * (n * p) := by rw [h3]
      rw [← mul_assoc, hσσ, one_mul] at h4
      have hkey : ((N : ℝ) + 1) = σ * n * p := by linear_combination h4
      cases negative
      · simp only [hσ, d4BMFourierSign, Bool.false_eq_true, if_false, one_mul] at hkey
        have hz : ((N + 1 : ℕ) : ℤ) = n * p := by exact_mod_cast hkey
        exact Int.natCast_dvd_natCast.mp ⟨n, by rw [hz]; ring⟩
      · simp only [hσ, d4BMFourierSign, if_true] at hkey
        have hkey' : ((N : ℝ) + 1) = -((n : ℝ) * p) := by linarith [hkey]
        have hz : ((N + 1 : ℕ) : ℤ) = -(n * p) := by exact_mod_cast hkey'
        exact Int.natCast_dvd_natCast.mp ⟨-n, by rw [hz]; ring⟩
    have hωp : ω ^ p = 1 := by
      rw [hω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
      cases negative
      · refine ⟨((N : ℤ) + 1), ?_⟩
        simp only [hσ, d4BMFourierSign, Bool.false_eq_true, if_false]
        push_cast
        field_simp [hpC]
      · refine ⟨-((N : ℤ) + 1), ?_⟩
        simp only [hσ, d4BMFourierSign, if_true]
        push_cast
        field_simp [hpC]
    rw [geom_sum_eq hω1 p, hωp, sub_self, zero_div, mul_zero]

/-! ## Scaling of the base terms -/

/-- The frequency shift `N ↦ p(N+1) − 1`. -/
def heckeShift (p N : ℕ) : ℕ := p * (N + 1) - 1

theorem heckeShift_add_one {p : ℕ} (hp : 0 < p) (N : ℕ) : heckeShift p N + 1 = p * (N + 1) := by
  unfold heckeShift
  have h1 : 1 ≤ p * (N + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

theorem heckeShift_injective {p : ℕ} (hp : 0 < p) : Function.Injective (heckeShift p) := by
  intro N N' h
  have h1 := heckeShift_add_one hp N
  have h2 := heckeShift_add_one hp N'
  rw [h] at h1
  have h3 : p * (N + 1) = p * (N' + 1) := by rw [← h1, ← h2]
  have h4 := Nat.eq_of_mul_eq_mul_left hp h3
  omega

theorem heckeShift_cast_add_one {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ((heckeShift p N : ℕ) : ℝ) + 1 = (p : ℝ) * ((N : ℝ) + 1) := by
  have h := heckeShift_add_one hp N
  have h' : ((heckeShift p N + 1 : ℕ) : ℝ) = ((p * (N + 1) : ℕ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem dvd_heckeShift_add_one {p : ℕ} (hp : 0 < p) (N : ℕ) : p ∣ heckeShift p N + 1 := by
  rw [heckeShift_add_one hp]
  exact Dvd.intro _ rfl

theorem heckeShift_add_one_div {p : ℕ} (hp : 0 < p) (N : ℕ) : (heckeShift p N + 1) / p = N + 1 := by
  rw [heckeShift_add_one hp, Nat.mul_div_cancel_left _ hp]

theorem exists_heckeShift_of_dvd {p : ℕ} {M : ℕ} (hdvd : p ∣ M + 1) :
    ∃ N, heckeShift p N = M := by
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  refine ⟨m - 1, ?_⟩
  unfold heckeShift
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  rw [Nat.sub_add_cancel hm1]
  omega

theorem baseTerm_scale (negative : Bool) {p : ℕ} (hp : 0 < p) (x y : ℝ) (N : ℕ) (u : ℂ) :
    baseTerm negative (p * x) (p * y) N u =
      (Real.sqrt p : ℂ) * baseTerm negative x y (heckeShift p N) u := by
  have hcast := heckeShift_cast_add_one hp N
  unfold baseTerm
  have hph : d4BMCompletedEisensteinFourierPhase negative N (p * x) =
      d4BMCompletedEisensteinFourierPhase negative (heckeShift p N) x := by
    unfold d4BMCompletedEisensteinFourierPhase
    rw [hcast]
    congr 3
    ring
  have hK : 2 * Real.pi * ((N : ℝ) + 1) * (p * y) =
      2 * Real.pi * (((heckeShift p N : ℕ) : ℝ) + 1) * y := by
    rw [hcast]
    ring
  rw [hph, hK, Real.sqrt_mul (Nat.cast_nonneg p) y]
  push_cast
  ring

theorem sqrt_bessel_div {p : ℕ} (hp : 0 < p) (y : ℝ) {N : ℕ} (hdvd : p ∣ N + 1) (u : ℂ) :
    (Real.sqrt (y / p) : ℂ) * modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * (y / p)) u =
      (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * (Real.sqrt y : ℂ) *
        modifiedBesselKOrder (2 * Real.pi * ((((N + 1) / p - 1 : ℕ) : ℝ) + 1) * y) u := by
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hdiv : (N + 1) / p = m := by rw [hm, Nat.mul_div_cancel_left _ hp]
  have hNm : ((N : ℝ) + 1) = p * m := by exact_mod_cast hm
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hK : 2 * Real.pi * ((N : ℝ) + 1) * (y / p) =
      2 * Real.pi * ((((N + 1) / p - 1 : ℕ) : ℝ) + 1) * y := by
    rw [hdiv, Nat.cast_sub hm1, hNm]
    push_cast
    field_simp
    ring
  rw [hK, Real.sqrt_div' y (Nat.cast_nonneg p)]
  push_cast
  ring

/-! ## The two reindexed sums -/

/-- The `p`-divisible part of the tail with the coefficient `W_u(m/p)`. -/
def heckeDivisibleTerm (negative : Bool) {p : ℕ} (x y : ℝ) (u : ℂ) (M : ℕ) : ℂ :=
  if p ∣ M + 1 then whittakerCoeff u ((M + 1) / p) * baseTerm negative x y M u else 0

theorem tsum_tailTerm_scale (negative : Bool) {p : ℕ} (hp : 0 < p) (x y : ℝ) (u : ℂ) :
    ∑' N : ℕ, eisensteinTailTerm negative (p * x) (p * y) N u =
      (Real.sqrt p : ℂ) * ∑' M : ℕ, heckeDivisibleTerm negative (p := p) x y u M := by
  have hterm : ∀ N : ℕ, eisensteinTailTerm negative (p * x) (p * y) N u =
      (Real.sqrt p : ℂ) * heckeDivisibleTerm negative (p := p) x y u (heckeShift p N) := by
    intro N
    rw [eisensteinTailTerm_eq_whittaker_mul_base, baseTerm_scale negative hp x y N u]
    unfold heckeDivisibleTerm
    rw [if_pos (dvd_heckeShift_add_one hp N), heckeShift_add_one_div hp]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  congr 1
  apply (heckeShift_injective hp).tsum_eq
  intro M hM
  rw [Function.mem_support] at hM
  have hdvd : p ∣ M + 1 := by
    by_contra hnd
    apply hM
    unfold heckeDivisibleTerm
    rw [if_neg hnd]
  obtain ⟨N, hN⟩ := exists_heckeShift_of_dvd hdvd
  exact ⟨N, hN⟩

/-- The residue-summed tail term at height `y/p`. -/
def heckeResidueTerm (negative : Bool) {p : ℕ} (x y : ℝ) (u : ℂ) (N : ℕ) : ℂ :=
  if p ∣ N + 1 then
    (((p : ℝ) / Real.sqrt p : ℝ) : ℂ) * whittakerCoeff u (N + 1) *
      baseTerm negative x y ((N + 1) / p - 1) u
  else 0

theorem sum_tailTerm_div (negative : Bool) {p : ℕ} (hp : p.Prime) (x y : ℝ) (u : ℂ) (N : ℕ) :
    ∑ b ∈ range p, eisensteinTailTerm negative ((x + b) / p) (y / p) N u =
      heckeResidueTerm negative (p := p) x y u N := by
  have hp0 : 0 < p := hp.pos
  have hsplit : ∀ b : ℕ, eisensteinTailTerm negative ((x + b) / p) (y / p) N u =
      (whittakerCoeff u (N + 1) * ((Real.sqrt (y / p) : ℂ) *
        modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * (y / p)) u)) *
        d4BMCompletedEisensteinFourierPhase negative N ((x + b) / p) := by
    intro b
    rw [eisensteinTailTerm_eq_whittaker_mul_base]
    unfold baseTerm
    ring
  simp_rw [hsplit]
  rw [← Finset.mul_sum, sum_fourierPhase_div negative hp N x]
  unfold heckeResidueTerm
  split_ifs with hdvd
  · rw [sqrt_bessel_div hp0 y hdvd u]
    unfold baseTerm
    have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
      exact_mod_cast this.ne'
    push_cast
    field_simp
  · simp

theorem sum_tsum_tailTerm_div (negative : Bool) {p : ℕ} (hp : p.Prime) (x : ℝ) {y : ℝ}
    (hy : 0 < y) (u : ℂ) :
    ∑ b ∈ range p, ∑' N : ℕ, eisensteinTailTerm negative ((x + b) / p) (y / p) N u =
      (((p : ℝ) / Real.sqrt p : ℝ) : ℂ) *
        ∑' M : ℕ, whittakerCoeff u (p * (M + 1)) * baseTerm negative x y M u := by
  have hp0 : 0 < p := hp.pos
  have hyp : 0 < y / p := by positivity
  have hswap : ∑ b ∈ range p, ∑' N : ℕ, eisensteinTailTerm negative ((x + b) / p) (y / p) N u =
      ∑' N : ℕ, ∑ b ∈ range p, eisensteinTailTerm negative ((x + b) / p) (y / p) N u :=
    (Summable.tsum_finsetSum (s := range p)
      (f := fun (b : ℕ) (N : ℕ) => eisensteinTailTerm negative ((x + (b : ℝ)) / p) (y / p) N u)
      (fun b _ => summable_eisensteinTailTerm negative ((x + b) / p) hyp u)).symm
  rw [hswap, tsum_congr (fun N => sum_tailTerm_div negative hp x y u N)]
  rw [← (heckeShift_injective hp0).tsum_eq (f := heckeResidueTerm negative (p := p) x y u)]
  · rw [← tsum_mul_left]
    refine tsum_congr fun M => ?_
    unfold heckeResidueTerm
    rw [if_pos (dvd_heckeShift_add_one hp0 M), heckeShift_add_one_div hp0, heckeShift_add_one hp0]
    simp only [Nat.add_sub_cancel]
    ring
  · intro M hM
    rw [Function.mem_support] at hM
    have hdvd : p ∣ M + 1 := by
      by_contra hnd
      apply hM
      unfold heckeResidueTerm
      rw [if_neg hnd]
    obtain ⟨N, hN⟩ := exists_heckeShift_of_dvd hdvd
    exact ⟨N, hN⟩

/-! ## The Hecke eigen-equation of the Fourier tail -/

theorem summable_heckeDivisibleTerm (negative : Bool) {p : ℕ} (hp : 0 < p) (x : ℝ) {y : ℝ}
    (hy : 0 < y) (u : ℂ) : Summable (heckeDivisibleTerm negative (p := p) x y u) := by
  have hzero : ∀ M ∉ Set.range (heckeShift p),
      heckeDivisibleTerm negative (p := p) x y u M = 0 := by
    intro M hM
    by_contra hne
    apply hM
    have hdvd : p ∣ M + 1 := by
      by_contra hnd
      apply hne
      unfold heckeDivisibleTerm
      rw [if_neg hnd]
    exact exists_heckeShift_of_dvd hdvd
  rw [← (heckeShift_injective hp).summable_iff hzero]
  have hpy : 0 < p * y := by positivity
  have hs := (summable_eisensteinTailTerm negative (p * x) hpy u).mul_left
    ((((Real.sqrt p)⁻¹ : ℝ) : ℂ))
  refine hs.congr fun N => ?_
  simp only [Function.comp]
  rw [eisensteinTailTerm_eq_whittaker_mul_base, baseTerm_scale negative hp x y N u]
  unfold heckeDivisibleTerm
  rw [if_pos (dvd_heckeShift_add_one hp N), heckeShift_add_one_div hp]
  have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
    exact_mod_cast this.ne'
  push_cast
  field_simp

theorem summable_heckeMultipleTerm (negative : Bool) {p : ℕ} (hp : p.Prime) (x : ℝ) {y : ℝ}
    (hy : 0 < y) (u : ℂ) :
    Summable (fun M : ℕ => whittakerCoeff u (p * (M + 1)) * baseTerm negative x y M u) := by
  have hp0 : 0 < p := hp.pos
  have hyp : 0 < y / p := by positivity
  have hres : Summable (heckeResidueTerm negative (p := p) x y u) := by
    have hsum : Summable (fun N : ℕ =>
        ∑ b ∈ range p, eisensteinTailTerm negative ((x + b) / p) (y / p) N u) :=
      summable_sum fun b _ => summable_eisensteinTailTerm negative ((x + b) / p) hyp u
    exact hsum.congr fun N => sum_tailTerm_div negative hp x y u N
  have hcomp := hres.comp_injective (heckeShift_injective hp0)
  have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
    exact_mod_cast this.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  refine (hcomp.mul_left (((Real.sqrt p / p : ℝ) : ℂ))).congr fun M => ?_
  simp only [Function.comp]
  unfold heckeResidueTerm
  rw [if_pos (dvd_heckeShift_add_one hp0 M), heckeShift_add_one_div hp0, heckeShift_add_one hp0]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp

/-- **Hecke eigen-equation of the signed Fourier tail.** -/
theorem heckeOp_tail (negative : Bool) {p : ℕ} (hp : p.Prime) (x : ℝ) {y : ℝ} (hy : 0 < y)
    (u : ℂ) :
    heckeOp p (fun x y => ∑' N : ℕ, eisensteinTailTerm negative x y N u) x y =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * ∑' N : ℕ, eisensteinTailTerm negative x y N u := by
  have hp0 : 0 < p := hp.pos
  unfold heckeOp
  beta_reduce
  rw [tsum_tailTerm_scale negative hp0 x y u, sum_tsum_tailTerm_div negative hp x hy u]
  have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp0)
    exact_mod_cast this.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hsqsq : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    exact Complex.ofReal_natCast p
  have hcombine : (((Real.sqrt p)⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt p : ℂ) * ∑' M : ℕ, heckeDivisibleTerm negative (p := p) x y u M +
        (((p : ℝ) / Real.sqrt p : ℝ) : ℂ) *
          ∑' M : ℕ, whittakerCoeff u (p * (M + 1)) * baseTerm negative x y M u) =
      ∑' M : ℕ, heckeDivisibleTerm negative (p := p) x y u M +
        ∑' M : ℕ, whittakerCoeff u (p * (M + 1)) * baseTerm negative x y M u := by
    push_cast
    field_simp
    linear_combination
      (-(∑' M : ℕ, whittakerCoeff u (p * (M + 1)) * baseTerm negative x y M u)) * hsqsq
  rw [hcombine, ← (summable_heckeDivisibleTerm negative hp0 x hy u).tsum_add
    (summable_heckeMultipleTerm negative hp x hy u), ← tsum_mul_left]
  refine tsum_congr fun M => ?_
  rw [eisensteinTailTerm_eq_whittaker_mul_base]
  have hrel := whittakerCoeff_hecke u hp (n := M + 1) (by omega)
  unfold heckeDivisibleTerm
  split_ifs with hdvd
  · rw [if_pos hdvd] at hrel
    linear_combination baseTerm negative x y M u * hrel
  · rw [if_neg hdvd] at hrel
    linear_combination baseTerm negative x y M u * hrel

/-! ## The Hecke eigen-equation of the constant term -/

theorem sqrt_eq_cpow_half (p : ℕ) :
    (Real.sqrt p : ℂ) = (p : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg p)]
  push_cast
  ring_nf

theorem heckeOp_cpow (p : ℕ) (c w : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeOp p (fun _ y => c * (y : ℂ) ^ w) x y =
      (((Real.sqrt p)⁻¹ : ℝ) : ℂ) * ((p : ℂ) ^ w + (p : ℂ) * ((p : ℂ) ^ w)⁻¹) *
        (c * (y : ℂ) ^ w) := by
  unfold heckeOp
  beta_reduce
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have h1 : ((p : ℂ) * (y : ℂ)) ^ w = (p : ℂ) ^ w * (y : ℂ) ^ w := by
    have := Complex.mul_cpow_ofReal_nonneg hpR hy.le w
    simpa using this
  have h2 : ((y : ℂ) / (p : ℂ)) ^ w = (y : ℂ) ^ w * ((p : ℂ) ^ w)⁻¹ := by
    have := Complex.mul_cpow_ofReal_nonneg hy.le (inv_nonneg.mpr hpR) w
    push_cast at this
    rw [div_eq_mul_inv, this]
    congr 1
    exact Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  rw [h1, h2]
  ring

theorem hecke_weyl_scalar_pos {r P : ℂ} (hr : r ≠ 0) (hP : P ≠ 0) :
    r⁻¹ * (r * P + r * r * (r * P)⁻¹) = P + P⁻¹ := by
  field_simp

theorem hecke_weyl_scalar_neg {r P : ℂ} (hr : r ≠ 0) (hP : P ≠ 0) :
    r⁻¹ * (r * P⁻¹ + r * r * (r * P⁻¹)⁻¹) = P + P⁻¹ := by
  field_simp
  ring

theorem heckeOp_constantTerm {p : ℕ} (hp : 0 < p) (u : ℂ) (epsilon : Bool) (x : ℝ) {y : ℝ}
    (hy : 0 < y) :
    heckeOp p (fun _ y => d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon y) x y =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) *
        d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon y := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsq : (Real.sqrt p : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp)
    exact_mod_cast this.ne'
  have hsqsq : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg p)]
    exact Complex.ofReal_natCast p
  have hPu : (p : ℂ) ^ u ≠ 0 := by
    intro h
    exact hpC ((Complex.cpow_eq_zero_iff _ _).mp h).1
  set w : ℂ := d4BMCompletedEisensteinCuspWeylExponent u epsilon with hw
  have hfun : (fun _ : ℝ => fun y : ℝ =>
      d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon y) =
      fun (_ : ℝ) (y : ℝ) => (d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
        d4BMCompletedEisensteinCuspConstantMaassFactor .scalar w) * (y : ℂ) ^ w := by
    funext _ y
    rfl
  have hval : d4BMCompletedEisensteinCuspConstantTerm .scalar u epsilon y =
      (d4BMCompletedEisensteinCuspConstantCoefficient u epsilon *
        d4BMCompletedEisensteinCuspConstantMaassFactor .scalar w) * (y : ℂ) ^ w := rfl
  rw [hfun, heckeOp_cpow p _ w x hy, hval]
  congr 1
  -- the scalar identity `p^{-1/2}(p^w + p·p^{-w}) = p^u + p^{-u}` for `w = 1/2 ± u`
  have hpw : (p : ℂ) ^ w = (Real.sqrt p : ℂ) * (p : ℂ) ^ ((d4BMCuspSign epsilon : ℂ) * u) := by
    rw [hw, d4BMCompletedEisensteinCuspWeylExponent, Complex.cpow_add _ _ hpC, sqrt_eq_cpow_half p]
  rw [hpw]
  cases epsilon
  · simp only [d4BMCuspSign, Bool.false_eq_true, if_false, Int.cast_neg, Int.cast_one, neg_mul,
      one_mul]
    rw [Complex.cpow_neg]
    push_cast
    generalize hPdef : (p : ℂ) ^ u = P at hPu ⊢
    rw [← hsqsq]
    exact hecke_weyl_scalar_neg hsq hPu
  · simp only [d4BMCuspSign, if_true, Int.cast_one, one_mul]
    rw [Complex.cpow_neg]
    push_cast
    generalize hPdef : (p : ℂ) ^ u = P at hPu ⊢
    rw [← hsqsq]
    exact hecke_weyl_scalar_pos hsq hPu

/-! ## The Hecke eigen-equation of the Eisenstein line model -/

/-- **Hecke eigen-equation of the completed Eisenstein line model.**  For every prime `p`,
parameter `u` and point `(x, y)` with `y > 0`,
`T_p E_u(x, y) = (p^u + p^{-u}) E_u(x, y)`. -/
theorem heckeOp_cuspLeg {p : ℕ} (hp : p.Prime) (u : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    heckeOp p (fun x y => d4BMCompletedEisensteinCuspLeg .scalar u x y) x y =
      ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * d4BMCompletedEisensteinCuspLeg .scalar u x y := by
  have hp0 : 0 < p := hp.pos
  have hfun : (fun x y : ℝ => d4BMCompletedEisensteinCuspLeg .scalar u x y) =
      fun x y : ℝ =>
        (d4BMCompletedEisensteinCuspConstantTerm .scalar u false y +
          d4BMCompletedEisensteinCuspConstantTerm .scalar u true y) +
        (2 : ℂ) * ((∑' N : ℕ, eisensteinTailTerm false x y N u) +
          ∑' N : ℕ, eisensteinTailTerm true x y N u) := by
    funext x y
    rfl
  have hval : d4BMCompletedEisensteinCuspLeg .scalar u x y =
      (d4BMCompletedEisensteinCuspConstantTerm .scalar u false y +
        d4BMCompletedEisensteinCuspConstantTerm .scalar u true y) +
      (2 : ℂ) * ((∑' N : ℕ, eisensteinTailTerm false x y N u) +
        ∑' N : ℕ, eisensteinTailTerm true x y N u) := rfl
  rw [hfun, heckeOp_add, heckeOp_add, heckeOp_const_mul, heckeOp_add,
    heckeOp_constantTerm hp0 u false x hy, heckeOp_constantTerm hp0 u true x hy,
    heckeOp_tail false hp x hy u, heckeOp_tail true hp x hy u, hval]
  ring

end

end RHTower
