import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsTheZeroAbscissa
import GaloisForLFunctions.HTGeometry.FinitePoleVerticalContourShift
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# The tangent data of Möbius and Liouville in world I

Let `A` be analytic right of a level `σ` with linear growth, and
`K(s) = e^{(s−c)²} A(s)/((s − 1) ζ(s))`. For `A(s) = s − 1` the signal of `K` is the Gaussian
window sum of the Möbius function on logarithmic scales; for `A(s) = (s − 1) ζ(2s)` that of the
Liouville function.

* **The residue against a power** (`laurentCoeff_cexp_mul_of_eq_div_pow`). At a pole
  `f = H/(s − ρ)^m`, `H` analytic, the residue of `Z^s f(s)` is
  `Z^ρ Σ_{j<m} (log Z)^j/j! · H^{(m−1−j)}(ρ)/(m−1−j)!`: a polynomial in `log Z` of degree `m − 1`
  with leading coefficient `H(ρ)/(m−1)!`.
* **The explicit formula above a level** (`signal_worldKernel_sub_eq_sum_residues`,
  `exists_norm_signal_worldKernel_le`). If the zeros of `ζ` right of `σ' < σ` are finitely many
  and none lies on `Re s = σ`, the signal of `K` is the sum of the residues of `Z^s K(s)` at the
  zeros right of `σ` plus a term `O(Z^σ)`. The line `Re s = 2` moves to `Re s = σ` across these
  finitely many poles: above the finite layer `ζ` has a subpolynomial lower bound, which the
  Gaussian absorbs.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.FloorFreeArithmetic

open HTGeometry FamilyContinuationTheory _root_.RHTower

/-! ### The residue against a power -/

theorem iteratedDeriv_cexp_affine (A L : ℂ) (i : ℕ) :
    iteratedDeriv i (fun t : ℂ => cexp (A + L * t)) = fun t => L ^ i * cexp (A + L * t) := by
  induction i with
  | zero =>
    funext t
    simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h1 : HasDerivAt (fun t : ℂ => A + L * t) L t := by
      simpa using ((hasDerivAt_id t).const_mul L).const_add A
    have h2 := (h1.cexp).const_mul (L ^ i)
    rw [h2.deriv]
    ring

theorem taylorCoeffZero_cexp_affine (A L : ℂ) (i : ℕ) :
    taylorCoeffZero (fun t : ℂ => cexp (A + L * t)) i = cexp A * L ^ i / (i.factorial : ℂ) := by
  rw [taylorCoeffZero, iteratedDeriv_cexp_affine]
  simp only [mul_zero, add_zero]
  ring

/-- Taylor coefficients of a product are the Cauchy product. -/
theorem taylorCoeffZero_mul {g h : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0)
    (n : ℕ) :
    taylorCoeffZero (fun t => g t * h t) n =
      ∑ i ∈ Finset.range (n + 1), taylorCoeffZero g i * taylorCoeffZero h (n - i) := by
  have hL := iteratedDeriv_mul (n := n) (x := (0 : ℂ)) (f := g) (g := h) hg.contDiffAt
    hh.contDiffAt
  have hd : iteratedDeriv n (fun t => g t * h t) 0 = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i g 0 * iteratedDeriv (n - i) h 0 := by
    simpa [Pi.mul_def] using hL
  rw [taylorCoeffZero, hd, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
      (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [taylorCoeffZero, taylorCoeffZero, div_mul_div_comm, div_eq_div_iff h3 (mul_ne_zero h1 h2)]
  linear_combination (iteratedDeriv i g 0 * iteratedDeriv (n - i) h 0) * hc

theorem taylorCoeffZero_comp_const_add (H : ℂ → ℂ) (ρ : ℂ) (k : ℕ) :
    taylorCoeffZero (fun t => H (ρ + t)) k = iteratedDeriv k H ρ / (k.factorial : ℂ) := by
  rw [taylorCoeffZero, _root_.iteratedDeriv_comp_const_add]
  simp only [add_zero]

/-- **The residue against an exponential at a pole of order `m`.** If `f = H/(s − ρ)^m` near `ρ`
with `H` analytic at `ρ`, the residue of `e^{Ls} f(s)` at `ρ` is
`Σ_{j<m} e^{Lρ} L^j/j! · H^{(m−1−j)}(ρ)/(m−1−j)!`. Clearing with `t^{m+1}` keeps the shift
analytic at the pole. -/
theorem laurentCoeff_cexp_mul_of_eq_div_pow {f H : ℂ → ℂ} {ρ : ℂ} {m : ℕ}
    (hH : AnalyticAt ℂ H ρ) (hf : ∀ᶠ s in 𝓝[≠] ρ, f s = H s / (s - ρ) ^ m) (L : ℂ) :
    laurentCoeff (fun s => cexp (L * s) * f s) ρ (-1) =
      ∑ j ∈ Finset.range m, cexp (L * ρ) * L ^ j / (j.factorial : ℂ) *
        (iteratedDeriv (m - 1 - j) H ρ / ((m - 1 - j).factorial : ℂ)) := by
  have hshift : laurentShift (fun s => cexp (L * s) * f s) ρ (m + 1) =ᶠ[𝓝 0]
      fun t : ℂ => t ^ 1 * (cexp (L * ρ + L * t) * H (ρ + t)) := by
    have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), f (ρ + t) = H (ρ + t) / (ρ + t - ρ) ^ m :=
      (tendsto_const_add_nhdsNE ρ).eventually hf
    have h2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → f (ρ + t) = H (ρ + t) / (ρ + t - ρ) ^ m :=
      eventually_nhdsWithin_iff.1 h1
    filter_upwards [h2] with t ht
    simp only [laurentShift]
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · rw [ht ht0, show ρ + t - ρ = t by ring, mul_add, Complex.exp_add]
      field_simp
      ring
  have hHt : AnalyticAt ℂ (fun t : ℂ => H (ρ + t)) 0 := by
    have : AnalyticAt ℂ (fun t : ℂ => ρ + t) 0 := by fun_prop
    exact (by simpa using hH : AnalyticAt ℂ H (ρ + 0)).comp this
  have hE : AnalyticAt ℂ (fun t : ℂ => cexp (L * ρ + L * t)) 0 := by fun_prop
  have hG : AnalyticAt ℂ (fun t : ℂ => cexp (L * ρ + L * t) * H (ρ + t)) 0 := hE.mul hHt
  have hana : AnalyticAt ℂ (laurentShift (fun s => cexp (L * s) * f s) ρ (m + 1)) 0 :=
    ((analyticAt_id.pow 1).mul hG).congr hshift.symm
  rw [laurentCoeff_eq_taylorCoeffZero hana (by omega)]
  have hidx : ((-1 : ℤ) + ((m + 1 : ℕ) : ℤ)).toNat = m := by omega
  rw [hidx, taylorCoeffZero, Filter.EventuallyEq.iteratedDeriv_eq m hshift, ← taylorCoeffZero,
    taylorCoeffZero_pow_mul hG]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [if_pos (show 1 ≤ m by omega), taylorCoeffZero_mul hE hHt, Nat.sub_add_cancel hm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [taylorCoeffZero_cexp_affine, taylorCoeffZero_comp_const_add]

/-! ### The signal as a line integral -/

/-- The signal on the line `Re s = c` is `(1/2π) ∫ Z^{c+it} G(c+it) dt`. -/
theorem signal_eq_integral (G : ℂ → ℂ) (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal G c Z = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, cexp ((Real.log Z : ℂ) * ((c : ℂ) + t * I)) * G ((c : ℂ) + t * I) := by
  have hZ0 : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have hlog : Complex.log (Z : ℂ) = (Real.log Z : ℂ) := (Complex.ofReal_log hZ.le).symm
  have hpt : ∀ y : ℝ, (Z : ℂ) ^ (-(((-c : ℝ) : ℂ) + y * I)) • G (-(((-c : ℝ) : ℂ) + y * I)) =
      (fun t : ℝ => cexp ((Real.log Z : ℂ) * ((c : ℂ) + t * I)) * G ((c : ℂ) + t * I)) (-y) := by
    intro y
    have e : -(((-c : ℝ) : ℂ) + y * I) = (c : ℂ) + ((-y : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e, smul_eq_mul, Complex.cpow_def_of_ne_zero hZ0, hlog]
  unfold signal
  rw [mellinInv, integral_congr_ae (Eventually.of_forall hpt),
    integral_neg_eq_self (fun t : ℝ => cexp ((Real.log Z : ℂ) * ((c : ℂ) + t * I)) *
      G ((c : ℂ) + t * I)), Complex.real_smul]
  push_cast
  ring

/-! ### The kernel and the finite layer -/

/-- The kernel `e^{(s−c)²} A(s)/((s − 1) ζ(s))`. -/
def worldKernel (c : ℝ) (A : ℂ → ℂ) (s : ℂ) : ℂ := cexp ((s - c) ^ 2) * A s / zetaEntire s

/-- The Gaussian absorbs a quadratic factor: `e^{−t²}(2 + |t|)² ≤ 16/(1 + t²)`. -/
theorem exp_neg_sq_mul_sq_le (t : ℝ) : Real.exp (-t ^ 2) * (2 + |t|) ^ 2 ≤ 16 / (1 + t ^ 2) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hE := Real.quadratic_le_exp_of_nonneg (sq_nonneg t)
  have h1 : (2 + |t|) ^ 2 ≤ 8 * (1 + t ^ 2) := by
    have : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, sq_nonneg (|t| - 2)]
  have h2 : (1 + t ^ 2) ^ 2 ≤ 2 * Real.exp (t ^ 2) := by nlinarith [sq_nonneg t]
  rw [le_div_iff₀ hpos, Real.exp_neg]
  have hexp : 0 < Real.exp (t ^ 2) := Real.exp_pos _
  rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ hexp]
  nlinarith [mul_le_mul_of_nonneg_right h1 hpos.le]

section Layer

variable {σ' σ : ℝ} (hσ' : 1 / 2 ≤ σ') (hσ'σ : σ' < σ) (hσ1 : σ < 1)
  (hfin : {z : ℂ | riemannZeta z = 0 ∧ σ' < z.re}.Finite)
  (hline : ∀ z : ℂ, riemannZeta z = 0 → z.re ≠ σ)

/-- The zeros right of the level `σ`. -/
def layerZeros (hfin : {z : ℂ | riemannZeta z = 0 ∧ σ' < z.re}.Finite) (σ : ℝ) : Finset ℂ :=
  hfin.toFinset.filter fun z => σ < z.re

include hσ'σ in
theorem mem_layerZeros {z : ℂ} : z ∈ layerZeros hfin σ ↔ riemannZeta z = 0 ∧ σ < z.re := by
  rw [layerZeros, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨h0, -⟩, h⟩
    exact ⟨h0, h⟩
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, hσ'σ.trans h⟩, h⟩

include hσ'σ hline in
/-- Right of `σ`, `(s − 1) ζ(s)` vanishes only at the finite layer. -/
theorem zetaEntire_ne_zero_of_not_mem {s : ℂ} (hs : σ ≤ s.re) (hP : s ∉ layerZeros hfin σ) :
    zetaEntire s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | h1
  · rw [zetaEntire_eval_one]
    exact one_ne_zero
  · rw [zetaEntire_eq h1]
    refine mul_ne_zero (sub_ne_zero.mpr h1) fun h0 => hP ?_
    exact (mem_layerZeros hσ'σ hfin).mpr
      ⟨h0, lt_of_le_of_ne hs (Ne.symm (hline s h0))⟩

include hσ' hσ'σ hσ1 hfin in
/-- **Above the finite layer.** `(s − 1) ζ(s)` is at least `κ/(2 + |t|)` on `Re s ≥ σ`,
`|t| ≥ T₁`. -/
theorem exists_zetaEntire_lower_bound :
    ∃ κ T₁ : ℝ, 0 < κ ∧ 6 ≤ T₁ ∧ ∀ s : ℂ, σ ≤ s.re → T₁ ≤ |s.im| →
      κ / (2 + |s.im|) ≤ ‖zetaEntire s‖ := by
  obtain ⟨B, hB⟩ := (hfin.image fun z => |z.im|).bddAbove
  have hzf : ∀ z : ℂ, σ' < z.re → B + 1 ≤ |z.im| → riemannZeta z ≠ 0 := by
    intro z hz hzim h0
    have := hB ⟨z, ⟨h0, hz⟩, rfl⟩
    linarith
  obtain ⟨κ, hκ, hlow⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree_above
    (T₀ := B + 1) hσ' (by linarith) hzf (δ := σ - σ') (by linarith) (by linarith) one_pos
  refine ⟨κ, max 6 (B + 1 + 4), hκ, le_max_left _ _, fun s hs hst => ?_⟩
  have h6 : 6 ≤ |s.im| := (le_max_left _ _).trans hst
  have hT : B + 1 + 4 ≤ |s.im| := (le_max_right _ _).trans hst
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at h6
  have hζ := hlow s (by linarith) h6 hT
  rw [Real.rpow_neg_one] at hζ
  have hnorm : (1 : ℝ) ≤ ‖s - 1‖ := by
    have him : |s.im| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rwa [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  rw [zetaEntire_eq hs1, norm_mul]
  calc κ / (2 + |s.im|) = κ * (2 + |s.im|)⁻¹ := div_eq_mul_inv _ _
    _ ≤ ‖riemannZeta s‖ := hζ
    _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := le_mul_of_one_le_left (norm_nonneg _) hnorm

end Layer

/-! ### Moving the line across the finite layer -/

/-- `Z^x ≤ Z^σ + Z²` for `σ ≤ x ≤ 2`. -/
theorem rpow_le_add_of_mem {Z σ x : ℝ} (hZ : 0 < Z) (hσx : σ ≤ x) (hx2 : x ≤ 2) :
    Z ^ x ≤ Z ^ σ + Z ^ (2 : ℝ) := by
  have h1 := Real.rpow_nonneg hZ.le σ
  have h2 := Real.rpow_nonneg hZ.le (2 : ℝ)
  rcases le_total 1 Z with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hx2
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hZ h hσx
    linarith

/-- `‖e^{(s−c)²}‖ ≤ e^{(|c|+2)²} e^{−t²}` on `0 ≤ Re s ≤ 2`. -/
theorem norm_cexp_sq_le {s : ℂ} (c : ℝ) (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((|c| + 2) ^ 2) * Real.exp (-s.im ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((s - c) ^ 2).re = (s.re - c) ^ 2 - s.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [hre]
  have : (s.re - c) ^ 2 ≤ (|c| + 2) ^ 2 := by
    have h : |s.re - c| ≤ |c| + 2 := by
      calc |s.re - c| ≤ |s.re| + |c| := abs_sub _ _
        _ ≤ 2 + |c| := by rw [abs_of_nonneg h0]; linarith
        _ = |c| + 2 := by ring
    nlinarith [abs_nonneg (s.re - c), sq_abs (s.re - c)]
  linarith

theorem norm_cexp_log_mul {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ‖cexp ((Real.log Z : ℂ) * s)‖ = Z ^ s.re := by
  rw [Complex.norm_exp, Real.rpow_def_of_pos hZ]
  congr 1
  simp [Complex.mul_re]

section Shift

variable {σ' σ : ℝ} (hσ' : 1 / 2 ≤ σ') (hσ'σ : σ' < σ) (hσ1 : σ < 1)
  (hfin : {z : ℂ | riemannZeta z = 0 ∧ σ' < z.re}.Finite)
  (hline : ∀ z : ℂ, riemannZeta z = 0 → z.re ≠ σ)
  {A : ℂ → ℂ} (hA : ∀ s : ℂ, σ ≤ s.re → AnalyticAt ℂ A s)
  {M : ℝ} (hM : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → ‖A s‖ ≤ M * (2 + |s.im|))
include hσ' hσ'σ hσ1 hfin hline

omit hline in
/-- On a line `Re s = x` without zeros, `|(s − 1) ζ(s)|⁻¹ ≤ D (2 + |t|)`. -/
theorem exists_inv_zetaEntire_line_le {x : ℝ} (hx : σ ≤ x)
    (hnz : ∀ t : ℝ, zetaEntire ((x : ℂ) + t * I) ≠ 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖(zetaEntire ((x : ℂ) + t * I))⁻¹‖ ≤ D * (2 + |t|) := by
  obtain ⟨κ, T₁, hκ, hT₁, hlow⟩ := exists_zetaEntire_lower_bound hσ' hσ'σ hσ1 hfin
  have hcont : Continuous fun t : ℝ => ‖zetaEntire ((x : ℂ) + t * I)‖ :=
    (differentiable_zetaEntire.continuous.comp (by fun_prop)).norm
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := -T₁) (b := T₁)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith)) hcont.continuousOn
  have hm₀ : 0 < ‖zetaEntire ((x : ℂ) + t₀ * I)‖ := norm_pos_iff.mpr (hnz t₀)
  refine ⟨κ⁻¹ + ‖zetaEntire ((x : ℂ) + t₀ * I)‖⁻¹, by positivity, fun t => ?_⟩
  have h2t : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  rw [norm_inv]
  rcases le_or_gt T₁ |t| with ht | ht
  · have hs : σ ≤ ((x : ℂ) + t * I).re := by simpa using hx
    have h := hlow _ hs (by simpa using ht)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h
    have hpos : 0 < κ / (2 + |t|) := by positivity
    calc ‖zetaEntire ((x : ℂ) + t * I)‖⁻¹ ≤ (κ / (2 + |t|))⁻¹ := inv_anti₀ hpos h
      _ = κ⁻¹ * (2 + |t|) := by field_simp
      _ ≤ (κ⁻¹ + ‖zetaEntire ((x : ℂ) + t₀ * I)‖⁻¹) * (2 + |t|) := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)
  · have hmem : t ∈ Set.Icc (-T₁) T₁ := abs_le.mp ht.le
    have h := isMinOn_iff.mp hmin t hmem
    calc ‖zetaEntire ((x : ℂ) + t * I)‖⁻¹ ≤ ‖zetaEntire ((x : ℂ) + t₀ * I)‖⁻¹ :=
          inv_anti₀ hm₀ h
      _ ≤ κ⁻¹ + ‖zetaEntire ((x : ℂ) + t₀ * I)‖⁻¹ := le_add_of_nonneg_left (by positivity)
      _ ≤ (κ⁻¹ + ‖zetaEntire ((x : ℂ) + t₀ * I)‖⁻¹) * (2 + |t|) :=
          le_mul_of_one_le_right (by positivity) h2t

omit hσ' hσ1 in
include hA in
/-- Off the finite layer the integrand is analytic on `Re s ≥ σ`. -/
theorem analyticAt_worldIntegrand (c : ℝ) (L : ℂ) {s : ℂ} (hs : σ ≤ s.re)
    (hP : s ∉ layerZeros hfin σ) :
    AnalyticAt ℂ (fun s => cexp (L * s) * worldKernel c A s) s := by
  have hne := zetaEntire_ne_zero_of_not_mem hσ'σ hfin hline hs hP
  have hz : AnalyticAt ℂ zetaEntire s := differentiable_zetaEntire.analyticAt s
  have hnum : AnalyticAt ℂ (fun s => cexp ((s - c) ^ 2) * A s) s :=
    (by fun_prop : AnalyticAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s).mul (hA s hs)
  exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => cexp (L * s)) s).mul (hnum.div hz hne)

omit hline in
include hM in
/-- The integrand on a zero-free line `Re s = x`, `σ ≤ x ≤ 2`, is integrable with a bound
`C Z^x/(1 + t²)`. -/
theorem exists_worldIntegrand_line_bound (c : ℝ) {x : ℝ} (hx : σ ≤ x)
    (hx2 : x ≤ 2) (hnz : ∀ t : ℝ, zetaEntire ((x : ℂ) + t * I) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z : ℝ, 0 < Z → ∀ t : ℝ, ‖cexp ((Real.log Z : ℂ) * ((x : ℂ) + t * I)) *
      worldKernel c A ((x : ℂ) + t * I)‖ ≤ C * Z ^ x / (1 + t ^ 2) := by
  obtain ⟨D, hD, hDb⟩ := exists_inv_zetaEntire_line_le hσ' hσ'σ hσ1 hfin hx hnz
  have hM0 : 0 ≤ M := by
    have h := hM ((x : ℂ) + 0 * I) (by simpa using hx) (by simpa using hx2)
    have h2 : |((x : ℂ) + 0 * I).im| = 0 := by simp
    rw [h2] at h
    linarith [norm_nonneg (A ((x : ℂ) + 0 * I))]
  refine ⟨16 * Real.exp ((|c| + 2) ^ 2) * M * D, by positivity, fun Z hZ t => ?_⟩
  set s : ℂ := (x : ℂ) + t * I
  have hre : s.re = x := by simp [s]
  have him : s.im = t := by simp [s]
  have hσ0 : (0 : ℝ) ≤ x := by linarith
  have hE := norm_cexp_sq_le c (by rw [hre]; exact hσ0) (by rw [hre]; exact hx2)
  have hAs := hM s (by rw [hre]; exact hx) (by rw [hre]; exact hx2)
  have hZs := norm_cexp_log_mul hZ s
  rw [hre] at hZs
  rw [him] at hE hAs
  have hinv := hDb t
  have hG := exp_neg_sq_mul_sq_le t
  have heq : ‖cexp ((Real.log Z : ℂ) * s) * worldKernel c A s‖ =
      Z ^ x * (‖cexp ((s - c) ^ 2)‖ * ‖A s‖ * ‖(zetaEntire s)⁻¹‖) := by
    rw [worldKernel, norm_mul, hZs, div_eq_mul_inv, norm_mul, norm_mul]
  rw [heq]
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hZx : 0 ≤ Z ^ x := Real.rpow_nonneg hZ.le x
  calc Z ^ x * (‖cexp ((s - c) ^ 2)‖ * ‖A s‖ * ‖(zetaEntire s)⁻¹‖)
      ≤ Z ^ x * (Real.exp ((|c| + 2) ^ 2) * Real.exp (-t ^ 2) * (M * (2 + |t|)) *
          (D * (2 + |t|))) := by
        gcongr
    _ = Z ^ x * (Real.exp ((|c| + 2) ^ 2) * M * D) * (Real.exp (-t ^ 2) * (2 + |t|) ^ 2) := by
        ring
    _ ≤ Z ^ x * (Real.exp ((|c| + 2) ^ 2) * M * D) * (16 / (1 + t ^ 2)) := by
        gcongr
    _ = 16 * Real.exp ((|c| + 2) ^ 2) * M * D * Z ^ x / (1 + t ^ 2) := by ring

include hA hM in
theorem integrable_worldIntegrand_line (c : ℝ) {Z : ℝ} (hZ : 0 < Z) {x : ℝ} (hx : σ ≤ x)
    (hx2 : x ≤ 2) (hnz : ∀ t : ℝ, zetaEntire ((x : ℂ) + t * I) ≠ 0) :
    Integrable fun t : ℝ => cexp ((Real.log Z : ℂ) * ((x : ℂ) + t * I)) *
      worldKernel c A ((x : ℂ) + t * I) := by
  obtain ⟨C, hC, hb⟩ := exists_worldIntegrand_line_bound hσ' hσ'σ hσ1 hfin hM c hx
    hx2 hnz
  have hcont : Continuous fun t : ℝ => cexp ((Real.log Z : ℂ) * ((x : ℂ) + t * I)) *
      worldKernel c A ((x : ℂ) + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hsx : σ ≤ ((x : ℂ) + t * I).re := by simpa using hx
    have hP : ((x : ℂ) + t * I) ∉ layerZeros hfin σ := by
      intro hmem
      exact hnz t (by
        have h0 := ((mem_layerZeros hσ'σ hfin).mp hmem).1
        have hs1 : ((x : ℂ) + t * I) ≠ 1 := by
          intro h
          rw [h] at h0
          exact riemannZeta_one_ne_zero h0
        rw [zetaEntire_eq hs1, h0, mul_zero])
    exact ContinuousAt.comp (g := fun s => cexp ((Real.log Z : ℂ) * s) * worldKernel c A s)
      (f := fun t : ℝ => (x : ℂ) + t * I)
      (analyticAt_worldIntegrand hσ'σ hfin hline hA c (Real.log Z : ℂ) hsx hP).continuousAt
      (by fun_prop)
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * Z ^ x))) hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  exact (hb Z hZ t).trans_eq (by rw [div_eq_mul_inv])

omit hσ' hσ1 hA hM in
/-- The line `Re s = σ` carries no zero. -/
theorem zetaEntire_ne_zero_line_sigma (t : ℝ) : zetaEntire ((σ : ℂ) + t * I) ≠ 0 := by
  refine zetaEntire_ne_zero_of_not_mem hσ'σ hfin hline (by simp) fun hmem => ?_
  have h := ((mem_layerZeros hσ'σ hfin).mp hmem).2
  simp at h

include hA hM in
/-- **The explicit formula above the level `σ`.** The signal on `Re s = 2` minus the signal on
`Re s = σ` is the sum of the residues of `Z^s K(s)` at the zeros right of `σ`. -/
theorem signal_worldKernel_sub_eq_sum_residues (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (worldKernel c A) 2 Z - signal (worldKernel c A) σ Z =
      ∑ p ∈ layerZeros hfin σ,
        laurentCoeff (fun s => cexp ((Real.log Z : ℂ) * s) * worldKernel c A s) p (-1) := by
  set L : ℂ := (Real.log Z : ℂ)
  set f : ℂ → ℂ := fun s => cexp (L * s) * worldKernel c A s with hf
  obtain ⟨κ, T₁, hκ, hT₁, hlow⟩ := exists_zetaEntire_lower_bound hσ' hσ'σ hσ1 hfin
  have hM0 : 0 ≤ M := by
    have h := hM ((σ : ℂ) + 0 * I) (by simp) (by simp; linarith)
    have h2 : |((σ : ℂ) + 0 * I).im| = 0 := by simp
    rw [h2] at h
    linarith [norm_nonneg (A ((σ : ℂ) + 0 * I))]
  set B₀ : ℝ := (Z ^ σ + Z ^ (2 : ℝ)) * Real.exp ((|c| + 2) ^ 2) * M / κ
  have hB₀ : 0 ≤ B₀ := by positivity
  -- the integrand above the finite layer
  have hstrip : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → T₁ ≤ |s.im| →
      ‖f s‖ ≤ B₀ * (16 / (1 + s.im ^ 2)) := by
    intro s hs hs2 hst
    have hE := norm_cexp_sq_le c (by linarith) hs2
    have hAs := hM s hs hs2
    have hZs := norm_cexp_log_mul hZ s
    have hz := hlow s hs hst
    have hzpos : 0 < ‖zetaEntire s‖ := lt_of_lt_of_le (by positivity) hz
    have hinv : ‖zetaEntire s‖⁻¹ ≤ (2 + |s.im|) / κ := by
      rw [inv_le_comm₀ hzpos (by positivity), inv_div]
      exact hz
    have hZx := rpow_le_add_of_mem hZ hs hs2
    have hG := exp_neg_sq_mul_sq_le s.im
    have hfs : ‖f s‖ = Z ^ s.re * (‖cexp ((s - c) ^ 2)‖ * ‖A s‖ * ‖zetaEntire s‖⁻¹) := by
      simp only [hf, worldKernel]
      rw [norm_mul, hZs, div_eq_mul_inv, norm_mul, norm_mul, norm_inv]
    rw [hfs]
    calc Z ^ s.re * (‖cexp ((s - c) ^ 2)‖ * ‖A s‖ * ‖zetaEntire s‖⁻¹)
        ≤ (Z ^ σ + Z ^ (2 : ℝ)) * (Real.exp ((|c| + 2) ^ 2) * Real.exp (-s.im ^ 2) *
            (M * (2 + |s.im|)) * ((2 + |s.im|) / κ)) := by
          gcongr
      _ = B₀ * (Real.exp (-s.im ^ 2) * (2 + |s.im|) ^ 2) := by
          simp only [B₀]
          field_simp
      _ ≤ B₀ * (16 / (1 + s.im ^ 2)) := by gcongr
  -- the horizontal sides vanish along `T₁ + n`
  have hhor : ∀ y : ℝ, T₁ ≤ |y| →
      ‖HIntegral f σ 2 y‖ ≤ B₀ * (16 / (1 + y ^ 2)) * |2 - σ| := by
    intro y hy
    unfold HIntegral
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le (by linarith)] at hx
    have h := hstrip ((x : ℂ) + y * I) (by simp; linarith [hx.1]) (by simp; exact hx.2)
      (by simpa using hy)
    simpa using h
  have hdecay : Tendsto (fun y : ℝ => B₀ * (16 / (1 + y ^ 2)) * |2 - σ|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    have h2 := (h1.inv_tendsto_atTop).const_mul (B₀ * 16)
    rw [mul_zero] at h2
    have h3 := h2.mul_const |2 - σ|
    rw [zero_mul] at h3
    exact h3.congr fun y => by simp only [Pi.inv_apply]; ring
  have hT : Tendsto (fun n : ℕ => T₁ + n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have htop : Tendsto (fun n : ℕ => HIntegral f σ 2 (T₁ + n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun n => hhor _ ?_) (hdecay.comp hT)
    rw [abs_of_nonneg (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbot : Tendsto (fun n : ℕ => HIntegral f σ 2 (-(T₁ + n))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun n => ?_) (hdecay.comp hT)
    have h := hhor (-(T₁ + n)) (by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    rw [neg_sq] at h
    exact h
  have hshift := verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq
    (f := f) (a := σ) (c := (2 : ℝ)) (by linarith) (P := layerZeros hfin σ)
    (fun p hp => by
      obtain ⟨h0, hre⟩ := (mem_layerZeros hσ'σ hfin).mp hp
      have h1 : p.re < 1 := by
        by_contra hge
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) h0
      exact ⟨hre, by linarith⟩)
    (fun p hp => by
      have hre := ((mem_layerZeros hσ'σ hfin).mp hp).2
      have hnum : AnalyticAt ℂ (fun s => cexp (L * s) * (cexp ((s - c) ^ 2) * A s)) p :=
        (by fun_prop : AnalyticAt ℂ (fun s : ℂ => cexp (L * s)) p).mul
          ((by fun_prop : AnalyticAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) p).mul (hA p hre.le))
      have hfeq : f = fun s => cexp (L * s) * (cexp ((s - c) ^ 2) * A s) / zetaEntire s := by
        funext s
        simp only [hf, worldKernel]
        ring
      rw [hfeq]
      exact hnum.meromorphicAt.div (differentiable_zetaEntire.analyticAt p).meromorphicAt)
    (fun s hs _ hP => analyticAt_worldIntegrand hσ'σ hfin hline hA c L hs hP)
    (integrable_worldIntegrand_line hσ' hσ'σ hσ1 hfin hline hA hM c hZ le_rfl (by linarith)
      (zetaEntire_ne_zero_line_sigma hσ'σ hfin hline))
    (integrable_worldIntegrand_line hσ' hσ'σ hσ1 hfin hline hA hM c hZ (by linarith) le_rfl
      fun t => zetaEntire_ne_zero_of_one_lt_re (by simp))
    hT htop hbot
  rw [signal_eq_integral _ 2 hZ, signal_eq_integral _ σ hZ, ← mul_sub]
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hcast : (fun t : ℝ => cexp ((Real.log Z : ℂ) * (((2 : ℝ) : ℂ) + t * I)) *
      worldKernel c A (((2 : ℝ) : ℂ) + t * I)) = fun t : ℝ => f (((2 : ℝ) : ℂ) + t * I) := rfl
  change (1 / (2 * Real.pi) : ℂ) * ((∫ t : ℝ, f (((2 : ℝ) : ℂ) + t * I)) -
    ∫ t : ℝ, f ((σ : ℂ) + t * I)) = _
  rw [hshift]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

include hM in
/-- The signal on the line `Re s = σ` is `O(Z^σ)`. -/
theorem exists_norm_signal_worldKernel_le (c : ℝ) :
    ∃ C : ℝ, ∀ Z : ℝ, 0 < Z → ‖signal (worldKernel c A) σ Z‖ ≤ C * Z ^ σ := by
  obtain ⟨C, hC, hb⟩ := exists_worldIntegrand_line_bound hσ' hσ'σ hσ1 hfin hM c le_rfl
    (by linarith) (zetaEntire_ne_zero_line_sigma hσ'σ hfin hline)
  refine ⟨C / 2, fun Z hZ => ?_⟩
  rw [signal_eq_integral _ σ hZ, norm_mul]
  have hint : Integrable fun t : ℝ => C * Z ^ σ * (1 + t ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le hint (Eventually.of_forall fun t => by
    rw [← div_eq_mul_inv]
    exact hb Z hZ t)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at h
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn]
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, cexp ((Real.log Z : ℂ) * ((σ : ℂ) + t * I)) *
        worldKernel c A ((σ : ℂ) + t * I)‖ ≤ 1 / (2 * Real.pi) * (C * Z ^ σ * Real.pi) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C / 2 * Z ^ σ := by field_simp

end Shift

/-! ### The tangent datum at a zero -/

/-- `(s − 1) ζ(s)` has a zero of finite order `m ≥ 1` at every zero `p ≠ 1` of `ζ`. -/
theorem exists_zetaEntire_factor {p : ℂ} (hp : riemannZeta p = 0) (hp1 : p ≠ 1) :
    ∃ (m : ℕ) (g : ℂ → ℂ), 1 ≤ m ∧ AnalyticAt ℂ g p ∧ g p ≠ 0 ∧
      ∀ᶠ z in 𝓝 p, zetaEntire z = (z - p) ^ m * g z := by
  have hzA : AnalyticOnNhd ℂ zetaEntire Set.univ := fun z _ =>
    differentiable_zetaEntire.analyticAt z
  have h1 : analyticOrderAt zetaEntire 1 ≠ ⊤ := by
    rw [(hzA 1 trivial).analyticOrderAt_eq_zero.mpr (by rw [zetaEntire_eval_one]; exact one_ne_zero)]
    exact ENat.zero_ne_top
  have hp' := hzA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial h1
    (y := p)
  obtain ⟨g, hg, hgp, heq⟩ := ((hzA p trivial).analyticOrderAt_ne_top).mp hp'
  refine ⟨analyticOrderNatAt zetaEntire p, g, ?_, hg, hgp, heq.mono fun z hz => by
    simpa [smul_eq_mul] using hz⟩
  by_contra h0
  have hm : analyticOrderNatAt zetaEntire p = 0 := by omega
  have hself : zetaEntire p = (p - p) ^ analyticOrderNatAt zetaEntire p • g p := heq.self_of_nhds
  rw [hm, pow_zero, one_smul, zetaEntire_eq hp1, hp, mul_zero] at hself
  exact hgp hself.symm

/-- **The residue at a zero of the layer.** With `(s − 1)ζ(s) = (s − p)^m g(s)` near `p` and
`H = e^{(s−c)²}A/g`, the residue of `Z^s K(s)` at `p` is
`Σ_{j<m} Z^p (log Z)^j/j! · H^{(m−1−j)}(p)/(m−1−j)!`. -/
theorem laurentCoeff_worldKernel_eq (c : ℝ) {A g : ℂ → ℂ} {p : ℂ} {m : ℕ}
    (hA : AnalyticAt ℂ A p) (hg : AnalyticAt ℂ g p) (hgp : g p ≠ 0)
    (heq : ∀ᶠ z in 𝓝 p, zetaEntire z = (z - p) ^ m * g z) (L : ℂ) :
    laurentCoeff (fun s => cexp (L * s) * worldKernel c A s) p (-1) =
      ∑ j ∈ Finset.range m, cexp (L * p) * L ^ j / (j.factorial : ℂ) *
        (iteratedDeriv (m - 1 - j) (fun s => cexp ((s - c) ^ 2) * A s / g s) p /
          ((m - 1 - j).factorial : ℂ)) := by
  have hH : AnalyticAt ℂ (fun s => cexp ((s - c) ^ 2) * A s / g s) p :=
    ((by fun_prop : AnalyticAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) p).mul hA).div hg hgp
  refine laurentCoeff_cexp_mul_of_eq_div_pow hH ?_ L
  have hgne : ∀ᶠ z in 𝓝 p, g z ≠ 0 := hg.continuousAt.eventually_ne hgp
  have h : ∀ᶠ z in 𝓝[≠] p, zetaEntire z = (z - p) ^ m * g z ∧ g z ≠ 0 :=
    nhdsWithin_le_nhds (heq.and hgne)
  filter_upwards [h, self_mem_nhdsWithin] with z ⟨hz, hgz⟩ hzp
  have hzp' : (z - p) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzp)
  rw [worldKernel, hz]
  field_simp

/-! ### World I -/

/-- **World I has a finite layer above a zero-free line.** If `Θ∞ < Θ`, there are levels
`½ ≤ σ' < σ < Θ` with finitely many zeros right of `σ'` and none on `Re s = σ`. -/
theorem exists_layer_of_worldOne
    (hI : ZeroConfigurationGeometry.zetaAsymptoticAbscissa < zetaZeroAbscissa) :
    ∃ σ' σ : ℝ, 1 / 2 ≤ σ' ∧ σ' < σ ∧ σ < zetaZeroAbscissa ∧ σ < 1 ∧
      {z : ℂ | riemannZeta z = 0 ∧ σ' < z.re}.Finite ∧
      ∀ z : ℂ, riemannZeta z = 0 → z.re ≠ σ := by
  obtain ⟨x, ⟨hx, hfinC⟩, hxΘ⟩ :=
    exists_lt_of_csInf_lt ZeroConfigurationGeometry.zetaAsymptoticAbscissaSet_nonempty hI
  have hfin : {z : ℂ | riemannZeta z = 0 ∧ x < z.re}.Finite := by
    refine (hfinC.image fun q => ((q.1 : ℂ))).subset fun z hz => ?_
    obtain ⟨h0, hre⟩ := hz
    have hpos : 0 < z.re := by linarith
    have h1 : z.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) h0
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip h0 hpos h1
    exact ⟨q, by simpa [Set.mem_setOf_eq, hq] using hre, hq⟩
  have hR : (Complex.re '' {z : ℂ | riemannZeta z = 0 ∧ x < z.re}).Finite := hfin.image _
  obtain ⟨σ, hσmem, hσR⟩ := ((Set.Ioo_infinite hxΘ).sdiff hR).nonempty
  refine ⟨x, σ, hx, hσmem.1, hσmem.2, lt_of_lt_of_le hσmem.2 zetaZeroAbscissa_le_one, hfin,
    fun z h0 hre => hσR ⟨z, ⟨h0, ?_⟩, hre⟩⟩
  rw [hre]
  exact hσmem.1

/-- `u^j e^{−au} → 0` for `a > 0`. -/
theorem tendsto_pow_mul_exp_neg_mul (j : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u : ℝ => u ^ j * Real.exp (-(a * u))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
    (tendsto_id.const_mul_atTop ha)
  have h' := h.const_mul (a ^ j)⁻¹
  rw [mul_zero] at h'
  refine h'.congr fun u => ?_
  simp only [Function.comp_apply, id]
  rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j ha.ne'), one_mul]

/-- A residue term below the top decays after normalization. -/
theorem tendsto_normalized_residue_term {Θ : ℝ} {p : ℂ} (hp : p.re < Θ) (j : ℕ) (k : ℂ) :
    Tendsto (fun u : ℝ => (Real.exp (-Θ * u) : ℂ) *
      (cexp ((u : ℂ) * p) * (u : ℂ) ^ j / (j.factorial : ℂ) * k)) atTop (𝓝 0) := by
  have hT := (tendsto_pow_mul_exp_neg_mul j (sub_pos.mpr hp)).mul_const (‖k‖ / j.factorial)
  rw [zero_mul] at hT
  refine squeeze_zero_norm' ?_ hT
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [norm_mul, norm_mul, norm_div, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu, Complex.norm_natCast]
  have hre : ((u : ℂ) * p).re = u * p.re := by simp
  rw [hre]
  have he : Real.exp (-Θ * u) * Real.exp (u * p.re) = Real.exp (-((Θ - p.re) * u)) := by
    rw [← Real.exp_add]
    ring_nf
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  apply le_of_eq
  field_simp
  rw [show Real.exp (-(u * (Θ - p.re))) = Real.exp (-(Θ * u)) * Real.exp (u * p.re) by
    rw [← Real.exp_add]; ring_nf]
  ring

/-- **The tangent datum in world I.** If `Θ∞ < Θ`, the signal of `K` at `e^u`, normalized by
`e^{−Θu}`, minus the residues at the zeros on the top line `Re s = Θ`, tends to zero. The top
residues are `e^{ρu}` times polynomials in `u` of degree the multiplicity minus one. -/
theorem tendsto_normalized_signal_sub_top
    (hI : ZeroConfigurationGeometry.zetaAsymptoticAbscissa < zetaZeroAbscissa) (c : ℝ)
    {A : ℂ → ℂ} (hA : ∀ s : ℂ, 1 / 2 < s.re → AnalyticAt ℂ A s)
    (hM : ∀ σ : ℝ, 1 / 2 < σ → ∃ M : ℝ, ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 →
      ‖A s‖ ≤ M * (2 + |s.im|)) :
    ∃ T : Finset ℂ, (∀ p : ℂ, p ∈ T ↔ riemannZeta p = 0 ∧ p.re = zetaZeroAbscissa) ∧
      Tendsto (fun u : ℝ => (Real.exp (-zetaZeroAbscissa * u) : ℂ) *
        (signal (worldKernel c A) 2 (Real.exp u) -
          ∑ p ∈ T, laurentCoeff (fun s => cexp ((u : ℂ) * s) * worldKernel c A s) p (-1)))
        atTop (𝓝 0) := by
  obtain ⟨σ', σ, hσ', hσ'σ, hσΘ, hσ1, hfin, hline⟩ := exists_layer_of_worldOne hI
  have hσh : 1 / 2 < σ := by linarith
  obtain ⟨M, hMb⟩ := hM σ hσh
  have hAσ : ∀ s : ℂ, σ ≤ s.re → AnalyticAt ℂ A s := fun s hs => hA s (by linarith)
  set P := layerZeros hfin σ
  set Θ := zetaZeroAbscissa
  set T := P.filter fun p => p.re = Θ
  refine ⟨T, fun p => ?_, ?_⟩
  · simp only [T, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hre⟩
      exact ⟨((mem_layerZeros hσ'σ hfin).mp hp).1, hre⟩
    · rintro ⟨h0, hre⟩
      exact ⟨(mem_layerZeros hσ'σ hfin).mpr ⟨h0, by rw [hre]; exact hσΘ⟩, hre⟩
  obtain ⟨C, hC⟩ := exists_norm_signal_worldKernel_le hσ' hσ'σ hσ1 hfin hline hMb c
  -- the residues at the zeros below the top
  have hlow : ∀ p ∈ P.filter (fun p => ¬ p.re = Θ),
      Tendsto (fun u : ℝ => (Real.exp (-Θ * u) : ℂ) *
        laurentCoeff (fun s => cexp ((u : ℂ) * s) * worldKernel c A s) p (-1)) atTop (𝓝 0) := by
    intro p hp
    obtain ⟨hpP, hpΘ⟩ := Finset.mem_filter.mp hp
    obtain ⟨h0, hre⟩ := (mem_layerZeros hσ'σ hfin).mp hpP
    have hp1 : p ≠ 1 := by
      rintro rfl
      exact riemannZeta_one_ne_zero h0
    have hlt : p.re < Θ := lt_of_le_of_ne (re_le_zetaZeroAbscissa h0) hpΘ
    obtain ⟨m, g, -, hg, hgp, heq⟩ := exists_zetaEntire_factor h0 hp1
    have hres := fun u : ℝ => laurentCoeff_worldKernel_eq c (hA p (by linarith)) hg hgp heq
      (u : ℂ)
    simp_rw [hres, Finset.mul_sum]
    rw [show (0 : ℂ) = ∑ j ∈ Finset.range m, (0 : ℂ) by simp]
    refine tendsto_finsetSum _ fun j _ => ?_
    have h := tendsto_normalized_residue_term hlt j
      (iteratedDeriv (m - 1 - j) (fun s => cexp ((s - c) ^ 2) * A s / g s) p /
        ((m - 1 - j).factorial : ℂ))
    refine h.congr fun u => ?_
    ring
  -- the line `Re s = σ`
  have hline' : Tendsto (fun u : ℝ => (Real.exp (-Θ * u) : ℂ) *
      signal (worldKernel c A) σ (Real.exp u)) atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => Real.exp (-((Θ - σ) * u))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (sub_pos.mpr hσΘ)))
    have hT := hexp.const_mul C
    rw [mul_zero] at hT
    refine squeeze_zero_norm' (Eventually.of_forall fun u => ?_) hT
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hb := hC (Real.exp u) (Real.exp_pos u)
    rw [← Real.exp_mul] at hb
    calc Real.exp (-Θ * u) * ‖signal (worldKernel c A) σ (Real.exp u)‖
        ≤ Real.exp (-Θ * u) * (C * Real.exp (u * σ)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = C * Real.exp (-((Θ - σ) * u)) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
  -- assemble
  have hsplit : ∀ u : ℝ, signal (worldKernel c A) 2 (Real.exp u) -
      ∑ p ∈ T, laurentCoeff (fun s => cexp ((u : ℂ) * s) * worldKernel c A s) p (-1) =
      signal (worldKernel c A) σ (Real.exp u) +
        ∑ p ∈ P.filter (fun p => ¬ p.re = Θ),
          laurentCoeff (fun s => cexp ((u : ℂ) * s) * worldKernel c A s) p (-1) := by
    intro u
    have h := signal_worldKernel_sub_eq_sum_residues hσ' hσ'σ hσ1 hfin hline hAσ hMb c
      (Real.exp_pos u)
    rw [Real.log_exp] at h
    rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p.re = Θ)] at h
    simp only [T]
    linear_combination h
  have hsum := tendsto_finsetSum _ hlow
  rw [Finset.sum_const_zero] at hsum
  have htot := hline'.add hsum
  rw [add_zero] at htot
  refine htot.congr fun u => ?_
  rw [hsplit, mul_add, Finset.mul_sum]

/-! ### Möbius and Liouville -/

/-- The numerator of the Möbius kernel: `e^{(s−c)²}(s − 1)/((s − 1)ζ(s)) = e^{(s−c)²}/ζ(s)`. -/
def mobiusNumerator (s : ℂ) : ℂ := s - 1

/-- The numerator of the Liouville kernel: `e^{(s−c)²}(s − 1)ζ(2s)/((s − 1)ζ(s))`. -/
def liouvilleNumerator (s : ℂ) : ℂ := (s - 1) * riemannZeta (2 * s)

theorem worldKernel_mobius (c : ℝ) {s : ℂ} (hs : s ≠ 1) :
    worldKernel c mobiusNumerator s = cexp ((s - c) ^ 2) / riemannZeta s := by
  rw [worldKernel, mobiusNumerator, zetaEntire_eq hs, mul_comm (s - 1) (riemannZeta s),
    mul_div_mul_right _ _ (sub_ne_zero.mpr hs)]

theorem worldKernel_liouville (c : ℝ) {s : ℂ} (hs : s ≠ 1) :
    worldKernel c liouvilleNumerator s =
      cexp ((s - c) ^ 2) * riemannZeta (2 * s) / riemannZeta s := by
  rw [worldKernel, liouvilleNumerator, zetaEntire_eq hs]
  by_cases hz : riemannZeta s = 0
  · simp [hz]
  · field_simp [sub_ne_zero.mpr hs]

theorem analyticAt_mobiusNumerator (s : ℂ) : AnalyticAt ℂ mobiusNumerator s := by
  unfold mobiusNumerator
  fun_prop

theorem analyticAt_liouvilleNumerator {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ liouvilleNumerator s := by
  have h2 : 2 * s ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      Complex.one_re] at hr
    linarith
  have hz : AnalyticAt ℂ (fun s : ℂ => riemannZeta (2 * s)) s := by
    have hopen : IsOpen {s : ℂ | 2 * s ≠ 1} :=
      isOpen_ne_fun (continuous_const.mul continuous_id) continuous_const
    have hd : DifferentiableOn ℂ (fun s => riemannZeta (2 * s)) {s : ℂ | 2 * s ≠ 1} :=
      fun s hs => ((differentiableAt_riemannZeta hs).comp s
        (differentiableAt_id.const_mul 2)).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds h2)
  exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - 1) s).mul hz

theorem norm_mobiusNumerator_le {s : ℂ} (h0 : 0 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖mobiusNumerator s‖ ≤ 1 * (2 + |s.im|) := by
  unfold mobiusNumerator
  have hre : |(s - 1).re| ≤ 1 := by
    rw [Complex.sub_re, Complex.one_re, abs_le]
    constructor <;> linarith
  have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
  linarith

theorem norm_liouvilleNumerator_le {σ : ℝ} (hσ : 1 / 2 < σ) {s : ℂ} (hs : σ ≤ s.re)
    (h2 : s.re ≤ 2) : ‖liouvilleNumerator s‖ ≤ (1 + 1 / (2 * σ - 1)) * (2 + |s.im|) := by
  unfold liouvilleNumerator
  rw [norm_mul]
  have hz := norm_riemannZeta_le_of_le_re (σ₁ := 2 * σ) (by linarith) (s := 2 * s) (by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith)
  have hm := norm_mobiusNumerator_le (s := s) (by linarith) h2
  unfold mobiusNumerator at hm
  have hpos : 0 ≤ 1 + 1 / (2 * σ - 1) := by
    have : 0 < 2 * σ - 1 := by linarith
    positivity
  calc ‖s - 1‖ * ‖riemannZeta (2 * s)‖ ≤ (1 * (2 + |s.im|)) * (1 + 1 / (2 * σ - 1)) :=
        mul_le_mul hm hz (norm_nonneg _) (by positivity)
    _ = (1 + 1 / (2 * σ - 1)) * (2 + |s.im|) := by ring

/-- **The tangent datum of Möbius in world I.** The Gaussian window sum of `1/ζ` at `e^u`,
normalized by `e^{−Θu}`, is asymptotic to the sum of its residues at the top zeros. -/
theorem tangentDatum_mobius
    (hI : ZeroConfigurationGeometry.zetaAsymptoticAbscissa < zetaZeroAbscissa) (c : ℝ) :
    ∃ T : Finset ℂ, (∀ p : ℂ, p ∈ T ↔ riemannZeta p = 0 ∧ p.re = zetaZeroAbscissa) ∧
      Tendsto (fun u : ℝ => (Real.exp (-zetaZeroAbscissa * u) : ℂ) *
        (signal (worldKernel c mobiusNumerator) 2 (Real.exp u) -
          ∑ p ∈ T, laurentCoeff (fun s => cexp ((u : ℂ) * s) * worldKernel c mobiusNumerator s)
            p (-1))) atTop (𝓝 0) :=
  tendsto_normalized_signal_sub_top hI c (fun s _ => analyticAt_mobiusNumerator s)
    fun _ _ => ⟨1, fun _ hs h2 => norm_mobiusNumerator_le (by linarith) h2⟩

/-- **The tangent datum of Liouville in world I.** -/
theorem tangentDatum_liouville
    (hI : ZeroConfigurationGeometry.zetaAsymptoticAbscissa < zetaZeroAbscissa) (c : ℝ) :
    ∃ T : Finset ℂ, (∀ p : ℂ, p ∈ T ↔ riemannZeta p = 0 ∧ p.re = zetaZeroAbscissa) ∧
      Tendsto (fun u : ℝ => (Real.exp (-zetaZeroAbscissa * u) : ℂ) *
        (signal (worldKernel c liouvilleNumerator) 2 (Real.exp u) -
          ∑ p ∈ T, laurentCoeff
            (fun s => cexp ((u : ℂ) * s) * worldKernel c liouvilleNumerator s) p (-1)))
        atTop (𝓝 0) :=
  tendsto_normalized_signal_sub_top hI c (fun _ hs => analyticAt_liouvilleNumerator hs)
    fun σ hσ => ⟨1 + 1 / (2 * σ - 1), fun _ hs h2 => norm_liouvilleNumerator_le hσ hs h2⟩

/-- **The leading coefficients of Möbius and Liouville differ by `ζ(2ρ)`.** With
`(s − 1)ζ(s) = (s − ρ)^m g(s)` at a zero `ρ` right of `½`, the numerators of the two residue
polynomials are `H_μ = e^{(s−c)²}(s − 1)/g` and `H_λ = ζ(2s) H_μ`; both are nonzero at `ρ`. -/
theorem leading_liouville_eq_mobius (c : ℝ) {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1)
    {g : ℂ → ℂ} (hgρ : g ρ ≠ 0) :
    (fun s => cexp ((s - c) ^ 2) * liouvilleNumerator s / g s) =
        (fun s => riemannZeta (2 * s) * (cexp ((s - c) ^ 2) * mobiusNumerator s / g s)) ∧
      cexp ((ρ - c) ^ 2) * mobiusNumerator ρ / g ρ ≠ 0 ∧ riemannZeta (2 * ρ) ≠ 0 := by
  refine ⟨funext fun s => by unfold liouvilleNumerator mobiusNumerator; ring, ?_, ?_⟩
  · unfold mobiusNumerator
    exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (sub_ne_zero.mpr hρ1)) hgρ
  · exact riemannZeta_ne_zero_of_one_lt_re (by
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith)

/-! ### The Möbius window sum -/

open scoped ArithmeticFunction.Moebius

/-- The Gaussian on the line `Re s = 2`: `∫ e^{v(2+it)} e^{(2+it−c)²} dt = √π e^{cv − v²/4}`. -/
theorem integral_gaussian_line (c v : ℝ) :
    ∫ t : ℝ, cexp ((v : ℂ) * (((2 : ℝ) : ℂ) + t * I)) * cexp ((((2 : ℝ) : ℂ) + t * I - c) ^ 2) =
      ((Real.sqrt Real.pi * Real.exp (c * v - v ^ 2 / 4) : ℝ) : ℂ) := by
  have hq : ∀ t : ℝ, cexp ((v : ℂ) * (((2 : ℝ) : ℂ) + t * I)) *
      cexp ((((2 : ℝ) : ℂ) + t * I - c) ^ 2) =
      cexp ((-1 : ℂ) * (t : ℂ) ^ 2 + (I * (2 * (2 - c) + v)) * t + ((2 - c) ^ 2 + 2 * v)) := by
    intro t
    rw [← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (t : ℂ) ^ 2 * Complex.I_sq
  simp_rw [hq]
  rw [integral_cexp_quadratic (by simp) _ _]
  have hπ : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [neg_neg, div_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    push_cast
    rfl
  have hexp : (2 - (c : ℂ)) ^ 2 + 2 * v - (I * (2 * (2 - c) + v)) ^ 2 / (4 * -1) =
      ((c * v - v ^ 2 / 4 : ℝ) : ℂ) := by
    push_cast
    linear_combination ((2 * (2 - (c : ℂ)) + v) ^ 2 / 4) * Complex.I_sq
  rw [hπ, hexp, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- `1/ζ(s) = Σ μ(n) n^{−s}` on `Re s > 1`. -/
theorem inv_riemannZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = LSeries (fun n => (μ n : ℂ)) s := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  exact (eq_inv_of_mul_eq_one_right h).symm

/-- **The Möbius window sum.** The signal of `e^{(s−c)²}/ζ(s)` at `Z` is the Gaussian window sum
`Σ_n μ(n) e^{c(log Z − log n) − (log Z − log n)²/4}/(2√π)` of the Möbius function on the
logarithmic scale. -/
theorem signal_mobius_eq_tsum (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (worldKernel c mobiusNumerator) 2 Z =
      ∑' n : ℕ, (μ n : ℂ) * ((Real.exp (c * (Real.log Z - Real.log n) -
        (Real.log Z - Real.log n) ^ 2 / 4) / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
  rw [signal_eq_integral _ 2 hZ]
  set s : ℝ → ℂ := fun t => ((2 : ℝ) : ℂ) + t * I with hsdef
  have hsre : ∀ t, (s t).re = 2 := fun t => by simp [s]
  have hsim : ∀ t, (s t).im = t := fun t => by simp [s]
  set F : ℕ → ℝ → ℂ := fun n t => cexp ((Real.log Z : ℂ) * s t) * cexp ((s t - c) ^ 2) *
    LSeries.term (fun n => (μ n : ℂ)) (s t) n with hFdef
  have hsum : ∀ t, cexp ((Real.log Z : ℂ) * s t) * worldKernel c mobiusNumerator (s t) =
      ∑' n, F n t := by
    intro t
    have hs1 : s t ≠ 1 := fun h => by
      have := congrArg Complex.re h
      rw [hsre] at this
      norm_num at this
    rw [worldKernel_mobius c hs1, div_eq_mul_inv,
      inv_riemannZeta_eq_LSeries (by rw [hsre]; norm_num), LSeries, ← tsum_mul_left,
      ← tsum_mul_left]
    exact tsum_congr fun n => by simp only [hFdef]; ring
  -- the bound `‖F n t‖ ≤ Z² e^{(|c|+2)²} e^{−t²}/n²`
  set K : ℝ := Z ^ (2 : ℝ) * Real.exp ((|c| + 2) ^ 2)
  have hnorm : ∀ n t, ‖F n t‖ ≤ K * Real.exp (-1 * t ^ 2) * (1 / (n : ℝ) ^ 2) := by
    intro n t
    simp only [F]
    rw [norm_mul, norm_mul, norm_cexp_log_mul hZ, hsre]
    have hE := norm_cexp_sq_le c (s := s t) (by rw [hsre]; norm_num) (by rw [hsre])
    rw [hsim] at hE
    have hT : ‖LSeries.term (fun n => (μ n : ℂ)) (s t) n‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [LSeries.norm_term_eq, hsre]
      split_ifs with hn
      · simp [hn]
      · have hμ : ‖(μ n : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hpos : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := by
          have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
          positivity
        rw [Real.rpow_two] at hpos ⊢
        exact div_le_div_of_nonneg_right hμ hpos.le
    have hK : 0 ≤ K := by positivity
    calc Z ^ (2 : ℝ) * ‖cexp ((s t - c) ^ 2)‖ * ‖LSeries.term (fun n => (μ n : ℂ)) (s t) n‖
        ≤ Z ^ (2 : ℝ) * (Real.exp ((|c| + 2) ^ 2) * Real.exp (-t ^ 2)) * (1 / (n : ℝ) ^ 2) := by
          gcongr
      _ = K * Real.exp (-1 * t ^ 2) * (1 / (n : ℝ) ^ 2) := by
          simp only [K, neg_one_mul]
          ring
  have hgauss : Integrable fun t : ℝ => Real.exp (-1 * t ^ 2) := integrable_exp_neg_mul_sq one_pos
  have hcontF : ∀ n, Continuous (F n) := by
    intro n
    simp only [F]
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, mul_zero]
      exact continuous_const
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hF : (fun t => cexp ((Real.log Z : ℂ) * s t) * cexp ((s t - c) ^ 2) *
          LSeries.term (fun n => (μ n : ℂ)) (s t) n) = fun t => cexp ((Real.log Z : ℂ) * s t) *
          cexp ((s t - c) ^ 2) * ((μ n : ℂ) / (n : ℂ) ^ s t) := by
        funext t
        rw [LSeries.term_of_ne_zero hn]
      rw [hF]
      have hcpow : Continuous fun t : ℝ => (n : ℂ) ^ s t :=
        continuous_const.cpow (by fun_prop) fun _ => Or.inl (by
          simpa using Nat.pos_of_ne_zero hn)
      have hne : ∀ t : ℝ, (n : ℂ) ^ s t ≠ 0 := fun t => by
        rw [Complex.cpow_def_of_ne_zero hn0]
        exact Complex.exp_ne_zero _
      exact (by fun_prop : Continuous fun t : ℝ => cexp ((Real.log Z : ℂ) * s t) *
        cexp ((s t - c) ^ 2)).mul (continuous_const.div hcpow hne)
  have hint : ∀ n, Integrable (F n) := fun n =>
    Integrable.mono' ((hgauss.const_mul K).mul_const (1 / (n : ℝ) ^ 2))
      (hcontF n).aestronglyMeasurable (Eventually.of_forall fun t => hnorm n t)
  have hsummable : Summable fun n => ∫ t, ‖F n t‖ := by
    have hb : ∀ n, ∫ t, ‖F n t‖ ≤ (K * ∫ t : ℝ, Real.exp (-1 * t ^ 2)) * (1 / (n : ℝ) ^ 2) := by
      intro n
      calc ∫ t, ‖F n t‖ ≤ ∫ t, K * Real.exp (-1 * t ^ 2) * (1 / (n : ℝ) ^ 2) :=
            integral_mono (hint n).norm ((hgauss.const_mul K).mul_const _) (hnorm n)
        _ = (K * ∫ t : ℝ, Real.exp (-1 * t ^ 2)) * (1 / (n : ℝ) ^ 2) := by
            rw [integral_mul_const, integral_const_mul]
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hb
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _)
  have hswap := integral_tsum_of_summable_integral_norm hint hsummable
  rw [integral_congr_ae (Eventually.of_forall hsum), ← hswap, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F]
  · have hFn : (F n) = fun t : ℝ => (μ n : ℂ) * (cexp (((Real.log Z - Real.log n : ℝ) : ℂ) *
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)) * cexp ((((2 : ℝ) : ℂ) + (t : ℂ) * I - c) ^ 2)) := by
      funext t
      simp only [F]
      rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
        ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), div_eq_mul_inv,
        ← Complex.exp_neg]
      simp only [s]
      rw [show cexp ((Real.log Z : ℂ) * (((2 : ℝ) : ℂ) + t * I)) *
          cexp ((((2 : ℝ) : ℂ) + t * I - c) ^ 2) * ((μ n : ℂ) *
          cexp (-((Real.log n : ℂ) * (((2 : ℝ) : ℂ) + t * I)))) =
          (μ n : ℂ) * (cexp ((Real.log Z : ℂ) * (((2 : ℝ) : ℂ) + t * I) +
          -((Real.log n : ℂ) * (((2 : ℝ) : ℂ) + t * I))) *
          cexp ((((2 : ℝ) : ℂ) + t * I - c) ^ 2)) by rw [Complex.exp_add]; ring]
      congr 3
      push_cast
      ring
    rw [hFn, integral_const_mul, integral_gaussian_line]
    have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    push_cast
    field_simp
    rw [← hsq]
    push_cast
    ring

end GaloisForLFunctions.FloorFreeArithmetic
