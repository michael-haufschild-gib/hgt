import GaloisForLFunctions.RHTower.JointAncestryExactPhaseBudget
import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorTotalVariation

/-!
# Per-zero phase budgets force positivity of the dressed aggregate

For a finite family of rational characters supported on a finite prime set `P`, the quadratic form
of the `σ`-dressed aggregate (`σ = 1/2 + c`, `c > 0`) splits over the zeros:

`Σ_{i,j} c_i c̄_j N_σ(n_i - n_j) = Σ_ρ (1/(ρ(1-ρ))) ∫_{T^P} |Σ_i c_i χ̄_{n_i}|² D_ρ`,

where `D_ρ = ∏_{p ∈ P} ℓ_p^ρ` is the depth-`P` density of the dressed sector of `ρ`, whose Fourier
coefficients are the dressed coefficients `u^{-(ρ+c)} v^{-(1-ρ+c)}`.  If the weight's argument plus
the sector's phase budget stays below `π/2`,

`|arg (1/(ρ(1-ρ)))| + Σ_p W_p(ρ) ≤ π/2`,

then `Re (D_ρ/(ρ(1-ρ))) ≥ 0` on the whole torus and the zero contributes a nonnegative amount.
Hence the dressed aggregate is positive semidefinite as soon as every zero is individually within
budget: positivity of the aggregate is free exactly in the regime where every sector is individually
oriented.  Under RH every budget vanishes and the weights are positive, recovering positivity for
every `σ > 1/2`.
-/

open Complex MeasureTheory
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-! ## Fourier coefficients of local densities -/

/-- The local coefficient: `a^k` for `k ≥ 0`, `b^{-k}` for `k < 0`. -/
def jasLocalCoeff (a b : ℂ) (k : ℤ) : ℂ := if 0 ≤ k then a ^ k.toNat else b ^ (-k).toNat

theorem tsum_pow_mul_single (a : ℂ) (k : ℤ) :
    ∑' j : ℕ, a ^ j * (Pi.single (j : ℤ) (1 : ℂ) : ℤ → ℂ) k = if 0 ≤ k then a ^ k.toNat else 0 := by
  split_ifs with hk
  · rw [tsum_eq_single k.toNat]
    · rw [Int.toNat_of_nonneg hk, Pi.single_eq_same, mul_one]
    · intro j hj
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h; apply hj; omega
  · refine (tsum_congr fun j => ?_).trans tsum_zero
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h; omega

theorem integral_fourier_neg_mul_inv_one_sub_eq {a : ℂ} (ha : ‖a‖ < 1) (k : ℤ) :
    ∫ θ, fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹ ∂jasCircleHaar =
      if 0 ≤ k then a ^ k.toNat else 0 := by
  rw [integral_fourier_mul_inv_one_sub ha, tsum_pow_mul_single]

theorem integral_fourier_neg_mul_inv_one_sub_conj_eq {b : ℂ} (hb : ‖b‖ < 1) (k : ℤ) :
    ∫ θ, fourier (-k) θ * (1 - b * conj (fourier 1 θ))⁻¹ ∂jasCircleHaar =
      if k ≤ 0 then b ^ (-k).toNat else 0 := by
  have h : ∀ θ : UnitAddCircle, fourier (-k) θ * (1 - b * conj (fourier 1 θ))⁻¹ =
      conj (fourier (-(-k)) θ * (1 - conj b * fourier 1 θ)⁻¹) := by
    intro θ
    rw [inv_one_sub_mul_conj_fourier, map_mul, neg_neg, ← fourier_neg]
  simp_rw [h]
  rw [integral_conj, integral_fourier_neg_mul_inv_one_sub_eq (by rwa [Complex.norm_conj])]
  by_cases hk : k ≤ 0
  · rw [if_pos (by omega), if_pos hk, map_pow, Complex.conj_conj]
  · rw [if_neg (by omega), if_neg hk, map_zero]

theorem integral_fourier_neg_eq (k : ℤ) :
    ∫ θ, fourier (-k) θ ∂jasCircleHaar = if k = 0 then 1 else 0 := by
  have hc := congrFun (fourierCoeff_fourier (T := 1) (0 : ℤ)) k
  rw [fourierCoeff] at hc
  simp only [smul_eq_mul, fourier_zero, mul_one] at hc
  rw [hc]
  by_cases hk : k = 0
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, if_neg hk]

/-- **Fourier coefficients of a local density.** -/
theorem integral_fourier_neg_mul_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (k : ℤ) :
    ∫ θ, fourier (-k) θ * jasHoloCircle a b θ ∂jasCircleHaar = jasLocalCoeff a b k := by
  have hc1 : Continuous fun θ : UnitAddCircle => fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹ :=
    (fourier (-k)).continuous.mul (continuous_inv_one_sub_mul_fourier ha)
  have hc2 : Continuous fun θ : UnitAddCircle =>
      fourier (-k) θ * (1 - b * conj (fourier 1 θ))⁻¹ := by
    refine (fourier (-k)).continuous.mul ?_
    simp_rw [inv_one_sub_mul_conj_fourier]
    exact Complex.continuous_conj.comp
      (continuous_inv_one_sub_mul_fourier (by rwa [Complex.norm_conj]))
  have hsplit : ∀ θ, fourier (-k) θ * jasHoloCircle a b θ =
      fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹ + fourier (-k) θ * (1 - b * conj (fourier 1 θ))⁻¹ -
        fourier (-k) θ := by
    intro θ; unfold jasHoloCircle jasHoloLocal; ring
  simp_rw [hsplit]
  have hf : Integrable (fun θ : UnitAddCircle => fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹ +
      fourier (-k) θ * (1 - b * conj (fourier 1 θ))⁻¹) jasCircleHaar :=
    (integrable_of_continuous_circle hc1).add (integrable_of_continuous_circle hc2)
  rw [integral_sub hf (integrable_of_continuous_circle (fourier (-k)).continuous),
    integral_add (integrable_of_continuous_circle hc1) (integrable_of_continuous_circle hc2),
    integral_fourier_neg_mul_inv_one_sub_eq ha, integral_fourier_neg_mul_inv_one_sub_conj_eq hb,
    integral_fourier_neg_eq, jasLocalCoeff]
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [if_neg (by omega), if_pos hk.le, if_neg hk.ne, if_neg (by omega)]; ring
  · subst hk; simp
  · rw [if_pos hk.le, if_neg (by omega), if_neg hk.ne', if_pos hk.le]; ring

/-! ## The single-zero Gram identity -/

/-- The conjugate character `x ↦ ∏_{p ∈ P} e(-n_p x_p)` on the depth-`P` torus. -/
def jasCharBar (P : Finset Nat.Primes) (n : Nat.Primes →₀ ℤ) (x : ↥P → UnitAddCircle) : ℂ :=
  ∏ i : ↥P, fourier (-(n i)) (x i)

theorem continuous_jasCharBar (P : Finset Nat.Primes) (n : Nat.Primes →₀ ℤ) :
    Continuous (jasCharBar P n) := by
  unfold jasCharBar
  exact continuous_finsetProd _ fun i _ => (fourier _).continuous.comp (continuous_apply i)

theorem jasCharBar_mul_conj (P : Finset Nat.Primes) (m n : Nat.Primes →₀ ℤ)
    (x : ↥P → UnitAddCircle) :
    jasCharBar P m x * conj (jasCharBar P n x) = jasCharBar P (m - n) x := by
  rw [jasCharBar, jasCharBar, jasCharBar, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← fourier_neg, neg_neg, ← fourier_add, Finsupp.sub_apply]
  congr 2; ring

/-- The depth-`P` density of a dressed sector. -/
def jasSectorDensity (q : ℂ) (c : ℝ) (P : Finset Nat.Primes) (x : ↥P → UnitAddCircle) : ℂ :=
  ∏ i : ↥P, jasHoloCircle (jasHoloA (q + c) i) (jasHoloB (q - c) i) (x i)

theorem norm_jasHoloA_dressed_lt_one {q : ℂ} {c : ℝ} (h : 0 < q.re + c) (p : Nat.Primes) :
    ‖jasHoloA (q + c) p‖ < 1 := by
  rw [norm_jasHoloA, Real.exp_lt_one_iff]
  simp only [Complex.add_re, Complex.ofReal_re]
  nlinarith [log_prime_pos p]

theorem norm_jasHoloB_dressed_lt_one {q : ℂ} {c : ℝ} (h : 0 < 1 - q.re + c) (p : Nat.Primes) :
    ‖jasHoloB (q - c) p‖ < 1 := by
  rw [jasHoloB, Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.neg_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [log_prime_pos p]

theorem continuous_jasSectorDensity {q : ℂ} {c : ℝ} (h0 : 0 < q.re + c) (h1 : 0 < 1 - q.re + c)
    (P : Finset Nat.Primes) : Continuous (jasSectorDensity q c P) := by
  unfold jasSectorDensity
  exact continuous_finsetProd _ fun i _ =>
    (continuous_jasHoloCircle (norm_jasHoloA_dressed_lt_one h0 i)
      (norm_jasHoloB_dressed_lt_one h1 i)).comp (continuous_apply i)

/-- Fourier coefficients of the depth-`P` sector density are the dressed coefficients. -/
theorem integral_jasCharBar_mul_jasSectorDensity {q : ℂ} {c : ℝ} (h0 : 0 < q.re + c)
    (h1 : 0 < 1 - q.re + c) (P : Finset Nat.Primes) {n : Nat.Primes →₀ ℤ}
    (hn : n.support ⊆ P) :
    ∫ x, jasCharBar P n x * jasSectorDensity q c P x ∂Measure.pi (fun _ => jasCircleHaar) =
      jasDressedCoeff (q + c) (q - c) n := by
  rw [jasDressedCoeff, Finsupp.prod_of_support_subset _ hn _ (fun i _ => by
      simp [jasDressedLocalCoeff])]
  unfold jasCharBar jasSectorDensity
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun i : ↥P => fun θ => fourier (-(n i)) θ *
      jasHoloCircle (jasHoloA (q + c) i) (jasHoloB (q - c) i) θ), ← Finset.prod_coe_sort P]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_fourier_neg_mul_jasHoloCircle (norm_jasHoloA_dressed_lt_one h0 i)
    (norm_jasHoloB_dressed_lt_one h1 i)]
  rfl

/-- **Single-zero Gram identity.** -/
theorem gram_jasDressedCoeff_eq_integral {q : ℂ} {c : ℝ} (h0 : 0 < q.re + c)
    (h1 : 0 < 1 - q.re + c) (P : Finset Nat.Primes) {ι : Type*} (t : Finset ι) (cc : ι → ℂ)
    (n : ι → Nat.Primes →₀ ℤ) (hn : ∀ i ∈ t, (n i).support ⊆ P) :
    ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasDressedCoeff (q + c) (q - c) (n i - n j) =
      ∫ x, (∑ i ∈ t, cc i * jasCharBar P (n i) x) * conj (∑ i ∈ t, cc i * jasCharBar P (n i) x) *
        jasSectorDensity q c P x ∂Measure.pi (fun _ => jasCircleHaar) := by
  have hint : ∀ i j, Integrable (fun x => cc i * conj (cc j) *
      (jasCharBar P (n i - n j) x * jasSectorDensity q c P x))
      (Measure.pi fun _ => jasCircleHaar) := by
    intro i j
    exact ((continuous_const.mul ((continuous_jasCharBar P _).mul
      (continuous_jasSectorDensity h0 h1 P))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hpt : ∀ x, (∑ i ∈ t, cc i * jasCharBar P (n i) x) *
      conj (∑ i ∈ t, cc i * jasCharBar P (n i) x) * jasSectorDensity q c P x =
      ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        (jasCharBar P (n i - n j) x * jasSectorDensity q c P x) := by
    intro x
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← jasCharBar_mul_conj, map_mul]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsub : (n i - n j).support ⊆ P := fun p hp => by
    rw [Finsupp.mem_support_iff, Finsupp.sub_apply] at hp
    by_contra hpP
    have h1' : n i p = 0 := Finsupp.notMem_support_iff.mp (fun h => hpP (hn i hi h))
    have h2' : n j p = 0 := Finsupp.notMem_support_iff.mp (fun h => hpP (hn j hj h))
    exact hp (by rw [h1', h2', sub_zero])
  rw [integral_const_mul, integral_jasCharBar_mul_jasSectorDensity h0 h1 P hsub]

/-! ## Per-zero orientation -/

/-- If the weight's argument plus the phase budget stays below `π/2`, the weighted sector density
has nonnegative real part at every point of the torus. -/
theorem re_mul_jasSectorDensity_nonneg {q : ℂ} {c : ℝ} (h0 : 0 < q.re + c)
    (h1 : 0 < 1 - q.re + c) (P : Finset Nat.Primes) {w : ℂ}
    (hbudget : |w.arg| + ∑ p ∈ P, jasPhaseWidth (jasR1 (q + c) p) (jasR2 (q - c) p) ≤ Real.pi / 2)
    (x : ↥P → UnitAddCircle) :
    0 ≤ (w * jasSectorDensity q c P x).re := by
  have hr₁ : ∀ p, 0 ≤ jasR1 (q + c) p := fun p => (Real.exp_pos _).le
  have hr₂ : ∀ p, 0 ≤ jasR2 (q - c) p := fun p => (Real.exp_pos _).le
  have hr₁' : ∀ p, jasR1 (q + c) p < 1 := fun p => by
    rw [jasR1_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hr₂' : ∀ p, jasR2 (q - c) p < 1 := fun p => by
    rw [jasR2_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  -- rotate each unit point to its Kronecker frame
  set φ : ↥P → ℝ := fun i =>
    (fourier 1 (x i) / jasKroneckerPoint (q + c) (i : Nat.Primes)).arg with hφ
  have hrot : ∀ i : ↥P, fourier 1 (x i) =
      cexp ((φ i : ℂ) * I) * jasKroneckerPoint (q + c) (i : Nat.Primes) := by
    intro i
    have hK : jasKroneckerPoint (q + c) (i : Nat.Primes) ≠ 0 := by
      rw [jasKroneckerPoint]; exact Complex.exp_ne_zero _
    have hn : ‖fourier 1 (x i) / jasKroneckerPoint (q + c) (i : Nat.Primes)‖ = 1 := by
      rw [norm_div, norm_fourier_unit, norm_jasKroneckerPoint, div_one]
    have := Complex.norm_mul_exp_arg_mul_I
      (fourier 1 (x i) / jasKroneckerPoint (q + c) (i : Nat.Primes))
    rw [hn, Complex.ofReal_one, one_mul] at this
    simp only [hφ]
    rw [this, div_mul_cancel₀ _ hK]
  have hD : jasSectorDensity q c P x =
      ∏ i : ↥P, jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i) := by
    unfold jasSectorDensity jasHoloCircle
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hrot i, jasHoloLocal_twisted_eq_jasRotLocal q c (φ i) i (hr₁' _) (hr₂' _)]
  rw [hD, prod_eq_prod_norm_mul_exp_sum_arg]
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I w]
  rw [show (‖w‖ : ℂ) * cexp ((w.arg : ℂ) * I) *
      (((∏ i : ↥P, ‖jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)‖ : ℝ) : ℂ) *
        cexp (((∑ i : ↥P, (jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)).arg : ℝ) : ℂ) *
          I)) =
      (((‖w‖ * ∏ i : ↥P, ‖jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)‖ : ℝ)) : ℂ) *
        cexp (((w.arg + ∑ i : ↥P, (jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)).arg :
          ℝ) : ℂ) * I) by
    rw [mul_mul_mul_comm, ← Complex.exp_add]; push_cast; ring_nf]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  refine mul_nonneg (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)) ?_
  apply Real.cos_nonneg_of_mem_Icc
  have hsum : |∑ i : ↥P, (jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)).arg| ≤
      ∑ p ∈ P, jasPhaseWidth (jasR1 (q + c) p) (jasR2 (q - c) p) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : ↥P, |(jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)).arg|
        ≤ ∑ i : ↥P, jasPhaseWidth (jasR1 (q + c) i) (jasR2 (q - c) i) :=
          Finset.sum_le_sum fun i _ => abs_arg_jasRotLocal_le (hr₁ _) (hr₁' _) (hr₂ _) (hr₂' _) _
      _ = ∑ p ∈ P, jasPhaseWidth (jasR1 (q + c) p) (jasR2 (q - c) p) :=
          Finset.sum_coe_sort P (fun p => jasPhaseWidth (jasR1 (q + c) p) (jasR2 (q - c) p))
  constructor <;> linarith [neg_abs_le w.arg, le_abs_self w.arg,
    neg_abs_le (∑ i : ↥P, (jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)).arg),
    le_abs_self (∑ i : ↥P, (jasRotLocal (jasR1 (q + c) i) (jasR2 (q - c) i) (φ i)).arg)]

/-! ## The aggregate -/

/-- **Per-zero phase budgets force positivity.**  If for every Xi zero the argument of its weight
`1/(ρ(1-ρ))` plus its dressed phase budget over any finite prime set stays below `π/2`, then the
dressed aggregate is positive semidefinite at `σ = 1/2 + c`. -/
theorem jasDressedPSD_of_phaseBudget {c : ℝ} (hc : 0 < c)
    (hbudget : ∀ (q : XiZeroCopy) (P : Finset Nat.Primes),
      |(1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).arg| +
        ∑ p ∈ P, jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) ≤ Real.pi / 2) :
    JasDressedPSD (1 / 2 + c) := by
  classical
  intro ι t cc n _
  set P : Finset Nat.Primes := t.biUnion (fun i => (n i).support) with hP
  have hn : ∀ i ∈ t, (n i).support ⊆ P := fun i hi p hp =>
    Finset.mem_biUnion.mpr ⟨i, hi, hp⟩
  have hc' : (1 / 2 + c - 1 / 2 : ℝ) = c := by ring
  have hs : ∀ i j, Summable (fun q : XiZeroCopy => cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    intro i j
    have := (summable_jasDressedCoeff_term (1 / 2 + c) (n i - n j)).mul_left (cc i * conj (cc j))
    simpa only [hc'] using this
  have hswap : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) * jasDressedLagAggregate (1 / 2 + c) (n i - n j) =
      ∑' q : XiZeroCopy, ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    simp_rw [jasDressedLagAggregate_eq_tsum, hc', ← tsum_mul_left]
    rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hs i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => hs i j]
  have hsumm : Summable (fun q : XiZeroCopy => ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) :=
    summable_sum fun i _ => summable_sum fun j _ => hs i j
  rw [hswap, Complex.re_tsum hsumm]
  refine tsum_nonneg fun q => ?_
  have h0 : 0 < (q.1 : ℂ).re + c := by
    linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
  have h1 : 0 < 1 - (q.1 : ℂ).re + c := by
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  set w : ℂ := 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) with hw
  have hterm : ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
      (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) =
      w * ∑ i ∈ t, ∑ j ∈ t, cc i * conj (cc j) *
        jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c) (n i - n j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw]; ring
  rw [hterm, gram_jasDressedCoeff_eq_integral h0 h1 P t cc n hn, ← integral_const_mul]
  set f : (↥P → UnitAddCircle) → ℂ := fun x => ∑ i ∈ t, cc i * jasCharBar P (n i) x with hf
  have hcont : Continuous fun x => w * (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x) := by
    refine continuous_const.mul ?_
    have hfc : Continuous f :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_jasCharBar P _)
    exact (hfc.mul (Complex.continuous_conj.comp hfc)).mul (continuous_jasSectorDensity h0 h1 P)
  have hint := hcont.integrable_of_hasCompactSupport (μ := Measure.pi fun _ => jasCircleHaar)
    (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  refine integral_nonneg fun x => ?_
  have hpos := re_mul_jasSectorDensity_nonneg h0 h1 P (hbudget q P) x
  rw [show w * (f x * conj (f x) * jasSectorDensity (q.1 : ℂ) c P x) =
      ((Complex.normSq (f x) : ℝ) : ℂ) * (w * jasSectorDensity (q.1 : ℂ) c P x) by
    rw [← Complex.mul_conj]; ring, Complex.re_ofReal_mul]
  exact mul_nonneg (Complex.normSq_nonneg _) hpos

/-- Under RH every budget vanishes and every weight is positive: positivity at every `σ > 1/2`
(a second proof of the forward direction through the phase-budget criterion). -/
theorem jasDressedPSD_of_riemannHypothesis_phaseBudget (hRH : RiemannHypothesis) {c : ℝ}
    (hc : 0 < c) : JasDressedPSD (1 / 2 + c) := by
  refine jasDressedPSD_of_phaseBudget hc fun q P => ?_
  have hcrit : ((q.1 : ℂ)).re = 1 / 2 := xi_divisor_support_re_eq_half_of_rh hRH q.1
  have hW : ∀ p ∈ P, jasPhaseWidth (jasR1 ((q.1 : ℂ) + c) p) (jasR2 ((q.1 : ℂ) - c) p) = 0 := by
    intro p _
    rw [jasPhaseWidth, jasR1_dressed, jasR2_dressed, hcrit,
      show -(1 - 1 / 2 + c) = -(1 / 2 + c) by ring, sub_self, abs_zero, zero_div,
      Real.arctan_zero]
  rw [Finset.sum_eq_zero hW, add_zero, inv_mul_one_sub_eq_of_critical hcrit,
    Complex.arg_ofReal_of_nonneg (by positivity), abs_zero]
  linarith [Real.pi_pos]

end

end RHTower
